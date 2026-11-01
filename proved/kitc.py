#!/usr/bin/env python3
"""kitc.py [--no-build] NAME...   (inside the image, in the repo's directory)

A kit program (hand/NAME.body, or a path to a .body file) through the proved route (with --reflect, first through the
verified compiler: see reflect(); a program it does not read takes the steps below):
  1. the translator reads the function `main` applies and every function of the file it uses (proved/KQMTrans.v)
     and the kernel checks, for each, that the KQL function computes it (proved/KQMAuto.v);
  2. the generated Clight is printed as C (proved/KQLPrint.v);
  3. a driver fills the two tables of the proved theorem (the address and the size of each block) from the kit's
     loader, calls the entry function with the numbers `main` gives it, and returns what `main` returns;
  4. clang builds it with the kit's support code: bin/P_NAME, a program that reads the same memory file and the
     same command line as the kit's own.
The Rocq files are written to proved/gen/, the C to proved/gen/NAME_proved.c."""
import re, subprocess, sys, os, glob, hashlib, time, concurrent.futures, shutil, functools

ROOT = os.getcwd()
GEN = os.path.join(ROOT, "proved", "gen")
os.makedirs(GEN, exist_ok=True)

HDR = """From Stdlib Require Import ZArith List.
From MetaRocq.Template Require Import All.
From KQC Require KQL KQLAuto KQM KQMAuto KQMTrans KQMTop KQLGen KQLProof KQLPrint.
From KQ Require Import KQRun.
Import KQMTrans KQMAuto.
Open Scope bool_scope.
"""

def coqc(path, extra=()):
    r = subprocess.run(["coqc", "-w", "-all", "-R", ROOT, "KQ", "-Q", os.path.join(ROOT, "proved"), "KQC", "-Q", GEN, "KQG", *extra, path],
                       capture_output=True, text=True, cwd=GEN)
    return r.returncode, r.stdout + r.stderr

def split_main(body):
    i = body.index("Definition main")
    return body[:i], body[i:]

def cexpr(e):
    """an expression of numbers, kq_arg k, + - * and parentheses, as unsigned 64-bit arithmetic in C"""
    e = re.sub(r"kq_arg\s+(\d+)", r"A(\1)", e)
    e = re.sub(r"(?<![A-Za-z_(0-9])(\d+)", r"\1ULL", e)
    return e

def parse_main(mt):
    """-> (entry, args, wrap): args are ('N', k) | ('I', k) | ('L', literal) | ('M',) ; wrap is 'sum' or 'int'"""
    m = re.search(r"kq_keep\s*:=.*?\bin\b(.*)\.\s*$", mt, re.S)
    if not m:
        raise SystemExit("cannot read main")
    e = " ".join(m.group(1).split())
    wrap = "int"
    if e.startswith("kq_sum"):
        wrap = "sum"
        e = e[len("kq_sum"):].strip()
        assert e[0] == "(" and e[-1] == ")", e
        e = e[1:-1].strip()
    # head and top-level arguments
    toks, depth, cur = [], 0, ""
    for ch in e:
        if ch == "(":
            depth += 1
        if ch == ")":
            depth -= 1
        if ch == " " and depth == 0:
            if cur:
                toks.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        toks.append(cur)
    entry, rest = toks[0], toks[1:]
    args = []
    for t in rest:
        t = t.strip()
        while t.startswith("(") and t.endswith(")") and re.fullmatch(r"\(\s*[-0-9]+\s*\)", t):
            t = t[1:-1].strip()
        if re.fullmatch(r"\(kq_nat \(kq_arg (\d+)\)\)", t):
            args.append(("N", int(re.fullmatch(r"\(kq_nat \(kq_arg (\d+)\)\)", t).group(1))))
        elif re.fullmatch(r"\(kq_arg (\d+)\)", t):
            args.append(("I", int(re.fullmatch(r"\(kq_arg (\d+)\)", t).group(1))))
        elif re.fullmatch(r"\(kq_input 0\)", t):
            args.append(("M",))
        elif re.fullmatch(r"-?\d+", t):
            args.append(("L", int(t)))
        else:
            m2 = re.fullmatch(r"\(kq_nat (.*)\)", t)
            inner = m2.group(1) if m2 else t
            if re.fullmatch(r"[0-9kq_arg+*()\- ]+", inner) and "kq_arg" in inner:
                args.append(("NE" if m2 else "IE", cexpr(inner)))
            else:
                raise SystemExit("main passes something this tool does not read: " + t)
    return entry, args, wrap

def translate_cmd(prog, entry, name):
    # a program that shares narrow blocks with another processor lists them: Definition kq_shared : list int := [6].
    if re.search(r"Definition\s+kq_shared\b", prog):
        return f'kqm_translate_s {entry} "{name}_prog" kq_shared'
    return f'kqm_translate {entry} "{name}_prog"'

def tactic_setup(helpers, pairfns):
    t = f"Set Default Timeout {os.environ.get('KQ_TIMEOUT', '300')}.\n"
    if helpers:
        t += "Ltac kqm_unf ::= cbv beta zeta iota delta [" + " ".join(helpers) + "].\n"
        t += "Ltac kqm_unf_nz ::= cbv beta iota delta [" + " ".join(helpers) + "].\n"
    if pairfns:
        # functions that give back two numbers: the second goes through the slot block, which the proof puts back as it was
        t += "Ltac kqm_laws ::= kqm_laws_on.\nLtac kqm_pairs ::= kqm_pairs_on.\n"
        t += "Ltac kqm_uh h ::= first [ progress cbn [h] | unfold h ].\n"
        t += "Ltac kqm_unf2 ::= cbn [" + " ".join(pairfns) + "].\n"
    return t

def units(fns, groups):
    """-> [(f, i, grp)]: one unit per function, or per group of functions that call each other"""
    out, done = [], set()
    for i, f in enumerate(fns):
        if f in done:
            continue
        grp = next((g for g in groups if g[0] == f), None)
        out.append((f, i, grp))
        done.update(grp if grp else [f])
    return out

def unit_text(fns, f, i, grp):
    pre = "".join(f"pose proof {g}_ok as H{j}; hnf in H{j}. " for j, g in enumerate(fns[:i]))
    if grp:
        # functions that call each other: one lemma for all, by induction on the counter they share
        n = len(grp)
        conj = lambda ms: ms[0] + "_kat d" if len(ms) == 1 else ms[0] + "_kat d /\\ (" + conj(ms[1:]) + ")"
        pat = lambda k: f"IH{k}" if k == n else f"[IH{k} " + pat(k + 1) + "]"
        hn = "; ".join(f"hnf in IH{k}" for k in range(1, n + 1))
        t = f"Lemma {f}_grp : forall d : nat, {conj(grp)}.\nProof. {pre}induction d as [|d {pat(1)}]; [ | {hn} ]; repeat split; kqm_auto. Qed.\n"
        for k, m in enumerate(grp):
            proj = f"({f}_grp d)"
            for _ in range(k):
                proj = f"(proj2 {proj})"
            if k < n - 1:
                proj = f"(proj1 {proj})"
            t += f"Lemma {m}_ok : {m}_kstmt. Proof. exact (fun d => {proj}). Qed.\n"
        return t
    return f"Lemma {f}_ok : {f}_kstmt. Proof. {pre}kqm_auto. Qed.\n"

def stub_text(fns, f, i, grp):
    return "".join(f"Lemma {m}_ok : {m}_kstmt. Proof. Admitted.\n" for m in (grp if grp else [f]))

def proof_file(name, prog, entry, fns, helpers, groups=(), pairfns=()):
    """the whole proof in one file (KQ_MONO=1): every lemma is checked in one run, in order"""
    t = HDR + prog + f'\nMetaRocq Run ({translate_cmd(prog, entry, name)}).\n' + tactic_setup(helpers, pairfns)
    for f, i, grp in units(fns, groups):
        t += unit_text(fns, f, i, grp)
    return t

@functools.lru_cache(maxsize=None)
def rocq_id():
    """the Rocq that checks the proofs: the content of its executables (the kernel is linked into them -- an upgrade or
    our fork must not reuse proofs another kernel checked) and whether the kernel's conversion memo is on"""
    h = hashlib.sha256()
    for exe in ("coqc", "rocq"):
        p = shutil.which(exe)
        if p:
            h.update(open(os.path.realpath(p), "rb").read())
    h.update(os.environ.get("ROCQ_CONV_CACHE", "").encode())
    return h.hexdigest()

def lib_hash():
    h = hashlib.sha256()
    for p in sorted(glob.glob(os.path.join(ROOT, "proved", "*.v")) + [os.path.join(ROOT, "KQRun.v")]):
        h.update(open(p, "rb").read())
    h.update(HDR.encode())
    h.update(rocq_id().encode())
    return h.hexdigest()

def unit_keys(name, fns, helpers, groups, pairfns, setup):
    """a key for each unit: the libraries, the tactic setup, and what Rocq prints for the unit's functions, their statements
    and everything of the program they mention (the functions are named in each other's printed text)"""
    info = os.path.join(GEN, f"{name}_i.v")
    names = list(fns) + [h for h in helpers if h not in fns]
    t = HDR + f"From KQG Require Import {name}_t.\nSet Printing All.\n"
    for n in names:
        t += f'Redirect "{name}_pr_{n}" Print {n}.\n'
    for n in fns:
        t += f'Redirect "{name}_ps_{n}" Print {n}_kstmt.\n'
    open(info, "w").write(t)
    rc, out = coqc(info)
    if rc != 0:
        return None
    rd = lambda path: open(path).read() if os.path.exists(path) else ""
    pr = {n: rd(os.path.join(GEN, f"{name}_pr_{n}.out")) for n in names}
    ps = {n: rd(os.path.join(GEN, f"{name}_ps_{n}.out")) for n in fns}
    base = lib_hash() + setup
    keys = {}
    for f, i, grp in units(fns, groups):
        seen, todo = set(), list(grp if grp else [f])
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            for m in names:
                if m not in seen and re.search(r"(?<![A-Za-z0-9_'])" + re.escape(m) + r"(?![A-Za-z0-9_'])", pr[n] + ps.get(n, "")):
                    todo.append(m)
        h = hashlib.sha256(base.encode())
        for n in sorted(seen):
            h.update(n.encode() + b"\0" + pr[n].encode() + b"\0" + ps.get(n, "").encode() + b"\0")
        keys[f] = h.hexdigest()
    return keys

def prove_units(name, fns, helpers, groups, pairfns, jobs, strict):
    """each unit is checked alone, in its own file, against the statements of the functions before it (taken as given
    there); the units that are not already in the cache run in parallel. -> the functions left unproved"""
    setup = tactic_setup(helpers, pairfns)
    us = units(fns, groups)
    keys = unit_keys(name, fns, helpers, groups, pairfns, setup)
    cdir = os.path.join(GEN, "cache")
    os.makedirs(cdir, exist_ok=True)
    def run(u):
        f, i, grp = u
        k = keys[f] if keys else None
        if k and os.path.exists(os.path.join(cdir, k)):
            return u, 0, "cached"
        t = HDR + f"From KQG Require Import {name}_t.\n" + setup
        t += "".join(stub_text(fns, g, j, gg) for g, j, gg in us[:us.index(u)])
        t += unit_text(fns, f, i, grp)
        path = os.path.join(GEN, f"{name}_u_{f}.v")
        open(path, "w").write(t)
        t0 = time.time()
        rc, out = coqc(path)
        if os.environ.get("KQ_TIMES"):
            print(f"  [{name} {f}: {time.time() - t0:.1f}s]", flush=True)
        if rc == 0 and k:
            open(os.path.join(cdir, k), "w").write(name + " " + f + "\n")
        return u, rc, out
    unproved = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        for u, rc, out in ex.map(run, us):
            if rc != 0:
                if strict:
                    print(name, "PROOF FAILED:", u[0], out[-400:].replace("\n", " "))
                    return None
                unproved.extend(u[2] if u[2] else [u[0]])
    return unproved

HW_WRAPPERS = r"""
unsigned long long f91000(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3) { kq_hw_load(a0, a1, a2, a3, KQ_V(0)); return 1ULL; }
unsigned long long f91001(unsigned long long a0, unsigned long long a1, unsigned long long a2) { kq_hw_store(a0, a1, a2, KQ_V(0)); return 1ULL; }
unsigned long long f91002(unsigned long long a0, unsigned long long a1, unsigned long long a2) { kq_hw_store64(a0, a1, a2, KQ_V(0)); return 1ULL; }
unsigned long long f91003(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4, unsigned long long a5) { kq_hw_atomic(a0, a1, a2, a3, a4, a5, KQ_V(0)); return 1ULL; }
unsigned long long f91004(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4, unsigned long long a5) { kq_hw_atomic64(a0, a1, a2, a3, a4, a5, KQ_V(0)); return 1ULL; }
unsigned long long f91005(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4, unsigned long long a5) { kq_hw_cas(a0, a1, a2, a3, a4, a5, KQ_V(0)); return 1ULL; }
unsigned long long f91006(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4, unsigned long long a5, unsigned long long a6) { kq_hw_cas64(a0, a1, a2, a3, a4, a5, a6, KQ_V(0)); return 1ULL; }
unsigned long long f91007(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3) { kq_hw_aload(a0, a1, a2, a3, KQ_V(0)); return 1ULL; }
unsigned long long f91008(unsigned long long a0, unsigned long long a1, unsigned long long a2) { kq_hw_astore(a0, a1, a2, KQ_V(0)); return 1ULL; }
unsigned long long f91009(unsigned long long a0, unsigned long long a1, unsigned long long a2) { kq_hw_astore64(a0, a1, a2, KQ_V(0)); return 1ULL; }
unsigned long long f91010(unsigned long long a0) { kq_hw_fence(a0, KQ_V(0)); return 1ULL; }
unsigned long long f91011(unsigned long long a0, unsigned long long a1, unsigned long long a2) { kq_hw_copy(a0, a1, a2, KQ_V(0)); return 1ULL; }
unsigned long long f91012(unsigned long long a0, unsigned long long a1, unsigned long long a2) { kq_hw_fill(a0, a1, a2, KQ_V(0)); return 1ULL; }
unsigned long long f91013(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4) { kq_hw_cmp(a0, a1, a2, a3, a4, KQ_V(0)); return 1ULL; }
unsigned long long f91014(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3) { kq_hw_call(a0, a1, a2, a3, KQ_V(0)); return 1ULL; }
unsigned long long f91015(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4, unsigned long long a5, unsigned long long a6, unsigned long long a7, unsigned long long a8, unsigned long long a9) { kq_hw_run(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, KQ_V(0)); return 1ULL; }
unsigned long long f91016(unsigned long long a0, unsigned long long a1) { kq_hw_code_sync(a0, a1, KQ_V(0)); return 1ULL; }
unsigned long long f91017(unsigned long long a0, unsigned long long a1) { kq_hw_irq_take(a0, a1, KQ_V(0)); return 1ULL; }
unsigned long long f91100(unsigned long long a) { return kq_hw_addr(a); }
unsigned long long f91101(unsigned long long a) { return kq_hw_irq_info(a); }
unsigned long long f91102(unsigned long long a) { return kq_hw_irq_entry(a); }
unsigned long long f91103(unsigned long long a) { return kq_hw_cpu_code(a); }
unsigned long long f91104(unsigned long long a) { return kq_hw_sym(a); }
unsigned long long f91018(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4) { kq_hw_user(a0, a1, a2, a3, a4, KQ_V(0)); return 1ULL; }
unsigned long long f91105(unsigned long long a0, unsigned long long a1, unsigned long long a2, unsigned long long a3, unsigned long long a4) { return kq_hw_userf(a0, a1, a2, a3, a4); }
"""

# growing a block (KQRun.v kq_grow): the kit's kq_grow may move the block, so the tables of the theorem are filled again
HW_GROW = r"""
unsigned long long f91019(unsigned long long a0, unsigned long long a1) {
  kq_grow(a0, a1, KQ_V(0));
  for (int h = 0; h < KQ_MAXB; h++) { f90000[h] = (unsigned long long *) kq_b[h].p; f90001[h] = kq_b[h].lim; }
  kq_hw_wlo = (uintptr_t) -1; kq_hw_whi = 0;
  for (int h = 0; h < KQ_MAXB; h++) if (kq_b[h].lim) { uintptr_t p = (uintptr_t) kq_b[h].p, e = p + 4 * (uintptr_t) kq_b[h].lim;
    if (p < kq_hw_wlo) kq_hw_wlo = p; if (e > kq_hw_whi) kq_hw_whi = e; }
  return 1ULL; }
"""

def ext_dispatch(extfile):
    """the program's own routines (hw/User.v): the C dispatchers kq_hw_user / kq_hw_userf over hw/NAME.ext, one line per
    routine: NUMBER CNAME ARGUMENTS KIND (KIND: mem or pure)"""
    mem, pure, decl = [], [], []
    if extfile and os.path.exists(extfile):
        for line in open(extfile):
            line = line.split("#")[0].split()
            if not line:
                continue
            k, cname, n, kind = int(line[0]), line[1], int(line[2]), line[3]
            decl.append(f"extern value {cname}();")
            xs = ", ".join(["a", "b", "c", "d"][:n])
            if kind == "mem":
                mem.append(f"    case {k}: return {cname}({xs + ', ' if xs else ''}s);")
            else:
                pure.append(f"    case {k}: return {cname}({xs});")
    return ("\n".join(decl) + "\n"
            "static inline value kq_hw_user(value k, value a, value b, value c, value d, value s) {\n"
            "  switch (KQ_N(k)) {\n" + "\n".join(mem) + "\n    default: return s; } }\n"
            "static inline value kq_hw_userf(value k, value a, value b, value c, value d) {\n"
            "  switch (KQ_N(k)) {\n" + "\n".join(pure) + "\n    default: return KQ_V(0); } }\n")

def driver(name, entry_id, kinds, res, args, wrap, uses_hw=False, bare=False, prefix="", entry_name="body", secondary=False, ext=None, slots=False):
    # the entry's parameters, in order, from what `main` passes
    vals = [a for a in args if a[0] != "M"]
    ks = [k for k in kinds if k != "M"]
    assert len(vals) == len(ks), (vals, ks)
    cargs = []
    for k, a in zip(ks, vals):
        if a[0] == "L":
            cargs.append(f"(unsigned long long) ((2L * {a[1]}L) | 1L)")
        elif a[0] == "NE":
            cargs.append(f"natW({a[1]})")
        elif a[0] == "IE":
            cargs.append(f"intW({a[1]})")
        elif k == "N":
            cargs.append(f"argN({a[1]})")
        else:
            cargs.append(f"argI({a[1]})")
    call = f"{prefix}f{entry_id}({', '.join(cargs)})"
    # a program with a function that gives back two numbers or a record: block 63 (at least 8 cells) carries the numbers after
    # the first back to the caller
    slotinit = (f"  static value kq_slot_cells[{2 * slots}]; if (!kq_b[63].p) {{ for (int j = 0; j < {2 * slots}; j++) kq_slot_cells[j] = KQ_V(0);\n"
                f"    kq_b[63].p = kq_slot_cells; kq_b[63].len = {slots}; kq_b[63].lim = {2 * slots}; }}\n") if slots else ""
    ret = "return kq_sum(KQ_V(0));" if res == "M" else "return (value) r;"
    hwdef = ("/* ---- the machine's operations: the kit's C bodies (hw/kq_hw.h) behind the external functions of the theorem */\n"
             + ("" if bare else "#include <sys/mman.h>\nuintptr_t kq_hw_wlo, kq_hw_whi;\n") + ext_dispatch(ext) + HW_WRAPPERS + ("" if bare else HW_GROW)) if (uses_hw and not secondary) else ""
    hwset = "" if (bare or secondary) else ("  kq_hw_wlo = (uintptr_t) -1; kq_hw_whi = 0;\n"
             "  for (int h = 0; h < KQ_MAXB; h++) if (kq_b[h].lim) { uintptr_t p = (uintptr_t) kq_b[h].p, e = p + 4 * (uintptr_t) kq_b[h].lim;\n"
             "    if (p < kq_hw_wlo) kq_hw_wlo = p; if (e > kq_hw_whi) kq_hw_whi = e; }\n"
             "  /* a hosted test: a page of memory at 0x10000000 stands for a device */\n"
             "  mmap((void *) 0x10000000, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);\n") if uses_hw else ""
    if secondary:
        return f"""
/* ---- a second program of the same kernel: it shares the tables and the machine's functions of the first */
extern value kq_arg(value);
value {entry_name}(struct thread_info *ti) {{
  unsigned long long r = {call};
  return (value) r;
}}
"""
    return f"""
/* ---- the driver: the loader's blocks into the tables of the theorem, the entry called, its answer returned */
unsigned long long *f90000[64];
unsigned int f90001[64];
int *f90002[64];
unsigned int f90003[64];
extern value kq_arg(value);
extern value kq_sum(value);
static unsigned long long argN(long k) {{ long n = KQ_N(kq_arg(KQ_V(k))); return (unsigned long long) KQ_V(n > 0 ? n : 0L); }}
#define A(k) ((unsigned long long) KQ_N(kq_arg(KQ_V(k))))
static unsigned long long natW(unsigned long long r) {{ long n = ((long) (r << 1)) >> 1; return (unsigned long long) KQ_V(n > 0 ? n : 0L); }}
static unsigned long long intW(unsigned long long r) {{ return (r << 1) | 1ULL; }}
static unsigned long long argI(long k) {{ return (unsigned long long) kq_arg(KQ_V(k)); }}
{hwdef}
value {entry_name}(struct thread_info *ti) {{
{slotinit}  for (int h = 0; h < KQ_MAXB; h++) {{ f90000[h] = (unsigned long long *) kq_b[h].p; f90001[h] = kq_b[h].lim; f90002[h] = kq_n[h].p; f90003[h] = kq_n[h].lim; }}
{hwset}  unsigned long long r = {call};
  (void) r;
  {ret}
}}
"""

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT, **kw)

def reflect(name, entry, prog, no_proof):
    """--reflect: the verified compiler (proved/KQR.v, Rocq-C-solution.md §1.12).  The reifier reads the entry `main`
    applies and every function it reaches (proved/KQRReify.v); each function is compiled by KQR.compile_f, and gets its
    statement from KQR.compile_f_ok -- proved once -- with the theorems of the functions before it as its callee
    assumption: one [exact_no_check] per function, which the kernel checks at Qed (the meaning of the syntax tree against
    the user's function, by conversion).  No tactic, no search.  -> (eid, kinds, res, n, slots) or None (not read: the caller
    takes the translator)"""
    # a program that shares blocks with another processor (step 18): a plain access to a narrow block names an unshared block
    # by a written number (the translator's rule, §9.4) -- KQR.sh_ok, worked out here on the trees read and proved by the
    # kernel beside each function's theorem
    shared = bool(re.search(r"Definition\s+kq_shared\b", prog))
    f0 = os.path.join(GEN, f"{name}_r.v")
    open(f0, "w").write(HDR + "From KQC Require KQR KQRReify.\n" + prog
        + f"\nDefinition {name}_res := ltac:(run_template_program (tmQuoteRec {entry})\n"
        + "  (fun q => let r := eval vm_compute in (KQRReify.reify_prog2 q, KQRReify.reify_why q, KQRReify.rec_info q) in exact r)).\n"
        + f"Definition {name}_src := option_map fst (fst (fst {name}_res)).\n"
        + f"Definition {name}_mts := match fst (fst {name}_res) with Some x => snd x | None => [] end.\n"
        + f'Redirect "{name}_rinfo" Eval vm_compute in (option_map KQRReify.info_of {name}_src).\n'
        + f'Redirect "{name}_rwhy" Eval vm_compute in (snd (fst {name}_res)).\n'
        + f'Redirect "{name}_rrec" Eval vm_compute in (snd {name}_res).\n'
        + (f'Redirect "{name}_rsh" Eval vm_compute in (match {name}_src with Some l => map (fun f => (snd (fst (fst f)), '
           f'KQR.sh_ok kq_shared (snd f))) l | None => [] end).\n' if shared else "")
        # a copy of a recursive function for the functions it is given: its meaning, the function applied to them (step 10)
        + f"MetaRocq Run (monad_iter (fun p => tmMkDefinition (fst p) (snd p)) {name}_mts).\n")
    rc, out = coqc(f0)
    info = open(os.path.join(GEN, f"{name}_rinfo.out")).read() if rc == 0 and os.path.exists(os.path.join(GEN, f"{name}_rinfo.out")) else ""
    fs = re.findall(r'\("([^"]+)"(?:%bs)?,\s*(\d+)(?:%nat)?,\s*"([IBa-h]*)"(?:%bs)?,\s*(true|false),\s*(true|false),\s*(true|false),'
                    r'\s*"([a-hBP]?)"(?:%bs)?\)', info)
    if rc != 0 or not fs or "= None" in info:
        wp = os.path.join(GEN, f"{name}_rwhy.out")
        why = open(wp).read() if os.path.exists(wp) else ""
        rs = [f + ": " + ", ".join(re.findall(r'"([^"]*)"', r)) for f, r in re.findall(r'\("([^"]+)",\s*\[(.*?)\]\)', why, re.S)]
        print(name, "reflect: not read by the verified compiler's reifier (" + ("; ".join(rs) if rs else "the reifier did not run")
              + "); the translator follows", flush=True)
        return None
    if shared:
        shp = os.path.join(GEN, f"{name}_rsh.out")
        bad = re.findall(r'\("([^"]+)"(?:%bs)?,\s*false\)', open(shp).read()) if os.path.exists(shp) else ["(not worked out)"]
        if bad:
            print(name, "reflect: not read by the verified compiler's reifier (" + "; ".join(
                  f + ": a block that another processor can change is read or written by a plain access, or its number is not written"
                  " where it is used" for f in bad) + "); the translator follows", flush=True)
            return None
    # the kinds of the parameters after the counters: I a number, B a boolean, a .. h a record of the program's type 0 .. 7
    kc = lambda c: "KQR.KNum" if c == "I" else "KQR.KBool" if c == "B" else f"(KQR.KRec {ord(c) - ord('a')})"
    kl = lambda f: "[" + "; ".join(kc(c) for c in f[2]) + "]"
    # the result: a record of the program's type 0 .. 7 (a .. h), a boolean (B, step 24), a number and a memory (P, step 26),
    # or none
    rq = lambda f: ("None" if f[6] == "" else "(Some KQR.KBool)" if f[6] == "B" else "(Some KQR.KNum)" if f[6] == "P"
                    else f"(Some (KQR.KRec {ord(f[6]) - ord('a')}))")
    sig = lambda f: f"(KQR.mksig {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)})"
    t = HDR + "From KQC Require KQR KQRReify.\nImport ListNotations.\n" + f"From KQG Require Import {name}_r.\n"
    # the program's record types (step 12): each its type, its constructor and match, a value of it; the laws by a fixed script
    rp = os.path.join(GEN, f"{name}_rrec.out")
    # each entry: its type, its constructor (a data type's: its constructors), its number of fields, a data type's widths
    recs = re.findall(r'\("([^"]*)"(?:%bs)?,\s*"([^"]*)"(?:%bs)?,\s*(\d+)(?:%nat)?,\s*"([^"]*)"(?:%bs)?\)', open(rp).read()) if os.path.exists(rp) else []
    if recs:
        inst, laws = f"{name}_recs", f"{name}_laws"
        pat = lambda j: "S (" * j + "O" + ")" * j
        t_rt = " | ".join(f"{pat(j)} => {ty}" for j, (ty, cn, n, wd) in enumerate(recs))
        t += f"Definition {name}_rt (i : nat) : Type := match i with {t_rt} | _ => unit end.\n"
        def ro(cn, n, wd):
            n = int(n); xs = [f"x{q}" for q in range(n)]
            if not wd.strip():
                mk = f"(fun l => {cn} " + " ".join(f"(nth {q}%nat l 0%uint63)" for q in range(n)) + ")" if n else f"(fun _ => {cn})"
                lst = "".join(f"(cons {x} " for x in xs) + "nil" + ")" * n
                return f"KQR.mkrops {n}%nat None {mk} (fun P v k => match v with {cn} {' '.join(xs)} => k {lst} end)"
            # a data type held as its tag and its fields (step 28): the constructor chosen by the tag, the fields after it
            cns, ws = cn.split(), [int(w) for w in wd.split()]
            app = lambda c, w: f"({c}" + "".join(f" (nth {q + 1}%nat l 0%uint63)" for q in range(w)) + ")"
            mk = app(cns[-1], ws[-1])
            for c in reversed(range(len(cns) - 1)):
                mk = f"(if PrimInt63.eqb (nth 0%nat l 0%uint63) {c}%uint63 then {app(cns[c], ws[c])} else {mk})"
            def arm(c):
                ys = [f"y{q}" for q in range(ws[c])]
                vals = [f"{c}%uint63"] + ys + ["0%uint63"] * (n - 1 - ws[c])
                return f"{cns[c]} {' '.join(ys)} => k " + "".join(f"(cons {v} " for v in vals) + "nil" + ")" * len(vals)
            wl = "[" + "; ".join(map(str, ws)) + "]%nat"
            return (f"KQR.mkrops {n}%nat (Some {wl}) (fun l => {mk}) (fun P v k => match v with "
                    + " | ".join(arm(c) for c in range(len(cns))) + " end)")
        def rd0(cn, n, wd):
            if not wd.strip(): return f"{cn}" + "".join(" 0%uint63" for _ in range(int(n)))
            return f"{cn.split()[0]}" + "".join(" 0%uint63" for _ in range(int(wd.split()[0])))
        t_ro = " | ".join(f"{pat(j)} => {ro(cn, n, wd)}" for j, (ty, cn, n, wd) in enumerate(recs))
        t += (f"Definition {name}_ro (i : nat) : KQR.rops ({name}_rt i) :=\n  match i as i0 return KQR.rops ({name}_rt i0) with {t_ro}\n"
              f"  | _ => KQR.mkrops 0%nat None (fun _ => tt) (fun P _ k => k nil) end.\n")
        t_rd = " | ".join(f"{pat(j)} => {rd0(cn, n, wd)}" for j, (ty, cn, n, wd) in enumerate(recs))
        t += f"Definition {name}_rd (i : nat) : {name}_rt i := match i as i0 return {name}_rt i0 with {t_rd} | _ => tt end.\n"
        t += f"#[local] Instance {inst} : KQR.RecTypes | 0 := {{| KQR.RT := {name}_rt; KQR.RO := {name}_ro; KQR.Rd := {name}_rd |}}.\n"
        dpat = "".join("[|" for _ in range(len(recs))) + "i" + "]" * len(recs)
        t += (f"#[local] Instance {laws} : @KQR.RecLaws {inst}.\nProof. split.\n"
              f"- intros i x P k. destruct i as {dpat}; destruct x; reflexivity.\n"
              f"- intros i x. destruct i as {dpat}; destruct x; reflexivity.\n"
              f"- intros i l E L. destruct i as {dpat}; cbn in E, L; try discriminate E; repeat (destruct l as [|? l]; try discriminate L); reflexivity.\n"
              f"- intros i ws c rest E Lc Lr Hz. destruct i as {dpat}; cbn in E; try discriminate E; injection E as <-; KQR.kq_tag_case.\nQed.\n")
    else:
        inst, laws = "KQR.no_recs", "KQR.no_recs_laws"
    t += f"Definition {name}_funs := match {name}_src with Some l => l | None => [] end.\n"
    t += f"Definition {name}_prog := KQL.mkprog (@KQRReify.funs_of {inst} 0 {name}_funs) [].\n"
    # the program's functions are unfolded last when the kernel compares a function with the meaning of its syntax tree: a
    # function applied to a written counter (f 20 ..) would otherwise be worked out round by round (F50).  The order of
    # unfolding only: nothing that converts stops converting
    tmpls = sorted({f[0].split("__c")[0] for f in fs if "__c" in f[0]})   # the templates the copies come from (step 10)
    t += "Strategy opaque [" + " ".join([f[0] for f in fs if "__c" not in f[0]] + tmpls) + "].\n"   # a copy is unfolded first
    if not no_proof:
        for j, f in enumerate(fs):
            cs = "[" + "; ".join(f"existT (@KQR.ftype {inst}) {sig(g)} {g[0]}" for g in fs[:j]) + "]"
            oks = "".join(f"(conj {name}_rok{i} " for i in range(j)) + "Logic.I" + ")" * j
            t += f"Lemma {name}_rok{j} : @KQR.callee_ok {inst} {name}_prog (KQR.gid1 {j}) (KQR.cbz {j}) {sig(f)} {f[0]}.\n"
            if "__c" in f[0]:
                # a copy: not a fix over its counter, so its statement comes from its two equations, each by conversion
                # (a copy that writes the memory and gives back a number has a memory: no memory argument)
                thm, p0, p1, mm = (("compile_f_okrm", "KQR.fm0", "KQR.fm1", f" {f[3]}") if f[4] == "true" else
                                   ("compile_f_okrx", "KQR.fx0", "KQR.fx1", "") if f[5] == "true" else
                                   ("compile_f_okr", "KQR.fr0", "KQR.fr1", f" {f[3]}"))
                b = f"(KQRReify.body_at {name}_funs {j})"
                t += (f"Proof. exact_no_check (@KQR.{thm} {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {int(f[1]) - 1} {kl(f)}{mm} ({p0} {b}) ({p1} {b})"
                      f" {f[0]} eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl eq_refl"
                      f" (fun n => eq_refl)). Qed.\n")
            else:
                t += (f"Proof. exact_no_check (@KQR.compile_f_ok {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {sig(f)} (KQRReify.body_at {name}_funs {j})"
                      f" eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl). Qed.\n")
            if shared:
                # the sequential meaning describes the program only if it reaches its shared blocks through marked operations
                t += f"Lemma {name}_rsh{j} : KQR.sh_ok kq_shared (KQRReify.body_at {name}_funs {j}) = true.\nProof. exact eq_refl. Qed.\n"
    t += c_print(name)
    f1 = os.path.join(GEN, f"{name}_rp.v")
    open(f1, "w").write(t)
    rc, out = coqc(f1)
    if rc != 0:
        print(name, "REFLECT CHECK FAILED (the translator follows):", out[-400:].replace("\n", " "), flush=True)
        return None
    idx = [f[0] for f in fs].index(entry) if entry in [f[0] for f in fs] else len(fs) - 1
    e = fs[idx]
    if any(c not in "IB" for c in e[2]) or e[6] not in ("", "B"):   # an entry taking or giving back a record: main gives and takes numbers
        print(name, "reflect: the entry takes or gives back a record; the translator follows", flush=True)
        return None
    kinds = "N" * int(e[1]) + "I" * len(e[2]) + ("M" if e[3] == "true" else "")   # a boolean is passed as a number, 1 or 0
    # the slot block: room for the fields after the first of each record type of the program ([KQR.slot_room], which every
    # theorem of the program takes; the driver provides it, as for the translator's two results)
    slots = max([int(n) for (_, _, n, _) in recs] + [1]) - 1
    return 1000 + idx, kinds, "M" if e[4] == "true" else "I", len(fs), slots

def main():
    build = True
    bare = False
    secondary = False
    prefix = ""
    entry_name = "body"
    ext = None
    names = []
    # --emit-first: the C is printed and built right after the translation (it is a function of the KQL program alone), the
    # proofs run after it; --no-proof: the C without the proofs (with --no-build: only the translation, a check of what is read)
    emit_first = False
    no_proof = False
    reflect_mode = bool(os.environ.get("KQ_REFLECT"))   # KQ_REFLECT=1: as --reflect (for the scripts that call kitc.py)
    for a in sys.argv[1:]:
        if a == "--reflect":
            reflect_mode = True
        elif a == "--emit-first":
            emit_first = True
        elif a == "--no-proof":
            no_proof = True
        elif a == "--no-build":
            build = False
        elif a == "--bare":
            build = False; bare = True
        elif a == "--secondary":
            secondary = True
        elif a.startswith("--prefix="):
            prefix = a[len("--prefix="):]
        elif a.startswith("--entry="):
            entry_name = a[len("--entry="):]
        elif a.startswith("--ext="):
            ext = a[len("--ext="):]
        else:
            names.append(a)
    for src in names:
        path = src if src.endswith(".body") else f"hand/{src}.body"
        name = re.sub(r"[^A-Za-z0-9_]", "_", os.path.basename(path)[:-5])
        body = open(path).read()
        # a program that names a function of a library of lib/ gets the library's text in front of it, as compile.sh does
        for pre, lib, mark in (("slab_", "Slab", "SLAB"), ("view_", "View", "VIEW"), ("(?:loop_|wfix)", "Loop", "LOOP")):
            if re.search(r"\b" + pre, body) and f"(* {mark}-BEGIN *)" not in body:
                lt = open(os.path.join(ROOT, "lib", lib + ".v")).read()
                body = lt[lt.index(f"(* {mark}-BEGIN *)") + len(f"(* {mark}-BEGIN *)"):lt.index(f"(* {mark}-END *)")] + "\n" + body
        prog, mt = split_main(body)
        try:
            entry, args, wrap = parse_main(mt)
        except SystemExit as ex:
            print(name, "NOT READ:", ex); continue
        if reflect_mode:
            r = reflect(name, entry, prog, no_proof)
            if r:
                eid, kinds, res, n, slots = r
                print(name, ("NOT PROVED (proofs skipped)" if no_proof else "PROVED"), n, "functions by the verified compiler; entry",
                      entry, "id", eid, kinds, "->", res, flush=True)
                write_c(name, eid, kinds, res, args, wrap, bare, prefix, entry_name, secondary, ext, [], slots)
                if build:
                    build_bin(name, bare)
                continue
        # 1: translate
        f0 = os.path.join(GEN, f"{name}_t.v")
        open(f0, "w").write(HDR + prog + f'\nMetaRocq Run ({translate_cmd(prog, entry, name)}).\n')
        rc, out = coqc(f0)
        m = re.search(r"KQM: \d+ functions: ([\w' ]+)", out)
        if not m:
            print(name, "TRANSLATION FAILED:", out[-300:].replace("\n", " ")); continue
        fns = m.group(1).split()
        mh = re.search(r"KQM helpers:([^\n]*)", out)
        helpers = mh.group(1).split() if mh else []
        me = re.search(r"KQM entry: (\w+) (\d+) (\w*) (\w)", out)
        _, eid, kinds, res = me.groups()
        mpf = re.search(r"KQM pairfns:([^\n]*)", out)
        pairfns = mpf.group(1).split() if mpf else []

        def emit():
            # the C, from the KQL program alone, with its driver; then the build
            fc = os.path.join(GEN, f"{name}_c.v")
            open(fc, "w").write(HDR + f"From KQG Require Import {name}_t.\n" + c_print(name))
            rc, out = coqc(fc)
            if rc != 0:
                print(name, "C NOT PRINTED:", out[-400:].replace("\n", " "), flush=True); return False
            write_c(name, eid, kinds, res, args, wrap, bare, prefix, entry_name, secondary, ext, pairfns)
            return (not build) or build_bin(name, bare)

        if emit_first or no_proof:
            if not emit():
                continue
            if no_proof:
                print(name, "NOT PROVED (proofs skipped)", len(fns), "functions; entry", entry, "id", eid, kinds, "->", res, flush=True)
                continue
            print(name, "C printed" + (" and built" if build else "") + "; the proofs follow", flush=True)
        # 2: prove, and print the C
        f1 = os.path.join(GEN, f"{name}_p.v")
        groups = [g.split() for g in re.findall(r"KQM group: ([\w' ]+)", out)]
        unproved = []
        if os.environ.get("KQ_MONO"):
            t = proof_file(name, prog, entry, fns, helpers, groups, pairfns)
        else:
            up = prove_units(name, fns, helpers, groups, pairfns, int(os.environ.get("KQ_JOBS", "3")), bool(os.environ.get("KQ_STRICT")))
            if up is None:
                continue
            unproved = up
            t = HDR + f"From KQG Require Import {name}_t.\n"
            if emit_first:
                # the C is already printed and built; the proofs were checked unit by unit
                print(name, ("UNPROVED " + " ".join(unproved) + " of") if unproved else "PROVED", len(fns), "functions"
                      + (" (the rest proved)" if unproved else "") + "; entry", entry, "id", eid, kinds, "->", res)
                continue
        t += c_print(name)
        # a lemma the kernel does not finish (KQ_TIMEOUT) is left unproved (Admitted): the C is still made and is
        # checked by tests only; the program is then reported as unproved
        while True:
            open(f1, "w").write(t)
            rc, out = coqc(f1)
            if rc == 0:
                break
            if not os.environ.get("KQ_MONO"):
                print(name, "PROOF FAILED:", out[-400:].replace("\n", " ")); break
            ml = re.search(r'File "[^"]*", line (\d+)', out)
            lines = t.split("\n")
            ln = int(ml.group(1)) - 1 if ml else -1
            if not ml:
                # the process died without a message (memory): the commands it finished say where it was
                rc2, out2 = coqc(f1, ["-time"])
                ends = [int(x) for x in re.findall(r"Chars \d+ - (\d+)", out2)]
                if ends:
                    pos, ln = 0, -1
                    for i, l in enumerate(t.split("\n")):
                        if pos + len(l.encode()) + 1 > ends[-1]:
                            ln = i; break
                        pos += len(l.encode()) + 1
            mm = re.match(r"Lemma (\w+)_ok : (\w+_kstmt)\.", lines[ln]) if 0 <= ln < len(lines) else None
            if not mm or os.environ.get("KQ_STRICT"):
                print(name, "PROOF FAILED:", out[-400:].replace("\n", " ")); break
            unproved.append(mm.group(1))
            lines[ln] = f"Lemma {mm.group(1)}_ok : {mm.group(2)}. Proof. Admitted."
            t = "\n".join(lines)
        if rc != 0:
            continue
        if unproved:
            print(name, "UNPROVED", " ".join(unproved), "of", len(fns), "functions (the rest proved); entry", entry, "id", eid, kinds, "->", res)
        else:
            print(name, "PROVED", len(fns), "functions; entry", entry, "id", eid, kinds, "->", res)
        if emit_first:
            # (KQ_MONO) the proofs checked together; the C is already printed and built
            continue
        # 3: the C
        write_c(name, eid, kinds, res, args, wrap, bare, prefix, entry_name, secondary, ext, pairfns)
        if not build:
            continue
        # 4: build, as the kit builds its programs
        build_bin(name, bare)

def c_print(name):
    """the command that prints the C of a translated program (from its KQL alone) into NAME_c.out"""
    return (f'\nFrom Stdlib Require Import String.\nLocal Open Scope string_scope.\n'
            f'Redirect "{name}_c" Eval vm_compute in (KQLPrint.pstr 77777%positive (KQMTop.tr_kit_program {name}_prog)).\n')

def write_c(name, eid, kinds, res, args, wrap, bare, prefix, entry_name, secondary, ext, pairfns, slots=0):
    """NAME_c.out -> the C file with its driver"""
    raw = open(os.path.join(GEN, f"{name}_c.out")).read()
    c = raw[raw.index('"') + 1: raw.rindex('"')].replace('""', '"')
    cfile = os.path.join(GEN, f"{name}_bare.c" if bare else f"{name}_proved.c")
    uses_hw = re.search(r"\bf91[01]\d\d\b", c) is not None
    if prefix:
        c = re.sub(r"\bf(1\d{3})\b", prefix + r"f\1", c)
    open(cfile, "w").write('#include "gc_stack.h"\n#include "kq_io.h"\n' + ('#include "kq_hw.h"\n' if uses_hw else "") + c
                           + driver(name, eid, kinds, res, args, wrap, uses_hw, bare, prefix, entry_name, secondary, ext,
                                    max(8, slots) if slots else (8 if pairfns else 0)))

def build_bin(name, bare):
    """build bin/P_NAME as the kit builds its programs"""
    cfile = os.path.join(GEN, f"{name}_bare.c" if bare else f"{name}_proved.c")
    rt = glob.glob(os.path.expanduser("~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime"))[0]
    os.makedirs("bld/user", exist_ok=True); os.makedirs("bin", exist_ok=True)
    for f in glob.glob("sup/v4/*.h") + glob.glob("sup/v4/*.c") + ["hw/kq_hw.h"]:
        run(["cp", f, "bld/user/"])
    cf = ["-w", "-O2", "-flto", "-fomit-frame-pointer", "-Ibld/user", f"-I{rt}", "-I."]
    r = run(["clang", *cf, "-o", f"bin/P_{name}", "bld/user/kq_io3.c", cfile, f"{rt}/gc_stack.c", "bld/user/kq_prim63.c"])
    print(name, "built bin/P_" + name if r.returncode == 0 else "BUILD FAILED: " + r.stderr[-400:], flush=True)
    return r.returncode == 0

if __name__ == "__main__":
    main()
