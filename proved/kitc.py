#!/usr/bin/env python3
"""kitc.py [--no-build] [--walk] NAME...   (inside the image, in the repo's directory)

A kit program (hand/NAME.body, or a path to a .body file) through the proved route: the verified compiler (see reflect():
the reifier reads each function into the syntax of proved/KQR.v, compile_f_ok gives its theorem, the kernel checks by
conversion that the tree means the function); a program it does not read is refused with the reifier's reasons.  With --walk
(or KQ_WALK=1) the retired route instead, kept as the yardstick a moved program is timed against (Rocq-C-solution.md, F49):
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

# the directory of a program whose text requires files beside it (step 51): those files are libraries of its directory
USER = []
USER_FILES = []   # those files: each its path and the prefix of its names
LOADED = []       # the files it loads, whose text is read in place

def coqc(path, extra=()):
    r = subprocess.run(["coqc", "-w", "-all", "-R", ROOT, "KQ", "-Q", os.path.join(ROOT, "proved"), "KQC", "-Q", GEN, "KQG", *USER, *extra, path],
                       capture_output=True, text=True, cwd=GEN)
    return r.returncode, r.stdout + r.stderr

def required(text):
    """the files a text requires, as paths under its directory: `Require [Import|Export] a b.`, `From d Require ..`"""
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    out = []
    for m in re.finditer(r"(?:\bFrom\s+([\w.']+)\s+)?\bRequire\s+(?:Import\s+|Export\s+)?([^.]*(?:\.[\w'][^.]*)*)\.(?:\s|$)", text):
        for w in m.group(2).split():
            out.append(((m.group(1) + "." if m.group(1) else "") + w).replace(".", "/"))
    return out

def loaded(text):
    """the files a text loads: `Load a.`, its text read in place"""
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    return [m.group(1).replace(".", "/") for m in re.finditer(r"\bLoad\s+(?:Verbose\s+)?([\w'./]+)\.(?:\s|$)", text)]

def user_files(text, d, seen, order):
    """the program's other files (step 51): each file a text requires that stands in its directory, those it requires first"""
    for p in required(text):
        f = os.path.join(d, p + ".v")
        if p not in seen and os.path.exists(f):
            seen.add(p)
            user_files(open(f).read(), d, seen, order)
            order.append(f)
    for p in loaded(text):
        f = os.path.join(d, p + ".v")
        if ("L", p) not in seen and os.path.exists(f):
            seen.add(("L", p))
            LOADED.append(f)
            user_files(open(f).read(), d, seen, order)

def build_user_files(body, path):
    """-> None, or Rocq's error for a file of the program that does not compile"""
    d = os.path.dirname(os.path.abspath(path))
    fs = []
    LOADED[:] = []
    user_files(body, d, set(), fs)
    USER[:] = ["-Q", d, ""] if fs or LOADED else []
    USER_FILES[:] = [(f, os.path.relpath(f, d)[:-2].replace(os.sep, ".") + ".") for f in fs] + [(f, "") for f in LOADED]
    kit = os.path.join(ROOT, "KQRun.vo")
    newest = os.path.getmtime(kit) if os.path.exists(kit) else 0
    for f in fs:
        vo = f + "o"
        newest = max(newest, os.path.getmtime(f))
        if not os.path.exists(vo) or os.path.getmtime(vo) < newest:
            rc, out = coqc(f)
            if rc != 0:
                return out
        newest = max(newest, os.path.getmtime(vo))
    return None

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

def last_def(prog):
    """the name of the last function of a file"""
    ns = re.findall(r"(?m)^\s*(?:#\[[^\]]*\]\s*)?(?:Program\s+)?(?:Definition|Fixpoint|Function|Equations|Let)\s+([A-Za-z_][\w']*)", prog)
    if not ns:
        raise SystemExit("no function in the file")
    return ns[-1]

def sig_args(name, prog, entry):
    """an entry read from its signature: -> (args, wrap), or None and the reason: a number or a boolean from the command line, a
    counter from the command line, the memory from the memory file; a number given back is printed, a memory given back summed"""
    f0 = os.path.join(GEN, f"{name}_sig.v")
    open(f0, "w").write(HDR + prog + f"\nSet Printing Width 100000.\nCheck {entry}.\n")
    rc, out = coqc(f0)
    if rc != 0:
        m = re.search(r"Error:\s*(.*?)(?:\n\n|$)", out, re.S)
        return None, "Rocq refused the file: " + (" ".join(m.group(1).split())[:200] if m else "it did not compile")
    ms = re.findall(r"(?m)^\s+:\s*(.+)$", out)
    if not ms:
        return None, "the type of " + entry + " was not read"
    ty = ms[-1].strip()
    if "forall" in ty or "(" in ty:
        return None, f"{entry} : {ty}: the entry takes numbers, counters, booleans and a memory, and gives back a number or a memory"
    parts = [p.strip() for p in ty.split("->")]
    args, k = [], 0
    for p in parts[:-1]:
        if p == "nat":
            args.append(("N", k)); k += 1
        elif p in ("int", "bool"):
            args.append(("I", k)); k += 1
        elif p == "mem":
            args.append(("M",))
        else:
            return None, f"{entry} : {ty}: the entry takes numbers, counters, booleans and a memory; {p} is not one"
    if parts[-1] in ("int", "bool"):
        return (args, "int"), None
    if parts[-1] == "mem":
        return (args, "sum"), None
    return None, f"{entry} : {ty}: the entry gives back a number or a memory; {parts[-1]} is not one"

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

def driver(name, entry_id, kinds, res, args, wrap, uses_hw=False, bare=False, prefix="", entry_name="body", secondary=False, ext=None, grows=False, slots=False):
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
             + ("" if bare else "#include <sys/mman.h>\nuintptr_t kq_hw_wlo, kq_hw_whi;\n") + ext_dispatch(ext) + HW_WRAPPERS + ("" if bare and not grows else HW_GROW)) if (uses_hw and not secondary) else ""
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

# what follows a program the verified compiler does not take: a refusal, or with --walk the retired route
FOLLOW = "; refused"

def shared_term(prog):
    """the list of blocks a program shares with another processor, `kq_shared`: its name, wherever it stands in the program's text
    and its files, in a module or not (step 51).  A program with none has no shared block; one it does not find here would go
    unchecked, so this looks wherever the program's text is"""
    for text, pre in [(prog, "")] + [(open(f).read(), n) for f, n in USER_FILES]:
        text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
        m = re.search(r"Definition\s+kq_shared\b", text)
        if m:
            mods = []
            for t in re.finditer(r"\bModule\s+([\w']+)\s*(?:<?:\s*[\w'.]+\s*)?\.(?:\s|$)|\bEnd\s+([\w']+)\s*\.", text[:m.start()]):
                if t.group(1):
                    mods.append(t.group(1))
                elif mods and mods[-1] == t.group(2):
                    mods.pop()
            return pre + "".join(x + "." for x in mods) + "kq_shared"
    return None

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
    shared = shared_term(prog)
    f0 = os.path.join(GEN, f"{name}_r.v")
    # (step 119) the time limit the walk's files have: a reading or a proof that does not end stops there, not the run
    tlim = f"Set Default Timeout {os.environ.get('KQ_TIMEOUT', '300')}.\n"
    open(f0, "w").write(HDR + "From KQC Require KQR KQRReify.\n" + tlim + prog
        + f"\nDefinition {name}_res := ltac:(let k q := (let r := eval vm_compute in (let r0 := KQRReify.reify_prog2 q in (r0, KQRReify.reify_why q, KQRReify.rec_info2 q r0, KQRReify.entry_perm q, KQRReify.fix1_info q, KQRReify.pf_info_r q r0)) in exact r) in\n"
        + f"  run_template_program (tmQuoteRecTransp {entry} false)\n"
        + "  (fun q0 => let b := eval vm_compute in (KQRReify.has_function q0) in\n"
        + "   match b with\n"
        + "   | false => k q0\n"
        + "   | true => run_template_program (KQRReify.quote_function q0) (fun q => k q)\n"
        + "   end)).\n"
        + f"Definition {name}_src := ltac:(let r := eval vm_compute in (option_map fst (fst (fst (fst (fst (fst {name}_res)))))) in exact r).\n"
        + f"Definition {name}_mts := match fst (fst (fst (fst (fst {name}_res)))) with Some x => snd x | None => [] end.\n"
        # a copy of a recursive function for the functions it is given: its meaning, the function applied to them (step 10)
        + f"MetaRocq Run (monad_iter KQRReify.mk_made (KQRReify.plain_mts {name}_mts)).\n")
    # (step 77) what the reader found, as Rocq prints it, read below: a notation of the program's or a scope it opens would print it otherwise; then in a file of its own
    q = f"KQG.{name}_r." if re.search(r"\b(Notation|Infix|Open Scope|Bind Scope|Declare Scope)\b", prog) else ""
    prt = (f'Redirect "{name}_rinfo" Eval vm_compute in (option_map KQRReify.info_of {q}{name}_src).\n'
        + f'Redirect "{name}_rwhy" Eval vm_compute in (snd (fst (fst (fst (fst {q}{name}_res))))).\n'
        + f'Redirect "{name}_rrec" Eval vm_compute in (snd (fst (fst (fst {q}{name}_res)))).\n'
        + f'Redirect "{name}_rperm" Eval vm_compute in (snd (fst (fst {q}{name}_res))).\n'
        + f'Redirect "{name}_rfix" Eval vm_compute in (snd (fst {q}{name}_res)).\n'
        + f'Redirect "{name}_rpf" Eval vm_compute in (snd {q}{name}_res).\n'
        + f'Redirect "{name}_rmts" Eval vm_compute in (KQRReify.mts_info {q}{name}_mts).\n'
        + (f'Redirect "{name}_rsh" Eval vm_compute in (match {q}{name}_src with Some l => map (fun f => (snd (fst (fst f)), '
           f'KQR.sh_ok {shared} (snd f))) l | None => [] end).\n' if shared else ""))
    if q:
        rc, out = coqc(f0)
        if rc == 0:
            f0b = os.path.join(GEN, f"{name}_ro.v")
            open(f0b, "w").write(HDR + "From KQC Require KQR KQRReify.\n" + f"From KQG Require {name}_r.\n" + prt)
            rc, out = coqc(f0b)
    else:
        open(f0, "a").write(prt)
        rc, out = coqc(f0)
    info = open(os.path.join(GEN, f"{name}_rinfo.out")).read() if rc == 0 and os.path.exists(os.path.join(GEN, f"{name}_rinfo.out")) else ""
    # each function: its name, counters, kinds, flags, result, bound and weights (polynomials, step 39: read to the tuple's end)
    head = re.compile(r'\("([^"]+)"(?:%bs)?,\s*(\d+)(?:%nat)?,\s*"([IBa-hp]*)"(?:%bs)?,\s*(true|false),\s*(true|false),\s*(true|false),'
                      r'\s*"([a-hBP]?)"(?:%bs)?,\s*(?:None|Some\s*\(?(\d+)(?:%Z)?\)?),\s*')
    fs = []
    for mh in head.finditer(info):
        i0 = j0 = mh.end(); d = 0
        while j0 < len(info) and not (info[j0] in ')]' and d == 0):
            d += 1 if info[j0] in '([' else -1 if info[j0] in ')]' else 0
            j0 += 1
        fs.append(mh.groups(default="") + (info[i0:j0].strip(),))
    if rc != 0:
        # the file did not compile: the program is not Rocq (Rocq's own error, the first of them), or the reifier failed
        m = re.search(r"Error:\s*(.*?)(?:\n\n|$)", out, re.S)
        err = " ".join(m.group(1).split())[:200] if m else "the reifier did not run"
        print(name, "reflect: not read by the verified compiler's reifier (Rocq refused the file: " + err + ")" + FOLLOW, flush=True)
        return None
    if not fs or "= None" in info:
        wp = os.path.join(GEN, f"{name}_rwhy.out")
        why = open(wp).read() if os.path.exists(wp) else ""
        rs = [f + ": " + ", ".join(re.findall(r'"([^"]*)"', r)) for f, r in re.findall(r'\("([^"]+)",\s*\[(.*?)\]\)', why, re.S)]
        print(name, "reflect: not read by the verified compiler's reifier (" + ("; ".join(rs) if rs else "the reifier did not run")
              + ")" + FOLLOW, flush=True)
        return None
    if shared:
        shp = os.path.join(GEN, f"{name}_rsh.out")
        bad = re.findall(r'\("([^"]+)"(?:%bs)?,\s*false\)', open(shp).read()) if os.path.exists(shp) else ["(not worked out)"]
        if bad:
            print(name, "reflect: not read by the verified compiler's reifier (" + "; ".join(
                  f + ": a block that another processor can change is read or written by a plain access, or its number is not written"
                  " where it is used" for f in bad) + ")" + FOLLOW, flush=True)
            return None
    # the kinds of the parameters after the counters: I a number, B a boolean, a .. h a record of the program's type 0 .. 7
    kc = lambda c: "KQR.KNum" if c == "I" else "KQR.KBool" if c == "B" else f"(KQR.KRec {ord(c) - ord('a')})"
    kl = lambda f: "[" + "; ".join(kc(c) for c in f[2] if c != "p") + "]"
    # the last number and the memory one parameter, a pair (step 44): "p" after the kinds
    isp = lambda f: f[2].endswith("p")
    # (step 93) a kit function for the library's recursive functions on counters: the pair flag without a memory, which only it has
    iskit = lambda f: isp(f) and f[3] == "false"
    kitop = lambda f: "KQR.LGcd" if f[0].endswith("kq_gcdg") else "KQR.LSqrt" if f[0].endswith("kq_sqrtg") else "KQR.LLog2"
    # the result: a record of the program's type 0 .. 7 (a .. h), a boolean (B, step 24), a number and a memory (P, step 26),
    # or none
    rq = lambda f: ("None" if f[6] == "" else "(Some KQR.KBool)" if f[6] == "B" else "(Some KQR.KNum)" if f[6] == "P"
                    else f"(Some (KQR.KRec {ord(f[6]) - ord('a')}))")
    # the weights of a function whose recursion grows counters (steps 37 to 39): polynomials, each below its bound at the counters
    ws = lambda f: "(" + " ".join(f[8].replace("%nat", "").split()) + ")%nat"
    bo = lambda f: "None" if not f[7] else f"(Some {f[7]}%Z)"
    wsl = lambda f: ws(f) if re.search(r"\d", f[8]) else "nil"
    sigc = lambda f: f"(KQR.mksig9 {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)} {bo(f)} {wsl(f)} false)"
    sig = lambda f: (f"(KQR.mksig9 {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)} {bo(f)} {wsl(f)} true)" if isp(f)
                     else f"(KQR.mksig8 {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)} {bo(f)} {ws(f)})" if re.search(r"\d", f[8])
                     else f"(KQR.mksig {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)})" if not f[7]
                     else f"(KQR.mksig7 {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)} (Some {f[7]}%Z))")
    bnd = lambda f, j: f"(KQR.cbz {j})" if not f[7] else f"{f[7]}%Z"
    # (step 56) a Program Fixpoint: its name, the constant holding its Fix_sub, its parameters, its made functions' stem, a measure on a machine number
    fp = os.path.join(GEN, f"{name}_rpf.out")
    pfs = {m[0]: m for m in re.findall(r'\("([^"]*)"(?:%bs)?,\s*"([^"]*)"(?:%bs)?,\s*(\d+)(?:%nat)?,\s*"([^"]*)"(?:%bs)?,\s*"([^"]*)"(?:%bs)?,\s*"([^"]*)"(?:%bs)?,\s*(\d+)(?:%nat)?\)', open(fp).read())} if os.path.exists(fp) else {}
    # (step 60) a fixpoint whose match on its counter gives a function: not a measure's, its theorem a copy's
    cv = {k for k, m in pfs.items() if m[5] == "c"}
    pfs = {k: m for k, m in pfs.items() if m[5] != "c"}
    t = HDR + f"Set Default Timeout {os.environ.get('KQ_TIMEOUT', '300')}.\n" + "From KQC Require KQR KQRReify KQREnd" + (" KQRWf" if pfs or (os.path.exists(os.path.join(GEN, f"{name}_rmts.out")) and "__wy" in open(os.path.join(GEN, f"{name}_rmts.out")).read()) else "") + ".\nImport ListNotations.\n" + ("From Stdlib Require Import FunInd.\n" if any(m[5] == "f" for m in pfs.values()) else "") + f"From KQG Require Import {name}_r.\n"
    # the program's record types (step 12): each its type, its constructor and match, a value of it; the laws by a fixed script
    rp = os.path.join(GEN, f"{name}_rrec.out")
    # each entry: its type, its constructor (a data type's: its constructors), its number of fields, a data type's widths
    recs = re.findall(r'\("([^"]*)"(?:%bs)?,\s*"([^"]*)"(?:%bs)?,\s*(\d+)(?:%nat)?,\s*"([^"]*)"(?:%bs)?\)', open(rp).read()) if os.path.exists(rp) else []
    if recs:
        inst, laws = f"{name}_recs", f"{name}_laws"
        pat = lambda j: "S (" * j + "O" + ")" * j
        t_rt = " | ".join(f"{pat(j)} => {ty}" for j, (ty, cn, n, wd) in enumerate(recs))
        t += f"Definition {name}_rt (i : nat) : Type := match i with {t_rt} | _ => unit end.\n"
        def shape(sh):
            # a record holding records (step 32): "pair(pair(i,i),i)" -> ("pair", ["i", ...]), a field "i" or an inner record
            pos = [0]
            def node():
                j = sh.index("(", pos[0]); cn = sh[pos[0]:j]; pos[0] = j + 1; fs = []
                while True:
                    if sh[pos[0]] == "i" and sh[pos[0] + 1] in ",)": fs.append("i"); pos[0] += 1
                    else: fs.append(node())
                    c = sh[pos[0]]; pos[0] += 1
                    if c == ")": return (cn, fs)
            return node()
        def width(nd): return sum(1 if f == "i" else width(f) for f in nd[1])
        def lst(vs): return "".join(f"(cons {v} " for v in vs) + "nil" + ")" * len(vs)
        def nested_ro(sh, n):
            root = shape(sh)
            def build(nd, start):   # the outer numbers first, then each inner record's fields, depth first
                cn, fs = nd; k = start + sum(1 for f in fs if f == "i"); q = start; parts = []
                for f in fs:
                    if f == "i": parts.append(f"(nth {q}%nat l 0%uint63)"); q += 1
                    else: parts.append(build(f, k)); k += width(f)
                return f"({cn} " + " ".join(parts) + ")"
            cnt = [0]
            def elim(nd, var):      # the matches nest for nest, in the fields' order, depth first
                cn, fs = nd; vs = []
                for _ in fs: cnt[0] += 1; vs.append(f"v{cnt[0]}")
                o, c, leaves = f"match {var} with {cn} {' '.join(vs)} => ", " end", [v for v, f in zip(vs, fs) if f == "i"]
                for v, f in zip(vs, fs):
                    if f != "i":
                        o2, c2, l2 = elim(f, v); o += o2; c = c2 + c; leaves += l2
                return o, c, leaves
            o, c, leaves = elim(root, "v")
            return f"KQR.mkrops {n}%nat None (fun l => {build(root, 0)}) (fun P v k => {o}k {lst(leaves)}{c})"
        # (step 67) the kinds of a value not free as numbers: "B:" a boolean, "G:i,3" a record, each field a number or an index in the
        # table, "T:N;J;x..|x.." a data type: N number slots, the record slots' types, each constructor's fields' slots
        def kind(j): return recs[j][3][:2] if recs[j][3][:2] in ("B:", "G:", "T:") else ""
        def cn_of(j): return recs[j][1]
        def gfs(wd): return [f for f in wd[2:].split(",") if f]
        def tfs(wd):
            n_, j_, cs = wd[2:].split(";")
            return int(n_), [int(x) for x in j_.split(",") if x], [[(f[0], int(f[1:])) for f in c[1:].split(",") if f] for c in cs.split("|")]
        def rd_new(j):
            ty, cn, n, wd = recs[j]
            if wd.startswith("B:"): return "false"
            if wd.startswith("G:"): return f"({cn} " + " ".join("0%uint63" if f == "i" else rd_new(int(f)) for f in gfs(wd)) + ")"
            if wd.startswith("T:"):
                _, J, ms = tfs(wd)
                return "(" + cn.split()[0] + "".join(" 0%uint63" if a == "n" else " " + rd_new(J[q]) for a, q in ms[0]) + ")"
            return "(" + rd0(cn, n, wd) + ")"
        def flats(pairs, end):
            # the numbers of records one after the other, then [end] of those lists
            ls = [f"l{q}" for q in range(len(pairs))]
            e = end("".join(f"(List.app {x} " for x in ls) + "nil" + ")" * len(ls))
            for (v, jj), x in reversed(list(zip(pairs, ls))): e = f"{rl_txt(jj)} _ {v} (fun {x} => {e})"
            return e
        def rl_txt(j):
            ty, cn, n, wd = recs[j]
            head = f"(fun (P : Type) (v : {ty}) (k : list PrimInt63.int -> P) => "
            if wd.startswith("B:"): return head + "k (cons (KQR.b2i v) nil))"
            if wd.startswith("G:"):
                fs = gfs(wd); vs = [f"v{j}_{q}" for q in range(len(fs))]
                nums = lst([v for v, f in zip(vs, fs) if f == "i"])
                return head + f"match v with {cn} {' '.join(vs)} => " + flats([(v, int(f)) for v, f in zip(vs, fs) if f != "i"], lambda c: f"k (List.app {nums} {c})") + " end)"
            if wd.startswith("T:"):
                N, J, ms = tfs(wd); arms = []
                for c, (cc, m) in enumerate(zip(cn.split(), ms)):
                    ys = [f"y{j}_{q}" for q in range(len(m))]
                    nums = lst([f"{c}%uint63"] + [next((y for y, a in zip(ys, m) if a == ("n", q)), "0%uint63") for q in range(N)])
                    prs = [(next((y for y, a in zip(ys, m) if a == ("r", q)), rd_new(jj)), jj) for q, jj in enumerate(J)]
                    arms.append(f"{cc} {' '.join(ys)} => " + flats(prs, lambda e: f"k (List.app {nums} {e})"))
                return head + "match v with " + " | ".join(arms) + " end)"
            return head + f"KQR.relim ({ro(cn, n, wd)}) v k)"
        def ro_new(j):
            ty, cn, n, wd = recs[j]
            if wd.startswith("B:"): tg = "(Some nil)"
            elif wd.startswith("G:"): tg = "None"
            else: tg = "(Some [" + "; ".join(str(sum(1 for a, _ in m if a == "n")) for m in tfs(wd)[2]) + "]%nat)"
            return f"KQR.mkrops {n}%nat {tg} (fun _ => {rd_new(j)}) (fun P v k => {rl_txt(j)} P v k)"
        def nested_rd(sh):
            def rd(nd): return f"({nd[0]} " + " ".join("0%uint63" if f == "i" else rd(f) for f in nd[1]) + ")"
            return rd(shape(sh))
        def ro(cn, n, wd, rty=""):
            if wd.startswith("N:"): return nested_ro(wd[2:].split("@")[0], int(n))
            n = int(n); xs = [f"x{q}" for q in range(n)]
            if not wd.strip():
                # (step 84) a record over a type: its constructor takes the type
                mt = re.match(r"\((\S+) (.*)\)$", rty) if rty else None
                ce = f"@{cn} {mt.group(2)}" if mt else cn
                mk = f"(fun l => {ce} " + " ".join(f"(nth {q}%nat l 0%uint63)" for q in range(n)) + ")" if n else f"(fun _ => {ce})"
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
        def rd0(cn, n, wd, rty=""):
            if wd.startswith("N:"): return nested_rd(wd[2:].split("@")[0])
            mt = re.match(r"\((\S+) (.*)\)$", rty) if rty else None
            if not wd.strip(): return (f"@{cn} {mt.group(2)}" if mt else f"{cn}") + "".join(" 0%uint63" for _ in range(int(n)))
            return f"{cn.split()[0]}" + "".join(" 0%uint63" for _ in range(int(wd.split()[0])))
        t_ro = " | ".join(f"{pat(j)} => {ro_new(j) if kind(j) else ro(cn, n, wd, ty)}" for j, (ty, cn, n, wd) in enumerate(recs))
        t += (f"Definition {name}_ro (i : nat) : KQR.rops ({name}_rt i) :=\n  match i as i0 return KQR.rops ({name}_rt i0) with {t_ro}\n"
              f"  | _ => KQR.mkrops 0%nat None (fun _ => tt) (fun P _ k => k nil) end.\n")
        t_rd = " | ".join(f"{pat(j)} => {rd_new(j) if kind(j) else rd0(cn, n, wd, ty)}" for j, (ty, cn, n, wd) in enumerate(recs))
        t += f"Definition {name}_rd (i : nat) : {name}_rt i := match i as i0 return {name}_rt i0 with {t_rd} | _ => tt end.\n"
        # the one-level match and constructor (step 43): a record holding records gives its number fields and its record fields
        # (each with its type), and is built from them; another record type: its match and its constructor
        def nest(wd):
            sh, _, js = wd[2:].partition("@")
            return shape(sh), [int(x) for x in js.split(",") if x]
        def rs_of(j, wd):
            cn = cn_of(j)
            if wd.startswith("B:"): return "fun P v k => k (cons (KQR.b2i v) nil) nil"
            if wd.startswith("G:"):
                fs = gfs(wd); vs = [f"v{q}" for q in range(len(fs))]
                rl = [(v, int(f)) for v, f in zip(vs, fs) if f != "i"]
                rls = "".join(f"(cons (existT {name}_rt {jj}%nat {v}) " for v, jj in rl) + "nil" + ")" * len(rl)
                return f"fun P v k => match v with {cn} {' '.join(vs)} => k {lst([v for v, f in zip(vs, fs) if f == 'i'])} {rls} end"
            if wd.startswith("T:"):
                N, J, ms = tfs(wd); arms = []
                for c, (cc, m) in enumerate(zip(cn.split(), ms)):
                    ys = [f"y{q}" for q in range(len(m))]
                    nums = lst([f"{c}%uint63"] + [next((y for y, a in zip(ys, m) if a == ("n", q)), "0%uint63") for q in range(N)])
                    prs = [(next((y for y, a in zip(ys, m) if a == ("r", q)), f"({name}_rd {jj}%nat)"), jj) for q, jj in enumerate(J)]
                    rls = "".join(f"(cons (existT {name}_rt {jj}%nat {v}) " for v, jj in prs) + "nil" + ")" * len(prs)
                    arms.append(f"{cc} {' '.join(ys)} => k {nums} {rls}")
                return "fun P v k => match v with " + " | ".join(arms) + " end"
            if wd.startswith("N:"):
                (cn0, fs), jl = nest(wd)
                vs = [f"v{q}" for q in range(len(fs))]
                recs = [v for v, f in zip(vs, fs) if f != "i"]
                rl = "".join(f"(cons (existT {name}_rt {jj}%nat {v}) " for v, jj in zip(recs, jl)) + "nil" + ")" * len(recs)
                return f"fun P v k => match v with {cn0} {' '.join(vs)} => k {lst([v for v, f in zip(vs, fs) if f == 'i'])} {rl} end"
            return f"fun P v k => KQR.relim ({name}_ro ({pat(j)})) v (fun l => k l nil)"
        def rb_of(j, wd):
            cn = recs[j][1]
            def rf(jj, r): return f"(KQR.tk {name}_rd {jj}%nat (nth {r}%nat rs (existT {name}_rt {jj}%nat ({name}_rd {jj}%nat))))"
            if wd.startswith("B:"): return "fun _ _ => false"
            if wd.startswith("G:"):
                parts, q, r = [], 0, 0
                for f in gfs(wd):
                    if f == "i": parts.append(f"(nth {q}%nat l 0%uint63)"); q += 1
                    else: parts.append(rf(int(f), r)); r += 1
                return f"fun l rs => ({cn} {' '.join(parts)})"
            if wd.startswith("T:"):
                N, J, ms = tfs(wd); cns = cn.split()
                app = lambda c: "(" + cns[c] + "".join(f" (nth {q + 1}%nat l 0%uint63)" if a == "n" else " " + rf(J[q], q) for a, q in ms[c]) + ")"
                mk = app(len(cns) - 1)
                for c in reversed(range(len(cns) - 1)):
                    mk = f"(if PrimInt63.eqb (nth 0%nat l 0%uint63) {c}%uint63 then {app(c)} else {mk})"
                return f"fun l rs => {mk}"
            if wd.startswith("N:"):
                (cn0, fs), jl = nest(wd)
                parts, q, r = [], 0, 0
                for f in fs:
                    if f == "i": parts.append(f"(nth {q}%nat l 0%uint63)"); q += 1
                    else:
                        jj = jl[r]; r += 1
                        parts.append(f"(KQR.tk {name}_rd {jj}%nat (nth {r - 1}%nat rs (existT {name}_rt {jj}%nat ({name}_rd {jj}%nat))))")
                return f"fun l rs => ({cn0} {' '.join(parts)})"
            return f"fun l _ => KQR.rmk ({name}_ro ({pat(j)})) l"
        def rj_of(wd):
            if wd.startswith("G:"): return "(" + "".join(f"cons {f}%nat (" for f in gfs(wd) if f != "i") + "nil" + ")" * (len([f for f in gfs(wd) if f != "i"]) + 1)
            if wd.startswith("T:"): return "(" + "".join(f"cons {jj}%nat (" for jj in tfs(wd)[1]) + "nil" + ")" * (len(tfs(wd)[1]) + 1)
            if wd.startswith("B:"): return "nil"
            return ("(" + "".join(f"cons {jj}%nat (" for jj in nest(wd)[1]) + "nil" + ")" * (len(nest(wd)[1]) + 1)) if wd.startswith("N:") else "nil"
        t_rs = " | ".join(f"{pat(j)} => {rs_of(j, wd)}" for j, (ty, cn, n, wd) in enumerate(recs))
        t_rb = " | ".join(f"{pat(j)} => {rb_of(j, wd)}" for j, (ty, cn, n, wd) in enumerate(recs))
        t_rj = " | ".join(f"{pat(j)} => {rj_of(wd)}" for j, (ty, cn, n, wd) in enumerate(recs))
        t += (f"Definition {name}_rs (i : nat) : forall P : Type, {name}_rt i -> (list PrimInt63.int -> list (sigT {name}_rt) -> P) -> P :=\n"
              f"  match i as i0 return forall P : Type, {name}_rt i0 -> (list PrimInt63.int -> list (sigT {name}_rt) -> P) -> P with {t_rs}\n"
              f"  | _ => fun P _ k => k nil nil end.\n")
        t += (f"Definition {name}_rb (i : nat) : list PrimInt63.int -> list (sigT {name}_rt) -> {name}_rt i :=\n"
              f"  match i as i0 return list PrimInt63.int -> list (sigT {name}_rt) -> {name}_rt i0 with {t_rb}\n"
              f"  | _ => fun _ _ => tt end.\n")
        t += f"Definition {name}_rj (i : nat) : list nat := match i with {t_rj} | _ => nil end.\n"
        # (step 67) which type is bool, which value's numbers are not free, a constructor's own record slots
        jb = [j for j in range(len(recs)) if recs[j][3].startswith("B:")]
        t_rbl = " | ".join(f"{pat(j)} => " + ("fun b => b" if j in jb else f"fun _ => {name}_rd {j}%nat") for j in range(len(recs)))
        t += (f"Definition {name}_rbl (i : nat) : bool -> {name}_rt i := match i as i0 return bool -> {name}_rt i0 with {t_rbl} | _ => fun _ => tt end.\n")
        t_rtb = " | ".join(f"{pat(j)} => " + ("fun v => v" if j in jb else "fun _ => false") for j in range(len(recs)))
        t += (f"Definition {name}_rtb (i : nat) : {name}_rt i -> bool := match i as i0 return {name}_rt i0 -> bool with {t_rtb} | _ => fun _ => false end.\n")
        t_rbi = "".join(f"{pat(j)} => true | " for j in jb)
        t_rnc = "".join(f"{pat(j)} => true | " for j in range(len(recs)) if kind(j))
        t += (f"Definition {name}_rbi (i : nat) : bool := match i with {t_rbi}_ => false end.\n"
              f"Definition {name}_rnc (i : nat) : bool := match i with {t_rnc}_ => false end.\n")
        def rm_of(wd):
            _, J, ms = tfs(wd)
            bl = lambda m: "(" + "".join(("cons true (" if any(a == ("r", q) for a in m) else "cons false (") for q in range(len(J))) + "nil" + ")" * (len(J) + 1)
            return "".join(f"cons {bl(m)} (" for m in ms) + "nil" + ")" * len(ms)
        t_rm = "".join(f"{pat(j)} => nth c ({rm_of(recs[j][3])}) nil | " for j in range(len(recs)) if recs[j][3].startswith("T:"))
        t += f"Definition {name}_rm (i c : nat) : list bool := match i with {t_rm}_ => nil end.\n"
        t += (f"#[local] Instance {inst} : KQR.RecTypes | 0 := {{| KQR.RT := {name}_rt; KQR.RO := {name}_ro; KQR.Rd := {name}_rd;\n"
              f"  KQR.RS := {name}_rs; KQR.RB := {name}_rb; KQR.RJ := {name}_rj; KQR.RBl := {name}_rbl; KQR.RTb := {name}_rtb;\n"
              f"  KQR.RBI := {name}_rbi; KQR.RNC := {name}_rnc; KQR.RM := {name}_rm |}}.\n")
        dpat = "".join("[|" for _ in range(len(recs))) + "i" + "]" * len(recs)
        t += (f"#[local] Instance {laws} : @KQR.RecLaws {inst}.\nProof. split.\n"
              f"- intros i x P k. destruct i as {dpat}; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].\n"
              f"- intros i x. destruct i as {dpat}; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].\n"
              f"- intros i l E L N. destruct i as {dpat}; cbn in E, L, N; try discriminate E; try discriminate N; repeat (destruct l as [|? l]; try discriminate L); reflexivity.\n"
              f"- intros i ws c rest E Lc Lr Hz N. destruct i as {dpat}; cbn in E, N; try discriminate E; try discriminate N; injection E as <-; KQR.kq_tag_case.\n"
              f"- intros i x P k. destruct i as {dpat}; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].\n"
              f"- intros i x. destruct i as {dpat}; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].\n"
              f"- intros i x. destruct i as {dpat}; destruct x; first [reflexivity | cbn; repeat match goal with |- context [match ?v with _ => _ end] => destruct v end; reflexivity].\n"
              f"- intros i l rs G Hk Hl. destruct i as {dpat}; cbn in G, Hk; try discriminate G; KQR.kq_rb_case.\n"
              f"- intros i ws c rest rs E Lc Hk Hl Hz Ho. destruct i as {dpat}; cbn in E; try discriminate E; injection E as <-; KQR.kq_rbt_case.\n"
              f"- intros i b E. destruct i as {dpat}; cbn in E; try discriminate E; reflexivity.\n"
              f"- intros i x E. destruct i as {dpat}; cbn in E; try discriminate E; reflexivity.\nQed.\n")
    else:
        inst, laws = "KQR.no_recs", "KQR.no_recs_laws"
    # a mutual block's meaning (step 45): blkT at the program's record types
    t += f"MetaRocq Run (monad_iter (fun p => tmMkDefinition (fst p) (snd p)) (KQRReify.blk_mts <% @{inst} %> {name}_mts)).\n"
    t += f"Definition {name}_funs := match {name}_src with Some l => l | None => [] end.\n"
    t += f"Definition {name}_prog := KQL.mkprog (@KQRReify.funs_of {inst} 0 {name}_funs) [].\n"
    # the program's functions are unfolded last when the kernel compares a function with the meaning of its syntax tree: a
    # function applied to a written counter (f 20 ..) would otherwise be worked out round by round (F50).  The order of
    # unfolding only: nothing that converts stops converting
    # the templates the copies come from (step 10); a local fixpoint's copy (kqlfix__cK, step 31) has no template constant
    # what the reifier made: each its name and the constant it is a copy or a wrapper of (step 51)
    mp = os.path.join(GEN, f"{name}_rmts.out")
    mts = re.findall(r'\(\s*"([^"]*)"(?:%bs)?,\s*"([^"]*)"(?:%bs)?\)', open(mp).read()) if os.path.exists(mp) else []
    made = {m for m, _ in mts}
    iscp = lambda nm: nm in made and re.search(r"__c(\d+|blk)$", nm) is not None   # a copy, a block
    isw = lambda nm: nm in made and nm.endswith("__o")                              # a wrapper of a function that recurses (step 41)
    iswr = lambda nm: iscp(nm) or (nm in made and re.search(r"__on?$", nm) is not None)   # a copy, or a wrapper (step 41)
    tmpls = sorted({h for m, h in mts if h and re.search(r"__c\d+$|__on?$", m)})
    # the functions that are one fixpoint, not a member of a block (step 51)
    xp = os.path.join(GEN, f"{name}_rfix.out")
    fix1 = set(re.findall(r'"([^"]*)"', open(xp).read())) if os.path.exists(xp) else set()
    fix1 |= {m for m in made if m.endswith("__rp__wy") and not m.endswith("__n__rp__wy")}   # (step 69) a fixpoint in another's place
    # (step 56) a Program Fixpoint equal to its budget function's call at every argument (KQRWf.fix_sub_budget), before anything is made opaque
    # (step 59) a copy, for the functions it is given, of a function that is one call of a budget function
    pfc = {m: h for m, h in mts if h in pfs and iscp(m)}
    reqs = {}
    for j, pf0 in enumerate(pfs):
        if True:
            f = (pf0,)
            reqs[pf0] = f"{name}_rq{j}"
            _, func, np, stem, tag, sp, ph = pfs[f[0]]
            np, ph = int(np), int(ph)
            W, D, WM, WN = stem + "__w", stem + "__wd", stem + "__wm", stem + "__wn"
            Gs = [stem + ("" if q == 0 else f"_{q}") + "__wg" for q in range(ph)]
            G = Gs[-1]
            ps = [f"kqp{q}" for q in range(np)]
            ss = " ".join(ps)
            def proj(r, q):
                u = r
                for _ in range(q): u = f"(projT2 {u})"
                return u if np == 1 else (f"(projT1 {u})" if q < np - 1 else u)
            unp = lambda r: " ".join(proj(r, q) for q in range(np))
            pack = ps[-1]
            for q in reversed(ps[:-1]): pack = f"(existT _ {q} {pack})"
            xs = [f"kqx{q}" for q in range(np)]
            pat = xs[-1]
            for q in reversed(xs[:-1]): pat = f"[{q} {pat}]"
            # the bound of the measure: a machine number's, the measure itself, or arithmetic (step 58)
            bound = {"m": "exact (KQRWf.to_nat_le_budget _)", "c": "exact (le_n _)", "l": f"KQRWf.bound_of ({WN} {ss}); unfold {WN}; KQRWf.bound_le"}[tag]
            K = "KQRWf.kq_budget"
            # the budget a phase's lemma holds above: the budgets of those before, and one more each
            Kp = [K]
            for q in range(1, ph): Kp.append(f"({K} + S {Kp[-1]})")
            if sp == "d":
                # (step 61) a budget function above a fixpoint with its own call on a deeper counter
                # (step 62) a member of a mixed block: the others unfolded as the tests take the counter apart
                mem = "cbn [" + " ".join(func.split()) + "]" if func.strip() else "idtac"
                t += (f"Lemma {reqs[pf0]} : forall {ss}, {W} {ss} = {f[0]} {ss}.\n"
                      f"Proof.\n  assert (kqA : forall kqk {ss} (kqh : {WM} {ss} <= kqk), {G} kqk {ss} = {f[0]} {ss}).\n"
                      f"  {{ induction kqk as [|kqk IH]; intros {ss} kqh; unfold {WM} in *; cbn [{G}]; destruct {ps[0]}; cbn [{f[0]}]; KQRWf.deep_step IH ltac:({mem}). }}\n"
                      f"  intros {ss}. unfold {W}. apply kqA. unfold {WM}. exact (le_n _).\nQed.\n")
                continue
            if sp == "e":
                # (step 60) Equations: FixWf, its functional's clauses unfolded
                def unpe(r):
                    parts, u = [], r
                    for q in range(np - 1):
                        parts.append(f"(Equations.Init.pr1 {u})"); u = f"(Equations.Init.pr2 {u})"
                    return " ".join(parts + [u])
                cl = " ".join(func.split())
                stp = lambda g: f"intros [|k'] {pat} h H; cbv beta zeta; cbn [{g} {D}] in *; cbv delta [{cl}] beta iota zeta; KQRWf.eq_step ltac:(cbn [Equations.Init.pr1 Equations.Init.pr2])"
                t += (f"Transparent {f[0]} {cl}.\nLemma {reqs[pf0]} : forall {ss}, {W} {ss} = {f[0]} {ss}.\n"
                      f"Proof.\n  intros {ss}. symmetry. unfold {W}, {f[0]}, Equations.Prop.Subterm.FixWf, Corelib.Init.Wf.Fix.\n")
                if ph == 1:
                    t += (f"  refine (@KQRWf.fix_wf_budget_F _ _ _ (fun r => {WM} {unpe('r')}) (fun _ _ H => H) _ (fun k r => {G} k {unpe('r')}) (fun r => {D} {unpe('r')}) _ _ _ _ _).\n"
                          f"  - {stp(G)}.\n"
                          f"  - cbv beta; cbn beta iota; {bound}.\nQed.\n")
                else:
                    t += "  match goal with |- @Corelib.Init.Wf.Fix_F ?A ?R (fun _ => ?B) ?F _ _ = _ =>\n"
                    for q in range(ph):
                        prev = f"(fun r => {D} {unpe('r')})" if q == 0 else f"(fun r => {Gs[q - 1]} {K} {unpe('r')})"
                        t += (f"    assert (kqS{q} : forall (k : nat) (x : A) (h : forall y : A, R y x -> B), (forall y r, h y r = (match k with O => {prev} | S k' => (fun k r => {Gs[q]} k {unpe('r')}) k' end) y) -> F x h = (fun k r => {Gs[q]} k {unpe('r')}) k x)\n"
                              f"      by ({stp(Gs[q])});\n")
                        if q == 0:
                            t += f"    pose proof (@KQRWf.fix_wf_budget_F A B R (fun r => {WM} {unpe('r')}) (fun _ _ H => H) F _ _ kqS0) as kqP0;\n"
                        else:
                            t += f"    pose proof (@KQRWf.fix_wf_phase_F A B R (fun r => {WM} {unpe('r')}) (fun _ _ H => H) F _ {Kp[q - 1]} (fun x r H => kqP{q - 1} x r {K} H) _ kqS{q}) as kqP{q};\n"
                    t += (f"    refine (kqP{ph - 1} _ _ {K} _); cbv beta; cbn beta iota; change ({WN} {ss} <= {K} + S {Kp[ph - 2]}); unfold {WN}; KQRWf.bound_le\n"
                          f"  end.\nQed.\n")
                continue
            if sp == "f":
                # (step 57) a Function: by its own induction principle, each call's measure below by its tcc lemma
                t += (f"Lemma {reqs[pf0]} : forall {ss}, {W} {ss} = {f[0]} {ss}.\n"
                      f"Proof.\n  assert (kqA0 : forall {ss} kqk (kqh : {WM} {ss} <= kqk), {Gs[0]} kqk {ss} = {f[0]} {ss}).\n"
                      f"  {{ intros {ss}. functional induction ({f[0]} {ss}); intros kqk kqh;\n"
                      f"    destruct kqk as [|kqk]; cbn [{Gs[0]}]; unfold {WM} in *; KQRWf.fn_branch {f[0]}_tcc. }}\n")
                for q in range(1, ph):
                    t += (f"  assert (kqA{q} : forall {ss} kqk (kqh : {WM} {ss} <= kqk + S {Kp[q - 1]}), {Gs[q]} kqk {ss} = {f[0]} {ss}).\n"
                          f"  {{ intros {ss}. functional induction ({f[0]} {ss}); intros kqk kqh;\n"
                          f"    destruct kqk as [|kqk]; cbn [{Gs[q]}]; unfold {WM} in *; KQRWf.fn_branch_ph {f[0]}_tcc {WM} kqA{q - 1}. }}\n")
                t += f"  intros {ss}. unfold {W}. apply kqA{ph - 1}. "
                t += (f"unfold {WM}. {bound}.\nQed.\n" if tag != "l" else
                      (f"{bound}.\nQed.\n" if ph == 1 else f"change ({WN} {ss} <= {K} + S {Kp[ph - 2]}); unfold {WN}; KQRWf.bound_le.\nQed.\n"))
                continue
            if ph == 1:
                t += (f"Lemma {reqs[pf0]} : forall {ss}, {W} {ss} = {f[0]} {ss}.\n"
                      f"Proof.\n  intros {ss}. symmetry. unfold {W}, {f[0]}{', ' + func if func else ''}.\n"
                      f"  refine (@KQRWf.fix_sub_budget _ _ _ _ _ (fun k r => {G} k {unp('r')}) (fun r => {D} {unp('r')}) _ _ {pack} _).\n"
                      f"  - intros [|k'] {pat} h H; cbv beta zeta; cbn [projT1 projT2 {G} {D}] in *; KQRWf.wf_step.\n"
                      f"  - cbv beta zeta; cbn [projT1 projT2]; {bound}.\nQed.\n")
                continue
            # (step 58) a budget in phases: each phase's lemma from the one before
            t += (f"Lemma {reqs[pf0]} : forall {ss}, {W} {ss} = {f[0]} {ss}.\n"
                  f"Proof.\n  intros {ss}. symmetry. unfold {W}, {f[0]}{', ' + func if func else ''}.\n"
                  f"  match goal with |- Corelib.Program.Wf.Fix_sub ?A (Corelib.Program.Wf.MR lt ?m) _ (fun _ => ?B) ?Fs _ = _ =>\n")
            for q in range(ph):
                prev = f"(fun r => {D} {unp('r')})" if q == 0 else f"(fun r => {Gs[q - 1]} {K} {unp('r')})"
                t += (f"    assert (kqS{q} : forall (k : nat) (x : A) (h : forall y : {{y : A | Corelib.Program.Wf.MR lt m y x}}, B), (forall y, h y = (match k with O => {prev} | S k' => (fun k r => {Gs[q]} k {unp('r')}) k' end) (proj1_sig y)) -> Fs x h = (fun k r => {Gs[q]} k {unp('r')}) k x)\n"
                      f"      by (intros [|k'] {pat} h H; cbv beta zeta; cbn [projT1 projT2 {Gs[q]} {D}] in *; KQRWf.wf_step);\n")
                if q == 0:
                    t += f"    pose proof (@KQRWf.fix_sub_budget_F A B m Fs _ _ kqS0) as kqP0;\n"
                else:
                    t += f"    pose proof (@KQRWf.fix_sub_phase_F A B m Fs _ {Kp[q - 1]} (fun x r H => kqP{q - 1} x r {K} H) _ kqS{q}) as kqP{q};\n"
            t += (f"    unfold Corelib.Program.Wf.Fix_sub; refine (kqP{ph - 1} _ _ {K} _); cbv beta zeta; cbn [projT1 projT2]; change ({WN} {ss} <= {K} + S {Kp[ph - 2]}); unfold {WN}; KQRWf.bound_le\n"
                  f"  end.\nQed.\n")
    # (step 61) a fixpoint read with a choice floated out of an operand: equal to the user's at each counter
    # (step 69) a function read in another form: equal at every argument to what is in its place, by induction, each one's lemma
    # among the rewrites of what follows
    rrs = [(m, h) for m, h in mts if m.endswith("__rq__wy")]
    rrn = []
    rrw = []
    # (step 85) what the proof of a class's program unfolds
    clu = [m[:-len("__clu__wy")].replace("''", "\0").replace("'_", ".").replace("\0", "'").split("kqcopy.")[-1] for m, _ in mts if m.endswith("__clu__wy")]
    if rrs or clu:
        t += "Ltac KQRWf.kq_unf ::= try unfold KQRReify.kq_sb2b; try unfold KQRReify.om_wrap; try unfold KQRReify.om_wrap0" + "".join(f"; try unfold {c}" for c in clu) + ".\n"
    # (step 72) what the tactic rewrites stays folded when the helpers are unfolded
    # (step 78) a value of several numbers and a memory given back by a recursion: through the slot block.  First, of each recursive function
    # that gives a memory, that it leaves the cells alone; the equations then hold where the block has room, the program's largest value
    kqunm = lambda x: x.replace("''", "\0").replace("'_", ".").replace("\0", "'")
    fqs = [m for m, _ in mts if m.endswith("__fq__wy")]
    # (step 79) a local fix is no constant: its lemma is stated of the fix itself
    kqfn = lambda x: "" if re.search(r"__l\d+(__v\d+)?$", x) else kqunm(x).split("kqcopy.")[-1]
    fqf = [(m, kqfn(re.match(r"(.*)__f\d+__fq__wy$", m).group(1)), int(re.search(r"__f(\d+)__fq__wy$", m).group(1))) for m in fqs]
    vmr = any(re.search(r"__v\d+__rq__wy$", m) for m, _ in rrs)
    qmr = any(re.search(r"__[qkm]\d+__rq__wy$|__kb\d+_\d+_\d+_.*__rq__wy$|__kv\d+__rq__wy$|__kva\d+_\d+__rq__wy$", m) for m, _ in rrs)
    rrw2 = []
    roomw = max([int(r[2]) for r in recs] + [1])
    roomR = f"({roomw} <= Sint63.to_Z (KQ.KQBound.kq_len 63) + 1)%Z" if roomw > 1 else "True"
    hrb = f"(Hr : {roomR}) " if vmr else ""
    keepf = " ".join(sorted({"KQ.KQRun.kq_nat"} | ({"Uint63.of_Z", "Z.of_nat", "Nat.add", "Nat.mul"} if any(re.search(r"__k\d+__rq__wy$|__kb\d+_\d+_\d+_.*__rq__wy$", m) for m, _ in rrs) else set()) | {x for m, h in rrs for x in (h, m[:-len("__rq__wy")] + "__rp__wy") if x} | {f[1] for f in fqf if f[1]} | {x for x in (kqfn(re.match(r"(.*)__[vqk]\d+__rq__wy$", m).group(1)) for m, _ in rrs if re.search(r"__[vqk]\d+__rq__wy$", m)) if x}
                            | {f[0] for f in fs if f[0] in fix1} | {f[0].rsplit(".", 1)[-1] + "__wy" for f in fs if f[0].rsplit(".", 1)[-1] + "__wy" in made}))
    if vmr:
        if roomw > 1:
            ri = [int(r[2]) for r in recs].index(roomw)
            t += (f"Lemma {name}_room : @KQR.slot_room {inst} -> {roomR}.\nProof. intros H. exact (H {ri}%nat (proj1 (PeanoNat.Nat.ltb_lt 1%nat {roomw}%nat) eq_refl)). Qed.\n")
        else:
            t += f"Lemma {name}_room : @KQR.slot_room {inst} -> {roomR}.\nProof. intros _. exact Logic.I. Qed.\n"
    if vmr or qmr:
        t += "Ltac KQRWf.kq_vm ::= KQRWf.kq_vm0.\n"
    for j, (m, fn, r) in enumerate(fqf):
        d0 = f"do {r} intro; " if r else ""
        cb0 = f"cbn [{fn}]" if fn else "cbn beta iota"
        t += (f"Lemma {name}_fq{j} : {m}.\nProof. unfold {m}. fix IH {r + 1}. {d0}intros kqn; destruct kqn as [|kqn]; intros; {cb0}; first [solve [KQRWf.fr_step IH] | solve [cbn; KQRWf.fr_step IH] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.fr_step IH]]. Qed.\n")
        t += "Ltac KQRWf.kq_fr ::= progress (rewrite " + ", ".join(f"?{name}_fq{i}" for i in range(j + 1)) + " by KQRWf.vm_side).\n"
    # (step 111) a block's rows (__kb<rarg>_<index>_<size>_<first member>): each member's statement, the counter first, proved by one
    # mutual fixpoint over the members' statements at a counter (__ra__wy), every hypothesis over every counter as a single row's
    kbre = re.compile(r"(.*)__kb(\d+)_(\d+)_(\d+)_(.*)__rq__wy$")
    kbg = {}
    for m0, _ in rrs:
        mk0 = kbre.match(m0)
        if mk0:
            kbg.setdefault(mk0.group(5), {})[int(mk0.group(3))] = (m0, mk0.group(1))
    for j, (m, h) in enumerate(rrs):
        mkb = kbre.match(m)
        if mkb:
            ktag, kib, kmb = mkb.group(5), int(mkb.group(3)), int(mkb.group(4))
            kgrp = kbg[ktag]
            if sorted(kgrp) != list(range(kmb)):
                sys.exit(f"{name}: a block's rows not all made ({ktag})")
            kats = [kgrp[i][0][:-len("__rq__wy")] + "__ra__wy" for i in range(kmb)]
            kfs = [kgrp[i][0][:-len("__rq__wy")] + "__rp__wy" for i in range(kmb)]
            khs = [kqfn(kgrp[i][1]) for i in range(kmb)]
            kunf = " ".join(x for x in khs + kfs if x)
            katl = ", ".join(kats)
            kwiths = " ".join("(IH%d (kqn : nat) {struct kqn} : %s kqn)" % (i, kats[i]) for i in range(kmb) if i != kib)
            krwt = "ltac:(rewrite " + ", ".join("<- ?IH%d" % i for i in range(kmb)) + ")"
            t += (f"Lemma {name}_rr{j} {hrb}: {m}.\n"
                  f"Proof. unfold {m}. fix IH{kib} 1 with {kwiths}. all: intros kqn; destruct kqn as [|kqn]; try unfold {katl} in *; intros; cbn [{kunf}]; "
                  f"first [solve [KQRWf.nr_stepT {krwt}] | solve [cbn; KQRWf.nr_stepT {krwt}] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.nr_stepT {krwt}]]. Qed.\n")
            rrn.append(f"{name}_rr{j}")
            rrw.append(f"match goal with Hr : {roomR} |- _ => rewrite <- ?({name}_rr{j} Hr) end" if vmr else f"rewrite <- ?{name}_rr{j}")
            t += "Ltac KQRWf.kq_rw ::= progress (" + "; ".join(rrw) + ").\n"
            continue
        F = m[:-len("__rq__wy")] + "__rp__wy"
        # (step 78) what is read through the slot block: its statement names the function by what follows the row
        h = kqfn(re.match(r"(.*)__(?:[vqkm]\d+|kv\d+|kva\d+_\d+)__rq__wy$", m).group(1)) if re.search(r"__(?:[vqkm]\d+|kv\d+|kva\d+_\d+)__rq__wy$", m) else h
        unf = " ".join(x for x in [h, F] if x)
        unfc = ", ".join(x for x in [h, F] if x)
        if m.endswith("__n__rq__wy"):
            # (step 76) a function giving back a proof: itself, by the name its row is made of
            of = m[:-len("__e__n__rq__wy")].replace("''", "\0").replace("'_", ".").replace("\0", "'") if m.endswith("__e__n__rq__wy") else ""
            unfc += f"; try unfold {of}" if of else ""
            t += (f"Lemma {name}_rr{j} {hrb}: {m}.\nProof. unfold {m}. intros; unfold {unfc}; first [solve [KQRWf.own_step0] | solve [cbn; KQRWf.own_step0] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.own_step0]]. Qed.\n")
        else:
            # (step 78) the counter of a function read through the slot block may stand anywhere
            mv = re.search(r"__(?:[vqgkm]|kv|kva)(\d+)(?:_\d+)?__rq__wy$", m)
            rv = int(mv.group(1)) if mv else 0
            d0 = f"do {rv} intro; " if rv else ""
            ost = "KQRWf.nr_step" if re.search(r"__k\d+__rq__wy$", m) else "KQRWf.nv_step" if re.search(r"__kv\d+__rq__wy$", m) else "KQRWf.own_step"
            # (step 121) a row taking accumulators at numbers: each of its calls paired with the function's call whose arguments made numbers
            # are its, the statement at those put in (KQRWf.nv_stepb); the same pairing rewrites the uses
            mva = re.search(r"__kva\d+_(\d+)__rq__wy$", m)
            if mva and h:
                na = int(mva.group(1))
                ys = " ".join(f"?kqy{q}" for q in range(na)); yv = " ".join(f"kqy{q}" for q in range(na))
                zs = " ".join(f"?kqz{q}" for q in range(na)); zv = " ".join(f"kqz{q}" for q in range(na))
                t += (f"Ltac {name}_kva{j} L := match goal with |- context [{h} {ys}] => match goal with |- context [{F} {zs}] => "
                      f"let E := constr:(L {yv}) in lazymatch type of E with ?FL = _ => replace ({F} {zv}) with FL by (f_equal; KQRWf.nv_acceq); rewrite E end end end.\n")
                t += f"Ltac {name}_kvs{j} IH := KQRWf.nv_stepb IH ltac:(repeat {name}_kva{j} IH).\n"
                ost = f"{name}_kvs{j}"
            t += (f"Lemma {name}_rr{j} {hrb}: {m}.\nProof. unfold {m}. fix IH {rv + 1}. {d0}intros kqn; destruct kqn as [|kqn]; intros; cbn [{unf}]; first [solve [{ost} IH] | solve [cbn; {ost} IH] | solve [cbv beta iota zeta delta -[{keepf}]; {ost} IH]]. Qed.\n")
        rrn.append(f"{name}_rr{j}")
        # (step 76) rewriting compares up to unfolding: such a lemma only where its function is in the goal, or it would turn the operation back
        rrj = f"match goal with Hr : {roomR} |- _ => rewrite ?({name}_rr{j} Hr) by KQRWf.vm_side end" if vmr else f"rewrite ?{name}_rr{j}"
        if re.search(r"__kva\d+_\d+__rq__wy$", m) and h:
            rrj = f"match goal with Hr : {roomR} |- _ => repeat {name}_kva{j} ({name}_rr{j} Hr) end" if vmr else f"repeat {name}_kva{j} {name}_rr{j}"
        # (step 82) a counter made a number: from what the text has
        if re.search(r"__k\d+__rq__wy$", m):
            rrj = f"match goal with Hr : {roomR} |- _ => rewrite <- ?({name}_rr{j} Hr) end" if vmr else f"rewrite <- ?{name}_rr{j}"
        if re.search(r"__q\d+__rq__wy$", m):
            # (step 80) read as a pair: what is known of the pair goes first
            rrw2.append(rrj)
            t += "Ltac KQRWf.kq_rw2 ::= progress (" + "; ".join(rrw2) + ").\n"
            continue
        rrw.append(f"try (match goal with |- context [{F}] => {rrj} end)" if m.endswith("__e__rq__wy") or m.endswith("__e__n__rq__wy") else rrj)
        t += "Ltac KQRWf.kq_rw ::= progress (" + "; ".join(rrw) + ").\n"
    # (step 83) a counter a function gives back, used as a counter: the bound of each such function, by induction, each after what it calls; the equations of what uses them hold where the counters are below the bound
    bqs = [m for m, _ in mts if (m.endswith("__bq__wy") or m.endswith("__bv__wy")) and not re.search(r"__bnd\d+__bq__wy$", m)]
    bbre = re.compile(r"(.*)__kb(\d+)_(\d+)_(\d+)_(.*)__bnd(\d+)__bq__wy$")
    bbs = [m for m, _ in mts if bbre.match(m)]
    # (step 104) or a use of such a counter where its value modulo a word is enough, which needs no bound
    ncp = bool(bqs) or bool(bbs) or any(m.endswith("__nc__wy") for m, _ in mts)
    if ncp:
        rrk0 = [f"{name}_rr{j}" for j, (m, h) in enumerate(rrs) if re.search(r"__k\d+__rq__wy$|__kb\d+_\d+_\d+_.*__rq__wy$", m)]
        nch = [kqfn(m[:-len("__nch__wy")]) for m, _ in mts if m.endswith("__nch__wy")]
        rrk = ("try unfold " + ", ".join(nch) + "; " if nch else "") + ("; ".join(f"match goal with Hr : {roomR} |- _ => rewrite ?({x} Hr) end" if vmr else f"rewrite ?{x}" for x in rrk0) or "idtac")
        bprev = "fail"
        vds = []
        # (step 120) a block's bounds, the counter first: one mutual fixpoint over them at a counter, each member's call posed by its own
        bbg = {}
        for m0 in bbs:
            mm0 = bbre.match(m0)
            bbg.setdefault(mm0.group(5), {})[int(mm0.group(3))] = (m0, kqfn(mm0.group(1)), int(mm0.group(2)), int(mm0.group(6)), int(mm0.group(4)))
        for g, (btag, grp) in enumerate(sorted(bbg.items())):
            bmb = list(grp.values())[0][4]
            if sorted(grp) != list(range(bmb)):
                sys.exit(f"{name}: a block's bounds not all made ({btag})")
            bst = [grp[i][0] for i in range(bmb)]
            bat = [x[:-len("__bq__wy")] + "__bba__wy" for x in bst]
            bfn = [grp[i][1] for i in range(bmb)]
            def bpose(i, pr):
                fn, r, ar = grp[i][1], grp[i][2], grp[i][3]
                xs = " ".join(f"?kx{q}" for q in range(ar))
                yin = " ".join(f"kx{q}" for q in range(ar))
                yrd = " ".join(f"kx{q}" for q in [r] + [q for q in range(ar) if q != r])
                return (f"match goal with |- context [{fn} {xs}] => lazymatch goal with _ : ({fn} {yin} <= _)%nat |- _ => fail | _ => pose proof ({pr} {yrd}) end end",
                        f"match goal with _ : context [{fn} {xs}] |- _ => lazymatch goal with _ : ({fn} {yin} <= _)%nat |- _ => fail | _ => pose proof ({pr} {yrd}) end end")
            for i in range(bmb):
                bwith = " ".join(f"(IH{k} (kqn : nat) {{struct kqn}} : {bat[k]} kqn)" for k in range(bmb) if k != i)
                bposes = " | ".join(bpose(k, f"IH{k}")[0] for k in range(bmb))
                t += (f"Lemma {name}_bdb{g}_{i} : {bst[i]}.\nProof. unfold {bst[i]}. fix IH{i} 1 with {bwith}. all: intros kqn; destruct kqn as [|kqn]; "
                      f"try unfold {', '.join(bat)} in *; intros; cbn [{' '.join(bfn)}]; KQRWf.nb_step ltac:(repeat first [{bposes} | {bprev}]). Qed.\n")
            for i in range(bmb):
                pa, pb = bpose(i, f"{name}_bdb{g}_{i}")
                t += f"Ltac {name}_btb{g}_{i} := first [{pa} | {pb} | {bprev}].\n"
                bprev = f"{name}_btb{g}_{i}"
        for j, m in enumerate(bqs):
            mb = re.match(r"(.*)__b(\d+)_(\d+)__b[qv]__wy$", m)
            fn, ar, r = kqfn(mb.group(1)), int(mb.group(2)), int(mb.group(3))
            isv = m.endswith("__bv__wy")
            xs = " ".join(f"?kx{i}" for i in range(ar))
            ys = " ".join(f"kx{i}" for i in range(ar))
            # (step 118) a value's bound is posed where no hypothesis but an equation names the call yet
            vno = f"assert_fails (idtac; match goal with H : ?P |- _ => match P with context [{fn} {ys}] => lazymatch P with _ = _ => fail | _ => idtac end end end)"
            ptn = (lambda pr: f"match goal with |- context [{fn} {xs}] => {vno}; pose proof ({pr} {ys}) end") if isv else \
                  (lambda pr: f"match goal with |- context [{fn} {xs}] => lazymatch goal with _ : ({fn} {ys} <= _)%nat |- _ => fail | _ => pose proof ({pr} {ys}) end end")
            nbs = "KQRWf.nb_stepv" if isv else "KQRWf.nb_step"
            pth = (lambda pr: f"match goal with _ : context [{fn} {xs}] |- _ => {vno}; pose proof ({pr} {ys}) end") if isv else \
                  (lambda pr: f"match goal with _ : context [{fn} {xs}] |- _ => lazymatch goal with _ : ({fn} {ys} <= _)%nat |- _ => fail | _ => pose proof ({pr} {ys}) end end")
            if r >= ar:
                t += (f"Lemma {name}_bd{j} : {m}.\nProof. unfold {m}. intros; unfold {fn}. {nbs} ltac:(repeat first [{bprev}]). Qed.\n")
            else:
                d0 = f"do {r} intro; " if r else ""
                t += (f"Lemma {name}_bd{j} : {m}.\nProof. unfold {m}. fix IH {r + 1}. {d0}intros kqn; destruct kqn as [|kqn]; intros; cbn [{fn}]; {nbs} ltac:(repeat first [{ptn('IH')} | " + (f"{pth('IH')} | " if isv else "") + f"{bprev}]). Qed.\n")
            # what the tests kept too
            t += f"Ltac {name}_bt{j} := first [{ptn(f'{name}_bd{j}')} | {pth(f'{name}_bd{j}')} | {bprev}].\n"
            bprev = f"{name}_bt{j}"
            if isv:
                # (step 118) the call taken apart where the text uses its counters, its bound posed first
                vds.append(f"match goal with |- context [{fn} {xs}] => (try {name}_bt{j}); let e := fresh \"kqe\" in destruct ({fn} {ys}) eqn:e; KQRWf.nb_vh0 end")
        t += f"Ltac KQRWf.kq_bd ::= repeat {bprev}.\nLtac KQRWf.kq_nc ::= first [KQRWf.nc_step ltac:({rrk}) | KQRWf.nc_match].\nLtac KQRWf.kq_nc_side ::= KQRWf.nc_lia.\n"
        if vds:
            t += "Ltac KQRWf.kq_vh ::= KQRWf.nb_vh.\nLtac KQRWf.kq_vd ::= first [" + " | ".join(vds) + "].\n"
        keepf = keepf + " Z.to_nat Uint63.to_Z"
    yf = {f[0]: f[0].rsplit(".", 1)[-1] + "__wy" for f in fs if f[0].rsplit(".", 1)[-1] + "__wy" in made}
    # (step 83) the bound as a number
    bnz = lambda f, j: str(2**62 - j * 2**20) if not f[7] else str(f[7])
    ncfs = {m[:-len("__nc__wy")] for m in made if m.endswith("__nc__wy")}
    ncf = lambda f: f[0].rsplit(".", 1)[-1] in ncfs
    keepg = " ".join(sorted({"KQ.KQRun.kq_nat"} | {m[:-len("__rq__wy")] + "__rp__wy" for m, _ in rrs} | set(yf.values())))
    alt0 = f" | solve [cbv beta iota zeta delta -[{keepg}]; KQRWf.own_step0]" if vmr else ""
    altn = f" | solve [cbv beta iota zeta delta -[{keepg}]; KQRWf.own_step IH]" if vmr else ""
    for j, f in enumerate(fs):
        if f[0] in yf:
            W = yf[f[0]]
            if ncf(f) and wsl(f) != "nil":
                # the counters held by weights: not yet
                t += "Check KQ_refused__a_counter_given_back_used_where_the_counters_are_held_by_weights.\n"
            if ncf(f):
                t += (f"Lemma {name}_rqy{j} {hrb}: KQR.eqCb {bnz(f, j)}%Z {f[1]} _ (KQR.eqN {kl(f)} {f[3]} _) {W} {f[0]}.\n"
                      + (f"Proof. cbn [KQR.eqCb KQR.eqN]. fix IH 1. intros kqn kqH; destruct kqn as [|kqn]; intros; cbn [{W} {f[0]}]; first [solve [KQRWf.own_step IH] | solve [cbn; KQRWf.own_step IH] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.own_step IH]{altn}]. Qed.\n" if f[0] in fix1 else
                         f"Proof. cbn [KQR.eqCb KQR.eqN]. intros. unfold {W}, {f[0]}. first [solve [KQRWf.own_step0] | solve [cbn; KQRWf.own_step0] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.own_step0] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.own_step0p]{alt0}]. Qed.\n"))
                continue
            t += (f"Lemma {name}_rqy{j} {hrb}: KQR.eqC {f[1]} _ (KQR.eqN {kl(f)} {f[3]} _) {W} {f[0]}.\n"
                  + (f"Proof. cbn [KQR.eqC KQR.eqN]. fix IH 1. intros kqn; destruct kqn as [|kqn]; intros; cbn [{W} {f[0]}]; first [solve [KQRWf.own_step IH] | solve [cbn; KQRWf.own_step IH] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.own_step IH]{altn}]. Qed.\n" if f[0] in fix1 else
                     f"Proof. cbn [KQR.eqC KQR.eqN]. intros. unfold {W}, {f[0]}. first [solve [KQRWf.own_step0] | solve [cbn; KQRWf.own_step0] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.own_step0] | solve [cbv beta iota zeta delta -[{keepf}]; KQRWf.own_step0p]{alt0}]. Qed.\n"))
    t += "Strategy opaque [" + " ".join([f[0] for f in fs if not iswr(f[0])] + tmpls) + "].\n"   # a copy is unfolded first
    # (step 94, 95) our abbreviations are unfolded first and the library's functions a node of S means last, so that the meaning and
    # the text meet at the same call and its arguments are compared: else the kernel opens the program's call on written numbers
    # and works it out in unary (F77, F78)
    t += "Strategy expand [KQC.KQLAuto.ofn KQR.cmpn KQR.nbop_nat KQR.nlop_nat].\n"
    t += ("Strategy opaque [Nat.pow Nat.add Nat.mul Nat.sub Nat.pred Nat.min Nat.max Nat.div2 Nat.div Nat.modulo Nat.land Nat.lor Nat.lxor"
          " Nat.ldiff Nat.shiftl Nat.shiftr Nat.testbit Nat.gcd Nat.sqrt Nat.log2 Nat.eqb Nat.ltb Nat.leb Nat.of_num_uint].\n")
    if not no_proof:
        for j, f in enumerate(fs):
            cs = "[" + "; ".join(f"existT (@KQR.ftype {inst}) {sig(g)} {g[0]}" for g in fs[:j]) + "]"
            oks = "".join(f"(conj {f'(conj (KQR.kit_entry_ok {kitop(fs[i])}) {name}_rok{i})' if iskit(fs[i]) else f'{name}_rok{i}'} " for i in range(j)) + "Logic.I" + ")" * j
            if f[0] in pfs or f[0] in pfc or f[0] in yf:
                # (step 56) the theorem of its budget function's call, then equal to it at every argument
                # (step 59) a copy: the same, its equation the function's at the functions given
                if f[0] in pfs:
                    W, rq0 = pfs[f[0]][3] + "__w", reqs[f[0]]
                elif f[0] in yf:
                    W, rq0 = yf[f[0]], f"{name}_rqy{j}"
                else:
                    W, rq0 = f[0] + "__w", f"{name}_rqc{j}"
                    t += (f"Lemma {rq0} : KQR.eqC {f[1]} _ (KQR.eqN {kl(f)} {f[3]} _) {W} {f[0]}.\n"
                          f"Proof. cbn [KQR.eqC KQR.eqN]; intros; unfold {W}, {f[0]}; apply {reqs[pfc[f[0]]]}. Qed.\n")
                t += f"Lemma {name}_rok{j} : @KQR.callee_ok {inst} {name}_prog (KQR.gid1 {j}) {bnd(f, j)} {sig(f)} {f[0]}.\n"
                if ncf(f):
                    # (step 118) the slot block's room, where the program gives back a record through it and has no __v row
                    rr0 = (f"{name}_room {rq0}" if vmr else f"(fun _ => Logic.I) (fun _ => {rq0})" if roomw <= 1 else
                           f"(fun Hs => Hs {[int(r[2]) for r in recs].index(roomw)}%nat (proj1 (PeanoNat.Nat.ltb_lt 1%nat {roomw}%nat) eq_refl)) (fun _ => {rq0})")
                    t += (f"Proof. exact_no_check (@KQR.callee_ok_eqb {inst} {name}_prog (KQR.gid1 {j}) {bnz(f, j)}%Z {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)} {bo(f)} ({roomR}) {W} {f[0]} {rr0}"
                          f" (@KQR.compile_f_ok {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {sig(f)} (KQRReify.body_at {name}_funs {j}) eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl)). Qed.\n")
                    continue
                t += (f"Proof. exact_no_check (@KQR.callee_ok_eqr {inst} {name}_prog (KQR.gid1 {j}) {bnd(f, j)} {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)} {bo(f)} {wsl(f)} ({roomR}) {W} {f[0]} {name}_room {rq0}"
                      f" (@KQR.compile_f_ok {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {sig(f)} (KQRReify.body_at {name}_funs {j}) eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl)). Qed.\n" if vmr and f[0] in yf else
                      f"Proof. exact_no_check (@KQR.callee_ok_eq {inst} {name}_prog (KQR.gid1 {j}) {bnd(f, j)} {f[1]} {kl(f)} {f[3]} {f[4]} {f[5]} {rq(f)} {bo(f)} {wsl(f)} {W} {f[0]} {rq0}"
                      f" (@KQR.compile_f_ok {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {sig(f)} (KQRReify.body_at {name}_funs {j}) eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl)). Qed.\n")
                continue
            t += f"Lemma {name}_rok{j} : @KQR.callee_ok {inst} {name}_prog (KQR.gid1 {j}) {bnd(f, j)} {sig(f)} {f[0]}.\n"
            # (step 45) a member of a mutual block is one call of its block: not a fix over its counter
            # (step 46) a copy is a fix over its counter too
            prec = isp(f) and not iskit(f) and (iscp(f[0]) or f[0] in fix1)
            if iskit(f):
                # (step 93) its theorem under the signature without the flag, the same for a function that takes no memory
                t += (f"Proof. exact_no_check (@KQR.compile_f_ok {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {sigc(f)} (KQRReify.body_at {name}_funs {j})"
                      f" eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl). Qed.\n")
            elif iscp(f[0]) or isw(f[0]) or prec or f[0] in cv:
                # a copy: not a fix over its counter, so its statement comes from its two equations, each by conversion
                # (a copy that writes the memory and gives back a number has a memory: no memory argument)
                # (step 41) a boolean, a number and a memory, a record given back: their own copies' theorems
                ri = f" {ord(f[6]) - ord('a')}" if f[6] not in ("", "B", "P") else ""
                # (step 48 continued) a copy giving back a boolean or a record whose body writes: an X body of those
                thm, p0, p1, mm = (("compile_f_okrxb", "KQR.fx0", "KQR.fx1", "") if f[6] == "B" and f[5] == "true" else
                                   ("compile_f_okrxr", "KQR.fx0", "KQR.fx1", "") if ri and f[5] == "true" else
                                   ("compile_f_okrb", "KQR.fbb0", "KQR.fbb1", f" {f[3]}") if f[6] == "B" else
                                   ("compile_f_okrp", "KQR.fpv0", "KQR.fpv1", f" {f[3]}") if f[6] == "P" else
                                   ("compile_f_okrr", "KQR.fbr0", "KQR.fbr1", f" {f[3]}") if ri else
                                   ("compile_f_okrm", "KQR.fm0", "KQR.fm1", f" {f[3]}") if f[4] == "true" else
                                   ("compile_f_okrx", "KQR.fx0", "KQR.fx1", "") if f[5] == "true" else
                                   ("compile_f_okr", "KQR.fr0", "KQR.fr1", f" {f[3]}"))
                b = f"(KQRReify.body_at {name}_funs {j})"
                # (step 53) a memory parameter never read: the theorem for each of its values
                dead = f[0] + "__g" in made
                hh = (f"(KQR.cmapT {f[1]} (KQR.ntypeTP {kl(f)} (KQR.rtq {f[4]} {rq(f)})) (KQR.ntypeT {kl(f)} true (KQR.rtq {f[4]} {rq(f)}))"
                      f" (KQR.unpairT {kl(f)} (KQR.rtq {f[4]} {rq(f)})) {f[0]})") if prec else f"({f[0]}__g u)" if dead else f[0]
                core = (f"(@KQR.{thm} {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {int(f[1]) - 1} {kl(f)}{mm} ({p0} {b}) ({p1} {b})"
                        f" {bo(f)} {ws(f)}{ri} {hh} eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl eq_refl"
                        f" (fun n => {'ltac:(reflexivity)' if prec else 'eq_refl'}))")
                if prec:
                    core = (f"(@KQR.callee_ok_unpair {inst} {name}_prog (KQR.gid1 {j}) {bnd(f, j)} {f[1]} {kl(f)} {f[4]} {f[5]}"
                            f" {rq(f)} {bo(f)} {wsl(f)} {f[0]} {core})")
                if dead:
                    core = (f"(@KQR.callee_ok_dead {inst} {name}_prog (KQR.gid1 {j}) {bnd(f, j)} {f[1]} {kl(f)} {f[4]} {f[5]}"
                            f" {rq(f)} {bo(f)} {wsl(f)} {f[0]}__g (fun u => {core}))")
                t += f"Proof. exact_no_check {core}. Qed.\n" 
            elif isp(f):
                # the pair (step 44): the theorem of the function on the two components, then the function's own
                t += (f"Proof. exact_no_check (@KQR.callee_ok_unpair {inst} {name}_prog (KQR.gid1 {j}) {bnd(f, j)} {f[1]} {kl(f)} {f[4]} {f[5]}"
                      f" {rq(f)} {bo(f)} {wsl(f)} {f[0]} (@KQR.compile_f_ok {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {sigc(f)}"
                      f" (KQRReify.body_at {name}_funs {j}) eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks})"
                      f" eq_refl eq_refl)). Qed.\n")
            else:
                t += (f"Proof. exact_no_check (@KQR.compile_f_ok {inst} {laws} {name}_prog {cs} KQR.gid1 {j} {sig(f)} (KQRReify.body_at {name}_funs {j})"
                      f" eq_refl eq_refl (@KQR.all_ok_callees {inst} {name}_prog KQR.gid1 {cs} {oks}) eq_refl eq_refl). Qed.\n")
            if shared:
                # the sequential meaning describes the program only if it reaches its shared blocks through marked operations
                t += f"Lemma {name}_rsh{j} : KQR.sh_ok {shared} (KQRReify.body_at {name}_funs {j}) = true.\nProof. exact eq_refl. Qed.\n"
    if not no_proof:
        # (step 96) the program's end theorem: the entry's theorem said of the Clight the generator makes (KQREnd.callee_end)
        t += f"Definition {name}_end := @KQREnd.callee_end {inst} _ _ _ _ _ {name}_rok{len(fs) - 1} eq_refl eq_refl.\n"
    t += c_print(name)
    f1 = os.path.join(GEN, f"{name}_rp.v")
    # (step 86) a function named p1 or p2: `.p1` is a token of MetaRocq's notations: by its short name, the program's file being imported
    t = re.sub(r"\bKQG\.\w+\.(p[12])\b", r"\1", t)
    open(f1, "w").write(t)
    rc, out = coqc(f1)
    if rc != 0:
        # (step 119) a check the time limit stopped, said first: the table keeps a line's start
        print(name, "REFLECT CHECK FAILED" + (" (the time limit, KQ_TIMEOUT)" if "Timeout!" in out else "") + FOLLOW + ":", out[-400:].replace("\n", " "), flush=True)
        return None
    if not no_proof and os.environ.get("KQ_ENDAX"):
        # (step 96) what the end theorem rests on, printed from a file that imports nothing: each name the one constant it names (F76)
        fa = os.path.join(GEN, f"{name}_ra.v")
        open(fa, "w").write(f"From KQG Require {name}_rp.\nPrint Assumptions KQG.{name}_rp.{name}_end.\n")
        rca, outa = coqc(fa)
        ax = sorted({m.group(1) for m in re.finditer(r"(?m)^([A-Za-z_][A-Za-z_0-9.']*) :", outa)})
        if rca != 0 or not (ax or "Closed under the global context" in outa):
            print(name, "REFLECT CHECK FAILED" + FOLLOW + ": the end theorem's assumptions not printed:", outa[-300:].replace("\n", " "), flush=True)
            return None
        print(name, f"END-ASSUM {len(ax)}:", " ".join(ax), flush=True)
    idx = len(fs) - 1   # the entry is the last function read: every function is read after those it calls
    e = fs[idx]
    if any(c not in "IB" for c in e[2]) or e[6] not in ("", "B"):   # an entry taking or giving back a record: main gives and takes numbers
        print(name, "reflect: the entry takes or gives back a record" + FOLLOW, flush=True)
        return None
    kinds = "N" * int(e[1]) + "I" * len(e[2]) + ("M" if e[3] == "true" else "")   # a boolean is passed as a number, 1 or 0
    # the slot block: room for the fields after the first of each record type of the program ([KQR.slot_room], which every
    # theorem of the program takes; the driver provides it, as for the translator's two results)
    slots = max([int(n) for (_, _, n, _) in recs] + [1]) - 1
    # an entry whose parameters stand in another order: the order the syntax takes, each its place in main's call (step 41)
    pp = os.path.join(GEN, f"{name}_rperm.out")
    pm = re.search(r"Some\s*\[([^\]]*)\]", open(pp).read()) if os.path.exists(pp) else None
    perm = [int(x) for x in re.findall(r"\d+", pm.group(1))] if pm else None
    return 1000 + idx, kinds, "M" if e[4] == "true" else "I", len(fs), slots, perm

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
    # the verified compiler is the route (step 29: the walk retired); --walk (or KQ_WALK=1) the translator and the walk
    # alone, the yardstick a moved program is timed against; --reflect and KQ_REFLECT are accepted and change nothing
    walk_mode = bool(os.environ.get("KQ_WALK"))
    # an ordinary .v file: the function the program starts with, by default the last of the file
    start = None
    for a in sys.argv[1:]:
        if a == "--reflect":
            pass
        elif a == "--walk":
            walk_mode = True
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
        elif a.startswith("--main="):
            start = a[len("--main="):]
        elif a.startswith("--entry="):
            entry_name = a[len("--entry="):]
        elif a.startswith("--ext="):
            ext = a[len("--ext="):]
        else:
            names.append(a)
    for src in names:
        path = src if src.endswith((".body", ".v")) else f"hand/{src}.body"
        name = re.sub(r"[^A-Za-z0-9_]", "_", os.path.splitext(os.path.basename(path))[0])
        body = open(path).read()
        # a program that names a function of a library of lib/ gets the library's text in front of it, as compile.sh does
        for pre, lib, mark in (("slab_", "Slab", "SLAB"), ("view_", "View", "VIEW"), ("(?:loop_|wfix)", "Loop", "LOOP"),
                               (r"(?:(?:[ui](?:8|16|32)|i64)_[a-z]+|rot[lr](?:32|64)|bswap(?:16|32|64)|popcount(?:32|64)|clz(?:32|64)|ctz(?:32|64)|u64_mulhi)\b", "CInt", "CINT")):
            if re.search(r"\b" + pre, body) and f"(* {mark}-BEGIN *)" not in body and not re.search(r"Require\b[^.]*\b" + lib + r"\b", body):
                lt = open(os.path.join(ROOT, "lib", lib + ".v")).read()
                text = lt[lt.index(f"(* {mark}-BEGIN *)") + len(f"(* {mark}-BEGIN *)"):lt.index(f"(* {mark}-END *)")]
                if mark == "CINT":
                    text = "Module KQCInt.\n" + text + "End KQCInt.\nImport KQCInt.\n"
                body = text + "\n" + body
        # a .body has a main of the kit's form; an ordinary file needs none, and a function of its own may be called main
        has_main = path.endswith(".body") or "kq_keep" in body
        prog, mt = split_main(body) if has_main else (body, None)
        err = build_user_files(body, path)
        if err:
            m = re.search(r"Error:\s*(.*?)(?:\n\n|$)", err, re.S)
            print(name, "reflect: not read by the verified compiler's reifier (Rocq refused a file of the program: "
                  + (" ".join(m.group(1).split())[:200] if m else "it did not compile") + ")" + FOLLOW, flush=True)
            print(name, "REFUSED: not compiled by the verified compiler (the reasons above)", flush=True)
            continue
        if has_main:
            try:
                entry, args, wrap = parse_main(mt)
            except SystemExit as ex:
                print(name, "NOT READ:", ex); continue
        else:
            entry = start or last_def(prog)
            r, why = sig_args(name, prog, entry)
            if not r:
                print(name, "NOT READ:", why); continue
            args, wrap = r
        if not walk_mode:
            r = reflect(name, entry, prog, no_proof)
            if not r:
                print(name, "REFUSED: not compiled by the verified compiler (the reasons above)", flush=True)
                continue
            if r:
                eid, kinds, res, n, slots, perm = r
                if perm:
                    # (step 53) an entry of two memory parameters: main gives it one memory
                    if any(args[i] != args[perm[-1]] for i in range(len(args)) if i not in perm):
                        print(name, "reflect: not read by the verified compiler's reifier (main gives the entry two memories)" + FOLLOW, flush=True)
                        print(name, "REFUSED: not compiled by the verified compiler (the reasons above)", flush=True)
                        continue
                    args = [args[i] for i in perm]
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
        t = re.sub(r"\bKQG\.\w+\.(p[12])\b", r"\1", t)
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
    grows = re.search(r"\bf91019\b", c) is not None
    def text(b, hw):
        return ('#include "gc_stack.h"\n#include "kq_io.h"\n' + ('#include "kq_hw.h"\n' if hw else "") + c
                + driver(name, eid, kinds, res, args, wrap, hw, b, prefix, entry_name, secondary, ext, grows,
                         max(8, slots) if slots else (8 if pairfns else 0)))
    open(cfile, "w").write(text(bare, uses_hw))
    if not bare and not secondary:
        # the same functions with no hosted header: sup/free/ builds it (proved/examples.sh); the wrappers of the machine's
        # operations only if one is called (a declaration of the others stays, as in the theorem's program)
        called = re.search(r"(?m)^(?!unsigned long long f91).*\bf91[01]\d\d\(", c) is not None
        open(os.path.join(GEN, f"{name}_bare.c"), "w").write(text(True, uses_hw and called))

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
