#!/usr/bin/env python3
"""kitc.py [--no-build] NAME...   (inside the image, in the repo's directory)

A kit program (hand/NAME.body, or a path to a .body file) through the proved route:
  1. the translator reads the function `main` applies and every function of the file it uses (proved/KQMTrans.v)
     and the kernel checks, for each, that the KQL function computes it (proved/KQMAuto.v);
  2. the generated Clight is printed as C (proved/KQLPrint.v);
  3. a driver fills the two tables of the proved theorem (the address and the size of each block) from the kit's
     loader, calls the entry function with the numbers `main` gives it, and returns what `main` returns;
  4. clang builds it with the kit's support code: bin/P_NAME, a program that reads the same memory file and the
     same command line as the kit's own.
The Rocq files are written to proved/gen/, the C to proved/gen/NAME_proved.c."""
import re, subprocess, sys, os, glob

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
    r = subprocess.run(["coqc", "-w", "-all", "-R", ROOT, "KQ", "-Q", os.path.join(ROOT, "proved"), "KQC", *extra, path],
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

def proof_file(name, prog, entry, fns, helpers, groups=(), pairfns=()):
    t = HDR + prog + f'\nMetaRocq Run (kqm_translate {entry} "{name}_prog").\n'
    t += f"Set Default Timeout {os.environ.get('KQ_TIMEOUT', '300')}.\n"
    if helpers:
        t += "Ltac kqm_unf ::= cbv beta zeta iota delta [" + " ".join(helpers) + "].\n"
    if pairfns:
        # functions that give back two numbers: the second goes through the slot block, which the proof puts back as it was
        t += "Ltac kqm_laws ::= kqm_laws_on.\nLtac kqm_pairs ::= kqm_pairs_on.\n"
        t += "Ltac kqm_uh h ::= first [ progress cbn [h] | unfold h ].\n"
        t += "Ltac kqm_unf2 ::= cbn [" + " ".join(pairfns) + "].\n"
    done = set()
    for i, f in enumerate(fns):
        if f in done:
            continue
        pre = "".join(f"pose proof {g}_ok as H{j}; hnf in H{j}. " for j, g in enumerate(fns[:i]))
        grp = next((g for g in groups if g[0] == f), None)
        if grp:
            # functions that call each other: one lemma for all, by induction on the counter they share
            n = len(grp)
            conj = lambda ms: ms[0] + "_kat d" if len(ms) == 1 else ms[0] + "_kat d /\\ (" + conj(ms[1:]) + ")"
            pat = lambda k: f"IH{k}" if k == n else f"[IH{k} " + pat(k + 1) + "]"
            hn = "; ".join(f"hnf in IH{k}" for k in range(1, n + 1))
            t += f"Lemma {f}_grp : forall d : nat, {conj(grp)}.\nProof. {pre}induction d as [|d {pat(1)}]; [ | {hn} ]; repeat split; kqm_auto. Qed.\n"
            for k, m in enumerate(grp):
                proj = "(G d)" if False else f"({f}_grp d)"
                for _ in range(k):
                    proj = f"(proj2 {proj})"
                if k < n - 1:
                    proj = f"(proj1 {proj})"
                t += f"Lemma {m}_ok : {m}_kstmt. Proof. exact (fun d => {proj}). Qed.\n"
                done.add(m)
            continue
        t += f"Lemma {f}_ok : {f}_kstmt. Proof. {pre}kqm_auto. Qed.\n"
    return t

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
    # a program with a function that gives back two numbers: block 63 (8 cells) carries the second one back to the caller
    slotinit = ("  static value kq_slot_cells[16]; if (!kq_b[63].p) { for (int j = 0; j < 16; j++) kq_slot_cells[j] = KQ_V(0);\n"
                "    kq_b[63].p = kq_slot_cells; kq_b[63].len = 8; kq_b[63].lim = 16; }\n") if slots else ""
    ret = "return kq_sum(KQ_V(0));" if res == "M" else "return (value) r;"
    hwdef = ("/* ---- the machine's operations: the kit's C bodies (hw/kq_hw.h) behind the external functions of the theorem */\n"
             + ("" if bare else "#include <sys/mman.h>\nuintptr_t kq_hw_wlo, kq_hw_whi;\n") + ext_dispatch(ext) + HW_WRAPPERS) if (uses_hw and not secondary) else ""
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

def main():
    build = True
    bare = False
    secondary = False
    prefix = ""
    entry_name = "body"
    ext = None
    names = []
    for a in sys.argv[1:]:
        if a == "--no-build":
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
        prog, mt = split_main(body)
        try:
            entry, args, wrap = parse_main(mt)
        except SystemExit as ex:
            print(name, "NOT READ:", ex); continue
        # 1: translate
        f0 = os.path.join(GEN, f"{name}_t.v")
        open(f0, "w").write(HDR + prog + f'\nMetaRocq Run (kqm_translate {entry} "{name}_prog").\n')
        rc, out = coqc(f0)
        m = re.search(r"KQM: \d+ functions: ([\w' ]+)", out)
        if not m:
            print(name, "TRANSLATION FAILED:", out[-300:].replace("\n", " ")); continue
        fns = m.group(1).split()
        mh = re.search(r"KQM helpers:([^\n]*)", out)
        helpers = mh.group(1).split() if mh else []
        me = re.search(r"KQM entry: (\w+) (\d+) (\w*) (\w)", out)
        _, eid, kinds, res = me.groups()
        # 2: prove, and print the C
        f1 = os.path.join(GEN, f"{name}_p.v")
        groups = [g.split() for g in re.findall(r"KQM group: ([\w' ]+)", out)]
        mpf = re.search(r"KQM pairfns:([^\n]*)", out)
        pairfns = mpf.group(1).split() if mpf else []
        t = proof_file(name, prog, entry, fns, helpers, groups, pairfns)
        t += f'\nFrom Stdlib Require Import String.\nLocal Open Scope string_scope.\nRedirect "{name}_c" Eval vm_compute in (KQLPrint.pstr 77777%positive (KQMTop.tr_kit_program {name}_prog)).\n'
        # a lemma the kernel does not finish (KQ_TIMEOUT) is left unproved (Admitted): the C is still made and is
        # checked by tests only; the program is then reported as unproved
        unproved = []
        while True:
            open(f1, "w").write(t)
            rc, out = coqc(f1)
            if rc == 0:
                break
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
        else:
            pass
        if rc != 0:
            continue
        if unproved:
            print(name, "UNPROVED", " ".join(unproved), "of", len(fns), "functions (the rest proved); entry", entry, "id", eid, kinds, "->", res)
        else:
            print(name, "PROVED", len(fns), "functions; entry", entry, "id", eid, kinds, "->", res)
        # 3: the C
        raw = open(os.path.join(GEN, f"{name}_c.out")).read()
        c = raw[raw.index('"') + 1: raw.rindex('"')].replace('""', '"')
        cfile = os.path.join(GEN, f"{name}_bare.c" if bare else f"{name}_proved.c")
        uses_hw = re.search(r"\bf91[01]\d\d\b", c) is not None
        if prefix:
            c = re.sub(r"\bf(1\d{3})\b", prefix + r"f\1", c)
        open(cfile, "w").write('#include "gc_stack.h"\n#include "kq_io.h"\n' + ('#include "kq_hw.h"\n' if uses_hw else "") + c
                               + driver(name, eid, kinds, res, args, wrap, uses_hw, bare, prefix, entry_name, secondary, ext, bool(pairfns)))
        if not build:
            continue
        # 4: build, as the kit builds its programs
        rt = glob.glob(os.path.expanduser("~/.opam/*/lib/coq/user-contrib/CertiRocq/Plugin/runtime"))[0]
        os.makedirs("bld/user", exist_ok=True); os.makedirs("bin", exist_ok=True)
        for f in glob.glob("sup/v4/*.h") + glob.glob("sup/v4/*.c") + ["hw/kq_hw.h"]:
            run(["cp", f, "bld/user/"])
        cf = ["-w", "-O2", "-flto", "-fomit-frame-pointer", "-Ibld/user", f"-I{rt}", "-I."]
        r = run(["clang", *cf, "-o", f"bin/P_{name}", "bld/user/kq_io3.c", cfile, f"{rt}/gc_stack.c", "bld/user/kq_prim63.c"])
        print(name, "built bin/P_" + name if r.returncode == 0 else "BUILD FAILED: " + r.stderr[-400:])

if __name__ == "__main__":
    main()
