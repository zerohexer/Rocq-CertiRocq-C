#!/usr/bin/env python3
"""vroute.py [NAMES]: every example and corpus program from an ordinary .v file: its text with no main, the arguments read from the
signature.  The C of its functions must be the C of the .body route, and the answer the same.  (Rocq-C-solution.md §12.B)"""
import glob, os, re, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
sys.path.insert(0, "proved")
import importlib.util
sp = importlib.util.spec_from_file_location("kitc", "proved/kitc.py"); kitc = importlib.util.module_from_spec(sp); sp.loader.exec_module(kitc)
D = "/tmp/vroute"; os.makedirs(D, exist_ok=True)
subprocess.run(["python3", "tests/mkworst.py", D], capture_output=True)   # the memory and the arguments examples.sh runs them on
bodies = sorted(glob.glob("proved/examples/*.body")) + sorted(glob.glob("hand/*.body"))
if len(sys.argv) > 1:
    bodies = [b for b in bodies if os.path.basename(b)[:-5] in sys.argv[1:]]
def funcs(c):
    # all of it but the driver's call of the entry, which takes its arguments from the command line
    return re.sub(r"(?m)^\s*unsigned long long r = f\d+\(.*$", "", c)
ok = bad = skip = 0
for b in bodies:
    n = os.path.basename(b)[:-5]
    text = open(b).read()
    if "Definition main" not in text:
        skip += 1; continue
    prog, mt = kitc.split_main(text)
    entry, args, wrap = kitc.parse_main(mt)
    if any(a[0] in ("NE", "IE") for a in args):
        print(n, "skipped: main computes an argument"); skip += 1; continue
    v = os.path.join(os.path.dirname(b), n + "_v.v")   # beside the program: a file it requires is found there
    open(v, "w").write("From KQ Require Import KQRun.\n" + prog)
    # the .body route's C
    subprocess.run(["python3", "proved/kitc.py", "--no-build", b], capture_output=True, text=True)
    r = subprocess.run(["python3", "proved/kitc.py", v, f"--main={entry}"], capture_output=True, text=True)
    fa, fb = f"proved/gen/{n}_proved.c", f"proved/gen/{n}_v_proved.c"
    if "PROVED" not in r.stdout or not os.path.exists(fb):
        print(n, "NOT READ:", (r.stdout + r.stderr)[-300:].replace("\n", " ")); bad += 1; continue
    same = funcs(open(fa).read()) == funcs(open(fb).read())
    # the answer: the arguments of main on the command line
    os.remove(v)
    if b.startswith("hand/"):   # the corpus's memory and answers are corpus.sh's: the C is what is compared here
        print(n, "C same" if same else "C DIFFERS", flush=True)
        if same: ok += 1
        else: bad += 1
        continue
    mem = f"proved/examples/{n}.mem" if os.path.exists(f"proved/examples/{n}.mem") else f"{D}/same.mem"
    given = open(f"proved/examples/{n}.args" if os.path.exists(f"proved/examples/{n}.args") else f"{D}/same.args").read().split()
    cli = []
    for a in args:
        if a[0] == "L": cli.append(str(a[1]))
        elif a[0] in ("N", "I"): cli.append(given[a[1]] if a[1] < len(given) else "0")
    exp = open(f"proved/examples/{n}.expect").read().split()[0] if os.path.exists(f"proved/examples/{n}.expect") else None
    env = dict(os.environ); env["KQ_MEM"] = mem
    out = subprocess.run([f"bin/P_{n}_v"] + cli, capture_output=True, text=True, env=env).stdout.split()
    got = out[1] if len(out) > 1 else None
    print(n, "C same" if same else "C DIFFERS", "answer", got, "expected", exp, flush=True)
    if same and got == exp: ok += 1
    else: bad += 1
print(f"{ok} programs with the same C and the expected answer, {bad} not, {skip} skipped")
