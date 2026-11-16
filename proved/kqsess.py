#!/usr/bin/env python3
# proved/kqsess.py DIR I: (option 2, step B) one Rocq session that checks cell after cell, the libraries loaded once.  It listens on
# DIR/sI.sock; a client (kitc.py with KQ_SESSION=2, holding DIR/sI.lock) sends its commands, one JSON line each, and gets back what
# Rocq printed.  When the client leaves, the session is set back to the mark made after the libraries (`Reset kq_mark.`), so nothing
# one cell defines, redefines or loads reaches the next.  The same files are checked by the same Rocq.  A session that fails or
# whose reset fails, that holds more than KQ_SESS_MB megabytes, or that has served KQ_SESS_CELLS cells is started afresh.
# Run by proved/matrix/run.sh from the repository's root; kitc.py falls back to a session of its own when none answers.
import json, os, re, socket, subprocess, sys

ROOT = os.getcwd()
GEN = os.path.join(ROOT, "proved", "gen")
os.makedirs(GEN, exist_ok=True)
FLAGS = ["-R", ROOT, "KQ", "-Q", os.path.join(ROOT, "proved"), "KQC", "-Q", GEN, "KQG"]
# loaded, not imported: each cell's files import what they import, as when coqc checks them.  KQRWf is not loaded here: only the
# proofs that need it load it (kitc.py), and a cell that does not see it as coqc would not.
PRE = ("From Stdlib Require ZArith List.\nFrom MetaRocq.Template Require All.\n"
       "From KQC Require KQL KQLAuto KQM KQMAuto KQMTrans KQMTop KQLGen KQLProof KQLPrint KQR KQRK KQRReify KQREnd.\n"
       "From KQ Require KQRun.\n")
MARK = "Definition kq_mark := tt."
MAX_MB = int(os.environ.get("KQ_SESS_MB", "1100"))
MAX_CELLS = int(os.environ.get("KQ_SESS_CELLS", "60"))
N = [0]

def send(p, cmd):
    """cmd to the session, then a command that fails with a marker in its message: what Rocq printed before it.  False: it ended."""
    N[0] += 1
    marker = f"kq_session_done_{N[0]}"
    try:
        p.stdin.write(cmd + "\n" + f"Fail Check {marker}.\n")
        p.stdin.flush()
    except (BrokenPipeError, OSError):
        return False, ""
    out = []
    while True:
        line = p.stdout.readline()
        if line == "":
            return False, "".join(out)
        if marker in line:
            return True, "".join(out)
        out.append(line)

def failed(out):
    return bool(re.search(r"^(?:Toplevel input|Error)", out, flags=re.M) and re.search(r"\bError\b", out))

def start():
    try:
        p = subprocess.Popen(["coqtop", "-q", "-w", "-all", *FLAGS], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, cwd=GEN, bufsize=1)
    except OSError as e:
        sys.stderr.write(f"kqsess: the session did not start: {e}\n")
        return None
    ok, out = send(p, PRE + MARK)
    if not ok or failed(out):
        stop(p)
        sys.stderr.write("kqsess: the session did not start: " + out[-400:] + "\n")
        return None
    return p

def stop(p):
    try:
        p.kill()
        p.wait(timeout=30)
    except Exception:
        pass

def rss_mb(p):
    try:
        for l in open(f"/proc/{p.pid}/status"):
            if l.startswith("VmRSS:"):
                return int(l.split()[1]) // 1024
    except OSError:
        pass
    return 0

def main():
    d, i = sys.argv[1], int(sys.argv[2])
    path = os.path.join(d, f"s{i}.sock")
    if os.path.exists(path):
        os.unlink(path)
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(path)
    srv.listen(8)
    p, served = start(), 0
    while True:
        c, _ = srv.accept()
        f = c.makefile("rw", encoding="utf-8")
        if p is None or p.poll() is not None:
            p, served = start(), 0
        try:
            for line in f:
                req = json.loads(line)
                if p is None:
                    ok, out = False, "kqsess: no session"
                else:
                    ok, out = send(p, req["cmd"])
                f.write(json.dumps({"ok": ok, "out": out}) + "\n")
                f.flush()
                if not ok:
                    if p is not None:
                        stop(p)
                    p = None
                    break
        except (BrokenPipeError, ConnectionResetError, OSError, ValueError):
            pass
        try:
            c.close()
        except OSError:
            pass
        served += 1
        if p is not None:
            # a proof a failed file left open is dropped first (where none is open, what it prints is not read)
            ok, _ = send(p, "Abort All.")
            ok, out = send(p, "Reset kq_mark.\n" + MARK) if ok else (False, "")
            mb = rss_mb(p)
            again = not ok or failed(out) or served >= MAX_CELLS or mb > MAX_MB
            # what each session did, one line a cell (proved/gen/kqsess.log): its number, the cells it served, its size, whether it starts afresh
            with open(os.path.join(GEN, "kqsess.log"), "a") as lg:
                lg.write(f"s{i} {served} {mb} {'again' if again else 'kept'}\n")
            if again:
                stop(p)
                p = None

if __name__ == "__main__":
    main()
