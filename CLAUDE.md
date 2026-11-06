# Rocq-CertiRocq-C — instructions for a session working here

**Read `Rocq-C-solution.md` first** ("READ THIS FIRST", §0 in full with §0.9 and §0.10, §10, §12, §13).  It is the complete record:
the goal, the architecture, every settled decision, every measurement and trap, and the ordered plan.  Do not re-derive what is
in it.

## THE GOAL IS COMPLETENESS — STRICTLY.  NO NARROWER SUBSTITUTE IS EVER "DONE".

The goal (§0): ordinary Rocq compiled to freestanding C at C speed, everything that is logic proved, only the hardware assumed —
and **nothing refused except the four reasons of §0.5** (a value allocated behind the programmer's back that outlives the call,
an unbounded number, two versions of the memory both used, a constant Rocq itself gives no meaning to).  Every other refusal of a correct,
ordinary program is a gap.

This is not a preference.  It is the measure every step is judged by:

1. **A construct is done only in its general form**: accepted in every place and with every type it can appear (§3.1: former ×
   place × type), not only in the shape of the cell that motivated it.  If the design of a step says "general" and what gets built
   is narrower ("only at the entry", "only in this order", "only one level", "not with a memory", "not inside an expression"),
   **the step is not done**.  Do not report it done, do not record it as done in the md, do not move on to the next item as if it
   were.  Keep building until the general form is accepted, or stop and say plainly that it is unfinished and why.
2. **"Not in this step" is a debt, not a scope.**  Every place a step leaves unread must get a cell in the construct table
   (`proved/matrix/gen.py`) in the same commit, so the table shows it as a gap.  A limit written in prose closes nothing (§3.6).
3. **"0 gaps" is a claim about the table's cells only.**  Never state completeness without saying what the table covers; never
   let the table's count stand in for completeness while known unread places have no cell.
4. **A boundary is "by design" only with a pin and a control** (§3.6): a cell refused for one of §0.5's reasons, shown in its
   own text, next to the nearest cell that is accepted.  Never because of a value's type.
5. **Soundness first, then completeness, then generality, then speed, then proof time** (§0.9).  A narrower step being sound does
   not make it complete.
6. If the general form is genuinely blocked (needs a new assumption, a decision of the owner, a change to a settled decision of
   §10), **stop and ask the owner** — do not land a substitute and call it the decision (§13.8, F36).

## WHAT MAY BE ASSUMED: ONLY WHAT HAS NO DEFINITION EXCEPT THE MACHINE (§0.3, D29, F66)

**Before writing anything that is not proved, ask: does it have a definition other than the machine?**  If Rocq can state what it computes,
it is logic: write it in Rocq and prove it.  A CPU having an instruction for it does not make it hardware.  "Trusted" and "hardware" are
different words: C written here that nobody proved is trusted, and it is this work's to prove.  About Rocq's own primitives assume its axioms
and kernel and nothing more; where they are silent add no fact (a closed term is computed, a test in the text rules the case out, otherwise a
refusal with that reason).

Any change to what is assumed (an `Axiom` or `Parameter`, `hwop`, `hwfop`, a body in `hw/kq_hw.h`, a line of `proved/TRUSTED.txt`) stops the
step and goes to the owner before any commit; "no need to wait" does not cover it.  `proved/check_trust.py` compares the list with the tree and
with the gate's log; chains and pushes stop on a difference.  Say what is true: today the proof ends at Clight, under that list.

## How a step is done (§13.2, §13.7)

- Record the step's design in `Rocq-C-solution.md` §12.V and commit it **before** building.
- Build it in its general form; add construct-table cells for every place and type the construct can appear in.
- The gate on the work machine, the walk switched off: `make.sh` `core-ok`, examples, corpus, the five kernels, every program
  through the verified compiler, none refused; the C of every program byte-identical (or a measured reason); the construct table
  re-run; `proved/check_trust.py --gate LOG`: `ASSUME=1 make.sh` lists what `proved/TRUSTED.txt` lists and nothing more.  A program moved to the verified compiler is timed
  against the translator's build (F49); a reifier change that touches the helpers or the call sites is timed on the kernels'
  programs (F58).
- Record the result in §12.V with the numbers that ran, then push.

## Process rules (owner's, standing)

- Commits are authored by the owner only (set the author per command, `git -c user.name=.. -c user.email=..`), **no co-author
  trailer, no narration** (D19).
- After a step is done (gate passed, md record committed, privacy scan clean): push to `origin main` and continue — no need to ask.
  Never push a step whose gate failed or did not run.
- The repository is public: no host names, addresses, user names, local paths or keys in it.  Scan every diff before committing.
- Heavy runs one at a time, every container memory-capped with `--ulimit core=0`, never `ulimit -v` (§13.3).
