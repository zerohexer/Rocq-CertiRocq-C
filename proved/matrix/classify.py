#!/usr/bin/env python3
"""classify.py RESULTS... : the construct table's verdict for every cell, from the output of kitc.py (one line per cell).

Each cell is `ok` (translated and proved), `design` (refused because the value would be allocated behind the programmer's
back, or a memory used after it was handed on: what a runtime-free language cannot do), `invalid` (the generated program
is not Rocq: no verdict) or `gap` (runtime-free, not yet translated or proved), with the category of the gap.
Prints the summary and, with --md FILE, writes the table."""
import re, sys, collections

# cells whose refusal is by design.  A cell belongs here only if its program shows the cause: a value whose size comes from
# the data (a list built by recursion), a value that must outlive the call where it cannot be put in (a closure returned by a
# recursive function), two versions of the memory both used, differing in cells whose number comes from the data.  Each needs a control: the nearest accepted cell that
# differs only in the cause.  The cells once listed here (option, sum, a list cell, a function in a pair, a function returned,
# a dead memory let) build and take apart their value in place, so they are gaps.
DESIGN_CELLS = {
  # a counter grown by the recursion's predecessor, from the data (kq_nat, up to 2^60): it reaches about n^2/2, beyond a machine
  # number -- an unbounded number (Rocq-C-solution.md §0.5, second reason); control: A_par_nat_rec_add_pred_lit, the same
  # function from a written budget, translated and proved (step 39)
  "A_par_nat_rec_add_pred",
  # two versions of the memory both used, differing in cells whose number comes from the data: each call a prefix sum in place
  # over n cells, both given the memory before both -- keeping the old one takes a copy or a log as long as the data
  # (Rocq-C-solution.md §0.5, third reason); control: A_par_write_two_seq, the same two calls with the memory handed on (step 49)
  "A_par_write_two_data",
  # the same, a memory made in place and read inside an expression: the two reads each from its own version, both from s; a read of
  # one version written into the other (§0.5, third reason); control: A_par_made_seq, the memory handed on (step 52)
  "A_par_made_two",
  "A_par_made_old_write",
  # the same, two memory parameters: read from one, written in the other, handed apart at each round; given two versions by the call;
  # control: A_par_mem2_live_control, one memory (step 53)
  "A_par_mem2_live",
  "A_par_mem2_live_given",
  # a constant with no body in Rocq's kernel: an Axiom, a Parameter, a function behind a module's ":".  Rocq cannot run it and nothing
  # says what it computes, so no theorem can say the C does (Rocq-C-solution.md §0.5, fourth reason); control: A_mod_ascribe, the
  # same function behind "<:", which keeps its body, and A_par_int, a Definition in the Parameter's place (step 51)
  "A_mod_sealed",
  "A_mod_sealed_helper",
  "A_mod_parameter",
  # a plain access to a block listed in kq_shared: the sequential meaning describes the program only if it reaches a shared block
  # through marked operations (§9.4), wherever the list stands; control: A_mod_shared, A_file_shared, a plain access to another block
  "A_mod_shared_plain",
  "A_file_shared_plain",
}
# gaps whose refusal message is shared with another category: classified by name
BY_NAME = {
  "A_par_own_opnd_choice": "the function's own call where it cannot be lifted out of the fixpoint: in a let of a pair used bare, in an operand under a choice",
  "A_par_pm_let_own": "the function's own call where it cannot be lifted out of the fixpoint: in a let of a pair used bare, in an operand under a choice",
  **{c: "a second memory parameter: never read, but given another memory by the call or by the recursion; beside a pair parameter; never read, in a copy or a mutual block"
     for c in ("A_par_mem2_dead_other", "A_par_mem2_dead_moved", "A_par_mem2_dead_pair_param", "A_par_mem2_hand_on_pair_param",
               "A_par_mem2_tmpl_dead", "A_par_mem2_lfix_dead", "A_par_mem2_mutual_moved")},
  "A_par_write_two": "two versions of the memory both used, differing in cells fixed by the text (their old values saved and put back)",
  "A_par_write_in_mem": "two versions of the memory both used, differing in cells fixed by the text (their old values saved and put back)",
  "P_mem_both": "two versions of the memory both used, differing in cells fixed by the text (their old values saved and put back)",
  "A_par_old_read_index": "two versions of the memory both used, differing in cells fixed by the text (their old values saved and put back)",
  "A_par_option": "a value built and taken apart in place (option, sum, a list cell, a function in a pair)",
  "A_par_sum": "a value built and taken apart in place (option, sum, a list cell, a function in a pair)",
  "A_par_list": "a value built and taken apart in place (option, sum, a list cell, a function in a pair)",
  "A_par_fun_in_pair": "a value built and taken apart in place (option, sum, a list cell, a function in a pair)",
  "P_mem_dup": "a memory made by a let that is never used, the old one used after it",
}
INVALID = re.compile(r"Cannot guess decreasing|Unable to unify|not found in the current environment|The reference .* was not found|Syntax error")

# (regex on the refusal, category), tried in order
GAP = [
  (r"PROOF FAILED", "a proof the tactics do not find (the translation was accepted)"),
  (r"must name no variable of the caller", "a function given that names a variable of the caller (a closure)"),
  (r"a let of a type this translator does not read", "a local function, a polymorphic or class-based helper, a memory inside a record"),
  (r"not a test this translator reads", "a boolean made by an if or a match"),
  (r"parameters or result are not of a kind", "a recursive function giving back a record of three numbers, or giving back or taking an option"),
  (r"a match used as a (number|memory) that this translator does not read", "a match on a counter that is not a recursion"),
  (r"not a counter this translator reads|not a test: (eqb|ltb)", "arithmetic or a comparison on counters"),
  (r"a match this translator does not read", "a pair of a number and a memory"),
  (r"not a record this translator reads", "a choice between records"),
]

def cells(paths):
    for p in paths:
        for line in open(p):
            line = line.strip()
            if not line:
                continue
            name = line.split()[0]
            yield name, line

def classify(name, line):
    if " PROVED " in line or line.split()[1:2] == ["PROVED"]:
        return "ok", ""
    if name in DESIGN_CELLS:
        return "design", ""
    if INVALID.search(line):
        return "invalid", ""
    if name in BY_NAME:
        return "gap", BY_NAME[name]
    # refused by the verified compiler (step 29: the walk retired): the reifier's reasons
    m = re.search(r"not read by the verified compiler's reifier \((.*?)\); refused", line)
    if m:
        return "gap", "not read by the verified compiler: " + m.group(1)[:120]
    for rx, cat in GAP:
        if re.search(rx, line):
            return "gap", cat
    return "gap", "unclassified: " + line[len(name):][:100]

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    md = None
    if "--md" in sys.argv:
        md = sys.argv[sys.argv.index("--md") + 1]
        args = [a for a in args if a != md]
    tally = collections.Counter()
    gaps = collections.defaultdict(list)
    design, invalid = [], []
    for name, line in cells(args):
        c, cat = classify(name, line)
        tally[c] += 1
        if c == "gap":
            gaps[cat].append(name)
        elif c == "design":
            design.append(name)
        elif c == "invalid":
            invalid.append(name)
    total = sum(tally.values())
    out = [f"{total} cells: {tally['ok']} translated and proved, {tally['design']} refused by design, "
           f"{tally['gap']} gaps, {tally['invalid']} not Rocq (no verdict)"]
    for cat, ns in sorted(gaps.items(), key=lambda kv: -len(kv[1])):
        out.append(f"\ngap ({len(ns)}): {cat}\n  " + " ".join(sorted(ns)))
    if design:
        out.append("\nby design: " + " ".join(sorted(design)))
    if invalid:
        out.append("\nnot Rocq: " + " ".join(sorted(invalid)))
    text = "\n".join(out)
    print(text)
    if md:
        open(md, "w").write("# The construct table\n\n```\n" + text + "\n```\n")

if __name__ == "__main__":
    main()
