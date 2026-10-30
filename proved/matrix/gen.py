#!/usr/bin/env python3
"""gen.py OUTDIR : the construct matrix.  Writes one program (OUTDIR/ID.body) for every cell of the matrix and a table
(OUTDIR/cells.tsv: id, family, what).

The matrix is built from the language's constructs, not from sample programs:
  family P: every way of PRODUCING a value of each result kind (a function f of type nat -> int -> int -> mem -> K),
            and the function that uses it ("go"), so each cell is a producer meeting its consumer;
  family A: every kind of PARAMETER a function can take, passed on to a helper and used;
  family N: every ordered nesting of the constructs of a small core (a context three deep), so that a construct is met
            inside every other one, in every order.
Each program defines `go : nat -> int -> int -> mem -> int` and `main` that applies it."""
import sys, os, itertools

PRE = """Record r3 := mk3 { f1 : int; f2 : int; f3 : int }.
Definition h (a b : int) : int := a * 2 + b.
Definition hp (a b : int) : int * int := (a + b, a - b).
Definition hb (a b : int) : bool := a <? b.
Definition hm (a b : int) (s : mem) : mem := upd 0 a b s.
Definition hr (a b : int) : r3 := mk3 a b (a + b).
Definition twice (f : int -> int) (x : int) : int := f (f x).
Fixpoint fold (n : nat) (i acc : int) (f : int -> int -> int) : int :=
  match n with O => acc | S m => fold m (i + 1) (f i acc) f end.
"""

MAIN = """Definition main : int :=
  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in
  go (kq_nat (kq_arg 0)) (kq_arg 1) (kq_arg 2) (kq_input 0).
"""

SIG = "(n : nat) (a b : int) (s : mem)"

# consumers: how go uses the result of f
CONS = {
  "int":    "f n a b s",
  "bool":   "if f n a b s then 1 else 0",
  "pair":   "let '(x, y) := f n a b s in x + y",
  "rec3":   "let w := f n a b s in f1 w + f2 w + f3 w",
  "intmem": "let '(x, s2) := f n a b s in x + rd 0 0 s2",
  "mem":    "rd 0 0 (f n a b s)",
  "pairp":  "let '(p, z) := f n a b s in let '(x, y) := p in x + y + z",
  "none":   None,
}
TY = {"int": "int", "bool": "bool", "pair": "int * int", "rec3": "r3", "intmem": "int * mem", "mem": "mem",
      "pairp": "(int * int) * int"}

def fdef(k, body):            # a function f of result kind k
    return f"Definition f {SIG} : {TY[k]} :=\n  {body}.\n"

def ffix(k, body):            # a recursive function f, the counter first
    return f"Fixpoint f {SIG} : {TY[k]} :=\n  {body}.\n"

P = []   # (id, kind, text-before-go)
def add(i, k, text, pre=""):
    P.append((i, k, pre + text))

# ---------------------------------------------------------------- producers, by result kind
# int
add("int_lit", "int", fdef("int", "7"))
add("int_arith", "int", fdef("int", "a * 3 + b - (a land b)"))
add("int_let", "int", fdef("int", "let x := a + 1 in let y := x * b in x + y"))
add("int_let2", "int", fdef("int", "let x := a + 1 in let x := x * 2 in x"))
add("int_if", "int", fdef("int", "if a <? b then a else b"))
add("int_if_and", "int", fdef("int", "if (a <? b) && (b <? 100) then a else b"))
add("int_if_or", "int", fdef("int", "if (a <? b) || (b =? 5) then a else b"))
add("int_if_not", "int", fdef("int", "if negb (a <? b) then a else b"))
add("int_if_let", "int", fdef("int", "let c := a <? b in if c then a else b"))
add("int_if_let_twice", "int", fdef("int", "let c := a <? b in if c then (if c then a else 0) else b"))
add("int_if_chain", "int", fdef("int", "if a <? 0 then 1 else if a <? 10 then 2 else if a <? 100 then 3 else 4"))
add("int_if_nested", "int", fdef("int", "if a <? b then (if a <? 0 then 1 else 2) else (if b <? 0 then 3 else 4)"))
add("int_if_arg", "int", fdef("int", "h (if a <? b then a else b) 1"))
add("int_if_in_arith", "int", fdef("int", "1 + (if a <? b then a else b) * 2"))
add("int_match_bool", "int", fdef("int", "match a <? b with true => a | false => b end"))
add("int_match_nat", "int", fdef("int", "match n with O => a | S _ => b end"))
add("int_match_nat2", "int", fdef("int", "match n with O => a | S O => b | S (S _) => a + b end"))
add("int_beta", "int", fdef("int", "(fun x => x + b) a"))
add("int_beta2", "int", fdef("int", "(fun x y => x * y) a b"))
add("int_lam_let", "int", fdef("int", "let g := fun x => x + b in g a"))
add("int_lam_let_twice", "int", fdef("int", "let g := fun x => x + b in g (g a)"))
add("int_lam_let_noncapt", "int", fdef("int", "let g := fun x => x + 1 in g (g a)"))
add("int_call_helper", "int", fdef("int", "h a b"))
add("int_call_helper_arith", "int", fdef("int", "h a b + h b a"))
add("int_call_helper_nest", "int", fdef("int", "h (h a b) (h b a)"))
add("int_call_helper_let", "int", fdef("int", "let x := h a b in x + x"))
add("int_hof_const", "int", fdef("int", "twice (fun z => z + 1) a"))
add("int_hof_capture", "int", fdef("int", "twice (fun z => z + b) a"))
add("int_hof_capture_let", "int", fdef("int", "let k := b * 2 in twice (fun z => z + k) a"))
add("int_hof_named", "int", fdef("int", "twice (h b) a"))
add("int_hof_passed", "int", fdef("int", "let g := fun z => z + 1 in twice g a"))
add("int_fold_const", "int", fdef("int", "fold n 0 a (fun i acc => acc + i)"))
add("int_fold_capture", "int", fdef("int", "fold n 0 a (fun i acc => acc + i * b)"))
add("int_fold_mem", "int", fdef("int", "fold n 0 a (fun i acc => acc + rd 0 i s)"))
add("int_fold_capt2", "int", fdef("int", "fold n 0 a (fun i acc => acc + i * b + rd 0 i s)"))
add("int_fold_capt_let", "int", fdef("int", "let k := a + b in fold n 0 a (fun i acc => acc + i + k)"))
add("int_fold_capt_twice", "int", fdef("int", "fold n 0 (fold n 0 a (fun i acc => acc + b)) (fun i acc => acc * 2 + a)"))
add("int_outer_capt", "int", fdef("int", "outer n a (fun i acc => acc + i * b)"),
    "Fixpoint outer (r : nat) (acc : int) (f : int -> int -> int) : int :=\n  match r with O => acc | S r' => outer r' (fold 3 0 acc f) f end.\n")
add("mem_fill_capt", "mem", fdef("mem", "fill n 0 (fun i => i + b) s"),
    "Fixpoint fill (n : nat) (i : int) (f : int -> int) (s : mem) : mem :=\n  match n with O => s | S m => fill m (i + 1) f (upd 0 i (f i) s) end.\n")
add("int_rd", "int", fdef("int", "rd 0 a s"))
add("int_rd_arith", "int", fdef("int", "rd 0 a s + rd 0 b s"))
add("int_rd_if", "int", fdef("int", "if rd 0 a s <? rd 0 b s then 1 else 2"))
add("int_wr_rd", "int", fdef("int", "let s := upd 0 a b s in rd 0 a s"))
add("int_wr_rd2", "int", fdef("int", "let s := upd 0 a b s in let s := upd 0 b a s in rd 0 a s + rd 0 b s"))
add("int_wr_helper", "int", fdef("int", "rd 0 a (hm a b s)"))
add("int_pair_destr", "int", fdef("int", "let '(x, y) := (a, b) in x + y"))
add("int_pair_call", "int", fdef("int", "let '(x, y) := hp a b in x * y"))
add("int_pair_fst", "int", fdef("int", "fst (hp a b)"))
add("int_pair_snd", "int", fdef("int", "snd (a, b)"))
add("int_rec_call", "int", fdef("int", "let w := hr a b in f1 w + f2 w + f3 w"))
add("int_match_pair", "int", fdef("int", "match hp a b with (x, y) => x - y end"))
add("int_tail_rec", "int", ffix("int", "match n with O => a | S m => f m (a + b) b s end"))
add("int_tail_rec_if", "int", ffix("int", "match n with O => a | S m => if a <? b then f m (a + 1) b s else f m a (b + 1) s end"))
add("int_tail_rec_mem", "int", ffix("int", "match n with O => a | S m => f m (a + rd 0 a s) b s end"))
add("int_nontail", "int", ffix("int", "match n with O => a | S m => 1 + f m a b s end"))
add("int_nontail_mul", "int", ffix("int", "match n with O => 1 | S m => a * f m a b s end"))
add("int_nontail_twice", "int", ffix("int", "match n with O => a | S m => f m a b s + f m (a + 1) b s end"))
add("int_nontail_let", "int", ffix("int", "match n with O => a | S m => let r := f m a b s in r + r end"))
add("int_nontail_arg", "int", ffix("int", "match n with O => a | S m => h (f m a b s) 1 end"))
add("int_nontail_if", "int", ffix("int", "match n with O => a | S m => if a <? b then 1 + f m (a + 1) b s else f m a b s end"))
add("int_mutual", "int", "Fixpoint ev (n : nat) (a : int) : int := match n with O => a | S m => od m (a + 1) end\nwith od (n : nat) (a : int) : int := match n with O => a * 2 | S m => ev m (a + 2) end.\n" + fdef("int", "ev n a"))
add("int_local_fix", "int", fdef("int", "let fix g (m : nat) (x : int) : int := match m with O => x | S k => g k (x + b) end in g n a"))
add("int_local_fun_multi", "int", fdef("int", "let g := fun x => x + b in if a <? b then g a else g b"))
add("int_proj_record", "int", fdef("int", "f1 (hr a b) + f3 (hr b a)"))
add("int_bool_ops", "int", fdef("int", "if hb a b then 1 else 0"))
add("int_bool_let", "int", fdef("int", "let c := hb a b in let d := hb b a in if c && d then 1 else if c || d then 2 else 3"))
add("int_bool_call_arg", "int", fdef("int", "if hb a b && hb b 10 then 1 else 0"))
add("int_w64", "int", fdef("int", "u64_to_int (u64_add (u64_of_int a) (u64_of_int b))"))
add("int_shift", "int", fdef("int", "((a << 3) lor (b >> 2)) lxor (a land 255)"))
add("int_cmp_chain", "int", fdef("int", "(if a <? b then 1 else 0) + (if a <=? b then 2 else 0) + (if a =? b then 4 else 0)"))
add("int_div", "int", fdef("int", "a / (b lor 1) + a mod (b lor 1)"))
add("int_deep_let", "int", fdef("int", "let a1 := a + 1 in let a2 := a1 + 1 in let a3 := a2 + 1 in let a4 := a3 + 1 in let a5 := a4 + 1 in let a6 := a5 + 1 in a6 + a1"))
# bool
add("bool_cmp", "bool", fdef("bool", "a <? b"))
add("bool_and", "bool", fdef("bool", "(a <? b) && (b <? 100)"))
add("bool_not", "bool", fdef("bool", "negb (a =? b)"))
add("bool_if", "bool", fdef("bool", "if a <? b then true else false"))
add("bool_if_call", "bool", fdef("bool", "if a <? b then hb a b else hb b a"))
add("bool_call", "bool", fdef("bool", "hb a b"))
add("bool_let", "bool", fdef("bool", "let c := a <? b in c && (b <? 10)"))
add("bool_rd", "bool", fdef("bool", "rd 0 a s =? b"))
add("bool_match_nat", "bool", fdef("bool", "match n with O => true | S _ => false end"))
add("bool_tail_rec", "bool", ffix("bool", "match n with O => a <? b | S m => f m (a + 1) b s end"))
add("bool_rec_search", "bool", ffix("bool", "match n with O => false | S m => if rd 0 a s =? b then true else f m (a + 1) b s end"))
add("bool_nontail_or", "bool", ffix("bool", "match n with O => false | S m => (a =? b) || f m (a + 1) b s end"))
add("bool_nontail_and", "bool", ffix("bool", "match n with O => true | S m => (a <? b) && f m (a + 1) b s end"))
add("bool_const", "bool", fdef("bool", "true"))
# pair
add("pair_lit", "pair", fdef("pair", "(a, b)"))
add("pair_arith", "pair", fdef("pair", "(a + b, a - b)"))
add("pair_let", "pair", fdef("pair", "let x := a + 1 in (x, x * b)"))
add("pair_if", "pair", fdef("pair", "if a <? b then (a, b) else (b, a)"))
add("pair_if_inside", "pair", fdef("pair", "(if a <? b then a else b, if a <? b then b else a)"))
add("pair_call", "pair", fdef("pair", "hp a b"))
add("pair_call_swap", "pair", fdef("pair", "let '(x, y) := hp a b in (y, x)"))
add("pair_call_arith", "pair", fdef("pair", "let '(x, y) := hp a b in (x + 1, y * 2)"))
add("pair_match_destr", "pair", fdef("pair", "match hp a b with (x, y) => (y, x) end"))
add("pair_rd", "pair", fdef("pair", "(rd 0 a s, rd 0 b s)"))
add("pair_tail_rec", "pair", ffix("pair", "match n with O => (a, b) | S m => f m b (a + b) s end"))
add("pair_nontail", "pair", ffix("pair", "match n with O => (0, 1) | S m => let '(x, y) := f m a b s in (y, x + y) end"))
add("pair_nontail_if", "pair", ffix("pair", "match n with O => (a, b) | S m => let '(x, y) := f m a b s in if x <? y then (x, y + 1) else (y, x) end"))
add("pair_proj_pair", "pair", fdef("pair", "let p := hp a b in (snd p, fst p)"))
add("pair_pass_through", "pair", fdef("pair", "let p := hp a b in p"))
add("pair_unit_mix", "pair", fdef("pair", "(a, 0)"))
add("pair_cons_of_rec", "pair", fdef("pair", "let w := hr a b in (f1 w, f3 w)"))
# nested pair
add("pairp_lit", "pairp", fdef("pairp", "((a, b), a + b)"))
add("pairp_let", "pairp", fdef("pairp", "let p := (a, b) in (p, a * b)"))
add("pairp_call", "pairp", fdef("pairp", "(hp a b, a)"))
add("pairp_rec", "pairp", ffix("pairp", "match n with O => ((a, b), 0) | S m => let '(p, z) := f m a b s in let '(x, y) := p in ((y, x), z + 1) end"))
# record of three
add("rec3_lit", "rec3", fdef("rec3", "mk3 a b (a + b)"))
add("rec3_call", "rec3", fdef("rec3", "hr a b"))
add("rec3_let", "rec3", fdef("rec3", "let x := a + b in mk3 x x (x * 2)"))
add("rec3_if", "rec3", fdef("rec3", "if a <? b then mk3 a b 0 else mk3 b a 1"))
add("rec3_update", "rec3", fdef("rec3", "let w := hr a b in mk3 (f1 w) (f2 w + 1) (f3 w)"))
add("rec3_tail_rec", "rec3", ffix("rec3", "match n with O => mk3 a b 0 | S m => f m b (a + b) s end"))
add("rec3_nontail", "rec3", ffix("rec3", "match n with O => mk3 a b 0 | S m => let w := f m a b s in mk3 (f2 w) (f1 w + f2 w) (f3 w + 1) end"))
add("rec3_pass", "rec3", fdef("rec3", "let w := hr a b in w"))
add("rec3_match", "rec3", fdef("rec3", "match hr a b with mk3 x y z => mk3 z y x end"))
# value and memory
add("intmem_lit", "intmem", fdef("intmem", "(a, s)"))
add("intmem_wr", "intmem", fdef("intmem", "(rd 0 a s, upd 0 a b s)"))
add("intmem_let", "intmem", fdef("intmem", "let s2 := upd 0 a b s in (rd 0 a s2, s2)"))
add("intmem_if", "intmem", fdef("intmem", "if a <? b then (a, upd 0 a b s) else (b, s)"))
add("intmem_call", "intmem", fdef("intmem", "(h a b, hm a b s)"))
add("intmem_tail_rec", "intmem", ffix("intmem", "match n with O => (a, s) | S m => f m (a + 1) b (upd 0 a b s) end"))
add("intmem_nontail", "intmem", ffix("intmem", "match n with O => (a, s) | S m => let '(x, s2) := f m a b s in (x + 1, upd 0 x b s2) end"))
add("intmem_alloc_like", "intmem", fdef("intmem", "let p := rd 0 0 s in (p, upd 0 0 (p + 1) s)"))
# memory
add("mem_wr", "mem", fdef("mem", "upd 0 a b s"))
add("mem_wr2", "mem", fdef("mem", "upd 0 b a (upd 0 a b s)"))
add("mem_let", "mem", fdef("mem", "let s := upd 0 a b s in let s := upd 0 b a s in s"))
add("mem_if", "mem", fdef("mem", "if a <? b then upd 0 a b s else s"))
add("mem_if_both", "mem", fdef("mem", "if a <? b then upd 0 a b s else upd 0 b a s"))
add("mem_call", "mem", fdef("mem", "hm a b s"))
add("mem_call_twice", "mem", fdef("mem", "hm b a (hm a b s)"))
add("mem_rmw", "mem", fdef("mem", "upd 0 a (rd 0 a s + b) s"))
add("mem_match_nat", "mem", fdef("mem", "match n with O => s | S _ => upd 0 a b s end"))
add("mem_tail_rec", "mem", ffix("mem", "match n with O => s | S m => f m (a + 1) b (upd 0 a b s) end"))
add("mem_nontail", "mem", ffix("mem", "match n with O => s | S m => upd 0 a b (f m a b s) end"))
add("mem_nontail_helper", "mem", ffix("mem", "match n with O => s | S m => hm a b (f m (a + 1) b s) end"))
add("mem_two_blocks", "mem", fdef("mem", "upd 1 b a (upd 0 a b s)"))
add("mem_u8", "mem", fdef("mem", "upd8 0 a b s"))
add("mem_u32", "mem", fdef("mem", "upd32 0 a b s"))
add("mem_grow", "mem", fdef("mem", "kq_grow 2 a s"))
add("mem_dup", "mem", fdef("mem", "let t := upd 0 a b s in upd 0 b a s"))      # old memory used after being handed on
add("mem_hof", "mem", fdef("mem", "twice_m (fun t => upd 0 a b t) s"), "Definition twice_m (f : mem -> mem) (s : mem) : mem := f (f s).\n")

# ---------------------------------------------------------------- family A: parameters
A = []
def addA(i, params, call, helper):
    A.append((i, helper + f"Definition go {SIG} : int :=\n  {call}.\n"))
addA("par_int", "", "k a b", "Definition k (x y : int) : int := x + y.\n")
addA("par_bool", "", "k (a <? b) a", "Definition k (c : bool) (x : int) : int := if c then x else 0.\n")
addA("par_bool_twice", "", "k (a <? b) a", "Definition k (c : bool) (x : int) : int := if c then (if c then x else 1) else 2.\n")
addA("par_bool_negb", "", "k (a <? b) a", "Definition k (c : bool) (x : int) : int := if negb c then x else 0.\n")
addA("par_bool_pass", "", "k (a <? b) a", "Definition k2 (c : bool) (x : int) : int := if c then x else 0.\nDefinition k (c : bool) (x : int) : int := k2 c (x + 1).\n")
addA("par_bool_and", "", "k (a <? b) (b <? 10)", "Definition k (c d : bool) : int := if c && d then 1 else 0.\n")
addA("par_pair", "", "k (a, b)", "Definition k (p : int * int) : int := fst p + snd p.\n")
addA("par_pair_destr", "", "k (a, b)", "Definition k (p : int * int) : int := let '(x, y) := p in x * y.\n")
addA("par_pair_match", "", "k (a, b)", "Definition k (p : int * int) : int := match p with (x, y) => x - y end.\n")
addA("par_pair_pass", "", "k (a, b)", "Definition k2 (p : int * int) : int := fst p.\nDefinition k (p : int * int) : int := k2 p + snd p.\n")
addA("par_pair_ret", "", "let '(x, y) := k (a, b) in x + y", "Definition k (p : int * int) : int * int := (snd p, fst p).\n")
addA("par_pair_nested", "", "k ((a, b), a)", "Definition k (p : (int * int) * int) : int := fst (fst p) + snd (fst p) + snd p.\n")
addA("par_record", "", "k (mk3 a b 1)", "Definition k (w : r3) : int := f1 w + f2 w + f3 w.\n")
addA("par_record_pass", "", "k (hr a b)", "Definition k (w : r3) : int := f3 w.\n")
addA("par_record_ret", "", "f2 (k (mk3 a b 1))", "Definition k (w : r3) : r3 := mk3 (f2 w) (f1 w) 0.\n")
addA("par_fun_const", "", "k (fun x => x + 1) a", "Definition k (g : int -> int) (x : int) : int := g (g x).\n")
addA("par_fun_capture", "", "k (fun x => x + b) a", "Definition k (g : int -> int) (x : int) : int := g (g x).\n")
addA("par_fun_name", "", "k h2 a", "Definition h2 (x : int) : int := x * 3.\nDefinition k (g : int -> int) (x : int) : int := g (g x).\n")
addA("par_fun_pass", "", "k (fun x => x + 1) a", "Definition k2 (g : int -> int) (x : int) : int := g x.\nDefinition k (g : int -> int) (x : int) : int := k2 g (g x).\n")
addA("par_fun2", "", "k (fun x y => x * y) a b", "Definition k (g : int -> int -> int) (x y : int) : int := g x (g y x).\n")
addA("par_fun_store", "", "k (fun x => x + 1) a", "Definition k (g : int -> int) (x : int) : int := let r := g x in r + r.\n")
addA("par_fun_result", "", "(k a) b", "Definition k (x : int) : int -> int := fun y => x + y.\n")
addA("par_fun_in_pair", "", "k (a, fun x => x + 1)", "Definition k (p : int * (int -> int)) : int := (snd p) (fst p).\n")
addA("par_fun_rec", "", "fold n 0 a (fun i acc => acc + i)", "")
addA("par_fun_rec_pass", "", "k n a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (twice (fun z => z + 1) x) end.\n")
addA("par_nat", "", "k n a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\n")
addA("par_nat_two", "", "k n n a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p m (x + 1) end.\n")
addA("par_nat_arith", "", "k n a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k (m + 0) (x + 1) end.\n")
addA("par_nat_mul", "", "k (n + n) a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\n")
addA("par_nat_pred", "", "k (Nat.pred n) a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\n")
addA("par_nat_ltb", "", "if Nat.ltb n 10 then a else b", "")
addA("par_nat_eqb", "", "if Nat.eqb n 3 then a else b", "")
addA("par_nat_to_int", "", "int_of_nat n", "Definition int_of_nat (n : nat) : int := match n with O => 0 | S _ => 1 end.\n")
addA("par_mem", "", "rd 0 0 (k s)", "Definition k (t : mem) : mem := upd 0 0 5 t.\n")
addA("par_mem_two", "", "rd 0 0 (k s s)", "Definition k (t u : mem) : mem := upd 0 0 5 t.\n")
addA("par_mem_pair", "", "let '(x, t) := k (a, s) in x + rd 0 0 t", "Definition k (p : int * mem) : int * mem := (fst p + 1, snd p).\n")
addA("par_mem_record", "", "k s a", "Record ms := mkms { mv : int; mm : mem }.\nDefinition k (t : mem) (x : int) : int := mv (mkms x t).\n")
addA("par_option", "", "match k a with Some x => x | None => 0 end", "Definition k (x : int) : option int := if x <? 0 then None else Some x.\n")
addA("par_list", "", "match k a with nil => 0 | cons x _ => x end", "Definition k (x : int) : list int := cons x nil.\n")
addA("par_sum", "", "match k a with inl x => x | inr y => y end", "Definition k (x : int) : int + int := if x <? 0 then inl x else inr x.\n")
# a boolean as a parameter and a result of a recursive function; a number and a memory given back by a recursive function and
# taken apart by [fst]/[snd]; an option given back by a recursive function and as a loop's state (its tag and its field)
addA("par_bool_rec", "", "k n (a <? b) a", "Fixpoint k (n : nat) (c : bool) (x : int) : int := match n with O => x | S m => k m (negb c) (if c then x + 1 else x) end.\n")
addA("par_bool_rec_negb", "", "if k n a then a else b", "Fixpoint k (n : nat) (x : int) : bool := match n with O => x <? 3 | S m => negb (k m (x + 1)) end.\n")
addA("par_mem_pair_rec", "", "let r := k n a s in fst r + rd 0 0 (snd r)", "Fixpoint k (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => k m (x + 1) (upd 0 x x t) end.\n")
addA("par_option_rec", "", "match k n a with Some y => y | None => 0 end", "Fixpoint k (n : nat) (x : int) : option int := match n with O => None | S m => if x =? 5 then Some x else k m (x + 1) end.\n")
addA("par_option_state", "", "k n a None", "Fixpoint k (n : nat) (x : int) (o : option int) : int := match n with O => match o with Some y => y | None => x end | S m => k m (x + 1) (if x =? 3 then Some x else o) end.\n")
addA("par_unit", "", "k tt a", "Definition k (u : unit) (x : int) : int := x.\n")
addA("par_prop_arg", "", "k a", "Definition k (x : int) : int := x.\n")
addA("par_poly_id", "", "pid a", "Definition pid {A : Type} (x : A) : A := x.\n")
addA("par_poly_pair", "", "pfst (a, b)", "Definition pfst {A B : Type} (p : A * B) : A := fst p.\n")
addA("par_poly_hof", "", "pmap (fun x => x + 1) a", "Definition pmap {A B : Type} (g : A -> B) (x : A) : B := g x.\n")
addA("par_typeclass", "", "cadd a b", "Class Ad (A : Type) := { ad : A -> A -> A }.\n#[export] Instance adint : Ad int := {| ad := fun x y => x + y |}.\nDefinition cadd {A} `{Ad A} (x y : A) : A := ad x y.\n")
addA("par_dep_record", "", "k a", "Record bnd := mkb { bv : int; bok : True }.\nDefinition k (x : int) : int := bv (mkb x I).\n")
addA("par_string", "", "a", "")
addA("par_float", "", "a", "")

# ---------------------------------------------------------------- family N: every nesting of a small core
# contexts with a hole (HOLE) of result kind int; the core is a producer of int
CTX = {
  "let":   "let x := HOLE in x + x",
  "if":    "if a <? b then HOLE else b",
  "arith": "HOLE * 3 + 1",
  "pair":  "let '(p, q) := (HOLE, b) in p - q",
  "call":  "h HOLE b",
  "fun":   "(fun z => z + a) (HOLE)",
  "match": "match n with O => HOLE | S _ => a end",
  "rd":    "rd 0 (HOLE land 7) s",
}
CORE = {"var": "a", "arith": "a + b", "rd": "rd 0 a s", "call": "h a b"}

def nest(names):
    t = CORE["arith"]
    for c in reversed(names):
        t = CTX[c].replace("HOLE", "(" + t + ")")
    return t

N = []
names = sorted(CTX)
for depth in (1, 2, 3):
    for combo in itertools.product(names, repeat=depth):
        N.append(("nest_" + "_".join(combo), fdef("int", nest(combo))))

# ---------------------------------------------------------------- write
def write(outdir):
    os.makedirs(outdir, exist_ok=True)
    rows = []
    for (i, k, text) in P:
        c = CONS[k]
        body = PRE + text + f"Definition go {SIG} : int :=\n  {c}.\n" + MAIN
        open(os.path.join(outdir, f"P_{i}.body"), "w").write(body)
        rows.append((f"P_{i}", "producer", k))
    for (i, text) in A:
        open(os.path.join(outdir, f"A_{i}.body"), "w").write(PRE + text + MAIN)
        rows.append((f"A_{i}", "parameter", i))
    for (i, text) in N:
        body = PRE + text + f"Definition go {SIG} : int :=\n  f n a b s.\n" + MAIN
        open(os.path.join(outdir, f"N_{i}.body"), "w").write(body)
        rows.append((f"N_{i}", "nesting", i))
    with open(os.path.join(outdir, "cells.tsv"), "w") as fh:
        for r in rows:
            fh.write("\t".join(r) + "\n")
    print(len(rows), "cells:", len(P), "producers,", len(A), "parameters,", len(N), "nestings")

if __name__ == "__main__":
    write(sys.argv[1] if len(sys.argv) > 1 else "cells")
