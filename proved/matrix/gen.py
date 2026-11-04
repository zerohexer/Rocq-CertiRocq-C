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
add("int_if_and_let", "int", fdef("int", "if (a <? b) && (let c := a + 1 in c <? 10) then a else b"))   # step 8
add("int_write_nontail", "int", ffix("int", "match n with O => rd 0 0 s | S m => f m a b (upd 0 a b s) + 1 end"))   # step 11
add("mem_grow", "mem", fdef("mem", "kq_grow 2 a s"))
add("mem_dup", "mem", fdef("mem", "let t := upd 0 a b s in upd 0 b a s"))      # old memory used after being handed on
# both versions used, differing in one cell written in the text (step 49): its old value can be kept and put back
add("mem_both", "mem", fdef("mem", "let t := upd 0 a b s in upd 0 b (rd 0 0 t) s"))
add("mem_hof", "mem", fdef("mem", "twice_m (fun t => upd 0 a b t) s"), "Definition twice_m (f : mem -> mem) (s : mem) : mem := f (f s).\n")
# a match on a counter in every result kind's place (step 35): on a sum (read as a let of it and a match on the variable), and on a
# counter variable where the table had none (a record or a pair chosen by the counter)
add("bool_match_add", "bool", fdef("bool", "match (n + n)%nat with O => true | S _ => a <? b end"))
add("bool_rec_match_add", "bool", ffix("bool", "match n with O => a <? b | S m => match (m + m)%nat with O => true | S _ => f m (a + 1) b s end end"))
add("mem_match_add", "mem", fdef("mem", "match (n + n)%nat with O => s | S _ => upd 0 a b s end"))
add("int_write_match_add", "int", fdef("int", "let s2 := upd 0 a b s in match (n + n)%nat with O => rd 0 0 s2 | S _ => rd 0 1 s2 end"))
add("pair_match_nat", "pair", fdef("pair", "match n with O => (a, b) | S _ => (b, a) end"))
add("pair_match_add", "pair", fdef("pair", "match (n + n)%nat with O => (a, b) | S _ => (b, a) end"))
add("rec3_match_nat", "rec3", fdef("rec3", "match n with O => mk3 a b 0 | S _ => mk3 b a 1 end"))
add("rec3_rec_match_add", "rec3", ffix("rec3", "match n with O => mk3 a b 0 | S m => match (m + m)%nat with O => mk3 b a 1 | S _ => f m b (a + b) s end end"))
add("pairp_match_nat", "pairp", fdef("pairp", "match n with O => ((a, b), 0) | S _ => ((b, a), 1) end"))
add("intmem_match_nat", "intmem", fdef("intmem", "match n with O => (a, s) | S _ => (b, upd 0 a b s) end"))
add("intmem_rec_match_add", "intmem", ffix("intmem", "match n with O => (a, s) | S m => match (m + m)%nat with O => (b, s) | S _ => f m (a + 1) b (upd 0 a b s) end end"))
# the constructs of the number sort in the boolean and record sorts (step 36): a test on a boolean, lets of every kind, a record
# taken apart, a match on a value of a data type
add("bool_if_bool", "bool", fdef("bool", "if (a <? b) && (b <? 100) then a =? b else false"))
add("bool_let_late", "bool", fdef("bool", "(a <? b) && (let c := a + 1 in c <? 10)"))
add("bool_match_rec", "bool", fdef("bool", "let '(x, y) := hp a b in x <? y"))
add("bool_match_option", "bool", fdef("bool", "match (if a <? b then Some a else None) with Some x => x <? 10 | None => false end"))
add("pair_if_bool", "pair", fdef("pair", "if (a <? b) && (b <? 100) then (a, b) else (b, a)"))
add("rec3_if_bool", "rec3", fdef("rec3", "if (a <? b) && (b <? 100) then mk3 a b 0 else mk3 b a 1"))
add("pair_let_bool", "pair", fdef("pair", "let c := a <? b in if c then (a, b) else (b, a)"))
add("pair_let_cnt", "pair", fdef("pair", "let w := S n in match w with O => (a, b) | S _ => (b, a) end"))
add("pair_match_option", "pair", fdef("pair", "match (if a <? b then Some a else None) with Some x => (x, b) | None => (b, a) end"))
add("rec3_match_option", "rec3", fdef("rec3", "match (if a <? b then Some a else None) with Some x => mk3 x b 0 | None => mk3 b a 1 end"))
# a counter grown by the recursion (step 37), in every result kind's place: the function's counters bound by a weighted sum
K37 = "Fixpoint k (n m : nat) "
add("bool_rec_succ", "bool", K37 + "(x : int) : bool := match n with O => x <? 5 | S p => k p (S m) (x + 1) end.\n" + fdef("bool", "k n n a"))
add("mem_rec_succ", "mem", K37 + "(x : int) (t : mem) : mem := match n with O => t | S p => k p (S m) (x + 1) (upd 0 x x t) end.\n" + fdef("mem", "k n n a s"))
add("pair_rec_succ", "pair", K37 + "(x y : int) : int * int := match n with O => (x, y) | S p => k p (S m) y x end.\n" + fdef("pair", "k n n a b"))
add("rec3_rec_succ", "rec3", K37 + "(x y : int) : r3 := match n with O => mk3 x y 0 | S p => k p (S m) y x end.\n" + fdef("rec3", "k n n a b"))
add("pairp_rec_succ", "pairp", K37 + "(x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S p => k p (S m) y x end.\n" + fdef("pairp", "k n n a b"))
add("intmem_rec_succ", "intmem", K37 + "(x : int) (t : mem) : int * mem := match n with O => (x, t) | S p => k p (S m) (x + 1) (upd 0 x x t) end.\n" + fdef("intmem", "k n n a s"))
add("int_write_rec_succ", "int", K37 + "(x : int) (t : mem) : int := match n with O => rd 0 0 t | S p => k p (S m) (x + 1) (upd 0 x x t) end.\n" + fdef("int", "k n n a s"))

# ---------------------------------------------------------------- family A: parameters
A = []
LIBS = {}     # the program's other files (step 51): a name under the cell's directory, its text
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

# ---------------------------------------------------------------- the places §12.V's steps left unread (2026-11-02): one cell each,
# so the table shows them until they are read (completeness is strict: CLAUDE.md, Rocq-C-solution.md §0.9)
# a sum of counters: given by a function that is itself called (step 33), under a successor, bound by a let, compared
addA("par_nat_add_called", "", "k2 n n a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\nFixpoint k2 (r n : nat) (x : int) : int := match r with O => k (n + n) x | S q => k2 q n (x + 1) end.\n")
addA("par_nat_add_called_succ", "", "k2 n (S n) a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\nFixpoint k2 (r n : nat) (x : int) : int := match r with O => k (n + n) x | S q => k2 q n (x + 1) end.\n")
addA("par_nat_add_succ", "", "k (S (n + n)) a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\n")
addA("par_nat_let_add", "", "let w := (n + n)%nat in k w a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\n")
addA("par_nat_eqb_add", "", "if Nat.eqb (n + n) 4 then a else b", "")
# a let of a successor of a counter variable (step 9)
addA("par_nat_match_add", "", "match (n + n)%nat with O => a | S p => k p a end", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\n")   # a match on a sum
addA("par_nat_rec_succ", "", "k n n a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (S m) (x + 1) end.\n")   # the recursive call given a successor: bounded by the sum of the two
addA("par_nat_let_succ", "", "let w := S n in k w a", "Fixpoint k (n : nat) (x : int) : int := match n with O => x | S m => k m (x + 1) end.\n")
# a counter grown by the recursion (step 37): by a constant, swapped with another, through a let, two grown, under a match on
# another counter, the function called by a recursion, a template, a mutual block; grown by the first counter's predecessor:
# its successor (each counter below the first's start) and a sum with it (quadratic: no weighted sum bounds it)
addA("par_nat_rec_add2", "", "k n n a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (m + 2) (x + 1) end.\n")
addA("par_nat_rec_swap_succ", "", "k n 1 n a", "Fixpoint k (n c d : nat) (x : int) : int := match n with O => x | S p => k p (S d) c (x + 1) end.\n")
addA("par_nat_rec_let_succ", "", "k n n a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => let q := S m in k p q (x + 1) end.\n")
addA("par_nat_rec_two_succ", "", "k n n n a", "Fixpoint k (n c d : nat) (x : int) : int := match n with O => x | S p => k p (S c) (S d) (x + 1) end.\n")
addA("par_nat_rec_match_succ", "", "k n n a",
     "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => match m with O => k p 1 x | S q => k p (S (S q)) (x + 1) end end.\n")
addA("par_nat_rec_succ_called", "", "k2 n a",
     "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (S m) (x + 1) end.\n"
     "Fixpoint k2 (r : nat) (x : int) : int := match r with O => x | S q => k2 q (k r r x) end.\n")
addA("par_nat_rec_succ_fn", "", "k n n a (fun y => y + 1)",
     "Fixpoint k (n m : nat) (x : int) (g : int -> int) : int := match n with O => x | S p => k p (S m) (g x) g end.\n")
addA("par_nat_rec_succ_mutual", "", "ev n n a",
     "Fixpoint ev (n m : nat) (x : int) : int := match n with O => x | S p => od p (S m) (x + 1) end\n"
     "with od (n m : nat) (x : int) : int := match n with O => x * 2 | S p => ev p (S m) (x + 2) end.\n")
addA("par_nat_rec_succ_pred", "", "k n n a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (S p) (x + 1) end.\n")
addA("par_nat_rec_add_pred", "", "k n n a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (m + p) (x + 1) end.\n")
# counters grown apart (step 38): several weighted sums -- three grown, one by two beside one by one, two grown beside a swap,
# each given its counters by the entry
addA("par_nat_rec_three_succ", "", "k n n n n a", "Fixpoint k (n c d e : nat) (x : int) : int := match n with O => x | S p => k p (S c) (S d) (S e) (x + 1) end.\n")
addA("par_nat_rec_add2_succ", "", "k n n n a", "Fixpoint k (n c d : nat) (x : int) : int := match n with O => x | S p => k p (c + 2) (S d) (x + 1) end.\n")
addA("par_nat_rec_succ_swap", "", "k n n n n a", "Fixpoint k (n c d e : nat) (x : int) : int := match n with O => x | S p => k p (S c) (S e) d (x + 1) end.\n")
addA("par_nat_rec_add_pred_lit", "", "k 100 0 a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (m + p) (x + 1) end.\n")   # the same from a written budget: bounded
# counters grown by other counters (step 39), from written budgets: by the predecessor's successor, a counter grown by one grown
# by the predecessor (degree 3), in a mutual block, in a template
addA("par_nat_rec_add_succ_pred", "", "k 100 0 a", "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (m + S p) (x + 1) end.\n")
addA("par_nat_rec_add_pred2", "", "k 50 0 0 a", "Fixpoint k (n m q : nat) (x : int) : int := match n with O => x | S p => k p (m + p) (q + m) (x + 1) end.\n")
addA("par_nat_rec_add_pred_mutual", "", "ev 100 0 a",
     "Fixpoint ev (n m : nat) (x : int) : int := match n with O => x | S p => od p (m + p) (x + 1) end\n"
     "with od (n m : nat) (x : int) : int := match n with O => x * 2 | S p => ev p (m + p) (x + 2) end.\n")
addA("par_nat_rec_add_pred_fn", "", "k 100 0 a (fun y => y + 1)",
     "Fixpoint k (n m : nat) (x : int) (g : int -> int) : int := match n with O => x | S p => k p (m + p) (g x) g end.\n")
# a recursive function passing on small written counters to one whose polynomial grows (its bound below kq_nat's 2^60)
# a function's bound from what its callers give it, however small (step 40): a template in between, a let of a written budget in
# a function with a small bound
addA("par_nat_rec_add_pred_tmpl", "", "kt 3 100 0 a (fun y => y + 1)",
     "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (m + p) (x + 1) end.\n"
     "Fixpoint kt (r n m : nat) (x : int) (g : int -> int) : int := match r with O => k n m (g x) | S q => kt q n m (g x) g end.\n")
addA("par_nat_small_let_budget", "", "kb 3 100 a",
     "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (m + p) (x + 1) end.\n"
     "Fixpoint kb (r n : nat) (x : int) : int := match r with O => k n 0 x | S q => let w : nat := 7%nat in kb q w (x + 1) end.\n")
addA("par_nat_rec_add_pred_pass", "", "kpass 3 100 0 a",
     "Fixpoint k (n m : nat) (x : int) : int := match n with O => x | S p => k p (m + p) (x + 1) end.\n"
     "Fixpoint kpass (r n m : nat) (x : int) : int := match r with O => k n m x | S q => kpass q n m (x + 1) end.\n")
# a record holding records (step 32): an inner record used as a value, taken apart later, given on
addA("par_pairp_proj", "", "let r := k n a b in fst (fst r) + snd (fst r) + snd r", "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\n")
addA("par_pairp_late", "", "let '(p, z) := k n a b in let w := z + 1 in let '(x, y) := p in x + y + w", "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\n")
addA("par_pairp_pass", "", "let '(p, z) := k n a b in pf n p + z",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\nFixpoint pf (n : nat) (p : int * int) : int := match n with O => fst p | S m => pf m (snd p, fst p) end.\n")
# records holding records as values (step 43): an inner record rebuilt into a new outer record, in a recursion and by a let; bound
# by a let; given back by a function; three levels; taken apart one level in a test, in functions giving back a boolean, a memory, a
# number after memories, a number and a memory, a record
addA("par_pairp_rebuild", "", "let '((x, y), z) := k n a b in x + y + z",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => let '(p, z) := k m y x in (p, z + 1) end.\n")
addA("par_pairp_build_let", "", "let '(p, z) := k n a b in let r := (p, z + 1) in let '((x, y), w) := r in x + y + w", "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\n")
addA("par_pairp_let", "", "let '(p, z) := k n a b in let q := p in fst q + snd q + z", "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\n")
addA("par_pairp_ret", "", "let q := kin n (k n a b) in fst q + snd q",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\nFixpoint kin (n : nat) (r : (int * int) * int) : int * int := match n with O => fst r | S m => kin m r end.\n")
addA("par_pairp_deep", "", "let '(p, w) := k3 n a b in let '(q, z) := p in fst q + snd q + z + w",
     "Fixpoint k3 (n : nat) (x y : int) : ((int * int) * int) * int := match n with O => (((x, y), 0), 1) | S m => k3 m y x end.\n")
addA("par_pairp_test", "", "if (let '(p, z) := k n a b in fst p <? z) then 1 else 0", "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\n")
addA("par_pairp_bool", "", "if kb n a b then 1 else 0",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\nFixpoint kb (n : nat) (x y : int) : bool := match n with O => let '(p, z) := k n x y in let w := z + 1 in fst p <? w | S m => kb m y x end.\n")
addA("par_pairp_mem", "", "rd 0 0 (km n a s)",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\nFixpoint km (n : nat) (x : int) (t : mem) : mem := match n with O => let '(p, z) := k n x x in let w := z + 1 in upd 0 (fst p) w t | S m => km m (x + 1) t end.\n")
addA("par_pairp_tail", "", "kx n a s",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\nFixpoint kx (n : nat) (x : int) (t : mem) : int := match n with O => let '(p, z) := k n x x in let t2 := upd 0 (fst p) z t in rd 0 0 t2 | S m => kx m (x + 1) t end.\n")
addA("par_pairp_pv", "", "let '(y, t2) := kp n a s in y + rd 0 0 t2",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\nFixpoint kp (n : nat) (x : int) (t : mem) : int * mem := match n with O => let '(p, z) := k n x x in let w := z + 1 in (fst p + w, upd 0 (snd p) z t) | S m => kp m (x + 1) t end.\n")
addA("par_pairp_rec", "", "let '(u, v) := kr n a b in u + v",
     "Fixpoint k (n : nat) (x y : int) : (int * int) * int := match n with O => ((x, y), 0) | S m => k m y x end.\nFixpoint kr (n : nat) (x y : int) : int * int := match n with O => let '(p, z) := k n x y in let w := z + 1 in (fst p + w, snd p) | S m => kr m y x end.\n")
# a number and a memory (step 26): taken apart by a function giving back a memory; as a parameter
addA("par_intmem_mem_fn", "", "rd 0 0 (wm n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\n"
     "Fixpoint wm (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => let '(y, t2) := g n x t in wm m y (upd 1 y y t2) end.\n")
# a memory taking a number-and-memory pair apart (step 44): one built in place after other text, one chosen by a test; at the end of
# a memory function; bound by a let and read through fst and snd; inside a memory given to a call; one a function gives that takes
# one apart itself
addA("par_intmem_mem_built", "", "rd 0 0 (wb n a s)",
     "Fixpoint wb (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => let z := x + 1 in let '(y, t2) := (z, upd 0 x z t) in wb m y t2 end.\n")
addA("par_intmem_mem_test", "", "rd 0 0 (wt n a s)",
     "Fixpoint wt (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => let '(y, t2) := (if x <? 5 then (x, upd 0 x x t) else (x + 1, t)) in wt m y t2 end.\n")
addA("par_intmem_mem_tail", "", "rd 1 0 (wl n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint wl (n : nat) (x : int) (t : mem) : mem := match n with O => let '(y, t2) := g n x t in upd 1 y y t2 | S m => wl m (x + 1) t end.\n")
addA("par_intmem_mem_let", "", "rd 1 0 (wv n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint wv (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => let w := g n x t in wv m (fst w) (upd 1 (fst w) 0 (snd w)) end.\n")
addA("par_intmem_mem_arg", "", "rd 1 0 (wc n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint wc (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => wc m x (hm x x (let '(y, t2) := g n x t in upd 1 y y t2)) end.\n")
addA("par_intmem_mem_nested", "", "rd 2 0 (wn n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint g2 (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => let '(y, t2) := g n x t in g2 m (y + 1) (upd 2 y y t2) end.\n"
     "Fixpoint wn (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => let '(y, t2) := g2 n x t in wn m y t2 end.\n")
addA("par_intmem_param", "", "k n (a, s)",
     "Fixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\n")
# a number and a memory as a parameter (step 44 continued): after other parameters; the function giving back a memory, a pair, a
# boolean; a call given a pair a function gives (a number, a memory, a pair given back); the pair taken apart in the body; the
# recursion given the pair as it is; a call inside an expression given a pair a function gives (a writing function inside an
# expression, a later item)
addA("par_pm_param_after", "", "k n b (a, s)",
     "Fixpoint k (n : nat) (y : int) (p : int * mem) : int := match n with O => fst p + y | S m => k m (y + 1) (fst p + rd 0 0 (snd p), snd p) end.\n")
addA("par_pm_param_mem", "", "rd 0 0 (k n (a, s))", "Fixpoint k (n : nat) (p : int * mem) : mem := match n with O => upd 0 (fst p) 0 (snd p) | S m => k m (fst p + 1, upd 1 (fst p) 0 (snd p)) end.\n")
addA("par_pm_param_pv", "", "let '(x, t) := k n (a, s) in x + rd 0 0 t", "Fixpoint k (n : nat) (p : int * mem) : int * mem := match n with O => p | S m => k m (fst p + 1, upd 0 (fst p) 0 (snd p)) end.\n")
addA("par_pm_param_bool", "", "if k n (a, s) then 1 else 0", "Fixpoint k (n : nat) (p : int * mem) : bool := match n with O => fst p <? rd 0 0 (snd p) | S m => k m (fst p + 1, snd p) end.\n")
addA("par_pm_call_fn", "", "k n (g n a s)", "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\n")
addA("par_pm_call_fn_mem", "", "rd 0 0 (k n (g n a s))", "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : mem := match n with O => upd 0 (fst p) 0 (snd p) | S m => k m (fst p + 1, upd 1 (fst p) 0 (snd p)) end.\n")
addA("par_pm_call_fn_pv", "", "let '(x, t) := k n (g n a s) in x + rd 0 0 t", "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int * mem := match n with O => p | S m => k m (fst p + 1, upd 0 (fst p) 0 (snd p)) end.\n")
addA("par_pm_match_body", "", "k n (a, s)",
     "Fixpoint k (n : nat) (p : int * mem) : int := match n with O => let '(x, t) := p in x + rd 0 0 t | S m => let '(x, t) := p in k m (x + 1, upd 0 x x t) end.\n")
addA("par_pm_rec_as_is", "", "k n (a, s)",
     "Fixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p + rd 0 0 (snd p) | S m => k m p end.\n")
addA("par_pm_call_expr", "", "k n (g n a s) + 1", "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\n")
addA("par_pm_call_bool_fn", "", "if k n (g n a s) then 1 else 0", "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : bool := match n with O => fst p <? rd 0 0 (snd p) | S m => k m (fst p + 1, snd p) end.\n")
# a mutual block (step 17): members of different signatures; members giving back a memory
addA("par_mutual_sig", "", "ev n a",
     "Fixpoint ev (n : nat) (x : int) : int := match n with O => x | S m => od m (x + 1) 3 end\n"
     "with od (n : nat) (x y : int) : int := match n with O => x + y | S m => ev m (x + y) end.\n")
addA("par_mutual_mem", "", "rd 0 0 (wa n s)",
     "Fixpoint wa (n : nat) (t : mem) : mem := match n with O => t | S m => wb m (upd 0 1 1 t) end\n"
     "with wb (n : nat) (t : mem) : mem := match n with O => t | S m => wa m (upd 0 2 2 t) end.\n")
# a mutual block of any signature (step 45): booleans and records among the members' parameters, a second counter, the
# recursion's counter not first; giving back a boolean, a record, a number and a memory, a number that writes; a number that
# reads and one that writes in one part; three members; members of different sorts in different parts; a member taking a pair;
# a part whose members give back different types (a later step)
addA("par_mutual_bool", "", "if ev n then a else b",
     "Fixpoint ev (n : nat) : bool := match n with O => true | S m => od m end\nwith od (n : nat) : bool := match n with O => false | S m => ev m end.\n")
addA("par_mutual_bool_param", "", "ev n a (a <? b)",
     "Fixpoint ev (n : nat) (x : int) (c : bool) : int := match n with O => if c then x else 0 | S m => od m (x + 1) end\nwith od (n : nat) (x : int) : int := match n with O => x | S m => ev m (x * 2) (x <? 100) end.\n")
addA("par_mutual_rec_param", "", "ev n (mk3 a b 1)",
     "Fixpoint ev (n : nat) (w : r3) : int := match n with O => f1 w + f3 w | S m => od m (f2 w) w end\nwith od (n : nat) (x : int) (w : r3) : int := match n with O => x | S m => ev m (mk3 x (f1 w) (f3 w + 1)) end.\n")
addA("par_mutual_counter2", "", "ev n 3 a",
     "Fixpoint ev (n k : nat) (x : int) : int := match n with O => x | S m => od m (x + 1) end\nwith od (n : nat) (x : int) : int := match n with O => x * 2 | S m => ev m 2 x end.\n")
addA("par_mutual_order", "", "ev a n",
     "Fixpoint ev (x : int) (n : nat) : int := match n with O => x | S m => od m (x + 1) end\nwith od (n : nat) (x : int) : int := match n with O => x * 2 | S m => ev (x + 3) m end.\n")
addA("par_mutual_rec_res", "", "f1 (ev n a) + f3 (ev n b)",
     "Fixpoint ev (n : nat) (x : int) : r3 := match n with O => mk3 x 0 1 | S m => od m (x + 1) end\nwith od (n : nat) (x : int) : r3 := match n with O => mk3 0 x 2 | S m => ev m (x * 2) end.\n")
addA("par_mutual_pv_res", "", "let '(x, t) := ev n a s in x + rd 0 0 t",
     "Fixpoint ev (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => od m (x + 1) (upd 0 x x t) end\nwith od (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x + 1, t) | S m => ev m x (upd 1 x x t) end.\n")
addA("par_mutual_write", "", "ev n a s",
     "Fixpoint ev (n : nat) (x : int) (t : mem) : int := match n with O => rd 0 0 t + x | S m => od m (x + 1) (upd 0 0 x t) end\nwith od (n : nat) (x : int) (t : mem) : int := match n with O => rd 1 0 t | S m => ev m x (upd 1 0 x t) end.\n")
addA("par_mutual_read_write", "", "ev n a s",
     "Fixpoint ev (n : nat) (x : int) (t : mem) : int := match n with O => rd 0 0 t + x | S m => od m x t end\nwith od (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => ev m (x + 1) (upd 0 0 x t) end.\n")
addA("par_mutual_three", "", "ma n a",
     "Fixpoint ma (n : nat) (x : int) : int := match n with O => x | S m => mb m (x + 1) end\nwith mb (n : nat) (x : int) : int := match n with O => x * 2 | S m => mc m (x * 3) end\nwith mc (n : nat) (x : int) : int := match n with O => x + 7 | S m => ma m (x - 1) end.\n")
addA("par_mutual_parts", "", "rd 0 0 (cg n s)",
     "Fixpoint cf (n : nat) (x : int) : int := match n with O => x | S m => cf m (x + 1) end\nwith cg (n : nat) (t : mem) : mem := match n with O => t | S m => upd 0 (cf m 1) 0 (cg m t) end.\n")
addA("par_mutual_pm", "", "ev n (a, s)",
     "Fixpoint ev (n : nat) (p : int * mem) : int := match n with O => fst p + rd 0 0 (snd p) | S m => od m (fst p + 1) (snd p) end\nwith od (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => ev m (x * 2, t) end.\n")
addA("par_mutual_mixed", "", "ev n a s",
     "Fixpoint ev (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => rd 0 0 (od m t) + x end\nwith od (n : nat) (t : mem) : mem := match n with O => t | S m => upd 0 (ev m 1 t) 0 t end.\n")
# a capture (step 13): of a counter, of a record, of a variable bound by a match on a record
addA("par_capture_nat", "", "fold n 0 a (fun i acc => match n with O => acc | S _ => acc + i end)", "")
addA("par_capture_rec", "", "let w := mk3 a b 1 in fold n 0 a (fun i acc => acc + f1 w)", "")
addA("par_capture_match", "", "kr n (mk3 a b 1) a",
     "Fixpoint kr (n : nat) (w : r3) (x : int) : int := match n with O => x | S m => match w with mk3 p q r => kr m w (fold m 0 x (fun i acc => acc + p)) end end.\n")
# captures of every kind (step 42): a counter and a record together, a counter captured inside a recursion, a counter captured by
# a local fixpoint, a template in another order given a function that captures
addA("par_capture_cnt_rec", "", "let w := mk3 a b 1 in fold n 0 a (fun i acc => match n with O => acc + f1 w | S _ => acc + i end)", "")
addA("par_capture_in_rec", "", "kc n n a",
     "Fixpoint kc (r n : nat) (x : int) : int := match r with O => x | S q => kc q n (fold n 0 x (fun i acc => match n with O => acc | S _ => acc + i end)) end.\n")
addA("par_capture_lfix", "", "let fix g (m : nat) (x : int) : int := match m with O => x | S p => g p (match n with O => x | S _ => x + 1 end) end in g n a", "")
addA("par_capture_tmpl_perm", "", "foldf (fun i acc => acc + b) n 0 a",
     "Fixpoint foldf (f : int -> int -> int) (n : nat) (i acc : int) : int := match n with O => acc | S m => foldf f m (i + 1) (f i acc) end.\n")
# a template giving back a record (step 12)
addA("par_fun_rec_pair", "", "let '(x, y) := foldp n (a, b) (fun z => z + 1) in x + y",
     "Fixpoint foldp (n : nat) (p : int * int) (g : int -> int) : int * int := match n with O => p | S m => foldp m (g (fst p), snd p + 1) g end.\n")
# a template of any signature (step 46): giving back a boolean (a capture among its functions), a record (a capture), a number
# and a memory; a record and a boolean among its parameters; a local fixpoint giving back a record; functions given that give
# back a record, take a record, write the memory, take a boolean; the pair as a parameter
addA("par_tmpl_bool", "", "if allp n a (fun z => z <? 1000) then 1 else 0",
     "Fixpoint allp (n : nat) (x : int) (g : int -> bool) : bool := match n with O => true | S m => if g x then allp m (x + 1) g else false end.\n")
addA("par_tmpl_bool_cap", "", "if allp n a (fun z => z <? b) then 1 else 0",
     "Fixpoint allp (n : nat) (x : int) (g : int -> bool) : bool := match n with O => true | S m => if g x then allp m (x + 1) g else false end.\n")
addA("par_tmpl_rec3", "", "f1 (fr n (mk3 a b 0) (fun z => z * 2)) + f3 (fr n (mk3 b a 1) (fun z => z * 2))",
     "Fixpoint fr (n : nat) (w : r3) (g : int -> int) : r3 := match n with O => w | S m => fr m (mk3 (g (f1 w)) (f2 w) (f3 w + 1)) g end.\n")
addA("par_tmpl_rec3_cap", "", "f1 (fr n (mk3 a b 0) (fun z => z + b))",
     "Fixpoint fr (n : nat) (w : r3) (g : int -> int) : r3 := match n with O => w | S m => fr m (mk3 (g (f1 w)) (f2 w) (f3 w + 1)) g end.\n")
addA("par_tmpl_pv", "", "let '(x, t) := fpv n a (fun z => z + 1) s in x + rd 0 0 t",
     "Fixpoint fpv (n : nat) (x : int) (g : int -> int) (t : mem) : int * mem := match n with O => (x, t) | S m => fpv m (g x) g (upd 0 x x t) end.\n")
addA("par_tmpl_rec_param", "", "sumr n (mk3 a b 0) (fun z => z + 3)",
     "Fixpoint sumr (n : nat) (w : r3) (g : int -> int) : int := match n with O => f1 w + f3 w | S m => sumr m (mk3 (g (f1 w)) (f2 w) (f3 w + 1)) g end.\n")
addA("par_tmpl_bool_param", "", "fb n (a <? b) a (fun z => z + 1)",
     "Fixpoint fb (n : nat) (c : bool) (x : int) (g : int -> int) : int := match n with O => if c then x else 0 | S m => fb m (negb c) (g x) g end.\n")
addA("par_lfix_rec3", "", "let fix lf (k : nat) (w : r3) : r3 := match k with O => w | S m => lf m (mk3 (f1 w + a) (f2 w) (f3 w)) end in f1 (lf n (mk3 a b 0))",
     "")
addA("par_tmpl_fn_rec_res", "", "fq n a (fun z => mk3 z (z + 1) 0)",
     "Fixpoint fq (n : nat) (x : int) (g : int -> r3) : int := match n with O => x | S m => fq m (f1 (g x) + f2 (g x)) g end.\n")
addA("par_tmpl_fn_rec_arg", "", "fw n (mk3 a b 0) (fun v => f1 v + f3 v)",
     "Fixpoint fw (n : nat) (w : r3) (g : r3 -> int) : int := match n with O => g w | S m => fw m (mk3 (g w) (f2 w) (f3 w)) g end.\n")
addA("par_tmpl_fn_mem", "", "rd 0 0 (fmw n a (fun z u => upd 0 z z u) s)",
     "Fixpoint fmw (n : nat) (x : int) (g : int -> mem -> mem) (t : mem) : mem := match n with O => t | S m => fmw m (x + 1) g (g x t) end.\n")
addA("par_tmpl_fn_bool_arg", "", "fba n a (fun c => if c then 1 else 2)",
     "Fixpoint fba (n : nat) (x : int) (g : bool -> int) : int := match n with O => x | S m => fba m (x + g (x <? 10)) g end.\n")
addA("par_tmpl_pm_param", "", "fpm n (fun z => z + 1) (a, s)",
     "Fixpoint fpm (n : nat) (g : int -> int) (p : int * mem) : int := match n with O => fst p + rd 0 0 (snd p) | S m => fpm m g (g (fst p), snd p) end.\n")
# a number function that writes, called inside an expression (step 11)
addA("par_write_fn_expr", "", "wr n s + 1",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
# a call inside an expression that writes the memory or is given a pair (step 47): after a read of the memory, before one, in a
# test, bound by a let, its result used twice, as a call's argument; the function's own; given a pair, giving back a record (a
# later step); two calls that write in one expression (each given the memory before both: a gap until a copy is decided)
addA("par_write_after_read", "", "rd 1 0 s + wr n s",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_write_before_read", "", "wr n s * 2 + rd 1 0 s",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_write_in_test", "", "if wr n s <? 5 then a else b",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_write_let", "", "let v := wr n s in v * 2 + a",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_write_twice_use", "", "let v := wr n s in v * v",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_write_call_arg", "", "h (wr n s) a",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_write_self_expr", "", "f n a b s",
     "Fixpoint f (n : nat) (a b : int) (s : mem) : int := match n with O => rd 0 0 s | S m => (f m a b (upd 0 a b s) + 1) * 2 end.\n")
addA("par_pm_call_rec", "", "f1 (kr n (g n a s))",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint kr (n : nat) (p : int * mem) : r3 := match n with O => mk3 (fst p) (rd 0 0 (snd p)) 0 | S m => kr m (fst p + 1, snd p) end.\n")
addA("par_write_two", "", "wr n s + wr2 n s",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nFixpoint wr2 (n : nat) (t : mem) : int := match n with O => rd 1 0 t | S m => wr2 m (upd 1 0 (rd 1 0 t + 2) t) end.\n")
# two versions of the memory both used (step 49).  `A_par_write_two` and these two differ from the old memory in cells fixed
# by the text (a save of those cells, no copy: gaps); the pin differs in cells whose number comes from the data -- each call a
# prefix sum in place over n cells from its own index, each round reading the cell the round before wrote, both given the
# memory before both -- so keeping the old memory needs a copy or a log of n cells (by design); its control hands the memory on
addA("par_write_in_mem", "", "rd 0 1 (kw n a s)",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nDefinition kw (n : nat) (x : int) (t : mem) : mem := upd 0 1 (wr n t + x) t.\n")
addA("par_write_two_data", "", "wp n a s + wp n b s",
     "Fixpoint wp (n : nat) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => wp m (x + 1) (upd 0 (x + 1) (rd 0 (x + 1) t + rd 0 x t) t) end.\n")
addA("par_write_two_seq", "", "let '(v, t) := wpp n a s in v + wp n b t",
     "Fixpoint wpp (n : nat) (x : int) (t : mem) : int * mem := match n with O => (rd 0 x t, t) | S m => wpp m (x + 1) (upd 0 (x + 1) (rd 0 (x + 1) t + rd 0 x t) t) end.\nFixpoint wp (n : nat) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => wp m (x + 1) (upd 0 (x + 1) (rd 0 (x + 1) t + rd 0 x t) t) end.\n")
# a call given a pair giving back a record, bound by a let, inside a test (step 48)
addA("par_pm_call_rec_let", "", "let w := kr n (g n a s) in f1 w + f2 w * f3 w",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint kr (n : nat) (p : int * mem) : r3 := match n with O => mk3 (fst p) (rd 0 0 (snd p)) 0 | S m => kr m (fst p + 1, snd p) end.\n")
addA("par_pm_call_rec_test", "", "if f2 (kr n (g n a s)) <? 7 then a else b",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint kr (n : nat) (p : int * mem) : r3 := match n with O => mk3 (fst p) (rd 0 0 (snd p)) 0 | S m => kr m (fst p + 1, snd p) end.\n")
# a call given a pair not built in place inside an expression of a function giving back a boolean, a record, a number and a
# memory, a memory (the places step 47 leaves: it reads them in a number's body only)
addA("par_pm_call_in_bool", "", "if kb n a s then 1 else 0",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kb (n : nat) (x : int) (t : mem) : bool := k n (g n x t) <? 5.\n")
addA("par_pm_call_in_rec", "", "f1 (kq n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kq (n : nat) (x : int) (t : mem) : r3 := mk3 (k n (g n x t)) 0 1.\n")
addA("par_pm_call_in_pv", "", "let '(x, t) := kp n a s in x + rd 0 0 t",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kp (n : nat) (x : int) (t : mem) : int * mem := let p := g n x t in (k n p + 1, snd p).\n")
addA("par_pm_call_in_mem", "", "rd 0 0 (km n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition km (n : nat) (x : int) (t : mem) : mem := let p := g n x t in upd 0 (k n p) 0 (snd p).\n")
# the pair a let holds, used bare (step 48 continued): given to two calls, in the body of a number, a boolean, a record; given in a
# test; given back; in a recursive function; as an operand; and the places left: the function's own call in the let's body, the
# memory before the pair read in it
addA("par_pm_let_two", "", "let '(x, t) := kx n a s in x + rd 0 0 t",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nFixpoint k2 (n : nat) (p : int * mem) : int := match n with O => snd (fst p, 1) | S m => k2 m (fst p + 2, snd p) end.\nDefinition kx (n : nat) (x : int) (t : mem) : int * mem := let p := g n x t in (k n p + k2 n p, snd p).\n")
addA("par_pm_let_num", "", "kx n a s + 1",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kx (n : nat) (x : int) (t : mem) : int := let p := g n x t in k n p + fst p.\n")
addA("par_pm_let_bool", "", "if kx n a s then a else b",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kx (n : nat) (x : int) (t : mem) : bool := let p := g n x t in k n p <? fst p.\n")
addA("par_pm_let_rec", "", "f1 (kx n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kx (n : nat) (x : int) (t : mem) : r3 := let p := g n x t in mk3 (k n p) (fst p) 0.\n")
addA("par_pm_let_test", "", "kx n a s",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kx (n : nat) (x : int) (t : mem) : int := let p := g n x t in if fst p <? 3 then k n p else rd 0 0 (snd p).\n")
addA("par_pm_let_back", "", "let '(x, t) := kx n a s in x + rd 0 0 t",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kx (n : nat) (x : int) (t : mem) : int * mem := let p := g n x t in p.\n")
addA("par_pm_let_in_fix", "", "kx n a s",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nFixpoint kx (m : nat) (x : int) (t : mem) : int := match m with O => let p := g 2 x t in k 2 p | S q => kx q (x + 1) t end.\n")
addA("par_pm_let_operand", "", "1 + (let p := g n a s in k n p)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\n\n")
addA("par_pm_let_own", "", "kx n a s",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nFixpoint kx (m : nat) (x : int) (t : mem) : int := match m with O => rd 0 0 t | S q => let p := g 2 x t in k 2 p + kx q (fst p) (snd p) end.\n")
addA("par_pm_let_old", "", "kx n a s",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nFixpoint k (n : nat) (p : int * mem) : int := match n with O => fst p | S m => k m (fst p + rd 0 0 (snd p), snd p) end.\nDefinition kx (n : nat) (x : int) (t : mem) : int := let p := g n x t in k n p + rd 0 0 t.\n")
# a read of the memory before a write, standing after the write (step 50): after a call that writes, a let of a memory, a pair
# taken apart and bound, in a memory's, a pair's, a boolean's body, in a test, a call that reads, two reads; the place left: its
# index from what the write gives.  And a pair a let holds read through fst and snd in the body of a pair, of a memory
addA("par_old_read_call", "", "let v := wr n s in v * 2 + rd 1 0 s",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_old_read_mem", "", "let t := upd 0 a b s in rd 0 b t + rd 1 0 s",
     "")
addA("par_old_read_match", "", "let '(x, t) := g n a s in x + rd 1 0 s + rd 0 0 t",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\n")
addA("par_old_read_pair", "", "let p := g n a s in fst p + rd 1 0 s",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\n")
addA("par_old_read_in_mem", "", "rd 0 0 (let t := upd 0 a b s in upd 1 (rd 1 0 s) 0 t)",
     "")
addA("par_old_read_mem_rec", "", "rd 1 a (kmf n a s)",
     "Fixpoint kmf (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => kmf m (x + 1) (let u := upd 0 x x t in upd 1 (rd 1 0 t) x u) end.\n")
addA("par_old_read_pv", "", "let '(v, w) := kv n a s in v + rd 0 0 w",
     "Fixpoint kv (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => let u := upd 0 x x t in (rd 1 0 t + x, u) end.\n")
addA("par_old_read_bool", "", "if (let t := upd 0 a b s in rd 0 b t <? rd 1 0 s) then a else b",
     "")
addA("par_old_read_test", "", "let p := g n a s in if fst p <? rd 1 a s then rd 0 0 (snd p) else 0",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\n")
addA("par_old_read_fn", "", "let v := wr n s in v + sm n s",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nFixpoint sm (n : nat) (t : mem) : int := match n with O => 0 | S m => rd 1 0 t + sm m t end.\n")
addA("par_old_read_two", "", "let t := upd 0 a b s in rd 1 0 s + rd 1 1 s + rd 0 0 t",
     "")
addA("par_old_read_index", "", "let v := wr n s in rd 1 v s",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_pm_let_fst_pv", "", "let '(x, t) := kz n a s in x + rd 0 0 t",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nDefinition kz (n : nat) (x : int) (t : mem) : int * mem := let p := g n x t in (fst p + 1, snd p).\n")
addA("par_pm_let_fst_mem", "", "rd 0 0 (kz n a s)",
     "Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nDefinition kz (n : nat) (x : int) (t : mem) : mem := let p := g n x t in upd 0 (fst p) 1 (snd p).\n")
# Rocq's own measure recursion (step 56): Program Fixpoint, each sort, a measure on a machine number and on a counter
addA("pf_num", "", "pq a",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_tail", "", "pq a b",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x y : int) {measure (mu x)} : int :=\n  match 0 <? x with true => pq (x - 1) (y + x) | false => y end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_read", "", "pq a b s",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x y : int) (t : mem) {measure (mu x)} : int :=\n  match 0 <? x with true => pq (x - 1) (y + rd 0 x t) t | false => y end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_mem", "", "rd 0 0 (pq a s)",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) (t : mem) {measure (mu x)} : mem :=\n  match 0 <? x with true => pq (x - 1) (upd 0 x x t) | false => t end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_write_num", "", "pq a s",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) (t : mem) {measure (mu x)} : int :=\n  match 0 <? x with true => pq (x - 1) (upd 0 x x t) + 1 | false => rd 0 0 t end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_bool", "", "if pq a then a else b",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : bool :=\n  match 0 <? x with true => negb (pq (x - 1)) | false => true end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_bool_test", "", "if pq a b then a else b",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x y : int) {measure (mu x)} : bool :=\n  match 0 <? x with true => (if pq (x - 1) y then x <? y else y <? x) | false => true end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_record", "", "f1 (pq a)",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : r3 :=\n  match 0 <? x with true => let w := pq (x - 1) in mk3 (f1 w + x) (f2 w) 0 | false => mk3 0 0 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_record_param", "", "pq a (mk3 b b b)",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) (w : r3) {measure (mu x)} : int :=\n  match 0 <? x with true => pq (x - 1) (mk3 (f1 w + x) (f2 w) 0) | false => f1 w end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_pair_result", "", "fst (pq a s)",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) (t : mem) {measure (mu x)} : int * mem :=\n  match 0 <? x with true => pq (x - 1) (upd 0 x x t) | false => (x, t) end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_pair_ints", "", "fst (pq a)",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int * int :=\n  match 0 <? x with true => let p := pq (x - 1) in (fst p + x, snd p) | false => (0, 1) end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_nested", "", "pq a b",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x y : int) {measure (mu x)} : int :=\n  match 0 <? x with true => (match y <? x with true => pq (x - 1) y | false => x + pq (x - 1) (y - 1) end) | false => y end.\nNext Obligation. apply mu_pred. auto. Qed.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_let", "", "pq a b",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x y : int) {measure (mu x)} : int :=\n  match 0 <? x with true => let z := y + x in pq (x - 1) z | false => y end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_calls", "", "pq n a",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nProgram Fixpoint pq (n : nat) (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => ff n x + pq n (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_caller_fix", "", "kc n a",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\nFixpoint kc (n : nat) (x : int) : int := match n with O => pq x | S m => kc m (pq x) end.\n")
addA("pf_given", "", "fold n a b (fun i acc => acc + pq i)",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_in_module", "", "Lib.pq a",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nModule Lib.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\nEnd Lib.\n")
addA("pf_two", "", "pq a + pr b",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\nProgram Fixpoint pr (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => pr (x - 1) + 1 | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_op", "", "(pq a + 1) * rd 0 0 s",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_counter", "", "pq n a",
     "From Stdlib Require Import Program.Wf.\nProgram Fixpoint pq (n : nat) (x : int) {measure n} : int :=\n  match n with O => x | S m => pq m (x + 1) end.\n")
addA("pf_counter_mem", "", "rd 0 0 (pq n a s)",
     "From Stdlib Require Import Program.Wf.\nProgram Fixpoint pq (n : nat) (x : int) (t : mem) {measure n} : mem :=\n  match n with O => t | S m => pq m (x + 1) (upd 0 x x t) end.\n")
addA("pf_counter_nontail", "", "pq n a",
     "From Stdlib Require Import Program.Wf.\nProgram Fixpoint pq (n : nat) (x : int) {measure n} : int :=\n  match n with O => x | S m => x + pq m (x + 1) end.\n")
addA("pf_counter_sum", "", "pq n n a",
     "From Stdlib Require Import Program.Wf Lia.\nProgram Fixpoint pq (n k : nat) (x : int) {measure (n + k)} : int :=\n  match n with O => x | S m => pq m k (x + 1) end.\n")
addA("pf_dec", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("pf_wf_rel", "", "pq a",
     "From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nDefinition rr (x y : int) : Prop := (mu x < mu y)%nat.\nLemma rr_wf : well_founded rr.\nProof. apply (well_founded_lt_compat _ mu). intros x y H. exact H. Qed.\nProgram Fixpoint pq (x : int) {wf rr x} : int :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\nNext Obligation. apply rr_wf. Defined.\n")
addA("par_own_nomem_record_let", "", "f1 (kf n a b)",
     "Fixpoint kf (n : nat) (a b : int) : r3 := match n with O => mk3 a b 0 | S m => let w := kf m (a + 1) b in mk3 (f1 w + a) b 0 end.\n")
addA("par_own_nomem_bool_let_num", "", "if kf n a b then a else b",
     "Fixpoint kf (n : nat) (a b : int) : bool := match n with O => a <? b | S m => let c := kf m (a + 1) b in (if c then 1 else 2) + a <? b end.\n")
addA("par_own_nomem_bool_let_neg", "", "if kf n a b then a else b",
     "Fixpoint kf (n : nat) (a b : int) : bool := match n with O => a <? b | S m => let c := kf m (a + 1) b in negb c end.\n")
addA("par_own_nomem_bool_let_test", "", "if kf n a b then a else b",
     "Fixpoint kf (n : nat) (a b : int) : bool := match n with O => a <? b | S m => let c := kf m (a + 1) b in if c then a <? b else b <? a end.\n")
addA("par_own_nomem_bool_test", "", "if kf n a b then a else b",
     "Fixpoint kf (n : nat) (a b : int) : bool := match n with O => a <? b | S m => if kf m (a + 1) b then a <? b else b <? a end.\n")
addA("par_own_nomem_record_match", "", "f1 (kf n a b)",
     "Fixpoint kf (n : nat) (a b : int) : r3 := match n with O => mk3 a b 0 | S m => match kf m (a + 1) b with mk3 x y z => mk3 (x + a) y z end end.\n")
addA("par_own_nomem_pair_let", "", "fst (kf n a b)",
     "Fixpoint kf (n : nat) (a b : int) : int * int := match n with O => (a, b) | S m => let p := kf m (a + 1) b in (fst p + a, snd p) end.\n")
addA("par_own_nomem_num_let", "", "kf n a b",
     "Fixpoint kf (n : nat) (a b : int) : int := match n with O => a | S m => let c := kf m (a + 1) b in if c <? b then c else b end.\n")
addA("par_pm_let_nested", "", "kn2 n a s",
     "Fixpoint gg (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => gg m (x + 1) (upd 0 x x t) end.\nDefinition kp (p : int * mem) : int := fst p + rd 0 0 (snd p).\nDefinition gg2 (p : int * mem) : int * mem := (fst p + 1, upd 1 0 (fst p) (snd p)).\nDefinition kn2 (n : nat) (x : int) (t : mem) : int := let p := gg n x t in let q := gg2 p in kp q + 1.\n")
addA("par_own_opnd_choice", "", "ko n a s",
     "Fixpoint ko (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => (if x <? 3 then ko m (x + 1) (upd 0 x x t) else x) + 1 end.\n")
# a second memory parameter (step 53): the same memory, a memory never read, both live (the pin), where the call gives another memory
addA("par_mem2_hand_on", "", "k4 n s a s",
     "Fixpoint k4 (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => k4 m u (x + 1) t end.\n")
addA("par_mem2_swap", "", "k5 n s s a",
     "Fixpoint k5 (n : nat) (u t : mem) (x : int) : int := match n with O => rd 0 x t | S m => k5 m t u (x + 1) end.\n")
addA("par_mem2_read_both", "", "k7 n s a s",
     "Fixpoint k7 (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x u + rd 1 x t | S m => k7 m u (x + 1) t end.\n")
addA("par_mem2_write_both", "", "rd 0 0 (k6 n s a s)",
     "Fixpoint k6 (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => let v := upd 0 x x t in k6 m v (x + 1) v end.\n")
addA("par_mem2_write_num", "", "k9 n s a s",
     "Fixpoint k9 (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x u | S m => let v := upd 0 x x t in k9 m v (x + 1) v end.\n")
addA("par_mem2_three", "", "k8 n s s a s",
     "Fixpoint k8 (n : nat) (u w : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t + rd 1 x w | S m => k8 m t u (x + 1) w end.\n")
addA("par_mem2_bool", "", "if kb n s a s then a else b",
     "Fixpoint kb (n : nat) (u : mem) (x : int) (t : mem) : bool := match n with O => rd 0 x u <? rd 0 x t | S m => kb m u (x + 1) t end.\n")
addA("par_mem2_record", "", "f1 (kr n s a s)",
     "Fixpoint kr (n : nat) (u : mem) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 x u) x (rd 0 x t) | S m => kr m u (x + 1) t end.\n")
addA("par_mem2_pair", "", "let '(v, w) := kp n s a s in v + rd 0 0 w",
     "Fixpoint kp (n : nat) (u : mem) (x : int) (t : mem) : int * mem := match n with O => (rd 0 x u, t) | S m => let v := upd 0 x x t in kp m v (x + 1) v end.\n")
addA("par_mem2_order", "", "kq s n a s",
     "Fixpoint kq (u : mem) (n : nat) (x : int) (t : mem) {struct n} : int := match n with O => rd 0 x u | S m => kq t m (x + 1) u end.\n")
addA("par_mem2_mem_first", "", "rd 0 0 (kq s s n a)",
     "Fixpoint kq (u t : mem) (n : nat) (x : int) {struct n} : mem := match n with O => t | S m => let v := upd 0 x x t in kq v v m (x + 1) end.\n")
addA("par_mem2_call_made", "", "k4 n (upd 0 a b s) a (upd 0 a b s)",
     "Fixpoint k4 (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => k4 m u (x + 1) t end.\n")
addA("par_mem2_caller_two", "", "kc s n a s",
     "Fixpoint k4 (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => k4 m u (x + 1) t end.\nFixpoint kc (u : mem) (n : nat) (x : int) (t : mem) {struct n} : int := match n with O => k4 n u x t | S m => kc u m (x + 1) t + k4 m t x u end.\n")
addA("par_mem2_big", "", "kg s a s",
     "Definition kg (u : mem) (x : int) (t : mem) : int :=\n  let v1 := rd 0 x u * 1 + rd 1 x t in\n  let v2 := rd 0 x u * 2 + rd 1 x t in\n  let v3 := rd 0 x u * 3 + rd 1 x t in\n  let v4 := rd 0 x u * 4 + rd 1 x t in\n  let v5 := rd 0 x u * 5 + rd 1 x t in\n  let v6 := rd 0 x u * 6 + rd 1 x t in\n  let v7 := rd 0 x u * 7 + rd 1 x t in\n  let v8 := rd 0 x u * 8 + rd 1 x t in\n  let v9 := rd 0 x u * 9 + rd 1 x t in\n  let v10 := rd 0 x u * 10 + rd 1 x t in\n  let v11 := rd 0 x u * 11 + rd 1 x t in\n  let v12 := rd 0 x u * 12 + rd 1 x t in\n  let v13 := rd 0 x u * 13 + rd 1 x t in\n  let v14 := rd 0 x u * 14 + rd 1 x t in\n  let v15 := rd 0 x u * 15 + rd 1 x t in\n  v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12 + v13 + v14 + v15.\n")
addA("par_mem2_tmpl", "", "kf n s a h s",
     "Fixpoint kf (n : nat) (u : mem) (x : int) (f : int -> int -> int) (t : mem) : int := match n with O => rd 0 x u + rd 1 x t | S m => kf m u (f x x) f t end.\n")
addA("par_mem2_tmpl_cap", "", "kf n s a (fun y z => y + z + b) s",
     "Fixpoint kf (n : nat) (u : mem) (x : int) (f : int -> int -> int) (t : mem) : int := match n with O => rd 0 x u + rd 1 x t | S m => kf m u (f x x) f t end.\n")
addA("par_mem2_mutual", "", "ka n s a s",
     "Fixpoint ka (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x u | S m => kd m t (x + 1) u end\nwith kd (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 1 x t | S m => ka m u (x + 2) t end.\n")
addA("par_mem2_mutual_write", "", "rd 0 0 (ka n s a s)",
     "Fixpoint ka (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => let v := upd 0 x x t in kd m v (x + 1) v end\nwith kd (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => let v := upd 1 x x u in ka m v (x + 2) v end.\n")
addA("par_mem2_mutual_moved", "", "rd 0 0 (ka n s a s)",
     "Fixpoint ka (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kd m u (x + 1) (upd 0 x x t) end\nwith kd (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => ka m u (x + 2) (upd 1 x x t) end.\n")
addA("par_mem2_tmpl_dead", "", "rd 0 0 (kf n s a h s)",
     "Fixpoint kf (n : nat) (u : mem) (x : int) (f : int -> int -> int) (t : mem) : mem := match n with O => t | S m => kf m u (f x x) f (upd 0 x x t) end.\n")
addA("par_mem2_lfix_dead", "", "rd 0 0 (ll n s a s)",
     "Definition ll (n : nat) (u : mem) (x : int) (t : mem) : mem := (fix go (k : nat) (v : mem) (y : int) (w : mem) : mem := match k with O => w | S j => go j v (y + 1) (upd 0 y y w) end) n u x t.\n")
addA("par_mem2_dead_pair", "", "let '(v, w) := kw n s a s in v + rd 0 0 w",
     "Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => kw m u (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_dead_pair_param", "", "kw n s (a, s)",
     "Fixpoint kw (n : nat) (u : mem) (p : int * mem) : int := match n with O => fst p + rd 0 0 (snd p) | S m => kw m u (fst p + 1, upd 0 (fst p) 1 (snd p)) end.\n")
addA("par_mem2_hand_on_pair_param", "", "kw n s (a, s)",
     "Fixpoint kw (n : nat) (u : mem) (p : int * mem) : int := match n with O => fst p + rd 0 0 (snd p) | S m => kw m u (fst p + 1, snd p) end.\n")
addA("par_mem2_lfix", "", "ll n s a s",
     "Definition ll (n : nat) (u : mem) (x : int) (t : mem) : int := (fix go (k : nat) (v : mem) (y : int) (w : mem) : int := match k with O => rd 0 y v + rd 1 y w | S j => go j w (y + 1) v end) n u x t.\n")
addA("par_mem2_dead_write", "", "rd 0 0 (kw n s a s)",
     "Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m u (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_dead_num", "", "kw n s a s",
     "Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => kw m u (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_dead_bool", "", "if kw n s a s then a else b",
     "Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : bool := match n with O => rd 0 x t <? 3 | S m => kw m u (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_dead_record", "", "f1 (kw n s a s)",
     "Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 x t) x x | S m => kw m u (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_dead_two", "", "rd 0 0 (kw n s s a s)",
     "Fixpoint kw (n : nat) (u v : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m u v (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_dead_order", "", "rd 0 0 (kw s n a s)",
     "Fixpoint kw (u : mem) (n : nat) (x : int) (t : mem) {struct n} : mem := match n with O => t | S m => kw u m (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_dead_other", "", "k4 n (upd 0 a b s) a s",
     "Fixpoint k4 (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => k4 m u (x + 1) t end.\n")
addA("par_mem2_dead_moved", "", "rd 0 0 (kw n s a s)",
     "Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m t (x + 1) (upd 0 x x t) end.\n")
addA("par_mem2_live", "", "rd 0 0 (cp n s s a)",
     "Fixpoint cp (n : nat) (u t : mem) (x : int) : mem := match n with O => t | S m => cp m u (upd 0 x (rd 1 x u) t) (x + 1) end.\n")
addA("par_mem2_live_control", "", "rd 0 0 (cp n s a)",
     "Fixpoint cp (n : nat) (t : mem) (x : int) : mem := match n with O => t | S m => cp m (upd 0 x (rd 1 x t) t) (x + 1) end.\n")
addA("par_mem2_live_given", "", "kr n s (fill n 0 s) a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nFixpoint kr (n : nat) (u t : mem) (x : int) : int := match n with O => rd 0 x u + rd 0 x t | S m => kr m u t (x + 1) end.\n")
A.append(("par_mem2_root", "Definition go2 (n : nat) (u : mem) (a b : int) (s : mem) : int := rd 0 a u + rd 1 b s.\nDefinition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  go2 (kq_nat (kq_arg 0)) (kq_input 0) (kq_arg 1) (kq_arg 2) (kq_input 0).\n"))
# a memory made in place and read inside an expression (step 52): bound by a let
addA("par_made_left", "", "rd 0 2 (fill n 0 s) + a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_right", "", "a + rd 0 2 (fill n 0 s)",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_upd", "", "rd 0 2 (upd 0 a b s) + a",
     "")
addA("par_made_let", "", "rd 0 2 (let t := upd 0 a b s in upd 1 a b t) + a",
     "")
addA("par_made_chain", "", "rd 0 2 (fill n 0 (fill n 1 s)) + a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_size", "", "kq_size 0 (fill n 0 s) + a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_rd32", "", "rd32 0 2 (upd32 0 a b s) + a",
     "")
addA("par_made_rd8", "", "rd8 0 2 (upd8 0 a b s) + a",
     "")
addA("par_made_rd16", "", "rd16 0 2 (upd16 0 a b s) + a",
     "")
addA("par_made_test", "", "if rd 0 2 (fill n 0 s) <? a then a else b",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_let_val", "", "let x := rd 0 2 (fill n 0 s) in x + a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_arg_helper", "", "h (rd 0 2 (fill n 0 s)) a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_arg_call", "", "ff n (rd 0 2 (fill n 0 s))",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("par_made_reader", "", "sm n a (fill n 0 s) + 1",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nFixpoint sm (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => sm m (x + rd 1 x t) t end.\n")
addA("par_made_writer", "", "wn n (fill n 0 s) + a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nFixpoint wn (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wn m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_made_old_after", "", "rd 0 2 (fill n 0 s) + rd 1 0 s",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_old_before", "", "rd 1 0 s + rd 0 2 (fill n 0 s)",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_same_twice", "", "rd 0 2 (fill n 0 s) + rd 0 3 (fill n 0 s)",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_seq", "", "let t := fill n 0 s in rd 0 2 t + rd 0 3 (fill n 1 t)",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_in_bool", "", "if kb n a s then a else b",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nDefinition kb (n : nat) (x : int) (t : mem) : bool := rd 0 2 (fill n 0 t) <? x.\n")
addA("par_made_in_record", "", "f1 (kr n a s)",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nDefinition kr (n : nat) (x : int) (t : mem) : r3 := mk3 (rd 0 2 (fill n 0 t) + 1) x 0.\n")
addA("par_made_in_fix", "", "kq n a s",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nFixpoint kq (n : nat) (x : int) (t : mem) : int := match n with O => x + rd 0 2 (fill 1 x t) | S m => kq m (x + 1) t end.\n")
addA("par_made_in_fix_rec", "", "kq2 n a s",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nFixpoint kq2 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => rd 0 2 (fill 1 x t) + kq2 m x (fill 1 x t) end.\n")
addA("par_made_helper", "", "rdh 2 (fill n 0 s) + a",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nDefinition rdh (i : int) (t : mem) : int := rd 0 i t + 1.\n")
addA("par_own_let_mem", "", "kq3 n a s",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := upd 0 x x t in kq3 m x u + 1 end.\n")
addA("par_own_let_mem_read", "", "kq3 n a s",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := upd 0 x x t in rd 0 2 u + kq3 m x u end.\n")
addA("par_own_let_mem_right", "", "kq3 n a s",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := upd 0 x x t in kq3 m x u + rd 0 2 u end.\n")
addA("par_own_let_mem_call", "", "kq3 n a s",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\nFixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := fill 1 x t in rd 0 2 u + kq3 m x u end.\n")
addA("par_own_let_mem_bool", "", "if kq3 n a s then a else b",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : bool := match n with O => x <? 3 | S m => let u := upd 0 x x t in negb (kq3 m x u) end.\n")
addA("par_own_let_mem_record", "", "f1 (kq3 n a s)",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 x x x | S m => let u := upd 0 x x t in let w := kq3 m x u in mk3 (f1 w + 1) x 0 end.\n")
addA("par_own_let_mem_test", "", "kq3 n a s",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := upd 0 x x t in if kq3 m x u <? 3 then x else 1 end.\n")
addA("par_own_let_mem_let", "", "kq3 n a s",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := upd 0 x x t in let v := kq3 m x u + 1 in v * 2 end.\n")
addA("par_own_let_mem_let_bool", "", "kq3 n a s",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := upd 0 x x t in let c := kq3 m x u <? 3 in if c then x else 1 end.\n")
addA("par_own_let_mem_two", "", "kq3 n a s",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => let u := upd 0 x x t in let v := upd 1 x x u in kq3 m x v + rd 1 2 v + rd 0 0 u end.\n")
addA("par_own_let_mem_match", "", "f1 (kq3 n a s)",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 x x x | S m => let u := upd 0 x x t in match kq3 m x u with mk3 p q r => mk3 (p + 1) q r end end.\n")
addA("par_own_let_mem_pair", "", "let '(v, w) := kq3 n a s in v + rd 0 0 w",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => let u := upd 0 x x t in let '(v, w) := kq3 m x u in (v + 1, w) end.\n")
addA("par_own_let_mem_mem", "", "rd 0 0 (kq3 n a s)",
     "Fixpoint kq3 (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => let u := upd 0 x x t in upd 1 x (rd 0 x u) (kq3 m x u) end.\n")
addA("par_made_two", "", "rd 0 2 (fill n 0 s) + rd 0 3 (fill n 1 s)",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
addA("par_made_old_write", "", "rd 1 0 (upd 1 (rd 0 2 (fill n 0 s)) a s)",
     "Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.\n")
# programs across modules (step 51): each sort of function in a nested module, two levels, two modules with one short name each, the
# entry in a module, an alias, an inclusion, a transparent ascription, a functor's instances, a section's closed variables; a sealed
# module has no body the kernel can see: the pin
addA("mod_fn", "", "Lib.hh a b",
     "Module Lib.\nDefinition hh (x y : int) : int := x * 3 + y.\nEnd Lib.\n")
addA("mod_fix", "", "Lib.ff n a",
     "Module Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd Lib.\n")
addA("mod_write", "", "rd 0 0 (Lib.ww n a s)",
     "Module Lib.\nFixpoint ww (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => ww m (x + 1) (upd 0 x x t) end.\nEnd Lib.\n")
addA("mod_write_num", "", "Lib.wn n a s",
     "Module Lib.\nFixpoint wn (n : nat) (x : int) (t : mem) : int := match n with O => rd 0 0 t | S m => wn m (x + 1) (upd 0 0 x t) end.\nEnd Lib.\n")
addA("mod_read", "", "Lib.sm n a s",
     "Module Lib.\nFixpoint sm (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => sm m (x + rd 1 x t) t end.\nEnd Lib.\n")
addA("mod_bool", "", "if Lib.ev n a then a else b",
     "Module Lib.\nFixpoint ev (n : nat) (x : int) : bool := match n with O => x <? 3 | S m => ev m (x + 1) end.\nEnd Lib.\n")
addA("mod_pm", "", "let '(x, t) := Lib.g n a s in x + rd 0 0 t",
     "Module Lib.\nFixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\nEnd Lib.\n")
addA("mod_record", "", "Lib.mid (Lib.mkp a b)",
     "Module Lib.\nRecord pt := mkp { px : int; py : int }.\nDefinition mid (p : pt) : int := px p + py p.\nEnd Lib.\n")
addA("mod_record_fix", "", "Lib.sumr n (Lib.mkp a b)",
     "Module Lib.\nRecord pt := mkp { px : int; py : int }.\nFixpoint sumr (n : nat) (p : pt) : int := match n with O => px p + py p | S m => sumr m (mkp (py p) (px p + 1)) end.\nEnd Lib.\n")
addA("mod_record_ret", "", "Lib.px (Lib.mv n a b)",
     "Module Lib.\nRecord pt := mkp { px : int; py : int }.\nFixpoint mv (n : nat) (x y : int) : pt := match n with O => mkp x y | S m => mv m (y + 1) x end.\nEnd Lib.\n")
addA("mod_record_holds", "", "Lib.qs (Lib.mkq (Lib.mkp a b) a)",
     "Module Lib.\nRecord pt := mkp { px : int; py : int }.\nRecord pq := mkq { q1 : pt; q2 : int }.\nDefinition qs (w : pq) : int := px (q1 w) + py (q1 w) + q2 w.\nEnd Lib.\n")
addA("mod_data", "", "Lib.tv (Lib.tm n a)",
     "Module Lib.\nInductive tg := T0 | T1 (x : int) | T2 (x y : int).\nFixpoint tm (n : nat) (x : int) : tg := match n with O => if x <? 3 then T1 x else T2 x x | S m => tm m (x + 1) end.\nDefinition tv (w : tg) : int := match w with T0 => 0 | T1 x => x | T2 x y => x + y end.\nEnd Lib.\n")
addA("mod_const", "", "a + Lib.c",
     "Module Lib.\nDefinition c : int := 7.\nEnd Lib.\n")
addA("mod_big", "", "Lib.big a b",
     "Module Lib.\nDefinition big (x y : int) : int :=\n  let v1 := x * 1 + y in\n  let v2 := x * 2 + y in\n  let v3 := x * 3 + y in\n  let v4 := x * 4 + y in\n  let v5 := x * 5 + y in\n  let v6 := x * 6 + y in\n  let v7 := x * 7 + y in\n  let v8 := x * 8 + y in\n  let v9 := x * 9 + y in\n  let v10 := x * 10 + y in\n  let v11 := x * 11 + y in\n  let v12 := x * 12 + y in\n  let v13 := x * 13 + y in\n  let v14 := x * 14 + y in\n  let v15 := x * 15 + y in\n  v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12 + v13 + v14 + v15.\nEnd Lib.\n")
addA("mod_two_levels", "", "Lib.In.ff n a",
     "Module Lib.\nModule In.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd In.\nEnd Lib.\n")
addA("mod_up", "", "Lib.ff n a",
     "Module Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => h x x | S m => ff m (h x 1) end.\nEnd Lib.\n")
addA("mod_up_fix", "", "Lib.ff n a",
     "Fixpoint wf (n : nat) (x : int) : int := match n with O => x | S m => wf m (x + 1) end.\nModule Lib.\nDefinition ff (n : nat) (x : int) : int := wf n x + 1.\nEnd Lib.\n")
addA("mod_two_mods", "", "A2.gg n a",
     "Module A1.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd A1.\nModule A2.\nFixpoint gg (n : nat) (x : int) : int := match n with O => A1.ff n x | S m => gg m (A1.ff n x) end.\nEnd A2.\n")
addA("mod_tmpl", "", "Lib.apl n a Lib.inc",
     "Module Lib.\nFixpoint apl (n : nat) (x : int) (f : int -> int) : int := match n with O => x | S m => apl m (f x) f end.\nDefinition inc (x : int) : int := x + 1.\nEnd Lib.\n")
addA("mod_tmpl_cap", "", "Lib.apl n a (fun x => x + b)",
     "Module Lib.\nFixpoint apl (n : nat) (x : int) (f : int -> int) : int := match n with O => x | S m => apl m (f x) f end.\nEnd Lib.\n")
addA("mod_tmpl_top", "", "fold n a b Lib.add2",
     "Module Lib.\nDefinition add2 (x y : int) : int := x + y + 2.\nEnd Lib.\n")
addA("mod_mutual", "", "if Lib.evn n then a else b",
     "Module Lib.\nFixpoint evn (n : nat) : bool := match n with O => true | S m => odd m end\nwith odd (n : nat) : bool := match n with O => false | S m => evn m end.\nEnd Lib.\n")
addA("mod_mutual_int", "", "Lib.mu1 n a",
     "Module Lib.\nFixpoint mu1 (n : nat) (x : int) : int := match n with O => x | S m => mu2 m (x + 1) end\nwith mu2 (n : nat) (x : int) : int := match n with O => x * 2 | S m => mu1 m (x + 2) end.\nEnd Lib.\n")
addA("mod_order", "", "Lib.pf a n",
     "Module Lib.\nFixpoint pf (x : int) (n : nat) {struct n} : int := match n with O => x | S m => pf (x + 1) m end.\nEnd Lib.\n")
addA("mod_order_def", "", "Lib.pn s a",
     "Module Lib.\nDefinition pn (t : mem) (x : int) : int := rd 0 x t.\nEnd Lib.\n")
addA("mod_lfix", "", "Lib.lo n a",
     "Module Lib.\nDefinition lo (n : nat) (x : int) : int := (fix go (k : nat) (y : int) : int := match k with O => y | S j => go j (y + 1) end) n x.\nEnd Lib.\n")
addA("mod_lift", "", "Lib.kl n a s",
     "Module Lib.\nFixpoint gg (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => gg m (x + 1) (upd 0 x x t) end.\nDefinition kp (p : int * mem) : int := fst p + rd 0 0 (snd p).\nDefinition kl (n : nat) (x : int) (t : mem) : int := let p := gg n x t in kp p + 1.\nEnd Lib.\n")
addA("mod_same_fn", "", "A1.hh a + A2.hh b",
     "Module A1.\nDefinition hh (x : int) : int := x + 1.\nEnd A1.\nModule A2.\nDefinition hh (x : int) : int := x + 2.\nEnd A2.\n")
addA("mod_same_fix", "", "A1.ff n a + A2.ff n b",
     "Module A1.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd A1.\nModule A2.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x * 2 | S m => ff m (x + 2) end.\nEnd A2.\n")
addA("mod_same_write", "", "rd 0 0 (A1.ww n a (A2.ww n b s))",
     "Module A1.\nFixpoint ww (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => ww m (x + 1) (upd 0 x x t) end.\nEnd A1.\nModule A2.\nFixpoint ww (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => ww m (x + 2) (upd 1 x x t) end.\nEnd A2.\n")
addA("mod_same_tmpl", "", "A1.apl n a h1 + A2.apl n b h2",
     "Definition h1 (x : int) : int := x + 1.\nDefinition h2 (x : int) : int := x + 2.\nModule A1.\nFixpoint apl (n : nat) (x : int) (f : int -> int) : int := match n with O => x | S m => apl m (f x) f end.\nEnd A1.\nModule A2.\nFixpoint apl (n : nat) (x : int) (f : int -> int) : int := match n with O => x | S m => apl m (f (x + 1)) f end.\nEnd A2.\n")
addA("mod_same_order", "", "A1.pf a n + A2.pf b n",
     "Module A1.\nFixpoint pf (x : int) (n : nat) {struct n} : int := match n with O => x | S m => pf (x + 1) m end.\nEnd A1.\nModule A2.\nFixpoint pf (x : int) (n : nat) {struct n} : int := match n with O => x | S m => pf (x + 2) m end.\nEnd A2.\n")
addA("mod_same_order_def", "", "A1.pn s a + A2.pn s b",
     "Module A1.\nDefinition pn (t : mem) (x : int) : int := rd 0 x t.\nEnd A1.\nModule A2.\nDefinition pn (t : mem) (x : int) : int := rd 1 x t.\nEnd A2.\n")
addA("mod_same_mutual", "", "(if A1.evn n then a else b) + (if A2.evn n then a else b)",
     "Module A1.\nFixpoint evn (n : nat) : bool := match n with O => true | S m => odd m end\nwith odd (n : nat) : bool := match n with O => false | S m => evn m end.\nEnd A1.\nModule A2.\nFixpoint evn (n : nat) : bool := match n with O => false | S m => odd m end\nwith odd (n : nat) : bool := match n with O => true | S m => evn m end.\nEnd A2.\n")
addA("mod_same_lift", "", "if a <? b then A1.kl n a s else A2.kl n b s",
     "Module A1.\nFixpoint gg (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => gg m (x + 1) (upd 0 x x t) end.\nDefinition kp (p : int * mem) : int := fst p + rd 0 0 (snd p).\nDefinition kl (n : nat) (x : int) (t : mem) : int := let p := gg n x t in kp p + 1.\nEnd A1.\nModule A2.\nFixpoint gg (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => gg m (x + 1) (upd 0 x x t) end.\nDefinition kp (p : int * mem) : int := fst p + rd 0 0 (snd p).\nDefinition kl (n : nat) (x : int) (t : mem) : int := let p := gg n x t in kp p + 2.\nEnd A2.\n")
addA("mod_same_lfix", "", "A1.lo n a + A2.lo n b",
     "Module A1.\nDefinition lo (n : nat) (x : int) : int := (fix go (k : nat) (y : int) : int := match k with O => y | S j => go j (y + 1) end) n x.\nEnd A1.\nModule A2.\nDefinition lo (n : nat) (x : int) : int := (fix go (k : nat) (y : int) : int := match k with O => y | S j => go j (y + 2) end) n x.\nEnd A2.\n")
addA("mod_same_record", "", "A1.m (A1.mk a b) + A2.m (A2.mk a b a)",
     "Module A1.\nRecord rr := mk { p1 : int; p2 : int }.\nDefinition m (w : rr) : int := p1 w + p2 w.\nEnd A1.\nModule A2.\nRecord rr := mk { p1 : int; p2 : int; p3 : int }.\nDefinition m (w : rr) : int := p1 w + p2 w * p3 w.\nEnd A2.\n")
addA("mod_same_top", "", "ff n a + top n b",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition top := ff.\nModule Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x * 2 | S m => ff m (x + 2) end.\nEnd Lib.\nImport Lib.\n")
addA("mod_import", "", "ff n a",
     "Module Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd Lib.\nImport Lib.\n")
addA("mod_alias", "", "N.ff n a",
     "Module Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd Lib.\nModule N := Lib.\n")
addA("mod_include", "", "B.ff n a",
     "Module Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd Lib.\nModule B.\nInclude Lib.\nEnd B.\n")
addA("mod_ascribe", "", "Lib.ff n a",
     "Module Type T.\nParameter ff : nat -> int -> int.\nEnd T.\nModule Lib <: T.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd Lib.\n")
addA("mod_sealed", "", "S.ff n a",
     "Module Type T.\nParameter ff : nat -> int -> int.\nEnd T.\nModule S : T.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd S.\n")
addA("mod_functor", "", "I.ff n a",
     "Module Type TC.\nParameter c : int.\nEnd TC.\nModule C3 <: TC.\nDefinition c : int := 3.\nEnd C3.\nModule C4 <: TC.\nDefinition c : int := 4.\nEnd C4.\nModule F (X : TC).\nFixpoint ff (n : nat) (x : int) : int := match n with O => x + X.c | S m => ff m (x + 1) end.\nEnd F.\nModule I := F(C3).\n")
addA("mod_functor_two", "", "I.ff n a + J.ff n b",
     "Module Type TC.\nParameter c : int.\nEnd TC.\nModule C3 <: TC.\nDefinition c : int := 3.\nEnd C3.\nModule C4 <: TC.\nDefinition c : int := 4.\nEnd C4.\nModule F (X : TC).\nFixpoint ff (n : nat) (x : int) : int := match n with O => x + X.c | S m => ff m (x + 1) end.\nEnd F.\nModule I := F(C3).\nModule J := F(C4).\n")
addA("mod_section", "", "fk b n a + dk b a",
     "Section Sc.\nVariable k : int.\nFixpoint fk (n : nat) (x : int) : int := match n with O => x + k | S m => fk m (x + k) end.\nDefinition dk (x : int) : int := x * k.\nEnd Sc.\n")
addA("mod_section_in_mod", "", "Lib.fk b n a + Lib.dk b a",
     "Module Lib.\nSection Sc.\nVariable k : int.\nFixpoint fk (n : nat) (x : int) : int := match n with O => x + k | S m => fk m (x + k) end.\nDefinition dk (x : int) : int := x * k.\nEnd Sc.\nEnd Lib.\n")
addA("mod_lemma", "", "Lib.ff n a",
     "Module Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nLemma ff_0 (x : int) : ff O x = x.\nProof. reflexivity. Qed.\nEnd Lib.\n")
addA("mod_parameter", "", "ext a",
     "Parameter ext : int -> int.\n")
addA("mod_sealed_helper", "", "kh n a",
     "Module Type T.\nParameter ff : nat -> int -> int.\nEnd T.\nModule S : T.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd S.\nDefinition kh (n : nat) (x : int) : int := S.ff n x + 1.\n")
addA("mod_prime_order", "", "Lib.pf' a n",
     "Module Lib.\nFixpoint pf' (x : int) (n : nat) {struct n} : int := match n with O => x | S m => pf' (x + 1) m end.\nEnd Lib.\n")
addA("mod_prim_record", "", "Lib.pa (Lib.mkq2 a b)",
     "Module Lib.\nSet Primitive Projections.\nRecord pr2 := mkq2 { pa : int; pb : int }.\nUnset Primitive Projections.\nEnd Lib.\n")
addA("mod_type_alias", "", "Lib.kk a",
     "Module Lib.\nDefinition myint := int.\nDefinition kk (x : myint) : myint := x + 1.\nEnd Lib.\n")
addA("mod_section_let", "", "dl b a",
     "Section Sl.\nVariable k : int.\nLet k2 : int := k + 1.\nDefinition dl (x : int) : int := x * k2.\nEnd Sl.\n")
addA("mod_section_let_fix", "", "fl b n a",
     "Section Sf.\nVariable k : int.\nLet k2 : int := k + 1.\nFixpoint fl (n : nat) (x : int) : int := match n with O => x + k2 | S m => fl m (x + k2) end.\nEnd Sf.\n")
addA("mod_section_let_two", "", "d2 b a a",
     "Section S2.\nVariable k : int.\nLet k2 : int := k + 1.\nVariable j : int.\nLet k3 : int := j * k2.\nDefinition d2 (x : int) : int := x * k3 + j.\nEnd S2.\n")
addA("mod_section_let_big", "", "bl b a",
     "Section Sb.\nVariable k : int.\nLet k2 : int := k + 1.\nDefinition bl (x : int) : int :=\n  let y := k2 in\n  let v1 := x * 1 + y in\n  let v2 := x * 2 + y in\n  let v3 := x * 3 + y in\n  let v4 := x * 4 + y in\n  let v5 := x * 5 + y in\n  let v6 := x * 6 + y in\n  let v7 := x * 7 + y in\n  let v8 := x * 8 + y in\n  let v9 := x * 9 + y in\n  let v10 := x * 10 + y in\n  let v11 := x * 11 + y in\n  let v12 := x * 12 + y in\n  let v13 := x * 13 + y in\n  let v14 := x * 14 + y in\n  let v15 := x * 15 + y in\n  v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12 + v13 + v14 + v15.\nEnd Sb.\n")
addA("par_let_then_fun", "", "lt1 a b",
     "Definition lt1 (x : int) : int -> int := let y := x + 1 in fun z => z * y.\n")
addA("par_app_let", "", "(let y := a + 1 in fun x => x * y) b",
     "")
addA("par_let_then_fun_big", "", "lt2 a b",
     "Definition lt2 (x : int) : int -> int :=\n let w := x + 1 in fun y =>\n  let v1 := x * 1 + y in\n  let v2 := x * 2 + y in\n  let v3 := x * 3 + y in\n  let v4 := x * 4 + y in\n  let v5 := x * 5 + y in\n  let v6 := x * 6 + y in\n  let v7 := x * 7 + y in\n  let v8 := x * 8 + y in\n  let v9 := x * 9 + y in\n  let v10 := x * 10 + y in\n  let v11 := x * 11 + y in\n  let v12 := x * 12 + y in\n  let v13 := x * 13 + y in\n  let v14 := x * 14 + y in\n  let v15 := x * 15 + y in\n  v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12 + v13 + v14 + v15.\n")
addA("mod_class", "", "Lib.useit a",
     "Module Lib.\nClass Cl := { cv : int }.\n#[export] Instance i3 : Cl := { cv := 3 }.\nDefinition useit (x : int) : int := x + cv.\nEnd Lib.\n")
addA("mod_shared", "", "rd32 5 a s",
     "Module Cfg.\nDefinition kq_shared : list int := cons 6 nil.\nEnd Cfg.\n")
addA("mod_shared_plain", "", "rd32 6 a s",
     "Module Cfg.\nDefinition kq_shared : list int := cons 6 nil.\nEnd Cfg.\n")
addA("par_name_like_derived", "", "foo__c3 n a + bar__o n b + baz__cblk n a + qux__on a b",
     "Fixpoint foo__c3 (n : nat) (x : int) : int := match n with O => x | S m => foo__c3 m (x + 1) end.\nFixpoint bar__o (n : nat) (x : int) : int := match n with O => x | S m => bar__o m (x + 2) end.\nFixpoint baz__cblk (n : nat) (x : int) : int := match n with O => x | S m => baz__cblk m (x + 3) end.\nDefinition qux__on (x y : int) : int := x + y.\n")
A.append(("mod_section_let_root", "Section Sr.\nVariable k : int.\nLet k2 : int := k + 1.\nDefinition go2 (n : nat) (a b : int) (s : mem) : int := a * k2 + b.\nEnd Sr.\nDefinition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  go2 3 (kq_nat (kq_arg 0)) (kq_arg 1) (kq_arg 2) (kq_input 0).\n"))
A.append(("mod_root", "Module P.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition go " + SIG + " : int := ff n a + b.\nEnd P.\nDefinition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  P.go (kq_nat (kq_arg 0)) (kq_arg 1) (kq_arg 2) (kq_input 0).\n"))
A.append(("mod_root_order", "Module P.\nDefinition go (s : mem) (a : int) (n : nat) (b : int) : int := rd 0 a s + b.\nEnd P.\nDefinition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  P.go (kq_input 0) (kq_arg 1) (kq_nat (kq_arg 0)) (kq_arg 2).\n"))
A.append(("mod_root_fix", "Module P.\nFixpoint go (n : nat) (a b : int) (s : mem) : int := match n with O => a + b | S m => go m (a + 1) b s end.\nEnd P.\nDefinition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  P.go (kq_nat (kq_arg 0)) (kq_arg 1) (kq_arg 2) (kq_input 0).\n"))
# programs across files (step 51): each sort of function, a record, a data type, a function given, in a file the program requires
LIBS['A_file_fn_lib'] = 'From KQ Require Import KQRun.\nDefinition hh (x y : int) : int := x * 3 + y.\n'
addA("file_fn", "", "hh a b",
     "Require Import A_file_fn_lib.\n")
LIBS['A_file_fix_lib'] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n'
addA("file_fix", "", "ff n a",
     "Require Import A_file_fix_lib.\n")
LIBS['A_file_write_lib'] = 'From KQ Require Import KQRun.\nFixpoint ww (n : nat) (x : int) (t : mem) : mem := match n with O => t | S m => ww m (x + 1) (upd 0 x x t) end.\n'
addA("file_write", "", "rd 0 0 (ww n a s)",
     "Require Import A_file_write_lib.\n")
LIBS['A_file_write_num_lib'] = 'From KQ Require Import KQRun.\nFixpoint wn (n : nat) (x : int) (t : mem) : int := match n with O => rd 0 0 t | S m => wn m (x + 1) (upd 0 0 x t) end.\n'
addA("file_write_num", "", "wn n a s",
     "Require Import A_file_write_num_lib.\n")
LIBS['A_file_read_lib'] = 'From KQ Require Import KQRun.\nFixpoint sm (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => sm m (x + rd 1 x t) t end.\n'
addA("file_read", "", "sm n a s",
     "Require Import A_file_read_lib.\n")
LIBS['A_file_bool_lib'] = 'From KQ Require Import KQRun.\nFixpoint ev (n : nat) (x : int) : bool := match n with O => x <? 3 | S m => ev m (x + 1) end.\n'
addA("file_bool", "", "if ev n a then a else b",
     "Require Import A_file_bool_lib.\n")
LIBS['A_file_pm_lib'] = 'From KQ Require Import KQRun.\nFixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.\n'
addA("file_pm", "", "let '(x, t) := g n a s in x + rd 0 0 t",
     "Require Import A_file_pm_lib.\n")
LIBS['A_file_record_lib'] = 'From KQ Require Import KQRun.\nRecord pt := mkp { px : int; py : int }.\nDefinition mid (p : pt) : int := px p + py p.\n'
addA("file_record", "", "mid (mkp a b)",
     "Require Import A_file_record_lib.\n")
LIBS['A_file_record_fix_lib'] = 'From KQ Require Import KQRun.\nRecord pt := mkp { px : int; py : int }.\nFixpoint sumr (n : nat) (p : pt) : int := match n with O => px p + py p | S m => sumr m (mkp (py p) (px p + 1)) end.\n'
addA("file_record_fix", "", "sumr n (mkp a b)",
     "Require Import A_file_record_fix_lib.\n")
LIBS['A_file_record_ret_lib'] = 'From KQ Require Import KQRun.\nRecord pt := mkp { px : int; py : int }.\nFixpoint mv (n : nat) (x y : int) : pt := match n with O => mkp x y | S m => mv m (y + 1) x end.\n'
addA("file_record_ret", "", "px (mv n a b)",
     "Require Import A_file_record_ret_lib.\n")
LIBS['A_file_record_holds_lib'] = 'From KQ Require Import KQRun.\nRecord pt := mkp { px : int; py : int }.\nRecord pq := mkq { q1 : pt; q2 : int }.\nDefinition qs (w : pq) : int := px (q1 w) + py (q1 w) + q2 w.\n'
addA("file_record_holds", "", "qs (mkq (mkp a b) a)",
     "Require Import A_file_record_holds_lib.\n")
LIBS['A_file_data_lib'] = 'From KQ Require Import KQRun.\nInductive tg := T0 | T1 (x : int) | T2 (x y : int).\nFixpoint tm (n : nat) (x : int) : tg := match n with O => if x <? 3 then T1 x else T2 x x | S m => tm m (x + 1) end.\nDefinition tv (w : tg) : int := match w with T0 => 0 | T1 x => x | T2 x y => x + y end.\n'
addA("file_data", "", "tv (tm n a)",
     "Require Import A_file_data_lib.\n")
LIBS['A_file_const_lib'] = 'From KQ Require Import KQRun.\nDefinition c : int := 7.\n'
addA("file_const", "", "a + c",
     "Require Import A_file_const_lib.\n")
LIBS['A_file_big_lib'] = 'From KQ Require Import KQRun.\nDefinition big (x y : int) : int :=\n  let v1 := x * 1 + y in\n  let v2 := x * 2 + y in\n  let v3 := x * 3 + y in\n  let v4 := x * 4 + y in\n  let v5 := x * 5 + y in\n  let v6 := x * 6 + y in\n  let v7 := x * 7 + y in\n  let v8 := x * 8 + y in\n  let v9 := x * 9 + y in\n  let v10 := x * 10 + y in\n  let v11 := x * 11 + y in\n  let v12 := x * 12 + y in\n  let v13 := x * 13 + y in\n  let v14 := x * 14 + y in\n  let v15 := x * 15 + y in\n  v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12 + v13 + v14 + v15.\n'
addA("file_big", "", "big a b",
     "Require Import A_file_big_lib.\n")
LIBS['A_file_tmpl_lib'] = 'From KQ Require Import KQRun.\nFixpoint apl (n : nat) (x : int) (f : int -> int) : int := match n with O => x | S m => apl m (f x) f end.\nDefinition inc (x : int) : int := x + 1.\n'
addA("file_tmpl", "", "apl n a inc",
     "Require Import A_file_tmpl_lib.\n")
LIBS['A_file_tmpl_cap_lib'] = 'From KQ Require Import KQRun.\nFixpoint apl (n : nat) (x : int) (f : int -> int) : int := match n with O => x | S m => apl m (f x) f end.\n'
addA("file_tmpl_cap", "", "apl n a (fun x => x + b)",
     "Require Import A_file_tmpl_cap_lib.\n")
LIBS['A_file_tmpl_given_lib'] = 'From KQ Require Import KQRun.\nFixpoint apl (n : nat) (x : int) (f : int -> int) : int := match n with O => x | S m => apl m (f x) f end.\n'
addA("file_tmpl_given", "", "apl n a h3",
     "Require Import A_file_tmpl_given_lib.\nDefinition h3 (x : int) : int := x + 3.\n")
LIBS['A_file_mutual_lib'] = 'From KQ Require Import KQRun.\nFixpoint evn (n : nat) : bool := match n with O => true | S m => odd m end\nwith odd (n : nat) : bool := match n with O => false | S m => evn m end.\n'
addA("file_mutual", "", "if evn n then a else b",
     "Require Import A_file_mutual_lib.\n")
LIBS['A_file_mutual_int_lib'] = 'From KQ Require Import KQRun.\nFixpoint mu1 (n : nat) (x : int) : int := match n with O => x | S m => mu2 m (x + 1) end\nwith mu2 (n : nat) (x : int) : int := match n with O => x * 2 | S m => mu1 m (x + 2) end.\n'
addA("file_mutual_int", "", "mu1 n a",
     "Require Import A_file_mutual_int_lib.\n")
LIBS['A_file_order_lib'] = 'From KQ Require Import KQRun.\nFixpoint pf (x : int) (n : nat) {struct n} : int := match n with O => x | S m => pf (x + 1) m end.\n'
addA("file_order", "", "pf a n",
     "Require Import A_file_order_lib.\n")
LIBS['A_file_order_def_lib'] = 'From KQ Require Import KQRun.\nDefinition pn (t : mem) (x : int) : int := rd 0 x t.\n'
addA("file_order_def", "", "pn s a",
     "Require Import A_file_order_def_lib.\n")
LIBS['A_file_lfix_lib'] = 'From KQ Require Import KQRun.\nDefinition lo (n : nat) (x : int) : int := (fix go (k : nat) (y : int) : int := match k with O => y | S j => go j (y + 1) end) n x.\n'
addA("file_lfix", "", "lo n a",
     "Require Import A_file_lfix_lib.\n")
LIBS['A_file_lift_lib'] = 'From KQ Require Import KQRun.\nFixpoint gg (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => gg m (x + 1) (upd 0 x x t) end.\nDefinition kp (p : int * mem) : int := fst p + rd 0 0 (snd p).\nDefinition kl (n : nat) (x : int) (t : mem) : int := let p := gg n x t in kp p + 1.\n'
addA("file_lift", "", "kl n a s",
     "Require Import A_file_lift_lib.\n")
LIBS['A_file_in_module_lib'] = 'From KQ Require Import KQRun.\nModule Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd Lib.\n'
addA("file_in_module", "", "Lib.ff n a",
     "Require Import A_file_in_module_lib.\n")
LIBS['A_file_lemma_lib'] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nLemma ff_0 (x : int) : ff O x = x.\nProof. reflexivity. Qed.\n'
addA("file_lemma", "", "ff n a",
     "Require Import A_file_lemma_lib.\n")
LIBS['A_file_unused_lib'] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition unused (n : nat) : nat := n + n.\n'
addA("file_unused", "", "ff n a",
     "Require Import A_file_unused_lib.\n")
LIBS['A_file_same_name_lib'] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x * 2 | S m => ff m (x + 2) end.\n'
addA("file_same_name", "", "ff n a + A_file_same_name_lib.ff n b",
     "Require Import A_file_same_name_lib.\nDefinition ff0 := A_file_same_name_lib.ff.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n\n")
LIBS['A_file_shared_lib'] = 'From KQ Require Import KQRun.\nDefinition kq_shared : list int := cons 6 nil.\n'
addA("file_shared", "", "rd32 5 a s",
     "Require Import A_file_shared_lib.\n")
LIBS['A_file_shared_plain_lib'] = 'From KQ Require Import KQRun.\nDefinition kq_shared : list int := cons 6 nil.\n'
addA("file_shared_plain", "", "rd32 6 a s",
     "Require Import A_file_shared_plain_lib.\n")
LIBS["A_file_load_lib"] = 'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n'
addA("file_load", "", "ff n a",
     "Load A_file_load_lib.\n")
LIBS['A_file_same_module_lib'] = 'From KQ Require Import KQRun.\nModule Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x * 2 | S m => ff m (x + 2) end.\nEnd Lib.\n'
addA("file_same_module", "", "Lib.ff n a + A_file_same_module_lib.Lib.ff n b",
     "Require Import A_file_same_module_lib.\nModule Lib.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nEnd Lib.\n")
LIBS['A_file_same_record_lib'] = 'From KQ Require Import KQRun.\nRecord rr := mk { p1 : int; p2 : int; p3 : int }.\nDefinition m (w : rr) : int := p1 w + p2 w * p3 w.\n'
addA("file_same_record", "", "m (mk a b) + A_file_same_record_lib.m (A_file_same_record_lib.mk a b a)",
     "Require Import A_file_same_record_lib.\nRecord rr := mk { p1 : int; p2 : int }.\nDefinition m (w : rr) : int := p1 w + p2 w.\n")
LIBS["ilib_A_file_holds_i"] = 'From KQ Require Import KQRun.\nRecord ip := imk { ia : int; ib : int }.\nRecord iq := iqk { ic : ip; id : int }.\nDefinition qs (w : iq) : int := ia (ic w) + id w.\n'
addA("file_holds_i", "", "qs (iqk (imk a b) a)",
     "Require Import ilib_A_file_holds_i.\n")
LIBS['A_file_lib_loop_lib'] = 'From KQ Require Import KQRun.\nFrom KQ.lib Require Import Loop.\nDefinition tot (a b : int) : int := loop_up 0 a b (fun i acc => acc + i).\n'
addA("file_lib_loop", "", "tot a b",
     "Require Import A_file_lib_loop_lib.\n")
LIBS["A_file_root_lib"] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition rg (n : nat) (a b : int) (s : mem) : int := ff n a + rd 0 b s.\n'
A.append(("file_root", "Require Import A_file_root_lib.\n" + 'Definition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  rg (kq_nat (kq_arg 0)) (kq_arg 1) (kq_arg 2) (kq_input 0).\n'))
LIBS["A_file_two_lib0"] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n'
LIBS["A_file_two_lib"] = 'From KQ Require Import KQRun.\nRequire Import A_file_two_lib0.\nDefinition hh (n : nat) (x : int) : int := ff n x + 1.\n'
addA("file_two", "", "hh n a",
     "Require Import A_file_two_lib.\n")
LIBS["A_file_export_lib0"] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n'
LIBS["A_file_export_lib"] = 'From KQ Require Import KQRun.\nRequire Export A_file_export_lib0.\n'
addA("file_export", "", "ff n a",
     "Require Import A_file_export_lib.\n")
LIBS["A_file_sub_d/X"] = 'From KQ Require Import KQRun.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n'
addA("file_sub", "", "ff n a",
     "From A_file_sub_d Require Import X.\n")
LIBS["A_file_two_sorts_lib"] = 'From KQ Require Import KQRun.\nRecord pt := mkp { px : int; py : int }.\nDefinition mid (p : pt) : int := px p + py p.\nFixpoint sumr (n : nat) (p : pt) : int := match n with O => px p + py p | S m => sumr m (mkp (py p) (px p + 1)) end.\n'
LIBS["A_file_two_sorts_lib2"] = 'From KQ Require Import KQRun.\nRequire Import A_file_two_sorts_lib.\nFixpoint qq (n : nat) (p : pt) (x : int) : int := match n with O => mid p + x | S m => qq m (mkp x (px p)) (sumr n p) end.\n'
addA("file_two_sorts", "", "qq n (mkp a b) a",
     "Require Import A_file_two_sorts_lib A_file_two_sorts_lib2.\n")
# a function giving back a boolean whose body writes the memory (step 48 continued): through a call that writes, its recursion
# given a memory it writes
addA("par_bool_write_call", "", "if kbr n a s then a else b",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nFixpoint kbr (n : nat) (x : int) (t : mem) : bool := match n with O => wr 3 t <? x | S m => kbr m (x + 1) t end.\n")
addA("par_bool_write_rec", "", "if kbw n a s then a else b",
     "Fixpoint kbw (n : nat) (x : int) (t : mem) : bool := match n with O => rd 0 0 t <? x | S m => kbw m (x + 1) (upd 0 x x t) end.\n")
# a function giving back a record whose body writes the memory (step 48 continued): through a call that writes, called inside
# an expression and in a test; its recursion given a memory it writes, bound by a let; and the places this step leaves: the
# function's own call not at the end in a record or a boolean that writes, a template giving back a record or a boolean that writes
addA("par_rec_write_call", "", "f1 (kqw n a s) + 1",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nDefinition kqw (n : nat) (x : int) (t : mem) : r3 := mk3 (wr n t) x 0.\n")
addA("par_rec_write_test", "", "if f2 (kqw n a s) <? 7 then a else b",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nDefinition kqw (n : nat) (x : int) (t : mem) : r3 := mk3 (wr n t) x 0.\n")
addA("par_rec_write_rec", "", "let w := krw n a s in f1 w * f2 w",
     "Fixpoint krw (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 0 t) x 0 | S m => krw m (x + 1) (upd 0 x x t) end.\n")
# a call that writes inside a record built in place: projected, bound by a let (the form a helper given a computed argument
# is written out in)
addA("par_write_in_rec_proj", "", "f1 (mk3 (wr n s) a 0) + 1",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_write_in_rec_let", "", "let w := mk3 (wr n s) a 0 in f1 w + 1",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\n")
addA("par_rec_write_own_let", "", "f2 (kro n a s)",
     "Fixpoint kro (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 0 t) x 0 | S m => let w := kro m (x + 1) (upd 0 x x t) in mk3 (f1 w + 1) (f2 w) (f3 w) end.\n")
addA("par_bool_write_own_neg", "", "if kbo n a s then a else b",
     "Fixpoint kbo (n : nat) (x : int) (t : mem) : bool := match n with O => rd 0 0 t <? x | S m => negb (kbo m (x + 1) (upd 0 x x t)) end.\n")
# the function's own call not at the end, bound by a let in a boolean, inside an expression in a record (step 48 continued)
addA("par_bool_write_own_let", "", "if kbl n a s then a else b",
     "Fixpoint kbl (n : nat) (x : int) (t : mem) : bool := match n with O => rd 0 0 t <? x | S m => let c := kbl m (x + 1) (upd 0 x x t) in negb c end.\n")
addA("par_rec_write_own_expr", "", "f2 (kre n a s)",
     "Fixpoint kre (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 0 t) x 0 | S m => mk3 (f1 (kre m (x + 1) (upd 0 x x t)) + 1) x 0 end.\n")
# and with a template (its copy), a mutual block of booleans and of records that write
addA("par_tmpl_bool_write_own", "", "if tbo n a (fun z => z + 1) s then a else b",
     "Fixpoint tbo (n : nat) (x : int) (g : int -> int) (t : mem) : bool := match n with O => rd 0 0 t <? g x | S m => negb (tbo m (g x) g (upd 0 x x t)) end.\n")
addA("par_tmpl_rec_write_own", "", "f1 (tro n a (fun z => z + 1) s)",
     "Fixpoint tro (n : nat) (x : int) (g : int -> int) (t : mem) : r3 := match n with O => mk3 (rd 0 0 t) (g x) 0 | S m => let w := tro m (g x) g (upd 0 x x t) in mk3 (f1 w + 1) (f2 w) (f3 w) end.\n")
addA("par_mutual_bool_write", "", "if evw n a s then a else b",
     "Fixpoint evw (n : nat) (x : int) (t : mem) : bool := match n with O => rd 0 0 t <? x | S m => odw m (x + 1) (upd 0 x x t) end\nwith odw (n : nat) (x : int) (t : mem) : bool := match n with O => x <? rd 0 0 t | S m => evw m (x + 1) (upd 0 x x t) end.\n")
addA("par_mutual_rec_write", "", "f1 (evr n a s)",
     "Fixpoint evr (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 0 t) x 0 | S m => odr m (x + 1) (upd 0 x x t) end\nwith odr (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 x (rd 0 0 t) 1 | S m => evr m (x + 1) (upd 0 x x t) end.\n")
# a boolean and a record that writes, called at the end of a recursive function giving back one
addA("par_bool_write_tail_call", "", "if ktc n a s then a else b",
     "Fixpoint wb (n : nat) (x : int) (t : mem) : bool := match n with O => rd 0 0 t <? x | S m => wb m (x + 1) (upd 0 x x t) end.\nFixpoint ktc (n : nat) (x : int) (t : mem) : bool := match n with O => wb 3 x t | S m => ktc m (x + 1) t end.\n")
addA("par_rec_write_tail_call", "", "f2 (ktr n a s)",
     "Fixpoint wq (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 0 t) x 0 | S m => wq m (x + 1) (upd 0 x x t) end.\nFixpoint ktr (n : nat) (x : int) (t : mem) : r3 := match n with O => wq 3 x t | S m => ktr m (x + 1) t end.\n")
addA("par_tmpl_rec_write", "", "f1 (trw n a (fun z => z + 1) s)",
     "Fixpoint trw (n : nat) (x : int) (g : int -> int) (t : mem) : r3 := match n with O => mk3 (rd 0 0 t) (g x) 0 | S m => trw m (g x) g (upd 0 x x t) end.\n")
addA("par_tmpl_bool_write", "", "if tbw n a (fun z => z + 1) s then a else b",
     "Fixpoint tbw (n : nat) (x : int) (g : int -> int) (t : mem) : bool := match n with O => rd 0 0 t <? g x | S m => tbw m (g x) g (upd 0 x x t) end.\n")
# templates giving back a boolean or a record whose body writes through a call (step 48 continued)
addA("par_tmpl_bool_write_call", "", "if tbc n a (fun z => z + 1) s then a else b",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nFixpoint tbc (n : nat) (x : int) (g : int -> int) (t : mem) : bool := match n with O => wr 2 t <? g x | S m => tbc m (g x) g t end.\n")
addA("par_tmpl_rec_write_call", "", "f1 (trc n a (fun z => z + 1) s)",
     "Fixpoint wr (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wr m (upd 0 0 (rd 0 0 t + 1) t) end.\nFixpoint trc (n : nat) (x : int) (g : int -> int) (t : mem) : r3 := match n with O => mk3 (wr 2 t) (g x) 0 | S m => trc m (g x) g t end.\n")
# the translator's own conventions (§3.7): the counter not first, the memory not last
addA("par_conv_nat_second", "", "k a n", "Fixpoint k (x : int) (n : nat) : int := match n with O => x | S m => k (x + 1) m end.\n")
addA("par_conv_mem_first", "", "k n s a", "Fixpoint k (n : nat) (t : mem) (x : int) : int := match n with O => x + rd 0 0 t | S m => k m t (x + 1) end.\n")
# parameters in any order (step 41): a boolean and a record before the counter, the recursion on the second counter, the memory
# between two numbers; each result kind with its parameters in another order; an entry with its parameters in another order
addA("par_conv_bool_rec_first", "", "k (a <? b) (mk3 a b 0) n",
     "Fixpoint k (c : bool) (r : r3) (n : nat) : int := match n with O => if c then f1 r else f2 r | S m => k c r m end.\n")
addA("par_conv_rec_second", "", "k n n a", "Fixpoint k (m n : nat) (x : int) : int := match n with O => x + 1 | S p => k m p (x + 1) end.\n")
addA("par_conv_mem_middle", "", "k n a s b",
     "Fixpoint k (n : nat) (x : int) (t : mem) (y : int) : int := match n with O => x + y + rd 0 0 t | S m => k m (x + 1) t y end.\n")
addA("par_conv_res_bool", "", "if k a n then 1 else 0", "Fixpoint k (x : int) (n : nat) : bool := match n with O => x <? 5 | S m => k (x + 1) m end.\n")
addA("par_conv_res_pair", "", "let '(x, y) := k a b n in x + y", "Fixpoint k (x y : int) (n : nat) : int * int := match n with O => (x, y) | S m => k y x m end.\n")
addA("par_conv_res_mem", "", "rd 0 0 (k s n a)", "Fixpoint k (t : mem) (n : nat) (x : int) : mem := match n with O => t | S m => k (upd 0 x x t) m (x + 1) end.\n")
addA("par_conv_res_intmem", "", "let '(x, s2) := k s n a in x + rd 0 0 s2",
     "Fixpoint k (t : mem) (n : nat) (x : int) : int * mem := match n with O => (x, t) | S m => k (upd 0 x x t) m (x + 1) end.\n")
addA("par_conv_res_write", "", "k s a n", "Fixpoint k (t : mem) (x : int) (n : nat) : int := match n with O => rd 0 0 t | S m => k (upd 0 x x t) (x + 1) m end.\n")
addA("par_conv_lfix", "", "let fix g (x : int) (m : nat) : int := match m with O => x | S p => g (x + 1) p end in g a n", "")   # a local fix, its recursion on its second parameter
addA("par_conv_tmpl", "", "foldf (fun i acc => acc + i) n 0 a",
     "Fixpoint foldf (f : int -> int -> int) (n : nat) (i acc : int) : int := match n with O => acc | S m => foldf f m (i + 1) (f i acc) end.\n")   # a template, its function given first
A.append(("par_conv_entry", "Fixpoint go2 (x : int) (n : nat) : int := match n with O => x | S m => go2 (x + 1) m end.\n"
          "Definition main : int :=\n  let kq_keep := kq_case (kq_S kq_O) (fun _ => tt) (fun _ => tt) in\n  go2 (kq_arg 1) (kq_nat (kq_arg 0)).\n"))

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

# ---------------------------------------------------------------- a memory made in place x what reads it x where it stands x the sort of the function (step 54)
XH = """Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.
Definition hw (x y : int) (t : mem) : mem := upd 0 x y t.
Fixpoint g (n : nat) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => g m (x + 1) (upd 0 x x t) end.
Fixpoint sm (n : nat) (x : int) (t : mem) : int := match n with O => x | S m => sm m (x + rd 1 x t) t end.
Fixpoint wn (n : nat) (t : mem) : int := match n with O => rd 0 0 t | S m => wn m (upd 0 0 (rd 0 0 t + 1) t) end.
Definition rdh (i : int) (t : mem) : int := rd 0 i t + 1.
Fixpoint kr (n : nat) (x : int) (t : mem) : r3 := match n with O => mk3 (rd 0 x t) x 0 | S m => kr m (x + 1) t end.
Fixpoint kb (n : nat) (x : int) (t : mem) : bool := match n with O => rd 0 x t <? x | S m => kb m (x + 1) t end.
Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.
"""
XM = {"upd": "upd 0 a b s", "upd32": "upd32 0 a b s", "two": "upd 1 a b (upd 0 a b s)", "let": "let t := upd 0 a b s in upd 1 a b t",
      "fix": "fill n a s", "helper": "hw a b s", "if": "if a <? b then upd 0 a b s else s", "match": "match n with O => s | S m => upd 0 a b s end",
      "fixfix": "fill n a (fill n b s)", "snd": "snd (g n a s)"}
XC = {"rd": "rd 0 b (M)", "rd32": "rd32 0 b (M)", "size": "kq_size 0 (M)", "reader": "sm n b (M)", "writer": "wn n (M)", "helper": "rdh b (M)",
      "fst": "fst (g n b (M))", "field": "f1 (kr n b (M))", "bool": "if kb n b (M) then 1 else 2", "pairboth": "let p := g n b (M) in fst p + rd 0 0 (snd p)",
      "sndrd": "rd 0 0 (snd (g n b (M)))", "matchpair": "match g n b (M) with (v, w) => v + rd 0 0 w end"}
XE = {"whole": "X", "left": "(X) + a", "right": "a + (X)", "test": "if (X) <? a then a else b", "let": "let y := X in y + a", "helper": "h (X) a",
      "call": "ff n (X)", "tmpl": "fold n a (X) (fun i acc => acc + i)", "field": "f1 (mk3 (X) a b)", "pair": "fst (X, a)", "twice": "((X) + a) * 2", "nested": "h ((X) + 1) (a + 2)",
      "inlet": "(let y := a + 1 in (X) + y) + a", "ifop": "(if a <? b then X else a) + b", "matchop": "(match n with O => X | S _ => a end) + b",
      "recfield": "(let w := mk3 (X) a b in f1 w) + 1", "pairfst": "let p := (X, a) in fst p + snd p", "ifboth": "if a <? b then (X) + 1 else (X) + 2"}
XF = {"int": lambda e: ("", e),
      "fix": lambda e: (f"Fixpoint kf {SIG} : int := match n with O => {e} | S m => kf m a b s end.\n", "kf n a b s"),
      "bool": lambda e: (f"Definition kf {SIG} : bool := ({e}) <? a.\n", "if kf n a b s then a else b"),
      "record": lambda e: (f"Definition kf {SIG} : r3 := mk3 ({e}) a b.\n", "f1 (kf n a b s)")}
X = {}
def addX(m, c, e, f):
    ex = XE[e].replace("X", XC[c].replace("M", XM[m]))
    d, call = XF[f](ex)
    X[f"{m}_{c}_{e}_{f}"] = XH + d + f"Definition go {SIG} : int :=\n  {call}.\n"
for m, c in itertools.product(XM, XC): addX(m, c, "left", "int")
for c, e in itertools.product(XC, XE): addX("fix", c, e, "int")
for m, e in itertools.product(XM, XE): addX(m, "rd", e, "int")
for e, f in itertools.product(XE, XF): addX("fix", "rd", e, f)
for c, f in itertools.product(XC, XF): addX("fix", c, "left", f)
for m, f in itertools.product(XM, XF): addX(m, "rd", "left", f)

# ---------------------------------------------------------------- the function's own call x where it stands x its memory x the sort of the function (step 55)
YMEM = {"same": ("", "s"), "upd": ("", "(upd 0 a b s)"), "letupd": ("let u := upd 0 a b s in ", "u"), "fill": ("", "(fill m a s)"), "letfill": ("let u := fill m a s in ", "u"), "none": ("", None)}
YE = {"tail": "X", "left": "X + a", "right": "a + X", "twice": "(X + a) * 2", "test": "if X <? a then a else b", "let": "let y := X in y + a", "helper": "h X a", "call": "ff m X",
      "field": "f1 (mk3 X a b)", "pair": "fst (X, a)", "ifop": "(if a <? b then X else a) + b", "inlet": "(let y := a + 1 in X + y) + a", "branch": "if a <? b then X else a + 1",
      "branch2": "if a <? b then X + 1 else a"}
YH = """Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.
Fixpoint fill (n : nat) (i : int) (t : mem) : mem := match n with O => t | S m => fill m (i + 1) (upd 0 i (i * 2) t) end.
"""
Y = {}
def addY(mm, e, sort):
    pre, m = YMEM[mm]
    arg = f"kf m (a + 1) b {m}" if m else "kf m (a + 1) b"
    call = {"int": arg, "bool": f"(if {arg} then 1 else 2)", "record": f"(f1 ({arg}))"}[sort]
    if e != "tail":
        call = "(" + call + ")"
    body = YE[e].replace("X", call)
    params = "(n : nat) (a b : int)" + (" (s : mem)" if m else "")
    c = "kf n a b s" if m else "kf n a b"
    if sort == "int":
        d = f"Fixpoint kf {params} : int := match n with O => a | S m => {pre}{body} end.\n"; g = c
    elif sort == "bool":
        d = f"Fixpoint kf {params} : bool := match n with O => a <? b | S m => {pre}(({body}) <? b) end.\n"; g = f"if {c} then a else b"
    else:
        d = f"Fixpoint kf {params} : r3 := match n with O => mk3 a b 0 | S m => {pre}mk3 ({body}) b 0 end.\n"; g = f"f1 ({c})"
    Y[f"{mm}_{e}_{sort}"] = YH + d + f"Definition go {SIG} : int :=\n  {g}.\n"
for mm, e, sort in itertools.product(YMEM, YE, ["int", "bool", "record"]):
    if mm == "none" and e not in ("left", "test", "let", "field", "ifop"):
        continue
    addY(mm, e, sort)

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
        open(os.path.join(outdir, f"A_{i}.body"), "w").write(PRE + text + ("" if "Definition main" in text else MAIN))   # a cell with its own main (step 41)
        rows.append((f"A_{i}", "parameter", i))
    for (i, text) in N:
        body = PRE + text + f"Definition go {SIG} : int :=\n  f n a b s.\n" + MAIN
        open(os.path.join(outdir, f"N_{i}.body"), "w").write(body)
        rows.append((f"N_{i}", "nesting", i))
    for (i, text) in Y.items():
        open(os.path.join(outdir, f"Y_{i}.body"), "w").write(PRE + text + MAIN)
        rows.append((f"Y_{i}", "own call", i))
    for (i, text) in X.items():
        open(os.path.join(outdir, f"X_{i}.body"), "w").write(PRE + text + MAIN)
        rows.append((f"X_{i}", "cross", i))
    for (f, text) in LIBS.items():
        p = os.path.join(outdir, f + ".v")
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, "w").write(text)
    with open(os.path.join(outdir, "cells.tsv"), "w") as fh:
        for r in rows:
            fh.write("\t".join(r) + "\n")
    print(len(rows), "cells:", len(P), "producers,", len(A), "parameters,", len(N), "nestings,", len(X), "crossings,", len(Y), "own calls")

if __name__ == "__main__":
    write(sys.argv[1] if len(sys.argv) > 1 else "cells")
