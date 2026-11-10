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
# a function read in another form: a memory never read, a type parameter (step 69)
addA('rp_dead_first', "", 'rd 0 0 (kw n s a s)',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m (upd 1 0 x u) (x + 1) (upd 0 x x t) end.\n')
addA('rp_dead_last', "", 'rd 0 0 (kw n s a s)',
     'Fixpoint kw (n : nat) (t : mem) (x : int) (u : mem) : mem := match n with O => t | S m => kw m (upd 0 x x t) (x + 1) t end.\n')
addA('rp_dead_three', "", 'kw n s s a s',
     'Fixpoint kw (n : nat) (u v : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => kw m t u (x + 1) t end.\n')
addA('rp_dead_num', "", 'kw n (upd 0 a b s) a s',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => kw m t (x + 1) t end.\n')
addA('rp_dead_bool', "", 'if kw n (upd 0 a b s) a s then a else b',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : bool := match n with O => rd 0 x t <? 3 | S m => kw m t (x + 1) t end.\n')
addA('rp_dead_rec', "", 'fst (kw n (upd 0 a b s) a s)',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : int * int := match n with O => (rd 0 x t, x) | S m => kw m t (x + 1) t end.\n')
addA('rp_dead_write_num', "", 'kw n s a s',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => kw m t (x + 1) (upd 0 x x t) end.\n')
addA('rp_dead_pm', "", 'fst (kw n s a s)',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : int * mem := match n with O => (x, t) | S m => kw m t (x + 1) (upd 0 x x t) end.\n')
addA('rp_dead_caller_fix', "", 'cl n a s',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m t (x + 1) (upd 0 x x t) end.\nFixpoint cl (m : nat) (x : int) (t : mem) : int := match m with O => rd 0 x t | S q => cl q (x + 1) (kw 2 t x t) end.\n')
addA('rp_dead_caller_mem', "", 'rd 0 0 (cl n a s)',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m t (x + 1) (upd 0 x x t) end.\nFixpoint cl (m : nat) (x : int) (t : mem) : mem := match m with O => t | S q => cl q (x + 1) (kw 2 t x t) end.\n')
addA('rp_dead_callee_too', "", 'rd 0 0 (ka n s a s)',
     'Fixpoint kb (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kb m t (x + 1) (upd 1 x x t) end.\nFixpoint ka (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => ka m (kb 1 u x u) (x + 1) (kb 2 t x t) end.\n')
addA('rp_dead_opnd', "", 'rd 0 0 (kw n s a s) + b',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m t (x + 1) (upd 0 x x t) end.\n')
addA('rp_dead_helper', "", 'hk n a s',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m t (x + 1) (upd 0 x x t) end.\nDefinition hk (n : nat) (x : int) (t : mem) : int := rd 0 0 (kw n t x t).\n')
addA('rp_dead_live_control', "", 'rd 0 0 (kw n s a s)',
     'Fixpoint kw (n : nat) (u : mem) (x : int) (t : mem) : mem := match n with O => t | S m => kw m u (x + 1) (upd 0 x (rd 1 x u) t) end.\n')
addA('rp_poly_pair', "", 'fst (pf n (fun p => (snd p, fst p)) (a, b))',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\n')
addA('rp_poly_bool', "", 'if pf n negb (a <? b) then a else b',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\n')
addA('rp_poly_mem', "", 'rd 0 0 (pf n (fun t => upd 0 a b t) s)',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\n')
addA('rp_poly_two', "", 'pf n (fun v => v + 1) a + (if pf n negb (a <? b) then 1 else 2)',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\n')
addA('rp_poly_record', "", 'f1 (pf n (fun r => mk3 (f2 r) (f3 r) (f1 r)) (mk3 a b 1))',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\n')
addA('rp_poly_option', "", 'match pf n (fun o => match o with Some v => None | None => Some a end) (Some b) with Some v => v | None => 0 end',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\n')
addA('rp_poly_in_rec', "", 'cl n a',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\nFixpoint cl (m : nat) (x : int) : int := match m with O => x | S q => cl q (pf 2 (fun v => v + 1) x) end.\n')
addA('rp_poly_nofun', "", 'pid n a',
     'Fixpoint pid {T : Type} (m : nat) (x : T) : T := match m with O => x | S q => pid q x end.\n')
addA('rp_poly_two_params', "", 'fst (pp n a (a <? b))',
     'Fixpoint pp {A B : Type} (m : nat) (x : A) (y : B) : A * B := match m with O => (x, y) | S q => pp q x y end.\n')
addA('rp_poly_helper', "", 'hp2 n a',
     'Fixpoint pf {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pf q g (g x) end.\nDefinition hp2 {U : Type} (m : nat) (x : U) : U := pf m (fun v => v) x.\n')
addA('rp_poly_mem_param', "", 'pw n a s',
     'Fixpoint pw {T : Type} (m : nat) (x : T) (t : mem) : T := match m with O => x | S q => pw q x (upd 0 0 1 t) end.\n')
addA('rp_poly_measure', "", 'pq a a',
     'From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq {T : Type} (x : int) (y : T) {measure (mu x)} : T :=\n  match 0 <? x with true => pq (x - 1) y | false => y end.\nNext Obligation. apply mu_pred. auto. Qed.\n')
# what Rocq's libraries and ordinary text spell otherwise (step 68)
addA('l_al_rec', "", 'f n a',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint f (m : C) (x : cell) : cell := match m with O => x | S q => f q (x + 1) end.\n')
addA('l_al_mem', "", 'rd 0 0 (f n a s)',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint f (m : C) (x : cell) (t : M) : M := match m with O => t | S q => f q (x + 1) (upd 0 x x t) end.\n')
addA('l_al_pair', "", 'fst (f n a) + b',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint f (m : nat) (x : int) : P := match m with O => (x, x) | S q => f q (x + 1) end.\n')
addA('l_al_state', "", 'f n (a, b)',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint f (m : nat) (p : P) : int := match m with O => fst p | S q => f q (snd p, fst p) end.\n')
addA('l_al_bool', "", 'if f n a then a else b',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint f (m : nat) (x : int) : B := match m with O => x <? 3 | S q => f q (x + 1) end.\n')
addA('l_al_two', "", 'let q := (a, b, 1) in let p := (a, b) in f n p q',
     'Definition P := (int * int)%type.\nDefinition Q := (int * int * int)%type.\nFixpoint f (m : nat) (p : P) (q : Q) : int := match m with O => fst p + snd q | S r => f r p q end.\n')
addA('l_al_sig_only', "", 'f n (k a) + 1',
     'Definition P := (int * int)%type.\nDefinition Q := (int * int * int)%type.\nDefinition k (x : int) : Q := (x, x, x).\nFixpoint f (m : nat) (q : Q) : int := match m with O => snd q | S r => f r q end.\nFixpoint e (m : nat) (p : P) : int := match m with O => snd p | S r => e r p end.\n')
addA('l_al_al', "", 'f n a',
     'Definition cell := int.\nDefinition cell2 := cell.\nFixpoint f (m : nat) (x : cell2) : cell := match m with O => x | S q => f q (x + 1) end.\n')
addA('l_al_let', "", 'f n a',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint f (m : nat) (x : int) : int := let y : cell := x + 1 in match m with O => y | S q => f q y end.\n')
addA('l_al_match', "", 'f n (a, b)',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint f (m : nat) (p : P) : cell := match m with O => match p return cell with (u, v) => u + v end | S q => f q p end.\n')
addA('l_al_rec_of', "", 'fst (f n a) + b',
     'Definition P2 := (int * bool)%type.\nFixpoint f (m : nat) (x : int) : P2 := match m with O => (x, x <? 3) | S q => f q (x + 1) end.\n')
addA('l_al_opt', "", 'match f n a with Some w => w | None => b end',
     'Definition O1 := option int.\nFixpoint f (m : nat) (x : int) : O1 := match m with O => None | S q => if x <? 0 then Some x else f q (x - 1) end.\n')
addA('l_al_mutual', "", 'ev n a',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nFixpoint ev (m : C) (x : cell) : cell := match m with O => x | S q => od q (x + 1) end with od (m : C) (x : cell) : cell := match m with O => x | S q => ev q (x * 2) end.\n')
addA('l_al_tmpl', "", 'fo n (fun v => v + 1) a',
     'Definition cell := int.\nDefinition M := mem.\nDefinition P := (int * int)%type.\nDefinition C := nat.\nDefinition B := bool.\nDefinition FF := int -> int.\nFixpoint fo (m : nat) (g : FF) (x : cell) : cell := match m with O => x | S q => fo q g (g x) end.\n')
addA('l_al_fun_param', "", 'tw (fun v => v + 1) a',
     'Definition FF := int -> int.\nDefinition tw (g : FF) (x : int) : int := g (g x).\n')
addA('l_al_root', "", 'hc a',
     'Definition cell := int.\nDefinition hc (x : cell) : cell := x + 1.\n')
addA('l_let_first', "", 'f n a',
     'Fixpoint f (m : nat) (x : int) : int := let y := x + 1 in match m with O => y | S q => f q y end.\n')
addA('l_test_first', "", 'f n a',
     'Fixpoint f (m : nat) (x : int) : int := if x <? 0 then x else match m with O => x | S q => f q (x - 1) end.\n')
addA('l_read_first', "", 'f n a s',
     'Fixpoint f (m : nat) (x : int) (t : mem) : int := let y := rd 0 x t in match m with O => y | S q => f q (x + 1) t + y end.\n')
addA('l_al_pf', "", 'pq a',
     'From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition cell := int.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : cell) {measure (mu x)} : cell :=\n  match 0 <? x with true => x + pq (x - 1) | false => 0 end.\nNext Obligation. apply mu_pred. auto. Qed.\n')
addA('l_fh_if', "", '(if a <? b then (fun v : int => v + 1) else (fun v : int => v * 2)) a',
     '')
addA('l_fh_named', "", '(if a <? b then g1 else g2) a',
     'Definition g1 (x : int) : int := x + 1.\nDefinition g2 (x : int) : int := x * 2.\n')
addA('l_fh_match', "", '(match n with O => (fun v : int => v + 1) | S _ => (fun v : int => v * 2) end) a',
     '')
addA('l_fh_two', "", '(if a <? b then (fun v w : int => v + w) else (fun v w : int => v * w)) a b',
     '')
addA('l_fh_opnd', "", '1 + (if a <? b then (fun v : int => v + 1) else (fun v : int => v * 2)) a',
     '')
addA('l_fh_let', "", 'let w := (if a <? b then (fun v : int => v + 1) else (fun v : int => v * 2)) a in w + w',
     '')
addA('l_fh_test', "", 'if (if a <? b then (fun v : int => v + 1) else (fun v : int => v * 2)) a <? 3 then a else b',
     '')
addA('l_fh_nest', "", '(if a <? b then (if b <? 3 then (fun v : int => v + 1) else (fun v : int => v + 2)) else (fun v : int => v * 2)) a',
     '')
addA('l_fh_rec', "", 'f n a',
     'Fixpoint f (m : nat) (x : int) : int := match m with O => x | S q => (if x <? 3 then f q else (fun v : int => v + 1)) (x + 1) end.\n')
addA('l_fh_mem', "", 'rd 0 0 ((if a <? b then (fun t : mem => upd 0 a b t) else (fun t : mem => t)) s)',
     '')
addA('l_fh_writes', "", '(if a <? b then (fun t : mem => rd 0 0 (upd 0 a b t)) else (fun t : mem => rd 0 0 t)) s',
     '')
addA('l_fh_bool', "", 'if (if a <? b then (fun v : int => v <? 1) else (fun v : int => v <? 2)) a then a else b',
     '')
addA('l_fh_pair', "", 'fst ((if a <? b then (fun v : int => (v, v)) else (fun v : int => (v, 1))) a) + b',
     '')
addA('l_fh_let_fun', "", '(let k := b + 1 in fun v : int => v + k) a',
     '')
addA('l_fh_pair_fun', "", '(match (a, b) with (u, w) => fun v : int => u + w + v end) 1',
     '')
addA('l_convoy', "", 'f n a',
     'Definition f (m : nat) (x : int) : int := match m as k return m = k -> int with O => fun _ => x | S q => fun _ => x + 1 end eq_refl.\n')
addA('l_convoy_b', "", 'f (a <? b) a',
     'Definition f (c : bool) (x : int) : int := match c as k return c = k -> int with true => fun _ => x | false => fun _ => x + 1 end eq_refl.\n')
addA('l_bool_rect', "", 'bool_rect (fun _ => int) a b (a <? b)',
     '')
addA('l_bool_rec', "", 'bool_rec (fun _ => int) a b (a <? b)',
     '')
addA('l_prod_rect', "", 'prod_rect (fun _ => int) (fun x y => x + y) (a, b)',
     '')
addA('l_prod_rec', "", 'prod_rec (fun _ => int) (fun x y => x + y) (a, b)',
     '')
addA('l_option_rect', "", 'option_rect (fun _ => int) (fun v => v + 1) b (Some a)',
     '')
addA('l_option_rec', "", 'option_rec (fun _ => int) (fun v => v + 1) b (if a <? b then Some a else None)',
     '')
addA('l_option_map', "", 'match option_map (fun v => v + 1) (Some a) with Some w => w | None => b end',
     '')
addA('l_sum_rect', "", 'sum_rect (fun _ => int) (fun v => v + 1) (fun v => v + 2) (inl a : int + int)',
     '')
addA('l_nat_rect_mem', "", 'rd 0 0 (nat_rect (fun _ => mem) s (fun _ t => upd 0 a b t) n)',
     '')
addA('l_eq_rect', "", 'eq_rect a (fun _ => int) b a eq_refl',
     '')
addA('l_dec_eq', "", 'if Nat.eq_dec n 3 then a else b',
     '')
addA('l_dec_lt', "", 'if Compare_dec.lt_dec n 3 then a else b',
     '')
addA('l_dec_le', "", 'if Compare_dec.le_dec n 3 then a else b',
     '')
addA('l_dec_gt', "", 'if Compare_dec.gt_dec n 3 then a else b',
     '')
addA('l_dec_ge', "", 'if Compare_dec.ge_dec n 3 then a else b',
     '')
addA('l_dec_le_lt', "", 'if Compare_dec.le_lt_dec n 3 then a else b',
     '')
addA('l_dec_le_gt', "", 'if Compare_dec.le_gt_dec n 3 then a else b',
     '')
addA('l_dec_eqs', "", 'if Uint63.eqs a b then a else b',
     '')
addA('l_dec_rec', "", 'f n 5 a',
     'Fixpoint f (m k : nat) (x : int) : int := match m with O => x | S q => if Nat.eq_dec q k then x else f q k (x + 1) end.\n')
addA('l_dec_let', "", 'let w := (if Nat.eq_dec n 3 then a else b) in w + 1',
     '')
addA('l_dec_opnd', "", '1 + (if Compare_dec.lt_dec n 3 then a else b)',
     '')
addA('l_dec_mem', "", 'rd 0 0 (if Nat.eq_dec n 3 then upd 0 a b s else s)',
     '')
addA('l_dec_bool', "", 'if (if Nat.eq_dec n 3 then a <? b else b <? a) then a else b',
     '')
addA('l_dec_proof_used', "", 'f n a',
     'Definition f (m : nat) (x : int) : int := match Nat.eq_dec m 3 with left H => (match H with eq_refl => x end) | right _ => x + 1 end.\n')
addA('l_dec_own', "", 'if d a b then a else b',
     'Definition d (x y : int) : {x = y} + {x <> y} := Uint63.eqs x y.\n')
addA('l_cmp_nat', "", 'match Nat.compare n 3 with Eq => a | Lt => b | Gt => 0 end',
     '')
addA('l_cmp_nat_rec', "", 'f n 5 a',
     'Fixpoint f (m k : nat) (x : int) : int := match m with O => x | S q => match Nat.compare q k with Eq => x | _ => f q k (x + 1) end end.\n')
addA('l_list_fold_left', "", 'List.fold_left (fun acc x => acc + x) (cons a (cons b nil)) 0',
     '')
addA('l_list_fold_right', "", 'List.fold_right (fun x acc => acc + x) 0 (cons a (cons b nil))',
     '')
addA('l_list_map', "", 'List.fold_left (fun acc x => acc + x) (List.map (fun x => x + 1) (cons a (cons b nil))) 0',
     '')
addA('l_list_nth', "", 'List.nth 1 (cons a (cons b nil)) 0',
     '')
addA('l_list_hd', "", 'List.hd 0 (cons a (cons b nil))',
     '')
addA('l_list_tl', "", 'List.hd 0 (List.tl (cons a (cons b nil)))',
     '')
addA('l_list_app', "", 'List.fold_left (fun acc x => acc + x) (List.app (cons a (cons b nil)) (cons a (cons b nil))) 0',
     '')
addA('l_list_rev', "", 'List.hd 0 (List.rev (cons a (cons b nil)))',
     '')
addA('l_list_mem', "", 'rd 0 0 (List.fold_left (fun t x => upd 0 x x t) (cons a (cons b nil)) s)',
     '')
addA('l_list_local', "", 'let l := cons a (cons b nil) in List.fold_left (fun acc x => acc + x) l 0',
     '')
addA('l_list_helper', "", 'List.fold_left (fun acc x => acc + x) (mk a) 0',
     'Definition mk (x : int) : list int := cons x (cons 1 nil).\n')
addA('l_list_data', "", 'f n a',
     'Fixpoint mk (m : nat) : list int := match m with O => nil | S q => cons 1 (mk q) end.\nDefinition f (m : nat) (x : int) : int := List.fold_left (fun acc y => acc + y) (mk m) x.\n')
addA('l_list_param', "", 'f (cons a nil)',
     'Definition f (l : list int) : int := List.fold_left (fun acc y => acc + y) l 0.\n')
addA('l_fix_mut', "", '(fix f (m : nat) (x : int) : int := match m with O => x | S q => g q (x + 1) end with g (m : nat) (x : int) : int := match m with O => x | S q => f q (x * 2) end for f) n a',
     '')
addA('l_poly_rec', "", 'pfold n (fun v => v + 1) a',
     'Fixpoint pfold {T : Type} (m : nat) (g : T -> T) (x : T) : T := match m with O => x | S q => pfold q g (g x) end.\n')
addA('l_poly_rec_nofun', "", 'pid n a',
     'Fixpoint pid {T : Type} (m : nat) (x : T) : T := match m with O => x | S q => pid q x end.\n')
addA('l_z_arith', "", 'Uint63.of_Z (Z.add (Uint63.to_Z a) (Uint63.to_Z b))',
     '')
addA('l_z_arith_ctrl', "", 'a + b',
     '')
addA('l_nat_ret_grow', "", 'match f n O with O => a | S _ => b end',
     'Fixpoint f (m k : nat) : nat := match m with O => k | S q => f q (S k) end.\n')
addA('l_nat_ret_ctrl', "", 'if f n 0 <? 1 then a else b',
     'Fixpoint f (m : nat) (k : int) : int := match m with O => k | S q => f q (k + 1) end.\n')
addA('l_nat_ret_same', "", 'match f n with O => a | S _ => b end',
     'Fixpoint f (m : nat) : nat := match m with O => O | S q => f q end.\n')
addA('l_ack', "", 'ack n 3 a',
     'Fixpoint ack (m : nat) : nat -> int -> int := match m with O => fun _ x => x + 1 | S p => fix go (r : nat) (x : int) : int := match r with O => ack p 1 x | S q => ack p 5 (go q x) end end.\n')
addA('l_pf_div2', "", 'pq n 5 a',
     'From Stdlib Require Import Program.Wf Lia.\nProgram Fixpoint pq (m k : nat) (x : int) {measure (m + Nat.div2 k)} : int := match m with O => x | S q => pq q k (x + 1) end.\n')
# values of a fixed size holding booleans, records and data types, crossed with the places a value stands in (step 67)
addA('fx_pb_let', "", 'let v := mv a in (if snd v then fst v else 0)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\n')
addA('fx_pb_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nDefinition uv (v : (int * bool)%type) : int := (if snd v then fst v else 0).\n')
addA('fx_pb_rec', "", 'let v := fr n a in (if snd v then fst v else 0)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint fr (n : nat) (x : int) : (int * bool)%type := match n with O => (x, x <? 3) | S m => fr m (x + 1) end.\n')
addA('fx_pb_nontail', "", 'let v := fn n a in (if snd v then fst v else 0)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint fn (n : nat) (x : int) : (int * bool)%type := match n with O => (x, x <? 3) | S m => let v := fn m (x + 1) in if (if snd v then fst v else 0) <? 5 then v else (x, x <? 3) end.\n')
addA('fx_pb_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint fs (n : nat) (v : (int * bool)%type) (x : int) : int := match n with O => (if snd v then fst v else 0) + x | S m => fs m (x, x <? 3) (x + (if snd v then fst v else 0)) end.\n')
addA('fx_pb_choice', "", 'let v := if a <? b then mv a else mv b in (if snd v then fst v else 0)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\n')
addA('fx_pb_writes', "", 'let v := fw n a s in (if snd v then fst v else 0)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint fw (n : nat) (x : int) (t : mem) : (int * bool)%type := match n with O => (let x := rd 0 x t in (x, x <? 3)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_pb_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint fm (n : nat) (v : (int * bool)%type) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (if snd v then fst v else 0) 1 t) end.\n')
addA('fx_pb_tmpl', "", 'let v := ft n (fun x w => if (if snd w then fst w else 0) <? 3 then (x, x <? 3) else w) (mv a) b in (if snd v then fst v else 0)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint ft (n : nat) (f : int -> (int * bool)%type -> (int * bool)%type) (v : (int * bool)%type) (x : int) : (int * bool)%type := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_pb_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint me (n : nat) (v : (int * bool)%type) : int := match n with O => (if snd v then fst v else 0) | S m => mo m v end with mo (n : nat) (v : (int * bool)%type) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_pb_mutres', "", 'let v := mua n a in (if snd v then fst v else 0)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nFixpoint mua (n : nat) (x : int) : (int * bool)%type := match n with O => (x, x <? 3) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (int * bool)%type := match n with O => (x, x <? 3) | S m => mua m (x * 2) end.\n')
addA('fx_pb_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (if snd v then fst v else 0) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\n')
addA('fx_pb_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (if snd v then fst v else 0))',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\n')
addA('fx_pb_fun', "", 'tw (fun v => (if snd v then fst v else 0)) (mv a)',
     'Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nDefinition tw (f : (int * bool)%type -> int) (v : (int * bool)%type) : int := f v + 1.\n')
addA('fx_bb_let', "", 'let v := mv a in (if fst v && snd v then 1 else 2)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\n')
addA('fx_bb_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nDefinition uv (v : (bool * bool)%type) : int := (if fst v && snd v then 1 else 2).\n')
addA('fx_bb_rec', "", 'let v := fr n a in (if fst v && snd v then 1 else 2)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint fr (n : nat) (x : int) : (bool * bool)%type := match n with O => (x <? 3, x <? 5) | S m => fr m (x + 1) end.\n')
addA('fx_bb_nontail', "", 'let v := fn n a in (if fst v && snd v then 1 else 2)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint fn (n : nat) (x : int) : (bool * bool)%type := match n with O => (x <? 3, x <? 5) | S m => let v := fn m (x + 1) in if (if fst v && snd v then 1 else 2) <? 5 then v else (x <? 3, x <? 5) end.\n')
addA('fx_bb_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint fs (n : nat) (v : (bool * bool)%type) (x : int) : int := match n with O => (if fst v && snd v then 1 else 2) + x | S m => fs m (x <? 3, x <? 5) (x + (if fst v && snd v then 1 else 2)) end.\n')
addA('fx_bb_choice', "", 'let v := if a <? b then mv a else mv b in (if fst v && snd v then 1 else 2)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\n')
addA('fx_bb_writes', "", 'let v := fw n a s in (if fst v && snd v then 1 else 2)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint fw (n : nat) (x : int) (t : mem) : (bool * bool)%type := match n with O => (let x := rd 0 x t in (x <? 3, x <? 5)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_bb_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint fm (n : nat) (v : (bool * bool)%type) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (if fst v && snd v then 1 else 2) 1 t) end.\n')
addA('fx_bb_tmpl', "", 'let v := ft n (fun x w => if (if fst w && snd w then 1 else 2) <? 3 then (x <? 3, x <? 5) else w) (mv a) b in (if fst v && snd v then 1 else 2)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint ft (n : nat) (f : int -> (bool * bool)%type -> (bool * bool)%type) (v : (bool * bool)%type) (x : int) : (bool * bool)%type := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_bb_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint me (n : nat) (v : (bool * bool)%type) : int := match n with O => (if fst v && snd v then 1 else 2) | S m => mo m v end with mo (n : nat) (v : (bool * bool)%type) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_bb_mutres', "", 'let v := mua n a in (if fst v && snd v then 1 else 2)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nFixpoint mua (n : nat) (x : int) : (bool * bool)%type := match n with O => (x <? 3, x <? 5) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (bool * bool)%type := match n with O => (x <? 3, x <? 5) | S m => mua m (x * 2) end.\n')
addA('fx_bb_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (if fst v && snd v then 1 else 2) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\n')
addA('fx_bb_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (if fst v && snd v then 1 else 2))',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\n')
addA('fx_bb_fun', "", 'tw (fun v => (if fst v && snd v then 1 else 2)) (mv a)',
     'Definition mv (x : int) : (bool * bool)%type := (x <? 3, x <? 5).\nDefinition tw (f : (bool * bool)%type -> int) (v : (bool * bool)%type) : int := f v + 1.\n')
addA('fx_pn_let', "", "let v := mv a in (let '((u, c), w) := v in if c then u else w)",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\n')
addA('fx_pn_param', "", 'uv (mv a)',
     "Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nDefinition uv (v : ((int * bool) * int)%type) : int := (let '((u, c), w) := v in if c then u else w).\n")
addA('fx_pn_rec', "", "let v := fr n a in (let '((u, c), w) := v in if c then u else w)",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint fr (n : nat) (x : int) : ((int * bool) * int)%type := match n with O => ((x, x <? 3), x + 1) | S m => fr m (x + 1) end.\n')
addA('fx_pn_nontail', "", "let v := fn n a in (let '((u, c), w) := v in if c then u else w)",
     "Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint fn (n : nat) (x : int) : ((int * bool) * int)%type := match n with O => ((x, x <? 3), x + 1) | S m => let v := fn m (x + 1) in if (let '((u, c), w) := v in if c then u else w) <? 5 then v else ((x, x <? 3), x + 1) end.\n")
addA('fx_pn_state', "", 'fs n (mv a) b',
     "Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint fs (n : nat) (v : ((int * bool) * int)%type) (x : int) : int := match n with O => (let '((u, c), w) := v in if c then u else w) + x | S m => fs m ((x, x <? 3), x + 1) (x + (let '((u, c), w) := v in if c then u else w)) end.\n")
addA('fx_pn_choice', "", "let v := if a <? b then mv a else mv b in (let '((u, c), w) := v in if c then u else w)",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\n')
addA('fx_pn_writes', "", "let v := fw n a s in (let '((u, c), w) := v in if c then u else w)",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint fw (n : nat) (x : int) (t : mem) : ((int * bool) * int)%type := match n with O => (let x := rd 0 x t in ((x, x <? 3), x + 1)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_pn_mem', "", 'rd 0 0 (fm n (mv a) s)',
     "Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint fm (n : nat) (v : ((int * bool) * int)%type) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (let '((u, c), w) := v in if c then u else w) 1 t) end.\n")
addA('fx_pn_tmpl', "", "let v := ft n (fun x w => if (let '((u, c), w) := w in if c then u else w) <? 3 then ((x, x <? 3), x + 1) else w) (mv a) b in (let '((u, c), w) := v in if c then u else w)",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint ft (n : nat) (f : int -> ((int * bool) * int)%type -> ((int * bool) * int)%type) (v : ((int * bool) * int)%type) (x : int) : ((int * bool) * int)%type := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_pn_mutual', "", 'me n (mv a)',
     "Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint me (n : nat) (v : ((int * bool) * int)%type) : int := match n with O => (let '((u, c), w) := v in if c then u else w) | S m => mo m v end with mo (n : nat) (v : ((int * bool) * int)%type) : int := match n with O => 1 | S m => me m v end.\n")
addA('fx_pn_mutres', "", "let v := mua n a in (let '((u, c), w) := v in if c then u else w)",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nFixpoint mua (n : nat) (x : int) : ((int * bool) * int)%type := match n with O => ((x, x <? 3), x + 1) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : ((int * bool) * int)%type := match n with O => ((x, x <? 3), x + 1) | S m => mua m (x * 2) end.\n')
addA('fx_pn_lfix', "", "let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (let '((u, c), w) := v in if c then u else w) | S q => g q (x + 1) end in g n b",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\n')
addA('fx_pn_closure', "", "let v := mv a in fold n 0 b (fun i acc => acc + (let '((u, c), w) := v in if c then u else w))",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\n')
addA('fx_pn_fun', "", "tw (fun v => (let '((u, c), w) := v in if c then u else w)) (mv a)",
     'Definition mv (x : int) : ((int * bool) * int)%type := ((x, x <? 3), x + 1).\nDefinition tw (f : ((int * bool) * int)%type -> int) (v : ((int * bool) * int)%type) : int := f v + 1.\n')
addA('fx_rb_let', "", 'let v := mv a in (if b1 v then b2 v else 0)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\n')
addA('fx_rb_param', "", 'uv (mv a)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nDefinition uv (v : rb) : int := (if b1 v then b2 v else 0).\n')
addA('fx_rb_rec', "", 'let v := fr n a in (if b1 v then b2 v else 0)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint fr (n : nat) (x : int) : rb := match n with O => (mkb (x <? 3) x) | S m => fr m (x + 1) end.\n')
addA('fx_rb_nontail', "", 'let v := fn n a in (if b1 v then b2 v else 0)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint fn (n : nat) (x : int) : rb := match n with O => (mkb (x <? 3) x) | S m => let v := fn m (x + 1) in if (if b1 v then b2 v else 0) <? 5 then v else (mkb (x <? 3) x) end.\n')
addA('fx_rb_state', "", 'fs n (mv a) b',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint fs (n : nat) (v : rb) (x : int) : int := match n with O => (if b1 v then b2 v else 0) + x | S m => fs m (mkb (x <? 3) x) (x + (if b1 v then b2 v else 0)) end.\n')
addA('fx_rb_choice', "", 'let v := if a <? b then mv a else mv b in (if b1 v then b2 v else 0)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\n')
addA('fx_rb_writes', "", 'let v := fw n a s in (if b1 v then b2 v else 0)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint fw (n : nat) (x : int) (t : mem) : rb := match n with O => (let x := rd 0 x t in (mkb (x <? 3) x)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_rb_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint fm (n : nat) (v : rb) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (if b1 v then b2 v else 0) 1 t) end.\n')
addA('fx_rb_tmpl', "", 'let v := ft n (fun x w => if (if b1 w then b2 w else 0) <? 3 then (mkb (x <? 3) x) else w) (mv a) b in (if b1 v then b2 v else 0)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint ft (n : nat) (f : int -> rb -> rb) (v : rb) (x : int) : rb := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_rb_mutual', "", 'me n (mv a)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint me (n : nat) (v : rb) : int := match n with O => (if b1 v then b2 v else 0) | S m => mo m v end with mo (n : nat) (v : rb) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_rb_mutres', "", 'let v := mua n a in (if b1 v then b2 v else 0)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nFixpoint mua (n : nat) (x : int) : rb := match n with O => (mkb (x <? 3) x) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : rb := match n with O => (mkb (x <? 3) x) | S m => mua m (x * 2) end.\n')
addA('fx_rb_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (if b1 v then b2 v else 0) | S q => g q (x + 1) end in g n b',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\n')
addA('fx_rb_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (if b1 v then b2 v else 0))',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\n')
addA('fx_rb_fun', "", 'tw (fun v => (if b1 v then b2 v else 0)) (mv a)',
     'Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mv (x : int) : rb := (mkb (x <? 3) x).\nDefinition tw (f : rb -> int) (v : rb) : int := f v + 1.\n')
addA('fx_rc_let', "", 'let v := mv a in (match cc v with Red => cv v | _ => 1 end)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\n')
addA('fx_rc_param', "", 'uv (mv a)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nDefinition uv (v : rc) : int := (match cc v with Red => cv v | _ => 1 end).\n')
addA('fx_rc_rec', "", 'let v := fr n a in (match cc v with Red => cv v | _ => 1 end)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint fr (n : nat) (x : int) : rc := match n with O => (mkc (if x <? 0 then Red else Blue) x) | S m => fr m (x + 1) end.\n')
addA('fx_rc_nontail', "", 'let v := fn n a in (match cc v with Red => cv v | _ => 1 end)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint fn (n : nat) (x : int) : rc := match n with O => (mkc (if x <? 0 then Red else Blue) x) | S m => let v := fn m (x + 1) in if (match cc v with Red => cv v | _ => 1 end) <? 5 then v else (mkc (if x <? 0 then Red else Blue) x) end.\n')
addA('fx_rc_state', "", 'fs n (mv a) b',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint fs (n : nat) (v : rc) (x : int) : int := match n with O => (match cc v with Red => cv v | _ => 1 end) + x | S m => fs m (mkc (if x <? 0 then Red else Blue) x) (x + (match cc v with Red => cv v | _ => 1 end)) end.\n')
addA('fx_rc_choice', "", 'let v := if a <? b then mv a else mv b in (match cc v with Red => cv v | _ => 1 end)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\n')
addA('fx_rc_writes', "", 'let v := fw n a s in (match cc v with Red => cv v | _ => 1 end)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint fw (n : nat) (x : int) (t : mem) : rc := match n with O => (let x := rd 0 x t in (mkc (if x <? 0 then Red else Blue) x)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_rc_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint fm (n : nat) (v : rc) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match cc v with Red => cv v | _ => 1 end) 1 t) end.\n')
addA('fx_rc_tmpl', "", 'let v := ft n (fun x w => if (match cc w with Red => cv w | _ => 1 end) <? 3 then (mkc (if x <? 0 then Red else Blue) x) else w) (mv a) b in (match cc v with Red => cv v | _ => 1 end)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint ft (n : nat) (f : int -> rc -> rc) (v : rc) (x : int) : rc := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_rc_mutual', "", 'me n (mv a)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint me (n : nat) (v : rc) : int := match n with O => (match cc v with Red => cv v | _ => 1 end) | S m => mo m v end with mo (n : nat) (v : rc) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_rc_mutres', "", 'let v := mua n a in (match cc v with Red => cv v | _ => 1 end)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nFixpoint mua (n : nat) (x : int) : rc := match n with O => (mkc (if x <? 0 then Red else Blue) x) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : rc := match n with O => (mkc (if x <? 0 then Red else Blue) x) | S m => mua m (x * 2) end.\n')
addA('fx_rc_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match cc v with Red => cv v | _ => 1 end) | S q => g q (x + 1) end in g n b',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\n')
addA('fx_rc_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match cc v with Red => cv v | _ => 1 end))',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\n')
addA('fx_rc_fun', "", 'tw (fun v => (match cc v with Red => cv v | _ => 1 end)) (mv a)',
     'Inductive color := Red | Green | Blue.\nRecord rc := mkc { cc : color; cv : int }.\nDefinition mv (x : int) : rc := (mkc (if x <? 0 then Red else Blue) x).\nDefinition tw (f : rc -> int) (v : rc) : int := f v + 1.\n')
addA('fx_rd_let', "", 'let v := mv a in (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\n')
addA('fx_rd_param', "", 'uv (mv a)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nDefinition uv (v : rs) : int := (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end).\n')
addA('fx_rd_rec', "", 'let v := fr n a in (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint fr (n : nat) (x : int) : rs := match n with O => (mks (if x <? 0 then Circle x else Rect x x) x) | S m => fr m (x + 1) end.\n')
addA('fx_rd_nontail', "", 'let v := fn n a in (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint fn (n : nat) (x : int) : rs := match n with O => (mks (if x <? 0 then Circle x else Rect x x) x) | S m => let v := fn m (x + 1) in if (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end) <? 5 then v else (mks (if x <? 0 then Circle x else Rect x x) x) end.\n')
addA('fx_rd_state', "", 'fs n (mv a) b',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint fs (n : nat) (v : rs) (x : int) : int := match n with O => (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end) + x | S m => fs m (mks (if x <? 0 then Circle x else Rect x x) x) (x + (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)) end.\n')
addA('fx_rd_choice', "", 'let v := if a <? b then mv a else mv b in (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\n')
addA('fx_rd_writes', "", 'let v := fw n a s in (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint fw (n : nat) (x : int) (t : mem) : rs := match n with O => (let x := rd 0 x t in (mks (if x <? 0 then Circle x else Rect x x) x)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_rd_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint fm (n : nat) (v : rs) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end) 1 t) end.\n')
addA('fx_rd_tmpl', "", 'let v := ft n (fun x w => if (match sa w with Circle r => r + sb w | Rect w h => w * h | Dot => 1 end) <? 3 then (mks (if x <? 0 then Circle x else Rect x x) x) else w) (mv a) b in (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint ft (n : nat) (f : int -> rs -> rs) (v : rs) (x : int) : rs := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_rd_mutual', "", 'me n (mv a)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint me (n : nat) (v : rs) : int := match n with O => (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end) | S m => mo m v end with mo (n : nat) (v : rs) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_rd_mutres', "", 'let v := mua n a in (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nFixpoint mua (n : nat) (x : int) : rs := match n with O => (mks (if x <? 0 then Circle x else Rect x x) x) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : rs := match n with O => (mks (if x <? 0 then Circle x else Rect x x) x) | S m => mua m (x * 2) end.\n')
addA('fx_rd_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end) | S q => g q (x + 1) end in g n b',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\n')
addA('fx_rd_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end))',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\n')
addA('fx_rd_fun', "", 'tw (fun v => (match sa v with Circle r => r + sb v | Rect w h => w * h | Dot => 1 end)) (mv a)',
     'Inductive shape := Circle (r : int) | Rect (w h : int) | Dot.\nRecord rs := mks { sa : shape; sb : int }.\nDefinition mv (x : int) : rs := (mks (if x <? 0 then Circle x else Rect x x) x).\nDefinition tw (f : rs -> int) (v : rs) : int := f v + 1.\n')
addA('fx_ob_let', "", 'let v := mv a in (match v with Some c => if c then 1 else 2 | None => 3 end)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\n')
addA('fx_ob_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nDefinition uv (v : (option bool)) : int := (match v with Some c => if c then 1 else 2 | None => 3 end).\n')
addA('fx_ob_rec', "", 'let v := fr n a in (match v with Some c => if c then 1 else 2 | None => 3 end)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint fr (n : nat) (x : int) : (option bool) := match n with O => (if x <? 0 then None else Some (x <? 5)) | S m => fr m (x + 1) end.\n')
addA('fx_ob_nontail', "", 'let v := fn n a in (match v with Some c => if c then 1 else 2 | None => 3 end)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint fn (n : nat) (x : int) : (option bool) := match n with O => (if x <? 0 then None else Some (x <? 5)) | S m => let v := fn m (x + 1) in if (match v with Some c => if c then 1 else 2 | None => 3 end) <? 5 then v else (if x <? 0 then None else Some (x <? 5)) end.\n')
addA('fx_ob_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint fs (n : nat) (v : (option bool)) (x : int) : int := match n with O => (match v with Some c => if c then 1 else 2 | None => 3 end) + x | S m => fs m (if x <? 0 then None else Some (x <? 5)) (x + (match v with Some c => if c then 1 else 2 | None => 3 end)) end.\n')
addA('fx_ob_choice', "", 'let v := if a <? b then mv a else mv b in (match v with Some c => if c then 1 else 2 | None => 3 end)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\n')
addA('fx_ob_writes', "", 'let v := fw n a s in (match v with Some c => if c then 1 else 2 | None => 3 end)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint fw (n : nat) (x : int) (t : mem) : (option bool) := match n with O => (let x := rd 0 x t in (if x <? 0 then None else Some (x <? 5))) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_ob_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint fm (n : nat) (v : (option bool)) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with Some c => if c then 1 else 2 | None => 3 end) 1 t) end.\n')
addA('fx_ob_tmpl', "", 'let v := ft n (fun x w => if (match w with Some c => if c then 1 else 2 | None => 3 end) <? 3 then (if x <? 0 then None else Some (x <? 5)) else w) (mv a) b in (match v with Some c => if c then 1 else 2 | None => 3 end)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint ft (n : nat) (f : int -> (option bool) -> (option bool)) (v : (option bool)) (x : int) : (option bool) := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_ob_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint me (n : nat) (v : (option bool)) : int := match n with O => (match v with Some c => if c then 1 else 2 | None => 3 end) | S m => mo m v end with mo (n : nat) (v : (option bool)) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_ob_mutres', "", 'let v := mua n a in (match v with Some c => if c then 1 else 2 | None => 3 end)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nFixpoint mua (n : nat) (x : int) : (option bool) := match n with O => (if x <? 0 then None else Some (x <? 5)) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (option bool) := match n with O => (if x <? 0 then None else Some (x <? 5)) | S m => mua m (x * 2) end.\n')
addA('fx_ob_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with Some c => if c then 1 else 2 | None => 3 end) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\n')
addA('fx_ob_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with Some c => if c then 1 else 2 | None => 3 end))',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\n')
addA('fx_ob_fun', "", 'tw (fun v => (match v with Some c => if c then 1 else 2 | None => 3 end)) (mv a)',
     'Definition mv (x : int) : (option bool) := (if x <? 0 then None else Some (x <? 5)).\nDefinition tw (f : (option bool) -> int) (v : (option bool)) : int := f v + 1.\n')
addA('fx_op_let', "", 'let v := mv a in (match v with Some (u, w) => u + w | None => 3 end)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\n')
addA('fx_op_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nDefinition uv (v : (option (int * int))) : int := (match v with Some (u, w) => u + w | None => 3 end).\n')
addA('fx_op_rec', "", 'let v := fr n a in (match v with Some (u, w) => u + w | None => 3 end)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint fr (n : nat) (x : int) : (option (int * int)) := match n with O => (if x <? 0 then None else Some (x, x + 1)) | S m => fr m (x + 1) end.\n')
addA('fx_op_nontail', "", 'let v := fn n a in (match v with Some (u, w) => u + w | None => 3 end)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint fn (n : nat) (x : int) : (option (int * int)) := match n with O => (if x <? 0 then None else Some (x, x + 1)) | S m => let v := fn m (x + 1) in if (match v with Some (u, w) => u + w | None => 3 end) <? 5 then v else (if x <? 0 then None else Some (x, x + 1)) end.\n')
addA('fx_op_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint fs (n : nat) (v : (option (int * int))) (x : int) : int := match n with O => (match v with Some (u, w) => u + w | None => 3 end) + x | S m => fs m (if x <? 0 then None else Some (x, x + 1)) (x + (match v with Some (u, w) => u + w | None => 3 end)) end.\n')
addA('fx_op_choice', "", 'let v := if a <? b then mv a else mv b in (match v with Some (u, w) => u + w | None => 3 end)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\n')
addA('fx_op_writes', "", 'let v := fw n a s in (match v with Some (u, w) => u + w | None => 3 end)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint fw (n : nat) (x : int) (t : mem) : (option (int * int)) := match n with O => (let x := rd 0 x t in (if x <? 0 then None else Some (x, x + 1))) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_op_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint fm (n : nat) (v : (option (int * int))) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with Some (u, w) => u + w | None => 3 end) 1 t) end.\n')
addA('fx_op_tmpl', "", 'let v := ft n (fun x w => if (match w with Some (u, w) => u + w | None => 3 end) <? 3 then (if x <? 0 then None else Some (x, x + 1)) else w) (mv a) b in (match v with Some (u, w) => u + w | None => 3 end)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint ft (n : nat) (f : int -> (option (int * int)) -> (option (int * int))) (v : (option (int * int))) (x : int) : (option (int * int)) := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_op_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint me (n : nat) (v : (option (int * int))) : int := match n with O => (match v with Some (u, w) => u + w | None => 3 end) | S m => mo m v end with mo (n : nat) (v : (option (int * int))) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_op_mutres', "", 'let v := mua n a in (match v with Some (u, w) => u + w | None => 3 end)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nFixpoint mua (n : nat) (x : int) : (option (int * int)) := match n with O => (if x <? 0 then None else Some (x, x + 1)) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (option (int * int)) := match n with O => (if x <? 0 then None else Some (x, x + 1)) | S m => mua m (x * 2) end.\n')
addA('fx_op_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with Some (u, w) => u + w | None => 3 end) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\n')
addA('fx_op_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with Some (u, w) => u + w | None => 3 end))',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\n')
addA('fx_op_fun', "", 'tw (fun v => (match v with Some (u, w) => u + w | None => 3 end)) (mv a)',
     'Definition mv (x : int) : (option (int * int)) := (if x <? 0 then None else Some (x, x + 1)).\nDefinition tw (f : (option (int * int)) -> int) (v : (option (int * int))) : int := f v + 1.\n')
addA('fx_or_let', "", 'let v := mv a in (match v with Some r => f1 r + f3 r | None => 3 end)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\n')
addA('fx_or_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nDefinition uv (v : (option r3)) : int := (match v with Some r => f1 r + f3 r | None => 3 end).\n')
addA('fx_or_rec', "", 'let v := fr n a in (match v with Some r => f1 r + f3 r | None => 3 end)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint fr (n : nat) (x : int) : (option r3) := match n with O => (if x <? 0 then None else Some (mk3 x x x)) | S m => fr m (x + 1) end.\n')
addA('fx_or_nontail', "", 'let v := fn n a in (match v with Some r => f1 r + f3 r | None => 3 end)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint fn (n : nat) (x : int) : (option r3) := match n with O => (if x <? 0 then None else Some (mk3 x x x)) | S m => let v := fn m (x + 1) in if (match v with Some r => f1 r + f3 r | None => 3 end) <? 5 then v else (if x <? 0 then None else Some (mk3 x x x)) end.\n')
addA('fx_or_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint fs (n : nat) (v : (option r3)) (x : int) : int := match n with O => (match v with Some r => f1 r + f3 r | None => 3 end) + x | S m => fs m (if x <? 0 then None else Some (mk3 x x x)) (x + (match v with Some r => f1 r + f3 r | None => 3 end)) end.\n')
addA('fx_or_choice', "", 'let v := if a <? b then mv a else mv b in (match v with Some r => f1 r + f3 r | None => 3 end)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\n')
addA('fx_or_writes', "", 'let v := fw n a s in (match v with Some r => f1 r + f3 r | None => 3 end)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint fw (n : nat) (x : int) (t : mem) : (option r3) := match n with O => (let x := rd 0 x t in (if x <? 0 then None else Some (mk3 x x x))) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_or_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint fm (n : nat) (v : (option r3)) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with Some r => f1 r + f3 r | None => 3 end) 1 t) end.\n')
addA('fx_or_tmpl', "", 'let v := ft n (fun x w => if (match w with Some r => f1 r + f3 r | None => 3 end) <? 3 then (if x <? 0 then None else Some (mk3 x x x)) else w) (mv a) b in (match v with Some r => f1 r + f3 r | None => 3 end)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint ft (n : nat) (f : int -> (option r3) -> (option r3)) (v : (option r3)) (x : int) : (option r3) := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_or_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint me (n : nat) (v : (option r3)) : int := match n with O => (match v with Some r => f1 r + f3 r | None => 3 end) | S m => mo m v end with mo (n : nat) (v : (option r3)) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_or_mutres', "", 'let v := mua n a in (match v with Some r => f1 r + f3 r | None => 3 end)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nFixpoint mua (n : nat) (x : int) : (option r3) := match n with O => (if x <? 0 then None else Some (mk3 x x x)) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (option r3) := match n with O => (if x <? 0 then None else Some (mk3 x x x)) | S m => mua m (x * 2) end.\n')
addA('fx_or_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with Some r => f1 r + f3 r | None => 3 end) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\n')
addA('fx_or_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with Some r => f1 r + f3 r | None => 3 end))',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\n')
addA('fx_or_fun', "", 'tw (fun v => (match v with Some r => f1 r + f3 r | None => 3 end)) (mv a)',
     'Definition mv (x : int) : (option r3) := (if x <? 0 then None else Some (mk3 x x x)).\nDefinition tw (f : (option r3) -> int) (v : (option r3)) : int := f v + 1.\n')
addA('fx_oo_let', "", 'let v := mv a in (match v with Some (Some w) => w | Some None => 2 | None => 3 end)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\n')
addA('fx_oo_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nDefinition uv (v : (option (option int))) : int := (match v with Some (Some w) => w | Some None => 2 | None => 3 end).\n')
addA('fx_oo_rec', "", 'let v := fr n a in (match v with Some (Some w) => w | Some None => 2 | None => 3 end)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint fr (n : nat) (x : int) : (option (option int)) := match n with O => (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)) | S m => fr m (x + 1) end.\n')
addA('fx_oo_nontail', "", 'let v := fn n a in (match v with Some (Some w) => w | Some None => 2 | None => 3 end)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint fn (n : nat) (x : int) : (option (option int)) := match n with O => (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)) | S m => let v := fn m (x + 1) in if (match v with Some (Some w) => w | Some None => 2 | None => 3 end) <? 5 then v else (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)) end.\n')
addA('fx_oo_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint fs (n : nat) (v : (option (option int))) (x : int) : int := match n with O => (match v with Some (Some w) => w | Some None => 2 | None => 3 end) + x | S m => fs m (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)) (x + (match v with Some (Some w) => w | Some None => 2 | None => 3 end)) end.\n')
addA('fx_oo_choice', "", 'let v := if a <? b then mv a else mv b in (match v with Some (Some w) => w | Some None => 2 | None => 3 end)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\n')
addA('fx_oo_writes', "", 'let v := fw n a s in (match v with Some (Some w) => w | Some None => 2 | None => 3 end)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint fw (n : nat) (x : int) (t : mem) : (option (option int)) := match n with O => (let x := rd 0 x t in (if x <? 0 then None else if x <? 5 then Some None else Some (Some x))) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_oo_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint fm (n : nat) (v : (option (option int))) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with Some (Some w) => w | Some None => 2 | None => 3 end) 1 t) end.\n')
addA('fx_oo_tmpl', "", 'let v := ft n (fun x w => if (match w with Some (Some w) => w | Some None => 2 | None => 3 end) <? 3 then (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)) else w) (mv a) b in (match v with Some (Some w) => w | Some None => 2 | None => 3 end)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint ft (n : nat) (f : int -> (option (option int)) -> (option (option int))) (v : (option (option int))) (x : int) : (option (option int)) := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_oo_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint me (n : nat) (v : (option (option int))) : int := match n with O => (match v with Some (Some w) => w | Some None => 2 | None => 3 end) | S m => mo m v end with mo (n : nat) (v : (option (option int))) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_oo_mutres', "", 'let v := mua n a in (match v with Some (Some w) => w | Some None => 2 | None => 3 end)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nFixpoint mua (n : nat) (x : int) : (option (option int)) := match n with O => (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (option (option int)) := match n with O => (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)) | S m => mua m (x * 2) end.\n')
addA('fx_oo_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with Some (Some w) => w | Some None => 2 | None => 3 end) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\n')
addA('fx_oo_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with Some (Some w) => w | Some None => 2 | None => 3 end))',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\n')
addA('fx_oo_fun', "", 'tw (fun v => (match v with Some (Some w) => w | Some None => 2 | None => 3 end)) (mv a)',
     'Definition mv (x : int) : (option (option int)) := (if x <? 0 then None else if x <? 5 then Some None else Some (Some x)).\nDefinition tw (f : (option (option int)) -> int) (v : (option (option int))) : int := f v + 1.\n')
addA('fx_sp_let', "", 'let v := mv a in (match v with inl (u, w) => u + w | inr w => w end)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\n')
addA('fx_sp_param', "", 'uv (mv a)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nDefinition uv (v : ((int * int) + int)%type) : int := (match v with inl (u, w) => u + w | inr w => w end).\n')
addA('fx_sp_rec', "", 'let v := fr n a in (match v with inl (u, w) => u + w | inr w => w end)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint fr (n : nat) (x : int) : ((int * int) + int)%type := match n with O => (if x <? 0 then inl (x, x) else inr x) | S m => fr m (x + 1) end.\n')
addA('fx_sp_nontail', "", 'let v := fn n a in (match v with inl (u, w) => u + w | inr w => w end)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint fn (n : nat) (x : int) : ((int * int) + int)%type := match n with O => (if x <? 0 then inl (x, x) else inr x) | S m => let v := fn m (x + 1) in if (match v with inl (u, w) => u + w | inr w => w end) <? 5 then v else (if x <? 0 then inl (x, x) else inr x) end.\n')
addA('fx_sp_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint fs (n : nat) (v : ((int * int) + int)%type) (x : int) : int := match n with O => (match v with inl (u, w) => u + w | inr w => w end) + x | S m => fs m (if x <? 0 then inl (x, x) else inr x) (x + (match v with inl (u, w) => u + w | inr w => w end)) end.\n')
addA('fx_sp_choice', "", 'let v := if a <? b then mv a else mv b in (match v with inl (u, w) => u + w | inr w => w end)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\n')
addA('fx_sp_writes', "", 'let v := fw n a s in (match v with inl (u, w) => u + w | inr w => w end)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint fw (n : nat) (x : int) (t : mem) : ((int * int) + int)%type := match n with O => (let x := rd 0 x t in (if x <? 0 then inl (x, x) else inr x)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_sp_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint fm (n : nat) (v : ((int * int) + int)%type) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with inl (u, w) => u + w | inr w => w end) 1 t) end.\n')
addA('fx_sp_tmpl', "", 'let v := ft n (fun x w => if (match w with inl (u, w) => u + w | inr w => w end) <? 3 then (if x <? 0 then inl (x, x) else inr x) else w) (mv a) b in (match v with inl (u, w) => u + w | inr w => w end)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint ft (n : nat) (f : int -> ((int * int) + int)%type -> ((int * int) + int)%type) (v : ((int * int) + int)%type) (x : int) : ((int * int) + int)%type := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_sp_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint me (n : nat) (v : ((int * int) + int)%type) : int := match n with O => (match v with inl (u, w) => u + w | inr w => w end) | S m => mo m v end with mo (n : nat) (v : ((int * int) + int)%type) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_sp_mutres', "", 'let v := mua n a in (match v with inl (u, w) => u + w | inr w => w end)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nFixpoint mua (n : nat) (x : int) : ((int * int) + int)%type := match n with O => (if x <? 0 then inl (x, x) else inr x) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : ((int * int) + int)%type := match n with O => (if x <? 0 then inl (x, x) else inr x) | S m => mua m (x * 2) end.\n')
addA('fx_sp_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with inl (u, w) => u + w | inr w => w end) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\n')
addA('fx_sp_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with inl (u, w) => u + w | inr w => w end))',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\n')
addA('fx_sp_fun', "", 'tw (fun v => (match v with inl (u, w) => u + w | inr w => w end)) (mv a)',
     'Definition mv (x : int) : ((int * int) + int)%type := (if x <? 0 then inl (x, x) else inr x).\nDefinition tw (f : ((int * int) + int)%type -> int) (v : ((int * int) + int)%type) : int := f v + 1.\n')
addA('fx_sb_let', "", 'let v := mv a in (match v with inl w => w | inr c => if c then 1 else 2 end)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\n')
addA('fx_sb_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nDefinition uv (v : (int + bool)%type) : int := (match v with inl w => w | inr c => if c then 1 else 2 end).\n')
addA('fx_sb_rec', "", 'let v := fr n a in (match v with inl w => w | inr c => if c then 1 else 2 end)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint fr (n : nat) (x : int) : (int + bool)%type := match n with O => (if x <? 0 then inl x else inr (x <? 5)) | S m => fr m (x + 1) end.\n')
addA('fx_sb_nontail', "", 'let v := fn n a in (match v with inl w => w | inr c => if c then 1 else 2 end)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint fn (n : nat) (x : int) : (int + bool)%type := match n with O => (if x <? 0 then inl x else inr (x <? 5)) | S m => let v := fn m (x + 1) in if (match v with inl w => w | inr c => if c then 1 else 2 end) <? 5 then v else (if x <? 0 then inl x else inr (x <? 5)) end.\n')
addA('fx_sb_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint fs (n : nat) (v : (int + bool)%type) (x : int) : int := match n with O => (match v with inl w => w | inr c => if c then 1 else 2 end) + x | S m => fs m (if x <? 0 then inl x else inr (x <? 5)) (x + (match v with inl w => w | inr c => if c then 1 else 2 end)) end.\n')
addA('fx_sb_choice', "", 'let v := if a <? b then mv a else mv b in (match v with inl w => w | inr c => if c then 1 else 2 end)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\n')
addA('fx_sb_writes', "", 'let v := fw n a s in (match v with inl w => w | inr c => if c then 1 else 2 end)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint fw (n : nat) (x : int) (t : mem) : (int + bool)%type := match n with O => (let x := rd 0 x t in (if x <? 0 then inl x else inr (x <? 5))) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_sb_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint fm (n : nat) (v : (int + bool)%type) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with inl w => w | inr c => if c then 1 else 2 end) 1 t) end.\n')
addA('fx_sb_tmpl', "", 'let v := ft n (fun x w => if (match w with inl w => w | inr c => if c then 1 else 2 end) <? 3 then (if x <? 0 then inl x else inr (x <? 5)) else w) (mv a) b in (match v with inl w => w | inr c => if c then 1 else 2 end)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint ft (n : nat) (f : int -> (int + bool)%type -> (int + bool)%type) (v : (int + bool)%type) (x : int) : (int + bool)%type := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_sb_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint me (n : nat) (v : (int + bool)%type) : int := match n with O => (match v with inl w => w | inr c => if c then 1 else 2 end) | S m => mo m v end with mo (n : nat) (v : (int + bool)%type) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_sb_mutres', "", 'let v := mua n a in (match v with inl w => w | inr c => if c then 1 else 2 end)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nFixpoint mua (n : nat) (x : int) : (int + bool)%type := match n with O => (if x <? 0 then inl x else inr (x <? 5)) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (int + bool)%type := match n with O => (if x <? 0 then inl x else inr (x <? 5)) | S m => mua m (x * 2) end.\n')
addA('fx_sb_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with inl w => w | inr c => if c then 1 else 2 end) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\n')
addA('fx_sb_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with inl w => w | inr c => if c then 1 else 2 end))',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\n')
addA('fx_sb_fun', "", 'tw (fun v => (match v with inl w => w | inr c => if c then 1 else 2 end)) (mv a)',
     'Definition mv (x : int) : (int + bool)%type := (if x <? 0 then inl x else inr (x <? 5)).\nDefinition tw (f : (int + bool)%type -> int) (v : (int + bool)%type) : int := f v + 1.\n')
addA('fx_po_let', "", 'let v := mv a in (match v with (Some u, w) => u + w | (None, w) => w end)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\n')
addA('fx_po_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nDefinition uv (v : (option int * int)%type) : int := (match v with (Some u, w) => u + w | (None, w) => w end).\n')
addA('fx_po_rec', "", 'let v := fr n a in (match v with (Some u, w) => u + w | (None, w) => w end)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint fr (n : nat) (x : int) : (option int * int)%type := match n with O => (if x <? 0 then None else Some x, x) | S m => fr m (x + 1) end.\n')
addA('fx_po_nontail', "", 'let v := fn n a in (match v with (Some u, w) => u + w | (None, w) => w end)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint fn (n : nat) (x : int) : (option int * int)%type := match n with O => (if x <? 0 then None else Some x, x) | S m => let v := fn m (x + 1) in if (match v with (Some u, w) => u + w | (None, w) => w end) <? 5 then v else (if x <? 0 then None else Some x, x) end.\n')
addA('fx_po_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint fs (n : nat) (v : (option int * int)%type) (x : int) : int := match n with O => (match v with (Some u, w) => u + w | (None, w) => w end) + x | S m => fs m (if x <? 0 then None else Some x, x) (x + (match v with (Some u, w) => u + w | (None, w) => w end)) end.\n')
addA('fx_po_choice', "", 'let v := if a <? b then mv a else mv b in (match v with (Some u, w) => u + w | (None, w) => w end)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\n')
addA('fx_po_writes', "", 'let v := fw n a s in (match v with (Some u, w) => u + w | (None, w) => w end)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint fw (n : nat) (x : int) (t : mem) : (option int * int)%type := match n with O => (let x := rd 0 x t in (if x <? 0 then None else Some x, x)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_po_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint fm (n : nat) (v : (option int * int)%type) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with (Some u, w) => u + w | (None, w) => w end) 1 t) end.\n')
addA('fx_po_tmpl', "", 'let v := ft n (fun x w => if (match w with (Some u, w) => u + w | (None, w) => w end) <? 3 then (if x <? 0 then None else Some x, x) else w) (mv a) b in (match v with (Some u, w) => u + w | (None, w) => w end)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint ft (n : nat) (f : int -> (option int * int)%type -> (option int * int)%type) (v : (option int * int)%type) (x : int) : (option int * int)%type := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_po_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint me (n : nat) (v : (option int * int)%type) : int := match n with O => (match v with (Some u, w) => u + w | (None, w) => w end) | S m => mo m v end with mo (n : nat) (v : (option int * int)%type) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_po_mutres', "", 'let v := mua n a in (match v with (Some u, w) => u + w | (None, w) => w end)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nFixpoint mua (n : nat) (x : int) : (option int * int)%type := match n with O => (if x <? 0 then None else Some x, x) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (option int * int)%type := match n with O => (if x <? 0 then None else Some x, x) | S m => mua m (x * 2) end.\n')
addA('fx_po_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with (Some u, w) => u + w | (None, w) => w end) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\n')
addA('fx_po_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with (Some u, w) => u + w | (None, w) => w end))',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\n')
addA('fx_po_fun', "", 'tw (fun v => (match v with (Some u, w) => u + w | (None, w) => w end)) (mv a)',
     'Definition mv (x : int) : (option int * int)%type := (if x <? 0 then None else Some x, x).\nDefinition tw (f : (option int * int)%type -> int) (v : (option int * int)%type) : int := f v + 1.\n')
addA('fx_ub_let', "", 'let v := mv a in (snd v + 1)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\n')
addA('fx_ub_param', "", 'uv (mv a)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nDefinition uv (v : (unit * int)%type) : int := (snd v + 1).\n')
addA('fx_ub_rec', "", 'let v := fr n a in (snd v + 1)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint fr (n : nat) (x : int) : (unit * int)%type := match n with O => (tt, x) | S m => fr m (x + 1) end.\n')
addA('fx_ub_nontail', "", 'let v := fn n a in (snd v + 1)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint fn (n : nat) (x : int) : (unit * int)%type := match n with O => (tt, x) | S m => let v := fn m (x + 1) in if (snd v + 1) <? 5 then v else (tt, x) end.\n')
addA('fx_ub_state', "", 'fs n (mv a) b',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint fs (n : nat) (v : (unit * int)%type) (x : int) : int := match n with O => (snd v + 1) + x | S m => fs m (tt, x) (x + (snd v + 1)) end.\n')
addA('fx_ub_choice', "", 'let v := if a <? b then mv a else mv b in (snd v + 1)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\n')
addA('fx_ub_writes', "", 'let v := fw n a s in (snd v + 1)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint fw (n : nat) (x : int) (t : mem) : (unit * int)%type := match n with O => (let x := rd 0 x t in (tt, x)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_ub_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint fm (n : nat) (v : (unit * int)%type) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (snd v + 1) 1 t) end.\n')
addA('fx_ub_tmpl', "", 'let v := ft n (fun x w => if (snd w + 1) <? 3 then (tt, x) else w) (mv a) b in (snd v + 1)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint ft (n : nat) (f : int -> (unit * int)%type -> (unit * int)%type) (v : (unit * int)%type) (x : int) : (unit * int)%type := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_ub_mutual', "", 'me n (mv a)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint me (n : nat) (v : (unit * int)%type) : int := match n with O => (snd v + 1) | S m => mo m v end with mo (n : nat) (v : (unit * int)%type) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_ub_mutres', "", 'let v := mua n a in (snd v + 1)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nFixpoint mua (n : nat) (x : int) : (unit * int)%type := match n with O => (tt, x) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : (unit * int)%type := match n with O => (tt, x) | S m => mua m (x * 2) end.\n')
addA('fx_ub_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (snd v + 1) | S q => g q (x + 1) end in g n b',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\n')
addA('fx_ub_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (snd v + 1))',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\n')
addA('fx_ub_fun', "", 'tw (fun v => (snd v + 1)) (mv a)',
     'Definition mv (x : int) : (unit * int)%type := (tt, x).\nDefinition tw (f : (unit * int)%type -> int) (v : (unit * int)%type) : int := f v + 1.\n')
addA('fx_dd_let', "", 'let v := mv a in (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\n')
addA('fx_dd_param', "", 'uv (mv a)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nDefinition uv (v : dp) : int := (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end).\n')
addA('fx_dd_rec', "", 'let v := fr n a in (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint fr (n : nat) (x : int) : dp := match n with O => (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC) | S m => fr m (x + 1) end.\n')
addA('fx_dd_nontail', "", 'let v := fn n a in (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint fn (n : nat) (x : int) : dp := match n with O => (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC) | S m => let v := fn m (x + 1) in if (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end) <? 5 then v else (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC) end.\n')
addA('fx_dd_state', "", 'fs n (mv a) b',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint fs (n : nat) (v : dp) (x : int) : int := match n with O => (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end) + x | S m => fs m (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC) (x + (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)) end.\n')
addA('fx_dd_choice', "", 'let v := if a <? b then mv a else mv b in (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\n')
addA('fx_dd_writes', "", 'let v := fw n a s in (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint fw (n : nat) (x : int) (t : mem) : dp := match n with O => (let x := rd 0 x t in (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC)) | S m => fw m (x + 1) (upd 0 x x t) end.\n')
addA('fx_dd_mem', "", 'rd 0 0 (fm n (mv a) s)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint fm (n : nat) (v : dp) (t : mem) : mem := match n with O => t | S m => fm m v (upd 0 (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end) 1 t) end.\n')
addA('fx_dd_tmpl', "", 'let v := ft n (fun x w => if (match w with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end) <? 3 then (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC) else w) (mv a) b in (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint ft (n : nat) (f : int -> dp -> dp) (v : dp) (x : int) : dp := match n with O => v | S m => ft m f (f x v) (x + 1) end.\n')
addA('fx_dd_mutual', "", 'me n (mv a)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint me (n : nat) (v : dp) : int := match n with O => (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end) | S m => mo m v end with mo (n : nat) (v : dp) : int := match n with O => 1 | S m => me m v end.\n')
addA('fx_dd_mutres', "", 'let v := mua n a in (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nFixpoint mua (n : nat) (x : int) : dp := match n with O => (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC) | S m => mub m (x + 1) end with mub (n : nat) (x : int) : dp := match n with O => (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC) | S m => mua m (x * 2) end.\n')
addA('fx_dd_lfix', "", 'let v := mv a in let fix g (m : nat) (x : int) : int := match m with O => x + (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end) | S q => g q (x + 1) end in g n b',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\n')
addA('fx_dd_closure', "", 'let v := mv a in fold n 0 b (fun i acc => acc + (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end))',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\n')
addA('fx_dd_fun', "", 'tw (fun v => (match v with DA (u, w) => u + w | DB c n => if c then n else 1 | DC => 2 end)) (mv a)',
     'Inductive dp := DA (p : int * int) | DB (c : bool) (n : int) | DC.\nDefinition mv (x : int) : dp := (if x <? 0 then DA (x, x) else if x <? 5 then DB (x <? 1) x else DC).\nDefinition tw (f : dp -> int) (v : dp) : int := f v + 1.\n')
addA("fx_bool_arg", "", "gb (snd (mv a))", "Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\nDefinition gb (c : bool) : int := if c then 1 else 2.\n")
addA("fx_bool_and", "", "if snd (mv a) && (a <? b) then a else b", "Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\n")
addA("fx_bool_let", "", "let c := snd (mv a) in if negb c then a else b", "Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\n")
addA("fx_bool_copy", "", "let p := mv a in let q := (fst p + 1, snd p) in if snd q then fst q else b", "Definition mv (x : int) : (int * bool)%type := (x, x <? 3).\n")
addA("fx_bool_val", "", "if snd (fb (a <? b) a) then a else b", "Definition fb (c : bool) (x : int) : (int * bool)%type := (x, c).\n")
addA("fx_bool_lit", "", "if snd (fb a) then a else b", "Definition fb (x : int) : (int * bool)%type := (x, true).\n")
addA("fx_nested3", "", "match mv a with (Some (u, c), w) => if c then u else w | (None, w) => w end", "Definition mv (x : int) : (option (int * bool) * int)%type := (if x <? 0 then None else Some (x, x <? 3), x).\n")
addA("fx_nested3_rec", "", "match fr n a with (Some (u, c), w) => if c then u else w | (None, w) => w end", "Fixpoint fr (n : nat) (x : int) : (option (int * bool) * int)%type := match n with O => (None, x) | S m => if x <? 3 then (Some (x, x <? 1), x) else fr m (x - 1) end.\n")
addA("fx_opt_mem", "", "match fo a s with Some t => rd 0 0 t | None => b end", "Definition fo (x : int) (t : mem) : option mem := if x <? 0 then None else Some (upd 0 0 x t).\n")
addA("fx_opt_mem_rec", "", "match fo n a s with Some t => rd 0 0 t | None => b end", "Fixpoint fo (n : nat) (x : int) (t : mem) : option mem := match n with O => Some t | S m => if x <? 0 then None else fo m (x - 1) (upd 0 0 x t) end.\n")
addA("par_mutual_three", "", "h n a", "Fixpoint h (n : nat) (x : int) : int := match n with O => x | S m => if t1 m x then fst (t2 m x) else x + 1 end\nwith t1 (n : nat) (x : int) : bool := match n with O => x <? 3 | S m => h m x <? 5 end\nwith t2 (n : nat) (x : int) : int * int := match n with O => (x, x) | S m => (h m (x + 1), x) end.\n")
addA("fx_nat_pair", "", "let (k, v) := fp n a in match k with O => v | S _ => b end", "Fixpoint fp (m : nat) (x : int) : nat * int := match m with O => (O, x) | S q => let (k, v) := fp q (x + 1) in (k, v + 1) end.\n")
addA("fx_nat_field", "", "match nc (fk a) with O => a | S _ => nv (fk a) end", "Record rn := mkn { nc : nat; nv : int }.\nDefinition fk (x : int) : rn := mkn 3 x.\n")
addA("fx_nat_opt", "", "match fq n with Some _ => a | None => b end", "Definition fq (m : nat) : option nat := match m with O => None | S q => Some q end.\n")
# counters: Nat.min, Nat.max, Nat.sub, Nat.div2 in more places (step 66)
addA("c_min_arg", "", "ff (Nat.min n 3) a",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_max_arg", "", "ff (Nat.max n 3) a",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_sub_arg", "", "ff (Nat.sub n 1) a",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_div2_arg", "", "ff (Nat.div2 n) a",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_min_let", "", "let k := Nat.min n 3 in ff k a + ff k b",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_sub_match", "", "match Nat.sub n 1 with O => a | S q => ff q b end",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_div2_match", "", "match Nat.div2 n with O => a | S q => ff q b end",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_nest", "", "ff (Nat.min (Nat.sub n 1) (Nat.max n 2)) a",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
addA("c_sub_cmp", "", "if Nat.leb (Nat.sub n 2) (Nat.div2 n) then a else b",
     "Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n")
# the operations of Rocq's machine numbers its axioms define by others (step 64), in more places
addA("pm_addcarryc", "", "match PrimInt63.addcarryc a b with C0 v => v | C1 v => v + 1 end",
     "From Corelib Require Import Numbers.Cyclic.Int63.CarryType.\n")
addA("pm_subcarryc", "", "match PrimInt63.subcarryc a b with C0 v => v | C1 v => v + 1 end",
     "From Corelib Require Import Numbers.Cyclic.Int63.CarryType.\n")
addA("pm_compare_fix", "", "kc n a b",
     "Fixpoint kc (n : nat) (x y : int) : int := match n with O => x | S m => match PrimInt63.compare x y with Eq => y | Lt => kc m (x + 1) y | Gt => kc m x (y + 1) end end.\n")
addA("pm_compare_mem", "", "kc n a b s",
     "Fixpoint kc (n : nat) (x y : int) (t : mem) : int := match n with O => rd 0 x t | S m => match PrimInt63.compare x y with Eq => y | Lt => kc m (x + 1) y (upd 0 x y t) | Gt => kc m x (y + 1) t end end.\n")
addA("pm_compare_op", "", "kc n a b",
     "Fixpoint kc (n : nat) (x y : int) : int := match n with O => x | S m => (match PrimInt63.compare x y with Eq => y | Lt => kc m (x + 1) y | Gt => 0 end) + 1 end.\n")
addA("pm_compare_let", "", "kl a b",
     "Definition kl (x y : int) : int := let c := PrimInt63.compare x y in match c with Eq => 1 | Lt => 2 | Gt => 3 end.\n")
addA("pm_compare_res", "", "cn (cres a b)",
     "Definition cres (x y : int) : comparison := PrimInt63.compare x y.\nDefinition cn (c : comparison) : int := match c with Eq => 1 | Lt => 2 | Gt => 3 end.\n")
addA("pm_addc_fix", "", "kc n a b",
     "From Corelib Require Import Numbers.Cyclic.Int63.CarryType.\nFixpoint kc (n : nat) (x y : int) : int := match n with O => x | S m => match PrimInt63.addc x y with C0 v => kc m v y | C1 v => v end end.\n")
addA("pm_addc_mem", "", "rd 0 0 (kc n a b s)",
     "From Corelib Require Import Numbers.Cyclic.Int63.CarryType.\nFixpoint kc (n : nat) (x y : int) (t : mem) : mem := match n with O => t | S m => match PrimInt63.addc x y with C0 v => kc m v y (upd 0 x v t) | C1 v => upd 0 x v t end end.\n")
addA("pm_diveucl_fix", "", "kc n a b",
     "Fixpoint kc (n : nat) (x y : int) : int := match n with O => x | S m => let (q, r) := PrimInt63.diveucl x y in kc m q r end.\n")
addA("pm_addmuldiv_fix", "", "kc n a b",
     "Fixpoint kc (n : nat) (x y : int) : int := match n with O => x | S m => kc m (PrimInt63.addmuldiv 3 x y) y end.\n")
addA("pm_two", "", "PrimInt63.addmuldiv 1 a b + (let (q, r) := PrimInt63.diveucl a b in q)",
     "")
# natural forms found by a probe (step 63): what Rocq's libraries define, the operations of PrimInt63, casts, data of other sorts
addA("n_nat_iter", "", "Nat.iter n (fun v => v + 1) a",
     "")
addA("n_nat_iter_mem", "", "rd 0 0 (Nat.iter n (fun t => upd 0 a b t) s)",
     "")
addA("n_nat_rect", "", "nat_rect (fun _ => int) a (fun _ r => r + 1) n",
     "")
addA("n_nat_rec", "", "nat_rec (fun _ => int) a (fun _ r => r + 1) n",
     "")
addA("n_compare", "", "match PrimInt63.compare a b with Eq => 0 | Lt => 1 | Gt => 2 end",
     "")
addA("n_compares", "", "match PrimInt63.compares a b with Eq => 0 | Lt => 1 | Gt => 2 end",
     "")
addA("n_xorb", "", "if xorb (a <? b) (b <? a) then a else b",
     "")
addA("n_bool_eqb", "", "if Bool.eqb (a <? b) (b <? a) then a else b",
     "")
addA("n_implb", "", "if implb (a <? b) (b <? a) then a else b",
     "")
addA("n_nat_eqb", "", "if Nat.eqb n 0 then a else b",
     "")
addA("n_nat_leb", "", "if Nat.leb n 3 then a else b",
     "")
addA("n_nat_ltb", "", "if Nat.ltb n 3 then a else b",
     "")
addA("n_nat_pred", "", "if Nat.ltb (Nat.pred n) 3 then a else b",
     "")
addA("n_nat_min", "", "if Nat.ltb (Nat.min n 3) 2 then a else b",
     "")
addA("n_head0", "", "PrimInt63.head0 a",
     "")
addA("n_tail0", "", "PrimInt63.tail0 a",
     "")
addA("n_mulc", "", "match PrimInt63.mulc a b with pair h l => h + l end",
     "")
addA("n_addc", "", "match PrimInt63.addc a b with C0 v => v | C1 v => v + 1 end",
     "From Corelib Require Import Numbers.Cyclic.Int63.CarryType.\n")
addA("n_subc", "", "match PrimInt63.subc a b with C0 v => v | C1 v => v + 1 end",
     "From Corelib Require Import Numbers.Cyclic.Int63.CarryType.\n")
addA("n_diveucl", "", "match PrimInt63.diveucl a b with pair q r => q + r end",
     "")
addA("n_diveucl_21", "", "match PrimInt63.diveucl_21 a b 3 with pair q r => q + r end",
     "")
addA("n_addmuldiv", "", "PrimInt63.addmuldiv a b 3",
     "")
addA("n_sint_abs", "", "Sint63.abs a",
     "")
addA("n_sint_asr", "", "PrimInt63.asr a 1",
     "")
addA("n_uint_opp", "", "Uint63.opp a",
     "")
addA("n_uint_oppc", "", "Uint63.oppcarry a",
     "")
addA("n_uint_pred", "", "Uint63.pred a",
     "")
addA("n_uint_succ", "", "Uint63.succ a",
     "")
addA("n_is_zero", "", "if Uint63.is_zero a then a else b",
     "")
addA("n_is_even", "", "if Uint63.is_even a then a else b",
     "")
addA("n_uint_eqb", "", "if PrimInt63.eqb a b then a else b",
     "")
addA("n_pat_let", "", "let '(x, y) := hp a b in x + y",
     "")
addA("n_pat_let_rec", "", "let 'mk3 p q r := hr a b in p + q + r",
     "")
addA("n_nested_pair", "", "let '(x, (y, z)) := tp a b in x + y + z",
     "Definition tp (a b : int) : int * (int * int) := (a, (b, a + b)).\n")
addA("n_idd", "", "idd a + b",
     "Definition idd {A : Type} (x : A) : A := x.\n")
addA("n_poly_fst", "", "fsta (a, b)",
     "Definition fsta {A B : Type} (p : A * B) : A := fst p.\n")
addA("n_section", "", "sf a n b",
     "Section Sc.\nVariable k : int.\nFixpoint sf (m : nat) (x : int) : int := match m with O => x + k | S q => sf q (x + k) end.\nEnd Sc.\n")
addA("n_section_ctx", "", "sg a b",
     "Section Sc.\nContext (k : int).\nDefinition sg (x : int) : int := x + k.\nEnd Sc.\n")
addA("n_sig_param", "", "sp (exist _ 1 one_pos) + a",
     "Definition sp (x : {v : int | (0 < Sint63.to_Z v)%Z}) : int := proj1_sig x + 1.\nLemma one_pos : (0 < Sint63.to_Z 1)%Z. Proof. reflexivity. Qed.\n")
addA("n_sig_result", "", "proj1_sig (sr a) + b",
     "Definition sr (x : int) : {v : int | v = x} := exist _ x eq_refl.\n")
addA("n_enum", "", "cn (col a) + b",
     "Inductive color := Red | Green | Blue.\nDefinition cn (c : color) : int := match c with Red => 1 | Green => 2 | Blue => 3 end.\nDefinition col (x : int) : color := if x <? 0 then Red else if x <? 5 then Green else Blue.\n")
addA("n_sum_ty", "", "match sm a with inl v => v | inr c => if c then 1 else 2 end",
     "Definition sm (x : int) : int + bool := if x <? 0 then inl x else inr (x <? 5).\n")
addA("n_ind_args", "", "ar (mks a) + b",
     "Inductive sh := Cir (r : int) | Rect (w h : int) | Pt.\nDefinition ar (s0 : sh) : int := match s0 with Cir r => r * r | Rect w h => w * h | Pt => 0 end.\nDefinition mks (x : int) : sh := if x <? 0 then Pt else if x <? 5 then Cir x else Rect x x.\n")
addA("n_unit_arg", "", "un tt a",
     "Definition un (u : unit) (x : int) : int := x + 1.\n")
addA("n_unit_res", "", "match unr a with tt => b end",
     "Definition unr (x : int) : unit := tt.\n")
addA("n_bool_let", "", "let c := a <? b in let d := negb c in if andb c d then a else b",
     "")
addA("n_nat_let", "", "let k := S n in if Nat.ltb k 3 then a else b",
     "")
addA("n_coerc", "", "(a <? b) + (b : int)",
     "Definition b2i (c : bool) : int := if c then 1 else 0.\nCoercion b2i : bool >-> int.\n")
addA("n_notation_op", "", "a ** b",
     "Notation \"x ** y\" := (x * y + 1) (at level 40).\n")
addA("n_record_update", "", "f1 (up1 (mk3 a b 0) 7) + f2 (up1 (mk3 a b 0) 7)",
     "Definition up1 (r : r3) (v : int) : r3 := {| f1 := v; f2 := f2 r; f3 := f3 r |}.\n")
addA("n_record_in_record", "", "f1 (g1 (mk2 (mk3 a b 0) 1)) + g2 (mk2 (mk3 a b 0) 1)",
     "Record r2 := mk2 { g1 : r3; g2 : int }.\n")
addA("n_match_int_lit", "", "lk a",
     "Definition lk (x : int) : int := if x =? 0 then 10 else if x =? 1 then 11 else 12.\n")
addA("n_big_lit", "", "a + 4611686018427387903",
     "")
addA("n_neg_lit", "", "a + (-5)%sint63",
     "")
addA("n_hex_lit", "", "a land 0xff",
     "")
addA("n_shift", "", "(a << 3) >> 1",
     "")
addA("n_fun_ret", "", "adder a b",
     "Definition adder (k : int) : int -> int := fun x => x + k.\n")
addA("n_fun_compose", "", "cmp (fun v => v + 1) (fun v => v * 2) a",
     "Definition cmp (f g : int -> int) (x : int) : int := f (g x).\n")
addA("n_fun_pair", "", "twoa (fun v => v + 1, a)",
     "Definition twoa (p : (int -> int) * int) : int := (fst p) (snd p).\n")
addA("n_fix_in_let", "", "let k := (fix lp (m : nat) (x : int) : int := match m with O => x | S q => lp q (x + 1) end) n a in k + b",
     "")
addA("n_wildcard_nat", "", "wn n a",
     "Fixpoint wn (m : nat) (x : int) : int := match m with S (S (S q)) => wn q (x + 3) | S _ => x + 1 | O => x end.\n")
addA("n_nat_lit_match", "", "nl n a",
     "Definition nl (m : nat) (x : int) : int := match m with 0%nat => x | 1%nat => x + 1 | 2%nat => x + 2 | _ => x + 3 end.\n")
addA("n_unit_arg2", "", "un (unr a) b",
     "Definition unr (x : int) : unit := tt.\nDefinition un (u : unit) (x : int) : int := x + 1.\n")
addA("n_coerc0", "", "b2i (a <? b) + b",
     "Definition b2i (c : bool) : int := if c then 1 else 0.\n")
addA("n_cast", "", "(a + b : int)",
     "")
addA("n_cast_arg", "", "h (a + b : int) b",
     "")
addA("n_cast_in_fix", "", "cf n a",
     "Fixpoint cf (m : nat) (x : int) : int := match m with O => x | S q => (cf q (x + 1) : int) + 1 end.\n")
addA("n_nat_max", "", "if Nat.ltb (Nat.max n 3) 2 then a else b",
     "")
addA("n_nat_sub", "", "if Nat.ltb (Nat.sub n 1) 2 then a else b",
     "")
addA("n_nat_even", "", "if Nat.even n then a else b",
     "")
addA("n_nat_div2", "", "if Nat.ltb (Nat.div2 n) 2 then a else b",
     "")
addA("n_nat_mul", "", "if Nat.ltb (Nat.mul n 2) 9 then a else b",
     "")
addA("n_option_bool", "", "match ob a with Some c => if c then 1 else 2 | None => b end",
     "Definition ob (x : int) : option bool := if x <? 0 then None else Some (x <? 5).\n")
addA("n_record_bool", "", "if b1 (mr a) then b2 (mr b) else a",
     "Record rb := mkb { b1 : bool; b2 : int }.\nDefinition mr (x : int) : rb := mkb (x <? 3) x.\n")
# (step 62) wf lt; a mutual block of mixed sorts that only reads; a mutual block whose match gives a function
addA("pf_wf_lt", "", "pq n a",
     "From Stdlib Require Import Program.Wf.\nProgram Fixpoint pq (n : nat) (x : int) {wf lt n} : int :=\n  match n with O => x | S m => pq m (x + 1) end.\n")
addA("fn_wf_lt", "", "pq n a",
     "From Stdlib Require Import Recdef Lia Wf_nat Arith.\nFunction pq (n : nat) (x : int) {wf lt n} : int :=\n  match n with O => x | S m => pq m (x + 1) end.\nProof. intros; lia. exact lt_wf. Defined.\n")
addA("par_mutual_int_bool", "", "ev n a",
     "Fixpoint ev (n : nat) (x : int) : int := match n with O => x | S m => if od m x then x else x + 1 end\nwith od (n : nat) (x : int) : bool := match n with O => x <? 3 | S m => ev m x <? 5 end.\n")
addA("par_mutual_int_bool_mem", "", "ev n a s",
     "Fixpoint ev (n : nat) (x : int) (t : mem) : int := match n with O => rd 0 x t | S m => if od m x t then x else x + 1 end\nwith od (n : nat) (x : int) (t : mem) : bool := match n with O => x <? rd 0 x t | S m => ev m x t <? 5 end.\n")
addA("par_mutual_int_record", "", "ev n a",
     "Fixpoint ev (n : nat) (x : int) : int := match n with O => x | S m => f1 (od m x) + x end\nwith od (n : nat) (x : int) : r3 := match n with O => mk3 x 0 0 | S m => mk3 (ev m x) x 1 end.\n")
addA("par_mutual_three", "", "ev n a",
     "Fixpoint ev (n : nat) (x : int) : int := match n with O => x | S m => if od m x then f1 (pd m x) else x + 1 end\nwith od (n : nat) (x : int) : bool := match n with O => x <? 3 | S m => ev m x <? 5 end\nwith pd (n : nat) (x : int) : r3 := match n with O => mk3 x 0 0 | S m => mk3 (ev m (x + 1)) x 1 end.\n")
addA("par_mutual_both_self", "", "ev n a",
     "Fixpoint ev (n : nat) (x : int) : int := match n with O => x | S m => if od m x then ev m (x + 1) else x + 1 end\nwith od (n : nat) (x : int) : bool := match n with O => x <? 3 | S m => if ev m x <? 5 then od m (x + 1) else true end.\n")
# the function's own call under a choice, the places around it (step 61)
addA("own_two_choices", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => (if a <? b then ko m (a + 1) b (upd 0 a b t) else a) + (if b <? a then ko m a (b + 1) t else b) end.\n")
addA("own_match_counter", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => (match m with O => a | S q => ko q (a + 1) b (upd 0 a b t) end) + b end.\n")
addA("own_in_own_arg", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => ko m (if a <? b then ko m (a + 1) b t else a) b t end.\n")
addA("own_deep_fib", "", "ko n a",
     "Fixpoint ko (n : nat) (a : int) : int := match n with O => a | S m => match m with O => a + 1 | S q => ko m (a + 1) + ko q (a + 2) end end.\n")
addA("own_deep_fib_mem", "", "ko n a s",
     "Fixpoint ko (n : nat) (a : int) (t : mem) : int := match n with O => a | S m => match m with O => a + rd 0 a t | S q => ko m (a + 1) t + ko q (a + 2) t end end.\n")
addA("own_deep_tail_read", "", "ko n a s",
     "Fixpoint ko (n : nat) (a : int) (t : mem) : int := match n with O => a | S m => match m with O => a + rd 0 a t | S q => ko q (a + 2) t end end.\n")
addA("own_deep_write_mem", "", "rd 0 0 (ko n a s)",
     "Fixpoint ko (n : nat) (a : int) (t : mem) : mem := match n with O => t | S m => match m with O => upd 0 a a t | S q => ko q (a + 2) (upd 0 a a t) end end.\n")
addA("own_deep_write_mem2", "", "rd 0 0 (ko n a s)",
     "Fixpoint ko (n : nat) (a : int) (t : mem) : mem := match n with O => t | S m => match m with O => ko m a t | S q => ko q (a + 2) (upd 0 a a t) end end.\n")
addA("own_deep_bool", "", "if ko n a then a else b",
     "Fixpoint ko (n : nat) (a : int) : bool := match n with O => true | S m => match m with O => false | S q => ko q (a + 2) end end.\n")
addA("own_deep_record", "", "f1 (ko n a)",
     "Fixpoint ko (n : nat) (a : int) : r3 := match n with O => mk3 a 0 0 | S m => match m with O => mk3 0 a 0 | S q => ko q (a + 2) end end.\n")
addA("own_match_deep_tail", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => match m with O => a | S q => ko q (a + 1) b (upd 0 a b t) end end.\n")
addA("own_match_deep_op", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => match m with O => a | S q => ko q (a + 1) b (upd 0 a b t) + b end end.\n")
addA("own_match_deep_read", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => (match m with O => a | S q => ko q (a + 1) b t end) + b end.\n")
addA("own_two_choices_read", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => (if a <? b then ko m (a + 1) b t else a) + (if b <? a then ko m a (b + 1) t else b) end.\n")
addA("own_let_used", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => let v := (if a <? b then ko m (a + 1) b (upd 0 a b t) else a) in v * v + b end.\n")
addA("own_in_test", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => if (if a <? b then ko m (a + 1) b (upd 0 a b t) else a) <? b then a else b end.\n")
addA("own_in_helper_arg", "", "ko n a b s",
     "Definition hh (x y : int) : int := x * 2 + y.\nFixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => hh (if a <? b then ko m (a + 1) b (upd 0 a b t) else a) b end.\n")
addA("own_deep", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => ((if a <? b then (if b <? 9 then ko m (a + 1) b (upd 0 a b t) else b) else a) + 1) * 2 end.\n")
addA("own_read_after", "", "ko n a b s",
     "Fixpoint ko (n : nat) (a b : int) (t : mem) : int := match n with O => a | S m => (if a <? b then ko m (a + 1) b (upd 0 a b t) else rd 0 a t) + rd 0 b t end.\n")
# Equations (step 60): each sort, tests through inspect and dec, nested, a measure on a counter and in phases, a function as a parameter, no recursion, structural, mutual
addA("eq_tail", "", "pq a b",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x y : int) : int by wf (mu x) lt :=\n  pq x y with inspect (0 <? x) => {\n    | true eqn: H => pq (x - 1) (y + x)\n    | false eqn: _ => y }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_read", "", "pq a b s",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x y : int) (t : mem) : int by wf (mu x) lt :=\n  pq x y t with inspect (0 <? x) => {\n    | true eqn: H => pq (x - 1) (y + rd 0 x t) t\n    | false eqn: _ => y }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_write_num", "", "pq a s",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) (t : mem) : int by wf (mu x) lt :=\n  pq x t with inspect (0 <? x) => {\n    | true eqn: H => pq (x - 1) (upd 0 x x t) + 1\n    | false eqn: _ => rd 0 0 t }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_bool", "", "if pq a then a else b",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : bool by wf (mu x) lt :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => negb (pq (x - 1))\n    | false eqn: _ => true }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_record", "", "f1 (pq a)",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : r3 by wf (mu x) lt :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => let w := pq (x - 1) in mk3 (f1 w + x) (f2 w) 0\n    | false eqn: _ => mk3 0 0 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_pair_result", "", "fst (pq a s)",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) (t : mem) : int * mem by wf (mu x) lt :=\n  pq x t with inspect (0 <? x) => {\n    | true eqn: H => pq (x - 1) (upd 0 x x t)\n    | false eqn: _ => (x, t) }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_let", "", "pq a b",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x y : int) : int by wf (mu x) lt :=\n  pq x y with inspect (0 <? x) => {\n    | true eqn: H => let z := y + x in pq (x - 1) z\n    | false eqn: _ => y }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_caller_fix", "", "kc n a",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : int by wf (mu x) lt :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => x + pq (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\nFixpoint kc (n : nat) (x : int) : int := match n with O => pq x | S m => kc m (pq x) end.\n")
addA("eq_in_module", "", "Lib.pq a",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nModule Lib.\nEquations pq (x : int) : int by wf (mu x) lt :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => x + pq (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\nEnd Lib.\n")
addA("eq_two", "", "pq a + pr b",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : int by wf (mu x) lt :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => x + pq (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\nEquations pr (x : int) : int by wf (mu x) lt :=\n  pr x with inspect (0 <? x) => {\n    | true eqn: H => pr (x - 1) + 1\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_given", "", "fold n a b (fun i acc => acc + pq i)",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : int by wf (mu x) lt :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => x + pq (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_nested", "", "pq a b",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x y : int) : int by wf (mu x) lt :=\n  pq x y with inspect (0 <? x) => {\n    | true eqn: H with inspect (y <? x) => {\n      | true eqn: H2 => pq (x - 1) y\n      | false eqn: _ => x + pq (x - 1) (y - 1) }\n    | false eqn: _ => y }.\nNext Obligation. apply mu_pred. auto. Qed.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_dec", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : int by wf (mu x) lt :=\n  pq x with dec (0 <? x) => {\n    | left H => x + pq (x - 1)\n    | right _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_counter", "", "pq n a",
     "From Stdlib Require Import Lia.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (n : nat) (x : int) : int by wf n lt :=\n  pq O x := x;\n  pq (S m) x := pq m (x + 1).\n")
addA("eq_pair_param", "", "pq (a, b)",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (p : int * int) : int by wf (mu (fst p)) lt :=\n  pq (x, y) with inspect (0 <? x) => {\n    | true eqn: H => pq (x - 1, y + x)\n    | false eqn: _ => y }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_hi_lo", "", "pq a b",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nLemma ltb_z : forall a b : int, (a <? b) = true -> (Sint63.to_Z a < Sint63.to_Z b)%Z.\nProof. intros a b H. apply Sint63.ltb_spec in H. exact H. Qed.\nLemma z_pred : forall x, (0 <? x) = true -> Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z.\nProof.\n  intros x H. apply ltb_z in H. change (Sint63.to_Z 0) with 0%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia.\nQed.\nEquations pq (lo hi : int) : int by wf (Z.to_nat (Sint63.to_Z hi - Sint63.to_Z lo)) lt :=\n  pq lo hi with inspect (0 <? hi) => {\n    | true eqn: H with inspect (lo <? hi) => {\n      | true eqn: H2 => hi + pq lo (hi - 1)\n      | false eqn: _ => 0 }\n    | false eqn: _ => 0 }.\nNext Obligation. pose proof (z_pred hi H) as E. apply ltb_z in H2. rewrite E. lia. Qed.\n")
addA("eq_fun_param", "", "pq (fun i => i + b) a",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (f : int -> int) (x : int) : int by wf (mu x) lt :=\n  pq f x with inspect (0 <? x) => {\n    | true eqn: H => f x + pq f (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_fun_two", "", "pq (fun i => i + b) a + pq (fun i => rd 0 i s) b",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (f : int -> int) (x : int) : int by wf (mu x) lt :=\n  pq f x with inspect (0 <? x) => {\n    | true eqn: H => f x + pq f (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_with_plain", "", "pq a",
     "From Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : int :=\n  pq x with (0 <? x) => {\n    | true => x + 1\n    | false => 0 }.\n")
addA("eq_struct", "", "pq n a",
     "From Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (n : nat) (x : int) : int :=\n  pq O x := x;\n  pq (S m) x := pq m (x + 1).\n")
addA("eq_mutual", "", "pq n a",
     "From Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (n : nat) (x : int) : int := {\n  pq O x := x;\n  pq (S m) x := pr m (x + 1) }\nwith pr (n : nat) (x : int) : int := {\n  pr O x := x + 2;\n  pr (S m) x := pq m (x + 3) }.\n")
addA("eq_where", "", "pq a",
     "From Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : int :=\n  pq x := go x\n  where go (z : int) : int :=\n  go z := z + 1.\n")
addA("eq_wf_rel", "", "pq a",
     "From Stdlib Require Import ZArith Lia.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nDefinition R (a b : int) : Prop := (mu a < mu b)%nat.\nLemma wfR : well_founded R. Proof. exact (Wf_nat.well_founded_ltof int mu). Qed.\n#[local] Instance wfR_i : WellFounded R := wfR.\nEquations pq (x : int) : int by wf x R :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => x + pq (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("par_match_fun", "", "pq n a",
     "Fixpoint pq (n : nat) : int -> int :=\n  match n with\n  | O => fun x => x\n  | S m => fun x => pq m (x + 1)\n  end.\n")
addA("par_match_fun_app", "", "pq n a",
     "Fixpoint pq (n : nat) (x : int) : int :=\n  (match n with\n   | O => fun y => y\n   | S m => fun y => pq m (y + 1)\n   end) x.\n")
addA("par_match_fun_mem", "", "rd 0 0 (pq n a s)",
     "Fixpoint pq (n : nat) (x : int) : mem -> mem :=\n  match n with\n  | O => fun t => t\n  | S m => fun t => pq m (x + 1) (upd 0 x x t)\n  end.\n")
addA("par_match_fun_mutual", "", "pq n a",
     "Fixpoint pq (n : nat) : int -> int :=\n  match n with\n  | O => fun x => x\n  | S m => fun x => pr m (x + 1)\n  end\nwith pr (n : nat) : int -> int :=\n  match n with\n  | O => fun x => x + 2\n  | S m => fun x => pq m (x + 3)\n  end.\n")
addA("par_match_fun_nontail", "", "pq n a",
     "Fixpoint pq (n : nat) : int -> int :=\n  match n with\n  | O => fun x => x\n  | S m => fun x => x + pq m (x + 1)\n  end.\n")
# a function as a parameter of a measure recursion (step 59): a copy per function given, each sort, a function named, reading the memory, giving a boolean
addA("fn_f_two", "", "pq (fun i => i + b) a + pq (fun i => i * 2) b",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then f x + pq f (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_two", "", "pq (fun i => i + b) a + pq (fun i => i * 2) b",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + pq f (x - 1) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_named", "", "pq inc a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nDefinition inc (i : int) : int := i + 1.\nFunction pq (f : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then f x + pq f (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_named", "", "pq inc a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nDefinition inc (i : int) : int := i + 1.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + pq f (x - 1) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_reads", "", "pq (fun i => rd 0 i s) a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then f x + pq f (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_reads", "", "pq (fun i => rd 0 i s) a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + pq f (x - 1) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_bool", "", "pq (fun i => i <? b) a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> bool) (x : int) {measure mu x} : int :=\n  if 0 <? x then (if f x then x + pq f (x - 1) else pq f (x - 1)) else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_bool", "", "pq (fun i => i <? b) a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> bool) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then (if f x then x + pq f (x - 1) else pq f (x - 1)) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_second", "", "pq a (fun i => i + b)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) (f : int -> int) {measure mu x} : int :=\n  if 0 <? x then f x + pq (x - 1) f else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_second", "", "pq a (fun i => i + b)",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) (f : int -> int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + pq (x - 1) f else 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_two_fns", "", "pq (fun i => i + b) (fun i => i * b) a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f g : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then f x + g x + pq f g (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_two_fns", "", "pq (fun i => i + b) (fun i => i * b) a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f g : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + g x + pq f g (x - 1) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_mem", "", "rd 0 0 (pq (fun i => i + b) a s)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) (t : mem) {measure mu x} : mem :=\n  if 0 <? x then pq f (x - 1) (upd 0 x (f x) t) else t.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_mem", "", "rd 0 0 (pq (fun i => i + b) a s)",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) (t : mem) {measure (mu x)} : mem :=\n  if dec (0 <? x) then pq f (x - 1) (upd 0 x (f x) t) else t.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_write_num", "", "pq (fun i => i + b) a s",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) (t : mem) {measure mu x} : int :=\n  if 0 <? x then pq f (x - 1) (upd 0 x (f x) t) + 1 else rd 0 0 t.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_write_num", "", "pq (fun i => i + b) a s",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) (t : mem) {measure (mu x)} : int :=\n  if dec (0 <? x) then pq f (x - 1) (upd 0 x (f x) t) + 1 else rd 0 0 t.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_record", "", "f1 (pq (fun i => i + b) a)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) {measure mu x} : r3 :=\n  if 0 <? x then let w := pq f (x - 1) in mk3 (f1 w + f x) (f2 w) 0 else mk3 0 0 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_record", "", "f1 (pq (fun i => i + b) a)",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : r3 :=\n  if dec (0 <? x) then let w := pq f (x - 1) in mk3 (f1 w + f x) (f2 w) 0 else mk3 0 0 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_given", "", "fold n a b (fun i acc => acc + pq (fun j => j + i) i)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then f x + pq f (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_given", "", "fold n a b (fun i acc => acc + pq (fun j => j + i) i)",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + pq f (x - 1) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("fn_f_helper", "", "hh (fun i => i + b) a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then f x + pq f (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Qed.\nDefinition hh (g : int -> int) (y : int) : int := pq g y + 1.\n")
addA("pf_f_helper", "", "hh (fun i => i + b) a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + pq f (x - 1) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\nDefinition hh (g : int -> int) (y : int) : int := pq g y + 1.\n")
addA("fn_f_counter", "", "pq (fun i => i + b) n a",
     "From Stdlib Require Import Recdef Lia.\nFunction pq (f : int -> int) (n : nat) (x : int) {measure (fun k => k) n} : int :=\n  match n with O => x | S m => pq f m (f x) end.\nProof. intros; lia. Defined.\n")
addA("pf_f_counter", "", "pq (fun i => i + b) n a",
     "From Stdlib Require Import Program.Wf.\nProgram Fixpoint pq (f : int -> int) (n : nat) (x : int) {measure n} : int :=\n  match n with O => x | S m => pq f m (f x) end.\n")
addA("fn_f_grows", "", "pq (fun i => i + b) a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then pq (fun i => f i + 1) (x - 1) else f 0.\nProof. all: intros; apply mu_pred; auto. Qed.\n")
addA("pf_f_grows", "", "pq (fun i => i + b) a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then pq (fun i => f i + 1) (x - 1) else f 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
# measures with a bound (step 58): written with the operations of nat and Z, on a counter and on machine numbers, a budget in phases above a counter's range
addA("pf_m_sub_machine", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x - mu 0)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); change (mu 0) with 0%nat; lia. Qed.\n")
addA("pf_m_min_machine", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Nat.min (mu x) (mu x))} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); lia. Qed.\n")
addA("pf_m_max_machine", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Nat.max (mu x) (mu x))} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); lia. Qed.\n")
addA("pf_m_div_machine", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x / 1)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); change (mu (x - 1) / 1 < mu x / 1)%nat; rewrite !Nat.div_1_r; lia. Qed.\n")
addA("pf_m_pred_machine", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Nat.pred (mu x + 1))} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); lia. Qed.\n")
addA("pf_m_plus_lit", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (mu x + 1)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); lia. Qed.\n")
addA("pf_m_two_times", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (2 * mu x)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); lia. Qed.\n")
addA("pf_m_z_plus", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Z.to_nat (Sint63.to_Z x + 1))} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); unfold mu in *; lia. Qed.\n")
addA("pf_m_z_sub", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Z.to_nat (Sint63.to_Z x - Sint63.to_Z 0))} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); change (Sint63.to_Z 0) with 0%Z; unfold mu in *; lia. Qed.\n")
addA("pf_m_own_def", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nDefinition mm (x : int) : nat := mu x + 1.\nProgram Fixpoint pq (x : int) {measure (mm x)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); unfold mm; lia. Qed.\n")
addA("pf_m_log2", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Nat.log2 (mu x) + mu x)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); pose proof (Nat.log2_le_mono (mu (x - 1)) (mu x) ltac:(lia)); lia. Qed.\n")
addA("pf_m_sqrt", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Nat.sqrt (mu x) + mu x)} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); pose proof (Nat.sqrt_le_mono (mu (x - 1)) (mu x) ltac:(lia)); lia. Qed.\n")
addA("pf_m_uint", "", "pq a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x : int) {measure (Z.to_nat (Sint63.to_Z x) + Z.to_nat (Uint63.to_Z 0))} : int :=\n  if dec (0 <? x) then x + pq (x - 1) else 0.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); change (Uint63.to_Z 0) with 0%Z; unfold mu in *; lia. Qed.\n")
addA("pf_m_hi_lo", "", "pq a b",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nLemma ltb_z : forall a b : int, (a <? b) = true -> (Sint63.to_Z a < Sint63.to_Z b)%Z.\nProof. intros a b H. apply Sint63.ltb_spec in H. exact H. Qed.\nLemma z_pred : forall x, (0 <? x) = true -> Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z.\nProof.\n  intros x H. apply ltb_z in H. change (Sint63.to_Z 0) with 0%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia.\nQed.\nProgram Fixpoint pq (lo hi : int) {measure (Z.to_nat (Sint63.to_Z hi - Sint63.to_Z lo))} : int :=\n  if dec (0 <? hi) then (if dec (lo <? hi) then hi + pq lo (hi - 1) else 0) else 0.\nNext Obligation.\n  assert (Z1 : (0 <? hi) = true) by auto. assert (Z2 : (lo <? hi) = true) by auto.\n  pose proof (z_pred hi Z1) as E. apply ltb_z in Z2. rewrite E. lia.\nQed.\n")
addA("pf_m_sub_counter", "", "pq O n a",
     "From Stdlib Require Import Program.Wf Lia.\nFrom Stdlib Require Import Program.Utils.\nProgram Fixpoint pq (i n : nat) (x : int) {measure (n - i)%nat} : int :=\n  if dec (Nat.ltb i n) then pq (S i) n (x + 1) else x.\nNext Obligation. pose proof (proj1 (Nat.ltb_lt i n) ltac:(auto)); lia. Qed.\n")
addA("fn_m_hi_lo", "", "pq (a, b)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nLemma ltb_z : forall a b : int, (a <? b) = true -> (Sint63.to_Z a < Sint63.to_Z b)%Z.\nProof. intros a b H. apply Sint63.ltb_spec in H. exact H. Qed.\nLemma z_pred : forall x, (0 <? x) = true -> Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z.\nProof.\n  intros x H. apply ltb_z in H. change (Sint63.to_Z 0) with 0%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia.\nQed.\nFunction pq (p : int * int) {measure (fun q => Z.to_nat (Sint63.to_Z (snd q) - Sint63.to_Z (fst q))) p} : int :=\n  let (lo, hi) := p in if 0 <? hi then (if lo <? hi then hi + pq (lo, hi - 1) else 0) else 0.\nProof.\n  intros; simpl. pose proof (z_pred hi teq0) as E. apply ltb_z in teq1. rewrite E. lia.\nDefined.\n")
addA("fn_m_sub_counter", "", "pq n O a",
     "From Stdlib Require Import Recdef Lia.\nFunction pq (n i : nat) (x : int) {measure (fun j => (n - j)%nat) i} : int :=\n  if Nat.ltb i n then pq n (S i) (x + 1) else x.\nProof. intros. apply Nat.ltb_lt in teq. lia. Defined.\n")
addA("fn_m_own_def", "", "pq a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nDefinition mm (x : int) : nat := mu x + 1.\nFunction pq (x : int) {measure mm x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. intros. unfold mm. pose proof (mu_pred x teq). lia. Defined.\n")
# Rocq's own measure recursion (step 57): Function, each sort
addA("fn_num", "", "pq a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure mu x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_tail", "", "pq a b",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x y : int) {measure mu x} : int :=\n  if 0 <? x then pq (x - 1) (y + x) else y.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_read", "", "pq a b s",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x y : int) (t : mem) {measure mu x} : int :=\n  if 0 <? x then pq (x - 1) (y + rd 0 x t) t else y.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_mem", "", "rd 0 0 (pq a s)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) (t : mem) {measure mu x} : mem :=\n  if 0 <? x then pq (x - 1) (upd 0 x x t) else t.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_write_num", "", "pq a s",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) (t : mem) {measure mu x} : int :=\n  if 0 <? x then pq (x - 1) (upd 0 x x t) + 1 else rd 0 0 t.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_bool", "", "if pq a then a else b",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure mu x} : bool :=\n  if 0 <? x then negb (pq (x - 1)) else true.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_record", "", "f1 (pq a)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure mu x} : r3 :=\n  if 0 <? x then let w := pq (x - 1) in mk3 (f1 w + x) (f2 w) 0 else mk3 0 0 0.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_pair_result", "", "fst (pq a s)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) (t : mem) {measure mu x} : int * mem :=\n  if 0 <? x then pq (x - 1) (upd 0 x x t) else (x, t).\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_nested", "", "pq a b",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x y : int) {measure mu x} : int :=\n  if 0 <? x then (if y <? x then pq (x - 1) y else x + pq (x - 1) (y - 1)) else y.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_let", "", "pq a b",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x y : int) {measure mu x} : int :=\n  if 0 <? x then (let z := y + x in pq (x - 1) z) else y.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_caller_fix", "", "kc n a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure mu x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Defined.\nFixpoint kc (n : nat) (x : int) : int := match n with O => pq x | S m => kc m (pq x) end.\n")
addA("fn_in_module", "", "Lib.pq a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nModule Lib.\nFunction pq (x : int) {measure mu x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Defined.\nEnd Lib.\n")
addA("fn_two", "", "pq a + pr b",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure mu x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Defined.\nFunction pr (x : int) {measure mu x} : int :=\n  if 0 <? x then pr (x - 1) + 1 else 0.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_given", "", "fold n a b (fun i acc => acc + pq i)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure mu x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_qed", "", "pq a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure mu x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. intros; apply mu_pred; auto. Qed.\n")
addA("fn_counter", "", "pq n a",
     "From Stdlib Require Import Recdef Lia.\nFunction pq (n : nat) (x : int) {measure (fun k => k) n} : int :=\n  match n with O => x | S m => pq m (x + 1) end.\nProof. intros; lia. Defined.\n")
addA("fn_pair_param", "", "pq (a, b)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (p : int * int) {measure (fun q => mu (fst q)) p} : int :=\n  let (x, y) := p in if 0 <? x then pq (x - 1, y + x) else y.\nProof. intros; simpl in *; subst; apply mu_pred; auto. Defined.\n")
addA("fn_option_param", "", "pq a (Some b)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) (o : option int) {measure mu x} : int :=\n  match o with\n  | Some v => if 0 <? x then pq (x - 1) (Some (v + x)) else v\n  | None => if 0 <? x then pq (x - 1) None else 0\n  end.\nProof. all: intros; apply mu_pred; auto. Defined.\n")
addA("fn_second", "", "pq a b",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (y x : int) {measure mu x} : int :=\n  if 0 <? x then pq (y + x) (x - 1) else y.\nProof. intros; apply mu_pred; auto. Defined.\n")
addA("fn_inline", "", "pq a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (x : int) {measure (fun v => Z.to_nat (Sint63.to_Z v)) x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. intros; apply mu_pred; auto. Defined.\n")
addA("fn_sum", "", "pq (a, b)",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (p : int * int) {measure (fun q => (mu (fst q) + mu (snd q))%nat) p} : int :=\n  let (x, y) := p in if 0 <? x then pq (x - 1, y) else if 0 <? y then pq (x, y - 1) else x + y.\nProof. all: intros; simpl; match goal with H : (0 <? ?v) = true |- _ => pose proof (mu_pred v H) end; lia. Defined.\n")
addA("fn_fun_param", "", "pq (fun i => i + b) a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFunction pq (f : int -> int) (x : int) {measure mu x} : int :=\n  if 0 <? x then f x + pq f (x - 1) else 0.\nProof. intros; apply mu_pred; auto. Defined.\n")
addA("fn_wf_rel", "", "pq a",
     "From Stdlib Require Import ZArith Lia Recdef.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nDefinition R (a b : int) : Prop := (mu a < mu b)%nat.\nLemma wfR : well_founded R. Proof. exact (Wf_nat.well_founded_ltof int mu). Qed.\nFunction pq (x : int) {wf R x} : int :=\n  if 0 <? x then x + pq (x - 1) else 0.\nProof. intros; apply mu_pred; auto. exact wfR. Defined.\n")
addA("fn_struct", "", "pq n a",
     "From Stdlib Require Import Recdef.\nFunction pq (n : nat) (x : int) {struct n} : int :=\n  match n with O => x | S m => pq m (x + 1) end.\n")
addA("fn_struct_mutual", "", "pq n a",
     "From Stdlib Require Import Recdef.\nFunction pq (n : nat) (x : int) {struct n} : int :=\n  match n with O => x | S m => pr m (x + 1) end\nwith pr (n : nat) (x : int) {struct n} : int :=\n  match n with O => x + 2 | S m => pq m (x + 3) end.\n")
addA("fn_nonrec", "", "pq a",
     "From Stdlib Require Import Recdef.\nFunction pq (x : int) : int := x + 1.\n")
addA("pf_fun_param", "", "pq (fun i => i + b) a",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (f : int -> int) (x : int) {measure (mu x)} : int :=\n  if dec (0 <? x) then f x + pq f (x - 1) else 0.\nNext Obligation. apply mu_pred; auto. Qed.\n")
addA("pf_sum_machine", "", "pq a b",
     "From Stdlib Require Import Program.Utils.\nFrom Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint pq (x y : int) {measure (mu x + mu y)} : int :=\n  if dec (0 <? x) then pq (x - 1) y else if dec (0 <? y) then pq x (y - 1) else x + y.\nNext Obligation. pose proof (mu_pred x ltac:(auto)); lia. Qed.\nNext Obligation. pose proof (mu_pred y ltac:(auto)); lia. Qed.\n")
addA("eq_num", "", "pq a",
     "From Stdlib Require Import ZArith Lia .\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) : int by wf (mu x) lt :=\n  pq x with inspect (0 <? x) => {\n    | true eqn: H => x + pq (x - 1)\n    | false eqn: _ => 0 }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
addA("eq_mem", "", "rd 0 0 (pq a s)",
     "From Stdlib Require Import ZArith Lia .\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nFrom Equations Require Import Equations.\nDefinition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.\nNotation \"x 'eqn:' p\" := (exist _ x p) (only parsing, at level 20).\nEquations pq (x : int) (t : mem) : mem by wf (mu x) lt :=\n  pq x t with inspect (0 <? x) => {\n    | true eqn: H => pq (x - 1) (upd 0 x x t)\n    | false eqn: _ => t }.\nNext Obligation. apply mu_pred. auto. Qed.\n")
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
# a counter as a number, a number as a counter, times a written number, div, mod, even, odd (step 70)
addA('c2_of_arg', "", 'ff n (Uint63.of_Z (Z.of_nat n))',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_of_nat_notation', "", 'a + Uint63.of_nat n',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_op', "", 'Uint63.of_Z (Z.of_nat n) * a + b',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_let', "", 'let v := Uint63.of_Z (Z.of_nat n) in v + v',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_rd', "", 'rd 0 (Uint63.of_Z (Z.of_nat n)) s',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_upd', "", 'rd 0 a (upd 0 (Uint63.of_Z (Z.of_nat n)) (Uint63.of_Z (Z.of_nat n)) s)',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_test', "", 'if Uint63.of_Z (Z.of_nat n) <? a then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_pred', "", 'match n with O => a | S m => Uint63.of_Z (Z.of_nat m) end',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_S', "", 'Uint63.of_Z (Z.of_nat (S n))',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_add', "", 'Uint63.of_Z (Z.of_nat (n + 2))',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_pair', "", 'fst (Uint63.of_Z (Z.of_nat n), a) + snd (b, Uint63.of_Z (Z.of_nat n))',
     'From Stdlib Require Import ZArith.\n')
addA('c2_of_loop', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat j)) end.\n')
addA('c2_of_loop_mem', "", 'rd 0 a (lp n s)',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (t : mem) : mem := match k with O => t | S j => lp j (upd 0 (Uint63.of_Z (Z.of_nat j)) (Uint63.of_Z (Z.of_nat k)) t) end.\n')
addA('c2_of_nontail', "", 'lp n',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) : int := match k with O => 0 | S j => Uint63.of_Z (Z.of_nat k) + lp j end.\n')
addA('c2_of_helper', "", 'tw n + a',
     'From Stdlib Require Import ZArith.\nDefinition tw (k : nat) : int := Uint63.of_Z (Z.of_nat k) * 2.\n')
addA('c2_of_field', "", 'f1 (mk3 (Uint63.of_Z (Z.of_nat n)) a b)',
     'From Stdlib Require Import ZArith.\n')
addA('c2_lit_pos', "", 'Uint63.of_Z 5 + a',
     'From Stdlib Require Import ZArith.\nOpen Scope Z_scope.\n')
addA('c2_lit_zero', "", 'Uint63.of_Z 0 + a',
     'From Stdlib Require Import ZArith.\nOpen Scope Z_scope.\n')
addA('c2_lit_neg', "", 'Uint63.of_Z (-3) + a',
     'From Stdlib Require Import ZArith.\nOpen Scope Z_scope.\n')
addA('c2_lit_big', "", 'Uint63.of_Z 1000000007 + a',
     'From Stdlib Require Import ZArith.\nOpen Scope Z_scope.\n')
addA('c2_lit_helper', "", 'base + a',
     'From Stdlib Require Import ZArith.\nDefinition base : int := Uint63.of_Z 7%Z.\n')
addA('c2_to_arg', "", 'ff (Z.to_nat (Sint63.to_Z a)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_arg_u', "", 'ff (Z.to_nat (Uint63.to_Z a)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_arg_notation', "", 'ff (Uint63.to_nat a) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_test', "", 'if Nat.ltb (Z.to_nat (Sint63.to_Z a)) 3 then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('c2_to_test_u', "", 'if Nat.eqb (Uint63.to_nat a) 3 then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('c2_to_let', "", 'let k := Z.to_nat (Sint63.to_Z a) in ff k b + ff k a',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_let_u', "", 'let k := Uint63.to_nat a in if Nat.ltb k 2 then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('c2_to_match', "", 'match Z.to_nat (Sint63.to_Z a) with O => b | S j => ff j b end',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_match_u', "", 'match Uint63.to_nat a with O => b | S j => a end',
     'From Stdlib Require Import ZArith.\n')
addA('c2_to_of', "", 'Uint63.of_Z (Z.of_nat (Z.to_nat (Sint63.to_Z a)))',
     'From Stdlib Require Import ZArith.\n')
addA('c2_to_of_u', "", 'Uint63.of_nat (Uint63.to_nat a)',
     'From Stdlib Require Import ZArith.\n')
addA('c2_to_loop', "", 'lp (Z.to_nat (Sint63.to_Z a)) b',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + 1) end.\n')
addA('c2_to_min', "", 'ff (Nat.min (Z.to_nat (Sint63.to_Z a)) n) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_min_u', "", 'ff (Nat.min (Uint63.to_nat a) n) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_add', "", 'ff (Z.to_nat (Sint63.to_Z a) + n) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_inner', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (ff (Z.to_nat (Sint63.to_Z x)) x) end.\n')
addA('c2_mul_l', "", 'ff (Nat.mul 2 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_r', "", 'ff (Nat.mul n 2) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_star', "", 'ff (2 * n)%nat a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_star_r', "", 'ff (n * 3)%nat a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_zero_l', "", 'ff (Nat.mul 0 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_zero_r', "", 'ff (Nat.mul n 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_one', "", 'ff (Nat.mul 1 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_test', "", 'if Nat.ltb (Nat.mul 3 n) 7 then a else b',
     '')
addA('c2_mul_let', "", 'let k := Nat.mul 2 n in ff k a + ff k b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_nest', "", 'ff (Nat.mul 2 (S n + 1)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_nest2', "", 'ff (Nat.mul 2 (Nat.mul 3 n)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_of', "", 'Uint63.of_Z (Z.of_nat (Nat.mul 4 n))',
     'From Stdlib Require Import ZArith.\n')
addA('c2_mul_rec', "", 'lp n a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (ff (Nat.mul 2 j) x) end.\n')
addA('c2_mul_vars_control', "", 'ff (Nat.mul 2 n + n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mul_vars', "", 'ff (Nat.mul n n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_div_arg', "", 'ff (Nat.div n 3) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_div_slash', "", 'ff (n / 2)%nat a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mod_arg', "", 'ff (Nat.modulo n 3) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mod_percent', "", 'ff (Nat.modulo (S n) 5) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_div_zero', "", 'ff (Nat.div n 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mod_zero', "", 'ff (Nat.modulo n 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_div_var', "", 'ff (Nat.div n (S n)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mod_test', "", 'if Nat.eqb (Nat.modulo n 2) 0 then a else b',
     '')
addA('c2_div_let', "", 'let k := Nat.div n 2 in ff k a + ff k b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_div_match', "", 'match Nat.div n 2 with O => a | S q => ff q b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_mod_match', "", 'match Nat.modulo n 2 with O => a | S _ => b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_div_rec', "", 'lp n a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (ff (Nat.modulo j 4) x) end.\n')
addA('c2_div_of', "", 'Uint63.of_Z (Z.of_nat (Nat.div n 7))',
     'From Stdlib Require Import ZArith.\n')
addA('c2_even_if', "", 'if Nat.even n then a else b',
     '')
addA('c2_odd_if', "", 'if Nat.odd n then a else b',
     '')
addA('c2_even_let', "", 'let e := Nat.even n in if e then a else b',
     '')
addA('c2_even_and', "", 'if Nat.even n && (a <? b) then a else b',
     '')
addA('c2_even_or', "", 'if orb (a <? b) (Nat.odd n) then a else b',
     '')
addA('c2_even_not', "", 'if negb (Nat.even n) then a else b',
     '')
addA('c2_even_val', "", 'kb (Nat.even n) a',
     'Definition kb (c : bool) (x : int) : int := if c then x else x + 1.\n')
addA('c2_odd_val', "", 'kb (Nat.odd n) a',
     'Definition kb (c : bool) (x : int) : int := if c then x else x + 1.\n')
addA('c2_even_ret', "", 'if ev n then a else b',
     'Definition ev (k : nat) : bool := Nat.even (S k).\n')
addA('c2_even_tail', "", 'lp n a',
     'Fixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => if Nat.even j then lp j (x + 1) else lp j x end.\n')
addA('c2_even_nontail', "", 'lp n',
     'Fixpoint lp (k : nat) : int := match k with O => 0 | S j => (if Nat.odd k then 1 else 2) + lp j end.\n')
addA('c2_even_mem', "", 'rd 0 a (lp n a b s)',
     'Fixpoint lp (k : nat) (x y : int) (t : mem) : mem := match k with O => t | S j => lp j x y (if Nat.even j then upd 0 x y t else t) end.\n')
addA('c2_even_add', "", 'if Nat.even (n + n) then a else b',
     '')
addA('c2_even_div2', "", 'if Nat.even (Nat.div2 n) then a else b',
     '')
addA('c2_even_of', "", 'if Nat.even (Uint63.to_nat a) then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('c2_even_loop', "", 'ev n a',
     'Fixpoint ev (k : nat) (x : int) : int := if Nat.even k then x else match k with O => x | S j => ev j (x + 1) end.\n')
addA('c2_even_field', "", 'if fst (Nat.even n, a) then a else b',
     '')
addA('c2_ar_min', "", 'ff (Nat.min n 3) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_max', "", 'ff (Nat.max n 3) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_sub', "", 'ff (Nat.sub n 3) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_div2', "", 'ff (Nat.div2 n) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_mul', "", 'ff (Nat.mul 2 n) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_div', "", 'ff (Nat.div n 2) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_mod', "", 'ff (Nat.modulo n 2) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_add', "", 'ff (Nat.add n 2) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_pred', "", 'ff (Nat.pred n) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_ar_eqb', "", 'if Nat.eqb n 2 then a else b',
     'From Stdlib Require Import Arith.\n')
addA('c2_ar_ltb', "", 'if Nat.ltb n 2 then a else b',
     'From Stdlib Require Import Arith.\n')
addA('c2_ar_leb', "", 'if Nat.leb n 2 then a else b',
     'From Stdlib Require Import Arith.\n')
addA('c2_ar_even', "", 'if Nat.even n then a else b',
     'From Stdlib Require Import Arith.\n')
addA('c2_ar_odd', "", 'if Nat.odd n then a else b',
     'From Stdlib Require Import Arith.\n')
addA('c2_ar_rec', "", 'lp n a',
     'From Stdlib Require Import Arith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => if Nat.even (Nat.min j 3) then lp j (x + 1) else lp j x end.\n')
addA('c2_mul_big', "", 'ff (Nat.mul 1000 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_to_add_u', "", 'ff (Uint63.to_nat a + n) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_choice', "", 'ff (if a <? b then n else 3) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_choice_let', "", 'let k : nat := if a <? b then n else 3%nat in ff k a + ff k b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_choice_rec', "", 'lp n n a',
     'Fixpoint lp (k m : nat) (x : int) : int := match k with O => x | S j => lp j (if x <? 3 then m else 2) (x + 1) end.\n')
addA('c2_choice_nest', "", 'ff (Nat.min (if a <? b then n else 3) (if b <? a then 1 else n)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_match_cnt', "", 'ff (match n with O => 1 | S m => m end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_choice_test', "", 'if Nat.ltb (if a <? b then n else 3) 2 then a else b',
     '')
addA('c2_choice_of', "", 'Uint63.of_Z (Z.of_nat (if a <? b then n else 3))',
     'From Stdlib Require Import ZArith.\n')
addA('c2_nat_pow_lit', "", 'ff (Nat.pow 2 3) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_min_clamp', "", 'ff (Nat.mul 3 (Nat.min (Uint63.to_nat a) 1000)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_double', "", 'ff (Nat.double n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_succ', "", 'ff (Nat.succ n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_b2n', "", 'ff (Nat.b2n (a <? b)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_square', "", 'ff (Nat.square n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_pow', "", 'ff (Nat.pow 2 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_log2', "", 'ff (Nat.log2 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_sqrt', "", 'ff (Nat.sqrt n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_gcd', "", 'ff (Nat.gcd n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_land', "", 'ff (Nat.land n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_shiftr', "", 'ff (Nat.shiftr n 1) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('c2_nat_testbit', "", 'if Nat.testbit n 1 then a else b',
     '')

# programs written as one writes Rocq, with no thought of the reader: a third probe (step 71)
addA('q_mon_seq', "", 'fst ((x <- rdm 0 a ;; y <- rdm 0 b ;; ret (x + y)) s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\n')
addA('q_mon_write', "", 'fst ((x <- rdm 0 a ;; _ <- wrm 0 b x ;; y <- rdm 0 b ;; ret (x + y)) s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\n')
addA('q_mon_def', "", 'fst (prog a b s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition prog (i j : int) : M int := x <- rdm 0 i ;; _ <- wrm 0 j (x + 1) ;; rdm 0 j.\n')
addA('q_mon_if', "", 'fst (prog a b s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition prog (i j : int) : M int := x <- rdm 0 i ;; if x <? j then ret x else (_ <- wrm 0 i j ;; ret j).\n')
addA('q_mon_rec', "", 'fst (loop n a s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint loop (k : nat) (i : int) : M int := match k with O => ret i | S m => _ <- wrm 0 i i ;; loop m (i + 1) end.\n')
addA('q_mon_rec_nontail', "", 'fst (loop n a s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint loop (k : nat) (i : int) : M int := match k with O => ret 0 | S m => x <- rdm 0 i ;; r <- loop m (i + 1) ;; ret (x + r) end.\n')
addA('q_mon_mem', "", 'rd 0 a (snd (loop n a s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint loop (k : nat) (i : int) : M unit := match k with O => ret tt | S m => _ <- wrm 0 i i ;; loop m (i + 1) end.\n')
addA('q_mon_two', "", 'fst (p2 a s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition p1 (i : int) : M int := x <- rdm 0 i ;; ret (x + 1).\nDefinition p2 (i : int) : M int := y <- p1 i ;; z <- p1 (i + 1) ;; ret (y * z).\n')
addA('q_st_tuple', "", 'fst (iter n (a, b))',
     'Definition step (st : int * int) : int * int := let (x, y) := st in (y, x + y).\nFixpoint iter (k : nat) (st : int * int) : int * int := match k with O => st | S m => iter m (step st) end.\n')
addA('q_st_iter', "", 'fst (Nat.iter n step (a, b))',
     'Definition step (st : int * int) : int * int := let (x, y) := st in (y, x + y).\n')
addA('q_st_mem_iter', "", 'rd 0 a (snd (Nat.iter n step (a, s)))',
     'Definition step (st : int * mem) : int * mem := let (i, t) := st in (i + 1, upd 0 i i t).\n')
addA('q_sm_step', "", 'out (step (step Idle a) b)',
     'Inductive state := Idle | Busy (x : int) | Done (x y : int).\nDefinition step (st : state) (v : int) : state := match st with Idle => Busy v | Busy x => Done x v | Done x y => Idle end.\nDefinition out (st : state) : int := match st with Idle => 0 | Busy x => x | Done x y => x + y end.\n')
addA('q_sm_run', "", 'out (run n Idle a s)',
     'Inductive state := Idle | Busy (x : int) | Done (x y : int).\nDefinition step (st : state) (v : int) : state := match st with Idle => Busy v | Busy x => Done x v | Done x y => Idle end.\nDefinition out (st : state) : int := match st with Idle => 0 | Busy x => x | Done x y => x + y end.\nFixpoint run (k : nat) (st : state) (i : int) (t : mem) : state := match k with O => st | S m => run m (step st (rd 0 i t)) (i + 1) t end.\n')
addA('q_sm_eq', "", 'if isidle (Busy a) then a else b',
     'Inductive state := Idle | Busy (x : int) | Done (x y : int).\nDefinition isidle (st : state) : bool := match st with Idle => true | _ => false end.\n')
addA('q_enum_scheme', "", 'if color_beq (if a <? b then Red else Green) Blue then a else b',
     'Inductive color := Red | Green | Blue.\nScheme Equality for color.\n')
addA('q_enum_dec', "", 'if color_eq_dec (if a <? b then Red else Green) Blue then a else b',
     'Inductive color := Red | Green | Blue.\nScheme Equality for color.\n')
addA('q_enum_many', "", 'val (next (if a <? b then D2 else D7))',
     'Inductive d := D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7.\nDefinition next (x : d) : d := match x with D0 => D1 | D1 => D2 | D2 => D3 | D3 => D4 | D4 => D5 | D5 => D6 | D6 => D7 | D7 => D0 end.\nDefinition val (x : d) : int := match x with D0 | D1 | D2 => 1 | D3 => 2 | _ => 3 end.\n')
addA('q_enum_rec', "", 'go2 n D0 a',
     'Inductive d := D0 | D1 | D2.\nDefinition next (x : d) : d := match x with D0 => D1 | D1 => D2 | D2 => D0 end.\nFixpoint go2 (k : nat) (x : d) (v : int) : int := match k with O => v | S m => go2 m (next x) (match x with D0 => v + 1 | D1 => v * 2 | D2 => v - 1 end) end.\n')
addA('q_pat_pair_opt', "", 'match (if a <? b then Some a else None), a <? 3 with Some x, true => x | Some x, false => x + 1 | None, _ => b end',
     '')
addA('q_pat_bools', "", 'match a <? b, b <? a with true, _ => a | _, true => b | _, _ => 0 end',
     '')
addA('q_pat_nat_deep', "", 'match n with 0 => a | 1 => b | 2 => a + b | _ => a - b end',
     '')
addA('q_pat_triple', "", "let '(p, q, r) := t3 a in p * q + r",
     'Definition t3 (x : int) : int * int * int := (x, x + 1, x + 2).\n')
addA('q_pat_nest_rec', "", "let '(mk2 u v, w) := (mk2 a b, a) in u + v + w",
     'Record r2 := mk2 { x2 : int; y2 : int }.\n')
addA('q_pat_or', "", 'match a <? b, n with true, O | false, S _ => a | _, _ => b end',
     '')
addA('q_rec_update', "", 'px (mv (mkpt a b) 1) + py (mv (mkpt a b) 2)',
     'Record pt := mkpt { px : int; py : int }.\nDefinition mv (p : pt) (d : int) : pt := {| px := px p + d; py := py p |}.\n')
addA('q_rec_nested', "", 'len (mkseg (mkpt a b) (mkpt b a))',
     'Record pt := mkpt { px : int; py : int }.\nRecord seg := mkseg { p1 : pt; p2 : pt }.\nDefinition len (q : seg) : int := px (p2 q) - px (p1 q).\n')
addA('q_rec_nested_rec', "", 'px (p1 (gr n (mkseg (mkpt a b) (mkpt b a))))',
     'Record pt := mkpt { px : int; py : int }.\nRecord seg := mkseg { p1 : pt; p2 : pt }.\nFixpoint gr (k : nat) (q : seg) : seg := match k with O => q | S m => gr m (mkseg (p2 q) (mkpt (px (p1 q) + 1) (py (p2 q)))) end.\n')
addA('q_rec_vtable', "", 'op2 myops (op1 myops a) b',
     'Record ops := mkops { op1 : int -> int; op2 : int -> int -> int }.\nDefinition myops : ops := mkops (fun x => x + 1) (fun x y => x * y).\n')
addA('q_rec_vtable_param', "", 'use myops a',
     'Record ops := mkops { op1 : int -> int; op2 : int -> int -> int }.\nDefinition use (o : ops) (x : int) : int := op2 o (op1 o x) x.\nDefinition myops : ops := mkops (fun x => x + 1) (fun x y => x * y).\n')
addA('q_rec_vtable_rec', "", 'use n (mkops (fun x => x + b)) a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\n')
addA('q_rec_prim', "", 'pa (sw (mkpp a b))',
     'Set Primitive Projections.\nRecord pp := mkpp { pa : int; pb : int }.\nUnset Primitive Projections.\nDefinition sw (p : pp) : pp := mkpp (pb p) (pa p).\n')
addA('q_rec_prim_rec', "", 'pa (sw n (mkpp a b))',
     'Set Primitive Projections.\nRecord pp := mkpp { pa : int; pb : int }.\nUnset Primitive Projections.\nFixpoint sw (k : nat) (p : pp) : pp := match k with O => p | S m => sw m (mkpp (pb p) (pa p)) end.\n')
addA('q_rec_param_type', "", 'unbox (mkbox (a + b))',
     'Record box (T : Type) := mkbox { unbox : T }.\nArguments mkbox {T}.\nArguments unbox {T}.\n')
addA('q_rec_param_rec', "", 'unbox (f n (mkbox a))',
     'Record box (T : Type) := mkbox { unbox : T }.\nArguments mkbox {T}.\nArguments unbox {T}.\nFixpoint f (k : nat) (x : box int) : box int := match k with O => x | S m => f m (mkbox (unbox x + 1)) end.\n')
addA('q_fn_partial', "", 'let g := add a in g b + g 1',
     'Definition add (x y : int) : int := x + y.\n')
addA('q_fn_compose', "", 'comp (fun x => x + 1) (comp (fun x => x * 2) (fun x => x - a)) b',
     'Definition comp (f g : int -> int) (x : int) : int := f (g x).\n')
addA('q_fn_returned', "", 'mk a b + mk b a',
     'Definition mk (d : int) : int -> int := fun x => x + d.\n')
addA('q_fn_returned_if', "", 'mk (a <? b) a',
     'Definition mk (c : bool) : int -> int := if c then (fun x => x + 1) else (fun x => x * 2).\n')
addA('q_fn_pair', "", 'let fg := (fun x : int => x + 1, fun x : int => x * 2) in fst fg a + snd fg b',
     '')
addA('q_fn_flip', "", 'flip PrimInt63.sub a b',
     'Definition flip {A B C : Type} (f : A -> B -> C) (y : B) (x : A) : C := f x y.\n')
addA('q_fn_const_id', "", 'idf (cst a b) + cst (idf b) true',
     'Definition idf {A : Type} (x : A) : A := x.\nDefinition cst {A B : Type} (x : A) (_ : B) : A := x.\n')
addA('q_fn_prim', "", 'PrimInt63.add a b + (if PrimInt63.ltb a b then 1 else 0)',
     '')
addA('q_fn_op_given', "", 'foldg n PrimInt63.add a b + foldg n PrimInt63.mul a b',
     'Fixpoint foldg (k : nat) (f : int -> int -> int) (acc i : int) : int := match k with O => acc | S m => foldg m f (f acc i) (i + 1) end.\n')
addA('q_cl_monoid', "", '@sum3 int add_m a b a + @sum3 int mul_m a b a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\nInstance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nInstance mul_m : Monoid int := { unit' := 1; op := PrimInt63.mul }.\nDefinition sum3 {T} `{Monoid T} (x y z : T) : T := op x (op y (op z unit')).\n")
addA('q_cl_fold', "", 'rep n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\nInstance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\n")
addA('q_cl_eqb', "", 'if same a b && same (a <? 1) (b <? 1) then a else b',
     "Class Eqb (T : Type) := { eqb' : T -> T -> bool }.\nInstance eq_int : Eqb int := { eqb' := PrimInt63.eqb }.\nInstance eq_bool : Eqb bool := { eqb' := Bool.eqb }.\nDefinition same {T} `{Eqb T} (x y : T) : bool := eqb' x y.\n")
addA('q_cl_coerce', "", '((a <? b) : int) + 1',
     "Definition b2i' (c : bool) : int := if c then 1 else 0.\nCoercion b2i' : bool >-> int.\n")
addA('q_univ_poly', "", 'pid a + pid b',
     'Polymorphic Definition pid {A : Type} (x : A) : A := x.\n')
addA('q_univ_poly_rec', "", 'prep n a',
     'Polymorphic Fixpoint prep {A : Type} (k : nat) (x : A) : A := match k with O => x | S m => prep m x end.\n')
addA('q_def_tactic', "", 'f a',
     'Definition f (x : int) : int. Proof. exact (x + 1). Defined.\n')
addA('q_def_refine', "", 'snd (f a)',
     'Definition f (x : int) : int * int. Proof. refine (x, _). exact (x + 2). Defined.\n')
addA('q_def_destruct', "", 'f (a <? b) a',
     'Definition f (c : bool) (x : int) : int. Proof. destruct c. exact x. exact (x + 1). Defined.\n')
addA('q_def_induct', "", 'f n a',
     'Definition f (k : nat) (x : int) : int. Proof. induction k as [|m IH]. exact x. exact (IH + 1). Defined.\n')
addA('q_sec_var', "", 'lp b n a',
     'Section S.\nVariable d : int.\nDefinition add_d (x : int) : int := x + d.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S m => lp m (add_d x) end.\nEnd S.\n')
addA('q_sec_ctx', "", 'lp (fun x => x + b) n a',
     'Section S.\nContext {T : Type} (f : T -> T).\nFixpoint lp (k : nat) (x : T) : T := match k with O => x | S m => lp m (f x) end.\nEnd S.\n')
addA('q_impl_types', "", 'mx a b',
     'Implicit Types x y : int.\nDefinition mx x y := if x <? y then y else x.\n')
addA('q_sig_param', "", 'val (exist _ 1 one_pos) + a',
     'Definition pos_int := { x : int | (0 <? x) = true }.\nDefinition val (p : pos_int) : int := proj1_sig p.\nLemma one_pos : (0 <? 1) = true. Proof. reflexivity. Qed.\n')
addA('q_sig_ret', "", 'proj1_sig (clamp a)',
     'Definition clamp (x : int) : { y : int | (y <? 0) = false \\/ True }.\nProof. exists (if x <? 0 then 0 else x). right. exact I. Defined.\n')
addA('q_sig_rec', "", 'proj1_sig (lp n a)',
     'Fixpoint lp (k : nat) (x : int) : { y : int | True } := match k with O => exist _ x I | S m => lp m (x + 1) end.\n')
addA('q_proof_arg', "", 'sdiv a 2 two_nz',
     'Definition sdiv (x y : int) (h : (y =? 0) = false) : int := x / y.\nLemma two_nz : (2 =? 0) = false. Proof. reflexivity. Qed.\n')
addA('q_sumbool_ret', "", "if lt_dec' a b then a else b",
     "Definition lt_dec' (x y : int) : {(x <? y) = true} + {(x <? y) = false}.\nProof. destruct (x <? y); [left | right]; reflexivity. Defined.\n")
addA('q_option_bind', "", 'match obind (safe a b) (fun v => safe v 2) with Some r => r | None => 0 end',
     'Definition obind {A B} (o : option A) (f : A -> option B) : option B := match o with Some x => f x | None => None end.\nDefinition safe (x y : int) : option int := if y =? 0 then None else Some (x / y).\n')
addA('q_option_rec', "", 'match find n a s with Some i => i | None => b end',
     'Fixpoint find (k : nat) (i : int) (t : mem) : option int := match k with O => None | S m => if rd 0 i t =? 7 then Some i else find m (i + 1) t end.\n')
addA('q_option_default', "", 'odflt a (if a <? b then Some b else None)',
     'Definition odflt (d : int) (o : option int) : int := match o with Some x => x | None => d end.\n')
addA('q_sum_result', "", 'match thn (chk a) (fun v => chk (v - b)) with Ok v => v | Err c => c end',
     'Inductive res := Ok (v : int) | Err (code : int).\nDefinition chk (x : int) : res := if x <? 0 then Err 1 else Ok x.\nDefinition thn (r : res) (f : int -> res) : res := match r with Ok v => f v | Err c => Err c end.\n')
addA('q_sum_result_rec', "", 'match lp n a s with Ok v => v | Err c => c end',
     'Inductive res := Ok (v : int) | Err (code : int).\nFixpoint lp (k : nat) (x : int) (t : mem) : res := match k with O => Ok x | S m => if rd 0 x t <? 0 then Err x else lp m (x + 1) t end.\n')
addA('q_list_fold', "", 'fold_left (fun acc x => acc + x) [a; b; 1] 0',
     'From Stdlib Require Import List.\nImport ListNotations.\n')
addA('q_list_table', "", 'fold_left (fun acc x => acc * x) tbl a',
     'From Stdlib Require Import List.\nImport ListNotations.\nDefinition tbl : list int := [1; 2; 3; 4].\n')
addA('q_list_rec_given', "", 'sum [a; b] 0',
     'From Stdlib Require Import List.\nImport ListNotations.\nFixpoint sum (l : list int) (acc : int) : int := match l with [] => acc | x :: r => sum r (acc + x) end.\n')
addA('q_list_map2', "", 'fold_right PrimInt63.add 0 (map (fun x => x * 2) [a; b])',
     'From Stdlib Require Import List.\nImport ListNotations.\n')
addA('q_tree_lit', "", 'sumt (Node (Leaf a) (Node (Leaf b) (Leaf 1)))',
     'Inductive tree := Leaf (x : int) | Node (l r : tree).\nFixpoint sumt (t : tree) : int := match t with Leaf x => x | Node l r => sumt l + sumt r end.\n')
addA('q_string_lit', "", 'slen "abc"%string + a',
     'From Stdlib Require Import String.\nFixpoint slen (x : string) : int := match x with EmptyString => 0 | String _ r => 1 + slen r end.\n')
addA('q_ascii_code', "", 'Uint63.of_nat (nat_of_ascii "a"%char) + a',
     'From Stdlib Require Import Ascii.\n')
addA('q_byte_lit', "", 'bv x41 + a',
     'From Stdlib Require Import Strings.Byte.\nDefinition bv (x : byte) : int := match x with x41 => 1 | _ => 0 end.\n')
addA('q_parray_get', "", 'PArray.get (PArray.make 3 a) 0 + b',
     'From Stdlib Require Import PArray.\n')
addA('q_float_lit', "", 'if PrimFloat.ltb 1.0%float 2.0%float then a else b',
     'From Stdlib Require Import Floats.\n')
addA('q_op_notations', "", '((a + b) * (a - b)) / 2 + (a mod 3)',
     '')
addA('q_op_bits', "", '((a land b) lor (a lxor 7)) << 1 >> 1',
     '')
addA('q_op_opp', "", '- a + Uint63.opp b',
     '')
addA('q_op_lnot', "", 'PrimInt63.lxor a (-1) + 1',
     '')
addA('q_op_succ', "", 'Uint63.succ a + Uint63.pred b',
     '')
addA('q_op_max_int', "", 'if a =? Uint63.max_int then b else a',
     '')
addA('q_op_bit', "", 'if Uint63.bit a 3 then a else b',
     '')
addA('q_op_b2i', "", 'Uint63.b2i (a <? b) + 1',
     '')
addA('q_op_sint_cmp', "", 'if Sint63.ltb a b then a else if Sint63.leb b a then b else 0',
     '')
addA('q_op_sint_div', "", 'Sint63.div a 2 + Sint63.rem b 3',
     '')
addA('q_op_sint_abs', "", 'Sint63.abs a + Sint63.asr b 1',
     '')
addA('q_op_sint_scope', "", '((a * b) / 2)%sint63',
     '')
addA('q_op_uint_scope', "", '((a * b) / 2)%uint63',
     '')
addA('q_op_eqb_sym', "", 'if andb (a =? b) (negb (b =? a)) then a else b',
     '')
addA('q_op_cast_int', "", '((a + b : int) * 2)%uint63',
     '')
addA('q_op_lit_hex', "", '(0x10 + a)%uint63',
     '')
addA('q_mem_helper_chain', "", 'rd 0 a (inc a (inc b (inc a s)))',
     'Definition put (i v : int) (t : mem) : mem := upd 0 i v t.\nDefinition inc (i : int) (t : mem) : mem := put i (rd 0 i t + 1) t.\n')
addA('q_mem_fun_comp', "", 'rd 0 a (seq (put a 1) (put b 2) s)',
     'Definition put (i v : int) (t : mem) : mem := upd 0 i v t.\nDefinition seq (f g : mem -> mem) (t : mem) : mem := g (f t).\n')
addA('q_mem_iter', "", 'rd 0 a (Nat.iter n (upd 0 a b) s)',
     '')
addA('q_mem_fold_given', "", 'rd 0 a (each n a (fun i t => upd 0 i (rd 0 i t + b) t) s)',
     'Fixpoint each (k : nat) (i : int) (f : int -> mem -> mem) (t : mem) : mem := match k with O => t | S m => each m (i + 1) f (f i t) end.\n')
addA('q_mem_block_tbl', "", 'rdt a s + rdt b s',
     'Definition tb : int := 2.\nDefinition rdt (i : int) (t : mem) : int := rd tb i t.\n')
addA('q_mem_ret_triple', "", "let '(u, v, t2) := rw a s in u + v + rd 0 v t2",
     'Definition rw (i : int) (t : mem) : int * int * mem := (rd 0 i t, i + 1, upd 0 i 0 t).\n')
addA('q_mem_rec_triple', "", "let '(u, v, t2) := rw n a s in u + v + rd 0 a t2",
     "Fixpoint rw (k : nat) (i : int) (t : mem) : int * int * mem := match k with O => (i, 0, t) | S m => let '(u, v, t2) := rw m (i + 1) (upd 0 i i t) in (u, v + 1, t2) end.\n")
addA('q_mem_opt_ret', "", 'let (o, t2) := tk a s in match o with Some v => v + rd 0 a t2 | None => b end',
     'Definition tk (i : int) (t : mem) : option int * mem := if rd 0 i t =? 0 then (None, t) else (Some (rd 0 i t), upd 0 i 0 t).\n')
addA('q_mem_record', "", 'rd 0 a (mm (lp n (mkst a s)))',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\n')
addA('q_prim_rec_num', "", 'f n (mkpp a b)',
     'Set Primitive Projections.\nRecord pp := mkpp { pa : int; pb : int }.\nUnset Primitive Projections.\nFixpoint f (k : nat) (p : pp) : int := match k with O => pa p | S m => f m (mkpp (pb p) (pa p)) end.\n')
addA('q_prim_ret', "", 'pa (f a) + pb (f b)',
     'Set Primitive Projections.\nRecord pp := mkpp { pa : int; pb : int }.\nUnset Primitive Projections.\nDefinition f (x : int) : pp := mkpp x (x + 1).\n')
addA('q_prim_ret_rec', "", 'pa (f n a)',
     'Set Primitive Projections.\nRecord pp := mkpp { pa : int; pb : int }.\nUnset Primitive Projections.\nFixpoint f (k : nat) (x : int) : pp := match k with O => mkpp x x | S m => f m (x + 1) end.\n')
addA('q_prim_nontail', "", 'let v := f n a in pa v + pb v',
     'Set Primitive Projections.\nRecord pp := mkpp { pa : int; pb : int }.\nUnset Primitive Projections.\nFixpoint f (k : nat) (x : int) : pp := match k with O => mkpp x x | S m => let r := f m (x + 1) in mkpp (pb r) (pa r + 1) end.\n')
addA('q_prim_nest', "", 'h2 (mkpp a b)',
     'Set Primitive Projections.\nRecord pp := mkpp { pa : int; pb : int }.\nUnset Primitive Projections.\nDefinition sw (p : pp) : pp := mkpp (pb p) (pa p).\nDefinition h2 (p : pp) : int := pa (sw (sw p)).\n')
addA('q_nat_ret_len', "", 'Uint63.of_nat (cnt n a s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => 0 | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('q_nat_ret_acc', "", 'Uint63.of_nat (cnt n a 0)',
     'Fixpoint cnt (k : nat) (i : int) (acc : nat) : nat := match k with O => acc | S m => cnt m (i + 1) (if i =? 0 then acc else S acc) end.\n')
addA('q_nat_field', "", 'Uint63.of_nat (ct (bump (mkcn n a)))',
     'Record cn := mkcn { ct : nat; vl : int }.\nDefinition bump (c : cn) : cn := mkcn (S (ct c)) (vl c).\n')
addA('q_nat_pair_ret', "", 'let (q, r) := sp n in if Nat.eqb r 0 then a else Uint63.of_nat q',
     'Definition sp (k : nat) : nat * nat := (Nat.div k 2, Nat.modulo k 2).\n')
addA('q_divmod', "", 'Uint63.of_nat (fst (Nat.divmod n 3 0 3))',
     '')

# the integer types of C (step 88)
addA('zg_u8_of', "", 'u8_of a',
     '')
addA('zg_u8_add', "", 'u8_add (u8_of a) (u8_of b)',
     '')
addA('zg_u8_sub', "", 'u8_sub (u8_of a) (u8_of b)',
     '')
addA('zg_u8_mul', "", 'u8_mul (u8_of a) (u8_of b)',
     '')
addA('zg_u8_div', "", 'u8_div (u8_of a) (u8_of b)',
     '')
addA('zg_u8_mod', "", 'u8_mod (u8_of a) (u8_of b)',
     '')
addA('zg_u8_and', "", 'u8_and (u8_of a) (u8_of b)',
     '')
addA('zg_u8_or', "", 'u8_or (u8_of a) (u8_of b)',
     '')
addA('zg_u8_xor', "", 'u8_xor (u8_of a) (u8_of b)',
     '')
addA('zg_u8_shl', "", 'u8_shl (u8_of a) (u8_of b)',
     '')
addA('zg_u8_shr', "", 'u8_shr (u8_of a) (u8_of b)',
     '')
addA('zg_u8_not', "", 'u8_not (u8_of a)',
     '')
addA('zg_u8_ltb', "", 'if u8_ltb (u8_of a) (u8_of b) then 1 else 0',
     '')
addA('zg_u8_leb', "", 'if u8_leb (u8_of a) (u8_of b) then 1 else 0',
     '')
addA('zg_i8_of', "", 'i8_of a',
     '')
addA('zg_i8_add', "", 'i8_add (i8_of a) (i8_of b)',
     '')
addA('zg_i8_sub', "", 'i8_sub (i8_of a) (i8_of b)',
     '')
addA('zg_i8_mul', "", 'i8_mul (i8_of a) (i8_of b)',
     '')
addA('zg_i8_div', "", 'i8_div (i8_of a) (i8_of b)',
     '')
addA('zg_i8_mod', "", 'i8_mod (i8_of a) (i8_of b)',
     '')
addA('zg_i8_and', "", 'i8_and (i8_of a) (i8_of b)',
     '')
addA('zg_i8_or', "", 'i8_or (i8_of a) (i8_of b)',
     '')
addA('zg_i8_xor', "", 'i8_xor (i8_of a) (i8_of b)',
     '')
addA('zg_i8_shl', "", 'i8_shl (i8_of a) (i8_of b)',
     '')
addA('zg_i8_shr', "", 'i8_shr (i8_of a) (i8_of b)',
     '')
addA('zg_i8_not', "", 'i8_not (i8_of a)',
     '')
addA('zg_i8_ltb', "", 'if i8_ltb (i8_of a) (i8_of b) then 1 else 0',
     '')
addA('zg_i8_leb', "", 'if i8_leb (i8_of a) (i8_of b) then 1 else 0',
     '')
addA('zg_u16_of', "", 'u16_of a',
     '')
addA('zg_u16_add', "", 'u16_add (u16_of a) (u16_of b)',
     '')
addA('zg_u16_sub', "", 'u16_sub (u16_of a) (u16_of b)',
     '')
addA('zg_u16_mul', "", 'u16_mul (u16_of a) (u16_of b)',
     '')
addA('zg_u16_div', "", 'u16_div (u16_of a) (u16_of b)',
     '')
addA('zg_u16_mod', "", 'u16_mod (u16_of a) (u16_of b)',
     '')
addA('zg_u16_and', "", 'u16_and (u16_of a) (u16_of b)',
     '')
addA('zg_u16_or', "", 'u16_or (u16_of a) (u16_of b)',
     '')
addA('zg_u16_xor', "", 'u16_xor (u16_of a) (u16_of b)',
     '')
addA('zg_u16_shl', "", 'u16_shl (u16_of a) (u16_of b)',
     '')
addA('zg_u16_shr', "", 'u16_shr (u16_of a) (u16_of b)',
     '')
addA('zg_u16_not', "", 'u16_not (u16_of a)',
     '')
addA('zg_u16_ltb', "", 'if u16_ltb (u16_of a) (u16_of b) then 1 else 0',
     '')
addA('zg_u16_leb', "", 'if u16_leb (u16_of a) (u16_of b) then 1 else 0',
     '')
addA('zg_i16_of', "", 'i16_of a',
     '')
addA('zg_i16_add', "", 'i16_add (i16_of a) (i16_of b)',
     '')
addA('zg_i16_sub', "", 'i16_sub (i16_of a) (i16_of b)',
     '')
addA('zg_i16_mul', "", 'i16_mul (i16_of a) (i16_of b)',
     '')
addA('zg_i16_div', "", 'i16_div (i16_of a) (i16_of b)',
     '')
addA('zg_i16_mod', "", 'i16_mod (i16_of a) (i16_of b)',
     '')
addA('zg_i16_and', "", 'i16_and (i16_of a) (i16_of b)',
     '')
addA('zg_i16_or', "", 'i16_or (i16_of a) (i16_of b)',
     '')
addA('zg_i16_xor', "", 'i16_xor (i16_of a) (i16_of b)',
     '')
addA('zg_i16_shl', "", 'i16_shl (i16_of a) (i16_of b)',
     '')
addA('zg_i16_shr', "", 'i16_shr (i16_of a) (i16_of b)',
     '')
addA('zg_i16_not', "", 'i16_not (i16_of a)',
     '')
addA('zg_i16_ltb', "", 'if i16_ltb (i16_of a) (i16_of b) then 1 else 0',
     '')
addA('zg_i16_leb', "", 'if i16_leb (i16_of a) (i16_of b) then 1 else 0',
     '')
addA('zg_u32_of', "", 'u32_of a',
     '')
addA('zg_u32_add', "", 'u32_add (u32_of a) (u32_of b)',
     '')
addA('zg_u32_sub', "", 'u32_sub (u32_of a) (u32_of b)',
     '')
addA('zg_u32_mul', "", 'u32_mul (u32_of a) (u32_of b)',
     '')
addA('zg_u32_div', "", 'u32_div (u32_of a) (u32_of b)',
     '')
addA('zg_u32_mod', "", 'u32_mod (u32_of a) (u32_of b)',
     '')
addA('zg_u32_and', "", 'u32_and (u32_of a) (u32_of b)',
     '')
addA('zg_u32_or', "", 'u32_or (u32_of a) (u32_of b)',
     '')
addA('zg_u32_xor', "", 'u32_xor (u32_of a) (u32_of b)',
     '')
addA('zg_u32_shl', "", 'u32_shl (u32_of a) (u32_of b)',
     '')
addA('zg_u32_shr', "", 'u32_shr (u32_of a) (u32_of b)',
     '')
addA('zg_u32_not', "", 'u32_not (u32_of a)',
     '')
addA('zg_u32_ltb', "", 'if u32_ltb (u32_of a) (u32_of b) then 1 else 0',
     '')
addA('zg_u32_leb', "", 'if u32_leb (u32_of a) (u32_of b) then 1 else 0',
     '')
addA('zg_i32_of', "", 'i32_of a',
     '')
addA('zg_i32_add', "", 'i32_add (i32_of a) (i32_of b)',
     '')
addA('zg_i32_sub', "", 'i32_sub (i32_of a) (i32_of b)',
     '')
addA('zg_i32_mul', "", 'i32_mul (i32_of a) (i32_of b)',
     '')
addA('zg_i32_div', "", 'i32_div (i32_of a) (i32_of b)',
     '')
addA('zg_i32_mod', "", 'i32_mod (i32_of a) (i32_of b)',
     '')
addA('zg_i32_and', "", 'i32_and (i32_of a) (i32_of b)',
     '')
addA('zg_i32_or', "", 'i32_or (i32_of a) (i32_of b)',
     '')
addA('zg_i32_xor', "", 'i32_xor (i32_of a) (i32_of b)',
     '')
addA('zg_i32_shl', "", 'i32_shl (i32_of a) (i32_of b)',
     '')
addA('zg_i32_shr', "", 'i32_shr (i32_of a) (i32_of b)',
     '')
addA('zg_i32_not', "", 'i32_not (i32_of a)',
     '')
addA('zg_i32_ltb', "", 'if i32_ltb (i32_of a) (i32_of b) then 1 else 0',
     '')
addA('zg_i32_leb', "", 'if i32_leb (i32_of a) (i32_of b) then 1 else 0',
     '')
addA('zg_rotl32', "", 'rotl32 a b',
     '')
addA('zg_rotr32', "", 'rotr32 a b',
     '')
addA('zg_rotl64', "", 'u64_to_int (rotl64 (u64_of_int a) b)',
     '')
addA('zg_rotr64', "", 'u64_to_int (rotr64 (u64_of_int a) b)',
     '')
addA('zg_bswap16', "", 'bswap16 a',
     '')
addA('zg_bswap32', "", 'bswap32 a',
     '')
addA('zg_popcount32', "", 'popcount32 a',
     '')
addA('zg_clz32', "", 'clz32 a',
     '')
addA('zg_ctz32', "", 'ctz32 a',
     '')
addA('zg_bswap64', "", 'u64_to_int (bswap64 (u64_of_int a))',
     '')
addA('zg_popcount64', "", 'popcount64 (u64_of_int a)',
     '')
addA('zg_clz64', "", 'clz64 (u64_of_int a)',
     '')
addA('zg_ctz64', "", 'ctz64 (u64_of_int a)',
     '')
addA('zg_u64_divu', "", 'u64_to_int (u64_divu (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_u64_modu', "", 'u64_to_int (u64_modu (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_u64_mulhi', "", 'u64_to_int (u64_mulhi (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_i64_add', "", 'u64_to_int (i64_add (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_i64_sub', "", 'u64_to_int (i64_sub (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_i64_mul', "", 'u64_to_int (i64_mul (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_i64_div', "", 'u64_to_int (i64_div (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_i64_mod', "", 'u64_to_int (i64_mod (u64_of_int a) (u64_of_int b))',
     '')
addA('zg_i64_shr', "", 'u64_to_int (i64_shr (u64_of_int a) b)',
     '')
addA('zg_i64_ltb', "", 'if i64_ltb (u64_of_int a) (u64_of_int b) then 1 else 0',
     '')
addA('zg_i64_leb', "", 'if i64_leb (u64_of_int a) (u64_of_int b) then 1 else 0',
     '')
addA('zg_p_own_name', "", 'rotl32 a b',
     'Definition rotl32 (x n : int) : int := x + n.\n')
addA('zg_p_own_name_beside', "", 'rotl32 a b + u8_add a b',
     'Definition rotl32 (x n : int) : int := x + n.\n')
addA('zg_p_own_helper_name', "", 'u32_add (mx a) b',
     'Definition mx (x : int) : int := x * 3.\nDefinition k (x : int) : int := x + 1.\n')
addA('zg_p_many_idiv', "", 'i32_div a b + i32_div a (b + 1) + i32_div a (b + 2) + i32_div a (b + 3) + i32_div a (b + 4) + i32_div a (b + 5) + i32_div a (b + 6) + i32_div a (b + 7) + i32_div a (b + 8) + i32_div a (b + 9) + i32_div a (b + 10) + i32_div a (b + 11)',
     '')
addA('zg_p_many_imod', "", 'i8_mod a b * i16_mod a b + i32_mod a b * i8_div a b + i16_div a b * i32_div a b + i8_mod a (b + 1) * i16_mod a (b + 1) + i32_mod a (b + 1) * i8_div a (b + 1)',
     '')
addA('zg_p_many_i64', "", 'u64_to_int (i64_div (u64_of_int a) (u64_of_int b)) + u64_to_int (i64_mod (u64_of_int a) (u64_of_int b)) + u64_to_int (i64_div (u64_of_int b) (u64_of_int a)) + u64_to_int (i64_mod (u64_of_int b) (u64_of_int a))',
     '')
addA('zg_p_nested_rot', "", 'rotl32 (rotl32 (rotl32 (rotl32 (rotl32 a 1) 2) 3) 4) 5',
     '')
addA('zg_p_nested_i8', "", 'i8_add (i8_add (i8_add (i8_add (i8_add a b) b) b) b) b',
     '')
addA('zg_p_sha_round', "", 'let e := u32_of a in let f := u32_of b in let g := u32_add e f in let h := u32_xor e g in u32_add (u32_add h (u32_xor (u32_xor (rotr32 e 6) (rotr32 e 11)) (rotr32 e 25))) (u32_add (u32_xor (u32_and e f) (u32_and (u32_not e) g)) 1116352408)',
     '')
addA('zg_p_loop_u32', "", 'lp n (u32_of a) (u32_of b)',
     'Fixpoint lp (k : nat) (x y : int) : int := match k with O => x | S m => lp m (u32_add (rotl32 x 5) y) (u32_xor y x) end.\n')
addA('zg_p_loop_i32_nontail', "", 'lp n a',
     'Fixpoint lp (k : nat) (x : int) : int := match k with O => x | S m => i32_add (lp m (i32_mul x 3)) (i32_of x) end.\n')
addA('zg_p_loop_mem', "", 'rd 0 1 (lp n a s)',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => lp m (u8_add i 1) (upd8 0 (u8_of i) (u8_of i) t) end.\n')
addA('zg_p_loop_u64', "", 'u64_to_int (lp n (u64_of_int a) (u64_of_int b))',
     'Fixpoint lp (k : nat) (x y : u64) : u64 := match k with O => x | S m => lp m (u64_divu (u64_add x y) (u64_add y (u64_of_int 1))) (u64_mulhi x y) end.\n')
addA('zg_p_u64_given_back', "", 'u64_to_int (dv (u64_of_int a) (u64_of_int b))',
     'Definition dv (x y : u64) : u64 := if u64_eqb y (u64_of_int 0) then x else u64_divu x y.\n')
addA('zg_p_choice', "", 'if a <? b then u8_add a b else i8_div a b',
     '')
addA('zg_p_field', "", 'let r := mk3 (u8_add a b) (i8_sub a b) (u16_mul a b) in f1 r + f2 r + f3 r',
     '')
addA('zg_p_pair', "", 'let p := (u32_add a b, i32_sub a b) in fst p * snd p',
     '')
addA('zg_p_function_given', "", 'twice (u8_add a) b + twice (i32_mul 3) a',
     '')
addA('zg_p_bool_param', "", 'k (u8_ltb a b) (i8_leb a b)',
     'Definition k (x y : bool) : int := if andb x y then 1 else 0.\n')
addA('zg_p_memory_read', "", 'u8_add (rd 0 a s) (i32_mul (rd 0 b s) (rd8 0 a s))',
     '')
# the bit operations of Rocq's library on counters (step 92)
addA('zh_land_budget', "", 'ff (Nat.land n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_land_num', "", 'Uint63.of_Z (Z.of_nat (Nat.land n (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_land_cmp', "", 'if Nat.leb (Nat.land n 3) 2 then a else b',
     '')
addA('zh_land_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.land j 5))) end.\n')
addA('zh_land_let', "", 'let c := Nat.land n 6 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_land_match', "", 'match Nat.land n 6 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lor_budget', "", 'ff (Nat.lor n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lor_num', "", 'Uint63.of_Z (Z.of_nat (Nat.lor n (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_lor_cmp', "", 'if Nat.leb (Nat.lor n 3) 2 then a else b',
     '')
addA('zh_lor_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.lor j 5))) end.\n')
addA('zh_lor_let', "", 'let c := Nat.lor n 6 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lor_match', "", 'match Nat.lor n 6 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lxor_budget', "", 'ff (Nat.lxor n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lxor_num', "", 'Uint63.of_Z (Z.of_nat (Nat.lxor n (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_lxor_cmp', "", 'if Nat.leb (Nat.lxor n 3) 2 then a else b',
     '')
addA('zh_lxor_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.lxor j 5))) end.\n')
addA('zh_lxor_let', "", 'let c := Nat.lxor n 6 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lxor_match', "", 'match Nat.lxor n 6 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_ldiff_budget', "", 'ff (Nat.ldiff n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_ldiff_num', "", 'Uint63.of_Z (Z.of_nat (Nat.ldiff n (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_ldiff_cmp', "", 'if Nat.leb (Nat.ldiff n 3) 2 then a else b',
     '')
addA('zh_ldiff_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.ldiff j 5))) end.\n')
addA('zh_ldiff_let', "", 'let c := Nat.ldiff n 6 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_ldiff_match', "", 'match Nat.ldiff n 6 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftr_budget', "", 'ff (Nat.shiftr n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftr_num', "", 'Uint63.of_Z (Z.of_nat (Nat.shiftr n (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_shiftr_cmp', "", 'if Nat.leb (Nat.shiftr n 3) 2 then a else b',
     '')
addA('zh_shiftr_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.shiftr j 5))) end.\n')
addA('zh_shiftr_let', "", 'let c := Nat.shiftr n 6 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftr_match', "", 'match Nat.shiftr n 6 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_clearbit_budget', "", 'ff (Nat.clearbit n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_clearbit_num', "", 'Uint63.of_Z (Z.of_nat (Nat.clearbit n (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_clearbit_cmp', "", 'if Nat.leb (Nat.clearbit n 3) 2 then a else b',
     '')
addA('zh_clearbit_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.clearbit j 5))) end.\n')
addA('zh_clearbit_let', "", 'let c := Nat.clearbit n 6 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_clearbit_match', "", 'match Nat.clearbit n 6 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_testbit_if', "", 'if Nat.testbit n 2 then a else b',
     '')
addA('zh_testbit_and', "", 'if andb (Nat.testbit n 1) (a <? b) then a else b',
     '')
addA('zh_testbit_neg', "", 'if negb (Nat.testbit n 0) then a else b',
     '')
addA('zh_testbit_sel', "", 'if Nat.testbit (Nat.shiftr n 1) 0 then a + 1 else b',
     '')
addA('zh_testbit_value', "", 'k (Nat.testbit n 3) a',
     'Definition k (t : bool) (x : int) : int := if t then x else 0.\n')
addA('zh_testbit_rec', "", 'pc n n a',
     'Fixpoint pc (k m : nat) (x : int) : int := match k with O => x | S j => pc j m (if Nat.testbit m j then x + 1 else x) end.\n')
addA('zh_testbit_big', "", 'if Nat.testbit (Z.to_nat (Uint63.to_Z a)) (Nat.modulo n 70) then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('zh_testbit_let', "", 'let t := Nat.testbit n 1 in if t then a else b',
     '')
addA('zh_testbit_b2n', "", 'ff (Nat.b2n (Nat.testbit n 2)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_b2n_num', "", 'Uint63.of_Z (Z.of_nat (Nat.b2n (a <? b))) + a',
     'From Stdlib Require Import ZArith.\n')
addA('zh_b2n_sum', "", 'ff (Nat.b2n (a <? b) + Nat.b2n (b <? a)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftl_lit', "", 'ff (Nat.shiftl n 1) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftl_masked', "", 'ff (Nat.shiftl (Nat.land n 7) 3) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftl_one', "", 'ff (Nat.shiftl 1 5) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftl_var', "", 'ff (Nat.shiftl 1 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_shiftl_big', "", 'ff (Nat.shiftl n 62) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_setbit_lit', "", 'ff (Nat.setbit n 2) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_setbit_var', "", 'ff (Nat.setbit 0 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_ones_lit', "", 'ff (Nat.ones 4) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_ones_var', "", 'ff (Nat.ones n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lnot_lit', "", 'ff (Nat.lnot n 4) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_lnot_var', "", 'ff (Nat.lnot 3 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_clearbit_var', "", 'ff (Nat.clearbit n n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_nested', "", 'ff (Nat.land (Nat.lor n 12) (Nat.shiftr n 2)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_nested_test', "", 'if Nat.testbit (Nat.lxor n (Nat.ldiff n 5)) 1 then a else b',
     '')
addA('zh_mach_lor', "", 'Uint63.of_Z (Z.of_nat (Nat.lor (Z.to_nat (Uint63.to_Z a)) (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_mach_lxor', "", 'Uint63.of_Z (Z.of_nat (Nat.lxor (Z.to_nat (Uint63.to_Z a)) (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_mach_shiftr', "", 'Uint63.of_Z (Z.of_nat (Nat.shiftr (Z.to_nat (Uint63.to_Z a)) (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zh_ar_land', "", 'ff (Nat.land n 6) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_ar_testbit', "", 'if Nat.testbit n 1 then a else b',
     'From Stdlib Require Import Arith.\n')
addA('zh_ar_shiftl', "", 'ff (Nat.shiftl n 1) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_ar_setbit', "", 'ff (Nat.setbit n 1) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_let_once', "", 'ff (let t := a <? b in if t then 1 else 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_let_twice', "", 'ff (let t := Nat.land n 6 in t + t) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zh_helper_bool', "", 'ff (bn (a <? b)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition bn (t : bool) : nat := if t then 1 else 0.\n')
addA('zh_row_land', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'From Stdlib Require Import ZArith.\nFixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.land (cb j m) 7 end.\n')
addA('zh_row_shiftr', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'From Stdlib Require Import ZArith.\nFixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.shiftr (cb j m) 1 end.\n')
addA('zh_row_testbit', "", 'Uint63.of_Z (Z.of_nat (pc n n))',
     'From Stdlib Require Import ZArith.\nFixpoint pc (k m : nat) : nat := match k with O => O | S j => if Nat.testbit m j then S (pc j m) else pc j m end.\n')
addA('zh_row_testbit_own', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'From Stdlib Require Import ZArith.\nFixpoint cb (k m : nat) : nat := match k with O => m | S j => if Nat.testbit (cb j m) 1 then S (cb j m) else cb j m end.\n')
# the recursive functions of Rocq's library on counters: a call of the kit's function (step 93)
addA('zi_gcd_budget', "", 'ff (Nat.gcd n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_gcd_num', "", 'Uint63.of_Z (Z.of_nat (Nat.gcd n (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zi_gcd_cmp', "", 'if Nat.leb (Nat.gcd n 6) 2 then a else b',
     '')
addA('zi_gcd_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.gcd j 6))) end.\n')
addA('zi_gcd_let', "", 'let c := Nat.gcd n 6 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_gcd_match', "", 'match Nat.gcd n 6 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_gcd_ar', "", 'ff (Nat.gcd n 6) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_gcd_twice', "", 'ff (Nat.gcd n 6) a + ff (S (Nat.gcd n 6)) b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_gcd_callee', "", 'g2 n a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (n : nat) (x : int) : int := ff (Nat.gcd n 6) x.\n')
addA('zi_sqrt_budget', "", 'ff (Nat.sqrt n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_sqrt_num', "", 'Uint63.of_Z (Z.of_nat (Nat.sqrt (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zi_sqrt_cmp', "", 'if Nat.leb (Nat.sqrt n) 2 then a else b',
     '')
addA('zi_sqrt_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.sqrt j))) end.\n')
addA('zi_sqrt_let', "", 'let c := Nat.sqrt n in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_sqrt_match', "", 'match Nat.sqrt n with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_sqrt_ar', "", 'ff (Nat.sqrt n) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_sqrt_twice', "", 'ff (Nat.sqrt n) a + ff (S (Nat.sqrt n)) b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_sqrt_callee', "", 'g2 n a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (n : nat) (x : int) : int := ff (Nat.sqrt n) x.\n')
addA('zi_log2_budget', "", 'ff (Nat.log2 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_log2_num', "", 'Uint63.of_Z (Z.of_nat (Nat.log2 (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zi_log2_cmp', "", 'if Nat.leb (Nat.log2 n) 2 then a else b',
     '')
addA('zi_log2_rec', "", 'lp n a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_Z (Z.of_nat (Nat.log2 j))) end.\n')
addA('zi_log2_let', "", 'let c := Nat.log2 n in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_log2_match', "", 'match Nat.log2 n with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_log2_ar', "", 'ff (Nat.log2 n) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_log2_twice', "", 'ff (Nat.log2 n) a + ff (S (Nat.log2 n)) b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_log2_callee', "", 'g2 n a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (n : nat) (x : int) : int := ff (Nat.log2 n) x.\n')
addA('zi_gcd_vars', "", 'Uint63.of_Z (Z.of_nat (Nat.gcd (Z.to_nat (Uint63.to_Z a)) (Z.to_nat (Uint63.to_Z b))))',
     'From Stdlib Require Import ZArith.\n')
addA('zi_gcd_zero_l', "", 'ff (Nat.gcd 0 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_gcd_zero_r', "", 'ff (Nat.gcd n 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_nested', "", 'ff (Nat.gcd (Nat.sqrt n) (Nat.log2 n)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_bits', "", 'ff (Nat.log2 (Nat.land n 255)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_all_three', "", 'ff (Nat.gcd n 4) a + ff (Nat.sqrt n) b + ff (Nat.log2 n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_log2_up', "", 'ff (Nat.log2_up n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_sqrt_up', "", 'ff (Nat.sqrt_up n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zi_lcm', "", 'ff (Nat.lcm n 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
# a counter written as a number, one number in the C (step 94)
addA('zj_budget_one', "", 'ff 1 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_small', "", 'ff 12 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_4999', "", 'ff 4999 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_5000', "", 'ff 5000 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_big', "", 'ff 1000000 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_hex_small', "", 'ff 0xFF a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_hex', "", 'ff 0x1F40 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_max', "", 'ff 9223372036854775807 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_budget_ar', "", 'ff 100000 a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_num_small', "", 'a + Uint63.of_nat 4095',
     'From Stdlib Require Import ZArith.\n')
addA('zj_num_big', "", 'a + Uint63.of_nat 100000',
     'From Stdlib Require Import ZArith.\n')
addA('zj_num_hex', "", 'a + Uint63.of_nat 0xFFFFF',
     'From Stdlib Require Import ZArith.\n')
addA('zj_cmp_small', "", 'if Nat.leb n 4095 then a else b',
     '')
addA('zj_cmp_big', "", 'if Nat.ltb n 100000 then a else b',
     '')
addA('zj_cmp_eq', "", 'if Nat.eqb n 5000 then a else b',
     '')
addA('zj_cmp_hex', "", 'if Nat.ltb 0x10000 n then a else b',
     '')
addA('zj_let_small', "", 'let c := 300%nat in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_let_big', "", 'let c := 6000%nat in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_add', "", 'ff (n + 100000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_sub', "", 'ff (n - 5000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_land', "", 'ff (Nat.land n 65535) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_land_hex', "", 'ff (Nat.land n 0xFFFF) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_land_max', "", 'ff (Nat.land n 9223372036854775807) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_land_past', "", 'ff (Nat.land n 9223372036854775808) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_mod', "", 'ff (Nat.modulo n 10007) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_div', "", 'ff (Nat.div n 10000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_min', "", 'ff (Nat.min n 100000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_mul_r', "", 'ff (Nat.mul (Nat.land n 255) 100000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_mul_l', "", 'ff (Nat.mul 7000 (Nat.land n 1023)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_mul_small', "", 'ff (Nat.mul (Nat.land n 255) 4000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_mul_big', "", 'ff (Nat.mul n 100000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_pow_lit', "", 'ff (Nat.pow 2 12) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_pow_big', "", 'ff (Nat.pow 2 13) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_match', "", 'match Nat.min n 6000 with O => a | S m => ff m b end',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zj_rec', "", 'lp n a',
     'Fixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (if Nat.ltb j 5000 then x + 1 else x) end.\n')
addA('zj_callee_small', "", 'g2 4000 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (k : nat) (x : int) : int := ff k x + ff k 1.\n')
addA('zj_callee_big', "", 'g2 100000 a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (k : nat) (x : int) : int := ff k x + ff k 1.\n')
# a power of two written numbers, its value one number in the C (step 95)
addA('zk_budget', "", 'ff (Nat.pow 2 13) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_budget_notation', "", 'ff (2 ^ 13)%nat a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_budget_ar', "", 'ff (Nat.pow 2 13) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_num_40', "", 'a + Uint63.of_nat (Nat.pow 2 40)',
     'From Stdlib Require Import ZArith.\n')
addA('zk_num_62', "", 'a + Uint63.of_nat (Nat.pow 2 62)',
     'From Stdlib Require Import ZArith.\n')
addA('zk_num_ten18', "", 'a + Uint63.of_nat (Nat.pow 10 18)',
     'From Stdlib Require Import ZArith.\n')
addA('zk_num_three39', "", 'a + Uint63.of_nat (Nat.pow 3 39)',
     'From Stdlib Require Import ZArith.\n')
addA('zk_num_hex_exp', "", 'a + Uint63.of_nat (Nat.pow 2 0x20)',
     'From Stdlib Require Import ZArith.\n')
addA('zk_num_big_base', "", 'a + Uint63.of_nat (Nat.pow 100000 3)',
     'From Stdlib Require Import ZArith.\n')
addA('zk_zero_zero', "", 'ff (Nat.pow 0 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_zero_big', "", 'ff (Nat.pow 0 100000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_one_big', "", 'ff (Nat.pow 1 100000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_cmp', "", 'if Nat.ltb n (Nat.pow 10 18) then a else b',
     '')
addA('zk_let', "", 'let c := Nat.pow 2 20 in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_land', "", 'ff (Nat.land n (Nat.pow 2 40 - 1)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_mod', "", 'ff (Nat.modulo n (Nat.pow 10 9)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_rec', "", 'lp n a',
     'Fixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (if Nat.ltb j (Nat.pow 2 14) then x + 1 else x) end.\n')
addA('zk_callee', "", 'g2 (Nat.pow 2 13) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (k : nat) (x : int) : int := ff k x + ff k 1.\n')
addA('zk_closed_add', "", 'ff (Nat.add 5000 100000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_closed_land', "", 'ff (Nat.land 1000000 65535) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_closed_cmp', "", 'if Nat.ltb 100000 1000000 then a else b',
     '')
addA('zk_closed_gcd', "", 'ff (Nat.gcd 100000 6) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_closed_mul', "", 'ff (Nat.mul 7000 3) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zk_past_63', "", 'a + Uint63.of_nat (Nat.pow 2 63)',
     'From Stdlib Require Import ZArith.\n')
addA('zk_past_ten19', "", 'a + Uint63.of_nat (Nat.pow 10 19)',
     'From Stdlib Require Import ZArith.\n')
# the bounds of a min and of a subtraction of counters exact (step 97)
addA('zl_min_first', "", 'ff (Nat.mul 3 (Nat.min 1000 (Uint63.to_nat a))) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_min_vars', "", 'ff (Nat.min n (Uint63.to_nat a)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_min_nested', "", 'ff (Nat.mul 2 (Nat.min (Nat.min (Uint63.to_nat a) (Uint63.to_nat b)) 500)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_min_let', "", 'let c := Nat.min (Uint63.to_nat a) 1000 in ff (Nat.mul 3 c) b + ff c a',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_min_test', "", 'if Nat.ltb (Nat.mul 4 (Nat.min (Uint63.to_nat a) 1000)) 3000 then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('zl_min_num', "", 'a + Uint63.of_nat (Nat.mul 1000 (Nat.min (Uint63.to_nat a) 1000))',
     'From Stdlib Require Import ZArith.\n')
addA('zl_min_call', "", 'lp (Nat.min (Uint63.to_nat a) 1000) a',
     'From Stdlib Require Import ZArith.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + 1) end.\n')
addA('zl_min_callee', "", 'g2 (Nat.min (Uint63.to_nat a) 1000) a',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (k : nat) (x : int) : int := ff (Nat.mul 3 k) x.\n')
addA('zl_sub_clamp', "", 'ff (Nat.mul 3 (Nat.sub 1000 (Uint63.to_nat a))) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_sub_vars', "", 'ff (Nat.sub n (Uint63.to_nat a)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_sub_let', "", 'let c := Nat.sub 1000 (Uint63.to_nat a) in ff (Nat.mul 3 c) b + ff c a',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_sub_test', "", 'if Nat.leb (Nat.mul 5 (Nat.sub 1000 (Uint63.to_nat a))) 2000 then a else b',
     'From Stdlib Require Import ZArith.\n')
addA('zl_sub_min', "", 'ff (Nat.mul 3 (Nat.sub (Nat.min (Uint63.to_nat a) 1000) (Uint63.to_nat b))) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_min_past', "", 'ff (Nat.min (Nat.mul (Uint63.to_nat a) 4) 5) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_min_past_ctl', "", 'ff (Nat.min (Nat.mul (Nat.land (Uint63.to_nat a) 255) 4) 5) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_sub_past', "", 'ff (Nat.sub 5 (Nat.mul (Uint63.to_nat a) 4)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zl_sub_past_ctl', "", 'ff (Nat.sub 5 (Nat.mul (Nat.land (Uint63.to_nat a) 255) 4)) b',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
# a match on a choice of constructors in any place: log2_up, sqrt_up, Nat.compare in a counter (step 98)
addA('zm_log2_up_num', "", 'a + Uint63.of_nat (Nat.log2_up n)',
     'From Stdlib Require Import ZArith.\n')
addA('zm_log2_up_cmp', "", 'if Nat.leb (Nat.log2_up n) 3 then a else b',
     '')
addA('zm_log2_up_let', "", 'let c := Nat.log2_up n in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_log2_up_ar', "", 'ff (Nat.log2_up n) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_log2_up_rec', "", 'lp n a',
     'Fixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_nat (Nat.log2_up j)) end.\n')
addA('zm_log2_up_zero', "", 'ff (Nat.log2_up 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_log2_up_lit', "", 'ff (Nat.log2_up 1000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_sqrt_up_num', "", 'a + Uint63.of_nat (Nat.sqrt_up n)',
     'From Stdlib Require Import ZArith.\n')
addA('zm_sqrt_up_cmp', "", 'if Nat.leb (Nat.sqrt_up n) 3 then a else b',
     '')
addA('zm_sqrt_up_let', "", 'let c := Nat.sqrt_up n in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_sqrt_up_ar', "", 'ff (Nat.sqrt_up n) a',
     'From Stdlib Require Import Arith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_sqrt_up_rec', "", 'lp n a',
     'Fixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_nat (Nat.sqrt_up j)) end.\n')
addA('zm_sqrt_up_zero', "", 'ff (Nat.sqrt_up 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_sqrt_up_lit', "", 'ff (Nat.sqrt_up 1000) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_compare_cnt', "", 'ff (match Nat.compare n 3 with Lt => 1 | Eq => 2 | Gt => 3 end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_compare_cnt_var', "", 'ff (match Nat.compare n (Uint63.to_nat b) with Lt => n | Eq => 0 | Gt => 5 end) a',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_compare_bool', "", 'if match Nat.compare n 3 with Lt => true | _ => false end then a else b',
     '')
addA('zm_compare_nested', "", 'ff (match Nat.compare n 3 with Lt => match Nat.compare n 1 with Lt => 0 | _ => 1 end | _ => 2 end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_choice_cnt', "", 'ff (match (if Nat.ltb n 3 then Lt else Gt) with Lt => 1 | _ => 2 end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_prim_compare_cnt', "", 'ff (match PrimInt63.compare a b with Lt => 1 | Eq => 2 | Gt => 3 end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zm_log2_up_sqrt_up', "", 'ff (Nat.log2_up (Nat.sqrt_up n)) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
# a counter chosen by a match on a counter (step 99)
addA('zn_num', "", 'a + Uint63.of_nat (match n with O => 1 | S m => m end)',
     'From Stdlib Require Import ZArith.\n')
addA('zn_test', "", 'if Nat.ltb (match n with O => 1 | S m => m end) 3 then a else b',
     '')
addA('zn_let', "", 'let c := match n with O => 1%nat | S m => m end in ff c a + ff c b',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zn_twice', "", 'ff (match n with O => 0 | S m => m + m end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zn_nested', "", 'ff (match n with O => 1 | S m => match m with O => 2 | S k => k end end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zn_of_expr', "", 'ff (match Nat.min n 5 with O => 1 | S m => m end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zn_of_mvar', "", 'ff (match Uint63.to_nat b with O => 1 | S m => Nat.min m 10 end) a',
     'From Stdlib Require Import ZArith.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zn_call_in', "", 'ff (match n with O => 0 | S m => Nat.log2 m end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zn_helper_in', "", 'ff (match n with O => 0 | S m => g2 m end) a',
     'Definition g2 (k : nat) : nat := Nat.add k 1.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zn_callee', "", 'g3 (match n with O => 1 | S m => m end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g3 (k : nat) (x : int) : int := ff k x + ff k 1.\n')
addA('zn_rec', "", 'lp n a',
     'Fixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (x + Uint63.of_nat (match j with O => 1 | S i => i end)) end.\n')
addA('zn_rec_arg', "", 'lp n a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint lp (k : nat) (x : int) : int := match k with O => x | S j => lp j (ff (match j with O => 1 | S i => i end) x) end.\n')
addA('zn_pred_like', "", 'ff (match n with O => 0 | S m => m end) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
# a function giving back a counter whose recursion goes more than one step down (step 100)
addA('zo_budget', "", 'ff (tw n) a',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S O => 5 | S (S m) => S (tw m) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zo_three', "", 'Uint63.of_nat (t3 n) + a',
     'Fixpoint t3 (k : nat) : nat := match k with O => 1 | S O => 2 | S (S O) => 3 | S (S (S m)) => S (t3 m) end.\n')
addA('zo_three_test', "", 'if Nat.leb (t3 n) 3 then a else b',
     'Fixpoint t3 (k : nat) : nat := match k with O => 1 | S O => 2 | S (S O) => 3 | S (S (S m)) => S (t3 m) end.\n')
addA('zo_acc', "", 'Uint63.of_nat (ta n 0)',
     'Fixpoint ta (k : nat) (c : nat) : nat := match k with O => c | S O => S c | S (S m) => ta m (S c) end.\n')
addA('zo_acc_budget', "", 'ff (ta n 0) a',
     'Fixpoint ta (k : nat) (c : nat) : nat := match k with O => c | S O => S c | S (S m) => ta m (S c) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zo_mem', "", 'Uint63.of_nat (tm n s)',
     'Fixpoint tm (k : nat) (t : mem) : nat := match k with O => O | S O => 1 | S (S m) => if 0 <? rd 0 0 t then S (tm m t) else tm m t end.\n')
addA('zo_two', "", 'Uint63.of_nat (tw n) + Uint63.of_nat (t3 n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S O => 5 | S (S m) => S (tw m) end.\nFixpoint t3 (k : nat) : nat := match k with O => 1 | S O => 2 | S (S O) => 3 | S (S (S m)) => S (t3 m) end.\n')
addA('zo_let', "", 'let c := tw n in ff c a + ff c b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S O => 5 | S (S m) => S (tw m) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zo_callee', "", 'g2 n a',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S O => 5 | S (S m) => S (tw m) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (k : nat) (x : int) : int := ff (tw k) x.\n')
# a counter a function gives back, used as a counter inside an operation (step 102)
addA('zs_land_cnt', "", 'ff (Nat.land (cnt n a s) 255) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_lor_lit', "", 'ff (Nat.lor (cnt n a s) 3) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_lxor_lit', "", 'ff (Nat.lxor (cnt n a s) 1) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_ldiff_lit', "", 'ff (Nat.ldiff (cnt n a s) 2) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_land_param', "", 'ff (Nat.land (cnt n a s) n) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_land_two', "", 'ff (Nat.land (cnt n a s) (cnt n b s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_lor_two', "", 'ff (Nat.lor (cnt n a s) (cnt n b s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_nested', "", 'ff (Nat.lor (Nat.land (cnt n a s) 12) 3) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_add_inside', "", 'ff (Nat.land (cnt n a s + 1) 255) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_inside_add', "", 'ff (Nat.land (cnt n a s) 255 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_test', "", 'if Nat.leb (Nat.land (cnt n a s) 7) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zs_eqb', "", 'if Nat.eqb (Nat.lxor (cnt n a s) n) 0 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zs_match', "", 'match Nat.land (cnt n a s) 15 with O => a | S m => ff m b end',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_let', "", 'let c := Nat.lor (cnt n a s) 1 in ff c a + ff c b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_callee', "", 'g2 (Nat.land (cnt n a s) 63) a',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nDefinition g2 (k : nat) (x : int) : int := ff k x + ff k 1.\n')
addA('zs_in_rec', "", 'lp n a s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint lp (k : nat) (x : int) (t : mem) : int := match k with O => x | S j => if Nat.eqb (Nat.land (cnt k x t) 1) 0 then lp j (x + 1) t else lp j x t end.\n')
addA('zs_shiftr', "", 'ff (Nat.shiftr (cnt n a s) 1) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_shiftl', "", 'ff (Nat.shiftl (cnt n a s) 1) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_div', "", 'ff (Nat.div (cnt n a s) 3) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_modulo', "", 'ff (Nat.modulo (cnt n a s) 7) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_min', "", 'ff (Nat.min (cnt n a s) 9) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sub', "", 'ff (cnt n a s - 2) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_testbit', "", 'if Nat.testbit (cnt n a s) 0 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zs_bitrow_direct', "", 'ff (cb n n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.land (S (cb j m)) 1023 end.\n')
addA('zs_bitrow_one', "", 'ff (cb n 0) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.land (S (cb j m)) 1023 end.\n')
addA('zs_bitrow_lor', "", 'ff (Nat.land (co n n) 7) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint co (k m : nat) : nat := match k with O => m | S j => Nat.lor (co j m) 4 end.\n')
addA('zs_big_const', "", 'ff (Nat.land (cbm n n) 255) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint cbm (k m : nat) : nat := match k with O => m | S j => Nat.mul (Nat.land (S (cbm j m)) 4095) 300 end.\n')
addA('zs_shiftl_two', "", 'ff (Nat.shiftl (cnt n a s) 2) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_shiftl_three', "", 'ff (Nat.shiftl (cnt n a s) 3) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_shiftl_var', "", 'ff (Nat.shiftl (cnt n a s) n) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_setbit', "", 'ff (Nat.setbit (cnt n a s) 4) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_clearbit', "", 'ff (Nat.clearbit (cnt n a s) 0) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_pred', "", 'ff (Nat.pred (cnt n a s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_max', "", 'ff (Nat.max (cnt n a s) 9) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_div2', "", 'ff (Nat.div2 (cnt n a s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_double', "", 'ff (Nat.double (cnt n a s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_lor', "", 'ff (Nat.lor (cnt n a s) 3 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_lxor', "", 'ff (Nat.lxor (cnt n a s) 1 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_ldiff', "", 'ff (Nat.ldiff (cnt n a s) 2 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_shiftr', "", 'ff (Nat.shiftr (cnt n a s) 1 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_div', "", 'ff (Nat.div (cnt n a s) 3 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_mod', "", 'ff (Nat.modulo (cnt n a s) 7 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_min', "", 'ff (Nat.min (cnt n a s) 9 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_max', "", 'ff (Nat.max (cnt n a s) 9 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_sub', "", 'ff (cnt n a s - 2 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_pred', "", 'ff (Nat.pred (cnt n a s) + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_div2', "", 'ff (Nat.div2 (cnt n a s) + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_clearbit', "", 'ff (Nat.clearbit (cnt n a s) 0 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_setbit', "", 'ff (Nat.setbit (cnt n a s) 4 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_double', "", 'ff (Nat.double (cnt n a s) + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_sum_shiftl', "", 'ff (Nat.shiftl (cnt n a s) 1 + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_mul_land', "", 'ff (2 * Nat.land (cnt n a s) 255) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\n')
addA('zs_const_4095', "", 'ff (cb4 n n) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint cb4 (k m : nat) : nat := match k with O => m | S j => Nat.land (S (cb4 j m)) 4095 end.\n')
addA('zs_const_mid', "", 'ff (Nat.land (cbm n n) 255) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint cbm (k m : nat) : nat := match k with O => m | S j => Nat.mul (Nat.land (S (cbm j m)) 255) 300 end.\n')
# a row's bit operations: land, lor, lxor, ldiff, the same modulo a word (step 101)
addA('zr_lor', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.lor (cb j m) 5 end.\n')
addA('zr_lxor', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.lxor (cb j m) 5 end.\n')
addA('zr_ldiff', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.ldiff (cb j m) 5 end.\n')
addA('zr_land_param', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.land (cb j m) m end.\n')
addA('zr_land_two', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.land (S (cb j m)) (cb j m + 3) end.\n')
addA('zr_lor_deep', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S O => 1 | S (S j) => Nat.lor (cb j m) 6 end.\n')
addA('zr_land_budget', "", 'ff (Nat.land (cb n n) 255) a',
     'Fixpoint ff (n : nat) (x : int) : int := match n with O => x | S m => ff m (x + 1) end.\nFixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.land (S (cb j m)) 1023 end.\n')
addA('zr_lxor_test', "", 'if Nat.leb (cb n n) 3 then a else b',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.lxor (cb j m) 1 end.\n')
addA('zr_mixed', "", 'Uint63.of_Z (Z.of_nat (cb n n))',
     'Fixpoint cb (k m : nat) : nat := match k with O => m | S j => Nat.lor (Nat.land (cb j m) 12) (j + 1) end.\n')
# a memory in a value of any data type; a sixth probe (step 87)
addA('zf_h_user', "", 'match st1 a s with Ok v t => v + rd 0 a t | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nDefinition st1 (i : int) (t : mem) : res := if i =? 0 then Err 1 else Ok i (upd 0 i i t).\n')
addA('zf_h_user_seq', "", 'match st1 a s with Ok v t => match st1 b t with Ok w u => v + w + rd 0 a u | Err e => e + v end | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nDefinition st1 (i : int) (t : mem) : res := if i =? 0 then Err 1 else Ok i (upd 0 i i t).\n')
addA('zf_h_sum', "", 'match st1 a s with inr (v, t) => v + rd 0 a t | inl e => e end',
     'Definition st1 (i : int) (t : mem) : int + (int * mem) := if i =? 0 then inl 1 else inr (i, upd 0 i i t).\n')
addA('zf_h_sum_left', "", 'match st1 a s with inl (v, t) => v + rd 0 a t | inr e => e end',
     'Definition st1 (i : int) (t : mem) : (int * mem) + int := if i =? 0 then inr 1 else inl (i, upd 0 i i t).\n')
addA('zf_h_sum_mem', "", 'match st1 a s with inr t => rd 0 a t | inl e => e end',
     'Definition st1 (i : int) (t : mem) : int + mem := if i =? 0 then inl 1 else inr (upd 0 i i t).\n')
addA('zf_h_both', "", 'match st1 a s with inl t => rd 0 1 t | inr t => rd 0 a t end',
     'Definition st1 (i : int) (t : mem) : mem + mem := if i =? 0 then inl (upd 0 1 1 t) else inr (upd 0 i i t).\n')
addA('zf_h_three', "", 'match st1 a s with A3 t => rd 0 0 t | B3 x t => x + rd 0 a t | C3 e f => e + f end',
     'Inductive r3c := A3 (t : mem) | B3 (x : int) (t : mem) | C3 (e f : int).\nDefinition st1 (i : int) (t : mem) : r3c := if i =? 0 then C3 1 2 else if i =? 1 then A3 t else B3 i (upd 0 i i t).\n')
addA('zf_r_user', "", 'match lp n a s with Ok v t => v + rd 0 a t | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : res := match k with O => Ok i t | S m => if i =? 7 then Err i else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_r_user_after', "", 'match lp n a s with Ok v t => v + rd 0 a t | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : res := match k with O => Ok i t | S m => match lp m (i + 1) t with Ok v u => Ok (v + 1) (upd 0 i v u) | Err e => Err (e + 1) end end.\n')
addA('zf_r_user_noval', "", 'match lp n a s with Good t => rd 0 a t | Bad => 0 end',
     'Inductive rm := Good (t : mem) | Bad.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => Good t | S m => if i =? 7 then Bad else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_r_sum', "", 'match lp n a s with inr (v, t) => v + rd 0 a t | inl e => e end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : int + (int * mem) := match k with O => inr (i, t) | S m => if i =? 7 then inl i else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_r_sum_after', "", 'match lp n a s with inr (v, t) => v + rd 0 a t | inl e => e end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : int + (int * mem) := match k with O => inr (i, t) | S m => match lp m (i + 1) t with inr (v, u) => inr (v + 1, upd 0 i v u) | inl e => inl (e + 1) end end.\n')
addA('zf_r_sum_mem', "", 'match lp n a s with inr t => rd 0 a t | inl e => e end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : int + mem := match k with O => inr t | S m => if i =? 7 then inl i else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_r_three', "", 'match lp n a s with A3 t => rd 0 0 t | B3 x t => x + rd 0 a t | C3 e f => e + f end',
     'Inductive r3c := A3 (t : mem) | B3 (x : int) (t : mem) | C3 (e f : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : r3c := match k with O => A3 t | S m => if i =? 7 then C3 i 1 else if i =? 8 then B3 i t else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_r_field_record', "", 'match lp n a s with OkR x t => pa x + pb x + rd 0 a t | ErrR => 0 end',
     'Record pr := mkpr { pa : int; pb : int }.\nInductive rr := OkR (x : pr) (t : mem) | ErrR.\nFixpoint lp (k : nat) (i : int) (t : mem) : rr := match k with O => OkR (mkpr i i) t | S m => if i =? 7 then ErrR else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_r_two_funcs', "", 'match lq n a s with Ok v t => v + rd 0 a t | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : res := match k with O => Ok i t | S m => lp m (i + 1) (upd 0 i 1 t) end.\nFixpoint lq (k : nat) (i : int) (t : mem) : res := match k with O => lp 2 i t | S m => match lq m i t with Ok v u => Ok (v + 1) u | Err e => Err e end end.\n')
addA('zf_r_in_number_fn', "", 'outer n a s',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : res := match k with O => Ok i t | S m => lp m (i + 1) (upd 0 i 1 t) end.\nFixpoint outer (j : nat) (x : int) (t : mem) : int := match j with O => x | S m => match lp 2 x t with Ok v u => outer m (x + v) u | Err e => e end end.\n')
addA('zf_r_let', "", 'let r := lp n a s in match r with Ok v _ => v | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : res := match k with O => Ok i t | S m => lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_r_old_mem', "", 'match lp n a s with Ok v _ => v | Err e => rd 0 0 s end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : res := match k with O => Ok i t | S m => lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zf_m_sum', "", 'match total n a s with inr (x, _) => x | inl e => 0 - e end',
     'Definition R (A : Type) := mem -> int + (A * mem).\nDefinition rok {A} (x : A) : R A := fun t => inr (x, t).\nDefinition rbind {A B} (m : R A) (f : A -> R B) : R B := fun t => match m t with inr (x, u) => f x u | inl e => inl e end.\nDefinition rerr {A} (e : int) : R A := fun _ => inl e.\nDefinition get (i : int) : R int := fun t => if i <? 16 then inr (rd 0 i t, t) else inl i.\nFixpoint total (k : nat) (i : int) : R int := match k with O => rok 0 | S m => rbind (get i) (fun v => rbind (total m (i + 1)) (fun r => rok (v + r))) end.\n')
addA('zf_m_user', "", 'match total n a s with Ok x _ => x | Err e => 0 - e end',
     'Inductive res (A : Type) := Ok (v : A) (t : mem) | Err (e : int).\nArguments Ok {A} v t. Arguments Err {A} e.\nDefinition R (A : Type) := mem -> res A.\nDefinition rok {A} (x : A) : R A := fun t => Ok x t.\nDefinition rbind {A B} (m : R A) (f : A -> R B) : R B := fun t => match m t with Ok x u => f x u | Err e => Err e end.\nDefinition get (i : int) : R int := fun t => if i <? 16 then Ok (rd 0 i t) t else Err i.\nFixpoint total (k : nat) (i : int) : R int := match k with O => rok 0 | S m => rbind (get i) (fun v => rbind (total m (i + 1)) (fun r => rok (v + r))) end.\n')
addA('zq_res_sum_mem', "", 'match total n a s with inr (x, _) => x | inl e => 0 - e end',
     'Definition R (A : Type) := mem -> int + (A * mem).\nDefinition rok {A} (x : A) : R A := fun t => inr (x, t).\nDefinition rbind {A B} (m : R A) (f : A -> R B) : R B := fun t => match m t with inr (x, u) => f x u | inl e => inl e end.\nDefinition rerr {A} (e : int) : R A := fun _ => inl e.\nDefinition get (i : int) : R int := fun t => if i <? 16 then inr (rd 0 i t, t) else inl i.\nFixpoint total (k : nat) (i : int) : R int :=\n  match k with O => rok 0 | S m => rbind (get i) (fun v => rbind (total m (i + 1)) (fun r => rok (v + r))) end.\n')
addA('zq_st_record', "", 'match run n a (mkst 0 0) with (x, z) => x + cnt z + sum0 z end',
     'Record st := mkst { cnt : int; sum0 : int }.\nDefinition S0 (A : Type) := st -> A * st.\nDefinition sret {A} (x : A) : S0 A := fun z => (x, z).\nDefinition sbind {A B} (m : S0 A) (f : A -> S0 B) : S0 B := fun z => let (x, z2) := m z in f x z2.\nDefinition tick (v : int) : S0 int := fun z => (cnt z, mkst (cnt z + 1) (sum0 z + v)).\nFixpoint run (k : nat) (i : int) : S0 int :=\n  match k with O => sret i | S m => sbind (tick i) (fun _ => run m (i + 1)) end.\n')
addA('zq_reader', "", 'walk n a (mkcfg 10 b)',
     'Record cfg := mkcfg { lim : int; stepz : int }.\nDefinition Rd (A : Type) := cfg -> A.\nDefinition rret {A} (x : A) : Rd A := fun _ => x.\nDefinition rbnd {A B} (m : Rd A) (f : A -> Rd B) : Rd B := fun c => f (m c) c.\nDefinition ask : Rd int := fun c => stepz c.\nFixpoint walk (k : nat) (i : int) : Rd int :=\n  match k with O => rret i | S m => rbnd ask (fun d => walk m (i + d)) end.\n')
addA('zq_option_pure', "", 'match calc a b 3 with Some v => v | None => 0 end',
     'Definition obind {A B} (m : option A) (f : A -> option B) : option B := match m with Some x => f x | None => None end.\nDefinition safe_div (x y : int) : option int := if y =? 0 then None else Some (x / y).\nDefinition calc (x y z : int) : option int := obind (safe_div x y) (fun p => obind (safe_div p z) (fun q => Some (p + q))).\n')
addA('zq_nested_pats', "", 'pick (oo a) (oo b) + pick (oo (a - 1)) None',
     'Definition pick (x y : option int) : int :=\n  match x, y with Some p, Some q => p + q | Some p, None => p | None, Some q => q | None, None => 0 end.\nDefinition oo (x : int) : option int := if x <? 0 then None else Some x.\n')
addA('zq_tuple_bools', "", 'mode (a <? b) (b <? 3) + mode (b <? a) (a <? 3)',
     'Definition mode (x y : bool) : int := match x, y with true, true => 1 | true, false => 2 | false, true => 3 | false, false => 4 end.\n')
addA('zq_enum_state', "", 'ticks (runj n (mkjob Idle a 0))',
     'Inductive phase := Idle | Busy | Done.\nDefinition phase_eq (x y : phase) : bool := match x, y with Idle, Idle | Busy, Busy | Done, Done => true | _, _ => false end.\nRecord job := mkjob { ph : phase; left0 : int; ticks : int }.\nDefinition stepj (j : job) : job :=\n  match ph j with\n  | Idle => {| ph := Busy; left0 := left0 j; ticks := ticks j |}\n  | Busy => if left0 j <=? 1 then {| ph := Done; left0 := 0; ticks := ticks j + 1 |} else {| ph := Busy; left0 := left0 j - 1; ticks := ticks j + 1 |}\n  | Done => j\n  end.\nFixpoint runj (k : nat) (j : job) : job := match k with O => j | S m => if phase_eq (ph j) Done then j else runj m (stepj j) end.\n')
addA('zq_nested_records', "", 'x0 (p1b (shrink n (mkseg (mkpt 0 0) (mkpt a b))))',
     'Record pt := mkpt { x0 : int; y0 : int }.\nRecord seg := mkseg { p0 : pt; p1b : pt }.\nDefinition mid (s0 : seg) : pt := mkpt ((x0 (p0 s0) + x0 (p1b s0)) / 2) ((y0 (p0 s0) + y0 (p1b s0)) / 2).\nFixpoint shrink (k : nat) (s0 : seg) : seg := match k with O => s0 | S m => shrink m (mkseg (p0 s0) (mid s0)) end.\n')
addA('zq_struct_in_mem', "", 'pr (load a (bump n a s))',
     'Record task := mkt { pr : int; st0 : int; nx : int }.\nDefinition load (i : int) (t : mem) : task := mkt (rd 0 (3 * i) t) (rd 0 (3 * i + 1) t) (rd 0 (3 * i + 2) t).\nDefinition store (i : int) (x : task) (t : mem) : mem := upd 0 (3 * i) (pr x) (upd 0 (3 * i + 1) (st0 x) (upd 0 (3 * i + 2) (nx x) t)).\nFixpoint bump (k : nat) (i : int) (t : mem) : mem :=\n  match k with O => t | S m => let x := load i t in bump m (nx x) (store i (mkt (pr x + 1) (st0 x) (nx x)) t) end.\n')
addA('zq_bitfields', "", 'getf (setf a 4 8 b) 4 8 + rot32 a 7',
     'Definition getf (w lo len : int) : int := (w >> lo) land ((1 << len) - 1).\nDefinition setf (w lo len v : int) : int := let m := ((1 << len) - 1) << lo in (w land (m lxor (0 - 1))) lor ((v << lo) land m).\nDefinition rot32 (x k : int) : int := ((x << k) lor (x >> (32 - k))) land 4294967295.\n')
addA('zq_fixed_sat', "", 'powf n a 65536',
     'Definition sat_add (x y lim : int) : int := let r := x + y in if lim <? r then lim else r.\nDefinition fxmul (x y : int) : int := (x * y) >> 16.\nFixpoint powf (k : nat) (x acc : int) : int := match k with O => acc | S m => powf m x (sat_add (fxmul acc x) 1 1000000) end.\n')
addA('zq_isqrt', "", 'bis 40 0 (a + 1) a',
     'Fixpoint bis (k : nat) (lo hi x : int) : int :=\n  match k with\n  | O => lo\n  | S m => let mid := (lo + hi) / 2 in\n           if mid * mid <=? x then bis m mid hi x else bis m lo mid x\n  end.\n')
addA('zq_knapsack', "", 'rd 0 a (outer n 0 a s)',
     'Fixpoint inner (k : nat) (w wi vi : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m =>\n      if w <? wi then t else\n      let c := rd 0 (w - wi) t + vi in\n      inner m (w - 1) wi vi (if rd 0 w t <? c then upd 0 w c t else t)\n  end.\nFixpoint outer (k : nat) (i cap : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m => outer m (i + 1) cap (inner 100 cap (rd 1 i t) (rd 2 i t) t)\n  end.\n')
addA('zq_matmul_loops', "", 'rd 2 a (rows n 0 s)',
     'Fixpoint dot (k : nat) (i j z acc : int) (t : mem) : int :=\n  match k with O => acc | S m => dot m i j (z + 1) (acc + rd 0 (i * 4 + z) t * rd 1 (z * 4 + j) t) t end.\nFixpoint row (k : nat) (i j : int) (t : mem) : mem :=\n  match k with O => t | S m => row m i (j + 1) (upd 2 (i * 4 + j) (dot 4 i j 0 0 t) t) end.\nFixpoint rows (k : nat) (i : int) (t : mem) : mem :=\n  match k with O => t | S m => rows m (i + 1) (row 4 i 0 t) end.\n')
addA('zq_strings', "", 'let t := rev2 n 0 a s in let (e, u) := itoa n b 0 t in slen n a 0 u + atoi n 0 0 u + e',
     'Fixpoint slen (k : nat) (i acc : int) (t : mem) : int :=\n  match k with O => acc | S m => if rd8 0 i t =? 0 then acc else slen m (i + 1) (acc + 1) t end.\nFixpoint rev2 (k : nat) (i j : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m => if i <? j then rev2 m (i + 1) (j - 1) (upd8 0 i (rd8 0 j t) (upd8 0 j (rd8 0 i t) t)) else t\n  end.\nFixpoint atoi (k : nat) (i acc : int) (t : mem) : int :=\n  match k with O => acc | S m => let c := rd8 0 i t in if (48 <=? c) && (c <=? 57) then atoi m (i + 1) (acc * 10 + c - 48) t else acc end.\nFixpoint itoa (k : nat) (v i : int) (t : mem) : int * mem :=\n  match k with\n  | O => (i, t)\n  | S m => if v =? 0 then (i, t) else itoa m (v / 10) (i + 1) (upd8 1 i (48 + v mod 10) t)\n  end.\n')
addA('zq_list_in_mem', "", 'match rev_list n a 0 s with (r, t) => sum_list n r 0 t end',
     'Definition nextp (p : int) (t : mem) : int := rd 0 (p + 1) t.\nDefinition valp (p : int) (t : mem) : int := rd 0 p t.\nFixpoint sum_list (k : nat) (p acc : int) (t : mem) : int :=\n  match k with O => acc | S m => if p =? 0 then acc else sum_list m (nextp p t) (acc + valp p t) t end.\nFixpoint rev_list (k : nat) (p prev : int) (t : mem) : int * mem :=\n  match k with\n  | O => (prev, t)\n  | S m => if p =? 0 then (prev, t) else let q := nextp p t in rev_list m q p (upd 0 (p + 1) prev t)\n  end.\n')
addA('zq_tree_ptrs', "", 'sum_tree n a (insert n a b 50 s)',
     'Fixpoint sum_tree (k : nat) (p : int) (t : mem) : int :=\n  match k with\n  | O => 0\n  | S m => if p =? 0 then 0 else rd 0 p t + sum_tree m (rd 0 (p + 1) t) t + sum_tree m (rd 0 (p + 2) t) t\n  end.\nFixpoint insert (k : nat) (p v fresh : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m =>\n      let u := rd 0 p t in\n      let side := if v <? u then p + 1 else p + 2 in\n      let c := rd 0 side t in\n      if c =? 0 then upd 0 side fresh (upd 0 fresh v t) else insert m c v fresh t\n  end.\n')
addA('zq_dfs_mutual', "", 'rd 1 a (dfs n a s)',
     'Fixpoint dfs (k : nat) (u : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m => if rd 1 u t =? 1 then t else nbrs m (rd 2 u t) (upd 1 u 1 t)\n  end\nwith nbrs (k : nat) (e : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m => if rd 0 e t =? 0 then t else nbrs m (e + 1) (dfs m (rd 0 e t) t)\n  end.\n')
addA('zq_generic_hash', "", 'probe n (fun i => (i * 31 + b) mod 64) a a s',
     'Fixpoint probe (k : nat) (h : int -> int) (i x : int) (t : mem) : int :=\n  match k with O => 0 | S m => if rd 0 (h i) t =? x then h i else probe m h (i + 1) x t end.\n')
addA('zq_class_container', "", 'bget a (fillb n a b s)',
     'Class Bag (B : Type) := { bget : int -> B -> int; bput : int -> int -> B -> B }.\n#[export] Instance bag_mem : Bag mem := { bget := fun i t => rd 0 i t; bput := fun i v t => upd 0 i v t }.\nFixpoint fillb {B} `{Bag B} (k : nat) (i v : int) (x : B) : B :=\n  match k with O => x | S m => fillb m (i + 1) v (bput i v x) end.\n')
addA('zq_functor_mem', "", 'O1.get a (O1.clear n a s)',
     'Module Type STORE. Parameter blk : int. End STORE.\nModule Ops (X : STORE).\n  Definition get (i : int) (t : mem) : int := rd X.blk i t.\n  Definition put (i v : int) (t : mem) : mem := upd X.blk i v t.\n  Fixpoint clear (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => clear m (i + 1) (put i 0 t) end.\nEnd Ops.\nModule B1 <: STORE. Definition blk : int := 1. End B1.\nModule O1 := Ops B1.\n')
addA('zq_section_blk', "", 'tget 2 a (tfill 2 n a b s)',
     'Section Tab.\nVariable blk : int.\nDefinition tget (i : int) (t : mem) : int := rd blk i t.\nDefinition tput (i v : int) (t : mem) : mem := upd blk i v t.\nFixpoint tfill (k : nat) (i v : int) (t : mem) : mem := match k with O => t | S m => tfill m (i + 1) v (tput i v t) end.\nEnd Tab.\n')
addA('zq_local_fn_mem', "", 'rd 0 a (upd2 a s)',
     'Definition upd2 (i : int) (t : mem) : mem :=\n  let w := fun j (u : mem) => upd 0 j (rd 0 j u + 1) u in\n  w i (w (i + 1) t).\n')
addA('zq_iter_closure', "", 'rd 0 a (iter_range n a (fun i t => upd 0 i (i + b) t) s)',
     'Fixpoint iter_range (k : nat) (i : int) (f : int -> mem -> mem) (t : mem) : mem :=\n  match k with O => t | S m => iter_range m (i + 1) f (f i t) end.\n')
addA('zq_nat_match3', "", 'lvl n + lvl 2 + lvl 7',
     'Definition lvl (k : nat) : int := match k with 0%nat => 10 | 1%nat => 20 | 2%nat => 30 | _ => 40 end.\n')
addA('zq_list_nth_table', "", 'lookup tbl 3 + List.nth 4 tbl 0 + fold_right PrimInt63.add 0 tbl',
     'Definition tbl : list int := 3 :: 1 :: 4 :: 1 :: 5 :: 9 :: 2 :: 6 :: nil.\nFixpoint lookup (l : list int) (i : nat) : int := match l, i with nil, _ => 0 | x :: _, O => x | _ :: r, S j => lookup r j end.\n')
addA('zq_fnv_u64', "", 'let r := fnv n a (u64_of_halves 3421674724 2216829733) s in w_lo r',
     'Fixpoint fnv (k : nat) (i : int) (h : u64) (t : mem) : u64 :=\n  match k with\n  | O => h\n  | S m => fnv m (i + 1) (u64_mul (u64_xor h (u64_of_int (rd8 0 i t))) (u64_of_halves 256 435)) t\n  end.\n')
addA('zq_early_exit_fold', "", 'match findf n a (fun i => rd 0 i s =? b) with Some i => i | None => 0 - 1 end',
     'Fixpoint findf (k : nat) (i : int) (p : int -> bool) : option int :=\n  match k with O => None | S m => if p i then Some i else findf m (i + 1) p end.\n')
addA('zq_acc_record_fold', "", 'let z := scan n a (mks 1000000 0) s in mx z - mn z',
     'Record st2 := mks { mn : int; mx : int }.\nDefinition upd_st (z : st2) (v : int) : st2 := mks (if v <? mn z then v else mn z) (if mx z <? v then v else mx z).\nFixpoint scan (k : nat) (i : int) (z : st2) (t : mem) : st2 := match k with O => z | S m => scan m (i + 1) (upd_st z (rd 0 i t)) t end.\n')
addA('zq_pair_ret_nontail', "", 'let (l, h0) := minmax n a s in h0 - l',
     'Fixpoint minmax (k : nat) (i : int) (t : mem) : int * int :=\n  match k with\n  | O => (1000000, 0)\n  | S m => let (lo, hi) := minmax m (i + 1) t in let v := rd 0 i t in (if v <? lo then v else lo, if hi <? v then v else hi)\n  end.\n')
# tests that cannot be moves, many in one expression (step 86)
addA('ze_mod_8', "", '(a + 0) mod (b + 1) + (a + 1) mod (b + 1) + (a + 2) mod (b + 1) + (a + 3) mod (b + 1) + (a + 4) mod (b + 1) + (a + 5) mod (b + 1) + (a + 6) mod (b + 1) + (a + 7) mod (b + 1)',
     '')
addA('ze_mod_5', "", '(a + 0) mod (b + 1) + (a + 1) mod (b + 1) + (a + 2) mod (b + 1) + (a + 3) mod (b + 1) + (a + 4) mod (b + 1)',
     '')
addA('ze_div_8', "", '(a + 0) / (b + 1) + (a + 1) / (b + 1) + (a + 2) / (b + 1) + (a + 3) / (b + 1) + (a + 4) / (b + 1) + (a + 5) / (b + 1) + (a + 6) / (b + 1) + (a + 7) / (b + 1)',
     '')
addA('ze_mod_16', "", '(a + 0) mod (b + 1) + (a + 1) mod (b + 1) + (a + 2) mod (b + 1) + (a + 3) mod (b + 1) + (a + 4) mod (b + 1) + (a + 5) mod (b + 1) + (a + 6) mod (b + 1) + (a + 7) mod (b + 1) + (a + 8) mod (b + 1) + (a + 9) mod (b + 1) + (a + 10) mod (b + 1) + (a + 11) mod (b + 1) + (a + 12) mod (b + 1) + (a + 13) mod (b + 1) + (a + 14) mod (b + 1) + (a + 15) mod (b + 1)',
     '')
addA('ze_if_call_8', "", '(if a =? 0 then g 3 b else hh b) + (if a =? 1 then g 3 b else hh b) + (if a =? 2 then g 3 b else hh b) + (if a =? 3 then g 3 b else hh b) + (if a =? 4 then g 3 b else hh b) + (if a =? 5 then g 3 b else hh b) + (if a =? 6 then g 3 b else hh b) + (if a =? 7 then g 3 b else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_if_call_5', "", '(if a =? 0 then g 3 b else hh b) + (if a =? 1 then g 3 b else hh b) + (if a =? 2 then g 3 b else hh b) + (if a =? 3 then g 3 b else hh b) + (if a =? 4 then g 3 b else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_if_call_12', "", '(if a =? 0 then g 3 b else hh b) + (if a =? 1 then g 3 b else hh b) + (if a =? 2 then g 3 b else hh b) + (if a =? 3 then g 3 b else hh b) + (if a =? 4 then g 3 b else hh b) + (if a =? 5 then g 3 b else hh b) + (if a =? 6 then g 3 b else hh b) + (if a =? 7 then g 3 b else hh b) + (if a =? 8 then g 3 b else hh b) + (if a =? 9 then g 3 b else hh b) + (if a =? 10 then g 3 b else hh b) + (if a =? 11 then g 3 b else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_arg_8', "", 'sum8 (if a =? 0 then g 3 b else hh b) (if a =? 1 then g 3 b else hh b) (if a =? 2 then g 3 b else hh b) (if a =? 3 then g 3 b else hh b) (if a =? 4 then g 3 b else hh b) (if a =? 5 then g 3 b else hh b) (if a =? 6 then g 3 b else hh b) (if a =? 7 then g 3 b else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\nDefinition sum8 (x0 x1 x2 x3 x4 x5 x6 x7 : int) : int := x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7.\n')
addA('ze_record_8', "", 'e3 (mk8 (if a =? 0 then g 3 b else hh b) (if a =? 1 then g 3 b else hh b) (if a =? 2 then g 3 b else hh b) (if a =? 3 then g 3 b else hh b) (if a =? 4 then g 3 b else hh b) (if a =? 5 then g 3 b else hh b) (if a =? 6 then g 3 b else hh b) (if a =? 7 then g 3 b else hh b))',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\nRecord r8 := mk8 { e0 : int; e1 : int; e2 : int; e3 : int; e4 : int; e5 : int; e6 : int; e7 : int }.\n')
addA('ze_let_8', "", 'let x0 := if a =? 0 then g 3 b else hh b in let x1 := if a =? 1 then g 3 x0 else hh x0 in let x2 := if a =? 2 then g 3 x1 else hh x1 in let x3 := if a =? 3 then g 3 x2 else hh x2 in let x4 := if a =? 4 then g 3 x3 else hh x3 in let x5 := if a =? 5 then g 3 x4 else hh x4 in let x6 := if a =? 6 then g 3 x5 else hh x5 in let x7 := if a =? 7 then g 3 x6 else hh x6 in x7 + x0',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_match_counter_8', "", '(match n with O => g 3 b | S _ => hh b end) + (match n with O => g 3 b | S _ => hh b end) + (match n with O => g 3 b | S _ => hh b end) + (match n with O => g 3 b | S _ => hh b end) + (match n with O => g 3 b | S _ => hh b end) + (match n with O => g 3 b | S _ => hh b end) + (match n with O => g 3 b | S _ => hh b end) + (match n with O => g 3 b | S _ => hh b end)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_reads_8', "", '(if rd 0 0 s =? 0 then g 3 (rd 1 0 s) else hh b) + (if rd 0 1 s =? 0 then g 3 (rd 1 1 s) else hh b) + (if rd 0 2 s =? 0 then g 3 (rd 1 2 s) else hh b) + (if rd 0 3 s =? 0 then g 3 (rd 1 3 s) else hh b) + (if rd 0 4 s =? 0 then g 3 (rd 1 4 s) else hh b) + (if rd 0 5 s =? 0 then g 3 (rd 1 5 s) else hh b) + (if rd 0 6 s =? 0 then g 3 (rd 1 6 s) else hh b) + (if rd 0 7 s =? 0 then g 3 (rd 1 7 s) else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_counter_8', "", '(if a =? 0 then g n b else hh b) + (if a =? 1 then g n b else hh b) + (if a =? 2 then g n b else hh b) + (if a =? 3 then g n b else hh b) + (if a =? 4 then g n b else hh b) + (if a =? 5 then g n b else hh b) + (if a =? 6 then g n b else hh b) + (if a =? 7 then g n b else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_bool_var_8', "", 'let t := a <? b in (if t then g 3 (b + 0) else hh b) + (if t then g 3 (b + 1) else hh b) + (if t then g 3 (b + 2) else hh b) + (if t then g 3 (b + 3) else hh b) + (if t then g 3 (b + 4) else hh b) + (if t then g 3 (b + 5) else hh b) + (if t then g 3 (b + 6) else hh b) + (if t then g 3 (b + 7) else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_record_var_8', "", 'use (mkpp a b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\nRecord pp := mkpp { p0 : int; p1z : int }.\nDefinition use (r : pp) : int := (if p0 r =? 0 then g 3 (p1z r) else hh (p1z r)) + (if p0 r =? 1 then g 3 (p1z r) else hh (p1z r)) + (if p0 r =? 2 then g 3 (p1z r) else hh (p1z r)) + (if p0 r =? 3 then g 3 (p1z r) else hh (p1z r)) + (if p0 r =? 4 then g 3 (p1z r) else hh (p1z r)) + (if p0 r =? 5 then g 3 (p1z r) else hh (p1z r)) + (if p0 r =? 6 then g 3 (p1z r) else hh (p1z r)) + (if p0 r =? 7 then g 3 (p1z r) else hh (p1z r)).\n')
addA('ze_nested_8', "", '(if a =? 0 then (if b =? 0 then g 3 a else hh a) else hh b) + (if a =? 1 then (if b =? 1 then g 3 a else hh a) else hh b) + (if a =? 2 then (if b =? 2 then g 3 a else hh a) else hh b) + (if a =? 3 then (if b =? 3 then g 3 a else hh a) else hh b) + (if a =? 4 then (if b =? 4 then g 3 a else hh a) else hh b) + (if a =? 5 then (if b =? 5 then g 3 a else hh a) else hh b) + (if a =? 6 then (if b =? 6 then g 3 a else hh a) else hh b) + (if a =? 7 then (if b =? 7 then g 3 a else hh a) else hh b)',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\n')
addA('ze_in_helper', "", 'many a b + many b a',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\nDefinition many (a b : int) : int := (if a =? 0 then g 3 b else hh b) + (if a =? 1 then g 3 b else hh b) + (if a =? 2 then g 3 b else hh b) + (if a =? 3 then g 3 b else hh b) + (if a =? 4 then g 3 b else hh b) + (if a =? 5 then g 3 b else hh b) + (if a =? 6 then g 3 b else hh b) + (if a =? 7 then g 3 b else hh b).\n')
addA('ze_in_rec', "", 'lp n a b',
     'Fixpoint g (k : nat) (x : int) : int := match k with O => x | S m => g m (x + 1) end.\nDefinition hh (x : int) : int := x * 2.\nFixpoint lp (k : nat) (a b : int) : int := match k with O => a | S m => lp m ((if a =? 0 then g 3 b else hh b) + (if a =? 1 then g 3 b else hh b) + (if a =? 2 then g 3 b else hh b) + (if a =? 3 then g 3 b else hh b) + (if a =? 4 then g 3 b else hh b) + (if a =? 5 then g 3 b else hh b) + (if a =? 6 then g 3 b else hh b) + (if a =? 7 then g 3 b else hh b)) b end.\n')
addA('ze_own_call_8', "", 'lp n a',
     'Fixpoint lp (k : nat) (a : int) : int := match k with O => a | S m => (if a =? 0 then lp m a else a) + (if a =? 1 then lp m a else a) + (if a =? 2 then lp m a else a) + (if a =? 3 then lp m a else a) + (if a =? 4 then lp m a else a) + (if a =? 5 then lp m a else a) + (if a =? 6 then lp m a else a) + (if a =? 7 then lp m a else a) end.\n')
addA('ze_own_call_12', "", 'lp n a',
     'Fixpoint lp (k : nat) (a : int) : int := match k with O => a | S m => (if a =? 0 then lp m a else a) + (if a =? 1 then lp m a else a) + (if a =? 2 then lp m a else a) + (if a =? 3 then lp m a else a) + (if a =? 4 then lp m a else a) + (if a =? 5 then lp m a else a) + (if a =? 6 then lp m a else a) + (if a =? 7 then lp m a else a) + (if a =? 8 then lp m a else a) + (if a =? 9 then lp m a else a) + (if a =? 10 then lp m a else a) + (if a =? 11 then lp m a else a) end.\n')
addA('ze_writes_8', "", 'let t := upd 0 a b s in (if a =? 0 then wr a t / 2 else b) + (if a =? 1 then wr a t / 2 else b) + (if a =? 2 then wr a t / 2 else b) + (if a =? 3 then wr a t / 2 else b) + (if a =? 4 then wr a t / 2 else b) + (if a =? 5 then wr a t / 2 else b) + (if a =? 6 then wr a t / 2 else b) + (if a =? 7 then wr a t / 2 else b)',
     'Definition wr (i : int) (t : mem) : int := rd 0 i t.\n')
addA('ze_mat', "", 'x12 (pw n (mk2 1 1 1 0) (mk2 1 0 0 1) a 1000007)',
     'Record m2 := mk2 { x11 : int; x12 : int; x21 : int; x22 : int }.\nDefinition mm (x y : m2) (p : int) : m2 := mk2 ((x11 x * x11 y + x12 x * x21 y) mod p) ((x11 x * x12 y + x12 x * x22 y) mod p) ((x21 x * x11 y + x22 x * x21 y) mod p) ((x21 x * x12 y + x22 x * x22 y) mod p).\nFixpoint pw (k : nat) (x r : m2) (e p : int) : m2 := match k with O => r | S m => pw m (mm x x p) (if (e land 1) =? 1 then mm r x p else r) (e >> 1) p end.\n')
addA('ze_zdiv_in_test', "", 'if ((a + 0) mod (b + 1) + (a + 1) mod (b + 1) + (a + 2) mod (b + 1) + (a + 3) mod (b + 1) + (a + 4) mod (b + 1) + (a + 5) mod (b + 1) + (a + 6) mod (b + 1) + (a + 7) mod (b + 1)) <? 3 then a else b',
     '')
# what a fifth probe found (step 85)
addA('zd_h_opt_pair', "", 'match alloc s with (Some p, t) => rd 0 0 t + p | (None, _) => 0 end',
     'Definition alloc (t : mem) : option int * mem :=\n  let h := rd 0 0 t in\n  if h =? 0 then (None, t) else (Some h, upd 0 0 (rd 0 h t) t).\n')
addA('zd_h_opt_pair_after', "", 'match alloc s with (o, t) => match o with Some p => rd 0 p t | None => rd 0 0 t end end',
     'Definition alloc (t : mem) : option int * mem :=\n  let h := rd 0 0 t in\n  if h =? 0 then (None, t) else (Some h, upd 0 0 (rd 0 h t) t).\n')
addA('zd_h_two', "", 'match alloc s with (Some p, t) => match alloc t with (Some q, u) => p + q + rd 0 0 u | (None, u) => p + rd 0 0 u end | (None, _) => 0 end',
     'Definition alloc (t : mem) : option int * mem :=\n  let h := rd 0 0 t in\n  if h =? 0 then (None, t) else (Some h, upd 0 0 (rd 0 h t) t).\n')
addA('zd_h_in_rec', "", 'lp n 0 s',
     'Definition alloc (t : mem) : option int * mem :=\n  let h := rd 0 0 t in\n  if h =? 0 then (None, t) else (Some h, upd 0 0 (rd 0 h t) t).\nFixpoint lp (k : nat) (acc : int) (t : mem) : int := match k with O => acc | S m => match alloc t with (Some p, u) => lp m (acc + p) u | (None, _) => acc end end.\n')
addA('zd_h_record', "", 'match step0 (mkst a 0) s with (x, t) => acc0 x + rd 1 a t end',
     'Record st := mkst { pc : int; acc0 : int }.\nDefinition step0 (x : st) (t : mem) : st * mem :=\n  let op := rd 0 (pc x) t in\n  if op =? 0 then (x, t)\n  else if op =? 1 then (mkst (pc x + 1) (acc0 x + 1), upd 1 (pc x) 1 t)\n  else (mkst (pc x + 2) (acc0 x), t).\n')
addA('zd_h_record_rec', "", 'match run n (mkst a 0) s with (x, _) => acc0 x end',
     'Record st := mkst { pc : int; acc0 : int }.\nDefinition step0 (x : st) (t : mem) : st * mem :=\n  let op := rd 0 (pc x) t in\n  if op =? 0 then (x, t)\n  else if op =? 1 then (mkst (pc x + 1) (acc0 x + 1), upd 1 (pc x) 1 t)\n  else (mkst (pc x + 2) (acc0 x), t).\nFixpoint run (k : nat) (x : st) (t : mem) : st * mem := match k with O => (x, t) | S m => let (y, u) := step0 x t in run m y u end.\n')
addA('zd_h_record_rec_write', "", 'match run n (mkst a 0) s with (x, t) => acc0 x + rd 1 0 t end',
     'Record st := mkst { pc : int; acc0 : int }.\nDefinition step0 (x : st) (t : mem) : st * mem :=\n  let op := rd 0 (pc x) t in\n  if op =? 0 then (x, t)\n  else if op =? 1 then (mkst (pc x + 1) (acc0 x + 1), upd 1 (pc x) 1 t)\n  else (mkst (pc x + 2) (acc0 x), t).\nFixpoint run (k : nat) (x : st) (t : mem) : st * mem := match k with O => (x, t) | S m => let (y, u) := step0 x t in run m y (upd 1 0 (pc y) u) end.\n')
addA('zd_h_long_tail', "", 'use s',
     'Definition alloc (t : mem) : option int * mem :=\n  let h := rd 0 0 t in\n  if h =? 0 then (None, t) else (Some h, upd 0 0 (rd 0 h t) t).\nDefinition big (x : int) : int := x * x + x * 2 + 1.\nDefinition use (t : mem) : int := match alloc t with (Some p, u) => big p + big (p + 1) + big (p + 2) + big (p + 3) + rd 0 p u | (None, u) => rd 0 0 u end.\n')
addA('zd_o_helper', "", 'match push a s with Some t => rd 0 1 t | None => 0 end',
     'Definition push (v : int) (t : mem) : option mem :=\n  let tl := rd 0 1 t in\n  if tl =? 9 then None else Some (upd 0 1 (tl + 1) (upd 1 tl v t)).\n')
addA('zd_o_helper_seq', "", 'match push a s with Some t => match push b t with Some u => rd 0 1 u | None => 1 end | None => 0 end',
     'Definition push (v : int) (t : mem) : option mem :=\n  let tl := rd 0 1 t in\n  if tl =? 9 then None else Some (upd 0 1 (tl + 1) (upd 1 tl v t)).\n')
addA('zd_o_helper_rec', "", 'rd 0 1 (fill n a s)',
     'Definition push (v : int) (t : mem) : option mem :=\n  let tl := rd 0 1 t in\n  if tl =? 9 then None else Some (upd 0 1 (tl + 1) (upd 1 tl v t)).\nFixpoint fill (k : nat) (v : int) (t : mem) : mem := match k with O => t | S m => match push v t with Some u => fill m (v + 1) u | None => t end end.\n')
addA('zd_o_helper_rec_ctl', "", 'fill n a s',
     'Definition push (v : int) (t : mem) : option mem :=\n  let tl := rd 0 1 t in\n  if tl =? 9 then None else Some (upd 0 1 (tl + 1) (upd 1 tl v t)).\nFixpoint fill (k : nat) (v : int) (t : mem) : int := match k with O => v | S m => match push v t with Some u => fill m (v + 1) u | None => v end end.\n')
addA('zd_o_helper_pair', "", 'match pop s with Some (v, t) => v + rd 0 1 t | None => 0 end',
     'Definition pop (t : mem) : option (int * mem) :=\n  let tl := rd 0 1 t in\n  if tl =? 0 then None else Some (rd 1 (tl - 1) t, upd 0 1 (tl - 1) t).\n')
addA('zd_o_helper_none_old', "", 'match push a s with Some t => rd 0 1 t | None => rd 0 0 s end',
     'Definition push (v : int) (t : mem) : option mem :=\n  let tl := rd 0 1 t in\n  if tl =? 9 then None else Some (upd 0 1 (tl + 1) (upd 1 tl v t)).\n')
addA('zd_o_old_after_some', "", 'match push a s with Some t => rd 0 1 t + rd 0 1 s | None => 0 end',
     'Definition push (v : int) (t : mem) : option mem :=\n  let tl := rd 0 1 t in\n  if tl =? 9 then None else Some (upd 0 1 (tl + 1) (upd 1 tl v t)).\n')
addA('zd_r_mem', "", 'match lp n a s with Some t => rd 0 a t | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option mem :=\n  match k with O => Some t | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_r_value_mem', "", 'match lp n a s with Some (v, t) => v + rd 0 a t | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_r_after_call', "", 'match lp n a s with Some (v, t) => v + rd 0 a t | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => match lp m (i + 1) t with Some (v, u) => Some (v + 1, upd 0 i v u) | None => None end end.\n')
addA('zd_r_mem_after_call', "", 'match lp n a s with Some t => rd 0 a t | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option mem :=\n  match k with O => Some t | S m => match lp m (i + 1) t with Some u => Some (upd 0 i i u) | None => None end end.\n')
addA('zd_r_default', "", 'match lp n a s with Some (v, _) => v | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => match lp m (i + 1) t with Some (v, u) => Some (v, u) | None => Some (0, t) end end.\n')
addA('zd_r_none_mem_used', "", 'match lp n a s with Some (v, _) => v | None => rd 0 0 s end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_r_ignored_mem', "", 'match lp n a s with Some (v, _) => v | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_r_record_value', "", 'match lp n a s with Some (v, t) => p1a v + p2a v + rd 0 a t | None => 0 end',
     'Record pr := mkpr { p1a : int; p2a : int }.\nFixpoint lp (k : nat) (i : int) (t : mem) : option (pr * mem) :=\n  match k with O => Some (mkpr i i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_r_counter_second', "", 'match lp a n s with Some (v, t) => v + rd 0 a t | None => 0 end',
     'Fixpoint lp (i : int) (k : nat) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp (i + 1) m (upd 0 i 1 t) end.\n')
addA('zd_r_mem_first', "", 'match lp s n a with Some (v, t) => v + rd 0 a t | None => 0 end',
     'Fixpoint lp (t : mem) (k : nat) (i : int) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp (upd 0 i 1 t) m (i + 1) end.\n')
addA('zd_r_reads_only', "", 'match lp n a s with Some (v, t) => v + rd 0 a t | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (rd 0 i t, t) | S m => if rd 0 i t =? 0 then None else lp m (i + 1) t end.\n')
addA('zd_r_two_funcs', "", 'match lq n a s with Some (v, t) => v + rd 0 a t | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\nFixpoint lq (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => lp 2 i t | S m => match lq m i t with Some (v, u) => Some (v + 1, u) | None => None end end.\n')
addA('zd_r_in_number_fn', "", 'outer n a s',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\nFixpoint outer (j : nat) (x : int) (t : mem) : int :=\n  match j with O => x | S m => match lp 2 x t with Some (v, u) => outer m (x + v) u | None => x end end.\n')
addA('zd_r_let', "", 'let r := lp n a s in match r with Some (v, _) => v | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_r_given_on', "", 'match lp n a s with Some (v, t) => match lp n v t with Some (w, u) => w + rd 0 a u | None => 1 end | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * mem) :=\n  match k with O => Some (i, t) | S m => if i =? 7 then None else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_m_copy', "", 'match copy n a b s with Some (_, t) => rd 0 b t | None => 0 end',
     'Definition M (A : Type) := mem -> option (A * mem).\nDefinition ret {A} (x : A) : M A := fun t => Some (x, t).\nDefinition bind {A B} (m : M A) (f : A -> M B) : M B := fun t => match m t with Some (x, u) => f x u | None => None end.\nDefinition fail {A} : M A := fun _ => None.\nDefinition rdc (i : int) : M int := fun t => if i <? 16 then Some (rd 0 i t, t) else None.\nDefinition wrc (i v : int) : M unit := fun t => if i <? 16 then Some (tt, upd 0 i v t) else None.\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint copy (k : nat) (i j : int) : M unit :=\n  match k with O => ret tt | S m => v <- rdc i ;; _u <- wrc j v ;; copy m (i + 1) (j + 1) end.\n')
addA('zd_m_sum', "", 'match sum n a s with Some (x, _) => x | None => 0 end',
     'Definition M (A : Type) := mem -> option (A * mem).\nDefinition ret {A} (x : A) : M A := fun t => Some (x, t).\nDefinition bind {A B} (m : M A) (f : A -> M B) : M B := fun t => match m t with Some (x, u) => f x u | None => None end.\nDefinition fail {A} : M A := fun _ => None.\nDefinition rdc (i : int) : M int := fun t => if i <? 16 then Some (rd 0 i t, t) else None.\nDefinition wrc (i v : int) : M unit := fun t => if i <? 16 then Some (tt, upd 0 i v t) else None.\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint sum (k : nat) (i : int) : M int :=\n  match k with O => ret 0 | S m => v <- rdc i ;; r <- sum m (i + 1) ;; ret (v + r) end.\n')
addA('zd_m_fail', "", 'match chk n a s with Some (x, _) => x | None => 0 end',
     'Definition M (A : Type) := mem -> option (A * mem).\nDefinition ret {A} (x : A) : M A := fun t => Some (x, t).\nDefinition bind {A B} (m : M A) (f : A -> M B) : M B := fun t => match m t with Some (x, u) => f x u | None => None end.\nDefinition fail {A} : M A := fun _ => None.\nDefinition rdc (i : int) : M int := fun t => if i <? 16 then Some (rd 0 i t, t) else None.\nDefinition wrc (i v : int) : M unit := fun t => if i <? 16 then Some (tt, upd 0 i v t) else None.\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint chk (k : nat) (i : int) : M int :=\n  match k with O => ret i | S m => v <- rdc i ;; if v =? 0 then fail else chk m (i + 1) end.\n')
addA('zd_m_helper', "", 'match two a s with Some (x, _) => x | None => 0 end',
     'Definition M (A : Type) := mem -> option (A * mem).\nDefinition ret {A} (x : A) : M A := fun t => Some (x, t).\nDefinition bind {A B} (m : M A) (f : A -> M B) : M B := fun t => match m t with Some (x, u) => f x u | None => None end.\nDefinition fail {A} : M A := fun _ => None.\nDefinition rdc (i : int) : M int := fun t => if i <? 16 then Some (rd 0 i t, t) else None.\nDefinition wrc (i v : int) : M unit := fun t => if i <? 16 then Some (tt, upd 0 i v t) else None.\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition two (i : int) : M int := x <- rdc i ;; y <- rdc (i + 1) ;; ret (x + y).\n')
addA('zd_m_helper_rec', "", 'match sum n a s with Some (x, _) => x | None => 0 end',
     'Definition M (A : Type) := mem -> option (A * mem).\nDefinition ret {A} (x : A) : M A := fun t => Some (x, t).\nDefinition bind {A B} (m : M A) (f : A -> M B) : M B := fun t => match m t with Some (x, u) => f x u | None => None end.\nDefinition fail {A} : M A := fun _ => None.\nDefinition rdc (i : int) : M int := fun t => if i <? 16 then Some (rd 0 i t, t) else None.\nDefinition wrc (i v : int) : M unit := fun t => if i <? 16 then Some (tt, upd 0 i v t) else None.\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition two (i : int) : M int := x <- rdc i ;; y <- rdc (i + 1) ;; ret (x + y).\nFixpoint sum (k : nat) (i : int) : M int :=\n  match k with O => ret 0 | S m => v <- two i ;; r <- sum m (i + 2) ;; ret (v + r) end.\n')
addA('zd_m_unit', "", 'match fill n a b s with Some (_, t) => rd 0 a t | None => 0 end',
     'Definition M (A : Type) := mem -> option (A * mem).\nDefinition ret {A} (x : A) : M A := fun t => Some (x, t).\nDefinition bind {A B} (m : M A) (f : A -> M B) : M B := fun t => match m t with Some (x, u) => f x u | None => None end.\nDefinition fail {A} : M A := fun _ => None.\nDefinition rdc (i : int) : M int := fun t => if i <? 16 then Some (rd 0 i t, t) else None.\nDefinition wrc (i v : int) : M unit := fun t => if i <? 16 then Some (tt, upd 0 i v t) else None.\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint fill (k : nat) (i v : int) : M unit :=\n  match k with O => ret tt | S m => _u <- wrc i v ;; fill m (i + 1) v end.\n')
addA('zd_c_helper_dec', "", 'if same n n then a else b',
     'Class EqD (T : Type) := { dec : forall x y : T, {x = y} + {x <> y} }.\n#[export] Instance eq_nat : EqD nat := { dec := Nat.eq_dec }.\nDefinition same {T} `{EqD T} (x y : T) : bool := if dec x y then true else false.\n')
addA('zd_c_helper_num', "", 'dbl a + dbl b',
     'Class Sz (T : Type) := { sz : T -> int }.\n#[export] Instance s_int : Sz int := { sz := fun x => x + 1 }.\nDefinition dbl {T} `{Sz T} (x : T) : int := sz x * 2.\n')
addA('zd_c_helper_helper', "", 'qd a',
     'Class Sz (T : Type) := { sz : T -> int }.\n#[export] Instance s_int : Sz int := { sz := fun x => x + 1 }.\nDefinition dbl {T} `{Sz T} (x : T) : int := sz x * 2.\nDefinition qd {T} `{Sz T} (x : T) : int := dbl x * 2.\n')
addA('zd_d_res', "", 'match stepr a s with Ok v t => v + rd 0 a t | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nDefinition stepr (i : int) (t : mem) : res := if i =? 0 then Err 1 else Ok i (upd 0 i i t).\n')
addA('zd_d_res_rec', "", 'match lp n a s with Ok v t => v + rd 0 a t | Err e => e end',
     'Inductive res := Ok (v : int) (t : mem) | Err (e : int).\nFixpoint lp (k : nat) (i : int) (t : mem) : res := match k with O => Ok i t | S m => if i =? 7 then Err i else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zd_d_sum_rec', "", 'match lp n a s with inr (v, t) => v + rd 0 a t | inl e => e end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : int + (int * mem) := match k with O => inr (i, t) | S m => if i =? 7 then inl i else lp m (i + 1) (upd 0 i 1 t) end.\n')
addA('zp_kv_probe', "", 'let c := mkcfg 64 0 in let t := ins n c (slot c a) a b s in match find n c (slot c a) a t with Some v => v | None => 0 end',
     'Record cfg := mkcfg { size : int; empty : int }.\nDefinition slot (c : cfg) (k : int) : int := k mod size c.\nFixpoint find (fuel : nat) (c : cfg) (i k : int) (t : mem) : option int :=\n  match fuel with\n  | O => None\n  | S f =>\n      let v := rd 0 i t in\n      if v =? k then Some (rd 1 i t)\n      else if v =? empty c then None\n      else find f c ((i + 1) mod size c) k t\n  end.\nFixpoint ins (fuel : nat) (c : cfg) (i k v : int) (t : mem) : mem :=\n  match fuel with\n  | O => t\n  | S f =>\n      let u := rd 0 i t in\n      if orb (u =? empty c) (u =? k) then upd 1 i v (upd 0 i k t)\n      else ins f c ((i + 1) mod size c) k v t\n  end.\n')
addA('zp_alloc', "", 'match alloc s with (Some p, t) => rd 0 0 (free p t) + p | (None, _) => 0 end',
     'Definition head : int := 0.\nDefinition alloc (t : mem) : option int * mem :=\n  let h := rd 0 head t in\n  if h =? 0 then (None, t) else (Some h, upd 0 head (rd 0 h t) t).\nDefinition free (p : int) (t : mem) : mem := upd 0 head p (upd 0 p (rd 0 head t) t).\n')
addA('zp_tokenizer', "", 'eval_all n a 0 s',
     'Inductive tok := TNum (v : int) | TPlus | TEnd | TBad.\nDefinition is_digit (c : int) : bool := (48 <=? c) && (c <=? 57).\nFixpoint num (k : nat) (i acc : int) (t : mem) : int * int :=\n  match k with\n  | O => (acc, i)\n  | S m => let c := rd8 0 i t in\n           if is_digit c then num m (i + 1) (acc * 10 + (c - 48)) t else (acc, i)\n  end.\nDefinition next (k : nat) (i : int) (t : mem) : tok * int :=\n  let c := rd8 0 i t in\n  if is_digit c then let (v, j) := num k i 0 t in (TNum v, j)\n  else if c =? 43 then (TPlus, i + 1)\n  else if c =? 0 then (TEnd, i)\n  else (TBad, i).\nFixpoint eval_all (k : nat) (i acc : int) (t : mem) : int :=\n  match k with\n  | O => acc\n  | S m => match next 10 i t with\n           | (TNum v, j) => eval_all m j (acc + v) t\n           | (TPlus, j) => eval_all m j acc t\n           | (TEnd, _) => acc\n           | (TBad, _) => 0\n           end\n  end.\n')
addA('zp_stack_vm', "", 'match run n (mkst a 0 0) s with (x, _) => acc x end',
     'Record st := mkst { pc : int; sp : int; acc : int }.\nDefinition step (x : st) (t : mem) : st * mem :=\n  let op := rd 0 (pc x) t in\n  if op =? 0 then (mkst (pc x) (sp x) (acc x), t)\n  else if op =? 1 then (mkst (pc x + 2) (sp x + 1) (acc x), upd 1 (sp x) (rd 0 (pc x + 1) t) t)\n  else if op =? 2 then (mkst (pc x + 1) (sp x - 1) (acc x + rd 1 (sp x - 1) t), t)\n  else (mkst (pc x + 1) (sp x) (acc x), t).\nFixpoint run (k : nat) (x : st) (t : mem) : st * mem :=\n  match k with\n  | O => (x, t)\n  | S m => let (y, u) := step x t in run m y u\n  end.\n')
addA('zp_heap_sift', "", 'rd 0 a (sift n 0 b s)',
     'Fixpoint sift (k : nat) (i len : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m =>\n      let l := 2 * i + 1 in\n      let r := 2 * i + 2 in\n      let c := if (r <? len) && (rd 0 l t <? rd 0 r t) then r else l in\n      if (c <? len) && (rd 0 i t <? rd 0 c t) then\n        sift m c len (upd 0 c (rd 0 i t) (upd 0 i (rd 0 c t) t))\n      else t\n  end.\n')
addA('zp_bfs', "", 'bfs n 0 1 (upd 2 0 a s)',
     'Fixpoint neigh (k : nat) (u e qt : int) (t : mem) : int * mem :=\n  match k with\n  | O => (qt, t)\n  | S m =>\n      let v := rd 0 e t in\n      if v =? 0 then (qt, t)\n      else if rd 1 v t =? 0 then neigh m u (e + 1) (qt + 1) (upd 2 qt v (upd 1 v 1 t))\n      else neigh m u (e + 1) qt t\n  end.\nFixpoint bfs (k : nat) (qh qt : int) (t : mem) : int :=\n  match k with\n  | O => qt\n  | S m =>\n      if qh <? qt then\n        let u := rd 2 qh t in\n        let (qt2, t2) := neigh 8 u (rd 3 u t) qt t in\n        bfs m (qh + 1) qt2 t2\n      else qt\n  end.\n')
addA('zp_bignum_add', "", 'fst (add_limbs n a 0 s)',
     'Fixpoint add_limbs (k : nat) (i c : int) (t : mem) : int * mem :=\n  match k with\n  | O => (c, t)\n  | S m =>\n      let x := rd 0 i t in\n      let y := rd 1 i t in\n      let r := x + y + c in\n      let c2 := if (r <? x) || (r <? y) then 1 else 0 in\n      add_limbs m (i + 1) c2 (upd 2 i r t)\n  end.\n')
addA('zp_crc', "", 'crc n a 255 s',
     'Definition tbl (i : int) (t : mem) : int := rd 0 (i land 255) t.\nFixpoint crc (k : nat) (i c : int) (t : mem) : int :=\n  match k with\n  | O => c lxor 255\n  | S m => crc m (i + 1) ((c >> 8) lxor tbl ((c lxor rd8 1 i t) land 255) t) t\n  end.\n')
addA('zp_mat_pow', "", 'a12 (mpow n (mk2 1 1 1 0) (mk2 1 0 0 1) a 1000007)',
     'Record m2 := mk2 { a11 : int; a12 : int; a21 : int; a22 : int }.\nDefinition mmul (x y : m2) (p : int) : m2 :=\n  mk2 ((a11 x * a11 y + a12 x * a21 y) mod p) ((a11 x * a12 y + a12 x * a22 y) mod p)\n      ((a21 x * a11 y + a22 x * a21 y) mod p) ((a21 x * a12 y + a22 x * a22 y) mod p).\nFixpoint mpow (k : nat) (x r : m2) (e p : int) : m2 :=\n  match k with\n  | O => r\n  | S m => mpow m (mmul x x p) (if (e land 1) =? 1 then mmul r x p else r) (e >> 1) p\n  end.\n')
addA('zp_class_num', "", 'horner n a 0 zero s + re (horner n (mkcx a b) 0 zero s)',
     'Class Num (T : Type) := { zero : T; add : T -> T -> T; mul : T -> T -> T; of_i : int -> T }.\n#[export] Instance num_int : Num int := { zero := 0; add := PrimInt63.add; mul := PrimInt63.mul; of_i := fun x => x }.\nRecord cx := mkcx { re : int; im : int }.\n#[export] Instance num_cx : Num cx := { zero := mkcx 0 0; add := fun x y => mkcx (re x + re y) (im x + im y);\n   mul := fun x y => mkcx (re x * re y - im x * im y) (re x * im y + im x * re y); of_i := fun x => mkcx x 0 }.\nFixpoint horner {T} `{Num T} (k : nat) (x : T) (i : int) (acc : T) (t : mem) : T :=\n  match k with\n  | O => acc\n  | S m => horner m x (i + 1) (add (mul acc x) (of_i (rd 0 i t))) t\n  end.\n')
addA('zp_date', "", 'total n Jan a',
     'Inductive month := Jan | Feb | Mar | Apr | May | Jun | Jul | Aug | Sep | Oct | Nov | Dec.\nDefinition leap (y : int) : bool := ((y mod 4 =? 0) && negb (y mod 100 =? 0)) || (y mod 400 =? 0).\nDefinition days (m : month) (y : int) : int :=\n  match m with\n  | Feb => if leap y then 29 else 28\n  | Apr | Jun | Sep | Nov => 30\n  | _ => 31\n  end.\nDefinition nextm (m : month) : month :=\n  match m with Jan => Feb | Feb => Mar | Mar => Apr | Apr => May | May => Jun | Jun => Jul | Jul => Aug | Aug => Sep | Sep => Oct | Oct => Nov | Nov => Dec | Dec => Jan end.\nFixpoint total (k : nat) (m : month) (y : int) : int :=\n  match k with\n  | O => 0\n  | S r => days m y + total r (nextm m) y\n  end.\n')
addA('zp_qsort', "", 'rd 0 a (qs n 0 b s)',
     'Fixpoint part (k : nat) (i j p : int) (t : mem) : int * mem :=\n  match k with\n  | O => (i, t)\n  | S m =>\n      if rd 0 j t <? p then\n        part m (i + 1) (j + 1) p (upd 0 i (rd 0 j t) (upd 0 j (rd 0 i t) t))\n      else part m i (j + 1) p t\n  end.\nFixpoint qs (fuel : nat) (lo hi : int) (t : mem) : mem :=\n  match fuel with\n  | O => t\n  | S f =>\n      if hi - lo <=? 1 then t else\n      let p := rd 0 (hi - 1) t in\n      let (m, u) := part 1000 lo lo p t in\n      qs f (m + 1) hi (qs f lo m u)\n  end.\n')
addA('zp_bytes_cmp', "", 'match cmp n a b s with Eq => 0 | Lt => 1 | Gt => 2 end',
     'Fixpoint cmp (k : nat) (i j : int) (t : mem) : comparison :=\n  match k with\n  | O => Eq\n  | S m =>\n      let x := rd8 0 i t in\n      let y := rd8 0 j t in\n      match PrimInt63.compare x y with\n      | Eq => cmp m (i + 1) (j + 1) t\n      | r => r\n      end\n  end.\n')
addA('zp_driver_ring', "", 'snd (fill n (mkring 0 15) a s)',
     'Record ring := mkring { base : int; mask : int }.\nDefinition push (r : ring) (v : int) (t : mem) : option mem :=\n  let hd := rd 0 0 t in\n  let tl := rd 0 1 t in\n  if (tl + 1) land mask r =? hd then None\n  else Some (upd 0 1 ((tl + 1) land mask r) (upd 1 (base r + tl) v t)).\nFixpoint fill (k : nat) (r : ring) (v : int) (t : mem) : mem * int :=\n  match k with\n  | O => (t, 0)\n  | S m => match push r v t with\n           | Some u => fill m r (v + 1) u\n           | None => (t, v)\n           end\n  end.\n')
addA('zp_sched_policy', "", 'rd 1 a (tick n s)',
     'Record task := mktask { prio : int; left : int }.\nDefinition load (i : int) (t : mem) : task := mktask (rd 0 i t) (rd 1 i t).\nDefinition store (i : int) (x : task) (t : mem) : mem := upd 0 i (prio x) (upd 1 i (left x) t).\nFixpoint best (k : nat) (i bi bp : int) (t : mem) : int :=\n  match k with\n  | O => bi\n  | S m => let x := load i t in\n           if (bp <? prio x) && (0 <? left x) then best m (i + 1) i (prio x) t else best m (i + 1) bi bp t\n  end.\nFixpoint tick (k : nat) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m => let i := best 8 0 0 0 t in\n           let x := load i t in\n           tick m (store i (mktask (prio x) (left x - 1)) t)\n  end.\n')
addA('zp_tree_array', "", 'if mem_tree n 0 a (ins_tree n 0 a s) then 1 else 0',
     'Fixpoint ins_tree (k : nat) (i v : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m =>\n      let u := rd 0 i t in\n      if u =? 0 then upd 0 i v t\n      else if v <? u then ins_tree m (2 * i + 1) v t\n      else ins_tree m (2 * i + 2) v t\n  end.\nFixpoint mem_tree (k : nat) (i v : int) (t : mem) : bool :=\n  match k with\n  | O => false\n  | S m =>\n      let u := rd 0 i t in\n      if u =? 0 then false\n      else if u =? v then true\n      else if v <? u then mem_tree m (2 * i + 1) v t\n      else mem_tree m (2 * i + 2) v t\n  end.\n')
addA('zp_utf8', "", 'count n a 0 s',
     'Definition cont (i : int) (t : mem) : int := rd8 0 i t land 63.\nDefinition decode (i : int) (t : mem) : int * int :=\n  let c := rd8 0 i t in\n  if c <? 128 then (c, 1)\n  else if c <? 224 then (((c land 31) << 6) lor cont (i + 1) t, 2)\n  else if c <? 240 then (((c land 15) << 12) lor (cont (i + 1) t << 6) lor cont (i + 2) t, 3)\n  else (((c land 7) << 18) lor (cont (i + 1) t << 12) lor (cont (i + 2) t << 6) lor cont (i + 3) t, 4).\nFixpoint count (k : nat) (i acc : int) (t : mem) : int :=\n  match k with\n  | O => acc\n  | S m => let (cp, w) := decode i t in count m (i + w) (acc + cp) t\n  end.\n')
addA('zp_base64', "", 'rd8 1 a (go64 n 0 0 s)',
     'Definition enc6 (v : int) : int :=\n  if v <? 26 then v + 65 else if v <? 52 then v + 71 else if v <? 62 then v - 4 else if v =? 62 then 43 else 47.\nFixpoint go64 (k : nat) (i j : int) (t : mem) : mem :=\n  match k with\n  | O => t\n  | S m =>\n      let w := (rd8 0 i t << 16) lor (rd8 0 (i + 1) t << 8) lor rd8 0 (i + 2) t in\n      let t1 := upd8 1 j (enc6 ((w >> 18) land 63)) t in\n      let t2 := upd8 1 (j + 1) (enc6 ((w >> 12) land 63)) t1 in\n      let t3 := upd8 1 (j + 2) (enc6 ((w >> 6) land 63)) t2 in\n      go64 m (i + 3) (j + 4) (upd8 1 (j + 3) (enc6 (w land 63)) t3)\n  end.\n')
addA('zp_mod_functor', "", 'MI.maxr n a 0 s',
     'Module Type ORD. Parameter leb : int -> int -> bool. End ORD.\nModule MaxOf (O : ORD).\n  Fixpoint maxr (k : nat) (i m : int) (t : mem) : int :=\n    match k with\n    | O => m\n    | S r => maxr r (i + 1) (if O.leb m (rd 0 i t) then rd 0 i t else m) t\n    end.\nEnd MaxOf.\nModule IntOrd <: ORD. Definition leb (x y : int) : bool := x <=? y. End IntOrd.\nModule MI := MaxOf IntOrd.\n')
addA('zp_sec_notation', "", 'sumw2 255 n a s',
     'Section Ops.\nContext (w : int).\nLocal Notation "x +++ y" := ((x + y) land w) (at level 50, left associativity).\nFixpoint sumw (k : nat) (i acc : int) (t : mem) : int :=\n  match k with O => acc | S m => sumw m (i + 1) (acc +++ rd 0 i t) t end.\nDefinition sumw2 (k : nat) (i : int) (t : mem) : int := sumw k i 0 t +++ sumw k (i + 1) 0 t.\nEnd Ops.\n')
addA('zp_closure_local', "", 'let f := mk a in f b + f (b + 1)',
     'Definition mk (y : int) : int -> int := fun x => x * y + 1.\n')
addA('zp_closure_rec', "", 'app n (mk a) b',
     'Definition mk (y : int) : int -> int := fun x => x * y + 1.\nFixpoint app (k : nat) (f : int -> int) (x : int) : int := match k with O => x | S m => app m f (f x) end.\n')
addA('zp_state_opt', "", 'match copy n a b s with Some (_, t) => rd 0 b t | None => 0 end',
     'Definition M (A : Type) := mem -> option (A * mem).\nDefinition ret {A} (x : A) : M A := fun t => Some (x, t).\nDefinition bind {A B} (m : M A) (f : A -> M B) : M B := fun t => match m t with Some (x, u) => f x u | None => None end.\nDefinition fail {A} : M A := fun _ => None.\nDefinition rdc (i : int) : M int := fun t => if i <? 16 then Some (rd 0 i t, t) else None.\nDefinition wrc (i v : int) : M unit := fun t => if i <? 16 then Some (tt, upd 0 i v t) else None.\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint copy (k : nat) (i j : int) : M unit :=\n  match k with\n  | O => ret tt\n  | S m => v <- rdc i ;; _u <- wrc j v ;; copy m (i + 1) (j + 1)\n  end.\n')
addA('zp_fold_range', "", 'let r := fold_range n a (mka 0 0) (fun x i => mka (sm x + rd 0 i s) (ct x + 1)) in sm r + ct r',
     'Record acc2 := mka { sm : int; ct : int }.\nFixpoint fold_range {A} (k : nat) (i : int) (x : A) (f : A -> int -> A) : A :=\n  match k with O => x | S m => fold_range m (i + 1) (f x i) f end.\n')
addA('zp_poly_list_lit', "", 'sum_list table + sum_list (List.map (fun x => x + a) table)',
     'Definition sum_list (l : list int) : int := List.fold_left PrimInt63.add l 0.\nDefinition table : list int := 1 :: 2 :: 3 :: 5 :: 8 :: nil.\n')
addA('zp_mutual_mem', "", 'rd 0 a (ev n a s)',
     'Fixpoint ev (k : nat) (i : int) (t : mem) : mem :=\n  match k with O => t | S m => od m (i + 1) (upd 0 i 1 t) end\nwith od (k : nat) (i : int) (t : mem) : mem :=\n  match k with O => t | S m => ev m (i + 1) (upd 0 i 2 t) end.\n')
addA('zp_rec_value_mem', "", 'match minmax n a s with (p, _) => hi p - lo p end',
     'Record pr := mkpr { lo : int; hi : int }.\nFixpoint minmax (k : nat) (i : int) (t : mem) : pr * mem :=\n  match k with\n  | O => (mkpr 1000000 0, t)\n  | S m =>\n      let (p, u) := minmax m (i + 1) t in\n      let v := rd 0 i u in\n      (mkpr (if v <? lo p then v else lo p) (if hi p <? v then v else hi p), upd 1 i v u)\n  end.\n')
addA('zp_if_chain_int', "", 'words n a 0 0 s',
     'Definition cls (c : int) : int :=\n  if c =? 32 then 0 else if c =? 10 then 1 else if (48 <=? c) && (c <=? 57) then 2\n  else if ((97 <=? c) && (c <=? 122)) || ((65 <=? c) && (c <=? 90)) then 3 else 4.\nFixpoint words (k : nat) (i prev acc : int) (t : mem) : int :=\n  match k with\n  | O => acc\n  | S m => let d := cls (rd8 0 i t) in\n           words m (i + 1) d (if (d =? 3) && negb (prev =? 3) then acc + 1 else acc) t\n  end.\n')
addA('zp_compare_prim', "", 'sgn a b + clamp 0 10 (a + b)',
     'Definition sgn (x y : int) : int :=\n  match PrimInt63.compare x y with Lt => 0 - 1 | Eq => 0 | Gt => 1 end.\nDefinition clamp (lo hi x : int) : int := if x <? lo then lo else if hi <? x then hi else x.\n')
addA('zp_nat_iter', "", 'Nat.iter n dbl a',
     'Definition dbl (x : int) : int := x * 2.\n')
addA('zp_nat_rect_loop', "", 'sumk n a',
     'Definition sumk (k : nat) (x : int) : int := nat_rec (fun _ => int) x (fun _ r => r + 1) k.\n')
addA('zp_dec_eqdec', "", 'if same n n then a else b',
     'Class EqDec (T : Type) := { dec : forall x y : T, {x = y} + {x <> y} }.\n#[export] Instance eq_nat : EqDec nat := { dec := Nat.eq_dec }.\nDefinition same {T} `{EqDec T} (x y : T) : bool := if dec x y then true else false.\n')
addA('zp_where_clause', "", 'ev2 n a',
     'Fixpoint ev2 (k : nat) (x : int) : int :=\n  match k with O => x | S m => od2 m (x + 1) end\nwith od2 (k : nat) (x : int) : int :=\n  match k with O => x * 2 | S m => ev2 m x end.\n')
addA('zp_local_loop_mem', "", 'rd 0 a (fillr n b s)',
     'Definition fillr (k0 : nat) (v : int) (t0 : mem) : mem :=\n  let fix lp (k : nat) (i : int) (t : mem) : mem :=\n    match k with O => t | S m => lp m (i + 1) (upd 0 i v t) end\n  in lp k0 0 t0.\n')
# a class or a record of functions given to a recursive function (step 84)
addA('zc_c_method', "", 'mx n a b',
     'Class Ord (A : Type) := { lt : A -> A -> bool }.\n#[export] Instance ord_int : Ord int := { lt := fun x y => x <? y }.\nFixpoint mx {A : Type} `{Ord A} (k : nat) (x y : A) : A := match k with O => x | S m => mx m (if lt x y then y else x) y end.\n')
addA('zc_c_no_braces', "", 'mx n a b',
     'Class Ord2 (A : Type) := lt2 : A -> A -> bool.\n#[export] Instance o2 : Ord2 int := fun x y => x <? y.\nFixpoint mx {A : Type} `{Ord2 A} (k : nat) (x y : A) : A := match k with O => x | S m => mx m (if lt2 x y then y else x) y end.\n')
addA('zc_c_two_fields', "", 'rep n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\n")
addA('zc_c_two_instances', "", 'rep n a + @rep int mul_m n b',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\n#[export] Instance mul_m : Monoid int | 5 := { unit' := 1; op := PrimInt63.mul }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\n")
addA('zc_c_explicit', "", '@rep int add_m n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\n")
addA('zc_c_build', "", 'rep add_m n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\nDefinition add_m : Monoid int := Build_Monoid int 0 PrimInt63.add.\nFixpoint rep {T} (H : Monoid T) (k : nat) (x : T) : T := match k with O => @unit' T H | S m => @op T H x (rep H m x) end.\n")
addA('zc_c_helper', "", 'twicef n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\nDefinition twicef {T} `{Monoid T} (k : nat) (x : T) : T := op x (rep k x).\n")
addA('zc_c_helper_two', "", 'rep2 n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\nDefinition rep2 {T} `{Monoid T} (k : nat) (x : T) : T := rep k (rep k x).\n")
addA('zc_c_rec_calls_rec', "", 'rr n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\nFixpoint rr {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => x | S m => rr m (rep 2 x) end.\n")
addA('zc_c_section', "", 'rep n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nSection S.\nContext {T : Type} `{Monoid T}.\nFixpoint rep (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\nEnd S.\n")
addA('zc_c_on_record', "", 'a2 (rep n (mk2 a b))',
     "Record r2 := mk2 { a2 : int; b2 : int }.\nClass Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance m2 : Monoid r2 := { unit' := mk2 0 0; op := fun x y => mk2 (a2 x + a2 y) (b2 x + b2 y) }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\n")
addA('zc_c_on_bool', "", 'cnt n a b 0',
     'Class Eq (T : Type) := { eqt : T -> T -> bool }.\n#[export] Instance e_int : Eq int := { eqt := PrimInt63.eqb }.\nFixpoint cnt {T} `{Eq T} (k : nat) (x y : T) (acc : int) : int := match k with O => acc | S m => cnt m x y (if eqt x y then acc + 1 else acc) end.\n')
addA('zc_c_writes', "", 'rd 0 a (fill n a b s)',
     'Class Wr (T : Type) := { wr : int -> T -> mem -> mem }.\n#[export] Instance w_int : Wr int := { wr := fun i v t => upd 0 i v t }.\nFixpoint fill {T} `{Wr T} (k : nat) (i : int) (v : T) (t : mem) : mem := match k with O => t | S m => fill m (i + 1) v (wr i v t) end.\n')
addA('zc_c_reads', "", 'sum n a b s',
     'Class Rd (T : Type) := { rdf : int -> mem -> T }.\n#[export] Instance r_int : Rd int := { rdf := fun i t => rd 0 i t }.\nFixpoint sum (k : nat) (i acc : int) (t : mem) : int := match k with O => acc | S m => sum m (i + 1) (acc + rdf i t) t end.\n')
addA('zc_c_superclass', "", 'rp n a',
     'Class Semi (T : Type) := { sop : T -> T -> T }.\nClass Mon (T : Type) `{Semi T} := { un : T }.\n#[export] Instance s_i : Semi int := { sop := PrimInt63.add }.\n#[export] Instance m_i : Mon int := { un := 0 }.\nFixpoint rp {T} `{Mon T} (k : nat) (x : T) : T := match k with O => un | S m => sop x (rp m x) end.\n')
addA('zc_c_built_from', "", 'fst (@dflt (int * int) _) + a',
     'Class Dflt (A : Type) := { dflt : A }.\n#[export] Instance d_int : Dflt int := { dflt := 7 }.\n#[export] Instance d_pair {A B} `{Dflt A} `{Dflt B} : Dflt (A * B) := { dflt := (dflt, dflt) }.\n')
addA('zc_c_inst_param', "", 'cnt n (a, b) (b, a) 0',
     'Class Eq (T : Type) := { eqt : T -> T -> bool }.\n#[export] Instance e_int : Eq int := { eqt := PrimInt63.eqb }.\n#[export] Instance e_pair {A B} `{Eq A} `{Eq B} : Eq (A * B) := { eqt := fun x y => eqt (fst x) (fst y) && eqt (snd x) (snd y) }.\nFixpoint cnt {T} `{Eq T} (k : nat) (x y : T) (acc : int) : int := match k with O => acc | S m => cnt m x y (if eqt x y then acc + 1 else acc) end.\n')
addA('zc_c_counter_late', "", 'rep n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint rep (k : nat) {T} `{Monoid T} (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\n")
addA('zc_c_mutual', "", 'ev n a',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\nFixpoint ev {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (od m x) end\nwith od {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => x | S m => ev m x end.\n")
addA('zc_c_generic_inst', "", 'fst (rep n (a, b))',
     "Class Monoid (T : Type) := { unit' : T; op : T -> T -> T }.\n#[export] Instance add_m : Monoid int := { unit' := 0; op := PrimInt63.add }.\n#[export] Instance add_p {A B} `{Monoid A} `{Monoid B} : Monoid (A * B) := { unit' := (unit', unit'); op := fun x y => (op (fst x) (fst y), op (snd x) (snd y)) }.\nFixpoint rep {T} `{Monoid T} (k : nat) (x : T) : T := match k with O => unit' | S m => op x (rep m x) end.\n")
addA('zc_r_capture', "", 'use n (mkops (fun x => x + b)) a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\n')
addA('zc_r_closed', "", 'use n (mkops (fun x => x + 1)) a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\n')
addA('zc_r_const', "", 'use n my a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\nDefinition my : ops := mkops (fun x => x + 1).\n')
addA('zc_r_leading', "", 'use (mkops (fun x => x + b)) n a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (o : ops) (k : nat) (x : int) : int := match k with O => x | S m => use o m (op1 o x) end.\n')
addA('zc_r_num_field', "", 'use n (mkops b (fun x => x + 1)) a',
     'Record ops := mkops { base : int; fa : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x + base o | S m => use m o (fa o x) end.\n')
addA('zc_r_two_funcs', "", 'use n (mkops (fun x => x + 1) PrimInt63.mul) a',
     'Record ops := mkops { fa : int -> int; fb : int -> int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (fb o (fa o x) x) end.\n')
addA('zc_r_unused_func', "", 'use n (mkops (fun x => x + 1) (fun x => x)) a',
     'Record ops := mkops { fa : int -> int; fb : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (fa o x) end.\n')
addA('zc_r_helper', "", 'use n (mkops (fun x => x + b)) a',
     'Record ops := mkops { op1 : int -> int }.\nDefinition hlp (o : ops) (x : int) : int := op1 o x + 1.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (hlp o x) end.\n')
addA('zc_r_let', "", 'let o := mkops (fun x => x + b) in use n o a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\n')
addA('zc_r_two_calls', "", 'use n (mkops (fun x => x + b)) a + use n (mkops (fun x => x * b)) a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\n')
addA('zc_r_helper_makes', "", 'use n (mk b) a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\nDefinition mk (y : int) : ops := mkops (fun x => x + y).\n')
addA('zc_r_writes', "", 'rd 0 a (run n (mkops (fun i t => upd 0 i b t)) a s)',
     'Record ops := mkops { step : int -> mem -> mem }.\nFixpoint run (k : nat) (o : ops) (i : int) (t : mem) : mem := match k with O => t | S m => run m o (i + 1) (step o i t) end.\n')
addA('zc_r_reads', "", 'sum n (mkops (fun i t => rd 0 i t)) a b s',
     'Record ops := mkops { get : int -> mem -> int }.\nFixpoint sum (k : nat) (o : ops) (i acc : int) (t : mem) : int := match k with O => acc | S m => sum m o (i + 1) (acc + get o i t) t end.\n')
addA('zc_r_gives_record', "", 'use n (mk b) a',
     'Record ops := mkops { op1 : int -> int }.\nDefinition mk (y : int) : ops := mkops (fun x => x + y).\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m (mk x) (op1 o x) end.\n')
addA('zc_r_chosen', "", 'use n (if a <? b then mkops (fun x => x + 1) else mkops (fun x => x + 2)) a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (op1 o x) end.\n')
addA('zc_r_in_pair', "", 'use n ((fun x => x + b), a) a',
     'Fixpoint use (k : nat) (p : (int -> int) * int) (x : int) : int := match k with O => x + snd p | S m => use m p (fst p x) end.\n')
addA('zc_r_mutual', "", 'ev n (mkops (fun x => x + b)) a',
     'Record ops := mkops { op1 : int -> int }.\nFixpoint ev (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => od m o (op1 o x) end\nwith od (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => ev m o x end.\n')
addA('zc_r_nested', "", 'use n (mkops (mki (fun x => x + 1)) (fun x => x + b)) a',
     'Record ins := mki { g1 : int -> int }.\nRecord ops := mkops { inner : ins; fa : int -> int }.\nFixpoint use (k : nat) (o : ops) (x : int) : int := match k with O => x | S m => use m o (g1 (inner o) (fa o x)) end.\n')
# a counter a function gives back, used as a counter (step 83)
addA('zb_u_lt', "", 'if Nat.ltb (cnt n a s) n then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_sum', "", 'ff (cnt n a s + cnt n b s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_succ', "", 'ff (S (cnt n a s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_add_lit', "", 'ff (cnt n a s + 3) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_lit_add', "", 'ff (3 + cnt n a s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_add_var', "", 'ff (cnt n a s + n) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_mul2', "", 'ff (2 * cnt n a s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_mul3', "", 'ff (3 * cnt n a s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_match_pred', "", 'match cnt n a s with O => a | S p => ff p b end',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_match_two', "", 'match cnt n a s with O => a | S O => b | S (S _) => a + b end',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_let', "", 'let c := cnt n a s in if Nat.leb c 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_let_twice', "", 'let c := cnt n a s in ff c b + ff c a',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_let_succ', "", 'let c := cnt n a s in ff (S c) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_let_add', "", 'let c := cnt n a s in ff (c + c) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_let_two', "", 'let c := cnt n a s in let d := cnt n b s in ff (c + d) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_let_nested', "", 'let c := cnt n a s in let d := S c in ff (S d) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_let_helper', "", 'let c := hh n a s in ff c b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nDefinition hh (k : nat) (i : int) (t : mem) : nat := S (cnt k i t).\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_let_number', "", 'let c := cnt n a s in Uint63.of_nat c + 1',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_pred', "", 'ff (Nat.pred (cnt n a s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_sub', "", 'ff (cnt n a s - 1) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_min', "", 'ff (Nat.min (cnt n a s) n) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_max', "", 'ff (Nat.max (cnt n a s) n) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_div2', "", 'ff (Nat.div2 (cnt n a s)) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('zb_u_nested', "", 'Uint63.of_nat (cnt (cnt n a s) b s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_nested_use', "", 'if Nat.leb (cnt (cnt n a s) b s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_two_funcs', "", 'if Nat.leb (cnt n a s) (tw n) then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\n')
addA('zb_u_in_rec', "", 'outer n a s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint outer (j : nat) (x : int) (t : mem) : int := match j with O => x | S m => if Nat.leb (cnt m x t) 3 then outer m (x + 1) t else x end.\n')
addA('zb_u_in_rec_given', "", 'outer n a s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\nFixpoint outer (j : nat) (x : int) (t : mem) : int := match j with O => x | S m => outer m (ff (cnt m x t) x) t end.\n')
addA('zb_u_helper', "", 'if wrap n a s then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nDefinition wrap (k : nat) (a : int) (t : mem) : bool := Nat.leb (cnt k a t) 3.\n')
addA('zb_u_helper_num', "", 'wrap n a s + wrap n b s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nDefinition wrap (k : nat) (a : int) (t : mem) : int := if Nat.leb (cnt k a t) 3 then a else 0.\n')
addA('zb_u_in_mem', "", 'rd 0 a (wr n a s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nDefinition wr (k : nat) (a : int) (t : mem) : mem := if Nat.leb (cnt k a t) 3 then upd 0 a 1 t else t.\n')
addA('zb_u_after_write', "", 'let t := upd 0 a b s in if Nat.leb (cnt n a t) 3 then a else rd 0 a t',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_rec_mem', "", 'rd 0 a (w n a s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint w (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => if Nat.leb (cnt m i t) 3 then w m (i + 1) (upd 0 i 1 t) else w m (i + 1) t end.\n')
addA('zb_u_match_pred_use', "", 'match cnt n a s with O => a | S p => if Nat.leb (cnt p a s) 3 then a else b end',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_lit', "", 'if Nat.leb (cnt 5 a s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_arg_add', "", 'if Nat.leb (cnt (n + n) a s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_arg_succ', "", 'if Nat.leb (cnt (S n) a s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('zb_u_budget_writes', "", 'fw (cnt n a s) b s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint fw (k : nat) (x : int) (t : mem) : int := match k with O => rd 0 x t | S m => fw m (x + 1) (upd 0 x 1 t) end.\n')
addA('zb_a_acc', "", 'if Nat.leb (tw n 0) 3 then a else b',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => tw m (S acc) end.\n')
addA('zb_a_acc_first', "", 'if Nat.leb (tw 0 n) 3 then a else b',
     'Fixpoint tw (acc k : nat) : nat := match k with O => acc | S m => tw (S acc) m end.\n')
addA('zb_a_acc_add', "", 'if Nat.leb (tw n 1) 3 then a else b',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => tw m (acc + 2) end.\n')
addA('zb_a_acc_if', "", 'if Nat.leb (tw n 0 a) 3 then a else b',
     'Fixpoint tw (k acc : nat) (i : int) : nat := match k with O => acc | S m => tw m (if i =? 0 then acc else S acc) (i + 1) end.\n')
addA('zb_a_two_acc', "", 'if Nat.leb (tw n 0 1) 3 then a else b',
     'Fixpoint tw (k x y : nat) : nat := match k with O => x | S m => tw m y (S x) end.\n')
addA('zb_a_acc_read', "", 'if Nat.leb (tw n 0) 3 then a else b',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => match acc with O => tw m 1 | S q => tw m q end end.\n')
addA('zb_a_acc_doubles', "", 'if Nat.leb (tw n 1) 3 then a else b',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => tw m (acc + acc) end.\n')
addA('zb_s_two', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (S (tw m)) end.\n')
addA('zb_s_three', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (S (S (tw m))) end.\n')
addA('zb_s_lit', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => 7 | S m => S (tw m) end.\n')
addA('zb_s_add', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => 2 + tw m end.\n')
addA('zb_s_var', "", 'if Nat.leb (tw n 3) 3 then a else b',
     'Fixpoint tw (k c : nat) : nat := match k with O => c | S m => S (tw m c) end.\n')
addA('zb_s_other_counter', "", 'if Nat.leb (tw n n) 3 then a else b',
     'Fixpoint tw (k c : nat) : nat := match k with O => c | S m => tw m c end.\n')
addA('zb_s_if_num', "", 'if Nat.leb (tw n a) 3 then a else b',
     'Fixpoint tw (k : nat) (i : int) : nat := match k with O => O | S m => if i =? 0 then tw m (i + 1) else S (tw m (i + 1)) end.\n')
addA('zb_s_let', "", 'if Nat.leb (tw n a) 3 then a else b',
     'Fixpoint tw (k : nat) (i : int) : nat := match k with O => O | S m => let r := i + 1 in S (tw m r) end.\n')
addA('zb_s_let_rec', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => let r := tw m in S (S r) end.\n')
addA('zb_s_deep', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S O => 5 | S (S m) => S (tw m) end.\n')
addA('zb_s_counter_second', "", 'if Nat.leb (tw a n) 3 then a else b',
     'Fixpoint tw (i : int) (k : nat) : nat := match k with O => O | S m => S (tw (i + 1) m) end.\n')
addA('zb_s_two_funcs', "", 'if Nat.leb (th n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\nFixpoint th (k : nat) : nat := match k with O => tw 2 | S m => S (th m) end.\n')
addA('zb_s_add_var', "", 'if Nat.leb (tw n 2) 3 then a else b',
     'Fixpoint tw (k c : nat) : nat := match k with O => O | S m => c + tw m c end.\n')
addA('zb_s_quadratic', "", 'if Nat.leb (th n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\nFixpoint th (k : nat) : nat := match k with O => O | S m => tw m + th m end.\n')
addA('zb_s_power', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => 1 | S m => tw m + tw m end.\n')
addA('zb_s_power_mul', "", 'if Nat.leb (tw n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => 1 | S m => 2 * tw m end.\n')
addA('zb_o_helper_two', "", 'if Nat.leb (hh n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\nDefinition hh (k : nat) : nat := tw k + tw k.\n')
addA('zb_o_section', "", 'if Nat.leb (tw b n a) 3 then a else b',
     'Section S.\nVariable d : int.\nFixpoint tw (k : nat) (i : int) : nat := match k with O => O | S m => if i =? d then tw m (i + 1) else S (tw m (i + 1)) end.\nEnd S.\n')
addA('zb_o_local', "", 'if tw n a then a else b',
     'Definition tw (k0 : nat) (i0 : int) : bool := let fix go (k : nat) (i : int) : nat := match k with O => O | S m => S (go m (i + 1)) end in Nat.leb (go k0 i0) 3.\n')
addA('zb_o_helper', "", 'if Nat.leb (hh n) 3 then a else b',
     'Definition hh (k : nat) : nat := S (S k).\n')
addA('zb_o_helper_call', "", 'if Nat.leb (hh n) 3 then a else b',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\nDefinition hh (k : nat) : nat := S (tw k).\n')
addA('zb_o_callee_grows', "", 'ff (cnt n a s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint hh (k : nat) (x : int) : int := match k with O => x | S m => hh m (x + 1) end.\nDefinition ff (k : nat) (x : int) : int := hh (S k) x.\n')
addA('zb_o_weights', "", 'pp n n a s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint pp (k c : nat) (x : int) (t : mem) : int := match k with O => x | S m => if Nat.leb (cnt c x t) 3 then pp m (S c) (x + 1) t else x end.\n')
addA('zb_o_row_uses', "", 'fst (w n a s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint w (k : nat) (i : int) (t : mem) : int * mem := match k with O => (i, t) | S m => if Nat.leb (cnt m i t) 3 then w m (i + 1) (upd 0 i 1 t) else (i, t) end.\n')
addA('zb_o_counter_row_uses', "", 'if Nat.leb (w n a s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint w (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if Nat.leb (cnt m i t) 3 then S (w m (i + 1) t) else w m (i + 1) t end.\n')
# a function giving back a counter, made a number where it is used (step 82)
addA('z_n_arith', "", 'Uint63.of_nat (cnt n a s) * 2 + b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_n_index', "", 'rd 0 (Uint63.of_nat (cnt n a s)) s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_n_write', "", 'rd 1 a (upd 1 a (Uint63.of_nat (cnt n a s)) s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_n_test', "", 'if Uint63.of_nat (cnt n a s) =? 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_n_let', "", 'let c := Uint63.of_nat (cnt n a s) in c + c',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_n_twice', "", 'Uint63.of_nat (cnt n a s) + Uint63.of_nat (cnt n b s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_n_in_rec', "", 'outer n a s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint outer (j : nat) (x : int) (t : mem) : int := match j with O => x | S m => outer m (x + Uint63.of_nat (cnt 3 x t)) t end.\n')
addA('z_n_in_helper', "", 'wrap a s',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nDefinition wrap (a : int) (t : mem) : int := Uint63.of_nat (cnt 3 a t) + 1.\n')
addA('z_n_after_write', "", 'let t := upd 0 a b s in Uint63.of_nat (cnt n a t) + rd 0 a t',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_n_lit_counter', "", 'Uint63.of_nat (cnt 5 a s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_s_two', "", 'Uint63.of_nat (tw n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (S (tw m)) end.\n')
addA('z_s_lit', "", 'Uint63.of_nat (tw n)',
     'Fixpoint tw (k : nat) : nat := match k with O => 7 | S m => S (tw m) end.\n')
addA('z_s_var', "", 'Uint63.of_nat (tw n 3)',
     'Fixpoint tw (k c : nat) : nat := match k with O => c | S m => S (tw m c) end.\n')
addA('z_s_other_counter', "", 'Uint63.of_nat (tw n n)',
     'Fixpoint tw (k c : nat) : nat := match k with O => c | S m => tw m c end.\n')
addA('z_s_add', "", 'Uint63.of_nat (tw n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => 3 + tw m end.\n')
addA('z_s_add_var', "", 'Uint63.of_nat (tw n 2)',
     'Fixpoint tw (k c : nat) : nat := match k with O => O | S m => c + tw m c end.\n')
addA('z_s_add_both', "", 'Uint63.of_nat (tw n)',
     'Fixpoint tw (k : nat) : nat := match k with O => 1 | S m => tw m + tw m end.\n')
addA('z_s_mul', "", 'Uint63.of_nat (tw n)',
     'Fixpoint tw (k : nat) : nat := match k with O => 1 | S m => 2 * tw m end.\n')
addA('z_s_match_counter', "", 'Uint63.of_nat (tw n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S O => 5 | S (S m) => S (tw m) end.\n')
addA('z_s_if_num', "", 'Uint63.of_nat (tw n a)',
     'Fixpoint tw (k : nat) (i : int) : nat := match k with O => O | S m => if i =? 0 then tw m (i + 1) else S (tw m (i + 1)) end.\n')
addA('z_s_let', "", 'Uint63.of_nat (tw n a)',
     'Fixpoint tw (k : nat) (i : int) : nat := match k with O => O | S m => let r := i + 1 in S (tw m r) end.\n')
addA('z_s_let_rec', "", 'Uint63.of_nat (tw n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => let r := tw m in S (S r) end.\n')
addA('z_s_counter_second', "", 'Uint63.of_nat (tw a n)',
     'Fixpoint tw (i : int) (k : nat) : nat := match k with O => O | S m => S (tw (i + 1) m) end.\n')
addA('z_a_acc', "", 'Uint63.of_nat (tw n 0)',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => tw m (S acc) end.\n')
addA('z_a_acc_first', "", 'Uint63.of_nat (tw 0 n)',
     'Fixpoint tw (acc k : nat) : nat := match k with O => acc | S m => tw (S acc) m end.\n')
addA('z_a_acc_if', "", 'Uint63.of_nat (tw n 0 a)',
     'Fixpoint tw (k acc : nat) (i : int) : nat := match k with O => acc | S m => tw m (if i =? 0 then acc else S acc) (i + 1) end.\n')
addA('z_a_acc_add', "", 'Uint63.of_nat (tw n 1)',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => tw m (acc + 2) end.\n')
addA('z_a_acc_from_counter', "", 'Uint63.of_nat (tw n n)',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => tw m (S acc) end.\n')
addA('z_a_acc_read', "", 'Uint63.of_nat (tw n 0)',
     'Fixpoint tw (k acc : nat) : nat := match k with O => acc | S m => match acc with O => tw m 1 | S q => tw m q end end.\n')
addA('z_a_two_acc', "", 'Uint63.of_nat (tw n 0 1)',
     'Fixpoint tw (k x y : nat) : nat := match k with O => x | S m => tw m y (S x) end.\n')
addA('z_o_section', "", 'Uint63.of_nat (tw b n a)',
     'Section S.\nVariable d : int.\nFixpoint tw (k : nat) (i : int) : nat := match k with O => O | S m => if i =? d then tw m (i + 1) else S (tw m (i + 1)) end.\nEnd S.\n')
addA('z_o_local', "", 'tw n a',
     'Definition tw (k0 : nat) (i0 : int) : int := let fix go (k : nat) (i : int) : nat := match k with O => O | S m => S (go m (i + 1)) end in Uint63.of_nat (go k0 i0).\n')
addA('z_o_helper', "", 'Uint63.of_nat (hh n)',
     'Definition hh (k : nat) : nat := S (S k).\n')
addA('z_o_helper_call', "", 'Uint63.of_nat (hh n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\nDefinition hh (k : nat) : nat := S (tw k).\n')
addA('z_o_two_funcs', "", 'Uint63.of_nat (th n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\nFixpoint th (k : nat) : nat := match k with O => tw 2 | S m => S (th m) end.\n')
addA('z_o_two_funcs_add', "", 'Uint63.of_nat (th n)',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (tw m) end.\nFixpoint th (k : nat) : nat := match k with O => O | S m => tw m + th m end.\n')
addA('z_o_mem_counter', "", 'match tw n a s with (c, t) => Uint63.of_nat c + rd 0 a t end',
     'Fixpoint tw (k : nat) (i : int) (t : mem) : nat * mem := match k with O => (O, t) | S m => let (c, u) := tw m (i + 1) (upd 0 i i t) in (S c, u) end.\n')
addA('z_o_pair_counter', "", 'Uint63.of_nat (fst (tw n a)) + snd (tw n a)',
     'Fixpoint tw (k : nat) (i : int) : nat * int := match k with O => (O, i) | S m => tw m (i + 1) end.\n')
addA('z_o_opt_counter', "", 'match tw n a with Some c => Uint63.of_nat c | None => 0 end',
     'Fixpoint tw (k : nat) (i : int) : option nat := match k with O => None | S m => if i =? 0 then Some k else tw m (i + 1) end.\n')
addA('z_u_counter_use', "", 'ff (cnt n a s) b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\nFixpoint ff (k : nat) (x : int) : int := match k with O => x | S m => ff m (x + 1) end.\n')
addA('z_u_match', "", 'match cnt n a s with O => a | S _ => b end',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_u_leb', "", 'if Nat.leb (cnt n a s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_u_eqb', "", 'if Nat.eqb (cnt n a s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('z_u_zofnat', "", 'if (Z.of_nat (cnt n a s) <? 3)%Z then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
# a proof as a parameter, a value with its proof as a parameter (step 81)
addA('y_p_first', "", 'f I a',
     'Definition f (H : True) (x : int) : int := x + 1.\n')
addA('y_p_last', "", 'f a I',
     'Definition f (x : int) (H : True) : int := x + 1.\n')
addA('y_p_two', "", 'f I a eq_refl b',
     'Definition f (H : True) (x : int) (J : 0 = 0) (y : int) : int := x + y.\n')
addA('y_p_mem', "", '(if PrimInt63.lesb 0 a as c return PrimInt63.lesb 0 a = c -> int then fun H => f a H s else fun _ => 0) eq_refl',
     'Definition f (i : int) (H : (PrimInt63.lesb 0 i) = true) (t : mem) : int := rd 0 i t.\n')
addA('y_p_mem_writes', "", 'rd 0 a ((if PrimInt63.lesb 0 a as c return PrimInt63.lesb 0 a = c -> mem then fun H => f a H s else fun _ => s) eq_refl)',
     'Definition f (i : int) (H : (PrimInt63.lesb 0 i) = true) (t : mem) : mem := upd 0 i i t.\n')
addA('y_p_lt', "", 'f 2 (ltac:(repeat constructor) : (2 < 5)%nat) a',
     'Definition f (x : nat) (H : (x < 5)%nat) (y : int) : int := y + 1.\n')
addA('y_p_not', "", 'f a (ltac:(discriminate) : ~ (0 = 1)%nat)',
     'Definition f (x : int) (H : ~ (0 = 1)%nat) : int := x + 1.\n')
addA('y_p_def', "", 'f 1 (ltac:(unfold small; repeat constructor) : small 1) a',
     'Definition small (x : nat) : Prop := (x <= 3)%nat.\nDefinition f (x : nat) (H : small x) (y : int) : int := y + 1.\n')
addA('y_p_and', "", 'f a (conj I I)',
     'Definition f (x : int) (H : True /\\ True) : int := x + 1.\n')
addA('y_p_forall', "", 'f a (fun _ => eq_refl)',
     'Definition f (x : int) (H : forall k : nat, (k = k)%nat) : int := x + 1.\n')
addA('y_p_rec_first', "", 'f I n a',
     'Fixpoint f (H : True) (k : nat) (x : int) {struct k} : int := match k with O => x | S m => f H m (x + 1) end.\n')
addA('y_p_rec_after', "", 'f n a I',
     'Fixpoint f (k : nat) (x : int) (H : True) {struct k} : int := match k with O => x | S m => f m (x + 1) I end.\n')
addA('y_p_rec_mem', "", 'rd 0 a (f n I a s)',
     'Fixpoint f (k : nat) (H : True) (i : int) (t : mem) {struct k} : mem := match k with O => t | S m => f m H (i + 1) (upd 0 i i t) end.\n')
addA('y_p_rec_val', "", 'match f n I a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint f (k : nat) (H : True) (i : int) (t : mem) {struct k} : option int * mem := match k with O => (Some i, t) | S m => f m H (i + 1) (upd 0 i i t) end.\n')
addA('y_p_rec_convoy', "", 'f (S (S O)) (ltac:(repeat constructor) : (2 <= 100)%nat) a',
     'Fixpoint f (k : nat) (H : (k <= 100)%nat) (x : int) {struct k} : int := match k as k0 return (k0 <= 100)%nat -> int with O => fun _ => x | S m => fun H0 => f m (PeanoNat.Nat.le_trans _ _ _ (PeanoNat.Nat.le_succ_diag_r m) H0) (x + 1) end H.\n')
addA('y_p_given', "", 'f a I',
     'Definition g (x : int) (H : True) : int := x + 1.\nDefinition f (x : int) (H : True) : int := g x H + 1.\n')
addA('y_p_given_rec', "", 'f n a I',
     'Definition g (x : int) (H : True) : int := x + 1.\nFixpoint f (k : nat) (x : int) (H : True) {struct k} : int := match k with O => g x H | S m => f m (g x H) H end.\n')
addA('y_p_section', "", 'f I a',
     'Section S.\nHypothesis H : True.\nDefinition f (x : int) : int := match H with I => x + 1 end.\nEnd S.\n')
addA('y_p_section_unused', "", 'f b eq_refl n a',
     'Section S.\nVariable d : int.\nHypothesis H : (0 = 0)%nat.\nFixpoint f (k : nat) (x : int) : int := match H with eq_refl => match k with O => x + d | S m => f m (x + 1) end end.\nEnd S.\n')
addA('y_p_cast', "", 'f eq_refl a',
     'Definition f (H : (0 = 0)%nat) (x : int) : int := match H with eq_refl => x + 1 end.\n')
addA('y_p_used_by_match', "", 'f I a',
     'Definition f (H : True) (x : int) : int := match H with I => x + 1 end.\n')
addA('y_p_tactic_def', "", '(if PrimInt63.lesb 0 a as c return PrimInt63.lesb 0 a = c -> int then fun H => f a H else fun _ => 0) eq_refl',
     'Definition f (x : int) (H : (PrimInt63.lesb 0 x) = true) : int.\nProof. exact (x + 1). Defined.\n')
addA('y_p_value_of_proof', "", 'f a (exist _ 0%nat eq_refl)',
     'Definition f (x : int) (H : {y : nat | y = 0%nat}) : int := match proj1_sig H with O => x | S _ => x + 1 end.\n')
addA('y_s_var', "", '(if PrimInt63.lesb 0 a as c return PrimInt63.lesb 0 a = c -> int then fun H => hh (exist _ a H) else fun _ => 0) eq_refl',
     'Definition g (x : {y : int | PrimInt63.lesb 0 y = true}) : int := proj1_sig x + 1.\nDefinition hh (x : {y : int | PrimInt63.lesb 0 y = true}) : int := g x + 2.\n')
addA('y_s_match', "", 'g (exist _ a I)',
     'Definition g (x : {y : int | True}) : int := match x with exist v _ => v + 1 end.\n')
addA('y_s_let', "", 'g (exist _ a I)',
     'Definition g (x : {y : int | True}) : int := let (v, _) := x in v + 1.\n')
addA('y_s_with_mem', "", 'rd 0 a (g (exist _ a I) s)',
     'Definition g (x : {y : int | True}) (t : mem) : mem := upd 0 (proj1_sig x) 1 t.\n')
addA('y_s_two', "", 'g (exist _ a I) (exist _ b I)',
     'Definition g (x y : {v : int | True}) : int := proj1_sig x + proj1_sig y.\n')
addA('y_s_rec', "", 'g n (exist _ a I)',
     'Fixpoint g (k : nat) (x : {y : int | True}) {struct k} : int := match k with O => proj1_sig x | S m => g m (exist _ (proj1_sig x + 1) I) end.\n')
addA('y_s_rec_mem', "", 'rd 0 a (g n (exist _ a I) s)',
     'Fixpoint g (k : nat) (x : {y : int | True}) (t : mem) {struct k} : mem := match k with O => t | S m => g m (exist _ (proj1_sig x + 1) I) (upd 0 (proj1_sig x) 1 t) end.\n')
addA('y_s_from_fn', "", 'u (clamp a) + u (clamp b)',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\nDefinition u (x : {y : int | True}) : int := proj1_sig x + 1.\n')
addA('y_s_from_rec', "", 'u (clamp n a)',
     'Fixpoint clamp (k : nat) (x : int) : {y : int | True} := match k with O => exist _ x I | S m => clamp m (x + 1) end.\nDefinition u (x : {y : int | True}) : int := proj1_sig x + 1.\n')
addA('y_s_nat', "", 'g (exist _ n I) a',
     'Definition g (x : {k : nat | True}) (y : int) : int := match proj1_sig x with O => y | S _ => y + 1 end.\n')
addA('y_s_bool', "", 'g (exist _ (a <? b) eq_refl) a',
     'Definition g (x : {k : bool | k = k}) (y : int) : int := if proj1_sig x then y else y + 1.\n')
addA('y_s_record', "", 'g (exist _ (mk2w a b) I)',
     'Record r2w := mk2w { wa : int; wb : int }.\nDefinition g (x : {k : r2w | True}) : int := wa (proj1_sig x) + wb (proj1_sig x).\n')
addA('y_s_given_var', "", 'hh (exist _ a I) b',
     'Definition g (x : {y : int | True}) : int := proj1_sig x + 1.\nDefinition hh (x : {y : int | True}) (k : int) : int := g x + k.\n')
addA('y_r_field', "", 'g (mkpos a eq_refl)',
     'Record pos := mkpos { pv : int; pp : (0 = 0)%nat }.\nDefinition g (x : pos) : int := pv x + 1.\n')
addA('y_r_two_nums', "", 'g (mkpos a b eq_refl)',
     'Record pos := mkpos { pv : int; pw : int; pp : (0 = 0)%nat }.\nDefinition g (x : pos) : int := pv x + pw x.\n')
addA('y_r_result', "", 'g (mk a)',
     'Record pos := mkpos { pv : int; pp : (0 = 0)%nat }.\nDefinition mk (a : int) : pos := mkpos (a + 1) eq_refl.\nDefinition g (x : pos) : int := pv x + 1.\n')
addA('y_r_rec', "", 'g n (mkpos a eq_refl)',
     'Record pos := mkpos { pv : int; pp : (0 = 0)%nat }.\nFixpoint g (k : nat) (x : pos) {struct k} : int := match k with O => pv x | S m => g m (mkpos (pv x + 1) eq_refl) end.\n')
# a memory in a record or a pair, at any place, as a result and as a parameter (step 80)
addA('x_r_mid', "", 'let r := lp n a s in qa r + qb r + rd 0 a (qt r)',
     'Record rq := mkq { qa : int; qt : mem; qb : int }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rq := match k with O => mkq i t (i + 1) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_first', "", 'let r := lp n a s in qa r + qb r + rd 0 a (qt r)',
     'Record rq := mkq { qt : mem; qa : int; qb : int }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rq := match k with O => mkq t i (i + 1) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_num', "", 'let r := lp n a s in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : st := match k with O => mkst i t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_mem_only', "", 'rd 0 a (wt (lp n a s))',
     'Record wm := mkw { wt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : wm := match k with O => mkw t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_bool', "", 'let r := lp n a s in if qf r then qa r + rd 0 a (qt r) else 0',
     'Record rq := mkq { qa : int; qf : bool; qt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rq := match k with O => mkq i (i <? 3) t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_data', "", 'let r := lp n a s in match qo r with Some v => v + rd 0 a (qt r) | None => 0 end',
     'Record rq := mkq { qo : option int; qt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rq := match k with O => mkq None t | S m => if rd 0 i t =? 0 then mkq (Some i) t else lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_ind', "", 'match lp n a s with W v t => v + rd 0 a t end',
     'Inductive w := W (a : int) (t : mem).\nFixpoint lp (k : nat) (i : int) (t : mem) : w := match k with O => W i t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_pattern', "", 'match lp n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_proj_one', "", 'ra (lp n a s)',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_proj_mem', "", 'rd 0 a (rt (lp n a s))',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_proj_two', "", 'ra (lp n a s) + rd 0 a (rt (lp n a s))',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_after', "", 'match lp n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => match lp m (i + 1) (upd 0 i i t) with mkm x y u => mkm (x + 1) y (upd 0 x y u) end end.\n')
addA('x_r_after_proj', "", 'match lp n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => let r := lp m (i + 1) (upd 0 i i t) in mkm (ra r + 1) (rb r) (upd 0 (ra r) (rb r) (rt r)) end.\n')
addA('x_r_update', "", 'match lp n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nDefinition bump (r : rm) : rm := mkm (ra r + 1) (rb r) (rt r).\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => bump (lp m (i + 1) (upd 0 i i t)) end.\n')
addA('x_r_in_loop', "", 'outer n a s',
     "Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => lp m (i + 1) (upd 0 i i t) end.\nFixpoint outer (j : nat) (a : int) (t : mem) : int := match j with O => rd 0 a t | S j' => match lp 3 a t with mkm x y u => outer j' (x + y) u end end.\n")
addA('x_r_section', "", 'match lp b n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nSection S.\nVariable c : int.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i c t | S m => lp m (i + c) (upd 0 i c t) end.\nEnd S.\n')
addA('x_r_local', "", 'match lp n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nDefinition lp (k0 : nat) (i0 : int) (t0 : mem) : rm := let fix go (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i i t | S m => go m (i + 1) (upd 0 i i t) end in go k0 i0 t0.\n')
addA('x_r_block', "", 'match lp 1 n a s with mkm x y t => x + y + rd 1 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (h : int) (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i i t | S m => lp h m (i + 1) (upd h i i t) end.\n')
addA('x_r_helper', "", 'match lp n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nDefinition mk (i : int) (t : mem) : rm := mkm i (i + 1) t.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mk i t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_r_two_funcs', "", 'match lq n a s with mkm x y t => x + y + rd 0 a t end',
     'Record rm := mkm { ra : int; rb : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i i t | S m => lp m (i + 1) (upd 0 i i t) end.\nFixpoint lq (k : nat) (i : int) (t : mem) : rm := match k with O => lp 2 i t | S m => match lp 3 i t with mkm x y u => lq m (x + y) u end end.\n')
addA('x_f_num', "", 'match lp n a s with (t, v) => v + rd 0 a t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem * int := match k with O => (t, i) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_f_num_fst', "", 'rd 0 a (fst (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem * int := match k with O => (t, i) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_f_num_snd', "", 'snd (lp n a s)',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem * int := match k with O => (t, i) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_f_pair', "", 'match lp n a s with (t, (x, y)) => x + y + rd 0 a t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem * (int * int) := match k with O => (t, (i, i + 1)) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_f_after', "", 'match lp n a s with (t, v) => v + rd 0 a t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem * int := match k with O => (t, i) | S m => let (u, v) := lp m (i + 1) (upd 0 i i t) in (upd 0 v v u, v + 1) end.\n')
addA('x_f_bool', "", 'match lp n a s with (t, true) => rd 0 a t | (_, false) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem * bool := match k with O => (t, i <? 3) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_f_three', "", 'match lp n a s with (x, t, y) => x + y + rd 0 a t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : int * mem * int := match k with O => (i, t, i + 1) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('x_p_rec_rec', "", 'let r := lp n (mkst a s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\n')
addA('x_p_rec_num', "", 'lp n (mkst a s)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : int := match k with O => cnt x + rd 0 0 (mm x) | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\n')
addA('x_p_rec_mem', "", 'rd 0 a (lp n (mkst a s))',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : mem := match k with O => mm x | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\n')
addA('x_p_rec_val', "", 'match lp n (mkst a s) with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : option int * mem := match k with O => (Some (cnt x), mm x) | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\n')
addA('x_p_match', "", 'let r := lp n (mkst a s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => match x with mkst c t => lp j (mkst (c + 1) (upd 0 c 1 t)) end end.\n')
addA('x_p_after_ctr', "", 'let r := lp (mkst a s) n in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (x : st) (k : nat) : st := match k with O => x | S j => lp (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) j end.\n')
addA('x_p_other_param', "", 'let r := lp n b (mkst a s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (d : int) (x : st) : st := match k with O => x | S j => lp j d (mkst (cnt x + d) (upd 0 (cnt x) d (mm x))) end.\n')
addA('x_p_helper_step', "", 'let r := lp n (mkst a s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nDefinition step (x : st) : st := mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x)).\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (step x) end.\n')
addA('x_p_helper_init', "", 'let r := lp n (init a s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nDefinition init (a : int) (s : mem) : st := mkst a s.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\n')
addA('x_p_let_arg', "", 'let x := mkst a s in let r := lp n x in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\n')
addA('x_p_pair_rec', "", 'let (c, t) := lp n (a, s) in c + rd 0 a t',
     'Fixpoint lp (k : nat) (x : int * mem) : int * mem := match k with O => x | S j => let (c, t) := x in lp j (c + 1, upd 0 c 1 t) end.\n')
addA('x_p_pair_num', "", 'lp n (a, s)',
     'Fixpoint lp (k : nat) (x : int * mem) : int := match k with O => fst x + rd 0 0 (snd x) | S j => lp j (fst x + 1, upd 0 (fst x) 1 (snd x)) end.\n')
addA('x_p_pair_first', "", 'let (t, c) := lp n (s, a) in c + rd 0 a t',
     'Fixpoint lp (k : nat) (x : mem * int) : mem * int := match k with O => x | S j => let (t, c) := x in lp j (upd 0 c 1 t, c + 1) end.\n')
addA('x_p_opt_mem', "", 'match lp n (Some a, s) with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (x : option int * mem) : option int * mem := match k with O => x | S j => match x with (Some v, t) => lp j (Some (v + 1), upd 0 v v t) | (None, t) => (None, t) end end.\n')
addA('x_p_var_caller', "", 'wrap n (mkst a s)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\nDefinition wrap (n : nat) (x : st) : int := cnt (lp n x).\n')
addA('x_p_var_rec', "", 'cnt (outer n (mkst a s))',
     "Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x))) end.\nFixpoint outer (j : nat) (x : st) : st := match j with O => x | S j' => outer j' (lp 2 x) end.\n")
addA('x_p_two_states', "", 'let r := lp n (mkst a s) (mkst b s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (k : nat) (x y : st) : st := match k with O => mkst (cnt x + cnt y) (mm y) | S j => lp j x (mkst (cnt y + 1) (upd 0 (cnt y) (rd 0 (cnt x) (mm x)) (mm y))) end.\n')
addA('x_p_section', "", 'let r := lp b n (mkst a s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nSection S.\nVariable d : int.\nFixpoint lp (k : nat) (x : st) : st := match k with O => x | S j => lp j (mkst (cnt x + d) (upd 0 (cnt x) d (mm x))) end.\nEnd S.\n')
addA('x_p_block', "", 'let r := lp 2 n (mkst a s) in cnt r + rd 2 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nFixpoint lp (h : int) (k : nat) (x : st) : st := match k with O => x | S j => lp h j (mkst (cnt x + 1) (upd h (cnt x) 1 (mm x))) end.\n')
addA('x_p_non_rec', "", 'let r := step (mkst a s) in cnt r + rd 0 a (mm r)',
     'Record st := mkst { cnt : int; mm : mem }.\nDefinition step (x : st) : st := mkst (cnt x + 1) (upd 0 (cnt x) 1 (mm x)).\n')
addA('x_p_non_rec_pair', "", 'let (c, t) := step (a, s) in c + rd 0 a t',
     'Definition step (x : int * mem) : int * mem := let (i, t) := x in (i + 1, upd 0 i i t).\n')
# a value and a memory under parameters, from a local fix, a block's number given, the same call named twice (step 79)
addA('w_b_two', "", 'match lp 0 1 n a s with (Some v, t) => v + rd 1 a t | (None, _) => 0 end',
     'Fixpoint lp (h j : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h j m (i + 1) (upd j i i (upd h i i t)) end.\n')
addA('w_b_const', "", 'match lp blk n a s with (Some v, t) => v + rd blk a t | (None, _) => 0 end',
     'Definition blk : int := 3.\nFixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (upd h i i t) end.\n')
addA('w_b_moved', "", 'match lp 0 n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp (h + 1) m (i + 1) (upd h i i t) end.\n')
addA('w_b_lit_moved', "", 'match lp 0 n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp 2 m (i + 1) (upd h i i t) end.\n')
addA('w_b_call_63', "", 'match lp 63 n a s with (Some v, t) => v + rd 63 a t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (upd h i i t) end.\n')
addA('w_b_call_var', "", 'match lp b n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (upd h i i t) end.\n')
addA('w_b_call_tested', "", 'if b =? 63 then 0 else match lp b n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (upd h i i t) end.\n')
addA('w_b_helper', "", 'match lp 0 n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition hw (b i v : int) (t : mem) : mem := upd b i v t.\nFixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (hw h i i t) end.\n')
addA('w_b_callee_rec', "", 'match lp n a s with (Some v, t) => v + rd 1 a t | (None, _) => 0 end',
     'Fixpoint wr (h : int) (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => wr h m (i + 1) (upd h i i t) end.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, wr 1 3 i t) | S m => lp m (i + 1) (wr 2 2 i t) end.\n')
addA('w_b_callee_given', "", 'match lp 1 n a s with (Some v, t) => v + rd 1 a t | (None, _) => 0 end',
     'Fixpoint wr (h : int) (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => wr h m (i + 1) (upd h i i t) end.\nFixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, wr h 3 i t) | S m => lp h m (i + 1) (wr h 2 i t) end.\n')
addA('w_b_row_given', "", 'match lq 1 n a s with (Some v, t) => v + rd 1 a t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (upd h i i t) end.\nFixpoint lq (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => match lp h 2 i t with (Some v, t1) => lq h m v t1 | (None, t1) => (None, t1) end end.\n')
addA('w_b_helper_given', "", 'wrap 1 n a s',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (upd h i i t) end.\nDefinition wrap (h : int) (n : nat) (a : int) (s : mem) : int := match lp h n a s with (Some v, t) => v + rd h a t | (None, _) => 0 end.\n')
addA('w_b_load', "", 'match lp 0 n a s with (Some v, t) => v + rd 0 0 t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => let t1 := hw_load 4 i h 0 t in lp h m (rd h 0 t1) t1 end.\n')
addA('w_s_two', "", 'match lp a b n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Section S.\nVariables c e : int.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (i + c), t) | S m => lp m (i + e) (upd 0 i c t) end.\nEnd S.\n')
addA('w_s_block', "", 'match lp 2 n a s with (Some v, t) => v + rd 2 a t | (None, _) => 0 end',
     'Section S.\nVariable h : int.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (upd h i i t) end.\nEnd S.\n')
addA('w_s_mem', "", 'match lp s n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Section S.\nVariable u : mem.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (rd 0 i u), t) | S m => lp m (i + 1) (upd 0 i i t) end.\nEnd S.\n')
addA('w_s_bool', "", 'match lp true n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Section S.\nVariable f : bool.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (if f then Some i else None, t) | S m => lp m (i + 1) (upd 0 i i t) end.\nEnd S.\n')
addA('w_s_counter', "", 'match lp 2 n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Section S.\nVariable j : nat.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (match j with O => Some i | S _ => None end, t) | S m => lp m (i + 1) (upd 0 i i t) end.\nEnd S.\n')
addA('w_s_fn', "", 'match lp (fun x => x + b) n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Section S.\nVariable f : int -> int.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (f i), t) | S m => lp m (f i) (upd 0 i i t) end.\nEnd S.\n')
addA('w_s_record', "", 'match lp (mk2w a b) n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Record r2w := mk2w { wa : int; wb : int }.\nSection S.\nVariable r : r2w.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (wa r), t) | S m => lp m (i + wb r) (upd 0 i i t) end.\nEnd S.\n')
addA('w_s_three_value', "", "let (r, t) := lp b n a s in let '(x, y, z) := r in x + y + z + rd 0 a t",
     'Section S.\nVariable c : int.\nFixpoint lp (k : nat) (i : int) (t : mem) : (int * int * int) * mem := match k with O => ((i, c, i + c), t) | S m => lp m (i + c) (upd 0 i c t) end.\nEnd S.\n')
addA('w_s_rec_caller', "", 'outer n a s',
     "Section S.\nVariable c : int.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (i + c), t) | S m => lp m (i + c) (upd 0 i c t) end.\nEnd S.\nFixpoint outer (j : nat) (a : int) (t : mem) : int := match j with O => rd 0 a t | S j' => match lp a 2 a t with (Some v, t1) => outer j' v t1 | (None, t1) => outer j' a t1 end end.\n")
addA('w_l_in_rec', "", 'outer n a s',
     "Fixpoint outer (j : nat) (a : int) (t : mem) : int := match j with O => rd 0 a t | S j' => let fix go (k : nat) (i : int) (u : mem) : option int * mem := match k with O => (Some i, u) | S m => go m (i + a) (upd 0 i a u) end in match go (S (S O)) a t with (Some v, t1) => outer j' v t1 | (None, t1) => outer j' a t1 end end.\n")
addA('w_l_two', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, t) => rd 1 a t end',
     'Definition lp (k0 : nat) (i0 : int) (t0 : mem) : option int * mem := let fix ga (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => ga m (i + 1) (upd 0 i i t) end in let fix gb (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (None, t) | S m => gb m (i + 2) (upd 1 i i t) end in match ga k0 i0 t0 with (Some v, t) => gb k0 v t | (None, t) => (None, t) end.\n')
addA('w_l_cap_mem', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (k0 : nat) (i0 : int) (u : mem) : option int * mem := let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (rd 0 i u), t) | S m => go m (i + 1) (upd 0 i i t) end in go k0 i0 u.\n')
addA('w_l_cap_bool', "", 'match lp (a <? b) n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (f : bool) (k0 : nat) (i0 : int) (t0 : mem) : option int * mem := let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (if f then Some i else None, t) | S m => go m (i + 1) (upd 0 i i t) end in go k0 i0 t0.\n')
addA('w_l_cap_lit', "", 'match lp 3 n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (c : int) (k0 : nat) (i0 : int) (t0 : mem) : option int * mem := let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (i + c), t) | S m => go m (i + c) (upd 0 i c t) end in go k0 i0 t0.\n')
addA('w_l_cap_pattern', "", 'match lp (Some a) n s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (o : option int) (k0 : nat) (t0 : mem) : option int * mem := match o with Some c => let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (i + c), t) | S m => go m (i + c) (upd 0 i c t) end in go k0 c t0 | None => (None, t0) end.\n')
addA('w_l_cap_let', "", 'match lp a n s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (c : int) (k0 : nat) (t0 : mem) : option int * mem := let e := c + 1 in let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (i + e), t) | S m => go m (i + e) (upd 0 i e t) end in go k0 c t0.\n')
addA('w_l_block_cap', "", 'match lp 1 n a s with (Some v, t) => v + rd 1 a t | (None, _) => 0 end',
     'Definition lp (h : int) (k0 : nat) (i0 : int) (t0 : mem) : option int * mem := let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => go m (i + 1) (upd h i i t) end in go k0 i0 t0.\n')
addA('w_l_writes_mem', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (k0 : nat) (i0 : int) (t0 : mem) : option int * mem := let fix wr (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => wr m (i + 1) (upd 0 i i t) end in let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, wr (S (S O)) i t) | S m => go m (i + 1) t end in go k0 i0 t0.\n')
addA('w_l_num_caller', "", 'lp n a s',
     'Definition lp (k0 : nat) (i0 : int) (t0 : mem) : int := let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => go m (i + 1) (upd 0 i i t) end in match go k0 i0 t0 with (Some v, t) => v + rd 0 i0 t | (None, _) => 0 end.\n')
addA('w_l_where', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (k0 : nat) (i0 : int) (t0 : mem) : option int * mem := (fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => go m (i + 1) (upd 0 i i t) end) k0 i0 t0.\n')
addA('w_t_sum', "", 'match fst (lp n a s) with Some v => v | None => 0 end + rd 0 a (snd (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('w_t_test', "", 'if rd 0 a (snd (lp n a s)) =? 0 then match fst (lp n a s) with Some v => v | None => 1 end else 2',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('w_t_let', "", 'let v := fst (lp n a s) in let t := snd (lp n a s) in match v with Some x => x + rd 0 a t | None => rd 0 b t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('w_t_three', "", 'match fst (lp n a s) with Some v => v + rd 0 a (snd (lp n a s)) + rd 0 b (snd (lp n a s)) | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('w_t_under_if', "", 'if a <? b then match fst (lp n a s) with Some v => v + rd 0 a (snd (lp n a s)) | None => 0 end else rd 0 a s',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('w_t_other_args', "", 'match fst (lp n a s) with Some v => v + rd 0 a (snd (lp n b s)) | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('w_t_in_rec', "", 'outer n a s',
     "Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint outer (j : nat) (a : int) (t : mem) : int := match j with O => rd 0 a t | S j' => match fst (lp 3 a t) with Some v => outer j' v (snd (lp 3 a t)) | None => outer j' a (snd (lp 3 a t)) end end.\n")
addA('w_t_in_row', "", 'match lq n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint lq (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => match fst (lp 3 i t) with Some v => lq m v (snd (lp 3 i t)) | None => (None, snd (lp 3 i t)) end end.\n')
# a value of several numbers and a memory given back by a recursion: through the slot block (step 78)
addA('v_record', "", 'let (r, t) := lp n a s in fa r + fb r + rd 0 a t',
     'Record r2 := mk2 { fa : int; fb : int }.\nFixpoint lp (k : nat) (i : int) (t : mem) : r2 * mem := match k with O => (mk2 i (i + 1), t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_triple', "", "let (r, t) := lp n a s in let '(x, y, z) := r in x + y + z + rd 0 a t",
     'Fixpoint lp (k : nat) (i : int) (t : mem) : (int * int * int) * mem := match k with O => ((i, i + 1, i + 2), t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_opt_pair', "", 'match lp n a s with (Some (x, y), t) => x + y + rd 0 a t | (None, t) => rd 0 a t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (int * int) * mem := match k with O => (None, t) | S m => if rd 0 i t =? 0 then (Some (i, i + 1), t) else lp m (i + 1) (upd 0 i 0 t) end.\n')
addA('v_sum', "", 'match fst (lp n a s) with inl x => x | inr y => y + 1 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : (int + int) * mem := match k with O => (inr i, t) | S m => if rd 0 i t =? 0 then (inl i, t) else lp m (i + 1) t end.\n')
addA('v_data', "", 'match lp n a s with (Okk x y, t) => x + y + rd 0 a t | (Err e, _) => e | (Nope, t) => rd 0 a t end',
     'Inductive res := Okk (x y : int) | Err (e : int) | Nope.\nFixpoint lp (k : nat) (i : int) (t : mem) : res * mem := match k with O => (Nope, t) | S m => if rd 0 i t =? 0 then (Okk i (i + 1), t) else if i <? 0 then (Err i, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_opt_opt', "", 'match fst (lp n a s) with Some (Some v) => v | Some None => 1 | None => 2 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option (option int) * mem := match k with O => (None, t) | S m => if rd 0 i t =? 0 then (Some (Some i), t) else if i <? 0 then (Some None, t) else lp m (i + 1) t end.\n')
addA('v_enum', "", 'match lp n a s with (Red, t) => rd 0 a t | (Green, _) => 1 | (Blue, _) => 2 end',
     'Inductive col := Red | Green | Blue.\nFixpoint lp (k : nat) (i : int) (t : mem) : col * mem := match k with O => (Red, t) | S m => if rd 0 i t =? 0 then (Green, t) else if i <? 0 then (Blue, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_rec_bool', "", 'let (r, t) := lp n a s in if fy r then fx r + rd 0 a t else 0',
     'Record rb := mkb { fx : int; fy : bool }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rb * mem := match k with O => (mkb i true, t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_rec_data', "", 'match lp n a s with (Some r, t) => fa r + fb r + rd 0 a t | (None, _) => 0 end',
     'Record r2 := mk2 { fa : int; fb : int }.\nFixpoint lp (k : nat) (i : int) (t : mem) : option r2 * mem := match k with O => (None, t) | S m => if rd 0 i t =? 0 then (Some (mk2 i i), t) else lp m (i + 1) t end.\n')
addA('v_poly', "", 'match fst (lp n a s) with Okk x => x | Err e => e + 1 end',
     'Inductive res (A : Type) := Okk (x : A) | Err (e : int).\nArguments Okk {A} x.\nArguments Err {A} e.\nFixpoint lp (k : nat) (i : int) (t : mem) : res int * mem := match k with O => (Err i, t) | S m => if rd 0 i t =? 0 then (Okk i, t) else lp m (i + 1) t end.\n')
addA('v_alias', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     'Definition kcell := option int.\nDefinition kst : Type := kcell * mem.\nFixpoint lp (k : nat) (i : int) (t : mem) : kst := match k with O => (None, t) | S m => if rd 0 i t =? 0 then (Some i, t) else lp m (i + 1) t end.\n')
addA('v_value_var', "", 'match fst (lp n (Some a) s) with Some v => v | None => 0 end',
     'Fixpoint lp (k : nat) (d : option int) (t : mem) : option int * mem := match k with O => (d, t) | S m => lp m (Some 1) (upd 0 1 1 t) end.\n')
addA('v_after', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     "Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => match lp m (i + 1) t with (Some v, t') => (Some (v + 1), upd 0 v v t') | (None, t') => (None, t') end end.\n")
addA('v_after_three', "", 'let (r, t) := lp n a s in fa r + fb r + rd 0 a t',
     "Record r2 := mk2 { fa : int; fb : int }.\nFixpoint lp (k : nat) (i : int) (t : mem) : r2 * mem := match k with O => (mk2 i i, t) | S m => let (r, t') := lp m (i + 1) (upd 0 i i t) in (mk2 (fb r) (fa r + 1), upd 0 i (fa r) t') end.\n")
addA('v_two_calls', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => match lp m (i + 1) t with (Some v, t1) => match lp m v t1 with (Some w, t2) => (Some (v + w), upd 0 i w t2) | (None, t2) => (None, t2) end | (None, t1) => (None, t1) end end.\n')
addA('v_counter_second', "", 'match lp a n s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (i : int) (k : nat) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp (i + 1) m (upd 0 i i t) end.\n')
addA('v_mem_first', "", 'match lp s n a with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (t : mem) (k : nat) (i : int) : option int * mem := match k with O => (Some i, t) | S m => lp (upd 0 i i t) m (i + 1) end.\n')
addA('v_two_counters', "", 'match lp 3 n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (j k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp j m (i + 1) (upd 0 i i t) end.\n')
addA('v_record_param', "", 'match lp n (mk2 a b) s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Record r2 := mk2 { fa : int; fb : int }.\nFixpoint lp (k : nat) (r : r2) (t : mem) : option int * mem := match k with O => (Some (fa r), t) | S m => lp m (mk2 (fb r) (fa r)) (upd 0 (fa r) 1 t) end.\n')
addA('v_bool_param', "", 'match lp n true a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (f : bool) (i : int) (t : mem) : option int * mem := match k with O => (if f then Some i else None, t) | S m => lp m (negb f) (i + 1) (upd 0 i i t) end.\n')
addA('v_no_write', "", 'match lp n a s with (Some v, _) => v | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (None, t) | S m => if rd 0 i t =? 0 then (Some i, t) else lp m (i + 1) t end.\n')
addA('v_let_in', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (None, t) | S m => let j := i + 1 in let t1 := upd 0 i j t in if j <? 0 then (Some j, t1) else lp m j t1 end.\n')
addA('v_call_fst', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_snd', "", 'rd 0 a (snd (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_both', "", 'match fst (lp n a s) with Some v => v + rd 0 a (snd (lp n a s)) | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_let', "", 'let p := lp n a s in match fst p with Some v => v + rd 0 a (snd p) | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_let_pat', "", 'let (v, t) := lp n a s in match v with Some x => x + rd 0 a t | None => rd 0 b t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_nested', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, t) => rd 0 b t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_twice', "", 'match lp n a s with (Some v, t) => match lp n v t with (Some w, t2) => w + rd 0 a t2 | (None, _) => 1 end | (None, _) => 2 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_under_if', "", 'if a <? b then match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end else rd 0 a s',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_writes_first', "", 'let t0 := upd 0 a b s in match lp n a (upd 0 b a t0) with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_call_value_given', "", 'let (v, t) := lp n a s in uses v (rd 0 a t)',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nDefinition uses (o : option int) (x : int) : int := match o with Some v => v + x | None => x end.\n')
addA('v_call_in_helper', "", 'wrap n a s + 1',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nDefinition wrap (n : nat) (a : int) (s : mem) : int := match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end.\n')
addA('v_call_in_helper_two', "", 'wrap n a s + wrap n b s',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nDefinition wrap (n : nat) (a : int) (s : mem) : int := match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end.\n')
addA('v_call_in_helper_val', "", 'match wrap n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nDefinition wrap (n : nat) (a : int) (s : mem) : option int * mem := lp n (a + 1) (upd 0 a a s).\n')
addA('v_call_in_loop', "", 'outer n a s',
     "Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint outer (j : nat) (a : int) (t : mem) : int := match j with O => rd 0 a t | S j' => match lp 3 a t with (Some v, t1) => outer j' v t1 | (None, t1) => outer j' (a + 1) (upd 0 a 0 t1) end end.\n")
addA('v_call_in_loop_mem', "", 'rd 0 a (outer n a s)',
     "Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint outer (j : nat) (a : int) (t : mem) : mem := match j with O => t | S j' => match lp 3 a t with (Some v, t1) => outer j' v t1 | (None, t1) => outer j' (a + 1) (upd 0 a 0 t1) end end.\n")
addA('v_call_in_nonlast', "", 'outer n a s',
     "Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint outer (j : nat) (a : int) (t : mem) : int := match j with O => rd 0 a t | S j' => let (v, t1) := lp 3 a t in match v with Some x => x + outer j' a t1 | None => outer j' a t1 end end.\n")
addA('v_callee_rec', "", 'match lq n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint lq (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => match lp 3 i t with (Some v, t1) => lq m v t1 | (None, t1) => (None, t1) end end.\n')
addA('v_callee_tail', "", 'match lq n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint lq (k : nat) (i : int) (t : mem) : option int * mem := match k with O => lp 3 i t | S m => lq m (i + 1) (upd 0 i i t) end.\n')
addA('v_callee_other_value', "", 'let (r, t) := lq n a s in fa r + fb r + rd 0 a t',
     'Record r2 := mk2 { fa : int; fb : int }.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => if rd 0 i t =? 0 then (None, t) else lp m (i + 1) (upd 0 i i t) end.\nFixpoint lq (k : nat) (i : int) (t : mem) : r2 * mem := match k with O => (mk2 i i, t) | S m => match lp 3 i t with (Some v, t1) => lq m v t1 | (None, t1) => (mk2 0 i, t1) end end.\n')
addA('v_callee_mem_rec', "", 'match lp n a s with (Some v, t) => v + rd 1 a t | (None, _) => 0 end',
     'Fixpoint wr (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => wr m (i + 1) (upd 1 i i t) end.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, wr 3 i t) | S m => lp m (i + 1) (wr 2 i t) end.\n')
addA('v_callee_num_mem', "", 'match lp n a s with (Some v, t) => v + rd 1 a t | (None, _) => 0 end',
     'Fixpoint ct (k : nat) (i : int) (t : mem) : int * mem := match k with O => (i, t) | S m => ct m (i + 1) (upd 1 i i t) end.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => let (j, t1) := ct 2 i t in lp m j t1 end.\n')
addA('v_callee_num', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : int := match k with O => i | S m => cnt m (i + rd 0 i t) t end.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (cnt 2 i t), t) | S m => lp m (cnt 2 i t) t end.\n')
addA('v_w_upd32', "", 'match lp n a s with (Some v, t) => v + rd32 1 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (upd32 1 i i t) end.\n')
addA('v_w_upd8', "", 'match lp n a s with (Some v, t) => v + rd8 1 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (upd8 1 i i t) end.\n')
addA('v_w_upd16', "", 'match lp n a s with (Some v, t) => v + rd16 1 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (upd16 1 i i t) end.\n')
addA('v_w_grow', "", 'match lp n a s with (Some v, t) => v + kq_size 2 t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (kq_grow 2 i t) end.\n')
addA('v_w_helper', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition hw (b i v : int) (t : mem) : mem := upd b i v t.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (hw 0 i i t) end.\n')
addA('v_w_const_block', "", 'match lp n a s with (Some v, t) => v + rd blk a t | (None, _) => 0 end',
     'Definition blk : int := 5.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (upd blk i i t) end.\n')
addA('v_w_block_param', "", 'match lp 0 n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (h : int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp h m (i + 1) (upd h i i t) end.\n')
addA('v_w_block_63', "", 'match lp n a s with (Some v, t) => v + rd 63 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (upd 63 i i t) end.\n')
addA('v_w_out', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (kq_out i t) end.\n')
addA('v_w_load', "", 'match lp n a s with (Some v, t) => v + rd 0 0 t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => let t1 := hw_load 4 i 0 0 t in lp m (rd 0 0 t1) t1 end.\n')
addA('v_w_store_fence', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (hw_fence 0 (hw_store 4 i i t)) end.\n')
addA('v_w_read_slot', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (rd 63 0 t), t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_m_rec', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     "Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t') := m t in f x t'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t') => f x t' | (None, t') => (None, t') end.\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nFixpoint lp (k : nat) (i : int) : R int := match k with O => rret i | S m => rbind (rrd 0 i) (fun x => if x =? 0 then rfail else lp m (i + 1)) end.\n")
addA('v_m_write', "", 'rd 0 a (snd (lp n a s))',
     "Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t') := m t in f x t'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t') => f x t' | (None, t') => (None, t') end.\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nFixpoint lp (k : nat) (i : int) : R unit := match k with O => rret tt | S m => rbind (rwr 0 i i) (fun _ => lp m (i + 1)) end.\n")
addA('v_m_pair', "", 'match lp n a s with (Some (x, y), t) => x + y + rd 0 a t | (None, _) => 0 end',
     "Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t') := m t in f x t'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t') => f x t' | (None, t') => (None, t') end.\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nFixpoint lp (k : nat) (i : int) : R (int * int) := match k with O => rret (i, i + 1) | S m => rbind (rwr 0 i i) (fun _ => lp m (i + 1)) end.\n")
addA('v_m_after', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     "Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t') := m t in f x t'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t') => f x t' | (None, t') => (None, t') end.\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nFixpoint lp (k : nat) (i : int) : R int := match k with O => rret i | S m => rbind (lp m (i + 1)) (fun v => rbind (rwr 0 v i) (fun _ => rret (v + 1))) end.\n")
addA('v_m_state_pair', "", 'let (p, t) := lp n a s in fst p + snd p + rd 0 a t',
     "Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t') := m t in f x t'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t') => f x t' | (None, t') => (None, t') end.\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nFixpoint lp (k : nat) (i : int) : M (int * int) := match k with O => ret (i, i) | S m => bind (wrm 0 i i) (fun _ => bind (lp m (i + 1)) (fun p => ret (fst p + 1, snd p))) end.\n")
addA('v_o_mutual', "", 'match la n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint la (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lb m (i + 1) (upd 0 i i t) end\nwith lb (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (None, t) | S m => la m (i + 2) t end.\n')
addA('v_o_given', "", 'match lp (fun x => x + b) n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (f : int -> int) (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (f i), t) | S m => lp f m (f i) (upd 0 i i t) end.\n')
addA('v_o_given_top', "", 'match lp (fun x => x + b) n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (f : int -> int) := fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (f i), t) | S m => go m (f i) (upd 0 i i t) end.\n')
addA('v_o_local_fix', "", 'match lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (k0 : nat) (i0 : int) (t0 : mem) : option int * mem := let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => go m (i + 1) (upd 0 i i t) end in go k0 i0 t0.\n')
addA('v_o_local_fix_cap', "", 'match lp n a b s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Definition lp (k0 : nat) (i0 c : int) (t0 : mem) : option int * mem := let fix go (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (i + c), t) | S m => go m (i + c) (upd 0 i c t) end in go k0 i0 t0.\n')
addA('v_o_program', "", 'match lp a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'From Stdlib Require Import ZArith Lia Program.Wf.\nDefinition mu (x : int) : nat := Z.to_nat (Sint63.to_Z x).\nLemma mu_pred : forall x, (0 <? x) = true -> (mu (x - 1) < mu x)%nat.\nProof.\n  intros x H. unfold mu. apply Sint63.ltb_spec in H. change (Sint63.to_Z 0) with 0%Z in H. change (0 < Sint63.to_Z x)%Z in H.\n  pose proof (Sint63.to_Z_bounded x) as [Bl Bh].\n  assert (Mi : Sint63.to_Z Sint63.max_int = 4611686018427387903%Z) by reflexivity. rewrite Mi in Bh.\n  assert (W2 : (Uint63.wB / 2 = 4611686018427387904)%Z) by reflexivity.\n  assert (E : Sint63.to_Z (x - 1) = (Sint63.to_Z x - 1)%Z).\n  { rewrite Sint63.sub_spec. change (Sint63.to_Z 1) with 1%Z. apply Sint63.cmod_small. rewrite W2. lia. }\n  rewrite E. lia.\nQed.\nProgram Fixpoint lp (x : int) (t : mem) {measure (mu x)} : option int * mem :=\n  match 0 <? x with true => lp (x - 1) (upd 0 x x t) | false => (Some x, t) end.\nNext Obligation. apply mu_pred. auto. Qed.\n')
addA('v_o_poly', "", 'match lp a n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp {A : Type} (d : A) (k : nat) (i : int) (t : mem) : option A * mem := match k with O => (Some d, t) | S m => lp d m (i + 1) (upd 0 i i t) end.\n')
addA('v_o_section', "", 'match lp b n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Section S.\nVariable c : int.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some (i + c), t) | S m => lp m (i + c) (upd 0 i c t) end.\nEnd S.\n')
addA('v_o_module', "", 'match Mv.lp n a s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Module Mv.\nFixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (Some i, t) | S m => lp m (i + 1) (upd 0 i i t) end.\nEnd Mv.\n')
addA('v_o_value_param', "", 'match lp n (Some a) s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (o : option int) (t : mem) : option int * mem := match k with O => (o, t) | S m => match o with Some v => lp m (Some (v + 1)) (upd 0 v v t) | None => (None, t) end end.\n')
addA('v_o_value_mem_param', "", 'match lp n (Some a, s) with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (st : option int * mem) : option int * mem := match k with O => st | S m => match st with (Some v, t) => lp m (Some (v + 1), upd 0 v v t) | (None, t) => (None, t) end end.\n')
addA('v_o_two_mems', "", 'match lp n a s s with (Some v, t) => v + rd 0 a t | (None, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t u : mem) : option int * mem := match k with O => (Some (rd 0 i u), t) | S m => lp m (i + 1) (upd 0 i (rd 0 i u) t) u end.\n')
addA('v_o_ret_in_pair_rev', "", 'match lp n a s with (t, Some v) => v + rd 0 a t | (_, None) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : mem * option int := match k with O => (t, Some i) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_o_ret_triple_mem', "", 'match lp n a s with (x, y, t) => x + y + rd 0 a t end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : int * int * mem := match k with O => (i, i + 1, t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_o_record_mem', "", 'let r := lp n a s in rv r + rw r + rd 0 a (rt r)',
     'Record rm := mkm { rv : int; rw : int; rt : mem }.\nFixpoint lp (k : nat) (i : int) (t : mem) : rm := match k with O => mkm i (i + 1) t | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('v_o_bool_mem_rec', "", 'match lp n a s with (true, t) => rd 0 a t | (false, _) => 0 end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : bool * mem := match k with O => (true, t) | S m => match lp m (i + 1) (upd 0 i i t) with (true, t1) => (i <? 3, t1) | (false, t1) => (false, upd 0 i 0 t1) end end.\n')
addA('v_o_unit_opt_loop', "", 'rd 0 a (snd (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : unit * mem := match k with O => (tt, t) | S m => match lp m (i + 1) (upd 0 i i t) with (_, t1) => (tt, upd 0 i 1 t1) end end.\n')
# a fourth probe: programs written as one writes Rocq (step 77)
addA('p_err_seq', "", 'match fst ((x <-? rrd 0 a ;; y <-? rrd 0 b ;; rret (x + y)) s) with Some v => v | None => 0 end',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t\') => f x t\' | (None, t\') => (None, t\') end.\nNotation "x <-? m ;; k" := (rbind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\n')
addA('p_err_def', "", 'match fst (p a b s) with Some v => v | None => 0 end',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t\') => f x t\' | (None, t\') => (None, t\') end.\nNotation "x <-? m ;; k" := (rbind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nDefinition p (i j : int) : R int := x <-? rrd 0 i ;; _ <-? rwr 0 j x ;; rret (x + 1).\n')
addA('p_err_rec', "", 'match fst (lp n a s) with Some v => v | None => 0 end',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t\') => f x t\' | (None, t\') => (None, t\') end.\nNotation "x <-? m ;; k" := (rbind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nFixpoint lp (k : nat) (i : int) : R int := match k with O => rret i | S m => x <-? rrd 0 i ;; if x =? 0 then rfail else lp m (i + 1) end.\n')
addA('p_err_rec_mem', "", 'rd 0 a (snd (lp n a s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition R (A : Type) : Type := M (option A).\nDefinition rret {A : Type} (x : A) : R A := ret (Some x).\nDefinition rfail {A : Type} : R A := ret None.\nDefinition rbind {A B : Type} (m : R A) (f : A -> R B) : R B := fun t => match m t with (Some x, t\') => f x t\' | (None, t\') => (None, t\') end.\nNotation "x <-? m ;; k" := (rbind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition rrd (h i : int) : R int := fun t => (if i <? 0 then None else Some (rd h i t), t).\nDefinition rwr (h i v : int) : R unit := fun t => if i <? 0 then (None, t) else (Some tt, upd h i v t).\nFixpoint lp (k : nat) (i : int) : R unit := match k with O => rret tt | S m => _ <-? rwr 0 i i ;; lp m (i + 1) end.\n')
addA('p_res_def', "", 'match safediv a b with Ok v => v | Err c => c end',
     'Inductive res := Ok (x : int) | Err (c : int).\nDefinition safediv (x y : int) : res := if y =? 0 then Err 1 else Ok (x / y).\n')
addA('p_res_rec', "", 'match f n a with Ok v => v | Err c => c end',
     'Inductive res := Ok (x : int) | Err (c : int).\nFixpoint f (k : nat) (x : int) : res := match k with O => Ok x | S m => if x <? 0 then Err x else f m (x - 1) end.\n')
addA('p_res_mem', "", 'let (r, t) := g a s in match r with Ok v => rd 0 v t | Err c => c end',
     'Inductive res := Ok (x : int) | Err (c : int).\nDefinition g (x : int) (t : mem) : res * mem := if x <? 0 then (Err x, t) else (Ok x, upd 0 x x t).\n')
addA('p_res_mem_rec', "", 'let (r, t) := g n a s in match r with Ok v => rd 0 v t | Err c => c end',
     'Inductive res := Ok (x : int) | Err (c : int).\nFixpoint g (k : nat) (x : int) (t : mem) : res * mem := match k with O => (Ok x, t) | S m => if x <? 0 then (Err x, t) else g m (x - 1) (upd 0 x x t) end.\n')
addA('p_ring', "", 'let (x, t) := pop (push a (push b s)) in x + rd 0 0 t',
     'Definition push (x : int) (t : mem) : mem := let h := rd 0 0 t in upd 0 (1 + (h land 7)) x (upd 0 0 (h + 1) t).\nDefinition pop (t : mem) : int * mem := let h := rd 0 1 t in (rd 0 (2 + (h land 7)) t, upd 0 1 (h + 1) t).\n')
addA('p_bitmap', "", 'fst0 n 0 (setb a s)',
     'Definition setb (i : int) (t : mem) : mem := upd 0 (i >> 6) (rd 0 (i >> 6) t lor (1 << (i land 63))) t.\nDefinition getb (i : int) (t : mem) : bool := ((rd 0 (i >> 6) t >> (i land 63)) land 1) =? 1.\nFixpoint fst0 (k : nat) (i : int) (t : mem) : int := match k with O => i | S m => if getb i t then fst0 m (i + 1) t else i end.\n')
addA('p_bsearch', "", 'bs n 0 a b s',
     'Fixpoint bs (k : nat) (lo hi v : int) (t : mem) : int := match k with O => lo | S m => if hi <=? lo then lo else let mid := (lo + hi) / 2 in if rd 0 mid t <? v then bs m (mid + 1) hi v t else bs m lo mid v t end.\n')
addA('p_isort', "", 'rd 0 a (srt n 1 s)',
     'Fixpoint ins (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => if i <=? 0 then t else let x := rd 0 i t in let y := rd 0 (i - 1) t in if y <=? x then t else ins m (i - 1) (upd 0 (i - 1) x (upd 0 i y t)) end.\nFixpoint srt (k : nat) (i : int) (t : mem) : mem := match k with O => t | S m => srt m (i + 1) (ins (kq_nat i) i t) end.\n')
addA('p_hash', "", 'if get n (slot a) a (put n (slot a) a s) then a else b',
     'Definition slot (x : int) : int := (x * 31) land 15.\nFixpoint put (k : nat) (i x : int) (t : mem) : mem := match k with O => t | S m => let j := i land 15 in if rd 0 j t =? 0 then upd 0 j x t else put m (i + 1) x t end.\nFixpoint get (k : nat) (i x : int) (t : mem) : bool := match k with O => false | S m => let j := i land 15 in let v := rd 0 j t in if v =? x then true else if v =? 0 then false else get m (i + 1) x t end.\n')
addA('p_sieve', "", 'rd 0 a (sv n 2 s)',
     'Fixpoint mark (k : nat) (i p : int) (t : mem) : mem := match k with O => t | S m => mark m (i + p) p (upd 0 i 1 t) end.\nFixpoint sv (k : nat) (p : int) (t : mem) : mem := match k with O => t | S m => let t1 := if rd 0 p t =? 0 then mark (kq_nat (100 / p)) (p * p) p t else t in sv m (p + 1) t1 end.\n')
addA('p_matmul', "", 'inner n a b 0 s',
     'Fixpoint inner (k : nat) (i j acc : int) (t : mem) : int := match k with O => acc | S m => inner m (i + 1) (j + 4) (acc + rd 0 i t * rd 1 j t) t end.\n')
addA('p_gcd_int', "", 'gcd n a b',
     'Fixpoint gcd (k : nat) (x y : int) : int := match k with O => x | S m => if y =? 0 then x else gcd m y (x mod y) end.\n')
addA('p_pow_mod', "", 'pw n a b 1 1000003',
     'Fixpoint pw (k : nat) (x e acc p : int) : int := match k with O => acc | S m => if e =? 0 then acc else pw m (x * x mod p) (e >> 1) (if (e land 1) =? 1 then acc * x mod p else acc) p end.\n')
addA('p_two_results', "", 'let (x, y) := mm n a b b s in y - x',
     'Fixpoint mm (k : nat) (i lo hi : int) (t : mem) : int * int := match k with O => (lo, hi) | S m => let v := rd 0 i t in mm m (i + 1) (if v <? lo then v else lo) (if hi <? v then v else hi) t end.\n')
addA('p_three_results', "", "let '(p, q, r) := st n a 0 0 1 s in p + q + r",
     'Fixpoint st (k : nat) (i x y z : int) (t : mem) : int * int * int := match k with O => (x, y, z) | S m => st m (i + 1) (x + rd 0 i t) (y + 1) (z * 2) t end.\n')
addA('p_class_use', "", 'mx a b',
     'Class Ord (A : Type) := { lt : A -> A -> bool }.\n#[export] Instance ord_int : Ord int := { lt := fun x y => x <? y }.\nDefinition mx {A : Type} `{Ord A} (x y : A) : A := if lt x y then y else x.\n')
addA('p_class_rec', "", 'mxn n a b',
     'Class Ord (A : Type) := { lt : A -> A -> bool }.\n#[export] Instance ord_int : Ord int := { lt := fun x y => x <? y }.\nFixpoint mxn {A : Type} `{Ord A} (k : nat) (x y : A) : A := match k with O => x | S m => mxn m (if lt x y then y else x) y end.\n')
addA('p_class_two', "", 'fst (@dflt (int * int) _) + a',
     'Class Dflt (A : Type) := { dflt : A }.\n#[export] Instance d_int : Dflt int := { dflt := 7 }.\n#[export] Instance d_pair {A B} `{Dflt A} `{Dflt B} : Dflt (A * B) := { dflt := (dflt, dflt) }.\n')
addA('p_class_monad', "", 'fst ((mbind (m := St) (fun t => (rd 0 a t, t)) (fun x => mret (x + 1))) s)',
     "Class Monad (m : Type -> Type) := { mret : forall {A}, A -> m A; mbind : forall {A B}, m A -> (A -> m B) -> m B }.\nDefinition St (A : Type) : Type := mem -> A * mem.\n#[export] Instance st_m : Monad St := { mret := fun _ x t => (x, t); mbind := fun _ _ m f t => let (x, t') := m t in f x t' }.\n")
addA('p_class_field', "", 'at_ a + at_ b',
     'Class Cfg := { base : int; size : int }.\n#[export] Instance c0 : Cfg := { base := 8; size := 64 }.\nDefinition at_ `{Cfg} (i : int) : int := base + (i mod size).\n')
addA('p_canon', "", '@op imon a (@un imon)',
     'Structure mon := { cr : Type; op : cr -> cr -> cr; un : cr }.\nDefinition imon : mon := {| cr := int; op := fun x y => x + y; un := 0 |}.\n')
addA('p_sec_var', "", 'f 3 n a',
     'Section S.\nVariable d : int.\nFixpoint f (k : nat) (x : int) : int := match k with O => x | S m => f m (x + d) end.\nEnd S.\n')
addA('p_sec_fun', "", 'f (fun y => y + 1) n a',
     'Section S.\nVariable g : int -> int.\nFixpoint f (k : nat) (x : int) : int := match k with O => x | S m => f m (g x) end.\nEnd S.\n')
addA('p_sec_ctx', "", 'twc (fun y : int => y * 2) a',
     'Section S.\nContext {T : Type} (g : T -> int).\nDefinition twc (x : T) : int := g x + g x.\nEnd S.\n')
addA('p_sec_let', "", 'f a b',
     'Section S.\nVariable c : int.\nLet d := c + 1.\nDefinition f (x : int) : int := x + d.\nEnd S.\n')
addA('p_mod_type', "", 'M1.f a',
     'Module Type T.\nParameter v : int.\nParameter f : int -> int.\nEnd T.\nModule M1 <: T.\nDefinition v : int := 3.\nDefinition f (x : int) : int := x + v.\nEnd M1.\n')
addA('p_functor', "", 'G.g a',
     'Module Type T.\nParameter v : int.\nEnd T.\nModule F (X : T).\nDefinition g (x : int) : int := x + X.v.\nEnd F.\nModule M1 <: T.\nDefinition v : int := 3.\nEnd M1.\nModule G := F M1.\n')
addA('p_proof_arg', "", '(if PrimInt63.lesb 0 a as c return PrimInt63.lesb 0 a = c -> int then fun H => gt1 a H s else fun _ => 0) eq_refl',
     'Definition gt1 (i : int) (H : PrimInt63.lesb 0 i = true) (t : mem) : int := rd 0 i t.\n')
addA('p_proof_arg_rec', "", 'f 5 (ltac:(repeat constructor) : (5 <= 100)%nat) a',
     'Fixpoint f (k : nat) (H : (k <= 100)%nat) (x : int) {struct k} : int := match k as k0 return (k0 <= 100)%nat -> int with O => fun _ => x | S m => fun H0 => f m (PeanoNat.Nat.le_trans _ _ _ (PeanoNat.Nat.le_succ_diag_r m) H0) (x + 1) end H.\n')
addA('p_sig_arg', "", '(if PrimInt63.lesb 0 a as c return PrimInt63.lesb 0 a = c -> int then fun H => g (exist _ a H) else fun _ => 0) eq_refl',
     'Definition g (x : {y : int | PrimInt63.lesb 0 y = true}) : int := proj1_sig x + 1.\n')
addA('p_dep_pair', "", 'hd2 (existT _ n a)',
     'Definition hd2 (p : {n0 : nat & int}) : int := projT2 p.\n')
addA('p_ex_falso', "", 'a',
     'Definition un (x : int) (H : False) : int := match H with end.\n')
addA('p_eq_rect', "", 'cst n n eq_refl a',
     'Definition cst (n0 m : nat) (e : n0 = m) (x : int) : int := match e with eq_refl => x end.\n')
addA('p_program_def', "", 'proj1_sig (pd a)',
     'From Stdlib Require Import Program.\nProgram Definition pd (x : int) : {y : int | True} := x + 1.\n')
addA('p_where', "", 'ev n a',
     'Fixpoint ev (k : nat) (x : int) : int := match k with O => x | S m => od m (x + 1) end\nwith od (k : nat) (x : int) : int := match k with O => x * 2 | S m => ev m (x - 1) end.\n')
addA('p_let_fix', "", '(fix f (k : nat) (x : int) : int := match k with O => x | S m => f m (x + b) end) n a',
     '')
addA('p_let_fix_mem', "", 'rd 0 a ((fix f (k : nat) (x : int) (t : mem) : mem := match k with O => t | S m => f m (x + 1) (upd 0 x b t) end) n a s)',
     '')
addA('p_nested_rec', "", 'outer n a',
     'Fixpoint inner (k : nat) (x : int) : int := match k with O => x | S m => inner m (x + 1) end.\nFixpoint outer (k : nat) (x : int) : int := match k with O => x | S m => outer m (inner k x) end.\n')
addA('p_cps', "", 'f n a (fun v => v * 2)',
     'Fixpoint f (k : nat) (x : int) (c : int -> int) : int := match k with O => c x | S m => f m (x + 1) c end.\n')
addA('p_cps_grow', "", 'f n a (fun v => v)',
     'Fixpoint f (k : nat) (x : int) (c : int -> int) : int := match k with O => c x | S m => f m (x + 1) (fun v => c (v + x)) end.\n')
addA('p_fun_result', "", 'app (add a) b',
     'Definition add (x : int) : int -> int := fun y => x + y.\nDefinition app (g : int -> int) (x : int) : int := g x.\n')
addA('p_compose', "", 'cmp (fun y => y + 1) (fun y => y * 2) a',
     'Definition cmp {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).\n')
addA('p_pipe', "", 'a |> (fun y => y + 1) |> (fun y => y * b)',
     'Notation "x |> f" := (f x) (at level 40, left associativity).\n')
addA('p_iter_lib', "", 'Nat.iter n (fun y => y + 1) a',
     '')
addA('p_iter_lib_pair', "", 'fst (Nat.iter n (fun p => (snd p, fst p + snd p)) (a, b))',
     '')
addA('p_iter_lib_mem', "", 'rd 0 a (Nat.iter n (fun t => upd 0 a (rd 0 a t + 1) t) s)',
     '')
addA('p_nat_rect_ty', "", 'nat_rect (fun _ => int) a (fun _ r => r + b) n',
     '')
addA('p_if_let', "", 'let x := if a <? b then a else b in let y := if x =? 0 then 1 else x in x + y',
     '')
addA('p_bool_fun', "", 'if both isodd a b then a else b',
     'Definition isodd (x : int) : bool := (x land 1) =? 1.\nDefinition both (f : int -> bool) (x y : int) : bool := f x && f y.\n')
addA('p_opt_map', "", 'match option_map (fun x => x + 1) (if a <? b then Some a else None) with Some v => v | None => b end',
     '')
addA('p_opt_default', "", 'odf (if a <? b then Some a else None) b',
     'Definition odf (o : option int) (d : int) : int := match o with Some v => v | None => d end.\n')
addA('p_opt_rec', "", 'match find n a b s with Some i => i | None => 0 end',
     'Fixpoint find (k : nat) (i v : int) (t : mem) : option int := match k with O => None | S m => if rd 0 i t =? v then Some i else find m (i + 1) v t end.\n')
addA('p_opt_opt', "", 'match oo a with None => 0 | Some None => 1 | Some (Some v) => v end',
     'Definition oo (x : int) : option (option int) := if x <? 0 then None else if x =? 0 then Some None else Some (Some x).\n')
addA('p_sum_rec', "", 'match fs n a with inl v => v | inr c => if c then 1 else 0 end',
     'Fixpoint fs (k : nat) (x : int) : int + bool := match k with O => inl x | S m => if x <? 0 then inr true else fs m (x - 1) end.\n')
addA('p_list_lit', "", 'fold_left (fun acc x => acc + x) [a; b; 3] 0',
     'From Stdlib Require Import List.\nImport ListNotations.\n')
addA('p_list_map', "", 'fold_left (fun acc x => acc + x) (map (fun y => y * 2) [a; b]) 0',
     'From Stdlib Require Import List.\nImport ListNotations.\n')
addA('p_list_len', "", 'Uint63.of_nat (length [a; b; 3])',
     'From Stdlib Require Import List.\nImport ListNotations.\n')
addA('p_list_nth', "", 'nth 1 [a; b; 3] 0',
     'From Stdlib Require Import List.\nImport ListNotations.\n')
addA('p_list_rec_lit', "", 'sm (cons a (cons b nil))',
     'Fixpoint sm (l : list int) : int := match l with nil => 0 | cons x r => x + sm r end.\n')
addA('p_list_built', "", 'sm (up n a)',
     'Fixpoint up (k : nat) (x : int) : list int := match k with O => nil | S m => cons x (up m (x + 1)) end.\nFixpoint sm (l : list int) : int := match l with nil => 0 | cons x r => x + sm r end.\n')
addA('p_vector', "", 'Vector.hd (Vector.cons int a 0 (Vector.nil int))',
     'From Stdlib Require Import Vector.\n')
addA('p_fin', "", 'idx (@Fin.F1 1) + a',
     'From Stdlib Require Import Fin.\nDefinition idx (i : Fin.t 2) : int := match i with Fin.F1 _ => 1 | Fin.FS _ _ => 2 end.\n')
addA('p_string_len', "", 'if String.eqb "ab" "ab" then a else b',
     'From Stdlib Require Import String.\nOpen Scope string_scope.\n')
addA('p_ascii', "", 'Uint63.of_nat (nat_of_ascii "a"%char) + a',
     'From Stdlib Require Import Ascii.\n')
addA('p_z_lit', "", 'Uint63.of_Z 42%Z + a',
     'From Stdlib Require Import ZArith.\n')
addA('p_z_to_int', "", 'Uint63.of_Z sz + a',
     'From Stdlib Require Import ZArith.\nDefinition sz : Z := 64.\n')
addA('p_nat_const', "", 'f K a',
     'Definition K : nat := 16.\nFixpoint f (k : nat) (x : int) : int := match k with O => x | S m => f m (x + 1) end.\n')
addA('p_int_const', "", '(a + MASK) land (PrimInt63.lxor MASK 4611686018427387903)',
     'Definition PAGE : int := 4096.\nDefinition MASK : int := PAGE - 1.\n')
addA('p_u64_ops', "", 'a',
     'Definition mk (x : int) : u64 := u64_of_int x.\n')
addA('p_byte_ops', "", 'rd16le a s',
     'Definition rd16le (i : int) (t : mem) : int := rd8 0 i t lor (rd8 0 (i + 1) t << 8).\n')
addA('p_rd32_ops', "", 'g a s',
     'Definition g (i : int) (t : mem) : int := rd32 0 i t + 1.\n')
addA('p_grow', "", 'kq_size 0 (ens 0 a s)',
     'Definition ens (h n0 : int) (t : mem) : mem := if kq_size h t <? n0 then kq_grow h n0 t else t.\n')
addA('p_io', "", 'rd 0 0 (rdn n s)',
     'Fixpoint rdn (k : nat) (t : mem) : mem := match k with O => t | S m => rdn m (kq_in 0 0 t) end.\n')
addA('p_hw_poll', "", 'rd 0 0 (poll n a s)',
     'Fixpoint poll (k : nat) (x : int) (t : mem) : mem := match k with O => t | S m => let t1 := hw_load 4 x 0 0 t in if (rd 0 0 t1 land 1) =? 1 then t1 else poll m x t1 end.\n')
addA('p_hw_spin', "", 'rd 0 1 (lock a s)',
     'Definition lock (x : int) (t : mem) : mem := hw_cas 4 x 0 1 0 0 t.\n')
addA('p_pagewalk', "", 'walk 4 a b 3 s',
     'Definition idx (v l : int) : int := (v >> (12 + 9 * l)) land 511.\nFixpoint walk (k : nat) (tb v l : int) (t : mem) : int := match k with O => tb | S m => let e := rd tb (idx v l) t in if (e land 1) =? 0 then 0 else walk m (e >> 12) v (l - 1) t end.\n')
addA('p_sched', "", 'tid (pick n a (mkt 0 0 0) s)',
     'Record task := mkt { tid : int; prio : int; tleft : int }.\nDefinition better (x y : task) : task := if prio x <? prio y then y else x.\nFixpoint pick (k : nat) (i : int) (best : task) (t : mem) : task := match k with O => best | S m => pick m (i + 3) (better best (mkt (rd 0 i t) (rd 0 (i + 1) t) (rd 0 (i + 2) t))) t end.\n')
addA('p_sm_io', "", 'match run n a Idle s with Idle => 0 | Rx k => k | Tx k => k + 100 end',
     'Inductive st := Idle | Rx (n0 : int) | Tx (n0 : int).\nDefinition step (x : st) (c : int) : st := match x with Idle => if c =? 1 then Rx 0 else Idle | Rx k => if c =? 0 then Tx k else Rx (k + 1) | Tx k => if k =? 0 then Idle else Tx (k - 1) end.\nFixpoint run (k : nat) (i : int) (x : st) (t : mem) : st := match k with O => x | S m => run m (i + 1) (step x (rd 0 i t)) t end.\n')
addA('p_rec_mem_state', "", 'let (d, t) := wr (mkd a 0) b s in cnt d + rd 0 a t',
     'Record dev := mkd { bs : int; cnt : int }.\nDefinition wr (d : dev) (v : int) (t : mem) : dev * mem := (mkd (bs d) (cnt d + 1), upd 0 (bs d + cnt d) v t).\n')
addA('p_rec_mem_loop', "", 'let (d, t) := fill n (mkd a 0) s in cnt d + rd 0 a t',
     'Record dev := mkd { bs : int; cnt : int }.\nFixpoint fill (k : nat) (d : dev) (t : mem) : dev * mem := match k with O => (d, t) | S m => fill m (mkd (bs d) (cnt d + 1)) (upd 0 (bs d + cnt d) 7 t) end.\n')
addA('p_nat_len', "", 'Uint63.of_nat (cnt n a s)',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('p_nat_len_cmp', "", 'if Nat.leb (cnt n a s) 3 then a else b',
     'Fixpoint cnt (k : nat) (i : int) (t : mem) : nat := match k with O => O | S m => if rd 0 i t =? 0 then cnt m (i + 1) t else S (cnt m (i + 1) t) end.\n')
addA('p_nat_add', "", 'Uint63.of_nat (tw n) + a',
     'Fixpoint tw (k : nat) : nat := match k with O => O | S m => S (S (tw m)) end.\n')
# a function giving back a value and a proof: the value alone (step 76)
addA('e_sig_def', "", 'proj1_sig (clamp a)',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\n')
addA('e_sig_tactic', "", 'proj1_sig (clamp a) + 1',
     'Definition clamp (x : int) : { y : int | (y <? 0) = false \\/ True }.\nProof. exists (if x <? 0 then 0 else x). right. exact I. Defined.\n')
addA('e_sig_let', "", "let 'exist y _ := clamp a in y + 1",
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\n')
addA('e_sig_match', "", 'match clamp a with exist y _ => y * 2 end',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\n')
addA('e_sig_two', "", 'proj1_sig (clamp a) + proj1_sig (clamp b)',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\n')
addA('e_sig_arg', "", 'k (proj1_sig (clamp a))',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\nDefinition k (x : int) : int := x + 1.\n')
addA('e_sig_spec', "", 'proj1_sig (same a)',
     'Definition same (x : int) : {y : int | y = x} := exist _ x eq_refl.\n')
addA('e_sig_spec_if', "", 'proj1_sig (cl a)',
     'Definition cl (x : int) : {y : int | y = x \\/ y = 0}.\nProof. destruct (x <? 0) eqn:E; [exists 0; right; reflexivity | exists x; left; reflexivity]. Defined.\n')
addA('e_sig_mem', "", 'proj1_sig (rdp a s)',
     'Definition rdp (i : int) (t : mem) : {y : int | True} := exist _ (rd 0 i t) I.\n')
addA('e_sig_rec', "", 'proj1_sig (lp n a)',
     'Fixpoint lp (k : nat) (i : int) : {y : int | True} := match k with O => exist _ i I | S m => lp m (i + 1) end.\n')
addA('e_sig_rec_match', "", 'match lp n a with exist y _ => y + b end',
     'Fixpoint lp (k : nat) (i : int) : {y : int | True} := match k with O => exist _ i I | S m => lp m (i + 1) end.\n')
addA('e_sig_rec_let', "", "let 'exist y _ := lp n a in y + b",
     'Fixpoint lp (k : nat) (i : int) : {y : int | True} := match k with O => exist _ i I | S m => lp m (i + 1) end.\n')
addA('e_sig_rec_mem', "", 'proj1_sig (lp n a s)',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : {y : int | True} := match k with O => exist _ (rd 0 i t) I | S m => lp m (i + 1) t end.\n')
addA('e_sig_nontail', "", 'proj1_sig (lp n a)',
     'Fixpoint lp (k : nat) (i : int) : {y : int | True} := match k with O => exist _ i I | S m => match lp m (i + 1) with exist y _ => exist _ (y + i) I end end.\n')
addA('e_sig_proj_own', "", 'proj1_sig (lp n a)',
     'Fixpoint lp (k : nat) (i : int) : {y : int | True} := match k with O => exist _ i I | S m => exist _ (proj1_sig (lp m (i + 1)) + i) I end.\n')
addA('e_sig_if', "", 'proj1_sig (lp n a)',
     'Fixpoint lp (k : nat) (i : int) : {y : int | True} := match k with O => exist _ i I | S m => if i <? 9 then lp m (i + 1) else exist _ i I end.\n')
addA('e_sig_calls', "", 'proj1_sig (g a)',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\nDefinition g (x : int) : {y : int | True} := exist _ (proj1_sig (clamp x) + 1) I.\n')
addA('e_sig_helper_rec', "", 'h2 n a',
     'Fixpoint lp (k : nat) (i : int) : {y : int | True} := match k with O => exist _ i I | S m => lp m (i + 1) end.\nDefinition h2 (k : nat) (x : int) : int := proj1_sig (lp k x) + 1.\n')
addA('e_sig_pair', "", 'fst (proj1_sig (pr a b))',
     'Definition pr (x y : int) : {p : int * int | True} := exist _ (x, y) I.\n')
addA('e_sig_bool', "", 'if proj1_sig (t a) then a else b',
     'Definition t (x : int) : {c : bool | True} := exist _ (x <? 0) I.\n')
addA('e_sig_nat', "", 'if Nat.ltb (proj1_sig (cn n)) 3 then a else b',
     'Definition cn (k : nat) : {m : nat | True} := exist _ (S k) I.\n')
addA('e_sig_param', "", 'u (clamp a)',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\nDefinition u (x : {y : int | True}) : int := proj1_sig x + 1.\n')
addA('e_sig_field', "", 'proj1_sig (fst (pp a))',
     'Definition clamp (x : int) : {y : int | True} := exist _ (if x <? 0 then 0 else x) I.\nDefinition pp (x : int) : {y : int | True} * int := (clamp x, x).\n')
addA('e_sb_def', "", 'if neg a then a else b',
     'Definition neg (x : int) : {True} + {True} := if x <? 0 then left I else right I.\n')
addA('e_sb_match', "", 'match neg a with left _ => a | right _ => b end',
     'Definition neg (x : int) : {True} + {True} := if x <? 0 then left I else right I.\n')
addA('e_sb_two', "", '(if neg a then 1 else 2) + (if neg b then 3 else 4)',
     'Definition neg (x : int) : {True} + {True} := if x <? 0 then left I else right I.\n')
addA('e_sb_let', "", 'let c := neg a in if c then a else b',
     'Definition neg (x : int) : {True} + {True} := if x <? 0 then left I else right I.\n')
addA('e_sb_negb', "", 'if negb (if neg a then true else false) then a else b',
     'Definition neg (x : int) : {True} + {True} := if x <? 0 then left I else right I.\n')
addA('e_sb_rec', "", 'if fnd n a s then a else b',
     'Fixpoint fnd (k : nat) (i : int) (t : mem) : {True} + {True} := match k with O => right I | S m => if rd 0 i t =? 7 then left I else fnd m (i + 1) t end.\n')
addA('e_sb_own', "", 'if od n a then a else b',
     'Fixpoint od (k : nat) (i : int) : {True} + {True} := match k with O => right I | S m => if od m (i + 1) then right I else left I end.\n')
addA('e_sb_tactic', "", 'if isz a then a else b',
     'Definition isz (x : int) : {x = 0} + {x <> 0}.\nProof. destruct (x =? 0) eqn:E; [left; apply Uint63.eqb_spec in E; exact E | right; intro H; subst x; discriminate E]. Defined.\n')
addA('e_sb_calls', "", 'if g a then a else b',
     'Definition neg (x : int) : {True} + {True} := if x <? 0 then left I else right I.\nDefinition g (x : int) : {True} + {True} := if neg x then right I else left I.\n')
addA('e_sb_helper_rec', "", 'h2 n a s',
     'Fixpoint fnd (k : nat) (i : int) (t : mem) : {True} + {True} := match k with O => right I | S m => if rd 0 i t =? 7 then left I else fnd m (i + 1) t end.\nDefinition h2 (k : nat) (x : int) (t : mem) : int := if fnd k x t then 1 else 0.\n')
addA('e_sb_proof_used', "", 'match isz a with left p => a | right p => b end',
     'Definition isz (x : int) : {x = 0} + {x <> 0}.\nProof. destruct (x =? 0) eqn:E; [left; apply Uint63.eqb_spec in E; exact E | right; intro H; subst x; discriminate E]. Defined.\n')
addA('e_sb_result', "", 'if nz a then a else b',
     'Definition nz (x : int) : {x = 0} + {x <> 0} := Uint63.eqs x 0.\n')
addA('e_enum_scheme', "", 'if color_eq_dec (if a <? b then Red else Green) Blue then a else b',
     'Inductive color := Red | Green | Blue.\nScheme Equality for color.\n')
addA('e_enum_decide', "", 'if cdec (if a <? b then Red else Green) Blue then a else b',
     'Inductive color := Red | Green | Blue.\nDefinition cdec (x y : color) : {x = y} + {x <> y}.\nProof. decide equality. Defined.\n')
# the bytes in bulk: functions of the kit over the byte loads and stores (step 75)
addA('h_fill', "", 'rd 0 a (hw_fill 268435456 7 b s)',
     '')
addA('h_fill_var', "", 'rd 0 a (hw_fill a b 16 s)',
     '')
addA('h_copy', "", 'rd 0 a (hw_copy a b 8 0 1 s)',
     '')
addA('h_copy_var', "", 'rd 0 a (hw_copy a b (rd 0 0 s) 0 1 s)',
     '')
addA('h_copy_cell', "", 'rd a b (hw_copy a b 8 a b s)',
     '')
addA('h_cmp', "", 'rd 0 1 (hw_cmp a b 8 0 1 s)',
     '')
addA('h_cmp_var', "", 'rd 0 1 (hw_cmp a b (a + b) 0 1 s)',
     '')
addA('h_let', "", 'let t := hw_copy a b 8 0 1 s in rd 0 1 t',
     '')
addA('h_chain', "", 'rd 0 1 (hw_copy a b 8 0 1 (hw_fill a 7 16 s))',
     '')
addA('h_two', "", 'let t := hw_fill a 7 16 s in let u := hw_copy a b 8 0 1 t in hw_load_kq a u',
     'Definition hw_load_kq (x : int) (t : mem) : int := rd 0 1 (hw_load 1 x 0 1 t).\n')
addA('h_test', "", 'let t := hw_cmp a b 8 0 1 s in if rd 0 1 t =? 0 then rd 0 2 t else b',
     '')
addA('h_choice', "", 'let t := if a <? b then hw_fill a 7 16 s else hw_fill b 7 16 s in rd 0 0 t',
     '')
addA('h_choice_two', "", 'let t := if a <? b then hw_copy a b 8 0 1 s else hw_fill b 7 16 s in rd 0 0 t',
     '')
addA('h_helper', "", 'rd 0 0 (clr a (clr b s))',
     'Definition clr (x : int) (t : mem) : mem := hw_fill x 0 16 t.\n')
addA('h_helper_cmp', "", 'if same a b s then a else b',
     'Definition same (x y : int) (t : mem) : bool := rd 0 1 (hw_cmp x y 8 0 1 t) =? 0.\n')
addA('h_loop', "", 'rd 0 a (lp n a s)',
     'Fixpoint lp (k : nat) (x : int) (t : mem) : mem := match k with O => t | S m => lp m (x + 16) (hw_fill x 0 16 t) end.\n')
addA('h_loop_copy', "", 'rd 0 a (lp n a s)',
     'Fixpoint lp (k : nat) (x : int) (t : mem) : mem := match k with O => t | S m => lp m (x + 16) (hw_copy x (x + 8) 8 0 1 t) end.\n')
addA('h_loop_cmp', "", 'lp n a s',
     'Fixpoint lp (k : nat) (x : int) (t : mem) : int := match k with O => 0 | S m => let u := hw_cmp x (x + 8) 8 0 1 t in rd 0 1 u + lp m (x + 16) u end.\n')
addA('h_match', "", 'rd 0 0 (match n with O => s | S _ => hw_fill a 0 8 s end)',
     '')
addA('h_monad', "", 'fst (wrm a s)',
     'Definition wrm (x : int) (t : mem) : int * mem := let u := hw_fill x 0 8 t in (rd 0 0 u, u).\n')
addA('h_unit', "", 'rd 0 0 (snd (wru a s))',
     'Definition wru (x : int) (t : mem) : unit * mem := (tt, hw_fill x 0 8 t).\n')
# the signed quotient: what the text shows of the one case Rocq's axioms leave open (step 74)
addA('s_slash_var', "", 'a / b',
     '')
addA('s_slash_lit', "", 'a / 7',
     '')
addA('s_slash_neg', "", 'a / (0 - 3)',
     '')
addA('s_mod_var', "", 'a mod b',
     '')
addA('s_slash_loop', "", 'lp n a b',
     'Fixpoint lp (k : nat) (i c : int) : int := match k with O => i | S m => lp m (i / c) c end.\n')
addA('s_lit_b', "", 'PrimInt63.divs a 7',
     '')
addA('s_lit_b_neg', "", 'PrimInt63.divs a (0 - 3)',
     '')
addA('s_lit_a', "", 'PrimInt63.divs 7 b',
     '')
addA('s_lit_both', "", 'PrimInt63.divs 42 5',
     '')
addA('s_lit_min_m1', "", 'PrimInt63.divs (PrimInt63.lsl 1 62) (0 - 1)',
     '')
addA('s_lit_let', "", 'let d := 7 in PrimInt63.divs a d',
     '')
addA('s_sint_lit', "", 'Sint63.div a 2',
     '')
addA('s_test_m1', "", 'if b =? (0 - 1) then 0 else PrimInt63.divs a b',
     '')
addA('s_test_m1_sym', "", 'if (0 - 1) =? b then 0 else PrimInt63.divs a b',
     '')
addA('s_test_pos', "", 'if 0 <? b then PrimInt63.divs a b else 0',
     '')
addA('s_test_nonneg', "", 'if 0 <=? b then PrimInt63.divs a b else 0',
     '')
addA('s_test_rlt', "", 'if b <? 0 then 0 else PrimInt63.divs a b',
     '')
addA('s_test_rle', "", 'if b <=? 0 then 0 else PrimInt63.divs a b',
     '')
addA('s_test_a_pos', "", 'if 0 <? a then PrimInt63.divs a b else 0',
     '')
addA('s_test_a_nonneg', "", 'if 0 <=? a then PrimInt63.divs a b else 0',
     '')
addA('s_test_a_rlt', "", 'if a <? 0 then 0 else PrimInt63.divs a b',
     '')
addA('s_test_a_min', "", 'if a =? (PrimInt63.lsl 1 62) then 0 else PrimInt63.divs a b',
     '')
addA('s_test_negb', "", 'if negb (b =? (0 - 1)) then PrimInt63.divs a b else 0',
     '')
addA('s_test_and', "", 'if (0 <? b) && (a <? 9) then PrimInt63.divs a b else 0',
     '')
addA('s_test_or', "", 'if (b =? (0 - 1)) || (a <? 9) then 0 else PrimInt63.divs a b',
     '')
addA('s_test_match', "", 'match 0 <? b with true => PrimInt63.divs a b | false => 0 end',
     '')
addA('s_test_let', "", 'let t := 0 <? b in if t then PrimInt63.divs a b else 0',
     '')
addA('s_test_let_arg', "", 'let d := b + 1 in if 0 <? d then PrimInt63.divs a d else 0',
     '')
addA('s_test_expr', "", 'if 0 <? b + 1 then PrimInt63.divs a (b + 1) else 0',
     '')
addA('s_test_read', "", 'let d := rd 0 a s in if 0 <? d then PrimInt63.divs b d else 0',
     '')
addA('s_test_write', "", 'if 0 <? b then rd 0 a (upd 0 a (PrimInt63.divs a b) s) else 0',
     '')
addA('s_sint_test', "", 'if 0 <? b then Sint63.div a b else 0',
     '')
addA('s_loop', "", 'lp n a b',
     'Fixpoint lp (k : nat) (i c : int) : int := match k with O => i | S m => if 0 <? c then lp m (PrimInt63.divs i c) c else i end.\n')
addA('s_nontail', "", 'lp n a b',
     'Fixpoint lp (k : nat) (i c : int) : int := match k with O => 0 | S m => if 0 <? c then PrimInt63.divs i c + lp m (i + 1) c else 0 end.\n')
addA('s_helper_in', "", 'k a b + k b a',
     'Definition k (x y : int) : int := if 0 <? y then PrimInt63.divs x y else 0.\n')
addA('s_helper_lit', "", 'k a + k b',
     'Definition k (x : int) : int := PrimInt63.divs x 3.\n')
addA('s_helper_out', "", 'if 0 <? b then k a b else 0',
     'Definition k (x y : int) : int := PrimInt63.divs x y.\n')
addA('s_given_lam', "", 'ap (fun x => PrimInt63.divs x 3) n a',
     'Fixpoint ap (f : int -> int) (k : nat) (x : int) : int := match k with O => x | S m => ap f m (f x) end.\n')
addA('s_none', "", 'PrimInt63.divs a b',
     '')
addA('s_sint_none', "", 'Sint63.div a b',
     '')
addA('s_lit_min', "", 'PrimInt63.divs (PrimInt63.lsl 1 62) b',
     '')
addA('s_lit_m1', "", 'PrimInt63.divs a (0 - 1)',
     '')
addA('s_else', "", 'if 0 <? b then 0 else PrimInt63.divs a b',
     '')
addA('s_other', "", 'if 0 <? b then PrimInt63.divs a (b + 1) else 0',
     '')
addA('s_test_unrelated', "", 'if a =? b then 0 else PrimInt63.divs a b',
     '')
# head0, tail0, mulc, diveucl_21: ordinary functions proved equal to the primitive (step 73)
addA('t_h0_let', "", 'let x := PrimInt63.head0 a in x + b',
     '')
addA('t_h0_arg', "", 'PrimInt63.head0 (a + b)',
     '')
addA('t_h0_lit', "", 'PrimInt63.head0 5',
     '')
addA('t_h0_zero', "", 'PrimInt63.head0 0',
     '')
addA('t_h0_test', "", 'if PrimInt63.head0 a <? b then a else b',
     '')
addA('t_h0_read', "", 'PrimInt63.head0 (rd 0 a s)',
     '')
addA('t_h0_write', "", 'rd 0 a (upd 0 a (PrimInt63.head0 b) s)',
     '')
addA('t_h0_match', "", 'match n with O => PrimInt63.head0 a | S _ => b end',
     '')
addA('t_h0_pair', "", 'fst (PrimInt63.head0 a, b)',
     '')
addA('t_h0_helper', "", 'k a + k b',
     'Definition k (x : int) : int := PrimInt63.head0 x + 1.\n')
addA('t_h0_helper_mem', "", 'rd 0 a (wr a s)',
     'Definition wr (x : int) (t : mem) : mem := upd 0 x (PrimInt63.head0 x) t.\n')
addA('t_h0_loop', "", 'lp n a 0',
     'Fixpoint lp (k : nat) (i acc : int) : int := match k with O => acc | S m => lp m (i + 1) (acc + PrimInt63.head0 i) end.\n')
addA('t_h0_nontail', "", 'lp n a',
     'Fixpoint lp (k : nat) (i : int) : int := match k with O => 0 | S m => PrimInt63.head0 i + lp m (i + 1) end.\n')
addA('t_h0_given_lam', "", 'ap (fun x => PrimInt63.head0 x) n a',
     'Fixpoint ap (f : int -> int) (k : nat) (x : int) : int := match k with O => x | S m => ap f m (f x) end.\n')
addA('t_h0_given_bare', "", 'ap PrimInt63.head0 n a',
     'Fixpoint ap (f : int -> int) (k : nat) (x : int) : int := match k with O => x | S m => ap f m (f x) end.\n')
addA('t_t0_let', "", 'let x := PrimInt63.tail0 a in x + b',
     '')
addA('t_t0_arg', "", 'PrimInt63.tail0 (a + b)',
     '')
addA('t_t0_lit', "", 'PrimInt63.tail0 5',
     '')
addA('t_t0_zero', "", 'PrimInt63.tail0 0',
     '')
addA('t_t0_test', "", 'if PrimInt63.tail0 a <? b then a else b',
     '')
addA('t_t0_read', "", 'PrimInt63.tail0 (rd 0 a s)',
     '')
addA('t_t0_write', "", 'rd 0 a (upd 0 a (PrimInt63.tail0 b) s)',
     '')
addA('t_t0_match', "", 'match n with O => PrimInt63.tail0 a | S _ => b end',
     '')
addA('t_t0_pair', "", 'fst (PrimInt63.tail0 a, b)',
     '')
addA('t_t0_helper', "", 'k a + k b',
     'Definition k (x : int) : int := PrimInt63.tail0 x + 1.\n')
addA('t_t0_helper_mem', "", 'rd 0 a (wr a s)',
     'Definition wr (x : int) (t : mem) : mem := upd 0 x (PrimInt63.tail0 x) t.\n')
addA('t_t0_loop', "", 'lp n a 0',
     'Fixpoint lp (k : nat) (i acc : int) : int := match k with O => acc | S m => lp m (i + 1) (acc + PrimInt63.tail0 i) end.\n')
addA('t_t0_nontail', "", 'lp n a',
     'Fixpoint lp (k : nat) (i : int) : int := match k with O => 0 | S m => PrimInt63.tail0 i + lp m (i + 1) end.\n')
addA('t_t0_given_lam', "", 'ap (fun x => PrimInt63.tail0 x) n a',
     'Fixpoint ap (f : int -> int) (k : nat) (x : int) : int := match k with O => x | S m => ap f m (f x) end.\n')
addA('t_t0_given_bare', "", 'ap PrimInt63.tail0 n a',
     'Fixpoint ap (f : int -> int) (k : nat) (x : int) : int := match k with O => x | S m => ap f m (f x) end.\n')
addA('t_h0_nest', "", 'PrimInt63.head0 (PrimInt63.tail0 a)',
     '')
addA('t_mc_fst', "", 'fst (PrimInt63.mulc a b)',
     '')
addA('t_mc_snd', "", 'snd (PrimInt63.mulc a b)',
     '')
addA('t_mc_let', "", 'let (h, l) := PrimInt63.mulc a b in h * l',
     '')
addA('t_mc_lit', "", 'fst (PrimInt63.mulc 3 b)',
     '')
addA('t_mc_big', "", 'fst (PrimInt63.mulc 4611686018427387903 b)',
     '')
addA('t_mc_arg', "", 'fst (PrimInt63.mulc (a + 1) (b * 2))',
     '')
addA('t_mc_test', "", 'if fst (PrimInt63.mulc a b) =? 0 then a else b',
     '')
addA('t_mc_read', "", 'fst (PrimInt63.mulc (rd 0 a s) b)',
     '')
addA('t_mc_let_pair', "", 'let p := PrimInt63.mulc a b in fst p + snd p',
     '')
addA('t_mc_helper', "", 'hi a b + hi b a',
     'Definition hi (x y : int) : int := fst (PrimInt63.mulc x y).\n')
addA('t_mc_helper_pair', "", 'let (h, l) := m a b in h + l',
     'Definition m (x y : int) : int * int := PrimInt63.mulc x y.\n')
addA('t_mc_loop', "", 'lp n a 0',
     'Fixpoint lp (k : nat) (i acc : int) : int := match k with O => acc | S m => lp m (i + 1) (acc + fst (PrimInt63.mulc i i)) end.\n')
addA('t_mc_nontail', "", 'lp n a',
     'Fixpoint lp (k : nat) (i : int) : int := match k with O => 0 | S m => fst (PrimInt63.mulc i i) + lp m (i + 1) end.\n')
addA('t_mc_write', "", 'rd 0 a (upd 0 a (fst (PrimInt63.mulc a b)) s)',
     '')
addA('t_d_ltb', "", 'if PrimInt63.ltb a b then fst (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_leb', "", 'if PrimInt63.leb b a then 0 else fst (PrimInt63.diveucl_21 a 7 b)',
     '')
addA('t_d_negb', "", 'if negb (PrimInt63.ltb a b) then 0 else fst (PrimInt63.diveucl_21 a 7 b)',
     '')
addA('t_d_negb_leb', "", 'if negb (PrimInt63.leb b a) then fst (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_andb', "", 'if PrimInt63.ltb a b && (a <? 3) then fst (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_andb2', "", 'if (a <? 3) && PrimInt63.ltb a b then fst (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_orb', "", 'if PrimInt63.leb b a || (a =? 3) then 0 else fst (PrimInt63.diveucl_21 a 7 b)',
     '')
addA('t_d_match', "", 'match PrimInt63.ltb a b with true => fst (PrimInt63.diveucl_21 a 7 b) | false => 0 end',
     '')
addA('t_d_pair', "", 'if PrimInt63.ltb a b then let (q, r) := PrimInt63.diveucl_21 a 7 b in q + r else 0',
     '')
addA('t_d_pair_match', "", 'if PrimInt63.ltb a b then match PrimInt63.diveucl_21 a 7 b with pair q r => q * r end else 0',
     '')
addA('t_d_snd', "", 'if PrimInt63.ltb a b then snd (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_var', "", 'if PrimInt63.ltb a b then fst (PrimInt63.diveucl_21 a a b) else 0',
     '')
addA('t_d_under_let', "", 'if PrimInt63.ltb a b then let z := a + 1 in fst (PrimInt63.diveucl_21 a z b) else 0',
     '')
addA('t_d_let_arg', "", 'let x := a + 1 in if PrimInt63.ltb x b then fst (PrimInt63.diveucl_21 x 7 b) else 0',
     '')
addA('t_d_expr_arg', "", 'if PrimInt63.ltb (a + 1) b then fst (PrimInt63.diveucl_21 (a + 1) 7 b) else 0',
     '')
addA('t_d_nested', "", 'if PrimInt63.ltb a b then (if a <? 3 then fst (PrimInt63.diveucl_21 a 7 b) else 1) else 0',
     '')
addA('t_d_twice', "", 'if PrimInt63.ltb a b then fst (PrimInt63.diveucl_21 a 7 b) + snd (PrimInt63.diveucl_21 a 8 b) else 0',
     '')
addA('t_d_read', "", 'let x := rd 0 a s in if PrimInt63.ltb x b then fst (PrimInt63.diveucl_21 x 7 b) else 0',
     '')
addA('t_d_write', "", 'if PrimInt63.ltb a b then rd 0 a (upd 0 a (fst (PrimInt63.diveucl_21 a 3 b)) s) else 0',
     '')
addA('t_d_loop', "", 'lp n a b 0',
     'Fixpoint lp (k : nat) (i c acc : int) : int := match k with O => acc | S m => if PrimInt63.ltb i c then lp m (i + 1) c (acc + fst (PrimInt63.diveucl_21 i 5 c)) else acc end.\n')
addA('t_d_nontail', "", 'lp n a b',
     'Fixpoint lp (k : nat) (i c : int) : int := match k with O => 0 | S m => if PrimInt63.ltb i c then fst (PrimInt63.diveucl_21 i 5 c) + lp m (i + 1) c else 0 end.\n')
addA('t_d_helper_in', "", 'k a b + k b a',
     'Definition k (x y : int) : int := if PrimInt63.ltb x y then fst (PrimInt63.diveucl_21 x 5 y) else 0.\n')
addA('t_d_lit_lt', "", 'fst (PrimInt63.diveucl_21 1 a 3)',
     '')
addA('t_d_lit_all', "", 'fst (PrimInt63.diveucl_21 1 2 3)',
     '')
addA('t_d_lit_all_ge', "", 'fst (PrimInt63.diveucl_21 5 2 3)',
     '')
addA('t_d_lit_a', "", 'if PrimInt63.ltb 1 b then fst (PrimInt63.diveucl_21 1 a b) else 0',
     '')
addA('t_d_lit_c', "", 'if PrimInt63.ltb a 3 then fst (PrimInt63.diveucl_21 a b 3) else 0',
     '')
addA('t_d_let_test', "", 'let t := PrimInt63.ltb a b in if t then fst (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_helper_out', "", 'if PrimInt63.ltb a b then k a b else 0',
     'Definition k (x y : int) : int := fst (PrimInt63.diveucl_21 x 5 y).\n')
addA('t_d_trans', "", 'if PrimInt63.ltb a 5 then (if PrimInt63.ltb 5 b then fst (PrimInt63.diveucl_21 a 7 b) else 0) else 0',
     '')
addA('t_d_let_alias', "", 'let x := a in if PrimInt63.ltb a b then fst (PrimInt63.diveucl_21 x 7 b) else 0',
     '')
addA('t_d_none', "", 'fst (PrimInt63.diveucl_21 a 7 b)',
     '')
addA('t_d_lit_ge', "", 'fst (PrimInt63.diveucl_21 5 a 3)',
     '')
addA('t_d_other', "", 'if PrimInt63.ltb a b then fst (PrimInt63.diveucl_21 a 7 a) else 0',
     '')
addA('t_d_signed', "", 'if a <? b then fst (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_else', "", 'if PrimInt63.ltb a b then 0 else fst (PrimInt63.diveucl_21 a 7 b)',
     '')
addA('t_d_leb_then', "", 'if PrimInt63.leb b a then fst (PrimInt63.diveucl_21 a 7 b) else 0',
     '')
addA('t_d_outside', "", 'fst (PrimInt63.diveucl_21 a 7 b) + (if PrimInt63.ltb a b then 1 else 0)',
     '')
# a function giving back unit or a boolean and a memory, read in another form (step 72)
addA('m_u_loop', "", 'rd 0 a (snd (loop n a s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint loop (k : nat) (i : int) : M unit := match k with O => ret tt | S m => _ <- wrm 0 i i ;; loop m (i + 1) end.\n')
addA('m_u_loop_bind', "", 'fst ((_ <- loop n a ;; x <- rdm 0 a ;; ret (x + 1)) s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint loop (k : nat) (i : int) : M unit := match k with O => ret tt | S m => _ <- wrm 0 i i ;; loop m (i + 1) end.\n')
addA('m_u_loop_nontail', "", 'rd 0 a (snd (loop n a s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint loop (k : nat) (i : int) : M unit := match k with O => ret tt | S m => _ <- loop m (i + 1) ;; x <- rdm 0 i ;; wrm 0 (i + 1) x end.\n')
addA('m_u_def', "", 'rd 0 a (snd (pr a b s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition pr (i j : int) : M unit := x <- rdm 0 i ;; wrm 0 j (x + 1).\n')
addA('m_u_def_if', "", 'rd 0 a (snd (pr a b s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition pr (i j : int) : M unit := x <- rdm 0 i ;; if x <? j then wrm 0 j x else ret tt.\n')
addA('m_u_two', "", 'rd 0 a (snd (q2 n a s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint q1 (k : nat) (i : int) : M unit := match k with O => ret tt | S m => _ <- wrm 0 i i ;; q1 m (i + 1) end.\nFixpoint q2 (k : nat) (i : int) : M unit := match k with O => ret tt | S m => _ <- q1 k i ;; q2 m (i + 2) end.\n')
addA('m_u_plain', "", 'rd 0 a (snd (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : unit * mem := match k with O => (tt, t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('m_u_plain_let', "", 'let (_, t2) := lp n a s in rd 0 a t2',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : unit * mem := match k with O => (tt, t) | S m => let (u, t1) := lp m (i + 1) t in (u, upd 0 i i t1) end.\n')
addA('m_u_snd_rec', "", 'rd 0 a (snd (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : unit * mem := match k with O => (tt, t) | S m => (tt, snd (lp m (i + 1) t)) end.\n')
addA('m_u_test_rec', "", 'rd 0 a (snd (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : unit * mem := match k with O => (tt, t) | S m => if rd 0 i t <? 3 then lp m (i + 1) t else (tt, upd 0 i 0 t) end.\n')
addA('m_u_a6', "", 'rd 0 a (snd (prog a b s))',
     'Definition prog (i j : int) (t : mem) : unit * mem := (tt, upd 0 i j t).\n')
addA('m_b_find', "", 'if fst (find n a s) then a else b',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint find (k : nat) (i : int) : M bool := match k with O => ret false | S m => x <- rdm 0 i ;; if x =? 7 then ret true else find m (i + 1) end.\n')
addA('m_b_find_bind', "", 'fst ((c <- find n a ;; if c then rdm 0 a else ret b) s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint find (k : nat) (i : int) : M bool := match k with O => ret false | S m => x <- rdm 0 i ;; if x =? 7 then ret true else find m (i + 1) end.\n')
addA('m_b_nontail', "", 'if fst (all n a s) then a else b',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint all (k : nat) (i : int) : M bool := match k with O => ret true | S m => r <- all m (i + 1) ;; x <- rdm 0 i ;; ret (r && (x =? 7)) end.\n')
addA('m_b_write', "", 'rd 0 a (snd (tas n a s))',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint tas (k : nat) (i : int) : M bool := match k with O => ret false | S m => x <- rdm 0 i ;; if x =? 0 then (_ <- wrm 0 i 1 ;; ret true) else tas m (i + 1) end.\n')
addA('m_b_def', "", 'if fst (isz a s) then a else b',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition isz (i : int) : M bool := x <- rdm 0 i ;; ret (x =? 0).\n')
addA('m_b_def_if', "", 'let (c, t) := isz a s in if c then rd 0 a t else b',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nDefinition isz (i : int) : M bool := x <- rdm 0 i ;; if x =? 0 then (_ <- wrm 0 i 1 ;; ret true) else ret false.\n')
addA('m_b_plain', "", 'let (c, t2) := f n a s in if c then rd 0 a t2 else b',
     'Fixpoint f (k : nat) (i : int) (t : mem) : bool * mem := match k with O => (true, t) | S m => if rd 0 i t =? 0 then (false, upd 0 i 1 t) else f m (i + 1) t end.\n')
addA('m_b_two_calls', "", 'if fst (f n a s) then a else rd 0 a (snd (f n a s))',
     'Fixpoint f (k : nat) (i : int) (t : mem) : bool * mem := match k with O => (true, t) | S m => if rd 0 i t =? 0 then (false, upd 0 i 1 t) else f m (i + 1) t end.\n')
addA('m_e_enum', "", 'fst (lp n a s)',
     'Inductive col := Red | Green.\nFixpoint lp (k : nat) (i : int) (t : mem) : int * mem := match k with O => (i, t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('m_e_enum_ret', "", 'match fst (lp n a s) with Red => a | Green => b end',
     'Inductive col := Red | Green.\nFixpoint lp (k : nat) (i : int) (t : mem) : col * mem := match k with O => (Red, t) | S m => if rd 0 i t =? 0 then (Green, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('m_e_opt_ret', "", 'match fst (lp n a s) with Some v => v | None => b end',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : option int * mem := match k with O => (None, t) | S m => if rd 0 i t =? 0 then (Some i, t) else lp m (i + 1) (upd 0 i i t) end.\n')
addA('m_e_pair_ret', "", 'fst (fst (lp n a s))',
     'Fixpoint lp (k : nat) (i : int) (t : mem) : (int * int) * mem := match k with O => ((i, i), t) | S m => lp m (i + 1) (upd 0 i i t) end.\n')
addA('m_e_name_p1', "", 'fst (p1 a s)',
     'Definition M (A : Type) : Type := mem -> A * mem.\nDefinition ret {A : Type} (x : A) : M A := fun t => (x, t).\nDefinition bind {A B : Type} (m : M A) (f : A -> M B) : M B := fun t => let (x, t\') := m t in f x t\'.\nDefinition rdm (h i : int) : M int := fun t => (rd h i t, t).\nDefinition wrm (h i v : int) : M unit := fun t => (tt, upd h i v t).\nNotation "x <- m ;; k" := (bind m (fun x => k)) (at level 61, m at next level, right associativity).\nFixpoint p2 (k : nat) (i : int) : M int := match k with O => ret i | S m => p2 m (i + 1) end.\nDefinition p1 (i : int) : M int := x <- p2 3 i ;; ret (x + 1).\n')

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
