# The construct table

```
780 cells: 759 translated and proved, 0 refused by design, 20 gaps, 1 not Rocq (no verdict)

gap (6): a proof the tactics do not find (the translation was accepted)
  P_int_match_nat2 P_pair_call_arith P_pair_if P_pair_if_inside P_pair_nontail_if P_pair_proj_pair

gap (5): a recursive function giving back a record of three numbers, or giving back or taking an option
  A_par_option_rec A_par_option_state P_pairp_rec P_rec3_nontail P_rec3_tail_rec

gap (4): arithmetic or a comparison on counters
  A_par_nat_eqb A_par_nat_ltb A_par_nat_mul A_par_nat_pred

gap (4): a local function, a polymorphic or class-based helper, a memory inside a record
  A_par_poly_hof A_par_poly_id A_par_poly_pair A_par_typeclass

gap (1): a function given that names a variable of the caller (a closure)
  P_int_local_fix

not Rocq: A_par_nat_arith
```
