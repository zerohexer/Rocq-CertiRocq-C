# The construct table

```
775 cells: 733 translated and proved, 5 refused by design, 36 gaps, 1 not Rocq (no verdict)

gap (9): a function giving back a boolean, a record of three, or a number with a memory, by recursion
  P_bool_nontail_and P_bool_nontail_or P_bool_rec_search P_bool_tail_rec P_intmem_nontail P_intmem_tail_rec P_pairp_rec P_rec3_nontail P_rec3_tail_rec

gap (7): a pair of a number and a memory
  A_par_mem_pair P_intmem_alloc_like P_intmem_call P_intmem_if P_intmem_let P_intmem_lit P_intmem_wr

gap (6): a proof the tactics do not find (the translation was accepted)
  P_int_match_nat2 P_pair_call_arith P_pair_if P_pair_if_inside P_pair_nontail_if P_pair_proj_pair

gap (5): a local function, a polymorphic or class-based helper, a memory inside a record
  A_par_mem_record A_par_poly_hof A_par_poly_id A_par_poly_pair A_par_typeclass

gap (4): arithmetic or a comparison on counters
  A_par_nat_eqb A_par_nat_ltb A_par_nat_mul A_par_nat_pred

gap (3): a boolean made by an if or a match
  P_bool_if P_bool_if_call P_bool_match_nat

gap (1): a function given that names a variable of the caller (a closure)
  P_int_local_fix

gap (1): a choice between records
  P_rec3_if

by design: A_par_fun_in_pair A_par_list A_par_option A_par_sum P_mem_dup

not Rocq: A_par_nat_arith
```
