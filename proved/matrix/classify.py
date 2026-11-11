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
  # a counter a function gives back plus a number past a word less one: past a word (Rocq-C-solution.md §0.5, second reason); control:
  # A_zv_add_big, plus 100000 (step 105)
  "A_zv_add_word",
  # a counter a function gives back with no bound (2^n) where its whole value counts: a land of two of them, mod 10, its bit 63: a number past a
  # word (Rocq-C-solution.md §0.5, second reason); controls: A_zu_land, A_zu_mod_pow2, A_zu_testbit, where its value modulo a word is enough (step 104)
  "A_zu_land_two", "A_zu_mod_ten", "A_zu_testbit_63",
  # a counter a function gives back in a sum with a power or a lcm of a counter: a number that may need more than a word (Rocq-C-solution.md §0.5,
  # second reason), as A_c2_nat_square and A_zi_lcm; controls: A_zt_sum_log2, A_zt_sum_gcd, a sum with an operation the check has a bound of (step 103)
  "A_zt_sum_pow", "A_zt_sum_lcm",
  # a counter a function gives back in a sum eight times its counters, or with a doubling: from kq_nat's 2^60, or 2^n, a number past a word
  # (§0.5, second reason), as A_zs_shiftl_three and A_zb_s_power; control: A_zt_sum_helper_two, three times (step 103)
  "A_zt_sum_helper_seven", "A_zt_sum_doubling",
  # a counter a function gives back shifted left by 3 or by a counter: up to 8 times a counter of up to 2^60, or 2^n, a number past a
  # word (Rocq-C-solution.md §0.5, second reason); controls: A_zs_shiftl, A_zs_shiftl_two, the shifts by 1 and 2 (step 102)
  "A_zs_shiftl_three", "A_zs_shiftl_var",
  # two records holding a memory, read from one and written in the other, given the same one by the call: two versions (Rocq-C-solution.md §0.5, third reason); control: A_x_p_other_param
  "A_x_p_two_states",
  # read from a memory and written in another, given the same one: two versions differing in cells whose number comes from the data (Rocq-C-solution.md §0.5, third reason); controls: A_w_s_three_value, A_w_l_cap_lit
  "A_w_s_mem", "A_w_l_cap_mem",
  # the same function from the same memory on other arguments, its value from one and its memory from the other: two versions; control: A_v_call_both
  "A_w_t_other_args",
  # two calls of a function that writes at each round, each from the same memory, the writes kept in place by what it gives back: two versions differing in cells whose number comes from the data (Rocq-C-solution.md §0.5, third reason); control: A_v_call_in_helper
  "A_v_call_in_helper_two",
  # the same, two memory parameters: read from one, written in the other, given the same one by the call: two versions; control: A_v_mem_first
  "A_v_o_two_mems",
  # a function built anew at each round of a recursion, a list whose size comes from the data: allocated behind the programmer's back (Rocq-C-solution.md §0.5, first reason); controls: A_p_cps, A_p_list_rec_lit (step 77)
  "A_p_cps_grow", "A_p_list_built",
  # divs with nothing ruling out the smallest number over -1: Rocq's axioms say nothing there, so nothing says what it computes (Rocq-C-solution.md §0.5, fourth reason); controls: A_s_test_pos, A_s_lit_b, and / : A_s_slash_var (step 74)
  "A_s_none", "A_s_sint_none", "A_s_lit_min", "A_s_lit_m1", "A_s_else", "A_s_other", "A_s_test_unrelated",
  # diveucl_21 with nothing showing a < c, or shown the other way: Rocq's axioms say nothing there, so nothing says what it computes (Rocq-C-solution.md §0.5, fourth reason); controls: A_t_d_ltb, A_t_d_leb, A_t_d_lit_lt (step 73)
  "A_n_diveucl_21", "A_t_d_none", "A_t_d_lit_ge", "A_t_d_other", "A_t_d_signed", "A_t_d_else", "A_t_d_leb_then", "A_t_d_outside",
  # two calls that write at a moving index, each from the memory before both (Rocq-C-solution.md §0.5, third reason); control: A_m_b_plain, one call (step 72)
  "A_m_b_two_calls",
  # Rocq's primitive arrays are persistent: every version kept, a runtime behind the programmer's back (Rocq-C-solution.md §0.5, first reason); control: a memory, A_q_mem_helper_chain (step 71)
  "A_q_parray_get",
  # a number that may need more than a word: a product of two counters, a power, a counter times a number or a sum past 2^63 (Rocq-C-solution.md §0.5, second reason); controls: A_c2_mul_r, A_c2_nat_pow_lit, A_c2_to_add (step 70)
  "A_c2_mul_vars", "A_c2_nat_square", "A_c2_nat_pow", "A_c2_mul_big", "A_c2_to_add_u",
  # two memory parameters both live: read from one, written in the other (Rocq-C-solution.md §0.5, third reason); control: A_rp_dead_first, one of them never read (step 69)
  "A_rp_dead_live_control",
  # arithmetic on Z: an unbounded number as a value (Rocq-C-solution.md §0.5, second reason); control: A_l_z_arith_ctrl, the same on int (step 68)
  "A_l_z_arith",
  # a record of functions built anew at each round of a recursion, from the data: allocated behind the programmer's back (Rocq-C-solution.md §0.5, first reason); control: A_zc_r_capture, the same record the same throughout (step 84)
  "A_zc_r_gives_record",
  # a counter that doubles at each round: 2^n from a written budget, a number past a word (§0.5, second reason); controls: A_zb_s_two, A_zb_a_acc, a bound linear in its counters (step 83)
  "A_zb_s_power", "A_zb_s_power_mul", "A_zb_a_acc_doubles",
  # a counter that a round adds a parameter to: n^2 from a written budget, a number past a word (§0.5, second reason); controls: A_zb_s_add, A_zb_s_two_funcs (step 83)
  "A_zb_s_add_var", "A_zb_s_quadratic",
  # a list whose length comes from the data, built by a recursion: its cells would be allocated behind the programmer's back (§0.5, first reason);
  # control: A_l_list_fold_left, A_l_list_param, a list written in the text (step 68)
  "A_l_list_data",
  # a mutual block of a memory and a number: the member giving a memory writes on what the other's call, writing too, was given: two versions
  # differing in cells whose number comes from the data (Rocq-C-solution.md §0.5, third reason); control: A_par_mutual_int_bool_mem, a block of
  # different types that reads (step 62)
  "A_par_mutual_mixed",
  # two calls of a function that writes at each round, each from the same memory, under two choices: two versions differing in cells
  # whose number comes from the data (Rocq-C-solution.md §0.5, third reason); control: A_own_two_choices_read, the same with no write (step 61)
  "A_own_two_choices",
  # a function built anew at each round of a measure recursion: a copy per function given, with no last copy (Rocq-C-solution.md
  # §0.5, the first reason); control: A_fn_fun_param, A_pf_fun_param, the function handed on as it is (step 59)
  "A_fn_f_grows",
  "A_pf_f_grows",
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
  # a power of two of a counter, or a counter shifted past a word: a number that may need more than a word (Rocq-C-solution.md §0.5, second reason);
  # controls: A_zh_shiftl_lit, A_zh_setbit_lit, A_zh_ones_lit, A_zh_lnot_lit, the same at a written number (step 92)
  "A_zh_shiftl_var", "A_zh_shiftl_big", "A_zh_setbit_var", "A_zh_ones_var", "A_zh_lnot_var",
  # Nat.lcm, a product of two counters: a number that may need more than a word, as Nat.mul n n (Rocq-C-solution.md §0.5, second reason);
  # control: A_c2_mul_r, a counter times a written number (step 93)
  "A_zi_lcm",
  # a written number past a word as a counter, a counter times a number past 2^63 (Rocq-C-solution.md §0.5, second reason);
  # controls: A_zj_land_max, A_zj_mul_r, the same below a word (step 94)
  "A_zj_land_past", "A_zj_mul_big",
  # a power of two written numbers past a word (Rocq-C-solution.md §0.5, second reason); controls: A_zk_num_62, A_zk_num_ten18 (step 95)
  "A_zk_past_63", "A_zk_past_ten19",
  # an operand of a min or a subtraction that may need more than a word (Rocq-C-solution.md §0.5, second reason); controls:
  # A_zl_min_past_ctl, A_zl_sub_past_ctl, the operand masked (step 97)
  "A_zl_min_past", "A_zl_sub_past",
}
# gaps whose refusal message is shared with another category: classified by name
BY_NAME = {
  "A_rp_poly_measure": "a measure recursion polymorphic in a type",
  "A_q_st_mem_iter": "a memory as a field of a data type",
  "A_q_mem_rec_triple": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_q_rec_vtable_rec": "a record of functions or a class's instance given to a recursive function",
  "A_q_cl_fold": "a record of functions or a class's instance given to a recursive function",
  "A_q_nat_ret_len": "a function giving back a counter, a counter as a field",
  "A_q_nat_ret_acc": "a function giving back a counter, a counter as a field",
  "A_q_divmod": "a function giving back a counter, a counter as a field",
  "A_q_ascii_code": "a function giving back a counter, a counter as a field",
  "A_q_float_lit": "floating point (§12.I)",
  "A_m_e_enum_ret": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_m_e_opt_ret": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_m_e_pair_ret": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_m_e_name_p1": "a function named p1 or p2: a token of MetaRocq's notations, in the proof file",
  "A_t_h0_given_lam": "a primitive Rocq's axioms only relate, given as a function to a recursive function: under the binder no equation reaches",
  "A_t_h0_given_bare": "a primitive Rocq's axioms only relate, given as a function to a recursive function: under the binder no equation reaches",
  "A_t_t0_given_lam": "a primitive Rocq's axioms only relate, given as a function to a recursive function: under the binder no equation reaches",
  "A_t_t0_given_bare": "a primitive Rocq's axioms only relate, given as a function to a recursive function: under the binder no equation reaches",
  "A_t_d_helper_out": "a diveucl_21 in a helper, the test that shows a < c in its caller",
  "A_t_d_trans": "a test that shows a < c only together with another",
  "A_s_helper_out": "a divs in a helper, the test that rules the case out in its caller",
  "A_s_given_lam": "a primitive Rocq's axioms only relate, given as a function to a recursive function: under the binder no equation reaches",
  "A_e_sig_field": "a value and a proof as a field of what a function gives back",
  "A_e_sig_nat": "a counter given back with a proof",
  "A_e_sig_param": "a value and a proof as a parameter",
  "A_p_err_rec": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_p_err_rec_mem": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_p_res_mem_rec": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_p_rec_mem_loop": "a value and a memory given back together by a recursion or a loop, the value not one number",
  "A_p_class_rec": "a record of functions or a class's instance given to a recursive function",
  "A_p_class_two": "a class's instance built from others, its fields read at once",
  "A_p_proof_arg": "a proof as a parameter",
  "A_p_proof_arg_rec": "a proof as a parameter",
  "A_p_sig_arg": "a proof as a parameter",
  "A_p_dep_pair": "a dependent pair, a vector: values whose type holds a value",
  "A_p_vector": "a dependent pair, a vector: values whose type holds a value",
  "A_p_string_len": "a test on strings: a library's fixpoint on a written string, whose constructors the test sees through",
  "A_p_ascii": "a closed term of a library computed by what the reader does not know: a number written through a definition, a character",
  "A_p_z_to_int": "a closed term of a library computed by what the reader does not know: a number written through a definition, a character",
  "A_p_io": "the kit's input and output: hosted (§12.I)",
  "A_p_nat_len": "a function giving back a counter, a counter as a field",
  "A_p_nat_add": "a function giving back a counter, a counter as a field",
  "A_v_w_block_63": "a recursion giving back a value and a memory that writes the slot block, or a block whose number is not written: nothing shows it leaves the value's cells alone",
  "A_v_w_out": "the kit's input and output: hosted (§12.I)",
  "A_v_o_mutual": "a value and a memory given back by a mutual block",
  "A_v_o_poly": "a value and a memory given back by a polymorphic recursion",
  "A_v_o_program": "a value and a memory given back by a Program Fixpoint",
  "A_w_b_call_63": "a recursion giving back a value and a memory that writes the slot block, or a block whose number is not written: nothing shows it leaves the value's cells alone",
  "A_w_b_call_tested": "a recursion giving back a value and a memory that writes the slot block, or a block whose number is not written: nothing shows it leaves the value's cells alone",
  "A_w_b_call_var": "a recursion giving back a value and a memory that writes the slot block, or a block whose number is not written: nothing shows it leaves the value's cells alone",
  "A_w_b_moved": "a recursion giving back a value and a memory that writes the slot block, or a block whose number is not written: nothing shows it leaves the value's cells alone",
  "A_w_l_writes_mem": "a local fix of a memory in what gives back a value and a memory",
  "A_x_f_three": "a memory deeper in a value given back: a pair in a pair",
  "A_x_p_var_rec": "a value holding a memory given as a parameter by a call of a recursion",
  "A_x_r_local": "a value and a memory given back by a local fix, a Section's fixpoint",
  "A_y_p_section_unused": "a proof a test gives, named by what follows",
  "A_z_o_local": "a function giving back a counter, a counter as a field",
  "A_z_o_mem_counter": "a function giving back a counter, a counter as a field",
  "A_z_o_opt_counter": "a function giving back a counter, a counter as a field",
  "A_z_o_pair_counter": "a function giving back a counter, a counter as a field",
  "A_p_nat_len_cmp": "a counter a function gives back used as a counter: its bound",
  "A_z_u_counter_use": "a counter a function gives back used as a counter: its bound",
  "A_z_u_eqb": "a counter a function gives back used as a counter: its bound",
  "A_z_u_leb": "a counter a function gives back used as a counter: its bound",
  "A_z_u_match": "a counter a function gives back used as a counter: its bound",
  "A_z_u_zofnat": "a test in Z on a counter",
  "A_zb_o_local": "a function giving back a counter, a counter as a field",
  "A_zb_o_callee_grows": "a counter a function gives back, given to a function that makes its counter larger: to the check it is any machine number",
  "A_zb_o_counter_row_uses": "a function giving back a counter that uses another's as a counter",
  "A_zb_o_weights": "a counter a function gives back, used where the counters are held by weights",
  "A_zc_c_mutual": "a class or a record of functions given to a mutual block",
  "A_zc_r_mutual": "a class or a record of functions given to a mutual block",
  "A_zc_c_counter_late": "a class given to a recursion, its type after the counter",
  "A_zc_r_nested": "a record of functions inside a record, given to a recursion",
  "A_zd_r_default": "the memory before a call that gave nothing, used after it",
  "A_ze_own_call_12": "tests that cannot be moves in one expression, an own call in each: what follows written in each arm",
  "A_zy_capture": "a local mutual fixpoint naming a variable of the function: its members want it as a parameter, given in each call (12.A)",
  "A_zy_capture_let": "a local mutual fixpoint naming a variable of the function: its members want it as a parameter, given in each call (12.A)",
  "A_zy_counter": "a mutual block giving back a counter: step 82's rows are of single functions (12.A)",
  "A_zy_top_counter": "a mutual block giving back a counter: step 82's rows are of single functions (12.A)",
  "A_zh_row_shiftr": "a function giving back a counter built by shiftr: not the same modulo a word, it wants the row's bound (step 83)",
  "A_zh_row_testbit_own": "a test on what a function giving back a counter gives back, in its own recursion: it wants the row's bound or the test on the machine's number",
  "A_zf_r_three": "three constructors or more holding a memory, through a recursion: a sum in a sum",
  "A_l_ack": "a fixpoint inside a fixpoint that gives back a function",
  "A_l_dec_proof_used": "a proof a test gives, named by what follows",
  "A_l_nat_ret_same": "a counter given back by a recursive function",
  "A_fx_nat_pair": "a counter as a field of a value given back by a recursive function",
  "A_fx_nat_opt": "a counter as a field of a record or a data type",
  "A_fx_opt_mem": "a memory as a field of a data type",
  "A_fx_opt_mem_rec": "a memory as a field of a data type",
  "A_pf_wf_rel": "a Program Fixpoint, a Function or Equations on a relation of the user's, {wf R x}: no measure to put a budget above",
  "A_fn_wf_rel": "a Program Fixpoint, a Function or Equations on a relation of the user's, {wf R x}: no measure to put a budget above",
  "A_eq_wf_rel": "a Program Fixpoint, a Function or Equations on a relation of the user's, {wf R x}: no measure to put a budget above",
  **{c: "the function's own call under a choice in an operand, in a body that writes or a boolean's or a record's: its value joined after the choice" for c in (
     "Y_fill_branch2_bool",
     "Y_fill_branch2_record",
     "Y_fill_branch_bool",
     "Y_fill_branch_record",
     "Y_fill_ifop_bool",
     "Y_fill_ifop_int",
     "Y_fill_ifop_record",
     "Y_letfill_branch2_bool",
     "Y_letfill_branch2_record",
     "Y_letfill_branch_bool",
     "Y_letfill_branch_record",
     "Y_letfill_ifop_bool",
     "Y_letfill_ifop_int",
     "Y_letfill_ifop_record",
     "Y_letupd_branch2_bool",
     "Y_letupd_branch2_record",
     "Y_letupd_branch_bool",
     "Y_letupd_branch_record",
     "Y_letupd_ifop_bool",
     "Y_letupd_ifop_int",
     "Y_letupd_ifop_record",
     "Y_none_ifop_bool",
     "Y_none_ifop_record",
     "Y_same_branch2_bool",
     "Y_same_branch2_record",
     "Y_same_branch_bool",
     "Y_same_branch_record",
     "Y_same_ifop_bool",
     "Y_same_ifop_record",
     "Y_upd_branch2_bool",
     "Y_upd_branch2_record",
     "Y_upd_branch_bool",
     "Y_upd_branch_record",
     "Y_upd_ifop_bool",
     "Y_upd_ifop_int",
     "Y_upd_ifop_record",
  )},
  "A_par_pm_let_own": "the function's own call beside a call given a number and a memory, in a let of the pair",
  "A_par_mutual_both_self": "a mutual block of different result types whose members call each other and themselves: no member the only one called",
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
