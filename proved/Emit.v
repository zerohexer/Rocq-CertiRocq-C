From Stdlib Require Import String List Uint63 ZArith.
From KQC Require Import KQL KQLGen KQLPrint KQLEx KQLSort.
Import ListNotations.
Definition sumsq_c := tr_program P_sumsq m_main f_sumsq [of_Z 100000000%Z; 1%uint63; 0%uint63].
Redirect "lcg_gen" Eval vm_compute in (pstr m_main lcg_c).
Redirect "sumsq_gen" Eval vm_compute in (pstr m_main sumsq_c).
Redirect "sort_gen" Eval vm_compute in (pstr m_main sort_c).
