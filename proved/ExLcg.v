From Stdlib Require Import ZArith List Uint63 Lia.
From compcert Require Import Coqlib Maps.
From MetaRocq.Template Require Import All.
From KQC Require Import KQL KQLAuto KQLTrans.
Import ListNotations.

Open Scope uint63_scope.
Definition step (s : i63) : i63 := (s * 1103515245 + 12345) land 2147483647.
Fixpoint rep (d : nat) (s : i63) : i63 := match d with O => step s | S d => rep d (rep d s) end.
Definition lcg : i63 := rep 24 1.

Fixpoint sumsq (k : nat) (i acc : i63) : i63 :=
  match k with O => acc | S k => sumsq k (i + 1) (acc + i * i) end.
Definition sq : i63 := sumsq 1000 1 0.
Close Scope uint63_scope.

MetaRocq Run (kql_translate lcg "lcg_prog").
Lemma rep_ok : rep_stmt. Proof. kql_auto. Qed.
Lemma lcg_ok : lcg_stmt. Proof. pose proof rep_ok as H; hnf in H. kql_auto. Qed.

MetaRocq Run (kql_translate sq "sq_prog").
Lemma sumsq_ok : sumsq_stmt. Proof. kql_auto. Qed.
Lemma sq_ok : sq_stmt. Proof. pose proof sumsq_ok as H; hnf in H. kql_auto. Qed.
Print rep_kql.
