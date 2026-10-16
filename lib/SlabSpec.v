(* lib/SlabSpec.v -- WHAT A SLAB GUARANTEES, proved against the memory's laws (KQSpec.v): a handle is live once its slot
   is taken, dead once its object is freed, and stays dead when the slot is taken again; a field reads what was last
   written to it.  Every number below is a 63-bit machine number; `Z_` reads it as an integer. *)
From Stdlib Require Import ZArith Lia Sint63 Bool.
Require Import KQ.KQRun KQ.KQBound KQ.KQSpec KQ.lib.Slab.
Open Scope sint63_scope.
Open Scope bool_scope.
Notation Z_ := Sint63.to_Z.

(* ---- machine numbers as integers: masks and shifts on numbers that are not negative *)
Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma phi_nonneg (x : int) : (0 <= Z_ x)%Z -> φ (x)%uint63 = Z_ x.
Proof.
  intro P. rewrite <- (Sint63.to_Z_mod_Uint63to_Z x). apply Z.mod_small.
  pose proof (to_Z_bounds x). rewrite wB_val. lia.
Qed.

Lemma to_Z_small (x : int) : (φ (x)%uint63 < 4611686018427387904)%Z -> Z_ x = φ (x)%uint63.
Proof.
  intro L. pose proof (Sint63.to_Z_mod_Uint63to_Z x) as M. pose proof (to_Z_bounds x) as B. rewrite wB_val in M.
  destruct (Z_le_gt_dec 0 (Z_ x)) as [P | P].
  - rewrite Z.mod_small in M; lia.
  - assert (E : (Z_ x + 9223372036854775808 = Z_ x mod 9223372036854775808)%Z)
      by (apply Z.mod_unique_pos with (q := (-1)%Z); lia).
    lia.
Qed.

(* x land (2^k - 1) is x's remainder modulo 2^k *)
Lemma land_ones (x : int) (k : Z) (m : int) : (0 <= Z_ x)%Z -> (0 <= k <= 61)%Z -> φ (m)%uint63 = Z.ones k ->
  Z_ (x land m) = (Z_ x mod 2 ^ k)%Z.
Proof.
  intros P K Mm. assert (U : φ (x land m)%uint63 = (Z_ x mod 2 ^ k)%Z).
  { rewrite Uint63.land_spec', Mm, (phi_nonneg x P). apply Z.land_ones. lia. }
  rewrite to_Z_small; [exact U | ]. rewrite U.
  assert (Q : (2 ^ k <= 2 ^ 61)%Z) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z.mod_pos_bound (Z_ x) (2 ^ k) ltac:(lia)). change (2 ^ 61)%Z with 2305843009213693952%Z in Q. lia.
Qed.

Lemma mask28 (x : int) : (0 <= Z_ x)%Z -> Z_ (x land 268435455) = (Z_ x mod 268435456)%Z.
Proof. intro P. rewrite (land_ones x 28); [reflexivity | exact P | lia | reflexivity]. Qed.

Lemma mask1 (x : int) : (0 <= Z_ x)%Z -> Z_ (x land 1) = (Z_ x mod 2)%Z.
Proof. intro P. rewrite (land_ones x 1); [reflexivity | exact P | lia | reflexivity]. Qed.

(* ---- a handle: b * 2^56 + slot * 2^28 + generation *)
Definition parts_ok (b i g : int) : Prop :=
  (0 <= Z_ b < 64)%Z /\ (0 <= Z_ i < 268435456)%Z /\ (0 <= Z_ g < 268435456)%Z.

Lemma handle_Z (b i g : int) : parts_ok b i g ->
  Z_ (slab_handle b i g) = (Z_ b * 72057594037927936 + Z_ i * 268435456 + Z_ g)%Z.
Proof.
  intros (Hb & Hi & Hg). unfold slab_handle.
  assert (E1 : Z_ (b * 72057594037927936) = (Z_ b * 72057594037927936)%Z)
    by (rewrite mul_Z; change (Z_ 72057594037927936) with 72057594037927936%Z; lia).
  assert (E2 : Z_ (i * 268435456) = (Z_ i * 268435456)%Z)
    by (rewrite mul_Z; change (Z_ 268435456) with 268435456%Z; lia).
  assert (E3 : Z_ (b * 72057594037927936 + i * 268435456) = (Z_ b * 72057594037927936 + Z_ i * 268435456)%Z)
    by (rewrite add_Z; rewrite E1, E2; lia).
  rewrite add_Z; rewrite E3; lia.
Qed.

Lemma handle_nonneg (b i g : int) : parts_ok b i g -> (0 <= Z_ (slab_handle b i g))%Z.
Proof. intro H. rewrite (handle_Z b i g H). destruct H as (Hb & Hi & Hg). lia. Qed.

Lemma handle_slot (b i g : int) : parts_ok b i g -> slab_slot (slab_handle b i g) = i.
Proof.
  intro H. pose proof (handle_Z b i g H) as E. pose proof (handle_nonneg b i g H) as P. destruct H as (Hb & Hi & Hg).
  apply Sint63.to_Z_inj. unfold slab_slot.
  assert (D : Z_ (slab_handle b i g >> 28) = (Z_ b * 268435456 + Z_ i)%Z).
  { rewrite Sint63.asr_spec, E. change (Z_ 28) with 28%Z. change (2 ^ 28)%Z with 268435456%Z.
    symmetry. apply Z.div_unique_pos with (r := Z_ g); lia. }
  rewrite mask28 by lia. rewrite D. symmetry. apply Z.mod_unique_pos with (q := Z_ b); lia.
Qed.

Lemma handle_gen (b i g : int) : parts_ok b i g -> slab_gen (slab_handle b i g) = g.
Proof.
  intro H. pose proof (handle_Z b i g H) as E. pose proof (handle_nonneg b i g H) as P. destruct H as (Hb & Hi & Hg).
  apply Sint63.to_Z_inj. unfold slab_gen. rewrite mask28 by exact P. rewrite E.
  symmetry. apply Z.mod_unique_pos with (q := (Z_ b * 268435456 + Z_ i)%Z); lia.
Qed.

Lemma handle_block (b i g : int) : parts_ok b i g -> (slab_handle b i g >> 56) = b.
Proof.
  intro H. pose proof (handle_Z b i g H) as E. destruct H as (Hb & Hi & Hg).
  apply Sint63.to_Z_inj. rewrite Sint63.asr_spec, E. change (Z_ 56) with 56%Z.
  change (2 ^ 56)%Z with 72057594037927936%Z. symmetry.
  apply Z.div_unique_pos with (r := (Z_ i * 268435456 + Z_ g)%Z); lia.
Qed.

(* ---- generations: 0 unused, odd live, even free; slab_next_gen moves one on, from 2^28 - 1 back to 2 *)
Definition gen_ok (g : int) : Prop := (0 <= Z_ g < 268435456)%Z.

Lemma next_gen_Z (g : int) : gen_ok g ->
  Z_ (slab_next_gen g) = (if (Z_ g + 1 =? 268435456)%Z then 2 else Z_ g + 1)%Z.
Proof.
  intro G. unfold gen_ok in G. unfold slab_next_gen.
  assert (A : Z_ (g + 1) = (Z_ g + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
  destruct (g + 1 =? 268435456) eqn:E.
  - apply eq_Z in E. rewrite A in E. change (Z_ 268435456) with 268435456%Z in E. rewrite E, Z.eqb_refl. reflexivity.
  - apply eq_Z_false in E. rewrite A in E. change (Z_ 268435456) with 268435456%Z in E.
    destruct (Z_ g + 1 =? 268435456)%Z eqn:E2; [apply Z.eqb_eq in E2; contradiction | exact A].
Qed.

Lemma next_gen_ok (g : int) : gen_ok g -> gen_ok (slab_next_gen g).
Proof.
  intro G. unfold gen_ok. rewrite (next_gen_Z g G). unfold gen_ok in G.
  destruct (Z_ g + 1 =? 268435456)%Z eqn:E; [lia | apply Z.eqb_neq in E; lia].
Qed.

Lemma next_gen_ne (g : int) : gen_ok g -> slab_next_gen g <> g.
Proof.
  intros G Eq. pose proof (next_gen_Z g G) as Z1. rewrite Eq in Z1. unfold gen_ok in G.
  destruct (Z_ g + 1 =? 268435456)%Z eqn:E; [apply Z.eqb_eq in E; lia | lia].
Qed.

(* two steps never come back: a handle freed and its slot taken again is still dead *)
Lemma next_next_ne (g : int) : gen_ok g -> slab_next_gen (slab_next_gen g) <> g.
Proof.
  intros G Eq. pose proof (next_gen_ok g G) as G1.
  pose proof (next_gen_Z (slab_next_gen g) G1) as Z2. pose proof (next_gen_Z g G) as Z1.
  rewrite Eq in Z2. unfold gen_ok in G.
  destruct (Z_ g + 1 =? 268435456)%Z eqn:E1; rewrite Z1 in Z2;
  [apply Z.eqb_eq in E1 | apply Z.eqb_neq in E1].
  - destruct (2 + 1 =? 268435456)%Z eqn:E2; lia.
  - destruct (Z_ g + 1 + 1 =? 268435456)%Z eqn:E2; [apply Z.eqb_eq in E2 | ]; lia.
Qed.

(* an even generation moved on is odd *)
Lemma next_gen_odd (g : int) : gen_ok g -> (g land 1) = 0 -> (slab_next_gen g land 1) = 1.
Proof.
  intros G Ev. pose proof (next_gen_ok g G) as G1. unfold gen_ok in G, G1.
  assert (M : (Z_ g mod 2 = 0)%Z) by (rewrite <- mask1 by lia; rewrite Ev; reflexivity).
  apply Sint63.to_Z_inj. rewrite mask1 by lia. rewrite (next_gen_Z g ltac:(unfold gen_ok; lia)).
  destruct (Z_ g + 1 =? 268435456)%Z eqn:E.
  - apply Z.eqb_eq in E. assert (Z_ g = 268435455)%Z by lia. rewrite H in M. discriminate M.
  - change (Z_ 1) with 1%Z. rewrite Z.add_mod by lia. rewrite M. reflexivity.
Qed.

(* ---- the memory, from KQSpec.v's laws *)
Lemma neq_Z (x y : int) : Z_ x <> Z_ y -> x <> y.
Proof. intros D E. subst y. apply D. reflexivity. Qed.

Lemma rd_upd_same (b j v : int) (s : mem) :
  (0 <= Z_ b)%Z -> (0 <= Z_ j)%Z -> (Z_ j < Z_ (kq_size b s))%Z -> rd b j (upd b j v s) = v.
Proof.
  intros B J L. apply (rd_upd_eq real real_laws). unfold cell. cbn [Size real].
  replace (0 <=? b) with true by (symmetry; apply le_Z; change (Z_ 0) with 0%Z; lia).
  replace (0 <=? j) with true by (symmetry; apply le_Z; change (Z_ 0) with 0%Z; lia).
  replace (j <? kq_size b s) with true by (symmetry; apply lt_Z; lia). reflexivity.
Qed.

Lemma rd_upd_other (b j j' v : int) (s : mem) : j <> j' -> rd b j' (upd b j v s) = rd b j' s.
Proof.
  intro D. apply (rd_upd_ne real real_laws). unfold other. rewrite Uint63.eqb_refl. cbn [andb].
  destruct (j =? j') eqn:E; [apply Uint63.eqb_spec in E; contradiction | reflexivity].
Qed.

Lemma size_upd' (b j v b' : int) (s : mem) : kq_size b' (upd b j v s) = kq_size b' s.
Proof. exact (size_upd real real_laws b j v b' s). Qed.

(* ---- a slab's cells *)
Lemma base_Z (f i : int) : (1 <= Z_ f <= 1024)%Z -> (0 <= Z_ i < 268435456)%Z ->
  Z_ (slab_base f i) = (8 + Z_ i * (Z_ f + 1))%Z.
Proof.
  intros F I. unfold slab_base.
  assert (A : Z_ (f + 1) = (Z_ f + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
  assert (M : Z_ (i * (f + 1)) = (Z_ i * (Z_ f + 1))%Z) by (rewrite mul_Z; rewrite A; nia).
  rewrite add_Z; change (Z_ 8) with 8%Z; rewrite M; nia.
Qed.

Lemma slot_range (h : int) : (0 <= Z_ h)%Z -> (0 <= Z_ (slab_slot h) < 268435456)%Z.
Proof.
  intro P. unfold slab_slot. rewrite mask28.
  - apply Z.mod_pos_bound. lia.
  - rewrite Sint63.asr_spec. apply Z.div_pos; [exact P | change (Z_ 28) with 28%Z; lia].
Qed.

Lemma gen_range (h : int) : (0 <= Z_ h)%Z -> gen_ok (slab_gen h).
Proof. intro P. unfold gen_ok, slab_gen. rewrite mask28 by exact P. apply Z.mod_pos_bound. lia. Qed.

(* what the theorems assume of the slab in block b: its header, room in the block for every slot it has room for, and
   the generations of the slots used so far *)
Record slab_ok (b : int) (s : mem) : Prop := {
  ok_b    : (0 <= Z_ b < 64)%Z;
  ok_f    : (1 <= Z_ (rd b 3 s) <= 1024)%Z;
  ok_used : (0 <= Z_ (rd b 1 s) <= Z_ (rd b 0 s))%Z;
  ok_cap  : (Z_ (rd b 0 s) < 134217728)%Z;
  ok_size : (8 + Z_ (rd b 0 s) * (Z_ (rd b 3 s) + 1) <= Z_ (kq_size b s))%Z;
  ok_free : (0 <= Z_ (rd b 2 s) <= Z_ (rd b 1 s))%Z;
  ok_gens : forall i, (0 <= Z_ i < Z_ (rd b 1 s))%Z -> gen_ok (rd b (slab_base (rd b 3 s) i) s)
}.

(* a live handle, taken apart *)
Lemma live_parts (b h : int) (s : mem) : slab_live b h s = true ->
  (0 <= Z_ h)%Z /\ (h >> 56) = b /\ (Z_ (slab_slot h) < Z_ (rd b 1 s))%Z /\ (slab_gen h land 1) = 1 /\
  rd b (slab_base (rd b 3 s) (slab_slot h)) s = slab_gen h.
Proof.
  unfold slab_live. cbv zeta. intro L.
  apply andb_prop in L as [L E5]. apply andb_prop in L as [L E4]. apply andb_prop in L as [L E3].
  apply andb_prop in L as [E1 E2].
  apply le_Z in E1. apply Uint63.eqb_spec in E2. apply lt_Z in E3. apply Uint63.eqb_spec in E4. apply Uint63.eqb_spec in E5.
  change (Z_ 0) with 0%Z in E1. repeat split; assumption.
Qed.

(* ---- FREEING KILLS THE HANDLE: after slab_free b h, h is not live, whoever holds a copy of it *)
Theorem slab_free_kills (b h : int) (s : mem) :
  slab_ok b s -> slab_live b h s = true -> slab_live b h (slab_free b h s) = false.
Proof.
  intros OK L. pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  pose proof (slot_range h P) as Ir.
  assert (Iu : (0 <= Z_ (slab_slot h) < Z_ (rd b 1 s))%Z) by lia.
  pose proof (base_Z (rd b 3 s) (slab_slot h) Hf Ir) as Cz.
  pose proof (Hgen (slab_slot h) Iu) as G0. rewrite Gn in G0.
  unfold slab_free. rewrite L. cbv beta iota zeta.
  set (f := rd b 3 s) in *. set (i := slab_slot h) in *. set (c := slab_base f i) in *.
  (* slot i's cells end before the block does: c + f < 8 + (i + 1) * (f + 1) <= 8 + room * (f + 1) <= size *)
  assert (Last : (Z_ i * (Z_ f + 1) + (Z_ f + 1) <= Z_ (rd b 0 s) * (Z_ f + 1))%Z) by nia.
  assert (C1 : Z_ (c + 1) = (Z_ c + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; nia).
  assert (I1 : Z_ (i + 1) = (Z_ i + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
  assert (Cin : (Z_ c + 1 < Z_ (kq_size b s))%Z) by lia.
  set (g := slab_next_gen (rd b c s)).
  set (s1 := upd b c g s). set (s2 := upd b (c + 1) (rd b 2 s) s1). set (s3 := upd b 2 (i + 1) s2).
  (* the slab's size of fields, and slot i's generation, after the three writes *)
  assert (R3 : rd b 3 s3 = f).
  { unfold s3, s2, s1. rewrite rd_upd_other by (apply neq_Z; change (Z_ 2) with 2%Z; change (Z_ 3) with 3%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; rewrite C1; change (Z_ 3) with 3%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; change (Z_ 3) with 3%Z; lia). reflexivity. }
  assert (RC : rd b c s3 = g).
  { unfold s3, s2, s1. rewrite rd_upd_other by (apply neq_Z; change (Z_ 2) with 2%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; rewrite C1; lia).
    apply rd_upd_same; lia. }
  fold s1 s2 s3. unfold slab_live. cbv zeta. fold i. rewrite R3. fold c. rewrite RC.
  assert (Ne : (g =? slab_gen h) = false).
  { unfold g. rewrite Gn. apply Uint63.eqb_false_spec. apply next_gen_ne, G0. }
  rewrite Ne. apply andb_false_r.
Qed.

(* a write to a cell that is not slot h's generation and not the header's count of slots or of fields leaves h as
   live (or dead) as it was *)
Lemma live_upd_other (b h j v : int) (s : mem) :
  j <> 1 -> j <> 3 -> j <> slab_base (rd b 3 s) (slab_slot h) ->
  slab_live b h (upd b j v s) = slab_live b h s.
Proof.
  intros D1 D3 Dc. unfold slab_live. cbv zeta.
  rewrite (rd_upd_other b j 3 v s D3). rewrite (rd_upd_other b j 1 v s D1).
  rewrite (rd_upd_other b j (slab_base (rd b 3 s) (slab_slot h)) v s Dc). reflexivity.
Qed.

(* zeroing fields from c + 1 + k on changes no cell at or below c: the slot's generation and the header *)
Lemma zero_rd_low (fuel : nat) : forall (b c k n j : int) (s : mem),
  (0 <= Z_ k)%Z -> (Z_ n <= 1024)%Z -> (0 <= Z_ c <= 1099511627776)%Z -> (Z_ j <= Z_ c)%Z ->
  rd b j (slab_zero fuel b c k n s) = rd b j s.
Proof.
  induction fuel as [ | fuel IH]; intros b c k n j s K Nn C J; cbn [slab_zero]; [reflexivity | ].
  destruct (n <=? k) eqn:E; [reflexivity | ]. apply le_Z_false in E.
  assert (K1 : Z_ (k + 1) = (Z_ k + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
  assert (C1 : Z_ (c + 1) = (Z_ c + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
  assert (A : Z_ (c + 1 + k) = (Z_ c + 1 + Z_ k)%Z) by (rewrite add_Z; rewrite C1; lia).
  rewrite IH by lia. apply rd_upd_other. apply neq_Z. rewrite A. lia.
Qed.

(* ---- A FIELD READS WHAT WAS WRITTEN TO IT, through a live handle *)
Theorem slab_get_set (b h k v : int) (s : mem) :
  slab_ok b s -> slab_live b h s = true -> (0 <= Z_ k < Z_ (rd b 3 s))%Z ->
  slab_get b h k (slab_set b h k v s) = v.
Proof.
  intros OK L K. pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  pose proof (slot_range h P) as Ir.
  pose proof (base_Z (rd b 3 s) (slab_slot h) Hf Ir) as Cz.
  assert (Last : (Z_ (slab_slot h) * (Z_ (rd b 3 s) + 1) + (Z_ (rd b 3 s) + 1) <= Z_ (rd b 0 s) * (Z_ (rd b 3 s) + 1))%Z)
    by nia.
  assert (C1 : Z_ (slab_base (rd b 3 s) (slab_slot h) + 1) = (Z_ (slab_base (rd b 3 s) (slab_slot h)) + 1)%Z)
    by (rewrite add_Z; change (Z_ 1) with 1%Z; nia).
  assert (CK : Z_ (slab_base (rd b 3 s) (slab_slot h) + 1 + k) = (Z_ (slab_base (rd b 3 s) (slab_slot h)) + 1 + Z_ k)%Z)
    by (rewrite add_Z; rewrite C1; nia).
  assert (K0 : (0 <=? k) = true) by (apply le_Z; change (Z_ 0) with 0%Z; lia).
  assert (KF : (k <? rd b 3 s) = true) by (apply lt_Z; lia).
  unfold slab_set. cbv zeta. rewrite L, K0, KF. cbn [andb].
  set (j := slab_base (rd b 3 s) (slab_slot h) + 1 + k) in *.
  assert (R3 : rd b 3 (upd b j v s) = rd b 3 s)
    by (apply rd_upd_other; apply neq_Z; rewrite CK; change (Z_ 3) with 3%Z; lia).
  assert (Lv : slab_live b h (upd b j v s) = true).
  { rewrite live_upd_other; [exact L | | | ]; apply neq_Z; rewrite CK; [change (Z_ 1) with 1%Z | change (Z_ 3) with 3%Z | ];
    lia. }
  unfold slab_get. cbv zeta. rewrite R3, Lv, K0, KF. cbn [andb]. fold j.
  apply rd_upd_same; lia.
Qed.

(* ---- A FREED HANDLE STAYS DEAD WHEN ITS SLOT IS TAKEN AGAIN: freeing h puts its slot first on the free list, the
   next slab_take takes that slot for a new object -- and h, freed, does not reach it *)
Theorem slab_reuse_keeps_dead (b h : int) (s : mem) :
  slab_ok b s -> slab_live b h s = true -> slab_live b h (slab_take b (slab_free b h s)) = false.
Proof.
  intros OK L. pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  pose proof (slot_range h P) as Ir.
  assert (Iu : (0 <= Z_ (slab_slot h) < Z_ (rd b 1 s))%Z) by lia.
  pose proof (base_Z (rd b 3 s) (slab_slot h) Hf Ir) as Cz.
  pose proof (Hgen (slab_slot h) Iu) as G0. rewrite Gn in G0.
  unfold slab_free. rewrite L. cbv beta iota zeta.
  set (f := rd b 3 s) in *. set (i := slab_slot h) in *. set (c := slab_base f i) in *.
  assert (Last : (Z_ i * (Z_ f + 1) + (Z_ f + 1) <= Z_ (rd b 0 s) * (Z_ f + 1))%Z) by nia.
  assert (C1 : Z_ (c + 1) = (Z_ c + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; nia).
  assert (I1 : Z_ (i + 1) = (Z_ i + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
  assert (Cin : (Z_ c + 1 < Z_ (kq_size b s))%Z) by lia.
  set (g := slab_next_gen (rd b c s)).
  set (s1 := upd b c g s). set (s2 := upd b (c + 1) (rd b 2 s) s1). set (s3 := upd b 2 (i + 1) s2).
  assert (Sz3 : kq_size b s3 = kq_size b s) by (unfold s3, s2, s1; rewrite !size_upd'; reflexivity).
  assert (R3 : rd b 3 s3 = f).
  { unfold s3, s2, s1. rewrite rd_upd_other by (apply neq_Z; change (Z_ 2) with 2%Z; change (Z_ 3) with 3%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; rewrite C1; change (Z_ 3) with 3%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; change (Z_ 3) with 3%Z; lia). reflexivity. }
  assert (R2 : rd b 2 s3 = i + 1).
  { unfold s3. apply rd_upd_same; [lia | change (Z_ 2) with 2%Z; lia | ].
    unfold s2, s1. rewrite !size_upd'. change (Z_ 2) with 2%Z. lia. }
  assert (RC : rd b c s3 = g).
  { unfold s3, s2, s1. rewrite rd_upd_other by (apply neq_Z; change (Z_ 2) with 2%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; rewrite C1; lia).
    apply rd_upd_same; lia. }
  fold s1 s2 s3.
  (* the take: the free list starts at slot i *)
  unfold slab_take. cbv zeta. rewrite R3, R2.
  assert (Pos : (0 <? i + 1) = true) by (apply lt_Z; rewrite I1; change (Z_ 0) with 0%Z; lia).
  assert (Ii : i + 1 - 1 = i).
  { apply Sint63.to_Z_inj. rewrite sub_Z; rewrite I1; change (Z_ 1) with 1%Z; lia. }
  rewrite Pos, Ii. fold c. rewrite RC.
  set (g2 := slab_next_gen g).
  set (s4 := upd b 2 (rd b (c + 1) s3) s3). set (s5 := upd b c g2 s4).
  assert (Cb : (0 <= Z_ c <= 1099511627776)%Z) by nia.
  assert (Z3 : rd b 3 (slab_zero (kq_nat f) b c 0 f s5) = f).
  { rewrite zero_rd_low by (change (Z_ 0) with 0%Z; change (Z_ 3) with 3%Z; lia).
    unfold s5, s4. rewrite rd_upd_other by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; change (Z_ 2) with 2%Z; change (Z_ 3) with 3%Z; lia). exact R3. }
  assert (ZC : rd b c (slab_zero (kq_nat f) b c 0 f s5) = g2).
  { rewrite zero_rd_low by (change (Z_ 0) with 0%Z; lia).
    unfold s5. apply rd_upd_same; [lia | lia | ]. unfold s4. rewrite size_upd', Sz3. lia. }
  unfold slab_live. cbv zeta. fold i. rewrite Z3. fold c. rewrite ZC.
  assert (Ne : (g2 =? slab_gen h) = false).
  { unfold g2, g. rewrite Gn. apply Uint63.eqb_false_spec. apply next_next_ne, G0. }
  rewrite Ne. apply andb_false_r.
Qed.

(* growing a block to n cells: it has at least n, and at least what it had *)
Lemma size_grow_ge (b n : int) (s : mem) : (0 <= Z_ b < 64)%Z -> (0 <= Z_ n < 2147483648)%Z ->
  (Z_ n <= Z_ (kq_size b (kq_grow b n s)))%Z /\ (Z_ (kq_size b s) <= Z_ (kq_size b (kq_grow b n s)))%Z.
Proof.
  intros B Nn.
  assert (G : growable b n = true).
  { unfold growable.
    replace (0 <=? b) with true by (symmetry; apply le_Z; change (Z_ 0) with 0%Z; lia).
    replace (b <? 64) with true by (symmetry; apply lt_Z; change (Z_ 64) with 64%Z; lia).
    replace (0 <=? n) with true by (symmetry; apply le_Z; change (Z_ 0) with 0%Z; lia).
    replace (n <? 2147483648) with true by (symmetry; apply lt_Z; change (Z_ 2147483648) with 2147483648%Z; lia).
    reflexivity. }
  pose proof (size_grow real real_laws b n s G) as E. cbn [Size Grow real] in E. rewrite E.
  destruct (kq_size b s <? n) eqn:L; [apply lt_Z in L | apply lt_Z_false in L]; lia.
Qed.

Lemma rd_grow' (b n b' j : int) (s : mem) : rd b' j (kq_grow b n s) = rd b' j s.
Proof. exact (rd_grow real real_laws b n b' j s). Qed.

(* a never-used slot i, its generation just set to 1 and the count of used slots to i + 1: the handle (b, i, 1) is
   live -- the two never-used cases of slab_take share this *)
Lemma fresh_live (b f i : int) (s : mem) :
  (0 <= Z_ b < 64)%Z -> (1 <= Z_ f <= 1024)%Z -> (0 <= Z_ i < 268435456)%Z -> rd b 3 s = f ->
  (Z_ (slab_base f i) + 1 < Z_ (kq_size b s))%Z ->
  slab_live b (slab_handle b i 1) (upd b (slab_base f i) 1 (upd b 1 (i + 1) s)) = true.
Proof.
  intros Hb Hf Hi R3 In. pose proof (base_Z f i Hf Hi) as Cz.
  assert (Pk : parts_ok b i 1) by (unfold parts_ok; change (Z_ 1) with 1%Z; lia).
  assert (I1 : Z_ (i + 1) = (Z_ i + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
  set (c := slab_base f i) in *.
  set (s1 := upd b 1 (i + 1) s). set (s2 := upd b c 1 s1).
  assert (Sz1 : kq_size b s1 = kq_size b s) by apply size_upd'.
  assert (R1 : rd b 1 s2 = i + 1).
  { unfold s2. rewrite rd_upd_other by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
    unfold s1. apply rd_upd_same; change (Z_ 1) with 1%Z; lia. }
  assert (R3' : rd b 3 s2 = f).
  { unfold s2, s1. rewrite rd_upd_other by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
    rewrite rd_upd_other by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 3) with 3%Z; lia). exact R3. }
  assert (RC : rd b c s2 = 1) by (unfold s2; apply rd_upd_same; [lia | lia | rewrite Sz1; lia]).
  unfold slab_live. cbv zeta. rewrite (handle_slot b i 1 Pk), (handle_gen b i 1 Pk), (handle_block b i 1 Pk).
  rewrite R1, R3'. fold c. rewrite RC.
  replace (0 <=? slab_handle b i 1) with true by (symmetry; apply le_Z; change (Z_ 0) with 0%Z; apply handle_nonneg, Pk).
  replace (i <? i + 1) with true by (symmetry; apply lt_Z; rewrite I1; lia).
  rewrite Uint63.eqb_refl. reflexivity.
Qed.

(* ---- TAKING GIVES A LIVE HANDLE: the handle slab_next promised is live after slab_take -- when the free list's first
   slot is free (an even generation) and, if the slab must double, the doubled block still has fewer than 2^31 cells *)
Theorem slab_take_live (b : int) (s : mem) :
  slab_ok b s ->
  ((0 <? rd b 2 s) = true -> (rd b (slab_base (rd b 3 s) (rd b 2 s - 1)) s land 1) = 0) ->
  (8 + (2 * Z_ (rd b 0 s) + 1) * (Z_ (rd b 3 s) + 1) < 2147483648)%Z ->
  slab_next b s <> 0 ->
  slab_live b (slab_next b s) (slab_take b s) = true.
Proof.
  intros OK FE Room Nz. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  unfold slab_next in *. unfold slab_take. cbv zeta in *.
  destruct (0 <? rd b 2 s) eqn:Fr; cbv beta iota in *.
  - (* the first slot of the free list *)
    apply lt_Z in Fr. change (Z_ 0) with 0%Z in Fr.
    specialize (FE eq_refl).
    set (f := rd b 3 s) in *. set (fr := rd b 2 s) in *.
    assert (J : Z_ (fr - 1) = (Z_ fr - 1)%Z) by (rewrite sub_Z; change (Z_ 1) with 1%Z; lia).
    set (j := fr - 1) in *.
    assert (Jr : (0 <= Z_ j < Z_ (rd b 1 s))%Z) by lia.
    pose proof (base_Z f j Hf ltac:(lia)) as Cz.
    set (c := slab_base f j) in *.
    pose proof (Hgen j Jr) as G0. fold f c in G0.
    set (g := slab_next_gen (rd b c s)).
    assert (Gk : gen_ok g) by (apply next_gen_ok, G0).
    assert (Go : (g land 1) = 1) by (apply next_gen_odd; assumption).
    assert (Pk : parts_ok b j g) by (unfold parts_ok; unfold gen_ok in Gk; lia).
    assert (Last : (Z_ j * (Z_ f + 1) + (Z_ f + 1) <= Z_ (rd b 0 s) * (Z_ f + 1))%Z) by nia.
    assert (Cb : (0 <= Z_ c <= 1099511627776)%Z) by nia.
    set (s1 := upd b 2 (rd b (c + 1) s) s). set (s2 := upd b c g s1).
    assert (Z1 : rd b 1 (slab_zero (kq_nat f) b c 0 f s2) = rd b 1 s).
    { rewrite zero_rd_low by (change (Z_ 0) with 0%Z; change (Z_ 1) with 1%Z; lia).
      unfold s2, s1. rewrite rd_upd_other by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
      rewrite rd_upd_other by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 2) with 2%Z; lia). reflexivity. }
    assert (Z3 : rd b 3 (slab_zero (kq_nat f) b c 0 f s2) = f).
    { rewrite zero_rd_low by (change (Z_ 0) with 0%Z; change (Z_ 3) with 3%Z; lia).
      unfold s2, s1. rewrite rd_upd_other by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
      rewrite rd_upd_other by (apply neq_Z; change (Z_ 2) with 2%Z; change (Z_ 3) with 3%Z; lia). reflexivity. }
    assert (ZC : rd b c (slab_zero (kq_nat f) b c 0 f s2) = g).
    { rewrite zero_rd_low by (change (Z_ 0) with 0%Z; lia).
      unfold s2. apply rd_upd_same; [lia | lia | ]. unfold s1. rewrite size_upd'. lia. }
    unfold slab_live. cbv zeta. rewrite (handle_slot b j g Pk), (handle_gen b j g Pk), (handle_block b j g Pk).
    rewrite Z1, Z3. fold c. rewrite ZC, Go.
    replace (0 <=? slab_handle b j g) with true by (symmetry; apply le_Z; change (Z_ 0) with 0%Z; apply handle_nonneg, Pk).
    replace (j <? rd b 1 s) with true by (symmetry; apply lt_Z; lia).
    rewrite !Uint63.eqb_refl. reflexivity.
  - (* a slot never used *)
    set (f := rd b 3 s) in *. set (i := rd b 1 s) in *. set (cap := rd b 0 s) in *.
    destruct (i <? cap) eqn:R; cbn [orb] in *.
    + (* there is room *)
      apply lt_Z in R. pose proof (base_Z f i Hf ltac:(lia)) as Cz.
      apply fresh_live; [lia | exact Hf | lia | reflexivity | nia].
    + (* full: the slab doubles, unless it is a fixed pool -- and then slab_next was 0 *)
      apply lt_Z_false in R.
      destruct (rd b 4 s =? 1) eqn:Gw; [ | exfalso; apply Nz; reflexivity]. cbv beta iota.
      assert (Ic : Z_ i = Z_ cap) by lia.
      assert (N2 : Z_ (2 * cap + 1) = (2 * Z_ cap + 1)%Z).
      { assert (M : Z_ (2 * cap) = (2 * Z_ cap)%Z) by (rewrite mul_Z; change (Z_ 2) with 2%Z; lia).
        rewrite add_Z; rewrite M; change (Z_ 1) with 1%Z; lia. }
      assert (F1 : Z_ (f + 1) = (Z_ f + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
      assert (NF : Z_ ((2 * cap + 1) * (f + 1)) = ((2 * Z_ cap + 1) * (Z_ f + 1))%Z)
        by (rewrite mul_Z; rewrite N2, F1; nia).
      assert (NN : Z_ (8 + (2 * cap + 1) * (f + 1)) = (8 + (2 * Z_ cap + 1) * (Z_ f + 1))%Z)
        by (rewrite add_Z; rewrite NF; change (Z_ 8) with 8%Z; nia).
      set (n := 8 + (2 * cap + 1) * (f + 1)) in *.
      pose proof (size_grow_ge b n s Hb ltac:(nia)) as [Gn1 Gn2].
      set (s1 := kq_grow b n s). set (s2 := upd b 0 (2 * cap + 1) s1).
      pose proof (base_Z f i Hf ltac:(lia)) as Cz.
      apply fresh_live; [lia | exact Hf | lia | | ].
      * unfold s2. rewrite rd_upd_other by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 3) with 3%Z; lia).
        unfold s1. rewrite rd_grow'. reflexivity.
      * unfold s2, s1. rewrite size_upd'. nia.
Qed.
