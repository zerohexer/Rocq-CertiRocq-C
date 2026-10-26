(* lib/SlabSpec.v -- WHAT A SLAB GUARANTEES, proved against the memory's laws (KQSpec.v): a handle is live once its slot
   is taken, dead once its object is freed, and stays dead when the slot is taken again; a field reads what was last
   written to it.  Every number below is a 63-bit machine number; `Z_` reads it as an integer. *)
From Stdlib Require Import ZArith Lia Sint63 Bool List.
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

(* ======================================================================================================================
   THE SLAB'S INVARIANT IS KEPT: slab_ok (the header and the generations are well formed) holds again after every
   operation -- init, set, free, take -- so a theorem about a program that calls them one after the other can use it at
   each step.  Each operation writes a few cells; what is shown is which cells, and that none of them breaks the invariant. *)

(* the cell t of slot i is slab_base f i + t *)
Lemma cell_Z (f i t : int) : (1 <= Z_ f <= 1024)%Z -> (0 <= Z_ i < 268435456)%Z -> (0 <= Z_ t <= 1025)%Z ->
  Z_ (slab_base f i + t) = (8 + Z_ i * (Z_ f + 1) + Z_ t)%Z.
Proof.
  intros F I T. pose proof (base_Z f i F I) as B.
  assert (P : (Z_ i * (Z_ f + 1) <= 268435456 * 1025)%Z) by nia.
  rewrite add_Z; [rewrite B; lia | rewrite B; lia].
Qed.

(* two cells of a slab are the same cell only if they are the same cell of the same slot *)
Lemma cell_ne (f x y t u : Z) : (1 <= f <= 1024)%Z -> (x <> y \/ t <> u) -> (0 <= t <= f)%Z -> (0 <= u <= f)%Z ->
  (8 + x * (f + 1) + t <> 8 + y * (f + 1) + u)%Z.
Proof.
  intros F D T U E. destruct (Z.eq_dec x y) as [Exy | Nxy].
  - subst y. destruct D as [D | D]; [contradiction | lia].
  - assert (H : ((x - y) * (f + 1) = u - t)%Z) by nia.
    destruct (Z.lt_trichotomy x y) as [L | [Q | G]]; [nia | contradiction | nia].
Qed.

(* a write that touches neither the header's first four cells nor the generation of a slot in use keeps the invariant *)
Lemma ok_upd_plain (b j v : int) (s : mem) : slab_ok b s -> (4 <= Z_ j)%Z ->
  (forall i, (0 <= Z_ i < Z_ (rd b 1 s))%Z -> j <> slab_base (rd b 3 s) i) -> slab_ok b (upd b j v s).
Proof.
  intros OK J G. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  assert (n0 : j <> 0) by (apply neq_Z; change (Z_ 0) with 0%Z; lia).
  assert (n1 : j <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
  assert (n2 : j <> 2) by (apply neq_Z; change (Z_ 2) with 2%Z; lia).
  assert (n3 : j <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
  assert (r0 := rd_upd_other b j 0 v s n0). assert (r1 := rd_upd_other b j 1 v s n1).
  assert (r2 := rd_upd_other b j 2 v s n2). assert (r3 := rd_upd_other b j 3 v s n3).
  assert (sz := size_upd' b j v b s).
  refine (Build_slab_ok b _ Hb _ _ _ _ _ _).
  - rewrite r3. exact Hf.
  - rewrite r1, r0. exact Hus.
  - rewrite r0. exact Hcap.
  - rewrite r0, r3, sz. exact Hsz.
  - rewrite r2, r1. exact Hfr.
  - intros i Hi. rewrite r1 in Hi. rewrite r3. rewrite (rd_upd_other b j _ v s (G i Hi)). exact (Hgen i Hi).
Qed.

(* the same, for a write of a good generation to the generation of a slot in use *)
Lemma ok_upd_gen (b i g : int) (s : mem) : slab_ok b s -> (0 <= Z_ i < Z_ (rd b 1 s))%Z -> gen_ok g ->
  slab_ok b (upd b (slab_base (rd b 3 s) i) g s).
Proof.
  intros OK Hi Gg. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (f := rd b 3 s) in *. set (j := slab_base f i).
  assert (I28 : (0 <= Z_ i < 268435456)%Z) by lia.
  assert (Jz : Z_ j = (8 + Z_ i * (Z_ f + 1))%Z) by (apply base_Z; assumption).
  assert (Last : (Z_ i * (Z_ f + 1) + (Z_ f + 1) <= Z_ (rd b 0 s) * (Z_ f + 1))%Z) by nia.
  assert (n0 : j <> 0) by (apply neq_Z; change (Z_ 0) with 0%Z; lia).
  assert (n1 : j <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
  assert (n2 : j <> 2) by (apply neq_Z; change (Z_ 2) with 2%Z; lia).
  assert (n3 : j <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
  assert (r0 := rd_upd_other b j 0 g s n0). assert (r1 := rd_upd_other b j 1 g s n1).
  assert (r2 := rd_upd_other b j 2 g s n2). assert (r3 := rd_upd_other b j 3 g s n3).
  assert (sz := size_upd' b j g b s).
  refine (Build_slab_ok b _ Hb _ _ _ _ _ _).
  - rewrite r3. exact Hf.
  - rewrite r1, r0. exact Hus.
  - rewrite r0. exact Hcap.
  - rewrite r0, r3, sz. exact Hsz.
  - rewrite r2, r1. exact Hfr.
  - intros i2 Hi2. rewrite r1 in Hi2. rewrite r3. fold f.
  destruct (Z.eq_dec (Z_ i2) (Z_ i)) as [E | N].
  + apply Sint63.to_Z_inj in E. subst i2. fold j. rewrite rd_upd_same; [exact Gg | lia | lia | lia].
  + assert (D : j <> slab_base f i2).
    { apply neq_Z. rewrite Jz. rewrite base_Z by (try assumption; lia).
      pose proof (cell_ne (Z_ f) (Z_ i) (Z_ i2) 0 0 Hf ltac:(left; lia) ltac:(lia) ltac:(lia)) as X. lia. }
    rewrite (rd_upd_other b j _ g s D). exact (Hgen i2 Hi2).
Qed.

(* slab_set keeps the invariant: it writes a field of a slot in use *)
Theorem slab_set_ok (b h k v : int) (s : mem) : slab_ok b s -> slab_ok b (slab_set b h k v s).
Proof.
  intros OK. unfold slab_set. cbv zeta.
  destruct (slab_live b h s && (0 <=? k) && (k <? rd b 3 s)) eqn:Hc; [ | exact OK].
  apply andb_prop in Hc as [Hc E3]. apply andb_prop in Hc as [L E2].
  apply lt_Z in E3. apply le_Z in E2. change (Z_ 0) with 0%Z in E2.
  pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  pose proof (slot_range h P) as Ir.
  pose proof OK as OK0. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (f := rd b 3 s) in *. set (i := slab_slot h) in *.
  assert (C1 : Z_ (slab_base f i + 1) = (8 + Z_ i * (Z_ f + 1) + 1)%Z).
  { apply cell_Z; [assumption | assumption | change (Z_ 1) with 1%Z; lia]. }
  assert (CK : Z_ (slab_base f i + 1 + k) = (8 + Z_ i * (Z_ f + 1) + 1 + Z_ k)%Z).
  { assert (PB : (Z_ i * (Z_ f + 1) <= 268435456 * 1025)%Z) by nia. rewrite add_Z; [rewrite C1; lia | rewrite C1; lia]. }
  apply ok_upd_plain; [exact OK0 | | ].
  - rewrite CK. nia.
  - intros i2 Hi2. apply neq_Z. rewrite CK. rewrite base_Z by (try assumption; lia).
    pose proof (cell_ne (Z_ f) (Z_ i) (Z_ i2) (1 + Z_ k) 0 Hf ltac:(right; lia) ltac:(lia) ltac:(lia)) as X. fold f. lia.
Qed.

(* a write to the header's cell 2 (the free list's head) of a value from 0 to the count of slots in use keeps the invariant *)
Lemma ok_upd_head (b v : int) (s : mem) : slab_ok b s -> (0 <= Z_ v <= Z_ (rd b 1 s))%Z -> slab_ok b (upd b 2 v s).
Proof.
  intros OK V. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  assert (n0 : 2 <> 0) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 2) with 2%Z; lia).
  assert (n1 : 2 <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 2) with 2%Z; lia).
  assert (n3 : 2 <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; change (Z_ 2) with 2%Z; lia).
  assert (r0 := rd_upd_other b 2 0 v s n0). assert (r1 := rd_upd_other b 2 1 v s n1).
  assert (r3 := rd_upd_other b 2 3 v s n3). assert (sz := size_upd' b 2 v b s).
  assert (Cap0 : (0 <= Z_ (rd b 0 s))%Z) by lia.
  assert (Pm : (0 <= Z_ (rd b 0 s) * (Z_ (rd b 3 s) + 1))%Z) by nia.
  refine (Build_slab_ok b _ Hb _ _ _ _ _ _).
  - rewrite r3. exact Hf.
  - rewrite r1, r0. exact Hus.
  - rewrite r0. exact Hcap.
  - rewrite r0, r3, sz. exact Hsz.
  - rewrite r1. rewrite rd_upd_same; [exact V | change (Z_ 0) with 0%Z; lia | change (Z_ 2) with 2%Z; lia | change (Z_ 2) with 2%Z; lia].
  - intros i Hi. rewrite r1 in Hi. rewrite r3.
    assert (Iz : (0 <= Z_ i < 268435456)%Z) by lia.
    assert (D : 2 <> slab_base (rd b 3 s) i).
    { apply neq_Z. rewrite base_Z by (try assumption; lia). change (Z_ 2) with 2%Z. nia. }
    rewrite (rd_upd_other b 2 _ v s D). exact (Hgen i Hi).
Qed.

(* slab_free keeps the invariant *)
Theorem slab_free_ok (b h : int) (s : mem) : slab_ok b s -> slab_ok b (slab_free b h s).
Proof.
  intros OK. unfold slab_free. destruct (slab_live b h s) eqn:L; [ | exact OK]. cbv zeta.
  pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  pose proof (slot_range h P) as Ir.
  pose proof OK as OK0. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (f := rd b 3 s) in *. set (i := slab_slot h) in *. set (c := slab_base f i) in *.
  assert (Hi : (0 <= Z_ i < Z_ (rd b 1 s))%Z) by lia.
  assert (Cz : Z_ c = (8 + Z_ i * (Z_ f + 1))%Z) by (apply base_Z; assumption).
  assert (PB : (Z_ i * (Z_ f + 1) <= 268435456 * 1025)%Z) by nia.
  assert (C1 : Z_ (c + 1) = (Z_ c + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; rewrite Cz; lia]).
  assert (I1 : Z_ (i + 1) = (Z_ i + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; lia]).
  set (g := slab_next_gen (rd b c s)).
  assert (Gg : gen_ok g) by (apply next_gen_ok, (Hgen i Hi)).
  pose proof (ok_upd_gen b i g s OK0 Hi Gg) as S1. fold f c in S1.
  set (s1 := upd b c g s) in *.
  assert (n1 : c <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
  assert (n3 : c <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
  assert (R1 : rd b 1 s1 = rd b 1 s) by apply (rd_upd_other b c 1 g s n1).
  assert (R3 : rd b 3 s1 = f) by apply (rd_upd_other b c 3 g s n3).
  assert (S2 : slab_ok b (upd b (c + 1) (rd b 2 s) s1)).
  { apply ok_upd_plain; [exact S1 | rewrite C1; lia | ].
    intros i2 Hi2. rewrite R1 in Hi2. rewrite R3. apply neq_Z. rewrite C1, Cz.
    rewrite base_Z by (try assumption; lia). fold f.
    pose proof (cell_ne (Z_ f) (Z_ i) (Z_ i2) 1 0 Hf ltac:(right; lia) ltac:(lia) ltac:(lia)) as X. lia. }
  set (s2 := upd b (c + 1) (rd b 2 s) s1) in *.
  assert (n1' : c + 1 <> 1) by (apply neq_Z; rewrite C1; change (Z_ 1) with 1%Z; lia).
  assert (R1' : rd b 1 s2 = rd b 1 s) by (unfold s2; rewrite (rd_upd_other b (c + 1) 1 _ s1 n1'); exact R1).
  apply ok_upd_head; [exact S2 | rewrite R1', I1; lia].
Qed.

(* ======================================================================================================================
   THE FREE LIST.  slab_ok alone does not say what a free slot's first field holds: freeing writes the next free slot
   there, taking reads it back as the new head.  The stronger invariant says the free list is a list of distinct slots in
   use, each with an even generation (free), the head cell naming the first and each slot's first field the next. *)
Open Scope list_scope.

(* the head pointer a list of slots stands for: 0 for the empty list, else the first slot plus 1 *)
Definition fl_next (l : list int) : int := match l with nil => 0 | y :: _ => y + 1 end.

Fixpoint fl_chain (b : int) (s : mem) (l : list int) : Prop :=
  match l with
  | nil => True
  | x :: r => rd b (slab_base (rd b 3 s) x + 1) s = fl_next r /\ fl_chain b s r
  end.

Definition fl_body (b : int) (s : mem) (l : list int) : Prop :=
  NoDup l /\
  (forall x, In x l -> (0 <= Z_ x < Z_ (rd b 1 s))%Z /\ (rd b (slab_base (rd b 3 s) x) s land 1) = 0) /\
  fl_chain b s l.

Definition slab_inv (b : int) (s : mem) : Prop :=
  slab_ok b s /\ exists l, fl_body b s l /\ rd b 2 s = fl_next l.

Lemma fl_chain_upd (b j v : int) (s : mem) (l : list int) : j <> 3 ->
  (forall x, In x l -> j <> slab_base (rd b 3 s) x + 1) -> fl_chain b s l -> fl_chain b (upd b j v s) l.
Proof.
  intros J3. induction l as [ | x r IH]; intros Hc Ch; [exact I | ].
  cbn [fl_chain] in Ch |- *. destruct Ch as [C1 C2].
  rewrite (rd_upd_other b j 3 v s J3). split.
  - rewrite (rd_upd_other b j _ v s (Hc x (or_introl eq_refl))). exact C1.
  - apply IH; [intros y Hy; apply Hc; right; exact Hy | exact C2].
Qed.

(* a write to a cell that is no cell of a free slot (nor the header's counts) leaves the free list's body as it was *)
Lemma fl_body_upd (b j v : int) (s : mem) (l : list int) : fl_body b s l -> j <> 1 -> j <> 3 ->
  (forall x, In x l -> j <> slab_base (rd b 3 s) x /\ j <> slab_base (rd b 3 s) x + 1) ->
  fl_body b (upd b j v s) l.
Proof.
  intros [Nd [Mem Ch]] J1 J3 Hc.
  unfold fl_body. rewrite (rd_upd_other b j 1 v s J1), (rd_upd_other b j 3 v s J3).
  split; [exact Nd | split].
  - intros x Hx. rewrite (rd_upd_other b j _ v s (proj1 (Hc x Hx))). exact (Mem x Hx).
  - apply fl_chain_upd; [exact J3 | intros x Hx; exact (proj2 (Hc x Hx)) | exact Ch].
Qed.

(* a live slot is not on the free list: the list's slots have an even generation, a live one an odd one *)
Lemma live_not_free (b h x : int) (s : mem) (l : list int) : slab_live b h s = true -> fl_body b s l -> In x l ->
  x <> slab_slot h.
Proof.
  intros L [Nd [Mem Ch]] Hx E. pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  pose proof (proj2 (Mem x Hx)) as Ev. subst x. rewrite Gn in Ev. rewrite Od in Ev.
  apply (f_equal Sint63.to_Z) in Ev. change (Z_ 1) with 1%Z in Ev. change (Z_ 0) with 0%Z in Ev. lia.
Qed.

(* slab_set keeps the whole invariant: a live slot is not on the free list, so its fields are not the list's cells *)
Theorem slab_set_inv (b h k v : int) (s : mem) : slab_inv b s -> slab_inv b (slab_set b h k v s).
Proof.
  intros [OK [l [Bd Hd]]]. pose proof (slab_set_ok b h k v s OK) as SOK. unfold slab_set. cbv zeta. unfold slab_set in SOK. cbv zeta in SOK.
  destruct (slab_live b h s && (0 <=? k) && (k <? rd b 3 s)) eqn:Hc.
  2: { split; [exact OK | exists l; split; assumption]. }
  apply andb_prop in Hc as [Hc E3]. apply andb_prop in Hc as [L E2].
  apply lt_Z in E3. apply le_Z in E2. change (Z_ 0) with 0%Z in E2.
  pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  pose proof (slot_range h P) as Ir.
  pose proof OK as OK0. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (f := rd b 3 s) in *. set (i := slab_slot h) in *.
  assert (PB : (Z_ i * (Z_ f + 1) <= 268435456 * 1025)%Z) by nia.
  assert (C1 : Z_ (slab_base f i + 1) = (8 + Z_ i * (Z_ f + 1) + 1)%Z).
  { apply cell_Z; [assumption | assumption | change (Z_ 1) with 1%Z; lia]. }
  assert (CK : Z_ (slab_base f i + 1 + k) = (8 + Z_ i * (Z_ f + 1) + 1 + Z_ k)%Z).
  { rewrite add_Z; [rewrite C1; lia | rewrite C1; lia]. }
  assert (J1 : slab_base f i + 1 + k <> 1) by (apply neq_Z; rewrite CK; change (Z_ 1) with 1%Z; nia).
  assert (J2 : slab_base f i + 1 + k <> 2) by (apply neq_Z; rewrite CK; change (Z_ 2) with 2%Z; nia).
  assert (J3 : slab_base f i + 1 + k <> 3) by (apply neq_Z; rewrite CK; change (Z_ 3) with 3%Z; nia).
  split.
  - exact SOK.
  - exists l. split.
    + apply fl_body_upd; [exact Bd | exact J1 | exact J3 | ].
      intros x Hx. pose proof (live_not_free b h x s l L Bd Hx) as Nx. fold i in Nx.
      pose proof (proj1 ((proj1 (proj2 Bd)) x Hx)) as Xr. fold f.
      assert (Xz : (0 <= Z_ x < 268435456)%Z) by lia.
      split; apply neq_Z; rewrite CK; rewrite ?base_Z by (try assumption; lia).
      * pose proof (cell_ne (Z_ f) (Z_ i) (Z_ x) (1 + Z_ k) 0 Hf ltac:(right; lia) ltac:(lia) ltac:(lia)) as X. lia.
      * rewrite cell_Z by (try assumption; change (Z_ 1) with 1%Z; lia).
        pose proof (cell_ne (Z_ f) (Z_ i) (Z_ x) (1 + Z_ k) 1 Hf ltac:(left; intro E; apply Nx; symmetry; apply Sint63.to_Z_inj; lia) ltac:(lia) ltac:(lia)) as X.
        change (Z_ 1) with 1%Z. lia.
    + rewrite (rd_upd_other b _ 2 v s J2). exact Hd.
Qed.

(* cells of different slots are different cells *)
Section Cells.
Variables (f i x : int).
Hypothesis Hf : (1 <= Z_ f <= 1024)%Z.
Hypothesis Hi : (0 <= Z_ i < 268435456)%Z.
Hypothesis Hx : (0 <= Z_ x < 268435456)%Z.
Hypothesis Hne : Z_ i <> Z_ x.
Let one : Z_ 1 = 1%Z := eq_refl.
Lemma cells_00 : slab_base f i <> slab_base f x.
Proof.
  apply neq_Z. rewrite !base_Z by assumption.
  pose proof (cell_ne (Z_ f) (Z_ i) (Z_ x) 0 0 Hf ltac:(left; lia) ltac:(lia) ltac:(lia)) as X. lia.
Qed.
Lemma cells_01 : slab_base f i <> slab_base f x + 1.
Proof.
  apply neq_Z. rewrite base_Z by assumption. rewrite cell_Z by (try assumption; rewrite one; lia). rewrite one.
  pose proof (cell_ne (Z_ f) (Z_ i) (Z_ x) 0 1 Hf ltac:(left; lia) ltac:(lia) ltac:(lia)) as X. lia.
Qed.
Lemma cells_10 : slab_base f i + 1 <> slab_base f x.
Proof.
  apply neq_Z. rewrite base_Z by assumption. rewrite cell_Z by (try assumption; rewrite one; lia). rewrite one.
  pose proof (cell_ne (Z_ f) (Z_ i) (Z_ x) 1 0 Hf ltac:(left; lia) ltac:(lia) ltac:(lia)) as X. lia.
Qed.
Lemma cells_11 : slab_base f i + 1 <> slab_base f x + 1.
Proof.
  apply neq_Z. rewrite !cell_Z by (try assumption; rewrite one; lia). rewrite one.
  pose proof (cell_ne (Z_ f) (Z_ i) (Z_ x) 1 1 Hf ltac:(left; lia) ltac:(lia) ltac:(lia)) as X. lia.
Qed.
End Cells.

(* freeing moves an odd generation to the next, which is even *)
Lemma next_gen_even (g : int) : gen_ok g -> (g land 1) = 1 -> (slab_next_gen g land 1) = 0.
Proof.
  intros G Od. pose proof (next_gen_ok g G) as G1. unfold gen_ok in G, G1.
  assert (M : (Z_ g mod 2 = 1)%Z) by (rewrite <- mask1 by lia; rewrite Od; reflexivity).
  apply Sint63.to_Z_inj. rewrite mask1 by lia. rewrite (next_gen_Z g ltac:(unfold gen_ok; lia)).
  destruct (Z_ g + 1 =? 268435456)%Z eqn:E.
  - reflexivity.
  - change (Z_ 0) with 0%Z. rewrite Z.add_mod by lia. rewrite M. reflexivity.
Qed.

(* slab_free keeps the whole invariant: the freed slot goes to the front of the free list *)
Theorem slab_free_inv (b h : int) (s : mem) : slab_inv b s -> slab_inv b (slab_free b h s).
Proof.
  intros [OK [l [Bd Hd]]]. split; [exact (slab_free_ok b h s OK) | ].
  unfold slab_free. destruct (slab_live b h s) eqn:L; [ | exists l; split; assumption]. cbv zeta.
  pose proof (live_parts b h s L) as (P & Bk & Sl & Od & Gn).
  pose proof (slot_range h P) as Ir.
  pose proof OK as OK0. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (f := rd b 3 s) in *. set (i := slab_slot h) in *. set (c := slab_base f i) in *.
  assert (Hi : (0 <= Z_ i < Z_ (rd b 1 s))%Z) by lia.
  assert (Cz : Z_ c = (8 + Z_ i * (Z_ f + 1))%Z) by (apply base_Z; assumption).
  assert (PB : (Z_ i * (Z_ f + 1) <= 268435456 * 1025)%Z) by nia.
  assert (Last : (Z_ i * (Z_ f + 1) + (Z_ f + 1) <= Z_ (rd b 0 s) * (Z_ f + 1))%Z) by nia.
  assert (C1 : Z_ (c + 1) = (Z_ c + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; rewrite Cz; lia]).
  assert (I1 : Z_ (i + 1) = (Z_ i + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; lia]).
  set (g := slab_next_gen (rd b c s)).
  assert (Gg : gen_ok g) by (apply next_gen_ok, (Hgen i Hi)).
  assert (Ge : (g land 1) = 0) by (unfold g; apply next_gen_even; [exact (Hgen i Hi) | rewrite Gn; exact Od]).
  pose proof Bd as Bd0. destruct Bd0 as [Nd [Mem Ch]].
  assert (Nx : forall x, In x l -> x <> i) by (intros x Hx; exact (live_not_free b h x s l L Bd Hx)).
  assert (Xr : forall x, In x l -> (0 <= Z_ x < 268435456)%Z) by (intros x Hx; pose proof (proj1 (Mem x Hx)); lia).
  assert (Nxz : forall x, In x l -> Z_ i <> Z_ x) by (intros x Hx E; apply (Nx x Hx); symmetry; apply Sint63.to_Z_inj; exact E).
  assert (n1 : c <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
  assert (n3 : c <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
  assert (n1' : c + 1 <> 1) by (apply neq_Z; rewrite C1; change (Z_ 1) with 1%Z; lia).
  assert (n3' : c + 1 <> 3) by (apply neq_Z; rewrite C1; change (Z_ 3) with 3%Z; lia).
  assert (n2' : c + 1 <> 2) by (apply neq_Z; rewrite C1; change (Z_ 2) with 2%Z; lia).
  assert (n2 : c <> 2) by (apply neq_Z; change (Z_ 2) with 2%Z; lia).
  set (s1 := upd b c g s).
  assert (B1 : fl_body b s1 l).
  { apply fl_body_upd; [exact Bd | exact n1 | exact n3 | ].
    intros x Hx. split; [apply cells_00 | apply cells_01]; try assumption; try (apply Xr; exact Hx); apply Nxz; exact Hx. }
  assert (R1 : rd b 1 s1 = rd b 1 s) by apply (rd_upd_other b c 1 g s n1).
  assert (R3 : rd b 3 s1 = f) by apply (rd_upd_other b c 3 g s n3).
  assert (Sz1 : kq_size b s1 = kq_size b s) by apply size_upd'.
  set (s2 := upd b (c + 1) (rd b 2 s) s1).
  assert (B2 : fl_body b s2 l).
  { apply fl_body_upd; [exact B1 | exact n1' | exact n3' | ].
    intros x Hx. rewrite R3. split; [apply cells_10 | apply cells_11]; try assumption; try (apply Xr; exact Hx); apply Nxz; exact Hx. }
  assert (R1' : rd b 1 s2 = rd b 1 s) by (unfold s2; rewrite (rd_upd_other b (c + 1) 1 _ s1 n1'); exact R1).
  assert (R3' : rd b 3 s2 = f) by (unfold s2; rewrite (rd_upd_other b (c + 1) 3 _ s1 n3'); exact R3).
  set (s3 := upd b 2 (i + 1) s2).
  assert (n21 : 2 <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 2) with 2%Z; lia).
  assert (n23 : 2 <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; change (Z_ 2) with 2%Z; lia).
  assert (B3 : fl_body b s3 l).
  { apply fl_body_upd; [exact B2 | exact n21 | exact n23 | ].
    intros x Hx. rewrite R3'. pose proof (Xr x Hx) as Xz. split; apply neq_Z; change (Z_ 2) with 2%Z.
    - rewrite base_Z by (try assumption; lia). nia.
    - rewrite cell_Z by (try assumption; change (Z_ 1) with 1%Z; lia). change (Z_ 1) with 1%Z. nia. }
  assert (S1 : rd b 1 s3 = rd b 1 s) by (unfold s3; rewrite (rd_upd_other b 2 1 _ s2 n21); exact R1').
  assert (S3 : rd b 3 s3 = f) by (unfold s3; rewrite (rd_upd_other b 2 3 _ s2 n23); exact R3').
  assert (SH : rd b 2 s3 = i + 1).
  { unfold s3. apply rd_upd_same; [lia | change (Z_ 2) with 2%Z; lia | ].
    unfold s2, s1. rewrite !size_upd'. change (Z_ 2) with 2%Z. lia. }
  assert (SG : rd b c s3 = g).
  { unfold s3. rewrite (rd_upd_other b 2 c _ s2 (not_eq_sym n2)). unfold s2.
    rewrite (rd_upd_other b (c + 1) c _ s1); [ | apply neq_Z; rewrite C1; lia].
    unfold s1. apply rd_upd_same; [lia | lia | lia]. }
  assert (SC : rd b (c + 1) s3 = rd b 2 s).
  { unfold s3. rewrite (rd_upd_other b 2 (c + 1) _ s2 (not_eq_sym n2')). unfold s2.
    apply rd_upd_same; [lia | rewrite C1; lia | rewrite Sz1; lia]. }
  exists (i :: l). split; [ | rewrite SH; reflexivity].
  destruct B3 as [Nd3 [Mem3 Ch3]].
  split; [ | split].
  - constructor; [intro Hin; exact (Nx i Hin eq_refl) | exact Nd3].
  - intros x [Hx | Hx].
    + subst x. rewrite S1, S3. split; [lia | ]. fold c. rewrite SG. exact Ge.
    + pose proof (Mem3 x Hx) as M3. rewrite S1, S3 in *. exact M3.
  - cbn [fl_chain]. rewrite S3. fold c. split; [ | exact Ch3].
    rewrite SC. exact Hd.
Qed.

(* ---- TAKING.  A never-used slot: the count of slots in use goes up by one and the new slot's generation becomes 1 *)
Lemma ok_new_slot (b : int) (s : mem) : slab_ok b s -> (Z_ (rd b 1 s) < Z_ (rd b 0 s))%Z ->
  slab_ok b (upd b (slab_base (rd b 3 s) (rd b 1 s)) 1 (upd b 1 (rd b 1 s + 1) s)).
Proof.
  intros OK Lt. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (f := rd b 3 s) in *. set (i := rd b 1 s) in *. set (c := slab_base f i).
  assert (I28 : (0 <= Z_ i < 268435456)%Z) by lia.
  assert (Cz : Z_ c = (8 + Z_ i * (Z_ f + 1))%Z) by (apply base_Z; assumption).
  assert (Last : (Z_ i * (Z_ f + 1) + (Z_ f + 1) <= Z_ (rd b 0 s) * (Z_ f + 1))%Z) by nia.
  assert (I1 : Z_ (i + 1) = (Z_ i + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; lia]).
  set (s1 := upd b 1 (i + 1) s).
  assert (n0 : c <> 0) by (apply neq_Z; change (Z_ 0) with 0%Z; lia).
  assert (n1 : c <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
  assert (n2 : c <> 2) by (apply neq_Z; change (Z_ 2) with 2%Z; lia).
  assert (n3 : c <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
  assert (m0 : 1 <> 0) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 1) with 1%Z; lia).
  assert (m2 : 1 <> 2) by (apply neq_Z; change (Z_ 2) with 2%Z; change (Z_ 1) with 1%Z; lia).
  assert (m3 : 1 <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; change (Z_ 1) with 1%Z; lia).
  assert (Sz1 : kq_size b s1 = kq_size b s) by apply size_upd'.
  assert (q0 : rd b 0 s1 = rd b 0 s) by (unfold s1; apply (rd_upd_other b 1 0 _ s m0)).
  assert (q1 : rd b 1 s1 = i + 1) by (unfold s1; apply rd_upd_same; [lia | change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; lia]).
  assert (q2 : rd b 2 s1 = rd b 2 s) by (unfold s1; apply (rd_upd_other b 1 2 _ s m2)).
  assert (q3 : rd b 3 s1 = f) by (unfold s1; apply (rd_upd_other b 1 3 _ s m3)).
  assert (r0 : rd b 0 (upd b c 1 s1) = rd b 0 s) by (rewrite (rd_upd_other b c 0 _ s1 n0); exact q0).
  assert (r1 : rd b 1 (upd b c 1 s1) = i + 1) by (rewrite (rd_upd_other b c 1 _ s1 n1); exact q1).
  assert (r2 : rd b 2 (upd b c 1 s1) = rd b 2 s) by (rewrite (rd_upd_other b c 2 _ s1 n2); exact q2).
  assert (r3 : rd b 3 (upd b c 1 s1) = f) by (rewrite (rd_upd_other b c 3 _ s1 n3); exact q3).
  assert (rs := size_upd' b c 1 b s1).
  refine (Build_slab_ok b _ Hb _ _ _ _ _ _).
  - rewrite r3. exact Hf.
  - rewrite r1, r0. lia.
  - rewrite r0. exact Hcap.
  - rewrite r0, r3, rs, Sz1. exact Hsz.
  - rewrite r2, r1. lia.
  - intros i2 Hi2. rewrite r1 in Hi2. rewrite r3.
    destruct (Z.eq_dec (Z_ i2) (Z_ i)) as [E | N].
    + apply Sint63.to_Z_inj in E. subst i2. fold c. rewrite rd_upd_same; [ | lia | lia | rewrite Sz1; lia].
      unfold gen_ok. change (Z_ 1) with 1%Z. lia.
    + assert (D : c <> slab_base f i2).
      { apply cells_00; [assumption | assumption | lia | lia]. }
      rewrite (rd_upd_other b c _ 1 s1 D). unfold s1.
      assert (D1 : 1 <> slab_base f i2).
      { apply neq_Z. change (Z_ 1) with 1%Z. rewrite base_Z by (try assumption; lia). nia. }
      rewrite (rd_upd_other b 1 _ _ s D1).
      apply Hgen. lia.
Qed.

(* a slab that is full gets room for 2 * cap + 1 slots: the header's capacity cell and the block grow together *)
Lemma ok_grow (b : int) (s : mem) : slab_ok b s ->
  (Z_ (rd b 0 s) <= Z_ (rd b 0 s) * 2 + 1 < 134217728)%Z ->
  (8 + (2 * Z_ (rd b 0 s) + 1) * (Z_ (rd b 3 s) + 1) < 2147483648)%Z ->
  slab_ok b (upd b 0 (2 * rd b 0 s + 1) (kq_grow b (8 + (2 * rd b 0 s + 1) * (rd b 3 s + 1)) s)).
Proof.
  intros OK Hc Hn. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (cap := rd b 0 s) in *. set (f := rd b 3 s) in *.
  assert (N2 : Z_ (2 * cap + 1) = (2 * Z_ cap + 1)%Z).
  { assert (M : Z_ (2 * cap) = (2 * Z_ cap)%Z) by (rewrite mul_Z; [change (Z_ 2) with 2%Z; lia | change (Z_ 2) with 2%Z; lia]).
    rewrite add_Z; [rewrite M; change (Z_ 1) with 1%Z; lia | rewrite M; change (Z_ 1) with 1%Z; lia]. }
  assert (F1 : Z_ (f + 1) = (Z_ f + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; lia]).
  assert (NF : Z_ ((2 * cap + 1) * (f + 1)) = ((2 * Z_ cap + 1) * (Z_ f + 1))%Z)
    by (rewrite mul_Z; [rewrite N2, F1; nia | rewrite N2, F1; nia]).
  assert (NN : Z_ (8 + (2 * cap + 1) * (f + 1)) = (8 + (2 * Z_ cap + 1) * (Z_ f + 1))%Z)
    by (rewrite add_Z; [rewrite NF; change (Z_ 8) with 8%Z; lia | rewrite NF; change (Z_ 8) with 8%Z; nia]).
  set (n := 8 + (2 * cap + 1) * (f + 1)) in *.
  pose proof (size_grow_ge b n s Hb ltac:(nia)) as [Gn1 Gn2].
  set (s1 := kq_grow b n s) in *.
  assert (Pm : (0 <= (2 * Z_ cap + 1) * (Z_ f + 1))%Z) by nia.
  assert (n0 : 0 <> 1) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 1) with 1%Z; lia).
  assert (n2 : 0 <> 2) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 2) with 2%Z; lia).
  assert (n3 : 0 <> 3) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 3) with 3%Z; lia).
  assert (g1 : forall b' j, rd b' j s1 = rd b' j s) by (intros; apply rd_grow').
  refine (Build_slab_ok b _ Hb _ _ _ _ _ _).
  - rewrite (rd_upd_other b 0 3 _ s1 n3), g1. exact Hf.
  - rewrite (rd_upd_other b 0 1 _ s1 n0), g1. rewrite rd_upd_same; [ | lia | change (Z_ 0) with 0%Z; lia | change (Z_ 0) with 0%Z; lia].
    rewrite N2. lia.
  - rewrite rd_upd_same; [ | lia | change (Z_ 0) with 0%Z; lia | change (Z_ 0) with 0%Z; lia]. rewrite N2. lia.
  - rewrite (rd_upd_other b 0 3 _ s1 n3), g1. rewrite rd_upd_same; [ | lia | change (Z_ 0) with 0%Z; lia | change (Z_ 0) with 0%Z; lia].
    rewrite N2, size_upd'. fold f. lia.
  - rewrite (rd_upd_other b 0 2 _ s1 n2), (rd_upd_other b 0 1 _ s1 n0), g1, g1. exact Hfr.
  - intros i Hi. rewrite (rd_upd_other b 0 1 _ s1 n0), g1 in Hi. rewrite (rd_upd_other b 0 3 _ s1 n3), g1.
    assert (Iz : (0 <= Z_ i < 268435456)%Z) by lia.
    assert (D0 : 0 <> slab_base f i).
    { apply neq_Z. rewrite base_Z by (try assumption; lia). change (Z_ 0) with 0%Z. nia. }
    rewrite (rd_upd_other b 0 _ _ s1 D0), g1.
    exact (Hgen i Hi).
Qed.

(* and the capacity cell then holds 2 * cap + 1 *)
Lemma rd0_grow (b : int) (s : mem) : slab_ok b s ->
  (8 + (2 * Z_ (rd b 0 s) + 1) * (Z_ (rd b 3 s) + 1) < 2147483648)%Z ->
  rd b 0 (upd b 0 (2 * rd b 0 s + 1) (kq_grow b (8 + (2 * rd b 0 s + 1) * (rd b 3 s + 1)) s)) = 2 * rd b 0 s + 1.
Proof.
  intros OK Hn. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  set (cap := rd b 0 s) in *. set (f := rd b 3 s) in *.
  assert (N2 : Z_ (2 * cap + 1) = (2 * Z_ cap + 1)%Z).
  { assert (M : Z_ (2 * cap) = (2 * Z_ cap)%Z) by (rewrite mul_Z; [change (Z_ 2) with 2%Z; lia | change (Z_ 2) with 2%Z; lia]).
    rewrite add_Z; [rewrite M; change (Z_ 1) with 1%Z; lia | rewrite M; change (Z_ 1) with 1%Z; lia]. }
  assert (F1 : Z_ (f + 1) = (Z_ f + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; lia]).
  assert (NF : Z_ ((2 * cap + 1) * (f + 1)) = ((2 * Z_ cap + 1) * (Z_ f + 1))%Z)
    by (rewrite mul_Z; [rewrite N2, F1; nia | rewrite N2, F1; nia]).
  assert (NN : Z_ (8 + (2 * cap + 1) * (f + 1)) = (8 + (2 * Z_ cap + 1) * (Z_ f + 1))%Z)
    by (rewrite add_Z; [rewrite NF; change (Z_ 8) with 8%Z; lia | rewrite NF; change (Z_ 8) with 8%Z; nia]).
  set (n := 8 + (2 * cap + 1) * (f + 1)) in *.
  pose proof (size_grow_ge b n s Hb ltac:(nia)) as [Gn1 Gn2].
  assert (Pm : (0 <= (2 * Z_ cap + 1) * (Z_ f + 1))%Z) by nia.
  apply rd_upd_same; [lia | change (Z_ 0) with 0%Z; lia | change (Z_ 0) with 0%Z; lia].
Qed.

(* ---- taking a slot off the free list zeroes its fields: each write is to a cell of that slot's fields *)
Lemma zero_pres (b c f : int) (Q : mem -> Prop) : (Z_ f <= 1024)%Z ->
  (forall k s, (0 <= Z_ k < Z_ f)%Z -> Q s -> Q (upd b (c + 1 + k) 0 s)) ->
  forall fuel k n s, (0 <= Z_ k)%Z -> (Z_ n <= Z_ f)%Z -> Q s -> Q (slab_zero fuel b c k n s).
Proof.
  intros F St. induction fuel as [|fuel IH]; intros k n s K N Hq; cbn [slab_zero]; [exact Hq | ].
  destruct (n <=? k) eqn:E; [exact Hq | ]. apply le_Z_false in E.
  apply IH; [ | exact N | apply St; [lia | exact Hq]].
  rewrite add_Z; change (Z_ 1) with 1%Z; lia.
Qed.

(* the property the zeroing keeps: the invariant without the list's head slot x, and the cells it does not write *)
Definition zq (b c : int) (r : list int) (u hd f cap g : int) (s : mem) : Prop :=
  slab_ok b s /\ fl_body b s r /\ rd b 1 s = u /\ rd b 2 s = hd /\ rd b 3 s = f /\ rd b 0 s = cap /\ rd b c s = g.

Lemma zq_step (b x : int) (r : list int) (u hd f cap g : int) (s : mem) (k : int) :
  (1 <= Z_ f <= 1024)%Z -> (0 <= Z_ x < Z_ u)%Z -> (Z_ u <= Z_ cap)%Z -> (Z_ cap < 134217728)%Z ->
  (forall y, In y r -> Z_ x <> Z_ y /\ (0 <= Z_ y < 268435456)%Z) ->
  (0 <= Z_ k < Z_ f)%Z ->
  zq b (slab_base f x) r u hd f cap g s -> zq b (slab_base f x) r u hd f cap g (upd b (slab_base f x + 1 + k) 0 s).
Proof.
  intros Hf Hx Hu Hc Hr Hk (OK & Bd & R1 & R2 & R3 & R0 & RC).
  set (c := slab_base f x) in *.
  assert (Xz : (0 <= Z_ x < 268435456)%Z) by lia.
  assert (Cz : Z_ c = (8 + Z_ x * (Z_ f + 1))%Z) by (apply base_Z; assumption).
  assert (PB : (Z_ x * (Z_ f + 1) <= 268435456 * 1025)%Z) by nia.
  assert (C1 : Z_ (c + 1) = (Z_ c + 1)%Z) by (rewrite add_Z; [change (Z_ 1) with 1%Z; lia | change (Z_ 1) with 1%Z; rewrite Cz; lia]).
  assert (CK : Z_ (c + 1 + k) = (Z_ c + 1 + Z_ k)%Z) by (rewrite add_Z; [rewrite C1; lia | rewrite C1; rewrite Cz; lia]).
  assert (J0 : c + 1 + k <> 0) by (apply neq_Z; rewrite CK; change (Z_ 0) with 0%Z; rewrite Cz; nia).
  assert (J1 : c + 1 + k <> 1) by (apply neq_Z; rewrite CK; change (Z_ 1) with 1%Z; rewrite Cz; nia).
  assert (J2 : c + 1 + k <> 2) by (apply neq_Z; rewrite CK; change (Z_ 2) with 2%Z; rewrite Cz; nia).
  assert (J3 : c + 1 + k <> 3) by (apply neq_Z; rewrite CK; change (Z_ 3) with 3%Z; rewrite Cz; nia).
  assert (JC : c + 1 + k <> c) by (apply neq_Z; rewrite CK; lia).
  unfold zq. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - apply ok_upd_plain; [exact OK | rewrite CK; rewrite Cz; nia | ].
    intros i2 Hi2. rewrite R3. rewrite R1 in Hi2. apply neq_Z. rewrite CK. rewrite base_Z by (try assumption; lia).
    pose proof (cell_ne (Z_ f) (Z_ x) (Z_ i2) (1 + Z_ k) 0 Hf ltac:(right; lia) ltac:(lia) ltac:(lia)) as X.
    rewrite Cz in *. lia.
  - apply fl_body_upd; [exact Bd | exact J1 | exact J3 | ].
    intros y Hy. rewrite R3. destruct (Hr y Hy) as [Ne Yz]. split; apply neq_Z; rewrite CK, Cz.
    + rewrite base_Z by (try assumption; lia).
      pose proof (cell_ne (Z_ f) (Z_ x) (Z_ y) (1 + Z_ k) 0 Hf ltac:(left; lia) ltac:(lia) ltac:(lia)) as X. lia.
    + rewrite cell_Z by (try assumption; change (Z_ 1) with 1%Z; lia). change (Z_ 1) with 1%Z.
      pose proof (cell_ne (Z_ f) (Z_ x) (Z_ y) (1 + Z_ k) 1 Hf ltac:(left; lia) ltac:(lia) ltac:(lia)) as X. lia.
  - rewrite (rd_upd_other b _ 1 0 s J1). exact R1.
  - rewrite (rd_upd_other b _ 2 0 s J2). exact R2.
  - rewrite (rd_upd_other b _ 3 0 s J3). exact R3.
  - rewrite (rd_upd_other b _ 0 0 s J0). exact R0.
  - rewrite (rd_upd_other b _ c 0 s JC). exact RC.
Qed.

Lemma plus1_minus1 (x : int) : (0 <= Z_ x < 268435456)%Z -> x + 1 - 1 = x.
Proof.
  intro X. apply Sint63.to_Z_inj. rewrite sub_Z; rewrite add_Z; change (Z_ 1) with 1%Z; lia.
Qed.

(* the head of a free list stands for a number from 0 to the count of slots in use *)
Lemma fl_next_range (b : int) (s : mem) (r : list int) : fl_body b s r -> (0 <= Z_ (rd b 1 s) < 268435456)%Z ->
  (0 <= Z_ (fl_next r) <= Z_ (rd b 1 s))%Z.
Proof.
  intros [Nd [Mem Ch]] U. destruct r as [ | y r'].
  - cbn [fl_next]. change (Z_ 0) with 0%Z. lia.
  - cbn [fl_next]. pose proof (proj1 (Mem y (or_introl eq_refl))) as Y.
    rewrite add_Z; change (Z_ 1) with 1%Z; lia.
Qed.

(* slab_take keeps the whole invariant (the room conditions are those of slab_take_live, and a doubled capacity must stay
   below 2^27 slots) *)
Theorem slab_take_inv (b : int) (s : mem) : slab_inv b s ->
  (Z_ (rd b 0 s) * 2 + 1 < 134217728)%Z ->
  (8 + (2 * Z_ (rd b 0 s) + 1) * (Z_ (rd b 3 s) + 1) < 2147483648)%Z ->
  slab_inv b (slab_take b s).
Proof.
  intros [OK [l [Bd Hd]]] Hc2 Hroom.
  pose proof OK as OK0. destruct OK as [Hb Hf Hus Hcap Hsz Hfr Hgen].
  unfold slab_take. cbv zeta.
  destruct l as [ | x r].
  - (* no free slot: a never-used one *)
    cbn [fl_next] in Hd. rewrite Hd. replace (0 <? 0) with false by reflexivity. cbv iota.
    assert (Bnil : fl_body b s nil) by exact Bd.
    destruct (rd b 1 s <? rd b 0 s) eqn:Lt.
    + apply lt_Z in Lt.
      split; [exact (ok_new_slot b s OK0 Lt) | exists nil; split].
      * split; [constructor | split; [intros y Hy; destruct Hy | exact I]].
      * set (c := slab_base (rd b 3 s) (rd b 1 s)).
        assert (n2 : c <> 2).
        { apply neq_Z. unfold c. rewrite base_Z by (try assumption; lia). change (Z_ 2) with 2%Z. nia. }
        assert (m2 : 1 <> 2) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 2) with 2%Z; lia).
        rewrite (rd_upd_other b c 2 _ _ n2), (rd_upd_other b 1 2 _ _ m2). exact Hd.
    + destruct (rd b 4 s =? 1) eqn:Gw.
      * apply lt_Z_false in Lt.
        assert (Rc : Z_ (rd b 1 s) = Z_ (rd b 0 s)) by lia.
        set (cap := rd b 0 s) in *. set (f := rd b 3 s) in *. set (i := rd b 1 s) in *.
        assert (Hg : (Z_ cap <= Z_ cap * 2 + 1 < 134217728)%Z) by lia.
        pose proof (ok_grow b s OK0 Hg Hroom) as G.
        set (s2 := upd b 0 (2 * cap + 1) (kq_grow b (8 + (2 * cap + 1) * (f + 1)) s)) in *.
        assert (N2 : Z_ (2 * cap + 1) = (2 * Z_ cap + 1)%Z).
        { assert (M : Z_ (2 * cap) = (2 * Z_ cap)%Z) by (rewrite mul_Z; [change (Z_ 2) with 2%Z; lia | change (Z_ 2) with 2%Z; lia]).
          rewrite add_Z; [rewrite M; change (Z_ 1) with 1%Z; lia | rewrite M; change (Z_ 1) with 1%Z; lia]. }
        assert (n0 : 0 <> 1) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 1) with 1%Z; lia).
        assert (n01 : 0 <> 3) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 3) with 3%Z; lia).
        assert (n02 : 0 <> 2) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 2) with 2%Z; lia).
        assert (g1 : forall b' j, rd b' j (kq_grow b (8 + (2 * cap + 1) * (f + 1)) s) = rd b' j s) by (intros; apply rd_grow').
        assert (E1 : rd b 1 s2 = i) by (unfold s2; rewrite (rd_upd_other b 0 1 _ _ n0), g1; reflexivity).
        assert (E3 : rd b 3 s2 = f) by (unfold s2; rewrite (rd_upd_other b 0 3 _ _ n01), g1; reflexivity).
        assert (E2 : rd b 2 s2 = rd b 2 s) by (unfold s2; rewrite (rd_upd_other b 0 2 _ _ n02), g1; reflexivity).
        assert (E0 : rd b 0 s2 = 2 * cap + 1).
        { exact (rd0_grow b s OK0 Hroom). }
        assert (Lt2 : (Z_ (rd b 1 s2) < Z_ (rd b 0 s2))%Z) by (rewrite E1, E0, N2; lia).
        pose proof (ok_new_slot b s2 G Lt2) as NS. rewrite E1, E3 in NS.
        split; [exact NS | exists nil; split; [split; [constructor | split; [intros y Hy; destruct Hy | exact I]] | ]].
        cbn [fl_next].
        set (c := slab_base f i).
        assert (n2 : c <> 2).
        { apply neq_Z. unfold c. rewrite base_Z by (try assumption; lia). change (Z_ 2) with 2%Z. nia. }
        assert (m2 : 1 <> 2) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 2) with 2%Z; lia).
        rewrite (rd_upd_other b c 2 _ _ n2), (rd_upd_other b 1 2 _ _ m2). rewrite E2. exact Hd.
      * split; [exact OK0 | exists nil; split; [exact Bnil | exact Hd]].
  - (* the first slot of the free list is taken *)
    cbn [fl_next] in Hd.
    pose proof Bd as Bd0. destruct Bd0 as [Nd [Mem Ch]].
    pose proof (Mem x (or_introl eq_refl)) as [Hx Hxe].
    cbn [fl_chain] in Ch. destruct Ch as [Chx Chr].
    assert (Nx : ~ In x r) by (inversion Nd; assumption).
    assert (Ndr : NoDup r) by (inversion Nd; assumption).
    assert (Bdr : fl_body b s r).
    { split; [exact Ndr | split; [intros y Hy; apply Mem; right; exact Hy | exact Chr]]. }
    set (f := rd b 3 s) in *. set (u := rd b 1 s) in *. set (cap := rd b 0 s) in *.
    assert (Xz : (0 <= Z_ x < 268435456)%Z) by lia.
    assert (X1 : Z_ (x + 1) = (Z_ x + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
    rewrite Hd.
    assert (Pos : (0 <? x + 1) = true) by (apply lt_Z; rewrite X1; change (Z_ 0) with 0%Z; lia).
    rewrite Pos. cbv iota. rewrite (plus1_minus1 x Xz). rewrite Chx.
    set (c := slab_base f x).
    set (g := slab_next_gen (rd b c s)).
    set (hd := fl_next r).
    assert (Gg : gen_ok g) by (apply next_gen_ok, (Hgen x Hx)).
    assert (NR : (0 <= Z_ hd <= Z_ u)%Z) by (apply (fl_next_range b s r Bdr); fold u; lia).
    pose proof (ok_upd_head b hd s OK0 NR) as S1.
    set (s1 := upd b 2 hd s) in *.
    assert (n21 : 2 <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 2) with 2%Z; lia).
    assert (n23 : 2 <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; change (Z_ 2) with 2%Z; lia).
    assert (n20 : 2 <> 0) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 2) with 2%Z; lia).
    assert (R1 : rd b 1 s1 = u) by (unfold s1; apply (rd_upd_other b 2 1 _ s n21)).
    assert (R3 : rd b 3 s1 = f) by (unfold s1; apply (rd_upd_other b 2 3 _ s n23)).
    assert (R0 : rd b 0 s1 = cap) by (unfold s1; apply (rd_upd_other b 2 0 _ s n20)).
    assert (R2 : rd b 2 s1 = hd) by (unfold s1; apply rd_upd_same; [lia | change (Z_ 2) with 2%Z; lia | change (Z_ 2) with 2%Z; nia]).
    assert (Sz1 : kq_size b s1 = kq_size b s) by apply size_upd'.
    pose proof (ok_upd_gen b x g s1 S1 ltac:(rewrite R1; exact Hx) Gg) as S2. rewrite R3 in S2. fold c in S2.
    assert (Cz : Z_ c = (8 + Z_ x * (Z_ f + 1))%Z) by (apply base_Z; assumption).
    assert (Last : (Z_ x * (Z_ f + 1) + (Z_ f + 1) <= Z_ cap * (Z_ f + 1))%Z) by nia.
    assert (n1 : c <> 1) by (apply neq_Z; change (Z_ 1) with 1%Z; lia).
    assert (n3 : c <> 3) by (apply neq_Z; change (Z_ 3) with 3%Z; lia).
    assert (n0 : c <> 0) by (apply neq_Z; change (Z_ 0) with 0%Z; lia).
    assert (n2 : c <> 2) by (apply neq_Z; change (Z_ 2) with 2%Z; lia).
    assert (Hr : forall y, In y r -> Z_ x <> Z_ y /\ (0 <= Z_ y < 268435456)%Z).
    { intros y Hy. split.
      - intro E. apply Nx. apply Sint63.to_Z_inj in E. subst y. exact Hy.
      - pose proof (proj1 (Mem y (or_intror Hy))). lia. }
    assert (B1 : fl_body b s1 r).
    { apply fl_body_upd; [exact Bdr | exact n21 | exact n23 | ].
      intros y Hy. destruct (Hr y Hy) as [_ Yz]. split; apply neq_Z; change (Z_ 2) with 2%Z.
      - rewrite base_Z by (try exact Hf; try exact Yz; lia). fold f. nia.
      - rewrite cell_Z by (try exact Hf; try exact Yz; change (Z_ 1) with 1%Z; lia). change (Z_ 1) with 1%Z. fold f. nia. }
    assert (B2 : fl_body b (upd b c g s1) r).
    { apply fl_body_upd; [exact B1 | exact n1 | exact n3 | ].
      intros y Hy. rewrite R3. destruct (Hr y Hy) as [Ne Yz]. split; [apply cells_00 | apply cells_01]; try assumption; lia. }
    assert (Z0 : zq b c r u hd f cap g (upd b c g s1)).
    { unfold zq. refine (conj S2 (conj B2 (conj _ (conj _ (conj _ (conj _ _)))))).
      - rewrite (rd_upd_other b c 1 _ s1 n1). exact R1.
      - rewrite (rd_upd_other b c 2 _ s1 n2). exact R2.
      - rewrite (rd_upd_other b c 3 _ s1 n3). exact R3.
      - rewrite (rd_upd_other b c 0 _ s1 n0). exact R0.
      - apply rd_upd_same; [lia | lia | rewrite Sz1; lia]. }
    pose proof (zero_pres b c f (zq b c r u hd f cap g) ltac:(lia)
                  (fun k s' Hk Hq => zq_step b x r u hd f cap g s' k Hf ltac:(lia) ltac:(lia) ltac:(lia) Hr Hk Hq)
                  (kq_nat f) 0 f (upd b c g s1) ltac:(change (Z_ 0) with 0%Z; lia) ltac:(lia) Z0) as ZF.
    destruct ZF as (OKz & Bz & _ & H2 & _).
    split; [exact OKz | exists r; split; [exact Bz | exact H2]].
Qed.

(* a freshly made slab is a slab: the header cells hold what slab_init wrote, the block has room, nothing is in use *)
Theorem slab_init_inv (b f cap grow : int) (s : mem) :
  (0 <= Z_ b < 64)%Z -> (1 <= Z_ f <= 1024)%Z -> (0 <= Z_ cap < 134217728)%Z -> (8 + Z_ cap * (Z_ f + 1) < 2147483648)%Z ->
  slab_inv b (slab_init b f cap grow s).
Proof.
  intros Hb Hf Hc Hn. unfold slab_init. cbv zeta.
  assert (C1 : Z_ (cap * (f + 1)) = (Z_ cap * (Z_ f + 1))%Z).
  { assert (F1 : Z_ (f + 1) = (Z_ f + 1)%Z) by (rewrite add_Z; change (Z_ 1) with 1%Z; lia).
    rewrite mul_Z; rewrite F1; nia. }
  assert (N8 : Z_ (8 + cap * (f + 1)) = (8 + Z_ cap * (Z_ f + 1))%Z)
    by (rewrite add_Z; rewrite C1; change (Z_ 8) with 8%Z; nia).
  pose proof (size_grow_ge b (8 + cap * (f + 1)) s Hb ltac:(rewrite N8; nia)) as [Gn _].
  rewrite N8 in Gn.
  set (s0 := kq_grow b (8 + cap * (f + 1)) s) in *.
  assert (Pm : (0 <= Z_ cap * (Z_ f + 1))%Z) by nia.
  assert (d01 : 0 <> 1) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 1) with 1%Z; lia).
  assert (d02 : 0 <> 2) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 2) with 2%Z; lia).
  assert (d03 : 0 <> 3) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 3) with 3%Z; lia).
  assert (d04 : 0 <> 4) by (apply neq_Z; change (Z_ 0) with 0%Z; change (Z_ 4) with 4%Z; lia).
  assert (d12 : 1 <> 2) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 2) with 2%Z; lia).
  assert (d13 : 1 <> 3) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 3) with 3%Z; lia).
  assert (d14 : 1 <> 4) by (apply neq_Z; change (Z_ 1) with 1%Z; change (Z_ 4) with 4%Z; lia).
  assert (d23 : 2 <> 3) by (apply neq_Z; change (Z_ 2) with 2%Z; change (Z_ 3) with 3%Z; lia).
  assert (d24 : 2 <> 4) by (apply neq_Z; change (Z_ 2) with 2%Z; change (Z_ 4) with 4%Z; lia).
  assert (d34 : 3 <> 4) by (apply neq_Z; change (Z_ 3) with 3%Z; change (Z_ 4) with 4%Z; lia).
  set (s1 := upd b 0 cap s0). set (s2 := upd b 1 0 s1). set (s3 := upd b 2 0 s2).
  set (s4 := upd b 3 f s3). set (s5 := upd b 4 grow s4).
  assert (Sz : kq_size b s5 = kq_size b s0) by (unfold s5, s4, s3, s2, s1; rewrite !size_upd'; reflexivity).
  assert (Q0 : rd b 0 s5 = cap).
  { unfold s5, s4, s3, s2. rewrite (rd_upd_other b 4 0 _ _ (not_eq_sym d04)), (rd_upd_other b 3 0 _ _ (not_eq_sym d03)),
      (rd_upd_other b 2 0 _ _ (not_eq_sym d02)), (rd_upd_other b 1 0 _ _ (not_eq_sym d01)).
    unfold s1. apply rd_upd_same; [lia | change (Z_ 0) with 0%Z; lia | change (Z_ 0) with 0%Z; lia]. }
  assert (Q1 : rd b 1 s5 = 0).
  { unfold s5, s4, s3. rewrite (rd_upd_other b 4 1 _ _ (not_eq_sym d14)), (rd_upd_other b 3 1 _ _ (not_eq_sym d13)),
      (rd_upd_other b 2 1 _ _ (not_eq_sym d12)).
    unfold s2. apply rd_upd_same; [lia | change (Z_ 1) with 1%Z; lia | unfold s1; rewrite size_upd'; change (Z_ 1) with 1%Z; lia]. }
  assert (Q2 : rd b 2 s5 = 0).
  { unfold s5, s4. rewrite (rd_upd_other b 4 2 _ _ (not_eq_sym d24)), (rd_upd_other b 3 2 _ _ (not_eq_sym d23)).
    unfold s3. apply rd_upd_same; [lia | change (Z_ 2) with 2%Z; lia | unfold s2, s1; rewrite !size_upd'; change (Z_ 2) with 2%Z; lia]. }
  assert (Q3 : rd b 3 s5 = f).
  { unfold s5. rewrite (rd_upd_other b 4 3 _ _ (not_eq_sym d34)).
    unfold s4. apply rd_upd_same; [lia | change (Z_ 3) with 3%Z; lia | unfold s3, s2, s1; rewrite !size_upd'; change (Z_ 3) with 3%Z; lia]. }
  split.
  - refine (Build_slab_ok b _ Hb _ _ _ _ _ _).
    + rewrite Q3. exact Hf.
    + rewrite Q1, Q0. change (Z_ 0) with 0%Z. lia.
    + rewrite Q0. lia.
    + rewrite Q0, Q3, Sz. lia.
    + rewrite Q2, Q1. change (Z_ 0) with 0%Z. lia.
    + intros i Hi. rewrite Q1 in Hi. change (Z_ 0) with 0%Z in Hi. lia.
  - exists nil. split; [ | rewrite Q2; reflexivity].
    split; [constructor | split; [intros y Hy; destruct Hy | exact I]].
Qed.
