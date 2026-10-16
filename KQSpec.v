(* KQSpec.v -- WHAT A PROOF MAY ASSUME about the memory and the machine: the laws of the operations KQRun.v declares.

   The memory's laws are its definition: a cell holds what was last written to it; a read outside a block gives 0, a
   write outside does nothing; the wide and the narrow blocks are apart.  The machine's laws are the HARDWARE'S
   PROMISES, kept small, and nothing about WHICH number a device gives back:
     - a load of w bytes gives back SOME number in 0 .. 2^(8w) - 1, into the cell it was told, and changes no other cell;
     - a store, an atomic, a copy, a fill change no cell of a wide block (hw/kq_hw.h refuses those addresses), and no
       cell of a narrow block either, when their bytes fall outside every narrow block (`clear`);
     - what the devices see -- every load, store and fence -- is recorded, in order (`Trace`).
   A proof about a program must hold for EVERY number a device could give back: the hardware is trusted, the logic is
   proved.  A call through a pointer (hw_call) promises nothing at all: the code called could do anything.

   All the laws are ONE axiom, `real_laws`, about one record of the operations (`real`).  KQModel.v defines every
   operation in Rocq and proves every law (`laws_satisfiable`), so they cannot contradict each other.  A proof imports
   this file; the program itself does not. *)
From Stdlib Require Import ZArith List Lia Sint63.
Require Import KQ.KQRun KQ.KQBound.
Import ListNotations.
Open Scope sint63_scope.
Open Scope bool_scope.

(* what the devices have seen, in order *)
Inductive hw_ev :=
| EvLoad  (w a lo hi : int)      (* a load of w bytes at a, and what came back (hi: the high half of 8 bytes; else 0) *)
| EvStore (w a lo hi : int)      (* a store of w bytes at a: the low 8w bits of lo (8 bytes: lo, then hi) *)
| EvFence (k : int).
Axiom hw_trace : mem -> list hw_ev.

(* the operations, as one value: their laws are stated once (`laws`) and shown satisfiable (KQModel.v) *)
Record ops := mkOps {
  M : Type;
  Rd : int -> int -> M -> int;  Upd : int -> int -> int -> M -> M;  Len : int -> int;
  Size : int -> M -> int;  Grow : int -> int -> M -> M;
  Rd32 : int -> int -> M -> int;  Upd32 : int -> int -> int -> M -> M;  Len32 : int -> int;
  Load : int -> int -> int -> int -> M -> M;
  Store : int -> int -> int -> M -> M;  Store64 : int -> int -> int -> M -> M;
  Atomic : int -> int -> int -> int -> int -> int -> M -> M;
  Atomic64 : int -> int -> int -> int -> int -> int -> M -> M;
  Cas : int -> int -> int -> int -> int -> int -> M -> M;
  Cas64 : int -> int -> int -> int -> int -> int -> int -> M -> M;
  ALoad : int -> int -> int -> int -> M -> M;
  AStore : int -> int -> int -> M -> M;  AStore64 : int -> int -> int -> M -> M;
  Fence : int -> M -> M;
  Copy : int -> int -> int -> M -> M;  Fill : int -> int -> int -> M -> M;
  Cmp : int -> int -> int -> int -> int -> M -> M;
  Call : int -> int -> int -> int -> M -> M;
  Addr : int -> int;
  Trace : M -> list hw_ev }.

(* a 32-bit number as a narrow cell keeps it: modulo 2^32, read back signed *)
Definition sx32 (v : int) : int := let u := v land 4294967295 in if u <? 2147483648 then u else u - 4294967296.
(* the bound of a load of w bytes; the widths a load or a store of one number takes *)
Definition lim (w : int) : int := if w =? 1 then 256 else if w =? 2 then 65536 else 4294967296.
Definition byte_w (w : int) : bool := (w =? 1) || (w =? 2) || (w =? 4).
Definition in_lim (w x : int) : bool := (0 <=? x) && (x <? lim w).
Definition other (h i h' i' : int) : bool := negb ((h =? h') && (i =? i')).

Section Laws.
Variable m : ops.
(* cell i of block h exists in the memory s: inside the block's size there (a block can grow, KQRun.v kq_grow) *)
Definition cell (h i : int) (s : M m) : bool := (0 <=? h) && (0 <=? i) && (i <? Size m h s).
(* the blocks and sizes kq_grow accepts *)
Definition growable (h n : int) : bool := (0 <=? h) && (h <? 64) && (0 <=? n) && (n <? 2147483648).
Definition nonneg2 (h i : int) : bool := (0 <=? h) && (0 <=? i).
(* the bytes a .. a + n - 1 fall outside every narrow block *)
Definition clear (a n : int) : Prop :=
  forall h, (0 <=? h) = true -> ((a + n <=? Addr m h) || (Addr m h + 4 * Len32 m h <=? a)) = true.

Record laws : Prop := {
  (* ---- THE MEMORY *)
  len_nonneg   : forall h, (0 <=? Len m h) = true;
  len32_nonneg : forall h, (0 <=? Len32 m h) = true;
  rd_out    : forall h i s, nonneg2 h i = true -> (Size m h s <=? i) = true -> Rd m h i s = 0;
  upd_out   : forall h i v s, nonneg2 h i = true -> (Size m h s <=? i) = true -> Upd m h i v s = s;
  (* a negative block or cell number is outside: a read gives 0, a write does nothing *)
  rd_neg    : forall h i s, nonneg2 h i = false -> Rd m h i s = 0;
  upd_neg   : forall h i v s, nonneg2 h i = false -> Upd m h i v s = s;
  rd_upd_eq : forall h i v s, cell h i s = true -> Rd m h i (Upd m h i v s) = v;
  rd_upd_ne : forall h i h' i' v s, other h i h' i' = true -> Rd m h' i' (Upd m h i v s) = Rd m h' i' s;
  rd32_out    : forall h i s, nonneg2 h i = true -> (Len32 m h <=? i) = true -> Rd32 m h i s = 0;
  upd32_out   : forall h i v s, nonneg2 h i = true -> (Len32 m h <=? i) = true -> Upd32 m h i v s = s;
  rd32_neg    : forall h i s, nonneg2 h i = false -> Rd32 m h i s = 0;
  upd32_neg   : forall h i v s, nonneg2 h i = false -> Upd32 m h i v s = s;
  rd32_upd32_eq : forall h i v s, nonneg2 h i && (i <? Len32 m h) = true -> Rd32 m h i (Upd32 m h i v s) = sx32 v;
  rd32_upd32_ne : forall h i h' i' v s, other h i h' i' = true -> Rd32 m h' i' (Upd32 m h i v s) = Rd32 m h' i' s;
  rd32_upd : forall h i v h' i' s, Rd32 m h' i' (Upd m h i v s) = Rd32 m h' i' s;
  rd_upd32 : forall h i v h' i' s, Rd m h' i' (Upd32 m h i v s) = Rd m h' i' s;
  trace_upd   : forall h i v s, Trace m (Upd m h i v s) = Trace m s;
  trace_upd32 : forall h i v s, Trace m (Upd32 m h i v s) = Trace m s;
  (* ---- LOADS: some number of the right size, into the cell asked for; nothing else changes *)
  load_lim  : forall w a h i s, byte_w w = true -> cell h i s = true -> in_lim w (Rd m h i (Load m w a h i s)) = true;
  load8_lim : forall a h i s, cell h i s = true -> cell h (i + 1) s = true ->
                in_lim 4 (Rd m h i (Load m 8 a h i s)) && in_lim 4 (Rd m h (i + 1) (Load m 8 a h i s)) = true;
  load_rd   : forall w a h i h' i' s, other h i h' i' = true -> (negb (w =? 8) || other h (i + 1) h' i') = true ->
                Rd m h' i' (Load m w a h i s) = Rd m h' i' s;
  load_rd32 : forall w a h i h' i' s, Rd32 m h' i' (Load m w a h i s) = Rd32 m h' i' s;
  load_trace : forall w a h i s, Trace m (Load m w a h i s) =
                 Trace m s ++ [EvLoad w a (Rd m h i (Load m w a h i s)) (if w =? 8 then Rd m h (i + 1) (Load m w a h i s) else 0)];
  aload_lim  : forall w a h i s, byte_w w = true -> cell h i s = true -> in_lim w (Rd m h i (ALoad m w a h i s)) = true;
  aload8_lim : forall a h i s, cell h i s = true -> cell h (i + 1) s = true ->
                 in_lim 4 (Rd m h i (ALoad m 8 a h i s)) && in_lim 4 (Rd m h (i + 1) (ALoad m 8 a h i s)) = true;
  aload_rd   : forall w a h i h' i' s, other h i h' i' = true -> (negb (w =? 8) || other h (i + 1) h' i') = true ->
                 Rd m h' i' (ALoad m w a h i s) = Rd m h' i' s;
  aload_rd32 : forall w a h i h' i' s, Rd32 m h' i' (ALoad m w a h i s) = Rd32 m h' i' s;
  (* ---- STORES: no wide cell changes; no narrow cell, when the bytes are clear of the narrow blocks *)
  store_rd    : forall w a v h i s, Rd m h i (Store m w a v s) = Rd m h i s;
  store_rd32  : forall w a v h i s, clear a w -> Rd32 m h i (Store m w a v s) = Rd32 m h i s;
  store_trace : forall w a v s, Trace m (Store m w a v s) = Trace m s ++ [EvStore w a v 0];
  store64_rd    : forall a lo hi h i s, Rd m h i (Store64 m a lo hi s) = Rd m h i s;
  store64_rd32  : forall a lo hi h i s, clear a 8 -> Rd32 m h i (Store64 m a lo hi s) = Rd32 m h i s;
  store64_trace : forall a lo hi s, Trace m (Store64 m a lo hi s) = Trace m s ++ [EvStore 8 a lo hi];
  astore_rd     : forall w a v h i s, Rd m h i (AStore m w a v s) = Rd m h i s;
  astore_rd32   : forall w a v h i s, clear a w -> Rd32 m h i (AStore m w a v s) = Rd32 m h i s;
  astore64_rd   : forall a lo hi h i s, Rd m h i (AStore64 m a lo hi s) = Rd m h i s;
  astore64_rd32 : forall a lo hi h i s, clear a 8 -> Rd32 m h i (AStore64 m a lo hi s) = Rd32 m h i s;
  (* ---- ATOMICS: the old value, of the right size, into the cell asked for *)
  atomic_lim  : forall op w a v h i s, byte_w w = true -> cell h i s = true -> in_lim w (Rd m h i (Atomic m op w a v h i s)) = true;
  atomic_rd   : forall op w a v h i h' i' s, other h i h' i' = true -> Rd m h' i' (Atomic m op w a v h i s) = Rd m h' i' s;
  atomic_rd32 : forall op w a v h i h' i' s, clear a w -> Rd32 m h' i' (Atomic m op w a v h i s) = Rd32 m h' i' s;
  atomic64_lim  : forall op a lo hi h i s, cell h i s = true -> cell h (i + 1) s = true ->
                    in_lim 4 (Rd m h i (Atomic64 m op a lo hi h i s)) && in_lim 4 (Rd m h (i + 1) (Atomic64 m op a lo hi h i s)) = true;
  atomic64_rd   : forall op a lo hi h i h' i' s, other h i h' i' = true -> other h (i + 1) h' i' = true ->
                    Rd m h' i' (Atomic64 m op a lo hi h i s) = Rd m h' i' s;
  atomic64_rd32 : forall op a lo hi h i h' i' s, clear a 8 -> Rd32 m h' i' (Atomic64 m op a lo hi h i s) = Rd32 m h' i' s;
  cas_lim   : forall w a o n h i s, byte_w w = true -> cell h i s = true -> in_lim w (Rd m h i (Cas m w a o n h i s)) = true;
  cas_flag  : forall w a o n h i s, cell h (i + 1) s = true ->
                let r := Rd m h (i + 1) (Cas m w a o n h i s) in (r =? 0) || (r =? 1) = true;
  cas_rd    : forall w a o n h i h' i' s, other h i h' i' = true -> other h (i + 1) h' i' = true ->
                Rd m h' i' (Cas m w a o n h i s) = Rd m h' i' s;
  cas_rd32  : forall w a o n h i h' i' s, clear a w -> Rd32 m h' i' (Cas m w a o n h i s) = Rd32 m h' i' s;
  cas64_flag : forall a ol oh nl nh h i s, cell h (i + 2) s = true ->
                 let r := Rd m h (i + 2) (Cas64 m a ol oh nl nh h i s) in (r =? 0) || (r =? 1) = true;
  cas64_rd   : forall a ol oh nl nh h i h' i' s, other h i h' i' = true -> other h (i + 1) h' i' = true -> other h (i + 2) h' i' = true ->
                 Rd m h' i' (Cas64 m a ol oh nl nh h i s) = Rd m h' i' s;
  cas64_rd32 : forall a ol oh nl nh h i h' i' s, clear a 8 -> Rd32 m h' i' (Cas64 m a ol oh nl nh h i s) = Rd32 m h' i' s;
  (* ---- FENCES, BYTES IN BULK *)
  fence_rd    : forall k h i s, Rd m h i (Fence m k s) = Rd m h i s;
  fence_rd32  : forall k h i s, Rd32 m h i (Fence m k s) = Rd32 m h i s;
  fence_trace : forall k s, Trace m (Fence m k s) = Trace m s ++ [EvFence k];
  copy_rd   : forall d x n h i s, Rd m h i (Copy m d x n s) = Rd m h i s;
  copy_rd32 : forall d x n h i s, clear d n -> Rd32 m h i (Copy m d x n s) = Rd32 m h i s;
  fill_rd   : forall d b n h i s, Rd m h i (Fill m d b n s) = Rd m h i s;
  fill_rd32 : forall d b n h i s, clear d n -> Rd32 m h i (Fill m d b n s) = Rd32 m h i s;
  cmp_val   : forall x y n h i s, cell h i s = true ->
                let r := Rd m h i (Cmp m x y n h i s) in (r =? -1) || (r =? 0) || (r =? 1) = true;
  cmp_rd    : forall x y n h i h' i' s, other h i h' i' = true -> Rd m h' i' (Cmp m x y n h i s) = Rd m h' i' s;
  cmp_rd32  : forall x y n h i h' i' s, Rd32 m h' i' (Cmp m x y n h i s) = Rd32 m h' i' s;
  (* ---- SIZES: a block is never smaller than when the program started; only kq_grow changes a size, and it changes no
     cell (the new cells read 0, as they did outside the block), no narrow cell, nothing the devices saw *)
  len_size   : forall h s, (Len m h <=? Size m h s) = true;
  size_grow  : forall h n s, growable h n = true -> Size m h (Grow m h n s) = (if Size m h s <? n then n else Size m h s);
  size_grow_ne : forall h n h' s, (h =? h') = false -> Size m h' (Grow m h n s) = Size m h' s;
  grow_out   : forall h n s, growable h n = false -> Grow m h n s = s;
  rd_grow    : forall h n h' i' s, Rd m h' i' (Grow m h n s) = Rd m h' i' s;
  rd32_grow  : forall h n h' i' s, Rd32 m h' i' (Grow m h n s) = Rd32 m h' i' s;
  trace_grow : forall h n s, Trace m (Grow m h n s) = Trace m s;
  size_upd   : forall h i v h' s, Size m h' (Upd m h i v s) = Size m h' s;
  size_upd32 : forall h i v h' s, Size m h' (Upd32 m h i v s) = Size m h' s;
  size_load  : forall w a h i h' s, Size m h' (Load m w a h i s) = Size m h' s;
  size_aload : forall w a h i h' s, Size m h' (ALoad m w a h i s) = Size m h' s;
  size_store : forall w a v h' s, Size m h' (Store m w a v s) = Size m h' s;
  size_store64 : forall a lo hi h' s, Size m h' (Store64 m a lo hi s) = Size m h' s;
  size_astore : forall w a v h' s, Size m h' (AStore m w a v s) = Size m h' s;
  size_astore64 : forall a lo hi h' s, Size m h' (AStore64 m a lo hi s) = Size m h' s;
  size_atomic : forall op w a v h i h' s, Size m h' (Atomic m op w a v h i s) = Size m h' s;
  size_atomic64 : forall op a lo hi h i h' s, Size m h' (Atomic64 m op a lo hi h i s) = Size m h' s;
  size_cas   : forall w a o n h i h' s, Size m h' (Cas m w a o n h i s) = Size m h' s;
  size_cas64 : forall a ol oh nl nh h i h' s, Size m h' (Cas64 m a ol oh nl nh h i s) = Size m h' s;
  size_fence : forall k h' s, Size m h' (Fence m k s) = Size m h' s;
  size_copy  : forall d x n h' s, Size m h' (Copy m d x n s) = Size m h' s;
  size_fill  : forall d b n h' s, Size m h' (Fill m d b n s) = Size m h' s;
  size_cmp   : forall x y n h i h' s, Size m h' (Cmp m x y n h i s) = Size m h' s
}.
End Laws.

(* THE REAL OPERATIONS, and the one axiom: they obey the laws *)
Definition real : ops := mkOps mem rd upd kq_len kq_size kq_grow rd32 upd32 kq_len32 hw_load hw_store hw_store64 hw_atomic hw_atomic64
                               hw_cas hw_cas64 hw_aload hw_astore hw_astore64 hw_fence hw_copy hw_fill hw_cmp hw_call
                               hw_addr hw_trace.
Axiom real_laws : laws real.

(* ---- from 63-bit numbers to Z, for proofs: comparisons, sums and products that do not overflow *)
Lemma lt_Z (x y : int) : (x <? y) = true <-> (Sint63.to_Z x < Sint63.to_Z y)%Z.
Proof. rewrite Sint63.ltb_spec. destruct (Z.compare_spec (Sint63.to_Z x) (Sint63.to_Z y)); split; intro; try lia; congruence. Qed.
Lemma le_Z (x y : int) : (x <=? y) = true <-> (Sint63.to_Z x <= Sint63.to_Z y)%Z.
Proof. rewrite Sint63.leb_spec. destruct (Z.compare_spec (Sint63.to_Z x) (Sint63.to_Z y)); split; intro; try lia; congruence. Qed.
Lemma lt_Z_false (x y : int) : (x <? y) = false <-> (Sint63.to_Z y <= Sint63.to_Z x)%Z.
Proof. destruct (x <? y) eqn:E; split; intro H; try discriminate; [apply lt_Z in E; lia | | ]; [ | reflexivity].
       destruct (Z_lt_le_dec (Sint63.to_Z x) (Sint63.to_Z y)) as [L | L]; [apply lt_Z in L; congruence | lia]. Qed.
Lemma le_Z_false (x y : int) : (x <=? y) = false <-> (Sint63.to_Z y < Sint63.to_Z x)%Z.
Proof. destruct (x <=? y) eqn:E; split; intro H; try discriminate; [apply le_Z in E; lia | | ]; [ | reflexivity].
       destruct (Z_le_gt_dec (Sint63.to_Z x) (Sint63.to_Z y)) as [L | L]; [apply le_Z in L; congruence | lia]. Qed.
Lemma eq_Z (x y : int) : (x =? y) = true <-> Sint63.to_Z x = Sint63.to_Z y.
Proof. rewrite Uint63.eqb_spec. split; [intros -> | apply Sint63.to_Z_inj]; reflexivity. Qed.
Lemma eq_Z_false (x y : int) : (x =? y) = false <-> Sint63.to_Z x <> Sint63.to_Z y.
Proof. destruct (x =? y) eqn:E; split; intro H; try discriminate; [apply eq_Z in E; contradiction | | reflexivity].
       intro C; apply eq_Z in C; congruence. Qed.
Lemma min_max : Sint63.to_Z Sint63.min_int = (-4611686018427387904)%Z /\ Sint63.to_Z Sint63.max_int = 4611686018427387903%Z.
Proof. split; reflexivity. Qed.
Lemma add_Z (x y : int) : (-4611686018427387904 <= Sint63.to_Z x + Sint63.to_Z y <= 4611686018427387903)%Z ->
  Sint63.to_Z (x + y) = (Sint63.to_Z x + Sint63.to_Z y)%Z.
Proof. intro B. apply Sint63.to_Z_add. destruct min_max as [-> ->]. exact B. Qed.
Lemma sub_Z (x y : int) : (-4611686018427387904 <= Sint63.to_Z x - Sint63.to_Z y <= 4611686018427387903)%Z ->
  Sint63.to_Z (x - y) = (Sint63.to_Z x - Sint63.to_Z y)%Z.
Proof. intro B. apply Sint63.to_Z_sub. destruct min_max as [-> ->]. exact B. Qed.
Lemma mul_Z (x y : int) : (-4611686018427387904 <= Sint63.to_Z x * Sint63.to_Z y <= 4611686018427387903)%Z ->
  Sint63.to_Z (x * y) = (Sint63.to_Z x * Sint63.to_Z y)%Z.
Proof. intro B. apply Sint63.to_Z_mul. destruct min_max as [-> ->]. exact B. Qed.
Lemma to_Z_bounds (x : int) : (-4611686018427387904 <= Sint63.to_Z x <= 4611686018427387903)%Z.
Proof. pose proof (Sint63.to_Z_bounded x) as B. destruct min_max as [E1 E2]. rewrite E1, E2 in B. exact B. Qed.
(* a 32-bit number that is not negative is kept as it is in a narrow cell *)
Lemma sx32_small (v : int) : (0 <= Sint63.to_Z v < 2147483648)%Z -> sx32 v = v.
Proof.
  intro B. unfold sx32.
  assert (L : v land 4294967295 = v).
  { apply Sint63.to_Z_inj. rewrite !Sint63.to_Z_cmodwB, Uint63.land_spec'.
    assert (U : φ (v)%uint63 = Sint63.to_Z v).
    { rewrite <- (Sint63.to_Z_mod_Uint63to_Z v). apply Z.mod_small. unfold wB, size, Uint63.digits. simpl. lia. }
    rewrite U. change (φ (4294967295)%uint63) with (Z.ones 32). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite L. destruct (v <? 2147483648) eqn:E; [reflexivity | ]. apply lt_Z_false in E. change (Sint63.to_Z 2147483648) with 2147483648%Z in E. lia.
Qed.
