import Papers.PODC2012.LimitedUseSnapshots.SnapshotMWDefs
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.StrongLin

/-!
# Algorithm 4: the invariant

Linearization points (as in the paper): `MW-Scan` at its `Scan(s)`; an `MW-Update` of component
`j` with timestamp `t` at the first `Update(s, ·)` (Line 3, by any process) after which the
largest timestamp of component `j` in `s` is `≥ t` (operations linearized at the same step are
ordered with the writer's own operation last). An `MW-Update` has a *determined* timestamp
(`detTs`) once it has performed `ReadMax(timestamp)`.
-/

namespace Podc.LimitedUseSnapshots.Snapshot.MW

open Cslib.SharedMemory

variable {n c : ℕ} {W : Type} {w₀ : Fin c → W} [NeZero n]

/-- Configurations of Algorithm 4. -/
abbrev Cfg4 (n c : ℕ) (W : Type) (w₀ : Fin c → W) :=
  Config (mwSnap c W w₀) (obj4 n c W w₀) (Fin n) (Loc4 c W)

/-- Linearizations. -/
abbrev Lin4 (c : ℕ) (W : Type) (w₀ : Fin c → W) (n : ℕ) :=
  List (OpId (Fin n) × (mwSnap c W w₀).Op)

/-- The determined timestamp (and component) of a pending `MW-Update` of process `k`. -/
def detTs (k : Fin n) (l : Loc4 c W) : Option (Fin c × ℕ) :=
  match l.pc with
  | .wr j _ r => some (j, n * (r + 1) + k)
  | .up j => some (j, (l.rcd j).2)
  | _ => none

variable (w₀) in
/-- The per-process invariant (`S` = content of `s`, `mr` = value of `timestamp`). -/
def PInv4 (S : Fin n → Rec c W) (mr : ℕ) (L : Lin4 c W w₀ n) (l : Loc4 c W)
    (pd : Option (MOp c W)) (x : OpId (Fin n)) (k : Fin n) : Prop :=
  match l.pc with
  | .idle => pd = none ∧ S k = l.rcd
  | .rd j v => pd = some (.update j v) ∧ S k = l.rcd ∧ x ∉ L.map Prod.fst
  | .wr j v r => pd = some (.update j v) ∧ S k = l.rcd ∧ r ≤ mr ∧
      (∀ j', (l.rcd j').2 < n * (r + 1) + k) ∧
      (x ∈ L.map Prod.fst ↔ n * (r + 1) + k ≤ maxTs S j)
  | .up j => pd = some (.update j (l.rcd j).1) ∧ (∀ j', j' ≠ j → S k j' = l.rcd j') ∧
      (l.rcd j).2 % n = k ∧ 0 < (l.rcd j).2 ∧ (l.rcd j).2 < n * (mr + 1) ∧
      (S k j).2 < (l.rcd j).2 ∧ (x ∈ L.map Prod.fst ↔ (l.rcd j).2 ≤ maxTs S j)
  | .ack => (∃ j v, pd = some (.update j v)) ∧ S k = l.rcd ∧ x ∈ L.map Prod.fst
  | .sc => pd = some .scan ∧ S k = l.rcd ∧ x ∉ L.map Prod.fst
  | .retS val => pd = some .scan ∧ S k = l.rcd ∧
      (mwSnap c W w₀).respIn (mwSnap c W w₀).init L x = some (some val)

/-- Shape of the entries of `s`: timestamp `0` carries the initial value, any other timestamp
`t` of process `k` satisfies `t mod n = k`. -/
def Good (w₀ : Fin c → W) (S : Fin n → Rec c W) : Prop :=
  ∀ k j, ((S k j).2 = 0 → (S k j).1 = w₀ j) ∧ ((S k j).2 ≠ 0 → (S k j).2 % n = k)

/-- **The invariant of Algorithm 4.** -/
structure Inv4 (α : List (Label (Fin n) (mwSnap c W w₀))) (C : Cfg4 n c W w₀)
    (L : Lin4 c W w₀ n) : Prop where
  lin : IsLinearization α L
  ts_lt : ∀ k j, (C.mem .s k j).2 < n * (C.mem .ts + 1)
  good : Good w₀ (C.mem .s)
  state : linState (A := mwSnap c W w₀) L = combine (C.mem .s)
  proc : ∀ k, PInv4 w₀ (C.mem .s) (C.mem .ts) L (C.loc k) (C.pend k) (curOp α k) k

/-! ### Maximal timestamps and `CombineScan` -/

omit [NeZero n] in
lemma le_maxTs (S : Fin n → Rec c W) (k : Fin n) (j : Fin c) : (S k j).2 ≤ maxTs S j :=
  Finset.le_sup (f := fun k => (S k j).2) (Finset.mem_univ k)

omit [NeZero n] in
lemma maxTs_lt {S : Fin n → Rec c W} {j : Fin c} {B : ℕ} (hB : 0 < B)
    (h : ∀ k, (S k j).2 < B) : maxTs S j < B :=
  (Finset.sup_lt_iff (f := fun k => (S k j).2) hB).2 fun k _ => h k

lemma exists_maxTs (S : Fin n → Rec c W) (j : Fin c) : ∃ k, (S k j).2 = maxTs S j := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
    Finset.univ_nonempty (fun k => (S k j).2)
  exact ⟨k, hk.symm⟩

/-- `CombineScan` returns the value with the largest timestamp. -/
lemma combine_eq {S : Fin n → Rec c W} (hG : Good w₀ S) {j : Fin c} {k : Fin n}
    (hk : (S k j).2 = maxTs S j) (hpos : maxTs S j ≠ 0) : combine S j = (S k j).1 := by
  have := (hG k j).2 (by omega)
  simp only [combine]
  congr 2
  ext; simp only [← hk, this]

lemma combine_eq_zero {S : Fin n → Rec c W} (hG : Good w₀ S) {j : Fin c}
    (h0 : maxTs S j = 0) : combine S j = w₀ j := by
  simp only [combine]
  apply (hG _ j).1
  have := le_maxTs S ⟨maxTs S j % n, Nat.mod_lt _ (NeZero.pos n)⟩ j
  omega

omit [NeZero n] in
lemma maxTs_congr {S S' : Fin n → Rec c W} {j : Fin c} (h : ∀ k, S' k j = S k j) :
    maxTs S' j = maxTs S j := by
  simp only [maxTs, h]

lemma combine_congr {S S' : Fin n → Rec c W} {j : Fin c} (h : ∀ k, S' k j = S k j) :
    combine S' j = combine S j := by
  simp only [combine, maxTs_congr h, h]

omit [NeZero n] in
/-- Raising one timestamp. -/
lemma maxTs_update {S : Fin n → Rec c W} {k : Fin n} {R : Rec c W} {j : Fin c}
    (hle : (S k j).2 ≤ (R j).2) :
    maxTs (Function.update S k R) j = max (maxTs S j) (R j).2 := by
  apply le_antisymm
  · refine Finset.sup_le fun k' _ => ?_
    by_cases hk : k' = k
    · subst hk; simp
    · simp only [Function.update_of_ne hk]; exact le_max_of_le_left (le_maxTs S k' j)
  · refine max_le (Finset.sup_le fun k' _ => ?_) ?_
    · by_cases hk : k' = k
      · subst hk
        exact hle.trans (by
          have := le_maxTs (Function.update S k' R) k' j; simpa using this)
      · have := le_maxTs (Function.update S k R) k' j
        simpa [Function.update_of_ne hk] using this
    · have := le_maxTs (Function.update S k R) k j; simpa using this

/-! ### Updates in sequence -/

lemma runOps_updates_on (j : Fin c) (q : Fin c → W) (os : List (MOp c W))
    (hos : ∀ o ∈ os, ∃ v, o = .update j v) (j' : Fin c) (hj : j' ≠ j) :
    (mwSnap c W w₀).runOps q os j' = q j' := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, ih _ (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))]
    obtain ⟨v, rfl⟩ := hos o List.mem_cons_self
    simp [Function.update_of_ne hj]

lemma runOps_updates_last (j : Fin c) (q : Fin c → W) (os : List (MOp c W))
    (hos : ∀ o ∈ os, ∃ v, o = .update j v) (v : W) :
    (mwSnap c W w₀).runOps q (os ++ [.update j v]) = Function.update q j v := by
  rw [ObjSpec.runOps_append, ObjSpec.runOps_cons, ObjSpec.runOps_nil]
  funext j'
  change Function.update ((mwSnap c W w₀).runOps q os) j v j' = Function.update q j v j'
  by_cases hj : j' = j
  · subst hj; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    exact runOps_updates_on (w₀ := w₀) j q os hos j' hj

omit [NeZero n] in
/-- The response of an `MW-Update` in any linearization containing it. -/
lemma respIn_update {α : List (Label (Fin n) (mwSnap c W w₀))} {L : Lin4 c W w₀ n}
    (hL : IsLinearization α L) {x : OpId (Fin n)} (hx : x ∈ L.map Prod.fst) {j : Fin c} {v : W}
    (hop : opOf α x = some (.update j v)) :
    (mwSnap c W w₀).respIn (mwSnap c W w₀).init L x = some none := by
  obtain ⟨⟨y, o⟩, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hy
  have := hL.op_eq _ hy
  rw [hop] at this; cases this
  rw [ObjSpec.respIn_of_split hL.nodup hsplit]

/-! ### Frame -/

omit [NeZero n] in
lemma PInv4.pc_idle {S : Fin n → Rec c W} {mr : ℕ} {L : Lin4 c W w₀ n} {l : Loc4 c W}
    {x : OpId (Fin n)} {k : Fin n} (h : PInv4 w₀ S mr L l none x k) : l.pc = .idle := by
  unfold PInv4 at h; split at h <;> simp_all

omit [NeZero n] in
/-- Steps that do not change the row of `k` in `s`, do not decrease `timestamp` nor the maximal
timestamps, and only add to `L` operations with determined timestamps that are now covered,
preserve the invariant of `k`. -/
lemma PInv4.frame {S S' : Fin n → Rec c W} {mr mr' : ℕ} {L L' : Lin4 c W w₀ n} {l : Loc4 c W}
    {pd : Option (MOp c W)} {x : OpId (Fin n)} {k : Fin n} (h : PInv4 w₀ S mr L l pd x k)
    (hSk : S' k = S k) (hmr : mr ≤ mr')
    (hiff : ∀ j thr, detTs k l = some (j, thr) → (x ∈ L.map Prod.fst ↔ thr ≤ maxTs S j) →
      (x ∈ L'.map Prod.fst ↔ thr ≤ maxTs S' j))
    (hnodet : detTs k l = none → (x ∈ L'.map Prod.fst ↔ x ∈ L.map Prod.fst))
    (hresp : ∀ y ∈ L.map Prod.fst, (mwSnap c W w₀).respIn (mwSnap c W w₀).init L' y =
      (mwSnap c W w₀).respIn (mwSnap c W w₀).init L y) :
    PInv4 w₀ S' mr' L' l pd x k := by
  unfold PInv4 at h ⊢
  split at h
  · rename_i hpc; exact ⟨h.1, hSk.trans h.2⟩
  · rename_i j v hpc
    have := hnodet (by simp [detTs, hpc])
    exact ⟨h.1, hSk.trans h.2.1, by rw [this]; exact h.2.2⟩
  · rename_i j v r hpc
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨h1, hSk.trans h2, h3.trans hmr, h4, hiff j _ (by simp [detTs, hpc]) h5⟩
  · rename_i j hpc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    refine ⟨h1, fun j' hj' => by rw [hSk]; exact h2 j' hj', h3, h4, ?_, by rw [hSk]; exact h6,
      hiff j _ (by simp [detTs, hpc]) h7⟩
    exact lt_of_lt_of_le h5 (Nat.mul_le_mul_left n (by omega))
  · rename_i hpc
    have := hnodet (by simp [detTs, hpc])
    exact ⟨h.1, hSk.trans h.2.1, by rw [this]; exact h.2.2⟩
  · rename_i hpc
    have := hnodet (by simp [detTs, hpc])
    exact ⟨h.1, hSk.trans h.2.1, by rw [this]; exact h.2.2⟩
  · rename_i val hpc
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, hSk.trans h2, by rw [hresp x (ObjSpec.mem_of_respIn_eq_some h3), h3]⟩

omit [NeZero n] in
/-- Pending `MW-Update`s with a determined timestamp. -/
lemma PInv4.of_detTs {S : Fin n → Rec c W} {mr : ℕ} {L : Lin4 c W w₀ n} {l : Loc4 c W}
    {pd : Option (MOp c W)} {x : OpId (Fin n)} {k : Fin n} (h : PInv4 w₀ S mr L l pd x k)
    {j : Fin c} {thr : ℕ} (hd : detTs k l = some (j, thr)) :
    (∃ v, pd = some (.update j v)) ∧ (x ∈ L.map Prod.fst ↔ thr ≤ maxTs S j) ∧ thr % n = k ∧
      (S k j).2 < thr := by
  unfold PInv4 at h; unfold detTs at hd
  split at h <;> rename_i hpc <;> simp only [hpc, reduceCtorEq] at hd
  · rename_i j' v r
    simp only [Option.some.injEq, Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd
    refine ⟨⟨v, h.1⟩, h.2.2.2.2, ?_, ?_⟩
    · rw [Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt k.isLt
    · rw [h.2.1]; exact h.2.2.2.1 _
  · rename_i j'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd; obtain ⟨rfl, rfl⟩ := hd
    exact ⟨⟨_, h.1⟩, h.2.2.2.2.2.2, h.2.2.1, h.2.2.2.2.2.1⟩

end Podc.LimitedUseSnapshots.Snapshot.MW
