import Papers.PODC2014.DistributedUniversality.InvA2

/-!
# Round-level facts derived from `InvA`

* `InvA.finR_agree`: in each round, for each object, at most one operation can be committed
  (if one process ends the adopt-commit part of round `r` with `(commit, V)`, every process ends it
  with a pair carrying `V`) — the paper's "sequence `(op^m_r)` of committed operations";
* `InvA.cf`: a process that does not end the round with `(commit, V)` has seen (in the base
  objects) a proposal of the round different from `V`.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

/-- All final pairs of round `r` for object `m` (there is at least one) carry the value `V`. -/
def Unif (s : St n k) (r : ℕ) (m : Fin k) (V : Op n) : Prop :=
  (∃ j tw, s.finR r m j = some tw) ∧ ∀ j b w, s.finR r m j = some (b, w) → w = V

/-- The well-formedness condition on modes used throughout: in Figure 2 line 4M proposes
`ac_opᵢ[m]` (not the literal text of Section 4.3). -/
def Mode.Good (M : Mode) : Prop := M.ca = true → M.typo4M = false

theorem InvA.finR_agree (I : InvA M s) (hM : M.Good) {r m i j V b w}
    (hi : s.finR r m i = some (true, V)) (hj : s.finR r m j = some (b, w)) : w = V := by
  rcases I.finR_src _ _ _ _ hi with hi' | ⟨-, hi'⟩ <;>
    rcases I.finR_src _ _ _ _ hj with hj' | ⟨hbt, hj'⟩
  · exact I.acR_agree _ _ _ _ _ _ _ _ hi' hj'
  · -- i committed in phase true, j in phase false (commit)
    simp only at hbt; subst hbt
    have hca := I.acI0_ca _ _ _ _ (I.acR_inv _ _ _ _ _ _ hj').choose_spec.1
    obtain ⟨own, -, ⟨j', hj''⟩, -⟩ := I.acR_inv _ _ _ _ _ _ hi'
    obtain ⟨j3, t3, h3⟩ := I.acI1ca hca (hM hca) _ _ _ _ hj''
    exact (I.acR_agree _ _ _ _ _ _ _ _ hj' h3).symm
  · have hca := I.acI0_ca _ _ _ _ (I.acR_inv _ _ _ _ _ _ hi').choose_spec.1
    obtain ⟨own, -, ⟨j', hj''⟩, -⟩ := I.acR_inv _ _ _ _ _ _ hj'
    obtain ⟨j3, t3, h3⟩ := I.acI1ca hca (hM hca) _ _ _ _ hj''
    exact I.acR_agree _ _ _ _ _ _ _ _ hi' h3
  · exact I.acR_agree _ _ _ _ _ _ _ _ hi' hj'

theorem InvA.unif_of_commit (I : InvA M s) (hM : M.Good) {r m j V}
    (h : s.finR r m j = some (true, V)) : Unif s r m V :=
  ⟨⟨j, _, h⟩, fun _ _ _ hj => I.finR_agree hM h hj⟩

/-- A final pair which is not `(commit, V)` witnesses a proposal of the round different
from `V`. -/
theorem InvA.cf (I : InvA M s) {r m i t W} (h : s.finR r m i = some (t, W)) (V : Op n) :
    (t = true ∧ W = V) ∨ ∃ j W', s.opRec r m j = some W' ∧ W' ≠ V := by
  have hsrc : ∃ b, s.acR r b m i = some (t, W) := by
    rcases I.finR_src _ _ _ _ h with h1 | ⟨-, h1⟩
    · exact ⟨true, h1⟩
    · exact ⟨false, h1⟩
  obtain ⟨b, hb⟩ := hsrc
  have hprov : ∀ q w, s.acI r b m q = some w → ∃ j, s.opRec r m j = some w := by
    intro q w hw
    cases b
    · exact ⟨q, I.acI0 _ _ _ _ hw⟩
    · exact I.acI1 _ _ _ _ hw
  obtain ⟨own, hown, -, hc⟩ := I.acR_inv _ _ _ _ _ _ hb
  by_cases hWV : t = true ∧ W = V
  · exact Or.inl hWV
  · right
    rcases hc with ⟨ht, rfl⟩ | ⟨q, w', -, hq, hne⟩
    · obtain ⟨j, hj⟩ := hprov _ _ hown
      exact ⟨j, W, hj, fun e => hWV ⟨ht, e⟩⟩
    · by_cases ho : own = V
      · subst ho
        obtain ⟨j, hj⟩ := hprov _ _ hq
        exact ⟨j, w', hj, hne⟩
      · obtain ⟨j, hj⟩ := hprov _ _ hown
        exact ⟨j, own, hj, ho⟩

/-- Uniformity is lost, never gained, once the round has a final pair. -/
theorem unif_pre (hmono : ∀ r m j tw, s.finR r m j = some tw → s'.finR r m j = some tw)
    {r m V} (hne : ∃ j tw, s.finR r m j = some tw) (hU : Unif s' r m V) : Unif s r m V :=
  ⟨hne, fun j b w hj => hU.2 j b w (hmono _ _ _ _ hj)⟩

theorem InvA.finR_nonempty (I : InvA M s) {i : Fin n} {r : ℕ} (m : Fin k) (h1 : 1 ≤ r)
    (h2 : r < (s.loc i).r) : ∃ j tw, s.finR r m j = some tw := by
  obtain ⟨tw, h⟩ := I.finR_past i r m h1 h2
  exact ⟨i, tw, h⟩

theorem InvA.unif_pos (I : InvA M s) {r m V} (h : Unif s r m V) : 1 ≤ r := by
  obtain ⟨⟨j, tw, hj⟩, -⟩ := h
  exact I.finR_pos _ _ _ _ hj

end Podc.DistributedUniversality
