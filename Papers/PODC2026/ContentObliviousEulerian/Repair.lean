import Papers.PODC2026.ContentObliviousEulerian.Decomposition

-- CSLib candidate: Cslib/Combinatorics/SimpleGraph/PortPairing.lean (re-pairing merges circuits)

/-!
# Lemma 4: re-pairing merges circuits

Frei, Gelles, Ghazy, Nolin, PODC 2026, §2.1, Lemma 4.

Node `v` has pairs `(a₀, b₀), …, (a_k, b_k)` (with `bᵢ = π.pair aᵢ`) lying on pairwise distinct
circuits `C₀, …, C_k`. It re-pairs its ports as `(b₀, a₁), (b₁, a₂), …, (b_k, a₀)`
(`Pairing.repair`), leaving all other pairs (at `v` and elsewhere) unchanged.

`lemma4` shows: in the new pairing two darts are on the same circuit iff they were on the same
circuit before, or both were on one of `C₀, …, C_k`. So `C₀, …, C_k` are merged into a single
circuit (whose edge set is their union, `lemma4_edges`), and every other circuit is unchanged.
Only node `v` changes its pairing (`repair_pair_of_fst_ne`).

The re-pairing itself only needs the `2(k+1)` darts to be distinct (`Pairing.repair`); the
distinctness of the circuits is used only for the merging statement. If two of the pairs lie on
the same circuit, re-pairing may instead *split* it (see `DoubleMerge.lean`).
-/

namespace Podc.ContentObliviousEulerian

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Pairing

set_option linter.unusedSectionVars false

variable (π : Pairing G) {k : ℕ} (a : Fin (k + 1) → G.Dart) {v : V}

/-- The re-pairing `(b₀, a₁), (b₁, a₂), …, (b_k, a₀)` of Lemma 4, where `bᵢ = π.pair aᵢ`. All other
pairs are unchanged. It is a valid pairing as soon as the darts `aᵢ, bᵢ` are distinct and at the
same node `v`. -/
noncomputable def repair (hv : ∀ i, (a i).fst = v) (hinj : Function.Injective a)
    (hab : ∀ i j, a i ≠ π.pair (a j)) : Pairing G := by
  classical
  have choose_b : ∀ i (h : ∃ j, π.pair (a i) = π.pair (a j)), h.choose = i := fun i h => by
    have := h.choose_spec
    have := congrArg π.pair this
    simp only [π.pair_pair] at this
    exact (hinj this).symm
  have choose_a : ∀ i (h : ∃ j, a i = a j), h.choose = i := fun i h => (hinj h.choose_spec).symm
  let f : G.Dart → G.Dart := fun d =>
    if h : ∃ i, d = π.pair (a i) then a (h.choose + 1)
    else if h' : ∃ i, d = a i then π.pair (a (h'.choose - 1)) else π.pair d
  have fb : ∀ i, f (π.pair (a i)) = a (i + 1) := fun i => by
    have h : ∃ j, π.pair (a i) = π.pair (a j) := ⟨i, rfl⟩
    simp only [f, dite_eq_left h, choose_b i h]
  have fa : ∀ i, f (a i) = π.pair (a (i - 1)) := fun i => by
    have h : ¬ ∃ j, a i = π.pair (a j) := fun ⟨j, hj⟩ => hab i j hj
    have h' : ∃ j, a i = a j := ⟨i, rfl⟩
    simp only [f, dite_eq_right h, dite_eq_left h', choose_a i h']
  have fo : ∀ d, (∀ i, d ≠ π.pair (a i)) → (∀ i, d ≠ a i) → f d = π.pair d := fun d h1 h2 => by
    have e1 : ¬ ∃ i, d = π.pair (a i) := fun ⟨i, hi⟩ => h1 i hi
    have e2 : ¬ ∃ i, d = a i := fun ⟨i, hi⟩ => h2 i hi
    simp only [f, dite_eq_right e1, dite_eq_right e2]
  have cases : ∀ d, (∃ i, d = π.pair (a i)) ∨ (∃ i, d = a i) ∨
      ((∀ i, d ≠ π.pair (a i)) ∧ (∀ i, d ≠ a i)) := fun d => by
    by_cases h1 : ∃ i, d = π.pair (a i)
    · exact Or.inl h1
    by_cases h2 : ∃ i, d = a i
    · exact Or.inr (Or.inl h2)
    push Not at h1 h2
    exact Or.inr (Or.inr ⟨h1, h2⟩)
  have other_pair : ∀ d, (∀ i, d ≠ π.pair (a i)) → (∀ i, d ≠ a i) →
      (∀ i, π.pair d ≠ π.pair (a i)) ∧ (∀ i, π.pair d ≠ a i) := fun d h1 h2 =>
    ⟨fun i h => h2 i (by simpa [π.pair_pair] using congrArg π.pair h),
      fun i h => h1 i (by rw [← h, π.pair_pair])⟩
  exact
  { pair := f
    pair_pair := fun d => by
      rcases cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
      · rw [fb, fa, add_sub_cancel_right]
      · rw [fa, fb, sub_add_cancel]
      · rw [fo d h1 h2, fo _ (other_pair d h1 h2).1 (other_pair d h1 h2).2, π.pair_pair]
    pair_ne := fun d => by
      rcases cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
      · rw [fb]; exact hab _ _
      · rw [fa]; exact (hab _ _).symm
      · rw [fo d h1 h2]; exact π.pair_ne d
    fst_pair := fun d => by
      rcases cases d with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨h1, h2⟩
      · rw [fb, hv, π.fst_pair, hv]
      · rw [fa, π.fst_pair, hv, hv]
      · rw [fo d h1 h2, π.fst_pair] }

variable {a} (hv : ∀ i, (a i).fst = v) (hinj : Function.Injective a)
  (hab : ∀ i j, a i ≠ π.pair (a j))

lemma repair_pair_b (i : Fin (k + 1)) :
    (π.repair a hv hinj hab).pair (π.pair (a i)) = a (i + 1) := by
  classical
  have h : ∃ j, π.pair (a i) = π.pair (a j) := ⟨i, rfl⟩
  have hc : h.choose = i := by
    have := congrArg π.pair h.choose_spec
    simp only [π.pair_pair] at this
    exact (hinj this).symm
  simp only [repair, dite_eq_left h, hc]

lemma repair_pair_a (i : Fin (k + 1)) :
    (π.repair a hv hinj hab).pair (a i) = π.pair (a (i - 1)) := by
  classical
  have h : ¬ ∃ j, a i = π.pair (a j) := fun ⟨j, hj⟩ => hab i j hj
  have h' : ∃ j, a i = a j := ⟨i, rfl⟩
  have hc : h'.choose = i := (hinj h'.choose_spec).symm
  simp only [repair, dite_eq_right h, dite_eq_left h', hc]

lemma repair_pair_other {d : G.Dart} (h1 : ∀ i, d ≠ π.pair (a i)) (h2 : ∀ i, d ≠ a i) :
    (π.repair a hv hinj hab).pair d = π.pair d := by
  classical
  have e1 : ¬ ∃ i, d = π.pair (a i) := fun ⟨i, hi⟩ => h1 i hi
  have e2 : ¬ ∃ i, d = a i := fun ⟨i, hi⟩ => h2 i hi
  simp only [repair, dite_eq_right e1, dite_eq_right e2]

/-- Only node `v` changes its pairing. -/
theorem repair_pair_of_fst_ne {d : G.Dart} (hd : d.fst ≠ v) :
    (π.repair a hv hinj hab).pair d = π.pair d :=
  π.repair_pair_other hv hinj hab (fun i h => hd (by rw [h, π.fst_pair, hv]))
    (fun i h => hd (by rw [h, hv]))

/-! ### Merging -/

variable (hdist : ∀ i j, i ≠ j → ¬ π.Circ (a i) (a j))

include hdist in
lemma injective_of_dist : Function.Injective a := fun i j h => by
  by_contra hij; exact hdist i j hij (h ▸ Circ.refl π _)

include hdist in
lemma ne_pair_of_dist : ∀ i j, a i ≠ π.pair (a j) := fun i j h => by
  by_cases hij : i = j
  · subst hij; exact π.pair_ne _ h.symm
  · exact hdist i j hij (h ▸ (Circ.pair π (a j)).symm)

/-- The set of darts on the circuits `C₀, …, C_k`. -/
def U (a : Fin (k + 1) → G.Dart) (x : G.Dart) : Prop := ∃ i, π.Circ (a i) x

include hdist in
/-- A dart on one of the circuits `C_j` whose reversal is not "other" lies on `C_j` only via one
of the re-paired ports. -/
lemma other_of_not_U {x : G.Dart} (hx : ¬ π.U a x) :
    (∀ i, x ≠ π.pair (a i)) ∧ (∀ i, x ≠ a i) :=
  ⟨fun i h => hx ⟨i, h ▸ Circ.pair π (a i)⟩, fun i h => hx ⟨i, h ▸ Circ.refl π _⟩⟩

include hdist in
/-- Walking along `C_i` from `aᵢ` reaches every dart of `C_i` without using the re-paired pair
`(aᵢ, bᵢ)`: all the darts `next^t aᵢ`, `t < period aᵢ`, stay on one circuit of the new pairing. -/
lemma repair_path (i : Fin (k + 1)) :
    ∀ t < π.period (a i), (π.repair a hv hinj hab).Circ (a i) ((π.next ^ t) (a i)) := by
  intro t
  induction t with
  | zero => intro _; exact Circ.refl _ _
  | succ t ih =>
    intro ht
    set x := (π.next ^ t) (a i)
    have hx : π.Circ (a i) x := Or.inl ⟨t, by simp [x]⟩
    have hother1 : ∀ j, x.symm ≠ π.pair (a j) := by
      intro j hj
      have hcj : π.Circ (a i) (a j) :=
        (hx.trans (Circ.symm_dart π x)).trans (hj ▸ (Circ.pair π (a j)).symm)
      by_cases hij : i = j
      · subst hij
        have h1 : (π.next ^ (t + 1)) (a i) = a i := by
          rw [pow_succ', Equiv.Perm.mul_apply, next_apply, hj, π.pair_pair]
        have := Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod (f := π.next) (x := a i)
          (Nat.succ_ne_zero t) ht
        apply this
        rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow]; exact h1
      · exact hdist i j hij hcj
    have hother2 : ∀ j, x.symm ≠ a j := by
      intro j hj
      by_cases hij : i = j
      · subst hij
        apply π.not_sameCycle_symm (a i)
        have : x = (a i).symm := by rw [← hj, Dart.symm_symm]
        rw [← this]; exact ⟨t, by simp [x]⟩
      · exact hdist i j hij ((hx.trans (Circ.symm_dart π x)).trans (hj ▸ Circ.refl π _))
    have h1 := ih (by omega)
    have h2 : (π.repair a hv hinj hab).Circ x x.symm := Circ.symm_dart _ x
    have h3 := Circ.pair (π.repair a hv hinj hab) x.symm
    rw [π.repair_pair_other hv hinj hab hother1 hother2] at h3
    have : (π.next ^ (t + 1)) (a i) = π.pair x.symm := by
      rw [pow_succ', Equiv.Perm.mul_apply, next_apply]
    rw [this]
    exact h1.trans (h2.trans h3)

include hdist in
lemma repair_circ_b (i : Fin (k + 1)) :
    (π.repair a hv hinj hab).Circ (a i) (π.pair (a i)) := by
  obtain ⟨m, hm⟩ : ∃ m, π.period (a i) = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (π.period_pos _)).symm⟩
  set x := (π.next ^ m) (a i)
  have hxs : x.symm = π.pair (a i) := by
    have : π.next x = a i := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ', ← hm, π.pow_period]
    rw [next_apply] at this
    rw [← this, π.pair_pair]
  rw [← hxs]
  exact (π.repair_path hv hinj hab hdist i m (by omega)).trans (Circ.symm_dart _ x)

include hdist in
lemma repair_circ_a_zero : ∀ i, (π.repair a hv hinj hab).Circ (a 0) (a i) := by
  intro i
  induction i using Fin.induction with
  | zero => exact Circ.refl _ _
  | succ i ih =>
    have h1 := π.repair_circ_b hv hinj hab hdist i.castSucc
    have h2 := Circ.pair (π.repair a hv hinj hab) (π.pair (a i.castSucc))
    rw [π.repair_pair_b hv hinj hab, Fin.coeSucc_eq_succ] at h2
    exact ih.trans (h1.trans h2)

include hdist in
lemma repair_circ_of_U {x : G.Dart} (hx : π.U a x) : (π.repair a hv hinj hab).Circ (a 0) x := by
  obtain ⟨i, hi⟩ := hx
  refine (π.repair_circ_a_zero hv hinj hab hdist i).trans ?_
  obtain ⟨n, hn | hn⟩ := (π.circ_iff_exists _ _).1 hi
  · rw [← hn, ← pow_mod_apply_of_pow (π.pow_period (a i))]
    exact π.repair_path hv hinj hab hdist i _ (Nat.mod_lt _ (π.period_pos _))
  · have := π.repair_path hv hinj hab hdist i (n % π.period (a i)) (Nat.mod_lt _ (π.period_pos _))
    rw [pow_mod_apply_of_pow (π.pow_period (a i)), hn] at this
    simpa using this.trans (Circ.symm_dart _ _)

include hdist in
lemma repair_circ_of_not_U {d d' : G.Dart} (hd : ¬ π.U a d) (h : π.Circ d d') :
    (π.repair a hv hinj hab).Circ d d' := by
  have hpow : ∀ n : ℕ, (π.repair a hv hinj hab).Circ d ((π.next ^ n) d) := by
    intro n
    induction n with
    | zero => exact Circ.refl _ _
    | succ n ih =>
      set x := (π.next ^ n) d
      have hx : π.Circ d x := Or.inl ⟨n, by simp [x]⟩
      have hxs : ¬ π.U a x.symm := fun ⟨i, hi⟩ =>
        hd ⟨i, hi.trans ((hx.trans (Circ.symm_dart π x)).symm)⟩
      obtain ⟨h1, h2⟩ := π.other_of_not_U hdist hxs
      have h3 := Circ.pair (π.repair a hv hinj hab) x.symm
      rw [π.repair_pair_other hv hinj hab h1 h2] at h3
      have : (π.next ^ (n + 1)) d = π.pair x.symm := by
        rw [pow_succ', Equiv.Perm.mul_apply, next_apply]
      rw [this]
      exact ih.trans ((Circ.symm_dart _ x).trans h3)
  obtain ⟨n, hn | hn⟩ := (π.circ_iff_exists _ _).1 h
  · rw [← hn]; exact hpow n
  · have := (hpow n).trans (Circ.symm_dart _ _)
    rw [hn] at this; simpa using this

include hdist in
/-- **Lemma 4.** After node `v` re-pairs `(b₀, a₁), …, (b_k, a₀)`, where the pairs `(aᵢ, bᵢ)` lie on
pairwise distinct circuits `C₀, …, C_k`, two darts are on the same circuit iff they were before, or
both lie on `C₀ ∪ … ∪ C_k`: the circuits `C₀, …, C_k` are merged into one circuit and all other
circuits are unchanged. -/
theorem lemma4 (d d' : G.Dart) :
    (π.repair a hv hinj hab).Circ d d' ↔ π.Circ d d' ∨ (π.U a d ∧ π.U a d') := by
  constructor
  · intro h
    by_cases hd : π.U a d
    · -- the set `U` is closed under the new pairing and reversal
      refine Or.inr ⟨hd, Circ.closed (S := {x | π.U a x}) _ ?_ ?_ hd h⟩
      · rintro x ⟨i, hi⟩
        by_cases h1 : ∃ j, x = π.pair (a j)
        · obtain ⟨j, rfl⟩ := h1
          rw [π.repair_pair_b hv hinj hab]; exact ⟨j + 1, Circ.refl _ _⟩
        by_cases h2 : ∃ j, x = a j
        · obtain ⟨j, rfl⟩ := h2
          rw [π.repair_pair_a hv hinj hab]; exact ⟨j - 1, Circ.pair _ _⟩
        push Not at h1 h2
        rw [π.repair_pair_other hv hinj hab h1 h2]
        exact ⟨i, hi.trans (Circ.pair _ _)⟩
      · rintro x ⟨i, hi⟩; exact ⟨i, hi.trans (Circ.symm_dart _ _)⟩
    · refine Or.inl (Circ.closed (S := {x | π.Circ d x}) _ ?_ ?_ (Circ.refl π d) h)
      · intro x hx
        have hxU : ¬ π.U a x := fun ⟨i, hi⟩ => hd ⟨i, hi.trans hx.symm⟩
        obtain ⟨h1, h2⟩ := π.other_of_not_U hdist hxU
        show π.Circ d _
        rw [π.repair_pair_other hv hinj hab h1 h2]
        exact hx.trans (Circ.pair _ _)
      · intro x hx; exact Circ.trans hx (Circ.symm_dart _ _)
  · rintro (h | ⟨hd, hd'⟩)
    · by_cases hd : π.U a d
      · obtain ⟨i, hi⟩ := hd
        exact (π.repair_circ_of_U hv hinj hab hdist ⟨i, hi⟩).symm.trans
          (π.repair_circ_of_U hv hinj hab hdist ⟨i, hi.trans h⟩)
      · exact π.repair_circ_of_not_U hv hinj hab hdist hd h
    · exact (π.repair_circ_of_U hv hinj hab hdist hd).symm.trans
        (π.repair_circ_of_U hv hinj hab hdist hd')

include hdist in
/-- Lemma 4, edge sets: the merged circuit is the union `C₀ ∪ … ∪ C_k`. -/
theorem lemma4_edges :
    (π.repair a hv hinj hab).circuitEdges (a 0) = univ.biUnion (fun i => π.circuitEdges (a i)) := by
  ext e
  simp only [circuitEdges, mem_image, mem_filter, mem_univ, true_and, mem_biUnion]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (π.lemma4 hv hinj hab hdist _ _).1 hx with h | ⟨-, ⟨i, hi⟩⟩
    · exact ⟨0, x, h, rfl⟩
    · exact ⟨i, x, hi, rfl⟩
  · rintro ⟨i, x, hx, rfl⟩
    exact ⟨x, (π.lemma4 hv hinj hab hdist _ _).2 (Or.inr ⟨⟨0, Circ.refl _ _⟩, ⟨i, hx⟩⟩), rfl⟩

include hdist in
/-- Lemma 4: circuits other than `C₀, …, C_k` are unchanged. -/
theorem lemma4_other {d : G.Dart} (hd : ¬ π.U a d) :
    (π.repair a hv hinj hab).circuitEdges d = π.circuitEdges d := by
  ext e
  simp only [circuitEdges, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (π.lemma4 hv hinj hab hdist _ _).1 hx with h | ⟨h, -⟩
    · exact ⟨x, h, rfl⟩
    · exact absurd h hd
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (π.lemma4 hv hinj hab hdist _ _).2 (Or.inl hx), rfl⟩

end Pairing

end Podc.ContentObliviousEulerian
