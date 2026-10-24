import Papers.PODC2021.PPStateComplexity.SmallBasis
import Podc.Foundations.Order.ControlledDickson

/-!
# A general upper bound for protocols with leaders (Section 4)

* `Protocol.ComputesGe.le_of_pump`: the common core of Lemmas 4.1 and 5.2 (pumping inside a
  basis element of `SC`).
* Lemma 4.1 (`lemma_4_1`, with the missing hypothesis `b ≥ 1`), and the variant actually needed in
  the proof of Theorem 4.5 (`lemma_4_1'`: condition 2 replaced by `B + D_a + b·x →* B + D_a + D_b`).
* Lemma 4.2 (`exists_seq`).
* Lemma 4.4 is the cited result of Figueira–Figueira–Schmitz–Schnoebelen; we state the property it
  provides as `CtrlChainProp δ g F` and prove that functions with this property exist
  (`ctrlChainProp_ctrlBound`, by compactness and Dickson's lemma), without the claim that they lie
  at level `F_ω` of the fast-growing hierarchy.
* Theorem 4.5 (`theorem_4_5`): `η < F(n)` for every `F` with `CtrlChainProp ℓ (ϑ + 2) F`;
  unconditional instance `theorem_4_5_ctrlBound`.
-/

namespace Podc.PPStateComplexity

open Cslib Cslib.PopulationProtocol Finset

variable {Q : Type*} [DecidableEq Q]

theorem sum_count_eq_card [Fintype Q] (s : Multiset Q) : ∑ q, s.count q = Multiset.card s := by
  rw [← Multiset.toFinset_sum_count_eq s]
  exact (sum_subset (subset_univ _) fun q _ hq => by
    simp [Multiset.count_eq_zero.2 (by simpa using hq)]).symm

namespace Protocol

variable {P : Protocol Q} {η : ℕ}

/-- **Pumping in a basis element.** If `IC(a + λb) →* B + D_a + λ D_b` for all `λ`, where `(B, S)` is
a basis element of `SC`, `D_a, D_b ∈ ℕ^S`, `a ≥ 2` and `b ≥ 1`, then `η ≤ a`. -/
theorem ComputesGe.le_of_pump [Fintype Q] (h : P.ComputesGe η) {B Da Db : Multiset Q}
    {S : Finset Q} (hB : IsBasisElem P.SC B S) (hDa : ∀ q ∈ Da, q ∈ S) (hDb : ∀ q ∈ Db, q ∈ S)
    {a b : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hreach : ∀ l : ℕ, P.Reach (P.IC (a + l * b)) (B + Da + l • Db)) : η ≤ a := by
  by_contra hlt
  have hsc : P.SC (B + Da + η • Db) := by
    rw [add_assoc]
    exact hB _ fun q hq => by
      rcases Multiset.mem_add.1 hq with hq | hq
      · exact hDa q hq
      · exact hDb q (Multiset.mem_of_mem_nsmul hq)
  rcases hsc with hs | hs
  · have h1 := h.stable_eq (by nlinarith) (hreach η) hs
    have h2 : η ≤ a + η * b := by nlinarith
    rw [eq_comm, decide_eq_false_iff_not] at h1
    exact h1 h2
  · have h0 : P.Stable true (B + Da) := hs.of_le (Multiset.le_add_right _ _)
    have h1 := h.stable_eq ha (by simpa using hreach 0) h0
    rw [eq_comm, decide_eq_true_iff] at h1
    omega

/-- **Lemma 4.1** (with the hypothesis `b ≥ 1`, missing in the paper; see
`lemma_4_1_b_zero_false`). -/
theorem lemma_4_1 [Fintype Q] (h : P.ComputesGe η) {a b : ℕ} {B Da Db : Multiset Q}
    {S : Finset Q} (hB : IsBasisElem P.SC B S) (hDa : ∀ q ∈ Da, q ∈ S) (hDb : ∀ q ∈ Db, q ∈ S)
    (ha : 2 ≤ a) (hb : 1 ≤ b)
    (h1 : P.Reach (P.IC a) (B + Da)) (h2 : P.Reach (Multiset.replicate b P.x) Db) : η ≤ a := by
  refine h.le_of_pump hB hDa hDb ha hb fun l => ?_
  rw [IC_add, ← Multiset.nsmul_replicate]
  exact MReach.add h1 (MReach.nsmul h2 l)

/-- **Lemma 4.1, repaired form** used for Theorem 4.5: condition 2 (`b·x →* D_b`) is replaced by
`B + D_a + b·x →* B + D_a + D_b`, which is what Lemma 4.2 provides. -/
theorem lemma_4_1' [Fintype Q] (h : P.ComputesGe η) {a b : ℕ} {B Da Db : Multiset Q}
    {S : Finset Q} (hB : IsBasisElem P.SC B S) (hDa : ∀ q ∈ Da, q ∈ S) (hDb : ∀ q ∈ Db, q ∈ S)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (h1 : P.Reach (P.IC a) (B + Da))
    (h2 : P.Reach (B + Da + Multiset.replicate b P.x) (B + Da + Db)) : η ≤ a := by
  set R := Multiset.replicate b P.x
  have hpump : ∀ l : ℕ, P.Reach (B + Da + l • R) (B + Da + l • Db) := by
    intro l
    induction l with
    | zero => simpa using (Relation.ReflTransGen.refl : P.Reach (B + Da) (B + Da))
    | succ l ih =>
      have e1 : B + Da + (l + 1) • R = (B + Da + R) + l • R := by rw [succ_nsmul]; abel
      have e2 : (B + Da + Db) + l • R = (B + Da + l • R) + Db := by abel
      have e3 : B + Da + (l + 1) • Db = (B + Da + l • Db) + Db := by rw [succ_nsmul]; abel
      rw [e1, e3]
      exact (MReach.add_right h2 _).trans (e2 ▸ MReach.add_right ih Db)
  refine h.le_of_pump hB hDa hDb ha hb fun l => ?_
  rw [IC_add, ← Multiset.nsmul_replicate]
  exact (MReach.add_right h1 _).trans (hpump l)

/-- The sequence of Lemma 4.2 (indexed from `0`: `seqAux h n` is `C_{n+2}`). -/
noncomputable def seqAux [Fintype Q] (h : P.ComputesGe η) :
    (n : ℕ) → {C : Multiset Q // P.Reach (P.IC (n + 2)) C ∧ P.SC C}
  | 0 =>
    ⟨(h.exists_SC (le_refl 2) .refl).choose, (h.exists_SC (le_refl 2) .refl).choose_spec.1,
      (h.exists_SC (le_refl 2) .refl).choose_spec.2⟩
  | n + 1 =>
    have hr : P.Reach (P.IC (n + 1 + 2)) ((seqAux h n).1 + {P.x}) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, IC_add]
      exact MReach.add_right (seqAux h n).2.1 _
    ⟨(h.exists_SC (by omega) hr).choose, hr.trans (h.exists_SC (by omega) hr).choose_spec.1,
      (h.exists_SC (by omega) hr).choose_spec.2⟩

theorem seqAux_succ [Fintype Q] (h : P.ComputesGe η) (n : ℕ) :
    P.Reach ((seqAux h n).1 + {P.x}) (seqAux h (n + 1)).1 := by
  simp only [seqAux]
  exact Exists.choose_spec (p := fun C' => P.Reach _ C' ∧ P.SC C') _ |>.1

/-- **Lemma 4.2.** There are configurations `C_i ∈ SC` (`i ≥ 2`) with `IC(i) →* C_i` and
`C_i + j·x →* C_{i+j}`. -/
theorem exists_seq [Fintype Q] (h : P.ComputesGe η) :
    ∃ C : ℕ → Multiset Q, ∀ i, 2 ≤ i → P.Reach (P.IC i) (C i) ∧ P.SC (C i) ∧
      ∀ j, P.Reach (C i + Multiset.replicate j P.x) (C (i + j)) := by
  refine ⟨fun i => (seqAux h (i - 2)).1, fun i hi => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine ⟨(seqAux h n).2.1, (seqAux h n).2.2, fun j => ?_⟩
  induction j with
  | zero => simp only [Multiset.replicate_zero, add_zero]; exact .refl
  | succ j ih =>
    have e : n + 2 + (j + 1) - 2 = (n + 2 + j - 2) + 1 := by omega
    rw [e, Multiset.replicate_add, Multiset.replicate_one, ← add_assoc]
    refine (MReach.add_right ih _).trans ?_
    rw [show n + 2 + j - 2 = n + j by omega]
    exact seqAux_succ h (n + j)

end Protocol

/-- The property provided by **Lemma 4.4** (Figueira et al.): every sequence `v₀, v₁, …` of vectors
of `ℕ^d` with `|vᵢ| ≤ i + δ` has an increasing chain `v_{i₀} ≤ … ≤ v_{i_{g(d)}}` with
`i₀ < … < i_{g(d)} ≤ F(d)`. -/
def CtrlChainProp (δ : ℕ) (g F : ℕ → ℕ) : Prop :=
  ∀ d (v : ℕ → Fin d → ℕ), (∀ i, ∑ k, v i k ≤ i + δ) →
    ∃ idx : Fin (g d + 1) → ℕ, StrictMono idx ∧ (∀ k, idx k ≤ F d) ∧ Monotone (v ∘ idx)

theorem le_of_strictMono_fin {m : ℕ} {f : Fin m → ℕ} (hf : StrictMono f) (k : Fin m) :
    (k : ℕ) ≤ f k := by
  obtain ⟨k, hk⟩ := k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := hf (show (⟨k, by omega⟩ : Fin m) < ⟨k + 1, hk⟩ by simp [Fin.lt_def])
    have h2 := ih (by omega)
    simp only at h1 h2 ⊢
    omega

namespace Protocol

variable {P : Protocol Q} {η : ℕ}

/-- **Theorem 4.5.** A protocol with `n` states and `ℓ` leaders computing `x ≥ η` satisfies
`η < F(n)` for every function `F` with the property of Lemma 4.4 for `δ = ℓ` and `g = ϑ + 2`.
(The paper uses `g = ϑ`; the shift by two accounts for the inputs `0, 1`, which are not inputs.) -/
theorem theorem_4_5 [Fintype Q] (h : P.ComputesGe η) {F : ℕ → ℕ}
    (hF : CtrlChainProp (Multiset.card P.L) (fun d => vartheta d + 2) F) :
    η < F (Fintype.card Q) := by
  classical
  obtain ⟨C, hC⟩ := exists_seq h
  obtain ⟨Bs, hcard, hBs, hcov⟩ := exists_small_basis_SC (P := P)
  set d := Fintype.card Q
  let e := Fintype.equivFin Q
  let v : ℕ → Fin d → ℕ := fun i k => if i < 2 then 0 else (C i).count (e.symm k)
  have hv : ∀ i, ∑ k, v i k ≤ i + Multiset.card P.L := by
    intro i
    by_cases hi : i < 2
    · simp [v, hi]
    · simp only [v, hi, if_false]
      rw [Equiv.sum_comp e.symm (fun q => (C i).count q), sum_count_eq_card,
        (hC i (by omega)).1.card_eq, card_IC]
      omega
  obtain ⟨idx, hmono, hle, hv'⟩ := hF d v hv
  have hidx : ∀ k : Fin (vartheta d + 2 + 1), (k : ℕ) ≤ idx k := fun k => le_of_strictMono_fin hmono k
  -- the chain elements with index `≥ 2`
  let j : Fin (vartheta d + 1) → Fin (vartheta d + 2 + 1) := fun m => ⟨m + 2, by omega⟩
  have hj2 : ∀ m, 2 ≤ idx (j m) := fun m => (show 2 ≤ (j m : ℕ) by simp [j]).trans (hidx _)
  have hmem : ∀ m, ∃ p ∈ Bs, InCone p.1 p.2 (C (idx (j m))) :=
    fun m => (hcov _).1 (hC _ (hj2 m)).2.1
  choose f hf hfc using hmem
  obtain ⟨m, m', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m => (⟨f m, hf m⟩ : Bs)) (by rw [Fintype.card_coe, Fintype.card_fin]; omega)
  have heq' : f m = f m' := congrArg Subtype.val heq
  -- order the two indices
  wlog hlt : m < m' generalizing m m'
  · exact this m' m hne.symm heq.symm heq'.symm (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)
  have hjlt : j m < j m' := by rw [Fin.lt_def]; show (m : ℕ) + 2 < m' + 2; omega
  have hilt : idx (j m) < idx (j m') := hmono hjlt
  set a := idx (j m)
  set a' := idx (j m')
  have hCle : C a ≤ C a' := by
    rw [Multiset.le_iff_count]
    intro q
    have := hv' hjlt.le (e q)
    simp only [Function.comp, v, Equiv.symm_apply_apply] at this
    rwa [if_neg (by have := hj2 m; omega), if_neg (by have := hj2 m'; omega)] at this
  obtain ⟨Da, hDa, hCa⟩ := hfc m
  obtain ⟨Da', hDa', hCa'⟩ := hfc m'
  rw [← heq'] at hDa' hCa'
  set B := (f m).1
  set S := (f m).2
  have hBe : IsBasisElem P.SC B S := (hBs _ (hf m)).2
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_le hilt (hle _))
  refine lemma_4_1' (b := a' - a) (Db := C a' - C a) h hBe hDa (fun q hq => ?_) (hj2 m) (by omega)
    (hCa ▸ (hC a (hj2 m)).1) ?_
  · by_contra hqS
    rw [← Multiset.count_pos, Multiset.count_sub] at hq
    have h1 : (C a).count q = B.count q := by
      rw [hCa, Multiset.count_add, Multiset.count_eq_zero.2 (fun h => hqS (hDa q h))]; simp
    have h2 : (C a').count q = B.count q := by
      rw [hCa', Multiset.count_add, Multiset.count_eq_zero.2 (fun h => hqS (hDa' q h))]; simp
    omega
  · rw [← hCa, add_tsub_cancel_of_le hCle]
    have := (hC a (hj2 m)).2.2 (a' - a)
    rwa [Nat.add_sub_cancel' hilt.le] at this

/-- Functions with the property of Lemma 4.4 exist (qualitative Lemma 4.4, via Dickson's lemma and
compactness): the least admissible bound `Cslib.ctrlChainBound`. -/
theorem ctrlChainProp_ctrlChainBound (δ : ℕ) (g : ℕ → ℕ) :
    CtrlChainProp δ g (fun d => Cslib.ctrlChainBound δ (g d) d) :=
  fun d v hv => Cslib.ctrlChainBound_spec δ (g d) d v hv

/-- **Theorem 4.5, unconditional form.** A protocol with `n` states and `ℓ` leaders computing
`x ≥ η` satisfies `η < N(ℓ, n)`, where `N(ℓ, n) = ctrlChainBound ℓ (ϑ(n) + 2) n` depends only on
`ℓ` and `n` (the paper's `F_{ℓ,ϑ}(n)`; that it is at level `F_ω` is the cited part of Lemma 4.4). -/
theorem theorem_4_5_ctrlChainBound [Fintype Q] (h : P.ComputesGe η) :
    η < Cslib.ctrlChainBound (Multiset.card P.L) (vartheta (Fintype.card Q) + 2)
      (Fintype.card Q) :=
  theorem_4_5 (F := fun d => Cslib.ctrlChainBound (Multiset.card P.L) (vartheta d + 2) d) h
    (ctrlChainProp_ctrlChainBound _ (fun d => vartheta d + 2))

end Protocol

end Podc.PPStateComplexity
