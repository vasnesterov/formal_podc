import Papers.PODC2020.TightBipartiteMatching.Problems

/-!
# Lemmas 4.1–4.3: one round-elimination step, followed by a relaxation

Each lemma is proved with `relax_of_meaning`: every new label stands for a set of old labels
(`phiPsi`, `phiPhi`, i.e. the renamings of the paper read backwards), and

* (`hA`, the universal side) every configuration of nonempty sets all of whose choices are allowed
  is enlarged, port by port, to the meaning of one of the listed new configurations. The paper
  does this via maximality and the "strength" diagrams; we construct the new configuration
  directly, by sorting the ports into classes (`exists_perm_classes`);
* (`hP`, the existential side) the existential lift of the old configurations (`Cond.gens_lift`)
  is contained in the new constraint.
-/

namespace TightBipartiteMatching

open Lab Finset

variable {d : ℕ}

/-! ### Generic helpers -/

/-- Sort the ports into three classes `S₂ ⊆ S₁ ⊆ univ`: there is a bijection to positions such that
ports of `S₂` come first and ports of `S₁` before the others. -/
theorem exists_perm_classes {n : ℕ} (S₂ S₁ : Finset (Fin n)) (h : S₂ ⊆ S₁) :
    ∃ σ : Fin n ≃ Fin n, ∀ k, (k ∈ S₂ → (σ k : ℕ) < #S₂) ∧ (k ∈ S₁ → (σ k : ℕ) < #S₁) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_lt_card fun k => if k ∈ S₂ then 2 else if k ∈ S₁ then 1 else 0
  refine ⟨σ, fun k => ⟨fun hk => ?_, fun hk => ?_⟩⟩
  · have := hσ k
    convert this using 2
    ext k'; simp only [mem_filter, mem_univ, true_and, hk, ite_true]
    split_ifs <;> simp_all
  · have := hσ k
    by_cases hk2 : k ∈ S₂
    · exact lt_of_lt_of_le (by simpa [hk2] using (show (σ k : ℕ) < #S₂ from by
        convert this using 2; ext k'; simp only [mem_filter, mem_univ, true_and, hk2, ite_true]
        split_ifs <;> simp_all)) (card_le_card h)
    · convert this using 2
      ext k'
      have := @h k'
      simp only [mem_filter, mem_univ, true_and, hk2, hk, ite_true, ite_false]
      split_ifs with h1 h2 <;> simp_all

/-- Threshold labelling of positions. -/
def thr {L : Type*} (n₁ n₂ : ℕ) (ℓ₁ ℓ₂ ℓ₃ : L) (p : ℕ) : L :=
  if p < n₁ then ℓ₁ else if p < n₁ + n₂ then ℓ₂ else ℓ₃

theorem mset_thr {L : Type*} (n₁ n₂ n₃ : ℕ) (hn : n₁ + n₂ + n₃ = d + 1) (ℓ₁ ℓ₂ ℓ₃ : L)
    (σ : Fin (d + 1) ≃ Fin (d + 1)) :
    mset (fun k => thr n₁ n₂ ℓ₁ ℓ₂ ℓ₃ (σ k)) =
      Multiset.replicate n₁ ℓ₁ + Multiset.replicate n₂ ℓ₂ + Multiset.replicate n₃ ℓ₃ := by
  rw [mset_threshold, ← hn]
  exact map_range_threshold3 n₁ n₂ n₃ ℓ₁ ℓ₂ ℓ₃

theorem gen3_replicate {L : Type*} (ℓ₁ ℓ₂ ℓ₃ : L) (n₁ n₂ n₃ : ℕ) :
    Multiset.replicate n₁ ℓ₁ + Multiset.replicate n₂ ℓ₂ + Multiset.replicate n₃ ℓ₃ ∈
      Cond.Gen [({ℓ₁}, n₁), ({ℓ₂}, n₂), ({ℓ₃}, n₃)] := by
  have := Cond.replicate_mem_gen [(ℓ₁, n₁), (ℓ₂, n₂), (ℓ₃, n₃)]
  simpa [add_assoc] using this

theorem card_le_count {n : ℕ} (f : Fin n → Lab) (S : Finset (Fin n)) (ℓ : Lab)
    (h : ∀ k ∈ S, f k = ℓ) : #S ≤ (mset f).count ℓ := by
  rw [count_mset]
  exact card_le_card fun k hk => by simp only [mem_filter, mem_univ, true_and]; exact h k hk

theorem card_le_count2 {n : ℕ} (f : Fin n → Lab) (S : Finset (Fin n)) (ℓ₁ ℓ₂ : Lab)
    (h : ∀ k ∈ S, f k = ℓ₁ ∨ f k = ℓ₂) : #S ≤ (mset f).count ℓ₁ + (mset f).count ℓ₂ := by
  rw [count_mset, count_mset]
  refine le_trans (card_le_card fun k hk => ?_) (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union]
  exact h k hk

theorem count_mset_eq_zero {n : ℕ} (f : Fin n → Lab) (ℓ : Lab) (h : ∀ k, f k ≠ ℓ) :
    (mset f).count ℓ = 0 := by
  rw [count_mset]; simp [h]

theorem card_add_card_le {n : ℕ} (S T : Finset (Fin n)) (h : Disjoint S T) : #S + #T ≤ n := by
  rw [← card_union_of_disjoint h]
  exact (card_le_univ _).trans (by simp)

theorem gen2_replicate {L : Type*} (ℓ₁ ℓ₂ : L) (n₁ n₂ : ℕ) :
    Multiset.replicate n₁ ℓ₁ + Multiset.replicate n₂ ℓ₂ ∈ Cond.Gen [({ℓ₁}, n₁), ({ℓ₂}, n₂)] := by
  have := Cond.replicate_mem_gen [(ℓ₁, n₁), (ℓ₂, n₂)]
  simpa using this

/-- Choose, wherever possible, a given label. -/
theorem exists_choice1 {n : ℕ} {g : Fin n → Set Lab} (hne : ∀ k, (g k).Nonempty)
    (S : Finset (Fin n)) (ℓ : Lab) (hS : ∀ k ∈ S, ℓ ∈ g k) :
    ∃ f : Fin n → Lab, (∀ k, f k ∈ g k) ∧ #S ≤ (mset f).count ℓ := by
  classical
  let f : Fin n → Lab := fun k => if ℓ ∈ g k then ℓ else (hne k).some
  refine ⟨f, fun k => ?_, card_le_count f S ℓ fun k hk => ?_⟩
  · simp only [f]; split_ifs with h1
    exacts [h1, (hne k).some_mem]
  · simp only [f]; simp [hS k hk]

/-! ### Meanings of the new labels -/

/-- The renaming of Lemmas 4.1 and 4.3, read backwards: `Z = {X}`, `P = {O, X}`, `O = {P, O, X}`,
`M = {M, X}`, `X = {M, Z, P, O, X}`. -/
def phiPsi : Lab → Set Lab
  | .Z => {X}
  | .P => {O, X}
  | .O => {P, O, X}
  | .M => {M, X}
  | .X => Set.univ

/-- The renaming of Lemma 4.2, read backwards: `M = {M}`, `P = {O, X}`, `O = {P, O, X}`,
`X = {M, P, O, X}` (`Z` is not used). -/
def phiPhi : Lab → Set Lab
  | .M => {M}
  | .P => {O, X}
  | .O => {P, O, X}
  | .X => {M, P, O, X}
  | .Z => ∅

theorem gens_mono {cs cs' : List (Cond Lab)}
    (h : List.Forall₂ (fun c c' : Cond Lab =>
      List.Forall₂ (fun b b' : Set Lab × ℕ => b.1 ⊆ b'.1 ∧ b.2 = b'.2) c c') cs cs')
    {m : Multiset Lab} (hm : m ∈ Cond.Gens cs) : m ∈ Cond.Gens cs' := by
  induction h with
  | nil => obtain ⟨c, hc, -⟩ := hm; simp at hc
  | @cons c c' cs cs' hcc _ ih =>
    obtain ⟨c₀, hc₀, hm⟩ := hm
    rcases List.mem_cons.1 hc₀ with rfl | hc₀
    · exact ⟨c', List.mem_cons_self .., Cond.gen_mono hcc hm⟩
    · obtain ⟨c₁, hc₁, hm₁⟩ := ih ⟨c₀, hc₀, hm⟩
      exact ⟨c₁, List.mem_cons_of_mem _ hc₁, hm₁⟩

/-! ### Lemma 4.1 -/

section Lemma41

variable {a b c : ℕ}

/-- The universal side of Lemma 4.1. -/
theorem lemma_4_1_univ (ha : 1 ≤ a) (ha' : a ≤ d) (g : Fin (d + 1) → Set Lab)
    (hg : mset g ∈ univC (Psi d a b c).B) :
    ∃ g' : Fin (d + 1) → Lab, mset g' ∈ (Psi d a (min (c + a) (d + 1 - a)) b).W ∧
      ∀ k, g k ⊆ phiPsi (g' k) := by
  classical
  obtain ⟨hne, hall⟩ := mset_mem_univC.1 hg
  set dd := min (c + a) (d + 1 - a)
  -- the ports whose set contains `M` or `Z`
  set MZ : Finset (Fin (d + 1)) := {k | M ∈ g k ∨ Z ∈ g k} with hMZ
  have hMZa : #MZ ≤ a := by
    let f : Fin (d + 1) → Lab := fun k =>
      if M ∈ g k then M else if Z ∈ g k then Z else (hne k).some
    have hf : ∀ k, f k ∈ g k := fun k => by
      simp only [f]; split_ifs with h1 h2
      exacts [h1, h2, (hne k).some_mem]
    have h1 := (psi_B_counts ha (hall f hf)).1
    have h2 := card_le_count2 f MZ M Z fun k hk => by
      simp only [hMZ, mem_filter, mem_univ, true_and] at hk
      simp only [f]; split_ifs with h1 h2 <;> simp_all
    omega
  have hsubPOX : ∀ k, k ∉ MZ → g k ⊆ {P, O, X} := fun k hk ℓ hℓ => by
    simp only [hMZ, mem_filter, mem_univ, true_and, not_or] at hk
    cases ℓ <;> simp_all
  by_cases hA : ∃ k₀, g k₀ ⊆ {M, X} ∧ M ∈ g k₀
  · -- Case `M X ∈ C`: extend to `X^{a-1} M O^{Δ-a}`
    obtain ⟨k₀, hk₀, hk₀M⟩ := hA
    have hk₀MZ : k₀ ∈ MZ := by simp [hMZ, hk₀M]
    obtain ⟨σ, hσ⟩ := exists_perm_classes {k₀} MZ (by simpa using hk₀MZ)
    have hσ₀ : (σ k₀ : ℕ) = 0 := by have := (hσ k₀).1 (by simp); simpa using this
    refine ⟨fun k => thr 1 (a - 1) M X O (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr 1 (a - 1) (d + 1 - a) (by omega)]
      have := gen3_replicate X M O (a - 1) 1 (d + 1 - a)
      exact ⟨_, List.mem_cons_self .., by convert this using 1; abel⟩
    · by_cases hk : k = k₀
      · subst hk; simp only [thr, hσ₀, zero_lt_one, ite_true]; exact hk₀
      · have hne' : (σ k : ℕ) ≠ 0 := fun h => hk (σ.injective (Fin.ext (h.trans hσ₀.symm)))
        by_cases hkMZ : k ∈ MZ
        · have := (hσ k).2 hkMZ
          simp only [thr]; split_ifs <;> first | omega | simp [phiPsi]
        · simp only [thr]
          split_ifs
          · omega
          · simp [phiPsi]
          · exact hsubPOX k hkMZ
  by_cases hB : ∃ k₀, g k₀ ⊆ {X}
  · -- Case `X ∈ C`: extend to `X^a Z O^{Δ-a-1}`
    obtain ⟨k₀, hk₀⟩ := hB
    have hk₀MZ : k₀ ∉ MZ := by
      simp only [hMZ, mem_filter, mem_univ, true_and, not_or]
      exact ⟨fun h => by simpa using hk₀ h, fun h => by simpa using hk₀ h⟩
    obtain ⟨σ, hσ⟩ := exists_perm_classes {k₀} (insert k₀ MZ) (by simp)
    have hσ₀ : (σ k₀ : ℕ) = 0 := by have := (hσ k₀).1 (by simp); simpa using this
    have hcard : #(insert k₀ MZ) ≤ a + 1 := by rw [card_insert_of_notMem hk₀MZ]; omega
    refine ⟨fun k => thr 1 a Z X O (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr 1 a (d + 1 - a - 1) (by omega)]
      have := gen3_replicate X Z O a 1 (d + 1 - a - 1)
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
      convert this using 1; abel
    · by_cases hk : k = k₀
      · subst hk; simp only [thr, hσ₀, zero_lt_one, ite_true]; exact hk₀
      · have hne' : (σ k : ℕ) ≠ 0 := fun h => hk (σ.injective (Fin.ext (h.trans hσ₀.symm)))
        by_cases hkMZ : k ∈ MZ
        · have := (hσ k).2 (mem_insert_of_mem hkMZ)
          simp only [thr]; split_ifs <;> first | omega | simp [phiPsi]
        · simp only [thr]
          split_ifs
          · omega
          · simp [phiPsi]
          · exact hsubPOX k hkMZ
  · -- Case: every set contains `Z`, `P` or `O`: extend to `X^a O^dd P^{Δ-a-dd}`
    push_neg at hA hB
    have hZPO : ∀ k, Z ∈ g k ∨ P ∈ g k ∨ O ∈ g k := by
      intro k
      obtain ⟨ℓ, hℓ, hℓ'⟩ := Set.not_subset.1 (show ¬ g k ⊆ {M, X} from fun h => by
        obtain ⟨ℓ, hℓ⟩ := hne k
        by_cases hM : M ∈ g k
        · exact hA k h hM
        · exact hB k fun ℓ' hℓ' => by
            have := h hℓ'; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
            rcases this with rfl | rfl
            · exact absurd hℓ' hM
            · rfl)
      cases ℓ <;> simp_all
    set PP : Finset (Fin (d + 1)) := {k | P ∈ g k} with hPP
    have hZP : #(MZ ∪ PP) ≤ a + dd := by
      -- choose `Z`, else `P`, else `O`
      let f : Fin (d + 1) → Lab := fun k => if Z ∈ g k then Z else if P ∈ g k then P else O
      have hf : ∀ k, f k ∈ g k := fun k => by
        simp only [f]; split_ifs with h1 h2
        · exact h1
        · exact h2
        · rcases hZPO k with h | h | h
          exacts [absurd h h1, absurd h h2, h]
      have hc := psi_B_counts ha (hall f hf)
      have hM0 : (mset f).count M = 0 :=
        count_mset_eq_zero f M fun k => by simp only [f]; split_ifs <;> simp
      have hX0 : (mset f).count X = 0 :=
        count_mset_eq_zero f X fun k => by simp only [f]; split_ifs <;> simp
      set ZP : Finset (Fin (d + 1)) := {k | Z ∈ g k ∨ P ∈ g k} with hZPdef
      set Q : Finset (Fin (d + 1)) := {k | ¬ (M ∈ g k ∨ Z ∈ g k) ∧ P ∈ g k} with hQ
      have hZPc := card_le_count2 f ZP Z P fun k hk => by
        simp only [hZPdef, mem_filter, mem_univ, true_and] at hk
        simp only [f]; split_ifs with h1 h2 <;> simp_all
      -- `MZ ∪ PP` splits into `MZ` and the ports with `P` but neither `M` nor `Z`
      have hdisj : Disjoint MZ Q := by
        rw [hMZ, hQ, disjoint_filter]; exact fun k _ h h' => h'.1 h
      have hsplit : #(MZ ∪ PP) = #MZ + #Q := by
        rw [← card_union_of_disjoint hdisj]
        congr 1; ext k; simp only [hMZ, hPP, hQ, mem_union, mem_filter, mem_univ, true_and]; tauto
      have hsub : #Q ≤ #ZP :=
        card_le_card fun k hk => by
          simp only [hQ, hZPdef, mem_filter, mem_univ, true_and] at hk ⊢; tauto
      have hdis := card_add_card_le MZ Q hdisj
      have hdd : dd = min (c + a) (d + 1 - a) := rfl
      omega
    obtain ⟨σ, hσ⟩ := exists_perm_classes MZ (MZ ∪ PP) subset_union_left
    refine ⟨fun k => thr a dd X O P (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr a dd (d + 1 - a - dd) (by omega)]
      have := gen3_replicate X O P a dd (d + 1 - a - dd)
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), this⟩
    · by_cases hkMZ : k ∈ MZ
      · have := (hσ k).1 hkMZ
        simp only [thr]; split_ifs <;> first | omega | simp [phiPsi]
      · have hPOX := hsubPOX k hkMZ
        by_cases hkP : k ∈ PP
        · have := (hσ k).2 (mem_union_right _ hkP)
          simp only [thr]
          split_ifs
          · simp [phiPsi]
          · exact hPOX
          · omega
        · have hOX : g k ⊆ {O, X} := fun ℓ hℓ => by
            have := hPOX hℓ
            simp only [hPP, mem_filter, mem_univ, true_and] at hkP
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
            rcases this with rfl | rfl | rfl
            · exact absurd hℓ hkP
            · simp
            · simp
          simp only [thr]
          split_ifs
          · simp [phiPsi]
          · exact hPOX
          · exact hOX

/-- The existential side of Lemma 4.1. -/
theorem lemma_4_1_ex (g' : Fin (d + 1) → Lab)
    (h : ∃ f : Fin (d + 1) → Lab, (∀ k, f k ∈ phiPsi (g' k)) ∧ mset f ∈ (Psi d a b c).W) :
    mset g' ∈ (Psi d a (min (c + a) (d + 1 - a)) b).B := by
  obtain ⟨f, hf, hW⟩ := h
  have := Cond.gens_lift (R := fun x y => x ∈ phiPsi y) hW (rel_mset_of hf)
  refine gens_mono ?_ this
  simp only [Cond.lift, List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil,
    and_true]
  repeat' constructor
  all_goals
    intro y hy
    cases y <;> simp_all [phiPsi]

/-- **Lemma 4.1.** For `Δ ≥ 2` and `1 ≤ a ≤ Δ - 1`, the problem `Ψ^B_Δ(a, d', b)` with
`d' = min{c + a, Δ - a}` is a black relaxation of `R_B(Ψ^W_Δ(a, b, c))`. (The hypotheses
`b, c ≤ Δ - a` of the paper are not needed.) -/
theorem lemma_4_1 (ha : 1 ≤ a) (ha' : a ≤ d) :
    (RB (Psi d a b c)).BlackRelax d (Psi d a (min (c + a) (d + 1 - a)) b).swap :=
  relax_of_meaning phiPsi (lemma_4_1_univ ha ha') lemma_4_1_ex

end Lemma41

/-! ### Lemma 4.2 -/

section Lemma42

variable {x y : ℕ}

/-- The universal side of Lemma 4.2. -/
theorem lemma_4_2_univ (hy : 1 ≤ y) (hy' : y ≤ d) (g : Fin (d + 1) → Set Lab)
    (hg : mset g ∈ univC (Phi d x y).B) :
    ∃ g' : Fin (d + 1) → Lab, mset g' ∈ (Phi' d x y).B ∧ ∀ k, g k ⊆ phiPhi (g' k) := by
  classical
  obtain ⟨hne, hall⟩ := mset_mem_univC.1 hg
  -- no set contains `Z`
  have hZ : ∀ k, Z ∉ g k := by
    intro k₀ hk₀
    obtain ⟨f, hf, hc⟩ := exists_choice1 hne {k₀} Z (by simpa using hk₀)
    have := (phi_B_counts hy (hall f hf)).1
    simp at hc; omega
  set MM : Finset (Fin (d + 1)) := {k | M ∈ g k} with hMM
  have hMMy : #MM ≤ y := by
    obtain ⟨f, hf, hc⟩ := exists_choice1 hne MM M (by simp [hMM])
    have := (phi_B_counts hy (hall f hf)).2.1
    omega
  have hsubMPOX : ∀ k, g k ⊆ {M, P, O, X} := fun k ℓ hℓ => by
    cases ℓ <;> simp_all
  have hsubPOX : ∀ k, k ∉ MM → g k ⊆ {P, O, X} := fun k hk ℓ hℓ => by
    simp only [hMM, mem_filter, mem_univ, true_and] at hk
    cases ℓ <;> simp_all
  by_cases hA : ∃ k₀, g k₀ ⊆ {M}
  · -- Case `M ∈ C`: extend to `X^{y-1} M O^{Δ-y}`
    obtain ⟨k₀, hk₀⟩ := hA
    have hk₀MM : k₀ ∈ MM := by
      obtain ⟨ℓ, hℓ⟩ := hne k₀
      have := hk₀ hℓ; simp only [Set.mem_singleton_iff] at this; subst this
      simp [hMM, hℓ]
    obtain ⟨σ, hσ⟩ := exists_perm_classes {k₀} MM (by simpa using hk₀MM)
    have hσ₀ : (σ k₀ : ℕ) = 0 := by have := (hσ k₀).1 (by simp); simpa using this
    refine ⟨fun k => thr 1 (y - 1) M X O (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr 1 (y - 1) (d + 1 - y) (by omega)]
      have := gen3_replicate X M O (y - 1) 1 (d + 1 - y)
      exact ⟨_, List.mem_cons_self .., by convert this using 1; abel⟩
    · by_cases hk : k = k₀
      · subst hk; simp only [thr, hσ₀, zero_lt_one, ite_true]; exact hk₀
      · have hne' : (σ k : ℕ) ≠ 0 := fun h => hk (σ.injective (Fin.ext (h.trans hσ₀.symm)))
        by_cases hkMM : k ∈ MM
        · have := (hσ k).2 hkMM
          simp only [thr]; split_ifs <;> first | omega | exact hsubMPOX k
        · simp only [thr]
          split_ifs
          · omega
          · exact hsubMPOX k
          · exact hsubPOX k hkMM
  · -- Case: no set is `{M}`: then no set contains `P`; extend to `X^y P^{Δ-y}`
    push_neg at hA
    have hP : ∀ k, P ∉ g k := by
      intro k₀ hk₀
      have hnM : ∀ k, ∃ ℓ ∈ g k, ℓ ≠ M := fun k => by
        obtain ⟨ℓ, hℓ, hℓ'⟩ := Set.not_subset.1 (hA k)
        exact ⟨ℓ, hℓ, by simpa using hℓ'⟩
      choose e he he' using hnM
      let f : Fin (d + 1) → Lab := fun k => if k = k₀ then P else e k
      have hf : ∀ k, f k ∈ g k := fun k => by
        simp only [f]; split_ifs with h
        · subst h; exact hk₀
        · exact he k
      have hc := (phi_B_counts hy (hall f hf)).2.2
      have hM0 : (mset f).count M = 0 := count_mset_eq_zero f M fun k => by
        simp only [f]; split_ifs
        · simp
        · exact he' k
      have hP1 : 1 ≤ (mset f).count P := by
        have := card_le_count f {k₀} P (by simp [f])
        simpa using this
      omega
    obtain ⟨σ, hσ⟩ := exists_perm_classes MM MM subset_rfl
    refine ⟨fun k => thr y (d + 1 - y) X P P (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr y (d + 1 - y) 0 (by omega)]
      have := gen2_replicate X P y (d + 1 - y)
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simpa using this⟩
    · by_cases hkMM : k ∈ MM
      · have := (hσ k).1 hkMM
        simp only [thr]; split_ifs <;> first | omega | exact hsubMPOX k
      · have hOX : g k ⊆ {O, X} := fun ℓ hℓ => by
          have := hsubPOX k hkMM hℓ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
          rcases this with rfl | rfl | rfl
          · exact absurd hℓ (hP k)
          · simp
          · simp
        simp only [thr]
        split_ifs
        · exact hsubMPOX k
        · exact hOX
        · exact hOX

/-- The existential side of Lemma 4.2. -/
theorem lemma_4_2_ex (g' : Fin (d + 1) → Lab)
    (h : ∃ f : Fin (d + 1) → Lab, (∀ k, f k ∈ phiPhi (g' k)) ∧ mset f ∈ (Phi d x y).W) :
    mset g' ∈ (Phi' d x y).W := by
  obtain ⟨f, hf, hW⟩ := h
  have := Cond.gens_lift (R := fun x y => x ∈ phiPhi y) hW (rel_mset_of hf)
  refine gens_mono ?_ this
  simp only [Cond.lift, List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil,
    and_true]
  repeat' constructor
  all_goals
    intro y hy
    cases y <;> simp_all [phiPhi]

/-- **Lemma 4.2.** For `Δ ≥ 2`, `0 ≤ x ≤ Δ` and `1 ≤ y ≤ Δ - 1`, the problem `Φ'(x, y)` is a black
relaxation of `R_B(Φ^W_Δ(x, y))`. -/
theorem lemma_4_2 (hy : 1 ≤ y) (hy' : y ≤ d) :
    (RB (Phi d x y)).BlackRelax d (Phi' d x y) :=
  relax_of_meaning phiPhi (lemma_4_2_univ hy hy') lemma_4_2_ex

end Lemma42

/-! ### Lemma 4.3 -/

section Lemma43

variable {x y : ℕ}

/-- The universal side of Lemma 4.3. -/
theorem lemma_4_3_univ (hy : 1 ≤ y) (hy' : y ≤ d) (g : Fin (d + 1) → Set Lab)
    (hg : mset g ∈ univC (Phi' d x y).W) :
    ∃ g' : Fin (d + 1) → Lab, mset g' ∈ (Psi d y (min x (d + 1 - y)) 0).W ∧
      ∀ k, g k ⊆ phiPsi (g' k) := by
  classical
  obtain ⟨hne, hall⟩ := mset_mem_univC.1 hg
  set x' := min x (d + 1 - y) with hx'
  have hZ : ∀ k, Z ∉ g k := by
    intro k₀ hk₀
    obtain ⟨f, hf, hc⟩ := exists_choice1 hne {k₀} Z (by simpa using hk₀)
    have := (phi'_W_counts hy (hall f hf)).1
    simp at hc; omega
  set MM : Finset (Fin (d + 1)) := {k | M ∈ g k} with hMM
  have hMMy : #MM ≤ y := by
    obtain ⟨f, hf, hc⟩ := exists_choice1 hne MM M (by simp [hMM])
    have := (phi'_W_counts hy (hall f hf)).2.1
    omega
  have hsubPOX : ∀ k, k ∉ MM → g k ⊆ {P, O, X} := fun k hk ℓ hℓ => by
    simp only [hMM, mem_filter, mem_univ, true_and] at hk
    cases ℓ <;> simp_all
  by_cases hA : ∃ k₀, g k₀ ⊆ {M, X} ∧ M ∈ g k₀
  · -- extend to `X^{y-1} M O^{Δ-y}`
    obtain ⟨k₀, hk₀, hk₀M⟩ := hA
    have hk₀MM : k₀ ∈ MM := by simp [hMM, hk₀M]
    obtain ⟨σ, hσ⟩ := exists_perm_classes {k₀} MM (by simpa using hk₀MM)
    have hσ₀ : (σ k₀ : ℕ) = 0 := by have := (hσ k₀).1 (by simp); simpa using this
    refine ⟨fun k => thr 1 (y - 1) M X O (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr 1 (y - 1) (d + 1 - y) (by omega)]
      have := gen3_replicate X M O (y - 1) 1 (d + 1 - y)
      exact ⟨_, List.mem_cons_self .., by convert this using 1; abel⟩
    · by_cases hk : k = k₀
      · subst hk; simp only [thr, hσ₀, zero_lt_one, ite_true]; exact hk₀
      · have hne' : (σ k : ℕ) ≠ 0 := fun h => hk (σ.injective (Fin.ext (h.trans hσ₀.symm)))
        by_cases hkMM : k ∈ MM
        · have := (hσ k).2 hkMM
          simp only [thr]; split_ifs <;> first | omega | simp [phiPsi]
        · simp only [thr]
          split_ifs
          · omega
          · simp [phiPsi]
          · exact hsubPOX k hkMM
  by_cases hB : ∃ k₀, g k₀ ⊆ {X}
  · -- extend to `X^y Z O^{Δ-y-1}`
    obtain ⟨k₀, hk₀⟩ := hB
    have hk₀MM : k₀ ∉ MM := by
      simp only [hMM, mem_filter, mem_univ, true_and]
      exact fun h => by simpa using hk₀ h
    obtain ⟨σ, hσ⟩ := exists_perm_classes {k₀} (insert k₀ MM) (by simp)
    have hσ₀ : (σ k₀ : ℕ) = 0 := by have := (hσ k₀).1 (by simp); simpa using this
    have hcard : #(insert k₀ MM) ≤ y + 1 := by rw [card_insert_of_notMem hk₀MM]; omega
    refine ⟨fun k => thr 1 y Z X O (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr 1 y (d + 1 - y - 1) (by omega)]
      have := gen3_replicate X Z O y 1 (d + 1 - y - 1)
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
      convert this using 1; abel
    · by_cases hk : k = k₀
      · subst hk; simp only [thr, hσ₀, zero_lt_one, ite_true]; exact hk₀
      · have hne' : (σ k : ℕ) ≠ 0 := fun h => hk (σ.injective (Fin.ext (h.trans hσ₀.symm)))
        by_cases hkMM : k ∈ MM
        · have := (hσ k).2 (mem_insert_of_mem hkMM)
          simp only [thr]; split_ifs <;> first | omega | simp [phiPsi]
        · simp only [thr]
          split_ifs
          · omega
          · simp [phiPsi]
          · exact hsubPOX k hkMM
  · -- every set contains `P` or `O`: extend to `X^y O^{x'} P^{Δ-y-x'}`
    push_neg at hA hB
    have hPO : ∀ k, P ∈ g k ∨ O ∈ g k := by
      intro k
      obtain ⟨ℓ, hℓ, hℓ'⟩ := Set.not_subset.1 (show ¬ g k ⊆ {M, X} from fun h => by
        by_cases hM : M ∈ g k
        · exact hA k h hM
        · exact hB k fun ℓ' hℓ' => by
            have := h hℓ'; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
            rcases this with rfl | rfl
            · exact absurd hℓ' hM
            · rfl)
      cases ℓ <;> simp_all
    set PP : Finset (Fin (d + 1)) := {k | P ∈ g k} with hPP
    have hPPx : #PP ≤ x := by
      let f : Fin (d + 1) → Lab := fun k => if P ∈ g k then P else O
      have hf : ∀ k, f k ∈ g k := fun k => by
        simp only [f]; split_ifs with h1
        · exact h1
        · exact (hPO k).resolve_left h1
      have hc := (phi'_W_counts hy (hall f hf)).2.2
      have hM0 : (mset f).count M = 0 :=
        count_mset_eq_zero f M fun k => by simp only [f]; split_ifs <;> simp
      have hX0 : (mset f).count X = 0 :=
        count_mset_eq_zero f X fun k => by simp only [f]; split_ifs <;> simp
      have := card_le_count f PP P fun k hk => by
        simp only [hPP, mem_filter, mem_univ, true_and] at hk; simp [f, hk]
      omega
    have hU : #(MM ∪ PP) ≤ y + x' := by
      have h1 := card_union_le MM PP
      have h2 : #(MM ∪ PP) ≤ d + 1 := (card_le_univ _).trans (by simp)
      omega
    obtain ⟨σ, hσ⟩ := exists_perm_classes MM (MM ∪ PP) subset_union_left
    refine ⟨fun k => thr y x' X O P (σ k), ?_, fun k => ?_⟩
    · rw [mset_thr y x' (d + 1 - y - x') (by omega)]
      have := gen3_replicate X O P y x' (d + 1 - y - x')
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), this⟩
    · by_cases hkMM : k ∈ MM
      · have := (hσ k).1 hkMM
        simp only [thr]; split_ifs <;> first | omega | simp [phiPsi]
      · have hPOX := hsubPOX k hkMM
        by_cases hkP : k ∈ PP
        · have := (hσ k).2 (mem_union_right _ hkP)
          simp only [thr]
          split_ifs
          · simp [phiPsi]
          · exact hPOX
          · omega
        · have hOX : g k ⊆ {O, X} := fun ℓ hℓ => by
            have := hPOX hℓ
            simp only [hPP, mem_filter, mem_univ, true_and] at hkP
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
            rcases this with rfl | rfl | rfl
            · exact absurd hℓ hkP
            · simp
            · simp
          simp only [thr]
          split_ifs
          · simp [phiPsi]
          · exact hPOX
          · exact hOX

/-- The existential side of Lemma 4.3 (including the added black configuration
`[ZMPOX]^y [X] [POX]^{Δ-y-1}`). -/
theorem lemma_4_3_ex (g' : Fin (d + 1) → Lab)
    (h : ∃ f : Fin (d + 1) → Lab, (∀ k, f k ∈ phiPsi (g' k)) ∧ mset f ∈ (Phi' d x y).B) :
    mset g' ∈ (Psi d y (min x (d + 1 - y)) 0).B := by
  obtain ⟨f, hf, hB⟩ := h
  obtain ⟨c, hc, hm⟩ := Cond.gens_lift (R := fun x y => x ∈ phiPsi y) hB (rel_mset_of hf)
  simp only [Phi', List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine ⟨_, List.mem_cons_self .., Cond.gen_mono ?_ hm⟩
    simp only [Cond.lift, List.map_cons, List.map_nil, List.forall₂_cons, List.Forall₂.nil,
      and_true]
    repeat' constructor
    all_goals
      intro y hy
      cases y <;> simp_all [phiPsi]
  · -- the lifted `X^y P^{Δ-y}` is `[ZMPOX]^y [OX]^{Δ-y}`: the second configuration with `c = 0`
    refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    obtain ⟨m₁, r, hr, h1, h2, hrr⟩ := Cond.gen_cons.1 hm
    obtain ⟨m₂, r₂, hr₂, h1₂, h2₂, hrr₂⟩ := Cond.gen_cons.1 hrr
    simp only [List.map_nil, Cond.gen_nil] at hrr₂; subst hrr₂
    refine Cond.gen_cons.2 ⟨m₁, m₂, by simp [hr, hr₂], h1, fun _ _ => Set.mem_univ _, ?_⟩
    refine Cond.gen_cons.2 ⟨0, m₂, by simp, by simp, by simp, ?_⟩
    refine Cond.gen_cons.2 ⟨m₂, 0, by simp, by simpa using h1₂, fun z hz => ?_, by simp⟩
    have := h2₂ z hz
    cases z <;> simp_all [phiPsi]

/-- **Lemma 4.3.** For `Δ ≥ 2`, `0 ≤ x ≤ Δ` and `1 ≤ y ≤ Δ - 1`, the problem
`Ψ^W_Δ(y, min{x, Δ - y}, 0)` is a white relaxation of `R_W(Φ'(x, y))`. The paper writes
`Ψ^W_Δ(y, x, 0)`, which is not a member of the family when `x > Δ - y` (its definition needs
`a + b ≤ Δ`); for `x ≤ Δ - y` the two coincide. -/
theorem lemma_4_3 (hy : 1 ≤ y) (hy' : y ≤ d) :
    (RW (Phi' d x y)).WhiteRelax d (Psi d y (min x (d + 1 - y)) 0) :=
  relax_of_meaning phiPsi (lemma_4_3_univ hy hy') lemma_4_3_ex

end Lemma43

end TightBipartiteMatching
