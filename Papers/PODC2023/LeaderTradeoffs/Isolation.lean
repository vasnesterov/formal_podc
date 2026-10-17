import Papers.PODC2023.LeaderTradeoffs.Glue

-- CSLib candidate

/-!
# Isolated ID sets (repaired Definition 3.5, Lemma 3.6, Corollary 3.7)

`Isolable A T X`: the nodes with IDs in `X` can run for `T` rounds without ever sending a message
outside `X`, i.e. there is a partial port mapping on `X` under which the restricted execution
prefix of `X` is defined for `T` rounds. This is the repaired version of "`X` forms terminating
components" (Definition 3.5): the paper's definition quantifies over *all* restricted execution
prefixes in `Exec_r(X)` and is vacuously true when `Exec_r(X)` is empty
(see `Counterexamples.lean`); the proof of Lemma 3.6 uses the existential reading.

* `not_disjoint_isolable` (Lemma 3.6): if `n = s · N` with `N ≥ 2`, there are no `N + 1` pairwise
  disjoint isolable `s`-subsets of the ID universe.
* `exists_universe_no_isolable` (Corollary 3.7): removing at most `n` IDs per size leaves an ID
  universe without isolable sets of the given sizes.
-/

open Classical Finset Function

namespace LeaderTradeoffs

variable {m : ℕ}

/-- The ID set `X` can run in isolation for `T` rounds (repaired Definition 3.5). -/
def Isolable (A : Algorithm m) (T : ℕ) (X : Finset ℕ) : Prop :=
  ∃ q : PortMap m, WF q X ∧ Valid A q T X

/-- **Lemma 3.6** (repaired). If `n = m + 1 = s · N` with `N ≥ 2`, then among `N + 1` pairwise
disjoint `s`-subsets of the ID universe at least one cannot run in isolation for `T` rounds. -/
theorem not_disjoint_isolable {A : Algorithm m} {U : Finset ℕ} {T : ℕ} (hA : ElectsBy A U T)
    {s N : ℕ} (hsN : s * N = m + 1) (hN : 2 ≤ N) (X : Fin (N + 1) → Finset ℕ)
    (hdisj : Pairwise (Disjoint on X)) (hsub : ∀ a, X a ⊆ U) (hcard : ∀ a, (X a).card = s)
    (hiso : ∀ a, Isolable A T (X a)) : False := by
  choose q hq using hiso
  -- number of leaders of block `a` in its isolated execution
  let c : Fin (N + 1) → ℕ := fun a =>
    ((X a).filter fun u => A.output (run A (q a) T u) = some true).card
  have key : ∀ j : Fin (N + 1), ∑ a ∈ univ.erase j, c a = 1 := by
    intro j
    let Y : {a : Fin (N + 1) // a ≠ j} → Finset ℕ := fun a => X a.1
    have hYd : Pairwise (Disjoint on Y) := fun a b hab => hdisj (fun h => hab (Subtype.ext h))
    have hYc : (univ.biUnion Y).card = m + 1 := by
      rw [card_biUnion_univ Y hYd s (fun a => hcard a.1)]
      simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
      rw [← hsN]; simp [mul_comm]
    obtain ⟨P, hP, hrun⟩ := glue_full A Y (fun a => q a.1) hYd (fun a => (hq a.1).1) T
      (fun a => (hq a.1).2) hYc
    have hsubY : univ.biUnion Y ⊆ U := by
      intro u hu
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
      exact hsub a.1 ha
    have h1 := hA _ hsubY hYc P hP
    have h2 : (leaders A P T (univ.biUnion Y)).card = ∑ a ∈ univ.erase j, c a := by
      rw [leaders, Finset.filter_biUnion, Finset.card_biUnion]
      · rw [← Finset.sum_coe_sort (univ.erase j)]
        refine Finset.sum_bij (fun a _ => ⟨a.1, Finset.mem_erase.2 ⟨a.2, Finset.mem_univ _⟩⟩)
          (fun _ _ => Finset.mem_univ _) (fun a _ b _ h => Subtype.ext (by simpa using h))
          (fun b _ => ⟨⟨b.1, (Finset.mem_erase.1 b.2).1⟩, Finset.mem_univ _, rfl⟩) ?_
        intro a _
        simp only [c, Y]
        congr 1
        apply Finset.filter_congr
        intro u hu
        rw [hrun a u hu T le_rfl]
      · intro a _ b _ hab
        exact Finset.disjoint_filter_filter (hYd hab)
    rw [← h2, h1]
  -- all `c a` are equal to `∑ c - 1`, which is impossible
  have htot : ∀ j, ∑ a, c a = c j + 1 := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), key j]
  have hsum : ∑ j : Fin (N + 1), (∑ a, c a) = ∑ j : Fin (N + 1), (c j + 1) :=
    Finset.sum_congr rfl fun j _ => htot j
  rw [Finset.sum_const, Finset.sum_add_distrib, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  set S := ∑ a, c a
  have h2 : N * S = N + 1 := by ring_nf at hsum ⊢; omega
  rcases Nat.lt_or_ge S 2 with h | h
  · interval_cases S <;> omega
  · nlinarith

/-- A maximal family of pairwise disjoint nonempty `P`-subsets of `U`. -/
theorem exists_maximal_disjoint (U : Finset ℕ) (P : Finset ℕ → Prop) :
    ∃ F : Finset (Finset ℕ), (∀ X ∈ F, X ⊆ U ∧ P X) ∧
      (∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → Disjoint X Y) ∧
      ∀ X ⊆ U \ F.biUnion id, P X → X = ∅ := by
  let C := (U.powerset.powerset).filter fun F =>
    (∀ X ∈ F, P X) ∧ ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → Disjoint X Y
  have hC : C.Nonempty := ⟨∅, by simp [C]⟩
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image C Finset.card hC
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hF
  refine ⟨F, fun X hX => ⟨Finset.mem_powerset.1 (hF.1 hX), hF.2.1 X hX⟩, hF.2.2, ?_⟩
  intro X hXU hPX
  by_contra hne
  have hXF : X ∉ F := by
    intro hX
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have h1 := hXU hx
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, id] at h1
    exact h1.2 ⟨X, hX, hx⟩
  have hdisjX : ∀ Y ∈ F, Disjoint X Y := by
    intro Y hY
    rw [Finset.disjoint_left]
    intro x hx hxY
    have h1 := hXU hx
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, id] at h1
    exact h1.2 ⟨Y, hY, hxY⟩
  have hins : insert X F ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro Y hY
      rcases Finset.mem_insert.1 hY with rfl | hY
      · exact Finset.mem_powerset.2 (hXU.trans Finset.sdiff_subset)
      · exact hF.1 hY
    · intro Y hY
      rcases Finset.mem_insert.1 hY with rfl | hY
      · exact hPX
      · exact hF.2.1 Y hY
    · intro Y hY Z hZ hYZ
      rcases Finset.mem_insert.1 hY with hY | hY <;> rcases Finset.mem_insert.1 hZ with hZ | hZ
      · exact absurd (hY.trans hZ.symm) hYZ
      · rw [hY]; exact hdisjX Z hZ
      · rw [hZ]; exact (hdisjX Y hY).symm
      · exact hF.2.2 Y hY Z hZ hYZ
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hXF] at this
  omega

/-- Enumerate `k` members of a finset of finsets. -/
theorem exists_fin_embedding {α : Type*} (F : Finset α) (k : ℕ) (hk : k ≤ F.card) :
    ∃ e : Fin k → α, Injective e ∧ ∀ a, e a ∈ F := by
  obtain ⟨G, hGF, hG⟩ := Finset.exists_subset_card_eq hk
  let e := (G.equivFin.trans (finCongr hG)).symm
  exact ⟨fun a => (e a).1, fun a b h => e.injective (Subtype.ext h), fun a => hGF (e a).2⟩

/-- **Corollary 3.7** (repaired, one size). If `n = m + 1 = s · N` with `N ≥ 2`, then removing at
most `n` IDs from the universe leaves no `s`-set that can run in isolation for `T` rounds. -/
theorem exists_universe_no_isolable {A : Algorithm m} {U : Finset ℕ} {T : ℕ}
    (hA : ElectsBy A U T) {s N : ℕ} (hsN : s * N = m + 1) (hN : 2 ≤ N) (hs : 0 < s) :
    ∃ U₀ ⊆ U, U.card ≤ U₀.card + (m + 1) ∧
      ∀ X ⊆ U₀, X.card = s → ¬ Isolable A T X := by
  obtain ⟨F, hF, hFd, hmax⟩ :=
    exists_maximal_disjoint U (fun X => X.card = s ∧ Isolable A T X)
  have hFcard : F.card ≤ N := by
    by_contra hlt
    push Not at hlt
    obtain ⟨e, he, heF⟩ := exists_fin_embedding F (N + 1) hlt
    exact not_disjoint_isolable hA hsN hN e
      (fun a b hab => hFd _ (heF a) _ (heF b) (fun h => hab (he h)))
      (fun a => (hF _ (heF a)).1) (fun a => (hF _ (heF a)).2.1) (fun a => (hF _ (heF a)).2.2)
  refine ⟨U \ F.biUnion id, Finset.sdiff_subset, ?_, ?_⟩
  · have h1 : (F.biUnion id).card = F.card * s := by
      rw [Finset.card_biUnion (s := F) (t := id) (fun X hX Y hY h => hFd X hX Y hY h)]
      rw [Finset.sum_congr rfl fun X hX => (show (id X).card = s from (hF X hX).2.1)]
      simp
    have h2 : U.card ≤ (U \ F.biUnion id).card + (F.biUnion id).card := by
      have := Finset.card_le_card_sdiff_add_card (s := U) (t := F.biUnion id)
      omega
    have h3 : F.card * s ≤ m + 1 := by rw [← hsN, mul_comm s]; exact Nat.mul_le_mul_right _ hFcard
    omega
  · intro X hX hXs hiso
    have := hmax X hX ⟨hXs, hiso⟩
    subst this
    simp at hXs
    omega

/-- **Corollary 3.7** (repaired, all sizes `2^ℓ` with `ℓ < k`, for `n = 2^k`). -/
theorem exists_universe_no_isolable_pow {A : Algorithm m} {U : Finset ℕ} {T : ℕ}
    (hA : ElectsBy A U T) {k : ℕ} (hk : m + 1 = 2 ^ k) :
    ∃ U₀ ⊆ U, U.card ≤ U₀.card + k * (m + 1) ∧
      ∀ ℓ < k, ∀ X ⊆ U₀, X.card = 2 ^ ℓ → ¬ Isolable A T X := by
  -- remove the levels one at a time
  have : ∀ L ≤ k, ∃ U₀ ⊆ U, U.card ≤ U₀.card + L * (m + 1) ∧
      ∀ ℓ < L, ∀ X ⊆ U₀, X.card = 2 ^ ℓ → ¬ Isolable A T X := by
    intro L
    induction L with
    | zero => exact fun _ => ⟨U, subset_rfl, by simp, fun ℓ h => absurd h (Nat.not_lt_zero _)⟩
    | succ L ih =>
      intro hL
      obtain ⟨U₁, hU₁, hc₁, hno₁⟩ := ih (by omega)
      have hA₁ : ElectsBy A U₁ T := fun I hI => hA I (hI.trans hU₁)
      have hsN : 2 ^ L * 2 ^ (k - L) = m + 1 := by
        rw [← pow_add, hk]; congr 1; omega
      have hN : 2 ≤ 2 ^ (k - L) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k - L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      obtain ⟨U₂, hU₂, hc₂, hno₂⟩ :=
        exists_universe_no_isolable hA₁ hsN hN (by positivity)
      refine ⟨U₂, hU₂.trans hU₁, by rw [Nat.succ_mul]; omega, ?_⟩
      intro ℓ hℓ X hX hXc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ with h | rfl
      · exact hno₁ ℓ h X (hX.trans hU₂) hXc
      · exact hno₂ X hX hXc
  exact this k le_rfl

end LeaderTradeoffs
