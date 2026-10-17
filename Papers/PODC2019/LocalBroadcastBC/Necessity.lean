import Papers.PODC2019.LocalBroadcastBC.Model

/-!
# Necessity (Section 4 and Appendix A of [KNV19])

* `three_scenarios`: the common core of the proofs of Lemmas A.1 and A.2 — a two-copy cover with
  three lifts `E₁` (honest inputs `0`), `E₂`, `E₃` (honest inputs `1`) contradicts consensus.
* `lemmaA1`: minimum degree at least `2f` (needs `f < n`).
* `lemmaA2`: no vertex cut of size at most `⌊3f/2⌋`.
* `theorem_4_1`: both conditions (`n ≥ 2` is needed for the connectivity part, see
  `differencies.md` and `Counterexample.lean`).
-/

open Cslib.Byzantine.LockStep Finset

namespace LocalBroadcastBC

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
/-- The core of the FLM-style argument: a two-copy cover with three admissible lifts. In `E₁`
(Byzantine set `B₁`) all honest nodes have input `false`, in `E₃` (Byzantine set `B₃`) all have
input `true`; in `E₂` the honest node `p` runs as in `E₁` and the honest node `q` as in `E₃`. -/
theorem three_scenarios {M : Type u} {alg : Protocol V Bool M Bool} (hb : IsBroadcast alg)
    {Z : AdvStructure V} (hsol : SolvesLB G alg Z Consensus)
    (c : V → Bool → V → Bool) (xq : V × Bool → Bool) (B₁ B₂ B₃ : Set V)
    (ℓ₁ ℓ₂ ℓ₃ κ₁ κ₂ κ₃ : V → Bool)
    (hh₁ : ∀ p q, p ∉ B₁ → q ∉ B₁ → G.Adj p q → c q (ℓ₁ q) p = ℓ₁ p)
    (hb₁ : ∀ b q, b ∈ B₁ → q ∉ B₁ → G.Adj b q → c q (ℓ₁ q) b = κ₁ b)
    (hh₂ : ∀ p q, p ∉ B₂ → q ∉ B₂ → G.Adj p q → c q (ℓ₂ q) p = ℓ₂ p)
    (hb₂ : ∀ b q, b ∈ B₂ → q ∉ B₂ → G.Adj b q → c q (ℓ₂ q) b = κ₂ b)
    (hh₃ : ∀ p q, p ∉ B₃ → q ∉ B₃ → G.Adj p q → c q (ℓ₃ q) p = ℓ₃ p)
    (hb₃ : ∀ b q, b ∈ B₃ → q ∉ B₃ → G.Adj b q → c q (ℓ₃ q) b = κ₃ b)
    (hZ₁ : B₁ ∈ Z) (hZ₂ : B₂ ∈ Z) (hZ₃ : B₃ ∈ Z)
    (hx₁ : ∀ p, p ∉ B₁ → xq (p, ℓ₁ p) = false) (hx₃ : ∀ p, p ∉ B₃ → xq (p, ℓ₃ p) = true)
    {p q : V} (hp₁ : p ∉ B₁) (hp₂ : p ∉ B₂) (hpℓ : ℓ₂ p = ℓ₁ p)
    (hq₃ : q ∉ B₃) (hq₂ : q ∉ B₂) (hqℓ : ℓ₂ q = ℓ₃ q) : False := by
  set C := twoCopy c xq
  have L₁ := twoCopy_lift (G := G) c xq B₁ ℓ₁ κ₁ hh₁ hb₁
  have L₂ := twoCopy_lift (G := G) c xq B₂ ℓ₂ κ₂ hh₂ hb₂
  have L₃ := twoCopy_lift (G := G) c xq B₃ ℓ₃ κ₃ hh₃ hb₃
  set s₁ := CoverSystem'.lbScenario C G alg B₁ (fun p => (p, ℓ₁ p)) (fun b => (b, κ₁ b))
    (fun _ => false)
  set s₂ := CoverSystem'.lbScenario C G alg B₂ (fun p => (p, ℓ₂ p)) (fun b => (b, κ₂ b))
    (fun _ => false)
  set s₃ := CoverSystem'.lbScenario C G alg B₃ (fun p => (p, ℓ₃ p)) (fun b => (b, κ₃ b))
    (fun _ => false)
  have h₁ := hsol s₁ hZ₁ (CoverSystem'.lbScenario_reliable _ _ _ _)
    (CoverSystem'.lbScenario_isLocalBroadcast _ _ _ _)
  have h₂ := hsol s₂ hZ₂ (CoverSystem'.lbScenario_reliable _ _ _ _)
    (CoverSystem'.lbScenario_isLocalBroadcast _ _ _ _)
  have h₃ := hsol s₃ hZ₃ (CoverSystem'.lbScenario_reliable _ _ _ _)
    (CoverSystem'.lbScenario_isLocalBroadcast _ _ _ _)
  -- decisions of `p` and `q` in `E₂`
  obtain ⟨op, hop⟩ := h₂.1 p hp₂
  obtain ⟨oq, hoq⟩ := h₂.1 q hq₂
  have hagree := h₂.2.2 p hp₂ q hq₂ op oq hop hoq
  -- `p` decides as in `E₁`
  have hop₁ : Decides G alg s₁ p op := by
    rw [CoverSystem'.decides_lbScenario_iff hb L₁ _ hp₁]
    rw [CoverSystem'.decides_lbScenario_iff hb L₂ _ hp₂] at hop
    simpa [hpℓ] using hop
  have hoq₃ : Decides G alg s₃ q oq := by
    rw [CoverSystem'.decides_lbScenario_iff hb L₃ _ hq₃]
    rw [CoverSystem'.decides_lbScenario_iff hb L₂ _ hq₂] at hoq
    simpa [hqℓ] using hoq
  obtain ⟨r, hr, hrv⟩ := h₁.2.1 p hp₁ op hop₁
  obtain ⟨r', hr', hrv'⟩ := h₃.2.1 q hq₃ oq hoq₃
  have hr1 : r ∉ B₁ := hr
  have hr3 : r' ∉ B₃ := hr'
  rw [show s₁.input r = xq (r, ℓ₁ r) from CoverSystem'.lbScenario_input _ _ _ _ hr1,
    hx₁ r hr1] at hrv
  rw [show s₃.input r' = xq (r', ℓ₃ r') from CoverSystem'.lbScenario_input _ _ _ _ hr3,
    hx₃ r' hr3] at hrv'
  subst hrv hrv'
  exact absurd hagree (by decide)

variable [DecidableRel G.Adj]

/-- Lemma A.1 of [KNV19]: if Byzantine consensus is solvable under local broadcast on `G` with at
most `f < n` faults, then every node has degree at least `2f`. -/
theorem lemmaA1 {f : ℕ} (hsol : SolvableLB G (atMost f) (Consensus : Spec V Bool Bool)) (hfn : f < Fintype.card V)
    (z : V) : 2 * f ≤ G.degree z := by
  obtain ⟨M, alg, hb, hsol⟩ := hsol
  by_contra hdeg
  push Not at hdeg
  set N := G.neighborFinset z with hN
  have hNcard : N.card = G.degree z := G.card_neighborFinset_eq_degree z
  obtain ⟨F₁, hF₁N, hF₁card⟩ := Finset.exists_subset_card_eq
    (show min (f - 1) N.card ≤ N.card from min_le_right _ _)
  set F₂ := N \ F₁
  have hF₂card : F₂.card = N.card - F₁.card := card_sdiff_of_subset hF₁N
  set W := univ \ insert z N
  have hzN : z ∉ N := by simp [hN]
  have hzF₁ : z ∉ F₁ := fun h => hzN (hF₁N h)
  have hzF₂ : z ∉ F₂ := fun h => hzN (mem_sdiff.1 h).1
  have hzW : z ∉ W := by simp [W]
  have hmemW : ∀ x, x ∈ W ↔ x ≠ z ∧ x ∉ N := by intro x; simp [W]
  have hadjW : ∀ p q, G.Adj p q → p ∈ W → q ≠ z := by
    rintro p q hpq hpW rfl
    exact ((hmemW p).1 hpW).2 (by simpa [hN] using hpq.symm)
  have hcl : ∀ q, q ∉ W → q ≠ z → q ∉ F₁ → q ∈ F₂ := by
    intro q hqW hqz hqF₁
    have : q ∈ N := by by_contra h; exact hqW ((hmemW q).2 ⟨hqz, h⟩)
    exact mem_sdiff.2 ⟨this, hqF₁⟩
  have hF₁W : ∀ x ∈ F₁, x ∉ W := fun x hx hxW => ((hmemW x).1 hxW).2 (hF₁N hx)
  have hF₂W : ∀ x ∈ F₂, x ∉ W := fun x hx hxW => ((hmemW x).1 hxW).2 (mem_sdiff.1 hx).1
  -- some node outside `F₁ ∪ {z}`
  obtain ⟨q, hq⟩ : ∃ q, q ∉ insert z F₁ := by
    by_contra h
    push Not at h
    have : (univ : Finset V) ⊆ insert z F₁ := fun x _ => h x
    have := card_le_card this
    have := card_insert_le z F₁
    simp at *
    omega
  have hqz : q ≠ z := fun h => hq (by simp [h])
  have hqF₁ : q ∉ F₁ := fun h => hq (by simp [h])
  let c : V → Bool → V → Bool := fun u i v =>
    if v ∈ W then (if u ∈ W then i else decide (u ∈ F₂)) else false
  let xq : V × Bool → Bool := fun x => if x.1 ∈ W then x.2 else decide (x.1 ∈ F₂)
  refine three_scenarios hb hsol c xq (F₂ : Set V) (F₁ : Set V) (insert z F₁ : Finset V)
    (fun _ => false) (fun p => decide (p ∈ W)) (fun p => decide (p ∈ W))
    (fun _ => false) (fun _ => false) (fun _ => false)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (p := z) (q := q) ?_ ?_ ?_ ?_ ?_ ?_
  · intro p q hp hq hpq
    simp only [c]
    split_ifs <;> simp_all
  · intro b q hb hq hbq
    simp only [c, hF₂W b hb, ite_false]
  · intro p q hp hq hpq
    simp only [c]
    by_cases hpW : p ∈ W
    · by_cases hqW : q ∈ W
      · simp [hpW, hqW]
      · have := hcl q hqW (hadjW _ _ hpq hpW) hq
        simp [hpW, hqW, this]
    · simp [hpW]
  · intro b q hb hq hbq
    simp only [c, hF₁W b hb, ite_false]
  · intro p q hp hq hpq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at hp hq
    simp only [c]
    by_cases hpW : p ∈ W
    · by_cases hqW : q ∈ W
      · simp [hpW, hqW]
      · have := hcl q hqW hq.1 hq.2
        simp [hpW, hqW, this]
    · simp [hpW]
  · intro b q hb hq hbq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hb
    have : b ∉ W := by rcases hb with rfl | hb; exacts [hzW, hF₁W b hb]
    simp only [c, this, ite_false]
  · rw [coe_mem_atMost]
    omega
  · rw [coe_mem_atMost]
    omega
  · rw [coe_mem_atMost]
    have := card_insert_le z F₁
    omega
  · intro p hp
    simp only [xq]
    split_ifs <;> simp_all
  · intro p hp
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at hp
    simp only [xq]
    by_cases hpW : p ∈ W
    · simp [hpW]
    · simp [hpW, hcl p hpW hp.1 hp.2]
  · simpa using hzF₂
  · simpa using hzF₁
  · simp [hzW]
  · simpa using hq
  · simpa using hqF₁
  · rfl

omit [DecidableRel G.Adj] in
/-- Lemma A.2 of [KNV19], in the form actually proved there: if Byzantine consensus is solvable
under local broadcast on `G` with at most `f` faults, then `G` has no vertex cut of size at most
`⌊3f/2⌋` (removing at most `⌊3f/2⌋` vertices leaves the graph connected). -/
theorem lemmaA2 {f : ℕ} (hsol : SolvableLB G (atMost f) (Consensus : Spec V Bool Bool))
    (X : Finset V) (hX : X.card ≤ 3 * f / 2) (u v : V) (hu : u ∉ X) (hv : v ∉ X) :
    G.ReachableAvoiding (X : Set V) u v := by
  classical
  obtain ⟨M, alg, hb, hsol⟩ := hsol
  by_contra hreach
  set A := univ.filter (fun w => G.ReachableAvoiding (X : Set V) u w) with hA
  set D := univ \ X with hD
  set B := D \ A with hB
  have hmemD : ∀ x, x ∈ D ↔ x ∉ X := by simp [hD]
  have hmemB : ∀ x, x ∈ B ↔ x ∉ X ∧ x ∉ A := by simp [hB, hD]
  have hAX : ∀ x ∈ A, x ∉ X := by
    intro x hx
    obtain ⟨p, hp⟩ := (mem_filter.1 hx).2
    exact hp x p.end_mem_support
  have huA : u ∈ A := mem_filter.2 ⟨mem_univ _, ⟨SimpleGraph.Walk.nil, by simpa using hu⟩⟩
  have hvA : v ∉ A := fun h => hreach (mem_filter.1 h).2
  have hAB : ∀ a b, G.Adj a b → a ∈ A → b ∉ X → b ∈ A := by
    intro a b hab ha hbX
    obtain ⟨p, hp⟩ := (mem_filter.1 ha).2
    refine mem_filter.2 ⟨mem_univ _, ⟨p.concat hab, fun x hx => ?_⟩⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hp x hx
    · exact_mod_cast hbX
  -- split the cut into three parts
  obtain ⟨C₁, hC₁X, hC₁⟩ := exists_subset_card_eq (min_le_right (f / 2) X.card)
  obtain ⟨C₂, hC₂X, hC₂⟩ := exists_subset_card_eq (min_le_right (f / 2) (X \ C₁).card)
  set C₃ := (X \ C₁) \ C₂ with hC₃
  have hXC₁ : (X \ C₁).card = X.card - C₁.card := card_sdiff_of_subset hC₁X
  have hC₃card : C₃.card = (X \ C₁).card - C₂.card := card_sdiff_of_subset hC₂X
  have hC₁X' : ∀ x ∈ C₁, x ∈ X := fun x hx => hC₁X hx
  have hC₂X' : ∀ x ∈ C₂, x ∈ X ∧ x ∉ C₁ := fun x hx => by simpa using hC₂X hx
  have hmemC₃ : ∀ x, x ∈ C₃ ↔ x ∈ X ∧ x ∉ C₁ ∧ x ∉ C₂ := by simp [hC₃, and_assoc]
  let c : V → Bool → V → Bool := fun u' i v' =>
    if v' ∈ D then
      (if u' ∈ D then i else if u' ∈ C₁ then false else if u' ∈ C₃ then true else decide (v' ∈ B))
    else false
  let xq : V × Bool → Bool := fun x => if x.1 ∈ D then x.2 else decide (x.1 ∉ C₁)
  have hBD : ∀ x, x ∈ B → x ∈ D := fun x hx => by
    rw [hmemD]; exact ((hmemB x).1 hx).1
  refine three_scenarios hb hsol c xq ((C₂ ∪ C₃ : Finset V) : Set V) ((C₁ ∪ C₃ : Finset V) : Set V)
    ((C₁ ∪ C₂ : Finset V) : Set V)
    (fun _ => false) (fun p => decide (p ∈ B)) (fun p => decide (p ∈ D))
    (fun _ => false) (fun _ => false) (fun _ => false)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (p := u) (q := v) ?_ ?_ ?_ ?_ ?_ ?_
  · intro p q hp hq _
    simp only [coe_union, Set.mem_union, mem_coe, not_or] at hp hq
    simp only [c]
    by_cases hpD : p ∈ D
    · by_cases hqD : q ∈ D
      · simp [hpD, hqD]
      · have hqX : q ∈ X := by simpa [hmemD] using hqD
        have : q ∈ C₁ := by by_contra h; exact hp.2 |> fun _ => hq.2 ((hmemC₃ q).2 ⟨hqX, h, hq.1⟩)
        simp [hpD, hqD, this]
    · simp [hpD]
  · intro b q hb' _ _
    simp only [coe_union, Set.mem_union, mem_coe] at hb'
    have : b ∉ D := by
      rw [hmemD, not_not]
      rcases hb' with h | h
      · exact (hC₂X' b h).1
      · exact ((hmemC₃ b).1 h).1
    simp only [c, this, ite_false]
  · intro p q hp hq hpq
    simp only [coe_union, Set.mem_union, mem_coe, not_or] at hp hq
    simp only [c]
    by_cases hpD : p ∈ D
    · by_cases hqD : q ∈ D
      · simp only [hpD, hqD, ite_true]
        have hpX : p ∉ X := (hmemD p).1 hpD
        have hqX : q ∉ X := (hmemD q).1 hqD
        have : q ∈ A ↔ p ∈ A :=
          ⟨fun h => hAB q p hpq.symm h hpX, fun h => hAB p q hpq h hqX⟩
        simp [hmemB, hpX, hqX, this]
      · simp [hpD, hqD, hq.1, hq.2]
    · have : p ∉ B := fun h => hpD (hBD p h)
      simp [hpD, this]
  · intro b q hb' _ _
    simp only [coe_union, Set.mem_union, mem_coe] at hb'
    have : b ∉ D := by
      rw [hmemD, not_not]
      rcases hb' with h | h
      · exact hC₁X' b h
      · exact ((hmemC₃ b).1 h).1
    simp only [c, this, ite_false]
  · intro p q hp hq _
    simp only [coe_union, Set.mem_union, mem_coe, not_or] at hp hq
    simp only [c]
    by_cases hpD : p ∈ D
    · by_cases hqD : q ∈ D
      · simp [hpD, hqD]
      · have hqX : q ∈ X := by simpa [hmemD] using hqD
        have : q ∈ C₃ := (hmemC₃ q).2 ⟨hqX, hq.1, hq.2⟩
        simp [hpD, hqD, this, hq.1]
    · simp [hpD]
  · intro b q hb' _ _
    simp only [coe_union, Set.mem_union, mem_coe] at hb'
    have : b ∉ D := by
      rw [hmemD, not_not]
      rcases hb' with h | h
      · exact hC₁X' b h
      · exact (hC₂X' b h).1
    simp only [c, this, ite_false]
  · rw [coe_mem_atMost]
    have := card_union_le C₂ C₃
    omega
  · rw [coe_mem_atMost]
    have := card_union_le C₁ C₃
    omega
  · rw [coe_mem_atMost]
    have := card_union_le C₁ C₂
    omega
  · intro p hp
    simp only [coe_union, Set.mem_union, mem_coe, not_or] at hp
    simp only [xq]
    by_cases hpD : p ∈ D
    · simp [hpD]
    · have hpX : p ∈ X := by simpa [hmemD] using hpD
      have : p ∈ C₁ := by
        by_contra h; exact hp.2 ((hmemC₃ p).2 ⟨hpX, h, hp.1⟩)
      simp [hpD, this]
  · intro p hp
    simp only [coe_union, Set.mem_union, mem_coe, not_or] at hp
    simp [xq, hp.1]
  · simp only [coe_union, Set.mem_union, mem_coe, not_or]
    exact ⟨fun h => hu (hC₂X' u h).1, fun h => hu ((hmemC₃ u).1 h).1⟩
  · simp only [coe_union, Set.mem_union, mem_coe, not_or]
    exact ⟨fun h => hu (hC₁X' u h), fun h => hu ((hmemC₃ u).1 h).1⟩
  · simp [hmemB, huA]
  · simp only [coe_union, Set.mem_union, mem_coe, not_or]
    exact ⟨fun h => hv (hC₁X' v h), fun h => hv (hC₂X' v h).1⟩
  · simp only [coe_union, Set.mem_union, mem_coe, not_or]
    exact ⟨fun h => hv (hC₁X' v h), fun h => hv ((hmemC₃ v).1 h).1⟩
  · simp [hmemB, hmemD, hv, hvA]

/-- **Theorem 4.1** of [KNV19] (necessity): if Byzantine consensus tolerating at most `f < n`
faults is solvable under local broadcast on `G`, then `G` has minimum degree at least `2f` and is
`(⌊3f/2⌋ + 1)`-connected. The hypothesis `2 ≤ n` is missing in the paper; it is needed (for
`n = 1`, `f = 0` the statement is false, see `not_theorem_4_1_single_node`). -/
theorem theorem_4_1 {f : ℕ} (hsol : SolvableLB G (atMost f) (Consensus : Spec V Bool Bool))
    (hfn : f < Fintype.card V) (hn : 2 ≤ Fintype.card V) :
    2 * f ≤ G.minDegree ∧ G.IsVertexConnected (3 * f / 2 + 1) := by
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨z⟩ := id hne
  refine ⟨G.le_minDegree_of_forall_le_degree _ fun z => lemmaA1 hsol hfn z, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos f with rfl | hf
    · omega
    · have h1 := lemmaA1 hsol hfn z
      have h2 := G.degree_lt_card_verts z
      omega
  · intro X hX u v hu hv
    exact lemmaA2 hsol X (by omega) u v hu hv

end LocalBroadcastBC
