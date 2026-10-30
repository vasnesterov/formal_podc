import Papers.PODC2017.DeltaEdgeColoring.EdgeSchedule

/-!
# Lemma 5.1 and Theorem 5.2: `(Δ + O(a))`-edge-colouring via an H-partition

**Lemma 5.1.** `V = A ∪ B` (disjoint), vertices of `A` have degree `≤ d`, `G(A)` and `G(B)` are
already properly edge-coloured. Every `a ∈ A` labels its edges to `B` injectively by
`0, …, d-1`; in round `i` every `b ∈ B` colours its edges of label `i`, choosing distinct colours
`< Δ + d - 1` that avoid the colours of all adjacent edges coloured so far.

**Theorem 5.2.** Given an H-partition `H_0, …, H_{ℓ-1}` of degree `d` (every vertex has at most `d`
neighbours in its own or later sets) and proper edge colourings of the sets `G(H_i)`, process the
sets from `H_{ℓ-1}` back to `H_0`; in stage `i` colour the edges between `H_i` and later sets by the
procedure of Lemma 5.1 (`A = H_i`). Globally, the edge `ab` with `h a < h b` is coloured in round
`(ℓ - 1 - h a) · d + lab a b` by its endpoint `b`.

## Main results

* `lemma_5_1`, `theorem_5_2`: every run (every colouring following the round rule) is a proper edge
  colouring with colours `< max k₀ (Δ + d - 1)`, and runs exist (the rule can always be followed).
* `lemma_5_1_parallel`, `theorem_5_2_parallel`: two adjacent edges coloured in the same round share
  the endpoint that chooses their colours (the `B`-endpoint / the endpoint in the later H-set), so the
  choices made in one round by different vertices never conflict.
* `lemma_5_1_rounds`, `theorem_5_2_rounds`: `d` rounds, resp. `ℓ · d` rounds.
* `theorem_5_2_colors`: with the H-sets coloured greedily (`2d - 1` colours, `exists_hSet_coloring`)
  the result uses at most `Δ + 2d` colours, i.e. `Δ + O(a)` for `d = O(a)`.
-/

open Finset

namespace Podc.DeltaEdgeColoring

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Lemma 5.1 -/

section Lemma51

variable (A : Set V) (lab : V → V → ℕ)

/-- An edge is pre-coloured iff both endpoints lie in `A` or both lie in `B = Aᶜ`. -/
def crossPre : Sym2 V → Prop :=
  Sym2.lift ⟨fun u v => (u ∈ A ↔ v ∈ A), fun _ _ => propext ⟨Iff.symm, Iff.symm⟩⟩

open Classical in
/-- The crossing edge `ab` (`a ∈ A`, `b ∉ A`) is coloured in round `lab a b`. -/
noncomputable def crossTime : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => if u ∈ A ∧ v ∉ A then lab u v else if v ∈ A ∧ u ∉ A then lab v u else 0,
    fun u v => by by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [hu, hv]⟩

/-- The schedule of Lemma 5.1. -/
noncomputable def schedule51 : EdgeSchedule V := ⟨crossPre A, crossTime A lab⟩

@[simp] lemma crossPre_mk {u v : V} : crossPre A s(u, v) ↔ (u ∈ A ↔ v ∈ A) := Iff.rfl

lemma crossTime_mk_of_mem {u v : V} (hu : u ∈ A) (hv : v ∉ A) :
    crossTime A lab s(u, v) = lab u v := by
  simp [crossTime, hu, hv]

lemma crossTime_mk_of_notMem {u v : V} (hu : u ∉ A) (hv : v ∈ A) :
    crossTime A lab s(u, v) = lab v u := by
  simp [crossTime, hu, hv]

variable {G : SimpleGraph V} {A lab} {Δ d : ℕ}

/-- The labelling of Lemma 5.1: every `a ∈ A` labels its edges to `B` injectively by `0, …, d-1`. -/
structure IsLabeling (G : SimpleGraph V) (A : Set V) (lab : V → V → ℕ) (d : ℕ) : Prop where
  lt : ∀ ⦃a b⦄, a ∈ A → b ∉ A → G.Adj a b → lab a b < d
  inj : ∀ ⦃a b b'⦄, a ∈ A → b ∉ A → b' ∉ A → G.Adj a b → G.Adj a b' → lab a b = lab a b' → b = b'

open Classical in
/-- Such labellings exist when vertices of `A` have degree `≤ d`. -/
lemma exists_isLabeling (hdA : ∀ a ∈ A, (G.neighborSet a).ncard ≤ d) :
    ∃ lab, IsLabeling G A lab d := by
  let N : V → Finset V := fun a => {b | G.Adj a b}
  have hN : ∀ a ∈ A, #(N a) ≤ d := fun a ha => by
    have := hdA a ha
    rwa [← Set.ncard_coe_finset, show ((N a : Finset V) : Set V) = G.neighborSet a by
      ext; simp [N]]
  refine ⟨fun a b => if hb : b ∈ N a then ((N a).equivFin ⟨b, hb⟩ : ℕ) else 0, ?_, ?_⟩
  · intro a b ha _ hab
    have hb : b ∈ N a := by simp [N, hab]
    simp only [hb, dite_true]
    exact lt_of_lt_of_le ((N a).equivFin ⟨b, hb⟩).2 (hN a ha)
  · intro a b b' _ _ _ hab hab' h
    have hb : b ∈ N a := by simp [N, hab]
    have hb' : b' ∈ N a := by simp [N, hab']
    simp only [hb, hb', dite_true] at h
    exact congrArg Subtype.val ((N a).equivFin.injective (Fin.ext h))

open Classical in
/-- The load bound for Lemma 5.1: a crossing edge has at most `d - 1` other edges at its
`A`-endpoint and at most `Δ - 1` at its `B`-endpoint. -/
lemma load_51 (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hdA : ∀ a ∈ A, (G.neighborSet a).ncard ≤ d) {u v : V} (huv : G.Adj u v)
    (hp : ¬ crossPre A s(u, v)) :
    #((schedule51 A lab).load G u v) + #((schedule51 A lab).load G v u) < Δ + d - 1 := by
  have hcard : ∀ x y, G.Adj x y → #((schedule51 A lab).load G x y) + 1 ≤ (G.neighborSet x).ncard := by
    intro x y hxy
    have hsub : insert y ((schedule51 A lab).load G x y) ⊆ G.neighborFinset x := by
      intro w hw
      rcases mem_insert.1 hw with rfl | hw
      · simpa using hxy
      · simp only [EdgeSchedule.load, mem_filter, mem_univ, true_and] at hw
        simpa using hw.1
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem (by simp [EdgeSchedule.load])] at h1
    have h2 : #(G.neighborFinset x) = (G.neighborSet x).ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
    omega
  have h1 := hcard u v huv
  have h2 := hcard v u huv.symm
  simp only [crossPre_mk] at hp
  by_cases hu : u ∈ A
  · have hv : v ∉ A := fun hv => hp ⟨fun _ => hv, fun _ => hu⟩
    have := hdA u hu; have := hΔ v
    omega
  · have hv : v ∈ A := by by_contra hv; exact hp ⟨fun h => absurd h hu, fun h => absurd h hv⟩
    have := hdA v hv; have := hΔ u
    omega

/-- **Lemma 5.1.** Let `G(A)` and `G(B)` (`B = Aᶜ`) be properly edge-coloured by `c₀` with colours
`< k₀`, let the vertices of `A` have degree `≤ d`, let all degrees be `≤ Δ`, and let `lab` be a
labelling as above. Then (i) every run of the procedure is a proper edge colouring of `G` with colours
`< max k₀ (Δ + d - 1)`, i.e. `Δ + O(d)` colours, and (ii) runs exist. -/
theorem lemma_5_1 (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hdA : ∀ a ∈ A, (G.neighborSet a).ncard ≤ d) (c₀ : Sym2 V → ℕ) {k₀ : ℕ}
    (hc₀ : ∀ ⦃u v w⦄, G.Adj u v → G.Adj u w → crossPre A s(u, v) → crossPre A s(u, w) →
      c₀ s(u, v) = c₀ s(u, w) → v = w)
    (hk₀ : ∀ ⦃u v⦄, G.Adj u v → crossPre A s(u, v) → c₀ s(u, v) < k₀) :
    (∀ c, (schedule51 A lab).Follows G c₀ c (Δ + d - 1) →
      G.IsProperEdgeColoring c (max k₀ (Δ + d - 1))) ∧
    ∃ c, (schedule51 A lab).Follows G c₀ c (Δ + d - 1) :=
  ⟨fun _ hf => hf.isProperEdgeColoring hc₀ hk₀,
    EdgeSchedule.exists_follows c₀ fun _ _ huv hp => load_51 hΔ hdA huv hp⟩

/-- Lemma 5.1, round count: every crossing edge is coloured in one of the rounds `0, …, d-1`. -/
theorem lemma_5_1_rounds (hlab : IsLabeling G A lab d) {u v : V} (huv : G.Adj u v)
    (hp : ¬ crossPre A s(u, v)) : crossTime A lab s(u, v) < d := by
  simp only [crossPre_mk] at hp
  by_cases hu : u ∈ A
  · have hv : v ∉ A := fun hv => hp ⟨fun _ => hv, fun _ => hu⟩
    rw [crossTime_mk_of_mem _ _ hu hv]
    exact hlab.lt hu hv huv
  · have hv : v ∈ A := by by_contra hv; exact hp ⟨fun h => absurd h hu, fun h => absurd h hv⟩
    rw [crossTime_mk_of_notMem _ _ hu hv]
    exact hlab.lt hv hu huv.symm

/-- Lemma 5.1, parallel consistency: if two distinct crossing edges `uv`, `uw` are coloured in the
same round, then their common endpoint `u` is in `B`: all edges coloured in one round at a vertex are
coloured by that vertex itself. -/
theorem lemma_5_1_parallel (hlab : IsLabeling G A lab d) {u v w : V} (huv : G.Adj u v)
    (huw : G.Adj u w) (hvw : v ≠ w) (hpv : ¬ crossPre A s(u, v)) (hpw : ¬ crossPre A s(u, w))
    (ht : crossTime A lab s(u, v) = crossTime A lab s(u, w)) : u ∉ A := by
  intro hu
  simp only [crossPre_mk] at hpv hpw
  have hv : v ∉ A := fun hv => hpv ⟨fun _ => hv, fun _ => hu⟩
  have hw : w ∉ A := fun hw => hpw ⟨fun _ => hw, fun _ => hu⟩
  rw [crossTime_mk_of_mem _ _ hu hv, crossTime_mk_of_mem _ _ hu hw] at ht
  exact hvw (hlab.inj hu hv hw huv huw ht)

end Lemma51

/-! ### Theorem 5.2 -/

section Theorem52

variable (h : V → ℕ) (ℓ d : ℕ) (lab : V → V → ℕ)

/-- The edges inside the H-sets are pre-coloured. -/
def hPre : Sym2 V → Prop :=
  Sym2.lift ⟨fun u v => h u = h v, fun _ _ => propext ⟨Eq.symm, Eq.symm⟩⟩

/-- The round of the edge `ab` with `h a < h b`: stage `ℓ - 1 - h a` (stages run from `H_{ℓ-1}`
back to `H_0`), round `lab a b` of that stage. -/
def stageTime (a b : V) : ℕ := (ℓ - 1 - h a) * d + lab a b

/-- The global round of every crossing edge. -/
def hTime : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => if h u < h v then stageTime h ℓ d lab u v
      else if h v < h u then stageTime h ℓ d lab v u else 0, fun u v => by
    by_cases h1 : h u < h v
    · have : ¬ h v < h u := by omega
      simp [h1, this]
    · by_cases h2 : h v < h u
      · simp [h1, h2]
      · simp [h1, h2]⟩

/-- The schedule of Theorem 5.2. -/
def schedule52 : EdgeSchedule V := ⟨hPre h, hTime h ℓ d lab⟩

@[simp] lemma hPre_mk {u v : V} : hPre h s(u, v) ↔ h u = h v := Iff.rfl

lemma hTime_mk_of_lt {u v : V} (huv : h u < h v) :
    hTime h ℓ d lab s(u, v) = stageTime h ℓ d lab u v := by simp [hTime, huv]

lemma hTime_mk_of_gt {u v : V} (huv : h v < h u) :
    hTime h ℓ d lab s(u, v) = stageTime h ℓ d lab v u := by
  have : ¬ h u < h v := by omega
  simp [hTime, huv, this]

variable {G : SimpleGraph V} {h ℓ d lab} {Δ : ℕ}

/-- An H-partition `H_i = h⁻¹(i)`, `i < ℓ`, of degree `d`: every vertex has at most `d` neighbours
in its own or later H-sets. -/
structure IsHPartition (G : SimpleGraph V) (h : V → ℕ) (ℓ d : ℕ) : Prop where
  lt : ∀ v, h v < ℓ
  deg : ∀ v, {u | G.Adj v u ∧ h v ≤ h u}.ncard ≤ d

open Classical in
lemma IsHPartition.card_le (hH : IsHPartition G h ℓ d) (v : V) :
    #{u | G.Adj v u ∧ h v ≤ h u} ≤ d := by
  have h2 := hH.deg v
  rwa [← coe_filter_univ, Set.ncard_coe_finset] at h2

/-- The labelling: every vertex labels its edges to later H-sets injectively by `0, …, d-1`. -/
structure IsHLabeling (G : SimpleGraph V) (h : V → ℕ) (lab : V → V → ℕ) (d : ℕ) : Prop where
  lt : ∀ ⦃a b⦄, G.Adj a b → h a < h b → lab a b < d
  inj : ∀ ⦃a b b'⦄, G.Adj a b → G.Adj a b' → h a < h b → h a < h b' → lab a b = lab a b' → b = b'

open Classical in
lemma exists_isHLabeling (hH : IsHPartition G h ℓ d) : ∃ lab, IsHLabeling G h lab d := by
  let N : V → Finset V := fun a => {b | G.Adj a b ∧ h a ≤ h b}
  refine ⟨fun a b => if hb : b ∈ N a then ((N a).equivFin ⟨b, hb⟩ : ℕ) else 0, ?_, ?_⟩
  · intro a b hab hlt
    have hb : b ∈ N a := by simp [N, hab, hlt.le]
    simp only [hb, dite_true]
    exact lt_of_lt_of_le ((N a).equivFin ⟨b, hb⟩).2 (hH.card_le a)
  · intro a b b' hab hab' hlt hlt' heq
    have hb : b ∈ N a := by simp [N, hab, hlt.le]
    have hb' : b' ∈ N a := by simp [N, hab', hlt'.le]
    simp only [hb, hb', dite_true] at heq
    exact congrArg Subtype.val ((N a).equivFin.injective (Fin.ext heq))

/-- Edges of later stages get later rounds: if `h w < h u` and `h u < h v`, the edge `wu` (stage of
`H_{h w}`, processed after `H_{h u}`) comes after `uv`. -/
lemma stageTime_lt (hlab : IsHLabeling G h lab d) (hH : IsHPartition G h ℓ d) {u v w : V}
    (huv : G.Adj u v) (hlt : h u < h v) (hwu : h w < h u) :
    stageTime h ℓ d lab u v < stageTime h ℓ d lab w u := by
  unfold stageTime
  have h1 := hlab.lt huv hlt
  have h2 := hH.lt u
  have h3 : ℓ - 1 - h u + 1 ≤ ℓ - 1 - h w := by omega
  have h4 : (ℓ - 1 - h u + 1) * d ≤ (ℓ - 1 - h w) * d := Nat.mul_le_mul_right _ h3
  rw [add_mul, one_mul] at h4
  omega

open Classical in
/-- The load bound for Theorem 5.2: the crossing edge `ab` (`h a < h b`) has at most `d - 1` other
edges at `a` that are pre-coloured or not scheduled later (edges to earlier H-sets are coloured in
later stages), and at most `Δ - 1` other edges at `b`. -/
lemma load_52 (hH : IsHPartition G h ℓ d) (hlab : IsHLabeling G h lab d)
    (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ) {u v : V} (huv : G.Adj u v)
    (hp : ¬ hPre h s(u, v)) :
    #((schedule52 h ℓ d lab).load G u v) + #((schedule52 h ℓ d lab).load G v u) < Δ + d - 1 := by
  -- at the lower endpoint
  have hlow : ∀ a b, G.Adj a b → h a < h b →
      #((schedule52 h ℓ d lab).load G a b) + 1 ≤ d := by
    intro a b hab hlt
    have hsub : insert b ((schedule52 h ℓ d lab).load G a b) ⊆
        ({u | G.Adj a u ∧ h a ≤ h u} : Finset V) := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and]
      rcases mem_insert.1 hw with rfl | hw
      · exact ⟨hab, hlt.le⟩
      · simp only [EdgeSchedule.load, mem_filter, mem_univ, true_and, schedule52, hPre_mk] at hw
        refine ⟨hw.1, ?_⟩
        by_contra hwa
        push Not at hwa
        rcases hw.2.2 with heq | hle
        · omega
        · rw [hTime_mk_of_gt h ℓ d lab hwa, hTime_mk_of_lt h ℓ d lab hlt] at hle
          have := stageTime_lt hlab hH hab hlt hwa
          omega
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem (by simp [EdgeSchedule.load])] at h1
    exact h1.trans (hH.card_le a)
  -- at the higher endpoint
  have hhigh : ∀ x y, G.Adj x y → #((schedule52 h ℓ d lab).load G x y) + 1 ≤ Δ := by
    intro x y hxy
    have hsub : insert y ((schedule52 h ℓ d lab).load G x y) ⊆ G.neighborFinset x := by
      intro w hw
      rcases mem_insert.1 hw with rfl | hw
      · simpa using hxy
      · simp only [EdgeSchedule.load, mem_filter, mem_univ, true_and] at hw
        simpa using hw.1
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem (by simp [EdgeSchedule.load])] at h1
    have h2 : #(G.neighborFinset x) = (G.neighborSet x).ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
    have := hΔ x
    omega
  simp only [hPre_mk] at hp
  rcases lt_or_gt_of_ne hp with hlt | hlt
  · have := hlow u v huv hlt; have := hhigh v u huv.symm; omega
  · have := hlow v u huv.symm hlt; have := hhigh u v huv; omega

/-- **Theorem 5.2.** Let `h` be an H-partition of `G` with `ℓ` sets and degree `d`, let all degrees
be `≤ Δ`, let `lab` be a labelling as above, and let `c₀` properly edge-colour the H-sets `G(H_i)`
with colours `< k₀`. Then (i) every run of the procedure (stages `H_{ℓ-1}, …, H_0`, each by
Lemma 5.1) is a proper edge colouring of `G` with colours `< max k₀ (Δ + d - 1)`, and (ii) runs
exist. -/
theorem theorem_5_2 (hH : IsHPartition G h ℓ d) (hlab : IsHLabeling G h lab d)
    (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ) (c₀ : Sym2 V → ℕ) {k₀ : ℕ}
    (hc₀ : ∀ ⦃u v w⦄, G.Adj u v → G.Adj u w → h u = h v → h u = h w →
      c₀ s(u, v) = c₀ s(u, w) → v = w)
    (hk₀ : ∀ ⦃u v⦄, G.Adj u v → h u = h v → c₀ s(u, v) < k₀) :
    (∀ c, (schedule52 h ℓ d lab).Follows G c₀ c (Δ + d - 1) →
      G.IsProperEdgeColoring c (max k₀ (Δ + d - 1))) ∧
    ∃ c, (schedule52 h ℓ d lab).Follows G c₀ c (Δ + d - 1) :=
  ⟨fun _ hf => hf.isProperEdgeColoring (fun _ _ _ huv huw hv hw he => hc₀ huv huw hv hw he)
      (fun _ _ huv hp => hk₀ huv hp),
    EdgeSchedule.exists_follows c₀ fun _ _ huv hp => load_52 hH hlab hΔ huv hp⟩

/-- Theorem 5.2, round count: `ℓ` stages of `d` rounds. -/
theorem theorem_5_2_rounds (hH : IsHPartition G h ℓ d) (hlab : IsHLabeling G h lab d) {u v : V}
    (huv : G.Adj u v) (hp : ¬ hPre h s(u, v)) : hTime h ℓ d lab s(u, v) < ℓ * d := by
  have key : ∀ a b, G.Adj a b → h a < h b → stageTime h ℓ d lab a b < ℓ * d := by
    intro a b hab hlt
    unfold stageTime
    have h1 := hlab.lt hab hlt
    have h2 := hH.lt a
    have : (ℓ - 1 - h a + 1) * d ≤ ℓ * d := Nat.mul_le_mul_right _ (by omega)
    rw [add_mul, one_mul] at this
    omega
  simp only [hPre_mk] at hp
  rcases lt_or_gt_of_ne hp with hlt | hlt
  · rw [hTime_mk_of_lt h ℓ d lab hlt]; exact key u v huv hlt
  · rw [hTime_mk_of_gt h ℓ d lab hlt]; exact key v u huv.symm hlt

/-- Theorem 5.2, parallel consistency: if two distinct crossing edges `uv`, `uw` are coloured in
the same round, then `u` is the endpoint in the later H-set of both, i.e. the vertex choosing both
colours (Lemma 5.1's `B`-endpoint). -/
theorem theorem_5_2_parallel (hH : IsHPartition G h ℓ d) (hlab : IsHLabeling G h lab d)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : v ≠ w) (hpv : ¬ hPre h s(u, v))
    (hpw : ¬ hPre h s(u, w)) (ht : hTime h ℓ d lab s(u, v) = hTime h ℓ d lab s(u, w)) :
    h v < h u ∧ h w < h u := by
  simp only [hPre_mk] at hpv hpw
  rcases lt_or_gt_of_ne hpv with hv | hv <;> rcases lt_or_gt_of_ne hpw with hw | hw
  · rw [hTime_mk_of_lt h ℓ d lab hv, hTime_mk_of_lt h ℓ d lab hw] at ht
    unfold stageTime at ht
    exact absurd (hlab.inj huv huw hv hw (by omega)) hvw
  · rw [hTime_mk_of_lt h ℓ d lab hv, hTime_mk_of_gt h ℓ d lab hw] at ht
    exact absurd ht (stageTime_lt hlab hH huv hv hw).ne
  · rw [hTime_mk_of_gt h ℓ d lab hv, hTime_mk_of_lt h ℓ d lab hw] at ht
    exact absurd ht.symm (stageTime_lt hlab hH huw hw hv).ne
  · exact ⟨hv, hw⟩

/-- The H-sets can be edge-coloured greedily with `2d - 1` colours (each `G(H_i)` has max degree
`≤ d`); the paper uses [17] or the algorithm of Section 4 for this step. -/
theorem exists_hSet_coloring (hH : IsHPartition G h ℓ d) :
    ∃ c₀ : Sym2 V → ℕ, (∀ ⦃u v w⦄, G.Adj u v → G.Adj u w → h u = h v → h u = h w →
      c₀ s(u, v) = c₀ s(u, w) → v = w) ∧
      ∀ ⦃u v⦄, G.Adj u v → h u = h v → c₀ s(u, v) < 2 * d - 1 := by
  classical
  let Gh : SimpleGraph V := { Adj := fun u v => G.Adj u v ∧ h u = h v
                              symm := ⟨fun _ _ huv => ⟨huv.1.symm, huv.2.symm⟩⟩
                              loopless := ⟨fun _ huv => G.loopless.irrefl _ huv.1⟩ }
  have hdeg : ∀ v, (Gh.neighborSet v).ncard ≤ d := by
    intro v
    refine le_trans (Set.ncard_le_ncard (t := (({u | G.Adj v u ∧ h v ≤ h u} : Finset V) : Set V))
      (fun u hu => ?_) (Finset.finite_toSet _)) ?_
    · simp only [SimpleGraph.mem_neighborSet, Gh] at hu
      simp [hu.1, hu.2.le]
    · rw [Set.ncard_coe_finset]; exact hH.card_le v
  obtain ⟨c, hcL, hc⟩ := Gh.exists_listEdgeColoring (fun _ => range (2 * d - 1)) (fun u v _ => by
    have := hdeg u; have := hdeg v; rw [card_range]; omega)
  refine ⟨c, fun u v w huv huw hv hw he => hc ⟨huv, hv⟩ ⟨huw, hw⟩ he,
    fun u v huv hv => by simpa using hcL (show Gh.Adj u v from ⟨huv, hv⟩)⟩

/-- **Theorem 5.2**, colour count: with the H-sets coloured with `2d - 1` colours, there is a run of
the procedure, and every run is a proper edge colouring with at most `Δ + 2d` colours (`Δ + O(a)`
for an H-partition of degree `d = (2 + ε) a`). -/
theorem theorem_5_2_colors (hH : IsHPartition G h ℓ d) (hlab : IsHLabeling G h lab d)
    (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ) :
    ∃ c₀ : Sym2 V → ℕ, (∀ c, (schedule52 h ℓ d lab).Follows G c₀ c (Δ + d - 1) →
      G.IsProperEdgeColoring c (Δ + 2 * d)) ∧
      ∃ c, (schedule52 h ℓ d lab).Follows G c₀ c (Δ + d - 1) := by
  obtain ⟨c₀, hc₀, hk₀⟩ := exists_hSet_coloring hH
  obtain ⟨h1, h2⟩ := theorem_5_2 hH hlab hΔ c₀ hc₀ hk₀
  exact ⟨c₀, fun c hc => (h1 c hc).mono le_rfl (by omega), h2⟩

end Theorem52

end Podc.DeltaEdgeColoring
