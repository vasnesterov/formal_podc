import Papers.PODC2019.AutomaticSpeedup.Theorem1

/-!
# Warm-up I: sinkless colouring and sinkless orientation (Brandt, PODC 2019, §4.4)

* `sinklessColoring`: labels `Bool` (`true` at `(v, e)`: `v` chooses the colour of `e`); an edge
  may not carry `true` on both sides; a node configuration has exactly one `true` (degree `Δ`).
* `sinkless_edgeAllMax`: the only maximal `Π'_{1/2}` edge configuration is `{{0}, {0, 1}}`
  (paper: "the only element of `g_{1/2}(Δ)` that is maximal is `{{0}{0,1}}`"), so `Π'_{1/2}` is
  sinkless orientation.
* `speedupMax_sinkless_relax`: every solution of `Π'_1` becomes a solution of sinkless colouring
  under the label map `W ↦ ({0} ∉ W)` (the direction of "`Π'_1 = Π`" needed for lower bounds).
* `sinklessColoring_lower_bound`: on a class of `Δ`-regular graphs with an input orientation that
  is `t'`-independent for all `t' ≤ t` and contains the configurations needed to defeat 0-round
  algorithms (`SinklessRich`), sinkless colouring is not solvable in `t` rounds; the same for
  sinkless orientation (`sinklessOrientation_lower_bound`). The paper concludes `Ω(log n)` using the
  existence of such classes with `t = Ω(log n)` ([Bollobás]), which we do not formalize.
-/

namespace AutomaticSpeedup

open Problem

/-- Sinkless colouring (§4.4), for `Δ`-regular graphs. -/
def sinklessColoring : Problem Bool where
  f _ := Set.univ
  g _ := {{false, false}, {false, true}}
  h Δ := {m | Multiset.card m = Δ ∧ m.count true = 1}

theorem sinkless_g_iff {Δ : ℕ} {a b : Bool} :
    ({a, b} : Multiset Bool) ∈ sinklessColoring.g Δ ↔ ¬ (a = true ∧ b = true) := by
  show ({a, b} : Multiset Bool) ∈ ({{false, false}, {false, true}} : Set (Multiset Bool)) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, pair_eq_pair_iff]
  cases a <;> cases b <;> simp

theorem sinkless_edgeAll {Δ : ℕ} {Y Z : Set Bool} :
    sinklessColoring.EdgeAll Δ Y Z ↔ ¬ (true ∈ Y ∧ true ∈ Z) := by
  show (Y ⊆ Set.univ ∧ Z ⊆ Set.univ ∧ ∀ y ∈ Y, ∀ z ∈ Z, ({y, z} : Multiset Bool) ∈
    sinklessColoring.g Δ) ↔ _
  simp only [Set.subset_univ, true_and, sinkless_g_iff]
  constructor
  · rintro h ⟨h1, h2⟩; exact h _ h1 _ h2 ⟨rfl, rfl⟩
  · rintro h y hy z hz ⟨rfl, rfl⟩; exact h ⟨hy, hz⟩

theorem set_bool_eq_univ {Y : Set Bool} : Y = Set.univ ↔ false ∈ Y ∧ true ∈ Y := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩; ext b; cases b <;> simp [h1, h2]

theorem set_bool_eq_false {Y : Set Bool} : Y = {false} ↔ false ∈ Y ∧ true ∉ Y := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩; ext b; cases b <;> simp [h1, h2]

/-- The maximal edge configurations of `Π_{1/2}` (§4.4): only `{{0}, {0, 1}}`. -/
theorem sinkless_edgeAllMax {Δ : ℕ} {Y Z : Set Bool} :
    sinklessColoring.EdgeAllMax Δ Y Z ↔
      (Y = {false} ∧ Z = Set.univ) ∨ (Y = Set.univ ∧ Z = {false}) := by
  simp only [EdgeAllMax, sinkless_edgeAll]
  constructor
  · rintro ⟨h, hY, hZ⟩
    by_cases hy : true ∈ Y
    · have hz : true ∉ Z := fun hz => h ⟨hy, hz⟩
      have hzf : false ∈ Z := by
        by_contra hzf
        refine hZ (insert false Z) (Set.ssubset_insert hzf) ?_
        rintro ⟨-, h2⟩; rcases h2 with h2 | h2
        · cases h2
        · exact hz h2
      have hyf : false ∈ Y := by
        by_contra hyf
        exact hY (insert false Y) (Set.ssubset_insert hyf) fun h2 => hz h2.2
      exact Or.inr ⟨set_bool_eq_univ.2 ⟨hyf, hy⟩, set_bool_eq_false.2 ⟨hzf, hz⟩⟩
    · by_cases hz : true ∈ Z
      · have hyf : false ∈ Y := by
          by_contra hyf
          refine hY (insert false Y) (Set.ssubset_insert hyf) ?_
          rintro ⟨h2, -⟩; rcases h2 with h2 | h2
          · cases h2
          · exact hy h2
        have hzf : false ∈ Z := by
          by_contra hzf
          exact hZ (insert false Z) (Set.ssubset_insert hzf) fun h2 => hy h2.1
        exact Or.inl ⟨set_bool_eq_false.2 ⟨hyf, hy⟩, set_bool_eq_univ.2 ⟨hzf, hz⟩⟩
      · exfalso
        refine hY (insert true Y) (Set.ssubset_insert hy) ?_
        rintro ⟨-, h2⟩; exact hz h2
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨by simp, fun Y' hY' h => ?_, fun Z' hZ' _ => ?_⟩
      · obtain ⟨b, hb, hb'⟩ := Set.exists_of_ssubset hY'
        cases b
        · exact hb' rfl
        · exact h ⟨hb, trivial⟩
      · exact (hZ'.2 (Set.subset_univ _)).elim
    · refine ⟨by simp, fun Y' hY' _ => ?_, fun Z' hZ' h => ?_⟩
      · exact (hY'.2 (Set.subset_univ _)).elim
      · obtain ⟨b, hb, hb'⟩ := Set.exists_of_ssubset hZ'
        cases b
        · exact hb' rfl
        · exact h ⟨trivial, hb⟩

theorem sinkless_half_g_iff {Δ : ℕ} {Y Z : Set Bool} :
    ({Y, Z} : Multiset (Set Bool)) ∈ sinklessColoring.edgeStepMax.g Δ ↔
      (Y = {false} ∧ Z = Set.univ) ∨ (Y = Set.univ ∧ Z = {false}) := by
  rw [edgeStepMax_g_iff, sinkless_edgeAllMax]

theorem count_map_range (Δ : ℕ) (b : ℕ → Bool) :
    ((Multiset.range Δ).map b).count true =
      ((Finset.range Δ).filter (fun i => b i = true)).card := by
  rw [Multiset.count_map, Finset.card_def, Finset.filter_val, Finset.range_val]
  congr 1
  exact Multiset.filter_congr fun _ _ => eq_comm

/-- Node configurations of `Π'_{1/2}` = sinkless orientation: some choice has exactly one `1`. -/
theorem sinkless_half_h_iff {Δ : ℕ} {y : ℕ → Set Bool} :
    (Multiset.range Δ).map y ∈ sinklessColoring.edgeStepMax.h Δ ↔
      ∃ b : ℕ → Bool, (∀ i < Δ, b i ∈ y i) ∧
        ((Finset.range Δ).filter (fun i => b i = true)).card = 1 := by
  show sinklessColoring.NodeEx Δ _ ↔ _
  rw [nodeEx_map_range]
  constructor
  · rintro ⟨-, -, b, hb, -, hc⟩
    exact ⟨b, hb, by rw [← count_map_range]; exact hc⟩
  · rintro ⟨b, hb, hc⟩
    exact ⟨le_rfl, fun _ _ => Set.subset_univ _, b, hb, by simp,
      by rw [count_map_range]; exact hc⟩

open Classical in
/-- The node part of "`Π'_1` relaxes to sinkless colouring": in a node configuration of `Π'_1`
whose sets are all usable (contain `{0}` or `{0, 1}`), exactly one set misses `{0}`. -/
theorem sinkless_node {Δ : ℕ} {W : ℕ → Set (Set Bool)}
    (hW : (Multiset.range Δ).map W ∈ sinklessColoring.speedupMax.h Δ)
    (huse : ∀ i < Δ, {false} ∈ W i ∨ Set.univ ∈ W i) :
    ((Finset.range Δ).filter (fun i => {false} ∉ W i)).card = 1 := by
  have hNA : ∀ y : ℕ → Set Bool, (∀ i < Δ, y i ∈ W i) → ∃ b : ℕ → Bool,
      (∀ i < Δ, b i ∈ y i) ∧ ((Finset.range Δ).filter (fun i => b i = true)).card = 1 :=
    fun y hy => sinkless_half_h_iff.1 ((nodeAll_map_range.1 hW.1).2.2 y hy)
  refine le_antisymm (Finset.card_le_one.2 fun a ha c hc => ?_) (Finset.one_le_card.2 ?_)
  · simp only [Finset.mem_filter, Finset.mem_range] at ha hc
    by_contra hac
    have hua : Set.univ ∈ W a := (huse a ha.1).resolve_left ha.2
    have huc : Set.univ ∈ W c := (huse c hc.1).resolve_left hc.2
    -- maximality at `a`: adding `{false}` to `W a` breaks Property 4
    have hmax := hW.2 (W a) (Multiset.mem_map.2 ⟨a, Multiset.mem_range.2 ha.1, rfl⟩)
      (insert {false} (W a)) (Set.ssubset_insert ha.2)
    have : ¬ ∀ y : ℕ → Set Bool, (∀ i < Δ, y i ∈ Function.update W a (insert {false} (W a)) i) →
        ∃ b : ℕ → Bool, (∀ i < Δ, b i ∈ y i) ∧
          ((Finset.range Δ).filter (fun i => b i = true)).card = 1 := by
      intro h
      apply hmax
      have e := ViewSystem.map_range_update ha.1 W (insert {false} (W a))
      rw [← e]
      · rw [nodeAll_map_range]
        refine ⟨le_rfl, fun _ _ => fun _ _ => Set.subset_univ _, fun y hy => ?_⟩
        exact sinkless_half_h_iff.2 (h y hy)
    push Not at this
    obtain ⟨y, hy, hbad⟩ := this
    have hya : y a = {false} ∨ y a ∈ W a := by
      have := hy a ha.1; rw [Function.update_self] at this; exact this
    have hyo : ∀ i < Δ, i ≠ a → y i ∈ W i := fun i hi hia => by
      have := hy i hi; rwa [Function.update_of_ne hia] at this
    rcases hya with hya | hya
    · -- replace `{false}` at `a` by `univ ∈ W a`
      obtain ⟨b, hb, hcard⟩ := hNA (Function.update y a Set.univ) fun i hi => by
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hua
        · rw [Function.update_of_ne hia]; exact hyo i hi hia
      have hba : b a = true := by
        by_contra hba
        refine hbad b (fun i hi => ?_) hcard
        by_cases hia : i = a
        · subst hia; rw [hya]; simp [Bool.eq_false_iff.2 hba]
        · have := hb i hi; rwa [Function.update_of_ne hia] at this
      -- all other ports must be `false` in `b`, so `y i ∋ false`
      have hfilt : (Finset.range Δ).filter (fun i => b i = true) = {a} := by
        obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
        have : a ∈ (Finset.range Δ).filter (fun i => b i = true) := by simp [ha.1, hba]
        rw [hx] at this ⊢; rw [Finset.mem_singleton.1 this]
      have hfalse : ∀ i < Δ, i ≠ a → b i = false := fun i hi hia => by
        by_contra h'
        have : i ∈ (Finset.range Δ).filter (fun i => b i = true) := by
          simp [hi, Bool.not_eq_false _ ▸ h']
        rw [hfilt, Finset.mem_singleton] at this; exact hia this
      -- if some other `y i` contains `true`, `y` is good
      have hyc : y c = {false} := by
        rw [set_bool_eq_false]
        refine ⟨?_, fun htc => ?_⟩
        · have := hb c hc.1; rwa [Function.update_of_ne (Ne.symm hac), hfalse c hc.1 (Ne.symm hac)]
            at this
        · refine hbad (fun i => decide (i = c)) (fun i hi => ?_) ?_
          · by_cases hic : i = c
            · subst hic; simpa using htc
            · have := hb i hi
              by_cases hia : i = a
              · subst hia; rw [hya]; simp [hic]
              · rw [Function.update_of_ne hia, hfalse i hi hia] at this; simpa [hic] using this
          · rw [Finset.card_eq_one]; exact ⟨c, by ext i; simp [hc.1]⟩
      exact hc.2 (hyc ▸ hyo c hc.1 (Ne.symm hac))
    · obtain ⟨b, hb, hcard⟩ := hNA y fun i hi => by
        by_cases hia : i = a
        · subst hia; exact hya
        · exact hyo i hi hia
      exact hbad b hb hcard
  · by_contra hne
    simp only [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff, Finset.mem_range,
      not_not] at hne
    obtain ⟨b, hb, hcard⟩ := hNA (fun _ => {false}) hne
    have : (Finset.range Δ).filter (fun i => b i = true) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
        not_and]
      intro hi; have := hb i hi; simp at this; simp [this]
    rw [this] at hcard; simp at hcard

theorem sinkless_one_g {Δ : ℕ} {W X : Set (Set Bool)}
    (h : ({W, X} : Multiset _) ∈ sinklessColoring.speedupMax.g Δ) :
    ({false} ∈ W ∨ Set.univ ∈ W) ∧ ({false} ∈ X ∨ Set.univ ∈ X) ∧ ({false} ∈ W ∨ {false} ∈ X) := by
  obtain ⟨-, -, y, hy, z, hz, hyz⟩ := nodeStepMax_g_iff.1 h
  rcases sinkless_half_g_iff.1 hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Or.inl hy, Or.inr hz, Or.inl hy⟩
  · exact ⟨Or.inr hy, Or.inl hz, Or.inr hz⟩

open Classical in
/-- **`Π'_1` is at least as hard as sinkless colouring** (§4.4, "we are back at sinkless
colouring"): on `Δ`-regular graphs, the node-local label map `W ↦ ({0} ∉ W)` turns solutions of
`Π'_1` into solutions of `Π`. -/
theorem speedupMax_sinkless_relax {I : Type} {n Δ t : ℕ} {𝒢 : Set (LGraph I n)}
    (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) (h : SolvableIn 𝒢 sinklessColoring.speedupMax Δ t) :
    SolvableIn 𝒢 sinklessColoring Δ t := by
  refine h.post (fun _ W i => decide ({false} ∉ W i)) fun G hG out hout => ?_
  refine ⟨fun _ _ _ => trivial, fun v i hi => ?_, fun v => ?_⟩
  · rw [sinkless_g_iff]
    rintro ⟨h1, h2⟩
    simp only [decide_eq_true_eq] at h1 h2
    rcases (sinkless_one_g (hout.2.1 v i hi)).2.2 with h3 | h3
    exacts [h1 h3, h2 h3]
  · refine ⟨by simp [hreg G hG v], ?_⟩
    rw [count_map_range]
    have := sinkless_node (Δ := Δ) (W := out v) (by have := hout.2.2 v; rwa [hreg G hG v] at this)
      fun i hi => (sinkless_one_g (hout.2.1 v i (by rw [hreg G hG v]; exact hi))).1
    rw [hreg G hG v]
    simpa only [decide_eq_true_eq] using this

/-- The class contains, for all ports `p, q`, an edge from port `p` of a node all of whose edges
are outgoing (input list `ιout`) to port `q` of a node all of whose edges are incoming (`ιin`).
This holds e.g. for the class of all `Δ`-regular graphs of a given girth with all port numberings
and all edge orientations (when nonempty); we take it as a hypothesis. -/
def SinklessRich {I : Type} {n : ℕ} (𝒢 : Set (LGraph I n)) (Δ : ℕ) (o : I → Bool) : Prop :=
  ∃ ιout ιin : List I, (∀ x ∈ ιout, o x = true) ∧ (∀ x ∈ ιin, o x = false) ∧
    ∀ p < Δ, ∀ q < Δ, ∃ G ∈ 𝒢, ∃ v, p < G.deg v ∧ G.inputs v = ιout ∧
      G.inputs (G.nbr v p) = ιin ∧ G.rport v p = q

/-- No 0-round algorithm for sinkless colouring. -/
theorem sinkless_not_zero_round {I : Type} {n Δ : ℕ} {𝒢 : Set (LGraph I n)} (hΔ : 1 ≤ Δ)
    (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool} (hrich : SinklessRich 𝒢 Δ o) :
    ¬ SolvableIn 𝒢 sinklessColoring Δ 0 := by
  rw [solvableIn_iff_view]
  rintro ⟨F, hF⟩
  obtain ⟨ιout, ιin, -, -, hr⟩ := hrich
  -- the port chosen by a node with inputs `ι` (which occurs in the class)
  have hpick : ∀ G ∈ 𝒢, ∀ v, ∃ p < Δ, F (G.inputs v) p = true := by
    intro G hG v
    have := ((hF G hG).2.2 v).2
    rw [count_map_range] at this
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 this
    have hp := hp ▸ Finset.mem_singleton_self p
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨p, hreg G hG v ▸ hp.1, hp.2⟩
  obtain ⟨G₀, hG₀, v₀, -, h₀, -, -⟩ := hr 0 hΔ 0 hΔ
  obtain ⟨p, hp, hFp⟩ := hpick G₀ hG₀ v₀
  obtain ⟨G₁, hG₁, v₁, -, -, h₁, -⟩ := hr 0 hΔ 0 hΔ
  obtain ⟨q, hq, hFq⟩ := hpick G₁ hG₁ (G₁.nbr v₁ 0)
  obtain ⟨G, hG, v, hpv, hv, hu, hpq⟩ := hr p hp q hq
  have := (hF G hG).2.1 v p hpv
  rw [sinkless_g_iff] at this
  apply this
  refine ⟨?_, ?_⟩
  · show F (G.inputs v) p = true
    rw [hv, ← h₀]; exact hFp
  · show F (G.inputs (G.nbr v p)) (G.rport v p) = true
    rw [hu, hpq, ← h₁]; exact hFq

/-- **Lower bound for sinkless colouring** (§4.4): on a class of `Δ`-regular graphs (`Δ ≥ 1`)
with an input edge orientation, which is `t'`-independent for all `1 ≤ t' ≤ t` and `SinklessRich`,
sinkless colouring cannot be solved in `t` rounds. (Theorem 2 applied `t` times, with
`speedupMax_sinkless_relax`.) -/
theorem sinklessColoring_lower_bound {I : Type} {n Δ : ℕ} {𝒢 : Set (LGraph I n)} (hΔ : 1 ≤ Δ)
    (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool} (hor : HasOrientation 𝒢 o)
    (hrich : SinklessRich 𝒢 Δ o) (t : ℕ) (hind : ∀ t', 1 ≤ t' → t' ≤ t → IsIndependent 𝒢 t') :
    ¬ SolvableIn 𝒢 sinklessColoring Δ t := by
  induction t with
  | zero => exact sinkless_not_zero_round hΔ hreg hrich
  | succ t ih =>
    intro h
    have h1 := (theorem_2 (Nat.le_add_left 1 t) (fun G hG v => (hreg G hG v).le)
      (hind (t + 1) (Nat.le_add_left 1 t) le_rfl) hor sinklessColoring).1 h
    rw [Nat.add_sub_cancel] at h1
    exact ih (fun t' h1 h2 => hind t' h1 (Nat.le_succ_of_le h2))
      (speedupMax_sinkless_relax hreg h1)

/-- Sinkless orientation (§4.4): labels `Bool` (`true` at `(v, e)`: `e` is oriented away from
`v`); the two ends of an edge disagree; every node has an outgoing edge. -/
def sinklessOrientation : Problem Bool where
  f _ := Set.univ
  g _ := {{false, true}}
  h Δ := {m | Multiset.card m = Δ ∧ true ∈ m}

open Classical in
/-- Sinkless orientation relaxes to sinkless colouring (choose the first outgoing edge). -/
theorem sinklessOrientation_relax {I : Type} {n Δ t : ℕ} {𝒢 : Set (LGraph I n)}
    (h : SolvableIn 𝒢 sinklessOrientation Δ t) : SolvableIn 𝒢 sinklessColoring Δ t := by
  refine h.post (fun _ y i => decide (y i = true ∧ ∀ j < i, y j = false)) fun G hG out hout => ?_
  refine ⟨fun _ _ _ => trivial, fun v i hi => ?_, fun v => ?_⟩
  · rw [sinkless_g_iff]
    rintro ⟨h1, h2⟩
    simp only [decide_eq_true_eq] at h1 h2
    have := hout.2.1 v i hi
    rw [show sinklessOrientation.g Δ = {{false, true}} from rfl, Set.mem_singleton_iff,
      pair_eq_pair_iff, h1.1, h2.1] at this
    simp at this
  · obtain ⟨hc, ht⟩ := hout.2.2 v
    simp only [Multiset.card_map, Multiset.card_range] at hc
    refine ⟨by simp [hc], ?_⟩
    rw [count_map_range, Finset.card_eq_one]
    obtain ⟨i, hi, hit⟩ := Multiset.mem_map.1 ht
    rw [Multiset.mem_range] at hi
    have hex : ∃ i, i < G.deg v ∧ out v i = true := ⟨i, hi, hit⟩
    refine ⟨Nat.find hex, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hjt, hjm⟩
      refine le_antisymm ?_ (Nat.find_min' hex ⟨hj, hjt⟩)
      by_contra hlt
      push Not at hlt
      have := hjm _ hlt
      rw [(Nat.find_spec hex).2] at this; cases this
    · rintro rfl
      refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj => ?_⟩
      have := Nat.find_min hex hj
      simp only [not_and, Bool.not_eq_true] at this
      exact this (lt_trans hj (Nat.find_spec hex).1)

/-- **Lower bound for sinkless orientation** (§4.4), under the same hypotheses. -/
theorem sinklessOrientation_lower_bound {I : Type} {n Δ : ℕ} {𝒢 : Set (LGraph I n)}
    (hΔ : 1 ≤ Δ) (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool} (hor : HasOrientation 𝒢 o)
    (hrich : SinklessRich 𝒢 Δ o) (t : ℕ) (hind : ∀ t', 1 ≤ t' → t' ≤ t → IsIndependent 𝒢 t') :
    ¬ SolvableIn 𝒢 sinklessOrientation Δ t := fun h =>
  sinklessColoring_lower_bound hΔ hreg hor hrich t hind (sinklessOrientation_relax h)

end AutomaticSpeedup
