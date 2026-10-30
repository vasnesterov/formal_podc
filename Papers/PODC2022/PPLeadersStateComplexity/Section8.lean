import Papers.PODC2022.PPLeadersStateComplexity.Bottom
import Papers.PODC2022.PPLeadersStateComplexity.ControlStates
import Papers.PODC2022.PPLeadersStateComplexity.Stabilized
import Papers.PODC2022.PPLeadersStateComplexity.Arith

/-!
# The Petri net with control-states of Section 8

For a net `T`, a set of places `Q` and a finite set `S` of `Q`-configurations closed under the
steps of `T|_Q`, the edges are the triples `(s, t, s')` with `s ∈ S`, `t ∈ T` and `s →t|_Q s'`.
Paths in this graph are exactly the runs of `T|_Q` inside `S` (`path_of_run`, `run_of_path`).
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

namespace Sec8

variable {P : Type*} [Fintype P] [DecidableEq P]

open Classical in
/-- The edges `(s, t, s')` with `s ∈ S`, `t ∈ T`, `s →t|_Q s'`. -/
noncomputable def edges (T : Finset (Trans P)) (Q : Finset P) (S : Finset (Config P)) :
    Finset (Edge (Config P) (Trans P)) :=
  ((S ×ˢ T).filter fun x => (x.2.res Q).1 ≤ x.1).image
    fun x => (x.1, x.2, x.1 - (x.2.res Q).1 + (x.2.res Q).2)

variable {T : Finset (Trans P)} {Q : Finset P} {S : Finset (Config P)}

theorem mem_edges {e : Edge (Config P) (Trans P)} :
    e ∈ edges T Q S ↔ e.1 ∈ S ∧ e.2.1 ∈ T ∧ (e.2.1.res Q).Step e.1 e.2.2 := by
  classical
  obtain ⟨s, t, s'⟩ := e
  simp only [edges, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Trans.step_iff]
  constructor
  · rintro ⟨x, ⟨⟨ha, hb⟩, hle⟩, hx⟩
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨ha, hb, hle, rfl⟩
  · rintro ⟨ha, hb, hle, rfl⟩
    exact ⟨(s, t), ⟨⟨ha, hb⟩, hle⟩, rfl⟩

theorem card_edges_le : (edges T Q S).card ≤ S.card * T.card := by
  classical
  calc (edges T Q S).card ≤ _ := Finset.card_image_le
    _ ≤ (S ×ˢ T).card := Finset.card_filter_le _ _
    _ = S.card * T.card := Finset.card_product _ _

/-- `S` is closed under the steps of `T|_Q`. -/
def Closed (T : Finset (Trans P)) (Q : Finset P) (S : Finset (Config P)) : Prop :=
  ∀ s ∈ S, ∀ t ∈ T, ∀ s', (t.res Q).Step s s' → s' ∈ S

theorem edges_sub (hS : Closed T Q S) : ∀ e ∈ edges T Q S, e.1 ∈ S ∧ e.2.2 ∈ S := by
  intro e he
  obtain ⟨h1, h2, h3⟩ := mem_edges.1 he
  exact ⟨h1, hS _ h1 _ h2 _ h3⟩

theorem path_of_run (hS : Closed T Q S) {σ : List (Trans P)} (hσ : IsWord T σ) {s s' : Config P}
    (hs : s ∈ S) (h : Run (σ.map (Trans.res Q)) s s') :
    ∃ π, IsPath (edges T Q S) s π s' ∧ π.map (fun e => e.2.1) = σ := by
  induction σ generalizing s with
  | nil => exact ⟨[], h, rfl⟩
  | cons t σ ih =>
    obtain ⟨γ, h1, h2⟩ := h
    have ht : t ∈ T := hσ t (List.mem_cons_self ..)
    have hγ : γ ∈ S := hS s hs t ht γ h1
    obtain ⟨π, hπ, hπσ⟩ := ih (fun u hu => hσ u (List.mem_cons_of_mem _ hu)) hγ h2
    exact ⟨(s, t, γ) :: π, ⟨mem_edges.2 ⟨hs, ht, h1⟩, rfl, hπ⟩, by simp [hπσ]⟩

theorem run_of_path {π : List (Edge (Config P) (Trans P))} {s s' : Config P}
    (h : IsPath (edges T Q S) s π s') :
    IsWord T (π.map fun e => e.2.1) ∧ Run ((π.map fun e => e.2.1).map (Trans.res Q)) s s' := by
  induction π generalizing s with
  | nil => exact ⟨fun _ h => by simp at h, h⟩
  | cons e π ih =>
    obtain ⟨he, rfl, hπ⟩ := h
    obtain ⟨h1, h2, h3⟩ := mem_edges.1 he
    obtain ⟨ih1, ih2⟩ := ih hπ
    refine ⟨fun u hu => ?_, ⟨e.2.2, h3, ih2⟩⟩
    rcases List.mem_cons.1 hu with rfl | hu
    exacts [h2, ih1 u hu]

theorem disp_eq_wordDelta (π : List (Edge (Config P) (Trans P))) (p : P) :
    disp Trans.delta π p = wordDelta (π.map fun e => e.2.1) p := by
  simp [disp, wordDelta, List.map_map, Function.comp_def]

theorem disp_eq_coe {δ : Trans P → P → ℤ} (π : List (Edge (Config P) (Trans P))) (p : P) :
    disp δ π p = (((π : Multiset (Edge (Config P) (Trans P)))).map fun e => δ e.2.1 p).sum := by
  simp [disp]

/-! ### The component of a bottom configuration -/

theorem closed_component {x₀ : Config P} (hbot : IsBottom (resNet Q T) x₀) :
    Closed T Q hbot.1.toFinset := by
  intro s hs t ht s' hst
  rw [Set.Finite.mem_toFinset] at hs ⊢
  have h1 : Reach (resNet Q T) s s' :=
    ⟨[t.res Q], fun u hu => by
      simp only [List.mem_singleton] at hu; exact hu ▸ Finset.mem_image_of_mem _ ht,
      run_singleton.2 hst⟩
  have h2 : Reach (resNet Q T) x₀ s' := hs.1.trans h1
  exact ⟨h2, hbot.2 _ h2⟩

theorem mem_component_self {x₀ : Config P} (hbot : IsBottom (resNet Q T) x₀) :
    x₀ ∈ hbot.1.toFinset := by
  rw [Set.Finite.mem_toFinset]
  exact ⟨Reach.refl _ _, Reach.refl _ _⟩

theorem stronglyConnected_component {x₀ : Config P} (hbot : IsBottom (resNet Q T) x₀) :
    StronglyConnected (edges T Q hbot.1.toFinset) hbot.1.toFinset := by
  intro s hs s' hs'
  have hs1 := hs
  rw [Set.Finite.mem_toFinset] at hs1 hs'
  obtain ⟨σ₀, hσ₀, hrun⟩ := hs1.2.trans hs'.1
  obtain ⟨σ, hσ, rfl⟩ := hσ₀.exists_of_resNet
  obtain ⟨π, hπ, -⟩ := path_of_run (closed_component hbot) hσ hs hrun
  exact ⟨π, hπ⟩

/-! ### Auxiliary facts -/

theorem trans_res_res {Q Q' : Finset P} (h : Q ⊆ Q') (t : Trans P) :
    (t.res Q').res Q = t.res Q := by
  simp [Trans.res, Finset.inter_eq_left.2 h]

theorem map_flatten_replicate {α β : Type*} (f : α → β) (k : ℕ) (σ : List α) :
    (List.flatten (List.replicate k σ)).map f = List.flatten (List.replicate k (σ.map f)) := by
  simp [List.map_flatten, List.map_replicate]

theorem length_flatten_replicate {α : Type*} (k : ℕ) (σ : List α) :
    (List.flatten (List.replicate k σ)).length = k * σ.length := by
  simp [List.length_flatten, List.map_replicate, List.sum_replicate]

theorem mem_flatten_replicate {α : Type*} {k : ℕ} {σ : List α} {x : α}
    (h : x ∈ List.flatten (List.replicate k σ)) : x ∈ σ := by
  simp only [List.mem_flatten, List.mem_replicate] at h
  obtain ⟨l, ⟨-, rfl⟩, hx⟩ := h
  exact hx

theorem IsWord.flatten_replicate {T : Finset (Trans P)} {σ : List (Trans P)} (h : IsWord T σ)
    (k : ℕ) : IsWord T (List.flatten (List.replicate k σ)) :=
  fun t ht => h t (mem_flatten_replicate ht)

theorem isPath_flatten_replicate {V L : Type*} [DecidableEq V] [DecidableEq L]
    {E : Finset (Edge V L)} {s : V} {θ : List (Edge V L)} (h : IsPath E s θ s) (k : ℕ) :
    IsPath E s (List.flatten (List.replicate k θ)) s := by
  induction k with
  | zero => exact rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons]
    exact isPath_append.2 ⟨s, h, ih⟩

theorem count_flatten_replicate {α : Type*} [DecidableEq α] (k : ℕ) (σ : List α) (x : α) :
    (List.flatten (List.replicate k σ)).count x = k * σ.count x := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.count_append, ih]; ring

/-- Runs of a net acting on `U` keep configurations vanishing outside `U`. -/
theorem Run.vanish {U : Finset P} {T : Finset (Trans P)} (hT : NetOn U T) {σ : List (Trans P)}
    (hσ : IsWord T σ) {α β : Config P} (h : Run σ α β) (hα : ∀ p ∉ U, α p = 0) :
    ∀ p ∉ U, β p = 0 := by
  intro p hp
  have h1 := h.apply_eq p
  have h2 : wordDelta σ p = 0 := by
    simp only [wordDelta]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e1, e2⟩ := hT t (hσ t ht) p hp
    simp [Trans.delta, e1, e2]
  rw [hα p hp, h2] at h1
  omega

theorem isInput_single (Pr : Protocol P) {i : P} (hI : Pr.I = {i}) (c : ℕ) :
    Pr.IsInput (Pi.single i c) := by
  intro p hp
  rw [hI, Finset.mem_singleton] at hp
  simp [hp]

/-- A `(T, γ⁻¹(0))`-stabilized configuration reaches no `1`-output stable configuration. -/
theorem not_S1 (Pr : Protocol P) {T : Finset (Trans P)} (hR : ∀ α β, Pr.R α β ↔ Reach T α β)
    {μ : Config P} (hμ : Stabilized T (Finset.univ.filter fun p => Pr.γ p = Out.zero) μ)
    {β : Config P} (hβ : Pr.R μ β) : β ∉ Pr.S1 := by
  intro h1
  have h2 := h1 β (Pr.refl β)
  have : Out.one ∈ Pr.outputs β := by rw [h2]; rfl
  obtain ⟨p, hp, hγ⟩ := this
  have := hμ β ((hR _ _).1 hβ) p (by simp [hγ])
  omega

/-- If an initial configuration with `c ≥ n` input agents reaches a stabilized configuration,
the protocol does not stably compute `(i ≥ n)`. -/
theorem false_of_reach_stabilized (Pr : Protocol P) {T : Finset (Trans P)}
    (hR : ∀ α β, Pr.R α β ↔ Reach T α β) {i : P} {n c : ℕ} (hc : Pr.StablyComputesGe i n)
    (hnc : n ≤ c) {μ : Config P} (hr : Reach T (Pr.leaders + Pi.single i c) μ)
    (hμ : Stabilized T (Finset.univ.filter fun p => Pr.γ p = Out.zero) μ) : False := by
  obtain ⟨β, hβ, hβS⟩ := hc.2 _ (isInput_single Pr hc.1 c) μ ((hR _ _).2 hr)
  have : countingPred i n (Pi.single i c) = true := by simp [countingPred, hnc]
  rw [this] at hβS
  exact not_S1 Pr hR hμ hβ hβS

theorem single_add_single (i : P) (a b : ℕ) :
    (Pi.single i a : Config P) + Pi.single i b = Pi.single i (a + b) := by
  funext p; by_cases hp : p = i
  · subst hp; simp
  · simp [hp]

theorem res_single_of_not_mem {U : Finset P} {i : P} (hi : i ∉ U) (c : ℕ) :
    res U (Pi.single i c : Config P) = 0 := by
  funext p; by_cases hp : p = i
  · subst hp; simp [hi]
  · by_cases hpU : p ∈ U <;> simp [res, hp, hpU]

theorem card_le_box {T : Finset (Trans P)} :
    T.card ≤ (netNorm T + 1) ^ (2 * Fintype.card P) := by
  classical
  have hsub : T ⊆ box (netNorm T) ×ˢ box (netNorm T) := by
    intro t ht
    simp only [Finset.mem_product, mem_box]
    exact ⟨fun p => (t.fst_le_supNorm p).trans (le_netNorm ht),
      fun p => (t.snd_le_supNorm p).trans (le_netNorm ht)⟩
  calc T.card ≤ (box (netNorm T) ×ˢ box (netNorm T)).card := Finset.card_le_card hsub
    _ = (netNorm T + 1) ^ (2 * Fintype.card P) := by
      rw [Finset.card_product]
      simp [box, Fintype.card_piFinset, Finset.prod_const, two_mul, pow_add]

end Sec8

end Podc.PPLeadersStateComplexity
