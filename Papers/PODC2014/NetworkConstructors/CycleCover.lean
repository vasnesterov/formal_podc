import Papers.PODC2014.NetworkConstructors.Problems

/-!
# Protocol 4 (Cycle-Cover) constructs a cycle cover with waste 2 (Theorem 6, correctness)

States `q₀, q₁, q₂` (the index is the degree), rules
`(q₀, q₀, 0) → (q₁, q₁, 1)`, `(q₁, q₀, 0) → (q₂, q₁, 1)`, `(q₁, q₁, 0) → (q₂, q₂, 1)`.
The output states are `{q₂}` (the paper leaves `Q_out` implicit; with `Q_out = Q` the two wasted
agents would be part of the output, which then is not a cycle cover).

Every effective rule activates an inactive edge between two agents of degree `< 2`, so the
configurations in which the agents of degree `< 2` are pairwise adjacent are silent and are
reached. In such a configuration at most two agents have degree `< 2`, and (by the handshake
lemma) they are not adjacent to agents of degree 2: the output is a cycle cover on at least
`n − 2` agents.
-/

namespace Podc.NetworkConstructors.CycleCover

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 4 (Cycle-Cover). -/
inductive St | q0 | q1 | q2
  deriving DecidableEq, Repr

open St

instance : Fintype St := ⟨{q0, q1, q2}, fun x => by cases x <;> simp⟩

/-- The index of a state (the intended degree). -/
def St.idx : St → ℕ
  | q0 => 0
  | q1 => 1
  | q2 => 2

/-- The transition function of Protocol 4; unlisted triples are ineffective. -/
def δ : St → St → Bool → St × St × Bool
  | q0, q0, false => (q1, q1, true)
  | q1, q0, false => (q2, q1, true)
  | q1, q1, false => (q2, q2, true)
  | a, b, e => (a, b, e)

/-- Protocol 4 (Cycle-Cover): initial state `q₀`, output states `{q₂}`. -/
def P : Protocol St where
  init := q0
  out s := s == q2
  δ := δ

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The invariant: the index of every agent is its degree. -/
def Inv (C : Config V St) : Prop := ∀ u, (C.st u).idx = C.deg u

/-- Final configurations: agents of degree `< 2` are pairwise adjacent. -/
def Final (C : Config V St) : Prop :=
  Inv C ∧ ∀ u v, u ≠ v → C.st u ≠ q2 → C.st v ≠ q2 → C.edge u v = true

theorem inv_init : Inv (P.initConfig : Config V St) := by
  intro u
  simp [Protocol.initConfig, Config.deg, St.idx, P]

/-- Effective rules: the edge was inactive, both agents had index `< 2`, and both indices grow by
one; the rule activates the edge. -/
theorem δ_cases (a b : St) (e : Bool) :
    δ a b e = (a, b, e) ∨
      (e = false ∧ a ≠ q2 ∧ b ≠ q2 ∧ (δ a b e).2.2 = true ∧
        (δ a b e).1.idx = a.idx + 1 ∧ (δ a b e).2.1.idx = b.idx + 1) := by
  cases a <;> cases b <;> cases e <;> simp [δ, St.idx]

theorem inv_step {C D : Config V St} (hC : Inv C) (h : P.Step C D) : Inv D := by
  obtain ⟨u, v, huv, rfl⟩ := h
  rcases δ_cases (C.st u) (C.st v) (C.edge u v) with h | ⟨he, -, -, hnew, hu, hv⟩
  · rw [Protocol.interact_eq_self C h]; exact hC
  · intro x
    by_cases hxu : x = u
    · subst hxu
      rw [Protocol.interact_st_left, Protocol.deg_interact_activate_left huv he hnew]
      exact (show (P.δ _ _ _).1.idx = _ from hu).trans (by rw [hC])
    by_cases hxv : x = v
    · subst hxv
      rw [Protocol.interact_st_right C huv, Protocol.deg_interact_activate_right huv he hnew]
      exact (show (P.δ _ _ _).2.1.idx = _ from hv).trans (by rw [hC])
    rw [Protocol.interact_st_other C hxu hxv, Protocol.deg_interact_other hxu hxv]
    exact hC x

theorem inv_reachable {C : Config V St} (h : P.Reachable P.initConfig C) : Inv C := by
  induction h with
  | refl => exact inv_init
  | tail _ hst ih => exact inv_step ih hst

/-- Final configurations are silent. -/
theorem final_silent {C : Config V St} (hC : Final C) {u v : V} (huv : u ≠ v) :
    P.interact C u v = C := by
  apply Protocol.interact_eq_self
  rcases δ_cases (C.st u) (C.st v) (C.edge u v) with h | ⟨he, hu, hv, -⟩
  · exact h
  · rw [hC.2 u v huv hu hv] at he; exact absurd he (by simp)

theorem final_step {C D : Config V St} (hC : Final C) (h : P.Step C D) : D = C := by
  obtain ⟨u, v, huv, rfl⟩ := h
  exact final_silent hC huv

theorem idx_le_two (s : St) : s.idx ≤ 2 := by cases s <;> simp [St.idx]

theorem idx_eq_two {s : St} : s.idx = 2 ↔ s = q2 := by cases s <;> simp [St.idx]

/-- The potential: total missing degree. -/
def pot (C : Config V St) : ℕ := ∑ u, (2 - (C.st u).idx)

theorem reach_final {C : Config V St} (hC : Inv C) : ∃ D, P.Reachable C D ∧ Final D := by
  suffices h : ∀ D : Config V St, Inv D → ¬ Final D →
      ∃ E, P.Reachable D E ∧ Inv E ∧ pot E < pot D by
    obtain ⟨D, hCD, -, hD⟩ := exists_reach_of_measure (R := P.Step) Inv Final pot
      (fun D hD hnf => h D hD hnf) C hC
    exact ⟨D, hCD, hD⟩
  intro D hD hnf
  simp only [Final, hD, true_and, not_forall] at hnf
  obtain ⟨a, b, hab, ha, hb, he⟩ := hnf
  have he : D.edge a b = false := by simpa using he
  -- orient so that the initiator has index ≥ the responder's
  obtain ⟨u, v, huv, hu, hv, hev, heff⟩ : ∃ u v, u ≠ v ∧ D.st u ≠ q2 ∧ D.st v ≠ q2 ∧
      D.edge u v = false ∧ δ (D.st u) (D.st v) (D.edge u v) ≠ (D.st u, D.st v, D.edge u v) := by
    cases hsa : D.st a <;> cases hsb : D.st b <;> simp_all [δ]
    · exact ⟨a, b, hab, by simp [hsa], by simp [hsb], he, by simp [hsa, hsb, he]⟩
    · exact ⟨b, a, Ne.symm hab, by simp [hsb], by simp [hsa], by rw [D.symm]; exact he,
        by rw [D.symm]; simp [hsa, hsb, he]⟩
    · exact ⟨a, b, hab, by simp [hsa], by simp [hsb], he, by simp [hsa, hsb, he]⟩
    · exact ⟨a, b, hab, by simp [hsa], by simp [hsb], he, by simp [hsa, hsb, he]⟩
  rcases δ_cases (D.st u) (D.st v) (D.edge u v) with h | ⟨-, -, -, -, hiu, hiv⟩
  · exact absurd h heff
  refine ⟨P.interact D u v, Protocol.reachable_of_ne huv, inv_step hD (Protocol.step_of_ne huv),
    ?_⟩
  have hu2 : (D.st u).idx < 2 := lt_of_le_of_ne (idx_le_two _) (fun h => hu (idx_eq_two.1 h))
  have key : ∀ x, 2 - ((P.interact D u v).st x).idx ≤ 2 - (D.st x).idx := by
    intro x
    by_cases hxu : x = u
    · subst hxu; rw [Protocol.interact_st_left]; exact (show (P.δ _ _ _).1.idx = _ from hiu) ▸ by omega
    by_cases hxv : x = v
    · subst hxv; rw [Protocol.interact_st_right D huv]
      exact (show (P.δ _ _ _).2.1.idx = _ from hiv) ▸ by omega
    rw [Protocol.interact_st_other D hxu hxv]
  apply Finset.sum_lt_sum (fun x _ => key x) ⟨u, Finset.mem_univ _, ?_⟩
  rw [Protocol.interact_st_left]
  exact (show (P.δ _ _ _).1.idx = _ from hiu) ▸ by omega

/-! ### The final output is a cycle cover on at least `n − 2` agents -/

/-- In a final configuration at most two agents have degree `< 2`, and they are not adjacent to
agents of degree 2. -/
theorem final_low {C : Config V St} (hC : Final C) :
    (Finset.univ.filter fun u => C.st u ≠ q2).card ≤ 2 ∧
      ∀ u w, C.st u = q2 → C.st w ≠ q2 → u ≠ w → C.edge u w = false := by
  obtain ⟨hI, hF⟩ := hC
  set N := Finset.univ.filter fun u => C.st u ≠ q2 with hN
  -- every low agent is adjacent to every other low agent, and has degree ≤ 1
  have hdeg : ∀ x ∈ N, (N.erase x).card ≤ C.deg x := by
    intro x hx
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_erase, hN, Finset.mem_filter, Finset.mem_univ, true_and] at hy hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hy.1, hF x y (Ne.symm hy.1) hx hy.2⟩
  have hlow : ∀ x ∈ N, C.deg x ≤ 1 := by
    intro x hx
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [← hI x]
    have := idx_le_two (C.st x)
    have : (C.st x).idx ≠ 2 := fun h => hx (idx_eq_two.1 h)
    omega
  have hcard : N.card ≤ 2 := by
    by_contra hlt
    obtain ⟨x, hx⟩ : N.Nonempty := Finset.card_pos.1 (by omega)
    have := hdeg x hx
    rw [Finset.card_erase_of_mem hx] at this
    have := hlow x hx
    omega
  refine ⟨hcard, fun u w hu hw huw => ?_⟩
  by_contra hne
  have hne : C.edge u w = true := by simpa using hne
  have hwN : w ∈ N := by simp [hN, hw]
  -- `w` has degree 1, its only neighbour is `u`; so `w` is the only low agent
  have hw1 : C.deg w = 1 := by
    apply le_antisymm (hlow w hwN)
    apply Finset.card_pos.2
    exact ⟨u, by simp [huw, C.symm w u, hne]⟩
  have hNw : N = {w} := by
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hwN, fun x hx => ?_⟩
    by_contra hxw
    -- `w` would be adjacent to both `u` and `x`
    have hux : u ≠ x := by
      rintro rfl; simp [hN, hu] at hx
    have hx' : C.st x ≠ q2 := by simpa [hN] using hx
    have hwx := hF w x (Ne.symm hxw) hw hx'
    have : 2 ≤ C.deg w := by
      have hsub : ({u, x} : Finset V) ⊆ Finset.univ.filter fun v => v ≠ w ∧ C.edge w v = true := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hy with rfl | rfl
        · exact ⟨huw, by rw [C.symm]; exact hne⟩
        · exact ⟨hxw, hwx⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hux] at this
    omega
  -- handshake: the degree sum is even, but it is `2 (n − 1) + 1`
  have hsum : ∑ x, C.deg x = 2 * (Fintype.card V - 1) + 1 := by
    have : ∀ x, C.deg x = if x = w then 1 else 2 := by
      intro x
      split_ifs with hxw
      · rw [hxw, hw1]
      · rw [← hI x]
        apply idx_eq_two.2
        by_contra hx
        have : x ∈ N := by simp [hN, hx]
        rw [hNw] at this
        exact hxw (Finset.mem_singleton.1 this)
    rw [Finset.sum_congr rfl (fun x _ => this x),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ w), ite_eq_left rfl,
      Finset.sum_congr rfl (fun x hx => ite_eq_right (Finset.ne_of_mem_erase hx)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      smul_eq_mul]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨w⟩
    omega
  have heven : Even (∑ x, C.deg x) := by
    simp_rw [Config.deg_eq_degree]
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  rw [hsum] at heven
  exact Nat.not_even_two_mul_add_one _ heven

/-- The guarantee of Theorem 6: a cycle cover on at least `n − 2` agents (waste at most 2). -/
def CoverWaste2 (H : (⊤ : SimpleGraph V).Subgraph) : Prop :=
  IsCycleCover H ∧ Fintype.card V - 2 ≤ H.verts.ncard

omit [Fintype V] [DecidableEq V] in
theorem output_verts (C : Config V St) :
    (P.output C).verts = {u | C.st u = q2} := by
  ext u; simp [Protocol.output, P]

theorem final_target {C : Config V St} (hC : Final C) : CoverWaste2 (P.output C) := by
  obtain ⟨hcard, hnb⟩ := final_low hC
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [output_verts] at hv
    have hv : C.st v = q2 := hv
    rw [Protocol.output_neighborSet]
    have : {w | v ≠ w ∧ C.edge v w = true ∧ P.out (C.st v) = true ∧ P.out (C.st w) = true} =
        ↑(Finset.univ.filter fun w => w ≠ v ∧ C.edge v w = true) := by
      ext w
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, -, -⟩; exact ⟨Ne.symm h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨Ne.symm h1, h2, by simp [P, hv], ?_⟩
        by_contra hw
        have hw : C.st w ≠ q2 := by simpa [P] using hw
        rw [hnb v w hv hw (Ne.symm h1)] at h2
        exact absurd h2 (by simp)
    rw [this, Set.ncard_coe_finset, ← Config.deg, ← hC.1 v, hv]
    rfl
  · have hset : {u | C.st u = q2} = ↑(Finset.univ.filter fun u => C.st u = q2) := by simp
    rw [output_verts, hset, Set.ncard_coe_finset]
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun u => C.st u = q2)
    rw [Finset.card_univ] at this
    simp only [ne_eq] at hcard
    omega

/-- **Theorem 6 (correctness) of Michail–Spirakis.** Protocol Cycle-Cover (with output states
`{q₂}`) constructs a cycle cover with waste at most 2: in every globally fair execution the output
stabilizes to a cycle cover on at least `n − 2` agents. -/
theorem constructs_cycleCover : P.Constructs (V := V) CoverWaste2 := by
  refine P.constructs_of_reach {C | Final C} (fun C D hC hCD => ?_) (fun C D hC hCD => ?_)
    (fun C hC => final_target hC) (fun C hC => ?_)
  · rw [Set.mem_ofPred_eq, final_step hC hCD]; exact hC
  · rw [final_step hC hCD]
  · obtain ⟨D, hCD, hD⟩ := reach_final (inv_reachable hC)
    exact ⟨D, hD, hCD⟩

/-! ### The waste 2 is attained (`n = 5`) -/

/-- A configuration on 5 agents from agent states and a list of active edges. -/
def mk (s : Fin 5 → St) (es : List (Fin 5 × Fin 5)) : Config (Fin 5) St where
  st := s
  edge u v := decide ((u, v) ∈ es) || decide ((v, u) ∈ es)
  symm _ _ := Bool.or_comm _ _

/-- An execution prefix building a triangle on `{0, 1, 2}` and an edge `{3, 4}`. -/
def tightPath : List (Config (Fin 5) St) :=
  [mk ![q0, q0, q0, q0, q0] [],
   mk ![q1, q1, q0, q0, q0] [(0, 1)],
   mk ![q1, q2, q1, q0, q0] [(0, 1), (1, 2)],
   mk ![q2, q2, q2, q0, q0] [(0, 1), (1, 2), (0, 2)],
   mk ![q2, q2, q2, q1, q1] [(0, 1), (1, 2), (0, 2), (3, 4)]]

instance : DecidableRel (P.Step (V := Fin 5)) := fun C D => by
  unfold Protocol.Step; infer_instance

theorem tightPath_chain : tightPath.IsChain (P.Step (V := Fin 5)) := by decide

/-- The final configuration of `tightPath`. -/
def tightLast : Config (Fin 5) St := mk ![q2, q2, q2, q1, q1] [(0, 1), (1, 2), (0, 2), (3, 4)]

theorem tight_final : Final tightLast := ⟨by unfold Inv; decide, by decide⟩

theorem tight_reach : P.Reachable P.initConfig tightLast := by
  have h := List.relationReflTransGen_of_exists_isChain _ tightPath_chain (by simp [tightPath])
  rwa [show tightPath.head (by simp [tightPath]) = P.initConfig by decide,
    show tightPath.getLast (by simp [tightPath]) = tightLast by decide] at h

/-- **The waste in Theorem 6 is attained.** On `n = 5` agents some globally fair execution of
Cycle-Cover stabilizes to a cycle cover on exactly `n − 2 = 3` agents (a triangle, while the two
other agents stay connected in state `q₁` forever). -/
theorem waste_two_attained : ∃ E : Run (P.Step (V := Fin 5)), E.st 0 = P.initConfig ∧
    E.GloballyFair ∧ ∀ᶠ t in Filter.atTop, (P.output (E.st t)).verts.ncard = 3 := by
  obtain ⟨E, hE0, hfair, k, hk⟩ := exists_globallyFair_of_reach Protocol.step_total tight_reach
  refine ⟨E, hE0, hfair, Filter.eventually_atTop.2 ⟨k, fun t ht => ?_⟩⟩
  have : E.st t = tightLast := by
    induction t, ht using Nat.le_induction with
    | base => exact hk
    | succ t _ ih => rw [final_step (ih ▸ tight_final) (E.step t), ih]
  rw [this, output_verts]
  have hset : {u | tightLast.st u = q2} = ↑({0, 1, 2} : Finset (Fin 5)) := by
    ext u; revert u; decide
  rw [hset, Set.ncard_coe_finset]
  rfl

end Podc.NetworkConstructors.CycleCover
