import Papers.PODC2014.NetworkConstructors.KRCMerge

/-!
# Protocol 7 (2RC) constructs a spanning ring (Theorem 11)

Protocol 7 (2RC) is, rule for rule, Protocol 8 (kRC) for `k = 2` (with the rule
`(l₃, l₁, 1) → (l₂, q₀, 0)`, which is how we read the corresponding kRC rule in general):
`δ_compat` checks this by `decide` along the state bijection `e`. Hence the closed set `S` of kRC
transports to 2RC, and Theorem 12 for `k = 2` gives an almost 2-regular network: all agents but at
most one have degree 2 and the remaining one has degree at most 1. By the handshake lemma that
agent would have even degree, hence degree 0, which is impossible in a connected network on
`n ≥ 3` agents. So the output is a spanning ring (`twoRC_constructs`).
-/

namespace Podc.NetworkConstructors.TwoRC

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 7 (2RC). -/
inductive St | q0 | q1 | q2 | l1 | l2 | l3
  deriving DecidableEq, Repr

open St

instance : Fintype St :=
  ⟨{q0, q1, q2, l1, l2, l3}, fun x => by cases x <;> simp⟩

/-- The transition function of Protocol 7 (2RC), as listed in the paper (unlisted triples are
ineffective). -/
def δ : St → St → Bool → St × St × Bool
  | q0, q0, false => (q1, l1, true)
  | q1, q0, false => (q2, q1, true)
  | q1, q1, false => (q2, q2, true)
  | l1, l1, false => (l2, q2, true)
  -- `(l₁, q_i, 0) → (q₂, l_{i+1}, 1)` for `i ∈ {0, 1}`
  | l1, q0, false => (q2, l1, true)
  | l1, q1, false => (q2, l2, true)
  -- swapping: `(l_i, q_j, 1) → (q_i, l_j, 1)` for `i, j ∈ {1, 2}`
  | l1, q1, true => (q1, l1, true)
  | l1, q2, true => (q1, l2, true)
  | l2, q1, true => (q2, l1, true)
  | l2, q2, true => (q2, l2, true)
  -- leader elimination: `(l_i, l_j, 1) → (q_i, l_j, 1)` for `i, j ∈ {1, 2}`
  | l1, l1, true => (q1, l1, true)
  | l1, l2, true => (q1, l2, true)
  | l2, l1, true => (q2, l1, true)
  | l2, l2, true => (q2, l2, true)
  -- opening cycles in the presence of other components
  | l2, q0, false => (l3, q1, true)
  | l2, l1, false => (l3, q2, true)
  | l2, l2, false => (l3, l3, true)
  | l3, q1, true => (l2, q0, false)
  | l3, q2, true => (l2, l1, false)
  | l3, l1, true => (l2, q0, false)
  | l3, l2, true => (l2, l1, false)
  | l3, l3, true => (l2, l2, false)
  | a, b, c => (a, b, c)

/-- **Protocol 7 (2RC)**: initial state `q₀`, all states are output states. -/
def P : Protocol St where
  init := q0
  out _ := true
  δ := δ

/-- The state bijection to kRC with `k = 2`. -/
def e : St → KRC.St 2
  | q0 => .q 0 (by omega)
  | q1 => .q 1 (by omega)
  | q2 => .q 2 (by omega)
  | l1 => .l 1 le_rfl (by omega)
  | l2 => .l 2 (by omega) (by omega)
  | l3 => .l 3 (by omega) le_rfl

/-- 2RC is kRC with `k = 2`, rule for rule. -/
theorem δ_compat : ∀ a b c, KRC.δ 2 le_rfl (e a) (e b) c =
    (e (δ a b c).1, e (δ a b c).2.1, (δ a b c).2.2) := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Configurations of 2RC as configurations of kRC (`k = 2`). -/
def φ (C : Config V St) : Config V (KRC.St 2) where
  st x := e (C.st x)
  edge := C.edge
  symm := C.symm

omit [Fintype V] in
theorem φ_interact (C : Config V St) (u v : V) :
    φ (P.interact C u v) = (KRC.kRC 2 le_rfl).interact (φ C) u v := by
  have h := δ_compat (C.st u) (C.st v) (C.edge u v)
  refine Config.ext (funext fun x => ?_) (funext fun x => funext fun y => ?_)
  · change e (if x = u then _ else _) = if x = u then _ else _
    simp only [KRC.kRC_δ]
    erw [h]
    split_ifs <;> rfl
  · change (if _ then _ else _) = if _ then _ else _
    simp only [KRC.kRC_δ]
    erw [h]
    rfl

omit [Fintype V] [DecidableEq V] in
theorem φ_init : φ (P.initConfig : Config V St) = (KRC.kRC 2 le_rfl).initConfig := rfl

omit [Fintype V] [DecidableEq V] in
theorem output_φ (C : Config V St) : P.output C = (KRC.kRC 2 le_rfl).output (φ C) := rfl

omit [Fintype V] in
theorem reachable_φ {C D : Config V St} (h : P.Reachable C D) :
    (KRC.kRC 2 le_rfl).Reachable (φ C) (φ D) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨u, v, huv, rfl⟩ := hst
    rw [φ_interact]
    exact ih.tail (Protocol.step_of_ne huv)

omit [Fintype V] in
theorem exists_of_reachable_φ {C : Config V St} {D' : Config V (KRC.St 2)}
    (h : (KRC.kRC 2 le_rfl).Reachable (φ C) D') : ∃ D, φ D = D' ∧ P.Reachable C D := by
  induction h with
  | refl => exact ⟨C, rfl, .refl⟩
  | tail _ hst ih =>
    obtain ⟨D, rfl, hR⟩ := ih
    obtain ⟨u, v, huv, rfl⟩ := hst
    exact ⟨P.interact D u v, φ_interact D u v, hR.tail (Protocol.step_of_ne huv)⟩

/-- Configurations of `S` (for `k = 2`) output a spanning ring when `n ≥ 3`. -/
theorem S_spanningRing (hn : 3 ≤ Fintype.card V) {C : Config V (KRC.St 2)} (hC : C ∈ KRC.S 2) :
    IsSpanningRing ((KRC.kRC 2 le_rfl).output C) := by
  have hout : ∀ q, (KRC.kRC 2 le_rfl).out q = true := fun _ => rfl
  obtain ⟨hverts, hconn, D, hD, hnot, hin⟩ := KRC.S_almostRegular le_rfl hn hC
  refine ⟨hverts, hconn, fun v => ?_⟩
  by_cases hv : v ∈ D
  · exfalso
    have hD1 : D = {v} := Finset.eq_singleton_iff_unique_mem.2
      ⟨hv, fun w hw => Finset.card_le_one.1 (by omega) w hw v hv⟩
    have hdeg : ∀ w, w ≠ v → C.deg w = 2 := fun w hw => by
      rw [← Protocol.ncard_neighborSet_output hout C w]
      exact hnot w (by simp [hD1, hw])
    have hdv : C.deg v ≤ 1 := by
      rw [← Protocol.ncard_neighborSet_output hout C v]
      exact (hin v hv).2
    have hconn' : C.active.Connected := (Protocol.output_connected_iff hout C).1 hconn
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨w, hwv⟩ := exists_ne v
    obtain ⟨p⟩ := hconn'.preconnected v w
    have hpos := KRC.deg_pos_of_adj (p.adj_snd (p.not_nil_of_ne hwv.symm))
    have hsum := C.active.sum_degrees_eq_twice_card_edges
    simp only [← Config.deg_eq_degree] at hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
      Finset.sum_congr rfl (fun w hw => hdeg w (Finset.ne_of_mem_erase hw)), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, smul_eq_mul] at hsum
    omega
  · exact hnot v hv

/-- **Theorem 11** of Michail–Spirakis (PODC 2014): Protocol 7 (2RC) constructs a spanning ring
(on every population of `n ≥ 3` agents). -/
theorem twoRC_constructs (hn : 3 ≤ Fintype.card V) : P.Constructs (V := V) IsSpanningRing := by
  refine P.constructs_of_reach (φ ⁻¹' KRC.S 2) ?_ ?_ ?_ ?_
  · rintro C D hC ⟨u, v, huv, rfl⟩
    change φ (P.interact C u v) ∈ KRC.S 2
    rw [φ_interact]
    exact (KRC.S_interact le_rfl hC huv).2
  · rintro C D hC ⟨u, v, huv, rfl⟩
    rw [output_φ, output_φ, φ_interact]
    exact KRC.S_output le_rfl hC (Protocol.step_of_ne huv)
  · intro C hC
    rw [output_φ]
    exact S_spanningRing hn hC
  · intro C hC
    have hR := reachable_φ hC
    rw [φ_init] at hR
    obtain ⟨D', hR', hD'⟩ := KRC.reach_S le_rfl (by omega) (φ C)
      (KRC.inv_reach le_rfl (KRC.inv_init le_rfl) hR)
    obtain ⟨D, rfl, hRD⟩ := exists_of_reachable_φ hR'
    exact ⟨D, hD', hRD⟩

/-- Non-vacuity: the hypothesis of Theorem 11 is satisfiable. -/
example : P.Constructs (V := Fin 3) IsSpanningRing := twoRC_constructs (by simp)

end Podc.NetworkConstructors.TwoRC
