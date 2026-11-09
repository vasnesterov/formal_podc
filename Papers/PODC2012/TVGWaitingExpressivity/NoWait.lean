import Papers.PODC2012.TVGWaitingExpressivity.Encoding
import Mathlib.Tactic.FinCases

/-!
# No waiting: every language is `L_nowait` of a 3-node TVG (Theorem 3.1), and the
# time-dilated variant for bounded waiting (Theorem 5.1, the construction)

The TVG `G₂` of Section 3 has nodes `v₀ = 0`, `v₁ = 1`, `v₂ = 2` and, for every letter `i`, all
edges `(u, i, v)` with `v ∈ {v₁, v₂}`. Presence and latency depend only on the target:

* `ρ((u, i, v₁), t) = 1` iff `t ∈ φ(Σ*)` and `φ⁻¹(t).i ∈ L`,
* `ρ((u, i, v₂), t) = 1` iff `t ∈ φ(Σ*)` and `φ⁻¹(t).i ∉ L`,
* `ζ((u, i, v), t) = φ(φ⁻¹(t).i) - t`.

`v₀` is initial; `v₁` is accepting, and so is `v₀` iff `ε ∈ L`.

The TVG `G_{2,d}` of Section 5 replaces `t` by `⌊t / (d+1)⌋` in the tests and `φ` by
`φ_d = (d+1) φ` in the latency. (The paper writes `⌊t/(d+1)⌋ ∈ φ_d(Σ*)` and `ψ_d⁻¹(t)` in two of the
four formulas; these are typos for `⌊t/(d+1)⌋ ∈ φ(Σ*)` and `ψ_d(t)`.) We prove both constructions
correct at once: `G₂` is `G_{2,0}` (`G2_eq_G2d`).
-/

namespace Podc.TVGWaitingExpressivity

open TVG TVGAutomaton

variable {q : ℕ}

open Classical

/-- The TVG-automaton `G₂` of Section 3, with the encoding `φ` in base `b`
(the paper: `b = q = |Σ|`). -/
noncomputable def G2 (b : ℕ) (L : Language (Fin q)) : TVGAutomaton (Fin 3) (Fin q) where
  present e t := e.2.2 ≠ 0 ∧ t ∈ Set.range (phi (q := q) b) ∧ (e.2.2 = 1 ↔ phiInv b t ++ [e.2.1] ∈ L)
  latency e t := phi b (phiInv b t ++ [e.2.1]) - t
  init := {0}
  accept := {v | v = 1 ∨ (v = 0 ∧ [] ∈ L)}
  start := 0

/-- The TVG-automaton `G_{2,d}` of Section 5 (time dilated by `d + 1`), encoding in base `b`. -/
noncomputable def G2d (b d : ℕ) (L : Language (Fin q)) : TVGAutomaton (Fin 3) (Fin q) where
  present e t := e.2.2 ≠ 0 ∧ t / (d + 1) ∈ Set.range (phi (q := q) b) ∧
    (e.2.2 = 1 ↔ phiInv b (t / (d + 1)) ++ [e.2.1] ∈ L)
  latency e t := (d + 1) * phi b (phiInv b (t / (d + 1)) ++ [e.2.1]) - t
  init := {0}
  accept := {v | v = 1 ∨ (v = 0 ∧ [] ∈ L)}
  start := 0

theorem G2_eq_G2d (b : ℕ) (L : Language (Fin q)) : G2 b L = G2d b 0 L := by
  simp [G2, G2d]

/-- The node where the unique journey labelled `w` ends, having started in `u` after reading `p`. -/
noncomputable def endNode (L : Language (Fin q)) (u : Fin 3) (p w : List (Fin q)) : Fin 3 :=
  if w = [] then u else if p ++ w ∈ L then 1 else 2

variable {b : ℕ} (hb : 2 ≤ b) (hq : q ≤ b)
include hb hq

/-- The key invariant: in `G_{2,d}` with pauses of at most `d`, a journey that is in `u` at time
`φ_d(p)` and reads `w` ends exactly in `endNode L u p w` at time `φ_d(p.w)`; and such a journey
exists. (The induction in the proofs of Theorems 3.1 and 5.1.) -/
theorem G2d_journey_iff (d : ℕ) (L : Language (Fin q)) (u : Fin 3) (p w : List (Fin q))
    (v : Fin 3) (t' : ℕ) :
    (G2d b d L).Journey (waitAtMost d) u ((d + 1) * phi b p) w v t' ↔
      v = endNode L u p w ∧ t' = (d + 1) * phi b (p ++ w) := by
  induction w generalizing u p with
  | nil => simp [endNode]
  | cons a w ih =>
    rw [journey_cons_iff]
    have hlt := phi_lt_phi_append hb p a
    have hdiv : ∀ t₁, waitAtMost d ((d + 1) * phi b p) t₁ → t₁ / (d + 1) = phi b p := by
      intro t₁ ⟨h1, h2⟩
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; exact h1
      · rw [Nat.succ_mul, mul_comm]; omega
    have hlat : ∀ t₁, waitAtMost d ((d + 1) * phi b p) t₁ →
        t₁ + (G2d b d L).latency (u, a, (if p ++ [a] ∈ L then 1 else 2)) t₁ =
          (d + 1) * phi b (p ++ [a]) := by
      intro t₁ ht
      simp only [G2d, hdiv t₁ ht, phiInv_phi hb hq]
      obtain ⟨_, h2⟩ := ht
      have : (d + 1) * phi b p + d < (d + 1) * phi b (p ++ [a]) := by nlinarith
      omega
    have hend : endNode L (if p ++ [a] ∈ L then 1 else 2) (p ++ [a]) w = endNode L u p (a :: w) := by
      simp only [endNode, List.append_assoc, List.singleton_append, reduceCtorEq, ite_false]
      split_ifs <;> simp_all
    constructor
    · rintro ⟨v', t₁, hw, ⟨hv0, -, hv1⟩, hj⟩
      have hv' : v' = if p ++ [a] ∈ L then 1 else 2 := by
        rw [hdiv t₁ hw, phiInv_phi hb hq] at hv1
        change v' ≠ 0 at hv0
        change (v' = 1 ↔ _) at hv1
        split_ifs with h
        · exact hv1.mpr h
        · have : v' ≠ 1 := fun h' => h (hv1.mp h')
          revert hv0 this; fin_cases v' <;> simp
      subst hv'
      rw [hlat t₁ hw, ih] at hj
      rw [hend] at hj
      simpa [List.append_assoc] using hj
    · rintro ⟨rfl, rfl⟩
      have hw : waitAtMost d ((d + 1) * phi b p) ((d + 1) * phi b p) := ⟨le_rfl, by omega⟩
      refine ⟨if p ++ [a] ∈ L then 1 else 2, _, hw, ⟨by split_ifs <;> simp, ?_, ?_⟩, ?_⟩
      · exact ⟨p, (hdiv _ hw).symm⟩
      · rw [hdiv _ hw, phiInv_phi hb hq]; split_ifs with h <;> simp [h]
      · rw [hlat _ hw, ih, hend]; simp [List.append_assoc]

/-- The language of `G_{2,d}` with waiting at most `d` is `L` (the construction in the proof of
Theorem 5.1). -/
theorem G2d_LwaitAtMost (d : ℕ) (L : Language (Fin q)) : (G2d b d L).LwaitAtMost d = L := by
  ext w
  simp only [LwaitAtMost, lang]
  show (∃ s ∈ _, _) ↔ _
  have h0 : (G2d b d L).start = (d + 1) * phi (q := q) b [] := by simp [G2d]
  rw [h0]
  simp only [G2d_journey_iff hb hq, List.nil_append]
  simp only [G2d, Set.mem_singleton_iff, Set.mem_ofPred_eq, endNode, exists_eq_left]
  by_cases hw : w = []
  · subst hw; simp
  · simp only [hw, ite_false, List.nil_append]
    split_ifs with h <;> simp [h]

/-- **Theorem 3.1** of [CFGSY'12]: `L_nowait(G₂) = L`, for an arbitrary language `L` over `Fin q`
(encoding in base `b ≥ max 2 q`; the paper's base is `b = q`, so it needs `q ≥ 2`). -/
theorem theorem_3_1 (L : Language (Fin q)) : (G2 b L).Lnowait = L := by
  rw [G2_eq_G2d, ← LwaitAtMost_zero]
  exact G2d_LwaitAtMost hb hq 0 L

omit hb hq

/-- Every language over a finite alphabet is accepted without waiting by a 3-node TVG
(no computability assumption on `ρ`, `ζ` is needed; the unary alphabet is handled by base `q + 2`). -/
theorem Lnowait_eq_univ (q : ℕ) : LnowaitFamily (Fin q) = Set.univ := by
  refine Set.eq_univ_of_forall fun L => ⟨Fin 3, inferInstance, G2 (q + 2) L, ?_⟩
  exact theorem_3_1 (by omega) (by omega) L

/-- Every language over a finite alphabet is accepted by a 3-node TVG with waiting at most `d`. -/
theorem LwaitAtMost_eq_univ (q d : ℕ) : LwaitAtMostFamily (Fin q) d = Set.univ := by
  refine Set.eq_univ_of_forall fun L => ⟨Fin 3, inferInstance, G2d (q + 2) d L, ?_⟩
  exact G2d_LwaitAtMost (by omega) (by omega) d L

/-- The one-word language `{10}` over `{0, 1}`. -/
def L10 : Language (Fin 2) := {w | w = [1, 0]}

theorem mem_L10 {w : List (Fin 2)} : w ∈ L10 ↔ w = [1, 0] := Iff.rfl

/-- The start date matters: if journeys of `G₂` could start at any date, `G₂` would accept words
outside `L`. With `L = {10}` over `{0, 1}`, a journey starting in `v₀` at date `φ(1) = 3` reads `0`
and ends in the accepting node `v₁`, but `0 ∉ L`. -/
theorem G2_other_start_date :
    (G2 2 L10).Journey noWait 0 (phi (q := 2) 2 [1]) [0] 1 (phi (q := 2) 2 [1, 0]) ∧
      [0] ∉ L10 ∧ (1 : Fin 3) ∈ (G2 2 L10).accept := by
  refine ⟨?_, by simp [mem_L10], by simp [G2]⟩
  have := (G2d_journey_iff (b := 2) (q := 2) le_rfl le_rfl 0 L10 0 [1] [0] 1
    (phi (q := 2) 2 [1, 0])).mpr ⟨by simp [endNode, mem_L10], by simp⟩
  rw [G2_eq_G2d, ← waitAtMost_zero]
  simpa using this

end Podc.TVGWaitingExpressivity
