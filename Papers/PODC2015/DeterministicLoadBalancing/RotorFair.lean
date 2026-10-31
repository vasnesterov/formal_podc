import Papers.PODC2015.DeterministicLoadBalancing.RotorRouter

/-!
# The ROTOR-ROUTER is cumulatively 1-fair

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, PODC 2015 (arXiv:1404.4344v4),
Observation 2.2 (second part), for the rotor-router without self-loops (`rotorRouter`).

The key identity is `rotorShare_add`: sending `a` tokens and then `b` tokens (from the advanced
rotor) puts on every edge exactly as many tokens as sending `a + b` tokens at once. Hence the
cumulative flow over the edge at position `i` after steps `0, …, t` is
`rotorShare (ρ₀ v) i (S v)`, where `S v` is the total number of tokens `v` has sent
(`cumFlow_rotorRouter`), and any two such values differ by at most `1`.
-/

open Finset Fin.NatCast

namespace Podc.DeterministicLoadBalancing

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

section RotorFair

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} [NeZero d]

/-- Value of `j - a` in `Fin d`, as a natural number. -/
lemma val_sub_natCast (j : Fin d) (a : ℕ) :
    ((j - (a : Fin d) : Fin d) : ℕ) =
      if a % d ≤ j.val then j.val - a % d else j.val + d - a % d := by
  have hd := NeZero.pos d
  have ha := Nat.mod_lt a hd
  have hj := j.isLt
  rw [Fin.val_sub, Fin.val_natCast]
  split_ifs with h
  · rw [show d - a % d + j.val = (j.val - a % d) + d by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- Sending `a` tokens and then `b` tokens from the advanced rotor `ρ + a` puts on every edge as
many tokens as sending `a + b` tokens at once. -/
lemma rotorShare_add (ρ i : Fin d) (a b : ℕ) :
    rotorShare ρ i a + rotorShare (ρ + (a : Fin d)) i b = rotorShare ρ i (a + b) := by
  have hd := NeZero.pos d
  unfold rotorShare
  have hj : (i - (ρ + (a : Fin d))) = (i - ρ) - (a : Fin d) := by abel
  rw [hj, val_sub_natCast]
  generalize (i - ρ) = j
  have hjd := j.isLt
  have ha := Nat.mod_lt a hd
  have hb := Nat.mod_lt b hd
  rw [Nat.add_div hd, Nat.add_mod]
  have hm : (a % d + b % d) % d = if d ≤ a % d + b % d then a % d + b % d - d
      else a % d + b % d := by
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hm]
  split_ifs <;> omega

lemma rotorShare_zero (ρ i : Fin d) : rotorShare ρ i 0 = 0 := by
  simp [rotorShare]

/-- Two edges of the same node receive rotor-router shares differing by at most `1`. -/
lemma rotorShare_le_add_one (ρ i j : Fin d) (x : ℕ) : rotorShare ρ i x ≤ rotorShare ρ j x + 1 := by
  unfold rotorShare
  split_ifs <;> omega

lemma div_le_rotorShare (ρ i : Fin d) (x : ℕ) : x / d ≤ rotorShare ρ i x := by
  unfold rotorShare
  omega

/-- Total number of tokens node `v` has sent in steps `0, …, t - 1`. -/
def sentTotal (A : Balancer G) (x₀ : V → ℕ) (t : ℕ) (v : V) : ℕ :=
  ∑ τ ∈ range t, A.load x₀ τ v

/-- The rotor of `v` at time `t` is the initial rotor advanced by the number of tokens sent so far. -/
lemma state_rotorRouter (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d) (x₀ : V → ℕ)
    (t : ℕ) (v : V) :
    @Eq (Fin d) ((rotorRouter ord ρ₀).state x₀ t v)
      (ρ₀ v + ((sentTotal (rotorRouter ord ρ₀) x₀ t v : ℕ) : Fin d)) := by
  induction t with
  | zero => simp [sentTotal, Balancer.state, Balancer.config, rotorRouter]
  | succ t ih =>
    rw [Balancer.state_succ]
    change @HAdd.hAdd (Fin d) (Fin d) (Fin d) _ ((rotorRouter ord ρ₀).state x₀ t v)
      ((rotorRouter ord ρ₀).load x₀ t v : Fin d) = _
    rw [ih, sentTotal, sentTotal, sum_range_succ, Nat.cast_add, add_assoc]

/-- The rotor-router flow in step `τ` over the edge at position `i`. -/
lemma flow_rotorRouter (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d)
    (x₀ : V → ℕ) {v w : V} (h : w ∈ G.neighborFinset v) (τ : ℕ) :
    (rotorRouter ord ρ₀).flow x₀ τ v w =
      rotorShare (ρ₀ v + ((sentTotal (rotorRouter ord ρ₀) x₀ τ v : ℕ) : Fin d))
        ((ord v).symm ⟨w, h⟩) ((rotorRouter ord ρ₀).load x₀ τ v) := by
  rw [← state_rotorRouter]
  exact rotorRouter_out_of_mem ord ρ₀ h _ _

/-- The cumulative rotor-router flow over the edge at position `i` is the rotor share of the total
number of tokens sent. -/
lemma sum_flow_rotorRouter (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d)
    (x₀ : V → ℕ) {v w : V} (h : w ∈ G.neighborFinset v) (t : ℕ) :
    ∑ τ ∈ range t, (rotorRouter ord ρ₀).flow x₀ τ v w =
      rotorShare (ρ₀ v) ((ord v).symm ⟨w, h⟩) (sentTotal (rotorRouter ord ρ₀) x₀ t v) := by
  induction t with
  | zero => simp [sentTotal, rotorShare_zero]
  | succ t ih =>
    rw [sum_range_succ, ih, flow_rotorRouter ord ρ₀ x₀ h, rotorShare_add, sentTotal, sentTotal, sum_range_succ]

/-- The cumulative flow `F_t(v, w)` of the rotor-router. -/
lemma cumFlow_rotorRouter (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d)
    (x₀ : V → ℕ) {v w : V} (h : w ∈ G.neighborFinset v) (t : ℕ) :
    (rotorRouter ord ρ₀).cumFlow x₀ t v w =
      rotorShare (ρ₀ v) ((ord v).symm ⟨w, h⟩) (sentTotal (rotorRouter ord ρ₀) x₀ (t + 1) v) :=
  sum_flow_rotorRouter ord ρ₀ x₀ h (t + 1)

lemma degree_eq_of_ord (ord : ∀ v, Fin d ≃ G.neighborFinset v) (v : V) : G.degree v = d := by
  rw [← G.card_neighborFinset_eq_degree, ← Fintype.card_coe, ← Fintype.card_congr (ord v),
    Fintype.card_fin]

/-- Observation 2.2 (second part) of [paper]: the ROTOR-ROUTER (here without self-loops,
`d◦ = 0`) is cumulatively `1`-fair. -/
theorem rotorRouter_cumulativelyFair (ord : ∀ v, Fin d ≃ G.neighborFinset v) (ρ₀ : V → Fin d) :
    (rotorRouter ord ρ₀).CumulativelyFair 0 1 := by
  intro x₀ t v
  refine ⟨fun w hw => ?_, ⟨fun _ => 0, by simp [Balancer.kept, rotorRouter], fun i => i.elim0⟩,
    fun w₁ hw₁ w₂ hw₂ => ?_⟩
  · rw [flow_rotorRouter ord ρ₀ x₀ hw, degree_eq_of_ord ord, add_zero]
    exact div_le_rotorShare _ _ _
  · rw [cumFlow_rotorRouter ord ρ₀ x₀ hw₁, cumFlow_rotorRouter ord ρ₀ x₀ hw₂]
    exact rotorShare_le_add_one _ _ _ _

end RotorFair

end Podc.DeterministicLoadBalancing
