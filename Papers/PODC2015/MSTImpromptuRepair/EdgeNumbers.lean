import Papers.PODC2015.MSTImpromptuRepair.HPTestOut

/-!
# Edge numbers and `HP-TestOut`

The paper defines the *edge number* of `{u, v}` as the concatenation of the endpoint IDs, smallest
first (`edgeNumber`), and uses it in `𝒫(D)(z) = ∏_{e ∈ D} (z - edge_number(e))` for sets `D` of
*ordered* pairs. Taken literally the number of `(u, v)` and of `(v, u)` coincide and `HP-TestOut`
never detects anything (`hpTestOut_edgeNumber_never`). With the *ordered* concatenation
(`dartNumber`) the numbers of distinct darts are distinct (`dartNumber_injective`), and all
hypotheses of `hpTestOut_error_lt` hold (`hpTestOut_dartNumber_error_lt`).
-/

namespace Podc.MSTImpromptuRepair

open Finset Cslib.Probability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Sym2 V → Prop) [DecidablePred P]

/-- The paper's edge number of `{u, v}` applied to the pair `(u, v)`: the concatenation (with
`b`-bit fields) of the two IDs, smallest first. -/
def edgeNumber (b : ℕ) (ident : V → ℕ) (d : V × V) : ℕ :=
  min (ident d.1) (ident d.2) * 2 ^ b + max (ident d.1) (ident d.2)

/-- The ordered dart number: the ID of the tail, then the ID of the head. -/
def dartNumber (b : ℕ) (ident : V → ℕ) (d : V × V) : ℕ := ident d.1 * 2 ^ b + ident d.2

theorem edgeNumber_swap (b : ℕ) (ident : V → ℕ) (d : V × V) :
    edgeNumber b ident d.swap = edgeNumber b ident d := by
  simp [edgeNumber, min_comm, max_comm]

/-- **With the paper's literal edge numbers, `HP-TestOut` always answers "no leaving edge".** -/
theorem hpTestOut_edgeNumber_never {p : ℕ} (b : ℕ) (ident : V → ℕ) (T : Finset V) (α : ZMod p) :
    ¬ hpTestOut G P (edgeNumber b ident) T α :=
  hpTestOut_symm_never G P _ (edgeNumber_swap b ident) T α

theorem dartNumber_injective {b : ℕ} {ident : V → ℕ} (hid : Function.Injective ident)
    (hlt : ∀ v, ident v < 2 ^ b) : Function.Injective (dartNumber b ident) := by
  intro d d' h
  unfold dartNumber at h
  have e : ∀ x y, y < 2 ^ b → (x * 2 ^ b + y) / 2 ^ b = x := fun x y hy => by
    rw [add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hy, zero_add]
  have e' : ∀ x y, y < 2 ^ b → (x * 2 ^ b + y) % 2 ^ b = y := fun x y hy => by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have h1 : ident d.1 = ident d'.1 := by
    have := congrArg (· / 2 ^ b) h
    simpa only [e _ _ (hlt _)] using this
  have h2 : ident d.2 = ident d'.2 := by
    have := congrArg (· % 2 ^ b) h
    simpa only [e' _ _ (hlt _)] using this
  exact Prod.ext (hid h1) (hid h2)

theorem dartNumber_lt {b : ℕ} {ident : V → ℕ} (hlt : ∀ v, ident v < 2 ^ b) (d : V × V) :
    dartNumber b ident d < 2 ^ (2 * b) := by
  unfold dartNumber
  have h1 := hlt d.1; have h2 := hlt d.2
  calc ident d.1 * 2 ^ b + ident d.2 < ident d.1 * 2 ^ b + 2 ^ b := by omega
    _ = (ident d.1 + 1) * 2 ^ b := by ring
    _ ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (2 * b) := by ring

/-- **`HP-TestOut` with ordered dart numbers** (inequality (2)): for distinct IDs below `2^b`, a
prime `p > 2^(2b)` (`p > maxEdgeNum`) with `p > D / ε` (`D` the sum of the degrees in `T`), the
test misses an existing leaving edge with probability `< ε`, and never reports a non-existing
one (`hpTestOut_false_of_no_cut`). -/
theorem hpTestOut_dartNumber_error_lt {p : ℕ} [Fact p.Prime] {b : ℕ} {ident : V → ℕ}
    (hid : Function.Injective ident) (hlt : ∀ v, ident v < 2 ^ b) (hp : 2 ^ (2 * b) ≤ p)
    (T : Finset V) {ε : ℝ} (hε : (#(Eup G P T) : ℝ) / ε < p) (hε0 : 0 < ε)
    (hcut : ∃ e ∈ cut G T, P e) :
    uprob (fun α : ZMod p => ¬ hpTestOut G P (dartNumber b ident) T α) < ε :=
  hpTestOut_error_lt (dartNumber b ident) T (dartNumber_injective hid hlt).injOn
    (fun d _ => lt_of_lt_of_le (dartNumber_lt hlt d) hp) hε hε0 hcut

end Podc.MSTImpromptuRepair
