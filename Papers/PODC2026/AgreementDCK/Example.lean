import Papers.PODC2026.AgreementDCK.Sufficiency

/-!
# A concrete AoN protocol: dynamic common knowledge without common knowledge

Non-vacuity check for the definitions and theorems of David–Moses (PODC 2026), and an
illustration of the paper's motivation (Halpern–Moses: common knowledge needs simultaneity).

Two processes, no failures, asynchronous delivery of one message. Runs are pairs `(b, d)`:
process `0` starts with the bit `b` (its local state is `some b` at all times) and sends it to
process `1`, which receives it at time `d + 1` for an arbitrary `d` chosen by the adversary (its
local state is `none` before delivery and `some b` afterwards). A process decides `v` when its local
state is `some v`.

* The protocol has local decisions, is AoN, and satisfies Agreement, Validity (`valid(v)`: the
  initial bit is `v`) and Decision (`example_spec`).
* Hence (Theorem 1.5) `all_decide(b)` is dynamic common knowledge w.r.t. `𝛅(b)` in every run
  (`example_CN`), and the decision facts satisfy all hypotheses of Theorem 1.7
  (`example_sufficient`).
* But the classical common knowledge of `b = v` (even `E²`) holds at no point
  (`example_not_C`).
-/

open Podc.Knowledge Podc.Knowledge.RunFact Podc.Knowledge.System Podc.Knowledge.Decisions

namespace Podc.Knowledge.Example

/-- The system of runs `(b, d)` described in the module docstring. -/
def S : System (Fin 2) (Bool × ℕ) (fun _ => Option Bool) where
  loc i r t := if i = 0 then some r.1 else if r.2 < t then some r.1 else none
  nf _ := Set.univ

/-- Process `i` decides `v` when its local state is `some v`. -/
def dec : Fin 2 → Bool → Fact (Bool × ℕ) := fun i v r t => S.loc i r t = some v

/-- Validity of the binary problem: `v` is the initial bit. -/
def valid : Bool → Bool × ℕ → Prop := fun v r => r.1 = v

lemma dec_iff {i : Fin 2} {v : Bool} {r : Bool × ℕ} {t : ℕ} :
    dec i v r t ↔ r.1 = v ∧ (i = 0 ∨ r.2 < t) := by
  fin_cases i <;> simp only [dec, S] <;> split_ifs <;> simp_all

lemma decides (i : Fin 2) (r : Bool × ℕ) : dec i r.1 r (r.2 + 1) :=
  dec_iff.2 ⟨rfl, Or.inr (Nat.lt_succ_self _)⟩

theorem example_spec :
    DecLocal S dec ∧ (∀ v, AoN S dec v) ∧ Agreement S dec ∧ Validity S dec valid ∧
      Decision S dec ∧ Stable S dec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v r t r' t' h
    simp only [dec, h]
  · intro v i r t _ h j _
    obtain ⟨rfl, -⟩ := dec_iff.1 h
    exact ⟨_, decides j r⟩
  · intro i j r t t' v w _ _ hv hw
    exact (dec_iff.1 hv).1.symm.trans (dec_iff.1 hw).1
  · intro v i r t _ h
    exact (dec_iff.1 h).1
  · intro r i _
    exact ⟨r.1, _, decides i r⟩
  · intro i v r t t' _ htt' h
    obtain ⟨h1, h2⟩ := dec_iff.1 h
    exact dec_iff.2 ⟨h1, h2.imp_right fun h => lt_of_lt_of_le h htt'⟩

/-- Dynamic common knowledge (w.r.t. `𝛅(b)`) of `all_decide(b)` holds in every run `(b, d)`. -/
theorem example_CN (r : Bool × ℕ) : S.CN (δ dec r.1) (lift (allDecide S dec r.1)) r :=
  allDecide_CN example_spec.1 (example_spec.2.1 _) r fun i _ => ⟨_, decides i r⟩

/-- The hypotheses of Theorem 1.7 are satisfiable: `θ_v := "some process decides v"` with the
profiles `𝛅(v)`. -/
theorem example_sufficient :
    Decisions.Sufficient S valid (fun v r => ∃ i ∈ S.nf r, ∃ t, dec i v r t) (δ dec) :=
  (exists_theta_of_AoN example_spec.1 example_spec.2.1 example_spec.2.2.1
    example_spec.2.2.2.1 example_spec.2.2.2.2.2).1

/-- Classical common knowledge of the decision value is never attained: already
`E² (b = v) = E (E (b = v))` fails at every point, because process `0` cannot rule out that the
message has not been delivered yet. -/
theorem example_not_E2 (v : Bool) (r : Bool × ℕ) (t : ℕ) :
    ¬ (S.E)^[2] (lift fun r => r.1 = v) r t := by
  intro h
  -- `K_0 (K_1 (b = v))` at `(r, t)`; process `0` considers `((r.1, 0), 0)` possible.
  have h1 : S.K 1 (lift fun r => r.1 = v) (r.1, 0) 0 :=
    (h 0 : S.K 0 (S.E (lift fun r => r.1 = v)) r t) (r.1, 0) 0 (by simp [S]) 1
  -- At `((r.1, 0), 0)` process `1` has state `none`, as at `((!v, 0), 0)` where `b ≠ v`.
  have := h1 (!v, 0) 0 (by simp [S])
  simp at this

theorem example_not_C (v : Bool) (r : Bool × ℕ) (t : ℕ) : ¬ S.C (lift fun r => r.1 = v) r t :=
  fun h => example_not_E2 v r t (h 1)

end Podc.Knowledge.Example
