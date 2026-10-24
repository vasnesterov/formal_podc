import Mathlib

-- CSLib candidate: generic model (SRB systems / round-layer spec), see README.
/-!
# Unidirectional rounds: the specification (Definition 2)

Ben-David and Nayak (PODC 2021, BA; arXiv 2105.10566) call a system *unidirectional* if it can
implement rounds such that for any two correct processes `p ≠ q` that both send in round `r`,
`p` receives `q`'s round-`r` message before `p` starts round `r + 1`, or `q` receives `p`'s before
`q` starts round `r + 1`.

We state "a system implements unidirectional rounds" for an abstract transition system
(`RoundSystem`) whose round layer exposes, for every process `p`, the list `rounds c p` of its
*completed* rounds: entry `r` is the function `q ↦ (q's round-r message, if received by p before
p ended round r)`. The messages are chosen by an arbitrary *client* (`Client`): the message of
`p` for round `r` may depend on everything `p` received in rounds `0, …, r - 1`.

`RoundSystem.ImplementsUnidirectional` asks for
* `prefix_of_step`: completed rounds are never changed;
* `unidirectional`: Definition 2;
* `integrity`: a message received from a correct `q` in round `r` really is `q`'s round-`r`
  message (without it, "receiving" could be faked);
* `live`: in every fair execution every correct process completes every round.

Concrete systems: sequenced reliable broadcast (`SRB.lean`) and SWMR shared memory (`SWMR.lean`).
-/

namespace Podc.TrustedHW

/-- A client of the round layer: the message a process sends in round `r`, as a function of the
results of its rounds `0, …, r - 1` (a list of length `r`). -/
abbrev Client (P V : Type) := List (P → Option V) → V

/-- An abstract system implementing rounds: configurations, initial configurations, steps, a
fairness condition on executions, and the output of the round layer: `rounds c p` is the list of
rounds completed by `p`, entry `r` mapping each `q` to the round-`r` message of `q` received by
`p` before `p` ended round `r` (if any). -/
structure RoundSystem (P V : Type) where
  /-- Global configurations. -/
  Config : Type
  /-- Initial configurations. -/
  Init : Config → Prop
  /-- One atomic step. -/
  Step : Config → Config → Prop
  /-- Fairness of infinite executions. -/
  Fair : (ℕ → Config) → Prop
  /-- The completed rounds of each process. -/
  rounds : Config → P → List (P → Option V)

namespace RoundSystem

variable {P V : Type} (S : RoundSystem P V)

/-- Configurations reachable from an initial one. -/
def Reachable (c : S.Config) : Prop :=
  ∃ c₀, S.Init c₀ ∧ Relation.ReflTransGen S.Step c₀ c

/-- An infinite execution: it starts in an initial configuration and each transition is a step
or a stutter. -/
def IsExec (e : ℕ → S.Config) : Prop :=
  S.Init (e 0) ∧ ∀ t, S.Step (e t) (e (t + 1)) ∨ e (t + 1) = e t

/-- **Definition 2** (unidirectional communication), for the correct processes `correct` and the
clients `cl`. See the module docstring. -/
structure ImplementsUnidirectional (correct : P → Prop) (cl : P → Client P V) : Prop where
  /-- Completed rounds are never modified. -/
  prefix_of_step : ∀ c c', S.Reachable c → S.Step c c' → ∀ p, correct p →
    S.rounds c p <+: S.rounds c' p
  /-- Definition 2: for correct `p ≠ q` that both completed round `r`, `p` received `q`'s
  round-`r` message before ending round `r`, or `q` received `p`'s. -/
  unidirectional : ∀ c, S.Reachable c → ∀ p q, correct p → correct q → p ≠ q →
    ∀ r (hp : r < (S.rounds c p).length) (hq : r < (S.rounds c q).length),
      ((S.rounds c p)[r] q).isSome ∨ ((S.rounds c q)[r] p).isSome
  /-- A round-`r` message received from a correct `q` is the message `q`'s client chose for
  round `r` (in particular `q` had started round `r`). -/
  integrity : ∀ c, S.Reachable c → ∀ p q, correct p → correct q →
    ∀ r (hp : r < (S.rounds c p).length) w, (S.rounds c p)[r] q = some w →
      r ≤ (S.rounds c q).length ∧ w = cl q ((S.rounds c q).take r)
  /-- In every fair execution, every correct process completes every round. -/
  live : ∀ e, S.IsExec e → S.Fair e → ∀ p, correct p → ∀ r, ∃ t, r < (S.rounds (e t) p).length

lemma Reachable.step {S : RoundSystem P V} {c c' : S.Config} (hc : S.Reachable c)
    (h : S.Step c c') : S.Reachable c' := by
  obtain ⟨c₀, h₀, hr⟩ := hc
  exact ⟨c₀, h₀, hr.tail h⟩

lemma reachable_of_init {S : RoundSystem P V} {c : S.Config} (h : S.Init c) : S.Reachable c :=
  ⟨c, h, .refl⟩

/-- Every configuration of an execution is reachable. -/
lemma IsExec.reachable {S : RoundSystem P V} {e : ℕ → S.Config} (he : S.IsExec e) (t : ℕ) :
    S.Reachable (e t) := by
  induction t with
  | zero => exact reachable_of_init he.1
  | succ t ih =>
    rcases he.2 t with h | h
    · exact ih.step h
    · rw [h]; exact ih

/-- A property preserved by steps (from reachable configurations) and stutters is monotone along
an execution. -/
lemma IsExec.mono {S : RoundSystem P V} {e : ℕ → S.Config} (he : S.IsExec e)
    {R : S.Config → S.Config → Prop} (hrefl : ∀ c, R c c)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ c c', S.Reachable c → S.Step c c' → R c c') {t t' : ℕ} (h : t ≤ t') :
    R (e t) (e t') := by
  induction h with
  | refl => exact hrefl _
  | step _ ih =>
    rename_i m _
    refine htrans _ _ _ ih ?_
    rcases he.2 m with h | h
    · exact hstep _ _ (he.reachable m) h
    · rw [h]; exact hrefl _

end RoundSystem

/-- Every window of `N` consecutive times contains a time `≡ i (mod N)` (round-robin schedulers). -/
lemma exists_mod_eq (a : ℕ) {N i : ℕ} (hN : 0 < N) (hi : i < N) :
    ∃ τ, a ≤ τ ∧ τ < a + N ∧ τ % N = i := by
  have h1 := Nat.div_add_mod a N
  have h2 := Nat.mod_lt a hN
  by_cases hc : a % N ≤ i
  · refine ⟨i + N * (a / N), by omega, by omega, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  · refine ⟨i + N * (a / N + 1), by rw [Nat.mul_add]; omega, by rw [Nat.mul_add]; omega, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

end Podc.TrustedHW
