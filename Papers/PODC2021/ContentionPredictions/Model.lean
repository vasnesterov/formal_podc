import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- CSLib candidate: radio-channel model (see wiki/library-map.md)

/-!
# Deterministic contention resolution with perfect advice (Section 3.1 of the paper)

Gilbert, Newport, Vaidya, Weaver. *Contention Resolution with Predictions.* PODC 2021.

**Model.** `n` potential players `Fin n` share a single-hop synchronous channel. An adversary picks
a nonempty set `P` of participants; every participant receives the same advice `f P` from an
advice function `f` with perfect knowledge of `P`. In each round each participant transmits or
listens; the problem is solved in the first round in which exactly one participant transmits.
If two or more transmit, all messages are lost: with collision detection (`cd = true`) every
player, including the transmitters, detects the collision; without collision detection every
unsuccessful round sounds like silence to everybody.

Hence, before the problem is solved, all participants have observed the same channel feedback, a
list of bits (one per completed round, `true` = collision), and a deterministic algorithm is a
function `advice → feedback history → id → transmit?` (`DetAlg`). Without collision detection the
history before success is always a list of `false`s.

`SolvesIn cd alg f t`: for every nonempty `P`, the execution with advice `f P` is solved in one of
the rounds `0, …, t - 1` (i.e. within `t` rounds). *Non-interactive* contention resolution is
`SolvesIn _ alg f 1`.
-/

namespace Podc.ContentionPredictions

open Finset

/-- A deterministic contention-resolution algorithm for the `n` potential players `Fin n` with
advice from the alphabet `A`: `alg a h v` says whether player `v`, having received advice `a` and
observed the channel feedback `h` (one bit per completed round, `true` = collision detected),
transmits in the current round. -/
abbrev DetAlg (n : ℕ) (A : Type*) := A → List Bool → Fin n → Bool

variable {n : ℕ} {A : Type*}

/-- The participants of `P` that transmit with advice `a` after feedback history `h`. -/
def transmitters (alg : DetAlg n A) (a : A) (h : List Bool) (P : Finset (Fin n)) :
    Finset (Fin n) :=
  P.filter fun v => alg a h v

/-- Feedback bit observed by everybody after an unsuccessful round with transmitters `T`: a
detected collision (`true`) iff collision detection is available and `|T| ≥ 2`. -/
def feedback (cd : Bool) (T : Finset (Fin n)) : Bool :=
  cd && decide (2 ≤ T.card)

/-- The common feedback history before round `r` of the execution with participants `P` and
advice `a`. -/
def history (cd : Bool) (alg : DetAlg n A) (a : A) (P : Finset (Fin n)) : ℕ → List Bool
  | 0 => []
  | r + 1 => history cd alg a P r ++ [feedback cd (transmitters alg a (history cd alg a P r) P)]

/-- Round `r` (counted from `0`) of the execution with participants `P` and advice `a` has exactly
one transmitter. -/
def SolvedAt (cd : Bool) (alg : DetAlg n A) (a : A) (P : Finset (Fin n)) (r : ℕ) : Prop :=
  (transmitters alg a (history cd alg a P r) P).card = 1

/-- `alg` with advice function `f` solves contention resolution within `t` rounds. -/
def SolvesIn (cd : Bool) (alg : DetAlg n A) (f : Finset (Fin n) → A) (t : ℕ) : Prop :=
  ∀ P : Finset (Fin n), P.Nonempty → ∃ r < t, SolvedAt cd alg (f P) P r

/-- Non-interactive contention resolution: exactly one participant transmits in the first round
(Section 3.2). -/
def NonInteractive (alg : DetAlg n A) (f : Finset (Fin n) → A) : Prop :=
  SolvesIn false alg f 1

/-- `b`-bit advice strings. -/
abbrev Bits (b : ℕ) := Fin b → Bool

theorem card_bits (b : ℕ) : Fintype.card (Bits b) = 2 ^ b := by simp

@[simp] theorem history_length (cd : Bool) (alg : DetAlg n A) (a : A) (P : Finset (Fin n))
    (r : ℕ) : (history cd alg a P r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [history, ih]

@[simp] theorem history_false (alg : DetAlg n A) (a : A) (P : Finset (Fin n)) (r : ℕ) :
    history false alg a P r = List.replicate r false := by
  induction r with
  | zero => rfl
  | succ r ih => simp [history, ih, feedback, List.replicate_succ']

theorem nonInteractive_iff (alg : DetAlg n A) (f : Finset (Fin n) → A) :
    NonInteractive alg f ↔ ∀ P : Finset (Fin n), P.Nonempty →
      (P.filter fun v => alg (f P) [] v).card = 1 := by
  simp [NonInteractive, SolvesIn, SolvedAt, transmitters]

theorem solvesIn_mono {cd : Bool} {alg : DetAlg n A} {f : Finset (Fin n) → A} {t t' : ℕ}
    (h : SolvesIn cd alg f t) (ht : t ≤ t') : SolvesIn cd alg f t' := fun P hP => by
  obtain ⟨r, hr, h⟩ := h P hP
  exact ⟨r, lt_of_lt_of_le hr ht, h⟩

/-- The number of feedback histories of length `< t` is `2 ^ t - 1`. -/
theorem card_sigma_vector (t : ℕ) :
    Fintype.card (Σ r : Fin t, List.Vector Bool r) = 2 ^ t - 1 := by
  rw [Fintype.card_sigma]
  simp only [card_vector, Fintype.card_bool]
  rw [Fin.sum_univ_eq_sum_range (fun r => 2 ^ r), Nat.geomSum_eq le_rfl]
  simp

end Podc.ContentionPredictions
