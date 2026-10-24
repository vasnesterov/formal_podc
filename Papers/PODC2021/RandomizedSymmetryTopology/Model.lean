import Mathlib

/-!
# Synchronous anonymous systems with correlated randomness sources

Fraigniaud, Gelles, Lotker, *The Topology of Randomized Symmetry-Breaking Distributed Computing*,
PODC 2021 (full version arXiv:2105.11713), Section 2 and Section 3.1–3.2.

* `n` anonymous fault-free parties `Fin n`, `k` independent randomness sources `Fin k`;
  a *randomness configuration* `α : Fin n → Fin k` says which source each party reads
  (the paper's facet `α = {(1, j₁), …, (n, jₙ)}` of the assignment complex `A`, Eq. (4)).
  `load α j` is the paper's `nⱼ`, the number of parties connected to source `j`.
* A *source stream* `ω : ℕ → Fin k → Bool`: `ω s j` is the bit produced by source `j` in round
  `s + 1` (rounds are numbered from `1` in the paper, from `0` here). Party `i` receives
  `ω s (α i)`.
* Full-information protocols: the knowledge `K ω t i` of party `i` at time `t` (the paper's
  `Kᵢ(t)`, Eqs. (1), (2)) is given by a `FullInfoModel`; the two concrete models are in
  `Blackboard.lean` and `MessagePassing.lean`.
* A symmetry-breaking task is a set `O` of output vectors (the facets of the output complex);
  `Solves O κ` (Definition 3.1) says that a global state `κ : Fin n → Kn` (a facet of `P(t)`)
  admits a name-independent decision map `f : Kn → Out` with `f ∘ κ ∈ O`.
* `probSolves M O t` is `Pr[P(t) solves O | α]` (Eq. (7)): the fraction of the `2^{kt}`
  equiprobable source realizations of length `t` whose global state solves `O`.
* `EventuallySolvable` is Definition 3.3: this probability tends to `1`.
-/

open Finset Filter Topology

namespace Podc.RandomizedSymmetryTopology

/-! ### Randomness configurations and source streams -/

/-- The number `nⱼ` of parties connected to source `j` under the configuration `α`. -/
def load {n k : ℕ} (α : Fin n → Fin k) (j : Fin k) : ℕ :=
  (univ.filter fun i => α i = j).card

/-- A realization of all `k` sources over infinitely many rounds: `ω s j` is the bit of source `j`
in round `s + 1`. -/
abbrev Stream (k : ℕ) : Type := ℕ → Fin k → Bool

/-- A realization of the `k` sources during the first `t` rounds (the paper's `R₁(1..t), …`). -/
abbrev Window (k t : ℕ) : Type := Fin t → Fin k → Bool

/-- Extend a finite realization by `false` bits (the extension is irrelevant at time `t`, see
`FullInfoModel.isLocal`). -/
def ext {k t : ℕ} (r : Window k t) : Stream k := fun s => if h : s < t then r ⟨s, h⟩ else fun _ => false

theorem ext_of_lt {k t : ℕ} (r : Window k t) {s : ℕ} (h : s < t) : ext r s = r ⟨s, h⟩ := by
  simp [ext, h]

/-- The stream seen from round `s` on. -/
def shiftStream {k : ℕ} (ω : Stream k) (s : ℕ) : Stream k := fun v => ω (s + v)

/-! ### Full-information models -/

/-- A synchronous full-information model with `n` parties fed by `k` randomness sources:
the knowledge `K ω t i : Know t` of party `i` at time `t` under source stream `ω`, with the three
structural properties the paper uses:
* `isLocal`: knowledge at time `t` only depends on the first `t` rounds of randomness;
* `prev`: knowledge is cumulative (`Kᵢ(t)` contains `Kᵢ(t-1)`);
* `shift`: running the same bits from a later starting point yields a refinement — the knowledge
  at time `s + u` determines the knowledge at time `u` of the run that starts with the bits of
  rounds `s+1, …, s+u` (this is what the proof of Lemma 3.2 uses when it says that the event
  `E_s` makes the system reach a solving state). -/
structure FullInfoModel (n k : ℕ) where
  /-- Knowledge values at time `t`. -/
  Know : ℕ → Type
  /-- Knowledge of party `i` at time `t`. -/
  K : Stream k → (t : ℕ) → Fin n → Know t
  /-- Knowledge at time `t` depends only on the first `t` rounds. -/
  isLocal : ∀ ω ω' t, (∀ s < t, ω s = ω' s) → K ω t = K ω' t
  /-- Knowledge is cumulative. -/
  prev : ∀ t, ∃ g : Know (t + 1) → Know t, ∀ ω i, K ω t i = g (K ω (t + 1) i)
  /-- Shifted runs are coarser. -/
  shift : ∀ ω s u, ∃ g : Know (s + u) → Know u, ∀ i, K (shiftStream ω s) u i = g (K ω (s + u) i)

/-! ### Tasks and solvability -/

/-- An input-free task on `n` parties: the set of legal output vectors (facets of `O`). -/
abbrev Task (n : ℕ) (Out : Type) : Type := Set (Fin n → Out)

/-- The output complex is stable under permutations of the names (Section 3.1). -/
def Task.Symmetric {n : ℕ} {Out : Type} (O : Task n Out) : Prop :=
  ∀ o ∈ O, ∀ σ : Equiv.Perm (Fin n), o ∘ σ ∈ O

/-- Leader election `O_LE` (Eq. (3)): exactly one party outputs `1` (`true`). -/
def leaderElection (n : ℕ) : Task n Bool := {o | ∃! i, o i = true}

theorem leaderElection_symmetric (n : ℕ) : (leaderElection n).Symmetric := by
  rintro o ⟨i, hi, hu⟩ σ
  refine ⟨σ.symm i, by simpa using hi, fun j hj => ?_⟩
  have := hu (σ j) hj
  simp [← this]

/-- **Definition 3.1.** A global state `κ` (the facet `{(i, κ i)}` of `P(t)`) solves `O` if there
is a name-preserving, name-independent map to a facet of `O`, i.e. a decision function `f` on
knowledge values with `f ∘ κ ∈ O`. -/
def Solves {n : ℕ} {Kn Out : Type} (O : Task n Out) (κ : Fin n → Kn) : Prop :=
  ∃ f : Kn → Out, f ∘ κ ∈ O

/-- Leader election is solved by a global state iff some party has a knowledge value that no
other party has. -/
theorem solves_leaderElection_iff {n : ℕ} {Kn : Type} (κ : Fin n → Kn) :
    Solves (leaderElection n) κ ↔ ∃ i, ∀ j, j ≠ i → κ j ≠ κ i := by
  classical
  constructor
  · rintro ⟨f, i, hi, hu⟩
    refine ⟨i, fun j hj hji => hj (hu j ?_)⟩
    simpa [Function.comp, hji] using hi
  · rintro ⟨i, hi⟩
    refine ⟨fun x => decide (x = κ i), i, by simp, fun j hj => ?_⟩
    by_contra h
    exact hi j h (by simpa using hj)

/-- If the partition of the parties by `κ'` is coarser than the one by `κ` (i.e. `κ' = g ∘ κ`),
then every task solved by `κ'` is solved by `κ`. -/
theorem Solves.of_comp {n : ℕ} {Kn Kn' Out : Type} {O : Task n Out} {κ : Fin n → Kn}
    {κ' : Fin n → Kn'} (g : Kn → Kn') (hg : ∀ i, κ' i = g (κ i)) (h : Solves O κ') :
    Solves O κ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f ∘ g, ?_⟩
  have : (f ∘ g) ∘ κ = f ∘ κ' := by funext i; simp [hg]
  rwa [this]

/-! ### Probabilities -/

open Classical in
/-- `Pr[P(t) solves O | α]` (Eq. (7), equivalently Eq. (20) via `probSolves_eq_realization`):
all `2^{kt}` source realizations of length `t` are equiprobable (Lemma B.1 of the full version),
so the probability is the fraction of those whose global state at time `t` solves `O`. -/
noncomputable def probSolves {n k : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out)
    (t : ℕ) : ℝ :=
  ((univ.filter fun r : Window k t => Solves O (M.K (ext r) t)).card : ℝ) / 2 ^ (k * t)

/-- **Definition 3.3.** A task is eventually solvable (for the configuration encoded in `M`) if
the probability that the global state at time `t` solves it tends to `1`. -/
def EventuallySolvable {n k : ℕ} (M : FullInfoModel n k) {Out : Type} (O : Task n Out) : Prop :=
  Tendsto (probSolves M O) atTop (𝓝 1)

end Podc.RandomizedSymmetryTopology
