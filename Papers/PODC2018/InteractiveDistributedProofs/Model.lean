import Papers.PODC2018.InteractiveDistributedProofs.Basic
import Cslib.Probability.Finite.Uniform

/-!
# Interactive distributed proofs: the dMAM and dAM models (Section 2.2)

A fixed finite set `V` of nodes (identifiers known to everybody, as in the paper) runs on a network
graph `G : SimpleGraph V`. A single prover sees all of `G`.

* **dAM** (Definition 1): every node `v` draws a uniformly random challenge `c v ∈ R` and sends it to
  the prover; the prover answers every node with a response `M v ∈ M` that may depend on `G` and on all
  challenges; then every node decides.
* **dMAM** (Section 2.2): the prover first sends every node a message `M₁ v`, then the nodes send
  challenges, then the prover answers with `M₂ v` (depending on all challenges).

**Locality.** A node's decision function only receives its *local view*: `mask G v x` keeps the
values `x u` for `u ∈ N(v)` (closed neighbourhood) and replaces all others by `none`. A node thus
knows its own identifier, its neighbours' identifiers (the `some` entries) and their messages and
challenges, as in Definition 1 (the lower-bound section gives nodes `r_{N(v)}`; the upper-bound
protocols only use their own challenge). Locality is therefore built into the type of a protocol.

**Provers** are deterministic functions of the challenges (they also depend on `G`, since the
statement `∃ P` is made for each graph). A randomized prover is a mixture of deterministic ones, so
its acceptance probability is an average of deterministic acceptance probabilities; restricting
to deterministic provers changes neither `∃ P, Pr > 2/3` nor `∀ P, Pr < 1/3`.

**Correctness** (Definition 2): `Decides Π 𝒢 L` — on every graph of the class `𝒢`, a YES-instance has a
prover making all nodes accept with probability `> 2/3`, and on a NO-instance every prover makes all
nodes accept with probability `< 1/3`. Probability is uniform over the challenge vector
`c : V → R` (`Cslib.Probability.uprob`).

**Cost.** `InDMAM L ℓ` / `InDAM L ℓ`: for every vertex set of size `n`, there is a protocol deciding `L`
on connected graphs whose message and challenge alphabets have at most `2^{ℓ(n)}` elements (i.e. every
node exchanges `O(ℓ(n))` bits with the prover).
-/

open Finset Cslib.Probability

namespace Podc.InteractiveDistributedProofs

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
-- CSLib candidate
/-- The local view of node `v` of a global assignment `x`: values on `N(v)`, `none` elsewhere. -/
noncomputable def mask (G : SimpleGraph V) (v : V) {α : Type*} (x : V → α) : V → Option α :=
  fun u => if u ∈ cnbhd G v then some (x u) else none

theorem mask_apply_of_mem {G : SimpleGraph V} {v u : V} {α : Type*} (x : V → α)
    (hu : u ∈ cnbhd G v) : mask G v x u = some (x u) := by
  simp [mask, hu]

theorem mask_apply_of_notMem {G : SimpleGraph V} {v u : V} {α : Type*} (x : V → α)
    (hu : u ∉ cnbhd G v) : mask G v x u = none := by
  simp [mask, hu]

open Classical in
/-- The neighbourhood a node reads off its view: the positions holding a value. -/
noncomputable def viewNbhd {α : Type*} (w : V → Option α) : Finset V :=
  univ.filter fun u => (w u).isSome

theorem viewNbhd_mask (G : SimpleGraph V) (v : V) {α : Type*} (x : V → α) :
    viewNbhd (mask G v x) = cnbhd G v := by
  ext u
  by_cases hu : u ∈ cnbhd G v <;> simp [viewNbhd, mask, hu]

/-! ### dMAM -/

/-- A dMAM protocol: one decision function per node, applied to the local view of
(first prover message, challenge, second prover message). -/
structure MAMProtocol (V M₁ R M₂ : Type*) where
  /-- decision of node `v` on its local view -/
  out : V → (V → Option (M₁ × R × M₂)) → Prop

/-- A (deterministic) dMAM prover: the first messages, and the second messages as a function of all
challenges. -/
structure MAMProver (V M₁ R M₂ : Type*) where
  /-- first round `P → v` -/
  first : V → M₁
  /-- third round `P → v`, after seeing all challenges -/
  second : (V → R) → V → M₂

variable {M₁ R M₂ M : Type*}

/-- All nodes accept for challenge vector `c`. -/
def MAMProtocol.Accepts (pr : MAMProtocol V M₁ R M₂) (G : SimpleGraph V) (P : MAMProver V M₁ R M₂)
    (c : V → R) : Prop :=
  ∀ v, pr.out v (mask G v fun u => (P.first u, c u, P.second c u))

/-- Acceptance probability over uniform challenges. -/
noncomputable def MAMProtocol.accProb [Fintype R] (pr : MAMProtocol V M₁ R M₂) (G : SimpleGraph V)
    (P : MAMProver V M₁ R M₂) : ℝ :=
  uprob (pr.Accepts G P)

/-- Definition 2 (for dMAM): `Π` decides `L` on the graphs of `𝒢`. -/
def MAMProtocol.Decides [Fintype R] (pr : MAMProtocol V M₁ R M₂) (𝒢 L : SimpleGraph V → Prop) :
    Prop :=
  ∀ G, 𝒢 G → (L G → ∃ P, 2 / 3 < pr.accProb G P) ∧ (¬ L G → ∀ P, pr.accProb G P < 1 / 3)

/-! ### dAM -/

/-- A dAM protocol (Definition 1): decision of node `v` on the local view of (challenge, response). -/
structure AMProtocol (V R M : Type*) where
  /-- decision of node `v` on its local view -/
  out : V → (V → Option (R × M)) → Prop

/-- All nodes accept for challenge vector `c` and prover `P` (the response vector as a function of all
challenges). -/
def AMProtocol.Accepts (pr : AMProtocol V R M) (G : SimpleGraph V) (P : (V → R) → V → M)
    (c : V → R) : Prop :=
  ∀ v, pr.out v (mask G v fun u => (c u, P c u))

/-- Acceptance probability over uniform challenges. -/
noncomputable def AMProtocol.accProb [Fintype R] (pr : AMProtocol V R M) (G : SimpleGraph V)
    (P : (V → R) → V → M) : ℝ :=
  uprob (pr.Accepts G P)

/-- Definition 2: `Π` decides `L` on the graphs of `𝒢`. -/
def AMProtocol.Decides [Fintype R] (pr : AMProtocol V R M) (𝒢 L : SimpleGraph V → Prop) : Prop :=
  ∀ G, 𝒢 G → (L G → ∃ P, 2 / 3 < pr.accProb G P) ∧ (¬ L G → ∀ P, pr.accProb G P < 1 / 3)

/-! ### Complexity classes -/

/-- `L ∈ dMAM[ℓ]` (on connected networks): for every node set of size `n` there is a dMAM protocol
deciding `L` whose message and challenge alphabets have at most `2^{ℓ n}` elements. -/
def InDMAM (L : ∀ (V : Type) [Fintype V] [DecidableEq V], SimpleGraph V → Prop) (ℓ : ℕ → ℕ) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V],
    ∃ (M₁ R M₂ : Type) (_ : Fintype M₁) (_ : Fintype R) (_ : Fintype M₂)
      (pr : MAMProtocol V M₁ R M₂),
      Fintype.card M₁ ≤ 2 ^ ℓ (Fintype.card V) ∧ Fintype.card R ≤ 2 ^ ℓ (Fintype.card V) ∧
      Fintype.card M₂ ≤ 2 ^ ℓ (Fintype.card V) ∧
      pr.Decides (fun G => G.Connected) (L V)

/-- `L ∈ dAM[ℓ]` (on connected networks). -/
def InDAM (L : ∀ (V : Type) [Fintype V] [DecidableEq V], SimpleGraph V → Prop) (ℓ : ℕ → ℕ) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V],
    ∃ (R M : Type) (_ : Fintype R) (_ : Fintype M) (pr : AMProtocol V R M),
      Fintype.card R ≤ 2 ^ ℓ (Fintype.card V) ∧ Fintype.card M ≤ 2 ^ ℓ (Fintype.card V) ∧
      pr.Decides (fun G => G.Connected) (L V)

/-! ### Helper facts -/

omit [Fintype V] [DecidableEq V] in
/-- On a connected graph, a function that agrees on every edge is constant. -/
theorem eq_of_connected {G : SimpleGraph V} (hG : G.Connected) {α : Type*} (f : V → α)
    (hf : ∀ u v, G.Adj u v → f u = f v) (u v : V) : f u = f v := by
  obtain ⟨w⟩ := hG.preconnected u v
  induction w with
  | nil => rfl
  | cons h _ ih => exact (hf _ _ h).trans ih

/-- An event that only depends on one coordinate of a uniform vector has the probability of that
coordinate's event. -/
theorem uprob_coord {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (i₀ : ι) (E : β → Prop) : uprob (fun c : ι → β => E (c i₀)) = uprob E := by
  classical
  have h := uprob_pi (α := fun _ : ι => β) (fun i b => if i = i₀ then E b else True)
  have h1 : (fun x : ι → β => ∀ i, (fun i b => if i = i₀ then E b else True) i (x i)) =
      fun c => E (c i₀) := by
    funext x
    apply propext
    constructor
    · intro hx; simpa using hx i₀
    · intro hx i; by_cases hi : i = i₀ <;> simp [hi, hx]
  rw [h1] at h
  rw [h, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀)]
  rw [Finset.prod_eq_one]
  · simp
  · intro i hi
    have : i ≠ i₀ := Finset.ne_of_mem_erase hi
    simp only [this, ite_false]
    rw [uprob_true]
    simp [Fintype.card_ne_zero]

end Podc.InteractiveDistributedProofs
