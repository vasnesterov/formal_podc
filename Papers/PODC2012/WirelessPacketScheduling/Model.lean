import Mathlib

/-!
# Static scheduling instances and Algorithm 1 (Section 3 of Kesselheim, PODC 2012)

A *static single-hop instance* (Section 2) consists of links `E`, packets `P` (each packet has to
cross one link `link p`) and the interference matrix `W : E → E → ℝ` with entries in `[0, 1]` and
`W e e = 1`. For a packet set `S`, `R_S(e')` is the number of packets of `S` on `e'`, and the
interference measure is `‖W · R_S‖∞ = max_e ∑_{e'} W e e' · R_S(e')`.

A static algorithm `𝒜(I', n')` is a black box: run (for its `f(n') · I'` time steps) on a packet
set `S`, it returns the random set of packets it did **not** deliver. The hypothesis of Theorem 1
is that `𝒜(I', n')` delivers everything with probability at least `1 - 1/n'` whenever
`‖W · R_S‖∞ ≤ I'` and `|S| ≤ n'`.

Algorithm 1 (verbatim):
```
for i := 1 to ξ = ⌈log(I / 2φχ log n)⌉ do
  Assign each remaining packet a delay of at most ⌈2^{-i+1} · I / χ⌉;
  Execute 𝒜(χ, m·χ) for f(mχ)·χ steps on all packets that received the same delay;
for i := 1 to ⌈φ⌉ + 1 do
  Execute 𝒜(2φχ log n, n) on the remaining packets;
```
with `χ = 6 (ln m + 9)`. The delays are independent and uniform in `[ψ]`, `ψ = ⌈2^{-i+1} I/χ⌉`
(proof of Claim 2). The base `b` of `log` is not fixed by the paper; we keep it as a parameter.

Here everything is a `PMF` over the final set of undelivered packets; "Algorithm 1 succeeds" means
this set is empty. The running time of Algorithm 1 is a deterministic quantity, treated in
`Time.lean`.
-/

namespace Podc.WirelessPacketScheduling

open Finset

/-- A static single-hop instance (Section 2): every packet `p` has to be sent over the link
`link p`; `W e e'` is the relative interference of a transmission on `e'` on the link `e`. -/
structure Instance (E P : Type*) where
  /-- The link of a packet. -/
  link : P → E
  /-- The interference matrix. -/
  W : E → E → ℝ
  W_nonneg : ∀ e e', 0 ≤ W e e'
  W_le_one : ∀ e e', W e e' ≤ 1
  W_self : ∀ e, W e e = 1

namespace Instance

variable {E P : Type*} (X : Instance E P)

/-- `(W · R_S)(e) = ∑_{p ∈ S} W e (link p)`. -/
noncomputable def load (S : Finset P) (e : E) : ℝ := ∑ p ∈ S, X.W e (X.link p)

/-- `‖W · R_S‖∞ ≤ c`. -/
def IntfLE (S : Finset P) (c : ℝ) : Prop := ∀ e, X.load S e ≤ c

/-- `‖W · R_S‖∞ = c`. -/
def IntfEq (S : Finset P) (c : ℝ) : Prop := X.IntfLE S c ∧ ∃ e, X.load S e = c

end Instance

/-- A randomized static scheduling algorithm `𝒜(I', n')`, run on the packet set `S` for its
`f(n') · I'` steps; the result is the random set of packets that were not delivered. -/
abbrev StaticAlg (P : Type*) := ℝ → ℝ → Finset P → PMF (Finset P)

/-- The hypothesis of Theorem 1: `𝒜(I', n')` only delivers packets it is run on, and it delivers
all of them with probability at least `1 - 1/n'` if `‖W · R_S‖∞ ≤ I'` and `|S| ≤ n'`. -/
structure StaticAlg.Good {E P : Type*} (X : Instance E P) (A : StaticAlg P) : Prop where
  subset : ∀ I' n' S, ∀ R ∈ (A I' n' S).support, R ⊆ S
  success : ∀ I' n' S, X.IntfLE S I' → (S.card : ℝ) ≤ n' → 1 - 1 / n' ≤ ((A I' n' S) ∅).toReal

/-- `χ = 6 (ln m + 9)`. -/
noncomputable def chi (m : ℕ) : ℝ := 6 * (Real.log m + 9)

/-- `ξ = ⌈log_b (I / (2 φ χ log_b n))⌉`, the number of iterations of the first loop. -/
noncomputable def xi (b : ℝ) (m n : ℕ) (I φ : ℝ) : ℤ :=
  ⌈Real.logb b (I / (2 * φ * chi m * Real.logb b n))⌉

/-- `ψ_i = ⌈2^{-i+1} · I / χ⌉`, the number of delay values in iteration `i`. -/
noncomputable def psi (m : ℕ) (I : ℝ) (i : ℕ) : ℕ := ⌈(2 : ℝ) ^ (-(i : ℤ) + 1) * I / chi m⌉₊

/-- The interference parameter `2 φ χ log_b n` of the clean-up executions. -/
noncomputable def finalParam (b : ℝ) (m n : ℕ) (φ : ℝ) : ℝ := 2 * φ * chi m * Real.logb b n

variable {P : Type*}

/-- Run `B` independently on each set of the list; the result is the union of the undelivered
packets. -/
noncomputable def runGroups (B : Finset P → PMF (Finset P)) [DecidableEq P] :
    List (Finset P) → PMF (Finset P)
  | [] => PMF.pure ∅
  | S :: Ss => (B S).bind fun r => (runGroups B Ss).bind fun rs => PMF.pure (r ∪ rs)

scoped instance instNeZeroMaxOne (ψ : ℕ) : NeZero (max ψ 1) := ⟨by omega⟩

/-- One iteration of the first loop of Algorithm 1: each remaining packet gets an independent
uniform delay in `[ψ]` (we use `max ψ 1` so that the type of delays is never empty; `ψ ≥ 1`
whenever the loop is executed), and `B` is run on each delay class. -/
noncomputable def iteration [Fintype P] [DecidableEq P] (B : Finset P → PMF (Finset P)) (ψ : ℕ)
    (R : Finset P) : PMF (Finset P) :=
  (PMF.uniformOfFintype (P → Fin (max ψ 1))).bind fun d =>
    runGroups B ((List.finRange (max ψ 1)).map fun j => R.filter (fun p => d p = j))

/-- Algorithm 1 with network size `m`, `n` packets, interference measure `I`, parameter `φ`,
and logarithms to the base `b`; the result is the random set of undelivered packets. -/
noncomputable def algorithm1 [Fintype P] [DecidableEq P] (A : StaticAlg P) (b : ℝ) (m n : ℕ)
    (I φ : ℝ) : PMF (Finset P) :=
  let loop1 := (List.range (xi b m n I φ).toNat).foldl
    (fun acc i => acc.bind (iteration (A (chi m) (m * chi m)) (psi m I (i + 1))))
    (PMF.pure Finset.univ)
  (List.range (⌈φ⌉₊ + 1)).foldl (fun acc _ => acc.bind (A (finalParam b m n φ) n)) loop1

/-- The probabilistic part of **Theorem 1** of [Kesselheim, PODC 2012], for logarithms to the
base `b`: for every instance (single-hop, `m = |E|`), every static algorithm satisfying the
hypothesis and every constant `φ > 0`, Algorithm 1 delivers all packets with probability at least
`1 - 1/n^φ`. (Delivering all packets is necessary for "Algorithm 1 uses at most … steps"; the step
bound itself is deterministic, see `Time.lean`.) -/
def Theorem1Claim (b : ℝ) : Prop :=
  ∀ (E P : Type) [Fintype E] [Fintype P] [DecidableEq P] (X : Instance E P) (A : StaticAlg P)
    (I φ : ℝ), A.Good X → X.IntfEq Finset.univ I → 0 < φ →
    1 - 1 / (Fintype.card P : ℝ) ^ φ ≤
      (algorithm1 A b (Fintype.card E) (Fintype.card P) I φ ∅).toReal

end Podc.WirelessPacketScheduling
