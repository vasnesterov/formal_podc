# Interplanetary and Relativistic Distributed Computing — PODC 2025

Siddhartha Jayanti. *On Interplanetary and Relativistic Distributed Computing.* PODC 2025. DOI
[10.1145/3732772.3733563](https://doi.org/10.1145/3732772.3733563). Formalized version: the proceedings
version (no arXiv version exists); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The Central Theorem (Theorem 6.7) and the Equivalence Theorem
(Theorem 6.8) hold when there are countably many processors. Theorem 6.8 holds with no assumption at
all, once its three notions of linearizability are all read over finite executions (Def. A.3 already
does this; see the under-specified definitions below). With uncountably many processors, Lemma 6.3
(backward direction), Lemma 6.4 (second half), Corollary 6.5 and the implication (1) ⟹ (2) of
Theorem 6.7 are false. The paper never restricts the set of processors, but this case is degenerate.
The proof of Lemma 6.3 also has a gap for countably infinite executions, though the statement is true
there.

## Mistakes in the paper

* **Lemma 6.3 (⇐), Lemma 6.4 (second half), Corollary 6.5 and Theorem 6.7 (1) ⟹ (2) are false
  for uncountably many processors.** *False only in a degenerate case.* Index the processors by the
  "double arrow" `ℝ ×ₗ Bool` (lexicographic order). Each processor takes one step from its initial
  state, and no messages are sent. The empty relation is then a computational execution, and the
  lexicographic order of the processors is a total ordering of it. That order satisfies P1–P3. But it
  does not embed into `(ℝ, <)`: there would be a rational between the images of `(x, false)` and
  `(x, true)` for every real `x`, all distinct. So it is not a classical execution. Placing the steps
  at distinct points of the `t = 0` slice of Minkowski spacetime makes the same order a total ordering
  of a relativistic execution, which refutes Corollary 6.5. For the property "the order embeds into
  ℝ", statement (1) of Theorem 6.7 holds trivially and (2) fails. Statement (3) also fails if observers
  may perceive simultaneous steps in any order. Statement (3) holds if only frames without
  simultaneous steps count. (`lemma_6_3_false`, `lemma_6_4_false`, `corollary_6_5_false`,
  `theorem_6_7_false`, `theorem_6_7_false_frames`)
  We proved instead that all four statements hold for executions with countably many steps. This
  covers every execution when `Π` is countable (`lemma_6_3_of_countable`, `lemma_6_4`, `theorem_6_7`),
  and any countable class of executions, e.g. finite ones (`theorem_6_7_on`). We also proved that
  "classical ⟺ every observer in every relativistic execution, frames without ties" holds for any
  `Π` (`classical_iff_frames`).
* **Proof of Lemma 6.3 (⇐): the map `t(sᵢ) = i` assumes order type `≤ ω`.** *Proof gap; the
  statement is true for countably many processors.* Lemma 6.4 inherits this gap via Lemma 6.3.
  Lemma 6.3 lists the steps as
  `s₁, s₂, …` in `<_S` order, but a total ordering of an infinite execution need not have order type
  `ω`, even with two processors. Example: processor 0 takes infinitely many steps and processor 1
  takes one step after all of them. This is a classical execution of order type `ω + 1`, with times
  `1 − 1/(n+1)` and `1`, and no indexing by `ℕ` exists (`omegaPlusOne_classical`,
  `omegaPlusOne_not_seq`). The repair: every countable linear order embeds into `ℚ ⊂ ℝ` (Cantor), so
  a time map exists anyway (`exists_real_embedding`).
* **Under-specified definitions.** *None of these affects the results once fixed.*
  * Def. 5.3 and the Central Theorem talk about "the total ordering of the execution according to the
    local time of frame R". This order is not total when two steps are simultaneous in R. The paper's
    own §7 scenario has `e₁ =_A e₂`. We formalize both readings: all tie-breakings
    (`RelativisticallySatisfies`) and only frames without ties (`RelativisticallySatisfies'`).
  * Theorem 6.8 combines definitions with different scopes. "Linearizable" (Def. A.3) quantifies over
    *finite* classical executions. "Relativistically/computationally linearizable" (Defs. 5.3, 6.1)
    quantify over *all* executions, and the proof instantiates Theorem 6.7 with no finiteness. Taken
    literally, (1) ⟹ (3) would need linearizability of infinite histories to follow from that of
    finite ones. This is delicate (cf. Guerraoui–Ruppert, "linearizability is not always a safety
    property"), and Def. A.3 does not pin down the infinite case. We read all three notions over
    finite executions.
  * "A predicate on classical executions" (Theorem 6.7) must really be a predicate on arbitrary
    totally ordered step sets, since (2) and (3) apply it to orders that are not a priori classical.
  * Φ2 ("a step can occur at π only if its current state is σ") presupposes that each processor's
    steps form a sequence. A real-valued time map alone allows Zeno behaviour, e.g. steps at
    `1 − 1/n` followed by one at time 2. We make "the steps of each processor, in time order, form a
    rooted consecutively permissible sequence (order type ≤ ω)" part of Φ2. The paper's proofs of
    Lemmas 6.2 and 6.3 ("by CP1 / RP2 these steps can be ordered into a sequence") rely on exactly
    this.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Algorithms are state machines per processor (Def. 4.1). A step is `(π, σ, e, σ')` with `δ_π(σ, e, σ')`
  (Def. 4.2). Events may be sends `(π, send, m, π')` or receives `(π', receive, m)`. The model is
  asynchronous, with arbitrary (possibly infinite) step sets and arbitrary processor sets.
* An execution is a set `S` of steps with a relation on the subtype `↥S`. The conditions that do not
  depend on the order are message validity and at-most-once delivery (`MsgValid`). The conditions
  that depend on the order are: per-processor steps form a rooted, consecutively permissible
  sequence (`ProcSeq`: a strict total order with finitely many predecessors), and messages are
  oriented forward (`MsgForward`).
* Classical execution: the order is induced by an injective time map `S → ℝ` (CP1, CP2). Computational
  execution: `◁ = TransGen(program order ∪ message edges)` as a fixed-point equation (A1–A3).
  Relativistic execution: the order is induced by an injective map into an abstract `Spacetime`. That
  structure has a strict causal order (RP1), real time coordinates for each frame that refine it
  (RP1), world lines that are chains (RP2), and one body at rest whose world line is parametrised by
  frame time (the physical fact used in Lemma 6.6). Messages go forward in `≺` (RP3).
* Instance: Minkowski spacetime `ℝ × ℝᵈ` with `c = 1`. Causal order: `‖Δx‖ ≤ Δt`. Inertial frames have
  velocity `‖v‖ < 1`, and frame time is `t − ⟪v, x⟫` (the Lorentz time up to the factor `γ_v`).
* Linearizability is CSLib's `Cslib.SharedMemory.HerlihyWing.Linearizable` (single object), applied to
  the history of a finite execution.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 6.2 | `lemma_6_2`, `lemma_6_2'` | `Central.lean` |
| Lemma 6.3 (corrected / countable `Π`) | `lemma_6_3`, `lemma_6_3_of_countable` | `Central.lean` |
| Lemma 6.4 | `lemma_6_4_forward`, `lemma_6_4_backward` (countable `S`), `lemma_6_4` (countable `Π`) | `Central.lean` |
| Corollary 6.5 (countable `S`) | `corollary_6_5` | `Central.lean` |
| Lemma 6.6 | `lemma_6_6`, `lemma_6_6_strong` | `Central.lean` |
| Theorem 6.7 (countable `Π`) | `theorem_6_7`; class version `theorem_6_7_on`; tie-free frames, any `Π`: `classical_iff_frames` | `Central.lean` |
| Theorem 6.8 | `theorem_6_8` | `Linearizability.lean` |
| Counterexamples (uncountable `Π`) | `lemma_6_3_false`, `lemma_6_4_false`, `corollary_6_5_false`, `theorem_6_7_false`, `theorem_6_7_false_frames` | `Counterexample.lean` |
| Proof gap (order type `ω + 1`) | `omegaPlusOne_classical`, `omegaPlusOne_not_seq` | `Examples.lean` |
| Relativity of simultaneity (§3.2) | `relativity_of_simultaneity` | `Spacetime.lean` |
| Observation 1, geometry (§7) | `observation1_geometry` | `Spacetime.lean` |

**Not formalized.** The JTUF union-find algorithm of §7: we prove only the spacetime geometry behind
Observation 1, namely that two observers see two ε-small operations in opposite orders. The
physics postulates themselves are axiomatized, not derived from Lorentz transformations, beyond the
Minkowski instance.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity checks:
* a ping execution (one message) that is classical, computational and relativistic in Minkowski
  spacetime (`ping_classical`, `ping_computational`, `ping_relativistic`);
* a relativistic execution with two causally unrelated steps that two observers order oppositely
  (`spacelike_relativistic`);
* Minkowski spacetime satisfies the `Spacetime` postulates (`minkowski`);
* every finite total order has a history (`exists_isHistoryOf`).
