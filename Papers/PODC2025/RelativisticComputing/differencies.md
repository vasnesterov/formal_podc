# Differences between the formalization and the paper

Paper: S. Jayanti, *On Interplanetary and Relativistic Distributed Computing*, PODC 2025
(DOI 10.1145/3732772.3733563), proceedings version.

## Errors in the paper

1. **Uncountably many processors: Lemma 6.3 (⇐), Lemma 6.4 (second half), Corollary 6.5 and
   Theorem 6.7 (1) ⟹ (2) are false.** *False only in a degenerate case.* The paper places no
   restriction on `Π`. Take `Π = ℝ ×ₗ Bool` and the trivial algorithm: one state, one event, no
   messages, each processor takes its single step. Let `S` be all these steps and `R = ∅`. Then `R` is
   a computational execution (`isComputational_S₀`). The lexicographic order `lt₀` of the processors is
   a total ordering of `R` and satisfies P1–P3. It is not a classical execution, because it does not
   embed into `(ℝ, <)` (`lt₀_not_real`: rationals between the images of `(x, false)` and `(x, true)`
   would give an injection `ℝ → ℚ`).
   * Lemma 6.4: `lemma_6_4_false`. Lemma 6.3: `lemma_6_3_false`.
   * Corollary 6.5: place step `(x, b)` at the event `(0, ±eˣ)` of 1+1 Minkowski spacetime. This gives
     a relativistic execution with `≺_S = ∅` of which `lt₀` is a total ordering (`corollary_6_5_false`).
   * Theorem 6.7: for `P :=` "the order embeds into ℝ", (1) holds and (2) fails
     (`theorem_6_7_false`). (3) in the tie-breaking reading also fails, because the observer at rest
     sees all steps of the execution above as simultaneous (`theorem_6_7_false_frames`). (3) in the
     tie-free reading holds, since it is equivalent to (1) for every `Π` (`classical_iff_frames`).
   * Fix: assume the executions are countable. This holds automatically for countable `Π`, because
     every per-processor sequence is countable (`ProcSeq.countable`). It also holds for every finite
     execution, which is all Theorem 6.8 needs (`theorem_6_7_on`).

2. **Proof of Lemma 6.3 (⇐), used by Lemma 6.4 and Theorem 6.7: `t(sᵢ) = i` assumes order type
   `≤ ω`.** *Proof gap; the statement is true for countable executions.* Counterexample to the step:
   two processors, a counter algorithm; processor `false` takes steps at times `1 − 1/(n+1)` for all
   `n`, processor `true` takes one step at time 1. This is classical (`omegaPlusOne_classical`), and its
   order has no embedding into `ℕ` (`omegaPlusOne_not_seq`). Repair: Cantor's theorem, every countable
   linear order embeds into `ℝ` (`exists_real_embedding`, via Mathlib's
   `Order.embedding_from_countable_to_dense`). The gap does not make Lemma 6.4 false for countable
   executions, infinite ones included. The lemma is false only for uncountable ones (item 1).

## Under-specified definitions (resolved)

3. **Reference-frame order with simultaneous steps** (Def. 5.3, Theorem 6.7 (3), Def. A.4). The
   chronological order `<_R` of a frame is only a total *preorder* on the steps: the paper's own
   relativity-of-simultaneity discussion and §7 have `e₁ =_A e₂`. The paper speaks of "the total
   ordering of the execution according to the local time of R". We give two readings:
   `RelativisticallySatisfies` (every strict total order refining the frame order, i.e. ties broken
   arbitrarily) and `RelativisticallySatisfies'` (only frames in which no two steps are simultaneous).
   Both are equivalent to (1) and (2) for countable executions. For uncountable ones only the tie-free
   reading stays equivalent to (1).

4. **Finite vs infinite executions in Theorem 6.8.** Def. A.3 calls `𝒜` linearizable if the history of
   every *finite* classical execution is linearizable. Defs. 5.3/A.4 (relativistic) and 6.1
   (computational) quantify over *all* executions. The proof of Theorem 6.8 instantiates Theorem 6.7
   with "the execution is linearizable" and no finiteness. Taken literally, (1) ⟹ (3) would need
   linearizability of infinite histories to follow from that of their finite prefixes. That is not
   true in general: for some object types the set of linearizable histories is not limit-closed
   (Guerraoui–Ruppert, "Linearizability is not always a safety property", 2014). Def. A.3 also does not
   say what a sequential history over an infinite set of events is. We define all three notions over
   finite executions (`IsLinearizable`, `IsCompLinearizable`, `IsRelLinearizable`). With this reading
   Theorem 6.8 holds for every `Π`.

5. **Typing of `𝒫` in Theorem 6.7.** The paper calls `𝒫` "a predicate on classical executions", but
   (2) and (3) evaluate `𝒫` on total orderings of computational and relativistic executions. We take
   `𝒫` to be a predicate on arbitrary pairs `(S, <_S)` (`Property`).

6. **"Sequence" in Φ2 / P2 / A2.** A real-valued time map (or a world line) does not force a
   processor's steps to form a sequence `s₁, s₂, …`. Zeno behaviour has order type `ω + 1` at one
   processor, and then the "current state" of Φ2 is undefined. The proofs of Lemmas 6.2 and 6.3 assert
   "by CP1/RP2 these steps can be ordered into a sequence". We make this part of Φ2: the steps of each
   processor, in physical order, form a rooted consecutively permissible sequence. This is `ProcSeq`:
   a strict total order on `S_π` in which every step has finitely many predecessors, the first step
   starts in an initial state, and each step starts in the state its immediate predecessor ends in.
   The same predicate is used for P2 and A2.

7. **Definition 6.1, A1 is circular** ("`◁_S` is the transitive closure of the relation satisfying
   A2, A3", where A2 refers to `◁_S`). We formalize it as a fixed-point equation
   `◁ = TransGen((same processor ∧ ◁) ∪ message edges)`, together with A2 (`ProcSeq` for `◁`) and A3.
   This matches items (a) and (b) in the proofs of Lemmas 6.2 and 6.4. Acyclicity is implied by A2.

## Modelling choices

8. **Physics.** RP1–RP3 are abstracted into the structure `Spacetime`: a strict causal order; real
   frame times that are strictly monotone along `≺`; world lines are `≺`-chains. The proof of Lemma
   6.6 needs one more physical fact, which we make a field of `Spacetime`: some body is at rest in some
   frame `F`, and its world line is `γ : ℝ → Pt` with `time F (γ τ) = τ` and `τ < τ' → γ τ ≺ γ τ'`.
   As in the paper, all processors may share that world line. RP3's "iff" is used only in the
   direction "permissible transmissions go forward in `≺`". The postulate "every reference frame's
   order is total" is weakened to a real time coordinate, which can have ties (item 3). Minkowski
   spacetime (`minkowski d`) is an instance. Its frame time `t − ⟪v, x⟫` is the Lorentz time
   `γ_v (t − ⟪v, x⟫)` up to the positive factor `γ_v`, which does not change the order.

9. **Algorithms.** All processors share one type of states and one type of events (`Σ_π`, `E_π` of
   the paper are encoded through `init π` and `δ π`). A send event carries its message and intended
   recipient, and a receive event carries its message. "Messages are instances" (uniqueness of a send)
   and "every received message was sent" are not imposed. The paper does not impose them either.
   These are order-independent conditions on `S`, identical in all three kinds of executions, so they
   do not affect any result.

10. **Executions as orders on `↥S`.** Orders are relations on the subtype of steps of `S`. "`X` is
    extracted from `𝒳`" (Def. 4.4) is `∃ t, IsClassicalPhys A S t ∧ ∀ a b, lt a b ↔ t a < t b`, and
    similarly for relativistic executions.

11. **Linearizability.** We do not re-define Appendix A. We use CSLib's
    `Cslib.SharedMemory.HerlihyWing.Linearizable` (Herlihy–Wing with the Sela–Herlihy–Petrank
    amendment, one object, operations identified by (process, index)) on the history of a finite
    execution (`IsHistoryOf`: invocation/response events listed in `<_S` order). Theorem 6.8 is the
    Central Theorem instantiated with this property. The proof does not depend on what linearizability
    is, so any other history-level definition would do equally well.

12. **Section 7.** Only the geometry is formalized (`observation1_geometry`). Two operations happen in
    the `ε`-neighbourhoods of `(0, −u)` and `(0, u)` with `ε < 1/3`. Then the observer moving with
    velocity `u/2` sees the second operation entirely before the first, and the observer moving with
    `−u/2` sees the opposite. The JTUF algorithm and the resulting linearization orders are not
    modelled.
