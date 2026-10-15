# The Only Undoable CRDTs are Counters — PODC 2020

Stephen Dolan. *Brief Announcement: The Only Undoable CRDTs are Counters.* PODC 2020, pp. 57–58.
DOI [10.1145/3382734.3405749](https://doi.org/10.1145/3382734.3405749). Formalized version: the full version
arXiv:2006.10494v1, whose Appendix A contains the proofs.

**Verdict: ✅ Correct.** The main theorem (every undoable CRDT is equivalent to a tuple of counters and modular
counters), Propositions 1–3, Facts 1–6 and the Section 3 consequences all hold under the paper's own definitions.
There are only typos, one point of reading that matters, and one degenerate edge case.

## Mistakes in the paper

There are no false statements. Three points are worth knowing.

- **Axiom 1 must include `p = q` (a clarification, not an error).** Axiom 1 has no distinctness condition, and
  Fact 2 uses "Commutativity with a = b", so the paper is consistent. The introductory prose ("any two primitive
  operations … commute") could be read as "two *different* operations", and under that reading the theorem is false.
  The nonnegative counter (states ℕ, `dec` undefined at 0) commutes for distinct operations, is undoable, has
  finitely many operations and every state is reachable. Yet it is equivalent to no undoable CRDT, so it is not a
  tuple of counters. Under the paper's literal Axiom 1 it is simply not a CRDT: from state 0, `inc` then `dec` with
  `p = q = dec` breaks the axiom. (`nnCounter_commutativeDistinct`, `nnCounter_not_equiv`,
  `nnCounter_not_commutative`)
- **"All operations are always valid" (Section 3) fails for dead operations (degenerate case).** The definitions
  allow a primitive operation that applies in no state. A one-state CRDT with one such operation is undoable. The
  correct statement, which we prove, is that an action applying in *some* state applies in *every* state. The same
  caveat applies to "negative states always exist". The main theorem is unaffected, because the paper's equivalence
  only constrains applicable operations, so dead operations can be mapped to the empty action.
  (`deadOp_not_valid`, `all_operations_valid`, `negative_states`)
- **Typos.**
  - In the definition of equivalence (Section 2.2), `φ⁻¹(s') · ψ'(p)` should be `ψ'(p')`.
  - In the proof of Proposition 3, `s₀ · ψ(a) · ψ(p)` should be `s₀' · ψ(a) · ψ(p)`.
  - In Section 2.5, "by fact 5, s · a⁻¹ₛ ok" should cite Fact 4.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** Purely algebraic, exactly as in the paper, with no replicas, network, failures or randomness.
- An `OpSystem` has states `S`, an initial state `s0`, primitive operations `P`, and partial maps
  `app p : S → Option S`. Actions are lists of operations applied left to right.
- A `CRDT` additionally has finitely many operations, every state reachable from `s0`, and Axiom 1 stated literally
  for all `p, q`. An `UndoableCRDT` also satisfies Axiom 2.
- `CRDTEquiv` is the paper's equivalence of Section 2.2, verbatim (with the `ψ'(p')` typo fixed). It consists of a
  bijection of states and translations of operations into actions in both directions, constrained only on
  applicable operations.
- Counters: `OpSystem.modCounter n` has states `ZMod n` (the unbounded counter is `n = 0`). `counters m` is
  the tuple of counters modulo `m i`, indexed by an arbitrary finite type.

**Main results in Lean** (namespace `UndoableCRDTs`).

| Paper | Lean | File |
|---|---|---|
| Proposition 1 (actions commute) | `OpSystem.prop1` | `Actions.lean` |
| Proposition 2 (actions are undoable) | `OpSystem.prop2` | `Actions.lean` |
| Facts 1–6 | `OpSystem.fact1` … `OpSystem.fact6` | `Actions.lean` |
| §2.4–2.5: `G_s` is a finitely generated abelian group; states ≅ `G_{s₀}` | `UndoableCRDT.G`, `groupOfActions_fg`, `UndoableCRDT.stateEquiv` | `Group.lean`, `Main.lean` |
| Proposition 3 (isomorphic `G_{s₀}` ⇒ equivalent) | `UndoableCRDT.prop3` | `Group.lean` |
| §2.6: group of a tuple of counters is `∏ ℤ/mᵢ` | `UndoableCRDT.countersGroupEquiv` | `Counters.lean` |
| **Theorem** (every undoable CRDT ≃ a tuple of counters) | `theorem_main` | `Main.lean` |
| Section 3 consequences | `all_operations_valid`, `negative_states`, `tradeoff`, `finite_states_periodic` | `Main.lean` |
| Section 3: no undoable nonnegative counter | `nnCounter_not_equiv` | `Counterexamples.lean` |

`theorem_main` also records that each modulus is `0` (unbounded counter) or a prime power. The structure theorem
for finitely generated abelian groups comes from Mathlib.

**Not formalized.** The informal motivation of Section 1 (OR-Set, PN-Set, T-Set, Figure 1). The OR-Set does not
fit the paper's model, because its removes carry observed IDs, so it has infinitely many primitive operations.
The Section 3 trade-off is proved for every CRDT, without modelling the `2ⁿ` membership states.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
counterexamples (`nnCounter`, `deadOp`) also show that the hypotheses are satisfiable and that the literal
Axiom 1 is needed. Self-contained: it depends only on Mathlib.
