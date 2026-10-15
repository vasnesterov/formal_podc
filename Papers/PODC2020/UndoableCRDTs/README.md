# The Only Undoable CRDTs are Counters (PODC 2020)

Stephen Dolan. *Brief Announcement: The Only Undoable CRDTs are Counters.* PODC 2020, pp. 57–58,
DOI 10.1145/3382734.3405749.
- Formalized version: the full version **arXiv:2006.10494v1** (18 Jun 2020), which adds Appendix A
  with the proofs. Local copy: `papers/2020/3382734.3405749_Brief_Announcement_The_Only_Undoable_CRDTs_are_Counters.pdf`.
- The paper has a **single author, Stephen Dolan** (OCaml Labs). W. Yu, V. Elvinger and C.-L. Ignat
  are the authors of reference [7] (a generic undo for state-based CRDTs, OPODIS 2019), not of this
  paper.

## Status

**Complete. No `sorry`, no axioms.** `#print axioms` on every result below reports at most
`propext`, `Classical.choice` and `Quot.sound`. Build with
`lake build Papers.PODC2020.UndoableCRDTs.Counterexamples` (which imports everything).

**The paper is correct.** The main theorem and Propositions 1–3 hold under the paper's own
definitions. All of Facts 1–6 and the Section 3 consequences hold too. See `differencies.md`.
- **Clarification: Axiom 1 includes `p = q`.** Axiom 1 has no distinctness condition, and Fact 2
  explicitly applies "Commutativity with `a = b`". Only the prose "any two primitive operations"
  is ambiguous. The case matters: with Axiom 1 for distinct operations only, the nonnegative
  counter satisfies all hypotheses but is equivalent to no undoable CRDT (`nnCounter_not_equiv`).
- **Minor edge case:** "all operations are always valid" (Section 3) holds for operations that
  apply in at least one state. The definitions also allow "dead" operations that apply nowhere
  (`deadOp`).
- **Typos:** ψ'(p) for ψ'(p') in Section 2.2; `s₀ · ψ(a) · ψ(p)` for `s₀' · …` in the proof of
  Proposition 3; "by fact 5" for "by fact 4" in Section 2.5.

## Model (explicit)

The model is purely algebraic, with no replicas, network, failures or randomness. It is the
paper's abstraction of operation-based CRDTs (Shapiro et al.'s CmRDTs). Concurrency is captured
entirely by Axiom 1.
- `OpSystem`: states `S`, an initial state `s0`, primitive operations `P`, and partial functions
  `app p : S → Option S`.
- Actions are `List P`, applied left to right: `act s [p, q] = s · p · q`. `Ok s a` means `s · a`
  is well defined.
- `CRDT`: `P` is finite, every state is reachable from `s0`, and Axiom 1 (`Commutative`) holds.
- `UndoableCRDT`: a `CRDT` that also satisfies Axiom 2 (`Undoable`).
- `CRDTEquiv C₁ C₂`: the paper's equivalence (Section 2.2), stated literally. It consists of a
  bijection `φ` with `φ s0 = s0'` and translations `ψ : P₁ → P₂*` and `ψ' : P₂ → P₁*` that
  simulate every *applicable* operation in each direction.
- The group of actions `G s` is the quotient of the actions applicable in `s` by `≡ₛ`. It is
  written additively and has an `AddCommGroup` instance.
- Counters: `OpSystem.modCounter n` has states `ZMod n`, initial state `0`, and the operations
  `inc` and `dec`. For `n = 0` this is the unbounded counter, since `ZMod 0 = ℤ` definitionally.
  `UndoableCRDT.counters m` is the tuple of the counters modulo `m i`, for `i` in a finite index
  type.

## Main results ↔ Lean (namespace `UndoableCRDTs`)

| Paper | Lean | File |
|---|---|---|
| Section 2: CRDT, Axiom 1, Axiom 2 | `CRDT`, `UndoableCRDT`, `OpSystem.Commutative`, `OpSystem.Undoable`, `OpSystem.Reachable` | `Defs.lean` |
| Section 2.2: equivalent CRDTs | `CRDTEquiv` | `Defs.lean` |
| Section 2.3: tuple construction | `OpSystem.tuple`, `CRDT.tuple`, `UndoableCRDT.tuple` (`tuple_commutative`, `tuple_undoable`, `tuple_reachable`) | `Defs.lean`, `Counters.lean` |
| Section 1.1: (modulo-n) counter is an undoable CRDT | `UndoableCRDT.modCounter` | `Counters.lean` |
| **Proposition 1** (commutativity of actions) | `OpSystem.prop1` | `Actions.lean` |
| **Proposition 2** (undoability of actions) | `OpSystem.prop2` | `Actions.lean` |
| Facts 1–6 | `OpSystem.fact1` … `OpSystem.fact6` | `Actions.lean` |
| Section 2.4: `G_s` is an abelian group | `UndoableCRDT.G`, `instAddCommGroupG` | `Group.lean` |
| Section 2.5: `G_s` is finitely generated | `instance : AddGroup.FG (C.G s)`, `groupOfActions_fg` | `Group.lean`, `Main.lean` |
| (implicit) states ≅ `G_{s₀}` | `UndoableCRDT.stateEquiv` | `Group.lean` |
| **Proposition 3** (isomorphic `G_{s₀}` ⇒ equivalent) | `UndoableCRDT.prop3` | `Group.lean` |
| Section 2.6: the group of actions of a tuple of counters is `⊕ ℤ/mᵢ` | `UndoableCRDT.countersGroupEquiv` | `Counters.lean` |
| **Theorem** (every undoable CRDT is equivalent to a tuple of counters / modulo counters) | `theorem_main` (moduli are `0` or prime powers) | `Main.lean` |
| Section 3: "all operations are always valid" | `all_operations_valid` (for operations valid somewhere); `deadOp`, `deadOp_not_valid` | `Main.lean`, `Counterexamples.lean` |
| Section 3: "negative states always exist" | `negative_states` | `Main.lean` |
| Section 3: trade-off (not undoable / infinitely many states / all operations cyclic) | `tradeoff`, `finite_states_periodic` | `Main.lean` |
| Section 3: no undoable nonnegative counter | `nnCounter_not_equiv` (equivalent to no undoable CRDT); also `nnCounter_not_commutative` (it violates Axiom 1 with `p = q`) | `Counterexamples.lean` |
| (new) Axiom 1 with `p = q` is essential | `nnCounter_commutativeDistinct`, `nnCounter_undoable`, `nnCounter_not_equiv` | `Counterexamples.lean` |

The structure theorem for finitely generated abelian groups is Mathlib's
`AddCommGroup.equiv_free_prod_directSum_zmod`.

## Not formalized

The motivating examples of Section 1 are not formalized: the OR-Set's failure of undo (Fig. 1),
the PN-Set and the T-Set. They are informal, and the OR-Set does not fit the paper's model with
finitely many primitive operations, because removes carry the observed IDs. The counter and the
modulo counter (Section 1.1) are formalized.

## CSLib candidates

None for now. The framework (`OpSystem`, actions, the group of actions) is small and specific to
this paper. If more CRDT papers are formalized, `Defs.lean` + `Actions.lean` + `Group.lean` could
become a `Podc/CRDT/` (or CSLib) module for operation-based CRDTs.

## Effort

About 0.2M tokens, with no subagents.
