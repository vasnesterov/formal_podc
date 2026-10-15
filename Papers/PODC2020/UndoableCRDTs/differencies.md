# Differences between the formalization and the paper

Paper: S. Dolan, *The Only Undoable CRDTs are Counters*, PODC 2020 (brief announcement), full
version arXiv:2006.10494v1 (with Appendix A).

**Overall verdict: the paper is correct.** Every claim below was formalized and holds under the
paper's definitions. The paper has no false statements. Item 2 is a clarification of how
Axiom 1 is read, item 6 is a minor edge case, and items 4 and 17 list typos.

## Definitions (Section 2)

1. **Partial operations and actions.** A primitive operation is `app p : S → Option S`. An action
   is a `List P` applied left to right, so `act s [p, q] = s · p · q = q(p(s))`. `Ok s a` is
   "`s · a ok`". This matches the paper's conventions exactly.
2. **Clarification: Axiom 1 includes `p = q`.** This is not an error in the paper. Axiom 1 as
   stated has no distinctness condition, and Fact 2 is derived "by applying Commutativity with
   `a = b`". Only the introductory prose ("any two primitive operations … commute") is ambiguous.
   We state Axiom 1 literally, as "for all `p, q`". Everything after Fact 2 depends on it, and
   the case is needed: We added
   `OpSystem.CommutativeDistinct`, Axiom 1 for `p ≠ q` only. The nonnegative counter `nnCounter`
   has states `ℕ` and a `dec` that is undefined at `0`. It satisfies `CommutativeDistinct`,
   Axiom 2, finiteness and reachability. However, it is not equivalent to *any* undoable CRDT
   (`nnCounter_not_equiv`), and in particular to no tuple of counters. So under the "distinct
   operations" reading, which is natural if Axiom 1 means "two different concurrent operations",
   the main theorem is false. The paper's justification for `p = q` is that two replicas can
   independently perform the same operation. Shapiro et al.'s Definition 2.6 concerns concurrent
   operation *instances*, which may be equal as operations. The paper's reading is therefore
   legitimate but strong. Even the plain nonnegative counter, often considered an
   operation-based CRDT, is not a CRDT under it (`nnCounter_not_commutative`). The paper's
   Section 3 remark "an undoable CRDT cannot represent a nonnegative counter" is formalized by
   `nnCounter_not_equiv`: the nonnegative counter is equivalent to no undoable CRDT. That result
   does not use Axiom 1 for `nnCounter` itself.
3. **Standing assumptions are part of the definition.** "`P` is finite" and "all states are
   reachable from `s₀`" are fields of `CRDT` (`finite`, `reachable`). The paper's other
   assumption, "distinct members of `S` are logically distinct states", has no formal content and
   is not modelled.
   - Finiteness of `P` is used only in Section 2.5, to show that `G_s` is finitely generated, and
     it is needed there. For example, `ℚ` with the operations `±1/n` for all `n` is commutative
     and undoable, but its group of actions `ℚ` is not finitely generated. This is not
     formalized.
   - Reachability is used for "`G_{s₀}` ≅ states" (`stateEquiv`) and for Fact 6 at `s₀`.
4. **Equivalence (Section 2.2)** is stated literally. "`φ(s) · ψ(p) = φ(s · p)` if `s · p ok`"
   means that the left side is well defined and equal to the right side. The paper's third
   bullet reads "`φ⁻¹(s') · ψ'(p) = φ⁻¹(s' · p')`". This is a typo for `ψ'(p')`, and we use
   `ψ'(p')`. The definition only constrains *applicable* operations. It does not require
   `φ(s) · ψ(p)` to be undefined when `s · p` is undefined. This is what makes Proposition 3 work
   with dead operations (item 6), which are sent to `ε`.
5. **Counters and tuples.** The counter modulo `n` is `OpSystem.modCounter n`, with states
   `ZMod n` and the operations `inc` and `dec`. The unbounded counter is `modCounter 0`, because
   `ZMod 0 = ℤ` definitionally. A tuple is indexed by an arbitrary finite type `ι` with decidable
   equality, instead of `1..n`. It has states `∀ i, Sᵢ` and operations `Σ i, Pᵢ` (Section 2.3).

## Statements

6. **Section 3, "All operations are always valid".** Nothing in the definitions forbids a
   primitive operation that applies in no state. `deadOp` is an undoable CRDT with one state and
   one never-applicable operation (`deadOp_not_valid`). The correct statement, which we prove as
   `all_operations_valid`, is: an action that applies in *some* state applies in *every* state.
   This is harmless for the main theorem, because the weak equivalence of item 4 maps dead
   operations to anything.
7. **Section 3, "Negative states always exist"** is stated for actions that apply somewhere
   (`negative_states`). For a dead operation it is false.
8. **The main theorem** (`theorem_main`) is stated as: there are a finite type `ι` and moduli
   `m : ι → ℕ` such that `C` is equivalent to `counters m`, the tuple of counters modulo `m i`.
   We additionally record that each `m i` is `0` (unbounded counter) or a prime power `p^k`. Here
   `k = 0`, giving a trivial counter, is not excluded, since Mathlib's structure theorem does not
   exclude it.
9. **Proposition 3** is stated for two *undoable* CRDTs. This is implicit in the paper, since
   `G_{s₀}` is only defined, as a group, for undoable CRDTs.
10. **Section 2.6** ("the group of actions of a counter is `ℤ` or `ℤₙ`; of a tuple, the direct
    sum") is proved directly for tuples of counters: `countersGroupEquiv : G_{s₀}(counters m) ≃+
    ∀ i, ZMod (m i)`. The general statement "G of a tuple = direct sum of the G's" is not
    formalized, since the main theorem does not need it.
11. **Section 3, trade-off.** "In any CRDT with `2ⁿ` states … one of the following must be true"
    is formalized for *every* CRDT as `tradeoff`: either some operation is not undoable, or `S` is
    infinite, or there is `k ≥ 1` such that `s · pᵏ = s` for every applicable `p` and every `s`.
    The `2ⁿ` "membership" states are not modelled. The informal "extra states" reading is
    "infinitely many states". `finite_states_periodic` gives the stronger uniform statement for
    actions: `k` is the exponent of `G_{s₀}`.

## Proofs

12. **Propositions 1 and 2, Facts 1–6** follow the paper's inductions. One difference is that
    Proposition 2 is proved by induction on the *first* operation of the action, not the last:
    `(p b)⁻¹ = b⁻¹ q₁…qₙ`. Fact 3 is stated with an explicit chosen inverse `a'` satisfying
    `s · a a' = s`. Fact 1 keeps the paper's hypothesis that `s · a₁ ok`, although it is not
    needed.
13. **The group `G_s` (Lean-only detail).** The paper's argument is complete: inverses in a
    monoid are unique, so "inverses exist thanks to fact 5" suffices. In Lean, `neg` is defined
    from a chosen inverse `a⁻¹ₛ` (Proposition 2). We therefore first build the commutative monoid
    on the quotient, then prove well-definedness from uniqueness of inverses (`Neg` instance in
    `Group.lean`).
14. **Section 2.5.** The paper writes "generated by `P/≡ₛ`". We use the finite set of classes
    `[p]` of the primitive operations that apply in `s`.
15. **Proposition 3.** The paper defines `φ(s) = s₀' · ψ(a)` for some `a` with `s₀ · a = s`. We
    use `φ = e₂ ∘ ψ ∘ e₁⁻¹`, where `eᵢ : G_{s₀} ≃ S` is `[a] ↦ s₀ · a` (`stateEquiv`, a
    bijection by injectivity of `≡` and reachability). For a primitive operation `p` that applies
    at `s₀`, `ψ(p)` is a representative (`Quotient.out`) of `ψ([p])`. For a dead operation it is
    `ε`. The verification of the three conditions is as in the paper.
16. **The structure theorem** (Kronecker/Poincaré/Noether) is Mathlib's
    `AddCommGroup.equiv_free_prod_directSum_zmod`. `directSumEquivPi` identifies
    `ℤⁿ × ⨁ᵢ ℤ/pᵢ^{eᵢ}` with `∀ j, ZMod (m j)`.

## Typos in the paper

17. Besides ψ'(p) for ψ'(p') (item 4):
    - The proof of Proposition 3 writes `ϕ(s) · ψ(p) = s₀ · ψ(a) · ψ(p)`; it should be `s₀'`.
    - Section 2.5 writes "by fact 5 `s · a⁻¹ₛ ok`"; this is Fact 4.

## Not formalized

18. Section 1 (OR-Set, PN-Set, T-Set, Figure 1, Logoot-Undo) is informal motivation. The OR-Set
    does not fit the paper's own model with finite `P`: its removes carry sets of observed IDs,
    and its adds carry fresh IDs.
