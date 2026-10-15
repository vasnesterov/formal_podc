# Differences between the formalization and the paper

Paper: G. Sela, M. Herlihy, E. Petrank, *Linearizability: A Typo*, PODC 2021 (brief announcement),
full version arXiv:2105.06737v2. Section/definition numbers follow the arXiv version.

**Overall verdict: the paper is correct.** Every claim we formalized holds as stated, up to the
modelling choices below. We found no errors, only implicit assumptions (items 3 and 9).

## Modelling of histories (Section 2.1)

1. **Events.** An event is `inv p x o` or `res p x r` (`Cslib.SharedMemory.HerlihyWing.Event`). It has a process `p`,
   an object `x`, and an operation `o` (with its arguments) or a response `r` (termination
   condition and results merged into one value). All objects share the types `Op` and `Res`. The
   per-object sequential specification restricts which ones are meaningful.
2. **Operation identities.** The paper identifies operations of `H`, `H'`, `complete(H')`, `S` and
   `H|x` implicitly, through equivalence (`H|P = S|P`). We make this explicit: an operation is
   `OpId = (p, x, k)`, the `k`-th operation of process `p` on object `x`. Restricting to a process
   or an object does not change these identities, and in a well-formed history they agree with
   "the `k`-th invocation of `p`, paired with its next matching response" (Definition 2.1).
   `<_H` is `RT H a b`: both are operations (completed) of `H`, and the response of `a` comes
   before the invocation of `b`.
3. **Sequential specifications** are arbitrary sets of histories, one set per object
   (`SeqSpec = X → Set History`). We do **not** require them to be prefix-closed.
   - The "only if" direction of locality (Theorem 5.1) needs the empty history to be legal for
     every object (`hnil : ∀ x, [] ∈ spec x`). Prefix-closure plus non-emptiness, as the paper
     assumes, gives this. Without it the direction fails trivially: take an object whose
     specification contains no empty history.
   - Deterministic objects (`detSpec`) contain only *complete* sequential histories. This makes no
     difference: legality is only ever checked on complete sequential histories `S`.
4. **Pending invocation / `complete(H)`.** We define an invocation to be pending when no later
   event of the same process follows it (`keep`, `completeAux`). The paper says "no matching
   response follows". The two coincide on well-formed histories, and all results assume
   well-formedness.
5. **Extension.** `IsExtension H H'` means `H' = H ++ R`, `R` consists of responses only, and `H'`
   is well-formed. Well-formedness of `H'` is how we make "responses to pending invocations"
   precise: each appended response matches a distinct pending invocation of `H`.
6. **Sequential histories.** `IsSeq` is the paper's definition: invocation/matching-response pairs,
   possibly followed by one pending invocation. Complete sequential histories are `seqHist M` for a
   list `M` of operation records. In L1, `S` is a legal sequential history equivalent to
   `complete(H')`, so it is necessarily complete.
7. **Total operations** (Section 3.3, Theorem 5.2). `Total spec p x o` means: for every legal
   complete sequential history `s` of `x`, some response `r` makes `s · inv p x o · res p x r`
   legal. This is the formal reading of "defined for every object value". Every operation of a
   deterministic object is total (`detSpec_total`).

## Definitions

8. **Definitions 2.2 and 4.1** (`LinearizableHW`, `Linearizable`) are stated literally: extension,
   L1 via `complete(H')` and equivalence, and L2 as `<_H ⊆ <_S` or `<_{complete(H')} ⊆ <_S`.
   For proofs we use list characterizations (`IsLinO`, `IsLinA`), proved equivalent in
   `linearizableHW_iff` and `linearizable_iff`.
9. **Definition 7.1 (linearization points)** (`LinearizableLP`). A linearization point is a *gap*
   of `H`, given as a prefix length `lp a`: after the invocation (`Invoked (H.take (lp a)) a`) and,
   for completed operations, not after the response.
   - The paper's "distinct points" may share a gap. Their relative order is then the order of
     the resulting sequential history `S = seqHist M`, which is required to be sorted by `lp`.
     This is equivalent to choosing distinct real-valued points.
   - The set `T` of linearized pending invocations, and their responses, are the pending
     operations that occur in `M` together with their recorded responses.
   - "Placing invocation and response at the point" is expressed by requiring `M`'s operations and
     responses to match `H` (`Matches`).

## Proofs

10. **Theorem 5.1 (locality).** We prove the theorem by a different route from the paper's, which
    repeats Herlihy–Wing's transitive-closure/minimal-cycle argument with `<_H` replaced by
    `<_{complete(H')}`.
    - For each object we take its linearization and give its operations the running-maximum
      linearization points from Claim 1, computed in `H`.
    - Points of different objects never coincide, because each is the invocation time of an
      operation of that object.
    - We then merge all operations by (point, position). The merged list respects the real-time
      order of `H` and restricts to each per-object linearization.

    We did not formalize the cycle argument itself. Its reasoning looked correct on inspection.
11. **Theorem 5.2 (nonblocking).** We follow the paper's proof:
    - If the pending invocation is already linearized, the same linearization works.
    - Otherwise the operation is appended at the end of `S` with a response given by totality.
12. **Claim 1.** We follow the paper's proof: the point of `e_i` is right after the later of
    `e_i`'s invocation and `e_{i-1}`'s point, i.e. a running maximum of invocation times.
13. **Section 3 counterexamples.** We use concrete instances: values 0/1 for the registers, and
    `x = 1`, `y = 2` for the queue. All claims of Sections 3.1–3.3 and 5.1 are verified exactly
    as stated.
14. **Section 4 remark** ("L2 is equivalent to `<_{H'} ⊆ <_S`"). This is
    `WellFormed.precedes_complete_iff`, which gives real-time order towards completed operations
    in `complete(H)` vs. `H`.

## Section 6 (alternative interpretation)

15. `LinearizableAlt` formalizes Definition 6.1 combined with the original L2. Pending operations
    never end, so `a <_H b` holds iff `a` completed before `b` was invoked, where `b` may be
    pending.
    - The stack of Figure 5 is a *partial* specification: `pop` on the empty stack has no legal
      response. This models the paper's "spinning" pop.
    - We use `H_s` = `A: Push(1)` completed, then `B: Pop() → 1`, then `B: Pop()` pending. The
      figure does not fix whether `Push(1)` overlaps the first pop; this does not matter for the
      claims.

## Not formalized

16. The non-volatile-memory motivation, and the informal comparison with Lynch's atomicity
    definition.
17. The paper's own proof of Theorem 5.1 (minimal-cycle argument); see item 10.
