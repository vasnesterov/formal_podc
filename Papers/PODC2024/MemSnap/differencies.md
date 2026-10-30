# Differences between the formalization and the paper

Paper: Jayanti, Jayanti, Jayanti, *MemSnap: A Fast Adaptive Snapshot Algorithm for RMWable
Shared-Memory*, PODC 2024 (proceedings version; no arXiv version).

## Statement-level issues

1. **Lemma 7.2 (Figure 2) is false as printed** (`Counterexample.lemma_7_2_false`). The third
   disjunct of `Q` has to require `x_μ = X`, as the sentence before the lemma says ("a successful
   CAS at Line 12 that will cause `B[j].seq` to become equal to `X`"). Without it, `Q` contains a
   possibility that no linearization realizes (`Counterexample.not_tracked`), so `Q ⊄ P`. The
   counterexample satisfies all of the paper's hypotheses: one component, primitive `write`, two
   updaters, one scanner, 16 steps. With the condition added the lemma holds
   (`lemma_7_2_fixed`). *Rule:* R3 (typo / evident intent). The intent is stated in the paper's
   prose. The fix is one local conjunct. The proof is omitted, so no published argument uses the
   wrong version. Theorem 7.3 is unaffected. Borderline aspect: Lemma 7.2 is a numbered lemma and
   the printed set is wrong for a non-degenerate execution. We grade ⚠️ rather than ❌ only because
   R3 applies.

## Proofs

2. **Lemmas 7.1 and 7.2: proofs omitted in the paper ("for lack of space").** We supply both.
3. **Lemma 7.1:** `I₁` is invariant but not inductive. We prove the stronger inductive invariant
   `FInv`, and `I₁` follows from it (`FInv.i1`). The additions are:
   * the shape of local states (`Shape`): which line a process can be at, given its pending
     operation;
   * `x̂_π ≤ x_π` at lines 11–12, and `x = X` while the scanner is between the read and the write
     of `X` (line 1);
   * Part (3) for all processes (not only updaters at lines 6–8);
   * Part (6) extended to a process in the second iteration at lines 10–12 with `B[i] = b`
     (field `mission`). Without it a successful CAS of another process poised with an old
     `x < x̂_μ` breaks Part (7) from a state satisfying `I₁` (an unreachable state; argued in the
     README, not in Lean).
4. **Lemma 7.2 (corrected):** proved together with `FInv` by induction over Algorithm 2. The
   induction proves only `Q ⊆ P`; `Q ≠ ∅` follows from `I₁` alone (`QSet_nonempty`).
5. **Theorem 7.3:** the paper deduces linearizability from `P ≠ ∅` by the tracker theorem of
   [21] and the claim that Algorithm 2 "satisfies the two rules". We do not use [21]. We prove that
   every possibility in `P` is realized by a linearization in CSLib's sense (`tracked_of_mem_PP`,
   built from the generic closure rules of `Podc/.../MetaConfig.lean`). Then
   `Poss.linearizable_of_tracked` turns `P ≠ ∅` into `Impl.Linearizable`.
6. **Wait-freedom and time complexity** ("immediate from the pseudo-code") are proved with a
   potential (`theorem_7_3_waitFree`, `theorem_7_3_steps`): at most 9 accesses per operation, 2
   per click.

## Modelling choices

7. **Atomicity of `X ← X + 1`.** The paper treats line 1 as atomic because only the scanner writes
   `X`. We model it as a read of `X` followed by a write of `x + 1` (local state `c1w x`), so only
   read/write/CAS are used, as in Section 3. Algorithm 2's line-1 augmentation is attached to the
   write. This is a refinement; nothing depends on atomicity. Consequently a `click` takes 2 accesses in
   `theorem_7_3_steps` (1 in the paper's atomic reading); every execution of the atomic version is
   an execution of ours with the two accesses adjacent, so all results transfer.
8. **Component words.** The paper's `update(i, uop, uarg)` uses "any primitive supported by
   hardware". We take an arbitrary deterministic sequential specification `W` (any primitive set
   and any responses) and add a `read` to the principal words `A[i]`, which `forward` needs
   (line 11).
9. **Base objects.** `B[i]` is a CAS object over pairs `(val, seq)`; its read is the paper's read
   of the double word. `X` and `seq` are unbounded naturals (the paper uses 64-bit counters and
   argues overflow does not happen). Decidable equality of values is classical; it is only used
   to define the CAS.
10. **Components** are an arbitrary type `K` with decidable equality instead of `[1, m]`. Space
    complexity is not stated as a theorem; there are `2|K| + 1` base objects.
11. **Processes.** Any type `P` with decidable equality, possibly infinite, as in the paper's
    "arbitrary set of updater processes". The scanner `σ` is not an updater: `σ` invokes only
    `click`/`observe`, the others only `update` (`Allowed`). This matches the paper's `Π ∪ {σ}`
    and its remark that only the scanner calls `forward` from line 3.
12. **Responses.** `update` returns the primitive's response, `click` returns `ack`, `observe`
    returns a value; each is wrapped in the sum type `CResp`. Invocations and returns are separate
    labels (CSLib); a return is a step without memory access.
13. **Program counters.** The paper's `pc` values are encoded in local states: `c1`/`c1w x`/`c2`,
    `f9…f12` (with caller `u`: `none` = observe, `some o` = update; `k2` = second iteration),
    `o4`/`o5`, `u7`/`u8`. "`pc ∈ [3,5]`" is `Loc.IsObs`, "`pc ∈ [6,8]`" is `Loc.IsUpd`, `i_π` is
    `Loc.comp`. Local computation is folded into the preceding access (e.g. the test of line 10
    happens in the read of `X`).
14. **Ghost `x̂_π`** is set at the invocation of `observe`/`update`, as in Algorithm 2 (the
    augmenting statement precedes line 3/6). Invocations of `click` do not change it.
15. **Definition 6.2 (TransitionsOK)** is formalized with its stated precondition: the processes
    of the sequence are distinct, active and not linearized in `p` (`TransOK`). At line 1 this
    also requires the scanner itself to be unlinearized, which holds.
16. **`Q ≜ {p ∈ P* | …}`.** Figure 2 writes `p ∈ P*` and `∃ q ∈ P*` without defining `P*`;
    we read it as "all possibilities" (`QSet` ranges over all `CPoss`). The permutation `α ∈
    Perm(S)` of a subset `S` is a duplicate-free list `l` whose elements satisfy the membership
    condition of `S` (`Cand`).
17. **Possibilities** carry the abstract state and a flag `Option Resp` per process (`Poss`). The
    correspondence of Section 6 (a possibility ↔ a linearization of the run so far) is
    `Poss.Realizes`: the linearization ends in the abstract state, and the response it assigns to
    the current instance of each process is its flag (`none` = not linearized).
18. **Linearizability** is CSLib's `IsLinearization` (the amended Herlihy–Wing definition).
    Executions are finite label lists; `Impl.Linearizable` asks for a linearization function on all
    valid finite executions.

## Not formalized

19. Space complexity as a theorem; the far-future-linearization scenario of §5.3; parallel
    observation and dynamic addition (§8); the comparison with related work.
