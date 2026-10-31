# Differences between the formalization and the paper

Paper: Wei, Huang, Lu, *Specification and Implementation of Replicated List: The Jupiter Protocol
Revisited*, arXiv:1708.04754v4 (full version of the PODC 2018 brief announcement).

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Out-of-range positions break CP1 (Section 2.3 + Section 2.4 + Figure A.1) — ⚠️ by R3,
   borderline ❌.** Section 2.3 explicitly allows `Ins(a, p)` / `Del(p)` with `p` beyond the list
   size ("insertion/deletion at the end"). Section 2.4 says that Figure A.1 gives "OT functions
   satisfying CP1". The clients send the user operation unchanged (Alg. B.5 line 9, Alg. C.5).
   With such positions CP1 fails (`cp1_fails`). Jupiter and CJupiter then diverge, so Theorem 11,
   Theorem 18 and the solution of the conjecture are false for the literal model
   (`jupiter_raw_counterexample`, `cjupiter_raw_counterexample`). The failure of `A_weak` holds for
   every well-formed abstract execution complying with the run, not only for our choice of `vis`
   (`cjupiter_raw_not_weak_any`, `jupiter_raw_not_weak_any`): `c₁`'s final `Read` misses `c₁`'s own
   insertion. (The failure of `A_cp` uses `vis` = happened-before; with an arbitrary `vis` the two
   `Read`s need not see the same updates.) Theorem 12 (equivalence) is not refuted: both protocols
   diverge in the same way (`cex_run`, `cex_run_cjupiter`). The fix is local: normalise the position
   when the operation is generated (`genOp`), i.e. one extra line in `Do`. The paper itself shows
   that this is intended: it requires transformed operations to "insert (resp. delete) the element
   `a`", and the OT functions it cites assume in-range positions. With the fix all statements hold.
   Why ⚠️ rather than ❌: the paper's proofs only use CP1 abstractly, the fix is a missing case in
   pseudocode, and the intended version can be recovered from the paper. Why borderline: the
   out-of-range convention is stated explicitly, so R4 would not excuse it. R3 applies because the
   paper states the intended behaviour itself (Appendix A: a transformed `Ins(a, p)`/`Del(a, p)`
   still inserts/deletes the element `a`, which presupposes in-range positions), the fix is a
   missing case in the `Do` pseudocode, and no proof of the paper reasons with out-of-range
   positions (CP1 is cited, not proved). A stricter reading (the convention is the paper's own
   definition and the fix changes the protocol) would give 🚨, since Theorems 11/18 are headlines;
   we judge the normalisation too evident to be a protocol design change.

## Proof-level issues (🛠️, statements true)

2. **Lemmas 22–25 / Theorem 26.** These are sketches: Lemma 23's inductive step; Lemma 24 Case 2.2
   ("step ladder"); Lemma 22 ("parallel transitions"). The one-step claim in the proof of Lemma 25
   requires that the operation "not correspond to any element of the list in `v`". This excludes
   deletions of common elements, which the induction needs. We replace Section 5's argument (see
   README):
   - the vertices of the global space are the causally closed sets of the form "a `≺s`-prefix plus
     operations of one client" (`Sched.Vert`);
   - these sets are closed under intersection (`Sched.Vert.inter`), so `V₁ ∩ V₂` plays the role of
     the unique LCA with disjoint paths (Lemmas 23–24);
   - lists along a path preserve the relative order of surviving elements
     (`Sched.sublist_of_subset`, Lemma 25);
   - common elements of two lists were inserted in `V₁ ∩ V₂` (`Sched.mem_L`).
3. **Remark after Definition 19.** "By definition, `lo` is transitive on `{a | a ∈ w}`" is false
   without pairwise compatibility. It follows from Theorem 26 (used in `Cfg.GI.weak`).
4. **Proposition 9 / Lemma 5 / Propositions 14, 16.** These are proved by induction sketches; the
   hard case of Prop. 9 (Case 2, an operation in the middle of the client's sequence) is only
   illustrated. We prove instead:
   - CJupiter: every replica's state space is sound and complete with respect to the global
     space (`CJup.CPI`, `CJup.walk`);
   - Jupiter: every edge of every 2D state space is an edge of the global space (`Jup.JPI`), and
     the edges each `xForm` needs exist.

   We do not prove the literal statements "CSS_s = ⋃ DSS_s^i" and "DSS_ci ⊆ CSS_ci" as equalities
   or inclusions of graphs. Our invariants imply what Theorems 12 and 18 need.
5. **Footnote 8.** It defines the LCAs as an antichain of common ancestors and does not require
   them to be lowest. Our proof does not need LCAs.

## Modelling choices

6. **Elements.** Inserted elements are the operation identifiers `(client, seq)`. The paper assumes
   unique elements "achieved by attaching replica identifiers and sequence numbers"; user content
   plays no role in the specification.
7. **Priorities.** The priority of an insertion is its client id, and Figure A.1's rule is taken
   literally (larger `pr` is shifted). Appendix A's prose says the smaller id has the higher
   priority, which contradicts that rule. With our convention, the schedule of Figure 1 ends in
   `ab` instead of `ba`. Any fixed convention works.
8. **OT with `NOP`.** Figure A.1 omits these cases. We use `OT(NOP, o) = NOP` and
   `OT(o, NOP) = o`.
9. **`Del` on an empty list.** It is recorded as `Del(⊥, k)` in the `do` event and sent as `NOP`.
   The paper leaves this case undefined.
10. **`Read`.** It generates a `NOP` operation that goes through the server, as `Do` does in
    Algorithms B.5/C.5 for every user operation. Reads do not change any list.
11. **Visibility.** The abstract execution uses `vis(e, e') ⇔ e` is earlier and its operation was
    processed by the replica of `e'` when `e'` happened. We prove that this is a well-formed
    visibility relation (`AbsExec.WF`). We do not prove that it coincides with Lamport's
    happened-before, which is the `vis` the proof of Theorem 18 picks. The specification only asks
    for *some* well-formed `vis`.
12. **Executions.** Executions are finite sequences of enabled events. FIFO reliable channels are
    built into the model, and fairness is not modelled. Non-vacuity: every handler succeeds
    whenever its channel is non-empty (`*_enabled`). The replicas agree once all channels are empty
    (`jupiter_quiescent`).
13. **Data structures.**
    - A state space is the list of its edges plus the current vertex.
    - `Locate` is implicit: the loop starts from `op.ctx`.
    - In Jupiter, "the edge of `u` in dimension `d`" is the latest added matching edge, which
      models the array overwrite of Algorithm C.4.
    - In CJupiter, `firstEdge` returns the edge that `Compare` ranks before all other edges of the
      vertex. `Compare` is not a priori a total order.
    - The loops run with fuel `|cur|`; we prove the fuel suffices.
14. **Theorem 12 ("behaviors are the same").** It is formalized as follows: for every event
    sequence, both protocols accept it or neither does, and they reach configurations with the
    same `do` events (replica, operation, returned list), the same knowledge, server order and
    identifiers in transit, and the same list at every replica (`equivalence`). Since this holds
    for every prefix, the behaviours coincide step by step.
15. **Proof device.** The global state space (`Sched.T`, `Sched.L`) is defined directly from a
    schedule. The schedule's ranks come from the final configuration of the execution (a
    prophecy), not from a constructed graph.
