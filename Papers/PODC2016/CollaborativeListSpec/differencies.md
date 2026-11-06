# Differences between the formalization and the paper

Paper: Attiya, Burckhardt, Gotsman, Morrison, Yang, Zawirski, *Specification and space complexity
of collaborative text editing*, TCS 855 (2021), which is the full version of PODC 2016. We use the
TCS numbering: TCS Theorems 8 and 9 are PODC Theorems 4 and 5, and TCS Theorem 1 is PODC Theorem 1.
The PODC version's Theorem 1 claims only the strong specification; the TCS version adds eventual
visibility. The verdict judges PODC 2016 (with its extended version). Its RGA pseudocode (Sections 4.1
and 4.2), Definitions 1–13 and the lower-bound construction (Fig. 4) are the same as in TCS. Other
renumberings: PODC Lemma 3 = TCS Lemma 6; PODC appendix Lemmas 13–16 = TCS Lemmas 3, 4, 5, 7; PODC
Claims 6–9 = TCS Claims 10–13. PODC Theorem 5 claims the bound for "some replica"; TCS Theorem 9
claims it for every replica `R₁`. We prove the stronger TCS form.

## Statement-level issues

1. **RGA's insert counts tombstones (Section 4.2 + "Insert" of Section 4.1) (🔧).** As written, RGA
   violates condition (1c), so Theorem 1 is false for the protocol as stated.
   - Counterexample: `ins(x,0); ins(y,1); del(x); ins(b,1)` at one replica. The last response is
     `[b, y]`, while (1c) requires `b` at index 1.
   - Lean: `RGA.literal_not_weak` (for any number of replicas) and `RGA.literal_not_satisfies`.
     There is no abstract execution in `A_weak`, so none in `A_strong`.
   - Fix: take the parent in the visible list `s(N) \ T` (`RGA.parentFor`), as the original RGA
     does. With it, Theorem 1 is proved (`RGA.theorem1_strong`).
   - The intent is recoverable from the paper itself. Section 3 says that `ins(a,k)`
     inserts at position `k` of the list returned to the user, and (1c) states this on the
     response. Insert's prose takes "the element to the left of the insertion position". Section
     4.1 states Insert for trees without tombstones, where `s(N)` *is* that list. The fix is local:
     the same state, messages and tree rule (the new node becomes the child of its left neighbour),
     with the index computed in `s(N) \ T` instead of `s(N)`. It is not a design change. The proof
     ("(1c) follows directly from the properties of the data structure") never reasons with the
     tombstone-counting index.
   - The pseudocode explicitly writes `s(N)`, so Theorem 1 is false for the paper's own algorithm
     `R_rga` as printed. The abstract presents that claim as a contribution ("a strong list
     specification, which we prove is implemented by an existing protocol"). However, that abstract
     sentence remains true for the original RGA [24], which indexes the visible list.
2. **(TCS only: Theorem 1 of PODC 2016 does not claim eventual visibility.) Definition 10
   (eventual visibility) has no connectivity assumption (✏️).** As literally
   stated, the liveness part of TCS Theorem 1 fails: in `RGA.def10_needs_connectivity`, replica 0 inserts and never
   sends, and replica 1 reads forever. The intended hypothesis is recoverable from the paper:
   - the remark after Definition 10 ("a protocol would rely on the network being sufficiently
     connected");
   - the proof of Theorem 1 ("If α is infinite, this already follows from our definition of a
     sufficiently connected network");
   - the analogous Definition 18, which includes it.

   We prove Theorem 1's liveness for infinite executions under Definition 1
   (`RGA.theorem1_eventualVisibility`). Taken literally, Definition 10 is violated by
   *every* protocol that can buffer an update: no protocol can make an unsent update visible. So
   no reader would take it literally.

The lower bound (TCS Theorems 8 and 9 = PODC Theorems 4 and 5) has no statement-level issue.

## Proof gaps (no effect on the statements)

3. **Claim 12 (adjacency) (🔧).** The paper concludes `v = …[ᵢ₋₁ ]ᵢ₋₁…` "from the definition of the weak
   list specification". The specification only fixes the *set* of elements of `v`. Adjacency, which
   lets `R₂` insert `x` between the brackets, needs another argument. `lo` orders both `v` and
   `R₁`'s earlier response at `ins ]ᵢ₋₁`, which has the same elements, and `lo` is transitive on
   `v`. Hence `v` equals `R₁`'s list (`eq_of_pairwise`). That list is computed from the user's
   positions by induction (`rval_insert_phase`).
4. **Which state is `σ_w` (🔧).** The paper takes `σ_w` at the end of `α_w`, *after* the final read. In
   the model of Section 2 a `do(read)` may change the state and the buffer. So `σ_w ≠ σ_{w'}` would
   not give distinct internal states `q`, which is what the metadata overhead measures. We take the
   state right after `send(m_{d+3})`. Its buffer is empty, and its content (the unique `w` with
   `do(read, w)` enabled) is `[∗]`, which the appended read shows.
5. **User assumptions on the constructed executions.** The paper never checks that `α_w`, `β_w^i`
   and `γ_w^i` respect the assumption that users delete only elements in the previous response. The
   protocol is only required to be correct on such executions. We prove it, together with
   well-formedness and the responses, by induction along `α_w` (`alpha_ok`).
6. **Lemma 7 / the list order.** The paper defines `lo` from all replica states and argues
   totality "w.l.o.g. all messages are delivered" (extending finite executions). We define `lo` as
   the order of `s(N_all)` instead, where `N_all` is the TI tree of *all* nodes created, and use
   Lemma 6 for every replica tree `N ⊆ N_all`. No extension is needed. Infinite executions use the
   union over prefixes (`RGALive.lean`).
7. **Lemma 6's proof.** The paper adds an arbitrary leaf whose parent is present. We prove the
   special case for the node with the *largest* timestamp (`s_cons_max`, which is also the remark
   after the Insert procedure) and induct by removing that node. The statement is the same.

## Modelling choices

8. *Replicas.* There is one internal-state type `Q` for all replicas (a per-replica family embeds
   into a sigma type). Transition functions are total, because every `do` and every `receive` is
   enabled. The protocol class is that of PODC 2016, Section 2, in full:
   - The response of `do(op, _)` is `resp r σ op`, a function of the whole state `σ = (q, m)`
     (PODC 2016 only requires determinism; the TCS version adds that it depends on `q` only).
   - `doStep` may change the whole state, including the buffer.
   - `send` from `(q, m)` moves to `(sendStep r (q, m), ⊥)` for an arbitrary function `sendStep`
     (PODC 2016: `Δ((q, m), send(m)) = (q′, ⊥)` for some `q′`; the TCS version requires
     `q′ = q`). The transition is also defined on `(q, ⊥)`, but such a send is not enabled and
     never occurs in a well-formed execution.

   Since the TCS class is a subclass, `theorem8`/`theorem9` cover both versions. RGA instantiates
   it with `sendStep (q, m) = q` and responses that read only `q`.
9. *Messages.* A receive names the *position* of its send event, which gives the "unique messages"
   of the paper. The receive transition sees only the payload. Broadcast goes to all replicas,
   including the sender.
10. *Executions.* Executions are finite lists. Infinite executions (`ℕ → Act`, all prefixes well
    formed) are used only for eventual visibility. Definition 1 is formalized for infinite
    executions. Its eventual delivery covers replicas `R′ ≠ R`, as in the paper.
11. *Abstract executions.* Events are the positions of `do` events in the execution, which share
    event ids with the abstract execution (footnote 4), so compliance is built in. We drop the
    linearization `H` and require `vis` to be transitive, irreflexive and to contain replica order.
    For finite executions this is equivalent (topological sort). For RGA we also show `vis ⊆ <`, so
    the execution order is an `H`. For the lower bound, dropping `H` weakens the hypothesis.
12. *Causal atomic broadcast, Def. 3(3).* Read as: if `R` receives `m` before `m′` and `R′`
    receives `m′`, then `R′` received `m` before `m′`. This is the strongest sensible reading, and
    it appears only in the conclusion of Theorem 9.
13. *Push-based (Def. 13)* is parametrized by the class of executions `Adm`. `theorem9` assumes it
    only for executions with causal *atomic* broadcast that satisfy the user assumptions. This is
    weaker than the paper's hypothesis, and the paper's form `theorem9_causal` follows. The third
    condition directly states `S (hist α) (visHB α)`.
14. *User assumptions (`UserOK`).* Inserted elements are unique, and `del(a)` requires `a` in the
    response of the *immediately preceding* `do` event of the same replica.
15. *Elements.* The universe `U` is infinite. The construction needs `2d+5` distinct elements,
    obtained from `Infinite.natEmbedding`.
16. *Positions in `α_w`.* The paper gives positions relatively ("just after `]ᵢ₋₁`"). We compute
    the integer positions from the intended lists `A_j [ⱼ ]ⱼ B_j` and prove that the responses are
    these lists. `γ_w^i` is the paper's `β_w^i` followed by `R₃`'s part, in the paper's order.
17. *Metadata overhead.* `|q|` is the length of `enc q` for an arbitrary injective
    `enc : Q → List Bool`. Theorem 9 concludes `⌊(D−2)/2⌋ ≤ |enc q|` with content `[u]`, where `u`
    is fixed before `D`. Theorem 8 is stated with `metadataOverhead σ = |enc q| / sz(content σ)` for
    a state `σ = (q, m)`, an arbitrary size measure `sz`, positive on non-empty lists, and constant `c = 1/(5·sz [u])`.
18. *Decoding.* We do not construct the decoder of Fig. 4(b). We prove that `w ↦ σ_w` is injective:
    take the first differing bit `i` and run the `Recover` experiment as part of `γ_w^i`. By the
    congruence of replay (`Protocol.foldl_step_congr`), equal states and equal `m₁ … mᵢ` give equal
    answers. This is exactly what the decoder relies on.
19. *RGA details.*
    - TI trees and the state sets `N`, `T` are lists, `N` duplicate-free; a receive uses
      `List.union`. Timestamps are `ℕ ×ₗ ℕ`, with replica ids `0 … n−1`. "1 + the largest
      timestamp in N" is read as `(1 + max x, i)`.
    - The DFS only descends to children with a larger timestamp. This guard ensures termination on
      arbitrary lists and is vacuous for TI trees.
    - The buffer `(A, K) = (∅, ∅)` is represented by `none`.
20. *Not formalized.* Theorem 2 (`O(D lg k)` overhead of RGA). Section 6.1 (Proposition 14,
    Corollary 15). Section 7 (Theorem 16, Corollary 17, Lemmas 20–21, Propositions 18–19).
