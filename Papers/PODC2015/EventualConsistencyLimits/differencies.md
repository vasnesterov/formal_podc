# Differences between the formalization and [AEM15]

Paper: Attiya, Ellen, Morrison, *Limitations of Highly-Available Eventually-Consistent Data
Stores*, PODC 2015 (authors' copy). Lemma 5, Lemma 7 and parts of Theorem 12 are proved only in
the full version (not available); all their proofs here are ours.

## Model

1. **Replicas** (`Store`): one partial transition function per replica, `step i σ e : Option St`,
   with a common state type. The paper's assumption that `send` is deterministic (the message is a
   function of the state) is not needed and not assumed.
2. **Executions** (`IsExec`, Def. 1) are built event by event; a receipt of `m` at `i` needs an
   earlier `send(m)` at some `j ≠ i`. Infinite executions are sequences all of whose prefixes are
   executions (`IsInfExec`).
3. **Happens-before** (Def. 2) and Proposition 1 are not formalized: we never need them. The
   constructions build the needed sub-executions explicitly.
4. **Implicit assumptions made explicit.** `Available`: in every state, every operation on every
   object is enabled with some response ("replicas handle client operations immediately").
   `RecvEnabled`: every receipt is enabled in every state ("messages may be delivered at any
   time"). The paper uses both (e.g. "Let `ê` be the transition in which `op(e)` is invoked",
   "we deliver it to `R` by appending a `receive`").
5. **Abstract executions** are indexed by `ℕ` with a domain predicate (`AE`). `ord` is the order
   `H`: a strict total order on the domain in which every event has finitely many predecessors
   (`H` is a sequence). Compliance (Def. 9) is formalized as `AE.On`: the abstract execution lives
   on the do-events of the execution and agrees with its per-replica order. This is Def. 9 up to
   renaming events. For Theorem 6, `Complies`/`AE.Equiv` give the renaming version.
6. **MVR specification** (Fig. 1b): `AE.mvr`; returned values are the values of the writes of the
   context that are not visible to another write of the context. Values need not be distinct in
   general; the lemmas that identify writes with values assume distinct values, as the paper does
   ("we assume that each write event writes a different value").
7. **Eventual consistency of a store** (Def. 14, see 13 below): `EventuallyConsistent P` = every
   infinite sufficiently connected execution complies with a *correct, eventually consistent*
   abstract execution satisfying `P`. Causal consistency of a store (`CausallyConsistent`,
   Defs. 10–12): every finite execution complies with a causally consistent abstract execution.
   Theorem 12 assumes both (`P` arbitrary), as the paper does ("causally consistent and eventually
   consistent").
8. **Consistency models** (Section 3.2) and satisfaction (Def. 11) appear only in
   `Theorem6Statement`, restricted to finite executions and finite abstract executions. In the
   paper a consistency model may contain infinite abstract executions. For those, "strictly
   stronger" can come from excluding infinite executions that are not eventually consistent (e.g.
   a model like `OCC ∩ {finite or eventually consistent}`), which has nothing to do with the
   construction of the proof (which builds finite executions). So the finite reading is the one the
   proof addresses.

## Statements

9. **Lemma 3** (`Store.lemma3`): as stated, for any responses (not only sets) of the two reads.
   Op-driven messages are not needed.
10. **Corollary 4** (`corollary4`): as stated. The extension sends every pending message and then
    delivers every message to every other replica. Needs `SendClears`, `OpDriven`, `RecvEnabled`.
11. **Lemma 5** (`lemma5`). *Changed hypothesis (🔧).* "`e →hb w ⇒ e →rcv w` for any do event `e`"
    is unsatisfiable for earlier events of `R` (no replica receives its own messages). We assume
    instead: no replica has a message pending at the end of `α` (before `w`), and `R` has received
    every message sent in `α` by another replica. This is what the uses need (Theorem 6's
    construction delivers exactly these messages; Theorem 12's writers have sent everything). We
    also assume the written values distinct and `w`'s value fresh (paper-wide assumption).
    *Added hypothesis `n ≥ 2` (✏️ slip, degenerate).* With one replica the lemma is false
    (`lemma5_false_one_replica`): a store that never sends satisfies all hypotheses.
12. **Lemma 7** (`lemma7`): as stated (writes of the operation context of `r`), with "`β` contains
    `r_w, w`" formalized by a map `φ` into the other abstract execution `Â` preserving replica,
    operation and response, keeping `r_w` before `w`. `Â` has pairwise distinct written values. We
    only need from "revealing" that `w`'s visible events are visible to `r_w` and that `r_w`
    precedes `w` at the same replica.
13. **Definition 14 literal** (`Store.literalEC_false`): with "every abstract execution that `α`
    complies with", even restricted to correct and causally consistent ones, no store with two
    replicas, available invisible reads, op-driven messages and correct finite executions is
    eventually consistent (✏️ slip). It is reported because it makes
    Theorems 6 and 12 vacuous as written. We use "some" (item 7), which is what the proofs use
    ("β∞ complies with some causally consistent MVR abstract execution Â such that …").
14. **Definition 18** (`AE.OCC`): condition 1's `w_{i−1}` is read as `w_{1−i}` (typo). We add
    `w₀ ≠ w₁`: for `w₀ = w₁` conditions 1 and 3 contradict each other, so a read returning a single
    write would violate OCC. "`rval(r) ⊇ {w₀, w₁}`" is formalized on writes: `w₀, w₁` are maximal
    writes of the context of `r`. Condition 4 quantifies over writes `ŵ` (the formula says "any
    `ŵ`", the prose "no write").
15. **Theorem 6** (`Theorem6Statement`): stated (finite abstract executions, equivalence-closed
    models, with the model assumptions of item 4 and `SendClears`), **not proved**.
    * *Gap 1 (❌ w.l.o.g. revealing).* The proof needs the revealing extension of `A` to be OCC
      (Lemma 11 is applied to every read, including the added `r_w`). The literal extension of
      Section 5.2.1 is not OCC in general (`Gap.revealing_extension_not_OCC`: writes `a`, `b`
      concurrent, both visible to `c`; `r_c` returns `{a, b}` with no witnesses). A different
      revealing abstract execution with the same per-replica histories might be OCC (in the example,
      order `a` before `b`). We do not know whether one always exists.
    * *Gap 2 (❌ Lemma 7 across objects).* The proof of Lemma 11 derives `w'_i →vis^ w₀` "from
      `w'_i →vis w₀` and Lemma 7", with `w'_i` a write to another object than `w₀`. Lemma 7 does not
      cover this (its `H'` contains only writes to `obj(r)`). The claim "`w'_i ∈ ctxt(A, e)`" is
      false by Definition 7. Visibility between writes of different objects is not revealed by the
      reads `r_w` (same object), and eventual consistency only forces same-object visibility.
      Example: `R₁` reads `x` (∅) and writes `x`; `R₂` reads `y` (∅) and writes `y`, with
      `w_x →vis r_y, w_y`. This is revealing and causally consistent, and so is the abstract
      execution with the same responses and only per-replica visibility, in which `w_x ↛vis w_y`.
      So the step needs a new argument.
    * The other steps of Lemmas 10 and 11 are sound modulo Propositions 2, 8, 9, which we did not
      formalize. Our proof of Lemma 5 shows how the paper's "quiescent completion" arguments go
      through.
    * *Status.* No statement is refuted. Gap 1 is a wrong implicit claim inside the proof ("the
      revealing extension is still OCC"); gap 2 applies Lemma 7 outside its statement (Lemma 7
      itself is true, `lemma7`; the cross-object form the proof needs is an unstated claim inside a
      proof). Lemma 11 is only unestablished: we have no store and OCC execution where the
      construction of Section 5.2.2 gives `ê ≠ e`. So Theorem 6 is unestablished, not refuted.
    * The formal statement adds the paper's standing assumption (Section 4) that written values are
      pairwise distinct in `A`; without it a store might "hide" the concurrency of two writes of
      the same value, which OCC does not account for.
16. **Theorem 12** (`theorem12`).
    * ✏️ Bound `⌊n' lg k⌋` (`Nat.log 2 (k ^ n')`) instead of `n' lg k`. The counting argument gives
      only the floor (bit strings of different lengths). Messages are bit strings via an injective
      `enc : M → List Bool`.
    * Hypotheses `n ≥ 3`, `s ≥ 2` (so that `n' ≥ 1`) and `k ≥ 1`, instead of
      "`k ≥ min{n − 2, s − 1}`" (irrelevant to the proof; for `n' ≤ 0` the claim is degenerate).
      Written values: `V` infinite (to have `n' k + 1` distinct values).
    * 🛠️ *New proof.* (a) The writers' messages `m^i_j` and `m_g` exist by Lemma 5, applied to
      sub-executions where the writer (resp. `R_{n−1}`) has heard everything. (b) "`w^i_j ∈ rval(r^i_j)`"
      (full version) is proved by `Cx.a_read`: `R_{n−1}`'s state after receiving `m^i_{g(i)}` is
      final in the sub-execution where the writers stop after the delivered rounds, so by eventual
      consistency its read returns exactly `{⟨g(i), i⟩}` (`Store.final_read`). (c) Decoding: the
      paper's justification ("`R_n` cannot return `w_y` … since `R_n` does not know this value") is
      wrong, because `m_g` may carry `R_i`'s writes. We replace the sequential decoder by a
      direct injectivity argument (`Cx.decode`, `Cx.key`, `Cx.mg_injective`), see `README.md`.
      `R_n` receives the first `g(p)` messages of every writer (not all `k` of the other writers'
      messages) and `m_g`.
    * Indices: rounds `j = 0, …, k − 1` (the paper: `1, …, k`), `R_{n−1} = a`, `R_n = b`.
17. **Abstract (and Section 6 intro):** "an `Ω(min{n, s} k)`-bit message" for every `k`. Section 1
    and Theorem 12 have `lg k`. Both readings follow from Theorem 12 (apply it with `2^k`), since the
    execution length is unbounded. Not an error.

## Not formalized

18. Propositions 1, 2, 8, 9; Lemmas 10, 11 (and hence Theorem 6); Section 5.3 (CAC theorem
    comparison; the example store without invisible reads); the read/write register remarks at
    the end of Section 6; Section 7's full-version extensions.
