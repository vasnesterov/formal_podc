# Limitations of Highly-Available Eventually-Consistent Data Stores — PODC 2015

Hagit Attiya, Faith Ellen, Adam Morrison. *Limitations of Highly-Available Eventually-Consistent
Data Stores.* PODC 2015. DOI [10.1145/2767386.2767419](https://doi.org/10.1145/2767386.2767419).
Formalized version: the authors' copy of the PODC paper (10 pages). Lemmas 5 and 7 and parts of
Theorem 12 are proved there only "in the full version" (IEEE TPDS 2017, not open access); we give
our own proofs.

**Verdict: ⚠️ Minor statement issues.** No checked statement is refuted except Lemma 5 in the
degenerate one-replica case. The headline Theorem 6 (no eventually consistent store with invisible
reads and op-driven messages satisfies a consistency model strictly stronger than OCC) is,
however, **not established**: its proof assumes without loss of generality that the abstract
execution is *revealing*, which fails, and it applies Lemma 7 to pairs of writes that Lemma 7 does
not cover. Neither gap refutes Theorem 6 or a numbered lemma, so by the project's verdict rules
(R1, R5) they do not lower the label below ⚠️; Theorem 6 remains open here. The second headline,
Theorem 12 (messages of `⌊n' lg k⌋` bits), holds; we prove it with a repaired decoding argument.
Lemmas 3, 5 and 7 and Corollary 4 hold (Lemma 5 needs two replicas). Definition 14 (eventual
consistency of a store), read literally, is satisfied by no store; we use its evident intent.

## Mistakes in the paper

* **Theorem 6 is not established (two gaps in its proof).**
  1. *The "w.l.o.g. revealing" step.* Section 5.2.1 assumes the OCC abstract execution `A` to be
     realized is revealing: before each write `w` there is a read `r_w` of the same object with
     the same visibility as `w`. It justifies this by "adding the appropriate `r_w` operations and
     vis edges to `A`". But the inductive argument (Lemma 11) is then applied to every read of the
     extended execution, including the added `r_w`, and needs OCC for them. The extension need not
     be OCC. Take writes `a` at `R₀` and `b` at `R₁` to one MVR, concurrent, both visible to a
     write `c` at `R₂`, and no reads. This is OCC (vacuously). The added read `r_c` returns
     `{a, b}`, and there is no write to another object that could serve as an OCC witness. So the
     revealing extension is not OCC. (`Gap.revealing_extension_not_OCC`) This particular `A` is
     trivially realizable (no reads), and a cleverer extension (ordering `a` before `b`) is OCC.
     We do not know whether a suitable revealing OCC extension always exists.
  2. *Lemma 7 is used outside its scope.* Lemma 7 transfers visibility between writes of the
     operation context of a read, i.e. writes to the *same* object. The proof of Lemma 11 uses it
     for `w'_i →vis w_0`, where `w'_i` is an OCC witness, a write to *another* object
     ("`w'_i ∈ ctxt(A, e)` since `w'_i →vis w_0 →vis e`" is wrong: contexts contain only writes to
     `obj(e)`). For writes to different objects the conclusion of Lemma 7 fails in general:
     visibility between them is constrained by nothing that the reads `r_w` reveal, and eventual
     consistency only concerns writes to the same object. A repair would need revealing reads of
     *every* object before each write, which makes gap 1 worse.
  Since neither gap could be closed, we state Theorem 6 (`Theorem6Statement`, for finite OCC
  abstract executions with distinct written values) without proof. Theorem 6 and Lemma 11 are
  thus *unestablished*, not refuted: we have no store and OCC execution for which the construction
  of Section 5.2.2 actually fails.
* **Definition 14, read literally, is unsatisfiable.** It requires that *every* abstract execution
  that an infinite execution complies with be eventually consistent. Compliance (Definition 9)
  fixes only the per-replica operation sequences, so the abstract execution whose visibility is
  just the per-replica order always complies. In an infinite execution where two replicas read the
  same MVR forever and nothing is written, this abstract execution is correct and causally
  consistent but not eventually consistent. So no store with two replicas satisfies Definition 14,
  and Theorems 6 and 12 would hold vacuously. The proofs use "*some* correct abstract execution that
  the execution complies with is eventually consistent", which we adopt.
  (`Store.literalEC_false`)
* **Lemma 5 needs two replicas, and its hypothesis is mis-stated.** With one replica nothing ever
  has to be sent: a single-replica store that never sends satisfies all assumptions, and after a
  write no message is pending (`lemma5_false_one_replica`; degenerate case). The hypothesis
  "`e →hb w ⇒ e →rcv w` for any do event `e`" cannot hold for earlier events of `R` itself, since a
  replica does not receive its own messages. We read it as: nobody has a message pending before `w`,
  and `R` has received every message sent by another replica. The lemma is proved only in the full
  version; we give a proof. Insert an invisible read `r` before `w` and complete the execution
  quiescently. If `R` sent nothing after `w`, late reads at another replica would never see `w`,
  but by Lemma 3 they return what `r` returned. A late read at `R` sees `w`, so `w` is overwritten
  by some `w₂` returned by `r`, while `w₂` is visible to `r` and hence to `w` (Definition 4(2)).
  This is a visibility cycle. (`lemma5`)
* **Theorem 12: the decoding argument is not sound as written (statement true).** The sketch says
  that `R_n` "cannot return `w_y`" before it has received `R_i`'s `g(i)`-th message "since `R_n`
  does not know this value". But `m_g` itself may carry `R_i`'s writes (e.g. in a store that
  piggybacks everything it knows). The paper also never shows that `R_n` exposes `w_y` once it has
  the `g(i)`-th message, and defers both facts to the full version. We decode differently. `R_n`
  receives only the first `g(p)` messages of every writer, and `m_g`. Its state is then *final*:
  it has heard everything sent in the sub-execution where every writer stops after `g(p)` rounds.
  So, by eventual consistency, its reads return exactly `{1}` from `y` and `⟨g(i), i⟩` from `x_i`.
  If `m_g = m_{g'}` with `g(i) < g'(i)`, the same state of `R_n` arises in the `g'` execution. There
  `R_{n-1}` read `⟨g'(i), i⟩` before writing `y`, so causal consistency makes `⟨g'(i), i⟩`, which
  overwrites `⟨g(i), i⟩`, visible to `R_n`'s read of `x_i`. (`theorem12`, `Cx.key`, `Cx.decode`)
* **Minor imprecisions.**
  * Theorem 12 claims `n' lg k` bits. The counting argument gives `⌊n' lg k⌋` (e.g. three distinct
    messages may have lengths 0, 1, 1). Its hypothesis "`k ≥ min{n−2, s−1}`" plays no role; we
    prove the bound for all `k ≥ 1`, and need `n ≥ 3` and `s ≥ 2` (otherwise `n' ≤ 0`).
  * Definition 18, condition 1 writes `w'_i →vis w_{i-1}`; the prose and the proof use `w_{1-i}`.
    Definition 18 also implicitly needs `w_0 ≠ w_1`.
  * High availability (every operation can be invoked in every state) and that messages can be
    received at any time are used but never stated as properties of the transition function.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* `n` replicas (finite type `ι`), each a partial, possibly nondeterministic state machine
  (`Store`, Section 2); objects are multi-value registers; written values are arbitrary.
  Events: `do(o, op, v)`, `send(m)` (broadcast), `recv(m)`.
* Asynchronous message passing, no failures. Messages may be lost, delayed, reordered and
  duplicated; an execution only requires that every receipt follows a send by another replica
  (`IsExec`, Definition 1). Infinite executions are considered only when sufficiently connected
  (`SuffConnected`, Definition 3).
* Assumptions on stores, as in the paper: a send leaves nothing pending (`SendClears`),
  op-driven messages (`OpDriven`, Def. 15), invisible reads (`InvisibleReads`, Def. 16); and,
  made explicit, high availability (`Available`) and input-enabled receipts (`RecvEnabled`).
* Abstract executions (`AE`, Def. 4) carry the total order `H` and visibility; MVR specification,
  correctness, causal and eventual consistency are Defs. 7, 8, 12, 13. Compliance (Def. 9) is
  "an abstract execution on the execution's own do-events with the same per-replica order"
  (`AE.On`), which is the same up to renaming events.
* Store-level consistency: `CausallyConsistent` (every finite execution complies with a causally
  consistent abstract execution) and `EventuallyConsistent P` (every infinite sufficiently
  connected execution complies with a correct, eventually consistent abstract execution, in the
  model `P`) — the latter is Definition 14 with "some" for "every" (see above).
* No randomness; all universal statements quantify over every store satisfying the hypotheses
  and every execution (adversarial scheduling and message delivery).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 3 | `Store.lemma3` | `Late.lean` |
| Corollary 4 | `corollary4` | `Cor4.lean` |
| Lemma 5 (`n ≥ 2`, explicit hypothesis) | `lemma5` | `Lemma5.lean` |
| Lemma 5 false for one replica | `lemma5_false_one_replica` | `Lemma5N1.lean` |
| Lemma 7 | `lemma7` | `Theorem6.lean` |
| Theorem 6 (**statement only, not proved**) | `Theorem6Statement` | `Theorem6.lean` |
| "W.l.o.g. revealing" fails | `Gap.revealing_extension_not_OCC` | `RevealingGap.lean` |
| Theorem 12 | `theorem12` | `Theorem12.lean` |
| Definition 14 literally unsatisfiable | `Store.literalEC_false` | `Def14.lean` |

Supporting results: `Store.exists_late_ae` (late reads see all writes), `Store.final_read` (a
replica that has heard everything returns the last write), the injectivity `Cx.mg_injective` of
`g ↦ m_g` and the counting lemma `exists_le_length`.

**Not formalized.** The proof of Theorem 6: Propositions 1, 2, 8, 9 and Lemmas 10, 11 (the
construction of Section 5.2.2), Section 5.3 (comparison with the CAC theorem and the example store without invisible
reads).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The single-replica store of `Lemma5N1.lean` satisfies all hypotheses of Lemma 5
except `n ≥ 2` (non-vacuity of those hypotheses for `n = 1`). We did not construct a store
satisfying the hypotheses of Theorem 12 (a causally consistent store with `n ≥ 3`).
