# Fast Byzantine Total Order Broadcast — PODC 2026

Matteo Monti, Martina Camaioni, Pierre-Louis Roman. *Fast Byzantine Total Order Broadcast.* PODC 2026.
DOI [10.1145/3796701.3815946](https://doi.org/10.1145/3796701.3815946). Formalized version: arXiv
[2412.14061](https://arxiv.org/abs/2412.14061) v2 (full version with appendices); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The safety results hold in the paper's model (`n = 5f + 1`).
Blink's Integrity, Agreement and Representative Validity (Theorems 2–4) hold with the underlying Binary
Consensus as a black box. For Flutter, No Duplication and Integrity (Theorems 6–7) hold, and so does the safety
core of Agreement and Total Order (Lemmas 15–20, Theorem 8): delivery sequences of correct servers are always
prefixes of one another. The abstract and introduction say both protocols work with "at least `5f + 1`
servers". With the paper's fixed thresholds (`4f + 1`, `2f + 1`) they do not: for `n = 5f + 2` both Blink's
Agreement and Flutter's Total Order fail, and we give Lean counterexamples. With thresholds `n − f` they work for
every `n ≥ 5f + 1`. Lemmas 5 and 6 are imprecisely stated (finite sequences, values in `X`); their intended
versions are true.

## Mistakes in the paper

* **"At least `5f + 1` servers" (abstract, introduction) does not hold for the algorithms as written.** §2.1
  fixes `n = 5f + 1`, and every proof uses it. But the thresholds are hard-coded as `4f + 1` and `2f + 1`, so
  they stop working when there are more servers.
  * *Blink.* Take `f = 1`, `n = 7`, with server 6 Byzantine. Servers 0–3 propose `True` and servers 4–5
    propose `False`. Server 0 receives `True` from 0–3 and from 6. That is `4f + 1 = 5` matching suggestions,
    so it fast-decides `True`. Server 4 receives `False` from 4, 5, 6 and `True` from 0, 1. That is 5
    suggestions, 3 of them `False`, so it proposes `False` to `dep`. Then `dep` may decide `False`, because a
    correct server proposed it, and server 4 decides `False`. The run can be completed so that `dep` decides
    everywhere and terminates. (`blink_agreement_fails_5f2`)
  * *Flutter (using only the specification of Representative Binary Consensus).* With `n = 5f + 2`, the `f + 1` correct
    servers backing a message need not meet the `4f + 1` servers whose `Time` messages raise a lock time.
    So Lemma 16 fails. Concretely, take `f = 1`, `n = 7`. Servers 0 and 1 receive `y` (bet 10) in time.
    Servers 2–5 receive `z` (bet 20) in time and announce time 20. Server 6 (Byzantine) also announces 20.
    Server 2 never hears of `y`. Both `con[y]` and `con[z]` decide `True`, each backed by at least 2
    correct proposals. Server 0 delivers `y` first, while server 2 delivers `z` first.
    (`flutter_totalOrder_fails_5f2`, `flutter_not_prefix_5f2`)
  * How serious: the paper's own model (`n = 5f + 1`) is fine. The "at least" in the abstract is a claim about
    the stated algorithms that is false for `n > 5f + 1`. The fix is local: use `n − f` instead of `4f + 1`.
    We prove Blink safe for every `n ≥ 5f + 1` with thresholds `n − f`/`2f + 1`/`n − f` (`blink_safe_general`).
    We prove Flutter's safety argument for every `n > f` with lock quorum `n − f`
    (`theorem8_totalOrder_general`). We classify this as a statement imprecision rather than a false headline:
    the intended reading "tolerates `f < n/5`" is achievable by an evident local change. See `differencies.md`
    for this borderline call.
* **Lemmas 5 and 6 are imprecisely stated** (an imprecision, not an error). Lemma 5 does not say whether the
  sequence may be finite; it must be, for finite `X` (no strictly increasing `ℕ`-indexed sequence lives in a
  finite nonempty set, `lemma5_literal_false`). The proof builds a bijection with `{n ≤ |X|}`, so a finite *or*
  infinite sequence is meant. We prove that version: `lemma5_infinite` gives a strictly increasing `z : ℕ → α`
  with range `X`, and `lemma5_finite` gives a sorted list. Lemma 6 does not say that `z` and `z'` take values in
  `X`; if they may leave `X` it fails (`X = {0}`, `z n = n`, `z' n = 2n`, `lemma6_literal_false`). The proof
  uses `z_n, z'_n ∈ X`, and at its use (Corollary 3) the sequences stay in `X` by Lemma 18. With
  `range z = range z' = X` the lemma holds (`lemma6_infinite`, `lemma6_finite`).
* **Typos and slips in proofs (statements unaffected).** Each is listed with the intended reading.
  * Lemma 4 says "previously set `decided = False`" twice; it means `True`.
  * The proof of Theorem 2 writes `v̄` where it means `v`, in "`ρ` satisfies `|{σ : suggestions[σ] = v̄}| ≥ 2f+1`".
  * Lemma 16 defines `Φ` with `remote_times[σ] > b`; it should be `≥ b`. It also says "before `t*`"; it means
    `t⁺`.
  * Lemma 17 writes `last_order` and Lemma 19 writes `last_delivered`; both mean `last_processed`.
  * Lemma 22 cites line 18; it means line 48.
  * Lemma 23 writes `order(m, _)`; it means `submit(m, _)`.
  * In Lemma 5, `φ` maps onto `1..|X|`, not `{n ≤ |X|}`.
  * The proofs of Theorems 2 and 4 invoke Lemma 1, i.e. the Termination of `dep`, for a safety property. This is
    unnecessary; our proofs use only the Validity and Agreement of `dep`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Message passing with authenticated links, **asynchronous interleaving semantics**, static Byzantine faults.
  Blink has servers `P` and a Byzantine set `F` with `|F| ≤ f`. Flutter has servers `P`, clients `C`,
  Byzantine servers `F` and Byzantine clients `G`, with no bound on `|G|`. Byzantine nodes have no state: they
  may send any message at any time. The scheduler is adversarial: any enabled action of any correct node may
  happen next.
* Only safety is formalized, so timing (`Δ`, `Ψ`, partial synchrony) plays no role. A safety violation in a
  finite asynchronous prefix is a violation in the paper's model too: choose `Δ`, `Ψ` larger than all delays and
  clock offsets of the prefix. Local clocks are non-decreasing and advanced by `tick` actions; Lemma 15 relies
  on this. Flutter's links are FIFO, as the paper assumes (Lemma 16).
* Deterministic, no randomness. `beat()` may run at any time, a superset of the paper's schedule, so safety
  results transfer. The counterexample only uses beats at their scheduled times.
* **Black boxes.** Blink's Binary Consensus `dep` and Flutter's instances `con[x]` deliver decisions through
  unconstrained environment actions. Their specifications (Validity/Agreement, resp. Representative Validity/
  Agreement) are hypotheses about whole runs. A value may even be decided before it is proposed, which is the
  weakest reading of a black-box spec. Termination is not used.
* Thresholds are parameters, with hypotheses only where needed. For Blink: `M, Q ≥ 2f + 1`, `n + |F| < Q + M`,
  `M ≤ Q`. For Flutter: lock quorum `q ≥ 1` and `n < (f + 1) + q`. The paper's values satisfy these for
  `n = 5f + 1`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Observation 1, Lemmas 2–4 (Blink) | `observation1`, `lemma2`, `lemma3`, `lemma4` | `Blink.lean` |
| Theorem 2 (Representative Validity) | `theorem2` | `Blink.lean` |
| Theorem 3 (Integrity) | `theorem3` | `Blink.lean` |
| Theorem 4 (Agreement) | `theorem4` | `Blink.lean` |
| Theorems 2–4, paper thresholds, `n ≤ 5f + 1` | `blink_safe` | `Blink.lean` |
| Theorems 2–4, thresholds `n − f`, any `n ≥ 5f + 1` | `blink_safe_general` | `Blink.lean` |
| "at least `5f + 1`" for Blink: **fails** at `n = 5f + 2` | `blink_agreement_fails_5f2` | `BlinkCounterexample.lean` |
| Lemma 5 (finite / infinite) | `lemma5_finite`, `lemma5_infinite`; literal: `lemma5_literal_false` | `Enumeration.lean` |
| Lemma 6 | `lemma6_finite`, `lemma6_infinite`; literal: `lemma6_literal_false` | `Enumeration.lean` |
| Theorem 6 (No Duplication) | `Flutter.theorem6` | `FlutterSafety.lean` |
| Lemmas 7–8, Theorem 7 (Integrity) | `Flutter.CInv`, `Flutter.theorem7` | `FlutterNet.lean`, `FlutterSafety.lean` |
| Lemma 15 | `Flutter.LInv.lemma15` | `FlutterLocal.lean` |
| Lemma 16 (safety form) | `Flutter.lemma16` | `FlutterSafety.lean` |
| Lemmas 17–20 (safety form), Observations 2–8 | `Flutter.orders_gapFree`, `Flutter.LInv` | `FlutterSafety.lean`, `FlutterLocal.lean` |
| Corollary 4 (safety form) | `Flutter.corollary4` | `FlutterSafety.lean` |
| Theorem 8, safety part (prefix consistency) | `Flutter.theorem8_totalOrder`, `_paper`, `_general` | `FlutterSafety.lean` |
| "at least `5f + 1`" for Flutter: **fails** at `n = 5f + 2` | `Flutter.flutter_totalOrder_fails_5f2`, `Flutter.flutter_not_prefix_5f2` | `FlutterCounterexample.lean` |

Lean names are in `Podc.FastByzantineTOB.Blink`, `Podc.FastByzantineTOB` and `Podc.FastByzantineTOB.Flutter`.

**Not formalized.**
* Liveness: Blink's Termination (Lemma 1, Theorem 1), Flutter's Validity (§B.3.3), and the eventual parts of
  Lemmas 10–14 and 21, Corollaries 1–3 and Theorem 8 ("eventually deliver the same messages").
* Latency: Theorem 5 (fast path in one message delay), good-case latency §B.4, quasi-optimality §B.5.
* The comparison with Bosco (§A.3). It does not conflict with the formalized two-step bound `n ≥ 3f + 2t − 1`
  of `Papers/PODC2021/FastByzantineConsensus`. That bound concerns leader-based two-step decisions; Blink's fast
  path is a unanimity-conditioned one-message-delay decision.

**Remark.** With an RBC black box, Flutter's own safety argument needs only `n < (f + 1) + q`, so it works with
quorum `q = n − f` for every `n > f` (`theorem8_totalOrder_general`). The `5f + 1` bound comes only from Blink.
This bears on the paper's open question (2) in §6.

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
Non-vacuity: `Flutter.example_delivers` is a run with one server and one client in which the black box meets its
spec, the hypotheses of `theorem8_totalOrder` hold, and the server delivers the message. The Blink
counterexample run also exercises the fast and slow paths. Concrete runs are checked by `decide` (lists of
actions, `ValidList`/`Run.ofList`). The model is paper-local; no CSLib model was reused, because the CSLib
Byzantine models (`PartialSync`, `LockStep`) have no black-box sub-protocols or client/server split. Generic
helpers used from Mathlib: `Finset.inter_nonempty_of_card_lt_card_add_card`, `StrictMono.range_inj_of_wellFoundedLT`,
`List.SortedLT.eq_of_mem_iff`, `Nat.Subtype.orderIsoOfNat`.
