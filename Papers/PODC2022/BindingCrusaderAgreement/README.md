# Binding Crusader Agreement — PODC 2022

Ittai Abraham, Naama Ben-David, Sravya Yandamuri. *Efficient and Adaptively Secure Asynchronous Binary
Agreement via Binding Crusader Agreement.* PODC 2022. DOI
[10.1145/3519270.3538426](https://doi.org/10.1145/3519270.3538426). Formalized version: the 11-page
proceedings version (no arXiv version; the proofs it defers to the "full version" are supplied here).

**Verdict: ⚠️ Minor statement issues.** All four (G)BCA protocols are correct as intended: Algorithm 3
(crash BCA, `n ≥ 2t + 1`), Algorithm 4 (Byzantine BCA, `n ≥ 3t + 1`, Lemmas 4.4–4.9), Algorithm 5
(crash GBCA) and Algorithm 6 (Byzantine GBCA). They satisfy agreement, validity, binding and termination
against an adaptive adversary, with at most 2/4/3/6 broadcasts per party. The deterministic core of the
framework (Theorems 3.1, 3.3–3.5: agreement, validity, the binding step of termination) holds. The only
statement-level slip is in the pseudocode of Algorithm 5: read literally, it can output "`⊥` grade 2",
which is not a GBCA output. The prose gives the intended version, which we prove. Two proof steps of
Section 4 need small repairs, and Theorems 4.1, 5.1 and 5.3 have no proofs in this version.

## Mistakes in the paper

No theorem or lemma is false. One pseudocode slip, proof repairs and remarks:

* **Algorithm 5, line 9, can output "`⊥` grade 2".** The line says "if all of the messages contain the same
  value `v` then decide `v, 2`". Line 10 counts `⊥` as "a value other than `v`", so line 9 also fires when
  all `n − t` echo2's are `⊥`. Example: `n = 3`, `t = 1`, inputs `0, 1, 0`, no crash, and a schedule in
  which every party first receives one `⟨val, 0⟩` and one `⟨val, 1⟩`. Then everybody sends `⟨echo, ⊥⟩` and then `⟨echo2, ⊥⟩`. Line 9 then outputs `⊥` with
  grade 2. That is not one of the five buckets of Definition 3.2, so Theorem 5.1 fails for the literal
  code. Line 11 becomes dead code, and Algorithm 2, line 7 ("if grade = 2 then commit val") would commit
  `⊥`. The prose above the algorithm says that a party with all `⊥` decides `⊥`. We prove Theorem 5.1 for
  this intended version (all `⊥` gives `⊥` grade 0). A typo with evident intent (rule R3). (`Alg5.decideG`,
  `Alg5.theorem_5_1`)
* **Lemma 4.5 (validity) cites the wrong guard.** The proof says that to decide `1 − v` a non-faulty party
  "must have `1 − v` in its approvedVals set (line 15)". Line 15 only asks for `n − t` messages
  `⟨echo3, 1 − v⟩`. The step is repaired by one more link of the chain. An uncorrupted sender of
  `⟨echo3, 1 − v⟩` saw `n − t` messages `⟨echo2, 1 − v⟩`. One of their senders is uncorrupted and has `1 − v`
  approved, which needs an uncorrupted party with input `1 − v`. (`Alg4.validity`)
* **Lemma 4.9 (binding) leaves the adaptive quantifier order implicit.** The proof argues with "the `t + 1`
  echo3 messages from non-faulty parties". Under adaptive corruption, who is non-faulty depends on the
  extension, while `b` must be fixed at the first decision. We fix `b` from the prefix. If some party has
  broadcast `⟨echo3, u⟩` with `u ≠ ⊥`, then `b = u`, by Lemma 4.8 applied inside the extension. Otherwise
  the decider's quorum contains at least `n − t − |bad(τ)|` genuine `⊥`'s. A later `⟨echo3, w⟩` quorum
  would then need `n − t` parties among at most `2t` candidates. The same repair works for Algorithm 6
  through its first `⟨echo4, ⊥⟩`. (`Alg4.binding`, `Alg6.graded_binding`)
* **Theorems 4.1, 5.1, 5.3 (Algorithms 3, 5, 6)** are stated with proofs deferred to the full version. We
  prove them. For Algorithm 6, binding must be argued at the `echo4` level. A grade-≥1 decision on `v` needs
  a genuine `⟨echo4, v⟩`, which is why line 25 checks `t + 1` echo4's. (`Alg3.theorem_4_1`,
  `Alg5.theorem_5_1`, `Alg6.theorem_5_3`)
* **"Communication rounds" = broadcasts, not asynchronous time.** "Terminates within 4 communication
  rounds" (Lemma 4.7) is proved by counting messages, and that is what we verify (≤ 4 broadcasts per
  party). In the normalized-delay measure, Algorithm 4 can take almost 5 time units. With `n = 7`, `t = 2`,
  the Byzantine parties make one correct party approve the minority value first. Then nobody gets `n − t`
  equal `echo2`'s, and everybody waits until both values are approved at time `≈ 4`. We checked this by an
  event simulation, not in Lean ([`scripts/latency.py`](scripts/latency.py)). The round comparisons with
  other papers in Tables 1–2 are fair only if those papers count the same way.
* **Typo.** Algorithm 6, line 11 reads "if 1 then"; it means "if (1) then", as in Algorithm 4, line 11.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing among `n` parties, with authenticated reliable channels and arbitrary
  finite delays. It is an interleaving system: a broadcast is one event, and each delivery is a separate
  event chosen by the adversary.
* The adversary is **adaptive**. It corrupts up to `t` parties at any time. A corrupted party stops
  following the protocol. In the Byzantine mode it can make anybody receive anything from it (equivocation);
  in the crash mode it just stops, and its earlier broadcasts may be delivered to only some parties.
* Liveness is proved for every **weakly fair** infinite execution. Messages between never-corrupted parties
  are delivered, and their enabled guards are eventually taken. Nothing is required of corrupted parties or
  injected messages. A round-robin execution shows that fair executions exist (`exists_fair`).
* Protocol guards are *liberal*: "`n − t` messages, all with `v`" is "`v` from `n − t` parties", and either
  branch of a "wait until" may fire when both hold. This is a superset of the paper's behaviours, so safety
  transfers. Parties keep running after deciding.
* Deterministic protocols; randomness appears only in the framework, as coin values per round. A strong coin
  is one value per round, a weak coin one value per party. The expected-round bound for Algorithm 1 is a
  counting statement over coin prefixes, for a deterministic adversary whose binding values depend on
  earlier coins only.
* Safety statements are stronger than the paper's. Agreement, validity and binding cover *all* recorded
  decisions, also of parties corrupted after deciding, in every reachable state and every extension.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 4.3 (Alg. 4 is BCA, `n ≥ 3t+1`, ≤ 4 broadcasts) | `Alg4.theorem_4_3` | `BCAByz.lean` |
| Lemma 4.4 (agreement) | `Alg4.agreement` | `BCAByz.lean` |
| Lemma 4.5 (validity) | `Alg4.validity` | `BCAByz.lean` |
| Lemma 4.6 (approvedVals become equal) | `Exec.approved_spread` | `EchoLayer.lean` |
| Lemma 4.7 (termination; ≤ 4 messages) | `Alg4.termination`, `Alg4.out_ncard_le_four` | `BCAByz.lean` |
| Lemma 4.8 | `Alg4.echo3_consistent` | `BCAByz.lean` |
| Lemma 4.9 (binding) | `Alg4.binding` | `BCAByz.lean` |
| Theorem 4.1 (Alg. 3 is BCA-Crash, `n ≥ 2t+1`, ≤ 2 broadcasts) | `Alg3.theorem_4_1` | `BCACrash.lean` |
| Theorem 5.1 (Alg. 5 is GBCA-Crash, ≤ 3 broadcasts) | `Alg5.theorem_5_1` | `GBCACrash.lean` |
| Theorem 5.3 (Alg. 6 is GBCA-Byz, ≤ 6 broadcasts) | `Alg6.theorem_5_3` | `GBCAByz.lean` |
| Lemma 3.2 | `Alg1.lemma_3_2` | `Framework.lean` |
| Theorems 3.1, 3.3: agreement, validity, binding step | `Alg1.agreement`, `Alg1.validity`, `Alg1.binding_step`, `Alg1.commit_after_binding` | `Framework.lean` |
| Theorems 3.1, 3.3: 4 expected rounds (counting form) | `Alg1.rounds_count`, `Alg1.tsum_succ_div_two_pow` | `CoinRounds.lean` |
| Theorems 3.4, 3.5: agreement, validity, binding step | `Alg2.agreement`, `Alg2.validity`, `Alg2.binding_step` | `Framework.lean` |
| Non-vacuity (fair executions exist, all decide) | `Alg4/Alg6/Alg3/Alg5.exists_fair_all_decide` | `Sanity.lean` |

**Not formalized.** Section 6 (threshold signatures), the EVBCA variants, and the broadcast totals of the
composed protocols (Theorems 4.2, 4.10, 4.11, 5.2, 5.4). Probability spaces: unpredictability, `ε`-good
coins, the `1 + 1/ε` bound of Theorems 3.4/3.5, and `E[T] = ∑ P(T > k)`.

**Trust.** No `sorry`. All listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: for every `n`, `t` and inputs, a fair execution exists and every party decides in it
(`Sanity.lean`). The model is new and shared:
`Podc/Computability/Distributed/Byzantine/AsyncBroadcast.lean` (namespace
`Cslib.Byzantine.AsyncBroadcast`, a CSLib candidate) is a generic asynchronous threshold-broadcast model
with adaptive crash/Byzantine corruption, fairness, monotone-justification and quorum lemmas, and
liveness helpers.

**CSLib candidates.** `Podc/Computability/Distributed/Byzantine/AsyncBroadcast.lean` (whole file).
