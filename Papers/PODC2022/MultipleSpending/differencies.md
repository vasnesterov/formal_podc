# Differences between the formalization and the paper

Paper: J. P. Bezerra, P. Kuznetsov, *How to Tame Multiple Spending in Decentralized
Cryptocurrencies*, PODC 2022 (brief announcement); full version arXiv:2205.14076v1, whose numbering
we follow. Verdict rules: `../../../.claude/skills/formalize-paper/verdicts.md`.

## Statement-level issues

1. **Theorem 5.1 is false** (R1 statement; R5 headline: the abstract and introduction present "the
   optimal spending number is precisely the inconsistency number" as a main contribution, and the
   lower bound is half of it; not excused by R2–R4 because the repaired bound is a different
   quantity). The proof takes the source `r ∈ F` for the faulty set `F` of a graph `G_{F,S}` of
   maximum independence number, but nothing guarantees that such an `F` contains the source.
   * `theorem_5_1_false` (`Broadcast.lean`): uniform model `n = 3`, `q = 1`, `f = 1`; `λ = 3`
     (all three processes are pairwise independent when nobody fails), yet the trivial algorithm
     (source sends, everybody delivers the first value from the source) is a `2`-CB for every
     choice of source, with per-value Local Progress.
   * `theorem_5_1_false'` (`EchoBroadcast.lean`): four processes `a, a', b, b'`, quorums
     `Q(a) = {a,a'}`, `Q(b) = {b,b'}`, `Q(a') = Q(b') = Π`, faulty sets `∅, {a}, {b}`; `λ = 2`
     but a quorum-echo algorithm is a `1`-CB for every source, with per-value Local Progress.
   * Repair (our theorems): for a source `s`, the optimal `k` is `max 1 λ_s` with
     `λ_s = srcInconsistencyNumber T s` (maximum only over faulty sets containing `s`):
     lower bound `lower_bound` / `srcInconsistencyNumber_le` (`LowerBound.lean`, with per-value
     Local Progress and `∅ ∈ F`), upper bound `echoAlg_isKCB` (`EchoBroadcast.lean`, needs
     `SelfMem`, `HasQuorums`); summary `optimal_kcb` (`Main.lean`). The gluing proof uses
     `∅ ∈ F` (Integrity applies to the failure-free Local-Progress runs only if they comply with
     `F`); it follows from inclusion-closure, and without it the bound fails
     (`lower_bound_needs_empty_mem`). It also uses `p ∈ S(p)`, which follows from Local Progress.
2. **Theorem 5.1 also needs a per-value Local Progress** (R3-borderline; recorded, does not change
   the verdict). The proof needs the values `m_1, …, m_k` delivered in the Local-Progress executions
   to be distinct, but Local Progress only promises that `p` delivers *some* value.
   `WeakLP.theorem_5_1_needs_localProgressAll` (`WeakLocalProgress.lean`): three processes, the
   source is faulty in the unique maximizing faulty set (`k_max = λ_s = 2`), and an algorithm that
   lets a process deliver a default value alone (other values only with help from outside its
   quorum) satisfies the paper's Local Progress and is a `1`-CB. Intended version (per-value) is
   recoverable from the proof ("`k` different values"), so on its own this would be R3 ⚠️.
3. **Optimality claim "Theorems 5.1 and 5.2 imply that Algorithms 1 and 2 implement the k-SAT
   abstraction with optimal k"** (end of §5) is false as a consequence of 1. Moreover the paper's own
   algorithm does better than `k_max`: only faulty issuers multiply spend
   (`spend_le_one_of_correct`), and a faulty issuer `r` spends at most `λ(Q, {B})` times, `B` the
   actual faulty set (`spend_le_byz`). `algorithms_beat_kmax` (`Optimality.lean`): in the `n = 3`,
   `q = 1`, `f = 1` model (`k_max = 3`) every run has spending number `≤ 2`;
   `algorithms_no_double_spending_pairsT`: in the four-process model of `theorem_5_1_false'`
   (`k_max = 2`) the spending number is `≤ 1`.
4. **Theorem 3.6** lacks the hypotheses `f < q ≤ n` (R4 ⚠️: the formula's denominator `q − f`
   is `≤ 0` otherwise, so a reader assumes `q > f`; all uses, e.g. Table 1, satisfy it).
   `theorem_3_6` proves the paper's formula under `f < q ≤ n`; `inconsistencyNumber_uniform` gives
   the value for all `f` (`⌊(n−m)/(q−m)⌋`, `m = min(f, q−1)`); `theorem_3_6_needs_q_gt_f` shows the
   value `n − q + 1` for `q ≤ f`.
5. **Accuracy (§4.2) is stated as "verify-acc(AC, P) returns true iff AC ⊆ F"**: the "if"
   direction is impossible for a run-independent function (`Setup.accuracy_iff_impossible`). Evident
   intent "only if" (R3 typo); we prove that (`accused_byzantine`).
6. **Lemma 4.4 / Definition 3.4 when some process has no quorum**: then there is no quorum map,
   `𝒢_{Q,F}` is empty and `k_max = max ∅` is undefined (in Lean `sSup ∅ = 0`). We assume
   `HasQuorums` (R2: degenerate). The protocol theorems also assume `SelfMem` (`p ∈ Q` for
   `Q ∈ Q(p)`), a standing assumption of §2; without it a process with an empty quorum accepts
   anything and Integrity fails.

## Proof-level issues (statements true)

* **Theorem 3.6 proof** only fixes a faulty set of size exactly `f` (smaller `F` need the
  monotonicity of `(n−x)/(q−x)`, `le_div_of_mul_max_le`) and only proves the upper bound: the
  construction attaining `⌊(n−f)/(q−f)⌋` (disjoint blocks of `q − f` correct processes plus all of
  `F`) is not given. Both added.
* **Lemma 4.4 proof**: the acceptors `p_1, …, p_k` of the `k` conflicting transactions must be
  distinct; this follows from No-Conflict of each history (Lemma 4.3), not stated. A quorum map
  must also be defined on processes outside the independent set (needs `HasQuorums`).
* **Theorem 4.1 proof** is informal but correct; our proof: outgoing stake of `w` = value of the
  inputs of `w`'s transactions (Validity), these input sets are disjoint (No-Conflict) and inside
  `T` (Completeness). Cycle-Freedom is not needed.
* **Theorem 5.2** (k-SAT implements k-CB) is not formalized. Its proof writes `deliver(m)` for a
  transaction carrying `m'` (typo), and to transfer the lower bound of Theorem 5.1 to k-SAT one also
  needs Local Progress for the derived broadcast, which is not discussed.

## Typos and slips

* Example 3.1: `F = {{p₃}}` is not inclusion-closed (we check both `{∅, {p₃}}` and `{{p₃}}`;
  answer `2` in both cases, `example_3_5`, `example_3_5_literal`); `Q(p₃) = {{p₁,p₂,p₄}}` violates
  `p ∈ Q` (`example_3_1_not_selfMem`); irrelevant for the claim.
* Algorithm 1 line 5 verifies the REQ signature with the *sender's* key `p_j` and then stores the
  pair as a request signed by `tx.s`; read literally, a Byzantine `p_j` can make a correct process
  store and echo a "request" of a correct issuer and accuse it (lines 26–31 add accusations without
  `verify-acc`). The text says `σ` is a signature of `tx.s`; we model a REQ as valid only when it
  comes from the issuer.
* Algorithm 2 line 26 must require `tx ≠ tx'` (otherwise every transaction with a nonempty input
  set yields an accusation of its issuer); the text says "distinct transactions".

## Modelling choices

* **Transactions** are an abstract type with issuer (`none` = originator, only `tx_init`), output
  map and finite input set (`TxSystem`); the paper's tuples are a special case. `inValue` of the
  originator is `0`. The spending number is valued in `ℕ∞` (`encard`).
* **Trust model**: quorums and faulty sets are `Finset`s of a finite process type; `SelfMem`,
  `DownClosed`, `HasQuorums` are separate hypotheses. The trust graph is a Mathlib `SimpleGraph`
  on `{p // p ∉ F}`; independence number = `SimpleGraph.indepNum`.
* **Algorithms 1–2** (`Protocol.lean`): interleaving model, static Byzantine set `B` (the run's `F`),
  authenticated asynchronous channels where messages may be received any number of times (a
  superset of the reliable-channel behaviours for safety). Local variables are derived from the
  messages (`usedInp` from own echoes, `signedRequests` = `HasReq`, `acHist` = own `ACC`
  messages); only `trHist` is explicit. Guards are liberal (echo/accept/accuse at any time after
  they become enabled); this is a superset of the code's behaviours, so safety transfers.
  Signatures: Byzantine processes may inject any message whose embedded issuer signatures are
  valid (`MsgSigned`: the issuer is Byzantine or sent the request). `verify-acc` checks distinctness,
  same issuer and a common input; signature validity is enforced by `MsgSigned`.
  The application's transfers are a fixed set `issue p`; "correct processes never issue
  conflicting transactions" (`HonestIssuers`) is an explicit hypothesis where needed (Accuracy and
  the refined bound), as the paper assumes it implicitly ("since p is correct, it will not send
  conflicting requests").
* **k-CB** (`Broadcast.lean`): CSLib-candidate model `Cslib.Byzantine.AsyncBroadcast`
  (adaptive corruption — a stronger adversary than the paper's static one, so our algorithms'
  correctness is a stronger result; for the lower bound we only use static corruption at time 0).
  Executions comply with the fault model iff the set of ever-corrupted processes is in `F`.
  Delivery = the single persistent decision. Local Progress: a reachable state with no corruption
  where only the source and `Q` sent, received or delivered, and `p` delivered (the paper: "only
  the source and processes in `Q` take steps, `p` is correct, and `p` delivers a value").
* **Liveness of Algorithms 1–2** (`Liveness.lean`): infinite stuttering executions; `Fair` =
  delivery of every message between correct processes, every transaction of `issue p` is issued,
  weak fairness of echo/accept/accuse/relay (guards mirror the `Step` premises). Non-vacuity:
  `exists_fair` (round robin, countable `P`, `Tx`).

## Liveness (Lemmas 4.5–4.7, Agreement)

* All proved (`agreement`, `lemma_4_5`/`conviction`, `lemma_4_6`, `lemma_4_7`), assuming `SelfMem`.
* **Lemma 4.7 (Validity)** needs three assumptions the paper only uses implicitly (R4 ⚠️, recorded):
  `HonestIssuers` ("since p is correct, it will not send conflicting requests"), the issued
  transaction is valid (§4.3: "transactions issued by correct processes are always valid", not in
  the problem statement), and the issuer has accepted all inputs of `tx` (the proof: "p must have
  previously added every transaction on which tx depends to trHist"; `transfer` never checks it).
  Without the last one Validity fails: `ValidityCex.validity_needs_inputs` (a correct live process
  issues a valid transaction whose input is never issued; it never accepts it nor accuses anyone).
* The "p did not echo tx" cases of Lemmas 4.5–4.6 are vacuous under `SelfMem` (an acceptor is in its
  own quorum, so it echoed `tx`). Termination's induction over the dependencies of `tx` is implicit
  in the paper; we do it by induction on acceptance time.
