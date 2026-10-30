# Differences between the formalization and the paper

Paper: Monti, Camaioni, Roman, *Fast Byzantine Total Order Broadcast*, PODC 2026, arXiv:2412.14061v2.

## Statement-level issues (with the deciding rule from `verdicts.md`)

1. **"At least `5f + 1` servers" (abstract; introduction) vs. hard-coded thresholds.** §2.1 fixes `n = 5f + 1`,
   and all proofs use it. Blink's `4f + 1`/`2f + 1` and Flutter's lock quorum `4f + 1` are wrong for
   `n = 5f + 2`. Lean counterexamples: `blink_agreement_fails_5f2` (Blink with a `dep` satisfying Validity,
   Agreement and Integrity) and `flutter_totalOrder_fails_5f2` / `flutter_not_prefix_5f2` (Flutter with a
   `con` satisfying Representative Validity and Agreement). Repaired: thresholds `n − f`
   (`blink_safe_general`, `theorem8_totalOrder_general`). In both counterexamples every black-box decision comes
   after the correct proposals that justify it, so they also hold under a temporal reading of the specs.
   *Rule:* borderline between R4 and a false claim. We chose ⚠️ for three reasons. (a) The paper's model
   section states `n = 5f + 1` explicitly, and the counterexamples violate that model. (b) Writing thresholds
   for `n = 5f + 1` and saying "at least `5f + 1`" is a common convention in BFT papers, meaning the resilience
   bound `f < n/5`. (c) The repair (`4f + 1 ↦ n − f`) is local and evident. A stricter reader could rate it a false claim
   (R4: "NOT excused if the paper explicitly claims more generality"); on that reading the label would be 🚨,
   not ❌, because the claim is about the paper's specific algorithm Flutter, the title result (R5: a false
   named algorithm is 🚨 even if a repaired protocol exists).
   *Reviewer note.* Precedents rated 🚨 for the same threshold pattern (`Papers/PODC2019/VABA`,
   `Papers/PODC2021/RoundEfficientBA`) differ in one decisive way: there the model section and the numbered
   theorems themselves claim every `f < n/3`, and the proofs reason in that generality. Here the model (§2.1,
   with a citation) fixes `n = 5f + 1`, every numbered result is stated and proved in that model and is true
   there; only the abstract/introduction phrase "at least `5f + 1` servers" overreaches. That is why ⚠️ is
   endorsed, as a borderline call.
2. **Lemma 5 as stated** does not say whether the sequence may be finite. Read as an `ℕ`-indexed strictly
   increasing sequence of elements of `X`, it is false for finite nonempty `X` (`lemma5_literal_false`); "sequence"
   may however be read as finite or infinite, so this is an imprecision rather than an error. Intended: a finite
   or infinite enumeration, as the proof shows (`φ` is a bijection with `{n ≤ |X|}`). Proved as `lemma5_finite` (sorted list) and `lemma5_infinite` (`z : ℕ → α`,
   `range z = X`). Our infinite case assumes `X` infinite instead of splitting on `|X|`. *Rule:* R3 (evident
   intent, local fix, the proof uses the intended version) → at most ⚠️.
3. **Lemma 6 as stated** does not say that `z`, `z'` take values in `X`; if they may leave `X` it is false
   (`lemma6_literal_false`: `X = {0}`, `z = id`, `z' = 2·`). Read as sequences in `X` it is true.
   Proved with `range z = range z' (= X)` (`lemma6_infinite`, via Mathlib's
   `StrictMono.range_inj_of_wellFoundedLT`; `lemma6_finite` for sorted lists). The proof uses `z_n, z'_n ∈ X`,
   and the hypothesis holds at its uses (Corollary 2 by construction; Corollary 3 by Lemma 18). *Rule:* R3 → at most ⚠️.

## Proof-level differences (statements unaffected)

* Theorems 2 and 4 (Blink): the paper's proofs go through Lemma 1, i.e. the Termination of `dep`. Our proofs
  use only the Validity and Agreement of `dep`, so they also cover runs where `dep` never decides.
* Lemma 4: the paper uses the Integrity of `dep`; we use its Agreement (with `p = q`). We also state Integrity
  (`DepIntegrity`); the safety theorems do not need it.
* Lemmas 2–4 and Theorems 2/4 are proved for general thresholds. The hypotheses are `n + |F| < Q + M` and
  `M ≤ Q` for Agreement, and `M, Q ≥ 2f + 1` for Representative Validity. The paper's argument "`3f + 1` and
  `f + 1` correct servers must meet" is the instance `Q = 4f + 1`, `M = 2f + 1`, `n = 5f + 1`. Note that
  Agreement needs `n ≤ 5f + 1` with these thresholds, which item 1 makes precise.
* Lemma 16 is proved in a **safety form**: "if `f + 1` correct servers propose `True` for `y` (at some time) and
  `p`'s lock time is `≥ y.bet` at time `k`, then `y ∈ candidates_p` at time `k`". The paper's statement
  `F ⊆ C[π]` also covers servers whose lock time never reaches `b`, and that part uses the liveness Lemma 10. The
  general hypothesis is `n < (f + 1) + q`, with lock quorum `q`.
* Lemmas 17–20 and Corollary 4 are proved as invariants at every time (`orders_gapFree`, `corollary4`):
  * order calls are strictly increasing and decided `True`;
  * every tag decided `True` below an order call is itself an order call;
  * the order-call sequences of two correct servers are prefix-comparable.

  The paper instead identifies the complete (possibly infinite) sequence of order calls with the enumeration of
  `F` (Corollaries 2–3, Lemma 21). That needs liveness and is not formalized.
* Theorem 8 is formalized in its safety part: at any two times the `tob.Deliver` sequences of two correct servers
  are prefixes of one another (`theorem8_totalOrder`). "Eventually deliver the same messages" is not formalized.
* Lemma 15 is a local invariant of each server's sequence of messages sent to all servers (`LInv.lemma15`).
  FIFO enters only in Lemma 16.
* Integrity (Theorem 7): we conclude "`θ` broadcast `m` at some time of the run". The black-box Representative
  Validity is over whole runs, so the supporting proposal may lie in the future.

## Modelling choices

* **Asynchronous interleaving model, safety only.** No `Δ`, `Ψ`, GST or real time. Any finite asynchronous prefix
  is consistent with the paper's partial synchrony (choose `Δ`, `Ψ` large), so the counterexamples are valid in
  the paper's model. The positive results hold in every asynchronous run, which is stronger than needed.
* **Clocks:** one local clock per correct node, moved forward by `tick` (non-decreasing; the paper uses this in
  Lemma 15). Initial clocks are arbitrary.
* **`beat()`** may run at any time. The paper runs it "regularly" (§4.2) and at the bets of observed messages
  (line 27). The superset of behaviours makes the safety results stronger. In the Flutter counterexample every
  beat is a scheduled one: at time 20, by a server that observed the message with bet 20.
* **Line 16 of Blink** ("the value suggested at least `2f + 1` times") is a nondeterministic guard. With the
  paper's `W = 4f + 1` there is exactly one such value. The wait threshold `W` plays no role in safety.
* **Links.** Blink: a delivery of `[Suggest, v]` from a correct `σ` is allowed iff `σ` proposed `v`. Repeated
  deliveries are allowed, which only generalizes. Flutter: per-link FIFO queues (`sent`, `dlv`) for correct
  senders; Byzantine senders' messages are arbitrary. In Flutter all server-to-server sends go to every server,
  so the queue from `ρ` to any server equals `ρ`'s history `obox` (`GInv.srv`). Likewise for clients (`cbox`).
* **Servers and clients are disjoint node sets** (`P ⊕ C`). The paper allows overlap (footnote 1). Overlap only
  merges identities and is not needed for the results here.
* **Atomic handlers:** each `upon` handler (e.g. lines 31–36) is one atomic step, as in the pseudocode.
* **History variables** are added to the states (`props`, `decs`, `procd`, `orders`, `dels`, `obox`, `bcast`,
  `cbox`, `depProp`, `depDecs`, `decs`, `input`). They do not influence the algorithm.
* **Black-box specs** are hypotheses on whole runs. `dep`: Validity and Agreement (Integrity optional).
  `con[x]`: Representative Validity and Agreement. Termination is never assumed.
* **Order on tags** is Assumption 1: bet, then client, then message (`Tag`, via `toLex`). `(⊥, ⊥, −∞)` is `⊥` in
  `WithBot Tag`; `−∞` in `remote_times` is `⊥ : WithBot T`.
* **`lock_time()`** is the largest value `t` with at least `q` entries `≥ t`, characterized in `le_lockTime_iff`.
  The quorum `q` is a parameter (paper: `4f + 1`).
* **Time type:** any linear order `T`. Clients need `+` and `•` on `T` to compute bets (`[AddCommMonoid T]`).
