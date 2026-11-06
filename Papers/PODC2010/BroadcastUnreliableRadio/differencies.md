# Differences between the formalization and the paper

Paper: Kuhn, Lynch, Newport, Oshman, Richa, *Broadcasting in Unreliable Radio Networks*, PODC 2010;
full version MIT-CSAIL-TR-2010-029 (June 2010), whose numbering we follow.

## Model (Sections 2.1, 3) — `Model.lean`

* **Algorithms** are deterministic automata indexed by identifiers (`Algorithm I S M`: `init`,
  `send : S → Option M`, `trans : S → Rx M → S`). The initial state only records whether the
  process is the source; the broadcast message is not part of the state, which encodes the
  paper's assumption that processes treat the message as a black box. Environment inputs other than
  the broadcast message are not modelled (no result uses them).
* **Arrival of the message.** We do not track message contents. A process is *informed* when it
  receives (`Rx.msg`) a message sent by an informed process. This over-approximates "the
  message arrives" (an informed sender need not include the message), so our lower bounds
  (Theorems 2, 4, 12) are at least as strong as the paper's. For the positive statement
  "2-broadcastable" the witness algorithm really forwards the message (source, then bridge), so
  the two notions agree there.
* **Adversary.** Node-level adversaries choose, per round and per set of senders, the set of nodes
  each message reaches (`Adversary V := ℕ → Finset V → V → Finset V`), subject to
  `G ⊆ reach ⊆ G' ∪ {sender}` (`Adversary.Admissible`). The paper's adversary may use the whole
  history. For deterministic algorithms this is equivalent: the execution is determined, so any
  history-based adversary agrees with one of our adversaries along its execution. This matters
  only for "2-broadcastable", which quantifies over all adversaries.
* **ID-level executions.** Executions are run on processes with a `Delivery I` (who is reached);
  a node-level adversary is transported along the placement `π` (`toDelivery`). This is a
  re-indexing, not a change of model (`toDelivery_fromDelivery`).
* **Collision rule CR1 and synchronous start** only (as in all of Sections 4 and 6). CR2–CR4
  and asynchronous start are not modelled in `Model.lean`. The upper bound (Theorem 10) uses its own
  abstract execution model, described in the README and in `StrongSelect*.lean`.
* **Identifier set.** The paper fixes `I` with `|I| = n`. The theorems quantify over every finite
  `I` of cardinality `n` (any `Type`). For Theorem 12, `I` may live in any universe.
* **Probabilistic algorithms (Theorem 4)** are probability measures on random choices `ω` together
  with a map `ω ↦ A ω` to deterministic algorithms (`SolvesWithinWithProb`). This covers processes
  with private coins (and even shared randomness), against the paper's adversary class, which
  fixes only the placement `proc` and resolves everything else by fixed rules. "Solves within `k`
  rounds with probability `q`" is read as: the success event contains a measurable event of
  probability `≥ q` (an inner probability). No measurability assumption is needed, and for
  measurable success events this is exactly the paper's notion. It only makes the impossibility
  stronger.

## Theorem 2 — `theorem_2` (TwoBroadcastable.lean)

* Statement as in the paper, for `V = Fin n`, `s = 0`, `b = 1`, `r = n − 1`. The paper's proof
  only treats `I = {1, …, n}`; we prove it for every identifier set of size `n`.
* "2-broadcastable" is proved (`bridgeNet_broadcastable`): the source sends in round 1, the bridge
  in round 2, against every admissible adversary.
* Proof: Claim 3 (`claim_3`) formalized as stated. The paper's argument is correct. Our induction
  shows "same configuration" directly, using the fact that a round only depends on the delivery
  rule of the messages actually sent (`step_congr`). This replaces the case analysis on what each
  process receives.

## Theorem 4 — `theorem_4` (TwoBroadcastable.lean)

* Stated for every `k`. The paper restricts to `1 ≤ k ≤ n − 3`. For larger `k` the bound
  `k/(n−2) ≥ 1` is trivially true, and for `k = 0` the success probability is `0`.
* The network, the fixed adversary rule `R` (admissible) and 2-broadcastability are part of the
  statement. The adversary class is "choose the placement only, then follow `R`", as in the paper.
* Claim 5's proof sums over `(n−2−k)`-element sets `J`, while the derived sets `I_k` only have *at
  least* `n − 2 − k` elements (🔧). We count directly: for every outcome `ω`,
  at most `k` of the `n − 2` placements succeed (`hpt`), then integrate (`lintegral_finset_sum`).

## Theorem 12 — `theorem_12`, `theorem_12_nlogn` (LowerBoundCore.lean, LowerBound.lean)

* **Sizes.** Proved for `n = 2^m + 1`, `m ≥ 2` (i.e. `n − 1` a power of two, `n − 1 ≥ 4`), the
  case the paper's proof treats ("we assume for simplicity"). The asymptotic `Ω(n log n)` claim for
  arbitrary `n` would need an additional padding argument, which is neither in the paper nor here.
* **Stronger form.** The paper says "every algorithm that *solves* broadcast has an execution taking
  `Ω(n log n)` rounds". We prove that *every* algorithm has an execution in which some process is
  still uninformed after `2^(m−2)·(m−1) = (n−1)/4 · (log₂(n−1) − 1)` rounds
  (`theorem_12`), and hence `k > (n−1) log₂(n−1) / 8` for every `k` within which an algorithm
  solves broadcast (`theorem_12_nlogn`). The paper uses "A solves broadcast" for the existence of
  the isolation round that ends each stage. When that round does not exist we exhibit the failing
  execution directly.
* **Constant.** The paper claims each stage extends the execution by at least `log(n−1) − 2`
  rounds. Counting the round in which the previous stage's process sends alone (round 0 of
  `β_{i,i'}`), each stage adds at least `log(n−1) − 1` rounds, which we use.
* **Proof gap (repaired), Claim 13, Case III.** Subcase IIIa asserts "no process in
  `I − (A_k ∪ {i₁, i₁'})` sends in round `ℓ + 1`" and Subcase IIIb says the only such sender is
  `n₁`. This overlooks the processes removed from the candidate set in *earlier* steps
  (`(I − A_k) − C_ℓ`, e.g. the two `N`-processes dropped in a Case I step), which can send in round
  `ℓ + 1`. `N_{ℓ+1}` only covers members of `C_ℓ`. The claim is false in general, but Part 2 of
  `P(ℓ+1)` still holds. Every process outside both candidate pairs is in the same state in both
  executions (Part 2 of `P(ℓ)`), so it sends the same message in both. In Case III no member of
  either pair sends. Hence the sets of senders coincide and avoid both pairs, and the reception
  of `j` is the same: `⊥`, `⊤`, the message of a lone sender outside `A_k` reaching everybody,
  or the message of a lone sender in `A_k` reaching `A_k ∪ pair`. This is the argument in
  `claim_13`. It also makes the split into IIIa/IIIb unnecessary. (🔧: a wrong claim inside
  a proof of a true result.)
* The adversary's realisability ("the adversary can always follow the rules regardless of the
  assignment to nodes `2k+3, …`") is proved: the delivery rule only ever restricts a lone message of
  a process on a layer `≤ s` to the processes on layers `≤ s + 1` (`LayerAdm`), and the final
  placement is built incrementally by two swaps per stage (`exists_equiv_extend`).
* Typos: "we assign processes `i` and `i'` to `L_k`" should be `L_{k+1}`. The case names
  "Cases 1 and 2(a) … Case 2(b)" in the proof of Claim 13 Part 1 refer to Cases I/II/III. The
  final bound there reads `n/2^{ℓ+2}` instead of `(n−1)/2^{ℓ+2}`. "`C_{ℓ+1}` … the two smallest
  elements of `N_{ℓ+1}`": any two work.

## Theorem 10, Lemmas 8, 9 — `StrongSelect.lean`, `StrongSelectBound.lean`, `StrongSelectExamples.lean`

* **Execution model.** Directed dual graph, CR4, asynchronous start, global round counter
  (the paper's footnote 1). Strong select is oblivious: whether a node sends depends only on its
  identifier, the round and the round in which it got the message. So an execution is described by
  the informed sets `inf t` (`inf 0 = {src}`, monotone), with the senders computed from `inf` by the
  algorithm. The only progress guarantee is: if `u` is the only sender of round `r`, all
  `G`-out-neighbours of `u` are informed after round `r`. Any other informing is allowed (`G'`
  links, CR4 collision resolution). Every CR4 execution yields such a sequence, so the bound is at
  least as strong as the paper's. Identifiers are identified with nodes; a placement just transports
  the families.
* **Parameters.** Instead of the paper's assumptions (`n ≥ 3`, `√(n / log n)` a power of 2,
  `s_max = log √(n/log n)`, `ℓ_s ≤ k_s² f(n)`), we take arbitrary `s_max ≥ 1`, `f ≥ 1` and families
  of *exactly* `ℓ_s = 4^s f` sets. The proof uses `ℓ'_s = 2ℓ'_{s−1}`, which needs exact sizes
  (pad by repetition), and `ℓ'_s = ℓ_s(2^{s_max} − 1)/2^{s−1}` must be an integer. `F_s` is
  `(n, 2^s)`-strongly selective for `s < s_max`, and `F_{s_max}` is `(n, n)`-strongly selective (the
  paper's "round robin", which needs `4^{s_max} f ≥ n`, i.e. `f ≥ log n` with the paper's `s_max`). ✏️
  The existence of small SSFs (Theorem 7, [14]) stays a hypothesis: `theorem10_asymptotic` turns
  `4^{s_max} f ≤ c₁ n` and `f ≤ c₂ log n` into `X² ≤ 144 c₁ c₂ n³ log n`, i.e.
  `X = O(n^{3/2} √log n)`.
* **Statement.** `theorem10`: every node is informed by round `X = n/ρ = 12 n f 2^{s_max}`, as in
  the paper. The paper also says the algorithm "terminates" by `T`. Nodes informed shortly before
  `T` still take part in later iterations, so it is only the delivery of the message that happens
  by `T` (✏️). Stopping is not formalized.
* **Proof gap (repaired), definition of `T`.** The paper takes `T` to be the first round with
  `den(1,T) < ρ`, where `den` counts nodes that receive the message *for the first time*. The
  source is not counted. If the source's identifier is not in `F_1[1]`, nobody sends in round 1,
  so `den(1,1) = 0 < ρ` and `T = 1`. The first step of the proof ("every node receives the
  message by the end of round `T`") is then false. The final contradiction ("`u` got the message
  for the first time in `[T − 1/ρ + 1, T]`") fails when `u` is the source. Lean illustration:
  `paper_T_claim_fails`, on the directed path `0 → 1 → 2` with `s_max = f = 1`. These parameters
  are below the paper's range, but the same happens for every `s_max` when the source is not in
  `F_1[1]`. Repair: count the source as receiving in round 1, i.e. `den(1,t) = |inf t| / t`. Then
  `T > 1/ρ` (`D_lt_T`), and Lemma 9, Lemma 8 and the final step go through with the paper's
  constants. Lemma 8's *proof* also needs the repair: when `T' = 1`, the source can be among the
  participants, and `P ≤ R` fails without it. (🔧: claims inside a proof; the theorem is true.)
* **Where the wrong claim sits.** The claim "every node receives the message by the end of round
  `T`" appears as the first step of the proof of Theorem 10 and, as a roadmap, in the Analysis
  preamble ("We will eventually show that the algorithm terminates no later than round `T`").
  `T` is an auxiliary quantity of the analysis, not part of any numbered statement, so both are
  proof-internal. The numbered Lemmas 8 and 9 are true with the paper's `T` as well
  (not formalized in that form): Lemma 9 directly from minimality (when `T' = 1` the interval is
  `[1, T]` and `den(1, T) < ρ`); in Lemma 8 the participants are at most `R + 1` (the source) and
  `R < k_s(1 − 2^{-s_max})` gives `R ≤ k_s − 1`, so at most `k_s` participants, which the
  `(n, k_s)`-SSF still isolates. The failure is in the paper's parameter range: for every `n`, the
  order of the sets of `F_1` is arbitrary and some set of an `(n, 2)`-SSF (`n ≥ 3`) misses the
  source; putting it first gives `T = 1`. The Lean example `paper_T_claim_fails` uses smaller
  parameters (`n = 3`, `s_max = f = 1`) for illustration only.
* Lemma 8 is formalized as `lemma8`: if `(m+1)ℓ'_s ≤ T < (m+5)ℓ'_s`, then every participant of
  iteration `m` of `F_s` sends alone during that iteration. Lemma 9 is formalized as `lemma9`:
  every node informed by `T` was informed by `T − 1/ρ`. Both use the repaired `T`.
* Typos: in Lemma 8's proof, "otherwise we would have `den(1, T') < ρ`" should be
  `den(1, T' − 1)`, and the display writes `den(T, T')` for `den(T', T)`. `2ℓ'_1 = 8f√(n/log n)`
  should be `8f(2^{s_max} − 1)` (harmless). In the induction step, `(m+4)ℓ' > T` follows from
  the induction hypothesis directly.

## Not formalized

* Lemma 1 (dual graphs simulate explicit-interference graphs). It is called "easy" in Section 2 and
  proved in Appendix A of the full version; formalizing it needs a second network model
  (explicit-interference graphs with the modified collision rules of Appendix A), and no other
  result uses it.
* Theorem 11 (`Ω(n^{3/2})` for directed networks, an adaptation of [9] relying on a
  selective-family lower bound).
* Section 7 (randomized `O(n log² n)` upper bound, Lemmas 14–18, Theorem 19).
