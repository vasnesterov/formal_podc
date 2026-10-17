# Differences between the formalization and the paper

Paper: Civit, Gilbert, Guerraoui, Komatovic, Vidigueira, *On the Validity of Consensus*, PODC 2023
(arXiv:2301.04920v3, extended version). Numbering below follows the extended version.

Summary: all formalized results are **correct**; the paper is morally right everywhere we looked. We found one
genuine (minor) gap in a proof (Lemma 3 for `n < 2t`), several implicit assumptions, and some places where the
formal statement is slightly stronger than the paper's.

## 1. Proof gaps / errors in the paper

1. **Lemma 3 (proof of Theorem 1), case `n < 2t`.** The paper builds `c_{n-t} ∈ I_{n-t}` from *all* `t`
   processes outside `π(base)` plus `n − 2t` processes of `π(base)`. When `n < 2t` this is impossible
   (`t > n − t` processes outside `base` do not fit into a configuration of size `n − t`, and `n − 2t < 0`).
   Example: `n = 3`, `t = 2` (allowed: `0 < t < n`, `n ≤ 3t`). The lemma is still true: take
   `min(t, n − t)` processes outside `π(base)` and `n − t − min(t, n − t)` processes of `π(base)`; this
   configuration is compatible with `base` for all `0 < t < n ≤ 3t`. Fixed in `trivial_of_solvesConsensus_auth`
   (`Triviality.lean`, construction of `X := U ∪ Y`).
2. **Theorem 2 has no content beyond Theorem 1** (formally). "There exists a finite procedure returning an
   always-admissible value" holds as soon as one always-admissible value `v` exists (the constant procedure
   returning `v`), provided values are finitely encodable. `alwaysAdmissible_computable` states this with
   Mathlib's `Computable` (Theorem 1 + `Computable.const`).
3. **Theorem 3 ("Turing-computable Λ") needs the algorithm to be computable.** The paper's model only says
   processes are deterministic state machines (with possibly infinite state spaces and arbitrary transition
   functions); "`A` computes `Λ`" is then unjustified. With arbitrary state machines only the existence of
   a (non-computable) `Λ` follows. We prove both: `similarityCondition_of_solvable` (any `Λ`) and
   `similarityCondition_computable` (Mathlib `Computable Λ`, assuming `Algorithm.IsComputable`: `init`,
   `step`, `send`, `decide` computable; processes `Fin n`; all value/message/state types `Primcodable`).
   Also, `Λ` must be total on all encodings: we define it on every configuration by first replacing a
   configuration that is not an input configuration by the failure-free configuration with a fixed
   proposal; `Λ c` is the first decision (by unbounded search, `Nat.rfindOpt`) of a process of `π(c)` in the
   lock-step canonical execution of `c`. The computable version is also proved in the signature model
   (`similarityCondition_computable_auth`).

## 2. Implicit assumptions made explicit

- `VI` (proposals) is nonempty (`[Nonempty VI]`) in Theorems 1, 3, 4. Without it there are no executions,
  every algorithm vacuously "solves" consensus, and Theorem 1 fails when `VO = ∅`.
- `0 < t < n` (paper §3.1) is a hypothesis where needed; Theorem 4 uses `n ≥ t + 2`, which follows from
  `n > 3t` (itself from Theorem 1 + non-triviality), as in the paper.
- The paper's validity property requires `val(c) ≠ ∅`; we do not need this anywhere and allow any
  `val : Config P VI → Set VO` (only its values on input configurations matter).
- Agreement is stated for all pairs of correct processes **including `p = q`**; this encodes "a correct
  process decides at most once" (decisions are read off the state, so a process could otherwise change its
  mind).

## 3. Model

The paper's model (§3.1): partial synchrony with unknown GST and known `δ`, local clocks drifting before GST,
processes possibly asleep before GST, authenticated channels, arbitrary Byzantine faults. Ours
(CSLib `Cslib/Computability/Distributed/Byzantine/PartialSync/`):

- **Discrete time** `ℕ`; every correct process takes one step per time unit from time `0` on (so it starts
  before GST and its step counter is a drift-free clock). Before GST the adversary can still make a process
  look asleep by delaying its messages, which is all the proofs need ("processes wake up later" in Lemmas 1,
  3 is implemented as "their messages are delayed past `T`").
- Messages are delivered in **batches** (all messages from `p` to `q` sent at the same time share one
  delivery time `dl`); delay `dl − τ ∈ [0, max τ gst + δ − τ]` for correct endpoints; zero delay allowed.
- These choices restrict the adversary / strengthen processes, so the **impossibility results (Theorems 1,
  3, 4) are stronger** than in the paper's model. Conversely, the **possibility side is weaker**: the
  verified vector consensus (`Cslib/Computability/Distributed/Byzantine/PartialSync/VC/`), hence Theorem 5 and the "unconditional"
  classification `solvable_iff`, hold in *this* model, where correct processes are drift-free and awake
  from time 0 (the round compilation relies on all processes starting rounds at the same global time).
  Lifting them to the paper's model (clock drift / sleeping processes before GST) would need a standard
  view-synchronizer argument, which is not formalized. (Found by independent review.)
- `δ` is a fixed parameter (known): impossibility for known `δ` implies impossibility for unknown `δ`.
- **Signatures** (PKI) are modelled abstractly as unforgeable tokens (`Cslib/Computability/Distributed/Byzantine/PartialSync/Auth.lean`,
  same design as the synchronous model). All impossibility results are proved in this authenticated model
  (`*_auth`), which contains the unauthenticated one (`Auth.none`); this formalizes the paper's remark
  "our lower bound holds even for algorithms which employ digital signatures" (§5.1), and also Theorems 1, 3
  with signatures. The adversary may use every token emitted by any correct process so far (eavesdropping,
  rushing) — the strongest standard choice.
- Executions are infinite objects; "finite execution `E` + continuation" is expressed as "runs agreeing up to
  time `T`". Canonical executions = runs whose faulty processes never send (`Run.Canonical`).

## 4. Statements that differ from the paper

- **Theorem 4.** Paper: message complexity `> ⌈t/2⌉²`. Ours (`message_lower_bound(_auth)`): there is a valid
  run with `gst = 0` and a finite `N` such that correct processes send at least
  `⌈t/2⌉·(⌈t/2⌉ + 1)` messages during `[0, N)` — slightly stronger (strict `> ⌈t/2⌉²` is
  `message_complexity_lower_bound(_auth)`, with message complexity defined as in the paper: messages sent by
  correct processes in `[GST, ∞)`, as a supremum in `ℕ∞`). The improvement comes from the pigeonhole step: if
  every `Q ∈ B` heard from `≥ ⌈t/2⌉ + 1` processes, there are already `⌈t/2⌉(⌈t/2⌉ + 1)` messages.
  Messages a process sends to itself are **not counted** (`Run.msgsAt` sums over receivers `q ≠ p`), so the
  bound cannot be met by local self-messages (the counted messages go from `A` to `B`, disjoint groups).
- **Lemma 5 simplification.** In `E_base` the faulty group `B` *ignores all* received messages (runs in
  isolation) instead of "ignoring the first `⌈t/2⌉` messages". Only the number of *distinct senders* to `Q`
  matters (it bounds the extra faulty processes in `E'_base`), so the argument is unchanged and simpler.
- **Lemma 6.** We build `c_{∌Q}` by giving every process other than `Q` a proposal (the paper removes `Q` and
  adds one process only when needed); either works.
- **Theorem 5 / Lemma 8.** Vector consensus (Algorithms 1, 3, 5 of the paper, built on Quad / DBFT / reliable
  broadcast) is **not formalized**; its existence is a hypothesis (`VectorConsensusSolvable(Auth)`).
  `Universal` itself only needs `n > 2t` given vector consensus (`solvesConsensus_universal`); the paper's
  `n > 3t` is needed for vector consensus. The `O(n²)` claim is formalized as "Universal sends exactly the
  messages of the vector-consensus black box in every run" (`universal A Λ = A.mapDecide Λ`, so
  `Run.msgsUpTo_mapDecide`, `Run.msgComplexity_mapDecide`); the `O(n²)` bound of Algorithm 1 (Quad) is not formalized.
- **Classification.** Formalized as `solvable_iff_trivial` (`n ≤ 3t`, unconditional) and
  `solvable_iff_similarityCondition` (`n > 3t`, assuming vector consensus is solvable), and the authenticated
  analogues `solvableAuth_iff_trivial`, `solvableAuth_iff_similarityCondition`.
- `C_S` is formalized with `Λ : Config P VI → VO` whose values matter only on `I_{n−t}`.
- **Computability in the classification.** `SimilarityCondition` (used in the `iff` classification
  theorems) does *not* require `Λ` to be computable: in our model algorithms are arbitrary state machines,
  so the sufficiency direction (`Universal` decides `Λ(vector)`) also works with non-computable `Λ`, and the
  necessity direction yields some `Λ`. The paper's computable `C_S` is necessary for computable algorithms
  (`similarityCondition_computable(_auth)`); with computable vector consensus and computable `Λ`,
  `Universal` is computable as well (not stated formally).
- **Universe restriction.** `ValidityProperty.Solvable` (and `SolvableAuth`, `VectorConsensusSolvable(Auth)`)
  quantify over message/state (and token) types in `Type` (universe 0), i.e. "solvable by an algorithm whose
  message and state spaces are small types". This is harmless (all concrete algorithms live in `Type`), but
  it means e.g. `solvable_iff_similarityCondition` relates solvability by `Type`-valued algorithms with the
  hypothesis that vector consensus is solvable by `Type`-valued algorithms. The algorithm-level theorems
  (`trivial_of_solvesConsensus`, `similarityCondition_of_solvesConsensus`, `message_lower_bound`, …) are
  universe-polymorphic.

## 5. Not formalized

- Appendix B (vector-consensus implementations, Quad modifications, communication complexity `O(n² log n)`),
  Appendix C (external validity extension), the randomized-protocol remark (Appendix A).
- **Vector consensus is formalized and verified for every `n > 3t`**, so the black-box hypothesis is
  discharged. The protocol (`Cslib/Computability/Distributed/Byzantine/PartialSync/VC/`) is *not* the paper's Algorithm 1 or 3 (Quad / DBFT +
  reliable broadcast). It is our own PBFT-style protocol in the DLS round model: views of 5 rounds; statuses
  are echoed so that the leader's evidence can be checked without signatures. Its message complexity
  (not analysed) is far above `O(n²)`, so the paper's `O(n²)` upper bound with PKI is still not formalized.
  Consequently:
  * `solvable_iff_similarityCondition'` / `solvableAuth_iff_similarityCondition'` (`Optimal.lean`): the
    `n > 3t` classification holds **unconditionally**;
  * `solvable_iff`: the full classification (trivial for `n ≤ 3t`, `C_S` for `n > 3t`);
  * `strongValidity_solvable_optimal`, `universal_vc_solves`: binary strong-validity consensus is
    solvable for every `n > 3t` by the explicit protocol `Universal ∘ VC`, deciding the vector's majority;
  * `optimal_message_lower_bound`: Theorem 4 applies to it, so Theorems 3 and 4 are non-vacuous at
    optimal resilience.
  These positive results (vector consensus, the unconditional classification) are stated for `P VI : Type`
  (universe 0).
- An earlier, simpler protocol (`Cslib/Computability/Distributed/Byzantine/PartialSync/BinaryConsensus.lean`, binary strong validity,
  `n ≥ 7t + 1`, no locks) and `NonVacuity.lean` remain as a lightweight example.
- As a further sanity check of the liveness semantics, `Cslib/Computability/Distributed/Byzantine/PartialSync/Examples.lean` has a trivial
  `t = 0` algorithm.
