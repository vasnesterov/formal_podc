# Differences between the formalization and the paper

Paper: Dolev, Lenzen, *Early-Deciding Consensus is Expensive*, PODC 2013 (camera-ready author copy).

## Verdict calibration

Verdict 🛠️ (Proof repaired). Every checked statement is true as written (Lemmas 3.4, 3.5, 3.7, 3.8, 4.2,
Theorems 3.2, 3.6, 4.3, 4.5), and four proofs need repairs:

- **Theorem 3.6.** The statement says "for any consensus protocol". The proof iterates Lemma 3.5, whose proof
  needs decision deadlines (`(f+2)`-deciding for fewer faults). This is a proof gap, not a false statement:
  we prove the theorem for every algorithm (`theorem_3_6_general`). Rule R1: a claim inside a proof that is
  wrong, with a true result, gives 🛠️.
- **Lemma 3.8.** It averages Lemma 3.7's bound over `V \ F_r`, but Lemma 3.7 as stated may count the
  critical node's messages. Lemma 3.7 is true as stated; its proof gives the needed stronger form.
- **Theorem 4.3.** The proof reduces "w.l.o.g." to `t ≤ n - 2`, which covers only `f ≤ n - 3`; the
  theorem claims every `f < t`. A missing case of a true statement (R1): 🛠️, not R2 (nothing is false).
  Repaired by `theorem_4_3_all'`.
- **Theorem 4.5.** The correctness proof never uses orderliness and contains a false claim ("a unique node
  `i₀` deciding in round `i₀` on its input"). The statement is true (proved).

Borderline calls:
- "Section 3 fixes an `(f+1)`-deciding algorithm" (and the proofs say so) where `(f+2)`-deciding is meant.
  Read literally, all of Section 3 would be vacuous, because Theorem 3.6 shows no algorithm is
  `(f+1)`-deciding. The theorem statements (Theorem 3.2, Corollary 3.9) say `(f+2)`, and every deadline the
  proofs use is the `(f+2)` one. We treat this as a slip in the setup text, not a statement issue (R1, R3).
- Theorem 3.6 does not say "with `f` faults". We prove the natural reading: an execution with exactly `f`
  faulty nodes in which some never-faulty node has not decided within `f + 1` rounds.

## Model and definitions

- **Algorithms.** A CSLib `LockStep.Protocol V Bool M Bool`. Messages and decisions are functions of the
  input and the history of received inboxes; the history records the sender of each message (authenticated
  links). The paper's "decides only once" becomes first decisions (`DecidesAt`): later status changes are
  ignored.
- **Executions** (Section 2).
  - The paper's monotone sequence `F₁ ⊆ F₂ ⊆ …` is a finite set `F` plus a fault round `fr p` for each node.
    This is equivalent, since every node fails at most once and `|F_r| ≤ t`.
  - Faulty nodes send arbitrary messages (`adv`), also to faulty nodes; this is irrelevant.
  - The number of faults `f^E = max_r |F_r|` is `F.card`.
  - Self-messages are always `none` (the paper: messages to "the other nodes").
- **Correctness** (termination, agreement, validity) is required for nodes that never fail. Validity is the
  paper's: the output is the input of some node (possibly faulty).
- **Definition 3.1** (`d`-deciding). We require only the never-faulty nodes to decide by round `d(f)`; the
  paper also requires the nodes faulty only after round `d(f)` to decide. As a hypothesis (Theorems 3.2, 4.3,
  Lemmas 3.5–3.8, 4.2) ours is weaker, so our results are stronger. For the algorithm of Theorem 4.5
  (`Orderly.decidedBy`) we prove the paper's version.
- **`(f+2)`-stopping** is proved as: a node that is not faulty in round `k` and sends in round `k` has
  `k ≤ f + 2`.
- **Byzantine section.** `n > 3t` is a hypothesis of Lemmas 3.7, 3.8 and Theorems 3.2, 3.6, as in the
  paper's Section 3. Lemma 3.5 only needs `r < n`.
- **Crash faults (Definition 4.1).** In its fault round a node sends to each node either its algorithm
  message (computed from its actual history) or nothing; later it sends nothing. A node with fault round 0
  is silent from round 1 on (harmless).
- **Orderly crashes (Definition 4.4).** The algorithm fixes a rank `rank p k q`; a crashing node delivers its
  algorithm messages exactly to the nodes of rank `< m`, for some `m`. For Theorem 4.5 the order is by id,
  so the delivered set is a prefix of `i+1, …, n`.
- **Message counts.** `msgCount E R` counts the messages sent in rounds `1..R` by nodes that are not faulty in
  the round of sending (the paper's convention for "non-faulty"). The paper remarks that counting
  eventually-faulty nodes as faulty from the start gives the same asymptotics; this is not formalized.
  Theorem 4.5's bound counts all messages, including those of faulty nodes.
- **Definition 3.3** has the output of `E₀` as a parameter `b` (the paper fixes `b = 0`). This is a pure
  relabelling (`IsCritical.swap`); the stated lemmas produce `b = 0` pairs. Our "the restrictions to the first
  `r - 1` rounds differ only at `v_r`" is: all messages to nodes `≠ v_r` in rounds `< r` coincide, and the
  inputs of nodes `≠ v_r` coincide. The pair records that both executions are admissible.
- **Indexing.** Nodes in Theorem 4.5 are `Fin n` (paper node `i` is our `i - 1`). Our node `i ≤ t` decides
  its own input "after `i` rounds", which is the paper's "at the beginning of round `i + 1`" (1-based `i + 1`).

## Statements

- **Lemma 3.4.** `exists_critical_one` holds for every fault class containing the fault-free executions, as
  the paper notes for the crash section.
- **Lemma 3.5** (`lemma_3_5`). Hypotheses: `A` correct against `t` Byzantine faults; executions with `r - 1`
  faults decide within `r + 1` rounds (the paper's "A is `(f+1)`-deciding" slip, meaning `(f+2)`); `r < n`.
  `lemma_3_5_general` (`Theorem36.lean`) needs no deadline, but produces the weaker pairs `IsCriticalG`:
  faulty nodes need not be silent after round `r`, they send the same messages in both executions to nodes
  other than the critical one.
- **Theorem 3.6.**
  - `theorem_3_6` is the paper's argument; it assumes decision within `f' + 2` rounds for `f' < f` faults.
  - `theorem_3_6_general` holds for every algorithm.
  - `not_deciding_succ`: no algorithm tolerating `t ≥ 1` faults is `(f+1)`-deciding, the remark after
    Lemma 3.5.
- **Lemma 3.7** (`lemma_3_7`). Stronger than stated: `n t ≤ 11 (c₀ + c₁)`, where `c_i` counts the round-`(r+1)`
  messages of the nodes of `V \ F_r` (excluding the critical node `v_r`) in `E_i`. This implies the paper's
  "`nt/22` in one of them". Hypotheses: `1 ≤ r`, `2r ≤ t`, `n > 3t`, decisions within `r + 1` rounds for
  `r - 1` faults.
- **Lemma 3.8** (`lemma_3_8`). As stated: an `(r+1)`-critical pair (with `b = 0`). In round `r + 1` of both
  executions, the nodes non-faulty in round `r + 1` other than `v_{r+1}` send `≥ t²/44` messages, i.e.
  `t² ≤ 44·count`. `lemma_3_8_heavy` also carries the invariant for rounds `2..r` needed by Theorem 3.2.
- **Theorem 3.2** (`theorem_3_2`). As stated, with the explicit bound `t² f ≤ 44 · msgCount E (f + 1)` and
  exactly `f` faulty nodes. Hypotheses `n > 3t`, `1 ≤ f`, `2f ≤ t`, `A` correct and `(f+2)`-deciding.
- **Corollary 3.9.** Not formalized: its `Ω(nt)` part is Dolev–Reischuk [6], cited as a black box.
- **Lemma 4.2** (`lemma_4_2`). As stated (`r < t ≤ n - 2`, `1 ≤ r`), with `(n - r - 1)²` messages in round
  `r + 1` from the nodes of `V \ (F_r ∪ {v_{r+1}})` that are non-faulty in that round, in both executions.
- **Theorem 4.3.**
  - `theorem_4_3`: an execution with exactly `f` crashes in which non-faulty nodes send
    `≥ ∑_{i=1}^f (n-i-1)²` messages.
  - `theorem_4_3'`: `6·msgs ≥ 6n²f − 6nf² + 2f³ − 18nf`, i.e. `nf(n−f) + f³/3 − 3nf`.
  - `theorem_4_3_omega`: `3·msgs ≥ n²f − 9nf`.
  - Hypotheses of these three: `f < t` and `f ≤ n − 3`. The paper's "w.l.o.g. `t ≤ n − 2`" reduction (we
    prove it: `Correct.mono`, `Deciding.mono`) yields exactly `f ≤ n − 3`.
  - `theorem_4_3_all'` (closed form, same constant `3nf`) and `theorem_4_3_omega_all` (`Ω(n²f)`): every
    `f < t` with `f ≤ n`. The cases `f ≥ n − 2` (possible only if `t ≥ n − 1`) are not covered by the paper's
    proof. We take the `f = n − 3` execution and crash `f − (n − 3)` never-faulty nodes silently from a round
    after `f + 1` (`msgCount_addFaults`). The exact sum bound `∑_{i=1}^f (n-i-1)²` is not proved there
    (our construction gives it up to the last summand, which is 1).
  - The paper's hypothesis `t > 1` is not needed.
- **Theorem 4.5.**
  - `Orderly.correct`: termination, agreement and validity against `t` orderly crashes.
  - `Orderly.decidedBy`: every node not faulty in round `f + 1` has decided within `f + 1` rounds (the
    paper's strong Definition 3.1); `Orderly.deciding` is the weak form.
  - `Orderly.stopping`: `(f+2)`-stopping.
  - `Orderly.totalCount_le`: `2·msgs ≤ (t+1)(2n − t − 2)`, i.e. `≤ (t+1)(n − t/2 − 1)`, assuming `t < n`.
    This is implicit in the paper; for `t ≥ n` the formula `(t+1)(n − t/2 − 1)` can be below the actual
    count.
  - `Orderly.totalCount_lt`: `< n(t+1)`.

## Proofs

- **Theorem 3.6.** The paper's proof needs deadlines (see above). Repaired with the forever-equivocating
  `E(W)` (`gpivot`).
- **Lemma 3.7.**
  - Our counting differs from the paper's: "light" nodes have in-degree `≤ t/4`; fewer than `4n/11` nodes
    are heavy; two light nodes are non-adjacent (`exists_light_pair`).
  - The paper's counting (`> 2n²/9` pairs, `> 2n²/11` non-adjacent pairs, average in-degree) is also correct.
  - The paper's contradiction execution is the same as ours: `E(W)` with `W = {v}`, plus the senders `S` to
    `v, w` failing in round `r + 1`.
- **Lemma 3.8.**
  - The averaging step needs Lemma 3.7 for senders in `V \ F_r` (see Verdict calibration).
  - The final extension of `E₀, E₁` "without further faults so that nodes in `V \ (W₀ ∪ {v} ∪ F_r)` cannot
    distinguish them" is replaced by stopping at round `r + 3`. `E₀` has `r + 1` faults, so these nodes
    decide by round `r + 3` (`(f+2)`-deciding), and their views coincide up to that round.
  - The (i)/(ii) swap in the summary is a typo.
  - The faulty `W₀` of `E₁` mimic in rounds `r + 2, r + 3` the messages of `W₀` in `E(W₀)`. These equal their
    messages in `E₀` because `W₀`'s view in `E₀` is that of `E(W₀)` up to round `r + 2`.
- **Theorem 3.2.** The paper says "Fix any `(f+1)`-deciding" (slip). The preservation of message counts of
  earlier rounds ("all non-faulty nodes behave identically in round `r + 1`") is formalized as the invariant
  `Heavy`. Round `k` counts the senders non-faulty in round `k`, without the critical node of round `k`,
  which fails in round `k` of the next pair.
- **Lemma 4.2.**
  - "W.l.o.g. `E₁` outputs 1" is made explicit (`exists_orientation`). If `E(∅)` built on `E₀` outputs the
    value of `E₀`, then `E(∅)` built on `E₁` does too (`out_cpivot_empty_swap`), and we use the swapped pair.
  - The two cases of the claim are one lemma (`cpivot_claim`).
- **Theorem 4.3.** The closed form of the sum in the proof is wrong by `(n − f − 2)²` (`sum_identity_false`:
  `n = 5`, `f = 1`). We prove the exact identity `6·∑ = 6n²f − 6nf² + 2f³ − 18nf + 9f² + 13f` inside
  `sum_sq_bound`.
- **Theorem 4.5.**
  - The paper's proof claims a unique `i₀` and never uses orderliness. We take `i₀` = the last node deciding
    its own input and prove by induction on rounds that all messages delivered to nodes after `i₀` carry
    `i₀`'s input. The induction uses orderliness (`msg_orderly`) and the timing fact that a node `p` sends
    only in a round `≤ p + 1` (`msg_round_le`).
  - `Orderly.not_crash_correct` (`n = 3`, `t = 1`, one non-orderly crash) shows the algorithm is not
    crash-resilient, so orderliness is essential.
  - For the "Decision and Stopping" part, the paper's "node with smallest ID that does not fail" is taken as
    the smallest node not faulty in round `f + 1` (needed for the strong Definition 3.1).

## Not formalized

- Corollary 3.9 (the `Ω(nt)` part is [6]).
- The remark on counting eventually-faulty nodes as faulty for the whole execution.
- Non-vacuity of the hypotheses of the lower bounds. The theorems assume an algorithm that is correct and
  `(f+2)`-deciding (Byzantine) or `(f+1)`-deciding (crash); none is constructed in Lean. Such algorithms exist
  in the literature: Berman–Garay–Perry [1] (Byzantine, `min(f+2, t+1)`) and Charron-Bost–Schiper [2]
  (crash). The orderly algorithm (`Orderly.correct`, `Orderly.deciding`) instantiates the analogous
  hypotheses in the orderly-crash model.
