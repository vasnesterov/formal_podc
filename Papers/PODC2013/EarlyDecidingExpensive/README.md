# Early-Deciding Consensus is Expensive — PODC 2013

Danny Dolev, Christoph Lenzen. *Early-Deciding Consensus is Expensive.* PODC 2013. DOI
[10.1145/2484239.2484269](https://doi.org/10.1145/2484239.2484269). Formalized version: the authors'
camera-ready copy (10 pages, proofs included; the paper says no full version exists).

**Verdict: 🛠️ Hard fix.** Every checked result holds: the `t²f/44` Byzantine bound for `(f+2)`-deciding consensus
(Theorem 3.2), the `f + 2` decision bound (Theorem 3.6), the `Ω(n²f)` crash bound (Theorem 4.3), the orderly-crash
algorithm (Theorem 4.5), and Lemmas 3.4–3.8 and 4.2. The lower bounds need only local repairs of their proofs. But the
correctness proof of the orderly-crash algorithm, one of the paper's three results, never uses orderliness, and the
algorithm is wrong without it, so it took a new induction.

## Mistakes in the paper

### ✏️ Slips
- Section 3 fixes "an `(f+1)`-deciding algorithm". So do the proofs of Lemmas 3.5 and 3.7 and of Theorem 3.2.
  All of them need, and Theorem 3.2 states, `(f+2)`-deciding. Taken literally the section would be vacuous,
  since Theorem 3.6 shows that no algorithm is `(f+1)`-deciding.
- Proof of Lemma 3.8, "In summary": (i) and (ii) are swapped. In `E₀` the non-faulty nodes of `W₀` decide 0;
  in `E₁` the non-faulty node `v` decides 1.
- Proof of Theorem 4.3: the closed form of `∑_{i=1}^f (n-i-1)²` is off by `(n-f-2)²`. The subtracted term
  should be `(n-f-2)(n-f-1)(2(n-f)-3)/6`; for `n = 5`, `f = 1` the sum is 9, not 13 (`sum_identity_false`).
  The next line carries a spurious `+6n²`. The final bound `nf(n-f) + f³/3 - O(nf)` is right
  (`sum_sq_bound`).

### Typos
- Definition 4.1: "a subset `W \ V`" should read `W ⊆ V`.

## Proof gaps (statements true)

### 🛠️ Theorem 4.5 (correctness of the orderly-crash algorithm)
The correctness proof claims "a unique node `i₀` deciding in round `i₀` on its input", which is false, and
never uses that crashes are orderly, although without orderly crashes the algorithm violates agreement
(`not_crash_correct`).

**Impact.** The statement is true, but the printed proof lacks the idea; we prove the theorem with a new argument
(`Orderly.correct`, `Orderly.decidedBy`, `Orderly.stopping`, `Orderly.totalCount_le`).

**Details.** If node 1 crashes before sending, node 2 also decides its own input, so `i₀` is not unique. The
real issue is the claim that every node `> i₀` adopts the value of `i₀`. It needs messages from nodes
`< i₀` never to reach nodes beyond `i₀` when `i₀` itself received nothing, and only orderliness gives that.

With ordinary crashes, take `n = 3`, `t = 1`. Node 1 (input 0) crashes in round 1, reaching only node 3.
Node 2 has received nothing, so it decides its input 1, while node 3 decides 0. Both stay correct.

**Repair.** Let `i₀` be the *last* node that decides its own input. Every node before `i₀` crashed. By
induction on rounds, every message delivered to a node after `i₀` carries `i₀`'s input. A sender before `i₀`
would also have reached `i₀` (prefix property) in a round `≤ i₀`.

### 🔧 Theorem 3.6 (decision before round `f + 2` is impossible)
The theorem is stated "for any consensus protocol", but its proof iterates Lemma 3.5, which needs the
algorithm to decide within `f' + 2` rounds whenever there are `f' < f` faults.

**Impact.** Statement true for every algorithm; a small change of the paper's construction proves it
(`theorem_3_6_general`, `not_deciding_succ`). The deadline-based version is `theorem_3_6`.

**Details.** In the paper's `E(W)` the faulty critical node `v_r` falls silent after round `r + 1`. So
`E(V \ F_r)` looks like `E₀` to the honest nodes only before round `r + 2`. Its output equals that of `E₀`
only if `E₀` (with `r - 1` faults) has decided by round `r + 1`.

**Repair.** Let `v_r` equivocate forever: in every round `k ≥ r` it sends to `W` what it sends in `E₀` and to
the rest what it sends in `E₁`. Then `E(V \ F_r)` and `E(∅)` look like `E₀` and `E₁` forever, and their
outputs follow without any deadline. The pairs obtained satisfy Definition 3.3 except that faulty nodes may
keep talking. They send the same messages in both executions to everybody but the critical node
(`IsCriticalG`, `lemma_3_5_general`). This is all the final step of the proof of Theorem 3.6 needs.

### 🔧 Lemma 3.8 (uses more than Lemma 3.7 states)
Lemma 3.7 bounds the round-`(r+1)` messages of all non-faulty nodes, including the critical node `v_r`,
but Lemma 3.8 averages this bound over `V \ F_r`, which excludes `v_r`.

**Impact.** Statements true (`lemma_3_7`, `lemma_3_8`).

**Details.** For `t < 22` the `nt/22` messages of Lemma 3.7 could all come from `v_r` (it can send `n - 1`
of them). Then inequality (1) of Lemma 3.8 does not follow.

**Repair.** The proof of Lemma 3.7 only counts messages from senders in `V \ F_r`, so it gives the bound we
need. `lemma_3_7` states it that way: `n t ≤ 11 (c₀ + c₁)`, counting the senders of `V \ F_r` in both
executions.

### 🔧 Theorem 4.3 (case `f ≥ n - 2`)
The proof's reduction to `t ≤ n - 2` only covers `f ≤ n - 3`, while the theorem claims every `f < t`,
including `f ≥ n - 2` when `t ≥ n - 1`.

**Impact.** Statement true for every `f < t` (`theorem_4_3_all'`, `theorem_4_3_omega_all`).

**Repair.** Take the execution for `n - 3` faults. Let `f - (n - 3)` more nodes crash silently after round
`f + 1`. This changes no counted message, and `∑_{i=1}^{n-3} (n-i-1)²` still meets the bound
`nf(n-f) + f³/3 - 3nf` for `f ≤ n`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Synchrony.** Synchronous rounds `1, 2, …` on a complete network of `n` nodes (`V`, any finite type).
  Links are authenticated: the receiver knows the sender. Messages and local computation are unbounded.
  Algorithms are deterministic CSLib lock-step protocols with binary inputs and outputs
  (`Cslib.Byzantine.LockStep.Protocol`); a node's messages and decision depend on its input and history.
  Decisions are first decisions, so they are final.
- **Executions.** An execution fixes the inputs, the faulty set `F` and, per faulty node, the round from
  which it is faulty (the paper's `F₁ ⊆ F₂ ⊆ …`). It also fixes the messages faulty nodes send. Before its
  fault round a node follows the algorithm. `f = |F|`. Our histories are exactly CSLib's lock-step histories
  of the corresponding static-Byzantine scenario (`hist_toScenario`).
- **Fault classes.**
  - Byzantine (`byzAdm t`): at most `t` faulty nodes, arbitrary messages, `n > 3t` as in Section 3.
  - Crash (`crashAdm`, Definition 4.1): in its fault round a node sends a subset of its algorithm messages,
    then nothing.
  - Orderly crash (`orderlyAdm`, Definition 4.4): that subset is a prefix of an order fixed by the algorithm.
  - No randomness. The adversary picks inputs, faulty nodes, fault rounds and faulty messages with full
    knowledge.
- **Specification.** Termination, agreement and validity (the decided value is some node's input) for the
  nodes that never fail. `d`-deciding (Definition 3.1) requires the never-faulty nodes to decide within
  `d(f)` rounds. The paper also constrains nodes that fail after round `d(f)`, so as a hypothesis our version
  is weaker and the lower bounds are slightly stronger. For the algorithm of Theorem 4.5 we prove the paper's
  strong form.
- **Message counts.** Counts include messages sent in rounds `1..R` by nodes that are not faulty in the round
  of sending, which is the paper's convention. Theorem 4.5 counts all messages, faulty senders included.

**Main results in Lean** (namespace `Podc.EarlyDecidingExpensive`).

| Paper | Lean | File |
|---|---|---|
| Model (Section 2), Definitions 3.1, 4.1, 4.4 | `Execution`, `hist`, `msg`, `Correct`, `Deciding`, `byzAdm`, `crashAdm`, `orderlyAdm`, `msgCount`, `hist_toScenario` | `Model.lean` |
| Definition 3.3 (critical pairs) | `IsCritical` (output of `E₀` a parameter), `IsCritical.swap` | `Critical.lean` |
| Lemma 3.4 | `exists_critical_one` | `Critical.lean` |
| Lemma 3.5 | `lemma_3_5` | `Critical.lean` |
| Theorem 3.6 (paper's proof, with deadlines) | `theorem_3_6` | `Critical.lean` |
| **Theorem 3.6** (every algorithm), remark "no `(f+1)`-deciding algorithm" | `theorem_3_6_general`, `not_deciding_succ` | `Theorem36.lean` |
| Lemma 3.7 (strengthened) | `lemma_3_7` | `Byzantine.lean` |
| Lemma 3.8 | `lemma_3_8` (and `lemma_3_8_heavy` with the invariant) | `Byzantine.lean` |
| **Theorem 3.2** (`t² f ≤ 44 · msgs`) | `theorem_3_2` | `Byzantine.lean` |
| Lemma 4.2 | `lemma_4_2` | `Crash.lean` |
| **Theorem 4.3** (`∑(n-i-1)²`, closed form, `Ω(n²f)`; `f ≤ n - 3`) | `theorem_4_3`, `theorem_4_3'`, `theorem_4_3_omega` | `Crash.lean` |
| **Theorem 4.3** (closed form, `Ω(n²f)`; every `f < t`) | `theorem_4_3_all'`, `theorem_4_3_omega_all` | `Crash.lean` |
| **Theorem 4.5** (orderly crashes) | `Orderly.correct`, `Orderly.decidedBy`, `Orderly.deciding`, `Orderly.stopping`, `Orderly.totalCount_le`, `Orderly.totalCount_lt` | `Orderly.lean` |
| Theorem 4.5 needs orderliness | `Orderly.not_crash_correct` | `CrashCounterexample.lean` |
| Sum in the proof of Theorem 4.3 | `sum_sq_bound`, `sum_identity_false` | `Combinatorics.lean` |

**Remarks.**
- The proof of Lemma 3.8 extends `E₀, E₁` forever without faults. Under `(f+2)`-deciding it suffices to
  extend them to round `r + 3` (the deadline for `r + 1` faults), which is what we do.
- Our proof of Lemma 3.7 counts differently: the "light" nodes have in-degree `≤ t/4`, and two of them must
  be non-adjacent. The paper's counting is also correct.
- Lemma 3.8 uses `⌈t/2⌉` nodes as in the paper. Theorem 3.2 is proved for `1 ≤ f ≤ t/2` exactly; for
  `f = 0` it is trivial.
- Theorem 4.3: the exact sum bound `∑_{i=1}^f (n-i-1)²` is proved for `f ≤ n - 3`, the range of the paper's
  proof; the closed and asymptotic forms, which are what the theorem states, for every `f < t`.

**Not formalized.**
- Corollary 3.9, whose `Ω(nt)` part cites Dolev–Reischuk [6].
- The remark that counting all eventually-faulty nodes as faulty from the start changes only constants.
- No Byzantine `(f+2)`-deciding algorithm (Berman–Garay–Perry [1]) and no crash `(f+1)`-deciding algorithm is
  constructed. So the hypotheses of Theorems 3.2 and 4.3 are not shown satisfiable in Lean. They are
  satisfiable by the cited literature. The orderly-crash algorithm shows the analogous hypotheses are
  satisfiable in the orderly model.

**CSLib candidates** (marked `-- CSLib candidate`): the execution model with per-round fault onset and
`addFaults` (`Model.lean`), `exists_flip` and `exists_subset_card_sum_ge` (`Combinatorics.lean`).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
The model reuses CSLib's lock-step protocols (`Cslib.Computability.Distributed.Byzantine.LockStep.Basic`).
