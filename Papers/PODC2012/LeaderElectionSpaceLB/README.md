# Randomized Test-And-Set: the space lower bound — PODC 2012

George Giakkoupis, Philipp Woelfel. *On the Time and Space Complexity of Randomized Test-And-Set.*
PODC 2012. DOI [10.1145/2332432.2332436](https://doi.org/10.1145/2332432.2332436). Formalized
version: the authors' copy of the PODC paper (HAL hal-00722947, 11 pages; no arXiv version);
numbering follows it.

**Verdict: ⚠️ Minor statement issues.** The headline space lower bound (Theorem 5.1: any leader
election algorithm with nondeterministic solo-termination needs `Ω(log n)` registers, concretely
`⌊log₂ n⌋ - 1`) is proved in Lean, together with Claims 5.2, 5.3, 5.5 and Lemma 5.4. The only
statement-level issue is that the `GroupElect` definition omits "if no process crashes", so read
literally Figure 1 does not satisfy it (Lemma 2.2). A few proof steps need small repairs. The
probabilistic upper bounds are not formalized.

## Mistakes in the paper

### ⚠️ Section 2.1, definition of `GroupElect` (used by Lemma 2.2)
"If some processes call `elect()`, then at least one process must get elected" lacks the "if no
process crashes" qualifier of `LeaderElect`, so in the paper's crash model Figure 1 violates it
(`p` writes `flag` and crashes, `q` reads `flag = 1` and returns `False`;
`GroupElect.not_groupElectLiteral`).

**Impact.** Local. The intended crash-free reading is clear from the `LeaderElect` definition just
before it and from its only use ("if no process crashes then some process wins … at least one of
the processes that call `GE_i.elect()` gets elected"). Under that reading Figure 1 is a
GroupElect object (`GroupElect.isGroupElection`).

### Typos and slips
- Proof of Lemma 2.2, last line: "since `ℓ = ⌈log n⌉ ≤ log k`" should be `≥`. The estimate holds
  (`GroupElect.lemma_2_2_final_bound`; in fact `2 log k + 4`, `GroupElect.final_bound`).
- Proof of Lemma 2.2, computation of `E[Y_j]`: for `i = ℓ − 1` the factor should be
  `(1 − 2^{-(ℓ-1)})^{j-1}`, because `Pr(x = ℓ) = 2^{-(ℓ-1)}`. So "=" is really "≤", and the bound
  is unaffected.
- Proof of Claim 5.2: "`C(E)` and `C(D)` are indistinguishable to all processes in `Q`" is too
  strong under the paper's definition of indistinguishability, which includes all register values.
  Only the states of `Q` agree, together with the registers last written by `Q` (`erase`).
- Claim 5.3 is false for `R = R' = ∅`, `Q = ∅`: then `β` must be empty (degenerate). It is only
  applied with `R ≠ ∅`, which we assume.
- Proof of Lemma 5.4: "every register in `R` is covered by exactly two processes" should read "at
  least two" (it is `n − k ≥ 2`). "No process in `Q` covers a register in `R'`" should say "no
  chosen representative": other members of `Q` may cover `R'`. Neither affects the argument.
- Lemma 5.4(e) relates `m_k` to `m_{k-1}` of a different witness. It only makes sense for the
  sequence the inductive construction builds, and that is what we formalize: `m_k ≥ f(k)`.

## Proof gaps (statements true)

### 🛠️ Theorem 5.1 (reduction to deterministic algorithms)
The proof's claim that the random choices can be fixed so that "the algorithm becomes
deterministic and obstruction free" (every process finishing solo "within a bounded number of
steps") is not justified.

**Impact.** Statement true. The step is not needed: Section 5.2 works verbatim with
nondeterministic executions, and we formalize it that way (`theorem_5_1`).

**Details.** Nondeterministic solo-termination only says that from every reachable configuration
some choice sequence lets the process finish solo. Choices that work from every configuration at
once need not exist if they depend only on the local state. Example gadget: choose a bit `b`,
announce it in `r₃`, read `r₂`, finish if `r₂ = b`, otherwise forget and retry. Another process
writes `1 − r₃` into `r₂`. Put this gadget in front of any correct algorithm. Then every
local-state-based fixing of `b` loops forever solo from a reachable configuration. The gadget does
not refute the usual reading "fix each process's coin tape" (the `i`-th coin of `p`): a tape that
is not eventually constant finishes it within two tries. The paper does not show that a tape with
finite solo runs from every configuration reachable under it exists, and solo runs need not be
bounded. So this is a missing justification of an unnecessary step, not a refuted one.

### 🛠️ Lemma 5.4(e), case `R = ∅`
When no register is covered by `n − k` representatives, the proof keeps the configuration and says
the claim for `k + 1` "follows immediately", but (e) then needs `m_k ≥ n − k`, which is not shown.

**Impact.** Statement true; repaired. `f(k) ≥ n − k` holds by induction (`sub_le_f`), so
`f(k+1) ≤ f(k)` (`f_succ_le`) and `m_{k+1} = m_k ≥ f(k) ≥ f(k+1)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.** (`Model.lean`, self-contained; CSLib's shared-memory `Impl` model is deterministic only.)
- Asynchronous shared memory with `n` processes (any finite type `P`) and atomic multi-reader
  multi-writer registers (any type `Reg`) with arbitrary values `V` and initial values `v₀`.
- Processes are nondeterministic automata. A randomized algorithm is modelled by allowing every coin
  outcome. The next action (read `r`, write `v` to `r`, return win/lose) depends on the local state;
  the successor state is any element of a set. Initial states are nondeterministic too.
- Crashes: finite executions in which some processes stop. No adversary is needed, since the lower
  bound is purely combinatorial.
- Registers carry a ghost "last writer" field. This is the paper's w.l.o.g. "values are pairs
  `(x, ID)`" made invisible to processes, so the theorem holds for arbitrary algorithms.
- Leader election follows Section 1.1. For every set `S` of callers and every finite execution in
  which only `S` steps: at most one process of `S` has won, and if all of `S` returned, one has won.
- Nondeterministic solo-termination: from every reachable configuration every process has a finite
  solo execution after which it has returned.
- For `n` not a power of two we run the construction on `2^⌊log₂ n⌋` active processes (the paper's
  w.l.o.g.).

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 5.1 (`≥ ⌊log₂ n⌋ − 1` registers) | `Alg.theorem_5_1` | `Main.lean` |
| Theorem 5.1, covering form (that many registers covered at once) | `Alg.theorem_5_1_covered` | `Main.lean` |
| Claim 5.2 (as stated; general form) | `Alg.claim_5_2_paper`, `Alg.claim_5_2` | `Erasure.lean` |
| Claim 5.3 (with `R ≠ ∅`) | `Alg.claim_5_3` | `Claim53.lean` |
| Lemma 5.4 (a)–(e) | `Alg.lemma_5_4` (data `Alg.Stage`), `Alg.Stage.group_closed` | `Lemma54.lean` |
| Claim 5.5 (a), (b); `f(n−4) = 4(log n − 1)` | `claim_5_5_a`, `claim_5_5_b`, `f_pow_sub_four` | `Arith.lean` |
| Lemma 2.2 deterministic part: `O(1)` steps, `ℓ + 2` registers, someone elected (crash-free) | `GroupElect.steps_le_four`, `GroupElect.waitFree`, `GroupElect.card_reg`, `GroupElect.isGroupElection` | `GroupElect.lean` |
| Lemma 2.2, literal `GroupElect` definition fails | `GroupElect.not_groupElectLiteral` | `GroupElect.lean` |
| Lemma 2.2, closing estimate `≤ 2 log k + 6` | `GroupElect.lemma_2_2_final_bound` | `GroupElect.lean` |
| Claim 3.1 (counting core only) | `GroupElect.claim_3_1` | `GroupElect.lean` |

**Proof remarks.** Claim 5.2 needs only that no process of `Q` sees a process outside `Q`. Claim
5.3 does not need `R' ∩ R = ∅`. The erasure argument behind Claim 5.2 is `Alg.erase`. The base
case of Lemma 5.4 ("a solo process must write before it returns") is `Alg.solo_writes`.

**CSLib candidates.** The nondeterministic read/write model and covering toolkit (`Model.lean`,
`Basic.lean`, `Erasure.lean`, `Claim53.lean`, marked `-- CSLib candidate`).

**Not formalized.** The probabilistic results: the expected step complexities of Sections 2–4
(Lemma 2.1, the performance bound `f(k) ≤ 2 log k + 6` except its last arithmetic step, Theorems
2.3, 2.4, Claim 3.2, Theorem 4.1, Corollary 4.2) and the 2-process time lower bound (Section 6).
Also not formalized: the semantics of splitters, RatRace and elimination paths behind Claim 3.1,
and the reduction from TAS to leader election.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `NonVacuity.lean` builds, for every number of processes, a deterministic
obstruction-free leader election from `n` single-writer registers ("racing counters": write your
counter, lose if somebody is ahead, win if you are ≥ 2 ahead of everybody). It proves
`Racing.racing_isLeaderElection` and `Racing.racing_soloTerminating`, so the hypotheses of Theorem
5.1 are satisfiable (an `example` in `Main.lean` applies the theorem to it).
`GroupElect.exists_finished_run` shows the GroupElect hypotheses are satisfiable.
