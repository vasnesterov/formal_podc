# Differences between the formalization and the paper

Paper: M. Shibata, T. Mega, F. Ooshita, H. Kakugawa, T. Masuzawa, *Uniform Deployment of Mobile Agents in
Asynchronous Rings*, PODC 2016. Formalized version: the journal version (JPDC 119:92–106, 2018), accepted manuscript
(Kyutech repository, record 6499), which contains the full proofs. Numbering (Theorems 1–6, Lemmas 1–9,
Algorithms 1–6, Definitions 1–2) follows that version.

## Mistakes (labels of `mistakes-labeling.md`)

1. ✏️ **Algorithm 2 (loop guard) and the sub-phase count of Section 3.2.** The selection phase is the loop
   `while phase ≠ ⌈log k⌉` with `phase = 1` initially. It runs only `⌈log k⌉ − 1` sub-phases and has no exit that
   makes the remaining active agents leaders. For `k = 2` the body never runs, so no agent ever becomes a leader or
   a follower. The text claims "at most ⌈log k⌉ sub-phases". The correct bound is `⌊log₂ k⌋ + 1`: with `k = 2` and an
   asymmetric configuration, sub-phase 1 leaves one active agent, and it becomes a leader only in sub-phase 2
   (line 6). The same happens for `k = 4`, e.g. homes `{0, 9, 11, 14}` with `n = 16` (simulation,
   `tools/test23.py`). The intended algorithm repeats sub-phases until line 6, 15 or 16 applies. Its proof (active
   agents at least halve in each sub-phase) gives `⌊log₂ k⌋ + 1`, and `O(n log k)` time is unaffected. No Lean proof
   (slip).
2. ✏️ **Algorithm 6, line 14 (array bounds).** `D_ℓ` has `4k'_ℓ` entries. The test needs a `t` with
   `D[j] = D_ℓ[j + t]` for `j < 4k'` and `D_ℓ[0] + … + D_ℓ[t−1] = nodes_ℓ − nodes`, where the right-hand side can
   exceed `4n'_ℓ`, the sum of all entries of `D_ℓ`. Read literally, with indices in range, a misestimating agent
   can reject every correct message. Our simulator gives a fair execution on the aperiodic ring with distance
   sequence `(1,1,9,9,9,9,1,2,2,1,1)` (`n = 45`, `k = 11`) where all agents end suspended forever and are not
   uniformly deployed: the agent at index 2 estimates `n' = 2` (`tools/target456.py "[1,1,9,9,9,9,1,2,2,1,1]" 2 l`).
   Read cyclically (`D_ℓ` as the periodic sequence `(d₀ … d_{k'−1})^∞`, as in "memorizes `a_i`'s whole distance
   sequence `D` as a part of `D_ℓ`"), the test succeeds whenever the paper's proof of Lemma 5 needs it. Random and
   adversarial simulations then find no failure (`tools/burst.py 456c`). No Lean proof (slip; Theorem 6 is not
   formalized).
3. ✏️ **Proof of Theorem 5, one sentence.** "Each agent `a'_i (0 ≤ i ≤ k−1)` behaves in the exactly same way as
   agent `a_i` in `R`" is not justified and can be false: these agents start in the first copy, next to the empty
   half of `R'`, which Lemma 1's shrinking window `V'_t` excludes first. The argument actually used, Lemma 1 applied
   to the last copy `V*`, is correct. Our proof is that argument.

## Typos (no claim affected)

- Section 3.2: "The selection phase of Algorithm 1 requires `O(n log k)` space" should be `O(k log n)`.
- Section 3.1: "`0 ≤ rank ≤ k′ − 1`", but `k'` is undefined there; in fact `rank < p`, the minimal period of `D`
  (`rank_lt_period`). "There exist rank−1 agents between `v_HOME(a_i)` and `v_base(a_i)`" makes sense only for
  `rank ≥ 1` with "between" exclusive.
- Footnote I: PODC 2016 was the 35th symposium, not the 29th.

## Modelling choices

- **Model** (`Model.lean`). Ring `ZMod n`; each node has a token counter, a list of staying agents and a FIFO list
  of agents in transit towards it (its incoming buffer). An atomic action of an agent staying at `v`, or at the head
  of `v`'s queue, does the following: consume all its messages; compute from its state, the messages, the token
  count of `v` and the states of the other agents staying at `v`; release a token or not; broadcast at most one
  message to the agents staying at `v`; stay or leave to the tail of the queue of `v + 1`. This is the paper's
  Section 2.1, with two generalizations:
  - Agents also see the *states* of the co-located staying agents (the paper only allows messages and seeing
    whether agents are present).
  - Token releases are unrestricted (the paper allows one token per agent).

  Both only strengthen the impossibility result (Theorem 5). Algorithm 1 uses neither.
- Agents carry identifiers that the algorithm never sees; they exist only to define schedules. A schedule is a
  sequence of agents. Scheduling an agent that can not act (in transit but not at the head of its queue, or halted)
  is a no-op. Fairness means every agent appears infinitely often, as in the paper.
- Halted agents never act (their messages are never consumed); the paper says the same.
- Initial configuration: no tokens, every agent in the initial state, each in the incoming buffer of its home node.
  This is the paper's assumption, made explicit.
- Definition 1 (`SolvesTD`): in every fair execution all agents eventually halt, and whenever all agents are halted,
  no agent is in transit and the deployment is uniform (`IsUniform`). `IsUniform`: at most one agent per node, and
  from each occupied node the next occupied node is at distance `⌊n/k⌋` or `⌈n/k⌉ = (n+k−1)/k`.
- Definition 2 (without termination detection) is not formalized, since Theorem 6 is not.
- "Knowledge of `k`" means the algorithm may depend on `k` (`alg1 k`). "No knowledge of `k` or `n`" means one
  algorithm for all rings.

## Statements

- **Theorem 3** (`theorem_3`). Correctness is proved for every `n`, every `1 ≤ k ≤ n` and every injective placement,
  including `n ≠ ck` (Section 3.1.1). That section's rule "the first `r/b` intervals are `⌈n/k⌉`, the others
  `⌊n/k⌋`" is written as `offset x N p = x·⌊N/p⌋ + min(x, N mod p)`, where `p` is the minimal rotation period of `D`
  and `N` is the sum of its first `p` entries (`= n/b`). The moves bound is per agent: exactly `n + moves1 D < 3n`
  moves (`alg1_moves_lt`, `trajMove_eq`), hence fewer than `3kn` in total. The `O(n)` time bound (ideal time) and
  the `O(k log n)` memory bound are not formalized.
- **Theorem 5** (`theorem_5`). Stated as: no single algorithm solves Definition 1 in every ring with `2 ≤ k ≤ n`
  agents at distinct nodes. The proof uses the ring `R` with `n = k = 2` and a ring `R'` with `N = 4(T+1)` nodes and
  `2(T+1)` agents, as in the paper (`2(q+1)n` nodes with `q = T`). The replay is asynchronous: every atomic step of
  the round-robin execution of `R` is replayed at all corresponding nodes of a window that shrinks by one node per
  step. The paper's synchronous rounds are not needed.
- **Theorem 1** (`LowerBound.lean`) is stated combinatorially: agents start on the block `0, …, k−1`, their final
  nodes `f` form a uniform deployment, and the total forward distance `∑ (f a − a).val` is a lower bound on the total
  number of moves in a unidirectional ring (this last step is not formalized in the execution model). We prove
  `kn ≤ 6·∑` for `4k ≤ n` (paper: `kn ≤ 16·∑`; `6` is tight, `theorem_1_tight`). The general `p < 1` case
  (`theorem_1_of_le_mul`) is `3(1−p)²/256 · kn ≤ ∑` under `n ≥ 2/(1−p)`. Some such condition is needed, since for
  `k = n − 1` every placement is already uniform. This is consistent with an asymptotic `Ω(kn)` claim. The paper's
  "`k/4` agents go to the opposite quarter" argument does not extend literally to `p` near `1`; we use a window
  argument instead.
- **Lemmas 2–4** (`Words.lean`). Lemma 2 is stated for lists: `B³` is a prefix of `A³` and `|B| < |A|` imply
  `2|B| ≤ |A|`, or `B` is a nontrivial rotation of itself ("periodic"). Lemma 3 holds for every ring, periodic or
  not, and without positivity. In Lemma 4 the proof maximizes the estimated number of *tokens* instead of nodes, and
  concludes with a weak Fine–Wilf lemma instead of the case split on `ℓ ∣ k`. The paper's proof is correct up to
  small unstated steps (it uses positivity of the distances to compare estimates of nodes and of tokens).

## Omitted arguments (not counted as mistakes)

- Theorem 3: "It is obvious that Algorithm 1 solves the uniform deployment problem". The argument needs a few
  ingredients:
  - an agent arriving at another agent's home always finds its token there, which relies on the incoming-buffer
    assumption and FIFO links;
  - the targets are distinct and uniform also for periodic configurations and for `n ≠ ck`;
  - termination under fair schedules with FIFO links.

  All of these are proved (`Inv`, `alg1_targets`, `eventually_allHalted`). There is no mistake.

## Not formalized

- Theorem 2 (`Ω(n)` time), and all ideal-time and memory bounds.
- Theorem 4 (Algorithms 2–3). We only simulated them: with the loop guard fixed, thousands of random and adversarial
  fair schedules, periodic and aperiodic rings, `k ≤ 12`, `n = ck`, gave no failure (`tools/test23.py`,
  `tools/burst.py 23`).
- Theorem 6, Lemmas 5–9 (Algorithms 4–6): simulated only (see mistake 2).
