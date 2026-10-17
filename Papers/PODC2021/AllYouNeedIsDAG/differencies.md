# Differences between the formalization and the paper

Paper: Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021, arXiv:2102.08325v2.

## Errors and gaps in the paper

1. **Lemma 1 is false as stated. The statement of Proposition 2 is true, but its proof has a gap.**
   Section 6.1 defines "commit" as popping from the stack. This includes leaders committed
   *indirectly* in lines 39–43. Lemma 1 claims that every later leader `u` has `strong_path(u, v)`
   to every committed leader `v`. The proof only uses the commit rule of line 36, so it covers only
   *directly* committed leaders.
   *Counterexample* (`n = 4`, `f = 1`, see `Lemma1Counterexample.lean`; observer: correct process `3`,
   whose DAG at `wave_ready(w)` is rounds `1..4w` minus its own `(4w, 3)`, a realizable view): the leader `v₁` of wave 1
   is not committed in wave 1. The wave-2 leader `v₂` has no strong path to `v₁` and is not
   committed either. The wave-3 leader `v₃` is committed directly and reaches `v₁` but not `v₂`.
   So `v₁` is committed with `v₃`, while `v₂` (in the same DAG) has no strong path to `v₁`.
   Proposition 2's proof cites Lemma 1 for all committed leaders.
   *Repair:* `lemma1_direct` proves Lemma 1 for direct commits. The total-order proof then shows
   that the output of a process is the delivery of the "full chain" of its last directly
   committed leader. That chain depends only on the global DAG (`orun_inv`, `gchain_through`).
   Classification: false statement (Lemma 1, with Section 6.1's definition of *commit*); proof gap
   with true statement (Proposition 2). Section 5 states Lemma 1 right after the commit rule; read as
   being about direct commits only, it is true (`lemma1_direct`) and only the Proposition 2 gap remains.
2. **Chain quality (Section 3) holds only for suitable delivery orders. The paper states it
   without proof.** `order_vertices` delivers "in some deterministic order".
   - If that order sorts by source first, chain quality fails (`chain_quality_false`: `n = 4`,
     `f = 1`, a prefix of size 3 with 2 Byzantine blocks).
   - If the order is round-major (non-decreasing rounds, arbitrary order inside a round), the
     claim holds (`chain_quality`). Key fact: in every prefix of the output, every round below
     the highest round of the prefix already has `2f + 1` vertices.

   Classification: under-specified definition / unproved claim (false for some admissible
   orders, true for round-major ones).
3. **Lemma 2 / Claim 6: the probabilistic argument needs a stronger Lemma 2 than the one stated.
   This is a proof gap; the statement is true.**
   - Lemma 2 gives a set `V` per process, depending on the process's DAG when it completes the
     wave. The coin is revealed once `f + 1` processes call it, so after the *first* correct
     process completes the wave. Other correct processes complete it later, and by then the
     adversary may know the leader.
   - What is needed is a set fixed *before* the reveal that every later round-4 vertex
     (including Byzantine ones created afterwards) reaches. We prove such a set exists:
     `core f C w E3` = the sources strongly reached by `≥ f + 1` of any `2f + 1` existing round-3
     vertices `E3`.
     - It has `≥ 2f + 1` members (`core_card`, by double counting rather than the paper's
       informal mapping to the common-core protocol).
     - Every round-4 vertex with `2f + 1` strong edges reaches all of it (`sPath_of_mem_core`).
     - It is determined by the strong past of `E3` (`core_congr`).
   - The paper's Lemma 2 follows (`lemma2`).
4. **Claim 2's proof ("by induction on rounds") is unsound as written. The statement is true.**
   - Line 25 checks only the number of strong edges. A Byzantine vertex may have weak edges to
     vertices of the same or a higher round, so predecessors need not have smaller rounds.
   - The proof also silently assumes that every correct process eventually reaches the vertex's
     round. That is round liveness, which the paper never proves and which itself needs
     Claim 2.
   - We prove round liveness and Claim 2 jointly: induction on rounds, with an inner strong
     induction on the *time* at which the vertex was added (`roundLive_succ`,
     `histLive_of_roundLive`, `claim2`, `round_liveness`).
5. **Proposition 4 (Validity): the proof skips a step. The statement is true.** Weak edges only
   ensure that vertices created by *correct* processes after time `T₀` reach `v`. A committed
   leader may be Byzantine. The missing step: every vertex of round `≥ R₀ + 1` has `2f + 1` strong
   edges, so it has at least one strong edge to a correct vertex of round `≥ R₀`, which reaches
   `v`. Here `R₀` exceeds all correct rounds at `T₀`. (`run_validity`, internal lemmas A/B.)
6. **The RBC specification lacks authenticity.** The paper's Integrity says only "at most once
   per `(r, k)`". Validity also needs the standard property that a correct process delivers a
   message of a correct sender `k` only if `k` broadcast it. Otherwise the contents of a correct
   process's vertex could be forged. We assume it (`Run.Valid.auth`). Classification: missing
   (standard) assumption.
7. **Claim 6 arithmetic.** With success probability `2/3 − ε` per wave the expectation is
   `1/(2/3 − ε) = 3/2 + 9ε/(4 − 6ε) + …`, not `≤ 3/2 + ε`. We prove `≤ (3f+1)/(2f+1) ≤ 3/2` for a
   perfect coin (`ε = 0`). Classification: typo-level imprecision.
8. **Pseudocode slips.**
   - Line 7 requires predecessors in `⋃_{k ≥ 1} DAG[k]`. Read literally, round-1 vertices, whose
     strong edges point to the genesis `DAG[0]`, could never be added. We use `k ≥ 0`.
   - Algorithm 2 signals `wave_ready(0)` at `r = 0`, and `round(0,1) = −3`. This is harmless (no
     commit) and omitted.
   - Line 25 checks only `|v.strongEdges| ≥ 2f + 1`. The prose (Section 4) also requires the strong
     edges to point to round `r − 1`. Without that check a Byzantine leader of wave `w' > w` could
     point to round 1 directly, bypass a directly committed leader `v` of wave `w`, and break
     total order. Our model encodes strong edges as sources of round `r − 1` (the prose version).
     This attack is not formalized.

   Classification: typos / under-specified pseudocode.
9. **Minor.** Claim 7's proof ("when it delivers `v` to itself, it adds `v`") ignores the buffer and
   round conditions of lines 6–7. They hold eventually by round liveness (`claim7`).

## Modelling choices (formalization vs. paper)

- **Non-equivocation is built in.** Vertices are identified by `(round, source)`, and all contents
  come from one global `Content`. This is the consequence of RBC Agreement + Integrity on infinite
  runs that the paper uses.
  - Safety (`Safety.lean`, `ChainQuality.lean`) is proved for *arbitrary* closed and valid local
    DAG snapshots. It needs no assumption on schedules, on the relation between processes, or on
    the number of Byzantine processes. Only `n ≤ 4f + 1` is used for total order; the paper has
    `n = 3f + 1`.
- **Ordering layer.** Algorithm 3 is a deterministic function of the snapshots at `wave_ready(w)`,
  `w = 1, 2, …` (`orun`). "Some deterministic order" is an arbitrary function `sortV` listing each
  finite set once (`SortSpec`).
- **DAG layer** (`DagLayer.lean`), asynchronous:
  - Each step of a correct process is one iteration of the main loop, after an
    adversary-chosen batch of RBC deliveries. A buffered vertex is added only if its predecessors
    were already present *before* the iteration; the paper's sequential for-loop can add a chain
    in one pass. This only delays additions (stuttering).
  - RBC Validity, Agreement and Authenticity are hypotheses of `Run.Valid`. Their satisfiability
    is shown by a lock-step run (`NonVacuity.lean`).
  - Weak edges of correct vertices are specified by their effect, "a path to every DAG vertex of
    round `≤ r − 2`", which `set_weak_edges` produces. Any such set is allowed.
- **Byzantine set.** It is static (fixed in the run). The paper allows adaptive corruption.
  Safety does not depend on it. For liveness, the theorems are about processes that are never
  corrupted.
- **Blocks.** Correct process `p` puts block `blk p r` into its round-`r` vertex. This is the
  paper's assumption that every process `a_bcast`s infinitely many blocks with consecutive
  sequence numbers. `a_deliver(m, r, k)` is represented by outputting the vertex id `(r, k)`; its
  block is `C.block (r, k)`.
- **Probability.**
  - Agreement and Validity are proved under the deterministic hypothesis "infinitely many good
    waves" (`Run.GoodWave`).
  - Claim 6 is proved in an abstract coin game (`Cslib/Probability/CoinGame.lean`, specialised in
    `Coin.lean`): perfect uniform coin (`ε = 0`), and
    an adaptive deterministic adversary whose good set for wave `i` is a function of the earlier
    coins.
  - The link between the two (the good set is the robust core, fixed before the coin is
    revealed) is the content of `goodWave_of_core` + `core_congr` + `core_card`.
  - What remains informal is identifying the execution's probability space with the coin game:
    the adversary's choices before the reveal of coin `w` depend only on coins `< w`, which is
    the coin's unpredictability.
- **Expected waiting time.** It is proved for every finite horizon `K`; the untruncated bound
  follows by monotone convergence (not formalized).

## Not formalized

- Communication and time complexity (Section 6.2, Table 1), and post-quantum safety. These are
  cryptographic or engineering claims.
- The threshold-signature coin implementation (Section 2).
- The total-order attack enabled by the missing round check of line 25 (item 8, third bullet), which is described only in
  words.
