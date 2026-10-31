# Differences between the formalization and the paper

Paper: Z. Xiang, N. H. Vaidya, *Partially Replicated Causally Consistent Shared Memory: Lower Bounds
and An Algorithm* (brief announcement, PODC 2018), full version arXiv:1703.05424v3 (29 May 2019);
numbering follows the full version.

## Errors in the paper

1. **Lemma 4 is false** (Appendix B; a numbered lemma ⇒ statement, rule R1; not a headline ⇒ ❌).
   It claims: if `u'` (from `k` to `i`, timestamp `T'`) happened before `u` (from `j` to `i`,
   timestamp `T`), then `T[e_ki] ≥ T'[e_ki]` (`k ≠ j`).
   * As stated it is ill-typed when `e_ki ∉ E_j` (then `T` has no entry `e_ki`); random testing
     (`modelcheck/lem4.py`) shows that this case occurs constantly. If the missing entry is read as
     `0`, the lemma is false there.
   * It is also false when `e_ki ∈ E_j`, the only reading under which it is well-typed:
     `Lemma4.lemma_4_false` / `Lemma4.not_lemma4Statement` (`Lemma4.lean`). Replicas
     `A, B, C, D, I` with `X_A = {f, e, b}`, `X_B = {e, a}`, `X_C = {a, g}`, `X_D = {g, b}`,
     `X_I = {f, a, g}`. `A` writes `f` (`u'`), then `e`; `B` applies and writes `a`; `C` applies and
     writes `g`; `D` applies and writes `g` (`u`). Then `u' ↪ u`, `e_AI ∈ E_D` (triangle `D, I, A`),
     `e_AI ∉ E_C` (since `X_C ⊆ X_I`, condition (iii) fails for every loop through `C`), and
     `T[e_AI] = 0 < 1 = T'[e_AI]`.
   * The intended use survives: Lemma 5 and Theorem 3 are true (`lemma_5`, `theorem_3_safety`). In
     the example `I` cannot apply `u` before `u'` because `B`'s and `C`'s updates (on `a`, `g`) also
     go to `I` and must be applied first.
   * The proof of Lemma 4 also assumes that a causal chain from `k` to `j` together with `i` forms a
     *simple* loop (chains may revisit replicas or pass through `i`), and it applies the induction
     hypothesis to loops whose replicas do not carry `e` either.

2. **Proof of Lemma 5 (and hence of Theorem 3) has a gap** (🛠️ for the theorem; the gap is the use
   of Lemma 4). Lemma 5's proof uses `T[e_ki] ≤ τ_i[e_ki]` from the predicate of Step 4, which only
   checks edges in `E_i ∩ E_j`, together with Lemma 4. Our replacement (`Chain.lean`,
   `chain_main`): strong induction on the length of a causal chain `a ↪ v₀ ↪ ⋯ ↪ v_m = u`.
   * A replica occurring twice ⇒ shorten the chain.
   * An intermediate update on a register of `X_i` ⇒ it is applied at `i` first (induction), and so
     is `a` (safety of the earlier step).
   * Otherwise either every replica of the chain has `e_ji ∈ E_{p_q}` and the counter is carried to
     `u`'s timestamp, or the chain plus `i` is a simple loop that is not a `(p_q, e_ji)`-loop. Each of
     the three failing conditions of Definition 6 then yields an update of the chain (or `a`) that is
     sent directly to a later replica of the chain, i.e. a shorter chain.

3. **Footnote 2 is false** ("our proposed algorithm in Section 3.2 actually satisfies this
   constraint", i.e. Constraint 1: the timestamp is a function of the causal past *set*). Explicit
   claim in the text about the paper's algorithm (R1), not a headline ⇒ ❌.
   `Footnote2.footnote_2_false`: six replicas, `X₀ = {e, b}`, `X₁ = {a, b}`, `X₂ = {a, c}`,
   `X₃ = {c, d}`, `X₄ = {e, d}`, `X₅ = {c, e, d}`. In two executions replica `0` ends with the same
   causal past `{u_c, u_d, u_e⁴, u_e⁵}` (one update per writer), but `τ₀[e_25] = 1` in one and
   `0` in the other. `e_25 ∈ E₀`, `e_25 ∉ E₄`, and `u_c` reaches `0` either through `5` (tracks
   `e_25`) or only through `4` (does not). Consequence: the lower bound of Section 4 (which assumes
   Constraint 1) does not in general apply to the paper's own algorithm. The special cases where
   the paper claims tightness (trees, cycles, full replication) are not formalized.
   * *Identity of updates (borderline reading, recorded per R6).* Updates are identified across
     executions by issuer, register and (unique) value, not by the attached timestamp `T`. If the
     message tuple `update(i, T, x, v)` (with `T`) were the identity, footnote 2 would be true:
     `τ_i` is the entrywise max of the timestamps of the updates applied at `i`, and by safety these
     are exactly the members of the causal past on registers of `X_i`. That reading does not fit
     Section 4. The paper calls the causal pasts produced by different executions (with
     algorithm-dependent timestamps) "identical" (Appendix D, Cases 1–2), and its conflict graph
     `H_i` is meant to be independent of the algorithm. So we use the value-based identity.
   * Footnote 2 does not decide the verdict: Lemma 4 already gives ❌, and neither is a headline.

## Theorem 1 (necessity)

Statement true; proof repaired (🛠️). Formalized as `Necessity.theorem_1` (`Necessity/Theorem1.lean`).

* **Class of algorithms.** "Implements causal consistency by storing and attaching metadata … when
  to apply is determined only using the local metadata and the attached metadata" is formalized as
  deterministic metadata algorithms (`Necessity.Alg`). The decision may also see the sender and the
  register, and the full metadata is attached (attaching a function of it is a special case).
  In this respect the class is larger, so the result is stronger. Two implicit restrictions:
  replicas are deterministic, and their metadata changes only on a write or an apply (receipt
  is merged into apply; there are no other messages). The paper's model (Section 2: replicas
  exchange only update messages and decide when to apply them) does not mention other algorithms.
  Its proof of Theorem 1 (and of Lemma 2) also treats the timestamp as fixed by the writes and
  applies. We judge the class faithful.
  `Implements` = safety in every reachable state and liveness (Definition 5) in every weakly fair
  execution. The paper's algorithm is in the class and implements causal consistency
  (`Necessity.paperAlg_implements`), so the hypothesis is satisfiable.
* **Obliviousness.** The paper's definition quantifies over graphs `R₁, R₂` with `R₀ < R₁`,
  `R₀ < R₂`, where `<` ranges over arbitrary executions passing through `R₀`. We fix a state `s₀`
  and quantify over its extensions (`Necessity.Oblivious`). This is a weaker hypothesis, so the
  theorem is stronger. Updates are identified across executions by (value, issuer, register), using
  the paper's unique-value assumption. "Differ only in updates on `e_jk`" (`DiffOnly`) is the
  paper's (i) and (ii).
* **Which `R₀`.** The theorem says "must not be oblivious" without fixing `R₀`; the proof
  (Appendix A) starts from an execution in which all issued updates have been applied. We prove it
  for every reachable *quiescent* state `s₀` (`Quiescent`). `[Fintype ι]` (finitely many replicas)
  is assumed, as in the paper (`R` replicas).
* **Gap in Case 2.** "`R₁` and `R₂` only differ in updates on `e_ji`" is false in general: applying
  `u₁` also brings `j`'s causal past (which may contain updates on other edges) into `i`'s graph.
  Repair: a pre-phase in which `j` writes and `i` applies, then the paper's argument with two
  further updates `u_A, u_B`.
* **Gaps in Case 3.** The proof says all other messages are "delayed indefinitely", but its liveness
  arguments then fail, because postponed dependencies are never applied. Moreover an earlier update
  `u'_p` of the path `l₁ … l_s` may already be sent to `l_s`, and in Case 3.2 the execution without
  `u₀` loses `j`'s causal past, so the two graphs differ by more than `u₀`. Repair: both executions
  share `j`'s first update `u_A`, which `k` applies. Execution E1 adds one more update `u_B` of `j` on
  the same register. Every intermediate replica applies *all* updates sent to it (a deterministic
  closure, which liveness forces to succeed). The critical update is the first `u'_p` whose register
  is stored at `k`. The two executions are compared by an explicit simulation (`LogSim`, `MdSim`).
* The paper's informal "timestamp" is the whole metadata of the replica.

## Modelling choices (all statement-level choices are faithful or more general)

* **Execution model.** Asynchronous, reliable, non-FIFO channels, no failures. A received update
  sits in `pending_i` until the predicate of Step 4 holds; we merge "receive" into "apply": an update
  may be applied at any time after it was issued. This gives exactly the paper's set of behaviours
  (any delivery order and delay). Liveness assumes weak fairness: an update that stays applicable is
  eventually applied (`Execution.Fair`). This encodes reliable channels plus "the replica performs
  Step 4 when the predicate holds".
* **Values and reads are omitted.** Neither affects updates, timestamps or Definition 5.
* **`↪` (Definition 4)** is defined through ghost data: each update stores the set `pre` of updates
  applied at its issuer before it was issued (condition 1), and `HB` is its transitive closure
  (condition 2). The issuer's own write counts as "applied" at the issuer, as in the algorithm
  (Step 2(a)).
* **Timestamps** are stored as total functions `ι → ι → ℕ`; the algorithm only reads and writes
  entries in `E_i` (entries outside stay `0`). The predicate `τ_i[e_ki] = T[e_ki] − 1` is written
  `τ_i[e_ki] + 1 = T[e_ki]` (equivalent, since `T[e_ki] ≥ 1` for an update of `k` sent to `i`).
* **Definition 6 (loops)** is formalized with lists `l = [l₁, …, l_{s−1}]`, `r = [r₂, …, r_t]`;
  `l_s = k`, `r₁ = j`, `r_{t+1} = i`; simplicity is `Nodup`, adjacency is `List.IsChain Adj`.
* **Safety (Definition 5)** is stated for every reachable state; liveness as
  `theorem_3_liveness` (applied within finite time after all dependencies are applied) and the
  corollary `eventually_applied` (every update is eventually applied at every replica storing its
  register).
* **Lemma 3** is formalized as stated (`lemma_3`); internally we prove the stronger invariant that
  replica `i` has applied exactly the first `τ_i[e_ji]` updates on `e_ji` (`Inv.count`).

## Not formalized

* Lemma 2 and Theorem 2 (timestamp-space lower bound `σ_i(m) ≥ χ(H_i)` under Constraint 1).
  "Possible causal past", the identity of updates across executions and the spanning-tree
  constructions of Appendix D are informal. Theorem 2 is a one-line consequence of Lemma 2 (a
  colouring argument). The "Implication" bullets (trees, cycles, full replication) are stated
  without proof.
* Section 3.3 (comparison with Hélary–Milani), Appendix C (numerics), Appendix E (optimizations),
  Section 5 / Appendix F (client–server architecture, Theorem 4).
