# Differences between the formalization and the paper

Paper: Ben-David, Dzulfikar, Ellen, Gilbert, *Byzantine Agreement with Predictions*, PODC 2025
(arXiv:2505.01793v1; numbering follows the arXiv version, whose Theorems 13/14 are the PODC
paper's lower bounds).

**Summary.** No main result is false.
- The message lower bound (Theorem 14) and the round lower bound (Theorem 13, unauthenticated
  algorithms) are proved as stated. Theorem 13's proof cites a crash-fault bound that is valid for
  halting times (the paper's literal measure) but not for decision times. We prove the stronger
  decision-time version by reducing to the Byzantine model and proving the cited early-deciding
  bound there.
- The conditional algorithms (Theorems 5 and 6) and the classification lemmas (Lemmas 1–6) are
  correct. Lemma 23 has a fixable proof gap. Lemmas 5 and 6 hold under weaker hypotheses.
- The wrapper (Algorithm 1, Lemmas 28–33) is verified against the specifications of the cited
  sub-protocols, which are not themselves formalized.
- The rest are under-specified details, typos and loose asymptotic statements.

## 1. Lower bounds (Section 10)

1. **Theorem 13: the cited bound covers halting, not decision times (imprecision, statement true).**
   - **What the proof does.** It simulates the predicted algorithm `A` by an algorithm `S'`
     without predictions on `n' = n − x` processes "at most `t'` of which may fail by
     crashing". Then it invokes [21] (Dolev–Reischuk–Strong): every algorithm has an execution
     with `f'` faults taking `min{f'+2, t'+1}` rounds.
   - **When this is correct.** For crash faults, `min{f+2, t+1}` is the DRS bound on *stopping*
     (all correct processes halt). It is also the bound on deciding for *uniform* consensus
     (Charron-Bost–Schiper, Keidar–Rajsbaum). The paper says `A` "terminates within `T(f)`
     rounds" and that rounds "are performed", and [21] is about early stopping. Read as halting
     time, the proof is correct.
   - **When it is not.** If the measure is the round in which the last honest process *decides*,
     the crash reduction does not suffice. `S'` inherits only agreement among correct processes,
     and non-uniform crash consensus can decide in `f + 1` rounds. Example with `n = 3`, `t = 1`:
     every process relays all inputs it knows for `t + 1` rounds. A process that received all `n`
     inputs in round 1 decides their minimum at once; the others decide the minimum they know at
     round `t + 1`. This is correct against one crash. Every failure-free run decides at round
     `1 = f + 1 < min{f+2, t+1} = 2`. It is consistent with the classical `t + 1` bound, which
     concerns runs with `f = t`.
   - **What we prove.** We formalize the decision-time version, which is stronger: an honest
     process cannot halt before deciding. The simulation works verbatim for Byzantine `S'`:
     Byzantine `q_i` sends the messages of Byzantine `p_i` (`simProtocol`,
     `solves_simProtocol`, `roundLowerBoundWith`).
   - **The cited bound is proved, not assumed.** We prove the Byzantine early-deciding bound
     `min{f'+2, t'+1}` for `n' ≥ t' + 2` and at least two values (`earlyDecidingLB_strong`,
     `drsBound`). The classical chain argument over send-omission runs gives `f' + 1`
     (`earlyDecidingLB_weak`). The extra round comes from one more process, which equivocates in
     the last round (`sameVal_hybrid`); this is possible because `f' < t'`.
   - **Result.** Theorem 13 holds as stated, for decision times, for unauthenticated algorithms
     (`theorem13`).
   - **Scope.** `theorem13` uses CSLib's unauthenticated `LockStep.Solves`. Algorithms with
     signatures are not covered. These matter for `n/3 ≤ t < n/2`, the regime of Theorems 6 and 12.
     For `n ≤ 3t` the hypothesis of `theorem13` is unsatisfiable.
   - We did not formalize the crash-model example above; it is a remark about the citation, not
     about the theorem.
2. **Theorem 13: "an execution with `f` faults" needs padding (imprecise proof).** The cited
   bound produces an execution with *at most* `f'` faults. To get exactly `f` faulty processes we
   declare extra processes Byzantine that behave honestly (`padScenario`). This needs a spare
   process other than the slow one, which `f ≤ t < n − 1` provides. We also note:
   - Theorem 13 implicitly needs at least two values: with one value, deciding at round 0 is
     correct.
   - "At least `R` rounds are performed" is formalized as "some honest process has no output
     after `R − 1` rounds".
3. **Theorem 14: proof gap in the "without loss of generality `|S₀| ≥ ⌈(n−1)/2⌉`" step
   (statement true).**
   - **The gap.** `S₀`/`S₁` are defined as the processes that decide 0/1 for *some*
     prediction "when they receive no messages". A process need not decide at all when it
     receives nothing, since such a run need not be an admissible execution. So the sets need not
     cover the non-senders.
   - **Fix.** We fix one pretended input and split the processes by whether their isolated run
     ever decides `v₁`. Processes that do pretend to have the honest value `v₀`; processes that
     do not pretend `v₁`. Both cases give a contradiction in `E_bad` (`t_sq_om`).
4. **Theorem 14 is proved directly for agreement and for broadcast.**
   - The paper proves it for Byzantine broadcast and says "this implies the same bounds for
     Byzantine agreement". The `O(n)`-message reduction only transfers the `t²` part; the
     `Ω(n)` part needs its own argument.
   - We prove both problems directly: agreement (`message_lower_bound`,
     `message_lower_bound_classification`) and broadcast (`message_lower_bound_bb`).
   - The explicit bound is `n + t² ≤ 8·#messages + 1`.
   - The faulty processes of `E_good` ignore *all* messages, not only the first `⌊t/2⌋`. This is
     equivalent, because messages sent are counted, not received ones.
   - The bound holds for any prediction type in which honest processes can receive correct
     predictions, with or without signatures, and for any delay bound `δ`.
5. **The abstract and introduction of arXiv v1 state Theorem 14 loosely (imprecise claim).**
   - They state an `Ω(n²)` lower bound, as does the first paragraph of §10.2. The theorem proves
     `Ω(n + t²)`, which is weaker when `t = o(n)`.
   - `Ω(n + t²) = Ω(n²)` when `t = Θ(n)`, the usual convention for Dolev–Reischuk (which
     the paper itself quotes as `Ω(n²)`). Read literally, `Ω(n²)` is false for small `t`. For `t = 0`, "send your value to `p₁`; `p₁` broadcasts the
     minimum" uses `2(n−1)` messages.
   - The PODC abstract states `Ω(n + t²)`.
   - Not formalized beyond Theorem 14 itself.

## 2. Classification and orderings (Section 6)

6. **Lemma 1** is proved in exact form: `k_A · (⌈n/2⌉ − f) ≤ B` (`card_mis_mul_le`). The `O(B/n)`
   statement follows for `f ≤ (1/2 − ε)n`. Observations 1 and 2 are merged into `obs12`.
7. **The position formula has a typo.** For `c[i] = 0` the paper writes position
   `n − f + i − Σ_{j≤i} c[j]`. It should be `Σ_j c[j] + i − Σ_{j≤i} c[j]`; `n − f` is only right
   for `c = ĉ`. The second form `i + Σ_{j>i} c[j]` is correct. Our `pos` is defined directly.
8. **Lemma 5 is proved under weaker hypotheses.** We only need `1 ≤ ℓ` and `r ≤ n − |F|`, with
   the same size `r − ℓ + 1 − k_A` (`lemma5`). The paper's proof is index-heavy and hard to
   check; ours uses `rank U j ≤ pos(c_i, j) ≤ rank W j` (`pos_mem_Icc`), where `U` are the
   properly classified honest processes and `W = U ∪ mis`.
   - Brute force over all instances with `n ≤ 8` found no counterexample to the paper's
     version.
   - `ℓ ≥ 1` is needed: positions are 1-indexed.
   - Lemma 6's hypothesis `r ≤ n − t − k_H` is not needed either.
9. **Lemma 6 is stated ambiguously.** "The number of honest processes `p_i` such that
   `i ∈ {π(c_i)[j] | j ≤ r}`" is used in two ways:
   - Theorem 5 uses it for a process in its *own* ordering;
   - Lemma 24 uses the union over all honest orderings.

   We prove the union version (`lemma6`), which implies both.
10. Lemmas 2–4 and Corollary 1 are `pos_mem_Icc`, `pos_gt_of_false`, `lemma4`/`lemma4'` and
    `corollary1`. Lemmas 15 and 19 (a phase with only honest leaders) are combined into
    `exists_clean_block`, a general pigeonhole statement about blocks of positions.

## 3. The unauthenticated conditional algorithm (Section 7)

11. **Algorithm 4 line 4 has a typo.** It reads `y ∈ L_y`; it should be `y ∈ T_i`. Also
    `m_i[z]` is undefined for `z ∉ T_i`, but only `z ∈ T_i ∩ L_i` is used.
12. **Under-specified details**; we fix choices, and the results hold for every choice.
    - Algorithm 3 line 14 may have several values with `≥ k+1` copies; any choice works.
    - Lines 4–5 have a unique value with `≥ 2k+1` copies only when `|L_i| ≤ 4k+1`.
    - Conciliation paths include the trivial path (`z` reaches itself).
    - When `T_i ∩ L_i = ∅`, conciliation returns the process's own value; this cannot happen
      under the core-set assumption.
    - Ties in plurality votes are broken arbitrarily.
13. **We model no early return.** In Algorithm 5 a process returns one phase after deciding. In
    our model processes keep running to round `5(2k+1)`. The output is set when the process
    decides (line 12), or at the end (line 14), and never changes (`dec_mono`). This only adds
    honest participation, and the outputs are the paper's return values. The message bound is
    proved for this version and matches the paper's: each honest process broadcasts only in the
    phase where it is its own listener.
14. **Algorithm 3 is proved under weaker assumptions.** The paper's precondition
    `|L_i| = 3k + 1` is replaced by `|L_i| ≤ 3k + 1` (`CoreSet`).
15. **Lemma 16, `k = 0` (imprecise).** It says the processes return "at the end of phase 2", but
    for `k = 0` there is only one phase. Lemma 17's "no honest process returns before phase
    `φ+1`" should be "before the end of phase `φ+1`".
16. **An informal remark of §7 is false (not used anywhere).** The introduction of Section 7
    says "if the number of misclassified processes is larger than `k` … if any honest process
    decides, then they all decide".
    - **Counterexample.** Take `k = 0`, so there is one phase with singleton listening sets.
      Suppose honest `p_i` ranks the faulty `q` first and honest `p_j` ranks the faulty
      `q' ≠ q` first. `q` sends `v` in all rounds, so `p_i` gets grade 1 twice and decides `v`
      at line 12. `q'` stays silent, so `p_j` never gets grade 1 and only returns its own value
      at line 14.
    - This is outside the theorem's hypotheses. Algorithm 1 only uses that the conditional
      algorithm terminates within its time limit. Not formalized.
17. The Section 7 introduction states the hypothesis as `(2k+1)(3k+1) + k ≤ n − t`, Theorem 5
    as `(2k+1)(3k+1) ≤ n − t − k`. They are equivalent.

## 4. The authenticated conditional algorithm (Section 8)

18. **Lemma 23 has a proof gap (statement true).**
    - The proof says that if `p_i` received a valid chain for `x` during the first `k` rounds,
      then `p_i` broadcast a chain for `x`. But `p_i` relays only values it *adds*: not when
      `x ∈ X_i` already, nor when `|X_i| = 2`.
    - **Fix.** Argue from the round in which `x` first entered `X_i`: `p_i` relayed it then,
      unless `|X_i| = 2` already, in which case `p_j` also ends with two values (`lemma23_core`,
      `spread`).
19. **"Faulty `p_j` has a committee certificate" is under-specified.** Lemma 24 needs: a
    process can present a certificate only if some honest process voted for it. We use the set
    `Csup` of processes with at least one honest vote (`mem_Csup`). It contains every process
    that can produce a certificate, and Lemma 24's bounds are proved for it (`lemma24_faulty`,
    `lemma24_card`).
20. **`n − t ≥ t + 1` is really needed** for `|C ∩ H| ≥ k + 1` (`lemma24_honest`). A core-set
    process gets votes from all `n − t` honest processes and needs `t + 1` of them. This is the
    `t < n/2` hypothesis of Theorem 6, so the theorem is fine.
21. **Under-specified defaults.** Line 10 is undefined if all broadcast outputs are `⊥`, and
    line 13 if `V_i` is empty. Neither happens under the hypotheses; we default to the process's
    own input. Chains carrying the receiver's own signature are not discussed; we filter them
    out, which is equivalent under unforgeability.
22. **Typos.**
    - Theorem 6 says "Algorithm 5" for Algorithm 7.
    - Algorithm 7 line 8 passes `v_i` for `x_i`.
    - Algorithm 6 line 13 writes `x_m`.
    - The §8.3 prose says `2k + 1 < n − t − k`; Lemma 24 and Theorem 6 use `≤`.
23. **Message bounds.**
    - Theorem 6's per-process bound `2k + 1 + n + 2n|C| < 2n(|C| + 1)` fails for `n = 1`
      (degenerate case).
    - We prove `≤ 2k + 1 + n + 2n²` per honest process with no hypotheses
      (`theorem6_messages_per_process`).
    - We prove `≤ n(2k+1) + (3k+1)·n(6k+3) = O(nk²)` in total under the hypotheses
      (`theorem6_messages`). A message is a bundle of chains sent to one receiver in one round.
24. **Signature modelling.**
    - Signatures are CSLib's abstract unforgeable tokens.
    - A certificate carries all received votes (not just `t + 1`).
    - A chain link signs `(value, sender)` but not the whole prefix. This gives the adversary more
      freedom, so the correctness results are, if anything, stronger.

## 5. The wrapper and the main theorems (Sections 5 and 9)

25. **Algorithm 1 is verified at the level of sub-protocol specifications.**
    - Graded consensus is cited ([14], [37]) and so is early-stopping agreement ([32]; Theorem 10
      is "not formally proved" in the paper). We do not implement them.
    - We verify the logic of Algorithm 1 (Lemmas 28–32) on abstract phase traces, in which every
      sub-protocol output is arbitrary subject to its specification (`Wrapper.Trace.Valid`).
    - The conditional algorithms enter through their specifications (Agreement and Strong
      Unanimity when the precondition holds). These are exactly what Theorems 5 and 6 provide.
      The formal composition of round algorithms with time limits is not done.
    - Lemma 33's round count is exact: `roundsUpTo`, `rounds_le`.
    - The final `O(min{B/n, f})` claims of Theorems 11 and 12 are assembled in prose, from
      Lemma 1, `theorem11_rounds` and `exists_pow_two_between`.
26. **In the abstract trace all honest processes run all phases.** In Algorithm 1 a process
    stops one phase after deciding. Our proofs only inspect phases up to one phase after the
    first decision, in which nobody has stopped yet.
27. **Asymptotic statements are loose.**
    - Theorem 2 says `O(min{B/n + 1, f})` rounds, Theorem 11 `O(min{B/n, f})`, Theorem 3
      `O(min{B/n, f})`. The `+1` is needed when `B < n`.
    - "`O(n² log(min{B/n, f}))` messages" should read `log(min{B/n, f} + 2)`, since the log
      is 0 or undefined for small arguments.
    - The phase count `⌈log₂ t⌉ + 1` is undefined for `t = 0`.

## 6. Modelling choices

- **Lower bounds.**
  - Theorem 14 is proved in CSLib's synchronous Byzantine model (`PartialSync` runs with
    `gst = 0`), via the omission model `OmExec`.
  - Theorem 13 is proved in CSLib's lock-step model (`LockStep`, complete graph, reliable
    channels).
  - Both have deterministic processes and a static Byzantine set.
- **Upper bounds.**
  - The algorithms are CSLib round algorithms (`RoundAlgorithm`) verified against synchronous
    abstract round executions (`RoundRun` with `SyncFrom 0`). Signatures use CSLib's token model
    (`RoundAlgorithm.Unforging`, `RoundRun.AuthValid`).
  - Inputs are `(value, classification vector)`. Algorithm 2 (voting) is analysed as a round on
    its own (`classify`, `card_mis_mul_le`). The conditional algorithms take the resulting
    vectors `c_i` as inputs.
- **Predictions.** Classification predictions are `P → Bool` per process (`true` = predicted
  honest). `B` counts only bits given to honest processes (`wrongBits`), as in Section 3.
