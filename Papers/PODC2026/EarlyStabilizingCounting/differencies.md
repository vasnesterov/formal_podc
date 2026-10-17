# Differences between the formalization and the paper

Lenzen, Loss, *Early-Stabilizing Counting*, PODC 2026 (arXiv 2605.18171v1). Numbering follows the
arXiv version.

## Errors in the paper

1. **Algorithm 1, line 3: input `C_v + R` is off by one (statement false for the literal pseudocode;
   typo-level fix).** By Section 4, round 1 of an `R`-round subroutine is computed from its input, and
   Algorithm 1 runs round 1 of a new instance in the round in which it is started (the loop
   `for r ∈ {R,…,1}` follows line 3). So an instance started in round `r` (input read from
   `C_{v,r−1}`) executes its round `R` in round `r + R − 1`. Line 7 then overwrites `C_v` with the
   output, and line 15 increments it once more. An agreed output `C_{v,r−1} + R` therefore gives
   `C_{v,r+R−1} = C_{v,r−1} + R + 1`. This does not depend on how rounds are labelled: there are `R`
   updates of `C_v` between reading the input and writing the output, and the proof of Lemma 5.4
   ("outputs in round `r + R`") needs `R + 1`. The paper is not consistent about this: Lemma 5.6 uses
   `J_ℓ` with `R` rounds, and Algorithm 7, line 19 uses input `C_v + R − 1` read after the increment
   of line 11 (correct with the pipeline timing), while Algorithm 7, line 2 repeats `C_v + R` (Section 7
   is not formalized). As written, the algorithm never counts. Every instance with an agreed correct
   leader (one every `k_b` rounds once a filtered clock counts) makes the clock jump by 2. Lean:
   `literal_breaks` (trace level, any `D`, independent of `k₀`, `k₁`, `X`), `literal_never_counts`
   (no fault-free execution of the literal algorithm ever stabilizes, for any early-stabilizing
   sub-counters, `n ≥ 2`, `C ≥ 2`; instantiated with our constants), `literal_counterexample` (with the
   sub-counters of `corollary_5_8`). Fix used everywhere else: input `C_v + R - 1` (`tmpl 2`, `R = 3`).
2. **Lemma 2.3 vs Definition 2.2: Algorithm 8 gives crusader agreement only over `X` rounds, not
   `X + 1` (proof error: the algorithm of the proof does not meet the definition; harmless
   downstream).** Lemma 2.3 itself is an existence claim, which we do not refute. Definition 2.2 requires
   `F_{w,r̂} ∈ {F_{v,r'} + r̂ − r', ⊥}` for `r̂ ∈ {r', …, r' + X}`. Algorithm 8 resets the cooldown
   to `X`, so two correct nodes can output inconsistent values `X` rounds apart. Counterexample:
   `n = 4`, one Byzantine node, `X = 1`, `K = 2`. At time `3 = X + 2`, node 0 outputs `1`. At time
   `4`, node 1 outputs `1`, although only `⊥` or `0` is allowed. The Byzantine node gave node 0 a
   quorum in round 3 but not node 1, so node 1's chain restarted one round later. Lean:
   `filt_crusader_window_false`. Proved instead: window `X − 1`, i.e. `r̂ ∈ {r', …, r' + X − 1}`,
   from time `X` (`filt_crusader`). Algorithm 5 (reset to `X + 1`) is consistent with the
   definition. Lemmas 5.2 and 5.6 only use windows of length `≤ X − 1`, so nothing downstream
   breaks.
3. **Lemma 5.5: the constants in the proof are wrong for some `ε` (proof gap, statement true).**
   The proof picks `k₀ = ⌈(R+1)/ε⌉`, `k₁ = k₀ + R + 1` and claims that after a colliding `L` the
   next `⌈1/ε⌉ − 1` values do not collide. This fails for `ε = 2/3`, `R = 1` (`k₀ = 3`, `k₁ = 5`):
   for `b = 1`, `o = 0`, both `L = 0` and `L = 1` collide (`[0,1] ∋ 0`, `[5,6] ∋ 6`). With
   `L ∈ {0,…,L_max}`, as Lemma 5.6 uses it, the count `2` exceeds `ε·1 + 1`. Lean:
   `lemma_5_5_proof_constants_fail`. The lemma holds with `k₀ = (R+1)⌈1/ε⌉`, `k₁ = k₀ + R + 1`
   (`lemma_5_5`, via the separation lemma `collides_sep`). For `ε = 1/4`, the only value the paper
   uses, both choices coincide.
4. **Lemma 5.6: proof gaps (statement true).**
   * "`L_max := ⌊(X−R)/k_b⌋ − 1 > 4`" is false for the `b` with `k_b = max{k₀,k₁}`: there
     `L_max = 4`, and the final count `L_max/2 − L_max/4 − 1 > 0` becomes `0`. It can be repaired by
     exact counting over the `L_max + 1` leaders.
   * Conditions (ii)–(iii) for `i₀` ("no overflow during `I_{i₀}`", "fewer than half of the leaders
     faulty") need `n` to be large. Footnote 8 admits this and proposes to change the algorithm
     (clocks modulo `m k_b n`) for small `n`. We prove the lemma for **all** `n` and the
     **unmodified** algorithm with a different counting argument. Group the `b`-instances into
     blocks of 4 consecutive leaders. By Lemma 5.5 at most one instance per block collides with the
     other schedule. Among the first `4(f+1)` leaders (consecutive modulo `n`), at most
     `f(⌊4(f+1)/n⌋ + 1) < 3(f+1)` are faulty, so some block contains an unimpeded instance.
     (`lemma_5_6`)
5. **Corollary 5.8, recursion step (proof gap, statement true).** The proof uses "in each step
   either `V₀` or `V₁` contains at most half of the faulty nodes". The time bound of Theorem 5.7,
   however, needs a part with `f_b < |V_b|/3`, and the part with at most half of the faults need not
   have this. Example: `n = 7`, `|V₀| = 3`, `|V₁| = 4`, one fault in each part; `V₀` has at most half
   the faults but `1 ≥ 3/3`. For the balanced partition there is always a part with both
   `3f_b < |V_b|` and `2f_b ≤ f` (`exists_good_side`).
6. **Notation `f < |V_b|/3` (imprecise).** In Lemmas 5.1 and 5.6 and Theorem 5.7, `f` denotes
   the number of faulty nodes *in `V_b`*. Read literally, with `f` the total number of faults, the
   first statement of Theorem 5.7 ("`f < n/3` hence `f < |V_b|/3` for some `b`") is false. We use
   `f_b = |F ∩ V_b|` throughout.

## Typos and small slips

* Definition 2.2: `F_{v,r̂} + r̂ − r'` should be `F_{v,r'} + r̂ − r'`.
* Lemma 5.2: the interval `[r₀ + iX, r₀ + i(X+1) − 1]` should be `[r₀ + iX, r₀ + (i+1)X − 1]`.
* Lemma 5.6: `F_{r,v}` / `F̂_{r}` index order varies; `ℓ > n` should be `ℓ ≥ n`.
* Algorithm 5, line 25: `F̂_{v,w} := C` should be `:= c`. Lemma 6.6 proof: `D_{v,r}` should be
  `N_{v,r}`; "`𝐴` variables" should be "`C` variables". (Algorithm 5 is not formalized.)

## Modelling choices and other differences

* **Model.** We use CSLib's self-stabilising Byzantine state-broadcast model
  (`Cslib.Byzantine.SyncCounting`): complete network, lock-step rounds, arbitrary initial states,
  a static Byzantine set `F` with `3|F| < n` whose members may send different states to different
  nodes. In every round each node sends its whole state. The paper's Section 4 conventions make
  every message a function of the sender's state at the end of the previous round, so this is no
  loss of generality for correctness and stabilization time. Message sizes and bit complexity are
  not expressible in this model.
* **Same-round input of the `b = 1` instance.** In Algorithm 1, read sequentially, the `b = 1`
  instance's input `C_v + R` uses `C_v` after a possible update by the `b = 0` instance in the
  same round. That update depends on received messages, which the Section 4 convention forbids
  in a send. We use the value at the end of the previous round for both instances.
* **Stage states of King Consensus.** Instance memory is modelled as the stage-2 and stage-3
  states of the two pipelines. Round 1 is computed from the current state, which is exactly what
  the paper's "memory block per round" achieves.
* **Out-of-range values** (the compiler's "reset to an in-spec default"): a cooldown above `X` is
  clamped to `X` before decrementing. Clock values are stored as natural numbers and read
  modulo `C`, `k_b n`. Filter outputs are reduced modulo `K`.
* **Tie-breaking** in Algorithm 9, line 4 uses the smallest sender. For Algorithm 8, the majority
  and the `n − t` quorum (unique when `n > 3t`) also use the smallest sender.
* **Leaders from filtered clocks** (line 2): `ℓ = φ / k_b` if `φ ≡ 0 mod k_b`, reading `φ` modulo
  `k_b n` (`leader`).
* **Constants.** King Consensus is Algorithm 10 (`R = 3`). With our timing the collision window
  has `D = R = 3` instances. We use `k₀ = 4D = 12`, `k₁ = 5D = 15` (the paper's
  `k₀ = ⌈(R+1)/ε⌉`, `k₁ = k₀ + R + 1` with `ε = 1/4`, in our timing) and filter parameter `X = 48`
  (crusader window `X − 1 = 47 ≥ 16D − 1`), instead of the paper's `X = 5 max{k₀,k₁} + R`. Lemma
  5.6 at trace level (`lemma_5_6`, `theorem_5_7_trace`) is proved for every `D ≥ 1` and every
  window `W ≥ 16D − 1`.
* **Explicit bounds.** Lemma 5.6: an unimpeded instance starts before
  `max{s₁, s₂} + 20D(f+1)`. Theorem 5.7: stabilization within `T_b(f_b) + 50 + 60(f+1) + 3`
  (`S_F = X + 2 = 50`; crusader agreement from time `X = 48`). Corollary 5.8: `120 f + 113⌈log₂ n⌉`.
* **Balanced partition**: `V₀ = {v < ⌊n/2⌋}`, `V₁` the rest. Each node stores the states of both
  sub-algorithms and uses only its own part's.
* **King agreement** (Definition 2.6) is stated as in the paper: `y_v = y_ℓ ≠ ⊥`.
* **Lemma 5.2** is stated per interval `[r₀, r₀ + W]` of the crusader window (`lemma_5_2`).
  Lemma 5.6 uses crusader agreement directly rather than the virtual clock.

* **Section 6.1** (`KingConsensus8.lean`) uses a separate one-instance model with per-link messages
  `Option Msg` (`none` = nothing sent; `val a`, `nack`, `runGC`). Ties go to the smallest sender.
  "Messages different from `x_v`" count every received message other than `val x_v`, including
  NACK. In Algorithm 4, line 8, only a `val` message from `ℓ_v` counts as "received `z_{ℓ_v}`". The
  bit bound of Theorem 6.5 is formalized as a message count: every correct message is sent by `ℓ`,
  to `ℓ`, or to a faulty node, so there are at most `8n(f+2)` messages of size `O(log|V|)`. In the
  proof of Lemma 6.2, the detour "their senders must have received …" is unnecessary but harmless.
  The 8-round algorithm is not plugged into the recursion (that uses Algorithm 10).

## Not formalized

* Message sizes in Lemmas 2.3/2.5/2.7 and Corollary 5.8, and bit-complexity statements other than
  the message count of Theorem 6.5.
* Section 6.2 (Algorithm 5, Lemmas 6.6–6.9) and Section 7 (Theorem 1.1: `O(f + 1)` stabilization
  via unbalanced recursion and expanders; weak king consensus).
* The optimality claim (`Ω(f + 1)`) rests on cited consensus lower bounds; it is not proved in the
  paper and not formalized.
