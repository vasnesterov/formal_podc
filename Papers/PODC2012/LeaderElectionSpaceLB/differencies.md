# Differences between the formalization and the paper

Paper: G. Giakkoupis, P. Woelfel, *On the Time and Space Complexity of Randomized Test-And-Set*,
PODC 2012 (authors' copy, HAL hal-00722947).

## Statement-level issues

1. ✏️ **`GroupElect` definition (Section 2.1) / Lemma 2.2 (implied assumption).** The
   definition says "If some processes call `elect()`, then at least one process must get elected".
   Unlike `LeaderElect`, it has no "if no process crashes", although the model of Section 1.1 has
   crashes. Read literally, Figure 1 is not a GroupElect object (`GroupElect.not_groupElectLiteral`,
   2 processes, `ℓ = 1`). This is an implied assumption: the crash-free reading is the
   `LeaderElect` convention stated just before, and the only use (Section 2.1, "if no process
   crashes then some process wins") is crash-free. Proved under that reading:
   `GroupElect.isGroupElection`. The statement "Figure 1 implements a GroupElect object" is false as
   written in the paper's own model, by a 2-process execution in which the returning process
   completes its call. GroupElect feeds Lemma 2.1 / Theorem 2.3.
1a. ✏️ **Claim 5.3 (degenerate).** It fails only for `Q = ∅` (hence `R = ∅`), where the `Q`-only `β`
   is empty (item 5).

## Proof gaps of true statements

2. 🔧 **Theorem 5.1, "fix the random choices"** (Section 5.2 and the proof of Theorem 5.1). The paper
   fixes the nondeterministic decisions by "an arbitrary (but fixed) one that guarantees that each
   process terminates within a bounded number of steps if it runs solo", so that "the algorithm
   becomes deterministic and obstruction free". No such fixing is shown to exist. A choice function
   on local states need not exist (gadget in the README; it does not refute fixing a per-process coin
   tape, the usual reading, which is merely not justified), and solo runs need not be bounded. Not
   needed: we formalize the whole argument for nondeterministic executions (events `(p, l')` fix
   the choice), using nondeterministic solo-termination directly, as Claims 5.3 and Lemma 5.4
   already do.
3. 🔧 **Lemma 5.4(e) for `R = ∅`.** "The claim for `k' = k+1` follows immediately" does not cover (e),
   which then needs `⌊m_k/(n−k)⌋ ≥ 1`. Repaired via `f(k) ≥ n − k` (`sub_le_f`) and
   `f(k+1) ≤ f(k)` (`f_succ_le`).

## Small errors inside proofs (no effect)

4. 🔧 Claim 5.2's proof: "`C(E)` and `C(D)` are indistinguishable to all processes in `Q`" is false
   under the paper's own definition of indistinguishability, which also compares all register
   values. What holds is our `AgreeOn`: same states of `Q`, and same value and writer on every
   register last written by `Q` or unwritten (`Alg.erase`).
5. Claim 5.3 fails for `R = R' = ∅`, `Q = ∅` (the `Q`-only `β` is empty). We add `R ≠ ∅`, which
   holds at the only use. We drop the unused hypothesis `R' ⊆ ℛ − R`.
6. Lemma 5.4's proof: "covered by exactly two processes … exactly one is in `Q`" should be "at
   least two". "By definition, no process in `Q` covers a register in `R'`" holds for the chosen
   representatives, not for all of `Q`. Only the former is needed.
7. Lemma 2.2's proof: "since `ℓ = ⌈log n⌉ ≤ log k`" should be `≥`. In the computation of `E[Y_j]`,
   the factor for `i = ℓ−1` uses `Pr(ℓ_j ≠ ℓ) = 1 − 2^{-ℓ}` instead of `1 − 2^{-(ℓ-1)}`, so the
   "=" is "≤". The final estimate holds and even gives `2 log k + 4` (`GroupElect.final_bound`,
   `GroupElect.lemma_2_2_final_bound`; numerically checked for `n < 1500`).
8. The "Further, let for `k ≥ 1` `δ(k+1) = …`" in the definition of `δ` should be `k ≥ 0` (Claim
   5.5 uses `δ(1)`).

## Modelling choices and changed statements

9. **Own model** (`Model.lean`) instead of CSLib's `SharedMemory.Impl`, which is deterministic only.
   The model has nondeterministic local transitions (`readNext l v`, `writeNext l` are sets),
   nondeterministic initial states, and an action function on local states. Local computation and
   coin flips between memory steps are folded into the successor sets. This covers randomized
   algorithms with every coin outcome possible.
10. **Leader election spec** (`IsLeaderElection`) is quantified over the set `S` of callers. For
    every finite execution from an initial configuration in which only `S` steps: at most one process
    of `S` has won, and if all of `S` returned, some process of `S` won. This is the paper's
    "at most one call returns True; if no process crashes, exactly one" (crash = stop in a finite
    execution).
11. **Nondeterministic solo-termination** (`SoloTerminating`) is required from every *reachable*
    configuration. The paper says "any configuration"; reachable ones are what the proof uses, so
    this is weaker and the theorem stronger.
12. **Visibility**: registers carry a ghost last-writer field invisible to processes. The paper
    instead assumes w.l.o.g. that values are pairs `(x, ID)`. Ours applies to arbitrary algorithms
    without transforming them.
13. **Closedness** `Closed C es Q` is defined via `Relation.EqvGen` of the paper's `↔_E`.
    `closed_iff` shows it equals "`p` sees `q` ⇒ (`p ∈ Q ↔ q ∈ Q`)".
14. **Claim 5.2** is formalized in the paper's form (`claim_5_2_paper`: `Q` = the processes that
    have returned) and in the general form used later (`claim_5_2`: any nonempty `Q`, all returned,
    no process of `Q` sees outside `Q`; exactly one winner in `Q`).
15. **Lemma 5.4** is formalized for a set `Act` of `N` active processes; the paper's version is
    `Act = P`. The others never take steps, which handles `n` not a power of two (the paper's
    "w.l.o.g."). The partition with representatives is a map `g` to representatives (`Stage.g`,
    `Stage.reps`). (d) is stated as "`p` sees `q` ⇒ `g p = g q`", and `Stage.group_closed` gives the
    paper's form. (e) is replaced by its consequence `f N k ≤ m_k`: as stated, (e) relates `m_k` to `m_{k-1}` of a different existential witness and only makes sense for the constructed sequence.
16. **Theorem 5.1** is stated as `⌊log₂ n⌋ − 1 ≤ |Reg|` for a finite register type
    (`theorem_5_1`). A stronger covering form (`theorem_5_1_covered`) gives a reachable
    configuration with `⌊log₂ n⌋ − 1` distinct covered registers. For `n = 2^t` this is exactly the
    paper's `log n − 1`.
17. **Claim 5.5** is stated with `N = 2^t`, `k = N − 2^{t−s} + d`. (a) is proved for
    `0 ≤ d ≤ 2^{t−s−1}`, i.e. `I(s)` plus the first point of `I(s+1)`; (b) for `d < 2^{t−s−1}`.
18. **Lemma 2.2** is formalized only in its deterministic part: at most 4 steps per process,
    wait-freedom, `ℓ + 2` registers, crash-free "someone is elected", and the final real-number
    estimate of its proof. The expected-number-of-elected bound and its probabilistic derivation
    (deferred decisions, location-oblivious adversary) are not formalized. Figure 1's coin is a
    nondeterministic choice of `x ∈ {1..ℓ}`.
19. **Claim 3.1**: only the counting core (`c(i+1) ≤ c(i) − 1`, `c(0) ≤ ℓ` ⇒ `c(ℓ) = 0`). The
    splitter guarantee is an assumption and splitters are not modelled.
20. Not formalized: Lemma 2.1, Theorems 2.3, 2.4, Claim 3.2, Theorem 4.1, Corollary 4.2 (step
    complexity against the various adversaries), Section 6 (2-process time lower bound), the
    LeaderElect → TAS reduction.
