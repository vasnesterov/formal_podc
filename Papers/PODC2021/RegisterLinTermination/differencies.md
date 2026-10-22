# Differences between the formalization and the paper

Hadzilacos, Hu, Toueg. *On Register Linearizability and Termination*. PODC 2021 (arXiv 2102.13242v1).

## Definitions (Section 2)

- **Histories vs. executions.** The paper defines (write) strong-linearization functions on the set of
  *histories* of an implementation, but its proofs use internal steps (Algorithm 3 scans the times at which
  writes write `Val[-]`; the proof of Theorem 13 describes histories by internal reads). We use CSLib's
  `Impl.IsLinFun` / `IsStrongLinFun`, whose functions map *executions* (label lists including the internal
  `tau` steps), as Golab–Higham–Woelfel do. For the impossibility results (Theorem 13, Corollary 11) this
  is the stronger statement (the function may look at internal steps); Theorem 14 is proved for an arbitrary
  set of histories (`swmr_writeStrongLin`), so it covers both readings. For the positive result Theorem 10
  the execution-based notion is formally weaker than a history-based one (the function may look at internal
  steps); this is what the paper's Algorithm 3 does (it uses the times of the writes to `Val[-]`). Theorem 7
  assumes a write strong-linearization function on `R1`'s *histories*, so Theorem 10 as proved does not plug
  directly into Theorem 7 (not claimed).
- **Definition 4.** Formalized for an arbitrary set of operations `O` (`Impl.IsStrongLinFunFor O`), as
  suggested at the end of Section 1; write strong-linearizability is `O = isWrite`. "The sequence of write
  operations in `f(G)`" is the subsequence of entries (operation instance, operation) whose operation is a
  write (`opsFor RWOp.isWrite`).
- **Definition 2** is CSLib's `IsLinearization`: pending operations may be included; the "matching
  responses added" are implicit (only completed operations' responses are checked).
- Write operations return the written value (CSLib's register specification has a dummy write response),
  instead of `done`.

## Theorem 14 / Appendix E

- **The proof of Lemma 67 is wrong.** The modified function `f*` (drop the last operation of `f(H)` if it is
  an incomplete write) need not satisfy property (P). Claim 67.1 asserts that an incomplete write that is
  not the last operation of `f(H)` is read by some read of `H`; but the operation after it can be a *pending*
  read linearized with an added response (allowed by Definition 2). Counterexample (atomic SWMR register,
  writer `p₀`, reader `p₁`): `G` = `p₀` completes `write 1`, invokes `write 2`; `p₁` invokes `read`.
  `f(G) = write 1, write 2, read`; `H` = `G` + the read returns `1`, `f(H) = write 1, read`. Then
  `f*(G) = f(G)`, `f*(H) = f(H)` and `write 1, write 2` is not a prefix of `write 1`
  (`lemma67_construction_fails`; the Lean function `badLinFun` is on executions, but `IsLinearization`
  depends only on the history, so the same choice `f(G) = linG`, `f(H) = linH` gives a history-based
  linearization function). The argument also silently assumes that written values are distinct
  ("read by" a read). **The theorem is true**: we use a different construction (a linearization with the
  least number of operations of the writer; restriction of a linearization of an extension to the operations
  of the prefix shows that this number is monotone along prefixes).
- Theorem 14 is proved for any set of well-formed histories in which only one process invokes writes and
  every history is linearizable (no prefix-closure or implementation structure needed); the writer may also
  read. The `Impl` corollary assumes the SWMR discipline through `allowed` (only `w` may invoke writes).

## Theorem 13 (Algorithm 4 not write strongly-linearizable)

- Proved for `n = 3` processes, values in `ℕ` with initial value `0`, written values `1, 2, 3` — exactly the
  histories of the paper's proof. (Any larger `n` would work the same way; not formalized.)
- Algorithm 4's read starts with the best cell `(v₀, ⟨0, 0⟩)` and keeps the lexicographic maximum while it reads
  `Val[1..n]` (same result as taking the maximum at the end). One base-object access per step.

## Theorem 10 (Algorithm 2 write strongly-linearizable) / Appendix C

- Proved for arbitrary `n ≥ 1`, `V`, `v₀`. The write sequence `WS` is built on-line exactly as in
  Algorithm 3 (at the step where a write `w_i` writes `Val[k]`, append the pending writes not yet in `WS`
  whose partial, `∞`-padded timestamp is below `ts_{w_i}`, then `w_i`); reads are inserted off-line after the
  write they read from via the reads-from criterion `MWMRReadsFrom`.
- **Ties in line 10 of Algorithm 3.** "In increasing order of `ts^i_w`" is ambiguous: two pending writes can
  have equal partial timestamps (e.g. both `[0, ∞, ∞]`). Harmless: the proof only needs `w_i` to come last in
  `B_i`; we order the other members of `B_i` by process id and use the strict comparison `< ts_{w_i}` (the
  paper's `≤` gives the same set since a pending `w ≠ w_i` cannot have partial timestamp `ts_{w_i}`).
- **Lemma 42, Case (b)** uses "since `r` starts after `w` completes" although only "`w` writes `Val[-]` before
  `r` starts" is assumed (and Lemma 44 B.2 applies Lemma 42 to a possibly pending write). Fix: by Lemma 40,
  `t_i ≤` the time of `w`'s write `<` the start of `r`.
- The paper's reset of `new_ts` to `[∞, …, ∞]` (line 9) is implicit: a process that is not computing a
  timestamp has no partial timestamp in its local state.

## Theorem 12 (Algorithm 4 linearizable) / Appendix D

- Proved for arbitrary `n ≥ 1`, value type `V` and initial value `v₀`, via a general reads-from criterion for
  multi-writer registers (`MWMRReadsFrom`): writes ordered by timestamp, every completed read right after the
  write whose timestamp it returned (reads from the same write in invocation order). Pending reads are not
  linearized; writes that have written `Val[-]` are, even if pending — as in Definition 55.
- Imprecisions of the proof (statement correct): "the timestamps in each `Val[-]` are non-decreasing"
  (used in Lemmas 50, 59–61) is asserted without proof; it needs the invariant that `p_k`'s computed maximum is
  at least `Val[k].sq` (`p_k` reads its own register). Definition 55 only lists constraints on `f(H)`; the
  existence of such a sequence is not shown (we construct it).

## Corollary 11 (Algorithm 2 not strongly linearizable)

- The paper derives it from Helmi–Higham–Woelfel (Corollary 3.7 of [22]); we prove it **directly** with a
  concrete counterexample (`n = 3`, values in `ℕ`): a read that has read `Val[1]` before a complete
  `write 1` may later return `0` (forcing it before `write 1`) or, after a complete `write 2`, return `2`.

## Section 3 (Algorithm 1, Theorems 6–7)

- **Model.** The paper's registers that are "only linearizable" are modelled as abstract registers whose
  responses are chosen by the adversary subject to linearizability of each register's history (`LinRegs`);
  the strong adversary is a deterministic function of the execution so far (`σ`), coin flips of `p₀` take
  their outcomes from a coin sequence `ω`. Initial register values (not given in the paper): `R1 = C = ⊥`,
  `R2 = 0`. Line 24's `⊥`-test is merged into the test of line 27 (equivalent).
- **Lemma 19 as stated does not imply Theorem 7.** "For all rounds `j`, with probability at least 1/2 no
  process enters round `j + 1`" only gives `P(game never ends) ≤ 1/2`. The proof actually shows the
  conditional statement (given the history up to `p₀`'s write of `[0, j]`, the round-`j` coin defeats the
  adversary's committed order with probability ≥ 1/2), which yields `P(round j+1 entered) ≤ 2^{-j}`.
- **Theorem 7** is proved in a stronger form: for a fixed strong adversary satisfying the hypotheses, the set of
  coin sequences for which every round is entered has at most one element (`Thm7.forever_subsingleton`); hence
  probability 0 under i.i.d. fair coins (`theorem7`, `theorem7_ae`). We state termination as "almost surely some
  round is never entered"; a process scheduled infinitely often then returns (bounded number of steps per round).
- The write strong-linearization function for `R1` is only required along the adversary's runs (for prefixes of
  one run), a weaker hypothesis than Definition 4 on the set of all histories.
- Lemmas 16–18 are stated in the form the proof uses: Lemma 16 (`host_write_before`) — when a player that
  reached line 31 in round `j` completes its line-22 read, both hosts have invoked their round-`j` write to
  `R1` (hence entered round `j`); Lemma 17 (`lemma17`) — if a host enters round `j + 1`, every player's
  line-34 write to `R2` in round `j` is *linearized* before the host's line-11 read of round `j` (the paper
  says "previously", i.e. real time); Lemma 18 (`lemma18`) — for a player that reached line 31 (rather than
  line 27) and read a bit `c` from `C`, `p₀`'s round-`j` write of `c` is linearized before that read.
- Lemma 18: the step "(*) implies that `p_i` read a value written in round ≥ j" needs an induction over rounds
  (filled in). Lemma 17 says "line 37" (should be line 34); Claims 17.1/17.3 write "enters round 2" in the general
  case (should be round `j + 2`).
- Theorem 6 is proved for every `n ≥ 3` and every coin sequence, with the adversary of Figures 1–2 (reading the
  coins from the history). In the coin-1 branch, `R1`'s linearization puts `p₁`'s write before `p₀`'s write
  although `p₀`'s write completed before the coin flip (the non-on-line choice).
- Corollary 8 is `corollary8` (Theorem 6 ∧ Theorem 7); Corollary 9 and Appendix B are not formalized.
- Only `R1` needs to be write strongly-linearizable in Theorem 7 (`R2` and `C` are only used through
  linearizability in Lemmas 15–18); the paper assumes all three (and composes them via Lemma 4.8 of [19]).
