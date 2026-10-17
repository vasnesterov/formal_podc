# Differences between the formalization and the paper

Paper: E. Godard, D. Imbs, M. Raynal, G. Taubenfeld, *From Bezout's Identity to Space-Optimal
Election in Anonymous Memory Systems*, PODC 2020, DOI 10.1145/3382734.3405727 (HAL
hal-03148627, the proceedings text; there is no arXiv version).

## Errors and gaps in the paper

1. **Theorem 1: the proof is imprecise; the statement is true.** The proof assigns to each
   process an "initial register" and defines `order(pᵢ, k)` as "the k-th *new* register that `pᵢ`
   accesses during ρ". This ties the anonymity permutation to the execution being built. It also
   claims that processes of a group `Qᵢ` with the same number of steps "must be at the same state".
   That is false as stated: they have different identifiers. They are in the same state *up to a
   renaming of identifiers*, and the memory is symmetric under a rotation combined with that
   renaming. The argument that works: process `i` of every group sees the memory rotated by
   `i · m/δ` (a fixed permutation, chosen in advance), its identifier is `τⁱ(a_q)` for a
   permutation `τ` cycling every group, and the lock-step execution preserves the invariant "local
   state of member `i` of group `q` = `τⁱ •` base state of `q`; `mem(rot y) = τ • mem(y)`". This is
   formalized in `LockStepExec.lean` (`exists_symmetric_outcome`, on top of the shared
   `Podc/SharedMemory/Anonymous/LockStep.lean`). Choosing
   the permutation lazily is legitimate without snapshots, and the paper explains it; we fix
   the permutations in advance instead, which also covers snapshots.
   *Classification: imprecision, statement true.*
2. **Section 4: "both `u′` and `v′` are positive" is false in a degenerate case.** For `m = 1`,
   `n = 2` and the Bezout pair `(u, v) = (−1, 1)`, the third case gives `(u′, v′) = (1, 0)`
   (`v_prime_zero_example`). Only `v′ ≥ 0` holds, and that is all the algorithm needs
   (`paper_rewrite`). The case `v ≤ 0` also silently uses `u > 0`, which holds because
   `u m = gcd(m, n) − v n > 0`. *Classification: typo / degenerate case, harmless.*

3. **Theorem 2 (Algorithm 1): the termination proof is a sketch; the statement is true.**
   "It follows that this pattern is repeated until all the processes except one are losers"
   gives no reason why two or more candidates cannot keep overwriting each other forever, with
   losers forever re-announcing their loss. Our proof of the electing phase (`Alg1Live.lean`,
   `Alg1Term.lean`) needs three things the paper does not state. (a) An extra invariant: there is
   always a non-loser, and any identifier in `REG.id` belongs to a non-loser. (b) A
   "minimal discarded set" argument. Once the set of candidates and their `discarded` sets are
   stable, a ⊥-value read by candidate `c′` was written by a loser `j ∉ D_c` who had read
   candidate `c`'s value. So `D_c ⊊ D_{c′}`, which is impossible for the `c′` with the smallest
   set. (c) Two rounds of flushing stale writes. The committing phase relies on "quiet" losers:
   once the leader's committing `discarded` set contains `j`, process `j` never writes again.
   *Classification: proof gap, statement true.*
4. **Line 16 of Algorithm 1 mixes phases.** A loser copies `REG.discarded` without looking at
   `REG.phase`, so committing-phase values can carry electing-phase sets. The paper does not
   discuss this. It is harmless: once the first electing value with `n − 1` discarded
   identifiers is written, every electing value carries all other identifiers (part of the
   invariant `Inv` in `Alg1Inv.lean`). *Classification: proof gap, statement true.*
5. **Theorem 4 (Algorithm 2): Lemmas 1 and 2 are sketches; the statements are true.**
   * Lemma 2 rests on Claim 1 ("after a process returns at line 7, no more writes occur"),
     applied to each competition of Algorithm 2. In Algorithm 2 a process decides a write from a
     copy read during an earlier, non-atomic collect, and the write may land much later. The
     property actually needed is level monotonicity: no write carrying level `L` lands after
     register `x` has reached level `L + 1`. Our proof needs a per-register invariant over the
     status of every process for every register (will read / holds an unprocessed copy / has a
     pending write / processed), with ghost data (`Alg2Abs*.lean`, `Alg2Glob*.lean`). The paper
     never states the counting argument either. When the first process sets `finishing`, every
     process has already won exactly `v ℓ` competitions: the collected sum of levels is at most
     the true sum, because levels are monotone. So exactly `d` distinct processes win a
     competition with `finishing = true` (`Alg2Safety.lean`).
   * Lemma 1 ("all competitions that have at least one candidate will terminate … Exactly d
     processes will then win remaining competitions") is one paragraph. Our proof
     (`Alg2Prog1–5.lean`) assumes that the number of solved competitions stays constant from some
     time on and derives a contradiction. It shows that cand flags, `to_win` and `finishing`
     stabilize, and that every process reads every register infinitely often. It then finds an
     open register with a stable candidate, either a pristine register or by counting with
     `U m ≤ W n + n`, i.e. `d ≤ n`. Finally it transfers Algorithm 1's convergence argument to
     that register, whose candidate set changes over time.
   *Classification: proof gaps, statements true.*
6. **Hypotheses.** The paper assumes `1 ≤ d < n` (§1.1); our `theorem_4` assumes
   `gcd(m, n) ℓ ≤ n`, which also covers `d = n` (not a paper error). Algorithm 2 needs `m ≥ 1`, as the paper assumes. For the generalized parameters
   `(U, W)` of our `Alg2.alg2_agreement`, `W n ≤ U m` is needed. With `n = 2`, `m = 1`, `U = W = 1`,
   the only competition is solved before anybody sets `finishing` and everybody returns `∅`. The
   paper's Bezout parameters always satisfy `W n ≤ U m`. The one-shot assumption is not needed
   by any of the algorithm proofs.
7. **Typos and small slips.**
   * Algorithm 2, line (5): `|reg_i.discarded| = n − 1 ∧ reg.id ≠ ⊥` should be
     `reg_i[x].discarded`, `reg_i[x].id`.
   * Section 5.2: the for loop is lines N(5)–N(20), not "N(2)–N(20)". "Case 2" refers to the `if`
     of line N(6), not N(3). Lemma 2's proof says `to_win_i` is set to 1 "at line N(3)"; it is N(4).
   * Lines N(16)–N(17) are described as "jumps to `reg_i[x].level`", but the code increments
     `level_i[x]` by one per collect. We formalize the code.
   * Claim 1's proof says "every other process `p_i` has `loser_i` set to false"; it should be
     `true`. The proof of Theorem 2 refers to "the predicate of line 16"; it means lines 5–6.
   * §3.1 prose says line 8 "leaves `REG.id = id_ℓ`", but the code writes
     `⟨⊥, ∅, committing⟩`. The Lean model follows the code.
   * The register size "1 + n log₂ n bits" for Algorithm 1 ignores the `id` field (≈ `log n`
     more bits). Not formalized.

## Modelling choices

* **Model** (`Defs.lean`). CSLib's asynchronous shared-memory model (`Impl`, executions as label
  lists). The anonymous memory is CSLib's `memObj m V bot` (one base object holding `m`
  registers; primitive steps are arbitrary read-modify-write of one register and atomic snapshots),
  accessed through per-process permutations `π p` (`SymAlg.impl`).
* **Symmetric algorithms** (`SymAlg.Symmetric`): the paper's "identities can only be compared for
  equality" is formalized semantically. The algorithm commutes with every renaming of identifiers
  (acting on register values and local states), and the initial register value is not an
  identifier.
* **Election object** `elecObj R`: one operation `elect()`, response in `R`. All processes
  participate: in the termination property, every process invokes `elect()` exactly once
  (`AllInvoke`, `IsOneShot`).
* **Termination** (`Terminates`): in every *fair* infinite execution in which every process
  invokes `elect()` once, every process returns. Fair = a process with a pending operation
  eventually takes a step. The paper's processes are fault-free and asynchronous; this is the
  standard reading of "each process terminates".
* **d-election with bit outputs** (`DElection`, `ExactElection`): the paper's impossibility proof
  only uses that "each process knows whether it is elected" (Section 2). We state Theorem 1 for
  bit outputs, which is the strongest form: an algorithm outputting leader sets or identifiers
  yields one with bit outputs.
* **Quantifiers in Theorem 1.** The algorithm must be correct for *every* choice of anonymity
  permutations (the adversary's choice) and for *one* injective identifier assignment. The
  theorem holds for any register values `V` and local states `S`, for read-modify-write and
  snapshot accesses, and for any `m ≥ 0`, `n ≥ 0` (for `n = 0` the hypotheses are
  contradictory).
* **Granularity of the algorithms.** Algorithm 1: one atomic read per loop iteration, followed
  by at most one atomic write; the local computation is folded into the read (`afterRead`).
  Algorithm 2: the collect is `m` separate atomic reads in local order (not a snapshot), and each
  write of the for loop is a separate atomic step. The for loop processes local indices in
  order. This is the finest granularity the pseudocode allows, so the correctness results are
  the strongest ones.
* **Outputs of the algorithms.** Algorithms 1 and 2 return `out id_i ℓ` (resp. `out id_i L`).
  The correctness theorems hold for every output map, and agreement is stated on the leader
  `ℓ` / leader set `L` themselves. Theorems 2 and 4 are also derived for the bit version
  `decide (id_i = ℓ)` / `decide (id_i ∈ L)` used in the characterizations.
* **Parameters of Algorithm 2.** The paper takes the *smallest* non-negative `u, v` with
  `u m = v n + gcd(m, n)`. Our `theorem_4` works for *any* such pair; existence is
  `exists_bezout_nat`. The proofs use only `U = u ℓ`, `W = v ℓ` and `U m = W n + d`.
* **Corollaries 1–3** are stated for `m ≥ 1`, `n ≥ 1` (and `d ≤ n` for Corollary 3). The
  solvability predicates `ExactSolvable` / `DSolvable` quantify over the register value and local
  state types. `rw = true` asks for a read/write algorithm; `rw = false` allows arbitrary
  read-modify-write accesses and snapshots.
