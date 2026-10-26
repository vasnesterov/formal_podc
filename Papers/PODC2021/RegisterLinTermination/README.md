# Register Linearizability and Termination — PODC 2021

Vassos Hadzilacos, Xing Hu, Sam Toueg. *On Register Linearizability and Termination.* PODC 2021. DOI
[10.1145/3465084.3467925](https://doi.org/10.1145/3465084.3467925). Formalized version: arXiv
[2102.13242](https://arxiv.org/abs/2102.13242) v1; numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** Every theorem we formalized holds: Theorem 14 (linearizable SWMR ⇒ write
strongly-linearizable), Theorems 10/12/13 and Corollary 11 (Algorithm 2 is write strongly-linearizable but not
strongly linearizable; Algorithm 4 is linearizable but not write strongly-linearizable) and Theorem 6 (with merely
linearizable registers a strong adversary keeps Algorithm 1 running forever) and Theorem 7 (if `R1` is write
strongly-linearizable, Algorithm 1 terminates with probability 1 — in fact at most one coin sequence defeats any
given strong adversary). **The proof of Theorem 14
(Lemma 67) is wrong**; we prove the theorem with a different construction. Several smaller gaps.

## Mistakes in the paper

* **The proof of Theorem 14 (Lemma 67) does not work.** From an arbitrary linearization function `f` the paper
  builds `f*` by deleting the last operation of `f(H)` when it is an incomplete write, and claims (Claim 67.1)
  that an incomplete write that is not last in `f(H)` must be read by some read of `H`. But the next operation
  may be a *pending* read, linearized with an added response (Definition 2 allows it). Counterexample, on the
  atomic SWMR register: in `G` the writer completes `write 1` and invokes `write 2`, and a reader invokes a read;
  `f(G) = write 1, write 2, read`. In the extension `H` the read returns `1` and `f(H) = write 1, read`. Then
  `f*(G) = f(G)`, `f*(H) = f(H)`, and the writes `write 1, write 2` of `f*(G)` are not a prefix of the writes
  `write 1` of `f*(H)` (`lemma67_construction_fails`). The claim also tacitly assumes distinct written values.
  The theorem is true: take, for each history, a linearization with the **fewest operations of the writer**;
  restricting a linearization of an extension to the operations of the prefix shows this number is monotone, so
  the write sequences are prefixes of each other (`swmr_writeStrongLin`, for any set of SWMR histories — shared
  memory, message passing or hybrid).
* **Lemma 19 is too weak for Theorem 7.** "For each round `j`, with probability ≥ 1/2 nobody enters round
  `j + 1`" only bounds the probability of an infinite game by 1/2. The proof does give the needed conditional
  statement (the adversary's order of the two round-`j` writes is fixed before the round-`j` coin is flipped).
  We prove more: against a fixed (deterministic) strong adversary, the round-`j` coin that lets the game go on
  is determined by the history before it is flipped, so **at most one coin sequence** keeps the game alive
  (`Thm7.forever_subsingleton`), which has probability 0 (`theorem7`). Lemma 18's step "(*) implies that the
  round of the write is ≥ j" needs an induction over rounds that the paper leaves implicit. Typos: Lemma 17 says
  "line 37" for line 34; Claims 17.1/17.3 say "round 2" in the general case.
* **Algorithm 3 (Theorem 10) is ambiguous on ties**: two pending writes can have equal partial timestamps (e.g.
  both `[0, ∞, ∞]`). Harmless — only "`w_i` last in `B_i`" is used; we order the rest by process id.
* Smaller gaps, all with correct statements: Lemma 42 Case (b) uses "`r` starts after `w` completes" where only
  "`w` writes `Val[-]` before `r` starts" is available (fix via Lemma 40); Appendix D asserts without proof that
  the timestamps in each `Val[-]` never decrease (needs an invariant: `p_k` reads its own register), and
  Definition 55 lists constraints on `f(H)` without showing that such a sequence exists.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Shared memory (Sections 4–6): CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): `n`
  processes (`Fin n`), atomic base registers `Val[i]` (single-writer by the code), deterministic programs, one
  base-object access per step; wait-free, no failures needed. Linearization functions map *executions* (label lists
  with internal steps), as the paper's proofs use them; Theorem 14 is also proved for arbitrary sets of histories.
* Write strong-linearizability is CSLib's strong linearizability restricted to a set of operations
  (`Impl.IsStrongLinFunFor RWOp.isWrite`): only the write subsequence must be prefix-monotone.
* Section 3: Algorithm 1 over **abstract registers whose responses are chosen by the adversary**, constrained only
  by linearizability of every register's history (`Game.LinRegs`); a **strong adversary** is a deterministic
  function of the whole execution (`σ : List Ev → Ev`), and `p₀`'s coin flips take their values from a coin
  sequence `ω` (`genRun σ ω`). Crashes are processes that are no longer scheduled; returned processes may take
  `noop` steps.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Def. 4–5 (write strong-linearizability) | `Impl.IsStrongLinFunFor`, `Impl.WriteStronglyLinearizable` | `Podc/…/WriteStrongLin.lean` |
| Theorem 6 | `Game.theorem6` (every `n ≥ 3`, every coin sequence) | `Theorem6.lean`, `Game.lean` |
| Theorem 7 | `Game.theorem7` (prob. 1, only `R1` write strongly-linearizable), `Thm7.forever_subsingleton` (≤ 1 bad coin sequence) | `Theorem7.lean`, `Theorem7Core.lean` |
| Lemmas 16–18, decision bit of Lemma 19 | `Thm7.host_write_before`, `Thm7.lemma17`, `Thm7.lemma18`, `Thm7.coin_decided` | `Theorem7Core.lean` |
| Corollary 8 | `Game.corollary8` | `Theorem7.lean` |
| Theorem 10 | `Alg2.alg2_writeStronglyLinearizable` (any `n`, values, initial value) | `Alg2WSL.lean`, `Alg2WSLInv.lean` |
| Corollary 11 | `Alg2.alg2_not_stronglyLinearizable` (`n = 3`, direct proof) | `Alg2.lean` |
| Theorem 12 | `Alg4.alg4_linearizable` (any `n`, values, initial value) | `Alg4Lin.lean` |
| Theorem 13 | `Alg4.alg4_not_writeStronglyLinearizable` (`n = 3`, values `ℕ`) | `Alg4.lean` |
| Theorem 14 | `swmr_writeStrongLin` (any set of SWMR histories), `Impl.writeStronglyLinearizable_of_swmr` | `SWMR.lean` |
| Lemma 67 (proof) | `lemma67_construction_fails` (counterexample to the construction) | `SWMR.lean` |

**Not formalized.** Corollary 9 (composition with an arbitrary algorithm `A`), Appendix B (bounded `R1`),
the remark that ABD is write strongly-linearizable (it follows from Theorem 14 once ABD is proved linearizable).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: the atomic SWMR register satisfies the hypotheses of Theorem 14
(`atomicSWMR_writeStronglyLinearizable`); the hypotheses of Theorem 7 are satisfiable (`theorem7_hyps_satisfiable`,
a simple adversary with atomic register behaviour — weak, but it rules out contradictory hypotheses); Theorems
10 and 12 are about concrete algorithms. Shared code (CSLib
candidates) in `Podc/Computability/Distributed/SharedMemory/`: `WriteStrongLin.lean` (definitions, restriction of
a linearization to a prefix, decidable real-time order, "reads force the order of writes" lemmas),
`MWMRRegister.lean` (reads-from criterion for multi-writer registers), `LinPointCheck.lean` (linearizability of all
prefixes from an annotated run with linearization points).
