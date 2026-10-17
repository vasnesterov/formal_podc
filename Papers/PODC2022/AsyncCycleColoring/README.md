# Fault Tolerant Coloring of the Asynchronous Cycle — PODC 2022

Pierre Fraigniaud, Patrick Lambein-Monette, Mikaël Rabie. *Brief Announcement: Fault Tolerant Coloring of
the Asynchronous Cycle.* PODC 2022. DOI [10.1145/3519270.3538456](https://doi.org/10.1145/3519270.3538456).
Formalized version: arXiv [2207.11198](https://arxiv.org/abs/2207.11198) v1 (the only version, the full
version of the brief announcement). Numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The headline result is false. The paper claims a wait-free 5-colouring
of every asynchronous cycle `C_n` in `O(log* n)` rounds (Algorithm 3, Theorem 4.4). Neither 5-colouring
algorithm is wait-free. Algorithm 2 (Theorem 3.11) and Algorithm 3 (Theorem 4.4) have executions on
every cycle `C_n`, `n ≥ 3`, in which two processes take rounds forever without returning. The 6-colour
Algorithm 1 is correct: we prove Theorem 3.1, with a better bound. The Cole–Vishkin lemmas 4.1–4.3 and the
safety Lemma 4.5 (the evolving identifiers of Algorithm 3 stay a proper colouring) also hold.

## Mistakes in the paper

* **Theorems 3.11 and 4.4 are false: Algorithms 2 and 3 are not wait-free.** Take `C_3` with
  identifiers `0, 1, 2`. At time 1 all three processes take a round. Each writes `(X, a, b) = (X, 0, 0)`
  and recomputes: process 0 gets `(1,1)`, process 1 gets `(1,1)`, process 2 gets `(0,1)`. Process 1
  then crashes, or is just slow, and its register keeps showing its initial colours `(0, 0)`.
  Processes 0 (the local minimum) and 2 (the local maximum) now take their rounds *simultaneously*,
  which the model explicitly allows. Each round they read the stale `(0,0)` of process 1 and each
  other's colours. Their states alternate forever between `(1,1)/(0,1)` and `(2,2)/(0,2)`, and each of
  them always finds both of its colours in the conflict set `C`. So neither returns, and no bound on the
  number of rounds exists.
  - In Algorithm 3 the same execution works. Process 0 is a local minimum and process 2 a local
    maximum, so both set `r ← ∞` in their first round and never change their identifiers again; after
    that the algorithm runs exactly like Algorithm 2.
  - The same pattern works on every `C_n`, `n ≥ 3`, with identifiers `0, …, n-1`. Processes `0` and
    `n-1` play the roles of 0 and 2. Their other neighbours `1` and `n-2` stop after their first round.
  - Lemma 3.13 is refuted by the same run. Process 2 is not a local minimum and its set `A_2` stays
    empty, yet it never returns. The proof's claim that the neighbours' `a`-values are positive "by
    time `t_4`" ignores registers that are frozen at the initial value `0`.
  - Severity: these are false statements, about the paper's main algorithms. The correctness and palette
    parts of both theorems do hold.
  - Two remarks from bounded model checking. If at most one process is activated per time step (no
    simultaneous rounds), Algorithm 2 terminates on all `C_n` with `n ≤ 5`. Leaving the initial
    colours unwritten (`⊥`) does not repair it.
  - Whether some wait-free 5-colouring of `C_n` exists is not settled here: we refute the algorithms,
    not the possibility. (`theorem_3_11_false`, `theorem_3_11_false_all`, `lemma_3_13_false`,
    `theorem_4_4_false`, `theorem_4_4_false_all`)
* **Theorem 3.1 is correct, but its proof leans on loose lemmas; we give a new, sharper proof.**
  Our bound is `max(4, n)` activations, where the paper has `⌊3n/2⌋ + 4`.
  - Local extrema return within 4 activations, as the paper claims. Our argument: after the first
    round of a local maximum `p`, each smaller neighbour can cause at most one more failure of `p`.
  - A non-extremal process returns within `ℓ + ℓ' + 1` activations (Lemma 3.9, third term), where
    `ℓ`, `ℓ'` are the monotone distances to the closest local maximum and minimum. Our argument: every
    failed round changes the colour (Lemma 3.2), `a_p` changes at most `ℓ` times, and `b_p` at most
    `ℓ'` times.
  - The parity bookkeeping with the sets `A_p`, `B_p` (Lemmas 3.5–3.8) is not needed.
  - Lemma 3.3 is false as written. With the open interval `(t₁, t₂)`, a neighbour that takes a round
    exactly at `t₂` can still conflict with `p`; random simulation finds such runs on `C_4`. The lemma
    holds for the half-open interval `(t₁, t₂]`, which is the form we prove and use
    (`fresh_of_conflict`).
  - The terms `3ℓ + 4`, `3ℓ' + 4` of Lemma 3.9 (via Lemma 3.4 for non-extremal processes) are not
    formalized. Exhaustive model checking for `n ≤ 6` found no violation.
  - Severity: proof gaps; the statement is true. (`theorem_3_1`, `alg1_workActs_le`, `lemma_3_9`,
    `workActs_le_four_of_max`)
* **Lemma 4.5 is true, but its proof is incomplete.** The induction claim `X_p ∉ {X_q, X̂_q}` is not
  inductive on its own.
  - The repaired invariant also records two things. First, a register holds an earlier state with a
    counter `r̂ ≤ r`, equal only if the identifier is unchanged. Second, if a neighbour's last step
    changed its identifier and `r̂_q = r_p`, then that step read exactly the current `X_p`.
  - The paper's stale-read case concludes something about `X̂_p` where it needs the current `X_p`.
    The case `X_q(T+1) = f(X_q(T), X_p(T))` omits the cases where `q` is a local maximum or reduces
    against its other neighbour.
  - Severity: proof gap; the statement is true. (`lemma_4_5`, `alg3_X_ne_reg`, `alg3_X_proper`)
* **Under-specified and minor points.**
  - The pseudocode never says how a `⊥` register enters lines 11–19 of Algorithm 3. We follow the proof
    of Lemma 4.10: an unwritten `r` blocks the green light. The counterexample does not depend on this
    choice.
  - Theorem 4.4 assumes only a proper initial colouring, but its `O(log* n)` bound needs identifiers in
    `[0, poly(n)]`, as Section 2.1 assumes for identifiers. Moot, since termination fails.
  - Lemma 4.1 is stated over the reals. We prove it over `ℕ`, with `α = 3`.
  - Typos: in the proof of Lemma 3.5, `Y` and `τ` should be `x` and `t'`. The proof of Lemma 4.10 uses
    an undefined `R`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`).
* **Network and processes.** `n` processes on `ZMod n`, where the neighbours of `p` are `p ± 1`. They
  are asynchronous, deterministic and crash-prone.
* **Registers.** Each process owns a single-writer register, initially `⊥`, that its two neighbours
  read. The full local state is written; the paper's algorithms write all their variables.
* **Rounds.** A round is a local immediate snapshot: write, then read both neighbours, then compute
  or return. A schedule `σ : ℕ → Finset (ZMod n)` gives the processes activated at each time.
  Processes activated together all write before any of them reads (Section 2.1). Activating a
  returned process does nothing.
* **Faults and adversary.** Crashes and slowness are schedules that stop or delay activating a process.
  The adversary is any schedule; no fairness is assumed.
* **Measures.**
  - `workActs` counts the working activations of a process, which is the paper's round complexity.
  - `WaitFreeWithin A init K` means that in every schedule every process is activated at most `K`
    times while working.
  - `ProperOutputs` means that terminated neighbours have distinct outputs; `OutputsIn` is the palette.
* **Inputs.** A proper colouring `X` (`X p ≠ X (p+1)`), as in the theorems. For Algorithm 1, `X` may take
  values in any linear order; the theorem itself uses `ℕ`.
* **Faithfulness.** The model is exactly the paper's. The counterexamples use only schedules the paper
  explicitly allows: simultaneous rounds and a process that stops after one round.

**Main results in Lean** (namespace `AsyncCycle`, all imported by `Main.lean`).

| Paper | Lean | File |
|---|---|---|
| Thm 3.1 (Alg. 1: termination ≤ ⌊3n/2⌋+4, 6 colours, proper) | `theorem_3_1`; sharper `alg1_workActs_le` (`max 4 n`) | `Alg1Extreme.lean` |
| Lemma 3.2 | `lemma_3_2`, `col_change_of_fails` | `Alg1Term.lean` |
| Lemma 3.9 (third term `ℓ+ℓ'+1`) | `lemma_3_9` | `Alg1Bound.lean` |
| Thm 3.1 proof: local extrema in ≤ 4 rounds | `workActs_le_four_of_max`, `workActs_le_four_of_min` | `Alg1Extreme.lean` |
| Thm 3.11 termination: **false** | `theorem_3_11_false` (`C_3`), `theorem_3_11_false_all` (all `n ≥ 3`) | `Alg2.lean`, `CounterexampleAllN.lean` |
| Thm 3.11 palette / correctness | `alg2_outputs_lt_five`, `alg2_properOutputs` | `Alg2.lean` |
| Lemma 3.13: **false** | `lemma_3_13_false` | `Alg2.lean` |
| Thm 4.4 termination (O(log* n)): **false** | `theorem_4_4_false`, `theorem_4_4_false_all` | `Alg3.lean`, `CounterexampleAllN.lean` |
| Thm 4.4 palette / correctness | `alg3_outputs_lt_five`, `alg3_properOutputs` | `Alg3.lean` |
| Lemma 4.1 (over ℕ, α = 3) | `lemma_4_1` | `ColeVishkin.lean` |
| Lemma 4.2, Lemma 4.3 | `lemma_4_2`, `lemma_4_3` | `ColeVishkin.lean` |
| Lemma 4.5 (+ the induction claim) | `lemma_4_5`, `alg3_X_ne_reg`, `alg3_X_proper` | `Alg3Proper.lean` |

Supporting pieces:
* `Simulation.lean`: simulation through state maps. It gives the `a ↔ b` / order-reversal symmetry of
  Algorithm 1.
* `Changes.lean`: counting changes of a sequence, with the "lag" and "follow" lemmas.
* `Activations.lean`: generic facts about activations.
* `Mex.lean`: a kernel-computable `mex`.

**Not formalized.**
* Properties 2.1–2.3: MIS impossibility, the `Ω(log* n)` lower bound and the 5-colour lower bound for
  `C_3`. They are reductions to cited results (strong symmetry breaking, Linial, renaming lower bounds).
* Lemmas 3.4–3.8, 3.14 and 4.6–4.10, which are steps of proofs we replaced or of claims that are false.
* The `3ℓ + 4` terms of Lemma 3.9.
* Appendix A (`O(Δ²)` colours on general graphs).

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The `C_3` counterexamples are checked by kernel `decide` (2-periodic configuration);
the all-`n` versions are symbolic. Correctness and palette are proved for every initial colouring.
`modelcheck/` holds the Python model checkers used to find the counterexample and to test the bounds:
exhaustive over all schedules for small `n` (`mc12.py`, `lasso.py`, `bounds1.py`, `scc3.py`), and
random/BFS search for Lemma 4.5 (`alg3.py`, `rand3b.py`, `bfs3.py`).

CSLib candidates: the local-immediate-snapshot cycle model (`Model.lean`, could be generalized to graphs),
`Simulation.lean`, `Changes.lean`.
