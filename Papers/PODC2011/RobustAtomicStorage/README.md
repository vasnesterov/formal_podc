# The Complexity of Robust Atomic Storage — PODC 2011

Dan Dobre, Rachid Guerraoui, Matthias Majuntke, Neeraj Suri, Marko Vukolić. *The Complexity of Robust
Atomic Storage.* PODC 2011. DOI [10.1145/1993806.1993816](https://doi.org/10.1145/1993806.1993816).
Formalized version: the EPFL accepted version (infoscience record 208945, 10 pages, proofs included;
no arXiv version); numbering follows it.

**Verdict: 🔧 Easy fix.** Both lower bounds hold in the round model of [1] (see Model below):
two-round reads are impossible when `S ≤ 4t` and `R ≥ 4` (Proposition 1), and with three-round
reads the write needs more than `min {R, k}` rounds when `S ≤ 3t + ⌊t/t_k⌋` (Lemma 1, Lemma 2,
Proposition 2; `Ω(log t)` rounds at optimal resilience). The run constructions of Proposition 1 and
Lemma 1 are correct, and the one gap, in the step to Lemma 2 and Proposition 2, where scaling the
blocks by `c = t/t_k` works only when `t_k` divides `t`, is closed by changing the block sizes. The
matching upper bounds of §5, and so the optimality of four read rounds, were not checked.

## Mistakes in the paper

### ✏️ Slips
- Proof of Lemma 2: "solving for k" derives `t ≥ t_k ⇒ k ≤ ⌊log ⌈(3t+1)/2⌉⌋`, while the proof needs
  the converse; both directions hold (`tseq_le_iff`).
- §4, proof of Lemma 1: "the state of `{B_l, C_l}` at the end of `Δpr_1`" should be `Δpr_l`.

### Typos
- §3, general step of Proposition 1: the index expressions (`σ_{((j mod 4)/j)(k−i−1)}`, footnote 3)
  are hard to parse; Fig. 1 gives the intended runs.

## Proof gaps (statements true)

### 🔧 Proposition 2 and Lemma 2 (scaling Lemma 1 to `t ≥ t_k`)
"By carefully choosing `c = t/t_k`" (Proposition 2), and "this is valid even with `R ≥ k` readers and
`t ≥ t_k` faults" (Lemma 2): multiplying the blocks of Lemma 1 by `c` needs an integer `c`, so the
argument covers only `t_k ∣ t`.

**Impact.** Statements true; repaired by another block-size assignment (`exists_fits`).

**Details.** For `t = c·t_k + d` with `0 < d < t_k`, uniform scaling by `c = ⌊t/t_k⌋` gives
`3c·t_k + c` objects with `c·t_k` faults, fewer than the claimed `3t + c` objects. Lemma 2 is the case
`S = 3t + 1`, and it relies on the same step.

**Repair.** The construction of Lemma 1 only needs *upper* bounds: every set of objects that is
malicious in some run, or skipped by a terminated round, has at most `t` objects (`Fits`). The
blocks `B_k`, `C_k` and `B_{k+1}` never lie in a common such set. So we take `c` times the paper's
sizes, add `d` objects to each of these three blocks, and get `3t + c` objects
(`exists_fits`, `write_lb_general`, `lemma2`, `proposition2`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous message passing between one writer, readers `Rd` (`R = card Rd`) and objects `Obj`
  (`S = card Obj`). At most `t` objects are malicious; there is no authentication. Objects never
  communicate with each other or with clients other than by replies, and clients do not message each
  other. Clients are one-shot.
- Deterministic protocols (`Proto`): objects reply as a function of their log; writes take exactly
  `K` rounds and reads exactly `N` rounds. In each round a client sends to all objects, which process
  a client's round messages in FIFO order. The round may terminate once `S − t` objects replied, and
  the scheduler decides when. This is the round model of [1]. The paper's own Definition 1 is more
  restrictive for the adversary: a round may end without the reply of `s_i` only if `s_i` is faulty
  or faulty in some indistinguishable run. So the Lean theorems are formally weaker than the
  paper's (a protocol cannot wait for extra replies after spotting a faulty one). The paper's runs
  satisfy its condition: in a symbolic replay of all runs, every terminated round has a run with
  the same client view in which the skipped objects and all forgers so far are at most `t`. This
  check is not in Lean.
- A malicious object may overwrite its state at any time (`forge`), which is the Byzantine behaviour
  used in all proofs.
- Atomicity is the paper's §2.2 definition, for histories with one write. `Proto.Atomic P t ⊥`
  quantifies over all runs and all malicious sets of size `≤ t`. Restricting the runs (one-shot,
  forging-only Byzantine) only strengthens the impossibility results.
- Operations take a fixed number of rounds (`K` for writes, `N` for reads); adaptive round counts are
  not representable. Proposition 1 is proved for `N = 2`, Lemma 1/2 and Proposition 2 for `N = 3`;
  "at most `N`" follows by padding with no-op rounds, which is not formalized (writes: every
  fixed `K` up to the bound is covered).

**Proof method.** Each construction is run with a protocol-independent label protocol whose messages
are `(instance, round)` labels (`Sim.lean`, `Label.lean`). A label run is checked to be *canonical*:
every terminated round sees its canonical transcript `T (i, q)`. A canonical label run maps to a run of
an arbitrary protocol with the same schedule (`sim`). So every read instance returns the same value in
all runs, and the atomicity chain is short. The paper's runs were first replayed symbolically in
Python (all `k ≤ 8`); this found no error in the constructions.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Proposition 1 (`S ≤ 4t`, `R > 3`: no 2-round reads) | `proposition1` | `Main.lean` |
| Proposition 1, block form (any 4 blocks of `≤ t` objects) | `ReadLB.read_lb` | `ReadLB.lean` |
| Lemma 1 (`3t_k+1` objects, `t_k` faults, `k` readers) | `lemma1` | `Main.lean` |
| Lemma 1, block form (any assignment that `Fits`) | `WriteLB.write_lb` | `WriteLB.lean` |
| Lemma 2 (`S ≤ 3t+1`) | `lemma2` | `Main.lean` |
| Proposition 2 (`S ≤ 3t + ⌊t/t_k⌋`) | `proposition2`, `write_lb_general` | `Main.lean` |
| `t_k = (2^{k+2} − (−1)^k − 3)/6` | `tseq_closed_form`, `tseq_closed` | `Main.lean`, `Arith.lean` |
| `⌊log ⌈(3t_k+1)/2⌉⌋ = k`; `t_k ≤ t ⇔ k ≤ ⌊log ⌈(3t+1)/2⌉⌋` | `log_tseq`, `tseq_le_iff` | `Arith.lean` |
| Equations (1)–(3) (`|M_l| = t_{l+1}`, `|P_l| = |𝒞_l| = t_k − t_{l−2}`) | `paper_sizes` | `Arith.lean` |
| Round model, atomicity (§2) | `Proto`, `Proto.exec`, `AtomicHist`, `Proto.Atomic` | `Model.lean` |

**Not formalized.** The matching upper bounds of §5 (built from other papers' algorithms and
transformations) and the secret-value model.

**Trust.** No `sorry`; the listed theorems use only `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `Sanity.atomic_one_object` exhibits an atomic protocol in the same model (one object,
`t = 0`), so `Proto.Atomic` is satisfiable outside the theorems' ranges. Proposition 1 is proved for
every `S ≤ 4t` directly, without the resilience bound `S ≥ 3t + 1`. Lemma 1 is proved also for
`k = 1`, which the paper takes from [1].
