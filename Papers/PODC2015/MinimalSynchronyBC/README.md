# Minimal Synchrony for Byzantine Consensus — PODC 2015

Zohir Bouzid, Achour Mostéfaoui, Michel Raynal. *Minimal Synchrony for Byzantine Consensus.* PODC 2015.
DOI [10.1145/2767386.2767418](https://doi.org/10.1145/2767386.2767418). Formalized version: the HAL deposit
hal-01178651v1 (July 2015). Its numbering is that of the proceedings. There is no arXiv version. The full version
cited as [6] ("Tech Report 2025, IRISA, 2015"; 2025 is the report number) is not available to us, so the proofs of
Lemmas 1 and 2 ("Proof in [6]") were reconstructed. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The EA object of Figure 3 is not live: **Lemma 2 (EA-Termination) and Theorem 3 are
false**. As a result, the consensus algorithm of Figure 4 does not terminate, so **Theorem 4 is false**. This holds
even in a synchronous run in which the only faulty process crashes at the start. The proof of Lemma 3 has two
further gaps. The paper therefore does not establish its headline claim that an eventual `⟨t+1⟩bisource` suffices for
signature-free Byzantine consensus. Theorems 1 and 2 (CB-broadcast, adopt-commit), Lemma 1 and the safety part of
Theorem 4 are correct and are proved.

## Mistakes in the paper

* **Lemma 2 / Theorem 3 are false: Figure 3 can block forever.** A correct process that returns at line 4 never
  executes line 5, so its `timer[r]` is never set. It then broadcasts `EA_RELAY[r]` only if it receives
  `EA_COORD[r]` from the coordinator (lines 15–19). If `coord(r)` is faulty and silent, these processes never relay.
  The processes that did not return at line 4 can then wait at line 6 forever for `n − t` relays.
  *Counterexample* (`n = 7`, `t = 2`, `m = ⌊(n−(t+1))/t⌋ = 2`):
  * Process `p₁ = coord(1)` crashes at the start.
  * Three correct processes propose `true` and three propose `false`.
  * The run is synchronous (all delays ≤ 1), so every correct process is a `⟨t+1⟩bisource`.
  * `CB[0]` returns each process its own proposal (three estimates `true`, three `false`). `CB[1]` (EA round 1)
    gives `aux = true` to five processes and `false` to the sixth.
  * Two processes see five `true` messages first and return at line 4. The other four see a mixed first five, set
    their timers and relay `⊥`.
  * Only `4 < n − t = 5` relays are ever sent, so the four wait forever at line 6 of round 1. The two others wait
    forever inside the CB of `AC_OBJECT[1]`, which has only two `AC_PROP` messages, fewer than `t + 1 = 3`.

  So in a run of Figure 4 where every correct process invokes `EA_propose(1, −)`, four invocations never return
  (`lemma2_false`), and no correct process ever decides (`theorem4_termination_false`). The paper's
  proof of Theorem 4 relies on EA-Termination in exactly this situation ("it follows from the EA-Termination and
  AC-Termination properties that they all terminate the first round"). *A repair* is to set the timer before
  returning at line 4, so that every correct process relays. With it, the same run decides
  (`repaired_blocking_run_decides`). We do not know whether the repaired algorithm is correct, because of the next
  item.
* **Lemma 3's proof ignores line 4 (proof gap; we do not know whether the statement holds).** The proof picks a
  round `r > 2δ` coordinated by the bisource `p_ℓ`, with `F(r) ⊆ C`, and concludes that every correct process returns
  the coordinator's value `w` "after executing lines 7–10". Processes that return at line 4 never reach line 7, and
  they may return a different value. *Lean witness*, for the EA object alone:
  * `n = 4`, `t = 1`, a synchronous run.
  * Round 15 has `coord(15) = p₃` correct and `F(15)` equal to the set of correct processes. The coordinator is a
    bisource with `X⁻ = X⁺ ⊆ F(15)`, so it is a round of exactly the kind the proof chooses.
  * The Byzantine process RB-broadcasts `EA_PROP1(false)` consistently and sends `EA_PROP2[15](true)`.
  * Process `p₁` returns `true` at line 4. The coordinator champions its own `false`, which `p₂` and `p₃` return.

  (`lemma3_proof_fails`.) Lemma 3 needs infinitely many such rounds, so this refutes the proof, not the statement.
  It also leaves the repaired algorithm unproven.
* **Lemma 3 also uses `p_k ∈ X⁻_ℓ ⊆ F(r)`, but the chosen round only guarantees `X⁺_ℓ ⊆ F(r) ⊆ C` (proof gap,
  fixable).** Choose instead `r` with `X⁻_ℓ ∪ X⁺_ℓ ⊆ F(r) ⊆ C`. Such rounds exist infinitely often:
  `|X⁻ ∪ X⁺| ≤ 2t + 1 ≤ n − t` because both sets contain `ℓ`. Our `lemma3_proof_fails` round satisfies the stronger
  choice. This point was not formalized further.
* **Minor.**
  * AC-Obligation and EA-Validity are stated as "if all correct processes propose `v`". Theorem 4 uses them in rounds
    that some correct processes may never reach. We state and prove them for the correct processes that invoke the
    object, which is what the proof needs.
  * The proof of Theorem 4 uses that `cb_valid` sets only grow, and that rounds take time (otherwise `CB[0]`'s
    "never updated after round `r₀`" can fail). Neither is stated.
  * Feasibility needs `t ≥ 1` for `⌊(n−(t+1))/t⌋`; we use `n − t > m t`.
  * "Decides and stops" must not stop the RB layer.
  * Claim C says the timer is set "at line 8"; it is set at line 5.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Abstract layer*, mirroring the paper's modular proofs (`Basic`, `CB`, `AC`, `EA`, `Consensus`):
  * `n` processes, a faulty set `B` with `|B| ≤ t < n/3`, time `ℕ`.
  * RB-broadcast is a primitive given by its four properties, over time-indexed delivery traces (`RBSpec`).
  * CB, AC and EA are specified by their properties on what correct processes observe (`CBSpec`, `ACSpec`,
    `EAValidity`).
  * Figures 1 and 2 are given as rules on traces; all "pick any" choices are adversarial. They are proved to meet
    their specifications.
  * Figure 4 is proved safe from the object specifications, and live *assuming* the EA specification.
* *Operational layer* (`Machine`, `Counterexample`):
  * Figures 1–4 are written as one deterministic `Algorithm` of CSLib's partially synchronous Byzantine model
    `Cslib.Byzantine.PartialSync`: authenticated links, discrete ticks, adversarial delivery times and Byzantine
    messages, timers counted in ticks.
  * RB is idealized: a correct process RB-broadcasts by sending to all, and the first `rb` message per
    sender and instance is delivered. Faulty processes must send RB messages consistently (`RBAdmissible`).
  * Asynchrony with an eventual `⟨k⟩bisource` is `Run.BisourceValid t k` (staged in `Podc/`).
  * Both counterexample runs are *synchronous* (`Run.SyncValid`), so they are valid in every bisource model.
  * In both runs every "pick any" choice is forced (a single candidate), so the counterexamples do not depend on how
    `Machine` resolves nondeterminism.
* The `coord(r)`/`F(r)` schedule is the paper's, with `F₁ … F_α` in `List.sublistsLen` order. The blocking run
  never consults `F`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 1 (Fig. 1 implements CB-broadcast) | `theorem1` | `CB.lean` |
| Feasibility `n − t > mt` ⇒ a value with `t+1` correct proposers | `feasible_of_mValued` | `CB.lean` |
| Thm 2 (Fig. 2 implements adopt-commit) | `theorem2` | `AC.lean` |
| Lemma 1 (EA-Validity) | `lemma1`, `lemma1_line4` | `EA.lean` |
| Lemma 2 / Thm 3 (EA-Termination): **false** | `lemma2_false` | `Counterexample.lean` |
| Lemma 3 (proof): **"good" round with disagreement** | `lemma3_proof_fails` | `Counterexample.lean` |
| Thm 4, CONS-Validity / CONS-Agreement | `Fig4.validity`, `Fig4.agreement` | `Consensus.lean` |
| Thm 4, CONS-Termination given an EA object (paper's composition) | `Fig4.termination` | `Consensus.lean` |
| Thm 4, CONS-Termination: **false** | `theorem4_termination_false` | `Counterexample.lean` |
| Repair of Fig. 3 unblocks the run | `repaired_blocking_run_decides` | `Sanity.lean` |

**Not formalized.**
* An implementation of RB, which is a primitive here.
* The real-time part of Lemma 3 (Claim C).
* The parameterized EA of Section 5.4 and its `αn`-round bound.
* Whether the repaired algorithm terminates.
* No bridge from the operational machine to the abstract layer. The safety theorems are proved at the level of the
  paper's object specifications.

**Trust.**
* No `sorry`. The listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
* Concrete runs are checked by `decide +kernel` on CSLib's memoised simulator `simHist`. "Stuck forever" follows from
  the generic quiescence lemma `Run.st_eq_of_quiescent`.
* Non-vacuity checks (`Sanity.lean`):
  * The machine decides in fault-free and crash runs (`sanity_decides`, `sanity_decides_crash`).
  * A concrete execution satisfies all hypotheses of `Fig4.termination` (`triv_follows`, `triv_live`).

**Infrastructure / CSLib candidates** (staged in `Podc/`):
* `Podc/Computability/Distributed/Byzantine/PartialSync/Timeliness.lean`: `Run.EventuallyTimely`, `Run.IsSink`,
  `Run.IsSource`, `Run.IsBisource`, `Run.BisourceValid` and `Run.SyncValid.isBisource`.
* `Podc/Computability/Distributed/Byzantine/PartialSync/Quiescence.lean`: `Run.st_eq_of_quiescent`.
