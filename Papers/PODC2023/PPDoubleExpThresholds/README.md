# Population Protocols Decide Double-exponential Thresholds — PODC 2023

Philipp Czerner. *Brief Announcement: Population Protocols Decide Double-exponential Thresholds.* PODC 2023.
DOI [10.1145/3583668.3594571](https://doi.org/10.1145/3583668.3594571). Formalized version: arXiv
[2204.02115](https://arxiv.org/abs/2204.02115) v2 (full version with appendices); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ❌ False claim.** The main results hold. Theorem 1 says there are population protocols with
`O(n)` states deciding `x ≥ k` for some `k ≥ 2^(2^n)`. Theorem 2 says they are almost self-stabilising.
Theorem 3 (the succinct population program), Theorem 5 (programs to protocols), Lemma 4 and
Propositions 14 and 16 are verified too. But **Lemma 11(c) is false**: `IncrPair` is not `i`-robust. The
proof of Lemma 12(c) relies on it, and we re-proved 12(c) by another argument. Several other proof steps
needed repairs.

## Mistakes in the paper

* **Lemma 11(c) is false (for `j = i`).** The lemma claims `IncrPair(x, y)` is `j`-robust for all
  `j ≤ i`. That means: called on a `j`-high configuration, every return is `j`-high again. Take one
  level (`n = i = 1`, `N₁ = 1`) and `x₁ = 0, x̄₁ = 1, y₁ = 1, ȳ₁ = 0`. This configuration is
  `1`-high: it is not `1`-proper, and both pair sums are `1`. `IncrPair(x̄₁, ȳ₁)` increments the
  two-digit counter `ctr = x̄₁·2 + ȳ₁` from `2` to `3`. It returns `x̄₁ = ȳ₁ = 1`, `x₁ = y₁ = 0`,
  which is `1`-proper, so not `1`-high. The same happens at every level, starting one counter step
  before the proper value. The proof of 11(c) overlooks that lines 3 and 5–7 change the level-`i`
  registers. Only `j < i` holds, and we prove that. Lemma 12(c) ("`Large` is robust") needs exactly
  the false case: `Large` at level `i` calls `IncrPair` at level `i − 1` on `(i−1)`-high
  configurations. Lemma 12(c) is still true, for a different reason. The walk of `Large` never
  changes the pair sums of level `i − 1`. Once line 9 has passed, one of these sums exceeds
  `N_{i−1}`, so the configuration cannot become `(i−1)`-proper. We prove termination with the
  paper's own symmetry idea: one loop iteration can be undone by another. In Lean this is the
  explicit relation `Iter` and `iter_symm`. (`lemma_11c_false`; `large_robust_mid`)
* **Proof of Theorem 3: the bound `k ≥ 2^(2^n)` is wrong.** The proof says
  "`N_{i+1} = (N_i+1)²` and `N₁ = 1`, implying `k ≥ 2^(2^n)`" for `k = 2 ∑ᵢ₌₁ⁿ Nᵢ`. This fails
  already for `n = 1, 2, 3` (`k = 2, 10, 60`). The bound in the theorem's own statement,
  `k ≥ 2^(2^(n−1))`, is correct, and so is Theorem 1 (apply Theorem 3 with `n + 1` levels).
  (`S_lt_claim`, `S_ge`)
* **Proposition 16: the initial value of `OF` must be `false`.** The construction lets the leader
  election give `OF` an arbitrary initial value `v_OF`. With fewer than `|F|` agents the election
  can create an `OF` agent but never an `IP` agent. With `v_OF = true`, that agent would broadcast
  `true` on inputs `x < i`, where `φ′(x)` is false. Fixing `v_OF = false` repairs the construction.
* **Proof of Lemma 15 / Proposition 16 is incomplete.** The proof says the agents are in their
  initial states `X^v_none` "at the moment this happens". Making this precise needs three new
  invariants of the election (prefix counts, empty levels, fresh agents). The fairness argument
  also needs the elected configuration to be reachable from every *reachable* configuration, not
  only from the initial one. (`Machine.lemma_15`)
* **Smaller gaps in the constructions of Appendix B.** In Proposition 14, the `restart` helper must
  skip moves between equal registers, and `V_y := V_□` needs a clamped map `f`. In Proposition 16,
  the paper assumes `Y ≠ IP` "w.l.o.g.", so transitions for `Y = IP` must be added. Map states also
  have to count as agents of their pointer in `⟨elect⟩`.
* **Typos and slips.** In `IncrPair`, the "Effect" line says the counter "decreases by 1", but the
  procedure increments it (prose and Lemma 11(a) say so). Line 12 of `Large` calls
  `CheckProper(i − 2)`, which should be `AssertProper(i − 2)`. In the proof of Theorem 3,
  "registers sum to `i`" should be "`m`", and the bound "`m − |C| ≤ 2N_j`" is too weak for the
  argument: the strict `< 2N_j` is needed (with equality the configuration would be `j`-proper, not
  `j`-low), and it does hold by the choice of `j`. On p. 27, the last `⟨move⟩` rule
  should read `v ∈ 𝓕_{V_y}`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Population protocols** (Section 3, `Protocol.lean`): states `Q`, transitions `(q, r ↦ q', r')`, input
  states `I`, accepting states `O`. Configurations are nonempty multisets. `C → C'` if `C = C'` or a
  transition fires. A protocol decides `φ` if every **globally fair** run (CSLib `Run.GloballyFair`) from
  an initial configuration stabilises to `φ`. The model is deterministic and fairness-based, with no
  probability and no leaders. Theorem 1's predicates are unary: `φ(|C|)` with one input state.
  Almost self-stabilisation (Def. 7) quantifies over runs from any configuration with at least `|Q|`
  agents in input states.
* **Population programs** (Section 5, `Program.lean`): registers `R → ℕ`, flat code with a call
  stack, an output flag `OF`, and `restart`. A restart replaces the registers by any configuration
  with the same total and restarts `Main`, keeping `OF`. The paper's pseudocode is written in a
  structured syntax and compiled to flat code; the `for` loops are expanded. A program decides `φ`
  if every globally fair run from `Main` stabilises to `φ(total)`. Well-formedness (acyclic calls,
  moves between distinct registers) is proved for the construction. Size is
  `|Q| + #instructions + swap-size`.
* **Population machines** (Def. 6/13, `Machine.lean`): registers, pointers with finite domains, and
  instructions `x ↦ y`, `detect x > 0`, `X := f(Y)`, with the paper's semantics. Nonempty pointer
  domains are a hypothesis of Proposition 16.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (`O(n)` states, `k ≥ 2^(2^n)`) and Theorem 2 (almost self-stabilising) | `theorem_1` | `Theorem1.lean` |
| Theorem 3 (program of size `O(n)` deciding `x ≥ k`, `k ≥ 2^(2^(n−1))`) | `theorem_3` (`prog_decides`, `wellFormed`, `size_le`, `S_ge`) | `Theorem3.lean`, `WellFormed.lean` |
| Theorem 5 (programs to protocols) | `theorem_5` | `Theorem1.lean` |
| Lemma 4 (a), (b), (c) | `lemma_4a`, `lemma_4b`, `lemma_4c` | `Lemma4c.lean`, `Lemma4.lean`, `Lemma4Main.lean` |
| Lemma 8 | `lemma_8` | `Lemma8.lean` |
| Lemmas 9, 10, 11(a,b), 12 at every level | `levels` (fields of `LevelOK`) | `Levels9to12.lean` |
| Lemma 11(c) restricted to `j < i` | `LevelOK.incrR` (`incr_robust_lt`) | `Incr.lean` |
| Lemma 11(c) is false | `lemma_11c_false` | `Lemma11c.lean` |
| Lemma 12(c) for `j = i − 1` (new proof) | `large_robust_mid` | `LargeSym.lean` |
| Proposition 14 (size `≤ 20λ + 20`) | `proposition_14` | `ProgramToMachine.lean` |
| Lemma 15 | `Machine.lemma_15` | `MachineToProtocolElect.lean` |
| Proposition 16 (`≤ 16·size` states, `i ≤ size`) | `proposition_16` | `MachineToProtocol.lean` |

The `O(·)` bounds are explicit. The program has `4n + 1` registers and size `≤ 363n + 108`. The
protocol of Theorem 1 has `≤ 116160n + 151040` states.

**Not formalized.** The simplified model of Section 4 and the intuition sections. The lower-bound
discussion is cited work.

**Trust.** No `sorry`. `theorem_1`, `theorem_3` and `lemma_11c_false` use only the axioms
`propext`, `Classical.choice` and `Quot.sound`. Non-vacuity: Proposition 14 also shows that every
register configuration is the register part of an initial machine configuration. The protocol
predicates are about all fair runs from all initial configurations, and every finite system has
fair runs (CSLib `exists_globallyFair`). Runs and global fairness come from CSLib
(`Cslib.TransitionSystem`), and transitions from `Cslib.PopulationProtocol.Transition`.
CSLib candidates: `trMap`/`fires_map`, `restrictTo`, `bcast` (`MachineToProtocolGeneric.lean`) and
`forall_fair_iff_reach` (`Stable.lean`).
