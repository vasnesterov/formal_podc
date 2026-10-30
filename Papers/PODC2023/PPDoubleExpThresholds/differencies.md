# Differences between the formalization and the paper

Paper: P. Czerner, *Population Protocols Decide Double-exponential Thresholds*, arXiv 2204.02115 v2
(full version of the PODC 2023 brief announcement). Numbering follows v2.

## Verdict

**❌ False claim.** Lemma 11(c) is a numbered lemma and it is false (R1). The fix "`j < i`" is not a typo
with evident intent (R3): the paper's proof of Lemma 12(c) applies 11(c) exactly in the false case
(`IncrPair` at level `i − 1` on `(i−1)`-high configurations). It is not a headline result (R5). All
headline results (Theorems 1, 2, 3, 5) are true and verified. Several proofs needed repairs (🛠️-level
items below).

## False statements

1. **Lemma 11(c)** ("`IncrPair(x, y)` is `j`-robust for `j ≤ i`") is false for `j = i`.
   Counterexample: `n = i = 1`, `x₁ = 0, x̄₁ = 1, y₁ = 1, ȳ₁ = 0` (1-high). `IncrPair(x̄₁, ȳ₁)` returns
   a 1-proper configuration (`lemma_11c_false`, `Lemma11c.lean`). We prove 11(c) for `j < i`
   (`incr_robust_lt`, field `LevelOK.incrR`). The proof of Lemma 12(c) for `j = i − 1` uses the false
   case; we replace it by a direct argument (`large_robust_mid`, `LargeSym.lean`): the walk keeps the
   level-`(i−1)` pair sums, one of them exceeds `N_{i−1}` after line 9, and termination follows from
   the symmetry of loop iterations (`Iter`, `iter_symm`). We also prove `IncrG`: `IncrPair` terminates
   on configurations with pair sums `≥ Nᵢ`, never restarts, and keeps that property.

## Proof gaps and wrong claims inside proofs (statements true)

2. **Proof of Theorem 3**: "`N_{i+1} = (Nᵢ+1)²` and `N₁ = 1`, implying `k ≥ 2^(2^n)`" is false
   (`k = 2, 10, 60` for `n = 1, 2, 3`; `S_lt_claim`). The statement's `k ≥ 2^(2^(n−1))` holds for
   `n ≥ 1` (`S_ge`, via `Nᵢ + 1 ≥ 2^(2^(i−1))`). Theorem 1's `2^(2^n)` follows with `n + 1` levels.
3. **Proof of Theorem 3**: "distribute the remaining `m − |C| ≤ 2N_j` units" states a bound that is
   true but too weak for the argument: `< 2N_j` is needed (equality would give a `j`-proper
   configuration). The paper's choice of `j` gives `<`. Our construction is `exists_good`.
4. **Proposition 16**: the initial value `v_OF` of the leader election must be `false`. The paper
   allows any value. With `v_OF = true` and fewer than `|F|` agents, an `OF` agent with value `true`
   can be created while no `IP` agent ever is, so the protocol would output `true` on `x < i`.
5. **Lemma 15**: the claim that the elected agents are in their initial states "at the moment this
   happens" needs new election invariants: prefix counts `InvJ`, empty levels `InvK`, fresh agents
   `InvFr` (`MachineToProtocolElect.lean`). The fairness argument for Proposition 16 needs an
   elected configuration to be reachable from every reachable configuration (`reach_good`), not only
   from the initial one.
6. **Appendix B.3 construction**: the paper assumes `Y ≠ IP` w.l.o.g. in `X := f(Y)`, so transitions
   for `Y = IP` are added. Map states `X^i_map` count as agents of `X` in the wildcard of `⟨elect⟩`.
   The stages of `V_□` are `{none, done}`. On p. 27 the last `⟨move⟩` rule should read
   `v ∈ 𝓕_{V_y}` (typo).
7. **Appendix B.2 construction** (Proposition 14): the `restart` helper must skip the pair `(x, x)`
   (moves between equal registers are not machine instructions). The pointer assignment `V_y := V_□`
   needs a clamped map `f : 𝓕_{V_□} → 𝓕_{V_y}`. Return-address pointers are created only for used
   procedures (`Main` and called ones). Each procedure block ends with a guard self-loop, because a
   program jumping past the end of a procedure hangs.

## Typos

8. `IncrPair`: "Effect: `βx + y (mod β²)` decreases by 1". The procedure *increments* the counter, as
   the prose and Lemma 11(a) say.
9. `Large`, line 12: `CheckProper(i − 2)` should be `AssertProper(i − 2)`.
10. Proof of Theorem 3: "configurations where registers sum to `i`" should be "`m`".

## Statements: form of the Lean versions

- **Theorem 1** (`theorem_1`): explicit bounds `|Q| ≤ 116160 n + 151040`. There is a single input
  state, the protocol decides `x ≥ k` with `k = 2 ∑ᵢ₌₁ⁿ⁺¹ Nᵢ + i ≥ 2^(2^n)`, and Theorem 2 (almost
  self-stabilisation) is included.
- **Theorem 3** (`theorem_3`): for `n ≥ 1` (for `n = 0`, `2^(2^(n−1))` is not meaningful: R2). The
  program of Section 6 itself (`prog n`) is well formed, has `4n + 1` registers and size
  `≤ 363 n + 108`, and decides `x ≥ k` with `k = 2 ∑ᵢ₌₁ⁿ Nᵢ`. `prog_decides` holds for every `n`.
- **Theorem 5** (`theorem_5`): `i ≤ 20 s + 20`, `|Q| ≤ 320 s + 320`, and a single input state, for
  well-formed programs (Proposition 14's `WellFormed`) over a nonempty register set (R2).
- **Proposition 14** (`proposition_14`): explicit size `≤ 20 λ + 20`. It adds that all pointer
  domains are nonempty and that every register configuration is the register part of an initial
  machine configuration.
- **Proposition 16** (`proposition_16`): `i = |F| ≤ size` and `|Q'| ≤ 16·size`. It needs the
  hypothesis that pointer domains are nonempty: this is in Definition 6 but not in the Lean
  structure `Machine`. Without it, a machine with `L = 0` has no initial configuration and decides
  everything vacuously.
- **Lemma 4**: formalized in terms of the reachable configurations of the program (finitely many).
  - (a) `lemma_4a`: if `C` is `j`-low and `(j+1)`-empty, some reachable configuration can no longer
    restart, and from every reachable configuration one is reachable from which `OF = false` forever.
  - (b) `lemma_4b`: for `n`-proper `C`, some reachable configuration cannot restart, and from every
    such configuration one is reachable from which `OF = true` forever.
  - (c) `lemma_4c`: otherwise, from every reachable configuration a `restart` is reachable.

  "May stabilise" is read in this sense. The preamble "can only restart or stabilise" is the
  combination used in `decides_of_restart`.
- **Lemmas 8–12**: `post(C, p)` is formalized as the specification `Spec`: the set of returns is
  given exactly, there are no restarts, and the call terminates. `C, f ↛ ⊥` is `Terminates`: from
  every configuration reachable during the call, a return or a restart is reachable, which is the
  fairness reading of the paper. Lemmas 10(a) and 12(a) are not stated separately; they are the
  special cases of (b) used in the proofs. Lemma 8's "robust" follows directly from its `post` and is
  not stated separately. The lemmas are proved together by induction on the level (`levels`).

## Modelling choices

- **Programs** (`Program.lean`): flat code with an explicit call stack. Procedures are written in a
  structured syntax (`Stmt`, `BExp`) and compiled; `for` loops are macros, expanded. Boolean `∧`/`∨`
  in conditions are evaluated left to right with short-circuiting. Procedures without an explicit
  `return` return `false`. If no instruction applies, the program hangs (stays).
- **`restart`** keeps `OF` and replaces the registers by any configuration with the same total; this
  is the paper's implementation in Appendix B.2. `Main` sets `OF := false` first anyway.
- **Decision** (`Program.Decides`): every globally fair run that starts at `Main` with any registers
  and any `OF` stabilises to `φ(total)`.
- **Well-formedness** adds "moves are between distinct registers" (true for the construction;
  machines require it, Def. 6). Swap-size: the number of ordered pairs `(x, y)`, `x ≠ y`, connected
  by a chain of swaps.
- **Registers** `Reg n`: `r i k` is register `k ∈ {x, x̄, y, ȳ}` of level `i + 1`, plus `R`;
  `reg n i k` maps out-of-range levels to `R` (never used). Convention `N₀ = 0`.
- **Machines** (`Machine.lean`): all pointer values live in one type `Val Q`. Deviation from
  Definition 13: `Exec` executes a non-jump instruction `I_L` and sets `IP := L + 1`, after which the
  machine hangs. To simulate this, the protocol's `IP` agents may hold `L + 1`, and the side
  conditions `i < L` of the transitions are dropped.
- **Protocols** (`Protocol.lean`): configurations are multisets of states, and `C → C'` includes
  `C = C'`. Global fairness and runs come from CSLib (`Cslib.TransitionSystem.Run.GloballyFair`).
  Output: `true` if all agents are accepting, `false` if none is. Almost self-stabilisation
  (Def. 7): runs from any configuration with at least `|Q|` agents in input states.
