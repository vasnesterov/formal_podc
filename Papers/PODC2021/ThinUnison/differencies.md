# Differences between the formalization and the paper

Paper: Y. Emek, E. Keren, *A Thin Self-Stabilizing Asynchronous Unison Algorithm with Applications to
Fault Tolerant Biological Networks*, PODC 2021. Formalized against the full version in `papers/2021/`
(stamped arXiv:1712.00285v2, 19 Aug 2021; `index.json` lists arXiv 2102.12787).

Verdict: **Theorem 1.1 is correct** (formalized in full, with explicit constants). Every gap
below is minor, and each has been repaired in the formalization.

## Model

1. **Deterministic transition function.** The paper's SA model has randomized transitions
   `δ : Q × {0,1}^Q → 2^Q`. We formalize only the deterministic case, `δ : Q → Set Q → Q`
   (`Cslib.StoneAge.Algorithm`). AlgAU is deterministic, so Theorem 1.1 is unaffected.
2. **Schedules.**
   - A schedule is any `A : ℕ → Set V`. Empty activation sets are allowed, which makes the setting
     slightly more general.
   - Fairness is the paper's "no node starvation": every node is activated infinitely often.
   - The round operator `ϱ` and `R(i) = ϱ^i(0)` are as in the paper. For an empty node set we define
     `ϱ(t) = t`; all theorems are vacuous or trivial there.
3. **Graph class.** "Diameter at most D" is `G.ediam ≤ D` (Mathlib): any two nodes are joined by a walk
   of length at most `D`. This implies connectivity.
4. **Levels and turns.**
   - Levels are integers with `1 ≤ |ℓ| ≤ k`.
   - A turn is the structure `Turn k`: a level, a faulty flag, and validity proofs (faulty requires
     `|ℓ| ≥ 2`).
   - The AU clock of a turn is its position on the cycle, in `ZMod (2k)` (`clock`). The output is
     `none` on faulty turns.
   - `card_turn` proves that there are exactly `4k − 2` states.
5. **Transition rules (Table 1).**
   - AA condition. We implement "every sensed turn is able and its level is `ℓ` or `φ(ℓ)`".
     `aaCond_iff` proves this equivalent to the paper's "good ∧ `Λ ⊆ {ℓ, φ(ℓ)}`".
   - AF and FA are verbatim.
   - A model checker (`tools/algau.py`) checks the reading exhaustively on K2, K3, P3 and C4. It
     confirms Obs 2.1, 2.3, 2.5 and Lemma 2.10, and that no fair execution avoids good
     configurations.
6. **AU specification (`Cslib.StoneAge.AUFrom`).**
   - From time `T` on, all nodes are in output states.
   - Safety: neighbouring clocks differ by `−1`, `0` or `+1`.
   - Clocks change only by `+1`.
   - Liveness: at least `i` output changes in `[t, ϱ^{d+i}(t))` for every `t ≥ T`.
   - The paper uses `d = diam(G)` (`theorem_1_1_diam`). We prove the statement for every `d ≤ D`
     with `G.ediam ≤ d`.

## Theorem 1.1

7. **Statement.**
   - We state stabilization by the explicit time `R(N(D))`, where
     `N(D) = ∑_{j=1}^{k-1}(k-j)(k-j-1) + (2k−3) + (D+1)·2(k−1)(2k−2)` and `k = 3D+2`.
   - `stabRounds_le` proves `N(D) ≤ 70 (D+1)^3`, which is the paper's `O(D³)`.
   - The proof works verbatim for every `k ≥ 3D+2` (`theorem_1_1_general`). The paper fixes
     `k = 3D+2`.

## Section 2.3 (analysis)

8. **Obs 2.7/2.9.**
   - We use the magnitude form: along a walk of protected nodes `|λ|` grows by at most 1 per edge
     (`natAbs_le_of_walk`). This replaces the cyclic level distance.
   - Obs 2.9 needs `|λ_v^s| < k − d` only for `t ≤ s < t'`, not for `s = t'`. With `s = t'` included,
     as in the paper's statement, the application in Lemma 2.20 at `d = D` would fail: there `v` is at
     level exactly `2D+2 = k − D` at time `t'`. The paper's proof of Obs 2.9 only uses `s < t'`.
9. **Obs 2.8 / Lemma 2.11 (liveness).**
   - Obs 2.8's proof ("apply Obs 2.7 to shortest paths") omits a step. Obs 2.7 gives pairwise cyclic
     level distances `≤ D`. To conclude that all levels lie in a window of `D+1` consecutive levels, one
     needs a short extremal-point argument: take the extreme levels on either side of a fixed node's
     level; their distance must be the short arc because `2k = 6D+4 > 3D`. The statement is true. The
     formalization uses an equivalent integer lifting along walks from one node instead.
   - Lemma 2.11 compares levels cyclically ("`ℓ_min(i+1) > ℓ_min(i)`"). This is only a presentation
     issue (it means "advances along the window").
   - Formalization: unwrapped integer clocks `U_v(t)` (`Good.lean`: `exists_offsets`, `uclk_inv`,
     `uclk_rho_iter`) with "min U grows by ≥ 1 per round". The statement of Lemma 2.11 holds as
     stated.
10. **Lemma 2.12.**
    - Formalized exactly, bound `ϱ^{2(k−|ℓ|)+1}(t)` (`fa_core`, `lemma_2_12`).
    - The step "no neighbour can move to turn `ψ^{+1}(ℓ)` from another turn" also needs that an able
      neighbour at `ψ^{+1}(ℓ)` cannot come from the faulty turn there. This holds because FA changes
      the level; it is proved explicitly as step (B).
11. **Lemma 2.13.**
    - The time bound is written `ϱ^{2(k−|ℓ|)+2}(t')` with an undefined `t'`. It should be `t`.
    - The proof uses that `v` (the endpoint with `λ_v = ℓ`) performs an AF transition. That is
      impossible if `|ℓ| = 1`: level `±1` has no faulty turn, and a node at `±1` that is not protected
      is stuck.
    - Hence the lemma is only proved under `2 ≤ |ℓ|`. This is the only way it is used: in Lemma 2.14
      with `|ℓ'| ≥ |ℓ|+2 ≥ 3`, and in Lemma 2.19 with a suitable endpoint. We did not decide whether
      the `|ℓ| = 1` case is false.
    - The paper's edge form is `lemma_2_13_edge`, proved for `2 ≤ |ℓ|`. It is derived from a node form
      (`lemma_2_13`: `u` changes level or becomes protected), which is what the later proofs use.
12. **Lemma 2.14.**
    - Formalized with the paper's exact bound `(k−|ℓ|)(k−|ℓ|−1)`, via
      `cost14 = ∑ (2(k−j)+2)` (`lemma_2_14`, `lemma_2_14_aux`).
    - The paper's inner induction is on the current level of `u`. Formally this needs strong induction
      on the remaining distance. The reason is that `u` may start anywhere in `Ψ^≫(ℓ)`, and the cost of
      each step depends on the current level.
13. **Corollary 2.15.**
    - Explicit `T₀ = R(∑_{j=1}^{k-1}(k−j)(k−j−1))`.
    - The positive and negative halves run in parallel, both starting at time 0.
14. **Corollary 2.17.** Explicit `T₁ = ϱ^{2k−3}(T₀)`. The paper says `ϱ^{O(k)}(T₀)`.
15. **Lemma 2.19 (constant).**
    - The paper claims `t' ≤ ϱ^{k(k−1)}(t)` with `z = ∑_{j=2}^k (2(k−j)+2)`. Its argument charges one
      Lemma 2.13 application per level `j`.
    - The argument does not cover three things:
      - both endpoints of an edge move, so up to two progress steps per level are needed;
      - `v` may have several non-protected edges, which resolve one after the other;
      - edges `{k, −k}` may become non-protected meanwhile.
    - We prove the bound `2(k−1)(2k−2) = 4(k−1)²` in two phases (`lemma_2_19_phaseA`, `phaseB`):
      - phase A: `v` moves inwards until it is protected or at `±1`;
      - phase B: while `v` is stuck at `±1`, every neighbour reaches `∓1` or becomes protected.
    - It is still `O(k²)`, and the paper's final `O(D³)` is unaffected. We did not decide whether
      `k(k−1)` itself is true.
    - Lemma 2.19 (and Lemma 2.22's main argument) only need the graph to be out-protected (`t ≥ T₀`),
      not justified.
16. **Lemma 2.20.**
    - The claim is formalized with general `ℓ`, `d` (`lemma_2_20_claim`) under `1 ≤ ℓ`, `ℓ + 3d < k`.
    - The claim itself does not need `t ≥ T₁`.
    - The paper's conclusion "G is protected at time `t'`" for an arbitrary later `t'` needs
      persistence of protection. That holds only after `T₁` (Lemmas 2.18 and 2.10).
    - Our `lemma_2_20` concludes that `G` is protected at the time `v` *first* reaches level `2D+2`.
      It also derives the times `t, t'` with properties (I)–(III) from "`|λ_v| = 1` at `t`,
      `|λ_v| ≥ 2D+2` later". The paper only says "plugging `d = D`". We need: from `−1` a node can
      only move to `1`, and between `1` and `k−1` levels change by `±1`.
    - Existence of `t_w, t'_w`: the paper says "there must exist". Formally, `t'_w` is the first time
      `w` reaches `ℓ+2d` (`exists_first`), and `t_w` is the last time before it at level `≤ ℓ+1`
      (`Nat.findGreatest`).
17. **Lemma 2.21.**
    - Formalized with an explicit hypothesis that protected graphs stay protected. This is supplied
      from `T₁` on.
    - "Grounded" (`Grounded`) is as in the paper: `v` lies anywhere on a walk of length `≤ D` with all
      nodes protected and an endpoint at `±1`.
18. **Lemma 2.22.**
    - The paper's potential argument picks `x_t` and `P^t` anew at every time, with tie-breaking by
      `|λ|`. It then applies Lemma 2.19 to `x_{τ(i)}`. But when that node becomes protected, `x_t` may
      already be a *different* node at the same distance, so "`d` decreases or `v` becomes grounded"
      does not follow literally.
    - Repair (`lemma_2_22_aux`): fix the walk `P` (from `v` to the first non-protected node `x`) at
      the start of a phase. Up to the first time some node of `P` changes protection status:
      - an interior node becoming non-protected gives a shorter walk (recursion on its length);
      - `x` becoming protected makes `P` grounded, since newly protected nodes are at `±1`
        (`natAbs_eq_one_of_newly_prot`).
    - Bound: `ϱ^{(D+1)·2(k−1)(2k−2)}(T₁)`. No tie-breaking or `G_p`-distances are needed.

## Corollary 1.2 and Theorems 1.3/1.4

19. **Corollary 1.2 (synchronizer).**
    - Proved only for deterministic Π and *static* tasks: the output is eventually fixed and legal,
      and Π synchronously self-stabilizes on the given `G` within `f` rounds.
    - Bound: `R(N(D) + D + f)`. The extra `D` rounds absorb the initial skew of the unwrapped clocks.
    - Section 4 specifies `δ*` only for AA steps. On other steps we keep the first two coordinates.
    - **Error.** For arbitrary tasks, as the paper states it, the corollary is false. Π* only
      guarantees that every node shows the synchronous execution at its *own* simulated round; rounds
      differ by at most 1 across edges (`synchronizer_simulation`).
    - Counterexample in Lean (`Counterexample.lean`), already for `D = 1` (complete graphs). Task:
      "outputs equal at all times and changing infinitely often".
      - It is solvable synchronously on every complete graph by `δ(b,S) = ¬(true ∈ S)`
        (`toggle_sync`). That algorithm cycles on `P₃`, so the counterexample uses the class `D = 1`.
      - It is solvable by no deterministic SA algorithm on `K₂` under the fair round-robin schedule
        (`no_async_alg_roundRobin`).
    - Randomization, expectation and w.h.p. bounds are not formalized. Neither is the
      `|Q*| = |Q|²(4k−2)` count.
20. **Theorems 1.3/1.4** (randomized synchronous LE / MIS, Section 3) are **not formalized**: they
    are out of scope, being randomized with w.h.p. analysis.
