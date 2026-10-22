# Differences between the formalization and the paper

Paper: Dubois, Guerraoui, *Introducing speculation in self-stabilization: an application to mutual
exclusion*, PODC 2013 (arXiv 1302.2217v1).

## Model and definitions

1. **Protocols.** The paper defines a protocol as an arbitrary set of global actions `(γ, γ')` and
   then uses guarded rules. We use guarded rules: one deterministic local rule `next γ v`, computed from
   `γ v` and the registers of the neighbours of `v`. The guards NA, CA, RA are pairwise exclusive. For an
   isolated process, NA and CA can both be enabled, but they have the same action. Lemma 5 is false for
   general global protocols (the next state may depend on far-away processes), so this restriction is
   needed and matches the paper's intent.
2. **Daemons (Definitions 1–2).** These are classes of executions `ω t = (configuration, activated set)`.
   *Unfair distributed daemon* (`unfairExecs`): CSLib's `IsUnfairRun`. Only enabled processes are
   activated, and some process is activated unless the configuration is terminal. Terminal
   configurations repeat forever, standing in for the paper's finite maximal executions; SSME has no
   terminal configuration (`ResetUnison.not_terminal`). *Synchronous daemon* (`syncExecs`): all enabled
   processes are activated. The partial order on daemons is only used as `syncExecs ⊆ unfairExecs`
   (`syncExecs_subset`). The central daemon is not formalized.
3. **Configurations.** Registers are integers. A configuration is valid (`SValid`) if every register
   lies in `cherry(n, K) = {-n, …, K-1}`. "Arbitrary initial configuration" means an arbitrary valid
   configuration.
4. **Clock arithmetic.** `φ`, `≤_l` and `correct` are written without `mod`, through `succK c = c + 1`,
   wrapping `K - 1 ↦ 0`. Equivalence with the paper's `mod`-based definitions on `stab` is proved
   (`succK_eq_emod`, `locLe_iff`, `correct_iff` with the paper's `d_K`).
5. **Guards.** `resetInit` is `¬allCorrect ∧ r_v > 0`; for clock values `r_v ∉ init_X ⟺ r_v > 0`.
   `convergeStep` keeps the paper's conditions `r_u ∈ init_X = {-n, …, 0}` and `r_v ≤ r_u`.
6. **Graph and identities.** Connected simple graph with `n ≥ 2` processes; `n = 1` is trivial and not
   treated. Identities: any injective `id : V → {0, …, n-1}` (necessarily a bijection), as the paper
   assumes.
7. **Specification 1.** `MutualExclusion priv ω`: at most one privileged process in each configuration,
   and every process is privileged *and* activated infinitely often. A privileged process "executes its
   critical section" when activated, as in the paper. The predicate `priv v γ` may depend on the whole
   configuration, so that the paper's "privileged over the variables of `v` and its neighbours" can be
   expressed.
8. **Self-stabilization (Definition 3)** is CSLib's `IsLegitimate` / `SelfStabilizing`. Some set `L` of
   configurations is reached by every execution, and every execution starting in `L` satisfies the
   specification. For SSME, `L = Γ₁`. **Convergence time:** `conv_time(π, d) ≤ T` is
   `PseudoStabilizingWithin Exec spec T`, i.e. the suffix from time `T` of every execution satisfies the
   specification. This matches "the number of actions required to reach a configuration from which any
   execution satisfies spec" for the deterministic synchronous daemon.
9. **Definition 4 (speculative stabilization)** and the Section 3 examples (Dijkstra's ring, min+1 BFS,
   maximal matching) are not formalized. The ratio condition `conv_time(π,d)/conv_time(π,d') ∈ Ω(f)` is
   asymptotic over graph families, and the claim that SSME is "sd-speculatively stabilizing" needs
   convergence-time bounds under the unfair daemon that the paper only quotes from [7].

## Theorem 1

10. The paper deduces convergence to `Γ₁` from the main result of Boulinier–Petit–Villain [2], with
    `α ≥ hole(g) - 2` and `K > cyclo(g)`. We prove convergence for `α ≥ n` and `K > n`, which covers
    `α = n` and `K = (2n-1)(D+1)+2`, without `hole`/`cyclo` (`ResetUnison.exists_legit`).
    The proof uses chains of resets: each reset is caused by an earlier reset of a neighbour, or the
    process was positive and not `allCorrect` from the start. With `α ≥ n`, a chain has fewer than `n`
    links, because a process cannot leave `init*` while its successor in the chain is still positive.
    So there are finitely many resets and finitely many CA steps. After that, a process next to a frozen
    process moves at most twice, so a run that never reached `Γ₁` would end in a terminal configuration,
    which does not exist.
11. Liveness of unison in `Γ₁` is also proved (`live_of_legit`, `visits_of_legit`); the paper takes it
    from [2]. It needs `K > n` (no deadlock in `Γ₁`, `exists_normalStep_of_legit`) and connectivity.
12. Safety in `Γ₁` follows the paper's argument: registers differ by at most the distance, modulo `K`,
    and different privileged values are more than `D` apart (`legit_safe`).

## Theorem 2 and Lemmas 1–4

13. **Lemma 1** is proved for `i ≤ D`; the paper states `i < D`. We use `i = D`. Our version also gives
    the register bounds `c - (i - j) ≤ r_u^j ≤ c` and `allCorrect` at all `j < i` (`lemma_1`). The
    paper's form is `lemma_1'`.
14. **Definition 5 (islands) is ill-defined.**
    * It requires neither connectivity nor `r ∈ stab`: an independent set of `init` processes is an
      island.
    * It excludes `I = V`, so a configuration with all registers in `stab` and only an incorrect chord
      has a process in no island. The proof of Theorem 2 nevertheless assumes `u` lies in an island.
    * `depth(I)` is a maximum over the island, but Case 1 uses it as the depth of `u`.

    **Lemmas 2 and 3** are not formalized as stated. The proof of Lemma 2 uses "same island and
    `dist ≤ D` ⇒ `d_K ≤ D`", which is false: the shortest path may leave the island (only `d_K ≤ n-1`
    follows). They are replaced by the light cone lemma `cone`, which needs no islands, and by
    `no_two_priv_early` for Case 1 (`⌈D/2⌉ ≤ i ≤ D`).
15. **Case 1 arithmetic.** The paper splits on `id_v - id_u ≥ 2` and `= 1`. We use one integer argument.
    The registers at time 0 differ by at most `dist(u,v) ≤ D` without wrap-around, and privileged values
    differ by `2D·(id_v - id_u)`. The equality case `i = D` (in the paper it falls into Case 2, whose
    Lemma 4 is false at `i = D`) needs the observation that a process moving at step 0 is a local
    minimum.
16. **Lemma 4 is false** (`lemma_4_false`, `C₅`, registers `(10,10,10,12,11)`, register `12` at time
    `D = 2`). The proof's claim "there exists `∅ ≠ V' ⊆ V` enabled by RA in `γ₀`" also fails when all
    registers are negative. **Corrected** (`lemma_4_corrected`): from time `D+1` on, every register is
    `≤ t` or `≥ K-D-1`. Case 2 then covers `D < i < 2n`: only the process with identity `n-1`
    (privileged value `K-D-1`) can be privileged.
17. **Case 3** uses [3] (synchronous unison stabilizes within `α + lcp(g) + D` steps). We prove instead
    that a synchronous execution is in `Γ₁` from time `n + α = 2n` on (`legit_sync`): no reset after
    time `n` (synchronous reset chains have consecutive times and fewer than `n` links), then `α` steps
    of CA. The paper needs `Γ₁` only from time `2n + D` on.
18. Liveness in Theorem 2 comes from `legit_sync` and the unison liveness; the paper only argues safety.

## Theorem 3

19. Not formalized. It is a direct citation of Devismes–Petit [7]
    (`2·diam·n³ + (α+1)n² + (α-2·diam)n` steps).

## Section 5 (lower bound)

20. **Lemma 5** is stated for protocols given by local rules (see 1). It is generalized to radius
    `r + k → r`, and the hypothesis "π is self-stabilizing" is dropped (it is not used). The paper's
    bound `1 ≤ k ≤ diam` is not needed.
21. **Theorem 4 is false as stated** when `privileged_v` reads the neighbours of `v`, as Specification 1
    allows: `theorem_4_false` (complete graphs `K_n`, `n ≥ 2`, `D = 1`; a token-passing protocol with
    convergence time 0, under the synchronous and the unfair daemon, `rr_unfair`) and
    `theorem_4_false_star` (stars, `n ≥ 3`, `D = 2`, synchronous daemon). In general
    (`theorem_4_false_centre`), if some vertex `z` has eccentricity `≤ R`, a clock at `z` broadcast
    along a BFS tree (`c_v := c_parent(v) + 1`, `privileged_v ≡ c_parent(v) = id_v`) gives mutual
    exclusion from time `R - 1` on in all synchronous executions; for graphs of radius `⌈D/2⌉`
    (trees, complete graphs, stars, …) this is `⌈D/2⌉ - 1` (`theorem_4_false_of_radius`). Proved instead:
    `theorem_4_radius`, i.e. `⌈D/2⌉ ≤ T + r` when `privileged_v` reads the `r`-ball. `theorem_4` is the
    case `r = 0`, which is the paper's statement for state-local `privileged`. The domain of
    configurations must be a product closed under the protocol, so that two configurations can be
    spliced.
22. In the lower bound we only use the liveness consequence "each process is privileged at some time
    `≥ T`" and safety at time `T`, as the paper does. The hypothesis is the synchronous convergence time
    only, matching the abstract's "even if asynchronous stabilization is not required".
23. **Optimality of SSME** (`conv_time_ssme`): `conv_time(SSME, sd) = ⌈D/2⌉` exactly.
