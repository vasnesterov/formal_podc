# Differences between the formalization and the paper

Paper: Biely, Robinson, Schmid, Schwarz, Winkler, *Gracefully Degrading Consensus and k-Set Agreement in
Directed Dynamic Networks*, arXiv 1501.02716v1 (full version of the PODC'14 brief announcement by Schwarz,
Winkler, Schmid, Biely, Robinson; Sections 6–7 are the PODC part, Sections 4–5 the SIROCCO'12 part).

## Model

- Full-information deterministic algorithms (`Alg`): every process broadcasts its state; the paper's
  sending/transition functions are a special case, so the impossibility results cover all algorithms of the
  paper. Algorithms may know `n`, `D`, `H`, `k`. Decisions are irrevocable (`dec_stable`), as in the paper.
- Round indices start at 0 (`ρ t` is the paper's `G^{t+1}`). Intervals keep their length.
- The causal-distance bound `cd_x(p, q) ≤ k` is the CSLib journey `Journey ρ x p (x + k) q`; we never use
  `cd` as a number.
- `k`-agreement is stated as "every finite set of decided values has at most `k` elements" (no `ncard` of a
  possibly infinite set).
- Definition 15 (iii) is ambiguous ("`1 ≤ ℓ ≤ k` H-network-bounded VSRCs exist simultaneously"): `VSRCk` is the
  literal reading (some `ℓ` stable root components), `VSRCkAll`/`VSRCkInf` the strong reading (all root
  components of the window are among them). Impossibilities are proved for the strong reading, which implies
  the literal one (`VSRCkAll_subset`, `theorem7_weak`).
- Definition 16 (influence "before or at the beginning of `I_j`"): a journey from time `b_i + 1` to time
  `a_j`. Definition 17's formula `cd_{s_cur+1}(p, q) ≤ r_suc − s_cur` would also allow the first round of
  `I_j`; for singleton (deaf) roots the two coincide.
- Def. 9/10 for infinite windows (`d = ∞`): `HNetBoundedFrom`.

## Section 4 (consensus)

- **Definition 13 is unsatisfiable** as written (`not_almostBounded`): "a unique `q` with `cd ≤ H` from all
  `p ∈ R`" contradicts "all other `q'` have `cd ≤ H − 1`" (they also have `cd ≤ H`). Hence `VSRC'(H − 1) = ∅`
  (`vsrcPrime_eq_empty`), the first claim of Theorem 4 is false (`theorem4_prime_false`), and Lemma 8's
  inclusion `VSRC(H) ⊆ VSRC'(H − 1)` is false (`lemma8_false`). Definition 13 also uses "for all `p ∈ R`" where
  Definition 10 uses "for some `p`", so Lemma 8 fails under the intended reading as well.
- **Lemma 9, cases (ii)/(iii)**, make the "distant" process `q` the single root right after `J`, so `q` never
  hears from `R`: this contradicts Definition 13 under its intended reading (`q` must be reached within `H`
  rounds from every `p ∈ R`). The intended `VSRC'(H − 1)` impossibility is not established. Under the
  weakest reading of Definition 13 (no condition on `q`), Lemma 9 (ii) works, but the induction has the gaps
  of the next item and our re-proof does not cover `VSRC'(H − 1)`; unproved either way (❌ for the first claim
  of Theorem 4, the literal unsatisfiability alone would be a slip).
- **Theorem 4's induction** never checks that the forever-bivalent run is feasible: Lemma 10's intermediate
  graphs are arbitrary single-root graphs, so item (ii) of Definition 12 (every VSRC `H`-network-bounded) can
  fail on the constructed run, and the window `J` is fixed "anywhere" so a VSRC of the prefix may extend into
  `J` and force `q` to be reached. We re-prove Theorem 4 for `VSRC(H − 1)` with a product sub-adversary
  (`famT4`): `J` = the first `H − 1` rounds with root `{a}`, afterwards only "fast" graphs with roots of at most
  two processes (`prodAdv_famT4_subset`), chain connectivity by single-process changes through stars
  (`chain_rootedAt`, `chain_famF`), and the Lemma 9 strategy `iso_famT4` (line `a → c₁ → ⋯ → q` during `J`,
  then `q` the eternal root). The generic bivalence argument is `not_solvesConsensus_of_chain_isolation`.
- **Implicit hypotheses of Theorem 4**: `2 ≤ H` (for `H = 1` the window `d = 0` is meaningless) and
  `H ≤ n − 1` (needed for the distant process; the paper's `H` is a causal diameter, `≤ n − 1` by Lemma 4).
  For large `H` (`H − 1 ≥ 4(n − 1) + 2`) the claim would contradict the paper's own Theorem 5 with `H' = n − 1`.
- Lemma 10 is used in the form "consecutive graphs differ in the in-neighbourhood of one process"
  (`OneChange`), which is what the valency argument needs; our chains stay inside the families above.
- Not formalized: Theorems 1–3, Lemmas 1–7 (except what is used), Section 5 (Algorithms 1–2, Theorem 5).

## Section 6 (k-set agreement impossibilities)

- **Theorem 7**: the parenthetical "(and only root component `R_k` is vertex-stable for at most
  `min{n − k, H} − 1` rounds)" is not part of our statement: in our runs (as in the paper's proof via
  Theorem 4) the remaining group may end with an eternal single root `{q}`.
- **Theorem 7**: proved (`theorem7`) for all `D ≥ 1`, `H ≥ 2`, `1 ≤ k`, `k + 2 ≤ n`, `|V| > k`, even with
  `k − 1` singleton roots stable forever. The paper's `k = 1` case reduces to Theorem 4 "with item (ii)
  dropped", i.e. for a larger adversary than claimed; our runs satisfy item (ii) of Definition 15 for every
  `D ≥ 1` (all roots are cliques of at most two processes, `dBounded_of_clique`).
- The generic Theorem 6 (Theorem 1 of [7]) is not used as a black box: its literal statement is false and
  needs repairs (see `Papers/PODC2011/KSetAgreement`). We prove the reduction directly
  (`restrict_solvesConsensus`): the processes of `D` are isolated forever and decide their own pairwise
  distinct inputs chosen to avoid two disagreeing values of `D̄`; validity of `A|D̄` follows by setting the
  inputs of `D` to an input of `D̄` (the missing condition (E) of the repaired Theorem 1).
- `|V| > k` is the paper's standing assumption; we use it as an injection `Fin (k + 1) → V`.
- **Lemma 17** as stated (`∃ r' > 0`) is trivial (`r' = 1`: no communication at all; `lemma17`). The proofs of
  Theorems 8 and 9 need it for every fixed `r'` (`lemma17_fixed`), which we prove by the finite-horizon chain
  argument `exists_lossy_disagree` instead of citing [52, Lemma 3] and [50].
- **Theorem 9**: the pair `Dᵢ` must disagree after a lossy period whose length is fixed by the earlier phases;
  "A|Dᵢ cannot have solved consensus" only gives some bad pattern. Fixed with `exists_lossy_disagree`, choosing
  each pair's pattern after its length is known. Our schedule is simpler than the paper's: groups
  `{2g − par k, 2g + 1 − par k}` (group 0 a singleton when `k` is even); group `g` has a lossy link in rounds
  `[0, T g)`, is deaf in `[T g, T (g+1))` and afterwards hears everybody; processes outside the groups always
  hear everybody; from the end of the last phase the graph is complete (single root, constant). Every root of
  every round is a clique (`D`-bounded for all `D ≥ 1`), at most `⌈k/2⌉ + 1` roots per round. Inputs: `x_i = i`
  for the `k + 1` deciding processes (needs `|V| > k`, `Fin (k + 1) ↪ V`), the hypothesis `1 < k` is not used.
- **Theorem 8** is derived from Theorem 9 (`VSRC(⌈k/2⌉+1, ∞) ⊆ VSRC(k, ∞)` for `k ≥ 2`), not by the paper's
  separate argument (which is the same construction with one pair).
- Typo in the proof of Theorem 8: "`(i < 0 < k)`" for `0 < i < k`.

## Section 7.1 (Theorem 10)

- Algorithm 3 in full-information form; the state carries the round counter. When several heard processes have
  decided, line 7 adopts the decision of one of them chosen by a choice function (the paper: "some `p_j`").
  After round `n` processes keep running with frozen decisions ("terminate"). `[Inhabited V]` only fills an
  unreachable branch.
- The paper's inductive proof leaves implicit why `p_i` decides `x_i` (we derive it from injectivity of the
  decision map and "decision ≥ own input") and why a line-11 decision in round `n` happens in a deaf round.
- Non-vacuity of `Σ_{n−1}-MAJ` (`complete_mem_sigmaMaj`) is weak: the complete graph has no singleton roots.

## Section 7.2–7.4 (Algorithm 4, Theorem 11)

- **Theorem 11 is false** (❌): `theorem11_false` (`n = 5`, `D = H = 1`, `k = 1`; tie of two locks with the same
  creation round, fallback of line 32 picks a fresh value) and `theorem11_false'` (`n = 8`, `D = 2`, `H = 1`,
  `k = 1`; a virtual lock is the unique most frequent lock, no tie); the same run with `H = D = 2` is
  `theorem11_false'_H2` (the paper assumes `H ≥ D`, p. 23). Lemma 26 fails: Definition 19 does not
  constrain locks spread during a VSRC's own interval nor virtual locks. Found by simulation only (scripts in the
  agent work folder, not in Lean): a re-lock run (`D = 2`, `n = 6`) where a member of `R_cur` releases (Corollary 2
  does not cover a VSRC of exactly `2D + 1` rounds) and re-locks with a newer lock of another value; and an
  off-by-one in Lemma 22 (decisions in round `a + 3D` may miss the `3D + H` window; periodic run).
- **Definition 19** literally includes `R = R_cur` and is then unsatisfiable (`majInfLit_false`); `MAJINF(k)`
  then only bounds `|V_{2D+1}|` (`mem_MAJINFLit_iff`). We use `MajInf`: `R ≠ R_cur` and `R_cur` ends before
  `R_suc` starts (otherwise a later VSRC can majority-influence an earlier one, contradicting Lemma 18).
- Definition 17 uses the paper's formula `cd_{s_cur+1}(p, q) ≤ r_suc − s_cur` (chains may use the first round of
  `I_suc`); `IS(R₁, R₂) = ∅` unless `R₁` ends before `R₂` starts. `V_d`: maximal VSRCs, `[a, ∞)` allowed.
- Algorithm 1 interpretation (Alg4.lean I1–I3): the vertex set of `A_p|t` contains `p`; `C_p|t` is the strongly
  connected component of `p` in `A_p|t` if no known edge enters it (read literally, "`A_p|t` if strongly
  connected" breaks Lemma 13 and Corollary 2 as soon as outside processes report edges leaving the root;
  observed in simulation); `InStableRoot` is `∅` on intervals containing a round `< 1`.
- Algorithm 4 interpretation (I4–I9): line 15 adds every newly learned lock to `hist_i[i][r]` (stored as earliest
  rounds, exact for line 26); the multiplicity in `S` is the number of members of `R` knowing the lock by round
  `r − 2D`; `mfrq_latest` exactly as line 27; fallback = max value over all of `S`; `τ_create` = current round;
  smallest decision adopted if several arrive; `V_p` omitted (unused).
- The counterexample runs satisfy the strong reading of Definition 15 (iii) (`VSRCkAll`), hence the literal one.
- Not formalized: Theorem 11's positive parts (Lemmas 19–25), Definition 20, Section 3.3.
