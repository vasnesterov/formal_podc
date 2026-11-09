# Differences between the formalization and the paper

Paper: Casteigts, Flocchini, Godard, Santoro, Yamashita, *Brief Announcement: Waiting in Dynamic Networks*, PODC 2012;
full version *Expressivity of Time-Varying Graphs and the Power of Waiting in Dynamic Networks*, arXiv:1205.1975v1
(numbering below follows the arXiv version).

## Model and definitions

- **Time domain** `ℕ` only (the paper allows `ℕ` or `ℝ⁺`). The regularity proof (Theorem 4.1) does not use
  discreteness; Theorems 3.1 and 5.1 are constructions in `ℕ`.
- **Edges** are triples `(u, a, v)` (the paper writes `(u, v, a)`). The footprint `E` is implicit: we take all of
  `V × Σ × V`, an edge outside the paper's `E` being never present. Equivalent since `V` and `Σ` are finite. The
  lifetime `𝒯` is absorbed into `ρ`.
- **Presence and latency.** The paper requires `ρ`, `ζ` to be "arbitrary computable functions". The main theorems
  (`theorem_3_1`, `theorem_4_1`, `theorem_5_1`) are for arbitrary `ρ`, `ζ`. The computable versions (nodes `Fin n`,
  alphabet `Fin q`, `TVG.IsComputable`: presence a computable predicate, latency a computable function) are in
  `Computable.lean`: `theorem_3_1_computable`, `theorem_4_1_computable`, `theorem_5_1_computable`, and the converse
  `LnowaitComp_eq_computable` (not claimed as a theorem in the paper, only as "as powerful as a Turing machine").
  The decoder `φ⁻¹` is shown computable via a primitive-recursive base-`b` decoder (`phiInv_eq_phiDec`), for bases
  of the form `c + 2`.
- **Journeys** are an inductive relation `Journey P u t w v t'` with a pause rule `P` instead of explicit sequences of
  transitions `(sᵢ, tᵢ →aᵢ sᵢ₊₁, tᵢ₊₁)`. Same content.
- **Start date.** The paper's acceptance condition does not say when journeys start; Section 3 implicitly uses date
  `0` (`φ(ε) = 0`), the example `G₁` date `1`. We put a start date into the automaton; the families quantify over it.
  It matters: if any start date were allowed, `L_nowait(G₂) ≠ L` (`G2_other_start_date`). ✏️ (implied assumption).
- **Waiting at the start node.** In the paper `start(J)` is the departure date of the first transition, and
  `J*x = J*_{0,x}`. In our model a journey is *at* the initial node at the start date and the first departure obeys
  the pause rule, so with waiting it may leave later. For `L_wait` and `L_nowait` this changes nothing (no waiting:
  same; waiting: the regularity proof covers any start configuration, and the strict variant is a finite union of
  `a · L_wait(from (v, ζ(e,0)))`, also regular — not formalized). For bounded waiting the first pause is also `≤ d`.
  Under the literal definition, Lemma 4.2 is false: with one node, `b` present only at `0` with latency `1` and `a`
  present only at `1`, every journey of `ba` from date `0` contains the walk `a` (so `a ≺ ba`), but no journey of `a`
  starts at date `0`. Not formalized (✏️, see README).
- **Bounded waiting** `waitAtMost d`: each pause (including before the first edge) lasts at most `d`.
- **Families** `𝓛_nowait`, `𝓛_wait`, `𝓛_wait[d]`: sets of languages over a fixed alphabet `α : Type` accepted by
  TVG-automata with a finite node type `V : Type`.

## Section 2 (example `G₁`)

- Formalized as stated (`ExampleG1.lean`), start date `1`, distinct primes `p`, `q`. The latencies of `e₃`, `e₄`
  ("any") are parameters. The presence condition of `e₂`, "`t ≠ pⁱqⁱ⁻¹, i > 1`", is read as "for all `i > 1`".
  Correct; determinism also proved (`G1_deterministic`).

## Section 3 (Theorem 3.1)

- **Base of the encoding.** The paper uses base `q = |Σ|`. For `q = 1` the encoding `φ(w) = 1.w` is not injective
  (every non-empty word gets `1`), so `φ⁻¹` and `G₂` are undefined (✏️ slip, degenerate alphabet). We encode in any
  base `b ≥ max 2 q`; `theorem_3_1` is the paper's statement for `b = q ≥ 2`, and `Lnowait_eq_univ` covers every `q`
  with `b = q + 2`.
- `φ(ε) = 0 "by convention"` while the formula gives `q⁰ = 1`: harmless (typo-level); we follow the convention.
- `φ⁻¹` is a classical inverse on the image of `φ` (junk value `ε` elsewhere, irrelevant since edges are absent there).
- **Strength.** Theorem 3.1 is stated for computable `L`, but the construction needs nothing about `L`: with arbitrary
  `ρ` every language is in `𝓛_nowait` (`Lnowait_eq_univ`). With the paper's computability requirement on `ρ`, `ζ`,
  decidable `L` gives a computable `G₂` (see `Computable.lean`).

## Section 4 (Theorem 4.1)

- **Easy inclusion** (regular ⊆ `𝓛_wait`): as in the paper, a DFA is a static TVG (`ofDFA`). The paper says
  determinism is needed; our `ofDFA_lang` works for any pause rule allowing immediate departure. (Remark, not a
  mistake.)
- **Hard inclusion: different proof.** The paper's route (the quasi-order `≺` on words, Proposition 4.4, Theorem 4.12
  via Lemma 4.13 and Lemma 4.10, then Harju–Ilie, Theorem 4.7) is not formalized. We prove `L_wait(G)` regular via
  walks: schedulable edge sequences are subword-closed (`Sched.sublist`, the corrected Lemma 4.2), hence regular
  (Haines' theorem, from Higman's lemma); intersect with the regular set of walks from `I` to `F`, then project
  edges to labels. So Theorem 4.7, Corollary 4.6, Propositions 4.3, 4.4, 4.8, 4.9, Theorem 4.12, Lemma 4.13 are
  neither used nor checked in Lean; Lemma 4.10 is refuted (`lemma_4_10_false`).
- **Lemma 4.10** (wqo `Q` ⇒ `(𝒫(Q), ≤_P)` wqo) is false for arbitrary subsets (Rado's example, `lemma_4_10_false`). ❌.
- **Proof of Theorem 4.12 / Lemma 4.13** (examined, not formalized): Lemma 4.13 needs `x ∈ Down≺(X) \ X` whenever
  `ax ∈ X`, i.e. `x ≺ ax`, which fails in general because `≺` requires equal endpoints (one edge `u →a v`: `ε ⊀ a`).
  The proof of Theorem 4.12 identifies `x ≺ y` with `x ⊆ y` ("ie x ⊆ y", contradicting Remark 4.14), asserts without
  argument that the `y`'s can be chosen distinct, and applies Lemma 4.10 to infinite sets. Part of the 🛠️ item for
  Theorem 4.1 in the README.
- **Proposition 4.8** (monotonicity), left part: `≺` quantifies over journeys starting at date `0`, but the
  `y`-part of a journey of `zy` starts later. Works under our reading (waiting at the start node), fails under the
  literal one together with Lemma 4.2. Covered by the ✏️ start-date item.
- Corollary 4.6 is printed as "`Down≺(L)L`" (missing relation symbol). Typo.
- Section 2, journeys in `G`: presence is required only "for `1 ≤ i < k`" (the last edge would be unconstrained);
  should be `1 ≤ i ≤ k`. Typo; the TVG-automaton journey definition and our `Journey` require every edge present.

## Section 5 (Theorem 5.1)

- **Typos in `G_{2,d}`**: presence tests "`⌊t/(d+1)⌋ ∈ φ_d(Σ*)`" should be `∈ φ(Σ*)`, and the latency of the edges
  into `v₂` uses "`ψ_d⁻¹(t)`" for `ψ_d(t)`. "time-expanded by a factor `d`" should be `d + 1`. Fixed in `G2d`.
- **Proof gap**: the proof shows only that every (computable) `L` is `L_wait[d](G_{2,d})` (`G2d_LwaitAtMost`), i.e.
  computable languages ⊆ `𝓛_wait[d]`. The equality of families needs `𝓛_wait[d] ⊆ 𝓛_nowait` (never argued) and
  `𝓛_nowait ⊆ 𝓛_wait[d]` (would need `𝓛_nowait` ⊆ computable languages, not proved in the paper). We prove both by
  direct simulations, for arbitrary TVGs: `dilate` (time dilation, `dilate_LwaitAtMost`) and `withPause` (nodes
  `V × Fin (d+1)` encode the next pause, `withPause_Lnowait`). Both preserve computability (`Computable.lean`).
- The final remark "`|φ_d(w) − φ_d(w')| > d`, minimal when the last letters are `i, i+1`" is imprecise (words of
  different lengths), but the claim follows from injectivity of `φ`; our proof does not use it.
- The paper writes both "`d > 0`" and "for any fixed `d ≥ 0`"; we allow all `d ≥ 0` (`d = 0` is `L_nowait`,
  `LwaitAtMost_zero`).

## Not formalized

- Theorem 4.7 (Harju–Ilie), cited; not needed.
- Whether `(Σ*, ≺)` is a well quasi-order (Proposition 4.4). Probably true via better-quasi-order theory (the
  Smyth-type order over walks, which form a bqo), but neither proved nor refuted here.
- Remark about timed automata (Section 2).
