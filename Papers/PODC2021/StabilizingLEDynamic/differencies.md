# Differences between the formalization and the paper

Paper: Altisen, Devismes, Durand, Johnen, Petit, *On Implementing Stabilizing Leader Election with
Weak Assumptions on Network Dynamics*, PODC 2021. We follow the full journal version (HAL
hal-03346225, Research Square preprint 2023, Theorems 1–7); the PODC numbering is given in the
docstrings (Theorem 2.1, Lemma 3.2, Theorems 3.3–3.11, Theorem 4.1).

## Errors and gaps in the paper

1. **Theorem 1: proof slip for `n = 2`** (statement true). In the paper a class is a set of
   dynamic graphs over all vertex sets, and Theorem 1 holds in that form (`theorem_1_classes`,
   which follows from the per-vertex-set version for `n ≥ 3`, `theorem_1`). But the proof works
   inside "a set `V` of `n > 1` vertices", and for `n = 2` the per-`V` statement fails:
   * recurrent and quasi-timely coincide: if `p ⇝ q` in every suffix and `p ≠ q`, the edge `p → q`
     appears infinitely often, so `d̂ = 1` infinitely often. Hence, restricted to two vertices,
     `J_{1,*} = J^Q_{1,*}(Δ)`, `J_{*,1} = J^Q_{*,1}(Δ)`, `J_{*,*} = J^Q_{*,*}(Δ)`
     (`theorem_1_false_card_two`);
   * a source is the same as a sink (the other vertex is a sink), so `J^τ_{1,*} = J^τ_{*,1}`
     (`J_src_eq_snk_of_card_two`). In particular the witness `G(1S)` (out-star) has a sink when
     `n = 2`, contrary to "by transitivity, `G(1S) ∉ J_{*,1}`".
   So the proof needs `n ≥ 3` (`not_theorem_1_card_two`; for `n = 1` all nine classes coincide,
   `J_card_one`). The PODC version gives no proof.
2. **The identifier domain must have more than `n` elements** (under-specified definition). All
   impossibility proofs replace a process by a fresh one (`v ∉ V`), i.e. use fake identifiers.
   The paper only says "`IDSET` is an arbitrary totally ordered domain". If `|IDSET| = n` there are
   no fake identifiers and the constant algorithm `lid := min IDSET` is self-stabilizing in every
   class, so Theorems 2–5 and Corollaries 1–3 all fail (`constAlg_selfStab`, `IDSET = Fin 2`,
   `n = 2`). We assume an infinite identifier domain (`[Infinite ι]`).
3. **Lemma 7 is false as stated** (false statement, harmless). It needs the received record to
   have `id ≠ id(p)`: line 12 skips records with `id = id(p)`, so a relayed copy of `p`'s own record
   inserts nothing into `Gstable(p)`. Counterexample (0-indexed rounds, `Δ = 2`,
   `V = {p, a, k}`, empty initial maps and `msgs`): `k → p` in round 1, `p → a` in round 3,
   `a → p` in round 4, no other edges. The `Gstable(p)` entry of `k`, inserted in round 1,
   expires at configuration 4. In round 4, `p` receives `⟨a, {a, p}, 2⟩` and its own relayed
   record `⟨p, {p, k}, 1⟩`, which line 12 skips. Hence `k ∉ Gstable(p)` at configuration 5,
   although `p` received a record whose map contains `k` in round 4. (Not formalized as a Lean
   execution.) Every use of Lemma 7 in the paper has `id ≠ id(p)`; our `lemma_7` assumes it. This
   is the same root cause as item 4.
4. **Lemma 16, proof gap** (statement true). `X_m` is defined as the last round in which `q`
   receives *some* record whose map contains `id(p)`, and the proof says that in that round line 17
   sets `Gstable(q)[id(p)]`. But lines 13–18 are skipped for records with `id = id(q)` (line 12),
   e.g. `q`'s own records relayed back to it. The fix: take `X_m` among records with `id ≠ id(q)`;
   Lemma 5's proof already has this restriction. (`lemma_5` states the stronger form, used in
   `lemma_16`.)
5. **Lemma 12, sloppy quantifiers** (proof gap, statement true). In the third case
   `d = d̂_i(r, q)` depends on `i`, yet the proof concludes "`∀ i ≥ t_p + d + 1`". The fix is to
   use, for a target round `k`, the source round `i = k − Δ`. Our `lemma_12` also handles the case
   `q = r` uniformly with the paper's second case.
6. **Lemma 8, intermediate claim of the proof misstated** (imprecision, harmless; Lemma 8 itself,
   for `i > 4Δ`, is true). The proof's step "for all `i₁ > Δ`, `msgs(p)_{i₁}`
   contains no record `⟨f, −, −⟩`" fails for `i₁ = Δ + 1`: an initial well-formed record
   `⟨f, L, Δ⟩` is still in `msgs(p)` at `γ_{Δ+1}`, with timer `0` (`lemma_8a_imprecise`). Such
   records are never sent, so (b)–(d) hold. Similarly Lemma 2 only covers timers `≥ 1`, while
   Lemma 8(c) is stated for all records in `msgs`. We state (b)–(d) for received records
   (`fake_L`, `fake_lsps`, `fake_G`), with slightly better bounds (`2Δ`, `3Δ − 1`, `4Δ − 1`
   0-indexed, i.e. the paper's `i > 2Δ`, `i ≥ 3Δ`, `i ≥ 4Δ`).
7. **Lemma 10, index slip** (typo). The proof considers rounds `i > 2Δ + 1` but concludes
   `t_r ≤ 2Δ + 1`. The argument actually works for `i ≥ 2Δ + 1`, so the conclusion holds
   (`lemma_10`: constant from 0-indexed time `2Δ`, the paper's `γ_{2Δ+1}`).

## Strengthenings

* **Theorem 7**: we prove `SP_LE` from `γ_{6Δ+1}` on (`theorem_7_sharp`, pseudo-stabilization
  phase `≤ 6Δ`), and derive the paper's bound `6Δ + 2` (`theorem_7`). Requires `n ≥ 1` (for
  `n = 0`, `SP_LE` is unsatisfiable while `J^B_{*,*}(Δ)` is not empty; degenerate).
* **Theorem 6** states the paper's description of the elected leader in the form "from time `T`
  on, `ℓ`'s suspicion value is constant and `≤` every process's, with ties broken by identifiers".
* **Theorem 5**: proved for every algorithm, without assuming it pseudo-stabilizing (a bound on
  the phase length implies pseudo-stabilization).
* **Lemma 1**: stated for every class containing the graphs `PK(X, y)` and every initial
  configuration ("some process eventually does not elect `p`"), which covers the paper's
  hypothesis "all `lid = id(p)` initially".
* **Lemma 3**: stated with `d̂ ≤ d` instead of `d̂ = d`, and combining (a) and (b) (`Good`).
* All results are per system size `n`, which is stronger than the paper's "for all `V`".

## Modelling choices

* **Theorem 4 and the sink part of Figure 1 need `n ≥ 3`**, as the paper's overview and proof say
  ("a set `V` of at least three processes"). We state Theorem 4 and Corollary 3 for `n ≥ 3`, and
  Theorems 2, 3, 5 for `n ≥ 2` (for `n = 1`, `lid := id` is trivially self-stabilizing). For
  `n = 2`, `J^B_{*,1}(Δ) = J^B_{1,*}(Δ)`, so Algorithm `LE` is pseudo-stabilizing there
  (`theorem_4_card_two`). This is a clarification, not an error.

* **Processes are identifiers**: `id(p) = p ∈ ι` (`IDSET = ι`); a system is a finite set
  `V : Finset ι`, `|V| = n`.
* **Rounds are 0-indexed**: `G t` is the paper's `G_{t+1}` and `exec A G γ t` is `γ_{t+1}`. All
  constants are translated accordingly.
* **Dynamic graphs** are `ℕ → ι → ι → Prop` with all edges between distinct vertices of `V`
  (`IsDG`). Journeys are `Reach G p a b q` ("`p = q` or a journey with edges at strictly
  increasing times in `[a, b)`", for `a ≤ b`; the shared `Cslib.DynNet.Journey`). `d̂_{G_{i▷}}(p, q)` is `tdist G i p q : ℕ∞`, with
  `tdist_le_iff : tdist ≤ Δ ↔ Reach G p i (i + Δ) q`. The nine classes are `J k τ Δ V`
  (`k ∈ {src, snk, all}`, `τ ∈ {recur, quasi, bounded}`), literally Table 1.
* **Algorithms** are deterministic full-information round algorithms (CSLib `HeardOf.StepFn`).
  Each process broadcasts its whole state, and the receiver knows the sender of each message.
  This is at least as strong as the paper's "send all or part of the local state", so the
  impossibilities are stronger. Codes may differ per process (`step p`). An algorithm is designed
  for a fixed `n` (and `Δ`); it does not know `V`. This is the paper's well-formedness
  assumption.
* **Local state sets**: one state type `σ` for all processes (the paper allows a set per
  process). Every algorithm with per-process state sets can be simulated by one with a single type
  (tag states with the owner, and treat a wrongly tagged state as a fixed default state). Its
  executions agree from the second configuration on, so the impossibilities transfer; this
  reduction is not formalized. `σ` must be nonempty: otherwise there are no configurations and
  `PseudoStab` is vacuous.
* **Self-stabilization**: the legitimate set `L` is a set of configurations of all of `ι` (values
  outside `V` are irrelevant; this is equivalent to sets of `V`-configurations). Remark 1
  (self ⇒ pseudo) needs recurring classes; we prove that all nine classes are suffix-closed
  (`J_shift`).
* **Pseudo-stabilization time**: `PseudoStabWithin A C n T` means that `SP_LE` holds from
  0-indexed time `T` on in every execution, i.e. every pseudo-stabilization phase has length
  `≤ T`.

### Algorithm `LE`

* Maps (`MapType`) are finite maps `ι ⇀ ℕ × Fin (Δ+1)` (`FMap`, finite support). Timers live in
  `{0, …, Δ}` as in the paper, also in arbitrary initial states; `msgs` is a `Finset` of records.
* The received records form a **set** (`mailbox`). A record received from two neighbours is
  processed once, so line 18 increments the suspicion value once per distinct record. The paper
  does not say whether the mailbox is a set or a multiset; the proof only uses "some increment"
  vs. "no increment".
* The loop of lines 11–18 processes the records **in an arbitrary fixed order**
  (`Finset.toList`). All our lemmas are proved for every processing order. The loop is written
  componentwise (`body = (bodyM, bodyL, bodyG)`). This is equivalent: line 13 only touches
  `msgs`, lines 14–15 only `Lstable[id]` with `id ≠ id(p)`, line 17 only `Gstable[id']` with
  `id' ≠ id(p)`, and line 18 only the entries of `id(p)`.
* `LSPs[id].susp` for a received record with `id ∉ LSPs` is `0` (never happens: line 2 filters
  such records).
* Line 27 with an empty `Gstable` returns `id(p)` (never happens after line 5).
* In the HeardOf model a process always "receives" its own state; `LE` ignores it (graphs are
  loopless in the paper).

## Not formalized

* The self-stabilizing algorithms for `J_{*,*}`, `J^Q_{*,*}(Δ)`, `J^B_{*,*}(Δ)` from the authors'
  earlier paper (ICDCN 2021, reference [5] of the paper), which Figure 1 relies on (green area).
* The informal discussion in the conclusion (bi-sources, eventual timeliness).
