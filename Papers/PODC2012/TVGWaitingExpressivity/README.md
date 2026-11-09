# Waiting in Dynamic Networks — PODC 2012

Arnaud Casteigts, Paola Flocchini, Emmanuel Godard, Nicola Santoro, Masafumi Yamashita. *Brief Announcement: Waiting
in Dynamic Networks.* PODC 2012. DOI [10.1145/2332432.2332452](https://doi.org/10.1145/2332432.2332452). Formalized
version: arXiv [1205.1975](https://arxiv.org/abs/1205.1975) v1, *Expressivity of Time-Varying Graphs and the Power of
Waiting in Dynamic Networks* (the full version with all proofs); numbering follows it.

**Verdict: 🛠️ Hard fix.** All three main results hold and are proved in Lean: without waiting every language is
accepted (Theorem 3.1), with waiting exactly the regular languages (Theorem 4.1), with bounded waiting the same as
without (Theorem 5.1). But the paper's proof of the hard half of Theorem 4.1 is broken (it rests on a false lemma and
several invalid steps); we prove it differently, via Higman's lemma on walks. The proof of Theorem 5.1 leaves one
inclusion unargued.

## Mistakes in the paper

### ❌ Lemma 4.10 (powerset of a well quasi-order)
The recalled "Higman" lemma — if `(Q, ≤)` is a wqo then so is `(𝒫(Q), ≤_P)` — is false for arbitrary (infinite)
subsets: Rado's wqo `Q = {(i, j) | i < j}` has the infinite `≤_P`-antichain `A_k = {(k, l) | l > k}`
(`lemma_4_10_false`).

**Impact.** Only the paper's proof of Theorem 4.12 uses it, on infinite antichains; Higman's result is about finite
subsets and does not suffice there. Theorem 4.1 is unaffected: we prove it without the `≺` machinery.

**Details.** Rado's order: `(i, j) ≤ (k, l)` iff `(i = k ∧ j ≤ l) ∨ j < k`. It is a wqo (`radoLE_wqo`: in any
sequence either some later first coordinate exceeds an earlier second one, or all first coordinates are bounded and
a pigeonhole + Dickson argument applies). For `k ≠ k'`, the element `(k, k + k' + 1)` of `A_k` is below no element
of `A_{k'}` (`not_injDom_radoSet`), so no map `A_k → A_{k'}`, injective or not, dominates.

### ✏️ Slips
- **Start date** (Section 2): acceptance does not fix when journeys start. Section 3 needs date `0`: if journeys of
  `G₂` may start at any date, `G₂` accepts words outside `L` (`G2_other_start_date`). The example `G₁` starts at date
  `1`. We make the start date part of the automaton.
- **Waiting at the start node** (Section 4): with `start(J)` = departure of the first transition and
  `J*x = J*_{0,x}`, Lemma 4.2 is false as written (one node; `b` present only at date `0` with latency `1`, `a` only
  at date `1`: every journey of `ba` contains the walk `a`, so `a ≺ ba`, but `a` has no journey departing at `0`), and
  so is the left half of Proposition 4.8's proof. Intended: a journey may wait at its start node, as in our model;
  then the corrected Lemma 4.2 holds (`Sched.sublist`).
- **Unary alphabet** (Theorem 3.1): in base `q = 1` the encoding `φ(w) = "1.w"` is not injective, so `G₂` is not
  defined. Any base `b ≥ max(2, q)` works (`theorem_3_1`, `Lnowait_eq_univ`).
- **`G_{2,d}`** (Theorem 5.1): the presence tests read "`⌊t/(d+1)⌋ ∈ φ_d(Σ*)`" instead of `∈ φ(Σ*)`, and one latency
  uses "`ψ_d⁻¹(t)`" instead of `ψ_d(t)`; as printed the construction is wrong. Corrected in `G2d`.

### Typos
- `φ(ε) = 0 "by convention"`, while the formula gives `q⁰ = 1`.
- Corollary 4.6 lacks its relation symbol ("`Down≺(L)L`"); "time-expanded by a factor `d`" should be `d + 1`; the
  journey definition requires `ρ(eᵢ, tᵢ) = 1` only "for `1 ≤ i < k`" (should be `≤ k`).

## Proof gaps (statements true)

### 🛠️ Theorem 4.1 (𝓛_wait ⊆ regular; Proposition 4.4, Theorem 4.12, Lemma 4.13)
The proof that `(Σ*, ≺)` is a well quasi-order does not work: Lemma 4.13 needs `x ≺ ax`, which fails, and the proof
of Theorem 4.12 confuses `≺` with the subword order and relies on the false Lemma 4.10.

**Impact.** Statement true; repaired with a new proof (`theorem_4_1`, `Lwait_isRegular`). Proposition 4.4 and
Theorem 4.12 themselves remain unverified.

**Details.** `≺` compares walks with the *same endpoints*. In Lemma 4.13, `A = {(a, x) | x ∈ Down≺(X) \ X, ax ∈ X}`
covers `X` only if `x ≺ ax` for all `ax ∈ X`; with a single edge `u →a v`, already `ε ⊀ a`. In Theorem 4.12, "for
all `x ∈ X_{i+1}` there is `y ∈ X_i` with `x ≺ y`, ie `x ⊆ y`" identifies `≺` with the subword order (which Remark
4.14 says is impossible), the claim that the `y`'s can be chosen pairwise distinct is unjustified, and Lemma 4.10 is
applied to infinite antichains. We did not try to save this route (it would need better-quasi-order theory).

**Repair.** We work with walks, i.e. words over the finite alphabet of edges. With waiting, every subsequence of a
schedulable edge sequence is schedulable (take the kept edges at their original departure dates; dropped edges become
pauses) — the content of Lemma 4.2 (`Sched.sublist`). So the schedulable sequences form a subword-closed language,
which is regular by Haines' theorem (complement = finitely many upward closures by Higman's lemma;
`Cslib.Language.IsRegular.of_sublist_closed`). `L_wait(G)` is its intersection with the regular set of walks from `I`
to `F`, mapped letter by letter to edge labels (`Lwait_eq_map`, `Cslib.Language.IsRegular.map`). The proof needs no
property of `ρ`, `ζ` and no discreteness of time; Theorem 4.7 (Harju–Ilie) is not needed.

### 🔧 Theorem 5.1 (𝓛_wait[d] = 𝓛_nowait)
The proof only shows that every computable language is `L_wait[d]` of the dilated TVG `G_{2,d}`; the inclusion
`𝓛_wait[d] ⊆ 𝓛_nowait` is not argued, and `𝓛_nowait ⊆ 𝓛_wait[d]` would need `𝓛_nowait ⊆` computable languages,
which the paper does not prove.

**Impact.** Statement true; repaired by two direct simulations (`theorem_5_1`, and `theorem_5_1_computable` for computable TVGs).

**Repair.** `dilate d A` stretches time by `d + 1` and opens edges only at multiples of `d + 1`, so pauses `≤ d` are
useless: `L_wait[d](dilate d A) = L_nowait(A)` (`dilate_LwaitAtMost`). `withPause d A` has nodes `V × Fin (d+1)`,
`(u, j)` meaning "leave `u` after a pause of `j`": `L_nowait(withPause d A) = L_wait[d](A)` (`withPause_Lnowait`).
Both preserve computability of `ρ` and `ζ`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- A TVG over discrete time `ℕ`: finite node type `V`, finite alphabet; edges `(u, a, v)` with presence
  `present e t` (`ρ(e, t) = 1`) and latency `latency e t` (`ζ(e, t)`), arbitrary functions. A TVG-automaton adds
  initial and accepting nodes and a start date. No distributed algorithm, no failures, no randomness: the TVG is the
  (adversarial) environment and the language measures its expressivity.
- One journey relation `Journey P u t w v t'` for all three settings, parametrised by the pause rule `P t t₁`
  (`noWait`: `t₁ = t`; `wait`: `t ≤ t₁`; `waitAtMost d`: `t ≤ t₁ ≤ t + d`). A journey is at its initial node at the
  start date and may wait there under the same rule.
- Families `LnowaitFamily α`, `LwaitFamily α`, `LwaitAtMostFamily α d` quantify over all finite TVG-automata. The
  paper requires `ρ`, `ζ` computable: `TVG.IsComputable` and the families `LnowaitComp q`, `LwaitComp q`,
  `LwaitAtMostComp q d` (nodes `Fin n`, alphabet `Fin q`) are the faithful versions. The arbitrary-`ρ` version is
  stronger for Theorem 4.1 (more TVGs, still only regular languages); for Theorems 3.1 and 5.1 it is a statement about
  a larger model, not a strengthening, so the computable versions are the ones that match the paper.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Example of Section 2 (`G₁`, Table 1): `L_nowait(G₁) = {aⁿbⁿ : n ≥ 1}` | `ExampleG1.Lnowait_G1`, `ExampleG1.G1_deterministic` | `ExampleG1.lean` |
| Theorem 3.1: `L_nowait(G₂) = L` | `theorem_3_1` | `NoWait.lean` |
| Theorem 3.1 as a family statement (every language) | `Lnowait_eq_univ` | `NoWait.lean` |
| Theorem 3.1, computable `ρ`, `ζ` | `theorem_3_1_computable`, `G2_isComputable` | `Computable.lean` |
| Theorem 4.1: `𝓛_wait = 𝓡` | `theorem_4_1` (`Lwait_isRegular`, `isRegular_mem_LwaitFamily`) | `Wait.lean`, `FromDFA.lean` |
| Theorem 4.1, computable `ρ`, `ζ` | `theorem_4_1_computable` | `Computable.lean` |
| Lemma 4.2 (corrected) | `TVG.Sched.sublist` | `Wait.lean` |
| Lemma 4.10 is false | `lemma_4_10_false` | `Rado.lean` |
| Theorem 5.1: `𝓛_wait[d] = 𝓛_nowait` | `theorem_5_1` | `BoundedWait.lean` |
| Theorem 5.1, the construction `G_{2,d}` | `G2d_LwaitAtMost` | `NoWait.lean` |
| Theorem 5.1, computable `ρ`, `ζ` | `theorem_5_1_computable` | `Computable.lean` |
| "as powerful as a Turing machine": `𝓛_nowait = 𝓛_wait[d]` = decidable languages (computable TVGs) | `LnowaitComp_eq_computable`, `LwaitAtMostComp_eq_computable` | `Computable.lean` |
| start date matters | `G2_other_start_date` | `NoWait.lean` |

**Remarks.** Theorem 3.1 holds for every language, computable or not, when `ρ` is arbitrary (`Lnowait_eq_univ`); the
paper's computability requirement on `ρ` is what makes "all computable languages" the right statement. The DFA
simulation in Theorem 4.1 does not need determinism (`ofDFA_lang` holds for any pause rule allowing immediate
departure). For computable TVGs the direct-journey language is decidable (`computablePred_mem_Lnowait`: the
reachable (node, date) pairs are computed letter by letter), so the abstract's "as powerful as a Turing machine" is
exact: `𝓛_nowait = 𝓛_wait[d]` = the decidable languages.

**Not formalized.** The `≺` route of Section 4 (Propositions 4.3–4.9, Theorem 4.12, Lemma 4.13, Corollary 4.6) and
the cited Theorem 4.7 (Harju–Ilie); not needed for Theorem 4.1.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. Haines'
theorem and closure of regular languages under letter maps are staged in
`Podc/Computability/Languages/SubwordClosed.lean` (CSLib candidates), on top of CSLib's
`Cslib/Computability/Languages/RegularLanguage.lean` and Mathlib's Higman lemma.
