import Papers.PODC2016.GreedySpanner.Lemma3
import Papers.PODC2016.GreedySpanner.MST

/-!
# Theorem 5: the greedy spanner is existentially optimal (Section 3)

* `optSparse G w t`, `optLight G w t` — `OPT_t^sparse(G)`, `OPT_t^light(G)`: the minimum size and
  the minimum lightness `w(H')/w(MST(G))` of a `t`-spanner `H'` of `G`.
* A graph family is a set `𝒢` of weighted graphs on the vertex type `V` (`|V| = n`);
  `familyOptSparse 𝒢 t = sup_{G ∈ 𝒢} OPT_t^sparse(G)` and similarly `familyOptLight`.
* `theorem5` — for `𝒢` closed under edge removal, the greedy `t`-spanner of any `G ∈ 𝒢` has at most
  `OPT_t^sparse(𝒢)` edges and lightness at most `OPT_t^light(𝒢)`.
  `existentially_optimal_sparse` / `existentially_optimal_light`: the worst greedy size (lightness)
  over `𝒢` *equals* `OPT_t^sparse(𝒢)` (`OPT_t^light(𝒢)`).
* `corollary1_size` — the greedy `t`-spanner with `t ≥ 2k - 1` has girth `> 2k`, hence at most
  `n^{1+1/k} + n` edges (Moore bound); `greedy_le_of_forall_exists` — any existential bound on the
  size and lightness of `t`-spanners of all graphs transfers to the greedy `t`-spanner (Corollary 1
  with Theorem 1 of [CW18], Corollary 2 with [BFN19], both cited results taken as hypotheses).
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} [Fintype V] {G H : SimpleGraph V} {w : Sym2 V → ℝ≥0} {t : ℝ≥0}

/-- `OPT_t^sparse(G)`: the minimum number of edges of a `t`-spanner of `(G, w)`. -/
noncomputable def optSparse (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) : ℕ∞ :=
  ⨅ (H : SimpleGraph V) (_ : IsWSpanner G H w t), (H.edgeSet.ncard : ℕ∞)

/-- The lightness `Ψ(H) = w(H) / w(MST(G))` of a subgraph `H` of `(G, w)`. -/
noncomputable def lightness (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (H : SimpleGraph V) : ℝ≥0∞ :=
  wt w H / mstWeight G w

/-- `OPT_t^light(G)`: the minimum lightness of a `t`-spanner of `(G, w)`. -/
noncomputable def optLight (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (H : SimpleGraph V) (_ : IsWSpanner G H w t), lightness G w H

/-- A family of weighted graphs on the vertex set `V` is closed under edge removal. -/
def ClosedUnderEdgeRemoval (𝒢 : Set (SimpleGraph V × (Sym2 V → ℝ≥0))) : Prop :=
  ∀ G H w, (G, w) ∈ 𝒢 → H ≤ G → (H, w) ∈ 𝒢

/-- `OPT_t^sparse(𝒢) = sup_{G ∈ 𝒢} OPT_t^sparse(G)`. -/
noncomputable def familyOptSparse (𝒢 : Set (SimpleGraph V × (Sym2 V → ℝ≥0))) (t : ℝ≥0) : ℕ∞ :=
  ⨆ p ∈ 𝒢, optSparse p.1 p.2 t

/-- `OPT_t^light(𝒢) = sup_{G ∈ 𝒢} OPT_t^light(G)`. -/
noncomputable def familyOptLight (𝒢 : Set (SimpleGraph V × (Sym2 V → ℝ≥0))) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨆ p ∈ 𝒢, optLight p.1 p.2 t

omit [Fintype V] in
lemma optSparse_le (hH : IsWSpanner G H w t) : optSparse G w t ≤ H.edgeSet.ncard :=
  iInf₂_le H hH

lemma optLight_le (hH : IsWSpanner G H w t) : optLight G w t ≤ lightness G w H :=
  iInf₂_le H hH

/-- By Lemma 3, the greedy spanner `H` is its own sparsest `t`-spanner. -/
theorem optSparse_greedy (ht : 1 ≤ t) (hH : IsGreedySpanner G w t H) :
    optSparse H w t = H.edgeSet.ncard :=
  le_antisymm (optSparse_le (isWSpanner_refl ht))
    (le_iInf₂ fun H' hH' => by rw [lemma3 hH hH'])

/-- By Lemma 3 and Observation 2, the lightest `t`-spanner of the greedy spanner `H` (lightness
measured in `H`) is `H` itself, and its lightness equals the lightness of `H` in `G`. -/
theorem optLight_greedy (ht : 1 ≤ t) (hH : IsGreedySpanner G w t H) :
    optLight H w t = lightness G w H := by
  have h : lightness H w H = lightness G w H := by
    unfold lightness
    rw [IsGreedySpanner.mstWeight_eq hH]
  rw [← h]
  exact le_antisymm (optLight_le (isWSpanner_refl ht))
    (le_iInf₂ fun H' hH' => by rw [lemma3 hH hH'])

/-- **Theorem 5** of Filtser–Solomon (*greedy is existentially optimal*). Let `𝒢` be a family of
weighted graphs on `n = |V|` vertices closed under edge removal, and `t ≥ 1`. For every `G ∈ 𝒢`, the
greedy `t`-spanner `H` of `G` has at most `OPT_t^sparse(𝒢)` edges and lightness at most
`OPT_t^light(𝒢)`. -/
theorem theorem5 {𝒢 : Set (SimpleGraph V × (Sym2 V → ℝ≥0))} (h𝒢 : ClosedUnderEdgeRemoval 𝒢)
    (hG : (G, w) ∈ 𝒢) (ht : 1 ≤ t) (hH : IsGreedySpanner G w t H) :
    (H.edgeSet.ncard : ℕ∞) ≤ familyOptSparse 𝒢 t ∧ lightness G w H ≤ familyOptLight 𝒢 t := by
  have hmem : (H, w) ∈ 𝒢 := h𝒢 G H w hG (hH.isWSpanner ht).1
  exact ⟨le_iSup₂_of_le (H, w) hmem (optSparse_greedy ht hH).ge,
    le_iSup₂_of_le (H, w) hmem (optLight_greedy ht hH).ge⟩

/-- Existential optimality (size), as defined in Section 1.3: the maximum size of the greedy
`t`-spanner over `𝒢` equals the maximum size of an optimal `t`-spanner over `𝒢`. -/
theorem existentially_optimal_sparse {𝒢 : Set (SimpleGraph V × (Sym2 V → ℝ≥0))}
    (h𝒢 : ClosedUnderEdgeRemoval 𝒢) (ht : 1 ≤ t) :
    (⨆ p ∈ 𝒢, ⨆ (H : SimpleGraph V) (_ : IsGreedySpanner p.1 p.2 t H), (H.edgeSet.ncard : ℕ∞)) =
      familyOptSparse 𝒢 t := by
  refine le_antisymm (iSup₂_le fun p hp => iSup₂_le fun H hH => (theorem5 h𝒢 hp ht hH).1)
    (iSup₂_le fun p hp => ?_)
  obtain ⟨H, hH⟩ := exists_isGreedySpanner p.1 p.2 t
  exact le_iSup₂_of_le p hp (le_iSup₂_of_le H hH (optSparse_le (hH.isWSpanner ht)))

/-- Existential optimality (lightness). -/
theorem existentially_optimal_light {𝒢 : Set (SimpleGraph V × (Sym2 V → ℝ≥0))}
    (h𝒢 : ClosedUnderEdgeRemoval 𝒢) (ht : 1 ≤ t) :
    (⨆ p ∈ 𝒢, ⨆ (H : SimpleGraph V) (_ : IsGreedySpanner p.1 p.2 t H), lightness p.1 p.2 H) =
      familyOptLight 𝒢 t := by
  refine le_antisymm (iSup₂_le fun p hp => iSup₂_le fun H hH => (theorem5 h𝒢 hp ht hH).2)
    (iSup₂_le fun p hp => ?_)
  obtain ⟨H, hH⟩ := exists_isGreedySpanner p.1 p.2 t
  exact le_iSup₂_of_le p hp (le_iSup₂_of_le H hH (optLight_le (hH.isWSpanner ht)))

/-- The family of all weighted graphs on `V` is closed under edge removal; hence any existential
upper bound on the size and lightness of `t`-spanners of *all* weighted graphs (Theorem 1 of [CW18]
for Corollary 1; the bound of [BFN19] for Corollary 2) holds for the greedy `t`-spanner. -/
theorem greedy_le_of_forall_exists (ht : 1 ≤ t) {m : ℕ} {ℓ : ℝ≥0∞}
    (hex : ∀ (G : SimpleGraph V) (w : Sym2 V → ℝ≥0), ∃ H', IsWSpanner G H' w t ∧
      H'.edgeSet.ncard ≤ m ∧ lightness G w H' ≤ ℓ)
    (hH : IsGreedySpanner G w t H) : H.edgeSet.ncard ≤ m ∧ lightness G w H ≤ ℓ := by
  have h5 := theorem5 (𝒢 := Set.univ) (fun _ _ _ _ _ => trivial) (Set.mem_univ (G, w)) ht hH
  refine ⟨?_, h5.2.trans (iSup₂_le fun p _ => ?_)⟩
  · have : familyOptSparse Set.univ t ≤ m := iSup₂_le fun p _ => by
      obtain ⟨H', hH', hm, -⟩ := hex p.1 p.2
      exact (optSparse_le hH').trans (by exact_mod_cast hm)
    exact_mod_cast h5.1.trans this
  · obtain ⟨H', hH', -, hl⟩ := hex p.1 p.2
    exact (optLight_le hH').trans hl

/-! ### Corollary 1, size part: girth and the Moore bound -/

/-- **Corollary 1, size part** (unconditional): for `k ≥ 1` and `t ≥ 2k - 1` (e.g. the paper's
`t = (2k - 1)(1 + ε)`), the greedy `t`-spanner has at most `n^{1+1/k} + n` edges. -/
theorem corollary1_size {k : ℕ} (hk : 1 ≤ k) (ht : ((2 * k - 1 : ℕ) : ℝ≥0) ≤ t)
    (hH : IsGreedySpanner G w t H) :
    (H.edgeSet.ncard : ℝ) ≤ (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) + Fintype.card V :=
  (hH.noShortCycles ht).ncard_edgeSet_le_rpow hk

end GreedySpanner
