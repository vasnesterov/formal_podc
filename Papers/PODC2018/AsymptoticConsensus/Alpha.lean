import Papers.PODC2018.AsymptoticConsensus.LowerBounds

/-!
# Section 7–8 of FNS'18: α-diameter, Theorem 5, Lemma 24, Theorem 6

* `Roots K`, `SourceIncompatible N` (Definition 18).
* `AlphaRel K G H` (Definition 15, **per-agent reading**: every root of `K` has the same
  in-neighbours in `G` and `H`). The paper literally defines `In_S(G) = ⋃_{j∈S} In_j(G)` (a set of
  nodes); this reading is `AlphaRelLit`, under which Lemma 20 and Theorem 5 are false (see
  `Counterexamples.lean`).
* `AlphaDiamLE rel N D`: the α-diameter of `N` is at most `D` (Definition 22).
* Lemma 20 (`val_inter_nonempty_alpha`), Lemma 21 (`lemma21`, with the better constant
  `1/(n-1)`), **Theorem 5** (`theorem5`, with the hypothesis "N is source-incompatible", which is
  implied by "exact consensus is not solvable", see `Exact.lean`), Corollary 23,
  Lemma 24 (`alphaDiam_NA`), **Theorem 6** (`theorem6`).
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set Classical
open Cslib.DynNet (IsRoot)
open scoped ENNReal

variable {α σ V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The roots `R(K)` of a graph: agents with a path to every agent. -/
def Roots (K : Graph α) : Set α := {r | IsRoot K r}

/-- **Definition 18.** `N` is source-incompatible if no agent is a root of all graphs of `N`. -/
def SourceIncompatible (N : Set (Graph α)) : Prop := ∀ r, ∃ G ∈ N, r ∉ Roots G

/-- **Definition 15** (per-agent reading): `G α_K H` iff every root of `K` has the same
in-neighbours in `G` and `H`. -/
def AlphaRel (K G H : Graph α) : Prop := ∀ i ∈ Roots K, SameIn G H i

/-- **Definition 15** (literal reading): `In_{R(K)}(G) = In_{R(K)}(H)` where
`In_S(G) = ⋃_{j ∈ S} In_j(G)` is a set of nodes. -/
def AlphaRelLit (K G H : Graph α) : Prop :=
  ∀ j, (∃ i ∈ Roots K, Hears G i j) ↔ (∃ i ∈ Roots K, Hears H i j)

/-- **Definition 22**: the α-diameter of `N` (w.r.t. a reading `rel` of Definition 15) is at most
`D`: any two graphs of `N` are joined by a chain of at most `D` α-steps inside `N`. -/
def AlphaDiamLE (rel : Graph α → Graph α → Graph α → Prop) (N : Set (Graph α)) (D : ℕ) : Prop :=
  ∀ G ∈ N, ∀ H ∈ N, ∃ q ≤ D, ∃ c : ℕ → Graph α, c 0 = G ∧ c q = H ∧
    ∀ r < q, c r ∈ N ∧ c (r + 1) ∈ N ∧ ∃ K ∈ N, rel K (c r) (c (r + 1))

theorem roots_closed {K : Graph α} {i j : α} (hi : i ∈ Roots K) (hj : Hears K i j) :
    j ∈ Roots K := by
  rcases hj with rfl | hj
  · exact hi
  · exact fun y => Relation.ReflTransGen.head hj (hi y)

namespace Alg

variable {A : Alg α σ V}

/-- **Lemma 20.** If `G α_{N,K} H`, then `Y*(G.C) ∩ Y*(H.C) ≠ ∅` (for reachable `C`). -/
theorem val_inter_nonempty_alpha [Nontrivial V] [Finite α] [Nonempty α] {N : Set (Graph α)}
    (hA : A.Solves N) {G H K : Graph α} (hG : G ∈ N) (hH : H ∈ N) (hK : K ∈ N)
    (hrel : AlphaRel K G H) {C : α → σ} (hC : A.Reach N C) :
    (A.val (Pat N) (next A.step G C) ∩ A.val (Pat N) (next A.step H C)).Nonempty := by
  obtain ⟨r, hr⟩ := hA.exists_root hK
  exact val_inter_nonempty_of_closed hA subset_rfl (const_mem_pat hK) ⟨r, hr⟩
    (fun i hi j hj => roots_closed hi hj) (hC.next hG) (hC.next hH)
    (fun i hi => next_eq_of_agree (hrel i hi) fun _ _ => rfl)

/-- **Lemma 21** (with the constant `1/(n-1)` instead of the paper's `1/n`). If `N` is
source-incompatible then for every `v` there is an initial configuration with values in `{0, v}`
whose valency diameter is at least `‖v‖/(n-1)`. -/
theorem lemma21 [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) {A : Alg (Fin n) σ V}
    {N : Set (Graph (Fin n))} (hA : A.Solves N) (hSI : SourceIncompatible N) (v : V) :
    ∃ x : Fin n → V, (∀ i, x i = 0 ∨ x i = v) ∧
      edist 0 v ≤ (n - 1 : ℕ) * A.δ N (A.initC x) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hN : N.Nonempty := by obtain ⟨G, hG, -⟩ := hSI ⟨0, by omega⟩; exact ⟨G, hG⟩
  let xs : ℕ → Fin n → V := fun k i => if i.val < k then v else 0
  let Y : ℕ → Set V := fun k => A.val (Pat N) (A.initC (xs k))
  -- consecutive valencies intersect
  have hint : ∀ k < n, (Y k ∩ Y (k + 1)).Nonempty := by
    intro k hk
    obtain ⟨G, hG, hkG⟩ := hSI ⟨k, hk⟩
    obtain ⟨r, hr⟩ := hA.exists_root hG
    refine val_inter_nonempty_of_closed hA subset_rfl (const_mem_pat hG) ⟨r, hr⟩
      (fun i hi j hj => roots_closed hi hj) (Reach.initC hN _) (Reach.initC hN _) ?_
    intro i hi
    have hik : i.val ≠ k := by
      rintro h; apply hkG
      have : i = ⟨k, hk⟩ := Fin.ext h
      rw [← this]; exact hi
    simp only [initC, xs]
    congr 1
    by_cases h : i.val < k
    · simp [h, show i.val < k + 1 by omega]
    · simp [h, show ¬ i.val < k + 1 by omega]
  have hY0 : Y 0 ⊆ {0} := by
    intro z hz
    have := hA.val_initC_subset_hull hN (xs 0) hz
    have hx : xs 0 = fun _ => 0 := by funext i; simp [xs]
    rwa [hx, range_const, convexHull_singleton] at this
  have hYn : Y n ⊆ {v} := by
    intro z hz
    have := hA.val_initC_subset_hull hN (xs n) hz
    have hx : xs n = fun _ => v := by funext i; simp [xs, i.isLt]
    rwa [hx, range_const, convexHull_singleton] at this
  obtain ⟨z0, hz0, hz0'⟩ := hint 0 (by omega)
  obtain ⟨zl, hzl, hzl'⟩ := hint (n - 1) (by omega)
  have hz0e : z0 = 0 := hY0 hz0
  have hzle : zl = v := hYn (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hzl')
  have hchain := edist_le_sum_chain (fun r => Y (r + 1)) (n - 2)
    (fun r hr => hint (r + 1) (by omega)) z0 hz0' zl (by rwa [show n - 2 + 1 = n - 1 by omega])
  rw [hz0e, hzle] at hchain
  obtain ⟨k, hk, hmax⟩ := (Finset.range (n - 2 + 1)).exists_max_image
    (fun r => Metric.ediam (Y (r + 1))) (by simp)
  refine ⟨xs (k + 1), fun i => by by_cases h : i.val < k + 1 <;> simp [xs, h], ?_⟩
  calc edist 0 v ≤ ∑ r ∈ Finset.range (n - 2 + 1), Metric.ediam (Y (r + 1)) := hchain
    _ ≤ ∑ _r ∈ Finset.range (n - 2 + 1), Metric.ediam (Y (k + 1)) :=
        Finset.sum_le_sum fun r hr => hmax r hr
    _ = (n - 1 : ℕ) * A.δ N (A.initC (xs (k + 1))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, show n - 2 + 1 = n - 1 by omega]
        rfl

/-- Some initial configuration has positive valency diameter in a source-incompatible model. -/
theorem exists_δ_pos_of_sourceIncompatible [Nontrivial V] {n : ℕ} (hn : 2 ≤ n)
    {A : Alg (Fin n) σ V} {N : Set (Graph (Fin n))} (hA : A.Solves N)
    (hSI : SourceIncompatible N) : ∃ x : Fin n → V, A.δ N (A.initC x) ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨x, -, hx⟩ := lemma21 hn hA hSI v
  refine ⟨x, fun h => ?_⟩
  rw [h, mul_zero, nonpos_iff_eq_zero, edist_eq_zero] at hx
  exact hv hx.symm

/-- **Theorem 5 of FNS'18.** In a source-incompatible network model (in particular, by
`Exact.lean`, whenever exact consensus is not solvable) with α-diameter at most `D`, every
asymptotic consensus algorithm has contraction rate at least `1/(D+1)`. -/
theorem theorem5 [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) {A : Alg (Fin n) σ V}
    {N : Set (Graph (Fin n))} (hA : A.Solves N) (hSI : SourceIncompatible N) {D : ℕ}
    (hD : AlphaDiamLE AlphaRel N D) : ((D : ℝ≥0∞) + 1)⁻¹ ≤ A.rate N := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hfin : N.Finite := Set.toFinite N
  obtain ⟨x, hx⟩ := exists_δ_pos_of_sourceIncompatible hn hA hSI
  have hN : N.Nonempty := by obtain ⟨G, hG, -⟩ := hSI ⟨0, by omega⟩; exact ⟨G, hG⟩
  have hK : ((hfin.toFinset : Finset (Graph (Fin n))) : Set (Graph (Fin n))) = N := by simp
  refine le_rate_of_chains hA hfin.toFinset (by simpa using hN) (fun G hG => by simpa using hG)
    D ?_ x (by rwa [hK])
  intro C hC G hG H hH
  rw [hK]
  obtain ⟨q, hq, c, hc0, hcq, hc⟩ := hD G (by simpa using hG) H (by simpa using hH)
  refine ⟨q, hq, c, hc0, hcq, fun r hr => ?_, fun r hr => ?_⟩
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simpa [hc0] using hG
    · have := (hc (r - 1) (by omega)).2.1
      rw [Nat.sub_add_cancel hr0] at this
      simpa using this
  · obtain ⟨h1, h2, K, hK', hrel⟩ := hc r hr
    exact val_inter_nonempty_alpha hA h1 h2 hK' hrel hC

/-- **Corollary 23.** If some submodel `N' ⊆ N` is source-incompatible with α-diameter `≤ D`,
the contraction rate in `N` is at least `1/(D+1)`. -/
theorem corollary23 [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) {A : Alg (Fin n) σ V}
    {N N' : Set (Graph (Fin n))} (hA : A.Solves N) (hN' : N' ⊆ N)
    (hSI : SourceIncompatible N') {D : ℕ} (hD : AlphaDiamLE AlphaRel N' D) :
    ((D : ℝ≥0∞) + 1)⁻¹ ≤ A.rate N :=
  (theorem5 hn (hA.mono hN') hSI hD).trans (rate_mono hN')

end Alg

/-! ### Asynchronous rounds with crashes: Lemma 24 and Theorem 6 -/

/-- The network model `N_A` of round-based algorithms waiting for `n - f` messages: every agent
hears at least `n - f` agents (itself included). -/
def NA (n f : ℕ) : Set (Graph (Fin n)) :=
  {G | ∀ i, n - f ≤ (Finset.univ.filter fun j => Hears G i j).card}

/-- `H_r`: agents `< r f` use `H`'s in-neighbours, the others `G`'s. -/
def mixG (f r : ℕ) (H G : Graph (Fin n)) : Graph (Fin n) :=
  fun j i => if i.val < r * f then H j i else G j i

/-- `K_r`: nobody hears the agents of block `r` (`r f ≤ j < (r+1) f`). -/
def blockK (f r : ℕ) : Graph (Fin n) := fun j _ => ¬ (r * f ≤ j.val ∧ j.val < (r + 1) * f)

theorem hears_mixG {f r : ℕ} {H G : Graph (Fin n)} {i j : Fin n} :
    Hears (mixG f r H G) i j ↔ if i.val < r * f then Hears H i j else Hears G i j := by
  unfold Hears mixG; split_ifs <;> rfl

theorem card_block_le (f r : ℕ) :
    (Finset.univ.filter fun j : Fin n => r * f ≤ j.val ∧ j.val < (r + 1) * f).card ≤ f := by
  calc _ ≤ (Finset.Ico (r * f) ((r + 1) * f)).card := by
        refine Finset.card_le_card_of_injOn (fun j => j.val) (fun j hj => ?_)
          (fun a _ b _ h => Fin.ext h)
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hj
        simpa using hj
    _ = f := by rw [Nat.card_Ico]; ring_nf; omega

theorem blockK_mem_NA {f : ℕ} (r : ℕ) : blockK (n := n) f r ∈ NA n f := by
  intro i
  have h1 := card_block_le (n := n) f r
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun j : Fin n => r * f ≤ j.val ∧ j.val < (r + 1) * f)
  have h3 : (Finset.univ.filter fun j : Fin n => ¬ (r * f ≤ j.val ∧ j.val < (r + 1) * f)) ⊆
      Finset.univ.filter fun j => Hears (blockK f r) i j := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact Or.inr hj
  have h4 := Finset.card_le_card h3
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem roots_blockK {f r : ℕ} (hn : f < n) {i : Fin n} (hi : i ∈ Roots (blockK (n := n) f r)) :
    ¬ (r * f ≤ i.val ∧ i.val < (r + 1) * f) := by
  intro hb
  -- an agent of the block reaches nobody else
  have hstay : ∀ y, Relation.ReflTransGen (blockK (n := n) f r) i y → y = i := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hbc ih => subst ih; exact absurd hb hbc
  -- the block has at most `f < n` agents, so some agent is outside it, hence `≠ i`
  obtain ⟨y, hy⟩ : ∃ y : Fin n, y ≠ i := by
    by_contra h; push Not at h
    have : Fintype.card (Fin n) ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
    simp only [Fintype.card_fin] at this
    have hf0 : f = 0 := by omega
    subst hf0; simp at hb
  exact hy (hstay y (hi y))

theorem mixG_mem_NA {f : ℕ} {G H : Graph (Fin n)} (hG : G ∈ NA n f) (hH : H ∈ NA n f) (r : ℕ) :
    mixG f r H G ∈ NA n f := by
  intro i
  by_cases h : i.val < r * f
  · have : (Finset.univ.filter fun j => Hears (mixG f r H G) i j) =
        Finset.univ.filter fun j => Hears H i j :=
      Finset.filter_congr fun j _ => by rw [hears_mixG]; simp [h]
    rw [this]; exact hH i
  · have : (Finset.univ.filter fun j => Hears (mixG f r H G) i j) =
        Finset.univ.filter fun j => Hears G i j :=
      Finset.filter_congr fun j _ => by rw [hears_mixG]; simp [h]
    rw [this]; exact hG i

/-- **Lemma 24 of FNS'18.** For `1 ≤ f < n`, the α-diameter of `N_A` is at most `⌈n/f⌉`. -/
theorem alphaDiam_NA {f : ℕ} (hf : 1 ≤ f) (hfn : f < n) :
    AlphaDiamLE AlphaRel (NA n f) ((n + f - 1) / f) := by
  intro G hG H hH
  have hq : n ≤ (n + f - 1) / f * f := by
    have h1 := Nat.div_add_mod (n + f - 1) f
    have h2 := Nat.mod_lt (n + f - 1) (show 0 < f by omega)
    rw [mul_comm]; omega
  refine ⟨(n + f - 1) / f, le_rfl, fun r => mixG f r H G, ?_, ?_, fun r hr => ⟨?_, ?_, ?_⟩⟩
  · funext j i; simp [mixG]
  · funext j i; simp [mixG, show i.val < (n + f - 1) / f * f by omega]
  · exact mixG_mem_NA hG hH r
  · exact mixG_mem_NA hG hH (r + 1)
  · refine ⟨blockK f r, blockK_mem_NA r, fun i hi j => ?_⟩
    have hnot := roots_blockK hfn hi
    rw [hears_mixG, hears_mixG]
    by_cases h1 : i.val < r * f
    · simp [h1, show i.val < (r + 1) * f by nlinarith]
    · have h2 : ¬ i.val < (r + 1) * f := fun h => hnot ⟨by omega, h⟩
      simp [h1, h2]

/-- `N_A` is source-incompatible for `1 ≤ f` and `n ≥ 2`. -/
theorem sourceIncompatible_NA {f : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n) : SourceIncompatible (NA n f) := by
  intro k
  refine ⟨fun j _ => j ≠ k, fun i => ?_, fun hk => ?_⟩
  · have h3 : (Finset.univ.erase k) ⊆ Finset.univ.filter fun j => Hears (fun j _ => j ≠ k) i j :=
      fun j hj => by
        simp only [Finset.mem_erase] at hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inr hj.1
    have := Finset.card_le_card h3
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega
  · obtain ⟨y, hy⟩ : ∃ y : Fin n, y ≠ k := by
      by_cases h : k.val = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h' => h (by simp [Fin.ext_iff] at h'; omega)⟩
    have hstay : ∀ z, Relation.ReflTransGen (fun j (_ : Fin n) => j ≠ k) k z → z = k := by
      intro z hz
      induction hz with
      | refl => rfl
      | tail _ hbc ih => subst ih; exact absurd rfl hbc
    exact hy (hstay y (hk y))

/-- **Theorem 6 of FNS'18** (network-model form). For `n ≥ 2` agents and `1 ≤ f < n`, every
asymptotic consensus algorithm in the model `N_A` of round-based algorithms waiting for `n - f`
messages has contraction rate at least `1/(⌈n/f⌉ + 1)`. -/
theorem theorem6 [Nontrivial V] {f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (hfn : f < n)
    {A : Alg (Fin n) σ V} (hA : A.Solves (NA n f)) :
    (((n + f - 1) / f : ℕ) + 1 : ℝ≥0∞)⁻¹ ≤ A.rate (NA n f) :=
  Alg.theorem5 hn hA (sourceIncompatible_NA hf hn) (alphaDiam_NA hf hfn)

end AsymptoticConsensus
