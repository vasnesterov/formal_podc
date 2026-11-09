import Podc.Foundations.GameTheory.NeverBestResponse

/-!
# First-price cost-sharing games (Section 3.2 of [NSVZ])

N. Nisan, M. Schapira, G. Valiant, A. Zohar, *Best-Response Mechanisms* (ICS 2011; brief
announcement at PODC 2011), Section 3.2: Theorem 3.3 and the bid rule of Theorem 3.4.

Users `i : ι` (finitely many) have cost shares `c i S` (for `i ∈ S`), nonnegative and
cross-monotonic (`i ∈ S ⊆ T → c i T ≤ c i S`), and private values `v i`. In the first-price
cost-sharing game every user bids `b i : ℝ≥0`; the *serviced set* for `b` is the
maximum-cardinality set `S` with `c j S ≤ b j` for all `j ∈ S`; a serviced user gets `v i - b i`,
others get `0`.

## Main definitions

* `CostSharingRule`: cross-monotonic cost shares.
* `CostSharingRule.serviced`: the serviced set (the union of all feasible sets), with the bridge
  `serviced_unique_maxCard`: it is *the unique* feasible set of maximum cardinality (so the paper's
  lexicographic tie-breaking among such sets is never used).
* `CostSharingRule.game`: the game, with the (repaired) tie-breaking "prefer bids strictly closer
  to `v i`, at equal distance the lower bid".
* `CostSharingRule.gameLit`: the game with the *literal* tie-breaking of the paper
  (`|s - vᵢ| ≤ |t - vᵢ| → t ≺ᵢ s`, reflexive), see `gameLit_isNBR`.
* `CostSharingRule.outcome` (`s*`): users in `R_v = serviced v` bid `c j R_v`, the others `v i`.
* `CostSharingRule.moulinSet`: Moulin's mechanism.
* `CostSharingRule.mechBid`: the bid prescribed by the mechanism of Theorem 3.4.

## Main statements

* `theorem_3_3` (Theorem 3.3): NBR-solvability by the explicit 3-step elimination `elimSeq`; `s*`
  is the unique outcome and a PNE; its serviced set is the set chosen by Moulin's mechanism
  (`moulinSet_eq`), each serviced user pays its Moulin cost share `≤ vⱼ`; `s*` is a clear outcome
  (`clearWitness`, player-specific order with witness index `1`); `e_G ≤ n` for *every* `n`
  (`elimParam_le_card`; `n = 1, 2` need 1 resp. 2 steps) and `e_G ≤ 3`.
* `isBR_mechBid` (Theorem 3.4's bid rule is a tie-broken best response; `mechBid_eq_bestBid`
  identifies it with `min (price) vᵢ`), `hasBR`.
* `gameLit_isNBR`, `gameLit_solves`: with the literal (reflexive) tie-breaking rule every bid is
  NBR in every subgame, so every profile is a one-step outcome.

The paper's assumption `vᵢ > 0` is never used.
-/

open Set Function Cslib.GameTheory
open scoped NNReal

namespace Podc.BestResponseMechanisms.CostSharing

/-! ### A generic criterion for elimination steps -/

section Generic

variable {ι : Type*} {S : ι → Type*} {R : Type*} [DecidableEq ι] [LinearOrder R]
  {G : TieBreakGame ι S R}

-- CSLib candidate
/-- If the tie-breaking orders are total and `br i s` is a tie-broken best response of `i` to `s`,
then passing from `H` to `H' ⊆ H` is an NBR-elimination step as soon as every best response to a
profile of `H` lies in `H'`. -/
theorem elimStep_of_isBR (htot : ∀ i (x y : S i), x ≠ y → G.prec i x y ∨ G.prec i y x)
    (br : ∀ i, (∀ j, S j) → S i) (hbr : ∀ i s, G.IsBR i (br i s) s)
    {H H' : Subgame S} (hsub : ∀ i, H' i ⊆ H i)
    (hmap : ∀ i (s : ∀ j, S j), (∀ j, j ≠ i → s j ∈ H j) → br i s ∈ H' i) :
    G.ElimStep H H' := by
  refine ⟨hsub, fun i y _ hy' s hs => ⟨br i s, hsub i (hmap i s hs), ?_⟩⟩
  have hne : br i s ≠ y := fun h => hy' (h ▸ hmap i s hs)
  have hnb := hbr i s y
  unfold TieBreakGame.Beats at hnb ⊢
  rcases lt_trichotomy (G.utility i (update s i y)) (G.utility i (update s i (br i s)))
    with h | h | h
  · exact Or.inl h
  · rcases htot i _ _ hne with h' | h'
    · exact absurd (Or.inr ⟨h.symm, h'⟩) hnb
    · exact Or.inr ⟨h, h'⟩
  · exact absurd (Or.inl h) hnb

-- CSLib candidate
/-- `e_G ≤ r` as soon as some elimination of length `r` solves the game. -/
theorem elimParam_le {E : ℕ → Subgame S} {r : ℕ} {s : ∀ i, S i} (h : G.Solves E r s) :
    G.elimParam ≤ r :=
  Nat.sInf_le ⟨E, s, h⟩

end Generic

/-! ### Cost-sharing rules and the serviced set -/

/-- A cost-sharing rule: `c i S` is the (nonnegative) cost share of `i` in the serviced set `S`
(only meaningful for `i ∈ S`); it is *cross-monotonic*. -/
structure CostSharingRule (ι : Type*) where
  /-- `c i S` is the cost share of user `i ∈ S` when `S` is serviced. -/
  c : ι → Finset ι → ℝ≥0
  /-- Cross-monotonicity: `i ∈ S ⊆ T → c i T ≤ c i S`. -/
  cross_mono : ∀ ⦃i : ι⦄ ⦃S T : Finset ι⦄, i ∈ S → S ⊆ T → c i T ≤ c i S

namespace CostSharingRule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (C : CostSharingRule ι)

/-- `S` can be serviced under the bids `b`: every member bids at least its cost share. -/
def Feasible (b : ι → ℝ≥0) (S : Finset ι) : Prop :=
  ∀ j ∈ S, C.c j S ≤ b j

open Classical in
/-- The serviced set for the bids `b`: the union of all feasible sets. By
`serviced_unique_maxCard` it is the unique feasible set of maximum cardinality, i.e. the paper's
serviced set. -/
noncomputable def serviced (b : ι → ℝ≥0) : Finset ι :=
  Finset.univ.filter fun i => ∃ S, C.Feasible b S ∧ i ∈ S

variable {C}

lemma mem_serviced {b : ι → ℝ≥0} {i : ι} :
    i ∈ C.serviced b ↔ ∃ S, C.Feasible b S ∧ i ∈ S := by
  simp [serviced]

lemma subset_serviced {b : ι → ℝ≥0} {S : Finset ι} (h : C.Feasible b S) :
    S ⊆ C.serviced b :=
  fun _ hi => mem_serviced.2 ⟨S, h, hi⟩

lemma feasible_serviced (b : ι → ℝ≥0) : C.Feasible b (C.serviced b) := by
  intro j hj
  obtain ⟨S, hS, hjS⟩ := mem_serviced.1 hj
  exact (C.cross_mono hjS (subset_serviced hS)).trans (hS j hjS)

/-- **Bridge to the paper's definition.** The serviced set is feasible, and every feasible set
has at most its cardinality, with equality only for the serviced set itself. Hence it is *the
unique* maximum-cardinality feasible set and lexicographic tie-breaking never applies. -/
theorem serviced_unique_maxCard (b : ι → ℝ≥0) :
    C.Feasible b (C.serviced b) ∧ ∀ T, C.Feasible b T →
      T.card ≤ (C.serviced b).card ∧ (T.card = (C.serviced b).card → T = C.serviced b) :=
  ⟨feasible_serviced b, fun _ hT => ⟨Finset.card_le_card (subset_serviced hT),
    fun h => Finset.eq_of_subset_of_card_le (subset_serviced hT) h.ge⟩⟩

omit [Fintype ι] [DecidableEq ι] in
lemma Feasible.mono {b b' : ι → ℝ≥0} {S : Finset ι} (h : C.Feasible b S)
    (hb : ∀ j, b j ≤ b' j) : C.Feasible b' S :=
  fun j hj => (h j hj).trans (hb j)

/-- The serviced set is monotone in the bids. -/
lemma serviced_mono {b b' : ι → ℝ≥0} (hb : ∀ j, b j ≤ b' j) :
    C.serviced b ⊆ C.serviced b' :=
  subset_serviced ((feasible_serviced b).mono hb)

/-! ### The price of a user -/

/-- `S` is feasible for the users other than `i` (whose bid is ignored). -/
def FeasibleExcept (i : ι) (b : ι → ℝ≥0) (S : Finset ι) : Prop :=
  ∀ j ∈ S, j ≠ i → C.c j S ≤ b j

variable (C) in
open Classical in
/-- The largest coalition `A_i(b)` that would be serviced if `i` bid arbitrarily high:
the union of all sets feasible for the users other than `i`. -/
noncomputable def coalition (i : ι) (b : ι → ℝ≥0) : Finset ι :=
  Finset.univ.filter fun k => ∃ S, C.FeasibleExcept i b S ∧ k ∈ S

variable (C) in
/-- The price `c i (A_i(b))` of user `i` against the bids `b₋ᵢ` of the others: `i` is serviced iff
it bids at least its price (`mem_serviced_iff_price`). -/
noncomputable def price (i : ι) (b : ι → ℝ≥0) : ℝ≥0 :=
  C.c i (C.coalition i b)

lemma mem_coalition {i k : ι} {b : ι → ℝ≥0} :
    k ∈ C.coalition i b ↔ ∃ S, C.FeasibleExcept i b S ∧ k ∈ S := by
  simp [coalition]

lemma subset_coalition {i : ι} {b : ι → ℝ≥0} {S : Finset ι} (h : C.FeasibleExcept i b S) :
    S ⊆ C.coalition i b :=
  fun _ hk => mem_coalition.2 ⟨S, h, hk⟩

lemma self_mem_coalition (i : ι) (b : ι → ℝ≥0) : i ∈ C.coalition i b :=
  mem_coalition.2 ⟨{i}, fun _ hj hji => absurd (Finset.mem_singleton.1 hj) hji,
    Finset.mem_singleton_self i⟩

lemma feasibleExcept_coalition (i : ι) (b : ι → ℝ≥0) :
    C.FeasibleExcept i b (C.coalition i b) := by
  intro j hj hji
  obtain ⟨S, hS, hjS⟩ := mem_coalition.1 hj
  exact (C.cross_mono hjS (subset_coalition hS)).trans (hS j hjS hji)

lemma coalition_mono {i : ι} {b b' : ι → ℝ≥0} (hb : ∀ j, j ≠ i → b j ≤ b' j) :
    C.coalition i b ⊆ C.coalition i b' :=
  subset_coalition fun j hj hji => (feasibleExcept_coalition i b j hj hji).trans (hb j hji)

lemma coalition_congr {i : ι} {b b' : ι → ℝ≥0} (hb : ∀ j, j ≠ i → b j = b' j) :
    C.coalition i b = C.coalition i b' :=
  (coalition_mono fun j hj => (hb j hj).le).antisymm (coalition_mono fun j hj => (hb j hj).ge)

lemma price_congr {i : ι} {b b' : ι → ℝ≥0} (hb : ∀ j, j ≠ i → b j = b' j) :
    C.price i b = C.price i b' := by
  rw [price, price, coalition_congr hb]

/-- Higher bids by the others lower the price (cross-monotonicity). -/
lemma price_anti {i : ι} {b b' : ι → ℝ≥0} (hb : ∀ j, j ≠ i → b j ≤ b' j) :
    C.price i b' ≤ C.price i b :=
  C.cross_mono (self_mem_coalition i b) (coalition_mono hb)

lemma price_update (i : ι) (b : ι → ℝ≥0) (y : ℝ≥0) : C.price i (update b i y) = C.price i b :=
  price_congr fun _ hj => update_of_ne hj y b

lemma c_univ_le_price (i : ι) (b : ι → ℝ≥0) : C.c i Finset.univ ≤ C.price i b :=
  C.cross_mono (self_mem_coalition i b) (Finset.subset_univ _)

/-- `i` is serviced iff it bids at least its price. -/
theorem mem_serviced_iff_price {i : ι} {b : ι → ℝ≥0} :
    i ∈ C.serviced b ↔ C.price i b ≤ b i := by
  constructor
  · intro h
    obtain ⟨S, hS, hiS⟩ := mem_serviced.1 h
    have : S ⊆ C.coalition i b := subset_coalition fun j hj _ => hS j hj
    exact (C.cross_mono hiS this).trans (hS i hiS)
  · intro h
    refine subset_serviced (S := C.coalition i b) ?_ (self_mem_coalition i b)
    intro j hj
    by_cases hji : j = i
    · subst hji; exact h
    · exact feasibleExcept_coalition i b j hj hji

/-- If `i` is serviced, its coalition is the serviced set. -/
lemma coalition_eq_serviced {i : ι} {b : ι → ℝ≥0} (h : i ∈ C.serviced b) :
    C.coalition i b = C.serviced b := by
  apply le_antisymm
  · refine subset_serviced fun j hj => ?_
    by_cases hji : j = i
    · subst hji; exact mem_serviced_iff_price.1 h
    · exact feasibleExcept_coalition i b j hj hji
  · exact subset_coalition fun j hj _ => feasible_serviced b j hj

lemma price_eq_of_mem {i : ι} {b : ι → ℝ≥0} (h : i ∈ C.serviced b) :
    C.price i b = C.c i (C.serviced b) := by
  rw [price, coalition_eq_serviced h]


/-! ### The first-price cost-sharing game -/

variable (C)

/-- Utility in the 1st-price cost-sharing game: `v i - b i` if `i` is serviced, `0` otherwise. -/
noncomputable def utility (v : ι → ℝ≥0) (i : ι) (b : ι → ℝ≥0) : ℝ :=
  if i ∈ C.serviced b then (v i : ℝ) - b i else 0

/-- The repaired tie-breaking order of a user with value `w`: `Closer w x y` (`x ≺ y`, i.e. `y`
is preferred) iff `y` is strictly closer to `w` than `x`, or equally close and lower. -/
def Closer (w x y : ℝ≥0) : Prop :=
  |(y : ℝ) - w| < |(x : ℝ) - w| ∨ (|(y : ℝ) - w| = |(x : ℝ) - w| ∧ y < x)

/-- The 1st-price cost-sharing game with the (repaired) tie-breaking rules "prefer bids closer
to `vᵢ`". -/
noncomputable def game (v : ι → ℝ≥0) : TieBreakGame ι (fun _ => ℝ≥0) ℝ where
  utility := C.utility v
  prec i := Closer (v i)

/-- The paper's literal tie-breaking rule: `|s - vᵢ| ≤ |t - vᵢ| → t ≺ᵢ s`. -/
def CloserLit (w x y : ℝ≥0) : Prop :=
  |(y : ℝ) - w| ≤ |(x : ℝ) - w|

/-- The 1st-price cost-sharing game with the paper's literal tie-breaking rules. -/
noncomputable def gameLit (v : ι → ℝ≥0) : TieBreakGame ι (fun _ => ℝ≥0) ℝ where
  utility := C.utility v
  prec i := CloserLit (v i)

variable {C}

/-- **Slip in the paper (tie-breaking rule).** The literal rule is reflexive (`t ≺ᵢ t`), so by
Definition 2.2 every bid of every subgame is NBR there: it is beaten by itself. -/
theorem gameLit_isNBR (v : ι → ℝ≥0) (H : Subgame (fun _ : ι => ℝ≥0)) (i : ι) (y : ℝ≥0)
    (hy : y ∈ H i) : (C.gameLit v).IsNBR H i y :=
  fun _ _ => ⟨y, hy, Or.inr ⟨rfl, le_refl _⟩⟩

/-- Consequently, with the literal rule *every* profile is the outcome of a one-step NBR
elimination: the claimed uniqueness of the outcome fails. -/
theorem gameLit_solves (v : ι → ℝ≥0) (s : ι → ℝ≥0) :
    (C.gameLit v).Solves (fun k => if k = 0 then TieBreakGame.full else fun i => {s i}) 1 s := by
  refine ⟨⟨rfl, fun k hk => ?_⟩, rfl⟩
  obtain rfl : k = 0 := by omega
  refine ⟨fun i => subset_univ _, fun i y _ _ => gameLit_isNBR v _ i y trivial⟩

lemma closer_irrefl (w x : ℝ≥0) : ¬ Closer w x x := by
  simp [Closer]

lemma closer_total (w : ℝ≥0) {x y : ℝ≥0} (h : x ≠ y) : Closer w x y ∨ Closer w y x := by
  unfold Closer
  rcases lt_trichotomy |(y : ℝ) - w| |(x : ℝ) - w| with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_or_gt_of_ne h with h2 | h2
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl h1)

lemma closer_trans (w : ℝ≥0) {x y z : ℝ≥0} (h1 : Closer w x y) (h2 : Closer w y z) :
    Closer w x z := by
  unfold Closer at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h2.trans h1)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h2.trans h1, h2'.trans h1'⟩

/-- The repaired tie-breaking rule is a strict total order. -/
instance (w : ℝ≥0) : IsStrictTotalOrder ℝ≥0 (Closer w) where
  irrefl := closer_irrefl w
  trans _ _ _ := closer_trans w
  trichotomous _ _ h1 h2 := by_contra fun h => (closer_total w h).elim h1 h2

lemma utility_update (v : ι → ℝ≥0) (i : ι) (b : ι → ℝ≥0) (y : ℝ≥0) :
    C.utility v i (update b i y) = if C.price i b ≤ y then (v i : ℝ) - y else 0 := by
  simp only [utility, mem_serviced_iff_price, price_update, update_self]

variable (C) in
/-- The tie-broken best response of `i` to `b₋ᵢ`: bid the price if it is at most `vᵢ`, else bid
`vᵢ`. -/
noncomputable def bestBid (v : ι → ℝ≥0) (i : ι) (b : ι → ℝ≥0) : ℝ≥0 :=
  min (C.price i b) (v i)

/-- `bestBid` is the tie-broken best response (against all bids `ℝ≥0`). -/
theorem isBR_bestBid (v : ι → ℝ≥0) (i : ι) (b : ι → ℝ≥0) :
    (C.game v).IsBR i (C.bestBid v i b) b := by
  intro y hy
  simp only [TieBreakGame.Beats, game, utility_update, Closer, bestBid] at hy
  set p := C.price i b
  rcases le_total p (v i) with hpv | hvp
  · simp only [min_eq_left hpv, le_refl, ↓reduceIte] at hy
    have hpv' : (p : ℝ) ≤ v i := by exact_mod_cast hpv
    split_ifs at hy with hpy
    · have hpy' : (p : ℝ) ≤ y := by exact_mod_cast hpy
      rcases hy with h | ⟨h, h'⟩
      · linarith
      · have : (y : ℝ) = p := by linarith
        have hyp : y = p := by exact_mod_cast this
        subst hyp
        simp at h'
    · have hpy' : (y : ℝ) < p := by exact_mod_cast lt_of_not_ge hpy
      rcases hy with h | ⟨h, h'⟩
      · linarith
      · have : (p : ℝ) = v i := by linarith
        rw [this, sub_self, abs_zero] at h'
        rcases h' with h' | ⟨h', h''⟩
        · exact absurd h' (not_lt.2 (abs_nonneg _))
        · have : (y : ℝ) = v i := by linarith [abs_eq_zero.1 h']
          linarith
  · rw [min_eq_right hvp] at hy
    by_cases hp : p ≤ v i
    · have : p = v i := le_antisymm hp hvp
      rw [this] at hy hp
      split_ifs at hy with hpy
      · have hpy' : (v i : ℝ) ≤ y := by exact_mod_cast hpy
        simp only [sub_self, abs_zero] at hy
        rcases hy with h | ⟨h, h'⟩
        · linarith
        · rcases h' with h' | ⟨h', h''⟩
          · exact absurd h' (not_lt.2 (abs_nonneg _))
          · have : (y : ℝ) = v i := by linarith [abs_eq_zero.1 h']
            exact absurd (show (y : ℝ) < v i by exact_mod_cast h'') (by linarith)
      · simp only [sub_self, abs_zero] at hy
        rcases hy with h | ⟨h, h'⟩
        · exact lt_irrefl _ h
        · rcases h' with h' | ⟨h', h''⟩
          · exact absurd h' (not_lt.2 (abs_nonneg _))
          · have : (y : ℝ) = v i := by linarith [abs_eq_zero.1 h']
            exact absurd (show (y : ℝ) < v i by exact_mod_cast h'') (by linarith)
    · simp only [hp, ↓reduceIte] at hy
      simp only [sub_self, abs_zero] at hy
      split_ifs at hy with hpy
      · have : (v i : ℝ) < y := by exact_mod_cast (lt_of_not_ge hp).trans_le hpy
        rcases hy with h | ⟨h, h'⟩
        · linarith
        · linarith
      · rcases hy with h | ⟨h, h'⟩
        · exact lt_irrefl _ h
        · rcases h' with h' | ⟨h', h''⟩
          · exact absurd h' (not_lt.2 (abs_nonneg _))
          · have : (y : ℝ) = v i := by linarith [abs_eq_zero.1 h']
            exact absurd (show (y : ℝ) < v i by exact_mod_cast h'') (by linarith)

/-- Tie-broken best responses exist in the cost-sharing game. -/
theorem hasBR (v : ι → ℝ≥0) : (C.game v).HasBR :=
  fun i b => ⟨C.bestBid v i b, isBR_bestBid v i b⟩

lemma elimStep_game {v : ι → ℝ≥0} {H H' : Subgame (fun _ : ι => ℝ≥0)} (hsub : ∀ i, H' i ⊆ H i)
    (hmap : ∀ i (s : ι → ℝ≥0), (∀ j, j ≠ i → s j ∈ H j) → C.bestBid v i s ∈ H' i) :
    (C.game v).ElimStep H H' :=
  elimStep_of_isBR (fun i _ _ h => closer_total (v i) h) (fun i s => C.bestBid v i s)
    (fun i s => isBR_bestBid v i s) hsub hmap

/-! ### The outcome and the elimination sequence of Theorem 3.3 -/

variable (C) in
/-- The outcome `s*`: users of `R_v = serviced v` bid their cost share `c j R_v`, the others bid
their value `vᵢ`. -/
noncomputable def outcome (v : ι → ℝ≥0) (i : ι) : ℝ≥0 :=
  if i ∈ C.serviced v then C.c i (C.serviced v) else v i

lemma c_le_of_mem {v : ι → ℝ≥0} {i : ι} (h : i ∈ C.serviced v) : C.c i (C.serviced v) ≤ v i :=
  feasible_serviced v i h

lemma bestBid_of_not_mem {v s : ι → ℝ≥0} {i : ι} (hs : ∀ j, j ≠ i → s j ≤ v j)
    (hi : i ∉ C.serviced v) : C.bestBid v i s = v i := by
  have h1 : v i < C.price i v := lt_of_not_ge (mt mem_serviced_iff_price.2 hi)
  exact min_eq_right (h1.trans_le (price_anti hs)).le

lemma c_le_price_of_mem {v s : ι → ℝ≥0} {i : ι} (hs : ∀ j, j ≠ i → s j ≤ v j)
    (hi : i ∈ C.serviced v) : C.c i (C.serviced v) ≤ C.price i s := by
  rw [← price_eq_of_mem hi]; exact price_anti hs

lemma price_eq_of_mem' {v s : ι → ℝ≥0} {i : ι} (hs : ∀ j, j ≠ i → s j ≤ v j)
    (hge : ∀ j ∈ C.serviced v, j ≠ i → C.c j (C.serviced v) ≤ s j) (hi : i ∈ C.serviced v) :
    C.price i s = C.c i (C.serviced v) :=
  le_antisymm (C.cross_mono hi (subset_coalition hge)) (c_le_price_of_mem hs hi)

variable (C) in
/-- The elimination sequence of the proof of Theorem 3.3: (1) remove bids above `vᵢ`; (2) users
outside `R_v` keep only `vᵢ`, users `j ∈ R_v` remove bids below `c_j(R_v)`; (3) users `j ∈ R_v`
remove bids above `c_j(R_v)`. -/
noncomputable def elimSeq (v : ι → ℝ≥0) : ℕ → Subgame (fun _ : ι => ℝ≥0)
  | 0 => TieBreakGame.full
  | 1 => fun i => Iic (v i)
  | 2 => fun i => if i ∈ C.serviced v then Icc (C.c i (C.serviced v)) (v i) else {v i}
  | _ => fun i => {C.outcome v i}

lemma le_of_mem_elimSeq_two {v : ι → ℝ≥0} {j : ι} {x : ℝ≥0} (h : x ∈ C.elimSeq v 2 j) :
    x ≤ v j := by
  by_cases hj : j ∈ C.serviced v
  · simp only [elimSeq, hj, ↓reduceIte, mem_Icc] at h; exact h.2
  · simp only [elimSeq, hj, ↓reduceIte, mem_singleton_iff] at h; exact h.le

lemma ge_of_mem_elimSeq_two {v : ι → ℝ≥0} {j : ι} {x : ℝ≥0} (hj : j ∈ C.serviced v)
    (h : x ∈ C.elimSeq v 2 j) : C.c j (C.serviced v) ≤ x := by
  simp only [elimSeq, hj, ↓reduceIte, mem_Icc] at h; exact h.1

lemma outcome_mem_elimSeq_two (v : ι → ℝ≥0) (i : ι) : C.outcome v i ∈ C.elimSeq v 2 i := by
  by_cases hi : i ∈ C.serviced v
  · simp only [elimSeq, outcome, hi, ↓reduceIte, mem_Icc]; exact ⟨le_rfl, c_le_of_mem hi⟩
  · simp [elimSeq, outcome, hi]

/-- Against bids of the others in the subgame after step 2, the best response is `s*ᵢ`. -/
lemma bestBid_eq_outcome {v s : ι → ℝ≥0} {i : ι} (hs : ∀ j, j ≠ i → s j ∈ C.elimSeq v 2 j) :
    C.bestBid v i s = C.outcome v i := by
  have hle : ∀ j, j ≠ i → s j ≤ v j := fun j hj => le_of_mem_elimSeq_two (hs j hj)
  by_cases hi : i ∈ C.serviced v
  · rw [bestBid, price_eq_of_mem' hle (fun j hj hji => ge_of_mem_elimSeq_two hj (hs j hji)) hi,
      min_eq_left (c_le_of_mem hi)]
    simp [outcome, hi]
  · rw [bestBid_of_not_mem hle hi]
    simp [outcome, hi]

lemma v_mem_elimSeq_two (v : ι → ℝ≥0) (j : ι) : v j ∈ C.elimSeq v 2 j := by
  by_cases hj : j ∈ C.serviced v
  · simp only [elimSeq, hj, ↓reduceIte, mem_Icc]; exact ⟨c_le_of_mem hj, le_rfl⟩
  · simp [elimSeq, hj]

lemma elimStep_zero (v : ι → ℝ≥0) : (C.game v).ElimStep (C.elimSeq v 0) (C.elimSeq v 1) :=
  elimStep_game (fun _ => subset_univ _) fun _ _ _ => by
    simp only [elimSeq, mem_Iic]; exact min_le_right _ _

lemma elimStep_one (v : ι → ℝ≥0) : (C.game v).ElimStep (C.elimSeq v 1) (C.elimSeq v 2) := by
  refine elimStep_game (fun i x hx => le_of_mem_elimSeq_two hx) fun i s hs => ?_
  have hle : ∀ j, j ≠ i → s j ≤ v j := fun j hj => hs j hj
  by_cases hi : i ∈ C.serviced v
  · simp only [elimSeq, hi, ↓reduceIte, mem_Icc]
    exact ⟨le_min (c_le_price_of_mem hle hi) (c_le_of_mem hi), min_le_right _ _⟩
  · simp only [elimSeq, hi, ↓reduceIte, mem_singleton_iff]
    exact bestBid_of_not_mem hle hi

lemma elimStep_two (v : ι → ℝ≥0) : (C.game v).ElimStep (C.elimSeq v 2) (C.elimSeq v 3) := by
  refine elimStep_game (fun i x hx => ?_) fun i s hs => ?_
  · simp only [elimSeq, mem_singleton_iff] at hx
    exact hx ▸ outcome_mem_elimSeq_two v i
  · exact bestBid_eq_outcome hs

/-- The NBR elimination of the proof of Theorem 3.3 ends at `s*` after 3 steps. -/
theorem elimSeq_solves (v : ι → ℝ≥0) : (C.game v).Solves (C.elimSeq v) 3 (C.outcome v) := by
  refine ⟨⟨rfl, fun k hk => ?_⟩, rfl⟩
  interval_cases k
  · exact elimStep_zero v
  · exact elimStep_one v
  · exact elimStep_two v

lemma outcome_le (v : ι → ℝ≥0) (i : ι) : C.outcome v i ≤ v i :=
  le_of_mem_elimSeq_two (outcome_mem_elimSeq_two v i)

/-- The serviced set of the outcome is `R_v`, the serviced set for truthful bids. -/
theorem serviced_outcome (v : ι → ℝ≥0) : C.serviced (C.outcome v) = C.serviced v := by
  refine (serviced_mono (outcome_le v)).antisymm (subset_serviced fun j hj => ?_)
  simp [outcome, hj]

/-! ### Clear outcome -/

lemma utility_le (v : ι → ℝ≥0) (i : ι) (t : ι → ℝ≥0) :
    C.utility v i t ≤ max 0 ((v i : ℝ) - C.price i t) := by
  unfold utility
  split_ifs with h
  · have : (C.price i t : ℝ) ≤ t i := by exact_mod_cast mem_serviced_iff_price.1 h
    exact le_max_of_le_right (by linarith)
  · exact le_max_left _ _

variable (C) in
/-- The player-specific elimination order for player `i`: first the others remove their bids
above their values, then continue as in `elimSeq`. -/
noncomputable def clearSeq (v : ι → ℝ≥0) (i : ι) (k : ℕ) : Subgame (fun _ : ι => ℝ≥0) :=
  if k = 1 then fun j => if j = i then univ else Iic (v j) else C.elimSeq v (k - 1)

/-- After the others have removed their bids above their values, `s*` is globally optimal for
`i`: `i` can never get more than `max 0 (vᵢ - c_i(R_i))`. -/
theorem clearWitness (v : ι → ℝ≥0) (i : ι) :
    (C.game v).ClearWitness (C.outcome v) i (C.clearSeq v i) 4 1 := by
  refine ⟨⟨⟨rfl, fun k hk => ?_⟩, rfl⟩, by omega, by simp [clearSeq], ?_⟩
  · have e : ∀ k, k ≠ 1 → C.clearSeq v i k = C.elimSeq v (k - 1) := fun k hk => by
      simp [clearSeq, hk]
    have e1 : C.clearSeq v i 1 = fun j => if j = i then univ else Iic (v j) := by
      simp [clearSeq]
    interval_cases k
    · rw [e 0 (by decide), e1]
      refine elimStep_game (fun _ => subset_univ _) fun j s _ => ?_
      by_cases hj : j = i
      · simp [hj]
      · simp only [hj, ↓reduceIte, mem_Iic]; exact min_le_right _ _
    · rw [e 2 (by decide), e1]
      refine elimStep_game (fun j x hx => ?_) fun j s _ => by
        simp only [elimSeq, mem_Iic]; exact min_le_right _ _
      by_cases hj : j = i
      · simp [hj]
      · simpa [hj, elimSeq] using hx
    · rw [e 2 (by decide), e 3 (by decide)]; exact elimStep_one v
    · rw [e 3 (by decide), e 4 (by decide)]; exact elimStep_two v
  · intro t ht
    have hle : ∀ j, j ≠ i → t j ≤ v j := fun j hj => by
      have := ht j
      simp only [clearSeq, ↓reduceIte, hj] at this
      exact this
    refine (utility_le v i t).trans ?_
    by_cases hi : i ∈ C.serviced v
    · have h1 : (C.c i (C.serviced v) : ℝ) ≤ C.price i t := by
        exact_mod_cast c_le_price_of_mem hle hi
      have h2 : (C.c i (C.serviced v) : ℝ) ≤ v i := by exact_mod_cast c_le_of_mem hi
      have : C.utility v i (C.outcome v) = (v i : ℝ) - C.c i (C.serviced v) := by
        simp [utility, serviced_outcome, hi, outcome]
      show _ ≤ C.utility v i (C.outcome v)
      rw [this]
      exact max_le (by linarith) (by linarith)
    · have h1 : (v i : ℝ) < C.price i t := by
        exact_mod_cast (lt_of_not_ge (mt mem_serviced_iff_price.2 hi)).trans_le (price_anti hle)
      have : C.utility v i (C.outcome v) = 0 := by
        simp [utility, serviced_outcome, hi]
      show _ ≤ C.utility v i (C.outcome v)
      rw [this]
      exact max_le le_rfl (by linarith)

/-- `s*` is a clear outcome (Definition 2.6). -/
theorem hasClearOutcome (v : ι → ℝ≥0) : (C.game v).HasClearOutcome (C.outcome v) :=
  ⟨⟨_, _, elimSeq_solves v⟩, fun i => ⟨_, _, _, clearWitness v i⟩⟩

/-! ### `e_G ≤ n` -/

lemma bestBid_self (v : ι → ℝ≥0) (i : ι) : C.bestBid v i v = C.outcome v i :=
  bestBid_eq_outcome fun j _ => v_mem_elimSeq_two v j

/-- `e_G ≤ 3`. -/
theorem elimParam_le_three (v : ι → ℝ≥0) : (C.game v).elimParam ≤ 3 :=
  elimParam_le (elimSeq_solves v)

/-- With two users `i ≠ j`, `j` belongs to the coalition of `i` iff it bids at least
`c_j(univ)`. -/
lemma mem_coalition_of_two {i j : ι} (hj : j ≠ i) (hother : ∀ k, k ≠ i → k = j)
    {b : ι → ℝ≥0} : j ∈ C.coalition i b ↔ C.c j Finset.univ ≤ b j := by
  constructor
  · intro h
    exact (C.cross_mono h (Finset.subset_univ _)).trans (feasibleExcept_coalition i b j h hj)
  · intro h
    refine subset_coalition (S := Finset.univ) (fun k _ hk => ?_) (Finset.mem_univ j)
    rw [hother k hk]; exact h

/-- `e_G ≤ n` for every number `n` of users (the paper's 3-step elimination covers `n ≥ 3`; one
step suffices for `n = 1` and two steps, keeping only best responses, for `n = 2`). -/
theorem elimParam_le_card (v : ι → ℝ≥0) : (C.game v).elimParam ≤ Fintype.card ι := by
  obtain h | h | h | h : Fintype.card ι = 0 ∨ Fintype.card ι = 1 ∨ Fintype.card ι = 2 ∨
      3 ≤ Fintype.card ι := by omega
  · rw [h]
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 h
    exact elimParam_le (E := fun _ => TieBreakGame.full) (s := C.outcome v)
      ⟨⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩, funext fun i => isEmptyElim i⟩
  · rw [h]
    have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 h.le
    refine elimParam_le (E := fun k => if k = 0 then TieBreakGame.full else
      fun i => {C.outcome v i}) (s := C.outcome v) ⟨⟨rfl, fun k hk => ?_⟩, rfl⟩
    obtain rfl : k = 0 := by omega
    refine elimStep_game (fun _ => subset_univ _) fun i s _ => ?_
    show C.bestBid v i s = C.outcome v i
    rw [← bestBid_self v i, bestBid, bestBid,
      price_congr fun j hj => absurd (Subsingleton.elim j i) hj]
  · rw [h]
    refine elimParam_le (E := fun k => if k = 0 then TieBreakGame.full else
      if k = 1 then fun i => range (C.bestBid v i) else fun i => {C.outcome v i})
      (s := C.outcome v) ⟨⟨rfl, fun k hk => ?_⟩, rfl⟩
    interval_cases k
    · exact elimStep_game (fun _ => subset_univ _) fun i s _ => ⟨s, rfl⟩
    · simp only [one_ne_zero, ↓reduceIte]
      refine elimStep_game (fun i x hx => ?_) fun i s hs => ?_
      · rw [mem_singleton_iff.1 hx]; exact ⟨v, bestBid_self v i⟩
      · obtain ⟨j, hj, huniq⟩ := (Nat.card_eq_two_iff' i).1 (by rw [Nat.card_eq_fintype_card, h])
        have hother : ∀ k, k ≠ i → k = j := fun k hk => huniq k hk
        show C.bestBid v i s = C.outcome v i
        have hco : C.coalition i s = C.coalition i v := by
          ext k
          by_cases hki : k = i
          · subst hki; simp only [self_mem_coalition]
          obtain rfl := hother k hki
          rw [mem_coalition_of_two hki hother, mem_coalition_of_two hki hother]
          obtain ⟨t, ht⟩ := hs k hki
          rw [← ht, bestBid, le_min_iff]
          exact ⟨fun h' => h'.2, fun h' => ⟨c_univ_le_price k t, h'⟩⟩
        rw [← bestBid_self v i, bestBid, bestBid, price, price, hco]
  · exact (elimParam_le_three v).trans h

/-! ### Moulin's mechanism -/

variable (C) in
/-- One round of Moulin's mechanism: drop the users whose value is below their cost share. -/
noncomputable def moulinStep (v : ι → ℝ≥0) (S : Finset ι) : Finset ι :=
  S.filter fun i => C.c i S ≤ v i

variable (C) in
/-- Moulin's mechanism: starting from all users, repeatedly drop the users whose value is below
their cost share (`n` rounds suffice: `moulinStep_moulinSet`). It services `moulinSet` and charges
`c i (moulinSet)`. -/
noncomputable def moulinSet (v : ι → ℝ≥0) : Finset ι :=
  (C.moulinStep v)^[Fintype.card ι] Finset.univ

lemma serviced_subset_iterate (v : ι → ℝ≥0) (k : ℕ) :
    C.serviced v ⊆ (C.moulinStep v)^[k] Finset.univ := by
  induction k with
  | zero => exact Finset.subset_univ _
  | succ k ih =>
    rw [iterate_succ_apply']
    intro i hi
    exact Finset.mem_filter.2 ⟨ih hi, (C.cross_mono hi ih).trans (c_le_of_mem hi)⟩

/-- After `n` rounds Moulin's mechanism has stabilized. -/
lemma moulinStep_moulinSet (v : ι → ℝ≥0) : C.moulinStep v (C.moulinSet v) = C.moulinSet v := by
  set f := C.moulinStep v
  have hsub : ∀ S, f S ⊆ S := fun S => Finset.filter_subset _ _
  obtain ⟨k, hk, hfix⟩ : ∃ k ≤ Fintype.card ι, f (f^[k] Finset.univ) = f^[k] Finset.univ := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have key : ∀ k ≤ Fintype.card ι + 1, (f^[k] Finset.univ).card + k ≤ Fintype.card ι := by
      intro k hk
      induction k with
      | zero => simp [Finset.card_univ]
      | succ k ih =>
        have h1 := ih (by omega)
        rw [iterate_succ_apply']
        have : (f (f^[k] Finset.univ)).card < (f^[k] Finset.univ).card :=
          Finset.card_lt_card ((hsub _).ssubset_of_ne (hne k (by omega)))
        omega
    have := key _ le_rfl
    omega
  have hfix' : IsFixedPt f (f^[k] Finset.univ) := hfix
  have : C.moulinSet v = f^[k] Finset.univ := by
    rw [moulinSet, show Fintype.card ι = (Fintype.card ι - k) + k by omega, iterate_add_apply]
    exact (hfix'.iterate _).eq
  rw [this]; exact hfix

/-- **Moulin's mechanism selects `R_v`**, the serviced set for truthful bids. -/
theorem moulinSet_eq (v : ι → ℝ≥0) : C.moulinSet v = C.serviced v := by
  refine le_antisymm (subset_serviced fun i hi => ?_) (serviced_subset_iterate v _)
  rw [← moulinStep_moulinSet v] at hi
  exact (Finset.mem_filter.1 hi).2

/-! ### The mechanism of Theorem 3.4 -/

open Classical in
variable (C) in
/-- The bid that the mechanism of Theorem 3.4 prescribes to user `i` facing the most recent bids
`b`: the minimal bid `x ≤ vᵢ` with which `i` is serviced, or `vᵢ` if there is none. -/
noncomputable def mechBid (v : ι → ℝ≥0) (i : ι) (b : ι → ℝ≥0) : ℝ≥0 :=
  if ({x | x ≤ v i ∧ i ∈ C.serviced (update b i x)} : Set ℝ≥0).Nonempty then
    sInf {x | x ≤ v i ∧ i ∈ C.serviced (update b i x)}
  else v i

lemma mechBid_eq_bestBid (v : ι → ℝ≥0) (i : ι) (b : ι → ℝ≥0) :
    C.mechBid v i b = C.bestBid v i b := by
  have hT : {x | x ≤ v i ∧ i ∈ C.serviced (update b i x)} = Icc (C.price i b) (v i) := by
    ext x
    simp only [mem_ofPred_eq, mem_serviced_iff_price, price_update, update_self, mem_Icc]
    exact and_comm
  rw [mechBid, hT, bestBid]
  by_cases hp : C.price i b ≤ v i
  · simp only [nonempty_Icc.2 hp, ↓reduceIte]
    rw [csInf_Icc hp, min_eq_left hp]
  · simp only [nonempty_Icc, hp, ↓reduceIte]
    rw [min_eq_right (le_of_not_ge hp)]

/-- **Theorem 3.4 (bid rule).** The bid prescribed by the mechanism is a tie-broken best
response, i.e. the mechanism is a best-response mechanism for the 1st-price cost-sharing game. -/
theorem isBR_mechBid (v : ι → ℝ≥0) (i : ι) (b : ι → ℝ≥0) :
    (C.game v).IsBR i (C.mechBid v i b) b := by
  rw [mechBid_eq_bestBid]; exact isBR_bestBid v i b

/-! ### Theorem 3.3 -/

lemma utility_outcome_nonneg (v : ι → ℝ≥0) (j : ι) : 0 ≤ C.utility v j (C.outcome v) := by
  unfold utility
  split_ifs with h
  · rw [serviced_outcome] at h
    have : (C.outcome v j : ℝ) ≤ v j := by exact_mod_cast outcome_le v j
    linarith
  · exact le_rfl

/-- **Theorem 3.3** of [NSVZ] (with the repaired tie-breaking rule `game`). For every 1st-price
cost-sharing game `G` with cross-monotonic cost shares:
* `G` is NBR-solvable, by the explicit 3-step elimination `elimSeq`, with outcome `s*`;
* `s*` is the unique outcome of every NBR elimination, and it is a pure Nash equilibrium;
* it induces the outcome of Moulin's mechanism: its serviced set is `moulinSet v` and every
  serviced user `j` pays its cost share `c j (moulinSet v)`, which is at most `v j`, so every user
  gets nonnegative utility (reasonable cost shares);
* `s*` is a clear outcome (Definition 2.6);
* `e_G ≤ n` (and `e_G ≤ 3`). -/
theorem theorem_3_3 (v : ι → ℝ≥0) :
    (C.game v).Solves (C.elimSeq v) 3 (C.outcome v) ∧
    (∀ E r s, (C.game v).Solves E r s → s = C.outcome v) ∧
    (C.game v).IsNash (C.outcome v) ∧
    C.serviced (C.outcome v) = C.moulinSet v ∧
    (∀ j ∈ C.moulinSet v, C.outcome v j = C.c j (C.moulinSet v) ∧ C.c j (C.moulinSet v) ≤ v j) ∧
    (∀ j, 0 ≤ C.utility v j (C.outcome v)) ∧
    (C.game v).HasClearOutcome (C.outcome v) ∧
    (C.game v).elimParam ≤ Fintype.card ι ∧ (C.game v).elimParam ≤ 3 := by
  refine ⟨elimSeq_solves v, fun E r s h => (elimSeq_solves v).unique (hasBR v) h |>.symm,
    (elimSeq_solves v).isNash (hasBR v), by rw [serviced_outcome, moulinSet_eq], ?_,
    utility_outcome_nonneg v, hasClearOutcome v, elimParam_le_card v, elimParam_le_three v⟩
  intro j hj
  rw [moulinSet_eq] at hj ⊢
  exact ⟨by simp [outcome, hj], c_le_of_mem hj⟩

/-- The outcome `s*` is a fixed point of the mechanism's bid rule (Theorem 3.4). -/
theorem mechBid_outcome (v : ι → ℝ≥0) (i : ι) : C.mechBid v i (C.outcome v) = C.outcome v i := by
  rw [mechBid_eq_bestBid]
  exact bestBid_eq_outcome fun j _ => outcome_mem_elimSeq_two v j

end CostSharingRule

/-! ### Non-vacuity: equal split of a fixed cost is cross-monotonic -/

/-- Equal split of a fixed cost `K`: `c i S = K / |S|`. -/
noncomputable def equalSplit (ι : Type*) (K : ℝ≥0) : CostSharingRule ι where
  c _ S := K / S.card
  cross_mono i S T hi hST := by
    have : (0 : ℝ≥0) < S.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hi⟩
    gcongr

end Podc.BestResponseMechanisms.CostSharing
