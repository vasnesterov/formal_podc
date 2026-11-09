/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

-- CSLib candidate: Cslib/Foundations/GameTheory/NeverBestResponse.lean

/-!
# Never-best-response elimination under tie-breaking

Normal-form games `G` with players `i : ι`, strategy types `S i` (arbitrary, possibly infinite),
utilities in a linear order `R`, together with a *tie-breaking rule* `G.prec i` on `S i`
(`G.prec i x y` reads "`x ≺ᵢ y`": among equally good best responses, `y` is preferred).
This is the setting of Nisan, Schapira, Valiant, Zohar, *Best-Response Mechanisms* (ICS 2011,
PODC 2011 brief announcement).

A *subgame* is a product of strategy sets `H : ∀ i, Set (S i)`. A strategy `y ∈ H i` is a
*never-best-response* (NBR) in `H` if against every `s₋ᵢ ∈ H₋ᵢ` some `x ∈ H i` *beats* it: `x` gives
strictly more utility, or equal utility and `y ≺ᵢ x`. A game is *NBR-solvable* if a finite sequence
of NBR-elimination steps (each removing, simultaneously for any players, strategies that are NBR in
the current subgame) leads to a single profile.

## Main definitions

* `TieBreakGame ι S R`: utilities and tie-breaking relations.
* `Beats`, `IsNBR`, `IsBR` (tie-broken best response over the *full* strategy set), `IsBRFixed`,
  `IsNash`.
* `ElimStep`, `IsElimSeq`, `Solves`, `NBRSolvable`, `elimParam` (the shortest-elimination
  parameter `e_G`), `GloballyOptimal`, `ClearWitness`, `HasClearOutcome`.

## Main statements

* `IsElimSeq.mem_of_isBR`: a tie-broken best response (over the full strategy set) to a profile
  of a subgame `E k` of an elimination sequence survives into `E (k + 1)`. This is the engine of
  all convergence arguments.
* `IsElimSeq.mem_of_isBRFixed`, `Solves.eq_of_isBRFixed`: tie-broken best-response fixed points
  survive every elimination sequence.
* `Solves.isBRFixed`, `Solves.isNash`, `Solves.unique`: if tie-broken best responses exist
  (`HasBR`, automatic for finite games with strict total tie-breaking orders, `hasBR_of_finite`),
  the outcome of NBR elimination is a pure Nash equilibrium and does not depend on the
  elimination order.
-/

open Set Function

namespace Cslib.GameTheory

/-- A normal-form game with utilities `utility i s : R` and tie-breaking relations
`prec i : S i → S i → Prop` (`prec i x y`: "`x ≺ᵢ y`", i.e. `y` is preferred among ties). -/
structure TieBreakGame (ι : Type*) (S : ι → Type*) (R : Type*) where
  /-- The utility of player `i` at the strategy profile `s`. -/
  utility : ι → (∀ i, S i) → R
  /-- The tie-breaking order `≺ᵢ` of player `i`: `prec i x y` means that `y` is preferred. -/
  prec : ∀ i, S i → S i → Prop

/-- A subgame: a product of (sub)sets of strategies. -/
abbrev Subgame {ι : Type*} (S : ι → Type*) := ∀ i, Set (S i)

namespace TieBreakGame

variable {ι : Type*} {S : ι → Type*} {R : Type*} [DecidableEq ι] [LinearOrder R]
variable (G : TieBreakGame ι S R)

/-- The full game: every strategy is available. -/
def full : Subgame S := fun _ => univ

/-- `G.Beats i x y s`: against the strategies `s₋ᵢ` of the others, player `i` strictly prefers
`x` to `y`, or is indifferent and `y ≺ᵢ x` (Definition 2.2's condition). -/
def Beats (i : ι) (x y : S i) (s : ∀ j, S j) : Prop :=
  G.utility i (update s i y) < G.utility i (update s i x) ∨
    (G.utility i (update s i y) = G.utility i (update s i x) ∧ G.prec i y x)

/-- **Definition 2.2** (never-best-response under tie-breaking), relative to a subgame `H`:
`y` is NBR in `H` if for every `s₋ᵢ ∈ H₋ᵢ` there is `x ∈ Hᵢ` beating it. -/
def IsNBR (H : Subgame S) (i : ι) (y : S i) : Prop :=
  ∀ s : ∀ j, S j, (∀ j, j ≠ i → s j ∈ H j) → ∃ x ∈ H i, G.Beats i x y s

/-- `x` is a tie-broken best response of `i` to `s₋ᵢ` (over the full strategy set `S i`): no
strategy beats it. This is what a player of a best-response mechanism announces. -/
def IsBR (i : ι) (x : S i) (s : ∀ j, S j) : Prop :=
  ∀ y : S i, ¬ G.Beats i y x s

/-- Tie-broken best responses always exist. -/
def HasBR : Prop :=
  ∀ (i : ι) (s : ∀ j, S j), ∃ x : S i, G.IsBR i x s

/-- `s` is a fixed point of tie-broken best response: every player's strategy is its tie-broken
best response to the others. -/
def IsBRFixed (s : ∀ j, S j) : Prop :=
  ∀ i, G.IsBR i (s i) s

/-- A pure Nash equilibrium (ignoring the tie-breaking rule). -/
def IsNash (s : ∀ j, S j) : Prop :=
  ∀ (i : ι) (x : S i), G.utility i (update s i x) ≤ G.utility i s

/-- One step of NBR elimination from `H` to `H'`: `H' ⊆ H`, and every removed strategy is NBR
in `H` ("removal of sets of NBR strategies", for any number of players at once). -/
def ElimStep (H H' : Subgame S) : Prop :=
  (∀ i, H' i ⊆ H i) ∧ ∀ i (y : S i), y ∈ H i → y ∉ H' i → G.IsNBR H i y

/-- `E 0, …, E r` is a sequence of NBR-elimination steps starting at the full game. -/
def IsElimSeq (E : ℕ → Subgame S) (r : ℕ) : Prop :=
  E 0 = full ∧ ∀ k < r, G.ElimStep (E k) (E (k + 1))

/-- **Definition 2.3/2.4**: the elimination sequence `E 0, …, E r` ends with the single profile
`s` (every player has a single strategy left). -/
def Solves (E : ℕ → Subgame S) (r : ℕ) (s : ∀ i, S i) : Prop :=
  G.IsElimSeq E r ∧ E r = fun i => {s i}

/-- **Definition 2.3** (NBR-solvable under tie-breaking). -/
def NBRSolvable : Prop :=
  ∃ (E : ℕ → Subgame S) (r : ℕ) (s : ∀ i, S i), G.Solves E r s

/-- `s` is an outcome of NBR elimination ("the unique PNE under tie-breaking"). -/
def IsOutcome (s : ∀ i, S i) : Prop :=
  ∃ (E : ℕ → Subgame S) (r : ℕ), G.Solves E r s

/-- **Definition 2.4** (shortest-elimination parameter `e_G`). -/
noncomputable def elimParam : ℕ :=
  sInf {r | ∃ (E : ℕ → Subgame S) (s : ∀ i, S i), G.Solves E r s}

/-- **Definition 2.5**, relative to a subgame `H`: `s` is globally optimal for `i` in `H`. -/
def GloballyOptimal (H : Subgame S) (i : ι) (s : ∀ j, S j) : Prop :=
  ∀ t : ∀ j, S j, (∀ j, t j ∈ H j) → G.utility i t ≤ G.utility i s

/-- A witness for Definition 2.6 for player `i`: an elimination order `E 0, …, E r` ending at `s`
and an index `k` before which no strategy of `i` has been eliminated (`E k i = univ`) such that
`s` is globally optimal for `i` in `E k`. (Taking for `k` the first step that eliminates a
strategy of `i` gives the paper's formulation; see `ClearWitness.of_le`.) -/
def ClearWitness (s : ∀ i, S i) (i : ι) (E : ℕ → Subgame S) (r k : ℕ) : Prop :=
  G.Solves E r s ∧ k ≤ r ∧ E k i = univ ∧ G.GloballyOptimal (E k) i s

/-- **Definition 2.6** (clear outcome): `s` is an outcome of NBR elimination, and for every
player `i` some elimination order makes `s` globally optimal for `i` at the first step that
eliminates a strategy of `i`. -/
def HasClearOutcome (s : ∀ i, S i) : Prop :=
  G.IsOutcome s ∧ ∀ i, ∃ (E : ℕ → Subgame S) (r k : ℕ), G.ClearWitness s i E r k

/-! ### Basic lemmas -/

variable {G}

lemma IsBR.not_isNBR_aux {i : ι} {x : S i} {s : ∀ j, S j} (h : G.IsBR i x s) {H : Subgame S}
    (hs : ∀ j, j ≠ i → s j ∈ H j) : ¬ G.IsNBR H i x := by
  intro hn
  obtain ⟨y, -, hy⟩ := hn s hs
  exact h y hy

lemma IsBR.congr {i : ι} {x : S i} {s t : ∀ j, S j} (h : G.IsBR i x s)
    (hst : ∀ j, j ≠ i → s j = t j) : G.IsBR i x t := by
  have : ∀ y : S i, update s i y = update t i y := by
    intro y; funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, hst j hj]
  intro y hy
  apply h y
  simpa only [Beats, this] using hy

lemma Beats.congr {i : ι} {x y : S i} {s t : ∀ j, S j} (h : G.Beats i x y s)
    (hst : ∀ j, j ≠ i → s j = t j) : G.Beats i x y t := by
  have : ∀ y : S i, update s i y = update t i y := by
    intro y; funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, hst j hj]
  simpa only [Beats, this] using h

lemma IsElimSeq.zero {E : ℕ → Subgame S} {r : ℕ} (h : G.IsElimSeq E r) (i : ι) (x : S i) :
    x ∈ E 0 i := by
  rw [h.1]; trivial

/-- Elimination sequences are decreasing. -/
lemma IsElimSeq.antitone {E : ℕ → Subgame S} {r : ℕ} (h : G.IsElimSeq E r) {k m : ℕ}
    (hkm : k ≤ m) (hm : m ≤ r) (i : ι) : E m i ⊆ E k i := by
  induction m, hkm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hkm ih => exact ((h.2 m (by omega)).1 i).trans (ih (by omega))

lemma IsElimSeq.mono {E : ℕ → Subgame S} {r r' : ℕ} (h : G.IsElimSeq E r) (hr : r' ≤ r) :
    G.IsElimSeq E r' :=
  ⟨h.1, fun k hk => h.2 k (by omega)⟩

/-- **Survival of best responses.** If `x` is a tie-broken best response of `j` (over all of
`S j`) to a profile whose other components lie in `E k`, then `x` lies in `E m j` for every
`m ≤ k + 1` (`m ≤ r`). -/
lemma IsElimSeq.mem_of_isBR {E : ℕ → Subgame S} {r : ℕ} (h : G.IsElimSeq E r) {j : ι}
    {x : S j} {v : ∀ l, S l} (hx : G.IsBR j x v) {k : ℕ} (hk : k ≤ r)
    (hv : ∀ l, l ≠ j → v l ∈ E k l) {m : ℕ} (hm : m ≤ k + 1) (hmr : m ≤ r) : x ∈ E m j := by
  induction m with
  | zero => exact h.zero j x
  | succ m ih =>
    have hxm := ih (by omega) (by omega)
    by_contra hn
    have hnbr := (h.2 m (by omega)).2 j x hxm hn
    exact hx.not_isNBR_aux (fun l hl => h.antitone (show m ≤ k by omega) hk l (hv l hl)) hnbr

/-- Tie-broken best-response fixed points survive every elimination sequence. -/
lemma IsElimSeq.mem_of_isBRFixed {E : ℕ → Subgame S} {r : ℕ} (h : G.IsElimSeq E r)
    {s : ∀ i, S i} (hs : G.IsBRFixed s) {k : ℕ} (hk : k ≤ r) (i : ι) : s i ∈ E k i := by
  induction k generalizing i with
  | zero => exact h.zero i _
  | succ k ih =>
    exact h.mem_of_isBR (hs i) (by omega) (fun l _ => ih (by omega) l) le_rfl hk

/-- A tie-broken best-response fixed point is the outcome of every NBR elimination. -/
lemma Solves.eq_of_isBRFixed {E : ℕ → Subgame S} {r : ℕ} {s t : ∀ i, S i}
    (h : G.Solves E r s) (ht : G.IsBRFixed t) : t = s := by
  funext i
  have := h.1.mem_of_isBRFixed ht le_rfl i
  rw [h.2] at this
  exact this

lemma Solves.mem {E : ℕ → Subgame S} {r : ℕ} {s : ∀ i, S i} (h : G.Solves E r s) {k : ℕ}
    (hk : k ≤ r) (i : ι) : s i ∈ E k i := by
  have : s i ∈ E r i := by rw [h.2]; rfl
  exact h.1.antitone hk le_rfl i this

/-- If tie-broken best responses exist, the outcome of NBR elimination is a tie-broken
best-response fixed point. -/
lemma Solves.isBRFixed (hBR : G.HasBR) {E : ℕ → Subgame S} {r : ℕ} {s : ∀ i, S i}
    (h : G.Solves E r s) : G.IsBRFixed s := by
  intro i
  obtain ⟨x, hx⟩ := hBR i s
  have hmem : x ∈ E r i := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; exact h.1.zero i x
    · exact h.1.mem_of_isBR hx (k := r - 1) (by omega) (fun l _ => h.mem (by omega) l)
        (by omega) le_rfl
  rw [h.2] at hmem
  have : x = s i := hmem
  subst this
  exact hx

lemma IsBRFixed.isNash {s : ∀ i, S i} (h : G.IsBRFixed s) : G.IsNash s := by
  intro i x
  by_contra hlt
  apply h i x
  left
  simpa using lt_of_not_ge hlt

/-- **Order independence** (remark after Definition 2.3): if tie-broken best responses exist,
all NBR eliminations to a single profile end at the same profile. -/
lemma Solves.unique (hBR : G.HasBR) {E E' : ℕ → Subgame S} {r r' : ℕ} {s s' : ∀ i, S i}
    (h : G.Solves E r s) (h' : G.Solves E' r' s') : s = s' :=
  h'.eq_of_isBRFixed (h.isBRFixed hBR)

/-- The outcome of NBR elimination is a pure Nash equilibrium (when best responses exist). -/
lemma Solves.isNash (hBR : G.HasBR) {E : ℕ → Subgame S} {r : ℕ} {s : ∀ i, S i}
    (h : G.Solves E r s) : G.IsNash s :=
  (h.isBRFixed hBR).isNash

/-- In a finite game with strict total tie-breaking orders, tie-broken best responses exist. -/
lemma hasBR_of_finite [∀ i, Finite (S i)] [∀ i, IsStrictTotalOrder (S i) (G.prec i)] :
    G.HasBR := by
  intro i s
  -- `Beats` at `s` is a strict order on the finite type `S i`, hence well founded.
  have hirr : ∀ x, ¬ G.Beats i x x s := by
    intro x hx
    rcases hx with hx | hx
    · exact lt_irrefl _ hx
    · exact irrefl _ hx.2
  have htr : ∀ x y z, G.Beats i x y s → G.Beats i y z s → G.Beats i x z s := by
    intro x y z hxy hyz
    rcases hxy with hxy | ⟨hxy, hxy'⟩ <;> rcases hyz with hyz | ⟨hyz, hyz'⟩
    · exact Or.inl (hyz.trans hxy)
    · exact Or.inl (hyz ▸ hxy)
    · exact Or.inl (hxy ▸ hyz)
    · exact Or.inr ⟨hyz.trans hxy, _root_.trans hyz' hxy'⟩
  let rel : S i → S i → Prop := fun y x => G.Beats i y x s
  have : IsTrans (S i) rel := ⟨fun a b c hab hbc => htr _ _ _ hab hbc⟩
  have : Std.Irrefl rel := ⟨hirr⟩
  have hwf : WellFounded rel := Finite.wellFounded_of_trans_of_irrefl rel
  obtain ⟨x, -, hx⟩ := hwf.has_min univ ⟨s i, trivial⟩
  exact ⟨x, fun y hy => hx y trivial hy⟩

omit [DecidableEq ι] in
/-- Monotonicity of global optimality in the subgame. -/
lemma GloballyOptimal.mono {H H' : Subgame S} {i : ι} {s : ∀ j, S j}
    (h : G.GloballyOptimal H i s) (hH : ∀ j, H' j ⊆ H j) : G.GloballyOptimal H' i s :=
  fun t ht => h t (fun j => hH j (ht j))

/-- A clear-outcome witness at index `k` is also one at every later index `k' ≤ r` with
`E k' i = univ`, in particular at the first step that eliminates a strategy of `i`. -/
lemma ClearWitness.of_le {s : ∀ i, S i} {i : ι} {E : ℕ → Subgame S} {r k k' : ℕ}
    (h : G.ClearWitness s i E r k) (hk : k ≤ k') (hk' : k' ≤ r) (hu : E k' i = univ) :
    G.ClearWitness s i E r k' :=
  ⟨h.1, hk', hu, h.2.2.2.mono (fun j => h.1.1.antitone hk hk' j)⟩

/-! ### Removing empty steps -/

/-- Dropping an empty step `m` (`E (m + 1) = E m`) of an elimination sequence. -/
def dropStep (E : ℕ → Subgame S) (m : ℕ) : ℕ → Subgame S :=
  fun j => if j ≤ m then E j else E (j + 1)

omit [DecidableEq ι] [LinearOrder R] in
lemma dropStep_reindex {E : ℕ → Subgame S} {m : ℕ} (hm : E (m + 1) = E m) (k : ℕ) :
    dropStep E m (if k ≤ m then k else k - 1) = E k := by
  unfold dropStep
  by_cases h1 : k ≤ m
  · simp [h1]
  · by_cases h2 : k - 1 ≤ m
    · have : k = m + 1 := by omega
      subst this; simp [hm]
    · simp only [h1, h2, ↓reduceIte]
      congr 1; omega

lemma Solves.dropStep {E : ℕ → Subgame S} {r : ℕ} {s : ∀ i, S i} (h : G.Solves E (r + 1) s)
    {m : ℕ} (hmr : m < r + 1) (hm : E (m + 1) = E m) : G.Solves (dropStep E m) r s := by
  refine ⟨⟨by simp [TieBreakGame.dropStep, h.1.1], fun j hj => ?_⟩, ?_⟩
  · unfold TieBreakGame.dropStep
    by_cases h1 : j + 1 ≤ m
    · simp only [show j ≤ m by omega, h1, ↓reduceIte]; exact h.1.2 j (by omega)
    · by_cases h2 : j ≤ m
      · obtain rfl : j = m := by omega
        simp only [le_refl, h1, ↓reduceIte]; rw [← hm]; exact h.1.2 (j + 1) (by omega)
      · simp only [h1, h2, ↓reduceIte]; exact h.1.2 (j + 1) (by omega)
  · have := dropStep_reindex hm (r + 1)
    simp only [show ¬ (r + 1 ≤ m) by omega, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [this, h.2]

/-- **Short elimination sequences.** In a finite game, any NBR elimination ending at `s`, with
a marked index `k`, can be shortened to one with at most `Σᵢ (|Sᵢ| - 1)` steps that passes
through the subgame `E k` (at an index `k' ≤ r'`). In particular `e_G ≤ Σᵢ |Sᵢ| - n` (remark
after Definition 2.4). -/
lemma Solves.exists_short [Fintype ι] [∀ i, Fintype (S i)] {E : ℕ → Subgame S} {r : ℕ}
    {s : ∀ i, S i} (h : G.Solves E r s) {k : ℕ} (hk : k ≤ r) :
    ∃ (E' : ℕ → Subgame S) (r' k' : ℕ), G.Solves E' r' s ∧ k' ≤ r' ∧ E' k' = E k ∧
      r' + Fintype.card ι ≤ ∑ i, Fintype.card (S i) := by
  classical
  induction r generalizing E k with
  | zero =>
    refine ⟨E, 0, k, h, hk, rfl, ?_⟩
    calc 0 + Fintype.card ι = ∑ _i : ι, 1 := by simp
      _ ≤ ∑ i, Fintype.card (S i) := Finset.sum_le_sum fun i _ =>
          Fintype.card_pos_iff.mpr ⟨s i⟩
  | succ r ih =>
    by_cases hempty : ∃ m < r + 1, E (m + 1) = E m
    · obtain ⟨m, hmr, hm⟩ := hempty
      obtain ⟨E', r', k', h', hk', hE', hr'⟩ :=
        ih (h.dropStep hmr hm) (k := if k ≤ m then k else k - 1) (by split_ifs <;> omega)
      exact ⟨E', r', k', h', hk', by rw [hE', dropStep_reindex hm], hr'⟩
    · push Not at hempty
      refine ⟨E, r + 1, k, h, hk, rfl, ?_⟩
      -- every step removes a strategy: the total number of strategies drops by `≥ 1` per step
      let μ : ℕ → ℕ := fun j => ∑ i, (E j i).toFinset.card
      have hstep : ∀ j < r + 1, μ (j + 1) + 1 ≤ μ j := by
        intro j hj
        have hsub : ∀ i, (E (j + 1) i).toFinset ⊆ (E j i).toFinset := fun i =>
          Set.toFinset_subset_toFinset.mpr ((h.1.2 j hj).1 i)
        obtain ⟨i, hi⟩ : ∃ i, E (j + 1) i ≠ E j i := by
          by_contra hc; push Not at hc; exact hempty j hj (funext hc)
        have hlt : (E (j + 1) i).toFinset.card < (E j i).toFinset.card := by
          apply Finset.card_lt_card
          refine (Finset.ssubset_iff_subset_ne).mpr ⟨hsub i, fun he => hi ?_⟩
          simpa using he
        have := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => Finset.card_le_card (hsub i))
          ⟨i, Finset.mem_univ _, hlt⟩
        simp only [μ]; omega
      have hμ0 : μ 0 = ∑ i, Fintype.card (S i) := by
        simp [μ, h.1.1, full]
      have hμr : Fintype.card ι ≤ μ (r + 1) := by
        rw [Finset.card_univ.symm, Finset.card_eq_sum_ones]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.one_le_card]
        exact ⟨s i, by simp [h.2]⟩
      have : ∀ j ≤ r + 1, μ j + j ≤ μ 0 := by
        intro j hj
        induction j with
        | zero => simp
        | succ j ihj => have := hstep j (by omega); have := ihj (by omega); omega
      have := this (r + 1) le_rfl
      omega

/-- In a finite game, clear-outcome witnesses can be chosen with `k ≤ r ≤ Σᵢ (|Sᵢ| - 1)`. -/
lemma ClearWitness.exists_short [Fintype ι] [∀ i, Fintype (S i)] {s : ∀ i, S i} {i : ι}
    {E : ℕ → Subgame S} {r k : ℕ} (h : G.ClearWitness s i E r k) :
    ∃ (E' : ℕ → Subgame S) (r' k' : ℕ), G.ClearWitness s i E' r' k' ∧
      r' + Fintype.card ι ≤ ∑ j, Fintype.card (S j) := by
  obtain ⟨E', r', k', h', hk', hE', hr'⟩ := h.1.exists_short h.2.1
  exact ⟨E', r', k', ⟨h', hk', by rw [hE']; exact h.2.2.1, by rw [hE']; exact h.2.2.2⟩, hr'⟩

end TieBreakGame

end Cslib.GameTheory
