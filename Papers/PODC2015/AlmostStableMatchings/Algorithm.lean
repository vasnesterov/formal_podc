import Papers.PODC2015.AlmostStableMatchings.Prefs

/-!
# The deterministic algorithm `ASM` (Section 3)

Ostrovsky, Rosenbaum, *Fast Distributed Almost Stable Matchings*, PODC 2015, Algorithms 1–3.

* The state of a man is `ManSt` = his remaining (not yet rejected) acceptable partners `Q`, his
  partner `p` and his set `A` of active potential mates. A woman stores her partner. (The woman's
  list `Q^w` of the paper is not stored: she sends `REJECT` to *all* acceptable men in a worse or
  equal quantile than her new partner, including men who have already removed her; this has no
  effect on any state.)
* The maximal-matching subroutine of Theorem 2.7 is a black box `MMOracle`: any function returning,
  for every bipartite graph `G₀`, a maximal matching of `G₀` (Definition 2.6).
* `prStep` is `ProposalRound` (Algorithm 1), assembled from the local rules `proposers` (step 1:
  `PROPOSE` messages received by a woman), `accepts` (step 2: `ACCEPT` messages), the subroutine
  (step 3), `rejects` (step 4: `REJECT` messages), `womanUpdate` and `manUpdate` (steps 4–5).
  Every node's new state depends only on its own state, the one-bit messages from its neighbours
  and its own partner in `M₀`.
* `quantileMatch` is Algorithm 2, `outer` is one iteration of the outer loop of Algorithm 3 (the
  men with `|Q| ≥ 2^i` at the beginning of the iteration run `ℓ` calls of `quantileMatch`), and
  `asm` runs the iterations `i = 0, …, L`.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2015.AlmostStableMatchings

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

/-- Local state of a man. -/
structure ManSt (W : Type*) where
  /-- Remaining preferences: acceptable women that have not rejected him. -/
  Q : Finset W
  /-- Current partner. -/
  p : Option W
  /-- Active potential mates (the women he currently proposes to). -/
  A : Finset W

/-- Global state: the men's local states and the women's partners. -/
structure St (M W : Type*) where
  /-- Local states of the men. -/
  man : M → ManSt W
  /-- Partners of the women. -/
  pw : W → Option M

namespace St

variable (s : St M W)

/-- `Q^m`. -/
abbrev Q (m : M) : Finset W := (s.man m).Q
/-- `p(m)`. -/
abbrev pm (m : M) : Option W := (s.man m).p
/-- `A_m`. -/
abbrev A (m : M) : Finset W := (s.man m).A

end St

/-- Partner functions of a bipartite matching (output of the maximal-matching subroutine). -/
structure BMatching (M W : Type*) where
  /-- Partner of a man. -/
  pm : M → Option W
  /-- Partner of a woman. -/
  pw : W → Option M

/-- Definition 2.6: `μ` is a maximal matching of the bipartite graph `G`: a matching inside `G`
such that every edge of `G` has a matched endpoint. -/
def BMatching.IsMaximalIn (μ : BMatching M W) (G : M → W → Bool) : Prop :=
  (∀ m w, μ.pm m = some w ↔ μ.pw w = some m) ∧
  (∀ m w, μ.pm m = some w → G m w = true) ∧
  (∀ m w, G m w = true → μ.pm m ≠ none ∨ μ.pw w ≠ none)

/-- The black-box deterministic `MaximalMatching` subroutine of Theorem 2.7, with its round bound
`rounds` (`log⁴ n` in [HKP]). -/
structure MMOracle (M W : Type*) where
  /-- The matching computed on the graph `G₀`. -/
  run : (M → W → Bool) → BMatching M W
  isMaximal : ∀ G, (run G).IsMaximalIn G
  /-- Number of communication rounds used by one call. -/
  rounds : ℕ

/-- Non-vacuity: every bipartite graph has a maximal matching, so `MMOracle`s exist. -/
theorem exists_maximal (G : M → W → Bool) : ∃ μ : BMatching M W, μ.IsMaximalIn G := by
  classical
  -- a matching as a finset of edges; pick one of maximum cardinality
  let IsMat : Finset (M × W) → Prop := fun F =>
    (∀ e ∈ F, G e.1 e.2 = true) ∧ (∀ e ∈ F, ∀ e' ∈ F, e.1 = e'.1 ∨ e.2 = e'.2 → e = e')
  obtain ⟨F, hF, hmax⟩ := (Finset.univ.filter IsMat).exists_max_image Finset.card
    ⟨∅, by simp [IsMat]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF hmax
  obtain ⟨hG, hU⟩ := hF
  refine ⟨⟨fun m => if h : ∃ w, (m, w) ∈ F then some h.choose else none,
    fun w => if h : ∃ m, (m, w) ∈ F then some h.choose else none⟩, ?_, ?_, ?_⟩
  · intro m w
    simp only
    constructor
    · intro h
      split_ifs at h with h1
      cases h
      have hw := h1.choose_spec
      have h2 : ∃ m', (m', h1.choose) ∈ F := ⟨m, hw⟩
      rw [dite_eq_left h2]
      have := hU _ h2.choose_spec _ hw (Or.inr rfl)
      simp only [Prod.mk.injEq] at this
      rw [this.1]
    · intro h
      split_ifs at h with h1
      cases h
      have hm := h1.choose_spec
      have h2 : ∃ w', (h1.choose, w') ∈ F := ⟨w, hm⟩
      rw [dite_eq_left h2]
      have := hU _ h2.choose_spec _ hm (Or.inl rfl)
      simp only [Prod.mk.injEq] at this
      rw [this.2]
  · intro m w h
    simp only at h
    split_ifs at h with h1
    cases h
    exact hG _ h1.choose_spec
  · intro m w hmw
    by_contra hc
    simp only [ne_eq, dite_eq_right_iff, reduceCtorEq, imp_false, not_exists, not_or,
      not_forall, not_not] at hc
    obtain ⟨h1, h2⟩ := hc
    have hnew : IsMat (insert (m, w) F) := by
      refine ⟨?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.1 he with rfl | he
        · exact hmw
        · exact hG e he
      · intro e he e' he' hee
        rcases Finset.mem_insert.1 he with rfl | he <;>
          rcases Finset.mem_insert.1 he' with rfl | he'
        · rfl
        · rcases hee with h | h
          · exact (h1 e'.2 (by rwa [show e' = (m, e'.2) from Prod.ext h.symm rfl] at he')).elim
          · exact (h2 e'.1 (by rwa [show e' = (e'.1, w) from Prod.ext rfl h.symm] at he')).elim
        · rcases hee with h | h
          · exact (h1 e.2 (by rwa [show e = (m, e.2) from Prod.ext h rfl] at he)).elim
          · exact (h2 e.1 (by rwa [show e = (e.1, w) from Prod.ext rfl h] at he)).elim
        · exact hU e he e' he' hee
    have := hmax _ hnew
    rw [Finset.card_insert_of_notMem (fun h => h1 _ h)] at this
    omega

namespace Prefs

variable (P : Prefs M W) (k : ℕ)

/-! ## ProposalRound (Algorithm 1) as local rules -/

/-- Step 1, as seen by woman `w`: the acceptable men who send her `PROPOSE` (those with `w ∈ A`). -/
def proposers (s : St M W) (w : W) : Finset M := (P.NW w).filter fun m => w ∈ s.A m

/-- Step 2: `w` sends `ACCEPT` to the proposers of her best quantile receiving proposals. -/
def accepts (props : Finset M) (w : W) (m : M) : Bool :=
  decide (m ∈ props ∧ ∀ m' ∈ props, P.qW k w m ≤ P.qW k w m')

/-- Step 4: `w`, matched to `m₀` in `M₀`, sends `REJECT` to every acceptable `m ≠ m₀` in a lesser or
equal quantile than `m₀`. -/
def rejects (w : W) (p0 : Option M) (m : M) : Bool :=
  match p0 with
  | none => false
  | some m0 => decide (m ∈ P.NW w ∧ m ≠ m0 ∧ P.qW k w m0 ≤ P.qW k w m)

/-- Step 4 (women): a woman matched in `M₀` takes her new partner. -/
def womanUpdate (pw p0 : Option M) : Option M := p0.or pw

/-- Steps 4–5 (men): given his partner `p0` in `M₀` and the `REJECT` messages `rej`, a man removes
the rejecting women from `Q` and `A`; if matched in `M₀` he takes the new partner and empties `A`;
if his partner rejected him he becomes unmatched. -/
def manUpdate (σ : ManSt W) (p0 : Option W) (rej : W → Bool) : ManSt W where
  Q := σ.Q.filter fun w => rej w = false
  p := p0.or (σ.p.filter fun w => !rej w)
  A := if p0.isSome then ∅ else σ.A.filter fun w => rej w = false

/-- The graph `G₀` of accepted proposals. -/
def acceptGraph (s : St M W) : M → W → Bool := fun m w => P.accepts k (P.proposers s w) w m

/-- The matching `M₀` computed by the subroutine in step 3. -/
def mmOut (mm : MMOracle M W) (s : St M W) : BMatching M W := mm.run (P.acceptGraph k s)

/-- `ProposalRound(Q, k, A)` (Algorithm 1). -/
def prStep (mm : MMOracle M W) (s : St M W) : St M W where
  man m := manUpdate (s.man m) ((P.mmOut k mm s).pm m)
    (fun w => P.rejects k w ((P.mmOut k mm s).pw w) m)
  pw w := womanUpdate (s.pw w) ((P.mmOut k mm s).pw w)

/-! ## QuantileMatch (Algorithm 2) and ASM (Algorithm 3) -/

/-- The best nonempty quantile `Q_i` of a man's remaining list. -/
def bestQ (m : M) (Q : Finset W) : Finset W := Q.filter fun w => ∀ w' ∈ Q, P.qM k m w ≤ P.qM k m w'

/-- First lines of `QuantileMatch`: every participating unmatched man sets `A ← Q_i`. -/
def initQM (act : Finset M) (s : St M W) : St M W where
  man m := if m ∈ act ∧ s.pm m = none then { s.man m with A := P.bestQ k m (s.Q m) } else s.man m
  pw := s.pw

/-- `QuantileMatch(Q, k)` run by the men in `act` (Algorithm 2): `k` calls of `ProposalRound`. -/
def quantileMatch (mm : MMOracle M W) (act : Finset M) (s : St M W) : St M W :=
  (P.prStep k mm)^[k] (P.initQM k act s)

/-- The men active in iteration `i` of the outer loop: those with `|Q| ≥ 2^i`. -/
def active (_P : Prefs M W) (i : ℕ) (s : St M W) : Finset M := Finset.univ.filter fun m => 2 ^ i ≤ (s.Q m).card

/-- Iteration `i` of the outer loop of `ASM`: the active men run `ℓ` calls of `QuantileMatch`. -/
def outer (mm : MMOracle M W) (ℓ i : ℕ) (s : St M W) : St M W :=
  (P.quantileMatch k mm (P.active i s))^[ℓ] s

/-- Initial state: full lists, nobody matched, `A = ∅`. -/
def init : St M W where
  man m := ⟨P.NM m, none, ∅⟩
  pw _ := none

/-- State after the outer iterations `0, …, i - 1`. -/
def stage (mm : MMOracle M W) (ℓ : ℕ) : ℕ → St M W
  | 0 => P.init
  | i + 1 => P.outer k mm ℓ i (stage mm ℓ i)

/-- `ASM` with `k` quantiles, `ℓ` calls of `QuantileMatch` per outer iteration and outer
iterations `i = 0, …, L`. -/
def asm (mm : MMOracle M W) (ℓ L : ℕ) : St M W := P.stage k mm ℓ (L + 1)

/-! ## The paper's parameters -/

/-- `k = ⌈8/ε⌉`. -/
noncomputable def kOf (ε : ℝ) : ℕ := ⌈8 / ε⌉₊

/-- `ℓ = ⌈2 δ⁻¹ k⌉` with `δ = ε/8`, i.e. `⌈16 k / ε⌉`. -/
noncomputable def ellOf (ε : ℝ) : ℕ := ⌈16 * kOf ε / ε⌉₊

/-- `ASM(P, ε, n)`: `k = ⌈8/ε⌉`, `δ = ε/8`, `ℓ = ⌈2k/δ⌉`, outer iterations `i = 0, …, ⌊log₂ n⌋`. -/
noncomputable def ASM (mm : MMOracle M W) (ε : ℝ) (n : ℕ) : St M W :=
  P.asm (kOf ε) mm (ellOf ε) (Nat.log 2 n)

end Prefs

end Papers.PODC2015.AlmostStableMatchings
