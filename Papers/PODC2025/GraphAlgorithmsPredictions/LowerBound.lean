import Papers.PODC2025.GraphAlgorithmsPredictions.Line
import Podc.Foundations.Combinatorics.HypergraphRamsey

/-!
# Theorem 4.1: lower bound for component-size bounded MIS algorithms on the line

Theorem 4.1 of Boyar–Ellen–Larsen (PODC 2025 BA) = Lemma 5 of the full version (arXiv:2501.05267):
every deterministic MIS algorithm for the `n`-node line whose round complexity does not depend on
the identifier domain needs at least `(n - 5) / 2` rounds in the LOCAL model. The proof (suggested
by J. Suomela) goes through Lemma 4 (3-colouring needs `(n - 3) / 2` rounds), proved with the
hypergraph Ramsey theorem.

## Model

A `T`-round algorithm for `n`-node lines is a function `f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → β` with
`Cslib.Local.IsLocal T f` (nodes are named by their identifiers, the label of a node holds the
identifiers of its left and right neighbours, see `Line.lean`). The algorithm may depend on `n`
(nodes know `n`), and it must be correct for *every* injective identifier placement
`id : Fin n ↪ ℕ`: its round complexity `T` does not depend on the identifier domain. Bounded-domain
versions (`*_bounded`) show that identifiers below an explicit bound `D(n, T)` already suffice to
defeat every `T`-round algorithm ("`d` is a sufficiently large function of `n`").

## Main results

* `exists_homogeneous_window`: Ramsey step — for every `T`-local `f` with finitely many output
  values there is an `L`-set `Y` of identifiers such that `f` outputs the same value at the centre of
  every window of `2T + 3` consecutive positions carrying increasing identifiers from `Y`.
* `lemma_4`: no `T`-round algorithm colours all `n`-node lines properly with finitely many colours
  (in particular 3) if `T < (n - 3) / 2` (`2T + 4 ≤ n`).
* `lemma_5_reduction`: an MIS algorithm with `T` rounds gives a 3-colouring algorithm with `T + 1`
  rounds.
* `theorem_4_1`: an MIS algorithm for `n`-node lines needs `T ≥ (n - 5) / 2` rounds (the paper's
  bound, via Lemmas 4 and 5).
* `mis_lowerBound_sharp`: the same direct Ramsey argument gives the slightly better bound
  `T ≥ (n - 4) / 2`.
-/

namespace Podc.GraphAlgorithmsPredictions

open SimpleGraph Cslib.Local

/-! ### Problems on the line -/

/-- `f` computes a maximal independent set of every `n`-node line: for every placement of
identifiers, the positions whose node outputs `true` form an MIS of the path. -/
def SolvesMISLine (n : ℕ) (f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool) : Prop :=
  ∀ id : Fin n ↪ ℕ, IsMIS (pathGraph n) {i | f (lineG id) (lineLab id) (id i) = true}

/-- `f` properly colours every `n`-node line (colours in `β`): adjacent nodes output different
colours. -/
def SolvesColouringLine {β : Type*} (n : ℕ) (f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → β) : Prop :=
  ∀ id : Fin n ↪ ℕ, ∀ i j : Fin n, (pathGraph n).Adj i j →
    f (lineG id) (lineLab id) (id i) ≠ f (lineG id) (lineLab id) (id j)

/-! ### The Ramsey step -/

/-- The line carrying the elements of a finite set `X` in increasing order. -/
noncomputable def sortedLine (X : Finset ℕ) : Fin X.card ↪ ℕ := (X.orderEmbOfFin rfl).toEmbedding

/-- **Ramsey step** (proof of Lemma 4). For every `T` and `L` there is a bound `D` such that for every
`T`-round algorithm `f` with finitely many outputs there is a set `Y` of `L` identifiers below `D`
and an output `b` such that `f` outputs `b` at the centre of every window of `2T + 3` consecutive
positions (of any line) that carry increasing identifiers from `Y`. -/
theorem exists_homogeneous_window (T L : ℕ) (β : Type*) [Finite β] :
    ∃ D, ∀ f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → β, IsLocal T f →
      ∃ Y : Finset ℕ, Y ⊆ Finset.range D ∧ Y.card = L ∧ ∃ b : β,
        ∀ {n : ℕ} (id : Fin n ↪ ℕ) (a : ℕ), a + 2 * T + 2 < n →
          (∀ k < 2 * T + 2, ix id (a + k) < ix id (a + k + 1)) →
          (∀ k ≤ 2 * T + 2, ix id (a + k) ∈ Y) →
          f (lineG id) (lineLab id) (ix id (a + T + 1)) = b := by
  classical
  obtain ⟨N, hN⟩ := Cslib.exists_homogeneous_finite (2 * T + 3) L β
  refine ⟨N, fun f hf => ?_⟩
  let c : Finset ℕ → β := fun X =>
    f (lineG (sortedLine X)) (lineLab (sortedLine X)) (ix (sortedLine X) (T + 1))
  obtain ⟨Y, hYS, hYc, b, hb⟩ := hN c (Finset.range N) (by simp)
  refine ⟨Y, hYS, hYc, b, fun {n} id a ha hmono hmem => ?_⟩
  let g : Fin (2 * T + 3) → ℕ := fun k => ix id (a + k)
  have gmono : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.2 fun k => ?_
    simp only [g, Fin.val_succ, Fin.val_castSucc]
    have := hmono k (by omega)
    rwa [Nat.add_assoc] at this
  let X := Finset.univ.image g
  have hXc : X.card = 2 * T + 3 := by
    rw [Finset.card_image_of_injective _ gmono.injective]; simp
  have hXY : X ⊆ Y := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hy
    exact hmem k (by omega)
  have hcX : c X = b := hb X hXY hXc
  -- identify the sorted line on `X` with the window
  let g' : Fin X.card → ℕ := fun k => ix id (a + k)
  have hg' : g' = X.orderEmbOfFin rfl := by
    refine Finset.orderEmbOfFin_unique rfl (fun k => ?_) ?_
    · exact Finset.mem_image.2 ⟨⟨k, by omega⟩, Finset.mem_univ _, rfl⟩
    · intro k l hkl
      exact gmono (a := ⟨k, by omega⟩) (b := ⟨l, by omega⟩) hkl
  have hw : ∀ k ≤ 2 * T + 2, ix id (a + k) = ix (sortedLine X) (0 + k) := by
    intro k hk
    rw [Nat.zero_add, ix_of_lt (sortedLine X) (show k < X.card by omega)]
    exact congrFun hg' ⟨k, _⟩
  have hv := viewEq_window id (sortedLine X) T a 0 ha (by omega) hw
  have hc := hw (T + 1) (by omega)
  rw [← Nat.add_assoc, Nat.zero_add] at hc
  rw [hf _ _ _ _ _ hv, hc]
  exact hcX

/-! ### Padded lines -/

/-- The `n`-node line whose first `|Y|` positions carry the elements of `Y` in increasing order and
whose remaining positions `i` carry `D + i` (fresh identifiers when `Y ⊆ [0, D)`). -/
noncomputable def padLine (Y : Finset ℕ) (D n : ℕ) (hY : Y ⊆ Finset.range D) : Fin n ↪ ℕ where
  toFun i := if h : i.val < Y.card then Y.orderEmbOfFin rfl ⟨i, h⟩ else D + i
  inj' := by
    have hlt : ∀ (k : ℕ) (h : k < Y.card), Y.orderEmbOfFin rfl ⟨k, h⟩ < D := fun k h =>
      Finset.mem_range.1 (hY (Finset.orderEmbOfFin_mem Y rfl _))
    intro i j hij
    simp only at hij
    split_ifs at hij with h1 h2 h2
    · exact Fin.ext (by simpa using (Y.orderEmbOfFin rfl).injective hij)
    · have := hlt _ h1; omega
    · have := hlt _ h2; omega
    · exact Fin.ext (by omega)

lemma padLine_apply (Y : Finset ℕ) (D n : ℕ) (hY : Y ⊆ Finset.range D) (i : Fin n) :
    padLine Y D n hY i =
      if h : i.val < Y.card then Y.orderEmbOfFin rfl ⟨i, h⟩ else D + i := rfl

lemma padLine_lt {Y : Finset ℕ} {D n : ℕ} (hY : Y ⊆ Finset.range D) (i : Fin n) :
    padLine Y D n hY i < D + n := by
  rw [padLine_apply]
  split_ifs with h
  · have := Finset.mem_range.1 (hY (Finset.orderEmbOfFin_mem Y rfl ⟨i, h⟩)); omega
  · omega

lemma ix_padLine {Y : Finset ℕ} {D n : ℕ} (hY : Y ⊆ Finset.range D) {k : ℕ} (hk : k < Y.card)
    (hkn : k < n) : ix (padLine Y D n hY) k = Y.orderEmbOfFin rfl ⟨k, hk⟩ := by
  rw [ix_of_lt _ hkn, padLine_apply]
  simp only [hk, ↓reduceDIte]

/-- On a padded line every window inside the `Y`-part satisfies the hypotheses of
`exists_homogeneous_window`. -/
lemma padLine_window {Y : Finset ℕ} {D n T : ℕ} (hY : Y ⊆ Finset.range D) {a : ℕ}
    (haY : a + 2 * T + 2 < Y.card) (hYn : Y.card ≤ n) :
    (∀ k < 2 * T + 2, ix (padLine Y D n hY) (a + k) < ix (padLine Y D n hY) (a + k + 1)) ∧
    (∀ k ≤ 2 * T + 2, ix (padLine Y D n hY) (a + k) ∈ Y) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [ix_padLine hY (by omega) (by omega), ix_padLine hY (by omega) (by omega)]
    exact (Y.orderEmbOfFin rfl).strictMono (by simp [Fin.lt_def])
  · rw [ix_padLine hY (by omega) (by omega)]
    exact Finset.orderEmbOfFin_mem Y rfl _

/-! ### Lemma 4: colouring -/

/-- **Lemma 4** (full version), bounded-identifier form, for any finite set of colours: if
`2T + 4 ≤ n` (i.e. `T < (n - 3) / 2`) there is `D` such that every `T`-round algorithm with
finitely many colours outputs the same colour at two adjacent nodes of some `n`-node line with
identifiers `< D`. -/
theorem lemma_4_bounded {n T : ℕ} (h : 2 * T + 4 ≤ n) (β : Type*) [Finite β] :
    ∃ D, ∀ f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → β, IsLocal T f →
      ∃ id : Fin n ↪ ℕ, (∀ i, id i < D) ∧ ∃ i j : Fin n, (pathGraph n).Adj i j ∧
        f (lineG id) (lineLab id) (id i) = f (lineG id) (lineLab id) (id j) := by
  obtain ⟨D, hD⟩ := exists_homogeneous_window T (2 * T + 4) β
  refine ⟨D + n, fun f hf => ?_⟩
  obtain ⟨Y, hYD, hYc, b, hb⟩ := hD f hf
  let id := padLine Y D n hYD
  refine ⟨id, padLine_lt hYD, ⟨T + 1, by omega⟩, ⟨T + 2, by omega⟩,
    by rw [pathGraph_adj]; simp, ?_⟩
  have w0 := padLine_window (n := n) (T := T) (a := 0) hYD (by omega) (by omega)
  have w1 := padLine_window (n := n) (T := T) (a := 1) hYD (by omega) (by omega)
  have h0 := hb id 0 (by omega) w0.1 w0.2
  have h1 := hb id 1 (by omega) w1.1 w1.2
  rw [← ix_fin, ← ix_fin]
  simp only [Nat.zero_add] at h0
  rw [show 1 + T + 1 = T + 2 by omega] at h1
  exact h0.trans h1.symm

/-- **Lemma 4** of the full version (arXiv:2501.05267): every deterministic algorithm that colours
the nodes of every `n`-node line with 3 colours (more generally, with any finite set of colours),
with a round complexity `T` that does not depend on the identifier domain, needs
`T ≥ (n - 3) / 2` rounds. -/
theorem lemma_4 {n T : ℕ} {β : Type*} [Finite β] (f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → β)
    (hf : IsLocal T f) (hs : SolvesColouringLine n f) : ((n : ℝ) - 3) / 2 ≤ T := by
  by_contra hlt
  have h : 2 * T + 4 ≤ n := by
    have : (2 * T + 3 : ℝ) < n := by push Not at hlt; linarith
    exact_mod_cast this
  obtain ⟨D, hD⟩ := lemma_4_bounded h β
  obtain ⟨id, -, i, j, hij, heq⟩ := hD f hf
  exact hs id i j hij heq

/-! ### MIS facts on the line -/

/-- An MIS of the path, in terms of positions: no two consecutive members, and every non-member has
a member neighbour. -/
lemma mis_facts {n : ℕ} (id : Fin n ↪ ℕ) {P : ℕ → Prop}
    (hs : IsMIS (pathGraph n) {i | P (id i)}) :
    (∀ k, k + 1 < n → ¬ (P (ix id k) ∧ P (ix id (k + 1)))) ∧
    (∀ k < n, ¬ P (ix id k) →
      (0 < k ∧ P (ix id (k - 1))) ∨ (k + 1 < n ∧ P (ix id (k + 1)))) := by
  refine ⟨fun k hk ⟨h1, h2⟩ => ?_, fun k hk hP => ?_⟩
  · have m1 : (⟨k, by omega⟩ : Fin n) ∈ {i | P (id i)} := by
      simpa [ix_of_lt id (show k < n by omega)] using h1
    have m2 : (⟨k + 1, hk⟩ : Fin n) ∈ {i | P (id i)} := by simpa [ix_of_lt id hk] using h2
    exact hs.1 m1 m2 (by simp [Fin.ext_iff]) (by rw [pathGraph_adj]; simp)
  · obtain ⟨u, hu, hadj⟩ := hs.2 ⟨k, hk⟩ (by simpa [ix_of_lt id hk] using hP)
    rw [pathGraph_adj] at hadj
    simp only [Set.mem_ofPred_eq] at hu
    rcases hadj with h | h
    · have h' : k + 1 = (u : ℕ) := by simpa using h
      refine Or.inr ⟨by omega, ?_⟩
      rwa [h', ix_fin]
    · have h' : (u : ℕ) + 1 = k := by simpa using h
      refine Or.inl ⟨by omega, ?_⟩
      rwa [show k - 1 = (u : ℕ) by omega, ix_fin]

/-! ### Direct lower bound for MIS -/

/-- Bounded-identifier form of `mis_lowerBound_sharp`: if `2T + 5 ≤ n` there is `D` such that every
`T`-round algorithm fails to compute an MIS on some `n`-node line with identifiers `< D`. -/
theorem mis_lowerBound_bounded {n T : ℕ} (h : 2 * T + 5 ≤ n) :
    ∃ D, ∀ f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool, IsLocal T f →
      ∃ id : Fin n ↪ ℕ, (∀ i, id i < D) ∧
        ¬ IsMIS (pathGraph n) {i | f (lineG id) (lineLab id) (id i) = true} := by
  obtain ⟨D, hD⟩ := exists_homogeneous_window T (2 * T + 5) Bool
  refine ⟨D + n, fun f hf => ?_⟩
  obtain ⟨Y, hYD, hYc, b, hb⟩ := hD f hf
  let id := padLine Y D n hYD
  refine ⟨id, padLine_lt hYD, fun hs => ?_⟩
  obtain ⟨hind, hdom⟩ := mis_facts id (P := fun u => f (lineG id) (lineLab id) u = true) hs
  have hpos : ∀ a, a ≤ 2 → f (lineG id) (lineLab id) (ix id (a + T + 1)) = b := by
    intro a ha
    have w := padLine_window (n := n) (T := T) (a := a) hYD (by omega) (by omega)
    exact hb id a (by omega) w.1 w.2
  have e1 := hpos 0 (by omega)
  have e2 := hpos 1 (by omega)
  have e3 := hpos 2 (by omega)
  simp only [Nat.zero_add] at e1
  rw [show 1 + T + 1 = T + 1 + 1 by omega] at e2
  rw [show 2 + T + 1 = T + 2 + 1 by omega] at e3
  cases b with
  | true => exact hind (T + 1) (by omega) ⟨e1, e2⟩
  | false =>
    rcases hdom (T + 2) (by omega) (by simp [e2]) with ⟨-, h'⟩ | ⟨-, h'⟩
    · simp [e1] at h'
    · simp [e3] at h'

/-- **Sharpened Theorem 4.1**: the direct Ramsey argument (three consecutive equal outputs instead of
the reduction to 3-colouring) shows that every MIS algorithm for `n`-node lines needs
`T ≥ (n - 4) / 2` rounds. -/
theorem mis_lowerBound_sharp {n T : ℕ} (f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool)
    (hf : IsLocal T f) (hs : SolvesMISLine n f) : ((n : ℝ) - 4) / 2 ≤ T := by
  by_contra hlt
  have h : 2 * T + 5 ≤ n := by
    have : (2 * T + 4 : ℝ) < n := by push Not at hlt; linarith
    exact_mod_cast this
  obtain ⟨D, hD⟩ := mis_lowerBound_bounded h
  obtain ⟨id, -, hn⟩ := hD f hf
  exact hn (hs id)

/-! ### Lemma 5: reduction from 3-colouring to MIS, and Theorem 4.1 -/

/-- One extra round turning an MIS (second component of the state) into a 3-colouring: MIS nodes
take colour `0`; a non-MIS node takes `1` if its left neighbour is in the MIS and `2` otherwise. -/
noncomputable def colourStep (G : SimpleGraph ℕ) (y : ℕ → Lab × Bool) (v : ℕ) : Fin 3 :=
  open Classical in
  if (y v).2 = true then 0
  else if ∃ u, (y v).1.1 = some u ∧ G.Adj v u ∧ (y u).2 = true then 1 else 2

/-- The 3-colouring algorithm of Lemma 5: run the MIS algorithm `f`, then `colourStep`. -/
noncomputable def misToColour (f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool) :
    SimpleGraph ℕ → (ℕ → Lab) → ℕ → Fin 3 :=
  fun G x => colourStep G (fun u => (x u, f G x u))

lemma colourStep_isLocal : IsLocal 1 colourStep := by
  intro G y G' y' v hv
  have hyv : y v = y' v := hv.2 v (by simp)
  have hadj := hv.1.adj_iff one_pos
  have hex : (∃ u, (y v).1.1 = some u ∧ G.Adj v u ∧ (y u).2 = true) ↔
      (∃ u, (y' v).1.1 = some u ∧ G'.Adj v u ∧ (y' u).2 = true) := by
    refine exists_congr fun u => ?_
    rw [hyv, ← hadj u]
    refine and_congr_right fun _ => and_congr_right fun ha => ?_
    rw [hv.2 u (by rw [edist_eq_one_iff_adj.2 ha]; simp)]
  classical
  unfold colourStep
  exact if_congr (by rw [hyv]) rfl (if_congr hex rfl rfl)

/-- **Lemma 5** (reduction): a `T`-round MIS algorithm gives a `(T + 1)`-round algorithm... -/
lemma misToColour_isLocal {T : ℕ} {f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool}
    (hf : IsLocal T f) : IsLocal (T + 1) (misToColour f) := by
  have h1 : IsLocal T (fun G (x : ℕ → Lab) u => (x u, f G x u)) := by
    intro G x G' x' v hv
    show (x v, f G x v) = (x' v, f G' x' v)
    rw [hv.2 v (by simp), hf _ _ _ _ _ hv]
  have := colourStep_isLocal.comp h1
  rwa [Nat.add_comm] at this

/-- **Lemma 5** (reduction): ... which properly 3-colours every `n`-node line if `f` computes an MIS
of every `n`-node line. -/
lemma misToColour_solves {n : ℕ} {f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool}
    (hs : SolvesMISLine n f) : SolvesColouringLine n (misToColour f) := by
  intro id
  obtain ⟨hind, hdom⟩ := mis_facts id (P := fun u => f (lineG id) (lineLab id) u = true) (hs id)
  set m : ℕ → Prop := fun k => f (lineG id) (lineLab id) (ix id k) = true with hm
  -- the colour at position `k`
  have hcol : ∀ k < n, misToColour f (lineG id) (lineLab id) (ix id k) =
      if m k then 0 else if 0 < k ∧ m (k - 1) then 1 else 2 := by
    intro k hk
    classical
    simp only [misToColour, colourStep, hm]
    congr 1
    have hex : (∃ u, (lineLab id (ix id k)).1 = some u ∧ (lineG id).Adj (ix id k) u ∧
        f (lineG id) (lineLab id) u = true) ↔
        (0 < k ∧ f (lineG id) (lineLab id) (ix id (k - 1)) = true) := by
      rw [lineLab_ix id hk]
      constructor
      · rintro ⟨u, hu, -, hfu⟩
        dsimp only at hu
        split_ifs at hu with h0
        · cases hu; exact ⟨h0, hfu⟩
      · rintro ⟨h0, hf0⟩
        refine ⟨_, by simp [h0], (lineG_adj_ix id hk _).2 (Or.inr ⟨h0, rfl⟩), hf0⟩
    simp only [hex]
  -- adjacent positions `k`, `k + 1` get different colours
  have key : ∀ k, k + 1 < n → misToColour f (lineG id) (lineLab id) (ix id k) ≠
      misToColour f (lineG id) (lineLab id) (ix id (k + 1)) := by
    intro k hk heq
    rw [hcol k (by omega), hcol (k + 1) hk] at heq
    simp only [Nat.add_sub_cancel, Nat.succ_pos, true_and] at heq
    by_cases hk0 : m k
    · have : ¬ m (k + 1) := fun h => hind k hk ⟨hk0, h⟩
      simp [hk0, this] at heq
    · by_cases hk1 : m (k + 1)
      · simp only [hk0, hk1, ↓reduceIte] at heq
        split_ifs at heq <;> simp at heq
      · simp only [hk0, hk1, ↓reduceIte] at heq
        split_ifs at heq with h2
        · exact absurd heq (by decide)
        · rcases hdom k (by omega) hk0 with h3 | ⟨-, h3⟩
          · exact h2 h3
          · exact hk1 h3
  intro i j hij
  rw [pathGraph_adj] at hij
  rw [← ix_fin, ← ix_fin]
  rcases hij with h | h
  · rw [← h]; exact key i (by omega)
  · rw [← h]; exact (key j (by omega)).symm

/-- **Theorem 4.1** of Boyar–Ellen–Larsen (PODC 2025 BA; Lemma 5 of the full version): every
deterministic algorithm that computes a maximal independent set of every `n`-node line, with a round
complexity `T` that does not depend on the identifier domain (in particular every component-size
bounded algorithm), needs at least `(n - 5) / 2` rounds in the LOCAL model. Proof as in the paper:
Lemma 5 reduces 3-colouring to MIS with one extra round, then Lemma 4. -/
theorem theorem_4_1 {n T : ℕ} (f : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool)
    (hf : IsLocal T f) (hs : SolvesMISLine n f) : ((n : ℝ) - 5) / 2 ≤ T := by
  have := lemma_4 (misToColour f) (misToColour_isLocal hf) (misToColour_solves hs)
  push_cast at this
  linarith

/-! ### Non-vacuity: an `n`-round MIS algorithm for `n`-node lines -/

/-- Distance to the left end, following left-neighbour labels along edges of `G`, truncated at `k`
steps. -/
noncomputable def leftDist (G : SimpleGraph ℕ) (x : ℕ → Lab) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, v =>
    open Classical in
    match (x v).1 with
    | none => 0
    | some u => if G.Adj v u then leftDist G x k u + 1 else 0

lemma leftDist_viewEq (k : ℕ) : ∀ {G G' : SimpleGraph ℕ} {x x' : ℕ → Lab} {v : ℕ},
    ViewEq k G x G' x' v → leftDist G x k v = leftDist G' x' k v := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro G G' x x' v hv
    have hxv : x v = x' v := hv.2 v (by simp)
    simp only [leftDist, ← hxv]
    split
    · rfl
    · rename_i u _
      have hadj := hv.1.adj_iff (Nat.succ_pos k) u
      by_cases ha : G.Adj v u
      · have hd : G.edist v u ≤ 1 := by rw [edist_eq_one_iff_adj.2 ha]
        have hu : ViewEq k G x G' x' u := by
          refine ⟨hv.1.mono hd (by omega), fun w hw => hv.2 w ?_⟩
          have := edist_le_natCast_add hd hw
          simpa [Nat.add_comm] using this
        simp only [ha, hadj.1 ha, ↓reduceIte, ih hu]
      · simp only [ha, (not_congr hadj).1 ha, ↓reduceIte]

lemma leftDist_line {n : ℕ} (id : Fin n ↪ ℕ) (k : ℕ) :
    ∀ p < n, p ≤ k → leftDist (lineG id) (lineLab id) k (ix id p) = p := by
  induction k with
  | zero => intro p _ hp; simp [leftDist]; omega
  | succ k ih =>
    intro p hp hpk
    simp only [leftDist, lineLab_ix id hp]
    rcases Nat.eq_zero_or_pos p with rfl | h0
    · simp
    · simp only [h0, ↓reduceIte]
      simp only [(lineG_adj_ix id hp _).2 (Or.inr ⟨h0, rfl⟩), ↓reduceIte,
        ih (p - 1) (by omega) (by omega)]
      omega

/-- The parity algorithm: a node joins iff its distance to the left end is even. -/
noncomputable def parityMIS (n : ℕ) : SimpleGraph ℕ → (ℕ → Lab) → ℕ → Bool :=
  fun G x v => decide (Even (leftDist G x n v))

/-- **Non-vacuity** of `theorem_4_1`: MIS on `n`-node lines is solvable in `n` rounds (by the
parity algorithm, which uses the orientation), so the lower bound `(n - 5) / 2` is linear-tight up
to a factor `2`. -/
theorem exists_mis_algorithm (n : ℕ) : ∃ f, IsLocal n f ∧ SolvesMISLine n f := by
  refine ⟨parityMIS n, fun G x G' x' v hv => by simp [parityMIS, leftDist_viewEq n hv], ?_⟩
  intro id
  have hpar : ∀ i : Fin n, parityMIS n (lineG id) (lineLab id) (id i) = decide (Even i.val) := by
    intro i
    rw [parityMIS, ← ix_fin, leftDist_line id n i i.2 (by omega)]
  refine ⟨fun i hi j hj hij hadj => ?_, fun i hi => ?_⟩
  · simp only [Set.mem_ofPred_eq, hpar, decide_eq_true_eq] at hi hj
    rw [pathGraph_adj] at hadj
    rcases hadj with h | h
    · rw [← h] at hj; exact Nat.not_even_iff_odd.2 hi.add_one hj
    · rw [← h] at hi; exact Nat.not_even_iff_odd.2 hj.add_one hi
  · simp only [Set.mem_ofPred_eq, hpar, decide_eq_true_eq, Nat.not_even_iff_odd] at hi
    obtain ⟨m, hm⟩ := hi
    refine ⟨⟨i.val - 1, by omega⟩, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, hpar, decide_eq_true_eq]
      exact ⟨m, by omega⟩
    · rw [pathGraph_adj]; right; simp; omega

end Podc.GraphAlgorithmsPredictions
