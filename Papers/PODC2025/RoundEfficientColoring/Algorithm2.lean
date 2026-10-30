import Papers.PODC2025.RoundEfficientColoring.Plan

/-!
# Algorithm 2: messages, outputs and correctness

Chang–Mishra–Nguyen–Salim, PODC 2025, Algorithm 2 (`Δ ≥ 8`), lines 11–23, Lemma 5.4 and
Lemma 5.5, and the correctness part of the proof of Theorem 2.

Palettes: one party (Alice) has the own palette `[o, o + Δ - 1)` with `o = 0`, the other (Bob)
`[o', o' + Δ - 1)` with `o' = Δ - 1`; the special colour is `2Δ - 2`. Each party sends one message
(`Plan.info`), computed from its own graph only:

* `cov v`: `v` is covered by its matching (line 11);
* `high v`: its degree at `v` is `> Δ / 2` (line 11);
* `cs`, `lvl`: the greedy colour cover of its low-degree vertices (Lemma 5.4);
* `used7 v j` (`j < 7`): its own palette colour `j` is used at `v` by its colouring of `R \ M`
  (Lemma 5.5).

Hence **one** round of simultaneous messages suffices (the paper uses `O(1)` rounds: it sends the
information of Lemma 5.5 in a later round, but nothing in it depends on the other party).

Outputs (`Plan.color`): edges of `R \ M` get their own colour; an edge `s(u, f u)` of the
matching gets the special colour if `f u` is not covered by the other party's matching or has
degree `> Δ/2` there, and otherwise the colour of the other party's palette that the cover
assigns to `f u` (lines 12–22); deferred edges are coloured greedily from the first seven colours
of the other party's palette, avoiding the colours the other party uses at the endpoints and the
colours of the own matching edges at the endpoints (line 23, Lemma 5.5).
-/

set_option linter.unusedSectionVars false

namespace Podc.RoundEfficientColoring

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The message of one party in Algorithm 2 (before encoding into bits). -/
structure Info (V : Type*) where
  /-- The colours of the greedy cover (Lemma 5.4). -/
  cs : List ℕ
  /-- The level of each low-degree vertex in the greedy cover. -/
  lvl : V → ℕ
  /-- Coverage by the sender's matching. -/
  cov : V → Bool
  /-- Sender's degree `> Δ / 2`. -/
  high : V → Bool
  /-- `used7 v j`: `j < 7` and the sender's own colour `j` is used at `v`. -/
  used7 : V → ℕ → Bool

/-- The colour of an edge of the own matching at its non-top endpoint `v` (lines 12–22). -/
def matchColor (Δ o' : ℕ) (q : Info V) (v : V) : ℕ :=
  if q.cov v = true ∧ q.high v = false then o' + q.cs.getD (q.lvl v) 0 else 2 * Δ - 2

namespace Plan

variable {Δ : ℕ} {X : SimpleGraph V} (p : Plan Δ X)

open Classical in
/-- The message of the party with plan `p`. -/
noncomputable def info : Info V where
  cs := p.cs
  lvl := p.lvl
  cov v := decide (∃ y, p.M.Adj v y)
  high v := decide (Δ < 2 * (X.neighborSet v).ncard)
  used7 v j := decide (j < 7 ∧ ∃ w, p.R'.Adj v w ∧ p.col s(v, w) = j)

open Classical in
/-- Colours of the matching edges. -/
noncomputable def mcol (o' : ℕ) (q : Info V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => if p.top a ∧ ¬ p.top b then matchColor Δ o' q b
    else if p.top b ∧ ¬ p.top a then matchColor Δ o' q a else 0, fun a b => by
      by_cases h1 : p.top a <;> by_cases h2 : p.top b <;> simp [h1, h2]⟩

open Classical in
/-- The list of a deferred edge (Lemma 5.5): indices `j < 7` of the other party's palette that the
other party does not use at the endpoints and that no own matching edge at an endpoint uses. -/
noncomputable def dlist (o' : ℕ) (q : Info V) (e : Sym2 V) : Finset ℕ :=
  (range 7).filter fun j => ∀ x ∈ e, q.used7 x j = false ∧
    ∀ y, p.M.Adj x y → p.mcol o' q s(x, y) ≠ o' + j

open Classical in
/-- The greedy colouring of the deferred graph from the lists `dlist` (indices into the other
party's palette). -/
noncomputable def dcol (o' : ℕ) (q : Info V) : Sym2 V → ℕ :=
  if h : ∃ c : Sym2 V → ℕ, (∀ ⦃u v : V⦄, p.D.Adj u v → c s(u, v) ∈ p.dlist o' q s(u, v)) ∧
      p.D.IsEdgeColoring c then h.choose else fun _ => 0

open Classical in
/-- The output of the party with plan `p`, own palette offset `o`, other palette offset `o'`,
having received the message `q`. -/
noncomputable def color (o o' : ℕ) (q : Info V) : Sym2 V → ℕ := fun e =>
  if e ∈ p.R'.edgeSet then o + p.col e
  else if e ∈ p.M.edgeSet then p.mcol o' q e else o' + p.dcol o' q e

variable {o o' : ℕ} {q : Info V}

lemma color_R' {u v : V} (h : p.R'.Adj u v) : p.color o o' q s(u, v) = o + p.col s(u, v) := by
  simp [color, h]

variable [Finite V] (hX : ∀ v, (X.neighborSet v).ncard ≤ Δ)
include hX

lemma color_M {u v : V} (h : p.M.Adj u v) : p.color o o' q s(u, v) = p.mcol o' q s(u, v) := by
  have : ¬ p.R'.Adj u v := fun h' => p.R'_not_M hX h' h
  simp [color, h, this]

lemma color_D {u v : V} (h : p.D.Adj u v) : p.color o o' q s(u, v) = o' + p.dcol o' q s(u, v) := by
  have h1 : ¬ p.R'.Adj u v := p.D_not_R' hX h
  have h2 : ¬ p.M.Adj u v := p.D_not_M hX h
  simp [color, h1, h2]

lemma mcol_of_not_top {v w : V} (h : p.M.Adj v w) (hv : ¬ p.top v) :
    p.mcol o' q s(v, w) = matchColor Δ o' q v := by
  rcases p.top_iff_ne_top hX h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact absurd h1 hv
  · simp [mcol, h1, hv]

/-- The two vertices of a deferred edge see at most 4 forbidden indices, so the list has at least
3 entries (Lemma 5.5). -/
lemma three_le_card_dlist {a b : V}
    (hq : ∀ x ∈ ({a, b} : Finset V), #((range 7).filter fun j => q.used7 x j = true) ≤ 1) :
    3 ≤ #(p.dlist o' q s(a, b)) := by
  classical
  let S : V → Finset ℕ := fun x => (range 7).filter fun j => q.used7 x j = true
  let T : V → Finset ℕ := fun x => (range 7).filter fun j => ∃ y, p.M.Adj x y ∧ p.mcol o' q s(x, y) = o' + j
  have hT : ∀ x, #(T x) ≤ 1 := fun x => by
    refine Finset.card_le_one.mpr fun j hj j' hj' => ?_
    obtain ⟨y, hy, hjy⟩ := (mem_filter.mp hj).2
    obtain ⟨y', hy', hjy'⟩ := (mem_filter.mp hj').2
    rw [p.M_unique hX hy hy'] at hjy
    omega
  have hsub : range 7 \ (S a ∪ S b ∪ T a ∪ T b) ⊆ p.dlist o' q s(a, b) := by
    intro j hj
    simp only [mem_sdiff, mem_union, not_or] at hj
    obtain ⟨hj7, ⟨⟨hSa, hSb⟩, hTa⟩, hTb⟩ := hj
    refine mem_filter.mpr ⟨hj7, fun x hx => ?_⟩
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · refine ⟨?_, fun y hy he => hTa (mem_filter.mpr ⟨hj7, y, hy, he⟩)⟩
      by_contra h; exact hSa (mem_filter.mpr ⟨hj7, by simpa using h⟩)
    · refine ⟨?_, fun y hy he => hTb (mem_filter.mpr ⟨hj7, y, hy, he⟩)⟩
      by_contra h; exact hSb (mem_filter.mpr ⟨hj7, by simpa using h⟩)
  have h1 := card_le_card hsub
  have h2 := le_card_sdiff (S a ∪ S b ∪ T a ∪ T b) (range 7)
  have h3 : #(S a ∪ S b ∪ T a ∪ T b) ≤ 4 := by
    have : #(S a) ≤ 1 := hq a (by simp)
    have : #(S b) ≤ 1 := hq b (by simp)
    have := hT a; have := hT b
    calc #(S a ∪ S b ∪ T a ∪ T b) ≤ #(S a ∪ S b ∪ T a) + #(T b) := card_union_le _ _
      _ ≤ #(S a ∪ S b) + #(T a) + #(T b) := by gcongr; exact card_union_le _ _
      _ ≤ #(S a) + #(S b) + #(T a) + #(T b) := by gcongr; exact card_union_le _ _
      _ ≤ 4 := by omega
  simp only [card_range] at h2
  omega

/-- If the received message is "good" at the deferred vertices, the deferred graph is coloured
properly from its lists. -/
lemma dcol_spec
    (hq : ∀ x, (∃ y, p.D.Adj x y) → #((range 7).filter fun j => q.used7 x j = true) ≤ 1) :
    (∀ ⦃u v : V⦄, p.D.Adj u v → p.dcol o' q s(u, v) ∈ p.dlist o' q s(u, v)) ∧
      p.D.IsEdgeColoring (p.dcol o' q) := by
  have hex : ∃ c : Sym2 V → ℕ, (∀ ⦃u v : V⦄, p.D.Adj u v → c s(u, v) ∈ p.dlist o' q s(u, v)) ∧
      p.D.IsEdgeColoring c := by
    refine exists_listEdgeColoring p.D _ fun a b hab => ?_
    have := p.three_le_card_dlist (o' := o') hX (a := a) (b := b) (fun x hx => by
      rcases mem_insert.mp hx with rfl | hx
      · exact hq x ⟨b, hab⟩
      · rw [mem_singleton.mp hx]; exact hq b ⟨a, hab.symm⟩)
    have := p.D_le_two hX a; have := p.D_le_two hX b
    omega
  unfold dcol
  rw [dite_eq_left hex]
  exact hex.choose_spec

end Plan

/-! ### The two-party setting -/

section TwoParty

variable [Finite V] {Δ : ℕ} {X Y : SimpleGraph V}

/-- Palettes: `o, o'` are `0, Δ - 1` in some order. -/
def Offsets (Δ o o' : ℕ) : Prop := (o = 0 ∧ o' = Δ - 1) ∨ (o = Δ - 1 ∧ o' = 0)

lemma Offsets.symm {o o' : ℕ} (h : Offsets Δ o o') : Offsets Δ o' o := by
  unfold Offsets at *; tauto

variable (hXY : Disjoint X Y) (hdeg : ∀ v, ((X ⊔ Y).neighborSet v).ncard ≤ Δ)

include hXY hdeg in
lemma deg_add_le (v : V) : (X.neighborSet v).ncard + (Y.neighborSet v).ncard ≤ Δ := by
  rw [← ncard_neighborSet_sup hXY]; exact hdeg v

include hXY hdeg in
lemma deg_left_le (v : V) : (X.neighborSet v).ncard ≤ Δ := by
  have := deg_add_le hXY hdeg v; omega

include hXY hdeg in
lemma deg_right_le (v : V) : (Y.neighborSet v).ncard ≤ Δ := by
  have := deg_add_le hXY hdeg v; omega

include hXY hdeg in
lemma pos_ncard_of_adj {v w : V} (h : Y.Adj v w) : 0 < (Y.neighborSet v).ncard :=
  (Set.ncard_pos (Set.toFinite _)).mpr ⟨w, h⟩

variable (p : Plan Δ X) (p' : Plan Δ Y)

include hXY hdeg in
/-- The partner's message is good at the deferred vertices: a deferred vertex has degree
`≥ Δ - 1` in its own graph, so at most one edge (hence one used colour) in the other graph. -/
lemma info_good {x : V} (hx : ∃ y, p.D.Adj x y) :
    #((range 7).filter fun j => p'.info.used7 x j = true) ≤ 1 := by
  classical
  obtain ⟨y, hy⟩ := hx
  have hX := deg_left_le hXY hdeg
  have hY := deg_right_le (X := X) (Y := Y) hXY hdeg
  have h1 := p.D_deg hX hy
  have h2 := deg_add_le hXY hdeg x
  have hsub : (range 7).filter (fun j => p'.info.used7 x j = true) ⊆
      (Set.toFinite (p'.R'.neighborSet x)).toFinset.image fun w => p'.col s(x, w) := by
    intro j hj
    simp only [Plan.info, mem_filter, decide_eq_true_eq] at hj
    obtain ⟨-, -, w, hw, rfl⟩ := hj
    exact mem_image.mpr ⟨w, by simpa using hw, rfl⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ #((Set.toFinite (p'.R'.neighborSet x)).toFinset) := card_image_le
    _ = (p'.R'.neighborSet x).ncard := (Set.ncard_eq_toFinset_card _ _).symm
    _ ≤ (Y.neighborSet x).ncard := p'.ncard_R'_le hY x
    _ ≤ 1 := by omega

/-- The partner's matching colour lies in `o' + [0, Δ - 1)` or is the special colour. -/
lemma matchColor_cases {o' : ℕ} (v : V) :
    (p'.info.cov v = true ∧ p'.info.high v = false ∧
      matchColor Δ o' p'.info v = o' + p'.cs.getD (p'.lvl v) 0 ∧
      p'.cs.getD (p'.lvl v) 0 < Δ - 1 ∧
      p'.R'.EdgeColorMissing p'.col v (p'.cs.getD (p'.lvl v) 0)) ∨
    matchColor Δ o' p'.info v = 2 * Δ - 2 := by
  unfold matchColor
  split_ifs with h
  · left
    have hlow : 2 * (Y.neighborSet v).ncard ≤ Δ := by
      have := h.2; simp only [Plan.info, decide_eq_false_iff_not] at this; omega
    obtain ⟨-, h2, h3⟩ := p'.cover' hlow
    exact ⟨h.1, h.2, rfl, h2, h3⟩
  · right; rfl

variable {o o' : ℕ} (hoo : Offsets Δ o o') (hΔ : 8 ≤ Δ)

include hXY hdeg hoo hΔ in
/-- **Internal correctness**: one party's output is a proper `(2Δ - 1)`-edge colouring of its own
edges. -/
theorem color_proper : X.IsProperEdgeColoring (p.color o o' p'.info) (2 * Δ - 1) := by
  classical
  have hX := deg_left_le hXY hdeg
  have hcol := p.col_proper'
  have hD := p.dcol_spec (o' := o') hX (fun x hx => info_good hXY hdeg p p' hx)
  -- bound for the matching colours
  have hmc : ∀ v, matchColor Δ o' p'.info v < 2 * Δ - 1 ∧
      (matchColor Δ o' p'.info v = 2 * Δ - 2 ∨
        ∃ c < Δ - 1, matchColor Δ o' p'.info v = o' + c) := fun v => by
    rcases matchColor_cases p' (o' := o') v with ⟨-, -, h, hc, -⟩ | h
    · rw [h]; unfold Offsets at hoo; exact ⟨by omega, Or.inr ⟨_, hc, rfl⟩⟩
    · rw [h]; exact ⟨by omega, Or.inl rfl⟩
  have hMcol : ∀ ⦃u v⦄, p.M.Adj u v → p.mcol o' p'.info s(u, v) < 2 * Δ - 1 ∧
      (p.mcol o' p'.info s(u, v) = 2 * Δ - 2 ∨ ∃ c < Δ - 1, p.mcol o' p'.info s(u, v) = o' + c) :=
    fun u v h => by
      rcases p.top_iff_ne_top hX h with ⟨-, h2⟩ | ⟨-, h2⟩
      · rw [Sym2.eq_swap, p.mcol_of_not_top hX h.symm h2]; exact hmc v
      · rw [p.mcol_of_not_top hX h h2]; exact hmc u
  have hdl : ∀ ⦃u v⦄, p.D.Adj u v → p.dcol o' p'.info s(u, v) < 7 := fun u v h =>
    mem_range.mp (mem_filter.mp (hD.1 h)).1
  unfold Offsets at hoo
  refine ⟨fun u v huv => ?_, fun u v w huv huw he => ?_⟩
  · rcases p.trichotomy hX huv with h | h | h
    · rw [p.color_R' h]; have := hcol.1 h; omega
    · rw [p.color_M hX h]; exact (hMcol h).1
    · rw [p.color_D hX h]; have := hdl h; omega
  · rcases p.trichotomy hX huv with h1 | h1 | h1 <;> rcases p.trichotomy hX huw with h2 | h2 | h2
    · rw [p.color_R' h1, p.color_R' h2] at he; exact hcol.2 h1 h2 (by omega)
    · rw [p.color_R' h1, p.color_M hX h2] at he
      have := hcol.1 h1
      rcases (hMcol h2).2 with h | ⟨c, hc, h⟩ <;> omega
    · rw [p.color_R' h1, p.color_D hX h2] at he
      have := hcol.1 h1; have := hdl h2; omega
    · rw [p.color_M hX h1, p.color_R' h2] at he
      have := hcol.1 h2
      rcases (hMcol h1).2 with h | ⟨c, hc, h⟩ <;> omega
    · exact p.M_unique hX h1 h2
    · rw [p.color_M hX h1, p.color_D hX h2] at he
      have hl := hD.1 h2
      have := hdl h2
      rcases (hMcol h1).2 with h | ⟨c, hc, h⟩
      · omega
      · exact absurd he (((mem_filter.mp hl).2 u (Sym2.mem_mk_left _ _)).2 v h1)
    · rw [p.color_D hX h1, p.color_R' h2] at he
      have := hcol.1 h2; have := hdl h1; omega
    · rw [p.color_D hX h1, p.color_M hX h2] at he
      have hl := hD.1 h1
      have := hdl h1
      rcases (hMcol h2).2 with h | ⟨c, hc, h⟩
      · omega
      · exact absurd he.symm (((mem_filter.mp hl).2 u (Sym2.mem_mk_left _ _)).2 w h2)
    · rw [p.color_D hX h1, p.color_D hX h2] at he
      exact hD.2 h1 h2 (by omega)

/-! ### Cross correctness: an edge of one party and an edge of the other at a common vertex -/

include hXY hdeg in
lemma not_top_of_adj_right {v w' : V} (h : Y.Adj v w') : ¬ p.top v := fun ht => by
  have h1 := p.top_ncard (deg_left_le hXY hdeg) ht
  have h2 := deg_add_le hXY hdeg v
  have h3 := pos_ncard_of_adj hXY hdeg h
  omega

include hXY hdeg hoo hΔ in
lemma cross_R'_R' {v w w' : V} (h1 : p.R'.Adj v w) (h2 : p'.R'.Adj v w') :
    p.color o o' p'.info s(v, w) ≠ p'.color o' o p.info s(v, w') := by
  rw [p.color_R' h1, p'.color_R' h2]
  have := p.col_proper'.1 h1; have := p'.col_proper'.1 h2
  unfold Offsets at hoo; omega

include hXY hdeg hoo hΔ in
lemma cross_R'_M {v w w' : V} (h1 : p.R'.Adj v w) (h2 : p'.M.Adj v w') :
    p.color o o' p'.info s(v, w) ≠ p'.color o' o p.info s(v, w') := by
  have hX := deg_left_le hXY hdeg
  have hY := deg_right_le hXY hdeg
  have hnt : ¬ p'.top v := not_top_of_adj_right (Y := X) hXY.symm
    (fun x => by rw [sup_comm]; exact hdeg x) p' ((p.R'_le_X hX) h1)
  rw [p.color_R' h1, p'.color_M hY h2, p'.mcol_of_not_top hY h2 hnt]
  have := p.col_proper'.1 h1
  rcases matchColor_cases p (o' := o) v with ⟨-, -, h, -, hmiss⟩ | h
  · rw [h]; exact fun he => hmiss h1 (by omega)
  · rw [h]; unfold Offsets at hoo; omega

include hXY hdeg hoo hΔ in
lemma cross_R'_D {v w w' : V} (h1 : p.R'.Adj v w) (h2 : p'.D.Adj v w') :
    p.color o o' p'.info s(v, w) ≠ p'.color o' o p.info s(v, w') := by
  classical
  have hY := deg_right_le hXY hdeg
  have hD := p'.dcol_spec (o' := o) hY (fun x hx => info_good (X := Y) (Y := X) hXY.symm
    (fun x => by rw [sup_comm]; exact hdeg x) p' p hx)
  rw [p.color_R' h1, p'.color_D hY h2]
  have hl := mem_filter.mp (hD.1 h2)
  set j := p'.dcol o p.info s(v, w') with hj
  have h7 := mem_range.mp hl.1
  have hu := (hl.2 v (Sym2.mem_mk_left _ _)).1
  have hu' : ¬ (j < 7 ∧ ∃ x, p.R'.Adj v x ∧ p.col s(v, x) = j) := by
    simpa [Plan.info] using hu
  intro he
  exact hu' ⟨h7, w, h1, by omega⟩

include hXY hdeg hoo hΔ in
lemma cross_M_M {v w w' : V} (h1 : p.M.Adj v w) (h2 : p'.M.Adj v w') :
    p.color o o' p'.info s(v, w) ≠ p'.color o' o p.info s(v, w') := by
  have hX := deg_left_le hXY hdeg
  have hY := deg_right_le hXY hdeg
  have hnt : ¬ p.top v := not_top_of_adj_right hXY hdeg p ((p'.M_le_X hY) h2)
  have hnt' : ¬ p'.top v := not_top_of_adj_right (Y := X) hXY.symm
    (fun x => by rw [sup_comm]; exact hdeg x) p' ((p.M_le_X hX) h1)
  rw [p.color_M hX h1, p.mcol_of_not_top hX h1 hnt, p'.color_M hY h2,
    p'.mcol_of_not_top hY h2 hnt']
  have hsum := deg_add_le hXY hdeg v
  unfold Offsets at hoo
  rcases matchColor_cases p' (o' := o') v with ⟨-, -, h, hc, -⟩ | h <;>
    rcases matchColor_cases p (o' := o) v with ⟨-, -, h', hc', -⟩ | h'
  · rw [h, h']; omega
  · rw [h, h']; omega
  · rw [h, h']; omega
  · -- both special: then both degrees at `v` exceed `Δ / 2`
    exfalso
    have hcov : p.info.cov v = true := by simp only [Plan.info, decide_eq_true_eq]; exact ⟨w, h1⟩
    have hcov' : p'.info.cov v = true := by
      simp only [Plan.info, decide_eq_true_eq]; exact ⟨w', h2⟩
    unfold matchColor at h h'
    have hh : p'.info.high v = true := by
      by_contra hc; simp only [Bool.not_eq_true] at hc; rw [ite_eq_left ⟨hcov', hc⟩] at h
      simp only [Plan.info] at h
      have := p'.cover' (v := v) (by simp [Plan.info] at hc; omega); omega
    have hh' : p.info.high v = true := by
      by_contra hc; simp only [Bool.not_eq_true] at hc; rw [ite_eq_left ⟨hcov, hc⟩] at h'
      simp only [Plan.info] at h'
      have := p.cover' (v := v) (by simp [Plan.info] at hc; omega); omega
    simp only [Plan.info, decide_eq_true_eq] at hh hh'
    omega

include hXY hdeg hoo hΔ in
lemma cross_M_D {v w w' : V} (h1 : p.M.Adj v w) (h2 : p'.D.Adj v w') :
    p.color o o' p'.info s(v, w) ≠ p'.color o' o p.info s(v, w') := by
  classical
  have hX := deg_left_le hXY hdeg
  have hY := deg_right_le hXY hdeg
  have hD := p'.dcol_spec (o' := o) hY (fun x hx => info_good (X := Y) (Y := X) hXY.symm
    (fun x => by rw [sup_comm]; exact hdeg x) p' p hx)
  have hnt : ¬ p.top v := not_top_of_adj_right hXY hdeg p ((p'.D_le_X hY) h2)
  rw [p.color_M hX h1, p.mcol_of_not_top hX h1 hnt, p'.color_D hY h2]
  have h7 := mem_range.mp (mem_filter.mp (hD.1 h2)).1
  unfold Offsets at hoo
  rcases matchColor_cases p' (o' := o') v with ⟨-, -, h, hc, -⟩ | h <;> rw [h] <;> omega

include hXY hdeg hoo hΔ in
lemma cross_D_D {v w w' : V} (h1 : p.D.Adj v w) (h2 : p'.D.Adj v w') :
    p.color o o' p'.info s(v, w) ≠ p'.color o' o p.info s(v, w') := by
  classical
  have hX := deg_left_le hXY hdeg
  have hY := deg_right_le hXY hdeg
  have hD := p.dcol_spec (o' := o') hX (fun x hx => info_good hXY hdeg p p' hx)
  have hD' := p'.dcol_spec (o' := o) hY (fun x hx => info_good (X := Y) (Y := X) hXY.symm
    (fun x => by rw [sup_comm]; exact hdeg x) p' p hx)
  rw [p.color_D hX h1, p'.color_D hY h2]
  have h7 := mem_range.mp (mem_filter.mp (hD.1 h1)).1
  have h7' := mem_range.mp (mem_filter.mp (hD'.1 h2)).1
  unfold Offsets at hoo; omega

include hXY hdeg hoo hΔ in
/-- **Cross correctness.** -/
theorem cross {v w w' : V} (h1 : X.Adj v w) (h2 : Y.Adj v w') :
    p.color o o' p'.info s(v, w) ≠ p'.color o' o p.info s(v, w') := by
  have hX := deg_left_le hXY hdeg
  have hY := deg_right_le hXY hdeg
  have hdeg' : ∀ x, ((Y ⊔ X).neighborSet x).ncard ≤ Δ := fun x => by rw [sup_comm]; exact hdeg x
  rcases p.trichotomy hX h1 with a | a | a <;> rcases p'.trichotomy hY h2 with b | b | b
  · exact cross_R'_R' hXY hdeg p p' hoo hΔ a b
  · exact cross_R'_M hXY hdeg p p' hoo hΔ a b
  · exact cross_R'_D hXY hdeg p p' hoo hΔ a b
  · exact (cross_R'_M hXY.symm hdeg' p' p hoo.symm hΔ b a).symm
  · exact cross_M_M hXY hdeg p p' hoo hΔ a b
  · exact cross_M_D hXY hdeg p p' hoo hΔ a b
  · exact (cross_R'_D hXY.symm hdeg' p' p hoo.symm hΔ b a).symm
  · exact (cross_M_D hXY.symm hdeg' p' p hoo.symm hΔ b a).symm
  · exact cross_D_D hXY hdeg p p' hoo hΔ a b

end TwoParty

end Podc.RoundEfficientColoring
