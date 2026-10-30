import Papers.PODC2020.PowerGraphApproximation.UnweightedLB
import Cslib.Computability.Distributed.Congest.Gather

/-!
# Theorems 20 and 22 for algorithms that are only correct on connected networks

`G_{x,y}` and `H_{x,y}` are disconnected exactly when `x` and `y` are both all-ones (no edges
between the two layers; `H_disconnected`); for `k ≥ 2` they are connected otherwise
(`H_connected`). A CONGEST algorithm is normally only required to work on connected networks, so
we prove the lower bounds for algorithms that are correct on the connected members of the family
only. This needs a variant of the fooling-set bound for `¬DISJ` in which the single input pair
`(1, 1)` is excluded (`not_disj_lowerBound_of_ne_one`; it holds for `K ≥ 2`).
-/

namespace Podc.PowerGraphApproximation.LowerBound

open Finset SimpleGraph Cslib.Congest Cslib.CommunicationComplexity Protocol

-- CSLib candidate (Cslib/Computability/CommunicationComplexity/Protocol.lean)
/-- Robust form of `CC(¬DISJ_K) ≥ K` (for `K ≥ 2`): a protocol that answers "the sets intersect"
correctly on all inputs except `x = y = 1` (all-ones) still needs `K` bits. -/
theorem protocol_not_disj_lowerBound_of_ne_one {ι : Type*} [Fintype ι]
    {P : Protocol (ι → Bool) (ι → Bool) Bool} {c : ℕ}
    (hP : ∀ x y, ((∃ i, x i = false) ∨ ∃ i, y i = false) → P.eval x y = !disj x y)
    (hc : P.CostLE c) (hι : 2 ≤ Fintype.card ι) : Fintype.card ι ≤ c := by
  classical
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hne
  let S : Finset ((ι → Bool) × (ι → Bool)) :=
    (univ.filter fun x : ι → Bool => x ≠ fun _ => false).image fun x => (x, fun i => !x i)
  have hinj : Function.Injective fun x : ι → Bool => (x, fun i => !x i) :=
    fun a b h => (Prod.ext_iff.1 h).1
  have hcard : S.card = 2 ^ Fintype.card ι - 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.filter_ne' , Finset.card_erase_of_mem
      (mem_univ _), Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hfool : IsFooling P.eval false S := by
    refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
      have hnz : (∃ i, x i = false) ∨ ∃ i, (fun i => !x i) i = false := by
        cases h : x i₀
        · exact Or.inl ⟨i₀, h⟩
        · exact Or.inr ⟨i₀, by simp [h]⟩
      rw [hP x _ hnz]
      simp [disj]
    · obtain ⟨x, hx0, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨x', hx'0, rfl⟩ := Finset.mem_image.1 ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0 hx'0
      have hx : x ≠ x' := fun h => hst (by rw [h])
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      -- `x' ≠ 0` gives an index where `!x'` is `false`
      obtain ⟨j', hj'⟩ : ∃ j, x' j = true := by
        by_contra h; push Not at h; exact hx'0 (funext fun j => by simpa using h j)
      obtain ⟨j, hj⟩ : ∃ j, x j = true := by
        by_contra h; push Not at h; exact hx0 (funext fun j => by simpa using h j)
      cases hxi : x i <;> cases hx'i : x' i <;> rw [hxi, hx'i] at hi <;> simp at hi
      · right
        rw [hP x' _ (Or.inr ⟨j, by simp [hj]⟩)]
        intro h
        simp only [disj, Bool.not_eq_false', decide_eq_true_eq] at h
        exact h i ⟨hx'i, by simp [hxi]⟩
      · left
        rw [hP x _ (Or.inr ⟨j', by simp [hj']⟩)]
        intro h
        simp only [disj, Bool.not_eq_false', decide_eq_true_eq] at h
        exact h i ⟨hxi, by simp [hx'i]⟩
  have h1 := card_le_of_fooling P c false S hc hfool
  rw [hcard] at h1
  by_contra hlt
  push Not at hlt
  have h2 : 2 ^ c ≤ 2 ^ (Fintype.card ι - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h4 : 2 ≤ 2 ^ (Fintype.card ι - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

-- CSLib candidate (Cslib/Computability/Distributed/Congest/LowerBound.lean)
/-- Theorem 1.1 for the complement of set disjointness, for algorithms that are only required to
be correct on the graphs `G x y` with `x ≠ 1` or `y ≠ 1` (e.g. because `G 1 1` is disconnected),
`K ≥ 2`. -/
theorem family_not_disj_lowerBound_of_ne_one {V I σ : Type*} {B : ℕ} {ι : Type*}
    [Fintype ι] [Finite V] (F : LBFamily (ι → Bool) (ι → Bool) V I)
    [∀ x y, DecidableRel (F.G x y).Adj] (A : Algorithm V I σ B) (T : ℕ)
    (hA : ∀ x y, ((∃ i, x i = false) ∨ ∃ i, y i = false) →
      (A.Accepts (F.G x y) (F.inp x y) T ↔ disj x y = false))
    (hι : 2 ≤ Fintype.card ι) :
    Fintype.card ι ≤ T * (2 * (F.Ecut.card * B)) + 2 := by
  have := Fintype.ofFinite V
  obtain ⟨P, hc, hP⟩ := F.simulation A T
  refine protocol_not_disj_lowerBound_of_ne_one (P := P) (fun x y hxy => ?_) hc hι
  rw [hP x y]
  cases h : disj x y <;> simp [hA x y hxy, h]

/-! ### Connectivity of `H_{x,y}` -/

variable {L : ℕ}

section Conn

variable {x y : Idx L × Idx L → Bool}

/-- The anchor row of clique `(s, ℓ)`. -/
def anchor (s ℓ : Bool) : GV L := .row s ℓ fun _ => true

lemma row_reach_anchor (s ℓ : Bool) (i : Idx L) :
    (G x y).Reachable (.row s ℓ i) (anchor s ℓ) := by
  by_cases hi : i = fun _ => true
  · subst hi; rfl
  · exact Adj.reachable (by simp [anchor, hi])

lemma reach_anchor (v : GV L) : ∃ s ℓ, (G x y).Reachable v (anchor s ℓ) := by
  rcases v with ⟨s, ℓ, i⟩ | ⟨s, ℓ, h, b⟩
  · exact ⟨s, ℓ, row_reach_anchor s ℓ i⟩
  · refine ⟨s, ℓ, (Adj.reachable (v := .row s ℓ fun _ => b) (by simp)).trans
      (row_reach_anchor _ _ _)⟩

lemma anchor_sides (hL : 1 ≤ L) (ℓ : Bool) :
    (G x y).Reachable (anchor false ℓ) (anchor true ℓ) := by
  let h0 : Fin L := ⟨0, hL⟩
  have e1 : (G x y).Adj (anchor false ℓ) (.bit false ℓ h0 true) := by simp [anchor]
  have e2 : (G x y).Adj (.bit false ℓ h0 true) (.bit true ℓ h0 false) := by simp
  have e3 : (G x y).Adj (.bit true ℓ h0 false) (.row true ℓ fun _ => false) := by simp
  exact e1.reachable.trans (e2.reachable.trans (e3.reachable.trans (row_reach_anchor _ _ _)))

lemma anchor_layers (hxy : (∃ p, x p = false) ∨ ∃ p, y p = false) :
    ∃ s, (G x y).Reachable (anchor s false) (anchor s true) := by
  rcases hxy with ⟨⟨i, j⟩, hp⟩ | ⟨⟨i, j⟩, hp⟩
  · refine ⟨false, (row_reach_anchor false false i).symm.trans
      ((Adj.reachable (v := .row false true j) ?_).trans (row_reach_anchor _ _ _))⟩
    simp [mat, hp]
  · refine ⟨true, (row_reach_anchor true false i).symm.trans
      ((Adj.reachable (v := .row true true j) ?_).trans (row_reach_anchor _ _ _))⟩
    simp [mat, hp]

/-- For `k ≥ 2`, `G_{x,y}` is connected unless `x` and `y` are both all-ones. -/
theorem G_connected (hL : 1 ≤ L) (hxy : (∃ p, x p = false) ∨ ∃ p, y p = false) :
    (G x y).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨anchor false false, fun v => ?_⟩
  obtain ⟨s, ℓ, hv⟩ := reach_anchor (x := x) (y := y) v
  refine Reachable.trans ?_ hv.symm
  have hA : ∀ s ℓ, (G x y).Reachable (anchor false false) (anchor s ℓ) := by
    obtain ⟨s0, h0⟩ := anchor_layers hxy
    have hside : ∀ ℓ, (G x y).Reachable (anchor false ℓ) (anchor true ℓ) := anchor_sides hL
    have hl : (G x y).Reachable (anchor false false) (anchor false true) := by
      cases s0
      · exact h0
      · exact (hside false).trans (h0.trans (hside true).symm)
    intro s ℓ
    cases s <;> cases ℓ
    · rfl
    · exact hl
    · exact hside false
    · exact hl.trans (hside true)
  exact hA s ℓ

lemma reachable_of_sq {V : Type*} {K : SimpleGraph V} {a b : V} (h : (K.power 2).Adj a b) :
    K.Reachable a b := by
  rcases (power_two_adj.1 h).2 with h | ⟨w, h1, h2⟩
  · exact h.reachable
  · exact h1.reachable.trans h2.reachable

/-- Every gadget is attached to some vertex of `G_{x,y}`. -/
lemma exists_att (e : PE L) : ∃ u, att x y e u = true := by
  rcases e with ⟨s, ℓ, i, h⟩ | ⟨ℓ, h, s, s'⟩ | ⟨s, i⟩
  · exact ⟨.row s ℓ i, by simp [att]⟩
  · exact ⟨.bit s ℓ h true, by simp [att]⟩
  · exact ⟨.row s false i, by simp [att]⟩

/-- For `k ≥ 2`, `H_{x,y}` is connected unless `x` and `y` are both all-ones. -/
theorem H_connected (hL : 1 ≤ L) {m : ℕ} [NeZero m]
    (hxy : (∃ p, x p = false) ∨ ∃ p, y p = false) : (H x y m).Connected := by
  have hG := G_connected hL hxy
  have hinl : ∀ u v, (H x y m).Reachable (.inl u) (.inl v) := by
    intro u v
    obtain ⟨p⟩ := hG.preconnected u v
    induction p with
    | nil => rfl
    | cons h _ ih =>
      exact (reachable_of_sq ((attach_sq_inl_iff (m := m) (isSquareTrace x y)).2 h)).trans ih
  have hinr : ∀ e (p : Fin m), (H x y m).Reachable (.inr (e, 0)) (.inr (e, p)) := by
    intro e p
    obtain ⟨p, hp⟩ := p
    induction p with
    | zero => rfl
    | succ q ih =>
      refine (ih (by omega)).trans (Adj.reachable ?_)
      simp [H]
  rw [connected_iff_exists_forall_reachable]
  refine ⟨.inl (anchor false false), fun v => ?_⟩
  rcases v with u | ⟨e, p⟩
  · exact hinl _ _
  · obtain ⟨u, hu⟩ := exists_att (x := x) (y := y) e
    exact (hinl _ u).trans ((Adj.reachable (v := .inr (e, 0)) (by simp [H, hu])).trans
      (hinr e p))

/-- The layer of a vertex of `H_{x,y}` (shared gadgets count as layer 1). -/
def layer {m : ℕ} : HV L m → Bool
  | .inl (.row _ ℓ _) => ℓ
  | .inl (.bit _ ℓ _ _) => ℓ
  | .inr (.rb _ ℓ _ _, _) => ℓ
  | .inr (.cyc ℓ _ _ _, _) => ℓ
  | .inr (.sh _ _, _) => false

set_option linter.unusedSimpArgs false in
/-- If `x` and `y` are both all-ones, `H_{x,y}` is disconnected: no edge joins the two layers. -/
theorem H_disconnected {m : ℕ} [NeZero m] (hx : ∀ p, x p = true) (hy : ∀ p, y p = true) :
    ¬(H x y m).Connected := by
  have hadj : ∀ a b, (H x y m).Adj a b → layer a = layer b := by
    intro a b hab
    rcases a with (⟨s, ℓ, i⟩ | ⟨s, ℓ, h, bb⟩) | ⟨⟨s, ℓ, i, h⟩ | ⟨ℓ, h, s, s'⟩ | ⟨s, i⟩, p⟩ <;>
      rcases b with (⟨t, ℓ', j⟩ | ⟨t, ℓ', h', bb'⟩) | ⟨⟨t, ℓ', j, h'⟩ | ⟨ℓ', h', t, t'⟩ | ⟨t, j⟩, q⟩ <;>
      simp [H, layer, att, mat, hx, hy] at hab ⊢ <;> grind
  intro hc
  obtain ⟨w⟩ := hc.preconnected (.inl (anchor false false)) (.inl (anchor false true))
  have : ∀ a b (w : (H x y m).Walk a b), layer a = layer b := by
    intro a b w
    induction w with
    | nil => rfl
    | cons h _ ih => exact (hadj _ _ h).trans ih
  simpa [layer, anchor] using this _ _ w

end Conn

/-! ### The lower bounds for algorithms correct on connected networks -/

lemma exists_false_of_not_connected {m : ℕ} [NeZero m] {x y : Idx L × Idx L → Bool}
    (hc : (H x y m).Connected) : (∃ p, x p = false) ∨ ∃ p, y p = false := by
  by_contra h
  push Not at h
  exact H_disconnected (fun p => by simpa using h.1 p) (fun p => by simpa using h.2 p) hc

lemma card_idx_ge (hL : 1 ≤ L) : 2 ≤ Fintype.card (Idx L × Idx L) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  nlinarith

/-- **Theorem 20 of [BCMPP20]**, for algorithms that are only correct on connected networks
(`k ≥ 2`): if `A` decides, on every *connected* `H_{x,y}`, whether `H²_{x,y}` has a vertex cover
of weight at most `4(k - 1) + 4 log k`, then `k² ≤ 8 T B log k + 2`. -/
theorem theorem_20_connected (hL : 1 ≤ L) {σ : Type*} {B : ℕ}
    (A : Algorithm (HV L 1) ((HV L 1 → Bool) × ℕ) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool, (H x y 1).Connected →
      (A.Accepts (H x y 1) (fun v => (fun w => decide ((H x y 1).Adj v w), wt v)) T ↔
        ∃ C : Finset (HV L 1), ((H x y 1).power 2).IsVertexCover ↑C ∧
          ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L)) :
    4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := family_not_disj_lowerBound_of_ne_one (wFamily L) A T (fun x y hxy => by
    change A.Accepts (H x y 1) (fun v => (fun w => decide ((H x y 1).Adj v w), wt v)) T ↔ _
    rw [hA x y (H_connected hL hxy)]
    exact weightedPred_iff x y) (card_idx_ge hL)
  rw [show (wFamily L).Ecut = hCut L 1 from rfl, card_hCut] at h
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  calc 4 ^ L ≤ T * (2 * (4 * L * B)) + 2 := h
    _ = T * (8 * L * B) + 2 := by ring

/-- **Theorem 22 of [BCMPP20]**, for algorithms that are only correct on connected networks
(`k ≥ 2`): if `A` decides, on every *connected* `H_{x,y}`, whether `H²_{x,y}` has a vertex cover
of size at most `W + 2(2k + 4k log k + 8 log k)`, then `k² ≤ 8 T B log k + 2`. -/
theorem theorem_22_connected (hL : 1 ≤ L) {σ : Type*} {B : ℕ}
    (A : Algorithm (HV L 3) (HV L 3 → Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx L × Idx L → Bool, (H x y 3).Connected →
      (A.Accepts (H x y 3) (fun v w => decide ((H x y 3).Adj v w)) T ↔
        ∃ C : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C ∧
          C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L))) :
    4 ^ L ≤ T * (8 * L * B) + 2 := by
  have h := family_not_disj_lowerBound_of_ne_one (hFamily L 3) A T (fun x y hxy => by
    change A.Accepts (H x y 3) (fun v w => decide ((H x y 3).Adj v w)) T ↔ _
    rw [hA x y (H_connected hL hxy)]
    exact unweightedPred_iff x y) (card_idx_ge hL)
  rw [hFamily_Ecut, card_hCut] at h
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  calc 4 ^ L ≤ T * (2 * (4 * L * B)) + 2 := h
    _ = T * (8 * L * B) + 2 := by ring

/-! ### Non-vacuity: the hypotheses of the connected versions are satisfiable -/

/-- Precompose the node inputs of an algorithm with `f`. -/
def mapInput {V I J σ : Type*} {B : ℕ} (A : Algorithm V I σ B) (f : J → I) :
    Algorithm V J σ B :=
  { A with init := fun v j => A.init v (f j) }

lemma run_mapInput {V I J σ : Type*} {B : ℕ} (A : Algorithm V I σ B) (f : J → I)
    (K : SimpleGraph V) [DecidableRel K.Adj] (inp : V → J) (t : ℕ) :
    (mapInput A f).run K inp t = A.run K (fun v => f (inp v)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Algorithm.run, ih]; rfl

/-- **Non-vacuity** of `theorem_22_connected`: the full-information gathering algorithm
(`T = n` rounds, `n + n²`-bit messages) decides the predicate on every connected `H_{x,y}`. -/
theorem theorem_22_hyp_satisfiable :
    ∃ (B : ℕ) (A : Algorithm (HV L 3) (HV L 3 → Bool) (Know (HV L 3)) B) (T : ℕ),
      ∀ x y : Idx L × Idx L → Bool, (H x y 3).Connected →
        (A.Accepts (H x y 3) (fun v w => decide ((H x y 3).Adj v w)) T ↔
          ∃ C : Finset (HV L 3), ((H x y 3).power 2).IsVertexCover ↑C ∧
            C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L)) :=
  ⟨_, gatherAlg fun M => ∃ C : Finset (HV L 3),
      ((SimpleGraph.fromRel fun a b => M a b = true).power 2).IsVertexCover ↑C ∧
        C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L),
    Fintype.card (HV L 3), fun x y hc =>
      gather_accepts_graph (H x y 3) (fun K => ∃ C : Finset (HV L 3),
        (K.power 2).IsVertexCover ↑C ∧
          C.card ≤ 4 * (2 ^ L - 1) + 4 * L + 2 * (2 * 2 ^ L + 4 * 2 ^ L * L + 8 * L)) hc⟩

/-- **Non-vacuity** of `theorem_20_connected`: gathering (ignoring the weight inputs, which are
fixed) decides the predicate on every connected `H_{x,y}`. -/
theorem theorem_20_hyp_satisfiable :
    ∃ (B : ℕ) (A : Algorithm (HV L 1) ((HV L 1 → Bool) × ℕ) (Know (HV L 1)) B) (T : ℕ),
      ∀ x y : Idx L × Idx L → Bool, (H x y 1).Connected →
        (A.Accepts (H x y 1) (fun v => (fun w => decide ((H x y 1).Adj v w), wt v)) T ↔
          ∃ C : Finset (HV L 1), ((H x y 1).power 2).IsVertexCover ↑C ∧
            ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L) := by
  refine ⟨_, mapInput (gatherAlg fun M => ∃ C : Finset (HV L 1),
      ((SimpleGraph.fromRel fun a b => M a b = true).power 2).IsVertexCover ↑C ∧
        ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L) Prod.fst,
    Fintype.card (HV L 1), fun x y hc => ?_⟩
  have := gather_accepts_graph (H x y 1) (fun K => ∃ C : Finset (HV L 1),
    (K.power 2).IsVertexCover ↑C ∧ ∑ v ∈ C, wt v ≤ 4 * (2 ^ L - 1) + 4 * L) hc
  rw [← this]
  simp only [Algorithm.Accepts, run_mapInput]
  rfl

end Podc.PowerGraphApproximation.LowerBound
