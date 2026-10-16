import Mathlib

/-!
# Reach sets, the reach conditions and source components of reduced graphs

Graph-theoretic part of Sakavalas–Tseng–Vaidya, *Asynchronous Byzantine Approximate Consensus in
Directed Networks* (PODC 2020), Sections 2–3.

* `Reaches G X a b` — `a ∉ X` and `b` is reachable from `a` in the subgraph induced by `V \ X`.
  The paper's reach set is `reach_v(X) = {u | Reaches G X u v}` (Definition 2).
* `ReachCondIn G F k` — "for all `Fu, Fv` with `|Fu|, |Fv| ≤ k` and `u ∉ F ∪ Fu`, `v ∉ F ∪ Fv`,
  `reach_v(F ∪ Fv) ∩ reach_u(F ∪ Fu) ≠ ∅`". The three conditions of Definition 3 are
  `OneReach` (`k = 0`, all `F`), `TwoReach` (`F = ∅`, `k = f`), `ThreeReach` (all `F`, `k = f`).
* `srcComp G F₁ F₂` — the source component `S_{F₁,F₂}` of the reduced graph (Definitions 5, 6).
* Simple and redundant paths (Section 3) as lists of nodes.
-/

open Finset Relation

-- CSLib candidate (general directed-network / asynchronous Byzantine infrastructure)

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V : Type*} [DecidableEq V]

/-! ## Reachability avoiding a set -/

/-- An edge of the subgraph induced by `V \ X`. -/
def AdjOut (G : Digraph V) (X : Finset V) (a b : V) : Prop := G.Adj a b ∧ a ∉ X ∧ b ∉ X

/-- `Reaches G X a b`: `a ∉ X` and there is a directed path from `a` to `b` in the subgraph of
`G` induced by `V \ X`. -/
def Reaches (G : Digraph V) (X : Finset V) (a b : V) : Prop :=
  a ∉ X ∧ ReflTransGen (AdjOut G X) a b

variable {G : Digraph V}

theorem Reaches.refl {X : Finset V} {a : V} (h : a ∉ X) : Reaches G X a a := ⟨h, .refl⟩

theorem Reaches.notMem_right {X : Finset V} {a b : V} (h : Reaches G X a b) : b ∉ X := by
  obtain ⟨ha, h⟩ := h
  induction h with
  | refl => exact ha
  | tail _ e _ => exact e.2.2

theorem Reaches.trans {X : Finset V} {a b c : V} (h₁ : Reaches G X a b) (h₂ : Reaches G X b c) :
    Reaches G X a c := ⟨h₁.1, h₁.2.trans h₂.2⟩

theorem Reaches.tail {X : Finset V} {a b c : V} (h : Reaches G X a b) (e : G.Adj b c)
    (hc : c ∉ X) : Reaches G X a c := ⟨h.1, h.2.tail ⟨e, h.notMem_right, hc⟩⟩

theorem Reaches.head {X : Finset V} {a b c : V} (e : G.Adj a b) (ha : a ∉ X)
    (h : Reaches G X b c) : Reaches G X a c := ⟨ha, .head ⟨e, ha, h.1⟩ h.2⟩

theorem Reaches.mono {X Y : Finset V} {a b : V} (h : Reaches G Y a b) (hXY : X ⊆ Y) :
    Reaches G X a b :=
  ⟨fun hx => h.1 (hXY hx), ReflTransGen.mono (fun _ _ e => ⟨e.1, fun hx => e.2.1 (hXY hx),
    fun hx => e.2.2 (hXY hx)⟩) _ _ h.2⟩

/-- If every edge into a node of `L` from outside `X` comes from `L`, then everything reaching a
node of `L` while avoiding `X` lies in `L`. -/
theorem Reaches.mem_of_closed {X : Finset V} {L : Set V}
    (hL : ∀ a b, G.Adj a b → a ∉ X → b ∈ L → a ∈ L) {a b : V} (h : Reaches G X a b)
    (hb : b ∈ L) : a ∈ L := by
  obtain ⟨-, h⟩ := h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hb
  | head e _ ih => exact hL _ _ e.1 e.2.1 ih

/-! ## The reach conditions (Definition 3) -/

/-- The reach condition with "global" fault set `F` and local suspect sets of size `≤ k`:
for every `u ∉ F ∪ Fu`, `v ∉ F ∪ Fv` with `|Fu|, |Fv| ≤ k`,
`reach_v(F ∪ Fv) ∩ reach_u(F ∪ Fu) ≠ ∅`. -/
def ReachCondIn (G : Digraph V) (F : Finset V) (k : ℕ) : Prop :=
  ∀ (Fu Fv : Finset V) (u v : V), Fu.card ≤ k → Fv.card ≤ k → u ∉ F ∪ Fu → v ∉ F ∪ Fv →
    ∃ w, Reaches G (F ∪ Fv) w v ∧ Reaches G (F ∪ Fu) w u

/-- **1-reach** (Definition 3): for every `F` with `|F| ≤ f` and `u, v ∉ F`,
`reach_u(F) ∩ reach_v(F) ≠ ∅`. -/
def OneReach (G : Digraph V) (f : ℕ) : Prop :=
  ∀ (F : Finset V) (u v : V), F.card ≤ f → u ∉ F → v ∉ F →
    ∃ w, Reaches G F w v ∧ Reaches G F w u

/-- **2-reach** (Definition 3): for every `Fu, Fv` with `|Fu|, |Fv| ≤ f`, `u ∉ Fu`, `v ∉ Fv`,
`reach_v(Fv) ∩ reach_u(Fu) ≠ ∅`. -/
def TwoReach (G : Digraph V) (f : ℕ) : Prop :=
  ∀ (Fu Fv : Finset V) (u v : V), Fu.card ≤ f → Fv.card ≤ f → u ∉ Fu → v ∉ Fv →
    ∃ w, Reaches G Fv w v ∧ Reaches G Fu w u

/-- **3-reach** (Definition 3): for every `F, Fu, Fv` with `|F|, |Fu|, |Fv| ≤ f`, `u ∉ F ∪ Fu`,
`v ∉ F ∪ Fv`, `reach_v(F ∪ Fv) ∩ reach_u(F ∪ Fu) ≠ ∅`. -/
def ThreeReach (G : Digraph V) (f : ℕ) : Prop :=
  ∀ (F Fu Fv : Finset V) (u v : V), F.card ≤ f → Fu.card ≤ f → Fv.card ≤ f → u ∉ F ∪ Fu →
    v ∉ F ∪ Fv → ∃ w, Reaches G (F ∪ Fv) w v ∧ Reaches G (F ∪ Fu) w u

theorem oneReach_iff {f : ℕ} : OneReach G f ↔ ∀ F : Finset V, F.card ≤ f → ReachCondIn G F 0 := by
  constructor
  · intro h F hF Fu Fv u v hu hv hu' hv'
    rw [Nat.le_zero, card_eq_zero] at hu hv
    subst hu hv
    simpa using h F u v hF (by simpa using hu') (by simpa using hv')
  · intro h F u v hF hu hv
    simpa using h F hF ∅ ∅ u v (by simp) (by simp) (by simpa using hu) (by simpa using hv)

theorem twoReach_iff {f : ℕ} : TwoReach G f ↔ ReachCondIn G ∅ f := by
  simp [TwoReach, ReachCondIn]

theorem threeReach_iff {f : ℕ} :
    ThreeReach G f ↔ ∀ F : Finset V, F.card ≤ f → ReachCondIn G F f := by
  constructor
  · intro h F hF Fu Fv u v hu hv hu' hv'; exact h F Fu Fv u v hF hu hv hu' hv'
  · intro h F Fu Fv u v hF hu hv hu' hv'; exact h F hF Fu Fv u v hu hv hu' hv'

/-! ## Small networks -/

section Card

variable [Fintype V]

/-- Every graph on at most one node satisfies 3-reach (both nodes of the condition coincide). -/
theorem threeReach_of_card_le_one {f : ℕ} (h : Fintype.card V ≤ 1) : ThreeReach G f := by
  intro F Fu Fv u v _ _ _ hu hv
  have huv : u = v := Fintype.card_le_one_iff.mp h u v
  subst huv
  exact ⟨u, Reaches.refl hv, Reaches.refl hu⟩

/-- In any graph with at least two nodes, 3-reach forces `n > 3f`. -/
theorem ThreeReach.three_mul_lt_card {f : ℕ} (hG : ThreeReach G f)
    (hn : 2 ≤ Fintype.card V) : 3 * f < Fintype.card V := by
  by_contra hcon
  push Not at hcon
  set n := Fintype.card V
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < n)
  set W : Finset V := (univ.erase u).erase v
  have hW : W.card = n - 2 := by
    rw [card_erase_of_mem (by simp [huv.symm]), card_erase_of_mem (mem_univ _), card_univ]; omega
  have hf : 1 ≤ f := by omega
  obtain ⟨A, hAW, hA⟩ := exists_subset_card_eq (s := W) (n := min (f - 1) (n - 2)) (by omega)
  obtain ⟨B, hBW, hB⟩ := exists_subset_card_eq (s := W \ A) (n := min (f - 1) (n - 2 - A.card))
    (by rw [card_sdiff_of_subset hAW]; omega)
  set F := (W \ A) \ B
  have hFc : F.card ≤ f := by
    rw [card_sdiff_of_subset hBW, card_sdiff_of_subset hAW]; omega
  have hu : u ∉ F ∪ insert v A := by
    simp only [mem_union, mem_insert, F, W, mem_sdiff, mem_erase]
    refine fun h => ?_
    rcases h with h | h | h
    · exact h.1.1.2.1 rfl
    · exact huv h
    · have := hAW h; simp [W] at this
  have hv : v ∉ F ∪ insert u B := by
    simp only [mem_union, mem_insert, F, W, mem_sdiff, mem_erase]
    refine fun h => ?_
    rcases h with h | h | h
    · exact h.1.1.1 rfl
    · exact huv h.symm
    · have := (mem_sdiff.mp (hBW h)).1; simp [W] at this
  obtain ⟨w, hw1, hw2⟩ := hG F (insert v A) (insert u B) u v hFc
    (by rw [card_insert_of_notMem]; · omega
        intro h; have := hAW h; simp [W] at this) (by
      rw [card_insert_of_notMem]; · omega
      intro h; have := (mem_sdiff.mp (hBW h)).1; simp [W] at this) hu hv
  have h1 : w ∉ F ∪ insert u B := hw1.1
  have h2 : w ∉ F ∪ insert v A := hw2.1
  by_cases hwu : w = u
  · exact h1 (by simp [hwu])
  by_cases hwv : w = v
  · exact h2 (by simp [hwv])
  have hwW : w ∈ W := by simp [W, hwu, hwv]
  by_cases hwA : w ∈ A
  · exact h2 (by simp [hwA])
  by_cases hwB : w ∈ B
  · exact h1 (by simp [hwB])
  · exact h1 (mem_union_left _ (by simp [F, hwW, hwA, hwB]))

end Card

/-! ## Complete graphs (remark after Definition 3) -/

section Complete

variable [Fintype V]

/-- In the complete graph, `reach_v(X) = V \ X` for `v ∉ X`. -/
theorem reaches_top {X : Finset V} {a b : V} (ha : a ∉ X) (hb : b ∉ X) :
    Reaches (⊤ : Digraph V) X a b :=
  ⟨ha, .single ⟨by simp, ha, hb⟩⟩

/-- Remark after Definition 3, corrected: in a clique, 3-reach holds iff `n ≤ 1` or `n > 3f`
(the paper says "iff `n > 3f`", which fails for `n = 1 ≤ 3f`). -/
theorem threeReach_top_iff {f : ℕ} :
    ThreeReach (⊤ : Digraph V) f ↔ Fintype.card V ≤ 1 ∨ 3 * f < Fintype.card V := by
  constructor
  · intro h
    by_cases hn : Fintype.card V ≤ 1
    · exact Or.inl hn
    · exact Or.inr (h.three_mul_lt_card (by omega))
  · rintro (h | h)
    · exact threeReach_of_card_le_one h
    · intro F Fu Fv u v hF hFu hFv hu hv
      have : (F ∪ Fu ∪ Fv).card < Fintype.card V := by
        calc (F ∪ Fu ∪ Fv).card ≤ F.card + Fu.card + Fv.card := by
              have := card_union_le (F ∪ Fu) Fv; have := card_union_le F Fu; omega
          _ < _ := by omega
      obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card (t := univ) (s := F ∪ Fu ∪ Fv)
        (by simpa using this)
      simp only [mem_union, not_or] at hw
      exact ⟨w, reaches_top (by simp [hw.1.1, hw.2]) hv, reaches_top (by simp [hw.1.1, hw.1.2]) hu⟩

/-- Remark after Definition 3, corrected: in a clique, 2-reach holds iff `n ≤ 1` or `n > 2f`. -/
theorem twoReach_top_iff {f : ℕ} :
    TwoReach (⊤ : Digraph V) f ↔ Fintype.card V ≤ 1 ∨ 2 * f < Fintype.card V := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
    -- `Fv ∋ u`, `Fu ∋ v`, `Fu ∪ Fv = V`
    obtain ⟨A, hA, hAc⟩ := exists_subset_card_eq (s := (univ.erase u).erase v)
      (n := min (f - 1) (Fintype.card V - 2)) (by
        rw [card_erase_of_mem (by simp [huv.symm]), card_erase_of_mem (mem_univ _), card_univ]
        omega)
    set Fu := insert v A
    set Fv := univ \ Fu
    have hvA : v ∉ A := fun h => by have := hA h; simp at this
    have huA : u ∉ A := fun h => by have := hA h; simp at this
    have hFu : Fu.card ≤ f := by rw [card_insert_of_notMem hvA]; omega
    have hFv : Fv.card ≤ f := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, card_insert_of_notMem hvA]; omega
    obtain ⟨w, hw1, hw2⟩ := h Fu Fv u v hFu hFv (by simp [Fu, huv, huA]) (by simp [Fv, Fu])
    exact hw1.1 (by simpa [Fv] using hw2.1)
  · rintro (h | h)
    · intro Fu Fv u v _ _ hu hv
      have huv : u = v := Fintype.card_le_one_iff.mp h u v
      subst huv
      exact ⟨u, Reaches.refl hv, Reaches.refl hu⟩
    · intro Fu Fv u v hFu hFv hu hv
      have : (Fu ∪ Fv).card < Fintype.card V := by
        have := card_union_le Fu Fv; omega
      obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card (t := univ) (s := Fu ∪ Fv)
        (by simpa using this)
      simp only [mem_union, not_or] at hw
      exact ⟨w, reaches_top hw.2 hv, reaches_top hw.1 hu⟩

/-- Remark after Definition 3, corrected: in a clique, 1-reach always holds (the paper says
"iff `n > f`"; but `F ⊂ V` already guarantees a common node). -/
theorem oneReach_top {f : ℕ} : OneReach (⊤ : Digraph V) f :=
  fun _ u _ _ hu hv => ⟨u, reaches_top hu hv, Reaches.refl hu⟩

end Complete

/-! ## Reduced graphs and source components (Definitions 5, 6) -/

/-- Edges of the reduced graph `G_{F₁,F₂}` when `X = F₁ ∪ F₂`: the outgoing links of `X` are
removed. -/
def RedAdj (G : Digraph V) (X : Finset V) (a b : V) : Prop := G.Adj a b ∧ a ∉ X

/-- `s` belongs to the source component `S_{F₁,F₂}`: it reaches every node in the reduced graph
`G_{F₁,F₂}`. -/
def InSrc (G : Digraph V) (F₁ F₂ : Finset V) (s : V) : Prop :=
  ∀ y, ReflTransGen (RedAdj G (F₁ ∪ F₂)) s y

/-- The source component `S_{F₁,F₂}` (Definition 6). -/
noncomputable def srcComp [Fintype V] (G : Digraph V) (F₁ F₂ : Finset V) : Finset V := by
  classical exact univ.filter (InSrc G F₁ F₂)

section Src

variable [Fintype V] {F₁ F₂ X : Finset V}

theorem mem_srcComp {s : V} : s ∈ srcComp G F₁ F₂ ↔ InSrc G F₁ F₂ s := by
  classical simp [srcComp]

theorem srcComp_comm : srcComp G F₁ F₂ = srcComp G F₂ F₁ := by
  ext s; simp only [mem_srcComp, InSrc, union_comm]

theorem Reaches.redAdj {a b : V} (h : Reaches G X a b) : ReflTransGen (RedAdj G X) a b :=
  ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ h.2

/-- In a graph with at least two nodes, the source component avoids `F₁ ∪ F₂`. -/
theorem notMem_of_mem_srcComp (hn : 2 ≤ Fintype.card V) {s : V} (hs : s ∈ srcComp G F₁ F₂) :
    s ∉ F₁ ∪ F₂ := by
  intro hX
  rw [mem_srcComp] at hs
  have : ∀ y, y = s := by
    intro y
    have h := hs y
    induction h with
    | refl => rfl
    | tail _ e ih => subst ih; exact absurd hX e.2
  have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => (this a).trans (this b).symm
  omega

/-- A node reaching the source component in `G − (F₁ ∪ F₂)` belongs to it. -/
theorem mem_srcComp_of_reaches {z s : V} (h : Reaches G (F₁ ∪ F₂) z s)
    (hs : s ∈ srcComp G F₁ F₂) : z ∈ srcComp G F₁ F₂ := by
  rw [mem_srcComp] at hs ⊢
  exact fun y => h.redAdj.trans (hs y)

/-- The source component is strongly connected, and the connecting paths stay inside it: any two
of its nodes are connected by a path avoiding any set disjoint from it. -/
theorem srcComp_reaches {s s' : V} (hs : s ∈ srcComp G F₁ F₂) (hs' : s' ∈ srcComp G F₁ F₂)
    (hX : ∀ x ∈ X, x ∉ srcComp G F₁ F₂) : Reaches G X s s' := by
  have hp := (mem_srcComp.mp hs) s'
  revert hs
  induction hp using ReflTransGen.head_induction_on with
  | refl => intro _; exact Reaches.refl fun h => hX _ h hs'
  | @head a c e hc ih =>
    intro ha
    have hcS : c ∈ srcComp G F₁ F₂ := mem_srcComp.mpr fun y => hc.trans ((mem_srcComp.mp hs') y)
    exact (ih hcS).head e.1 (fun h => hX _ h ha)

/-- Under 3-reach (and `n ≥ 2`), the source component of every reduced graph `G_{F₁,F₂}` with
`|F₁|, |F₂| ≤ f` is non-empty. (Used implicitly throughout Section 4 of the paper.) -/
theorem ThreeReach.srcComp_nonempty {f : ℕ} (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V)
    (h₁ : F₁.card ≤ f) (h₂ : F₂.card ≤ f) : (srcComp G F₁ F₂).Nonempty := by
  classical
  have h3 := hG.three_mul_lt_card hn
  have hXc : (F₁ ∪ F₂).card < Fintype.card V := by have := card_union_le F₁ F₂; omega
  set Y := F₁ ∪ F₂ with hY
  set W : Finset V := univ \ Y
  have hW : W.Nonempty := by
    rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ]; omega
  let A : V → Finset V := fun w => univ.filter (fun a => Reaches G Y a w)
  obtain ⟨s, hsW, hmin⟩ := exists_min_image W (fun w => (A w).card) hW
  have hsY : s ∉ Y := (mem_sdiff.mp hsW).2
  -- `s` reaches every node outside `X` while avoiding `X`
  have hreach : ∀ w, w ∉ Y → Reaches G Y s w := by
    intro w hw
    obtain ⟨z, hz1, hz2⟩ := hG F₁ F₂ F₂ w s h₁ h₂ h₂ hw hsY
    have hsub : A z ⊆ A s := fun a ha => by
      simp only [A, mem_filter, mem_univ, true_and] at ha ⊢; exact ha.trans hz1
    have hzW : z ∈ W := mem_sdiff.mpr ⟨mem_univ _, hz1.1⟩
    have heq := eq_of_subset_of_card_le hsub (hmin z hzW)
    have : s ∈ A z := by rw [heq]; simpa [A] using Reaches.refl hsY
    simp only [A, mem_filter, mem_univ, true_and] at this
    exact this.trans hz2
  refine ⟨s, mem_srcComp.mpr fun y => ?_⟩
  by_cases hy : y ∈ Y
  · -- `y` has an in-neighbour outside `X`
    by_contra hcon
    have hf : 1 ≤ f := by
      rcases mem_union.mp hy with h | h
      · exact (card_pos.mpr ⟨y, h⟩).trans_le h₁
      · exact (card_pos.mpr ⟨y, h⟩).trans_le h₂
    have hin : ∀ a, G.Adj a y → a ≠ y → a ∈ Y := by
      intro a e hay
      by_contra haY
      exact hcon ((hreach a haY).redAdj.tail ⟨e, haY⟩)
    obtain ⟨z, hz1, hz2⟩ := hG (F₁.erase y) {y} (F₂.erase y) s y
      ((card_erase_le).trans h₁) (by simp [hf]) ((card_erase_le).trans h₂)
      (by simp only [mem_union, mem_erase, mem_singleton, not_or]
          exact ⟨fun h => hsY (mem_union_left _ h.2), fun h => hsY (h ▸ hy)⟩)
      (by simp)
    have hzy : z = y := by
      have := hz1.mem_of_closed (L := {y}) (fun a b e ha hb => by
        simp only [Set.mem_singleton_iff] at hb ⊢
        subst hb
        by_contra hab
        have := hin a e hab
        simp only [mem_union, mem_erase, not_or, not_and] at ha
        rcases mem_union.mp this with h | h
        · exact ha.1 hab h
        · exact ha.2 hab h) rfl
      simpa using this
    exact hz2.1 (by simp [hzy])
  · exact (hreach y hy).redAdj

/-- A node of the source component outside `F₁ ∪ F₂`. -/
theorem ThreeReach.exists_srcComp {f : ℕ} (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V)
    (h₁ : F₁.card ≤ f) (h₂ : F₂.card ≤ f) : ∃ s ∈ srcComp G F₁ F₂, s ∉ F₁ ∪ F₂ := by
  obtain ⟨s, hs⟩ := hG.srcComp_nonempty hn h₁ h₂
  exact ⟨s, hs, notMem_of_mem_srcComp hn hs⟩

/-- **Theorem 5** (in the "no `f`-cover" form used by all proofs of the paper; by Menger's theorem
it is equivalent to the existence of `f + 1` node-disjoint paths): under 3-reach, for every
`F₁, F₂, X` of size `≤ f` and every node `b ∉ F₁ ∪ X`, some node of the source component
`S_{F₁,F₂}` reaches `b` in `G − (F₁ ∪ X)`. The paper's hypothesis `F₂ ⊆ V \ F₁` is not needed. -/
theorem ThreeReach.theorem5 {f : ℕ} (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V)
    (h₁ : F₁.card ≤ f) (h₂ : F₂.card ≤ f) (hX : X.card ≤ f) {b : V} (hb : b ∉ F₁ ∪ X) :
    ∃ s ∈ srcComp G F₁ F₂, Reaches G (F₁ ∪ X) s b := by
  obtain ⟨s₀, hs₀, hs₀X⟩ := hG.exists_srcComp hn h₁ h₂
  obtain ⟨z, hz1, hz2⟩ := hG F₁ F₂ X s₀ b h₁ h₂ hX hs₀X hb
  exact ⟨z, mem_srcComp_of_reaches hz2 hs₀, hz1⟩

/-- **Theorem 12**: under 3-reach, `S_{Fv,Fu} ∩ S_{Fv,Fw} ≠ ∅` for all `Fv, Fu, Fw` of size
`≤ f` (the paper's disjointness hypotheses `Fu, Fw ⊆ V \ Fv` are not needed). We prove it
directly from 3-reach (the paper goes through condition BCS). -/
theorem ThreeReach.theorem12 {f : ℕ} (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V)
    {Fv Fu Fw : Finset V} (hv : Fv.card ≤ f) (hu : Fu.card ≤ f) (hw : Fw.card ≤ f) :
    (srcComp G Fv Fu ∩ srcComp G Fv Fw).Nonempty := by
  obtain ⟨l, hl, hlX⟩ := hG.exists_srcComp hn hv hu
  obtain ⟨r, hr, hrX⟩ := hG.exists_srcComp hn hv hw
  obtain ⟨z, hz1, hz2⟩ := hG Fv Fu Fw l r hv hu hw hlX hrX
  exact ⟨z, mem_inter.mpr ⟨mem_srcComp_of_reaches hz2 hl, mem_srcComp_of_reaches hz1 hr⟩⟩

end Src

/-! ## Paths (Section 3) -/

/-- `p` is a directed path of `G` from `a` to `b`, given by the list of its nodes. -/
def IsPathFT (G : Digraph V) (p : List V) (a b : V) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.IsChain G.Adj

/-- A simple path (no repeated node). -/
def IsSimplePath (G : Digraph V) (p : List V) (a b : V) : Prop := IsPathFT G p a b ∧ p.Nodup

/-- A *redundant path* (Section 3): the concatenation `p₁ ‖ p₂` of two simple paths with
`ter(p₁) = init(p₂)` (one of them may be trivial). -/
def IsRedundant (G : Digraph V) (p : List V) : Prop :=
  ∃ p₁ p₂ a q b, IsSimplePath G p₁ a q ∧ IsSimplePath G p₂ q b ∧ p = p₁ ++ p₂.tail

theorem isSimplePath_singleton {a : V} : IsSimplePath G [a] a a := by
  simp [IsSimplePath, IsPathFT]

/-- `Reaches` yields a simple path avoiding the forbidden set. -/
theorem Reaches.exists_simplePath {X : Finset V} {a b : V} (h : Reaches G X a b) :
    ∃ p, IsSimplePath G p a b ∧ ∀ y ∈ p, y ∉ X := by
  obtain ⟨ha, h⟩ := h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨[b], isSimplePath_singleton, by simpa using ha⟩
  | @head a c e _ ih =>
    obtain ⟨p, ⟨⟨hph, hpl, hpc⟩, hpn⟩, hpX⟩ := ih e.2.2
    by_cases hap : a ∈ p
    · obtain ⟨s, t, rfl⟩ := List.append_of_mem hap
      refine ⟨a :: t, ⟨⟨rfl, ?_, hpc.right_of_append⟩, (List.nodup_append.mp hpn).2.1⟩,
        fun y hy => hpX y (by simp_all)⟩
      rw [List.getLast?_append] at hpl
      simpa using hpl
    · refine ⟨a :: p, ⟨⟨rfl, ?_, hpc.cons (by simpa [hph] using e.1)⟩,
        List.nodup_cons.mpr ⟨hap, hpn⟩⟩, ?_⟩
      · cases p with
        | nil => simp at hph
        | cons x l => simpa using hpl
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact e.2.1
        · exact hpX y hy

theorem IsSimplePath.isRedundant {p : List V} {a b : V} (h : IsSimplePath G p a b) :
    IsRedundant G p :=
  ⟨p, [b], a, b, b, h, isSimplePath_singleton, by simp⟩

end AsyncApproxBCDirected
