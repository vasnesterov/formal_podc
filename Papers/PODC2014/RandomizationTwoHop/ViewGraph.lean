import Papers.PODC2014.RandomizationTwoHop.Views

/-!
# The infinite view graph (Definition 1) and Lemmas 2–4

For a labelled graph `X` we identify the depth-infinity view `L_∞(v)` with the walk language
`⟪X⟫ v` (`forall_teq_iff_lang`: for 2-hop coloured graphs this is the same as equality of the
view trees). The *infinite view graph* `X∞ = viewLGraph X` (Definition 1) has the different views
as nodes, an edge between `L_∞(u)` and `L_∞(v)` for every edge `(u, v)` of `X`, and labels
`ℓ∞(L_∞(v)) = ℓ(v)`. `toView X : X.V → X∞.V` is the infinite view map `f∞`.

* `lemma_2`: `f∞` is a factorizing map (`X∞` is a factor of `X`).
* `lemma_3`: `X∞` is prime, and every prime factor of `X` is isomorphic to `X∞`.
* `lemma_4`: in a prime 2-hop coloured graph, `u = v ↔ L_∞(u) = L_∞(v)`.
* `reach_lang`: `X∞`'s node set can be reconstructed from any single `L_∞(v)` (§2.1): it is the
  set of sub-languages `reach (⟪X⟫ v)` reached by walks.
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

variable {L : Type}

/-- `⟪X⟫ v`: the walk language of `v` in `X`, the canonical representation of `L_∞(v)`. -/
notation:max "⟪" X "⟫" => Podc.RandomizationTwoHop.lang (LGraph.G X) (LGraph.lab X)

namespace LGraph

/-- The labelling of `X` is a 2-hop colouring. -/
abbrev TwoHop (X : LGraph L) : Prop := IsTwoHopColoring X.G X.lab

end LGraph

/-- Adjacency of the infinite view graph. -/
def viewAdj (X : LGraph L) (T T' : Set.range ⟪X⟫) : Prop :=
  T.1 ≠ T'.1 ∧ ∃ u v, X.G.Adj u v ∧ ⟪X⟫ u = T.1 ∧ ⟪X⟫ v = T'.1

/-- The infinite view graph `X∞` of `X` (Definition 1). -/
noncomputable def viewLGraph (X : LGraph L) : LGraph L where
  V := Set.range ⟪X⟫
  finite := Set.finite_range _ |>.to_subtype
  G := { Adj := viewAdj X
         symm := ⟨fun _ _ ⟨hne, u, v, h, hu, hv⟩ => ⟨hne.symm, v, u, h.symm, hv, hu⟩⟩
         loopless := ⟨fun _ h => h.1 rfl⟩ }
  conn := by
    have : Nonempty (Set.range ⟪X⟫) := ⟨⟨_, Classical.arbitrary X.V, rfl⟩⟩
    refine ⟨fun T T' => ?_⟩
    obtain ⟨_, u, rfl⟩ := T
    obtain ⟨_, v, rfl⟩ := T'
    obtain ⟨p⟩ := X.conn.preconnected u v
    induction p with
    | nil => rfl
    | @cons a b c h p ih =>
      refine Reachable.trans ?_ ih
      by_cases he : ⟪X⟫ a = ⟪X⟫ b
      · simp only [he]; rfl
      · exact Adj.reachable ⟨he, a, b, h, rfl, rfl⟩
  lab T := X.lab T.2.choose

/-- The infinite view map `f∞ : V → V∞`, `v ↦ L_∞(v)`. -/
def toView (X : LGraph L) (v : X.V) : (viewLGraph X).V := ⟨⟪X⟫ v, v, rfl⟩

theorem mem_range_of_eq {X Y : LGraph L} (h : Set.range ⟪Y⟫ = Set.range ⟪X⟫) (y : Y.V) :
    ⟪Y⟫ y ∈ Set.range ⟪X⟫ := h ▸ Set.mem_range_self y

theorem lab_eq_of_lang_eq {X Y : LGraph L} {u : X.V} {v : Y.V} (h : ⟪X⟫ u = ⟪Y⟫ v) :
    X.lab u = Y.lab v := by
  have : [X.lab u] ∈ ⟪Y⟫ v := h ▸ single_mem_lang u
  have := InLang.head this; simpa using this

theorem viewLGraph_lab (X : LGraph L) {T : (viewLGraph X).V} {v : X.V} (h : ⟪X⟫ v = T.1) :
    (viewLGraph X).lab T = X.lab v :=
  show X.lab T.2.choose = X.lab v from lab_eq_of_lang_eq (T.2.choose_spec.trans h.symm)

/-- The general form of Lemma 2: if `Y` is 2-hop coloured and has the same views as the 2-hop
coloured `X`, then `y ↦ L_∞(y)` is a factorizing map from `Y` onto `X∞`. -/
theorem isFactorMap_view {X Y : LGraph L} (hX : X.TwoHop) (hY : Y.TwoHop)
    (h : Set.range ⟪Y⟫ = Set.range ⟪X⟫) :
    IsFactorMap Y (viewLGraph X) (fun y => ⟨⟪Y⟫ y, mem_range_of_eq h y⟩) where
  lab y := by
    obtain ⟨x, hx⟩ := mem_range_of_eq h y
    exact (viewLGraph_lab X (T := ⟨⟪Y⟫ y, mem_range_of_eq h y⟩) hx).trans (lab_eq_of_lang_eq hx)
  bij y := by
    refine ⟨fun x hx => ?_, fun x hx x' hx' he => ?_, fun T hT => ?_⟩
    · obtain ⟨a, ha⟩ := mem_range_of_eq h y
      refine ⟨fun e => hY.ne_of_adj hx (lab_eq_of_lang_eq e), ?_⟩
      have hm : [Y.lab y, Y.lab x] ∈ ⟪X⟫ a := ha ▸ InLang.cons hx (single_mem_lang x)
      obtain ⟨b, hab, hbl, -⟩ := exists_adj_of_mem_lang hm
      refine ⟨a, b, hab, ha, ?_⟩
      show ⟪X⟫ b = ⟪Y⟫ x
      rw [← child_lang hX hab, ← child_lang hY hx, ha, hbl]
    · have := congrArg Subtype.val he
      exact hY.injOn_nbhd y hx hx' (lab_eq_of_lang_eq this)
    · obtain ⟨-, a, b, hab, ha, hb⟩ := hT
      have hm : [Y.lab y, X.lab b] ∈ ⟪Y⟫ y := by
        simp only at ha
        rw [← ha]; rw [← lab_eq_of_lang_eq ha]; exact InLang.cons hab (single_mem_lang b)
      obtain ⟨x, hx, hxl, -⟩ := exists_adj_of_mem_lang hm
      refine ⟨x, hx, Subtype.ext ?_⟩
      simp only at ha hb ⊢
      rw [← hb, ← child_lang hY hx, ← child_lang hX hab, ha, hxl]
  surj T := by
    obtain ⟨_, x, rfl⟩ := T
    obtain ⟨y, hy⟩ := mem_range_of_eq h.symm x
    exact ⟨y, Subtype.ext hy⟩

/-- **Lemma 2.** For a 2-hop coloured graph `X`, the infinite view graph `X∞` is a factor of `X`
induced by the infinite view map `f∞`. -/
theorem lemma_2 (X : LGraph L) (hX : X.TwoHop) : IsFactorMap X (viewLGraph X) (toView X) :=
  isFactorMap_view hX hX rfl

/-- The view of the node `T` of `X∞` is `T` itself. -/
theorem lang_viewLGraph (X : LGraph L) (hX : X.TwoHop) (T : (viewLGraph X).V) :
    ⟪viewLGraph X⟫ T = T.1 := by
  obtain ⟨_, v, rfl⟩ := T
  exact (lemma_2 X hX).lang_eq v

theorem viewLGraph_twoHop (X : LGraph L) (hX : X.TwoHop) : (viewLGraph X).TwoHop :=
  (lemma_2 X hX).toIsLocalIso.twoHop _root_.id (lemma_2 X hX).surj hX

/-- Factors preserve the set of views. -/
theorem IsFactorMap.range_lang {X Y : LGraph L} {f : X.V → Y.V} (hf : IsFactorMap X Y f) :
    Set.range ⟪Y⟫ = Set.range ⟪X⟫ := by
  ext T; constructor
  · rintro ⟨y, rfl⟩; obtain ⟨x, rfl⟩ := hf.surj y; exact ⟨x, (hf.lang_eq x).symm⟩
  · rintro ⟨x, rfl⟩; exact ⟨f x, hf.lang_eq x⟩

theorem IsFactorMap.twoHop {X Y : LGraph L} {f : X.V → Y.V} (hf : IsFactorMap X Y f)
    (hX : X.TwoHop) : Y.TwoHop := hf.toIsLocalIso.twoHop _root_.id hf.surj hX

/-- **Lemma 3.** For a 2-hop coloured graph `X`, the infinite view graph `X∞` is the unique prime
factor of `X` up to isomorphism: it is a factor, it is prime, and every prime factor of `X` is
isomorphic to it. -/
theorem lemma_3 (X : LGraph L) (hX : X.TwoHop) :
    IsFactor (viewLGraph X) X ∧ Prime (viewLGraph X) ∧
      ∀ K : LGraph L, IsFactor K X → Prime K → Isomorphic K (viewLGraph X) := by
  refine ⟨⟨_, lemma_2 X hX⟩, ?_, ?_⟩
  · rw [prime_iff_bijective]
    intro Y g hg
    refine ⟨fun T T' he => ?_, hg.surj⟩
    have h1 := hg.lang_eq T
    have h2 := hg.lang_eq T'
    rw [he, h2, lang_viewLGraph X hX, lang_viewLGraph X hX] at h1
    exact Subtype.ext h1.symm
  · rintro K ⟨f, hf⟩ hK
    exact hK _ _ (isFactorMap_view hX (hf.twoHop hX) hf.range_lang)

/-- **Lemma 4.** In a prime 2-hop coloured graph, `u = v` iff `L_∞(u) = L_∞(v)`. -/
theorem lemma_4 (X : LGraph L) (hX : X.TwoHop) (hP : Prime X) (u v : X.V) :
    u = v ↔ ViewEqInf X u X v := by
  constructor
  · rintro rfl k; exact TEq.refl k u
  · intro h
    have hl : ⟪X⟫ u = ⟪X⟫ v := lang_eq_of_forall_teq h
    have hb := (prime_iff_bijective X).1 hP _ _ (lemma_2 X hX)
    exact hb.1 (Subtype.ext hl)

/-! ### Reconstructing `X∞` from one view (§2.1) -/

/-- The sub-languages of `T` reached along its words: for `T = L_∞(v)` these are the views of all
nodes (`reach_lang`). -/
def reach (T : Set (List L)) : Set (Set (List L)) := {S | ∃ w ∈ T, w.tail.foldl child T = S}

theorem foldl_child_lang {X : LGraph L} (hX : X.TwoHop) {v : X.V} {w : List L}
    (hw : w ∈ ⟪X⟫ v) : ∃ x, w.tail.foldl child (⟪X⟫ v) = ⟪X⟫ x := by
  change InLang X.G X.lab v w at hw
  induction hw with
  | single v => exact ⟨v, rfl⟩
  | @cons v u w hvu hw ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨x, ?_⟩
    have h0 := InLang.head hw
    cases w with
    | nil => simp at h0
    | cons a w =>
      simp at h0; subst h0
      simp only [List.tail_cons, List.foldl_cons] at hx ⊢
      rw [child_lang hX hvu]; exact hx

/-- §2.1: every `L_∞(u)` can be read off `L_∞(v)` (`X` connected), so the node set `V∞` of the
infinite view graph is determined by any single view. -/
theorem reach_lang {X : LGraph L} (hX : X.TwoHop) (v : X.V) :
    reach (⟪X⟫ v) = Set.range ⟪X⟫ := by
  ext S; constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx⟩ := foldl_child_lang hX hw
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    suffices ∀ (a : X.V) (p : X.G.Walk a x), ∃ w ∈ ⟪X⟫ a, w.tail.foldl child (⟪X⟫ a) = ⟪X⟫ x
      from this v (X.conn.preconnected v x).some
    intro a q
    induction q with
    | nil => exact ⟨_, single_mem_lang _, rfl⟩
    | @cons a b c h p ih =>
      obtain ⟨w, hw, hwx⟩ := ih
      refine ⟨X.lab a :: w, InLang.cons h hw, ?_⟩
      have h0 := InLang.head hw
      cases w with
      | nil => simp at h0
      | cons d w =>
        simp at h0; subst h0
        simp only [List.tail_cons, List.foldl_cons] at hwx ⊢
        rw [child_lang hX h]; exact hwx

end Podc.RandomizationTwoHop
