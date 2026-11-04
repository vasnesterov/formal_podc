import Papers.PODC2014.RandomizationTwoHop.Graphs

-- CSLib candidate (paper-local for now; see README)

/-!
# Local views

§1.1 of the paper: the depth-`d` local view `L_d(v, G)` is the rooted tree with `L_1(v)` a single
vertex marked `ℓ(v)`, and `L_{d+1}(v)` obtained by hanging `L_d(u)` below the root for every
`u ∈ Γ(v)`. We never build the trees; we only need *equality* of views, which we define by
recursion (`TEq`): two rooted unordered marked trees are equal iff the root marks agree and there
is a bijection between the children matching equal subtrees.

* `TEq G lG H lH k u v`: `L_{k+1}(u, G) = L_{k+1}(v, H)` (tree depth `k`).
* `ViewEq X u Y v d`: the paper's `L_d(u, X) = L_d(v, Y)` (`d ≥ 1`), `ViewEqInf`: `L_∞(u) = L_∞(v)`
  (equality of all finite truncations; for the finitely branching trees at hand this is equality of
  the infinite trees).
* `lang G lG v`: the set of label sequences of walks starting at `v`. For a 2-hop coloured graph
  siblings in a view tree carry different marks, so the tree is determined by this set of words
  (`teq_iff_trunc_lang`): `lang` is the canonical representation of `L_∞(v)` that we use for the
  infinite view graph and the infinity model.
* `IsLocalIso.teq`, `IsLocalIso.lang_eq`: **Fact 1** (local isomorphisms preserve views).
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

variable {L : Type}

section TEq

variable {V W U : Type} (G : SimpleGraph V) (lG : V → L) (H : SimpleGraph W) (lH : W → L)
  (K : SimpleGraph U) (lK : U → L)

/-- `TEq G lG H lH k u v`: the local views of tree depth `k` agree, i.e.
`L_{k+1}(u, G) = L_{k+1}(v, H)` in the paper's notation. -/
def TEq : ℕ → V → W → Prop
  | 0, u, v => lG u = lH v
  | k + 1, u, v => lG u = lH v ∧ ∃ e : G.neighborSet u ≃ H.neighborSet v, ∀ w : G.neighborSet u, TEq k w.1 (e w).1

variable {G lG H lH K lK}

theorem TEq.lab {k : ℕ} {u : V} {v : W} (h : TEq G lG H lH k u v) : lG u = lH v := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem TEq.refl (k : ℕ) (u : V) : TEq G lG G lG k u u := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih => exact ⟨rfl, Equiv.refl _, fun w => ih w⟩

theorem TEq.symm {k : ℕ} {u : V} {v : W} (h : TEq G lG H lH k u v) : TEq H lH G lG k v u := by
  induction k generalizing u v with
  | zero => exact (show lG u = lH v from h).symm
  | succ k ih =>
    obtain ⟨hl, e, he⟩ := h
    refine ⟨hl.symm, e.symm, fun w => ?_⟩
    have := ih (he (e.symm w))
    simpa using this

theorem TEq.trans {k : ℕ} {u : V} {v : W} {x : U} (h₁ : TEq G lG H lH k u v)
    (h₂ : TEq H lH K lK k v x) : TEq G lG K lK k u x := by
  induction k generalizing u v x with
  | zero => exact (show lG u = lH v from h₁).trans h₂
  | succ k ih =>
    obtain ⟨hl₁, e₁, he₁⟩ := h₁
    obtain ⟨hl₂, e₂, he₂⟩ := h₂
    exact ⟨hl₁.trans hl₂, e₁.trans e₂, fun w => ih (he₁ w) (he₂ (e₁ w))⟩

theorem TEq.of_succ {k : ℕ} {u : V} {v : W} (h : TEq G lG H lH (k + 1) u v) :
    TEq G lG H lH k u v := by
  induction k generalizing u v with
  | zero => exact h.1
  | succ k ih => exact ⟨h.1, h.2.choose, fun w => ih (h.2.choose_spec w)⟩

theorem TEq.of_le {k m : ℕ} (hkm : k ≤ m) {u : V} {v : W} (h : TEq G lG H lH m u v) :
    TEq G lG H lH k u v := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

/-- Changing the labels: if equal old labels force equal new labels, equal views stay equal. -/
theorem TEq.map_lab {mG : V → L'} {mH : W → L'} (hm : ∀ x y, lG x = lH y → mG x = mH y)
    {k : ℕ} {u : V} {v : W} (h : TEq G lG H lH k u v) : TEq G mG H mH k u v := by
  induction k generalizing u v with
  | zero => exact hm u v h
  | succ k ih => exact ⟨hm u v h.1, h.2.choose, fun w => ih (h.2.choose_spec w)⟩

/-- **Fact 1** (finite depths): a label-preserving local isomorphism preserves local views. -/
theorem IsLocalIso.teq {f : V → W} (hf : IsLocalIso G lG H lH f) (k : ℕ) (u : V) :
    TEq G lG H lH k u (f u) := by
  induction k generalizing u with
  | zero => exact (hf.lab u).symm
  | succ k ih => exact ⟨(hf.lab u).symm, (hf.bij u).equiv, fun w => ih w⟩

end TEq

/-! ### Paper notation for views of labelled graphs -/

/-- `ViewEq X u Y v d`: the paper's `L_d(u, X) = L_d(v, Y)` (for `d ≥ 1`; `L_1` is the root
alone). -/
def ViewEq (X : LGraph L) (u : X.V) (Y : LGraph L) (v : Y.V) (d : ℕ) : Prop :=
  TEq X.G X.lab Y.G Y.lab (d - 1) u v

/-- `L_∞(u, X) = L_∞(v, Y)`: all finite-depth views agree. -/
def ViewEqInf (X : LGraph L) (u : X.V) (Y : LGraph L) (v : Y.V) : Prop :=
  ∀ k, TEq X.G X.lab Y.G Y.lab k u v

/-! ### Words of walks -/

section Lang

variable {V W : Type} (G : SimpleGraph V) (lG : V → L) {H : SimpleGraph W} {lH : W → L}

/-- `InLang G lG v w`: `w` is the label sequence of a walk in `G` starting at `v`. -/
inductive InLang : V → List L → Prop
  | single (v : V) : InLang v [lG v]
  | cons {v u : V} {w : List L} : G.Adj v u → InLang u w → InLang v (lG v :: w)

/-- The set of label sequences of walks starting at `v`: the canonical representation of the
view `L_∞(v)` in a 2-hop coloured graph. -/
def lang (v : V) : Set (List L) := {w | InLang G lG v w}

/-- Truncation of a set of words to words of length `≤ k + 1` (walks with `≤ k` edges). -/
def trunc (k : ℕ) (T : Set (List L)) : Set (List L) := {w | w ∈ T ∧ w.length ≤ k + 1}

/-- The words of the sub-tree below a child with label `a`. -/
def child (T : Set (List L)) (a : L) : Set (List L) := {w | w.head? = some a ∧ ∃ b, b :: w ∈ T}

variable {G lG}

theorem InLang.head {v : V} {w : List L} (h : InLang G lG v w) : w.head? = some (lG v) := by
  cases h <;> rfl

theorem mem_lang_iff {v : V} {w : List L} :
    w ∈ lang G lG v ↔ w = [lG v] ∨ ∃ u w', G.Adj v u ∧ w' ∈ lang G lG u ∧ w = lG v :: w' := by
  constructor
  · rintro (_ | ⟨h, h'⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, h, h', rfl⟩
  · rintro (rfl | ⟨u, w', h, h', rfl⟩)
    · exact InLang.single v
    · exact InLang.cons h h'

theorem single_mem_lang (v : V) : [lG v] ∈ lang G lG v := InLang.single v

theorem mem_trunc {k : ℕ} {T : Set (List L)} {w : List L} :
    w ∈ trunc k T ↔ w ∈ T ∧ w.length ≤ k + 1 := Iff.rfl

theorem trunc_trunc {k m : ℕ} (h : k ≤ m) (T : Set (List L)) : trunc k (trunc m T) = trunc k T := by
  ext w; simp only [mem_trunc]; constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩

theorem trunc_eq_of_le {k m : ℕ} (h : k ≤ m) {T T' : Set (List L)} (hT : trunc m T = trunc m T') :
    trunc k T = trunc k T' := by
  rw [← trunc_trunc h T, hT, trunc_trunc h]

theorem lang_nonempty_word {v : V} {w : List L} (h : w ∈ lang G lG v) : w ≠ [] := by
  intro e; have := InLang.head h; simp [e] at this

/-- **Fact 1**: a label-preserving local isomorphism preserves the walk languages. -/
theorem IsLocalIso.lang_eq {f : V → W} (hf : IsLocalIso G lG H lH f) (v : V) :
    lang H lH (f v) = lang G lG v := by
  ext w
  constructor
  · intro h
    change InLang H lH (f v) w at h
    change InLang G lG v w
    generalize hx : f v = x at h
    induction h generalizing v with
    | single x => subst hx; rw [hf.lab v]; exact InLang.single v
    | @cons x u w hxu _ ih =>
      subst hx
      obtain ⟨u', hu', rfl⟩ := (hf.bij v).surjOn hxu
      rw [hf.lab v]; exact InLang.cons hu' (ih u' rfl)
  · intro h
    change InLang G lG v w at h
    change InLang H lH (f v) w
    induction h with
    | single x => rw [← hf.lab x]; exact InLang.single _
    | @cons x u w hxu _ ih => rw [← hf.lab x]; exact InLang.cons (hf.adj hxu) ih

theorem trunc_lang_subset_of_teq {k : ℕ} {u : V} {v : W} (h : TEq G lG H lH k u v) :
    trunc k (lang G lG u) ⊆ trunc k (lang H lH v) := by
  induction k generalizing u v with
  | zero =>
    rintro w ⟨hw, hl⟩
    rcases mem_lang_iff.1 hw with rfl | ⟨_, w', _, hw', rfl⟩
    · refine ⟨?_, hl⟩; rw [show lG u = lH v from h]; exact single_mem_lang v
    · exfalso; have := lang_nonempty_word hw'
      cases w' with
      | nil => exact this rfl
      | cons _ _ => simp at hl
  | succ k ih =>
    obtain ⟨hl0, e, he⟩ := h
    rintro w ⟨hw, hl⟩
    rcases mem_lang_iff.1 hw with rfl | ⟨x, w', hx, hw', rfl⟩
    · refine ⟨?_, hl⟩; rw [hl0]; exact single_mem_lang v
    · have := ih (he ⟨x, hx⟩) ⟨hw', by simp at hl; omega⟩
      refine ⟨?_, hl⟩
      rw [hl0]
      exact InLang.cons (e ⟨x, hx⟩).2 this.1

/-- Equal views have equal (truncated) languages. -/
theorem trunc_lang_eq_of_teq {k : ℕ} {u : V} {v : W} (h : TEq G lG H lH k u v) :
    trunc k (lang G lG u) = trunc k (lang H lH v) :=
  (trunc_lang_subset_of_teq h).antisymm (trunc_lang_subset_of_teq h.symm)

theorem lang_eq_of_forall_teq {u : V} {v : W} (h : ∀ k, TEq G lG H lH k u v) :
    lang G lG u = lang H lH v := by
  ext w
  have := trunc_lang_eq_of_teq (h (w.length))
  constructor
  · intro hw
    exact (this ▸ (show w ∈ trunc w.length (lang G lG u) from ⟨hw, by omega⟩)).1
  · intro hw
    exact (this.symm ▸ (show w ∈ trunc w.length (lang H lH v) from ⟨hw, by omega⟩)).1

/-- In a 2-hop coloured graph the word `ℓ(v) ℓ(u) …` of a walk through a neighbour `u` of `v`
determines `u`: the child sub-language of `lang v` with root label `ℓ(u)` is `lang u`. -/
theorem child_lang (h2 : IsTwoHopColoring G lG) {v u : V} (huv : G.Adj v u) :
    child (lang G lG v) (lG u) = lang G lG u := by
  ext w
  constructor
  · rintro ⟨hw, b, hbw⟩
    rcases mem_lang_iff.1 hbw with h | ⟨x, w', hx, hw', he⟩
    · simp at h; obtain ⟨-, rfl⟩ := h; simp at hw
    · simp only [List.cons.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hl : lG x = lG u := by
        have := InLang.head hw'; rw [hw] at this; simpa using this.symm
      rw [h2.injOn_nbhd v hx huv hl] at hw'
      exact hw'
  · intro hw
    exact ⟨InLang.head hw, lG v, InLang.cons huv hw⟩

theorem exists_adj_of_mem_lang {v : V} {a b : L} {w : List L} (h : a :: b :: w ∈ lang G lG v) :
    ∃ u, G.Adj v u ∧ lG u = b ∧ b :: w ∈ lang G lG u := by
  rcases mem_lang_iff.1 h with h | ⟨x, w', hx, hw', he⟩
  · simp at h
  · simp only [List.cons.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨x, hx, by have := InLang.head hw'; simpa using this.symm, hw'⟩

/-- A bijection between neighbourhoods that matches labels, from label injectivity. -/
theorem exists_nbhd_equiv {u : V} {v : W} (hu : Set.InjOn lG (G.neighborSet u))
    (hv : Set.InjOn lH (H.neighborSet v))
    (h₁ : ∀ x ∈ G.neighborSet u, ∃ y ∈ H.neighborSet v, lH y = lG x)
    (h₂ : ∀ y ∈ H.neighborSet v, ∃ x ∈ G.neighborSet u, lG x = lH y) :
    ∃ e : G.neighborSet u ≃ H.neighborSet v, ∀ x, lH (e x) = lG x := by
  choose φ hφ hφl using h₁
  let f : G.neighborSet u → H.neighborSet v := fun x => ⟨φ x.1 x.2, hφ x.1 x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have : lG x.1 = lG y.1 := by
        rw [← hφl x.1 x.2, ← hφl y.1 y.2]; exact congrArg (fun z => lH z.1) hxy
      exact Subtype.ext (hu x.2 y.2 this)
    · intro y
      obtain ⟨x, hx, hxl⟩ := h₂ y.1 y.2
      refine ⟨⟨x, hx⟩, Subtype.ext (hv (hφ x hx) y.2 ?_)⟩
      rw [hφl x hx, hxl]
  exact ⟨Equiv.ofBijective f hf, fun x => hφl x.1 x.2⟩

/-- In 2-hop coloured graphs, views are determined by the (truncated) walk languages. -/
theorem teq_of_trunc_lang_eq (hG : IsTwoHopColoring G lG) (hH : IsTwoHopColoring H lH)
    {k : ℕ} {u : V} {v : W} (h : trunc k (lang G lG u) = trunc k (lang H lH v)) :
    TEq G lG H lH k u v := by
  have hlab : lG u = lH v := by
    have : [lG u] ∈ trunc k (lang H lH v) := h ▸ ⟨single_mem_lang u, by simp⟩
    have := InLang.head this.1; simpa using this
  induction k generalizing u v with
  | zero => exact hlab
  | succ k ih =>
    refine ⟨hlab, ?_⟩
    -- neighbours correspond by labels
    have key₁ : ∀ x ∈ G.neighborSet u, ∃ y ∈ H.neighborSet v, lH y = lG x := by
      intro x hx
      have hm : [lG u, lG x] ∈ trunc (k + 1) (lang G lG u) :=
        ⟨InLang.cons hx (single_mem_lang x), by simp⟩
      rw [h] at hm
      obtain ⟨y, hy, hyl, -⟩ := exists_adj_of_mem_lang hm.1
      exact ⟨y, hy, hyl⟩
    have key₂ : ∀ y ∈ H.neighborSet v, ∃ x ∈ G.neighborSet u, lG x = lH y := by
      intro y hy
      have hm : [lH v, lH y] ∈ trunc (k + 1) (lang H lH v) :=
        ⟨InLang.cons hy (single_mem_lang y), by simp⟩
      rw [← h] at hm
      obtain ⟨x, hx, hxl, -⟩ := exists_adj_of_mem_lang hm.1
      exact ⟨x, hx, hxl⟩
    obtain ⟨e, he⟩ := exists_nbhd_equiv (hG.injOn_nbhd u) (hH.injOn_nbhd v) key₁ key₂
    refine ⟨e, fun x => ?_⟩
    apply ih _ (he x).symm
    -- the truncated languages of `x` and `e x` agree
    have hsub : ∀ {V W : Type} {G : SimpleGraph V} {lG : V → L} {H : SimpleGraph W} {lH : W → L},
        IsTwoHopColoring H lH → ∀ {u : V} {v : W} {x : V} {y : W}, G.Adj u x → H.Adj v y →
        lG u = lH v → lG x = lH y →
        trunc (k + 1) (lang G lG u) = trunc (k + 1) (lang H lH v) →
        trunc k (lang G lG x) ⊆ trunc k (lang H lH y) := by
      intro V W G lG H lH hH u v x y hx hy hl hl' h w ⟨hw, hwl⟩
      have hm : lG u :: w ∈ trunc (k + 1) (lang G lG u) := ⟨InLang.cons hx hw, by simp; omega⟩
      rw [h, hl] at hm
      have hw0 := InLang.head hw
      obtain ⟨a, w', rfl⟩ : ∃ a w', w = a :: w' := by
        cases w with
        | nil => simp at hw0
        | cons a w' => exact ⟨a, w', rfl⟩
      obtain ⟨z, hz, hzl, hzw⟩ := exists_adj_of_mem_lang hm.1
      have : z = y := hH.injOn_nbhd v hz hy (by simp at hw0; rw [hzl, hw0, hl'])
      subst this
      exact ⟨hzw, hwl⟩
    exact (hsub hH x.2 (e x).2 hlab (he x).symm h).antisymm
      (hsub hG (e x).2 x.2 hlab.symm (he x) h.symm)

theorem teq_iff_trunc_lang (hG : IsTwoHopColoring G lG) (hH : IsTwoHopColoring H lH)
    {k : ℕ} {u : V} {v : W} :
    TEq G lG H lH k u v ↔ trunc k (lang G lG u) = trunc k (lang H lH v) :=
  ⟨trunc_lang_eq_of_teq, teq_of_trunc_lang_eq hG hH⟩

/-- In 2-hop coloured graphs, `L_∞(u) = L_∞(v)` iff the walk languages agree. -/
theorem forall_teq_iff_lang (hG : IsTwoHopColoring G lG) (hH : IsTwoHopColoring H lH)
    {u : V} {v : W} : (∀ k, TEq G lG H lH k u v) ↔ lang G lG u = lang H lH v :=
  ⟨lang_eq_of_forall_teq, fun h k => teq_of_trunc_lang_eq hG hH (by rw [h])⟩

end Lang

end Podc.RandomizationTwoHop
