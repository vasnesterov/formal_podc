import Papers.PODC2018.JupiterListSpec.Jupiter
import Papers.PODC2018.JupiterListSpec.Weak

/-!
# The transformation loop of Jupiter along a known path

`xLoop_spec`: if, along the path `u → u ∪ {l₁} → … → cur` of the state space, every lookup of
the next edge returns the edge labelled with the transformed form `T lᵢ uᵢ` of the global state
space, then `xForm` returns `T x cur` and adds exactly the edges `T x uᵢ` (from `uᵢ`) and
`T lᵢ (uᵢ₋₁ ∪ {x})` (the other side of each square, Figure 3).
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

namespace Jup

variable (S : Sched (Oid n))

/-- The edge labelled `T y V` from `V`. -/
noncomputable def tE (y : Oid n) (V : Finset (Oid n)) : JOp n := ⟨S.T y V, y, V⟩

/-- The edges added by transforming `x` along `path` from `u`. -/
def New (x : Oid n) (path : List (Oid n)) (u : Finset (Oid n)) : Set (JOp n) :=
  {e | ∃ pre l rest, path = pre ++ l :: rest ∧
    (e = tE S x (insert l (u ∪ pre.toFinset)) ∨ e = tE S l (insert x (u ∪ pre.toFinset)))}

theorem xLoop_spec {c : Fin n} {d : Bool} {cur : Finset (Oid n)} {x : Oid n} :
    ∀ (path : List (Oid n)) (u : Finset (Oid n)) (E : List (JOp n)) (f : ℕ),
    path.length ≤ f → u ∪ path.toFinset = cur → (∀ l ∈ path, l ∉ u) → path.Nodup →
    (∀ pre l rest, path = pre ++ l :: rest →
      xf (S.T x (u ∪ pre.toFinset)) (S.T l (u ∪ pre.toFinset)) =
          S.T x (insert l (u ∪ pre.toFinset)) ∧
        xf (S.T l (u ∪ pre.toFinset)) (S.T x (u ∪ pre.toFinset)) =
          S.T l (insert x (u ∪ pre.toFinset)) ∧
        ∀ E' : List (JOp n), (∀ e ∈ E, e ∈ E') → (∀ e ∈ E', e ∈ E ∨ e ∈ New S x path u) →
          edgeFrom c E' (u ∪ pre.toFinset) d = some (tE S l (u ∪ pre.toFinset))) →
    ∃ Ef, xLoop c d cur f E (tE S x u) = some (Ef, tE S x cur) ∧ (∀ e ∈ E, e ∈ Ef) ∧
      (∀ e ∈ Ef, e ∈ E ∨ e ∈ New S x path u) ∧ (∀ e ∈ New S x path u, e ∈ Ef)
  | [], u, E, f, _, hcur, _, _, _ => by
    simp only [List.toFinset_nil, Finset.union_empty] at hcur
    subst hcur
    refine ⟨E, ?_, fun e he => he, fun e he => Or.inl he, ?_⟩
    · cases f <;> simp [xLoop, tE]
    · rintro e ⟨pre, l, rest, h, -⟩; simp at h
  | l :: rest, u, E, f, hf, hcur, hdisj, hnd, hstep => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp only [List.length_cons] at hf; omega⟩
    have hlu : l ∉ u := hdisj l (by simp)
    have hne : (tE S x u).ctx ≠ cur := by
      intro h; apply hlu; simp only [tE] at h; rw [h, ← hcur]; simp
    obtain ⟨h1, h2, hfind⟩ := hstep [] l rest rfl
    simp only [List.toFinset_nil, Finset.union_empty] at h1 h2 hfind
    have hfe := hfind E (fun e he => he) (fun e he => Or.inl he)
    have hxf1 : (tE S x u).xf (tE S l u) = tE S x (insert l u) := by
      simp [JOp.xf, tE, h1]
    have hxf2 : (tE S l u).xf (tE S x u) = tE S l (insert x u) := by
      simp [JOp.xf, tE, h2]
    have hnew0 : tE S x (insert l u) ∈ New S x (l :: rest) u ∧
        tE S l (insert x u) ∈ New S x (l :: rest) u :=
      ⟨⟨[], l, rest, rfl, Or.inl (by simp)⟩, ⟨[], l, rest, rfl, Or.inr (by simp)⟩⟩
    have hsubNew : ∀ e ∈ New S x rest (insert l u), e ∈ New S x (l :: rest) u := by
      rintro e ⟨pre, l', rest', hp, he⟩
      refine ⟨l :: pre, l', rest', by simp [hp], ?_⟩
      have : insert l u ∪ pre.toFinset = u ∪ (l :: pre).toFinset := by
        ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto
      rw [this] at he; exact he
    obtain ⟨Ef, hloop, hsub, hback, hall⟩ :=
      xLoop_spec (c := c) (d := d) (cur := cur) (x := x) rest (insert l u)
        (tE S x (insert l u) :: tE S l (insert x u) :: E) f
        (by simp only [List.length_cons] at hf; omega)
        (by rw [← hcur]; ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto)
        (by
          intro l' hl' hl'u
          rcases Finset.mem_insert.1 hl'u with rfl | hl'u
          · exact (List.nodup_cons.1 hnd).1 hl'
          · exact hdisj l' (List.mem_cons_of_mem _ hl') hl'u)
        (List.nodup_cons.1 hnd).2
        (by
          intro pre l' rest' hp
          have hp' : l :: rest = (l :: pre) ++ l' :: rest' := by simp [hp]
          obtain ⟨g1, g2, gfind⟩ := hstep (l :: pre) l' rest' hp'
          have hU : u ∪ (l :: pre).toFinset = insert l u ∪ pre.toFinset := by
            ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto
          rw [hU] at g1 g2 gfind
          refine ⟨g1, g2, fun E' hE hE' => gfind E' (fun e he => hE e (by simp [he])) ?_⟩
          intro e he
          rcases hE' e he with he | he
          · simp only [List.mem_cons] at he
            rcases he with rfl | rfl | he
            · exact Or.inr hnew0.1
            · exact Or.inr hnew0.2
            · exact Or.inl he
          · exact Or.inr (hsubNew e he))
    refine ⟨Ef, ?_, fun e he => hsub e (by simp [he]), ?_, ?_⟩
    · rw [xLoop, if_neg hne, show (tE S x u).ctx = u from rfl, hfe]
      dsimp only
      rw [hxf1, hxf2]; exact hloop
    · intro e he
      rcases hback e he with he | he
      · simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        · exact Or.inr hnew0.1
        · exact Or.inr hnew0.2
        · exact Or.inl he
      · exact Or.inr (hsubNew e he)
    · rintro e ⟨pre, l', rest', hp, he⟩
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        simp only [List.toFinset_nil, Finset.union_empty] at he
        rcases he with rfl | rfl
        · exact hsub _ (by simp)
        · exact hsub _ (by simp)
      | cons a pre =>
        simp only [List.cons_append, List.cons.injEq] at hp
        obtain ⟨rfl, hp⟩ := hp
        apply hall
        refine ⟨pre, l', rest', hp, ?_⟩
        have : u ∪ (l :: pre).toFinset = insert l u ∪ pre.toFinset := by ext y; simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto
        rw [this] at he; exact he

end Jup

end Podc.JupiterListSpec
