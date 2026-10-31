import Papers.PODC2018.JupiterListSpec.CJupiter
import Papers.PODC2018.JupiterListSpec.Weak

/-!
# The transformation loop of CJupiter along a known path

`cLoop_spec`: if, along the path `u → u ∪ {l₁} → … → cur`, every `firstEdge` lookup returns the
edge `fe lᵢ uᵢ` labelled by the global transformation `T lᵢ uᵢ`, then `xForm` returns `T x cur`
and adds exactly the edges labelled `T x uᵢ` (from every `uᵢ`, including `cur`) and the
transformed edges `(fe lᵢ uᵢ)⟨x⟩` (Figure 3).
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

namespace CJup

variable (S : Sched (Oid n))

/-- The edge labelled `T x V` from `V` with server context `sx`. -/
noncomputable def opE (x : Oid n) (sx : Finset (Oid n)) (V : Finset (Oid n)) : COp n :=
  ⟨S.T x V, x, V, sx⟩

/-- The edges added by transforming `x` along `path` from `u`. -/
def CNew (x : Oid n) (sx : Finset (Oid n)) (fe : Oid n → Finset (Oid n) → COp n)
    (path : List (Oid n)) (u : Finset (Oid n)) : Set (COp n) :=
  {e | e = opE S x sx (u ∪ path.toFinset) ∨ ∃ pre l rest, path = pre ++ l :: rest ∧
    (e = opE S x sx (u ∪ pre.toFinset) ∨ e = (fe l (u ∪ pre.toFinset)).xf (opE S x sx (u ∪ pre.toFinset)))}

theorem cLoop_spec {r : Option (Fin n)} {cur : Finset (Oid n)} {x : Oid n} {sx : Finset (Oid n)}
    (fe : Oid n → Finset (Oid n) → COp n)
    (hfe : ∀ l V, (fe l V).o = S.T l V ∧ (fe l V).oid = l ∧ (fe l V).ctx = V) :
    ∀ (path : List (Oid n)) (u : Finset (Oid n)) (E : List (COp n)) (f : ℕ),
    path.length ≤ f → u ∪ path.toFinset = cur → (∀ l ∈ path, l ∉ u) → path.Nodup → x ∉ cur →
    (∀ pre l rest, path = pre ++ l :: rest →
      xf (S.T x (u ∪ pre.toFinset)) (S.T l (u ∪ pre.toFinset)) =
          S.T x (insert l (u ∪ pre.toFinset)) ∧
        xf (S.T l (u ∪ pre.toFinset)) (S.T x (u ∪ pre.toFinset)) =
          S.T l (insert x (u ∪ pre.toFinset)) ∧
        ∀ E' : List (COp n), (∀ e ∈ E, e ∈ E') →
          (∀ e ∈ E', e ∈ E ∨ (e ∈ CNew S x sx fe path u ∧ e.ctx ≠ u ∪ pre.toFinset)) →
          firstEdge r E' (u ∪ pre.toFinset) = some (fe l (u ∪ pre.toFinset))) →
    ∃ Ef, cLoop r cur f E (opE S x sx u) = some (Ef, opE S x sx cur) ∧ (∀ e ∈ E, e ∈ Ef) ∧
      (∀ e ∈ Ef, e ∈ E ∨ e ∈ CNew S x sx fe path u) ∧ (∀ e ∈ CNew S x sx fe path u, e ∈ Ef)
  | [], u, E, f, _, hcur, _, _, _, _ => by
    simp only [List.toFinset_nil, Finset.union_empty] at hcur
    subst hcur
    refine ⟨opE S x sx u :: E, ?_, fun e he => List.mem_cons_of_mem _ he, ?_, ?_⟩
    · cases f <;> simp [cLoop, opE]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Or.inr (Or.inl (by simp))
      · exact Or.inl he
    · rintro e (rfl | ⟨pre, l, rest, h, -⟩)
      · simp
      · simp at h
  | l :: rest, u, E, f, hf, hcur, hdisj, hnd, hxcur, hstep => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp only [List.length_cons] at hf; omega⟩
    have hlu : l ∉ u := hdisj l (by simp)
    have hne : (opE S x sx u).ctx ≠ cur := by
      intro h; apply hlu; simp only [opE] at h; rw [h, ← hcur]; simp
    obtain ⟨h1, h2, hfind⟩ := hstep [] l rest rfl
    simp only [List.toFinset_nil, Finset.union_empty] at h1 h2 hfind
    have hfe0 := hfind E (fun e he => he) (fun e he => Or.inl he)
    have hxcur' : x ∉ cur := hxcur
    obtain ⟨hfo, hfoid, hfctx⟩ := hfe l u
    have hxf1 : (opE S x sx u).xf (fe l u) = opE S x sx (insert l u) := by
      simp [COp.xf, opE, h1, hfo, hfoid]
    have hU : ∀ pre : List (Oid n), u ∪ (l :: pre).toFinset = insert l u ∪ pre.toFinset := by
      intro pre; ext y
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]; tauto
    have hnew0 : opE S x sx u ∈ CNew S x sx fe (l :: rest) u ∧
        (fe l u).xf (opE S x sx u) ∈ CNew S x sx fe (l :: rest) u :=
      ⟨Or.inr ⟨[], l, rest, rfl, Or.inl (by simp)⟩, Or.inr ⟨[], l, rest, rfl, Or.inr (by simp)⟩⟩
    have hsubNew : ∀ e ∈ CNew S x sx fe rest (insert l u), e ∈ CNew S x sx fe (l :: rest) u := by
      rintro e (he | ⟨pre, l', rest', hp, he⟩)
      · left; rw [he, ← hU rest]
      · refine Or.inr ⟨l :: pre, l', rest', by simp [hp], ?_⟩
        rw [hU pre]; exact he
    obtain ⟨Ef, hloop, hsub, hback, hall⟩ :=
      cLoop_spec fe hfe (r := r) (cur := cur) (x := x) (sx := sx) rest (insert l u)
        (opE S x sx u :: (fe l u).xf (opE S x sx u) :: E) f
        (by simp only [List.length_cons] at hf; omega)
        (by rw [← hcur, ← hU rest])
        (by
          intro l' hl' hl'u
          rcases Finset.mem_insert.1 hl'u with rfl | hl'u
          · exact (List.nodup_cons.1 hnd).1 hl'
          · exact hdisj l' (List.mem_cons_of_mem _ hl') hl'u)
        (List.nodup_cons.1 hnd).2 hxcur
        (by
          intro pre l' rest' hp
          have hp' : l :: rest = (l :: pre) ++ l' :: rest' := by simp [hp]
          obtain ⟨g1, g2, gfind⟩ := hstep (l :: pre) l' rest' hp'
          rw [hU pre] at g1 g2 gfind
          refine ⟨g1, g2, fun E' hE hE' => gfind E' (fun e he => hE e (by simp [he])) ?_⟩
          have hlU : l ∈ insert l u ∪ pre.toFinset := by simp
          have hxU : x ∉ insert l u ∪ pre.toFinset := by
            intro hx; apply hxcur; rw [← hcur, hU rest]
            rcases Finset.mem_union.1 hx with hx | hx
            · exact Finset.mem_union_left _ hx
            · rw [hp] at *
              simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_cons] at hx ⊢
              tauto
          intro e he
          rcases hE' e he with he | ⟨he, hne⟩
          · simp only [List.mem_cons] at he
            rcases he with rfl | rfl | he
            · refine Or.inr ⟨hnew0.1, ?_⟩
              simp only [opE]; intro hc; exact hlu (hc ▸ hlU)
            · refine Or.inr ⟨hnew0.2, ?_⟩
              simp only [COp.xf, opE, (hfe l u).2.2]
              intro hc; exact hxU (hc ▸ Finset.mem_insert_self _ _)
            · exact Or.inl he
          · exact Or.inr ⟨hsubNew e he, hne⟩)
    refine ⟨Ef, ?_, fun e he => hsub e (by simp [he]), ?_, ?_⟩
    · rw [cLoop, if_neg hne, show (opE S x sx u).ctx = u from rfl, hfe0]
      dsimp only
      rw [hxf1]; exact hloop
    · intro e he
      rcases hback e he with he | he
      · simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        · exact Or.inr hnew0.1
        · exact Or.inr hnew0.2
        · exact Or.inl he
      · exact Or.inr (hsubNew e he)
    · rintro e (he | ⟨pre, l', rest', hp, he⟩)
      · apply hall; left; rw [he, ← hU rest]
      · cases pre with
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
          refine Or.inr ⟨pre, l', rest', hp, ?_⟩
          rw [← hU pre]; exact he

end CJup

end Podc.JupiterListSpec
