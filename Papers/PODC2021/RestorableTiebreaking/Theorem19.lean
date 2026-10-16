import Papers.PODC2021.RestorableTiebreaking.Defs

/-!
# Theorem 19: ATW functions generate stable, consistent, restorable schemes

Bodwin–Parter, PODC 2021, Section 3.1.

The heart is `restore_one` (the case of one new fault on top of an arbitrary fault set `A`, which is
the paper's reduction "it suffices to consider `f = 1` on `G \ F'`").
-/

open Finset SimpleGraph SimpleGraph.Walk

set_option linter.unusedSectionVars false

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r : V → V → ℝ}
  {A B : Set (Sym2 V)}

/-! ### Unique minimum walks -/

lemma IsMinWalk.dwt_le {s t : V} {p q : G.Walk s t} (hp : IsMinWalk G r A p) (hq : q.Avoids A) :
    p.dwt (wstar r) ≤ q.dwt (wstar r) := by
  by_cases h : q = p
  · rw [h]
  · exact (hp.2 q hq h).le

lemma IsMinWalk.unique {s t : V} {p q : G.Walk s t} (hp : IsMinWalk G r A p)
    (hq : IsMinWalk G r A q) : p = q := by
  by_contra h
  exact lt_asymm (hp.2 q hq.1 (Ne.symm h)) (hq.2 p hp.1 h)

lemma append_ne_append_of_ne {s u v t : V} (p₁ : G.Walk s u) {q q' : G.Walk u v}
    (p₂ : G.Walk v t) (h : q' ≠ q) : p₁.append (q'.append p₂) ≠ p₁.append (q.append p₂) := by
  intro heq
  apply h
  apply darts_injective
  have := congrArg Walk.darts heq
  simp only [darts_append] at this
  exact List.append_cancel_right (List.append_cancel_left this)

/-- Subwalks of unique shortest walks are unique shortest walks (consistency). -/
lemma IsMinWalk.sub {s u v t : V} {p₁ : G.Walk s u} {q : G.Walk u v} {p₂ : G.Walk v t}
    (h : IsMinWalk G r A (p₁.append (q.append p₂))) : IsMinWalk G r A q := by
  obtain ⟨hav, hmin⟩ := h
  simp only [avoids_append] at hav
  refine ⟨hav.2.1, fun q' hq' hne => ?_⟩
  by_contra hle
  push Not at hle
  have := hmin (p₁.append (q'.append p₂)) (by simp [hav, hq']) (append_ne_append_of_ne _ _ hne)
  simp only [dwt_append] at this
  linarith

lemma IsMinWalk.prefix {s u t : V} {p₁ : G.Walk s u} {p₂ : G.Walk u t}
    (h : IsMinWalk G r A (p₁.append p₂)) : IsMinWalk G r A p₁ :=
  IsMinWalk.sub (p₁ := nil) (p₂ := p₂) (by simpa using h)

lemma IsMinWalk.suffix {s u t : V} {p₁ : G.Walk s u} {p₂ : G.Walk u t}
    (h : IsMinWalk G r A (p₁.append p₂)) : IsMinWalk G r A p₂ :=
  IsMinWalk.sub (p₁ := p₁) (p₂ := nil) (by simpa using h)

/-- Stability: a unique shortest walk avoiding more faults stays the unique shortest walk. -/
lemma IsMinWalk.mono {s t : V} {p : G.Walk s t} (h : IsMinWalk G r A p) (hAB : A ⊆ B)
    (hB : p.Avoids B) : IsMinWalk G r B p :=
  ⟨hB, fun q hq hne => h.2 q (hq.mono hAB) hne⟩

lemma HasMinWalks.isShortestIn (hA : HasMinWalks G r A) {s t : V} {p : G.Walk s t}
    (hp : IsMinWalk G r A p) : p.IsShortestIn A := by
  obtain ⟨q, hq, hqs⟩ := hA s t hp.1.reachable
  rwa [hp.unique hq]

lemma HasMinWalks.nil (hA : HasMinWalks G r A) (s : V) : IsMinWalk G r A (nil : G.Walk s s) := by
  obtain ⟨q, hq, hqs⟩ := hA s s (Reachable.refl _)
  rwa [hqs.nil_iff] at hq

lemma HasMinWalks.exists (hA : HasMinWalks G r A) {s t : V} {p : G.Walk s t} (hp : p.Avoids A) :
    ∃ q : G.Walk s t, IsMinWalk G r A q := by
  obtain ⟨q, hq, -⟩ := hA s t hp.reachable
  exact ⟨q, hq⟩

/-! ### The one-fault restoration argument -/

/-- **Core of Theorem 19** (one new failing edge `e` on top of the fault set `A`). If `G* \ A` and
`G* \ (A ∪ {e})` have unique shortest walks which are unweighted-shortest, and `r` is
antisymmetric, then for every pair `s, t` connected in `G \ (A ∪ {e})` there is a vertex `x` such
that `π(s, x | A) ∘ π(t, x | A)⁻¹` is a shortest `s ⇝ t` path of `G \ (A ∪ {e})`. -/
theorem restore_one {e : Sym2 V} (hanti : ∀ u v, G.Adj u v → r u v = - r v u) (hA : HasMinWalks G r A)
    (hB : HasMinWalks G r (insert e A)) {s t : V}
    (hst : (G.deleteEdges (insert e A)).Reachable s t) :
    ∃ (x : V) (p : G.Walk s x) (q : G.Walk t x), IsMinWalk G r A p ∧ IsMinWalk G r A q ∧
      (p.append q.reverse).IsShortestIn (insert e A) := by
  have hsub : A ⊆ insert e A := Set.subset_insert e A
  obtain ⟨P, -, hPS⟩ := hB s t hst
  have hPA : P.Avoids A := hPS.1.mono hsub
  obtain ⟨p₀, hp₀M, hp₀S⟩ := hA s t hPA.reachable
  by_cases he : e ∉ p₀.edges
  · -- `π(s, t | A)` survives: take `x = t`
    refine ⟨t, p₀, nil, hp₀M, hA.nil t, ?_⟩
    simpa using hp₀S.mono hsub (avoids_insert.mpr ⟨he, hp₀M.1⟩)
  push Not at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  -- the last vertex `x` of `P` whose selected path from `s` avoids `e`
  let Q : V → Prop := fun z => ∃ pz : G.Walk s z, IsMinWalk G r A pz ∧ d.edge ∉ pz.edges
  have hQs : Q s := ⟨nil, hA.nil s, by simp⟩
  have hQt : ¬ Q t := by
    rintro ⟨pz, hpz, hpze⟩
    exact hpze (hpz.unique hp₀M ▸ he)
  obtain ⟨x, y, hxy, P₁, P₂, hP, ⟨px, hpxM, hpxe⟩, hy⟩ := exists_dart_of_pred Q P hQs hQt
  rw [hP] at hPS hPA
  have hxyA : s(x, y) ∉ insert d.edge A := by
    have := (avoids_append.mp hPS.1).2
    exact (avoids_cons.mp this).1
  have hxy_ne : s(x, y) ≠ d.edge := fun h => hxyA (h ▸ Set.mem_insert _ _)
  have hxy_A : s(x, y) ∉ A := fun h => hxyA (Set.mem_insert_of_mem _ h)
  have hpxS := hA.isShortestIn hpxM
  -- `π(s, y | A)` contains `e`, in the orientation `(u, v)` of `π(s, t | A)`
  obtain ⟨py, hpyM⟩ := hA.exists (p := P₁.append (cons hxy nil))
    (by simpa [hxy_A] using (avoids_append.mp hPA).1)
  have hpyS := hA.isShortestIn hpyM
  have hpye : d.edge ∈ py.edges := by
    by_contra h; exact hy ⟨py, hpyM, h⟩
  obtain ⟨d', hd', hd'e⟩ := List.mem_map.mp hpye
  have hdd' : d' = d := hpyS.dart_eq_of_edge_eq hp₀S hd' hd hd'e
  subst hdd'
  obtain ⟨a, b, hpy⟩ := exists_eq_append_cons_of_mem_darts hd'
  rw [hpy] at hpyM hpyS
  have hcbM : IsMinWalk G r A (cons d'.adj b) := hpyM.suffix
  have hbM : IsMinWalk G r A b := (show cons d'.adj b = (cons d'.adj nil).append b from rfl) ▸
    hcbM |>.suffix
  -- `π(u, x | A)`
  obtain ⟨pux, hpuxM⟩ := hA.exists (p := a.reverse.append px)
    (by simp [(avoids_append.mp hpyM.1).1, hpxM.1])
  -- inequality (1): `w(u,v) + d*(v,y) < d*(u,x) + w(x,y)`
  have hW1 : (pux.append (cons hxy nil)).Avoids A := by simp [hpuxM.1, hxy_A]
  have hW1ne : pux.append (cons hxy nil) ≠ cons d'.adj b := by
    intro heq
    have hpy' : a.append (cons d'.adj b) = (a.append pux).append (cons hxy nil) := by
      rw [← heq, append_assoc]
    rw [hpy'] at hpyM
    have hpre := hpyM.prefix
    have := hpre.unique hpxM
    apply hpxe
    rw [← this, edges_append, List.mem_append]
    right
    have hdm : d' ∈ (pux.append (cons hxy nil)).darts := by rw [heq]; simp
    rw [darts_append, List.mem_append] at hdm
    rcases hdm with hdm | hdm
    · exact List.mem_map_of_mem hdm
    · exfalso
      simp only [darts_cons, darts_nil, List.mem_singleton] at hdm
      apply hxy_ne
      rw [hdm]; rfl
  have h1 := hcbM.2 _ hW1 hW1ne
  -- inequality (2), by antisymmetry: `d*(v,y) + w(y,x) < w(v,u) + d*(u,x)`
  have hW2 : (b.append (cons hxy.symm nil)).Avoids A := by
    simp [(avoids_cons.mp hcbM.1).2, Sym2.eq_swap, hxy_A]
  obtain ⟨pvx, hpvxM⟩ := hA.exists hW2
  have hvx_le := hpvxM.dwt_le hW2
  have hanti' : ∀ a b, G.Adj a b → wstar r a b = 2 - wstar r b a := by
    intro a b hab; simp only [wstar, hanti a b hab]; ring
  have hpvx_ne : pvx ≠ cons d'.adj.symm pux := by
    intro heq
    rw [heq] at hvx_le
    simp only [dwt_cons, dwt_append, dwt_nil] at h1 hvx_le
    rw [hanti' _ _ hxy.symm, hanti' _ _ d'.adj.symm] at hvx_le
    linarith
  -- `π(t, x | A)` avoids `e`
  obtain ⟨ptx, hptxM⟩ := hA.exists (p := p₀.reverse.append px) (by simp [hp₀M.1, hpxM.1])
  have hptxS := hA.isShortestIn hptxM
  have hptxe : d'.edge ∉ ptx.edges := by
    intro hin
    obtain ⟨d'', hd'', hd''e⟩ := List.mem_map.mp hin
    have hsym : d'.symm ∈ p₀.reverse.darts := by
      rw [darts_reverse, List.mem_reverse]; exact List.mem_map_of_mem hd
    have : d'' = d'.symm :=
      hptxS.dart_eq_of_edge_eq hp₀S.reverse hd'' hsym (by rw [hd''e, Dart.edge_symm])
    subst this
    obtain ⟨g, g', hg⟩ := exists_eq_append_cons_of_mem_darts hd''
    rw [hg] at hptxM
    have hcg : IsMinWalk G r A (cons d'.symm.adj g') := hptxM.suffix
    have hg' : IsMinWalk G r A g' :=
      (show cons d'.symm.adj g' = (cons d'.symm.adj nil).append g' from rfl) ▸ hcg |>.suffix
    have := hg'.unique hpuxM
    subst this
    exact hpvx_ne (hpvxM.unique hcg)
  refine ⟨x, px, ptx, hpxM, hptxM, ?_⟩
  refine Avoids.isShortestIn ?_ ?_
  · simp only [avoids_append, avoids_reverse, avoids_insert]
    exact ⟨⟨hpxe, hpxM.1⟩, ⟨hptxe, hptxM.1⟩⟩
  · rw [← hPS.2, length_append, length_reverse, length_append]
    have h1 := (hPS.append_left).1.mono hsub |>.edist_le
    have h2 := (hPS.append_right).1.mono hsub |>.edist_le
    rw [← hpxS.2] at h1
    rw [edist_comm, ← hptxS.2] at h2
    push_cast
    exact add_le_add h1 h2

/-! ### Theorem 19 -/

variable {f : ℕ}

lemma atwScheme_eq_some_iff {F : Finset (Sym2 V)} {s t : V} {p : G.Walk s t} :
    atwScheme G r F s t = some p ↔ IsMinWalk G r (F : Set (Sym2 V)) p := by
  unfold atwScheme
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun hp => hp ▸ h.choose_spec, fun hp => (h.choose_spec.unique hp)⟩
  · simp only [false_iff]
    exact fun hp => h ⟨p, hp⟩

/-- **Theorem 19 of [Bodwin–Parter].** The RPTS generated by an antisymmetric `f`-fault
tiebreaking weight function is an `f`-RPTS which is stable, consistent and `f`-restorable. -/
theorem theorem19 (hr : IsATW G f r) :
    IsRPTS G f (atwScheme G r) ∧ IsStable G f (atwScheme G r) ∧
      IsConsistent G f (atwScheme G r) ∧ IsRestorable G f (atwScheme G r) := by
  refine ⟨fun F hF => ⟨fun s t p hp => ?_, fun s t hst => ?_⟩, ?_, ?_, ?_⟩
  · exact (hr.tiebreak F hF).isShortestIn (atwScheme_eq_some_iff.mp hp)
  · obtain ⟨p, hp, -⟩ := hr.tiebreak F hF s t hst
    rw [atwScheme_eq_some_iff.mpr hp]; rfl
  · intro F hF e s t p hp he
    rw [atwScheme_eq_some_iff] at hp ⊢
    exact hp.mono (by simp) (by
      rw [coe_insert, avoids_insert]; exact ⟨he, hp.1⟩)
  · intro F hF s t p hp u v p₁ q p₂ hpq
    rw [atwScheme_eq_some_iff, hpq] at hp
    exact atwScheme_eq_some_iff.mpr hp.sub
  · intro F hF hne s t hst
    obtain ⟨e, he⟩ := hne
    have hF' : #(F.erase e) ≤ f := (card_erase_le).trans hF
    have hins : insert e (F.erase e : Set (Sym2 V)) = (F : Set (Sym2 V)) := by
      rw [← coe_insert, insert_erase he]
    have hB := hr.tiebreak F hF
    rw [← hins] at hB hst
    obtain ⟨x, p, q, hp, hq, hpq⟩ :=
      restore_one hr.antisymm (hr.tiebreak _ hF') hB (A := (F.erase e : Set (Sym2 V))) hst
    refine ⟨F.erase e, erase_ssubset he, x, p, q, atwScheme_eq_some_iff.mpr hp,
      atwScheme_eq_some_iff.mpr hq, ?_⟩
    rwa [← hins]

end RestorableTiebreaking
