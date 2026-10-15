import Papers.PODC2022.ArrowTopology.Orientation

/-!
# Theorem 2.2 for two voters and three alternatives: the index-lemma proof (Section 3.3)

We work in the sign model (`SignModel.lean`) with voters `Fin 2`. A unanimous simplicial
chromatic map `f : N_I → N_O` is a sign function `s` with `SignUnanimous s` and `SignSimplicial s`.

The proof of Section 3.3:
1. colour each vertex `U^σ_j` of `N_I` by `p = ID + s (mod 3)` where `ID(AB) = 0`, `ID(BC) = 1`,
   `ID(CA) = 2` and the sign `s ∈ {+1, −1}` (`col`);
2. a triangle is trichromatic iff its three signs are equal, i.e. iff `f` maps it to a hollow
   triangle of `N_O`; so the content is `C = 0` (`content_eq_zero`);
3. by the index lemma (Theorem 3.1) and Lemma 3.2, the index is `I = 0`;
4. the boundary of `N_I` consists of the four Condorcet cycles `{U^σ_{AB}, U^σ_{BC}, U^σ_{CA}}`,
   `σ ∈ {++, −−, +−, −+}` (`index_eq`); the two unanimous ones contribute `+1` each
   (`cyc_unanimous`), each of the other two contributes `0` or `−1`, and `−1` exactly when its three
   signs are equal (`cyc_split`). Hence both split cycles are mapped onto boundary cycles of `N_O`;
5. they cannot have the same sign, otherwise the triangle `{U^{−+}_{AB}, U^{−+}_{BC}, U^{+−}_{CA}}` is
   mapped onto a hollow triangle; so `f` is a projection (`theorem_2_2_signs`).
-/

namespace Podc.ArrowTopology

open Cslib.Simplicial

/-- The colouring `p = ID + s (mod 3)` of Section 3.3 (sign `+1 ↦ 1`, `−1 ↦ 2`). -/
def col {ι : Type*} (s : Vtx ι → Bool) (v : Vtx ι) : Fin 3 := v.1 + if s v then 1 else 2

/-- A triangle is trichromatic only if its three signs are equal (whatever its orientation). -/
theorem triValCol_eq_zero {a b c : Bool} (h : OutTri a b c) :
    triValCol (0 + if a then 1 else 2) (1 + if b then 1 else 2) (2 + if c then 1 else 2) = 0 ∧
    triValCol (0 + if a then 1 else 2) (2 + if c then 1 else 2) (1 + if b then 1 else 2) = 0 := by
  revert h; cases a <;> cases b <;> cases c <;> decide

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Step 2: no triangle is trichromatic, so the content vanishes. -/
theorem content_eq_zero {s : Vtx ι → Bool} (hs : SignSimplicial s) :
    content orient (col s) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  have h := triValCol_eq_zero (hs t.1 t.2)
  unfold triVal orient
  by_cases hp : parity t.1 = 0
  · simp only [hp, ite_true]; exact h.1
  · simp only [hp, ite_false]; exact h.2

/-- Step 3: the index of `N_I` vanishes. -/
theorem index_eq_zero {s : Vtx ι → Bool} (hs : SignSimplicial s) :
    index orient (col s) = 0 := by
  rw [index_eq_content _ lemma_3_2, content_eq_zero hs]

omit [DecidableEq ι] in
theorem dirEdges_orient_ne (t : Tri ι) : ∀ e ∈ dirEdges (orient t), e.1.1 ≠ e.2.1 := by
  unfold orient dirEdges
  split_ifs <;> simp

/-- The index only involves the edges `{U^α_j, U^α_{j'}}` with equal sign vectors (Figure 7). -/
theorem index_eq_sum_filter (c : Vtx ι → Fin 3) :
    index orient c = ∑ t : Tri ι,
      (((dirEdges (orient t)).filter fun e => decide (e.1.2 = e.2.2)).map (edgeVal c)).sum := by
  unfold index
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  refine List.filter_congr fun e he => ?_
  rw [decide_eq_decide]
  exact isBoundary_iff (dirEdges_orient_ne t e he) _ _

/-! ### Two voters -/

/-- The sign vectors `++`, `−−`, `+−`, `−+` of two voters. -/
def pp : Fin 2 → Bool := ![true, true]
def mm : Fin 2 → Bool := ![false, false]
def pm : Fin 2 → Bool := ![true, false]
def mp : Fin 2 → Bool := ![false, true]

/-- The Condorcet cycle `{U^σ_{AB}, U^σ_{BC}, U^σ_{CA}}`, oriented `AB → BC → CA` (`fwd = true`)
or `AB → CA → BC` (`fwd = false`). -/
def cycEdges (σ : Fin 2 → Bool) (fwd : Bool) : List (Vtx (Fin 2) × Vtx (Fin 2)) :=
  if fwd then [((0, σ), (1, σ)), ((1, σ), (2, σ)), ((2, σ), (0, σ))]
  else [((0, σ), (2, σ)), ((2, σ), (1, σ)), ((1, σ), (0, σ))]

/-- The boundary of `N_I` (two voters, three alternatives) with its induced orientation: the four
Condorcet cycles; the unanimous ones are oriented `AB → BC → CA`, the other two the opposite way
(Figure 7 and Figure 8). -/
def boundaryEdges : List (Vtx (Fin 2) × Vtx (Fin 2)) :=
  cycEdges pp true ++ cycEdges mm true ++ cycEdges pm false ++ cycEdges mp false

theorem boundary_multiset :
    (Finset.univ.val.bind fun t : Tri (Fin 2) =>
      (((dirEdges (orient t)).filter fun e => decide (e.1.2 = e.2.2)) :
        Multiset (Vtx (Fin 2) × Vtx (Fin 2)))) = (boundaryEdges : Multiset _) := by
  decide

/-- Contribution of a Condorcet cycle to the index. -/
def cyc (c : Vtx (Fin 2) → Fin 3) (σ : Fin 2 → Bool) (fwd : Bool) : ℤ :=
  ((cycEdges σ fwd).map (edgeVal c)).sum

/-- Step 4: the index is the sum of the contributions of the four boundary cycles. -/
theorem index_eq (c : Vtx (Fin 2) → Fin 3) :
    index orient c = cyc c pp true + cyc c mm true + cyc c pm false + cyc c mp false := by
  rw [index_eq_sum_filter]
  have h : ∀ φ : Vtx (Fin 2) × Vtx (Fin 2) → ℤ,
      ∑ t : Tri (Fin 2), (((dirEdges (orient t)).filter fun e => decide (e.1.2 = e.2.2)).map
        φ).sum = (boundaryEdges.map φ).sum := by
    intro φ
    rw [← Multiset.sum_coe, ← Multiset.map_coe, ← boundary_multiset, Multiset.map_bind,
      Multiset.sum_bind]
    rfl
  rw [h]
  simp [boundaryEdges, cyc, List.map_append, List.sum_append, add_assoc]

theorem pp_eq : pp = fun _ => true := by funext i; fin_cases i <;> rfl
theorem mm_eq : mm = fun _ => false := by funext i; fin_cases i <;> rfl

/-- The unanimous boundary cycles contribute `+1` each (Figure 8). -/
theorem cyc_unanimous {s : Vtx (Fin 2) → Bool} (hs : SignUnanimous s) :
    cyc (col s) pp true = 1 ∧ cyc (col s) mm true = 1 := by
  have h1 : ∀ j, s (j, pp) = true := fun j => by rw [pp_eq]; exact hs j true
  have h2 : ∀ j, s (j, mm) = false := fun j => by rw [mm_eq]; exact hs j false
  simp only [cyc, cycEdges, edgeVal, col, h1, h2, ite_true, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  decide

/-- A Condorcet cycle oriented `AB → CA → BC` contributes `0` or `−1`, and `−1` exactly when its
three vertices have the same sign (i.e. it is wrapped around a hollow triangle of `N_O`). -/
theorem cyc_split (s : Vtx (Fin 2) → Bool) (σ : Fin 2 → Bool) :
    (cyc (col s) σ false = 0 ∨ cyc (col s) σ false = -1) ∧
      (cyc (col s) σ false = -1 ↔ s (0, σ) = s (1, σ) ∧ s (1, σ) = s (2, σ)) := by
  simp only [cyc, cycEdges, edgeVal, col, Bool.false_eq_true, ite_false, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  rcases Bool.eq_false_or_eq_true (s (0, σ)) with h0 | h0 <;>
  rcases Bool.eq_false_or_eq_true (s (1, σ)) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (s (2, σ)) with h2 | h2 <;>
  simp only [h0, h1, h2] <;> decide

/-- **Theorem 2.2** for `n = 2`, `|X| = 3`, in the sign model, proved as in Section 3.3 with the
index lemma: a unanimous simplicial (chromatic) map `N_I → N_O` is a projection. -/
theorem theorem_2_2_signs {s : Vtx (Fin 2) → Bool} (hU : SignUnanimous s)
    (hS : SignSimplicial s) : ∃ k, SignProjection s k := by
  have hI := index_eq_zero hS
  rw [index_eq] at hI
  obtain ⟨hpp, hmm⟩ := cyc_unanimous hU
  obtain ⟨h1, h1'⟩ := cyc_split s pm
  obtain ⟨h2, h2'⟩ := cyc_split s mp
  -- both split cycles contribute `−1`, hence have constant signs
  have hpm : s (0, pm) = s (1, pm) ∧ s (1, pm) = s (2, pm) := h1'.1 (by omega)
  have hmp : s (0, mp) = s (1, mp) ∧ s (1, mp) = s (2, mp) := h2'.1 (by omega)
  -- the two split cycles have different signs: look at the triangle `{U^{−+}_AB, U^{−+}_BC, U^{+−}_CA}`
  have hne : s (0, mp) ≠ s (0, pm) := by
    have := hS ![mp, mp, pm] (by intro i; fin_cases i <;> decide)
    change ¬ (s (0, mp) = s (1, mp) ∧ s (1, mp) = s (2, pm)) at this
    intro h
    exact this ⟨hmp.1, by rw [← hmp.1, h, hpm.1, hpm.2]⟩
  -- every vertex: `j` and a sign vector among `++, −−, +−, −+`
  have hσ : ∀ σ : Fin 2 → Bool, σ = pp ∨ σ = mm ∨ σ = pm ∨ σ = mp := by
    intro σ
    have h0 : σ = ![σ 0, σ 1] := by funext i; fin_cases i <;> rfl
    rw [h0]; cases σ 0 <;> cases σ 1 <;> simp [pp, mm, pm, mp]
  have hp1 : ∀ j, s (j, pp) = true := fun j => by rw [pp_eq]; exact hU j true
  have hm1 : ∀ j, s (j, mm) = false := fun j => by rw [mm_eq]; exact hU j false
  have hpmj : ∀ j, s (j, pm) = s (0, pm) := by
    intro j; fin_cases j
    · rfl
    · exact hpm.1.symm
    · exact (hpm.1.trans hpm.2).symm
  have hmpj : ∀ j, s (j, mp) = s (0, mp) := by
    intro j; fin_cases j
    · rfl
    · exact hmp.1.symm
    · exact (hmp.1.trans hmp.2).symm
  cases hb : s (0, pm)
  · -- `+−` ↦ `−`: the second voter is the dictator
    have hb' : s (0, mp) = true := by
      cases h : s (0, mp)
      · exact absurd (h.trans hb.symm) hne
      · rfl
    refine ⟨1, fun ⟨j, σ⟩ => ?_⟩
    rcases hσ σ with rfl | rfl | rfl | rfl
    · rw [hp1]; rfl
    · rw [hm1]; rfl
    · rw [hpmj, hb]; rfl
    · rw [hmpj, hb']; rfl
  · -- `+−` ↦ `+`: the first voter is the dictator
    have hb' : s (0, mp) = false := by
      cases h : s (0, mp)
      · rfl
      · exact absurd (h.trans hb.symm) hne
    refine ⟨0, fun ⟨j, σ⟩ => ?_⟩
    rcases hσ σ with rfl | rfl | rfl | rfl
    · rw [hp1]; rfl
    · rw [hm1]; rfl
    · rw [hpmj, hb]; rfl
    · rw [hmpj, hb']; rfl

end Podc.ArrowTopology
