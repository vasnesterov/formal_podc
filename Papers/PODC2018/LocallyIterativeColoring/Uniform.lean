import Papers.PODC2018.LocallyIterativeColoring.Main

/-!
# A uniform (round-independent) AG + colour-reduction step (Section 4.1 of [BEG18])

At the end of Section 4.1 [BEG18] combine AG with a colour reduction that needs **no round
counter** (as required for self-stabilization): a final vertex `⟨0, b⟩` with `b > Δ` whose neighbours
are all final and have smaller second coordinates recolours itself with a colour `⟨0, b'⟩`,
`b' ≤ Δ`, not used by any neighbour. All vertices execute the same step in every round.

* `uniStep Δ`: the combined step (colours `GF(q)²`, second coordinates compared via `ZMod.val`).
* `uniform_isProper`: every round is proper.
* `isAGRun_uniform`: the running-time analysis of AG applies unchanged (a final vertex with a working
  neighbour never recolours).
* `uniform_le` (**the `(Δ+1)`-colouring paragraph before Theorem 4.4**, from a proper
  `GF(q)²`-colouring, `2Δ < q`): after `2q - (Δ + 1)` rounds every colour is `⟨0, b⟩` with `b ≤ Δ`.
-/

namespace BEG18

open Cslib.LocallyIterative

variable {q : ℕ} [NeZero q]

/-- The smallest second coordinate (as a number) not used by the colours in `N`. -/
noncomputable def freeColor (N : Set (ZMod q × ZMod q)) : ZMod q :=
  (firstFree ((fun y => y.2.val) '' N) : ℕ)

open Classical in
/-- The uniform step: AG for working vertices; a final vertex `⟨0, b⟩` with `b > Δ`, all of whose
neighbours are final with smaller second coordinate, recolours to `⟨0, freeColor N⟩`. -/
noncomputable def uniStep (Δ : ℕ) (x : ZMod q × ZMod q) (N : Set (ZMod q × ZMod q)) :
    ZMod q × ZMod q :=
  if x.1 = 0 ∧ Δ < x.2.val ∧ ∀ y ∈ N, y.1 = 0 ∧ y.2.val < x.2.val then (0, freeColor N)
  else agStep x N

/-- The uniform algorithm. -/
noncomputable def uniform (q Δ : ℕ) [NeZero q] : Algorithm (ZMod q × ZMod q) :=
  Algorithm.ofStep (uniStep Δ)

variable {V : Type*} {G : SimpleGraph V} {Δ : ℕ}

/-- `v` recolours in the reduction part of the step. -/
def Recolours (Δ : ℕ) (c : V → ZMod q × ZMod q) (v : V) : Prop :=
  (c v).1 = 0 ∧ Δ < (c v).2.val ∧ ∀ y ∈ nbrColors G c v, y.1 = 0 ∧ y.2.val < (c v).2.val

theorem uniform_run_succ (c₀ : V → ZMod q × ZMod q) (t : ℕ) (v : V) :
    (uniform q Δ).run G c₀ (t + 1) v =
      haveI := Classical.dec
      if Recolours (G := G) Δ ((uniform q Δ).run G c₀ t) v then
        (0, freeColor (nbrColors G ((uniform q Δ).run G c₀ t) v))
      else agStep ((uniform q Δ).run G c₀ t v) (nbrColors G ((uniform q Δ).run G c₀ t) v) := by
  rw [Algorithm.run_succ_apply]
  simp only [uniform, Algorithm.ofStep, uniStep, Recolours]
  congr 1

omit [NeZero q] in
theorem recolours_of_adj {c : V → ZMod q × ZMod q} {u v : V} (huv : G.Adj u v)
    (h : Recolours (G := G) Δ c v) : (c u).1 = 0 ∧ ¬ Recolours (G := G) Δ c u := by
  have hu := h.2.2 (c u) (mem_nbrColors_of_adj c huv.symm)
  refine ⟨hu.1, fun h' => ?_⟩
  have := (h'.2.2 (c v) (mem_nbrColors_of_adj c huv)).2
  omega

variable [G.LocallyFinite]

omit [NeZero q] in
theorem freeColor_val (hΔ : ∀ v, G.degree v ≤ Δ) (hq : Δ < q) (c : V → ZMod q × ZMod q) (v : V) :
    (freeColor (nbrColors G c v)).val = firstFree ((fun y => y.2.val) '' nbrColors G c v) ∧
      firstFree ((fun y => y.2.val) '' nbrColors G c v) ≤ Δ := by
  have hfin := (finite_nbrColors (G := G) c v).image (fun y : ZMod q × ZMod q => y.2.val)
  have hle : firstFree ((fun y => y.2.val) '' nbrColors G c v) ≤ Δ :=
    (firstFree_le_ncard hfin).trans ((Set.ncard_image_le (finite_nbrColors (G := G) c v)).trans
      ((ncard_nbrColors_le c v).trans (hΔ v)))
  exact ⟨ZMod.val_cast_of_lt (by omega), hle⟩

/-- Every colouring computed by the uniform algorithm from a proper colouring is proper. -/
theorem uniform_isProper (hΔ : ∀ v, G.degree v ≤ Δ) (hq : Δ < q) {c₀ : V → ZMod q × ZMod q}
    (h₀ : IsProper G c₀) (t : ℕ) : IsProper G ((uniform q Δ).run G c₀ t) := by
  classical
  induction t with
  | zero => exact h₀
  | succ t ih =>
    set c := (uniform q Δ).run G c₀ t
    -- a recolouring vertex gets a colour different from all (unchanged) neighbours
    have key : ∀ u v, G.Adj u v → Recolours (G := G) Δ c v →
        (0, freeColor (nbrColors G c v)) ≠ c u := by
      intro u v huv hv he
      have hmem : (c u).2.val ∈ (fun y : ZMod q × ZMod q => y.2.val) '' nbrColors G c v :=
        ⟨c u, mem_nbrColors_of_adj c huv.symm, rfl⟩
      rw [← he, (freeColor_val hΔ hq c v).1] at hmem
      exact firstFree_notMem ((finite_nbrColors c v).image _) hmem
    intro u v huv
    rw [uniform_run_succ, uniform_run_succ]
    by_cases hv : Recolours (G := G) Δ c v
    · obtain ⟨hu0, hu⟩ := recolours_of_adj huv hv
      rw [ite_eq_right hu, ite_eq_left hv, agStep_of_fst_eq_zero _ _ hu0]
      exact (key u v huv hv).symm
    · by_cases hu : Recolours (G := G) Δ c u
      · obtain ⟨hv0, -⟩ := recolours_of_adj huv.symm hu
        rw [ite_eq_left hu, ite_eq_right hv, agStep_of_fst_eq_zero _ _ hv0]
        exact key v u huv.symm hu
      · rw [ite_eq_right hu, ite_eq_right hv]
        exact agStep_ne huv (ih huv)

omit [G.LocallyFinite] in
/-- The running-time analysis of AG applies to the uniform algorithm. -/
theorem isAGRun_uniform (c₀ : V → ZMod q × ZMod q) :
    IsAGRun G ((uniform q Δ).run G c₀) where
  working t v h := by
    classical
    rw [uniform_run_succ] at h ⊢
    split_ifs at h ⊢ with hr
    · exact absurd rfl h
    · have hagRun := isAGRun_ag (G := G) (fun w => (uniform q Δ).run G c₀ t w)
      have := hagRun.working 0 v (by simpa [Algorithm.run_succ_apply, ag, Algorithm.ofStep] using h)
      simpa [Algorithm.run_succ_apply, ag, Algorithm.ofStep] using this
  final t v h := by
    classical
    rw [uniform_run_succ]
    split_ifs
    · rfl
    · rw [agStep_of_fst_eq_zero _ _ h]; exact h
  stable t u w h huw hw := by
    classical
    rw [uniform_run_succ, ite_eq_right, agStep_of_fst_eq_zero _ _ h]
    exact fun hr => hw (hr.2.2 _ (mem_nbrColors_of_adj _ huw)).1

/-- Once all vertices are final and all second coordinates are `< K` or `≤ Δ` (`K > Δ + 1`), one
round of the uniform algorithm lowers the bound to `K - 1`. -/
theorem uniform_reduce_step (hΔ : ∀ v, G.degree v ≤ Δ) (hq : Δ < q) {c₀ : V → ZMod q × ZMod q}
    (h₀ : IsProper G c₀) {t K : ℕ}
    (hfin : ∀ v, ((uniform q Δ).run G c₀ t v).1 = 0)
    (hK : ∀ v, ((uniform q Δ).run G c₀ t v).2.val < K ∨ ((uniform q Δ).run G c₀ t v).2.val ≤ Δ) :
    (∀ v, ((uniform q Δ).run G c₀ (t + 1) v).1 = 0) ∧
    ∀ v, ((uniform q Δ).run G c₀ (t + 1) v).2.val < K - 1 ∨
      ((uniform q Δ).run G c₀ (t + 1) v).2.val ≤ Δ := by
  classical
  set c := (uniform q Δ).run G c₀ t
  have hp := uniform_isProper hΔ hq h₀ t
  constructor
  · intro v
    rw [uniform_run_succ]
    split_ifs
    · rfl
    · rw [agStep_of_fst_eq_zero _ _ (hfin v)]; exact hfin v
  · intro v
    rw [uniform_run_succ]
    by_cases hr : Recolours (G := G) Δ c v
    · rw [ite_eq_left hr]
      right
      exact (freeColor_val hΔ hq c v).1 ▸ (freeColor_val hΔ hq c v).2
    · rw [ite_eq_right hr, agStep_of_fst_eq_zero _ _ (hfin v)]
      by_contra hcon
      push Not at hcon
      have hval : (c v).2.val = K - 1 := by rcases hK v with h | h <;> omega
      apply hr
      refine ⟨hfin v, by omega, ?_⟩
      rintro _ ⟨u, hvu, rfl⟩
      refine ⟨hfin u, ?_⟩
      have hne : (c u).2.val ≠ (c v).2.val := fun he =>
        hp hvu.symm (Prod.ext ((hfin u).trans (hfin v).symm) (ZMod.val_injective q he))
      rcases hK u with h | h <;> omega

/-- **Self-stabilizing-style `(Δ + 1)`-colouring (paragraph before Theorem 4.4 of [BEG18]), from a
proper `GF(q)²`-colouring.** `q` prime, `2Δ < q`, maximum degree `≤ Δ`: the uniform
(round-independent) algorithm keeps a proper colouring in every round and after `2q - (Δ + 1)`
rounds every colour is `⟨0, b⟩` with `b ≤ Δ`. -/
theorem uniform_le [Fact q.Prime] (hΔ : ∀ v, G.degree v ≤ Δ) (hq : 2 * Δ < q)
    {c₀ : V → ZMod q × ZMod q} (h₀ : IsProper G c₀) {t : ℕ} (ht : 2 * q - (Δ + 1) ≤ t) (v : V) :
    ((uniform q Δ).run G c₀ t v).1 = 0 ∧ ((uniform q Δ).run G c₀ t v).2.val ≤ Δ := by
  have hq' : Δ < q := by omega
  have hR := isAGRun_uniform (G := G) (Δ := Δ) c₀
  -- all final from round `q` on
  have hfinq : ∀ v, ((uniform q Δ).run G c₀ (1 * q) v).1 = 0 :=
    hR.allFinal h₀ hΔ (by omega)
  rw [one_mul] at hfinq
  have inv : ∀ s, (∀ v, ((uniform q Δ).run G c₀ (q + s) v).1 = 0) ∧
      ∀ v, ((uniform q Δ).run G c₀ (q + s) v).2.val < q - s ∨
        ((uniform q Δ).run G c₀ (q + s) v).2.val ≤ Δ := by
    intro s
    induction s with
    | zero => exact ⟨hfinq, fun v => Or.inl (by simpa using ZMod.val_lt _)⟩
    | succ s ih =>
      have := uniform_reduce_step hΔ hq' h₀ ih.1 ih.2
      rw [show q - s - 1 = q - (s + 1) by omega] at this
      exact this
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show q ≤ t by omega)
  refine ⟨(inv s).1 v, ?_⟩
  rcases (inv s).2 v with h | h <;> omega

end BEG18
