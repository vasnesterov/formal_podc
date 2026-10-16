import Papers.PODC2021.RestorableTiebreaking.Theorem19

/-!
# Definition 18 with simple paths

Definition 18 asks that `G* \ F` have a unique shortest *path* for each pair. Since `r` may be
negative, "shortest path" could mean a minimum-weight *simple path* (`IsATWPath`) or a
minimum-weight *walk* (`IsATW`, used in `theorem19`). The two readings agree
(`isATW_iff_isATWPath`): the simple-path reading already forces every closed walk of `G*` to
have positive weight (each closed walk `x → a ⇝ x` weighs at least `w(x,a) + w(a,x) = 2`, because
the edge `a → x` is the unique lightest `a ⇝ x` path), so lightest walks are simple paths.
Hence Theorem 19 holds for the literal Definition 18 as well (`theorem19_path`).
-/

open Finset SimpleGraph SimpleGraph.Walk

set_option linter.unusedSectionVars false

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r : V → V → ℝ} {f : ℕ}

variable (G) in
/-- `p` is the unique lightest simple `s ⇝ t` path of `G* \ A`. -/
def IsMinPath (r : V → V → ℝ) (A : Set (Sym2 V)) {s t : V} (p : G.Walk s t) : Prop :=
  p.IsPath ∧ p.Avoids A ∧
    ∀ q : G.Walk s t, q.IsPath → q.Avoids A → q ≠ p → p.dwt (wstar r) < q.dwt (wstar r)

variable (G) in
/-- Definition 18 read with simple paths. -/
structure IsATWPath (f : ℕ) (r : V → V → ℝ) : Prop where
  antisymm : ∀ u v, G.Adj u v → r u v = - r v u
  tiebreak : ∀ F : Finset (Sym2 V), #F ≤ f → ∀ s t, (G.deleteEdges F).Reachable s t →
    ∃ p : G.Walk s t, IsMinPath G r F p ∧ p.IsShortestIn F

lemma wstar_add (hanti : ∀ u v, G.Adj u v → r u v = - r v u) {u v : V} (h : G.Adj u v) :
    wstar r u v + wstar r v u = 2 := by
  simp only [wstar, hanti u v h]; ring

/-- Under the simple-path reading, every closed walk of positive length has positive weight. -/
lemma IsATWPath.closed_pos (hr : IsATWPath G f r) :
    ∀ n, ∀ (x : V) (c : G.Walk x x), 0 < c.length → c.length ≤ n → 0 < c.dwt (wstar r) := by
  intro n
  induction n with
  | zero => intro x c h1 h2; omega
  | succ n ih =>
    intro x c hpos hlen
    cases c with
    | nil => simp at hpos
    | @cons _ a _ hxa c' =>
      rw [length_cons] at hlen
      have hb := (dwt_bypass_le (wstar r) n ih c' (by omega)).1
      obtain ⟨p, hpM, hpS⟩ := hr.tiebreak ∅ (by simp) a x
        (by simpa using hxa.symm.reachable)
      have hp1 : p = cons hxa.symm nil := by
        have := hpS.2
        simp only [coe_empty, deleteEdges_empty, edist_eq_one_iff_adj.mpr hxa.symm] at this
        have hl : p.length = 1 := by exact_mod_cast this
        cases p with
        | nil => simp at hl
        | cons h q =>
          cases q with
          | nil => rfl
          | cons h' q' => simp at hl
      have hle : p.dwt (wstar r) ≤ c'.bypass.dwt (wstar r) := by
        by_cases heq : c'.bypass = p
        · rw [heq]
        · exact (hpM.2.2 _ c'.bypass_isPath (by simp [Avoids]) heq).le
      rw [hp1, dwt_cons, dwt_nil] at hle
      rw [dwt_cons]
      have := wstar_add hr.antisymm hxa
      linarith

/-- Definition 18 with simple paths implies Definition 18 with walks. -/
theorem IsATWPath.isATW (hr : IsATWPath G f r) : IsATW G f r := by
  refine ⟨hr.antisymm, fun F hF s t hst => ?_⟩
  obtain ⟨p, ⟨hpP, hpA, hpmin⟩, hpS⟩ := hr.tiebreak F hF s t hst
  refine ⟨p, ⟨hpA, fun q hq hne => ?_⟩, hpS⟩
  by_cases hqP : q.IsPath
  · exact hpmin q hqP hq hne
  · have hb := dwt_bypass_le (wstar r) q.length (fun x c h1 _ => hr.closed_pos _ x c h1 le_rfl)
      q le_rfl
    have hbq : q.bypass ≠ q := fun h => hqP (h ▸ q.bypass_isPath)
    have hbA : q.bypass.Avoids F := fun e he => hq e (q.edges_bypass_subset_edges he)
    have : p.dwt (wstar r) ≤ q.bypass.dwt (wstar r) := by
      by_cases heq : q.bypass = p
      · rw [heq]
      · exact (hpmin _ q.bypass_isPath hbA heq).le
    linarith [hb.2 hbq]

/-- Definition 18 with walks implies Definition 18 with simple paths. -/
theorem IsATW.isATWPath (hr : IsATW G f r) : IsATWPath G f r := by
  refine ⟨hr.antisymm, fun F hF s t hst => ?_⟩
  obtain ⟨p, ⟨hpA, hpmin⟩, hpS⟩ := hr.tiebreak F hF s t hst
  exact ⟨p, ⟨hpS.isPath, hpA, fun q _ hq hne => hpmin q hq hne⟩, hpS⟩

theorem isATW_iff_isATWPath : IsATW G f r ↔ IsATWPath G f r :=
  ⟨IsATW.isATWPath, IsATWPath.isATW⟩

/-- **Theorem 19** for the literal (simple-path) reading of Definition 18. -/
theorem theorem19_path (hr : IsATWPath G f r) :
    IsRPTS G f (atwScheme G r) ∧ IsStable G f (atwScheme G r) ∧
      IsConsistent G f (atwScheme G r) ∧ IsRestorable G f (atwScheme G r) :=
  theorem19 hr.isATW

end RestorableTiebreaking
