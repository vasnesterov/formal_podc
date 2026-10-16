import Papers.PODC2020.NonEquivocation.Exec

/-!
# Strong non-equivocation (Section 3)

Madsen–Debois, PODC 2020, Section 3: under strong non-equivocation interactive consistency is
solved in **one round**: `p` sets `vec_p[q] = σ_p(p|q)` (`alg0`). The paper states this for `n > t`;
it holds for every `n` and `t` (`sne_solvesIC`). One round is optimal: with `0` rounds nothing is
learnt about the others (`not_solvesIC_zero`, any fault model containing the fault-free runs, for
`n ≥ 2`).
-/

namespace NonEquivocation

variable {P V : Type*} [Fintype P] [DecidableEq P] [OmitVal V]

/-- The one-round algorithm of Section 3: decide what the source sent in round 1. -/
def alg0 : Alg P V := fun p τ q => if p = q then rep (τ []) else rep (τ [q])

/-- **Section 3**: under strong non-equivocation, `alg0` solves interactive consistency in one round,
for any number `t` of faulty processes (the paper: for `n > t`). -/
theorem sne_solvesIC (t : ℕ) : SolvesIC sne 1 t (alg0 (P := P) (V := V)) := by
  intro F σ _ hm hpriv
  have val : ∀ p q, p ∉ F → q ∉ F → σ [q] = some (alg0 p (view 1 σ p) q) := by
    intro p q hp hq
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hpriv q hq)
    by_cases hpq : p = q
    · subst hpq; simp [alg0, view, ha]
    · have := hm.1 q (Finset.mem_univ _) hq p (Finset.mem_univ _) [] (by simp)
        (seq_pair.2 hpq) (by simp)
      simp [alg0, hpq, view, this, ha]
  refine ⟨val, fun p p' q hp hp' => ?_⟩
  by_cases hq : q ∈ F
  · have hpq : p ≠ q := fun h => hp (h ▸ hq)
    have hp'q : p' ≠ q := fun h => hp' (h ▸ hq)
    have := hm.2 q (Finset.mem_univ _) p (Finset.mem_univ _) p' (Finset.mem_univ _) []
      (by simp) (seq_pair.2 hpq) (seq_pair.2 hp'q) (by simp)
    simp [alg0, hpq, hp'q, view, this]
  · have h1 := val p q hp hq
    have h2 := val p' q hp' hq
    rw [h1] at h2
    exact Option.some.inj h2

/-! ### Zero rounds do not suffice -/

namespace ExecSys

variable {W : Type*} (E : ExecSys W P V)

omit [Fintype P] [DecidableEq P] in
/-- In a world where nobody imitates another world or omits, strong non-equivocation holds. -/
lemma strongNE_of {w : W} (h : E.Honest w ∅) (k : ℕ) (S : Finset P) : StrongNE k S (E.σ w) := by
  intro y _ r _ r' _ l _ _ _ _
  have h' := h y (Finset.notMem_empty y)
  classical
  simp only [σ_cons_cons, h'.2, h'.1, ↓reduceIte]

omit [DecidableEq P] in
lemma sne_of {w : W} (h : E.Honest w ∅) (k : ℕ) : sne k ∅ (E.σ w) :=
  ⟨E.nonFaulty_of h k _, E.strongNE_of h k _⟩

end ExecSys

/-- The fault-free runs with prescribed private values. -/
def freeSys : ExecSys (P → V) P V where
  input w y := some (w y)
  nb w _ := w
  om _ _ _ _ := False

omit [Fintype P] [DecidableEq P] [OmitVal V] in
lemma freeSys_honest (w : P → V) : (freeSys (P := P) (V := V)).Honest w ∅ :=
  fun _ _ => ⟨rfl, fun _ _ h => h⟩

/-- With `0` rounds, no algorithm solves interactive consistency (for `n ≥ 2` and two values), in
any fault model that contains the fault-free runs — in particular under strong or weak
non-equivocation. So the one round of Section 3 is optimal. -/
theorem not_solvesIC_zero [Nontrivial V] (hn : 2 ≤ Fintype.card P) (M : FaultModel P V)
    (hM : ∀ w : P → V, M 0 ∅ (freeSys.σ w)) (t : ℕ) (A : Alg P V) :
    ¬ SolvesIC M 0 t A := by
  intro hA
  obtain ⟨v, u, hvu⟩ := exists_pair_ne V
  obtain ⟨s⟩ : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card (by omega) s
  let wv : P → V := fun _ => v
  let wu : P → V := fun y => if y = s then u else v
  have dec : ∀ w : P → V, A c (view 0 (freeSys.σ w) c) s = w s := by
    intro w
    have := (hA ∅ (freeSys.σ w) (by simp) (hM w) (fun y _ => by simp [freeSys])).1 c s
      (Finset.notMem_empty _) (Finset.notMem_empty _)
    simp only [ExecSys.σ_single, freeSys] at this
    exact (Option.some.inj this).symm
  have hview : view 0 (freeSys.σ wv) c = view 0 (freeSys.σ wu) c := by
    funext l
    unfold view
    split_ifs with hl
    · rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]
      simp [freeSys, wv, wu, hc]
    · rfl
  have h1 := dec wv
  have h2 := dec wu
  rw [hview] at h1
  rw [h1] at h2
  simp [wv, wu] at h2
  exact hvu h2

/-- One round is optimal for strong non-equivocation. -/
theorem sne_not_solvesIC_zero [Nontrivial V] (hn : 2 ≤ Fintype.card P) (t : ℕ) (A : Alg P V) :
    ¬ SolvesIC sne 0 t A :=
  not_solvesIC_zero hn sne (fun w => freeSys.sne_of (freeSys_honest w) 0) t A

end NonEquivocation
