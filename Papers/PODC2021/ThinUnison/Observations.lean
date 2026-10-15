import Papers.PODC2021.ThinUnison.LvlTac

/-!
# AlgAU: fundamental properties (Section 2.3.1, Observations 2.1–2.9)

The pairwise invariants are first proved as statements about integers (`*_pure`), from which the
execution versions follow via `AURun.moveRel`.
-/

namespace ThinUnison

open Cslib.StoneAge

section Pure

variable {k : ℕ}

/-- Adjacency of levels without `fwd`. -/
theorem lAdj_iff {a b : ℤ} : LAdj k a b ↔ a = b ∨ (b = -1 ∧ a = 1) ∨ (b ≠ -1 ∧ b = k ∧ a = -k) ∨
    (b ≠ -1 ∧ b ≠ k ∧ a = b + 1) ∨ (a = -1 ∧ b = 1) ∨ (a ≠ -1 ∧ a = k ∧ b = -k) ∨
    (a ≠ -1 ∧ a ≠ k ∧ b = a + 1) := by
  unfold LAdj fwd; split_ifs <;> omega

/-- Core of Observation 2.1. -/
theorem obs21_pure {a b a' b' : ℤ} {f g : Bool} (ha : IsLevel k a) (hb : IsLevel k b)
    (hf : f = true → 2 ≤ a ∨ a ≤ -2) (hg : g = true → 2 ≤ b ∨ b ≤ -2)
    (ma : MoveRel k a a' f b g) (mb : MoveRel k b b' g a f) (h : LAdj k a b)
    (hk : ¬ (a = k ∧ b = -k)) (hk' : ¬ (a = -k ∧ b = k)) : LAdj k a' b' := by
  unfold MoveRel Outward at ma mb
  unfold LAdj at *
  cases f <;> cases g <;> simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, and_false,
    or_false, false_or, true_and, true_implies, IsEmpty.forall_iff] at * <;>
  rcases ma with rfl | ⟨h1, rfl⟩ <;> rcases mb with rfl | ⟨h2, rfl⟩
  all_goals (rcases h with rfl | rfl | rfl <;> lvl_omega)

/-- Core of Observation 2.3: out-protection is preserved (pairwise). -/
theorem obs23_pure {a b a' b' : ℤ} {f g : Bool} (ha : IsLevel k a) (hb : IsLevel k b)
    (hf : f = true → 2 ≤ a ∨ a ≤ -2) (hg : g = true → 2 ≤ b ∨ b ≤ -2)
    (ma : MoveRel k a a' f b g) (mb : MoveRel k b b' g a f) (h : ¬ FarOut a b) :
    ¬ FarOut a' b' := by
  unfold MoveRel at ma mb
  cases f <;> cases g <;> simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, and_false,
    or_false, false_or, true_and, true_implies, IsEmpty.forall_iff] at * <;>
  rcases ma with rfl | ⟨h1, rfl⟩ <;> rcases mb with rfl | ⟨h2, rfl⟩ <;>
  (try rcases h1 with rfl | rfl) <;> (try rcases h2 with h2 | h2) <;> lvl_omega

/-- Core of Observation 2.4: a node that changes its level is out-protected afterwards. -/
theorem obs24_pure {a b a' b' : ℤ} {f g : Bool} (ha : IsLevel k a) (hb : IsLevel k b)
    (hf : f = true → 2 ≤ a ∨ a ≤ -2) (hg : g = true → 2 ≤ b ∨ b ≤ -2)
    (ma : MoveRel k a a' f b g) (mb : MoveRel k b b' g a f) (hne : a' ≠ a) :
    ¬ FarOut a' b' := by
  unfold MoveRel at ma mb
  cases f <;> cases g <;> simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, and_false,
    or_false, false_or, true_and, true_implies, IsEmpty.forall_iff] at * <;>
  rcases ma with rfl | ⟨h1, rfl⟩ <;> rcases mb with rfl | ⟨h2, rfl⟩ <;>
  (try rcases h1 with rfl | rfl) <;> (try rcases h2 with h2 | h2) <;> lvl_omega

/-- Core of Observation 2.5: across a non-protected edge, the levels move towards each other. -/
theorem obs25_pure {a b a' b' : ℤ} {f g : Bool} (ha : IsLevel k a) (hb : IsLevel k b)
    (hf : f = true → 2 ≤ a ∨ a ≤ -2) (hg : g = true → 2 ≤ b ∨ b ≤ -2)
    (ma : MoveRel k a a' f b g) (mb : MoveRel k b b' g a f) (h : ¬ LAdj k a b) (hab : a < b) :
    a ≤ a' ∧ a' < b' ∧ b' ≤ b := by
  unfold MoveRel at ma mb
  cases f <;> cases g <;> simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, and_false,
    or_false, false_or, true_and, true_implies, IsEmpty.forall_iff] at * <;>
  rcases ma with rfl | ⟨h1, rfl⟩ <;> rcases mb with rfl | ⟨h2, rfl⟩ <;>
  (try rcases h1 with rfl | rfl) <;> (try rcases h2 with rfl | rfl) <;> lvl_omega

/-- Adjacent levels have magnitudes differing by at most one. -/
theorem natAbs_le_of_lAdj {a b : ℤ} (ha : IsLevel k a) (hb : IsLevel k b) (h : LAdj k a b) :
    b.natAbs ≤ a.natAbs + 1 := by
  rcases h with rfl | rfl | rfl <;> lvl_omega

end Pure

/-! ## Execution versions -/

namespace AURun

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}
variable (hC : AURun G A C)
include hC

/-- Observation 2.1: a protected edge whose levels are not `{-k, k}` stays protected. -/
theorem obs21 {t : ℕ} {u v : V} (huv : G.Adj u v) (h : LAdj k (C t u).lvl (C t v).lvl)
    (hk : ¬ ((C t u).lvl = k ∧ (C t v).lvl = -k)) (hk' : ¬ ((C t u).lvl = -k ∧ (C t v).lvl = k)) :
    LAdj k (C (t + 1) u).lvl (C (t + 1) v).lvl :=
  obs21_pure (C t u).isLevel (C t v).isLevel (C t u).faulty_two (C t v).faulty_two
    (hC.moveRel huv) (hC.moveRel huv.symm) h hk hk'

/-- Observation 2.2: a protected node whose level is not `±k` stays protected. -/
theorem obs22 {t : ℕ} {v : V} (h : Prot G C t v) (hk : (C t v).lvl ≠ k) (hk' : (C t v).lvl ≠ -k) :
    Prot G C (t + 1) v := fun u hu =>
  hC.obs21 hu (h u hu) (fun h' => hk h'.1) (fun h' => hk' h'.1)

/-- Observation 2.3: out-protected nodes stay out-protected. -/
theorem obs23 {t : ℕ} {v : V} (h : OutProt G C t v) : OutProt G C (t + 1) v := fun u hu =>
  obs23_pure (C t v).isLevel (C t u).isLevel (C t v).faulty_two (C t u).faulty_two
    (hC.moveRel hu) (hC.moveRel hu.symm) (h u hu)

theorem outProt_le {t s : ℕ} {v : V} (h : OutProt G C t v) (hts : t ≤ s) : OutProt G C s v := by
  induction s, hts using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact hC.obs23 ih

/-- Observation 2.4: a node that changes its level is out-protected afterwards. -/
theorem obs24 {t : ℕ} {v : V} (h : (C (t + 1) v).lvl ≠ (C t v).lvl) : OutProt G C (t + 1) v :=
  fun u hu => obs24_pure (C t v).isLevel (C t u).isLevel (C t v).faulty_two (C t u).faulty_two
    (hC.moveRel hu) (hC.moveRel hu.symm) h

/-- Observation 2.5: across a non-protected edge with `λ_u < λ_v`,
`λ_u ≤ λ'_u < λ'_v ≤ λ_v`. -/
theorem obs25 {t : ℕ} {u v : V} (huv : G.Adj u v) (h : ¬ LAdj k (C t u).lvl (C t v).lvl)
    (hlt : (C t u).lvl < (C t v).lvl) :
    (C t u).lvl ≤ (C (t + 1) u).lvl ∧ (C (t + 1) u).lvl < (C (t + 1) v).lvl ∧
      (C (t + 1) v).lvl ≤ (C t v).lvl :=
  obs25_pure (C t u).isLevel (C t v).isLevel (C t u).faulty_two (C t v).faulty_two
    (hC.moveRel huv) (hC.moveRel huv.symm) h hlt

/-- Observation 2.6: `ℓ`-out-protection is preserved. -/
theorem obs26 {t : ℕ} {ℓ : ℤ} (h : LOutProt G C t ℓ) : LOutProt G C (t + 1) ℓ := by
  intro v hv
  by_cases hl : (C (t + 1) v).lvl = (C t v).lvl
  · exact hC.obs23 (h v (hl ▸ hv))
  · exact hC.obs24 hl

theorem lOutProt_le {t s : ℕ} {ℓ : ℤ} (h : LOutProt G C t ℓ) (hts : t ≤ s) :
    LOutProt G C s ℓ := by
  induction s, hts using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact hC.obs26 ih

theorem allOutProt_le {t s : ℕ} (h : AllOutProt G C t) (hts : t ≤ s) : AllOutProt G C s :=
  fun v => hC.outProt_le (h v) hts

omit hC in
/-- Along a walk of protected nodes, the magnitude of the level grows by at most one per edge
(the content of Observation 2.7 needed later). -/
theorem natAbs_le_of_walk {t : ℕ} {v u : V} (p : G.Walk v u)
    (hp : ∀ w ∈ p.support, Prot G C t w) :
    ∀ w ∈ p.support, (C t w).lvl.natAbs ≤ (C t v).lvl.natAbs + p.length := by
  induction p with
  | nil => intro w hw; simp at hw; subst hw; simp
  | @cons a b c hab q ih =>
    intro w hw
    have hq : ∀ w ∈ q.support, Prot G C t w := fun w hw => hp w (by simp [hw])
    have h1 : (C t b).lvl.natAbs ≤ (C t a).lvl.natAbs + 1 :=
      natAbs_le_of_lAdj (C t a).isLevel (C t b).isLevel (hp a (by simp) b hab)
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp
    · have := ih hq w hw; simp only [SimpleGraph.Walk.length_cons]; omega

/-- Observation 2.9 (node version): if all nodes of a walk `P` from `v` of length `d` are
protected at time `t` and `|λ_v| < k - d` at all times `t ≤ s < t'`, then all nodes of `P` are
protected at time `t'`. -/
theorem obs29 {t t' : ℕ} {v u : V} (p : G.Walk v u) (hp : ∀ w ∈ p.support, Prot G C t w)
    (htt' : t ≤ t') (hv : ∀ s, t ≤ s → s < t' → (C s v).lvl.natAbs + p.length < k) :
    ∀ w ∈ p.support, Prot G C t' w := by
  induction t', htt' using Nat.le_induction with
  | base => exact hp
  | succ n hn ih =>
    have ih' := ih fun s h1 h2 => hv s h1 (by omega)
    intro w hw
    have h1 := natAbs_le_of_walk p ih' w hw
    have h2 := hv n hn (Nat.lt_succ_self n)
    exact hC.obs22 (ih' w hw) (by omega) (by omega)

end AURun

end ThinUnison
