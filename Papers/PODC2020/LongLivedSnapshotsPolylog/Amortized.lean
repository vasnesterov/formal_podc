import Papers.PODC2020.LongLivedSnapshotsPolylog.LinBasic
import Papers.PODC2020.LongLivedSnapshotsPolylog.Section4Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The counting core of Lemma 3.6 (amortized step complexity of Algorithm 1)

The proof of Lemma 3.6 bounds the number `|L_u|` of completed unsuccessful loop iterations:
by Observation 6, two unsuccessful iterations of the same process have different indices
`⌊r₁/m⌋ + ⌊l/m⌋`, all below the final `h* = ⌊MR_left/m⌋ + ⌊MR_right/m⌋`, so
`|L_u| ≤ n · h*` (eq. (7)); and in an `ℓ`-bounded-increment execution `h* ≤ ℓ |W| / m`
(eq. (6), with `ℓ = n`). With `m ≥ n²` this gives `|L_u| ≤ |W|`, hence `O(|W| + |S|)` loop
iterations in total; every iteration costs `O(1)` accesses to the base objects plus a collect
(`n` reads) every `X` iterations.

We prove this counting argument for Algorithm 1 over atomic base objects:

* `fails α p` is the number of unsuccessful iterations of `p` in `α` (steps at which a test of
  line 13 or line 18 fails);
* `fails_le`: `fails α p ≤ ⌊MR_left/m⌋ + ⌊MR_right/m⌋` at the end of `α` (Observation 6);
* `vL_le`, `vR_le`: in an `ℓ`-bounded-increment execution, `MR_left ≤ ℓ · #writes(MR_left)`
  (and likewise for `MR_right`);
* `lemma_3_6_unsuccessful`: `m · Σ_p fails α p ≤ n · ℓ · |W|`, where `|W|` is the number of
  `WriteMax` steps of line 4 (at most the number of `MaxUpdate`s), and
  `lemma_3_6_unsuccessful_of_sq`: if `n · ℓ ≤ m` (e.g. `ℓ = n`, `m ≥ n²`) then
  `Σ_p fails α p ≤ |W|`.

The amortized costs of the black boxes ([12] and the bounded max arrays of [4]) are not modelled.
-/

namespace Podc.LongLivedSnapshotsPolylog.Amortized

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

variable {n m X : ℕ}

variable (m) in
/-- The step of `p` from `C` is the failing test of an unsuccessful iteration (line 13 or one of
the two reads of line 18). -/
def failStep (C : Cfg n) (p : Fin n) : Bool :=
  match (C.loc p).pc with
  | .rdR2 _ r1 _ => decide (r1 / m ≠ vR C / m)
  | .chkL _ l _ _ => decide (vL C / m ≠ l / m)
  | .chkR _ _ r2 _ => decide (vR C / m ≠ r2 / m)
  | _ => false

variable (m X) in
/-- The number of unsuccessful loop iterations of `p` in `α`. -/
noncomputable def fails (α : List (Lbl n)) (p : Fin n) : ℕ :=
  ((List.range α.length).filter (fun t =>
    ((α[t]?).map (·.isTauOf p)).getD false && failStep m (cfgAt m X α t) p)).length

lemma fails_snoc {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) (ℓ : Lbl n)
    (p : Fin n) :
    fails m X (α ++ [ℓ]) p = fails m X α p + if ℓ.isTauOf p && failStep m C p then 1 else 0 := by
  unfold fails
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
    List.length_append]
  congr 1
  · congr 1
    apply List.filter_congr
    intro t ht
    have ht' : t < α.length := List.mem_range.1 ht
    rw [List.getElem?_append_left ht', cfgAt_append (le_of_lt ht')]
  · have e : cfgAt m X (α ++ [ℓ]) α.length = C := by rw [cfgAt_append le_rfl, cfgAt_length h]
    simp only [List.filter_cons, List.filter_nil, List.getElem?_concat_length, Option.map_some,
      Option.getD_some, e]
    split <;> simp_all

/-- The per-process invariant: the number `k` of unsuccessful iterations of `p` is at most the
index of the current iteration (computed from the values read so far). -/
def FIL (k : ℕ) (C : Cfg n) : PC n → Prop
  | .rdL _ r1 => r1 ≤ vR C ∧ k ≤ r1 / m + vL C / m
  | .rdR2 _ r1 l => r1 ≤ vR C ∧ l ≤ vL C ∧ k ≤ r1 / m + l / m
  | .upL _ l r2 => l ≤ vL C ∧ r2 ≤ vR C ∧ k ≤ l / m + r2 / m
  | .upR _ l r2 => l ≤ vL C ∧ r2 ≤ vR C ∧ k ≤ l / m + r2 / m
  | .scanMA _ l r2 => l ≤ vL C ∧ r2 ≤ vR C ∧ k ≤ l / m + r2 / m
  | .chkL _ l r2 _ => l ≤ vL C ∧ r2 ≤ vR C ∧ k ≤ l / m + r2 / m
  | .chkR _ l r2 _ => l ≤ vL C ∧ r2 ≤ vR C ∧ k ≤ l / m + r2 / m
  | _ => True

variable (m) in
/-- The invariant of a process. -/
def FI (k : ℕ) (C : Cfg n) (p : Fin n) : Prop :=
  k ≤ vL C / m + vR C / m ∧ FIL (m := m) k C (C.loc p).pc

lemma fil_afterFail (k : ℕ) (C : Cfg n) (i : Fin n) (cs : CS n) :
    FIL (m := m) k C (afterFail X i cs) := by
  unfold afterFail; split_ifs <;> trivial

lemma fil_retOf (k : ℕ) (C : Cfg n) (cs : CS n) (v : ℕ × ℕ) : FIL (m := m) k C (retOf cs v) := by
  unfold retOf; split_ifs <;> trivial

lemma fil_afterCollect (k : ℕ) (C : Cfg n) (cs : CS n) (f : Bool) (acc : Fin n → HEntry) :
    FIL (m := m) k C (afterCollect cs f acc) := by
  unfold afterCollect
  split
  · trivial
  · split
    · exact fil_retOf _ _ _ _
    · trivial

lemma fil_mono {k : ℕ} {C C' : Cfg n} {pc : PC n} (hL : vL C ≤ vL C') (hR : vR C ≤ vR C')
    (h : FIL (m := m) k C pc) : FIL (m := m) k C' pc := by
  have dL := Nat.div_le_div_right (c := m) hL
  cases pc <;> simp only [FIL] at h ⊢ <;> omega

lemma fi_step {α : List (Lbl n)} {C C' : Cfg n} {ℓ : Lbl n}
    (hrun : (alg1 n m X).run α = some C) (hs : (alg1 n m X).step C ℓ = some C') (p : Fin n)
    (h : FI m (fails m X α p) C p) : FI m (fails m X (α ++ [ℓ]) p) C' p := by
  obtain ⟨-, hL, hR, -, -⟩ := step_basic (basicInv_run hrun) hs
  have dL := Nat.div_le_div_right (c := m) hL
  have dR := Nat.div_le_div_right (c := m) hR
  rw [fails_snoc hrun ℓ p]
  obtain ⟨h1, h2⟩ := h
  -- steps of other processes leave `p`'s local state alone
  by_cases hq : ℓ.proc = p
  swap
  · have hloc : C'.loc p = C.loc p := (Impl.step_other hs hq).1
    have : (ℓ.isTauOf p && failStep m C p) = false := by
      cases ℓ <;> simp_all [Label.proc]
    rw [this]
    exact ⟨by simp; omega, by rw [hloc]; exact fil_mono hL hR h2⟩
  cases ℓ with
  | inv q o =>
    simp only [Label.proc] at hq; subst hq
    obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv hs
    refine ⟨by simp; omega, ?_⟩
    rw [hloc, Function.update_self]; cases o <;> trivial
  | ret q r =>
    simp only [Label.proc] at hq; subst hq
    obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret hs
    refine ⟨by simp; omega, ?_⟩
    rw [hloc, Function.update_self]
    rcases hpc : (C.loc q).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, f, k, acc⟩ | r' <;> simp [act, hpc] at hact <;> rw [← hact.2] <;> simp [hpc, FIL]
  | tau q =>
    simp only [Label.proc] at hq; subst hq
    have hs0 := hs
    simp only [Impl.step] at hs
    split_ifs at hs with hc
    rcases hpc : (C.loc q).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, f, k, acc⟩ | r <;>
      simp [act, hpc] at hs <;> subst hs <;> rw [hpc] at h2 <;>
      simp only [FI, Label.isTauOf_tau, decide_true, Bool.true_and, failStep, hpc,
        Function.update_self] at h2 ⊢
    case neg.wm.false =>
      simp only [vL, vR, Function.update_self] at dL dR ⊢
      exact ⟨by simp only [Bool.false_eq_true, ↓reduceIte]; simp only [vL, vR] at h1; omega, trivial⟩
    case neg.wm.true =>
      simp only [vL, vR, Function.update_self] at dL dR ⊢
      exact ⟨by simp only [Bool.false_eq_true, ↓reduceIte]; simp only [vL, vR] at h1; omega, trivial⟩
    case neg.rdR2 =>
      obtain ⟨g1, g2, g3⟩ := h2
      have e1 := Nat.div_le_div_right (c := m) g1
      have e2 := Nat.div_le_div_right (c := m) g2
      simp only [vL, vR] at e1 e2 g1 g2 h1 dL dR ⊢
      by_cases hr : r1 / m = C.mem Obj.mrR / m
      · simp only [hr, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero, FIL]
        exact ⟨by omega, g2, le_rfl, by omega⟩
      · simp only [hr, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
        exact ⟨by omega, fil_afterFail _ _ _ _⟩
    case neg.chkL =>
      obtain ⟨g1, g2, g3⟩ := h2
      have e1 := Nat.div_le_div_right (c := m) g1
      have e2 := Nat.div_le_div_right (c := m) g2
      split_ifs with ha hb hb
      · exact ((by simpa using ha : ¬ vL C / m = l / m) hb).elim
      · have hne : ¬ vL C / m = l / m := hb
        exact ⟨(show fails m X α q + 1 ≤ vL C / m + vR C / m by omega), fil_afterFail _ _ _ _⟩
      · exact ⟨(show fails m X α q + 0 ≤ vL C / m + vR C / m by omega), g1, g2, g3⟩
      · exact (hb (show vL C / m = l / m by simpa using ha)).elim
    case neg.chkR =>
      obtain ⟨g1, g2, g3⟩ := h2
      have e1 := Nat.div_le_div_right (c := m) g1
      have e2 := Nat.div_le_div_right (c := m) g2
      split_ifs with ha hb hb
      · exact ((by simpa using ha : ¬ vR C / m = r2 / m) hb).elim
      · have hne : ¬ vR C / m = r2 / m := hb
        exact ⟨(show fails m X α q + 1 ≤ vL C / m + vR C / m by omega), fil_afterFail _ _ _ _⟩
      · exact ⟨(show fails m X α q + 0 ≤ vL C / m + vR C / m by omega), trivial⟩
      · exact (hb (show vR C / m = r2 / m by simpa using ha)).elim
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      refine ⟨by omega, ?_⟩
    case neg.rdR1 => exact ⟨le_rfl, (show fails m X α q ≤ vR C / m + vL C / m by omega)⟩
    case neg.rdL => exact ⟨h2.1, le_rfl, h2.2⟩
    case neg.upL => exact fil_mono hL hR h2
    case neg.upR => exact fil_mono hL hR h2
    case neg.scanMA => exact fil_mono hL hR h2
    case neg.wH => exact fil_retOf _ _ _ _
    case neg.col =>
      split
      · trivial
      · exact fil_afterCollect _ _ _ _ _

/-- **Observation 6 / eq. (7) of the paper**, per process: the number of unsuccessful
iterations of `p` is at most the final sum `h*` of the high-order bits of `MR_left` and
`MR_right`. -/
theorem fails_le {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) (p : Fin n) :
    fails m X α p ≤ vL C / m + vR C / m := by
  have := Impl.run_induction (Q := fun α C => ∀ p, FI m (fails m X α p) C p) (I := alg1 n m X)
    (fun p => by simp [FI, fails, Impl.initCfg, FIL]) (fun α C ℓ C' hr hI hs p =>
      fi_step hr hs p (hI p)) h p
  exact this.1

lemma lmax_le_of_stepBounded {ℓ : ℕ} {ws : List ℕ} (h : StepBounded ℓ ws) :
    lmax ws ≤ ℓ * ws.length := by
  have key : ∀ k, k ≤ ws.length → lmax (ws.take k) ≤ ℓ * k := by
    intro k
    induction k with
    | zero => intro; simp
    | succ k ih =>
      intro hk
      rw [List.take_succ_eq_append_getElem (by omega), lmax_append]
      have h1 := ih (by omega)
      have h2 := h k (by omega)
      simp only [lmax_cons, lmax_nil]
      rw [Nat.mul_succ]
      exact max_le (h1.trans (Nat.le_add_right _ _)) (max_le (by omega) (Nat.zero_le _))
  simpa using key ws.length le_rfl

/-- `MR_left` and `MR_right` hold the maximum of the values written to them. -/
theorem mr_eq_lmax {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) :
    vL C = lmax (writesTo (alg1 n m X) wm1 α false) ∧
      vR C = lmax (writesTo (alg1 n m X) wm1 α true) := by
  refine Impl.run_induction (I := alg1 n m X)
    (Q := fun α C => vL C = lmax (writesTo (alg1 n m X) wm1 α false) ∧
      vR C = lmax (writesTo (alg1 n m X) wm1 α true))
    ⟨by simp [vL, Impl.initCfg, memInit, writesTo, wlogFrom],
      by simp [vR, Impl.initCfg, memInit, writesTo, wlogFrom]⟩ ?_ h
  intro α C ℓ C' hr ⟨ih1, ih2⟩ hs
  have hw : ∀ k, writesTo (alg1 n m X) wm1 (α ++ [ℓ]) k = writesTo (alg1 n m X) wm1 α k ++
      (Section4.stepLog wm1 C ℓ).filterMap (Section4.selK k) := by
    intro k
    simp only [writesTo]
    rw [Section4.wlogFrom_append (alg1 n m X) wm1 α hr [ℓ],
      Section4.wlogFrom_singleton (alg1 n m X) wm1 hs, List.filterMap_append]
    rfl
  rw [hw, hw, lmax_append, lmax_append, ← ih1, ← ih2]
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, -, hm⟩ := Impl.step_inv hs
    simp [Section4.stepLog, vL, vR, hm]
  | ret p r =>
    obtain ⟨-, -, hm, -⟩ := Impl.step_ret hs
    simp [Section4.stepLog, vL, vR, hm]
  | tau p =>
    simp only [Impl.step] at hs
    split_ifs at hs with hc
    rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, f, k, acc⟩ | r <;>
      simp [act, hpc] at hs <;> subst hs <;>
      simp [Section4.stepLog, Section4.selK, wm1, hpc, vL, vR, lmax]

/-- **Eqs. (6)–(7) of the proof of Lemma 3.6**: in an `ℓ`-bounded-increment execution, the
total number of unsuccessful iterations of all processes, times `m`, is at most
`n · ℓ · |W|`, where `|W|` is the number of `WriteMax` steps of line 4 (one per started
`MaxUpdate`). -/
theorem lemma_3_6_unsuccessful {α : List (Lbl n)} {C : Cfg n} {ℓ : ℕ}
    (h : (alg1 n m X).run α = some C) (hBI : BIExec n m X ℓ α) :
    m * ∑ p, fails m X α p ≤ n * (ℓ * ((writesTo (alg1 n m X) wm1 α false).length +
      (writesTo (alg1 n m X) wm1 α true).length)) := by
  obtain ⟨e1, e2⟩ := mr_eq_lmax h
  have bL := lmax_le_of_stepBounded (boundedIncr_iff_stepBounded.1 (hBI false))
  have bR := lmax_le_of_stepBounded (boundedIncr_iff_stepBounded.1 (hBI true))
  have hs : ∑ p, fails m X α p ≤ n * (vL C / m + vR C / m) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin n)) (fails m X α)
      (vL C / m + vR C / m) (fun p _ => fails_le h p)
    simpa using this
  have hm1 := Nat.div_mul_le_self (vL C) m
  have hm2 := Nat.div_mul_le_self (vR C) m
  calc m * ∑ p, fails m X α p ≤ m * (n * (vL C / m + vR C / m)) := Nat.mul_le_mul_left _ hs
    _ = n * (vL C / m * m + vR C / m * m) := by
      rw [Nat.mul_left_comm, Nat.mul_add, Nat.mul_comm m (vL C / m), Nat.mul_comm m (vR C / m)]
    _ ≤ n * (ℓ * ((writesTo (alg1 n m X) wm1 α false).length +
          (writesTo (alg1 n m X) wm1 α true).length)) := by
      apply Nat.mul_le_mul_left
      rw [Nat.mul_add]
      rw [← e1] at bL; rw [← e2] at bR
      omega

/-- **Lemma 3.6, counting core** (with the paper's parameters `ℓ = n`, `m ≥ n²`, or more
generally `n · ℓ ≤ m`): there are at most `|W|` unsuccessful iterations in total, so at most
`|W| + (number of operations)` loop iterations (Observation 7). -/
theorem lemma_3_6_unsuccessful_of_le {α : List (Lbl n)} {C : Cfg n} {ℓ : ℕ}
    (h : (alg1 n m X).run α = some C) (hBI : BIExec n m X ℓ α) (hm : n * ℓ ≤ m) (hm0 : 0 < m) :
    ∑ p, fails m X α p ≤ (writesTo (alg1 n m X) wm1 α false).length +
      (writesTo (alg1 n m X) wm1 α true).length := by
  have h1 := lemma_3_6_unsuccessful h hBI
  have h2 : n * (ℓ * ((writesTo (alg1 n m X) wm1 α false).length +
      (writesTo (alg1 n m X) wm1 α true).length)) ≤ m * ((writesTo (alg1 n m X) wm1 α false).length +
      (writesTo (alg1 n m X) wm1 α true).length) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hm
  exact Nat.le_of_mul_le_mul_left (h1.trans h2) hm0

end Podc.LongLivedSnapshotsPolylog.Amortized
