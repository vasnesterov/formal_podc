import Papers.PODC2020.LongLivedSnapshotsPolylog.WaitFreeBasic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Wait-freedom of Algorithm 1: execution segments

Two facts about an execution segment from `C₀` to `C`:

* `V_le_of_seg` (the bounded-increment half of Lemma 3.4): in an `ℓ`-bounded-increment execution,
  `MR_left + MR_right` grows by at most `ℓ` per `WriteMax`;
* `good_of_three_writes` (Observation 5, used twice in Lemma 3.5): if some process performs three
  `WriteMax` steps (i.e. starts three `MaxUpdate`s, each `MaxUpdate` performs exactly one
  `WriteMax`) in the segment, then some entry `H[k].ts` grows by at least `2` in the segment.
-/

namespace Podc.LongLivedSnapshotsPolylog.WaitFree

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

variable {n m X : ℕ}

/-- `MR_left + MR_right`. -/
def V (C : Cfg n) : ℕ := mrL C + mrR C

/-- The `WriteMax` of process `p` in local state `l`, tagged with the process. -/
def wP (p : Fin n) (l : Loc n) : Option (Fin n × ℕ) :=
  match l.pc with
  | .wm _ v => some (p, v)
  | _ => none

/-- The processes performing the `WriteMax` steps along `γ` from `C`, in order. -/
noncomputable def wr (m X : ℕ) (C : Cfg n) (γ : List (Lbl n)) : List (Fin n) :=
  (wlogFrom (alg1 n m X) wP C γ).map Prod.fst

lemma wr_cons {C C₁ : Cfg n} {x : Lbl n} (γ : List (Lbl n))
    (hs : (alg1 n m X).step C x = some C₁) :
    wr m X C (x :: γ) = (wstep wP C x).map Prod.fst ++ wr m X C₁ γ := by
  simp [wr, wlogFrom, hs]
  cases x <;> rfl

/-- The writers of one step: only the process taking the step. -/
lemma mem_wstep {C : Cfg n} {x : Lbl n} {q : Fin n} (h : q ∈ (wstep wP C x).map Prod.fst) :
    x.proc = q ∧ ∃ s v, x = .tau q ∧ (C.loc q).pc = .wm s v := by
  cases x with
  | tau p =>
    simp only [wstep, wP, List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    split at he
    · rename_i s v hpc
      simp only [Option.toList_some, List.mem_singleton] at he
      subst he
      exact ⟨rfl, s, v, rfl, hpc⟩
    · simp at he
  | inv p o => simp [wstep] at h
  | ret p r => simp [wstep] at h

/-! ### The bounded-increment bound -/

lemma V_step {ℓ : ℕ} {C C' : Cfg n} {x : Lbl n} (hs : (alg1 n m X).step C x = some C')
    (hbi : ∀ p s v, x = .tau p → (C.loc p).pc = .wm s v → v ≤ mrS s C + ℓ) :
    V C' ≤ V C + ℓ * ((wstep wP C x).map Prod.fst).length := by
  cases x with
  | inv p o =>
    obtain ⟨-, -, -, -, hm⟩ := Impl.step_inv hs
    simp [V, mrL, mrR, hm]
  | ret p r =>
    obtain ⟨-, -, hm, -⟩ := Impl.step_ret hs
    simp [V, mrL, mrR, hm]
  | tau p =>
    have hb := hbi p
    rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, first, j, acc⟩ | r
    all_goals simp [Impl.step, act, hpc] at hs
    all_goals obtain ⟨-, rfl⟩ := hs
    all_goals simp [V, mrL, mrR, wstep, wP, hpc]
    · have := hb false v rfl hpc; simp [mrS, mrL] at this; omega
    · have := hb true v rfl hpc; simp [mrS, mrR] at this; omega

/-- **Lemma 3.4, bounded-increment part**: along a segment `γ` (from the end of `β₀`) of an
`ℓ`-bounded-increment execution `α`, `MR_left + MR_right` grows by at most `ℓ` times the number
of `WriteMax` steps of the segment. -/
lemma V_le_of_seg {ℓ : ℕ} {α : List (Lbl n)} {Cα : Cfg n} (hα : (alg1 n m X).run α = some Cα)
    (hBI : BIExec n m X ℓ α) :
    ∀ (γ β₀ : List (Lbl n)) (C₀ C : Cfg n), β₀ ++ γ <+: α → (alg1 n m X).run β₀ = some C₀ →
      (alg1 n m X).runFrom C₀ γ = some C → V C ≤ V C₀ + ℓ * (wr m X C₀ γ).length
  | [], β₀, C₀, C, _, _, h => by
    simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; simp [wr, wlogFrom]
  | x :: γ, β₀, C₀, C, hp, h₀, h => by
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg1 n m X).step C₀ x with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have h₁ : (alg1 n m X).run (β₀ ++ [x]) = some C₁ := by
        rw [Impl.run_concat, h₀, Option.bind_some, hs]
      have ih := V_le_of_seg hα hBI γ (β₀ ++ [x]) C₁ C (by simpa using hp) h₁ h
      have hstep := V_step (ℓ := ℓ) hs (fun p s v hx hpc => by
        subst hx
        exact bi_step hα hBI (List.IsPrefix.trans (by simp) hp) h₀ hpc)
      rw [wr_cons γ hs, List.length_append]
      rw [Nat.mul_add]; omega

/-! ### Observation 5 -/

/-- Some entry `H[k].ts` grew by at least `2` from `C₀` to `C`. -/
def Good (C₀ C : Cfg n) : Prop := ∃ k, tsOf C₀ k + 2 ≤ tsOf C k

/-- The first collect `h₀` of `cs` (if any) was read after `C₀`. -/
def H0ok (C₀ : Cfg n) (cs : CS n) : Prop := ∀ h0, cs.h0 = some h0 → ∀ k, tsOf C₀ k ≤ (h0 k).1

/-- The invariant of process `j` after its `w`-th `WriteMax` since `C₀` (`w ≥ 1`): all but
possibly the last `CompScan` started after `C₀` completed and incremented `ts_j` (otherwise `Good`
holds), and the current `CompScan` started after `C₀`. -/
def BodyPc (C₀ C : Cfg n) (j : Fin n) (w : ℕ) : PC n → Prop
  | .idle => tsOf C₀ j + w ≤ tsOf C j
  | .wm _ _ => tsOf C₀ j + w ≤ tsOf C j
  | .retV _ => tsOf C₀ j + w ≤ tsOf C j
  | .rdR1 cs => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .rdL cs _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .rdR2 cs _ _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .upL cs _ _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .upR cs _ _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .scanMA cs _ _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .chkL cs _ _ _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .chkR cs _ _ _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .wH cs _ => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs
  | .col cs true k acc => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs ∧
      ∀ k' : Fin n, k' < k → tsOf C₀ k' ≤ (acc k').1
  | .col cs false k acc => tsOf C₀ j + w ≤ tsOf C j + 1 ∧ H0ok C₀ cs ∧
      ∀ k' : Fin n, k' < k → (acc k').1 ≤ tsOf C k'

/-- The segment invariant of process `j`. -/
def Seg (C₀ C : Cfg n) (j : Fin n) (w : ℕ) : Prop :=
  Good C₀ C ∨ w = 0 ∨ BodyPc C₀ C j w (C.loc j).pc

lemma good_mono {C₀ C C' : Cfg n} (h : Good C₀ C) (hm : ∀ k, tsOf C k ≤ tsOf C' k) :
    Good C₀ C' := by
  obtain ⟨k, hk⟩ := h; exact ⟨k, hk.trans (hm k)⟩

/-- `BodyPc` is preserved when `ts_j` is unchanged and the others do not decrease. -/
lemma bodyPc_mono {C₀ C C' : Cfg n} {j : Fin n} {w : ℕ} {pc : PC n}
    (hj : tsOf C' j = tsOf C j) (hm : ∀ k, tsOf C k ≤ tsOf C' k) (h : BodyPc C₀ C j w pc) :
    BodyPc C₀ C' j w pc := by
  cases pc with
  | col cs first k acc =>
    cases first with
    | true => simpa [BodyPc, hj] using h
    | false =>
      simp only [BodyPc, hj] at h ⊢
      exact ⟨h.1, h.2.1, fun k' hk' => (h.2.2 k' hk').trans (hm k')⟩
  | _ => simpa [BodyPc, hj] using h

/-- `BodyPc` at the state after an unsuccessful iteration. -/
lemma bodyPc_afterFail {C₀ C : Cfg n} {j : Fin n} {w : ℕ} {cs : CS n}
    (h1 : tsOf C₀ j + w ≤ tsOf C j + 1) (h2 : H0ok C₀ cs) :
    BodyPc C₀ C j w (afterFail X j cs) := by
  unfold afterFail
  split_ifs
  · exact ⟨h1, h2, fun k' hk' => absurd (Fin.lt_def.1 hk') (Nat.not_lt_zero _)⟩
  · exact ⟨h1, h2, fun k' hk' => absurd (Fin.lt_def.1 hk') (Nat.not_lt_zero _)⟩
  · exact ⟨h1, h2⟩

@[simp] lemma tsOf_upd_self (L : Fin n → Loc n) (pe : Fin n → Option MAOp)
    (me : (o : Obj n) → (objSpec n o).State) (j : Fin n) (l : Loc n) :
    tsOf (⟨Function.update L j l, pe, me⟩ : Cfg n) j = l.ts := by
  simp [tsOf]

lemma tsOf_le_upd (C : Cfg n) (pe : Fin n → Option MAOp)
    (me : (o : Obj n) → (objSpec n o).State) (j k : Fin n) (pc : PC n) :
    tsOf C k ≤ tsOf (⟨Function.update C.loc j ⟨(C.loc j).ts, pc⟩, pe, me⟩ : Cfg n) k := by
  by_cases hk : k = j
  · subst hk; simp [tsOf]
  · simp [tsOf, Function.update_of_ne hk]

lemma fin_lt_succ {k k' : Fin n} {h : k.1 + 1 < n} (hk' : k' < ⟨k.1 + 1, h⟩) :
    k' < k ∨ k' = k := by
  rcases Nat.lt_or_ge k'.1 k.1 with h1 | h1
  · exact Or.inl h1
  · right; ext; simp only [Fin.lt_def] at hk'; omega

lemma seg_tau {C₀ C C' : Cfg n} {j : Fin n} {w : ℕ} (hB : Basic C)
    (hm0 : ∀ k, tsOf C₀ k ≤ tsOf C k) (hs : (alg1 n m X).step C (.tau j) = some C')
    (h : w = 0 ∨ BodyPc C₀ C j w (C.loc j).pc) :
    Seg C₀ C' j (w + ((wstep wP C (.tau j)).map Prod.fst).count j) := by
  have hm := (step_mono hs).2.2
  have hj0 : tsOf C₀ j + w ≤ tsOf C j + 1 ∨ w = 0 := by
    rcases h with h | h
    · exact Or.inr h
    · left
      rcases hpc : (C.loc j).pc <;> rw [hpc] at h <;> simp only [BodyPc] at h <;>
        first | omega | (cases ‹Bool› <;> simp only at h <;> omega)
  rcases hpc : (C.loc j).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
    ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
    ⟨cs, first, k, acc⟩ | r
  all_goals rw [hpc] at h
  all_goals simp [Impl.step, act, hpc] at hs
  all_goals obtain ⟨-, rfl⟩ := hs
  all_goals simp only [Seg, wstep, wP, hpc, Option.toList_some, Option.toList_none, List.map_nil,
    List.map_cons, List.count_nil, List.count_singleton_self, add_zero, Function.update_self]
  -- `wm`
  · right; right
    simp only [BodyPc, tsOf, Function.update_self, H0ok, csInit, reduceCtorEq, false_imp_iff,
      implies_true, and_true]
    rcases h with rfl | h
    · have := hm0 j; simp only [tsOf] at this; omega
    · simp only [BodyPc, tsOf] at h; omega
  · right; right
    simp only [BodyPc, tsOf, Function.update_self, H0ok, csInit, reduceCtorEq, false_imp_iff,
      implies_true, and_true]
    rcases h with rfl | h
    · have := hm0 j; simp only [tsOf] at this; omega
    · simp only [BodyPc, tsOf] at h; omega
  all_goals rcases h with rfl | h
  all_goals first | exact Or.inr (Or.inl rfl) | skip
  all_goals first | (right; right; simpa [BodyPc, tsOf] using h) | skip
  -- the tests of lines 13 and 18
  · split_ifs
    · right; right; simpa [BodyPc, tsOf] using h
    · right; right; simp only [BodyPc] at h
      exact bodyPc_afterFail (by simpa [tsOf] using h.1) h.2
  · split_ifs
    · right; right; simpa [BodyPc, tsOf] using h
    · right; right; simp only [BodyPc] at h
      exact bodyPc_afterFail (by simpa [tsOf] using h.1) h.2
  · split_ifs
    · right; right; simpa [BodyPc, tsOf] using h
    · right; right; simp only [BodyPc] at h
      exact bodyPc_afterFail (by simpa [tsOf] using h.1) h.2
  -- line 21
  · right; right; unfold retOf
    split_ifs <;> simp only [BodyPc, tsOf_upd_self] at h ⊢ <;> simp only [tsOf] at h ⊢ <;> omega
  -- the collects
  · have hread : (C.mem (.help k)).1 = tsOf C k := hB.1 k
    by_cases hk : k.1 + 1 < n
    · simp only [hk, ↓reduceDIte]
      right; right
      cases first
      · simp only [BodyPc, tsOf_upd_self] at h ⊢
        refine ⟨h.1, h.2.1, fun k' hk' => ?_⟩
        rcases fin_lt_succ hk' with hk' | rfl
        · rw [Function.update_of_ne (ne_of_lt hk')]; exact (h.2.2 k' hk').trans (tsOf_le_upd _ _ _ _ _ _)
        · rw [Function.update_self, hread]; exact tsOf_le_upd _ _ _ _ _ _
      · simp only [BodyPc, tsOf_upd_self] at h ⊢
        refine ⟨h.1, h.2.1, fun k' hk' => ?_⟩
        rcases fin_lt_succ hk' with hk' | rfl
        · rw [Function.update_of_ne (ne_of_lt hk')]; exact h.2.2 k' hk'
        · rw [Function.update_self, hread]; exact hm0 k'
    · simp only [hk, ↓reduceDIte]
      have hle : ∀ k' : Fin n, k' ≠ k → k' < k := fun k' hne => by
        rcases lt_or_gt_of_ne hne with h' | h'
        · exact h'
        · exfalso; simp only [Fin.lt_def] at h'; omega
      cases first
      · simp only [afterCollect, Bool.false_eq_true, ↓reduceIte]
        simp only [BodyPc] at h
        split
        · rename_i v hv
          left
          obtain ⟨h0, hh0, hf⟩ := Option.bind_eq_some_iff.1 hv
          simp only [findHelp, Option.map_eq_some_iff] at hf
          obtain ⟨k0, hk0, -⟩ := hf
          have hp := List.find?_some hk0
          simp only [decide_eq_true_eq] at hp
          refine ⟨k0, ?_⟩
          have e1 := h.2.1 h0 hh0 k0
          have e2 : (Function.update acc k (C.mem (Obj.help k)) k0).1 ≤ tsOf C k0 := by
            by_cases hk0' : k0 = k
            · subst hk0'; rw [Function.update_self, hread]
            · rw [Function.update_of_ne hk0']; exact h.2.2 k0 (hle k0 hk0')
          have e3 := tsOf_le_upd C C.pend C.mem j k0 (retOf cs v)
          omega
        · right; right
          simp only [BodyPc, tsOf_upd_self]
          exact ⟨by simpa [tsOf] using h.1, h.2.1⟩
      · simp only [afterCollect, ↓reduceIte]
        simp only [BodyPc] at h
        right; right
        simp only [BodyPc, tsOf_upd_self]
        refine ⟨by simpa [tsOf] using h.1, fun h0 hh0 k' => ?_⟩
        simp only [Option.some.injEq] at hh0
        subst hh0
        by_cases hk' : k' = k
        · subst hk'; rw [Function.update_self, hread]; exact hm0 k'
        · rw [Function.update_of_ne hk']; exact h.2.2 k' (hle k' hk')

lemma seg_step {C₀ C C' : Cfg n} {x : Lbl n} {j : Fin n} {w : ℕ} (hB : Basic C)
    (hm0 : ∀ k, tsOf C₀ k ≤ tsOf C k) (hs : (alg1 n m X).step C x = some C')
    (h : Seg C₀ C j w) : Seg C₀ C' j (w + ((wstep wP C x).map Prod.fst).count j) := by
  have hm := (step_mono hs).2.2
  rcases h with hg | h
  · exact Or.inl (good_mono hg hm)
  by_cases hx : x.proc = j
  · cases x with
    | tau p =>
      simp only [Label.proc] at hx; subst hx
      exact seg_tau hB hm0 hs h
    | inv p o =>
      simp only [Label.proc] at hx; subst hx
      simp only [wstep, List.map_nil, List.count_nil, add_zero]
      obtain ⟨hpe, -, -, hl, -⟩ := Impl.step_inv hs
      have hidle := hB.2 _ hpe
      have hts : tsOf C' p = tsOf C p := by
        simp only [tsOf, hl, Function.update_self]; cases o <;> rfl
      rcases h with rfl | h
      · exact Or.inr (Or.inl rfl)
      right; right
      rw [hidle] at h
      simp only [BodyPc] at h
      have hl' : C'.loc p = (alg1 n m X).invoke p (C.loc p) o := by simp [hl]
      rw [hl']
      cases o <;> simp [BodyPc, H0ok, csInit] <;> rw [← hts] at h <;>
        first | exact h | (simp only [tsOf, hl, Function.update_self] at h ⊢; omega)
    | ret p r =>
      simp only [Label.proc] at hx; subst hx
      simp only [wstep, List.map_nil, List.count_nil, add_zero]
      obtain ⟨-, -, -, l, hact, hl⟩ := Impl.step_ret hs
      rcases h with rfl | h
      · exact Or.inr (Or.inl rfl)
      right; right
      have hts : tsOf C' p = tsOf C p := by
        simp only [tsOf, hl, Function.update_self]; exact act_ret_ts hact
      simp only [hl, Function.update_self]
      simp only [act] at hact
      split at hact <;> first | (split at hact <;> cases hact) | skip
      all_goals cases hact
      all_goals rename_i hpc
      all_goals rw [hpc] at h
      all_goals simp only [hpc, BodyPc] at h ⊢
      all_goals simp only [tsOf, hl, Function.update_self] at h ⊢
      all_goals omega
  · have hcnt : ((wstep wP C x).map Prod.fst).count j = 0 :=
      List.count_eq_zero.2 fun hj => hx (mem_wstep hj).1
    rw [hcnt, add_zero]
    have hloc := (Impl.step_other hs hx).1
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · right; right
      rw [hloc]
      exact bodyPc_mono (by simp [tsOf, hloc]) hm h

lemma seg_run {C₀ : Cfg n} {j : Fin n} :
    ∀ (γ : List (Lbl n)) (C C' : Cfg n) (w : ℕ), Basic C → (∀ k, tsOf C₀ k ≤ tsOf C k) →
      (alg1 n m X).runFrom C γ = some C' → Seg C₀ C j w →
      Seg C₀ C' j (w + (wr m X C γ).count j)
  | [], C, C', w, _, _, h, hS => by
    simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; simpa [wr, wlogFrom] using hS
  | x :: γ, C, C', w, hB, hm0, h, hS => by
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg1 n m X).step C x with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have := seg_run γ C₁ C' _ (basic_step hB hs)
        (fun k => (hm0 k).trans ((step_mono hs).2.2 k)) h (seg_step hB hm0 hs hS)
      rw [wr_cons γ hs, List.count_append, ← add_assoc]
      exact this

/-- **Observation 5, applied twice** (proof of Lemma 3.5): if a process performs three `WriteMax`
steps along a segment from a reachable configuration `C₀` to `C`, then some `H[k].ts` grows by at
least `2` from `C₀` to `C`. -/
lemma good_of_three_writes {α : List (Lbl n)} {C₀ C : Cfg n} {γ : List (Lbl n)} {j : Fin n}
    (h₀ : (alg1 n m X).run α = some C₀) (h : (alg1 n m X).runFrom C₀ γ = some C)
    (hj : 3 ≤ (wr m X C₀ γ).count j) : Good C₀ C := by
  have hS := seg_run (j := j) γ C₀ C 0 (basic_run h₀) (fun _ => le_rfl) h (Or.inr (Or.inl rfl))
  rw [zero_add] at hS
  rcases hS with hS | hS | hS
  · exact hS
  · omega
  · refine ⟨j, ?_⟩
    rcases hpc : (C.loc j).pc with _ | ⟨_, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, first, k, acc⟩ | r
    all_goals rw [hpc] at hS
    all_goals try cases first
    all_goals simp only [BodyPc] at hS
    all_goals omega

/-- Pigeonhole: `2n + 1` writes by `n` processes contain three by the same process. -/
lemma exists_three {l : List (Fin n)} (hl : 2 * n + 1 ≤ l.length) : ∃ j, 3 ≤ l.count j := by
  by_contra hc
  push Not at hc
  have : l.length = ∑ j : Fin n, l.count j := by
    have := Multiset.sum_count_eq_card (s := Finset.univ) (m := (l : Multiset (Fin n)))
      (by simp)
    simpa using this.symm
  have h2 : ∑ j : Fin n, l.count j ≤ ∑ _j : Fin n, 2 :=
    Finset.sum_le_sum fun j _ => by have := hc j; omega
  simp at h2
  omega

end Podc.LongLivedSnapshotsPolylog.WaitFree
