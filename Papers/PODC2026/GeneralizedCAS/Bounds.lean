import Papers.PODC2026.GeneralizedCAS.Invariant

/-!
# Algorithm 1: monotonicity of "done", and two counting invariants

* `done_step`: **Observation B.1.8** — once an operation is done, it stays done.
* `Inv2.wd_le`: the owner of `τ` writes `τ` into `A` (lines 8, 15) at most twice while `τ` is done
  (after `τ` is done, its owner finds this out on its next execution of line 5 and stops). This is
  the fact behind Proposition B.2.13.
* `Inv2.ns`: the number of steps of a process in its current operation is at most
  `3 + 7 · it` where `it` is the number of executions of line 5 (the loop body has 7 steps).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]
variable (cellInit : ℕ → CellVal T.Resp)

/-- `ts` entries are never changed (only new timestamps are added). -/
lemma ts_step {C C' : Cfg T P} {G : Ghost T P} (hI : CInv C G) {ℓ : Label P T}
    (h : (alg T P cellInit).step C ℓ = some C') {τ : ℕ} {x : P × ℕ × T.Op}
    (hx : G.ts τ = some x) : (augStep C ℓ G).ts τ = some x := by
  cases ℓ with
  | inv p o => exact hx
  | ret p r => exact hx
  | tau p =>
    have hτ : τ ≠ C.M.cnt := by
      rintro rfl; have := (hI.ts_range C.M.cnt).1 (by simp [hx]); omega
    simp only [augStep]
    split <;> (try split_ifs) <;> (try split) <;> (try split) <;>
      simp [Function.update_of_ne hτ, hx]

/-- `G.k` only grows. -/
lemma k_step {C : Cfg T P} {G : Ghost T P} {ℓ : Label P T}
    (q : P) : G.k q ≤ (augStep C ℓ G).k q := by
  cases ℓ with
  | inv p o => exact le_rfl
  | ret p r =>
    simp only [augStep, Function.update_apply]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  | tau p =>
    simp only [augStep]
    split <;> (try split_ifs) <;> (try split) <;> (try split) <;> exact le_rfl

/-- **Observation B.1.8**: a done operation stays done. -/
theorem done_step {C C' : Cfg T P} {G : Ghost T P} (hI : CInv C G) {ℓ : Label P T}
    (h : (alg T P cellInit).step C ℓ = some C') {τ : ℕ} (hd : Done C G τ) :
    Done C' (augStep C ℓ G) τ := by
  rcases hd with h0 | ⟨q, k, o, h1, h2, h3⟩
  · exact Or.inl h0
  refine Or.inr ⟨q, k, o, ts_step cellInit hI h h1, ?_, ?_⟩
  · -- `WrittenAt` is monotone
    have hptr := hI.ts_ptr τ q k o h1
    cases ℓ with
    | inv p o' =>
      obtain ⟨hp, -, -, hloc⟩ := step_inv_eff cellInit h
      unfold WrittenAt at h2 ⊢; rw [hloc]
      rcases eq_or_ne q p with rfl | hq
      · left
        rcases h2 with h2 | h2
        · exact h2
        · rcases lt_or_eq_of_le (hI.ts_k τ q k o h1) with hk | hk
          · exact hk
          · subst hk; have := (hI.ts_cur τ q o h1).1; rw [hp] at this; cases this
      · simp only [Function.update_of_ne hq]; exact h2
    | ret p r =>
      obtain ⟨hp, hpc, -, -, hloc⟩ := step_ret_eff cellInit h
      unfold WrittenAt at h2 ⊢; rw [hloc]
      rcases eq_or_ne q p with rfl | hq
      · right; simp
      · simp only [augStep, Function.update_of_ne hq]; exact h2
    | tau p =>
      obtain ⟨hp, -, -, -, hloc⟩ := step_tau_eff cellInit h
      unfold WrittenAt at h2 ⊢; rw [hloc]
      have hk : (augStep C (.tau p) G).k = G.k := by
        simp only [augStep]; split <;> (try split_ifs) <;> (try split) <;> (try split) <;> rfl
      rw [hk]
      rcases eq_or_ne q p with rfl | hq
      · simp only [Function.update_self]
        rcases lt_or_eq_of_le (hI.ts_k τ q k o h1) with hk | hk
        · exact Or.inl hk
        · subst hk
          have h3' := (hI.ts_cur τ q o h1).2.1
          right
          cases hpc : (C.loc q).pc <;> simp [hpc, PC.Past3] at h3' <;> simp [effect, hpc] <;>
            (try (unfold pc5; split_ifs <;> (try split) <;> simp))
          split_ifs <;> simp
      · simp only [Function.update_of_ne hq]; exact h2
  · -- the cell no longer contains `(τ, Null)`
    have hptr := hI.ts_ptr τ q k o h1
    cases ℓ with
    | inv p o' =>
      obtain ⟨-, -, hmem, hloc⟩ := step_inv_eff cellInit h
      have hme : (C'.loc q).me = (C.loc q).me := by
        rw [hloc]; by_cases hq : q = p
        · subst hq; simp [Loc.me, Loc.invoke]
        · simp [Function.update_of_ne hq]
      rw [hme]; simpa [Cfg.M, hmem] using h3
    | ret p r =>
      obtain ⟨-, -, -, hmem, hloc⟩ := step_ret_eff cellInit h
      have hme : (C'.loc q).me = (C.loc q).me := by
        rw [hloc]; by_cases hq : q = p
        · subst hq; simp [Loc.me]
        · simp [Function.update_of_ne hq]
      rw [hme]; simpa [Cfg.M, hmem] using h3
    | tau p =>
      obtain ⟨hp, -, -, hM, hloc⟩ := step_tau_eff cellInit h
      rw [hM, hloc]
      by_cases hpc2 : (C.loc p).pc = .l2
      · have hqp : q ≠ p := by
          rintro rfl; exact hptr ((hI.pc_ptr q hp).1 hpc2)
        simp only [effect, hpc2, Function.update_of_ne hqp]; exact h3
      have hme : (Function.update C.loc p (effect (C.loc p) C.M).2 q).me = (C.loc q).me := by
        apply me_upd
        cases hpc : (C.loc p).pc <;> simp [effect, hpc] at hpc2 ⊢ <;>
          (try (unfold pc5; split_ifs <;> (try split) <;> rfl)) <;> split_ifs <;> rfl
      rw [hme]
      cases hpc : (C.loc p).pc
      case l2 => exact absurd hpc hpc2
      case l4 =>
        simp only [effect, hpc]
        have hpp : (C.loc p).ptr ≠ none := (hI.pc_ptr p hp).not.1 (by simp [hpc])
        rcases eq_or_ne q p with rfl | hq
        · simp only [Function.update_self, ne_eq, CellVal.mk.injEq, and_true]
          rintro rfl
          obtain ⟨o', ho⟩ := Option.ne_none_iff_exists'.mp hp
          have hcur := hI.cur q o' ho (by simp [hpc, PC.Past3])
          rw [hcur] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨-, rfl, -⟩ := h1
          rcases h2 with h2 | h2
          · exact lt_irrefl _ h2
          · exact h2 hpc
        · rw [Function.update_of_ne (hI.me_ne hq hpp)]; exact h3
      case l7 =>
        simp only [effect, hpc]
        by_cases hx : (C.loc q).me = (C.loc p).snap.ptr
        · rw [hx, Function.update_self]
          unfold cellCAS; split_ifs with hc
          · simp only [ne_eq, CellVal.mk.injEq, not_and]
            intro _ hr
            by_cases h0 : (C.loc p).snap.time = 0
            · have := (hI.snap_zero p hp (by simp [hpc, PC.HasSnap]) h0).2; rw [hr] at this; cases this
            · obtain ⟨-, -, -, -, -, -, r, hr', -⟩ := hI.snap_pos p hp (by simp [hpc, PC.HasSnap]) h0
              rw [hr] at hr'; cases hr'
          · rw [← hx]; exact h3
        · rw [Function.update_of_ne hx]; exact h3
      all_goals (simp only [effect, hpc]; exact h3)

/-! ## The counting invariants -/

/-- How many more times line 8 or 15 can be executed in the current iteration. -/
def PC.rem {R : Type} : PC R → ℕ
  | .l6 | .l7 | .l8 => 2
  | .l9 | .l10 | .l15 => 1
  | _ => 0

lemma PC.rem_le {R : Type} (c : PC R) : c.rem ≤ 2 := by cases c <;> simp [PC.rem]

/-- The step counter of the current operation, relative to the number `it` of complete
iterations of the loop (the loop body has 7 steps). -/
def PC.NsOK {R : Type} : PC R → ℕ → ℕ → Prop
  | .l2, ns, it => ns = 0 ∧ it = 0
  | .l3, ns, it => ns ≤ 1 ∧ it = 0
  | .l4, ns, it => ns ≤ 2 ∧ it = 0
  | .l5, ns, it => ns ≤ 3 + 7 * it
  | .l6, ns, it => ns ≤ 4 + 7 * it
  | .l7, ns, it => ns ≤ 5 + 7 * it
  | .l8, ns, it => ns ≤ 6 + 7 * it
  | .l9, ns, it => ns ≤ 7 + 7 * it
  | .l10, ns, it => ns ≤ 8 + 7 * it
  | .l13, ns, it => ns ≤ 9 + 7 * it
  | .l15, ns, it => ns ≤ 9 + 7 * it
  | .l16 _, ns, it => ns ≤ 4 + 7 * it

lemma PC.NsOK.le {R : Type} {c : PC R} {ns it : ℕ} (h : c.NsOK ns it) : ns ≤ 9 + 7 * it := by
  cases c <;> simp only [PC.NsOK] at h <;> omega

lemma pc5_rem {l : Loc T} {M : Mem T} (h : M.cell l.me ≠ ⟨l.t, .null⟩) : (pc5 l M).rem = 0 := by
  unfold pc5; rw [if_neg h]; split <;> rfl

lemma pc5_cases (l : Loc T) (M : Mem T) :
    pc5 l M = .l6 ∨ pc5 l M = .l5 ∨ ∃ r, pc5 l M = .l16 r := by
  unfold pc5; split_ifs
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
    · exact Or.inr (Or.inl rfl)

/-- Two counting invariants. -/
structure Inv2 (C : Cfg T P) (G : Ghost T P) : Prop where
  wd_le : ∀ τ, G.wd τ ≤ 2
  wd_zero : ∀ τ, ¬ Done C G τ → G.wd τ = 0
  wd_cur : ∀ τ q o, G.ts τ = some (q, G.k q, o) → Done C G τ → G.wd τ + (C.loc q).pc.rem ≤ 2
  ns : ∀ q, C.pend q ≠ none → (C.loc q).pc.NsOK (G.ns q) (G.it q)

lemma inv2_init : Inv2 (alg T P cellInit).initCfg (ginit T P) where
  wd_le _ := by simp [ginit]
  wd_zero _ _ := rfl
  wd_cur _ _ _ h := by simp [ginit] at h
  ns _ h := by simp [Impl.initCfg] at h

/-- `wd` changes only at line 8 or 15 of the owner of a done current operation. -/
lemma wd_step {C : Cfg T P} {G : Ghost T P} {ℓ : Label P T} (τ : ℕ) :
    (augStep C ℓ G).wd τ = G.wd τ ∨ ∃ p, ℓ = .tau p ∧ ((C.loc p).pc = .l8 ∨ (C.loc p).pc = .l15) ∧
      (C.loc p).t = τ ∧ Done C G τ ∧ (augStep C ℓ G).wd τ = G.wd τ + 1 := by
  cases ℓ with
  | inv p o => exact Or.inl rfl
  | ret p r => exact Or.inl rfl
  | tau p =>
    simp only [augStep]
    split
    case h_2 hpc | h_3 hpc =>
      split_ifs with hd
      · by_cases hτ : τ = (C.loc p).t
        · subst hτ; exact Or.inr ⟨p, rfl, by simp [hpc], rfl, hd, by simp⟩
        · exact Or.inl (by simp [Function.update_of_ne hτ])
      · exact Or.inl rfl
    case h_4 =>
      split_ifs
      · cases G.ts (C.loc p).ann.time <;> exact Or.inl rfl
      · exact Or.inl rfl
    all_goals exact Or.inl rfl

theorem Inv2.step {C C' : Cfg T P} {G : Ghost T P} (hI : CInv C G) (hJ : Inv2 C G)
    {ℓ : Label P T} (h : (alg T P cellInit).step C ℓ = some C') :
    Inv2 C' (augStep C ℓ G) := by
  set G' := augStep C ℓ G with hG'
  have hdone : ∀ τ, Done C G τ → Done C' G' τ := fun τ => done_step cellInit hI h
  -- wd of a not-done operation stays 0
  have hwd0 : ∀ τ, ¬ Done C G τ → G'.wd τ = 0 := by
    intro τ hn
    rcases wd_step (C := C) (G := G) (ℓ := ℓ) τ with h' | ⟨p, -, -, -, hd, -⟩
    · rw [h']; exact hJ.wd_zero τ hn
    · exact absurd hd hn
  have hI' := hI.step cellInit h
  -- `ns`/`it` of other processes do not change; `k` changes only at responses
  have hns : ∀ q, (∀ r, ℓ ≠ .ret q r) → (∀ o, ℓ ≠ .inv q o) → (∀ q', ℓ = .tau q' → q' ≠ q) →
      G'.ns q = G.ns q ∧ G'.it q = G.it q := by
    intro q h1 h2 h3
    cases ℓ with
    | inv p o =>
      have hq : q ≠ p := fun e => h2 o (by rw [e])
      simp [G', augStep, Function.update_of_ne hq]
    | ret p r => exact ⟨rfl, rfl⟩
    | tau p =>
      have hq : q ≠ p := fun e => h3 p rfl e.symm
      simp only [G', augStep]
      split <;> (try split_ifs) <;> (try split) <;> simp [Function.update_of_ne hq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ
    rcases wd_step (C := C) (G := G) (ℓ := ℓ) τ with h' | ⟨p, rfl, hpc, rfl, hd, h'⟩
    · rw [h']; exact hJ.wd_le τ
    · obtain ⟨hp, -⟩ := step_tau_eff cellInit h
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hp
      have hcur := hI.cur p o ho (by rcases hpc with hpc | hpc <;> simp [hpc, PC.Past3])
      have := hJ.wd_cur _ p o hcur hd
      rw [h']; rcases hpc with hpc | hpc <;> simp [hpc, PC.rem] at this <;> omega
  · intro τ hn
    exact hwd0 τ (fun hd => hn (hdone τ hd))
  · intro τ q o hts' hd'
    by_cases hd : Done C G τ
    swap
    · rw [hwd0 τ hd]; simpa using PC.rem_le _
    have hτ0 : τ ≠ 0 := by
      intro h0
      have := (hI'.ts_range τ).1 (by intro hn; rw [← hG', hts'] at hn; cases hn); omega
    obtain ⟨q₀, k₀, o₀, h0, -, -⟩ := hd.resolve_left hτ0
    rw [ts_step cellInit hI h h0] at hts'
    simp only [Option.some.injEq, Prod.mk.injEq] at hts'
    obtain ⟨e1, hk, e2⟩ := hts'
    subst q₀ o₀
    cases ℓ with
    | inv p o' =>
      obtain ⟨hp, -, -, hloc⟩ := step_inv_eff cellInit h
      have hq : q ≠ p := by
        rintro rfl; have := (hI.ts_cur τ q o (hk ▸ h0)).1; rw [hp] at this; cases this
      rw [hloc, Function.update_of_ne hq]
      exact hJ.wd_cur τ q o (hk ▸ h0) hd
    | ret p r =>
      obtain ⟨-, -, -, -, hloc⟩ := step_ret_eff cellInit h
      have hq : q ≠ p := by
        rintro rfl; have := hI.ts_k τ q k₀ o h0
        simp only [G', augStep, Function.update_self] at hk; omega
      have hk' : G'.k q = G.k q := by simp [G', augStep, Function.update_of_ne hq]
      rw [hloc, Function.update_of_ne hq]
      exact hJ.wd_cur τ q o (by rw [hk'] at hk; exact hk ▸ h0) hd
    | tau p =>
      obtain ⟨hp, hmem, -, hM, hloc⟩ := step_tau_eff cellInit h
      have hkk : G'.k = G.k := by
        simp only [G', augStep]; split <;> (try split_ifs) <;> (try split) <;> rfl
      rw [hkk] at hk; subst hk
      have hpre := hJ.wd_cur τ q o h0 hd
      rcases eq_or_ne q p with rfl | hq
      · have htq : (C.loc q).t = τ := (hI.ts_cur τ q o h0).2.2
        rw [hloc, Function.update_self]
        rcases wd_step (C := C) (G := G) (ℓ := .tau q) τ with hw | ⟨p', hp', hpc, -, -, hw⟩
        · rw [hw]
          cases hpc : (C.loc q).pc <;> simp only [effect, hpc] at hpre ⊢
          case l5 =>
            -- the operation is done, so line 5 leaves the loop
            have hne : C.M.cell (C.loc q).me ≠ ⟨(C.loc q).t, .null⟩ := by
              obtain ⟨q₁, k₁, o₁, e1, -, e3⟩ := hd.resolve_left hτ0
              rw [h0] at e1; simp only [Option.some.injEq, Prod.mk.injEq] at e1
              obtain ⟨rfl, rfl, rfl⟩ := e1; rw [htq]; exact e3
            rw [pc5_rem hne]; simp only [PC.rem] at hpre; omega
          case l10 => split_ifs <;> simp only [PC.rem] at hpre ⊢ <;> omega
          case l16 r => exact absurd hpc (hmem r)
          all_goals (simp only [PC.rem] at hpre ⊢; omega)
        · cases hp'
          rw [hw]
          rcases hpc with hpc | hpc <;> simp only [effect, hpc, PC.rem] at hpre ⊢ <;> omega
      · rw [hloc, Function.update_of_ne hq]
        rcases wd_step (C := C) (G := G) (ℓ := .tau p) τ with hw | ⟨p', hp', hpc, ht, -, -⟩
        · rw [hw]; exact hpre
        · cases hp'
          obtain ⟨o', ho⟩ := Option.ne_none_iff_exists'.mp hp
          have hcur := hI.cur p o' ho (by rcases hpc with hpc | hpc <;> simp [hpc, PC.Past3])
          rw [ht, h0] at hcur; simp at hcur; exact absurd hcur.1 hq
  · intro q hq'
    cases ℓ with
    | inv p o =>
      obtain ⟨hp, hpend, -, hloc⟩ := step_inv_eff cellInit h
      rcases eq_or_ne q p with rfl | hq
      · rw [hloc, Function.update_self]
        simp only [G', augStep, Function.update_self, Loc.invoke]
        split_ifs <;> simp [PC.NsOK]
      · rw [hpend, Function.update_of_ne hq] at hq'
        rw [hloc, Function.update_of_ne hq]
        obtain ⟨e1, e2⟩ := hns q (by simp) (fun o' e => by cases e; exact hq rfl) (by simp)
        rw [e1, e2]; exact hJ.ns q hq'
    | ret p r =>
      obtain ⟨hp, -, hpend, -, hloc⟩ := step_ret_eff cellInit h
      rcases eq_or_ne q p with rfl | hq
      · simp [hpend] at hq'
      · rw [hpend, Function.update_of_ne hq] at hq'
        rw [hloc, Function.update_of_ne hq]
        obtain ⟨e1, e2⟩ := hns q (fun r' e => by cases e; exact hq rfl) (by simp) (by simp)
        rw [e1, e2]; exact hJ.ns q hq'
    | tau p =>
      obtain ⟨hp, hmem, hpend, -, hloc⟩ := step_tau_eff cellInit h
      rw [hpend] at hq'
      rcases eq_or_ne q p with rfl | hq
      · have hpre := hJ.ns q hq'
        rw [hloc, Function.update_self]
        cases hpc : (C.loc q).pc <;> simp only [effect, hpc] at hpre ⊢ <;>
          simp only [G', augStep, hpc, Function.update_self]
        case l5 =>
          rcases pc5_cases (C.loc q) C.M with h5 | h5 | ⟨r, h5⟩
          · rw [h5]; simp only [PC.NsOK] at hpre ⊢; omega
          · exfalso
            obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp hq'
            obtain ⟨ht, hr⟩ := hI.own_cell ho (by simp [hpc, PC.Past3]) (by simp [hpc])
            unfold pc5 at h5
            split_ifs at h5 with hc
            rcases hr with hr | ⟨r, hr, -⟩
            · exact hc (CellVal.ext ht hr)
            · rw [hr] at h5; cases h5
          · rw [h5]; simp only [PC.NsOK] at hpre ⊢; omega
        case l10 => split_ifs <;> simp only [PC.NsOK] at hpre ⊢ <;> omega
        case l8 => split_ifs <;> simp only [PC.NsOK, Function.update_self] at hpre ⊢ <;> omega
        case l15 => split_ifs <;> simp only [PC.NsOK, Function.update_self] at hpre ⊢ <;> omega
        case l13 =>
          split_ifs <;> (try (cases G.ts (C.loc q).ann.time)) <;>
            simp only [PC.NsOK, Function.update_self] at hpre ⊢ <;> omega
        all_goals (try (simp only [PC.NsOK] at hpre ⊢; omega))
        case l16 r => exact absurd hpc (hmem r)
      · rw [hloc, Function.update_of_ne hq]
        obtain ⟨e1, e2⟩ := hns q (by simp) (by simp) (fun q' e => by cases e; exact hq.symm)
        rw [e1, e2]; exact hJ.ns q hq'

/-- Both invariants hold in every state of an augmented run. -/
theorem arun_inv2 {α : List (Label P T)} {C : Cfg T P} {G : Ghost T P}
    (h : arun cellInit α = some (C, G)) : Inv2 C G :=
  (arun_induction cellInit (Q := fun _ C G => CInv C G ∧ Inv2 C G)
    ⟨cinv_init cellInit, inv2_init cellInit⟩
    (fun _ _ _ _ _ _ hI hs => ⟨hI.1.step cellInit hs, hI.2.step cellInit hI.1 hs⟩) h).2

end Podc.GeneralizedCAS
