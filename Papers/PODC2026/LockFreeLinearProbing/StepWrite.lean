import Papers.PODC2026.LockFreeLinearProbing.StepVal

/-!
# The invariant `Inv` is preserved: owners writing their own cell

Writing a tentative copy (lines 43, 58, 69, 78: a new round, with a fresh timestamp), finalizing
it (line 67) and withdrawing it (line 80).
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

@[simp] lemma ds48_pc (l : Loc K m) : (ds48 h l).pc = .dsLL := rfl
@[simp] lemma ds48_j (l : Loc K m) : (ds48 h l).j = l.j := rfl
@[simp] lemma ds48_i (l : Loc K m) : (ds48 h l).i = h l.op.key := rfl
@[simp] lemma ds48_op (l : Loc K m) : (ds48 h l).op = l.op := rfl

/-- The cell of an owner is not the cell of another owner, nor a free cell. -/
lemma ne_owner_cell (hI : Inv h N ts C) {q : P} (hq : (C.loc q).pc.isVal) {x : Fin m}
    (hx : C.val x = .empty ∨ C.val x = .tomb) : (C.loc q).j ≠ x := by
  rintro rfl
  rcases hI.own q hq with h1 | h1 | h1 | h1 <;> rcases hx with h2 | h2 <;> rw [h1] at h2 <;>
    cases h2

/-- Writing `⟨v, tentative⟩` into the own cell starts a new round of the duplicate scan with a
fresh timestamp: by a process that found a free cell (line 43), or by an owner (lines 58, 69,
78). -/
lemma inv_tentWrite (hI : Inv h N ts C) (hp : C.pend p ≠ none)
    (hpre : ((C.loc p).pc.isIns ∧ (C.val (C.loc p).j = .empty ∨ C.val (C.loc p).j = .tomb)) ∨
      (C.loc p).pc.isVal) :
    Inv h (N + 1) (update ts p N)
      (upd C p (ds48 h (C.loc p)) (C.loc p).j (.key (C.loc p).op.key .tent, [])) := by
  set l := C.loc p with hl
  set C' := upd C p (ds48 h l) l.j (.key l.op.key .tent, []) with hC'
  have hJ : ∀ J, J ≠ p → C'.loc J = C.loc J := fun J hJ => upd_loc_ne _ _ _ _ hJ
  have hmv : ∀ y, C'.val y = if y = l.j then .key l.op.key .tent else C.val y := fun y => by
    rw [hC', mem_val_upd]
  -- other owners have other cells
  have hoth : ∀ q, q ≠ p → (C.loc q).pc.isVal → (C.loc q).j ≠ l.j := by
    intro q hqp hq
    rcases hpre with ⟨-, hx⟩ | hv
    · exact ne_owner_cell hI hq hx
    · intro hj; exact hqp (hI.own_inj q p hq hv hj)
  have hpv : (C.loc p).pc.isVal = false → (C.loc p).pc.isIns := by
    intro h1; rcases hpre with ⟨h2, -⟩ | h2
    · exact h2
    · rw [h1] at h2; cases h2
  have hp3' : ∀ c, dist h l.op.key c < dist h l.op.key l.j → C.val c ≠ .empty := by
    intro c hc
    rcases hpre with ⟨h2, -⟩ | h2
    · exact hI.p3' p (Or.inl h2) c hc
    · exact hI.p3' p (Or.inr h2) c hc
  have hEold : ∀ y, C'.val y = .empty → C.val y = .empty := by
    intro y hy; rw [hmv] at hy; split_ifs at hy; exact hy
  have hts : ∀ q, q ≠ p → update ts p N q = ts q := fun q hq => update_of_ne hq _ _
  have hlt : ∀ q, ts q < N := hI.ts_lt
  refine ⟨idle_upd hI hp, loc_upd_inv hI (by simp [LocInv]), ?_, ?_, ?_, ?_, ?_, ?_,
    ts_lt_upd hI _ (fun q => by by_cases hq : q = p <;> simp [hq]), ?_, ?_, ?_, ?_, ?_⟩
  · apply link_upd hI (Or.inr (Or.inr rfl))
    intro y w hr; simp [recorded] at hr
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; simp [C', hmv]
    · rw [hJ q hqp] at hq ⊢; rw [hmv, if_neg (hoth q hqp hq)]; exact hI.own q hq
  · intro q r hq hr hqr
    by_cases hqp : q = p
    · subst hqp
      by_cases hrp : r = q
      · exact hrp.symm
      · rw [hJ r hrp] at hr hqr; simp only [C', upd_loc_self, ds48_j] at hqr
        exact absurd hqr.symm (hoth r hrp hr)
    · rw [hJ q hqp] at hq hqr
      by_cases hrp : r = p
      · subst hrp; simp only [C', upd_loc_self, ds48_j] at hqr
        exact absurd hqr (hoth q hqp hq)
      · rw [hJ r hrp] at hr hqr; exact hI.own_inj q r hq hr hqr
  · intro c v t hc ht
    rw [hmv] at hc; split_ifs at hc with hx
    · subst hx; simp only [Cell.key.injEq] at hc
      exact ⟨p, by simp [C', PC.isVal], by simp [C'], by simp [C', hc.1]⟩
    · obtain ⟨q, hq1, hq2, hq3⟩ := hI.own2 c v t hc ht
      have hqp : q ≠ p := by
        rintro rfl
        rcases hpre with ⟨h2, -⟩ | h2
        · revert hq1 h2; cases (C.loc q).pc <;> simp [PC.isVal, PC.isIns]
        · exact hx hq2.symm
      exact ⟨q, by rw [hJ q hqp]; exact ⟨hq1, hq2, hq3⟩⟩
  · intro c v t hc c'' hd hc''
    have hc''' := hEold c'' hc''
    rw [hmv] at hc; split_ifs at hc with hx
    · subst hx; simp only [Cell.key.injEq] at hc; obtain ⟨rfl, -⟩ := hc
      rcases Nat.lt_or_eq_of_le hd with hd | hd
      · exact hp3' c'' hd hc'''
      · rw [dist_inj h _ hd] at hc'''
        rw [dist_inj h _ hd, hmv, if_pos rfl] at hc''; cases hc''
    · exact hI.p3 c v t hc c'' hd hc'''
  · intro q hq c hd hc
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self, ds48_j, ds48_op] at hd
      exact hp3' c hd (hEold c hc)
    · rw [hJ q hqp] at hq hd; exact hI.p3' q hq c hd (hEold c hc)
  · -- a1
    intro I J hIJ hIv hJv hk ht hc
    by_cases hIp : I = p
    · subst hIp
      simp only [C', upd_loc_self, covers, ds48_pc, ds48_i, ds48_op, dist_self] at hc
      exact absurd hc (Nat.not_lt_zero _)
    · rw [hJ I hIp] at hIv hk ht hc
      rw [hts I hIp]
      by_cases hJp : J = p
      · subst hJp; simp [hlt I]
      · rw [hJ J hJp] at hJv hk ht hc; rw [hts J hJp]
        rw [hmv, if_neg (hoth J hJp hJv)] at ht
        exact hI.a1 I J hIJ hIv hJv hk ht hc
  · -- doc
    intro I J hd hJv hjj hk ht
    by_cases hIp : I = p
    · subst hIp; simp only [C', upd_loc_self, ds48_pc] at hd
      rcases hd with ⟨h1 | h1, -⟩ | h1 <;> cases h1
    · rw [hJ I hIp] at hd hjj hk ht; rw [hts I hIp]
      by_cases hJp : J = p
      · subst hJp; simp [hlt I]
      · rw [hJ J hJp] at hJv hjj hk; rw [hts J hJp]
        have hx : (C.loc I).i ≠ l.j := hjj ▸ hoth J hJp hJv
        rw [hmv, if_neg hx] at ht
        have hd' : ((((C.loc I).pc = .docRD ∨ (C.loc I).pc = .docSC) ∧ I ∉ C.lks (C.loc I).i) ∨
            (C.loc I).pc = .docRD2) := by
          rcases hd with ⟨h1, h2⟩ | h1
          · exact Or.inl ⟨h1, by rwa [hC', upd_lks_ne _ _ _ _ hx] at h2⟩
          · exact Or.inr h1
        exact hI.doc I J hd' hJv hjj hk ht
  · -- a4
    intro J c hJv ht hc
    by_cases hJp : J = p
    · subst hJp
      simp only [C', upd_loc_self, covers, ds48_pc, ds48_i, ds48_op, dist_self] at hc
      exact absurd hc (Nat.not_lt_zero _)
    · rw [hJ J hJp] at hJv ht hc ⊢
      rw [hmv, if_neg (hoth J hJp hJv)] at ht
      rw [hmv]; split_ifs
      · simp
      · exact hI.a4 J c hJv ht hc
  · intro v c c'' hc hc''
    rw [hmv] at hc hc''
    split_ifs at hc hc'' with h1 h2 h2
    · exact h1.trans h2.symm
    · cases hc
    · cases hc''
    · exact hI.l4 v c c'' hc hc''
  · intro q hq hE
    by_cases hqp : q = p
    · subst hqp; simp [C'] at hq
    · rw [hJ q hqp] at hq hE ⊢
      rw [hmv] at hE; split_ifs at hE with hx
      rw [hC', upd_lks_ne _ _ _ _ hx]; exact hI.isc q hq hE

/-- An owner overwrites its own cell with `w'` (a final copy, line 67, or `TOMBSTONE`, line 80)
and leaves (it is about to return). -/
lemma inv_leave (hI : Inv h N ts C) (hp : C.pend p ≠ none) {l' : Loc K m} {w' : Cell K}
    (hv : (C.loc p).pc.isVal) (hnv' : l'.pc.isVal = false) (hni' : l'.pc.isIns = false)
    (hloc : LocInv l') (hrec : recorded l' = none) (hE : w' ≠ .empty)
    (hnoTt : ∀ v, w' ≠ .key v .tent) (hreval : ∀ v, w' ≠ .key v .reval)
    (hF : ∀ v, w' = .key v .fin → v = (C.loc p).op.key ∧
      C.val (C.loc p).j = .key (C.loc p).op.key .tent ∧ (C.loc p).pc = .l67SC) :
    Inv h (N + 1) ts (upd C p l' (C.loc p).j (w', [])) := by
  set l := C.loc p with hl
  set C' := upd C p l' l.j (w', []) with hC'
  have hJ : ∀ J, J ≠ p → C'.loc J = C.loc J := fun J hJ => upd_loc_ne _ _ _ _ hJ
  have hmv : ∀ y, C'.val y = if y = l.j then w' else C.val y := fun y => by
    rw [hC', mem_val_upd]
  have hoth : ∀ q, q ≠ p → (C.loc q).pc.isVal → (C.loc q).j ≠ l.j := by
    intro q hqp hq hj; exact hqp (hI.own_inj q p hq hv hj)
  have hEold : ∀ y, C'.val y = .empty → C.val y = .empty := by
    intro y hy; rw [hmv] at hy; split_ifs at hy
    · exact absurd hy hE
    · exact hy
  have hpnv : (C'.loc p).pc.isVal = false := by simp [C', hnv']
  refine ⟨idle_upd hI hp, loc_upd_inv hI hloc, ?_, ?_, ?_, ?_, ?_, ?_,
    ts_lt_upd hI ts (fun _ => Or.inl rfl), ?_, ?_, ?_, ?_, ?_⟩
  · apply link_upd hI (Or.inr (Or.inr rfl))
    intro y w hr; rw [hrec] at hr; cases hr
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [hpnv] at hq; cases hq
    · rw [hJ q hqp] at hq ⊢; rw [hmv, if_neg (hoth q hqp hq)]; exact hI.own q hq
  · intro q r hq hr hqr
    have hqp : q ≠ p := by rintro rfl; rw [hpnv] at hq; cases hq
    have hrp : r ≠ p := by rintro rfl; rw [hpnv] at hr; cases hr
    rw [hJ q hqp] at hq hqr; rw [hJ r hrp] at hr hqr
    exact hI.own_inj q r hq hr hqr
  · intro c v t hc ht
    rw [hmv] at hc; split_ifs at hc with hx
    · subst hx; cases t
      · exact absurd hc (hnoTt v)
      · exact absurd rfl ht
      · exact absurd hc (hreval v)
    · obtain ⟨q, hq1, hq2, hq3⟩ := hI.own2 c v t hc ht
      have hqp : q ≠ p := by rintro rfl; exact hx hq2.symm
      exact ⟨q, by rw [hJ q hqp]; exact ⟨hq1, hq2, hq3⟩⟩
  · intro c v t hc c'' hd hc''
    have hc''' := hEold c'' hc''
    rw [hmv] at hc; split_ifs at hc with hx
    · subst hx
      obtain ⟨rfl, hj, -⟩ := hF v (by cases t <;> simp_all)
      exact hI.p3 _ _ _ hj c'' hd hc'''
    · exact hI.p3 c v t hc c'' hd hc'''
  · intro q hq c hd hc
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self] at hq; simp [hnv', hni'] at hq
    · rw [hJ q hqp] at hq hd; exact hI.p3' q hq c hd (hEold c hc)
  · -- a1
    intro I J hIJ hIv hJv hk ht hc
    have hIp : I ≠ p := by rintro rfl; rw [hpnv] at hIv; cases hIv
    have hJp : J ≠ p := by rintro rfl; rw [hpnv] at hJv; cases hJv
    rw [hJ I hIp] at hIv hk ht hc; rw [hJ J hJp] at hJv hk ht hc
    rw [hmv, if_neg (hoth J hJp hJv)] at ht
    exact hI.a1 I J hIJ hIv hJv hk ht hc
  · -- doc
    intro I J hd hJv hjj hk ht
    have hJp : J ≠ p := by rintro rfl; rw [hpnv] at hJv; cases hJv
    have hIp : I ≠ p := by
      rintro rfl; simp only [C', upd_loc_self] at hd
      rcases hd with ⟨h1 | h1, -⟩ | h1 <;> simp [h1, PC.isVal] at hnv'
    rw [hJ I hIp] at hd hjj hk ht; rw [hJ J hJp] at hJv hjj hk
    have hx : (C.loc I).i ≠ l.j := hjj ▸ hoth J hJp hJv
    rw [hmv, if_neg hx] at ht
    have hd' : ((((C.loc I).pc = .docRD ∨ (C.loc I).pc = .docSC) ∧ I ∉ C.lks (C.loc I).i) ∨
        (C.loc I).pc = .docRD2) := by
      rcases hd with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨h1, by rwa [hC', upd_lks_ne _ _ _ _ hx] at h2⟩
      · exact Or.inr h1
    exact hI.doc I J hd' hJv hjj hk ht
  · -- a4: the key step of Lemma 4
    intro J c hJv ht hc
    have hJp : J ≠ p := by rintro rfl; rw [hpnv] at hJv; cases hJv
    rw [hJ J hJp] at hJv ht hc ⊢
    rw [hmv, if_neg (hoth J hJp hJv)] at ht
    rw [hmv]; split_ifs with hx
    · intro hw
      obtain ⟨hk, hj, hpc⟩ := hF _ hw
      subst hx
      -- `J` covers `p`'s cell, and `p` covers everything: contradiction via `a1` twice
      have h1 := hI.a1 J p (Ne.symm hJp.symm) hJv hv hk.symm (by rw [hj, hk]) hc
      have h2 := hI.a1 p J hJp.symm hv hJv hk (by rw [ht, hk])
        (by show covers h l _; simp [covers, hpc])
      omega
    · exact hI.a4 J c hJv ht hc
  · -- l4
    intro v c c'' hc hc''
    rw [hmv] at hc hc''
    split_ifs at hc hc'' with h1 h2 h2
    · exact h1.trans h2.symm
    · subst h1
      obtain ⟨rfl, hj, hpc⟩ := hF v hc
      exact absurd hc'' (hI.a4 p c'' hv hj (by show covers h l _; simp [covers, hpc]))
    · subst h2
      obtain ⟨rfl, hj, hpc⟩ := hF v hc''
      exact absurd hc (hI.a4 p c hv hj (by show covers h l _; simp [covers, hpc]))
    · exact hI.l4 v c c'' hc hc''
  · intro q hq hE'
    by_cases hqp : q = p
    · subst hqp; simp only [C', upd_loc_self] at hq; simp [hq, PC.isIns] at hni'
    · rw [hJ q hqp] at hq hE' ⊢
      rw [hmv] at hE'; split_ifs at hE' with hx
      · exact absurd hE' hE
      · rw [hC', upd_lks_ne _ _ _ _ hx]; exact hI.isc q hq hE'

end Podc.LockFreeLinearProbing
