import Papers.PODC2025.AuditingWithoutLeaks.SimCommon

/-!
# Lemma 6: writes are uncompromised by readers

If reader `p_j` never applied fetch&xor to `R` while `R` held a triple with value `v` (at a
sequence number `≥ 1`), then renaming the input of every `write(v)` to `v' ≠ v` yields an
execution (same schedule, same one-time pads) that `p_j` cannot distinguish.
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au]

section Defs

variable (v v' : V)

/-- Renaming of write inputs. -/
def rn (x : V) : V := if x = v then v' else x

/-- Renaming of the value associated with sequence number `t` (`t = 0` holds the initial value,
which is not the input of a write). -/
def rv (t : ℕ) (x : V) : V := if t = 0 then x else rn v v' x

/-- Renaming of a triple. -/
def rR (r : RVal m V) : RVal m V := ⟨r.seq, rv v v' r.seq r.val, r.bits⟩

/-- Renaming of a writer's local state. -/
def rW : Loc m V → Loc m V
  | .wSN x => .wSN (rn v v' x)
  | .wR x sn => .wR (rn v v' x) sn
  | .wV x sn r => .wV (rn v v' x) sn (rR v v' r)
  | .wB x sn r todo => .wB (rn v v' x) sn (rR v v' r) todo
  | .wCAS x sn r => .wCAS (rn v v' x) sn (rR v v' r)
  | .wIdle => .wIdle
  | .wHelp sn => .wHelp sn
  | .wRet => .wRet
  | l => l

/-- Renaming of invocations. -/
def renOp : AOp m V → AOp m V
  | .write x => .write (rn v v' x)
  | o => o

variable (j : Fin m) (v₀ : V)

/-- Per-process part of the simulation relation: reader `j` is in the same local state, writers
are renamed, the other processes have the same control skeleton. -/
def PRelA : Proc m W Au → Loc m V → Loc m V → Prop
  | .rd i, l, l' => if i = j then l' = l else skel v₀ l' = skel v₀ l
  | .wr _, l, l' => l' = rW v v' l
  | .au _, l, l' => skel v₀ l' = skel v₀ l

/-- The simulation relation between a configuration of the original execution and one of the
renamed execution. -/
structure SimA (C C' : Cfg m W Au V v₀) : Prop where
  pend : ∀ p, C'.pend p = (C.pend p).map (renOp v v')
  R : (C'.mem .R : RVal m V) = rR v v' (C.mem .R)
  SN : (C'.mem .SN : ℕ) = C.mem .SN
  loc : ∀ p, PRelA v v' j v₀ p (C.loc p) (C'.loc p)

end Defs

variable {v v' v₀ : V} {j : Fin m} {rnd : ℕ → Fin m → Bool}

lemma rW_wBnext (x : V) (sn : ℕ) (r : RVal m V) (todo : List (Fin m)) :
    rW v v' (wBnext x sn r todo) = wBnext (rn v v' x) sn (rR v v' r) todo := by
  cases todo <;> simp [wBnext, rW]

lemma todoOf_rR (r : RVal m V) : todoOf rnd (rR v v' r) = todoOf rnd r := rfl

lemma rn_ne (hvv : v' ≠ v) (x : V) : rn v v' x ≠ v := by
  unfold rn; split_ifs with h
  · exact hvv
  · exact h

lemma rR_eq_iff {r R : RVal m V} (h1 : r.seq ≤ R.seq) (h2 : r.seq = R.seq → r.val = R.val) :
    rR v v' R = rR v v' r ↔ R = r := by
  constructor
  · intro h
    have hs : R.seq = r.seq := by simpa [rR] using congrArg RVal.seq h
    have hb : R.bits = r.bits := by simpa [rR] using congrArg RVal.bits h
    have hv : R.val = r.val := (h2 hs.symm).symm
    cases R; cases r; simp_all
  · rintro rfl; rfl

lemma renOp_ne (hvv : v' ≠ v) (o : AOp m V) : renOp v v' o ≠ AOp.write v := by
  cases o <;> simp [renOp, rn_ne hvv]

lemma SimA.frame {C C' D D' : Cfg m W Au V v₀} (hS : SimA v v' j v₀ C C') (p : Proc m W Au)
    (hp : ∀ q, D'.pend q = (D.pend q).map (renOp v v'))
    (hl : ∀ q, q ≠ p → D.loc q = C.loc q) (hl' : ∀ q, q ≠ p → D'.loc q = C'.loc q)
    (hR : (D'.mem .R : RVal m V) = rR v v' (D.mem .R)) (hSN : (D'.mem .SN : ℕ) = D.mem .SN)
    (hpp : PRelA v v' j v₀ p (D.loc p) (D'.loc p)) : SimA v v' j v₀ D D' := by
  refine ⟨hp, hR, hSN, fun q => ?_⟩
  by_cases h : q = p
  · subst h; exact hpp
  · rw [hl q h, hl' q h]; exact hS.loc q

/-- Writer steps. -/
lemma simA_tau_wr {C C' D : Cfg m W Au V v₀} (hI : Inv rnd C) (hS : SimA v v' j v₀ C C')
    {w : W} (hs : (alg1 rnd v₀).step C (.tau (.wr w)) = some D) :
    ∃ D', (alg1 rnd v₀).step C' (.tau (.wr w)) = some D' ∧ SimA v v' j v₀ D D' := by
  obtain ⟨h0, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have h0' : C'.pend (.wr w) ≠ none := fun h => h0 (Option.map_eq_none_iff.1 (hS.pend _ ▸ h))
  have hl' : C'.loc (.wr w) = rW v v' (C.loc (.wr w)) := hS.loc (.wr w)
  have hR := hS.R
  have hSN := hS.SN
  have hr := hI.wr w
  unfold WInv at hr
  cases hl : C.loc (.wr w) <;> rw [hl] at hr hl' <;>
    simp only [alg1, writerAct, hl, reduceCtorEq] at hact
  case wB x sn r todo =>
    cases todo with
    | nil => simp at hact
    | cons i rest =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact
      obtain rfl := eq_of_heq ho
      obtain rfl := eq_of_heq hk
      refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
      refine hS.frame (.wr w) (fun q => by rw [hpend]; exact hS.pend q)
        (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
        (by simp [hmem, hSN]) ?_
      simp [PRelA, hloc, rW_wBnext]
  case wCAS x sn r =>
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨-, ⟨hw1, hw2, hw3, -, -⟩, -, -⟩ := hr
    have hiff : rR v v' (C.mem .R) = rR v v' r ↔ (C.mem .R : RVal m V) = r := by
      refine rR_eq_iff hw2 (fun h => ?_)
      rw [hw3]; simp [AuditingWithoutLeaks.hv, h, rOf]
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    have hsn : sn ≠ 0 := by omega
    by_cases heq : (C.mem .R : RVal m V) = r
    · refine hS.frame (.wr w) (fun q => by rw [hpend]; exact hS.pend q)
        (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (by simp [hmem, hR, heq, rR, rv, hsn]) (by simp [hmem, hSN]) ?_
      simp [PRelA, hloc, hl', rW, hR, heq]
    · have hne : rR v v' (C.mem .R) ≠ rR v v' r := fun h => heq (hiff.1 h)
      refine hS.frame (.wr w) (fun q => by rw [hpend]; exact hS.pend q)
        (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (by simp [hmem, hR, heq, hne]) (by simp [hmem, hSN]) ?_
      simp [PRelA, hloc, hl', rW, hR, heq, hne]
  all_goals
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine hS.frame (.wr w) (fun q => by rw [hpend]; exact hS.pend q)
      (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
  case wSN x => simp [PRelA, hloc, hl', hSN, rW]
  case wR x sn =>
    simp only [PRelA, hloc, hl', hR, Function.update_self, rW]
    simp only [rR]; by_cases h : sn ≤ (C.mem Obj.R).seq <;> simp [h, rW, rR]
  case wV x sn r => simp [PRelA, hloc, rW_wBnext, todoOf_rR]
  case wHelp sn => simp [PRelA, hloc, hl', rW]

lemma obs_other {C C' : Cfg m W Au V v₀} {rnd' : ℕ → Fin m → Bool} {p q : Proc m W Au}
    (h : p ≠ q) {ℓ ℓ' : Label (Proc m W Au) (auditReg m V v₀)} (h1 : ℓ.proc = p) (h2 : ℓ'.proc = p) :
    (alg1 rnd' v₀).obsStep C' q ℓ' = (alg1 rnd v₀).obsStep C q ℓ := by
  rw [Impl.obsStep_eq_none_of_proc_ne _ _ (by rw [h2]; exact h),
    Impl.obsStep_eq_none_of_proc_ne _ _ (by rw [h1]; exact h)]

/-- Reader steps. -/
lemma simA_tau_rd {C C' D : Cfg m W Au V v₀} (hI : Inv rnd C) (hS : SimA v v' j v₀ C C')
    {i : Fin m} (hs : (alg1 rnd v₀).step C (.tau (.rd i)) = some D)
    (hfx : i = j → ∀ prev y, C.loc (.rd j) = .rFX prev y →
      rv v v' (C.mem .R : RVal m V).seq (C.mem .R : RVal m V).val = (C.mem .R : RVal m V).val) :
    ∃ D', (alg1 rnd v₀).step C' (.tau (.rd i)) = some D' ∧ SimA v v' j v₀ D D' ∧
      (alg1 rnd v₀).obsStep C' (.rd j) (.tau (.rd i)) =
        (alg1 rnd v₀).obsStep C (.rd j) (.tau (.rd i)) := by
  obtain ⟨h0, hpend, o_i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hact0 := hact
  have h0' : C'.pend (.rd i) ≠ none := fun h => h0 (Option.map_eq_none_iff.1 (hS.pend _ ▸ h))
  have hP := hS.loc (.rd i)
  have hsk : skel v₀ (C'.loc (.rd i)) = skel v₀ (C.loc (.rd i)) := by
    simp only [PRelA] at hP; split_ifs at hP
    · rw [hP]
    · exact hP
  have heqj : i = j → C'.loc (.rd i) = C.loc (.rd i) := by
    intro h; simp only [PRelA, h, ite_true] at hP; subst h; exact hP
  have hR := hS.R
  have hSN := hS.SN
  have hr := (hI.rd i).2
  cases hl : C.loc (.rd i) <;> rw [hl] at hr hsk heqj <;>
    simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
    cases hl' : C'.loc (.rd i) <;> simp only [skel, hl', reduceCtorEq] at hsk
  case rSN.rSN prev prev' =>
    simp only [Loc.rSN.injEq] at hsk
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_, ?_⟩
    · refine hS.frame (.rd i) (fun q => by rw [hpend]; exact hS.pend q)
        (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
        (by simp [hmem, hSN]) ?_
      by_cases hij : i = j
      · have := heqj hij; rw [hl'] at this; cases this
        simp only [PRelA, hij, ↓reduceIte, hloc, Function.update_self]
        rw [hSN]
      · simp only [PRelA, hij, ↓reduceIte, hloc, Function.update_self]
        rw [hSN]
        rcases prev with _ | ⟨a, b⟩ <;> rcases prev' with _ | ⟨a', b'⟩ <;>
          simp_all [skP, skel] <;> split_ifs <;> simp_all [skel, skP]
    · by_cases hij : i = j
      · subst hij
        simp [Impl.obsStep, hl, hl', alg1, readerAct, hSN]
      · exact obs_other (p := .rd i) (by simpa using hij) rfl rfl
  case rFX.rFX prev y prev' y' =>
    simp only [Loc.rFX.injEq] at hsk
    obtain ⟨hsk, rfl⟩ := hsk
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_, ?_⟩
    · refine hS.frame (.rd i) (fun q => by rw [hpend]; exact hS.pend q)
        (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR, rR, flip])
        (by simp [hmem, hSN]) ?_
      simp only [PRelA, hloc, Function.update_self]
      split_ifs with hij
      · subst hij
        have := heqj rfl; rw [hl'] at this; cases this
        have hv := hfx rfl _ _ hl
        simp [hR, rR, hv]
      · simp [hR, rR, skel, hsk]
    · by_cases hij : i = j
      · subst hij
        have hv := hfx rfl _ _ hl
        simp [Impl.obsStep, hl, hl', alg1, readerAct, hR, rR, hv]
      · exact obs_other (p := .rd i) (by simpa using hij) rfl rfl
  case rCAS.rCAS prev sn val prev' sn' val' =>
    simp only [Loc.rCAS.injEq] at hsk
    obtain ⟨hsk, rfl, -⟩ := hsk
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_, ?_⟩
    · refine hS.frame (.rd i) (fun q => by rw [hpend]; exact hS.pend q)
        (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
        (by simp [hmem, hSN]) ?_
      simp only [PRelA, hloc, Function.update_self]
      split_ifs with hij
      · have := heqj hij; rw [hl'] at this; cases this; simp
      · simp [skel, skP]
    · by_cases hij : i = j
      · subst hij
        simp [Impl.obsStep, hl, hl', alg1, readerAct, hSN]
      · exact obs_other (p := .rd i) (by simpa using hij) rfl rfl

/-- Auditor steps. -/
lemma simA_tau_au {C C' D : Cfg m W Au V v₀} (hI : Inv rnd C) (hS : SimA v v' j v₀ C C')
    {a : Au} (hs : (alg1 rnd v₀).step C (.tau (.au a)) = some D) :
    ∃ D', (alg1 rnd v₀).step C' (.tau (.au a)) = some D' ∧ SimA v v' j v₀ D D' := by
  obtain ⟨h0, hpend, o_i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have h0' : C'.pend (.au a) ≠ none := fun h => h0 (Option.map_eq_none_iff.1 (hS.pend _ ▸ h))
  have hsk : skel v₀ (C'.loc (.au a)) = skel v₀ (C.loc (.au a)) := hS.loc (.au a)
  have hR := hS.R
  have hSN := hS.SN
  cases hl : C.loc (.au a) <;> rw [hl] at hsk <;>
    simp only [alg1, auditorAct, hl, reduceCtorEq] at hact <;>
    cases hl' : C'.loc (.au a) <;> simp only [skel, hl', reduceCtorEq] at hsk <;>
    simp only [Action.access.injEq] at hact <;>
    obtain ⟨rfl, ho, hk⟩ := hact <;>
    obtain rfl := eq_of_heq ho <;>
    obtain rfl := eq_of_heq hk
  case aR.aR A lsa A' lsa' =>
    simp only [Loc.aR.injEq, true_and] at hsk; subst hsk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine hS.frame (.au a) (fun q => by rw [hpend]; exact hS.pend q)
      (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    simp only [PRelA, hloc, Function.update_self]
    rw [hR]; exact skel_aNext v₀ (r := C.mem Obj.R) (r' := rR v v' (C.mem Obj.R)) rfl _
  case aV.aV A r s A' r' s' =>
    simp only [Loc.aV.injEq, true_and, skR, RVal.mk.injEq, and_true] at hsk
    obtain ⟨hr, rfl⟩ := hsk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine hS.frame (.au a) (fun q => by rw [hpend]; exact hS.pend q)
      (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    simp only [PRelA, hloc, Function.update_self]
    exact skel_aVnext v₀ hr _ _ _
  case aB.aB A r s val i A' r' s' val' i' =>
    simp only [Loc.aB.injEq, true_and, skR, RVal.mk.injEq, and_true] at hsk
    obtain ⟨hr, rfl, rfl⟩ := hsk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine hS.frame (.au a) (fun q => by rw [hpend]; exact hS.pend q)
      (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    simp only [PRelA, hloc, Function.update_self]
    exact skel_aBnext v₀ hr _ _ _ _
  case aCAS.aCAS A r A' r' =>
    simp only [Loc.aCAS.injEq, true_and, skR, RVal.mk.injEq, and_true] at hsk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine hS.frame (.au a) (fun q => by rw [hpend]; exact hS.pend q)
      (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
      (by simp [hmem, hSN, hsk]) ?_
    simp [PRelA, hloc, skel, hsk]

/-- Invocations. -/
lemma simA_inv {C C' D : Cfg m W Au V v₀} (hI : Inv rnd C) (hS : SimA v v' j v₀ C C')
    {p : Proc m W Au} {o : AOp m V} (hs : (alg1 rnd v₀).step C (.inv p o) = some D) :
    ∃ D', (alg1 rnd v₀).step C' (.inv p (renOp v v' o)) = some D' ∧ SimA v v' j v₀ D D' ∧
      (alg1 rnd v₀).obsStep C' (.rd j) (.inv p (renOp v v' o)) =
        (alg1 rnd v₀).obsStep C (.rd j) (.inv p o) := by
  obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have h0' : C'.pend p = none := by rw [hS.pend, h0]; rfl
  have hal' : (alg1 (W := W) (Au := Au) rnd v₀).allowed p (renOp v v' o) := by
    cases p <;> cases o <;> simp_all [alg1, allowed, renOp]
  have hR := hS.R
  have hSN := hS.SN
  refine ⟨_, Impl.step_inv_eq_some h0' hal', ?_, ?_⟩
  · refine hS.frame p (fun q => ?_) (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    · by_cases hq : q = p
      · subst hq; simp [hpend]
      · simp [hpend, Function.update_of_ne hq]; exact hS.pend q
    have hP := hS.loc p
    cases p with
    | rd i =>
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      subst hal
      obtain ⟨prev, hl, -⟩ := (hI.rd _).idle h0
      simp only [PRelA, hl] at hP
      simp only [PRelA, hloc, Function.update_self, hl, renOp, alg1]
      split_ifs at hP ⊢ with hij
      · rw [hP]
      · cases hl' : C'.loc (.rd _) <;> simp only [hl', skel, reduceCtorEq] at hP
        simp only [Loc.rIdle.injEq] at hP
        simp [invoke, skel, hP]
    | wr w =>
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      have hl := (hI.wr w).idle h0
      simp only [PRelA, hl, rW] at hP
      simp [PRelA, hloc, hl, hP, renOp, alg1, invoke, rW]
    | au a =>
      cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
      obtain ⟨A, lsa, hl, -⟩ := (hI.au a).idle h0
      simp only [PRelA, hl] at hP
      cases hl' : C'.loc (.au a) <;> simp only [hl', skel, reduceCtorEq] at hP
      simp only [Loc.aIdle.injEq, true_and] at hP
      simp [PRelA, hloc, hl, hl', hP, renOp, alg1, invoke, skel]
  · by_cases hp : p = .rd j
    · subst hp
      cases o <;> simp_all [alg1, allowed, renOp, Impl.obsStep]
    · simp [Impl.obsStep, hp]

/-- Responses. -/
lemma simA_ret {C C' D : Cfg m W Au V v₀} (hI : Inv rnd C) (hS : SimA v v' j v₀ C C')
    {p : Proc m W Au} {r : AResp m V} (hs : (alg1 rnd v₀).step C (.ret p r) = some D) :
    ∃ r' D', (alg1 rnd v₀).step C' (.ret p r') = some D' ∧ SimA v v' j v₀ D D' ∧
      (alg1 rnd v₀).obsStep C' (.rd j) (.ret p r') = (alg1 rnd v₀).obsStep C (.rd j) (.ret p r) := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  have h0' : C'.pend p ≠ none := fun h => h0 (Option.map_eq_none_iff.1 (hS.pend _ ▸ h))
  have hR := hS.R
  have hSN := hS.SN
  have hP := hS.loc p
  have fr : ∀ l', PRelA v v' j v₀ p l l' →
      SimA v v' j v₀ D ⟨Function.update C'.loc p l', Function.update C'.pend p none, C'.mem⟩ := by
    intro l' hl'
    refine hS.frame p (fun q => ?_) (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (by simp [hmem, hR])
      (by simp [hmem, hSN]) (by simpa [hloc] using hl')
    by_cases hq : q = p
    · subst hq; simp [hpend]
    · simp [hpend, Function.update_of_ne hq]; exact hS.pend q
  cases p with
  | rd i =>
    have hr := (hI.rd i).2
    cases hl : C.loc (.rd i) <;> rw [hl] at hr hP <;>
      simp only [alg1, readerAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
      simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
    · exact absurd hr.1 h0
    · rename_i prev val
      obtain ⟨rfl, rfl⟩ := hact
      simp only [PRelA] at hP
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte] at hP
        refine ⟨_, _, Impl.step_ret_eq_some h0' (by rw [hP]; rfl), fr _ (by simp [PRelA]), rfl⟩
      · simp only [hij, ↓reduceIte] at hP
        cases hl' : C'.loc (.rd i) <;> simp only [hl', skel, reduceCtorEq] at hP
        rename_i prev' val'
        simp only [Loc.rRet.injEq, and_true] at hP
        refine ⟨_, _, Impl.step_ret_eq_some h0' (by rw [hl']; rfl),
          fr _ (by simp [PRelA, hij, skel, hP]), ?_⟩
        simp [Impl.obsStep, hij]
  | wr w =>
    have hr := hI.wr w
    unfold WInv at hr
    simp only [PRelA] at hP
    cases hl : C.loc (.wr w) <;> rw [hl] at hr hP <;>
      simp only [alg1, writerAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
      simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
    · exact absurd hr h0
    · rename_i x sn rr todo
      cases todo with
      | nil => exact absurd rfl hr.2.2.2.1
      | cons j rest => simp at hact
    · obtain ⟨rfl, rfl⟩ := hact
      refine ⟨_, _, Impl.step_ret_eq_some h0' (by rw [hP]; rfl),
        fr _ (by simp [PRelA, rW]), ?_⟩
      simp [Impl.obsStep]
  | au a =>
    have hr := hI.au a
    unfold AInv at hr
    simp only [PRelA] at hP
    cases hl : C.loc (.au a) <;> rw [hl] at hr hP <;>
      simp only [alg1, auditorAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
      simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
    · exact absurd hr.1 h0
    · rename_i A lsa
      obtain ⟨rfl, rfl⟩ := hact
      cases hl' : C'.loc (.au a) <;> simp only [hl', skel, reduceCtorEq] at hP
      simp only [Loc.aRet.injEq, true_and] at hP
      refine ⟨_, _, Impl.step_ret_eq_some h0' (by rw [hl']; rfl),
        fr _ (by simp [PRelA, skel, hP]), ?_⟩
      simp [Impl.obsStep]

/-- One step of the simulation. -/
lemma simA_step (hvv : v' ≠ v) {C C' D : Cfg m W Au V v₀} (hI : Inv rnd C)
    (hS : SimA v v' j v₀ C C') {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hs : (alg1 rnd v₀).step C ℓ = some D)
    (hfx : ℓ = .tau (.rd j) → ∀ prev y, C.loc (.rd j) = .rFX prev y →
      rv v v' (C.mem .R : RVal m V).seq (C.mem .R : RVal m V).val = (C.mem .R : RVal m V).val) :
    ∃ ℓ' D', (alg1 rnd v₀).step C' ℓ' = some D' ∧ SimA v v' j v₀ D D' ∧
      (alg1 rnd v₀).obsStep C' (.rd j) ℓ' = (alg1 rnd v₀).obsStep C (.rd j) ℓ ∧
      ∀ w, ℓ'.invOf (.wr w) ≠ some (.write v) := by
  cases ℓ with
  | inv p o =>
    obtain ⟨D', h1, h2, h3⟩ := simA_inv hI hS hs
    refine ⟨_, D', h1, h2, h3, fun w => ?_⟩
    dsimp only [Label.invOf]
    split_ifs
    · intro h; exact renOp_ne hvv o (Option.some.inj h)
    · simp
  | ret p r =>
    obtain ⟨r', D', h1, h2, h3⟩ := simA_ret hI hS hs
    exact ⟨_, D', h1, h2, h3, fun w => by simp⟩
  | tau p =>
    cases p with
    | rd i =>
      obtain ⟨D', h1, h2, h3⟩ := simA_tau_rd hI hS hs (fun h => hfx (by rw [h]))
      exact ⟨_, D', h1, h2, h3, fun w => by simp⟩
    | wr w =>
      obtain ⟨D', h1, h2⟩ := simA_tau_wr hI hS hs
      exact ⟨_, D', h1, h2, obs_other (p := .wr w) (by simp) rfl rfl, fun w => by simp⟩
    | au a =>
      obtain ⟨D', h1, h2⟩ := simA_tau_au hI hS hs
      exact ⟨_, D', h1, h2, obs_other (p := .au a) (by simp) rfl rfl, fun w => by simp⟩

lemma simA_init :
    SimA v v' j v₀ (alg1 (W := W) (Au := Au) rnd v₀).initCfg (alg1 rnd v₀).initCfg := by
  refine ⟨fun p => rfl, by simp [Impl.initCfg, alg1, rR, rv], rfl, fun p => ?_⟩
  cases p <;> simp [PRelA, Impl.initCfg, alg1, locInit, rW]

lemma obsFrom_concat {rnd' : ℕ → Fin m → Bool} {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    {C : Cfg m W Au V v₀} (hα : (alg1 rnd' v₀).run α = some C) {ℓ} {D : Cfg m W Au V v₀}
    (hs : (alg1 rnd' v₀).step C ℓ = some D) (p : Proc m W Au) :
    (alg1 rnd' v₀).obsFrom p (alg1 rnd' v₀).initCfg (α ++ [ℓ]) =
      (alg1 rnd' v₀).obsFrom p (alg1 rnd' v₀).initCfg α ++ ((alg1 rnd' v₀).obsStep C p ℓ).toList := by
  rw [Impl.obsFrom_append_of_runFrom _ p hα, Impl.obsFrom_cons_of_step _ p hs]; simp

/-- The renamed execution exists along every execution in which reader `j` never fetched a
triple with value `v`. -/
lemma simA_run (hvv : v' ≠ v) {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    {C : Cfg m W Au V v₀} (hα : (alg1 rnd v₀).run α = some C)
    (hnf : ∀ t, Fetched rnd C j t → hv v₀ C t ≠ v) :
    ∃ α' C', (alg1 rnd v₀).run α' = some C' ∧ SimA v v' j v₀ C C' ∧
      (alg1 rnd v₀).obsFrom (.rd j) (alg1 rnd v₀).initCfg α' =
        (alg1 rnd v₀).obsFrom (.rd j) (alg1 rnd v₀).initCfg α ∧
      ∀ w, ∀ o ∈ opsOf α' (.wr w), o ≠ .write v := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at hα; subst hα
    exact ⟨[], _, rfl, simA_init, rfl, fun w o ho => by simp at ho⟩
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at hα
    cases hα₁ : (alg1 rnd v₀).run α with
    | none => simp [hα₁] at hα
    | some C₁ =>
      simp only [hα₁, Option.bind_some] at hα
      have hI₁ := Inv.of_run hα₁
      have hI := Inv.of_run (α := α ++ [ℓ]) (by rw [Impl.run_concat, hα₁]; exact hα)
      have E := (Inv.step hI₁ hα).2
      have hnf₁ : ∀ t, Fetched rnd C₁ j t → hv v₀ C₁ t ≠ v := by
        intro t hf
        have ht : t ≤ (rOf C₁).seq := by rcases hf with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
        rw [← E.hv t ht]; exact hnf t (E.fet _ _ hf)
      obtain ⟨α', C₁', h1, hS, hobs, hops⟩ := ih hα₁ hnf₁
      have hfx : ℓ = .tau (.rd j) → ∀ prev y, C₁.loc (.rd j) = .rFX prev y →
          rv v v' (C₁.mem .R : RVal m V).seq (C₁.mem .R : RVal m V).val =
            (C₁.mem .R : RVal m V).val := by
        rintro rfl prev y hl
        obtain ⟨-, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hα
        simp only [alg1, readerAct, hl, Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact
        obtain rfl := eq_of_heq ho
        obtain rfl := eq_of_heq hk
        have hlj : C.loc (.rd j) = .rCAS prev (C₁.mem .R : RVal m V).seq
            (C₁.mem .R : RVal m V).val := by simp [hloc]
        have hr := (hI.rd j).2
        rw [hlj] at hr
        obtain ⟨-, -, -, -, -, h6, h7⟩ := hr
        have := hnf _ h7
        rw [← h6] at this
        unfold rv rn; split_ifs <;> simp_all
      obtain ⟨ℓ', D', h2, hS', hob, hinv⟩ := simA_step hvv hI₁ hS hα hfx
      refine ⟨α' ++ [ℓ'], D', by rw [Impl.run_concat, h1]; exact h2, hS', ?_, fun w o ho => ?_⟩
      · rw [obsFrom_concat h1 h2, obsFrom_concat hα₁ hα, hobs, hob]
      · rw [opsOf_concat, List.mem_append] at ho
        rcases ho with h | h
        · exact hops w o h
        · cases h' : ℓ'.invOf (.wr w) with
          | none => simp [h'] at h
          | some o' =>
            simp only [h', Option.toList_some, List.mem_singleton] at h; subst h
            intro h''; subst h''; exact hinv w h'

/-- **Lemma 6** of Attiya et al. (core): if reader `p_j` never applied fetch&xor to `R` while
`R` held a triple whose value is `v` (`Fetched` at the end of the execution records every
fetch&xor of `p_j`; `hv` gives the value of each sequence number), then renaming the input of
every `write(v)` to `v' ≠ v` (same schedule, same one-time pads) gives an execution that `p_j`
cannot distinguish from `α` and in which no write has input `v`. -/
theorem rename_writes {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) (j : Fin m) {v v' : V} (hvv : v' ≠ v)
    (hnf : ∀ t, Fetched rnd C j t → hv v₀ C t ≠ v) :
    ∃ α', (alg1 rnd v₀).Valid α' ∧
      Impl.IndistFam (fun θ => alg1 (W := W) (Au := Au) θ v₀) (.rd j) (rnd, α) (rnd, α') ∧
      ∀ w, ∀ o ∈ opsOf α' (.wr w), o ≠ .write v := by
  obtain ⟨α', C', h1, -, hobs, hops⟩ := simA_run (j := j) hvv hα hnf
  refine ⟨α', ⟨C', h1⟩, ?_, hops⟩
  simp only [Impl.IndistFam, Impl.procView, hobs]

end Podc.AuditingWithoutLeaks
