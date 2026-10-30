import Papers.PODC2025.AuditingWithoutLeaks.RenameWrites

/-!
# Lemma 7: reads are uncompromised by other readers

For readers `p_j ≠ p_k`, every execution `α` of Algorithm 1 has an indistinguishable (to `p_j`)
execution `α'`, with other one-time pads, in which `p_k` invokes nothing.

The paper's construction ("remove the reads of `p_k`, flip bit `k` of `rand_x`") has to be
completed in two places:

* a direct read of `p_k` also applies `SN.compare&swap(sn-1, sn)` (line 5); when this step
  moves `SN`, the writer poised at line 15 for `sn` (it exists, `DInv`) takes its step at this
  point of `α'` instead, and its own (in `α` failing) line-15 step is dropped later;
* a writer's `R.compare&swap` may fail in `α` only because `p_k` flipped bit `k` in between;
  hence every loop iteration of a writer (lines 10–14) whose compare&swap fails in `α`, or which
  is not finished at the end of `α`, is dropped from `α'` (its only shared effects are writes to
  `V` and `B`, which affect only audit responses). Writes of `B[s][k]` are dropped as well.

The pads of `α'` agree with those of `α` except for bit `k` of `rand_s`, which is the bit `k`
that `p_j` observes when it applies fetch&xor to `R` while `R.seq = s` (if it does). This is
well defined because `p_j` applies at most one fetch&xor per sequence number (Lemma 17).

Since whether an iteration's compare&swap succeeds depends on the future, the simulation
relation is indexed by the remaining suffix of `α` (`casOK`), and the new pads are computed from
the whole execution (`fxBit`).
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au]

section Defs

variable (rnd rnd' : ℕ → Fin m → Bool) (v₀ : V) (j k : Fin m)

/-- A reader poised to apply fetch&xor (line 4). -/
def isFX : Loc m V → Bool
  | .rFX _ _ => true
  | _ => false

/-- The triple a writer poised at line 14 compares `R` with. -/
def casTarget : Loc m V → Option (RVal m V)
  | .wCAS _ _ r => some r
  | _ => none

open Classical in
/-- The bit `k` of `R` when reader `j` applies its first fetch&xor while `R.seq = s`, in the
run of the labels `γ` from `C` (`none` if it does not). -/
noncomputable def fxBit (s : ℕ) : Cfg m W Au V v₀ →
    List (Label (Proc m W Au) (auditReg m V v₀)) → Option Bool
  | _, [] => none
  | C, ℓ :: γ =>
    if ℓ = .tau (.rd j) ∧ isFX (C.loc (.rd j)) = true ∧ (C.mem .R : RVal m V).seq = s then
      some ((C.mem .R : RVal m V).bits k)
    else match (alg1 rnd v₀).step C ℓ with
      | some D => fxBit s D γ
      | none => none

open Classical in
/-- The next compare&swap of writer `w` on `R`, in the run of the labels `γ` from `C`,
succeeds. -/
noncomputable def casOK (w : W) : Cfg m W Au V v₀ →
    List (Label (Proc m W Au) (auditReg m V v₀)) → Prop
  | _, [] => False
  | C, ℓ :: γ =>
    if ℓ = .tau (.wr w) ∧ (casTarget (C.loc (.wr w))).isSome then
      casTarget (C.loc (.wr w)) = some (C.mem .R)
    else match (alg1 rnd v₀).step C ℓ with
      | some D => casOK w D γ
      | none => False

/-- The pads of the transformed execution. -/
noncomputable def padsB (α : List (Label (Proc m W Au) (auditReg m V v₀))) :
    ℕ → Fin m → Bool := fun s i =>
  if i = k then (fxBit rnd v₀ j k s (alg1 rnd v₀).initCfg α).getD (rnd s k) else rnd s i

/-- The contents of `R` in the transformed execution: bit `k` is never flipped. -/
def prR (r : RVal m V) : RVal m V := ⟨r.seq, r.val, Function.update r.bits k (rnd' r.seq k)⟩

/-- Relation between the local states of a writer (`l` in `α`, `l'` in `α'`). -/
def WRelB (γ : List (Label (Proc m W Au) (auditReg m V v₀))) (C : Cfg m W Au V v₀) (w : W)
    (l l' : Loc m V) : Prop :=
  match l with
  | .wV x sn r => (casOK rnd v₀ w C γ → l' = .wV x sn (prR rnd' k r)) ∧
      (¬ casOK rnd v₀ w C γ → l' = .wR x sn)
  | .wB x sn r todo =>
      (casOK rnd v₀ w C γ → l' = wBnext x sn (prR rnd' k r) (todo.filter (· ≠ k))) ∧
      (¬ casOK rnd v₀ w C γ → l' = .wR x sn)
  | .wCAS x sn r => (casOK rnd v₀ w C γ → l' = .wCAS x sn (prR rnd' k r)) ∧
      (¬ casOK rnd v₀ w C γ → l' = .wR x sn)
  | .wHelp s => l' = .wHelp s ∨ (l' = .wRet ∧ s ≤ (C.mem .SN : ℕ))
  | l => l' = l

/-- Per-process relation. Reader `k` is unconstrained. -/
def PRelB (γ : List (Label (Proc m W Au) (auditReg m V v₀))) (C : Cfg m W Au V v₀) :
    Proc m W Au → Loc m V → Loc m V → Prop
  | .rd i, l, l' => i ≠ k → l' = l
  | .wr w, l, l' => WRelB rnd rnd' v₀ k γ C w l l'
  | .au _, l, l' => skel v₀ l' = skel v₀ l

/-- The simulation relation, indexed by the remaining suffix `γ` of `α`. -/
structure SimB (γ : List (Label (Proc m W Au) (auditReg m V v₀)))
    (C C' : Cfg m W Au V v₀) : Prop where
  pend : ∀ p, p ≠ .rd k → C'.pend p = C.pend p
  R : (C'.mem .R : RVal m V) = prR rnd' k (C.mem .R)
  SN : (C'.mem .SN : ℕ) = C.mem .SN
  loc : ∀ p, PRelB rnd rnd' v₀ k γ C p (C.loc p) (C'.loc p)

end Defs

variable {v₀ : V} {rnd rnd' : ℕ → Fin m → Bool} {j k : Fin m}

section Basic

lemma casOK_cons {C D : Cfg m W Au V v₀} {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    {γ : List (Label (Proc m W Au) (auditReg m V v₀))} {w : W}
    (hs : (alg1 rnd v₀).step C ℓ = some D)
    (h : ¬ (ℓ = .tau (.wr w) ∧ (casTarget (C.loc (.wr w))).isSome)) :
    casOK rnd v₀ w C (ℓ :: γ) ↔ casOK rnd v₀ w D γ := by
  simp only [casOK, h, ite_false, hs]

lemma casOK_cons_cas {C : Cfg m W Au V v₀} {γ : List (Label (Proc m W Au) (auditReg m V v₀))}
    {w : W} {x : V} {sn : ℕ} {r : RVal m V} (hl : C.loc (.wr w) = .wCAS x sn r) :
    casOK rnd v₀ w C (.tau (.wr w) :: γ) ↔ (C.mem .R : RVal m V) = r := by
  simp only [casOK, hl, casTarget, Option.isSome_some, and_self, ite_true, Option.some.injEq]
  exact eq_comm

lemma prR_flip_k (r : RVal m V) : prR rnd' k { r with bits := flip r.bits k } = prR rnd' k r := by
  simp [prR, flip]

lemma prR_flip (r : RVal m V) {i : Fin m} (hik : i ≠ k) :
    prR rnd' k { r with bits := flip r.bits i } = { prR rnd' k r with bits := flip (prR rnd' k r).bits i } := by
  simp only [prR, flip, RVal.mk.injEq, true_and]
  funext x
  by_cases hx : x = i
  · subst hx; simp [Function.update_of_ne hik]
  · by_cases hxk : x = k
    · subst hxk; simp [Function.update_of_ne hx]
    · simp [Function.update_of_ne hx, Function.update_of_ne hxk]

lemma prR_pad (hagree : ∀ s i, i ≠ k → rnd' s i = rnd s i) (sn : ℕ) (x : V) :
    prR rnd' k ⟨sn, x, rnd sn⟩ = ⟨sn, x, rnd' sn⟩ := by
  simp only [prR, RVal.mk.injEq, true_and]
  funext i
  by_cases hi : i = k
  · subst hi; simp
  · simp [Function.update_of_ne hi, hagree sn i hi]

lemma prR_eq_self {r : RVal m V} (h : rnd' r.seq k = r.bits k) : prR rnd' k r = r := by
  rw [prR, h, Function.update_eq_self]

lemma todoOf_prR (hagree : ∀ s i, i ≠ k → rnd' s i = rnd s i) (r : RVal m V) :
    todoOf rnd' (prR rnd' k r) = (todoOf rnd r).filter (· ≠ k) := by
  simp only [todoOf, prR, List.filter_filter]
  congr 1
  funext i
  by_cases hi : i = k
  · subst hi; simp
  · simp [Function.update_of_ne hi, hagree _ i hi, hi]

end Basic

section Frame

variable {C C' D : Cfg m W Au V v₀} {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
  {γ : List (Label (Proc m W Au) (auditReg m V v₀))}

lemma wrel_frame (hs : (alg1 rnd v₀).step C ℓ = some D) {w : W}
    (hnot : ¬ (ℓ = .tau (.wr w) ∧ (casTarget (C.loc (.wr w))).isSome))
    (hsn : (C.mem .SN : ℕ) ≤ D.mem .SN) {l l' : Loc m V}
    (h : WRelB rnd rnd' v₀ k (ℓ :: γ) C w l l') : WRelB rnd rnd' v₀ k γ D w l l' := by
  have hc := casOK_cons (γ := γ) hs hnot
  cases l <;> simp only [WRelB] at h ⊢ <;> try rw [hc] at h
  all_goals try exact h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2.trans hsn⟩

lemma SimB.frame (hI : Inv rnd C) (hS : SimB rnd rnd' v₀ k (ℓ :: γ) C C')
    (hs : (alg1 rnd v₀).step C ℓ = some D) {D' : Cfg m W Au V v₀} (p : Proc m W Au)
    (hp : ℓ.proc = p)
    (hl : ∀ q, q ≠ p → D.loc q = C.loc q) (hl' : ∀ q, q ≠ p → D'.loc q = C'.loc q)
    (hpend : ∀ q, q ≠ .rd k → D'.pend q = D.pend q)
    (hR : (D'.mem .R : RVal m V) = prR rnd' k (D.mem .R)) (hSN : (D'.mem .SN : ℕ) = D.mem .SN)
    (hpp : PRelB rnd rnd' v₀ k γ D p (D.loc p) (D'.loc p)) : SimB rnd rnd' v₀ k γ D D' := by
  refine ⟨hpend, hR, hSN, fun q => ?_⟩
  by_cases hq : q = p
  · subst hq; exact hpp
  rw [hl q hq, hl' q hq]
  have h := hS.loc q
  cases q with
  | rd i => exact h
  | au a => exact h
  | wr w =>
    refine wrel_frame hs (fun h' => hq ?_) (Inv.step hI hs).2.sn h
    rw [← hp, h'.1]; rfl

end Frame

section TauReader

variable {C C' D : Cfg m W Au V v₀} {γ : List (Label (Proc m W Au) (auditReg m V v₀))}

/-- Steps of readers other than `k`. -/
lemma simB_tau_rd (hI : Inv rnd C) (hS : SimB rnd rnd' v₀ k (.tau (.rd i) :: γ) C C')
    (hik : i ≠ k) (hs : (alg1 rnd v₀).step C (.tau (.rd i)) = some D)
    (hfx : i = j → isFX (C.loc (.rd j)) = true →
      rnd' (C.mem .R : RVal m V).seq k = (C.mem .R : RVal m V).bits k) :
    ∃ D', (alg1 rnd' v₀).step C' (.tau (.rd i)) = some D' ∧ SimB rnd rnd' v₀ k γ D D' ∧
      (alg1 rnd' v₀).obsStep C' (.rd j) (.tau (.rd i)) =
        (alg1 rnd v₀).obsStep C (.rd j) (.tau (.rd i)) := by
  obtain ⟨h0, hpend, o_i, o, kk, hact, hmem, hloc⟩ := Impl.step_tau hs
  have h0' : C'.pend (.rd i) ≠ none := by rw [hS.pend _ (by simpa using hik)]; exact h0
  have hl' : C'.loc (.rd i) = C.loc (.rd i) := hS.loc (.rd i) hik
  have hR := hS.R
  have hSN := hS.SN
  have fr := fun {D'} => hS.frame (D' := D') hI hs (.rd i) rfl
  cases hl : C.loc (.rd i) <;> rw [hl] at hl' <;>
    simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
    simp only [Action.access.injEq] at hact <;>
    obtain ⟨rfl, ho, hk⟩ := hact <;>
    obtain rfl := eq_of_heq ho <;>
    obtain rfl := eq_of_heq hk
  case rSN prev =>
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_, ?_⟩
    · refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
        (by simp [hmem, hSN]) (fun _ => ?_)
      simp only [hloc, Function.update_self]
      rw [hSN]
    · by_cases hij : i = j
      · subst hij; simp [Impl.obsStep, hl, hl', alg1, readerAct, hSN]
      · exact obs_other (p := .rd i) (by simpa using hij) rfl rfl
  case rFX prev y =>
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_, ?_⟩
    · refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by rw [hpend]; exact hS.pend q hq) ?_
        (by simp [hmem, hSN]) (fun _ => ?_)
      · simp only [hmem, Function.update_self, rObj, hR]
        exact (prR_flip _ hik).symm
      · simp [hloc, hR, prR]
    · by_cases hij : i = j
      · subst hij
        have hv := prR_eq_self (hfx rfl (by simp [hl, isFX]))
        simp [Impl.obsStep, hl, hl', alg1, readerAct, hR, hv]
      · exact obs_other (p := .rd i) (by simpa using hij) rfl rfl
  case rCAS prev sn val =>
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_, ?_⟩
    · refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
        (by simp [hmem, hSN]) (fun _ => ?_)
      simp [hloc]
    · by_cases hij : i = j
      · subst hij; simp [Impl.obsStep, hl, hl', alg1, readerAct, hSN]
      · exact obs_other (p := .rd i) (by simpa using hij) rfl rfl

end TauReader

section TauAuditor

variable {C C' D : Cfg m W Au V v₀} {γ : List (Label (Proc m W Au) (auditReg m V v₀))}

/-- Auditor steps. -/
lemma simB_tau_au (hI : Inv rnd C) (hS : SimB rnd rnd' v₀ k (.tau (.au a) :: γ) C C')
    (hs : (alg1 rnd v₀).step C (.tau (.au a)) = some D) :
    ∃ D', (alg1 rnd' v₀).step C' (.tau (.au a)) = some D' ∧ SimB rnd rnd' v₀ k γ D D' := by
  obtain ⟨h0, hpend, o_i, o, kk, hact, hmem, hloc⟩ := Impl.step_tau hs
  have h0' : C'.pend (.au a) ≠ none := by rw [hS.pend _ (by simp)]; exact h0
  have hsk : skel v₀ (C'.loc (.au a)) = skel v₀ (C.loc (.au a)) := hS.loc (.au a)
  have hR := hS.R
  have hSN := hS.SN
  have fr := fun {D'} => hS.frame (D' := D') hI hs (.au a) rfl
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
    refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq])
      (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    simp only [PRelB, hloc, Function.update_self]
    rw [hR]; exact skel_aNext v₀ (r := C.mem Obj.R) (r' := prR rnd' k (C.mem Obj.R)) rfl _
  case aV.aV A r s A' r' s' =>
    simp only [Loc.aV.injEq, true_and, skR, RVal.mk.injEq, and_true] at hsk
    obtain ⟨hr, rfl⟩ := hsk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq])
      (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    simp only [PRelB, hloc, Function.update_self]
    exact skel_aVnext v₀ hr _ _ _
  case aB.aB A r s val i A' r' s' val' i' =>
    simp only [Loc.aB.injEq, true_and, skR, RVal.mk.injEq, and_true] at hsk
    obtain ⟨hr, rfl, rfl⟩ := hsk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq])
      (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    simp only [PRelB, hloc, Function.update_self]
    exact skel_aBnext v₀ hr _ _ _ _
  case aCAS.aCAS A r A' r' =>
    simp only [Loc.aCAS.injEq, true_and, skR, RVal.mk.injEq, and_true] at hsk
    refine ⟨_, Impl.step_tau_eq_some h0' (by rw [hl']; rfl), ?_⟩
    refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq])
      (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
      (by simp [hmem, hSN, hsk]) ?_
    simp [PRelB, hloc, skel, hsk]

end TauAuditor

section TauWriter

lemma runFrom_tau {rnd' : ℕ → Fin m → Bool} {C' : Cfg m W Au V v₀} {p : Proc m W Au}
    (h0 : C'.pend p ≠ none) {i : Obj m} {o : (BO m V v₀ i).Op} {kk : (BO m V v₀ i).Resp → Loc m V}
    (hact : (alg1 rnd' v₀).act p (C'.loc p) = .access i o kk) :
    (alg1 rnd' v₀).runFrom C' [.tau p] =
      some { C' with mem := Function.update C'.mem i ((BO m V v₀ i).δ (C'.mem i) o).1,
                     loc := Function.update C'.loc p (kk ((BO m V v₀ i).δ (C'.mem i) o).2) } := by
  rw [Impl.runFrom_singleton]; exact Impl.step_tau_eq_some h0 hact

variable {C C' D : Cfg m W Au V v₀} {γ : List (Label (Proc m W Au) (auditReg m V v₀))}

lemma wrel_wBnext_ok {w : W} (hc : casOK rnd v₀ w D γ) (x : V) (sn : ℕ) (r : RVal m V)
    (t : List (Fin m)) :
    WRelB rnd rnd' v₀ k γ D w (wBnext x sn r t) (wBnext x sn (prR rnd' k r) (t.filter (· ≠ k))) := by
  cases t <;> simp [wBnext, WRelB, hc]

lemma wrel_wBnext_bad {w : W} (hc : ¬ casOK rnd v₀ w D γ) (x : V) (sn : ℕ) (r : RVal m V)
    (t : List (Fin m)) : WRelB rnd rnd' v₀ k γ D w (wBnext x sn r t) (.wR x sn) := by
  cases t <;> simp [wBnext, WRelB, hc]

/-- Writer steps: the writer's step is either replayed or dropped. -/
lemma simB_tau_wr (hagree : ∀ s i, i ≠ k → rnd' s i = rnd s i) (hI : Inv rnd C) {w : W}
    (hS : SimB rnd rnd' v₀ k (.tau (.wr w) :: γ) C C')
    (hs : (alg1 rnd v₀).step C (.tau (.wr w)) = some D) :
    ∃ ℓs D', (alg1 rnd' v₀).runFrom C' ℓs = some D' ∧ SimB rnd rnd' v₀ k γ D D' ∧
      (ℓs = [] ∨ ℓs = [.tau (.wr w)]) := by
  obtain ⟨h0, hpend, o_i, o, kk, hact, hmem, hloc⟩ := Impl.step_tau hs
  have h0' : C'.pend (.wr w) ≠ none := by rw [hS.pend _ (by simp)]; exact h0
  have hP : WRelB rnd rnd' v₀ k (.tau (.wr w) :: γ) C w (C.loc (.wr w)) (C'.loc (.wr w)) :=
    hS.loc (.wr w)
  have hR := hS.R
  have hSN := hS.SN
  have fr := fun {D'} => hS.frame (D' := D') hI hs (.wr w) rfl
  have hr := hI.wr w
  unfold WInv at hr
  have hc : ∀ x sn r t, C.loc (.wr w) = .wV x sn r ∨ C.loc (.wr w) = .wB x sn r t →
      (casOK rnd v₀ w C (.tau (.wr w) :: γ) ↔ casOK rnd v₀ w D γ) := by
    intro x sn r t h
    refine casOK_cons hs (fun h' => ?_)
    rcases h with h | h <;> simp [h, casTarget] at h'
  cases hl : C.loc (.wr w) <;> rw [hl] at hP hr <;>
    simp only [alg1, writerAct, hl, reduceCtorEq] at hact
  case wSN x =>
    simp only [WRelB] at hP
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    refine ⟨[.tau (.wr w)], _, runFrom_tau h0'
      (by rw [hP]; rfl), ?_, Or.inr rfl⟩
    refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq])
      (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
      (by simp [hmem, hSN]) ?_
    simp only [PRelB, WRelB, hloc, Function.update_self]
    rw [hSN]
  case wR x sn =>
    simp only [WRelB] at hP
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hDR : (D.mem .R : RVal m V) = C.mem .R := by simp [hmem]
    by_cases hb : sn ≤ (C.mem .R : RVal m V).seq
    · refine ⟨[.tau (.wr w)], _, runFrom_tau h0'
        (by rw [hP]; rfl), ?_, Or.inr rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
        (by simp [hmem, hSN]) ?_
      have hb' : sn ≤ (prR rnd' k (C.mem .R : RVal m V)).seq := hb
      simp [PRelB, WRelB, hloc, hR, hb, hb']
    · by_cases hcas : casOK rnd v₀ w D γ
      · refine ⟨[.tau (.wr w)], _, runFrom_tau h0'
          (by rw [hP]; rfl), ?_, Or.inr rfl⟩
        refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
          (fun q hq => by simp [Function.update_of_ne hq])
          (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
          (by simp [hmem, hSN]) ?_
        have hb' : ¬ sn ≤ (prR rnd' k (C.mem .R : RVal m V)).seq := hb
        simp [PRelB, WRelB, hloc, hR, hb, hb', hcas]
      · refine ⟨[], C', rfl, ?_, Or.inl rfl⟩
        refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun q hq => rfl)
          (fun q hq => by rw [hpend]; exact hS.pend q hq) (by rw [hDR]; exact hR)
          (by simp [hmem, hSN]) ?_
        simp [PRelB, WRelB, hloc, hb, hcas, hP]
  case wV x sn r =>
    have hc' := hc x sn r [] (Or.inl hl)
    simp only [WRelB, hc'] at hP
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hDR : (D.mem .R : RVal m V) = C.mem .R := by simp [hmem]
    have hDS : (D.mem .SN : ℕ) = C.mem .SN := by simp [hmem]
    by_cases hcas : casOK rnd v₀ w D γ
    · refine ⟨[.tau (.wr w)], _, runFrom_tau h0'
        (by rw [hP.1 hcas]; rfl), ?_, Or.inr rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
        (by simp [hmem, hSN]) ?_
      simp only [PRelB, hloc, Function.update_self]
      rw [todoOf_prR hagree]
      exact wrel_wBnext_ok hcas _ _ _ _
    · refine ⟨[], C', rfl, ?_, Or.inl rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun q hq => rfl)
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by rw [hDR]; exact hR)
        (by rw [hDS]; exact hSN) ?_
      simp only [PRelB, hloc, Function.update_self]
      rw [hP.2 hcas]
      exact wrel_wBnext_bad hcas _ _ _ _
  case wB x sn r todo =>
    cases todo with
    | nil => simp at hact
    | cons i rest =>
    have hc' := hc x sn r (i :: rest) (Or.inr hl)
    simp only [WRelB, hc'] at hP
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    have hDR : (D.mem .R : RVal m V) = C.mem .R := by simp [hmem]
    have hDS : (D.mem .SN : ℕ) = C.mem .SN := by simp [hmem]
    by_cases hcas : casOK rnd v₀ w D γ
    · have hP1 := hP.1 hcas
      by_cases hik : i = k
      · subst hik
        refine ⟨[], C', rfl, ?_, Or.inl rfl⟩
        refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun q hq => rfl)
          (fun q hq => by rw [hpend]; exact hS.pend q hq) (by rw [hDR]; exact hR)
          (by rw [hDS]; exact hSN) ?_
        simp only [PRelB, hloc, Function.update_self]
        rw [hP1]
        simpa using wrel_wBnext_ok (rnd' := rnd') (k := i) hcas x sn r rest
      · have hP2 : C'.loc (.wr w) = .wB x sn (prR rnd' k r) (i :: rest.filter (· ≠ k)) := by
          rw [hP1]; simp [wBnext, hik]
        refine ⟨[.tau (.wr w)], _, runFrom_tau h0'
          (by rw [hP2]; rfl), ?_, Or.inr rfl⟩
        refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
          (fun q hq => by simp [Function.update_of_ne hq])
          (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
          (by simp [hmem, hSN]) ?_
        simp only [PRelB, hloc, Function.update_self]
        exact wrel_wBnext_ok hcas _ _ _ _
    · refine ⟨[], C', rfl, ?_, Or.inl rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun q hq => rfl)
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by rw [hDR]; exact hR)
        (by rw [hDS]; exact hSN) ?_
      simp only [PRelB, hloc, Function.update_self]
      rw [hP.2 hcas]
      exact wrel_wBnext_bad hcas _ _ _ _
  case wCAS x sn r =>
    simp only [WRelB, casOK_cons_cas hl] at hP
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨-, ⟨hw1, -⟩, -⟩ := hr
    by_cases heq : (C.mem .R : RVal m V) = r
    · have hP1 := hP.1 heq
      have heq' : (C'.mem .R : RVal m V) = prR rnd' k r := by rw [hR, heq]
      refine ⟨[.tau (.wr w)], _, runFrom_tau h0'
        (by rw [hP1]; rfl), ?_, Or.inr rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by rw [hpend]; exact hS.pend q hq)
        (by simp [hmem, heq, heq', prR_pad hagree]) (by simp [hmem, hSN]) ?_
      simp [PRelB, WRelB, hloc, heq, heq']
    · have hP2 := hP.2 heq
      have hDR : (D.mem .R : RVal m V) = C.mem .R := by simp [hmem, heq]
      have hDS : (D.mem .SN : ℕ) = C.mem .SN := by simp [hmem]
      refine ⟨[], C', rfl, ?_, Or.inl rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun q hq => rfl)
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by rw [hDR]; exact hR)
        (by rw [hDS]; exact hSN) ?_
      simp [PRelB, WRelB, hloc, heq, hP2]
  case wHelp s =>
    simp only [WRelB] at hP
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    obtain rfl := eq_of_heq ho
    obtain rfl := eq_of_heq hk
    obtain ⟨-, hs1, -⟩ := hr
    rcases hP with hP | ⟨hP, hle⟩
    · refine ⟨[.tau (.wr w)], _, runFrom_tau h0'
        (by rw [hP]; rfl), ?_, Or.inr rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by simp [hmem, hR])
        (by simp [hmem, hSN]) ?_
      simp [PRelB, WRelB, hloc]
    · have hle' : s ≤ (C.mem .SN : ℕ) := hle
      have hne : (s - 1 : ℕ) ≠ C.mem .SN := by omega
      have hDR : (D.mem .R : RVal m V) = C.mem .R := by simp [hmem]
      have hDS : (D.mem .SN : ℕ) = C.mem .SN := by simp [hmem, casObject, hne, Ne.symm hne]
      refine ⟨[], C', rfl, ?_, Or.inl rfl⟩
      refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq]) (fun q hq => rfl)
        (fun q hq => by rw [hpend]; exact hS.pend q hq) (by rw [hDR]; exact hR)
        (by rw [hDS]; exact hSN) ?_
      simp [PRelB, WRelB, hloc, hP]

end TauWriter

section TauK

variable {C C' D : Cfg m W Au V v₀} {γ : List (Label (Proc m W Au) (auditReg m V v₀))}

/-- Steps of reader `k` are dropped; a compare&swap of `k` that moves `SN` is replaced by the
line-15 step of the writer poised for that sequence number. -/
lemma simB_tau_rdk (hI : Inv rnd C) (hD : DInv C)
    (hS : SimB rnd rnd' v₀ k (.tau (.rd k) :: γ) C C')
    (hs : (alg1 rnd v₀).step C (.tau (.rd k)) = some D) :
    ∃ ℓs D', (alg1 rnd' v₀).runFrom C' ℓs = some D' ∧ SimB rnd rnd' v₀ k γ D D' ∧
      (ℓs = [] ∨ ∃ w, ℓs = [.tau (.wr w)]) := by
  obtain ⟨h0, hpend, o_i, o, kk, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hR := hS.R
  have hSN := hS.SN
  have fr := fun {D'} => hS.frame (D' := D') hI hs (.rd k) rfl
  have hr := (hI.rd k).2
  have hpk : ∀ q, q ≠ Proc.rd k → C'.pend q = D.pend q := fun q hq => by
    rw [hpend]; exact hS.pend q hq
  cases hl : C.loc (.rd k) <;> rw [hl] at hr <;>
    simp only [alg1, readerAct, hl, reduceCtorEq] at hact <;>
    simp only [Action.access.injEq] at hact <;>
    obtain ⟨rfl, ho, hk⟩ := hact <;>
    obtain rfl := eq_of_heq ho <;>
    obtain rfl := eq_of_heq hk
  case rSN prev =>
    refine ⟨[], C', rfl, fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => rfl) hpk (by simp [hmem, hR]) (by simp [hmem, hSN]) (fun h => absurd rfl h),
      Or.inl rfl⟩
  case rFX prev y =>
    refine ⟨[], C', rfl, fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => rfl) hpk ?_ (by simp [hmem, hSN]) (fun h => absurd rfl h), Or.inl rfl⟩
    simp only [hmem, Function.update_self, rObj, hR]
    exact (prR_flip_k _).symm
  case rCAS prev sn val =>
    obtain ⟨-, -, -, hsn1, hsn2, -, -⟩ := hr
    have hle := hI.seq_le
    have hDS : snOf D = if snOf C = sn - 1 then sn else snOf C := by
      simp [snOf, hmem, casObject]; split_ifs <;> simp_all
    have hDR : (D.mem .R : RVal m V) = C.mem .R := by simp [hmem]
    have hSN' : snOf C' = snOf C := hSN
    by_cases hch : sn = snOf C + 1
    · -- the step moves `SN`: the writer poised at line 15 for `sn` takes its step instead
      have hseq : (rOf C).seq = snOf C + 1 := by omega
      obtain ⟨w, hw⟩ := hD hseq
      rw [show (rOf C).seq = sn by omega] at hw
      have hPw : WRelB rnd rnd' v₀ k (.tau (.rd k) :: γ) C w (C.loc (.wr w)) (C'.loc (.wr w)) :=
        hS.loc (.wr w)
      rw [hw] at hPw
      simp only [WRelB] at hPw
      have hw' : C'.loc (.wr w) = .wHelp sn := by
        rcases hPw with h | ⟨-, h⟩
        · exact h
        · have h' : sn ≤ snOf C := h
          omega
      have hwp : C'.pend (.wr w) ≠ none := by
        rw [hS.pend _ (by simp)]
        have := hI.wr w; unfold WInv at this; rw [hw] at this
        obtain ⟨⟨x, hx⟩, -⟩ := this; rw [hx]; simp
      have hc1 : snOf C' = sn - 1 := by omega
      refine ⟨[.tau (.wr w)], _, runFrom_tau hwp (by rw [hw']; rfl), ?_, Or.inr ⟨w, rfl⟩⟩
      have hE := (Inv.step hI hs).2
      have hDS2 : snOf D = sn := by rw [hDS]; simp [show snOf C = sn - 1 by omega]
      refine ⟨fun q hq => hpk q hq, by simp [hDR, hR], ?_, fun q => ?_⟩
      · have h1 : (C'.mem .SN : ℕ) = sn - 1 := hc1
        have h2 : (D.mem .SN : ℕ) = sn := hDS2
        simp [casObject, h1, h2]
      · by_cases hqw : q = .wr w
        · subst hqw
          have hDw : D.loc (.wr w) = .wHelp sn := by simp [hloc, hw]
          simp only [PRelB, hDw, WRelB, Function.update_self]
          right; refine ⟨trivial, ?_⟩
          have : sn ≤ snOf D := by omega
          exact this
        · by_cases hqk : q = .rd k
          · subst hqk; exact fun h => absurd rfl h
          simp only [Function.update_of_ne hqw]
          rw [show D.loc q = C.loc q by simp [hloc, Function.update_of_ne hqk]]
          have h := hS.loc q
          cases q with
          | rd i => exact h
          | au a => exact h
          | wr w₂ => exact wrel_frame hs (fun h' => by cases h'.1) hE.sn h
    · have hDS' : snOf D = snOf C := by rw [hDS]; split_ifs <;> omega
      refine ⟨[], C', rfl, fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
        (fun q hq => rfl) hpk (by rw [hDR]; exact hR) (hSN'.trans hDS'.symm)
        (fun h => absurd rfl h), Or.inl rfl⟩

end TauK

section InvRet

variable {C C' D : Cfg m W Au V v₀} {γ : List (Label (Proc m W Au) (auditReg m V v₀))}

/-- Invocations: those of `k` are dropped, the others replayed. -/
lemma simB_inv (hI : Inv rnd C) {p : Proc m W Au} {o : AOp m V}
    (hS : SimB rnd rnd' v₀ k (.inv p o :: γ) C C')
    (hs : (alg1 rnd v₀).step C (.inv p o) = some D) :
    (p = .rd k ∧ SimB rnd rnd' v₀ k γ D C') ∨
    (p ≠ .rd k ∧ ∃ D', (alg1 rnd' v₀).step C' (.inv p o) = some D' ∧
      SimB rnd rnd' v₀ k γ D D') := by
  obtain ⟨h0, hal, hpend, hloc, hmem⟩ := Impl.step_inv hs
  have hR := hS.R
  have hSN := hS.SN
  have fr := fun {D'} => hS.frame (D' := D') hI hs p rfl
  by_cases hpk : p = .rd k
  · subst hpk
    refine Or.inl ⟨rfl, fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => rfl) (fun q hq => ?_) (by simp [hmem, hR]) (by simp [hmem, hSN])
      (fun h => absurd rfl h)⟩
    rw [hpend, Function.update_of_ne hq]; exact hS.pend q hq
  refine Or.inr ⟨hpk, ?_⟩
  have h0' : C'.pend p = none := by rw [hS.pend p hpk, h0]
  have hal' : (alg1 (W := W) (Au := Au) rnd' v₀).allowed p o := hal
  refine ⟨_, Impl.step_inv_eq_some h0' hal', ?_⟩
  refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
    (fun q hq => by simp [Function.update_of_ne hq]) (fun q hq => ?_) (by simp [hmem, hR])
    (by simp [hmem, hSN]) ?_
  · by_cases hqp : q = p
    · subst hqp; simp [hpend]
    · simp [hpend, Function.update_of_ne hqp]; exact hS.pend q hq
  have hP := hS.loc p
  cases p with
  | rd i =>
    have hik : i ≠ k := fun h => hpk (by rw [h])
    have hl' : C'.loc (.rd i) = C.loc (.rd i) := hP hik
    simp [PRelB, hloc, hl', alg1]
  | wr w =>
    have hl := (hI.wr w).idle h0
    simp only [PRelB, hl, WRelB] at hP
    simp [PRelB, WRelB, hloc, hl, hP, alg1, invoke]
    cases o <;> simp [invoke, WRelB]
  | au a =>
    cases o <;> simp only [alg1, allowed, reduceCtorEq] at hal
    obtain ⟨A, lsa, hl, -⟩ := (hI.au a).idle h0
    simp only [PRelB, hl] at hP
    cases hl' : C'.loc (.au a) <;> simp only [hl', skel, reduceCtorEq] at hP
    simp only [Loc.aIdle.injEq, true_and] at hP
    simp [PRelB, hloc, hl, hl', hP, alg1, invoke, skel]

/-- Responses: those of `k` are dropped, the others replayed (with the response computed in the
new execution; for readers other than `k` it is the same). -/
lemma simB_ret (hI : Inv rnd C) {p : Proc m W Au} {r : AResp m V}
    (hS : SimB rnd rnd' v₀ k (.ret p r :: γ) C C')
    (hs : (alg1 rnd v₀).step C (.ret p r) = some D) :
    (p = .rd k ∧ SimB rnd rnd' v₀ k γ D C') ∨
    (p ≠ .rd k ∧ ∃ r' D', (alg1 rnd' v₀).step C' (.ret p r') = some D' ∧
      SimB rnd rnd' v₀ k γ D D' ∧ ∀ i, p = .rd i → r' = r) := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret hs
  have hR := hS.R
  have hSN := hS.SN
  have fr := fun {D'} => hS.frame (D' := D') hI hs p rfl
  by_cases hpk : p = .rd k
  · subst hpk
    refine Or.inl ⟨rfl, fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => rfl) (fun q hq => ?_) (by simp [hmem, hR]) (by simp [hmem, hSN])
      (fun h => absurd rfl h)⟩
    rw [hpend, Function.update_of_ne hq]; exact hS.pend q hq
  refine Or.inr ⟨hpk, ?_⟩
  have h0' : C'.pend p ≠ none := by rw [hS.pend p hpk]; exact h0
  have fr' : ∀ l', PRelB rnd rnd' v₀ k γ D p l l' →
      SimB rnd rnd' v₀ k γ D ⟨Function.update C'.loc p l', Function.update C'.pend p none,
        C'.mem⟩ := by
    intro l' hl'
    refine fr (fun q hq => by simp [hloc, Function.update_of_ne hq])
      (fun q hq => by simp [Function.update_of_ne hq]) (fun q hq => ?_) (by simp [hmem, hR])
      (by simp [hmem, hSN]) (by simpa [hloc] using hl')
    by_cases hqp : q = p
    · subst hqp; simp [hpend]
    · simp [hpend, Function.update_of_ne hqp]; exact hS.pend q hq
  have hP := hS.loc p
  cases p with
  | rd i =>
    have hik : i ≠ k := fun h => hpk (by rw [h])
    have hl' : C'.loc (.rd i) = C.loc (.rd i) := hP hik
    refine ⟨r, _, Impl.step_ret_eq_some h0' (by rw [hl']; exact hact),
      fr' _ (fun _ => rfl), fun _ _ => rfl⟩
  | wr w =>
    have hr := hI.wr w
    unfold WInv at hr
    cases hl : C.loc (.wr w) <;> rw [hl] at hr hP <;>
      simp only [alg1, writerAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
      simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
    · exact absurd hr h0
    · rename_i x sn rr todo
      cases todo with
      | nil => exact absurd rfl hr.2.2.2.1
      | cons j rest => simp at hact
    · obtain ⟨rfl, rfl⟩ := hact
      simp only [PRelB, WRelB] at hP
      refine ⟨_, _, Impl.step_ret_eq_some h0' (by rw [hP]; rfl),
        fr' _ (by simp [PRelB, WRelB]), fun _ h => by cases h⟩
  | au a =>
    have hr := hI.au a
    unfold AInv at hr
    simp only [PRelB] at hP
    cases hl : C.loc (.au a) <;> rw [hl] at hr hP <;>
      simp only [alg1, auditorAct, hl, Action.ret.injEq, reduceCtorEq] at hact <;>
      simp only [false_and, and_false, IsEmpty.forall_iff, not_true_eq_false] at hr
    · exact absurd hr.1 h0
    · rename_i A lsa
      obtain ⟨rfl, rfl⟩ := hact
      cases hl' : C'.loc (.au a) <;> simp only [hl', skel, reduceCtorEq] at hP
      simp only [Loc.aRet.injEq, true_and] at hP
      refine ⟨_, _, Impl.step_ret_eq_some h0' (by rw [hl']; rfl),
        fr' _ (by simp [PRelB, skel, hP]), fun _ h => by cases h⟩

end InvRet

section Step

variable {C C' D : Cfg m W Au V v₀} {γ : List (Label (Proc m W Au) (auditReg m V v₀))}

lemma obsFrom_single {C' D' : Cfg m W Au V v₀} {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (h : (alg1 rnd' v₀).step C' ℓ = some D') (q : Proc m W Au) :
    (alg1 rnd' v₀).obsFrom q C' [ℓ] = ((alg1 rnd' v₀).obsStep C' q ℓ).toList := by
  rw [Impl.obsFrom_cons_of_step _ q h]; simp

lemma obsFrom_other {C' : Cfg m W Au V v₀} {ℓs : List (Label (Proc m W Au) (auditReg m V v₀))}
    {q : Proc m W Au} (h : ∀ ℓ ∈ ℓs, ℓ.proc ≠ q) : (alg1 rnd' v₀).obsFrom q C' ℓs = [] := by
  induction ℓs generalizing C' with
  | nil => rfl
  | cons ℓ ℓs ih =>
    simp only [Impl.obsFrom, Impl.obsStep_eq_none_of_proc_ne _ _ (h ℓ (by simp)),
      Option.toList_none, List.nil_append]
    split
    · exact ih (fun ℓ' hℓ' => h ℓ' (by simp [hℓ']))
    · rfl

/-- One step of the simulation of Lemma 7. -/
lemma simB_step (hjk : j ≠ k) (hagree : ∀ s i, i ≠ k → rnd' s i = rnd s i) (hI : Inv rnd C)
    (hD : DInv C) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hS : SimB rnd rnd' v₀ k (ℓ :: γ) C C') (hs : (alg1 rnd v₀).step C ℓ = some D)
    (hfx : ℓ = .tau (.rd j) → isFX (C.loc (.rd j)) = true →
      rnd' (C.mem .R : RVal m V).seq k = (C.mem .R : RVal m V).bits k) :
    ∃ ℓs D', (alg1 rnd' v₀).runFrom C' ℓs = some D' ∧ SimB rnd rnd' v₀ k γ D D' ∧
      (alg1 rnd' v₀).obsFrom (.rd j) C' ℓs = ((alg1 rnd v₀).obsStep C (.rd j) ℓ).toList ∧
      ∀ ℓ' ∈ ℓs, ℓ'.proc ≠ .rd k := by
  have hkj : (Proc.rd k : Proc m W Au) ≠ .rd j := by simpa using hjk.symm
  cases ℓ with
  | inv p o =>
    rcases simB_inv hI hS hs with ⟨rfl, h⟩ | ⟨hpk, D', h1, h2⟩
    · refine ⟨[], C', rfl, h, ?_, by simp⟩
      rw [Impl.obsStep_eq_none_of_proc_ne _ _ (by simpa [Label.proc] using hkj)]; rfl
    · refine ⟨[.inv p o], D', by rw [Impl.runFrom_singleton]; exact h1, h2, ?_, by simpa [Label.proc] using hpk⟩
      rw [obsFrom_single h1]; simp [Impl.obsStep]
  | ret p r =>
    rcases simB_ret hI hS hs with ⟨rfl, h⟩ | ⟨hpk, r', D', h1, h2, h3⟩
    · refine ⟨[], C', rfl, h, ?_, by simp⟩
      rw [Impl.obsStep_eq_none_of_proc_ne _ _ (by simpa [Label.proc] using hkj)]; rfl
    · refine ⟨[.ret p r'], D', by rw [Impl.runFrom_singleton]; exact h1, h2, ?_, by simpa [Label.proc] using hpk⟩
      rw [obsFrom_single h1]
      by_cases hpj : p = .rd j
      · subst hpj; rw [h3 j rfl]; simp [Impl.obsStep]
      · simp [Impl.obsStep, hpj]
  | tau p =>
    cases p with
    | rd i =>
      by_cases hik : i = k
      · subst hik
        obtain ⟨ℓs, D', h1, h2, h3⟩ := simB_tau_rdk hI hD hS hs
        have hother : ∀ ℓ' ∈ ℓs, ℓ'.proc ≠ .rd i := by
          rcases h3 with rfl | ⟨w, rfl⟩ <;> simp [Label.proc]
        refine ⟨ℓs, D', h1, h2, ?_, hother⟩
        rw [Impl.obsStep_eq_none_of_proc_ne _ _ (by simpa [Label.proc] using hkj), obsFrom_other]
        · rfl
        · rcases h3 with rfl | ⟨w, rfl⟩ <;> simp [Label.proc]
      · obtain ⟨D', h1, h2, h3⟩ := simB_tau_rd hI hS hik hs (fun h => hfx (by rw [h]))
        refine ⟨[.tau (.rd i)], D', by rw [Impl.runFrom_singleton]; exact h1, h2, ?_,
          by simpa [Label.proc] using hik⟩
        rw [obsFrom_single h1, h3]
    | wr w =>
      obtain ⟨ℓs, D', h1, h2, h3⟩ := simB_tau_wr hagree hI hS hs
      refine ⟨ℓs, D', h1, h2, ?_, by rcases h3 with rfl | rfl <;> simp [Label.proc]⟩
      rw [Impl.obsStep_eq_none_of_proc_ne _ _ (by simp [Label.proc]), obsFrom_other]
      · rfl
      · rcases h3 with rfl | rfl <;> simp [Label.proc]
    | au a =>
      obtain ⟨D', h1, h2⟩ := simB_tau_au hI hS hs
      refine ⟨[.tau (.au a)], D', by rw [Impl.runFrom_singleton]; exact h1, h2, ?_, by simp [Label.proc]⟩
      rw [obsFrom_single h1, obs_other (p := .au a) (ℓ := .tau (.au a)) (ℓ' := .tau (.au a))
        (by simp) rfl rfl]

end Step

section Pads

variable {C₀ C D : Cfg m W Au V v₀}

/-- `Fetched` only grows along runs. -/
lemma fetched_mono (hI : Inv rnd C₀) {β : List (Label (Proc m W Au) (auditReg m V v₀))}
    (hβ : (alg1 rnd v₀).runFrom C₀ β = some C) {i : Fin m} {t : ℕ}
    (hf : Fetched rnd C₀ i t) : Fetched rnd C i t := by
  induction β generalizing C₀ with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at hβ; subst hβ; exact hf
  | cons ℓ β ih =>
    simp only [Impl.runFrom_cons] at hβ
    cases hs : (alg1 rnd v₀).step C₀ ℓ with
    | none => simp [hs] at hβ
    | some D =>
      rw [hs, Option.bind_some] at hβ
      obtain ⟨hI', E⟩ := Inv.step hI hs
      exact ih hI' hβ (E.fet _ _ hf)

/-- A reader poised to apply fetch&xor has not yet fetched at the current sequence number
(this gives Lemma 17: at most one fetch&xor per reader and sequence number). -/
lemma not_fetched_of_rFX (hI : Inv rnd C) {i : Fin m} {prev : Option (ℕ × V)} {y : ℕ}
    (hl : C.loc (.rd i) = .rFX prev y) : ¬ Fetched rnd C i (rOf C).seq := by
  obtain ⟨hb, hr⟩ := hI.rd i
  rw [hl] at hr hb
  obtain ⟨-, -, hp3, hp4⟩ := hr
  have hle := hI.sn_le
  have hbj : (rOf C).bits i = rnd (rOf C).seq i := by
    by_contra hc
    obtain ⟨⟨x, v⟩, hx, hxe⟩ := Option.map_eq_some_iff.1 (hb.1 hc)
    have := hp3 x v hx
    simp at hxe; omega
  rintro (⟨h, -⟩ | ⟨-, h⟩)
  · omega
  · exact h hbj

lemma fetched_after_fx (hI : Inv rnd C) {prev : Option (ℕ × V)} {y : ℕ}
    (hl : C.loc (.rd j) = .rFX prev y) (hs : (alg1 rnd v₀).step C (.tau (.rd j)) = some D) :
    Fetched rnd D j (rOf C).seq := by
  obtain ⟨-, -, i, o, kk, hact, hmem, hloc⟩ := Impl.step_tau hs
  simp only [alg1, readerAct, hl, Action.access.injEq] at hact
  obtain ⟨rfl, ho, hk⟩ := hact
  obtain rfl := eq_of_heq ho
  obtain rfl := eq_of_heq hk
  have hlj : D.loc (.rd j) = .rCAS prev (C.mem .R : RVal m V).seq (C.mem .R : RVal m V).val := by
    simp [hloc]
  have hr := ((Inv.step hI hs).1.rd j).2
  rw [hlj] at hr
  exact hr.2.2.2.2.2.2

lemma fxBit_append {β δ : List (Label (Proc m W Au) (auditReg m V v₀))} (s : ℕ)
    (hβ : (alg1 rnd v₀).runFrom C₀ β = some C) :
    fxBit rnd v₀ j k s C₀ (β ++ δ) = (fxBit rnd v₀ j k s C₀ β).or (fxBit rnd v₀ j k s C δ) := by
  induction β generalizing C₀ with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at hβ; subst hβ; simp [fxBit]
  | cons ℓ β ih =>
    simp only [Impl.runFrom_cons] at hβ
    cases hs : (alg1 rnd v₀).step C₀ ℓ with
    | none => simp [hs] at hβ
    | some D =>
      rw [hs, Option.bind_some] at hβ
      by_cases hc : ℓ = .tau (.rd j) ∧ isFX (C₀.loc (.rd j)) = true ∧
          (C₀.mem .R : RVal m V).seq = s
      · simp [fxBit, hc]
      · simp only [List.cons_append, fxBit, hc, ite_false, hs]
        exact ih hβ

lemma fxBit_fetched (hI : Inv rnd C₀) {β : List (Label (Proc m W Au) (auditReg m V v₀))}
    {s : ℕ} {b : Bool} (hb : fxBit rnd v₀ j k s C₀ β = some b)
    (hβ : (alg1 rnd v₀).runFrom C₀ β = some C) : Fetched rnd C j s := by
  induction β generalizing C₀ with
  | nil => simp [fxBit] at hb
  | cons ℓ β ih =>
    simp only [Impl.runFrom_cons] at hβ
    cases hs : (alg1 rnd v₀).step C₀ ℓ with
    | none => simp [hs] at hβ
    | some D =>
      rw [hs, Option.bind_some] at hβ
      obtain ⟨hI', E⟩ := Inv.step hI hs
      by_cases hc : ℓ = .tau (.rd j) ∧ isFX (C₀.loc (.rd j)) = true ∧
          (C₀.mem .R : RVal m V).seq = s
      · obtain ⟨rfl, hfx, rfl⟩ := hc
        cases hl : C₀.loc (.rd j) <;> simp [hl, isFX] at hfx
        exact fetched_mono hI' hβ (fetched_after_fx hI hl hs)
      · simp only [fxBit, hc, ite_false, hs] at hb
        exact ih hI' hb hβ

lemma padsB_agree (α : List (Label (Proc m W Au) (auditReg m V v₀))) :
    ∀ s i, i ≠ k → padsB rnd v₀ j k α s i = rnd s i := by
  intro s i hi; simp [padsB, hi]

/-- The pads `padsB` give reader `j` the bit `k` it observes at each of its fetch&xor. -/
lemma padsB_fx {α β γ : List (Label (Proc m W Au) (auditReg m V v₀))} (hα : β ++ γ = α)
    {C : Cfg m W Au V v₀} (hβ : (alg1 rnd v₀).run β = some C) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    {γ' : List (Label (Proc m W Au) (auditReg m V v₀))} (hγ : γ = ℓ :: γ')
    (hℓ : ℓ = .tau (.rd j)) (hfx : isFX (C.loc (.rd j)) = true) :
    padsB rnd v₀ j k α (C.mem .R : RVal m V).seq k = (C.mem .R : RVal m V).bits k := by
  have hI := Inv.of_run hβ
  have h0 : fxBit rnd v₀ j k (C.mem .R : RVal m V).seq (alg1 rnd v₀).initCfg β = none := by
    cases hb : fxBit rnd v₀ j k (C.mem .R : RVal m V).seq (alg1 rnd v₀).initCfg β with
    | none => rfl
    | some b =>
      exfalso
      have hf := fxBit_fetched Inv.init hb hβ
      cases hl : C.loc (.rd j) <;> simp [hl, isFX] at hfx
      exact not_fetched_of_rFX hI hl hf
  have h1 : fxBit rnd v₀ j k (C.mem .R : RVal m V).seq C γ = some ((C.mem .R : RVal m V).bits k) := by
    subst hγ hℓ; simp [fxBit, hfx]
  simp only [padsB, ite_true]
  rw [← hα, fxBit_append _ hβ, h0, h1]
  rfl

end Pads

section Run

lemma simB_init (hagree : ∀ s i, i ≠ k → rnd' s i = rnd s i)
    (γ : List (Label (Proc m W Au) (auditReg m V v₀))) :
    SimB rnd rnd' v₀ k γ (alg1 (W := W) (Au := Au) rnd v₀).initCfg (alg1 rnd' v₀).initCfg := by
  refine ⟨fun p _ => rfl, ?_, rfl, fun p => ?_⟩
  · simp only [Impl.initCfg, alg1]; exact (prR_pad hagree 0 v₀).symm
  · cases p <;> simp [PRelB, WRelB, Impl.initCfg, alg1, locInit]

/-- The transformed execution exists for every prefix of `α`. -/
lemma simB_run (hjk : j ≠ k) (α : List (Label (Proc m W Au) (auditReg m V v₀)))
    {β γ : List (Label (Proc m W Au) (auditReg m V v₀))} (hα : β ++ γ = α)
    {C : Cfg m W Au V v₀} (hβ : (alg1 rnd v₀).run β = some C) :
    ∃ β' C', (alg1 (padsB rnd v₀ j k α) v₀).run β' = some C' ∧
      SimB rnd (padsB rnd v₀ j k α) v₀ k γ C C' ∧
      (alg1 (padsB rnd v₀ j k α) v₀).obsFrom (.rd j) (alg1 (padsB rnd v₀ j k α) v₀).initCfg β' =
        (alg1 rnd v₀).obsFrom (.rd j) (alg1 rnd v₀).initCfg β ∧
      ∀ ℓ ∈ β', ℓ.proc ≠ .rd k := by
  induction β using List.reverseRecOn generalizing γ C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at hβ; subst hβ
    exact ⟨[], _, rfl, simB_init (padsB_agree α) γ, rfl, by simp⟩
  | append_singleton β ℓ ih =>
    rw [Impl.run_concat] at hβ
    cases hβ₁ : (alg1 rnd v₀).run β with
    | none => simp [hβ₁] at hβ
    | some C₁ =>
      simp only [hβ₁, Option.bind_some] at hβ
      have hα' : β ++ ℓ :: γ = α := by rw [← hα]; simp
      obtain ⟨β', C₁', h1, hS, hobs, hk⟩ := ih hα' hβ₁
      have hI₁ := Inv.of_run hβ₁
      have hD₁ := DInv.of_run hβ₁
      obtain ⟨ℓs, D', h2, hS', hob, hk'⟩ := simB_step hjk (padsB_agree α) hI₁ hD₁ hS hβ
        (fun hℓ hfx => padsB_fx hα' hβ₁ rfl hℓ hfx)
      refine ⟨β' ++ ℓs, D', by rw [Impl.run_append_of_eq _ h1]; exact h2, hS', ?_, ?_⟩
      · rw [Impl.obsFrom_append_of_runFrom _ _ h1, obsFrom_concat hβ₁ hβ, hobs, hob]
      · intro ℓ' hℓ'
        rcases List.mem_append.1 hℓ' with h | h
        · exact hk ℓ' h
        · exact hk' ℓ' h

/-- **Lemma 7** of Attiya et al. (PODC 2025), strengthened: for readers `p_j ≠ p_k`, every
execution `α` of Algorithm 1 (with one-time pads `rnd`) has an execution `α'` (with pads `rnd'`
that differ from `rnd` only in bit `k`) which `p_j` cannot distinguish from `α` and in which
`p_k` invokes no operation at all; in particular no read of `p_k` is effective in `α'`. -/
theorem remove_reader {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j k : Fin m} (hjk : j ≠ k) :
    ∃ rnd' α', (alg1 rnd' v₀).Valid α' ∧
      Impl.IndistFam (fun θ => alg1 (W := W) (Au := Au) θ v₀) (.rd j) (rnd, α) (rnd', α') ∧
      opsOf α' (.rd k) = [] ∧ ∀ s i, i ≠ k → rnd' s i = rnd s i := by
  obtain ⟨α', C', h1, -, hobs, hk⟩ := simB_run hjk α (List.append_nil α) hα
  refine ⟨padsB rnd v₀ j k α, α', ⟨C', h1⟩, ?_, opsOf_eq_nil_of_proc_ne hk, padsB_agree α⟩
  simp only [Impl.IndistFam, Impl.procView, hobs]
  rfl

end Run

end Podc.AuditingWithoutLeaks
