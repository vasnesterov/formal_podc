import Papers.PODC2025.TwoShotConsensusObjects.Model

/-!
# Necessity (Section 6) — basic indistinguishability and valency tools

* `AgreeExcept i r C D`: process `r` has the same local state in `C` and `D` and all objects
  other than `i` have the same values. Solo runs of `r` that do not access `i` preserve it.
* `CritSetup A`: a critical execution `α` from an initial configuration, with the valencies
  `val p` of the two one-step extensions `α p` (`val 0 ≠ val 1`).
* `CritSetup.contra`: if an extension of `α 0` and an extension of `α 1` are
  indistinguishable to `r` except for object `i`, then `r`'s solo run from the first must access
  `i` (before outputting). With two-shot objects this gives the paper's indistinguishability
  argument: a process that has used a copy twice cannot tell the copy's state.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

section Generic

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-- `r` has the same local state in `C` and `D`, and objects other than `i` agree. -/
def AgreeExcept (i : ι) (r : Fin n) (C D : Cfg A) : Prop :=
  C.loc r = D.loc r ∧ ∀ j, j ≠ i → C.mem j = D.mem j

lemma objOf_eq_some_iff (C : Cfg A) (p : Fin n) (i : ι) :
    objOf C p = some i ↔ ∃ o κ, A.act (C.loc p) = .access i o κ := by
  unfold objOf
  constructor
  · intro h
    split at h
    · rename_i i' o κ hact; simp at h; subst h; exact ⟨o, κ, hact⟩
    · simp at h
  · rintro ⟨o, κ, h⟩; rw [h]

lemma objOf_congr {C D : Cfg A} {p : Fin n} (h : C.loc p = D.loc p) : objOf C p = objOf D p := by
  simp [objOf, h]

/-- A step of `r` that does not access `i` preserves `AgreeExcept i r`. -/
lemma AgreeExcept.step {i : ι} {r : Fin n} {C D : Cfg A} (h : AgreeExcept i r C D)
    (hno : objOf C r ≠ some i) : AgreeExcept i r (C.next (.step r)) (D.next (.step r)) := by
  obtain ⟨hl, hm⟩ := h
  simp only [Cfg.next]
  rcases hact : A.act (C.loc r) with ⟨j, o, κ⟩ | v
  · have hact' : A.act (D.loc r) = .access j o κ := by rw [← hl]; exact hact
    have hji : j ≠ i := by
      intro hji; subst hji; apply hno; rw [objOf_eq_some_iff]; exact ⟨o, κ, hact⟩
    rw [stepP_of_access C hact, stepP_of_access D hact']
    refine ⟨by simp [hm j hji], fun j' hj' => ?_⟩
    by_cases hjj : j' = j
    · subst hjj; simp [hm j' hj']
    · simp [Function.update_of_ne hjj, hm j' hj']
  · have hact' : D.Out r v := by rw [Cfg.Out, ← hl]; exact hact
    rw [stepP_of_out C (show C.Out r v from hact), stepP_of_out D hact']
    exact ⟨hl, hm⟩

/-- Solo runs of `r` that do not access `i` preserve `AgreeExcept i r`. -/
lemma AgreeExcept.soloRun {i : ι} {r : Fin n} {C D : Cfg A} (h : AgreeExcept i r C D) (t : ℕ)
    (hno : ∀ t' < t, objOf (run C (solo r t')) r ≠ some i) :
    AgreeExcept i r (run C (solo r t)) (run D (solo r t)) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    have hs : solo r (t + 1) = solo r t ++ [Ev.step r] := List.replicate_succ' ..
    rw [hs, run_append, run_append]
    have := (ih (fun t' ht' => hno t' (by omega))).step (hno t (by omega))
    simpa using this

lemma AgreeExcept.symm {i : ι} {r : Fin n} {C D : Cfg A} (h : AgreeExcept i r C D) :
    AgreeExcept i r D C := ⟨h.1.symm, fun j hj => (h.2 j hj).symm⟩

lemma AgreeExcept.out_iff {i : ι} {r : Fin n} {C D : Cfg A} (h : AgreeExcept i r C D) (v : Bool) :
    C.Out r v ↔ D.Out r v := by simp [Cfg.Out, h.1]

/-- All processes have the same local states and objects other than `i` agree. -/
def AgreeAll (i : ι) (C D : Cfg A) : Prop :=
  (∀ p, C.loc p = D.loc p) ∧ ∀ j, j ≠ i → C.mem j = D.mem j

lemma AgreeAll.agreeExcept {i : ι} {C D : Cfg A} (h : AgreeAll i C D) (r : Fin n) :
    AgreeExcept i r C D := ⟨h.1 r, h.2⟩

/-- Crash-free executions in which nobody accesses `i` preserve `AgreeAll i`. -/
lemma AgreeAll.run {i : ι} {C D : Cfg A} (h : AgreeAll i C D) (γ : List (Ev n))
    (hγ : CrashFree γ) (hno : ∀ p, accCount C γ p i = 0) : AgreeAll i (run C γ) (run D γ) := by
  induction γ generalizing C D with
  | nil => simpa using h
  | cons e γ ih =>
    rw [run_cons, run_cons]
    have hγ' : CrashFree γ := fun q hq => hγ q (by simp [hq])
    rcases e with r | r
    · have hr : objOf C r ≠ some i := by
        intro hr; have := hno r; rw [accCount_cons] at this; simp [hr] at this
      have hstep : AgreeAll i (C.next (.step r)) (D.next (.step r)) := by
        refine ⟨fun q => ?_, (h.agreeExcept r |>.step hr).2⟩
        by_cases hq : q = r
        · subst hq; exact (h.agreeExcept q |>.step hr).1
        · rw [next_loc_other C _ (by simpa using hq), next_loc_other D _ (by simpa using hq)]
          exact h.1 q
      refine ih hstep hγ' (fun p => ?_)
      have := hno p; rw [accCount_cons] at this; omega
    · exact absurd (by simp) (hγ r)

lemma accCount_congr_of_agreeAll {i : ι} {C D : Cfg A} (h : AgreeAll i C D) (γ : List (Ev n))
    (hγ : CrashFree γ) (hno : ∀ p, accCount C γ p i = 0) (p : Fin n) : accCount D γ p i = 0 := by
  induction γ generalizing C D with
  | nil => rfl
  | cons e γ ih =>
    have hγ' : CrashFree γ := fun q hq => hγ q (by simp [hq])
    rw [accCount_cons]
    have h1 := hno p; rw [accCount_cons] at h1
    have hstep : AgreeAll i (C.next e) (D.next e) := by
      have := h.run [e] (fun q hq => hγ q (by simp at hq; simp [hq])) (fun q => by
        have := hno q; rw [accCount_cons] at this ⊢; rw [accCount_nil]; omega)
      simpa using this
    have := ih hstep hγ' (fun q => by have := hno q; rw [accCount_cons] at this; omega)
    rw [this, ← objOf_congr (h.1 p)]
    omega

end Generic

/-! ## Critical executions -/

section Crit

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {A : Alg 2 T}

/-- A critical (crash-free) execution `α` from the initial configuration with inputs `x`, with the
valency `val p` of the extension by one step of `p`. -/
structure CritSetup (A : Alg 2 T) where
  /-- The inputs. -/
  x : Fin 2 → Bool
  /-- The critical execution. -/
  α : List (Ev 2)
  hα : CrashFree α
  /-- Valency of `α p`. -/
  val : Fin 2 → Bool
  hval : val 0 ≠ val 1
  team : ∀ p, Univ 0 (initCfg A x) (α ++ [.step p]) (val p)
  /-- At the critical configuration nobody has output. -/
  notOut : ∀ p v, ¬ (run (initCfg A x) α).Out p v

lemma fin2_ne_iff {a b : Fin 2} : a ≠ b ↔ b = 1 - a := by
  fin_cases a <;> fin_cases b <;> simp

lemma fin2_cases_ne (r a b : Fin 2) (hab : a ≠ b) : r = a ∨ r = b := by
  fin_cases r <;> fin_cases a <;> fin_cases b <;> simp_all

lemma CritSetup.val_ne (S : CritSetup A) {a b : Fin 2} (hab : a ≠ b) : S.val a ≠ S.val b := by
  have := S.hval
  fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- Existence of a critical execution (FLP / Herlihy valency argument; CSLib). -/
theorem exists_critSetup (hA : WFConsensus A) :
    ∃ S : CritSetup A, ∃ i, ∀ p, (run (initCfg A S.x) S.α).Poised p i := by
  classical
  set x : Fin 2 → Bool := ![false, true]
  have hb := biv_initial (z := 0) hA admOK_crashFree x ⟨0, rfl⟩ ⟨1, rfl⟩
  obtain ⟨α, hc⟩ := exists_crit hA admOK_crashFree (Reach.initial admOK_crashFree x) hb
  have hcf : CrashFree α := crashFree_of_inE_zero hc.1.inE
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA admOK_crashFree (Reach.initial admOK_crashFree x)
    (by norm_num)
  have hpq : p ≠ q := by
    rintro rfl
    have := hp.unique hA admOK_crashFree (Reach.initial admOK_crashFree x) hq
    simp at this
  obtain ⟨v0, h0⟩ := hc.team 0
  obtain ⟨v1, h1⟩ := hc.team 1
  have hv : v0 ≠ v1 := by
    intro hv; subst hv
    have u : ∀ r, Team 0 (initCfg A x) α r v0 := by
      intro r; fin_cases r
      · exact h0
      · exact h1
    have e1 := (u p).unique hA admOK_crashFree (Reach.initial admOK_crashFree x) hp
    have e2 := (u q).unique hA admOK_crashFree (Reach.initial admOK_crashFree x) hq
    rw [e1] at e2; simp at e2
  refine ⟨⟨x, α, hcf, ![v0, v1], by simpa using hv, fun r => ?_,
    fun r v => hc.not_out hA admOK_crashFree (Reach.initial admOK_crashFree x) r v⟩, ?_⟩
  · fin_cases r
    · exact h0
    · exact h1
  · exact hc.poised hA admOK_crashFree (Reach.initial admOK_crashFree x) (by norm_num)

variable (S : CritSetup A)

/-- A crash-free extension of `α p` has valency `val p`: every process running solo outputs it. -/
lemma CritSetup.soloOut (hA : WFConsensus A) (p : Fin 2) (β : List (Ev 2)) (hβ : CrashFree β)
    (r : Fin 2) : SoloOut (run (initCfg A S.x) (S.α ++ [.step p] ++ β)) r (S.val p) := by
  have hcf : CrashFree (S.α ++ [.step p] ++ β) :=
    (S.hα.append (crashFree_steps [p])).append hβ
  have hu := Univ.append (S.team p) (β := β) (InEs.of_crashFree hcf 0)
  exact UnivQ.soloOut hA admOK_crashFree (Reach.initial admOK_crashFree S.x) hu (Set.mem_univ r)

/-- **The basic indistinguishability argument.** If an extension of `α a` and an extension of
`α b` (`a ≠ b`) are indistinguishable to `r` except for object `i`, and `r` running solo from
the first outputs (at `t`) without accessing `i`, we have a contradiction. -/
lemma CritSetup.contra_out (hA : WFConsensus A) {a b : Fin 2} (hab : a ≠ b) {β β' : List (Ev 2)}
    (hβ : CrashFree β) (hβ' : CrashFree β') {r : Fin 2} {i : ι}
    (hag : AgreeExcept i r (run (initCfg A S.x) (S.α ++ [.step a] ++ β))
      (run (initCfg A S.x) (S.α ++ [.step b] ++ β')))
    {t : ℕ} (hno : ∀ t' < t, objOf (run (run (initCfg A S.x) (S.α ++ [.step a] ++ β)) (solo r t')) r
      ≠ some i)
    {v : Bool} (hout : (run (run (initCfg A S.x) (S.α ++ [.step a] ++ β)) (solo r t)).Out r v) :
    False := by
  have h1 : SoloOut (run (initCfg A S.x) (S.α ++ [.step a] ++ β)) r v := ⟨t, hout⟩
  have h2 : SoloOut (run (initCfg A S.x) (S.α ++ [.step b] ++ β')) r v :=
    ⟨t, ((hag.soloRun t hno).out_iff v).1 hout⟩
  have e1 := h1.unique (S.soloOut hA a β hβ r)
  have e2 := h2.unique (S.soloOut hA b β' hβ' r)
  exact S.val_ne hab (e1.symm.trans e2)

/-- Solo runs: either the process reaches a configuration where it is poised on `i`, or it outputs,
without accessing `i` before. -/
lemma solo_cases (hA : WFConsensus A) (C : Cfg A) (hC : Reach A CrashFree C) (r : Fin 2) (i : ι) :
    ∃ t, (∀ t' < t, objOf (run C (solo r t')) r ≠ some i) ∧
      (objOf (run C (solo r t)) r = some i ∨ ∃ v, (run C (solo r t)).Out r v) := by
  classical
  obtain ⟨v, t0, ht0⟩ := hA.exists_soloOut admOK_crashFree hC r
  have hex : ∃ t, objOf (run C (solo r t)) r = some i ∨ ∃ v, (run C (solo r t)).Out r v :=
    ⟨t0, Or.inr ⟨v, ht0⟩⟩
  refine ⟨Nat.find hex, fun t' ht' h => Nat.find_min hex ht' (Or.inl h), Nat.find_spec hex⟩

/-- **`r` must access `i`.** Under the hypotheses of `contra_out`, `r` running solo from the
first configuration reaches a configuration where it is poised on `i`, without accessing `i`
before. -/
lemma CritSetup.must_access (hA : WFConsensus A) {a b : Fin 2} (hab : a ≠ b)
    {β β' : List (Ev 2)} (hβ : CrashFree β) (hβ' : CrashFree β') {r : Fin 2} {i : ι}
    (hag : AgreeExcept i r (run (initCfg A S.x) (S.α ++ [.step a] ++ β))
      (run (initCfg A S.x) (S.α ++ [.step b] ++ β'))) :
    ∃ t, (∀ t' < t, objOf (run (run (initCfg A S.x) (S.α ++ [.step a] ++ β)) (solo r t')) r
      ≠ some i) ∧ objOf (run (run (initCfg A S.x) (S.α ++ [.step a] ++ β)) (solo r t)) r = some i := by
  have hC : Reach A CrashFree (run (initCfg A S.x) (S.α ++ [.step a] ++ β)) :=
    ⟨S.x, _, (S.hα.append (crashFree_steps [a])).append hβ, rfl⟩
  obtain ⟨t, hno, h | ⟨v, hv⟩⟩ := solo_cases hA _ hC r i
  · exact ⟨t, hno, h⟩
  · exact (S.contra_out hA hab hβ hβ' hag hno hv).elim

end Crit

end TwoShotCons
