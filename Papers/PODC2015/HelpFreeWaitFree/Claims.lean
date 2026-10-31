import Papers.PODC2015.HelpFreeWaitFree.Setting

/-!
# Claims 4.4.5, 4.5.2 and 4.5.3 of [CPT15]

In the context `Ctx` of the proof of Theorem 4.3 (wait-free, weakly help-free `f`):

* `exists_finish` — a process runs solo until its current operation (pending, or invoked now)
  completes (wait-freedom);
* `not_decidedBefore_cur` — **Observation 4.4.4 (2)**: an operation not yet invoked is not
  decided before the current operation of another process;
* `claim_4_4_5` — **Claim 4.4.5**: if `a` is decided before the current operation `b` of another
  process, then `a` is decided before every operation not yet invoked;
* `claim_4_5_2` — **Claim 4.5.2**: if `op₁` or `op₂` is decided before `op₃`, the order of `op₁`
  and `op₂` is decided;
* `claim_4_5_3_1`, `claim_4_5_3_2`, `claim_4_5_3_3` — **Claim 4.5.3 (1)–(3)**, stated as
  indistinguishability contradictions.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]

namespace Ctx

variable {I : Impl A B P L} (X : Ctx I)

/-! ### Solo runs -/

include X in
/-- Process `q` runs solo until its current operation completes: if `q` is pending it finishes,
if it is idle it invokes `o` and runs it to completion. -/
lemma exists_finish {h : List (Label P A)} {C : Config A B P L} (hC : I.run h = some C)
    (q : P) (o : A.Op) :
    ∃ s C', I.runFrom C s = some C' ∧ (∀ γ ∈ s, γ.proc = q) ∧ C'.pend q = none ∧
      (C.pend q = none → opsOf s q = [o]) ∧ (C.pend q ≠ none → opsOf s q = []) ∧
      (respsOf s q).length = 1 := by
  have hof := X.wf.obstructionFree
  by_cases hp : C.pend q = none
  · obtain ⟨C', h1, h2, h3, h4, h5⟩ := I.soloOp_spec hof q o (X.allowed q o) hC hp
    exact ⟨_, C', h1, h3, h2, fun _ => h4, fun h => absurd hp h, h5⟩
  · have hfin := hof C q ⟨h, hC⟩ hp
    refine ⟨I.soloLabels q C (I.soloTime q C), _, I.runFrom_soloLabels q C _,
      fun γ hγ => I.soloLabels_proc q C _ γ hγ, I.soloTime_spec q C hfin, fun h => absurd h hp,
      fun _ => I.opsOf_soloLabels q q C _, ?_⟩
    have := I.runFrom_counts (I.runFrom_soloLabels q C (I.soloTime q C)) q 1 0 (Or.inr ⟨hp, rfl⟩)
    rw [I.opsOf_soloLabels] at this
    simp only [I.soloTime_spec q C hfin, true_and, ne_eq, not_true_eq_false, false_and,
      or_false] at this
    simp at this; omega

/-- Labels of other processes leave the operations of `q` unchanged. -/
lemma opsOf_of_proc {s : List (Label P A)} {q r : P} (hs : ∀ γ ∈ s, γ.proc = q) (hr : r ≠ q) :
    opsOf s r = [] ∧ respsOf s r = [] :=
  ⟨opsOf_eq_nil_of_proc_ne (fun γ hγ => by rw [hs γ hγ]; exact Ne.symm hr),
    respsOf_eq_nil_of_proc_ne (fun γ hγ => by rw [hs γ hγ]; exact Ne.symm hr)⟩

/-- After `exists_finish`, the current operation of `q` (before the run) is completed and the
next one is not invoked. -/
lemma finish_spec {h s : List (Label P A)} {C : Config A B P L} (hC : I.run h = some C)
    {q : P} {o : A.Op} (hs1 : (C.pend q = none → opsOf s q = [o]))
    (hs2 : (C.pend q ≠ none → opsOf s q = [])) (hs3 : (respsOf s q).length = 1) :
    Completed (h ++ s) (curOp h q) ∧ ∀ j, (respsOf h q).length < j → ¬ Invoked (h ++ s) (q, j) := by
  constructor
  · simp [Completed, hs3]
  · intro j hj
    simp only [Invoked, opsOf_append, List.length_append]
    by_cases hp : C.pend q = none
    · rw [hs1 hp, I.run_idle_counts hC hp]; simp; omega
    · rw [hs2 hp, I.run_pend_counts hC hp]; simp; omega

/-! ### Observation 4.4.4 and Claim 4.4.5 -/

/-- **Observation 4.4.4 (2)**: an operation `a` not yet invoked is not decided before the
current operation of another process `q`. -/
lemma not_decidedBefore_cur {h : List (Label P A)} (hv : I.Valid h) {a : OpId P} {q : P}
    (ha : ¬ Invoked h a) (hq : a.1 ≠ q) : ¬ X.DB h a (curOp h q) := by
  obtain ⟨C, hC⟩ := hv
  obtain ⟨s, C', h1, h2, -, h4, h5, h6⟩ := X.exists_finish hC q (X.W 0)
  have hv' : I.Valid (h ++ s) := ⟨C', by rw [I.run_append_of_eq hC, h1]⟩
  refine not_decidedBefore_of_extension X.lin hv' (finish_spec hC h4 h5 h6).1 ?_
  simp only [Invoked, opsOf_append, (opsOf_of_proc h2 hq).1, List.append_nil]
  exact ha

/-- **Claim 4.4.5**: if `a` is decided before the current operation of another process `q`, then
`a` is decided before every operation `c` that is not yet invoked (other than that current
operation). The proof runs `q` solo to complete its operation; its steps cannot decide `a`
before anything. -/
theorem claim_4_4_5 {h : List (Label P A)} (hv : I.Valid h) {a c : OpId P} {q : P}
    (hq : a.1 ≠ q) (hab : X.DB h a (curOp h q)) (hc : ¬ Invoked h c) (hcb : c ≠ curOp h q) :
    X.DB h a c := by
  obtain ⟨C, hC⟩ := hv
  obtain ⟨s, C', h1, h2, -, h4, h5, h6⟩ := X.exists_finish hC q (X.W 0)
  have hv' : I.Valid (h ++ s) := ⟨C', by rw [I.run_append_of_eq hC, h1]⟩
  obtain ⟨hcomp, hnext⟩ := finish_spec hC h4 h5 h6
  have hc' : ¬ Invoked (h ++ s) c := by
    by_cases hcq : c.1 = q
    · obtain ⟨c1, c2⟩ := c
      simp only at hcq; subst hcq
      apply hnext
      have : c2 ≠ (respsOf h c1).length := fun e => hcb (by rw [e])
      have h7 : (respsOf h c1).length ≤ (opsOf h c1).length := hv'.of_append.wellFormed.resps_le_ops c1
      simp only [Invoked] at hc
      omega
    · simp only [Invoked, opsOf_append, (opsOf_of_proc h2 hcq).1, List.append_nil]; exact hc
  have hbc : X.DB (h ++ s) (curOp h q) c := decidedBefore_of_completed X.lin hcomp hc'
  exact X.owner.decidedBefore_of_append hv' (fun γ hγ => by rw [h2 γ hγ]; exact Ne.symm hq)
    ((hab.append s).trans hbc)

/-! ### Preliminaries for Claims 4.5.2 and 4.5.3 -/

lemma prec_asymm {S : List (OpId P × A.Op)} {a b : OpId P} (h : Prec S a b) : ¬ Prec S b a := by
  rw [prec_iff_pos_lt] at *; omega

lemma prec_of_not_prec {S : List (OpId P × A.Op)} {a b : OpId P} (ha : a ∈ S.map Prod.fst)
    (h : ¬ Prec S b a) (hne : a ≠ b) : Prec S a b := by
  rw [not_prec_iff] at h
  rw [prec_iff_pos_lt]
  by_cases hb : b ∈ S.map Prod.fst
  · exact pos_lt_of_le_of_ne hb h hne
  · rw [pos_eq_length_iff.2 hb]; exact pos_lt_length_iff.2 ha

/-- The exact-order separation property for `n` and `m`. -/
def Sep (n m : ℕ) : Prop :=
  0 < m ∧ ∀ a ∈ seqWFirst X.op X.W X.R n m, ∀ b ∈ seqOpFirst X.op X.W X.R n m,
    taggedResps A A.init a ≠ taggedResps A A.init b

lemma Sep.not_both {n m : ℕ} (hs : X.Sep n m) {rs : List A.Resp} (h1 : X.ResW n m rs)
    (h2 : X.ResOp n m rs) : False := by
  obtain ⟨a, ha, rfl⟩ := h1
  obtain ⟨b, hb, hb'⟩ := h2
  exact hs.2 a ha b hb hb'.symm

/-- `Std` is preserved by steps of `p₁` and `p₂` following their programs. -/
lemma Std.append {n : ℕ} {h s : List (Label P A)} (hstd : X.Std n h) (hv : I.Valid (h ++ s))
    (hs : ∀ γ ∈ s, γ.proc = X.p₁ ∨ γ.proc = X.p₂)
    (h1 : opsOf (h ++ s) X.p₁ = [] ∨ opsOf (h ++ s) X.p₁ = [X.op])
    (h2 : opsOf (h ++ s) X.p₂ = pre X.W n ∨ opsOf (h ++ s) X.p₂ = pre X.W (n + 1)) :
    X.Std n (h ++ s) := by
  have hnil : ∀ q, q ≠ X.p₁ → q ≠ X.p₂ → opsOf s q = [] := fun q hq1 hq2 =>
    opsOf_eq_nil_of_proc_ne (fun γ hγ => by
      rcases hs γ hγ with h' | h' <;> rw [h'] <;> [exact Ne.symm hq1; exact Ne.symm hq2])
  refine ⟨hv, h1, h2, ?_, ?_, ?_, fun i hi => (hstd.dec i hi).append s⟩
  · have := hstd.resp2; simp only [respsOf_append, List.length_append]; omega
  · simp [hstd.ops3, hnil X.p₃ (Ne.symm X.h13) (Ne.symm X.h23)]
  · intro q hq1 hq2 hq3; simp [hstd.other q hq1 hq2 hq3, hnil q hq1 hq2]

/-- `p₃` runs `R(m)` solo. -/
lemma exists_run3 {n : ℕ} {h : List (Label P A)} (hstd : X.Std n h) (m : ℕ) :
    ∃ t C, I.run (h ++ t) = some C ∧ (∀ γ ∈ t, γ.proc = X.p₃) ∧ opsOf t X.p₃ = pre X.R m ∧
      (respsOf t X.p₃).length = m := by
  obtain ⟨C₀, hC₀⟩ := hstd.valid
  have hp := I.pend_none_of_opsOf_nil hC₀ hstd.ops3
  obtain ⟨C, h1, -, h3, h4, h5⟩ := I.soloOps_spec X.wf.obstructionFree X.p₃ (pre X.R m)
    (fun o _ => X.allowed _ o) hC₀ hp
  exact ⟨_, C, by rw [I.run_append_of_eq hC₀, h1], h3, h4, by rw [h5]; simp [pre]⟩

/-- Executions of the processes of `Q` from `Q`-agreeing configurations. -/
lemma transport {h h' t : List (Label P A)} {C C' D : Config A B P L} {Q : Set P}
    (hC : I.run h = some C) (hD : I.run h' = some D) (hag : Impl.AgreeOn Q C D)
    (ht : ∀ γ ∈ t, γ.proc ∈ Q) (hCt : I.run (h ++ t) = some C') :
    ∃ D', I.run (h' ++ t) = some D' ∧ Impl.AgreeOn Q C' D' := by
  rw [I.run_append_of_eq hC] at hCt
  obtain ⟨D', h1, h2⟩ := Impl.runFrom_agreeOn hag ht hCt
  exact ⟨D', by rw [I.run_append_of_eq hD, h1], h2⟩

/-- In `Std n h`, if `op₁` is decided before `op₂`, it is decided before `op₃`
(Claim 4.4.5, or Observation 4.4.4 (1) if `op₂` already completed). -/
lemma Std.db13_of_db12 {n : ℕ} {h : List (Label P A)} (hstd : X.Std n h)
    (hd : X.DB h (X.p₁, 0) (X.p₂, n)) : X.DB h (X.p₁, 0) (X.p₃, 0) := by
  have hno3 : ¬ Invoked h (X.p₃, 0) := by simp [Invoked, hstd.ops3]
  by_cases hc : Completed h (X.p₂, n)
  · exact hd.trans (decidedBefore_of_completed X.lin hc hno3)
  · have hcur : curOp h X.p₂ = (X.p₂, n) := by
      simp only [Completed] at hc; have := hstd.resp2
      simp only [curOp, Prod.mk.injEq, true_and]; omega
    rw [← hcur] at hd
    exact X.claim_4_4_5 hstd.valid X.h12 hd hno3
      (by rw [hcur]; exact fun e => X.h23 (Prod.ext_iff.1 e).1.symm)

/-- In `Std n h`, if `op₂` is decided before `op₁`, it is decided before `op₃`. -/
lemma Std.db23_of_db21 {n : ℕ} {h : List (Label P A)} (hstd : X.Std n h)
    (hd : X.DB h (X.p₂, n) (X.p₁, 0)) : X.DB h (X.p₂, n) (X.p₃, 0) := by
  have hno3 : ¬ Invoked h (X.p₃, 0) := by simp [Invoked, hstd.ops3]
  by_cases hc : Completed h (X.p₁, 0)
  · exact hd.trans (decidedBefore_of_completed X.lin hc hno3)
  · have hcur : curOp h X.p₁ = (X.p₁, 0) := by
      simp only [Completed, not_lt, Nat.le_zero] at hc
      simp [curOp, hc]
    rw [← hcur] at hd
    exact X.claim_4_4_5 hstd.valid (Ne.symm X.h12) hd hno3
      (by rw [hcur]; exact fun e => X.h13 (Prod.ext_iff.1 e).1.symm)

/-- Linearizations contain completed operations. -/
lemma mem_of_completed {α : List (Label P A)} (hv : I.Valid α) {x : OpId P}
    (hx : Completed α x) : x ∈ (X.f α).map Prod.fst := (X.lin α hv).complete x hx

/-! ### Claim 4.5.2 -/

/-- **Claim 4.5.2**: in the situation `Std n h`, if `op₁` (or `op₂`) is decided before `op₃`,
then the order between `op₁` and `op₂` is already decided. -/
theorem claim_4_5_2 {n m : ℕ} {h : List (Label P A)} (hstd : X.Std n h) (hsep : X.Sep n m)
    (hdec : X.DB h (X.p₁, 0) (X.p₃, 0) ∨ X.DB h (X.p₂, n) (X.p₃, 0)) :
    X.DB h (X.p₁, 0) (X.p₂, n) ∨ X.DB h (X.p₂, n) (X.p₁, 0) := by
  obtain ⟨t, C, hCt, htp, hto, htr⟩ := X.exists_run3 hstd m
  have hcore := fun s hv => X.core hstd hsep.1 htp hto htr (s := s) hv hdec
  have hv0 : I.Valid (h ++ t ++ []) := ⟨C, by simpa using hCt⟩
  have hvt : I.Valid (h ++ t) := ⟨C, hCt⟩
  have hback : ∀ a b, a.1 ≠ X.p₃ → X.DB (h ++ t) a b → X.DB h a b := fun a b ha hd =>
    X.owner.decidedBefore_of_append hvt (fun γ hγ => by rw [htp γ hγ]; exact Ne.symm ha) hd
  by_cases hP : Prec (X.f (h ++ t ++ [])) (X.p₂, n) (X.p₁, 0)
  · have hW := (hcore [] hv0).1 hP
    right
    apply hback _ _ X.h23
    intro s hv hprec
    exact Sep.not_both X hsep hW ((hcore s (by simpa using hv)).2 (by simpa using prec_asymm hprec))
  · have hO := (hcore [] hv0).2 hP
    left
    apply hback _ _ X.h13
    intro s hv hprec
    exact Sep.not_both X hsep ((hcore s (by simpa using hv)).1 (by simpa using hprec)) hO

/-! ### Claim 4.5.3 -/

/-- **Claim 4.5.3 (1)**: histories where `op₁` is decided before `op₂`, resp. `op₂` before `op₁`,
are distinguishable by `p₃`: they cannot agree on the memory and on `p₃`. -/
theorem claim_4_5_3_1 {n m : ℕ} {h₁ h₂ : List (Label P A)} {C₁ C₂ : Config A B P L}
    (hs₁ : X.Std n h₁) (hs₂ : X.Std n h₂) (hC₁ : I.run h₁ = some C₁) (hC₂ : I.run h₂ = some C₂)
    (hag : Impl.AgreeOn {X.p₃} C₁ C₂) (hsep : X.Sep n m)
    (hd₁ : X.DB h₁ (X.p₁, 0) (X.p₂, n)) (hd₂ : X.DB h₂ (X.p₂, n) (X.p₁, 0)) : False := by
  have h13 := Std.db13_of_db12 X hs₁ hd₁
  have h23 := Std.db23_of_db21 X hs₂ hd₂
  obtain ⟨t, C, hCt, htp, hto, htr⟩ := X.exists_run3 hs₁ m
  obtain ⟨D, hDt, -⟩ := transport (Q := {X.p₃}) hC₁ hC₂ hag (fun γ hγ => by simp [htp γ hγ]) hCt
  have hv1 : I.Valid (h₁ ++ t ++ []) := ⟨C, by simpa using hCt⟩
  have hv2 : I.Valid (h₂ ++ t ++ []) := ⟨D, by simpa using hDt⟩
  have hO := (X.core hs₁ hsep.1 htp hto htr hv1 (Or.inl h13)).2
    (by have := hd₁ (t ++ []) (by simpa using hv1); simpa using this)
  have hW := (X.core hs₂ hsep.1 htp hto htr hv2 (Or.inr h23)).1 (by
    have h3 : ((X.p₃, 0) : OpId P) ∈ (X.f (h₂ ++ (t ++ []))).map Prod.fst :=
      X.mem_of_completed (by simpa using hv2) (by
        have := hsep.1
        simp only [Completed, respsOf_append, List.length_append, List.append_nil]; omega)
    have hm2 := (h23.mem (by simpa using hv2) h3).1
    have := prec_of_not_prec hm2 (hd₂ (t ++ []) (by simpa using hv2))
      (fun e => X.h12 (Prod.ext_iff.1 e).1.symm)
    simpa using this)
  exact Sep.not_both X hsep hW hO

/-- **Claim 4.5.3 (2)**: a history where the order of `op₁`, `op₂` is not decided in favour of
`op₁` and one where `op₁` is decided before `op₂` cannot agree on the memory and on `p₂`, `p₃`
(when `p₂` has completed exactly `n` operations in both). -/
theorem claim_4_5_3_2 {n m : ℕ} {h h' : List (Label P A)} {C C' : Config A B P L}
    (hs : X.Std n h) (hs' : X.Std n h') (hC : I.run h = some C) (hC' : I.run h' = some C')
    (hag : Impl.AgreeOn {X.p₂, X.p₃} C' C) (hsep : X.Sep n m)
    (hr : (respsOf h X.p₂).length = n) (hr' : (respsOf h' X.p₂).length = n)
    (hnd : ¬ X.DB h (X.p₁, 0) (X.p₂, n)) (hd' : X.DB h' (X.p₁, 0) (X.p₂, n)) : False := by
  obtain ⟨s, E', h1, h2, -, h4, h5, h6⟩ := X.exists_finish hC' X.p₂ (X.W n)
  have hrun' : I.run (h' ++ s) = some E' := by rw [I.run_append_of_eq hC', h1]
  obtain ⟨E, hrun, hagE⟩ := transport (Q := _) hC' hC hag (fun γ hγ => by simp [h2 γ hγ]) hrun'
  have hpend : C.pend X.p₂ = C'.pend X.p₂ := (hag.pend X.p₂ (by simp)).symm
  -- `p₂`'s operations after the run
  have hops : ∀ h₀ (C₀ : Config A B P L), I.run h₀ = some C₀ → X.Std n h₀ →
      (respsOf h₀ X.p₂).length = n → C₀.pend X.p₂ = C'.pend X.p₂ →
      opsOf (h₀ ++ s) X.p₂ = pre X.W (n + 1) := by
    intro h₀ C₀ hC₀ hs₀ hr₀ hp₀
    by_cases hp : C'.pend X.p₂ = none
    · have hl := I.run_idle_counts hC₀ (hp₀.trans hp)
      have : opsOf h₀ X.p₂ = pre X.W n := by
        rcases hs₀.ops2 with e | e
        · exact e
        · rw [e] at hl; simp [pre] at hl; omega
      rw [opsOf_append, this, h4 hp, pre_succ']
    · have hl := I.run_pend_counts hC₀ (by rw [hp₀]; exact hp)
      have : opsOf h₀ X.p₂ = pre X.W (n + 1) := by
        rcases hs₀.ops2 with e | e
        · rw [e] at hl; simp [pre] at hl; omega
        · exact e
      rw [opsOf_append, this, h5 hp, List.append_nil]
  have hp1 : ∀ h₀, opsOf (h₀ ++ s) X.p₁ = opsOf h₀ X.p₁ := fun h₀ => by
    simp [(opsOf_of_proc h2 X.h12).1]
  have hsS' : X.Std n (h' ++ s) := Std.append X hs' ⟨E', hrun'⟩ (fun γ hγ => Or.inr (h2 γ hγ))
    (by rw [hp1]; exact hs'.ops1) (Or.inr (hops h' C' hC' hs' hr' rfl))
  have hsS : X.Std n (h ++ s) := Std.append X hs ⟨E, hrun⟩ (fun γ hγ => Or.inr (h2 γ hγ))
    (by rw [hp1]; exact hs.ops1) (Or.inr (hops h C hC hs hr hpend))
  have hcomp : ∀ h₀, (respsOf h₀ X.p₂).length = n → Completed (h₀ ++ s) (X.p₂, n) := by
    intro h₀ hr₀; simp [Completed, hr₀, h6]
  have hno3 : ∀ h₀ : List (Label P A), X.Std n h₀ → ¬ Invoked h₀ (X.p₃, 0) := fun h₀ hs₀ => by
    simp [Invoked, hs₀.ops3]
  have hd23' := decidedBefore_of_completed X.lin (hcomp h' hr') (hno3 _ hsS')
  have hd23 := decidedBefore_of_completed X.lin (hcomp h hr) (hno3 _ hsS)
  obtain ⟨t, F', hFt', htp, hto, htr⟩ := X.exists_run3 hsS' m
  obtain ⟨F, hFt, -⟩ := transport (Q := _) hrun' hrun hagE (fun γ hγ => by simp [htp γ hγ]) hFt'
  -- after `h'`: `op₁` before `op₂`
  have hO := (X.core hsS' hsep.1 htp hto htr (s := []) ⟨F', by simpa using hFt'⟩ (Or.inr hd23')).2
    (by have := hd' (s ++ t ++ []) (by have : I.Valid (h' ++ s ++ t) := ⟨F', hFt'⟩; simpa using this)
        simpa using this)
  -- after `h`: `op₁` still not decided before `op₂`
  have hnd' : ¬ X.DB (h ++ s ++ t) (X.p₁, 0) (X.p₂, n) := by
    intro hd
    apply hnd
    refine X.owner.decidedBefore_of_append (s := s ++ t) (by have : I.Valid (h ++ s ++ t) := ⟨F, hFt⟩; simpa using this)
      (fun γ hγ => ?_) (by simpa using hd)
    rcases List.mem_append.1 hγ with hγ | hγ
    · rw [h2 γ hγ]; exact X.h12.symm
    · rw [htp γ hγ]; exact X.h13.symm
  simp only [DB, DecidedBefore, not_forall, not_not] at hnd'
  obtain ⟨s', hv', hprec⟩ := hnd'
  have hW := (X.core hsS hsep.1 htp hto htr hv' (Or.inr hd23)).1 hprec
  exact Sep.not_both X hsep hW hO

/-- **Claim 4.5.3 (3)**: symmetric to (2), with the roles of `p₁` and `p₂` exchanged (the paper
remarks it is not needed; it is used here to repair the proof of Claim 4.5.10). -/
theorem claim_4_5_3_3 {n m : ℕ} {h h' : List (Label P A)} {C C' : Config A B P L}
    (hs : X.Std n h) (hs' : X.Std n h') (hC : I.run h = some C) (hC' : I.run h' = some C')
    (hag : Impl.AgreeOn {X.p₁, X.p₃} C' C) (hsep : X.Sep n m)
    (hr : respsOf h X.p₁ = []) (hr' : respsOf h' X.p₁ = [])
    (hnd : ¬ X.DB h (X.p₂, n) (X.p₁, 0)) (hd' : X.DB h' (X.p₂, n) (X.p₁, 0)) : False := by
  obtain ⟨s, E', h1, h2, -, h4, h5, h6⟩ := X.exists_finish hC' X.p₁ X.op
  have hrun' : I.run (h' ++ s) = some E' := by rw [I.run_append_of_eq hC', h1]
  obtain ⟨E, hrun, hagE⟩ := transport (Q := _) hC' hC hag (fun γ hγ => by simp [h2 γ hγ]) hrun'
  have hpend : C.pend X.p₁ = C'.pend X.p₁ := (hag.pend X.p₁ (by simp)).symm
  have hops : ∀ h₀ (C₀ : Config A B P L), I.run h₀ = some C₀ → X.Std n h₀ →
      respsOf h₀ X.p₁ = [] → C₀.pend X.p₁ = C'.pend X.p₁ → opsOf (h₀ ++ s) X.p₁ = [X.op] := by
    intro h₀ C₀ hC₀ hs₀ hr₀ hp₀
    by_cases hp : C'.pend X.p₁ = none
    · have hl := I.run_idle_counts hC₀ (hp₀.trans hp)
      rw [hr₀] at hl
      rw [opsOf_append, List.eq_nil_of_length_eq_zero hl, h4 hp]; rfl
    · have hl := I.run_pend_counts hC₀ (by rw [hp₀]; exact hp)
      have : opsOf h₀ X.p₁ = [X.op] := by
        rcases hs₀.ops1 with e | e
        · rw [e, hr₀] at hl; simp at hl
        · exact e
      rw [opsOf_append, this, h5 hp, List.append_nil]
  have hp2 : ∀ h₀, opsOf (h₀ ++ s) X.p₂ = opsOf h₀ X.p₂ := fun h₀ => by
    simp [(opsOf_of_proc h2 (Ne.symm X.h12)).1]
  have hsS' : X.Std n (h' ++ s) := Std.append X hs' ⟨E', hrun'⟩ (fun γ hγ => Or.inl (h2 γ hγ))
    (Or.inr (hops h' C' hC' hs' hr' rfl)) (by rw [hp2]; exact hs'.ops2)
  have hsS : X.Std n (h ++ s) := Std.append X hs ⟨E, hrun⟩ (fun γ hγ => Or.inl (h2 γ hγ))
    (Or.inr (hops h C hC hs hr hpend)) (by rw [hp2]; exact hs.ops2)
  have hcomp : ∀ h₀ : List (Label P A), respsOf h₀ X.p₁ = [] → Completed (h₀ ++ s) (X.p₁, 0) := by
    intro h₀ hr₀; simp [Completed, hr₀, h6]
  have hno3 : ∀ h₀ : List (Label P A), X.Std n h₀ → ¬ Invoked h₀ (X.p₃, 0) := fun h₀ hs₀ => by
    simp [Invoked, hs₀.ops3]
  have hd13' := decidedBefore_of_completed X.lin (hcomp h' hr') (hno3 _ hsS')
  have hd13 := decidedBefore_of_completed X.lin (hcomp h hr) (hno3 _ hsS)
  obtain ⟨t, F', hFt', htp, hto, htr⟩ := X.exists_run3 hsS' m
  obtain ⟨F, hFt, -⟩ := transport (Q := _) hrun' hrun hagE (fun γ hγ => by simp [htp γ hγ]) hFt'
  have hv' : I.Valid (h' ++ s ++ t ++ []) := ⟨F', by simpa using hFt'⟩
  -- after `h'`: `op₂ ≺ op₁`
  have hW := (X.core hsS' hsep.1 htp hto htr hv' (Or.inl hd13')).1 (by
    have h1m : ((X.p₁, 0) : OpId P) ∈ (X.f (h' ++ (s ++ t ++ []))).map Prod.fst :=
      X.mem_of_completed (by simpa using hv') (by
        have := hcomp h' hr'
        simpa [List.append_assoc] using (this.mono (β := t)))
    have hm2 := (hd'.mem (by simpa using hv') h1m).1
    have := prec_of_not_prec hm2 (hd' (s ++ t ++ []) (by simpa using hv'))
      (fun e => X.h12 (Prod.ext_iff.1 e).1.symm)
    simpa using this)
  have hnd' : ¬ X.DB (h ++ s ++ t) (X.p₂, n) (X.p₁, 0) := by
    intro hd
    apply hnd
    refine X.owner.decidedBefore_of_append (s := s ++ t) (by have : I.Valid (h ++ s ++ t) := ⟨F, hFt⟩; simpa using this)
      (fun γ hγ => ?_) (by simpa using hd)
    rcases List.mem_append.1 hγ with hγ | hγ
    · rw [h2 γ hγ]; exact X.h12
    · rw [htp γ hγ]; exact X.h23.symm
  simp only [DB, DecidedBefore, not_forall, not_not] at hnd'
  obtain ⟨s', hv'', hprec⟩ := hnd'
  have hO := (X.core hsS hsep.1 htp hto htr hv'' (Or.inl hd13)).2 (prec_asymm hprec)
  exact Sep.not_both X hsep hW hO

end Ctx

end Podc.HelpFreeWaitFree
