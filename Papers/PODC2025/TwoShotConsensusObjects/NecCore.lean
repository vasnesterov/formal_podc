import Papers.PODC2025.TwoShotConsensusObjects.NecBasic

/-!
# Necessity (Section 6) — the critical configuration on a copy of `O`

Helper lemmas about steps on a copy `k` of `O`, solo segments that do not access `k`, two-shot
"done" processes, and the setting `KSetup`: a critical execution at which both processes are
poised on copy `k` (operations `op 0 = f`, `op 1 = g`, state `s` of the copy).
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

section Steps

variable {C : Cfg A} {p : Fin 2} {k : ιS} {o : O.Op} {κ : O.Resp → A.L}

lemma stepK_loc_self (h : A.act (C.loc p) = .access (.inr k) o κ) :
    (C.next (.step p)).loc p = κ (O.δ (C.mem (.inr k)) o).2 := by
  simp [Cfg.next, stepP_of_access C h]

lemma stepK_loc_other (h : A.act (C.loc p) = .access (.inr k) o κ) {q : Fin 2} (hq : q ≠ p) :
    (C.next (.step p)).loc q = C.loc q := next_loc_other C _ (by simpa using hq)

lemma stepK_mem_self (h : A.act (C.loc p) = .access (.inr k) o κ) :
    (C.next (.step p)).mem (.inr k) = (O.δ (C.mem (.inr k)) o).1 := by
  simp only [Cfg.next, stepP_of_access C h]
  exact Function.update_self _ _ _

lemma stepK_mem_other (h : A.act (C.loc p) = .access (.inr k) o κ) {j : ιR ⊕ ιS}
    (hj : j ≠ .inr k) : (C.next (.step p)).mem j = C.mem j := by
  simp only [Cfg.next, stepP_of_access C h]
  exact Function.update_of_ne hj _ _

lemma stepK_objOf (h : A.act (C.loc p) = .access (.inr k) o κ) : objOf C p = some (.inr k) := by
  simp [objOf, h]

/-- A solo segment of `r` without access to `i` does not change `i` nor other local states. -/
lemma solo_noAcc_mem {C : Cfg A} {r : Fin 2} {i : ιR ⊕ ιS} {t : ℕ}
    (hno : ∀ t' < t, objOf (run C (solo r t')) r ≠ some i) : (run C (solo r t)).mem i = C.mem i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs : solo r (t + 1) = solo r t ++ [Ev.step r] := List.replicate_succ' ..
    rw [hs, run_append, ← ih (fun t' ht' => hno t' (by omega))]
    set X := run C (solo r t)
    have hX := hno t (by omega)
    simp only [run_cons, run_nil, Cfg.next]
    rcases hact : A.act (X.loc r) with ⟨j, o, κ⟩ | v
    · rw [stepP_of_access X hact]
      have : i ≠ j := by
        rintro rfl; exact hX ((objOf_eq_some_iff _ _ _).2 ⟨o, κ, hact⟩)
      simp [Function.update_of_ne this]
    · rw [stepP_of_out X (show X.Out r v from hact)]

lemma solo_loc_other {C : Cfg A} {r q : Fin 2} (hq : q ≠ r) (t : ℕ) :
    (run C (solo r t)).loc q = C.loc q :=
  run_loc_other C _ (fun e he => by
    simp [solo, List.mem_replicate] at he; rw [he.2]; simpa using fun h => hq h.symm)

lemma solo_accCount_other {C : Cfg A} {r q : Fin 2} (hq : q ≠ r) (t : ℕ) (i : ιR ⊕ ιS) :
    accCount C (solo r t) q i = 0 := by
  induction t generalizing C with
  | zero => rfl
  | succ t ih =>
    change accCount C (.step r :: solo r t) q i = 0
    rw [accCount_cons, ih]
    have : (Ev.step r : Ev 2) ≠ .step q := by simpa using fun h => hq h.symm
    simp [this]

lemma solo_accCount_self {C : Cfg A} {r : Fin 2} {i : ιR ⊕ ιS} {t : ℕ}
    (hno : ∀ t' < t, objOf (run C (solo r t')) r ≠ some i) : accCount C (solo r t) r i = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs : solo r (t + 1) = solo r t ++ [Ev.step r] := List.replicate_succ' ..
    rw [hs, accCount_append, ih (fun t' ht' => hno t' (by omega))]
    simp [accCount_cons, hno t (by omega)]

lemma solo_crashFree (r : Fin 2) (t : ℕ) : CrashFree (solo r t : List (Ev 2)) :=
  crashFree_replicate t r

lemma crashFree_single (r : Fin 2) : CrashFree [(Ev.step r : Ev 2)] := by
  simpa using crashFree_steps (n := 2) [r]

lemma accCount_step_self (C : Cfg A) (h : A.act (C.loc p) = .access (.inr k) o κ) :
    accCount C [.step p] p (.inr k) = 1 := by
  simp [accCount_cons, stepK_objOf h]

lemma accCount_step_other (C : Cfg A) {q : Fin 2} (hq : q ≠ p) (i : ιR ⊕ ιS) :
    accCount C [.step p] q i = 0 := by
  have : (Ev.step p : Ev 2) ≠ .step q := by simpa using fun h => hq h.symm
  simp [accCount_cons, this]

end Steps

section Done

/-- A process that has applied two operations to copy `k` never accesses `k` again. -/
lemma done_noAcc (h2 : TwoShot A) (x : Fin 2 → Bool) {γ : List (Ev 2)} (hγ : CrashFree γ)
    {r : Fin 2} {k : ιS} (hc : 2 ≤ accCount (initCfg A x) γ r (.inr k)) (t : ℕ) :
    objOf (run (run (initCfg A x) γ) (solo r t)) r ≠ some (.inr k) := by
  intro h
  have := h2 x (γ ++ solo r t ++ [.step r])
    ((hγ.append (solo_crashFree r t)).append (crashFree_single r)) r k
  rw [accCount_append, accCount_append] at this
  have h1 : accCount (run (initCfg A x) (γ ++ solo r t)) [.step r] r (.inr k) = 1 := by
    rw [run_append]; simp [accCount_cons, h]
  omega

end Done

/-! ## The critical configuration on copy `k` -/

/-- The setting of Section 6: a critical execution `α` at which `p₀` is poised to apply `op 0`
(the paper's `f`) and `p₁` to apply `op 1` (`g`) to copy `k` of `O`, in state `s`. -/
structure KSetup (A : Alg 2 (withRW (ιS := ιS) R O)) extends CritSetup A where
  k : ιS
  op : Fin 2 → O.Op
  κ : Fin 2 → O.Resp → A.L
  hop : ∀ p, A.act ((run (initCfg A x) α).loc p) = .access (.inr k) (op p) (κ p)

namespace KSetup

variable (S : KSetup A)

/-- The initial configuration. -/
abbrev I : Cfg A := initCfg A S.x
/-- The critical configuration. -/
abbrev E : Cfg A := run S.I S.α
/-- The state of copy `k` at the critical configuration. -/
abbrev s : O.State := S.E.mem (.inr S.k)

/-- `r` cannot tell an extension of `α a` from an extension of `α b` (except for copy `k`) and has
used copy `k` twice: contradiction. -/
lemma contra_done (hA : WFConsensus A) (h2 : TwoShot A) {a b : Fin 2} (hab : a ≠ b)
    {β β' : List (Ev 2)} (hβ : CrashFree β) (hβ' : CrashFree β') {r : Fin 2}
    (hag : AgreeExcept (.inr S.k) r (run S.I (S.α ++ [.step a] ++ β))
      (run S.I (S.α ++ [.step b] ++ β')))
    (hc : 2 ≤ accCount S.I (S.α ++ [.step a] ++ β) r (.inr S.k)) : False := by
  have hcf : CrashFree (S.α ++ [.step a] ++ β) := (S.hα.append (crashFree_single a)).append hβ
  obtain ⟨t, -, ht⟩ := S.must_access hA hab hβ hβ' hag
  exact done_noAcc h2 S.x hcf hc t ht

lemma accCount_crit_le (h2 : TwoShot A) (p : Fin 2) :
    accCount S.I S.α p (.inr S.k) ≤ 1 := by
  have := h2 S.x (S.α ++ [.step p]) (S.hα.append (crashFree_single p)) p S.k
  rw [accCount_append] at this
  have h1 : accCount (run S.I S.α) [.step p] p (.inr S.k) = 1 := accCount_step_self _ (S.hop p)
  change accCount S.I S.α p (.inr S.k) + accCount (run S.I S.α) [.step p] p (.inr S.k) ≤ 2 at this
  omega

/-- Configuration after `α a b`. -/
lemma two_steps_loc_self {a b : Fin 2} (hab : a ≠ b) :
    (run S.I (S.α ++ [.step a] ++ [.step b])).loc a = S.κ a (O.δ S.s (S.op a)).2 := by
  rw [run_append, run_append]
  set E1 := run S.E [.step a]
  have h1 : E1.loc a = S.κ a (O.δ S.s (S.op a)).2 := stepK_loc_self (S.hop a)
  change (E1.next (.step b)).loc a = _
  rw [next_loc_other _ _ (by simpa using hab), h1]

lemma two_steps_loc_other {a b : Fin 2} (hab : a ≠ b) :
    (run S.I (S.α ++ [.step a] ++ [.step b])).loc b =
      S.κ b (O.δ (O.δ S.s (S.op a)).1 (S.op b)).2 := by
  rw [run_append, run_append]
  set E1 := run S.E [.step a]
  have h1 : E1.loc b = S.E.loc b := stepK_loc_other (S.hop a) (Ne.symm hab)
  have h2 : E1.mem (.inr S.k) = (O.δ S.s (S.op a)).1 := stepK_mem_self (S.hop a)
  have hb : A.act (E1.loc b) = .access (.inr S.k) (S.op b) (S.κ b) := by rw [h1]; exact S.hop b
  change (E1.next (.step b)).loc b = _
  rw [stepK_loc_self hb, h2]

lemma two_steps_mem_k {a b : Fin 2} (hab : a ≠ b) :
    (run S.I (S.α ++ [.step a] ++ [.step b])).mem (.inr S.k) =
      (O.δ (O.δ S.s (S.op a)).1 (S.op b)).1 := by
  rw [run_append, run_append]
  set E1 := run S.E [.step a]
  have h1 : E1.loc b = S.E.loc b := stepK_loc_other (S.hop a) (Ne.symm hab)
  have h2 : E1.mem (.inr S.k) = (O.δ S.s (S.op a)).1 := stepK_mem_self (S.hop a)
  have hb : A.act (E1.loc b) = .access (.inr S.k) (S.op b) (S.κ b) := by rw [h1]; exact S.hop b
  change (E1.next (.step b)).mem _ = _
  rw [stepK_mem_self hb, h2]

lemma two_steps_mem_other {a b : Fin 2} (hab : a ≠ b) {j : ιR ⊕ ιS} (hj : j ≠ .inr S.k) :
    (run S.I (S.α ++ [.step a] ++ [.step b])).mem j = S.E.mem j := by
  rw [run_append, run_append]
  set E1 := run S.E [.step a]
  have h1 : E1.loc b = S.E.loc b := stepK_loc_other (S.hop a) (Ne.symm hab)
  have hb : A.act (E1.loc b) = .access (.inr S.k) (S.op b) (S.κ b) := by rw [h1]; exact S.hop b
  change (E1.next (.step b)).mem _ = _
  rw [stepK_mem_other hb hj]
  exact stepK_mem_other (S.hop a) hj

lemma one_step_loc_self (a : Fin 2) :
    (run S.I (S.α ++ [.step a])).loc a = S.κ a (O.δ S.s (S.op a)).2 := by
  rw [run_append]; exact stepK_loc_self (S.hop a)

lemma one_step_loc_other {a b : Fin 2} (hab : a ≠ b) :
    (run S.I (S.α ++ [.step a])).loc b = S.E.loc b := by
  rw [run_append]; exact stepK_loc_other (S.hop a) (Ne.symm hab)

lemma one_step_mem_k (a : Fin 2) :
    (run S.I (S.α ++ [.step a])).mem (.inr S.k) = (O.δ S.s (S.op a)).1 := by
  rw [run_append]; exact stepK_mem_self (S.hop a)

lemma one_step_mem_other (a : Fin 2) {j : ιR ⊕ ιS} (hj : j ≠ .inr S.k) :
    (run S.I (S.α ++ [.step a])).mem j = S.E.mem j := by
  rw [run_append]; exact stepK_mem_other (S.hop a) hj

/-- **If `f` is the last access of `p` to `k`, `p` distinguishes `fg` from `gf`.** -/
lemma dist_of_last (hA : WFConsensus A) (h2 : TwoShot A) {a b : Fin 2} (hab : a ≠ b) (r : Fin 2)
    (hr : r = a ∨ r = b) (hc : accCount S.I S.α r (.inr S.k) = 1) :
    Dist O S.s r [(a, S.op a), (b, S.op b)] [(b, S.op b), (a, S.op a)] := by
  intro heq
  -- the configurations after `α a b` and `α b a` are indistinguishable to `r` except for `k`
  have hag : AgreeExcept (.inr S.k) r (run S.I (S.α ++ [.step a] ++ [.step b]))
      (run S.I (S.α ++ [.step b] ++ [.step a])) := by
    refine ⟨?_, fun j hj => by rw [S.two_steps_mem_other hab hj, S.two_steps_mem_other
      (Ne.symm hab) hj]⟩
    rcases hr with rfl | rfl
    · rw [S.two_steps_loc_self hab, S.two_steps_loc_other (Ne.symm hab)]
      simp [view, hab, Ne.symm hab] at heq
      rw [heq]
    · rw [S.two_steps_loc_other hab, S.two_steps_loc_self (Ne.symm hab)]
      simp [view, hab, Ne.symm hab] at heq
      rw [heq]
  refine S.contra_done hA h2 hab (crashFree_single b) (crashFree_single a) hag ?_
  rw [accCount_append, accCount_append]
  rcases hr with rfl | rfl
  · have := accCount_step_self (S.E) (S.hop r)
    change 2 ≤ accCount S.I S.α r _ + accCount S.E [.step r] r _ + _
    omega
  · have : accCount (run S.E [.step a]) [.step r] r (.inr S.k) = 1 := by
      apply accCount_step_self (run S.E [.step a])
      rw [show (run S.E [.step a]).loc r = S.E.loc r from stepK_loc_other (S.hop a) (Ne.symm hab)]
      exact S.hop r
    have e : run S.I (S.α ++ [.step a]) = run S.E [.step a] := run_append _ _ _
    rw [e, this, hc]
    omega

/-! ### Branches and access counts as predicates on configurations -/

/-- `X` is reached by a crash-free extension of `α a`. -/
def Branch (a : Fin 2) (X : Cfg A) : Prop :=
  ∃ β, CrashFree β ∧ X = run S.I (S.α ++ [.step a] ++ β)

/-- `X` is reached from the initial configuration by a crash-free execution in which `r` applies
`c` operations to copy `k`. -/
def Cnt (r : Fin 2) (X : Cfg A) (c : ℕ) : Prop :=
  ∃ β, CrashFree β ∧ X = run S.I β ∧ accCount S.I β r (.inr S.k) = c

lemma branch_step (a : Fin 2) : S.Branch a (run S.I (S.α ++ [.step a])) :=
  ⟨[], fun _ h => by simp at h, by simp⟩

variable {S}

lemma Branch.next {a : Fin 2} {X : Cfg A} (h : S.Branch a X) (p : Fin 2) :
    S.Branch a (X.next (.step p)) := by
  obtain ⟨β, hβ, rfl⟩ := h
  exact ⟨β ++ [.step p], hβ.append (crashFree_single p), by
    rw [← List.append_assoc, run_concat]⟩

lemma Branch.ext {a : Fin 2} {X : Cfg A} (h : S.Branch a X) (γ : List (Ev 2))
    (hγ : CrashFree γ) : S.Branch a (run X γ) := by
  obtain ⟨β, hβ, rfl⟩ := h
  exact ⟨β ++ γ, hβ.append hγ, by simp only [run_append, List.append_assoc]⟩

variable (S) in
lemma cnt_crit (r : Fin 2) : S.Cnt r S.E (accCount S.I S.α r (.inr S.k)) :=
  ⟨S.α, S.hα, rfl, rfl⟩

lemma Cnt.ext {r : Fin 2} {X : Cfg A} {c : ℕ} (h : S.Cnt r X c) (γ : List (Ev 2))
    (hγ : CrashFree γ) : S.Cnt r (run X γ) (c + accCount X γ r (.inr S.k)) := by
  obtain ⟨β, hβ, rfl, rfl⟩ := h
  exact ⟨β ++ γ, hβ.append hγ, by rw [run_append], by rw [accCount_append]⟩

lemma Cnt.next_other {r q : Fin 2} (hq : q ≠ r) {X : Cfg A} {c : ℕ} (h : S.Cnt r X c) :
    S.Cnt r (X.next (.step q)) c := by
  have := h.ext [.step q] (crashFree_single q)
  rwa [accCount_step_other X (Ne.symm hq), Nat.add_zero] at this

lemma Cnt.next_self {r : Fin 2} {X : Cfg A} {c : ℕ} (h : S.Cnt r X c) {o : O.Op}
    {κ : O.Resp → A.L} (ho : A.act (X.loc r) = .access (.inr S.k) o κ) :
    S.Cnt r (X.next (.step r)) (c + 1) := by
  have := h.ext [.step r] (crashFree_single r)
  rwa [accCount_step_self X ho] at this

lemma Cnt.solo_other {r q : Fin 2} (hq : q ≠ r) {X : Cfg A} {c : ℕ} (h : S.Cnt r X c) (t : ℕ) :
    S.Cnt r (run X (solo q t)) c := by
  have := h.ext (solo q t) (solo_crashFree q t)
  rwa [solo_accCount_other (Ne.symm hq), Nat.add_zero] at this

lemma Cnt.solo_self {r : Fin 2} {X : Cfg A} {c : ℕ} (h : S.Cnt r X c) {t : ℕ}
    (hno : ∀ t' < t, objOf (run X (solo r t')) r ≠ some (.inr S.k)) :
    S.Cnt r (run X (solo r t)) c := by
  have := h.ext (solo r t) (solo_crashFree r t)
  rwa [solo_accCount_self hno, Nat.add_zero] at this

/-- A process that has applied two operations to copy `k` never accesses it again. -/
lemma Cnt.noAcc (h2 : TwoShot A) {r : Fin 2} {X : Cfg A} {c : ℕ} (h : S.Cnt r X c) (hc : 2 ≤ c)
    (t : ℕ) : objOf (run X (solo r t)) r ≠ some (.inr S.k) := by
  obtain ⟨β, hβ, rfl, rfl⟩ := h
  exact done_noAcc h2 S.x hβ hc t

variable (S)

lemma must_access' (hA : WFConsensus A) {a b : Fin 2} (hab : a ≠ b) {X Y : Cfg A}
    (hX : S.Branch a X) (hY : S.Branch b Y) {r : Fin 2} (hag : AgreeExcept (.inr S.k) r X Y) :
    ∃ t, (∀ t' < t, objOf (run X (solo r t')) r ≠ some (.inr S.k)) ∧
      ∃ (o : O.Op) (κ : O.Resp → A.L), A.act ((run X (solo r t)).loc r) = .access (.inr S.k) o κ := by
  obtain ⟨β, hβ, rfl⟩ := hX
  obtain ⟨β', hβ', rfl⟩ := hY
  obtain ⟨t, hno, ht⟩ := S.must_access hA hab hβ hβ' hag
  obtain ⟨o, κ, h⟩ := (objOf_eq_some_iff _ _ _).1 ht
  exact ⟨t, hno, o, κ, h⟩

lemma contra' (hA : WFConsensus A) (h2 : TwoShot A) {a b : Fin 2} (hab : a ≠ b) {X Y : Cfg A}
    (hX : S.Branch a X) (hY : S.Branch b Y) {r : Fin 2} (hag : AgreeExcept (.inr S.k) r X Y)
    {c : ℕ} (hc : S.Cnt r X c) (h2c : 2 ≤ c) : False := by
  obtain ⟨t, -, o, κ, h⟩ := S.must_access' hA hab hX hY hag
  exact hc.noAcc h2 h2c t ((objOf_eq_some_iff _ _ _).2 ⟨o, κ, h⟩)

/-- Transport of "no access before `t`" along `AgreeExcept`. -/
lemma noAcc_transfer {i : ιR ⊕ ιS} {r : Fin 2} {X Y : Cfg A} (h : AgreeExcept i r X Y) {t : ℕ}
    (hno : ∀ t' < t, objOf (run X (solo r t')) r ≠ some i) :
    ∀ t' < t, objOf (run Y (solo r t')) r ≠ some i := by
  intro t' ht'
  have := h.soloRun t' (fun t'' h'' => hno t'' (by omega))
  rw [← objOf_congr this.1]
  exact hno t' ht'

end KSetup

end TwoShotCons
