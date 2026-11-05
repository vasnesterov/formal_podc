import Papers.PODC2016.RWLockRMRTradeoff.Regions

/-!
# Non-vacuity of the hypotheses of Theorem 5

A concrete reader-writer lock `toyLock n` for `n` readers and one writer from read/write
registers satisfying all hypotheses of Theorem 5 except the RMR bounds: every operation is allowed,
Mutual Exclusion, Bounded Exit, Concurrent Entering and Deadlock Freedom (`toyLock_spec`).

Registers: `none` is the writer flag `W`, `some i` the flag of reader `i`; all initially `0`.

* Reader `i`, `lock`: `r0` write `flag[i] := 1`; `r1` read `W`: if `0` enter the CS, else go to
  `r2`; `r2` write `flag[i] := 0`; `r3` read `W`: if `0` go to `r0`, else stay at `r3`.
  `unlock`: `rExit` write `flag[i] := 0`, return.
* Writer, `lock`: `w0` write `W := 1`; then for `k = 0, …, n-1` (`wScan k`): read `flag[k]` until
  it is `0`; enter the CS. `unlock`: `wExit` write `W := 0`, return.

A process returns from `lock` in local state `cs` and from `unlock` in local state `rem`.
Invocations that violate the client pattern (`lock` in the CS, `unlock` in the remainder) are
answered immediately without changing anything.
-/

namespace Podc.RWLockRMRTradeoff.NonVacuity

open Cslib.SharedMemory

/-- Local states. -/
inductive Loc (n : ℕ) where
  | rem
  | cs
  | r0
  | r1
  | r2
  | r3
  | rExit
  | w0
  | wScan (k : Fin n)
  | wExit
  deriving DecidableEq

variable {n : ℕ}

/-- The flag register of a process (`none`, the writer flag, for the writer). -/
def flagReg : Proc n 1 → Option (Fin n)
  | .inl i => some i
  | .inr _ => none

/-- The writer's state after having checked the flags `0, …, k-1`. -/
def wNext (k : ℕ) : Loc n := if h : k < n then .wScan ⟨k, h⟩ else .cs

/-- Actions. -/
abbrev TAct (n : ℕ) := Action mutexObj (Regs (Option (Fin n)) ℕ 0) (Loc n)

/-- The program. -/
def toyAct (p : Proc n 1) : Loc n → TAct n
  | .rem => .ret () .rem
  | .cs => .ret () .cs
  | .r0 => .access (flagReg p) (.write 1) fun _ => .r1
  | .r1 => .access none .read fun r => if r = some 0 then .cs else .r2
  | .r2 => .access (flagReg p) (.write 0) fun _ => .r3
  | .r3 => .access none .read fun r => if r = some 0 then .r0 else .r3
  | .rExit => .access (flagReg p) (.write 0) fun _ => .rem
  | .w0 => .access none (.write 1) fun _ => wNext 0
  | .wScan k => .access (some k) .read fun r => if r = some 0 then wNext (k.1 + 1) else .wScan k
  | .wExit => .access none (.write 0) fun _ => .rem

/-- Invocations. -/
def toyInvoke (p : Proc n 1) : Loc n → MutexOp → Loc n
  | .rem, .lock => if p.isLeft then .r0 else .w0
  | .cs, .unlock => if p.isLeft then .rExit else .wExit
  | l, _ => l

/-- The toy reader-writer lock. -/
def toyLock (n : ℕ) : RWAlg n 1 (Option (Fin n)) ℕ 0 (Loc n) where
  memInit _ := 0
  locInit _ := .rem
  invoke := toyInvoke
  act := toyAct

/-! ### Steps -/

/-- Configurations of the toy lock. -/
abbrev TCfg (n : ℕ) := Config mutexObj (Regs (Option (Fin n)) ℕ 0) (Proc n 1) (Loc n)

/-- Effect of an internal step: the register written (reads write back the value read), the
new value, the new local state. -/
def tauEff (p : Proc n 1) (M : Option (Fin n) → ℕ) : Loc n → Option (Option (Fin n) × ℕ × Loc n)
  | .rem => none
  | .cs => none
  | .r0 => some (flagReg p, 1, .r1)
  | .r1 => some (none, M none, if M none = 0 then .cs else .r2)
  | .r2 => some (flagReg p, 0, .r3)
  | .r3 => some (none, M none, if M none = 0 then .r0 else .r3)
  | .rExit => some (flagReg p, 0, .rem)
  | .w0 => some (none, 1, wNext 0)
  | .wScan k => some (some k, M (some k), if M (some k) = 0 then wNext (k.1 + 1) else .wScan k)
  | .wExit => some (none, 0, .rem)

lemma step_tau' {C C' : TCfg n} {p : Proc n 1} (h : (toyLock n).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ ∃ x, tauEff p C.mem (C.loc p) = some x ∧
      C' = { C with mem := Function.update C.mem x.1 x.2.1,
                    loc := Function.update C.loc p x.2.2 } := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  refine ⟨hp, ?_⟩
  cases C'
  simp only at hpend hmem hloc
  subst hpend hmem hloc
  cases hl : C.loc p <;> simp only [toyLock, hl, toyAct] at hact <;> cases hact <;>
    exact ⟨_, rfl, by first | rfl | simp⟩

lemma step_inv' {C C' : TCfg n} {p : Proc n 1} {o : MutexOp}
    (h : (toyLock n).step C (.inv p o) = some C') :
    C.pend p = none ∧
      C' = { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (toyInvoke p (C.loc p) o) } := by
  obtain ⟨h1, -, h2, h3, h4⟩ := Impl.step_inv h
  refine ⟨h1, ?_⟩
  cases C'; simp only at h2 h3 h4; subst h2 h3 h4; rfl

lemma toyAct_ret {p : Proc n 1} {l l' : Loc n} {r : Unit} (h : toyAct p l = .ret r l') :
    (l = .rem ∨ l = .cs) ∧ l' = l := by
  cases l <;> simp [toyAct] at h <;> simp [h]

lemma step_ret' {C C' : TCfg n} {p : Proc n 1} {r : Unit}
    (h : (toyLock n).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ (C.loc p = .rem ∨ C.loc p = .cs) ∧
      C' = { C with pend := Function.update C.pend p none } := by
  obtain ⟨h1, h2, h3, l, h4, h5⟩ := Impl.step_ret h
  obtain ⟨h6, rfl⟩ := toyAct_ret h4
  refine ⟨h1, h6, ?_⟩
  cases C'; simp only at h2 h3 h5; subst h2 h3 h5; simp

/-! ### The invariant -/

/-- Reader local states (and `rem`, `cs`). -/
def isRd : Loc n → Bool
  | .w0 | .wScan _ | .wExit => false
  | _ => true

/-- Writer local states (and `rem`, `cs`). -/
def isWr : Loc n → Bool
  | .r0 | .r1 | .r2 | .r3 | .rExit => false
  | _ => true

/-- The reader's flag is `1`. -/
def flagOn : Loc n → Bool
  | .r1 | .r2 | .cs | .rExit => true
  | _ => false

/-- The writer flag is `1`. -/
def wOn : Loc n → Bool
  | .wScan _ | .cs | .wExit => true
  | _ => false

/-- Entry-section states. -/
def isEntry : Loc n → Bool
  | .r0 | .r1 | .r2 | .r3 | .w0 | .wScan _ => true
  | _ => false

/-- Exit-section states. -/
def isExit : Loc n → Bool
  | .rExit | .wExit => true
  | _ => false

/-- The writer (in local state `l`) has checked the flag of reader `i`. -/
def chk : Loc n → Fin n → Prop
  | .wScan k, i => i < k
  | .cs, _ => True
  | .wExit, _ => True
  | _, _ => False

/-- The writer. -/
abbrev wr : Proc n 1 := .inr 0

/-- The invariant of the toy lock (holds in every reachable configuration). -/
structure Inv (C : TCfg n) : Prop where
  idle : ∀ p, C.pend p = none → C.loc p = .rem ∨ C.loc p = .cs
  lockL : ∀ p, C.pend p = some .lock → C.loc p ≠ .rem ∧ isExit (C.loc p) = false
  unlockL : ∀ p, C.pend p = some .unlock → C.loc p ≠ .cs ∧ isEntry (C.loc p) = false
  rd : ∀ i, isRd (C.loc (.inl i)) = true
  wrl : isWr (C.loc wr) = true
  flag : ∀ i, C.mem (some i) = if flagOn (C.loc (.inl i)) then 1 else 0
  wflag : C.mem none = if wOn (C.loc wr) then 1 else 0
  excl : ∀ i, chk (C.loc wr) i → C.loc (.inl i) ≠ .cs ∧ C.loc (.inl i) ≠ .rExit

lemma fin_one (j : Fin 1) : j = 0 := Subsingleton.elim _ _

lemma Inv.init : Inv (toyLock n).initCfg where
  idle p _ := Or.inl rfl
  lockL p h := by simp [Impl.initCfg] at h
  unlockL p h := by simp [Impl.initCfg] at h
  rd i := rfl
  wrl := rfl
  flag i := rfl
  wflag := rfl
  excl i h := by simp [Impl.initCfg, toyLock, chk] at h

lemma chk_wOn {l : Loc n} {i : Fin n} (h : chk l i) : wOn l = true := by
  cases l <;> simp_all [chk, wOn]

@[simp] lemma wNext_ne_rem (k : ℕ) : wNext (n := n) k ≠ .rem := by
  unfold wNext; split_ifs <;> simp

@[simp] lemma wNext_ne_cs_iff (k : ℕ) : wNext (n := n) k ≠ .cs ↔ k < n := by
  unfold wNext; split_ifs with h <;> simp [h]

@[simp] lemma isExit_wNext (k : ℕ) : isExit (wNext (n := n) k) = false := by
  unfold wNext; split_ifs <;> rfl

@[simp] lemma isWr_wNext (k : ℕ) : isWr (wNext (n := n) k) = true := by
  unfold wNext; split_ifs <;> rfl

@[simp] lemma wOn_wNext (k : ℕ) : wOn (wNext (n := n) k) = true := by
  unfold wNext; split_ifs <;> rfl

lemma chk_wNext {k : ℕ} {i : Fin n} (h : chk (wNext k) i) : i.1 < k := by
  unfold wNext at h; split_ifs at h with hk
  · exact h
  · exact lt_of_lt_of_le i.2 (not_lt.1 hk)

lemma Inv.upd_reader {C : TCfg n} (hI : Inv C) (i0 : Fin n) (l' : Loc n)
    (pd : Option MutexOp) (M' : Option (Fin n) → ℕ)
    (hM0 : M' none = C.mem none) (hMi : ∀ i, i ≠ i0 → M' (some i) = C.mem (some i))
    (hMi0 : M' (some i0) = if flagOn l' then 1 else 0)
    (hrd : isRd l' = true)
    (hpn : pd = none → l' = .rem ∨ l' = .cs)
    (hpl : pd = some .lock → l' ≠ .rem ∧ isExit l' = false)
    (hpu : pd = some .unlock → l' ≠ .cs ∧ isEntry l' = false)
    (hex : chk (C.loc wr) i0 → l' ≠ .cs ∧ l' ≠ .rExit) :
    Inv (n := n) { loc := Function.update C.loc (.inl i0) l',
                   pend := Function.update C.pend (.inl i0) pd, mem := M' } where
  idle q h := by
    by_cases hq : q = .inl i0
    · subst hq; simp at h ⊢; exact hpn h
    · simp [Function.update_of_ne hq] at h ⊢; exact hI.idle q h
  lockL q h := by
    by_cases hq : q = .inl i0
    · subst hq; simp at h ⊢; exact hpl h
    · simp [Function.update_of_ne hq] at h ⊢; exact hI.lockL q h
  unlockL q h := by
    by_cases hq : q = .inl i0
    · subst hq; simp at h ⊢; exact hpu h
    · simp [Function.update_of_ne hq] at h ⊢; exact hI.unlockL q h
  rd i := by
    by_cases hq : i = i0
    · subst hq; simpa using hrd
    · simpa [Function.update_of_ne (show (Sum.inl i : Proc n 1) ≠ .inl i0 by simpa using hq)]
        using hI.rd i
  wrl := by simpa using hI.wrl
  flag i := by
    by_cases hq : i = i0
    · subst hq; simpa using hMi0
    · simpa [Function.update_of_ne (show (Sum.inl i : Proc n 1) ≠ .inl i0 by simpa using hq),
        hMi i hq] using hI.flag i
  wflag := by simpa [hM0] using hI.wflag
  excl i h := by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne] at h
    by_cases hq : i = i0
    · subst hq; simpa using hex h
    · simpa [Function.update_of_ne (show (Sum.inl i : Proc n 1) ≠ .inl i0 by simpa using hq)]
        using hI.excl i h

lemma Inv.upd_writer {C : TCfg n} (hI : Inv C) (l' : Loc n)
    (pd : Option MutexOp) (M' : Option (Fin n) → ℕ)
    (hM0 : M' none = if wOn l' then 1 else 0) (hMi : ∀ i, M' (some i) = C.mem (some i))
    (hwr : isWr l' = true)
    (hpn : pd = none → l' = .rem ∨ l' = .cs)
    (hpl : pd = some .lock → l' ≠ .rem ∧ isExit l' = false)
    (hpu : pd = some .unlock → l' ≠ .cs ∧ isEntry l' = false)
    (hex : ∀ i, chk l' i → C.loc (.inl i) ≠ .cs ∧ C.loc (.inl i) ≠ .rExit) :
    Inv (n := n) { loc := Function.update C.loc wr l',
                   pend := Function.update C.pend wr pd, mem := M' } where
  idle q h := by
    by_cases hq : q = wr
    · subst hq; simp at h ⊢; exact hpn h
    · simp [Function.update_of_ne hq] at h ⊢; exact hI.idle q h
  lockL q h := by
    by_cases hq : q = wr
    · subst hq; simp at h ⊢; exact hpl h
    · simp [Function.update_of_ne hq] at h ⊢; exact hI.lockL q h
  unlockL q h := by
    by_cases hq : q = wr
    · subst hq; simp at h ⊢; exact hpu h
    · simp [Function.update_of_ne hq] at h ⊢; exact hI.unlockL q h
  rd i := by simpa using hI.rd i
  wrl := by simpa using hwr
  flag i := by simpa [hMi i] using hI.flag i
  wflag := by simpa using hM0
  excl i h := by simpa using hex i (by simpa using h)

lemma Inv.tau {C C' : TCfg n} {p : Proc n 1} (hI : Inv C)
    (h : (toyLock n).step C (.tau p) = some C') : Inv C' := by
  obtain ⟨hp, x, hx, rfl⟩ := step_tau' h
  clear h
  rcases p with i0 | j0
  · have hrd := hI.rd i0
    have hpe : C.pend = Function.update C.pend (.inl i0) (C.pend (.inl i0)) := by simp
    rw [hpe]; clear hpe
    have hL := hI.lockL (.inl i0)
    have hU := hI.unlockL (.inl i0)
    have hE := hI.excl i0
    have hF := hI.flag i0
    have hW := hI.wflag
    cases hl : C.loc (.inl i0) <;> rw [hl] at hx hrd hL hU hE hF <;>
      simp [tauEff, isRd] at hx hrd <;> subst hx <;>
      refine hI.upd_reader i0 _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [flagReg, flagOn, isRd, isExit, isEntry, hF] at hL hU hE ⊢
    all_goals first
      | done
      | assumption
      | (intro i hi; simp [hi])
      | (intro hc; have := chk_wOn hc; split_ifs <;> simp_all)
      | (split_ifs <;> simp_all [flagOn])
  · obtain rfl := fin_one j0
    have hrd := hI.wrl
    have hpe : C.pend = Function.update C.pend wr (C.pend wr) := by simp
    rw [hpe]; clear hpe
    have hL := hI.lockL wr
    have hU := hI.unlockL wr
    have hE := hI.excl
    have hW := hI.wflag
    cases hl : C.loc wr <;> rw [hl] at hx hrd hL hU hE hW <;>
      simp [tauEff, isWr] at hx hrd <;> subst hx
    · refine hI.upd_writer _ _ _ (by simp) (fun i => by simp) (by simp) (fun h => absurd h hp)
        (fun _ => by simp) (fun h => by simp [h, isEntry] at hU) ?_
      intro i hi; have := chk_wNext hi; simp at this
    · rename_i k
      simp only [wOn, ite_true] at hW
      refine hI.upd_writer _ _ _ ?_ (fun i => by simp) ?_ (fun h => absurd h hp)
        ?_ (fun h => by simp [h, isEntry] at hU) ?_
      · by_cases h0 : C.mem (some k) = 0
        · simp [h0, hW]
        · simp [h0, hW, wOn]
      · by_cases h0 : C.mem (some k) = 0
        · simp [h0]
        · simp [h0, isWr]
      · intro _
        by_cases h0 : C.mem (some k) = 0
        · simp [h0]
        · simp [h0, isExit]
      · intro i hi
        split_ifs at hi with h0
        · have hik := chk_wNext hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hik with h1 | h1
          · exact hE i h1
          · have hik : i = k := Fin.ext h1
            subst hik
            have hF := hI.flag i
            rw [h0] at hF
            constructor <;> intro hc <;> rw [hc] at hF <;> simp [flagOn] at hF
        · exact hE i hi
    · refine hI.upd_writer _ _ _ (by simp [wOn]) (fun i => by simp) (by simp [isWr])
        (fun h => absurd h hp) (fun h => by simp [h, isExit] at hL) (fun _ => by simp [isEntry]) ?_
      intro i hi; simp [chk] at hi

lemma Inv.inv {C C' : TCfg n} {p : Proc n 1} {o : MutexOp} (hI : Inv C)
    (h : (toyLock n).step C (.inv p o) = some C') : Inv C' := by
  obtain ⟨hp, rfl⟩ := step_inv' h
  clear h
  rcases p with i0 | j0
  · have hF := hI.flag i0
    have hE := hI.excl i0
    rcases hI.idle _ hp with hl | hl <;> rw [hl] at hF hE <;> cases o <;>
      refine hI.upd_reader i0 _ _ C.mem rfl (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp_all [toyInvoke, flagOn, isRd, isExit, isEntry]
  · obtain rfl := fin_one j0
    have hW := hI.wflag
    have hE := hI.excl
    rcases hI.idle _ hp with hl | hl <;> rw [hl] at hW hE <;> cases o <;>
      refine hI.upd_writer _ _ C.mem ?_ (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ <;>
      simp_all [toyInvoke, wOn, isWr, isExit, isEntry, chk]

lemma Inv.ret {C C' : TCfg n} {p : Proc n 1} {r : Unit} (hI : Inv C)
    (h : (toyLock n).step C (.ret p r) = some C') : Inv C' := by
  obtain ⟨hp, hl, rfl⟩ := step_ret' h
  clear h
  have hloc : C.loc = Function.update C.loc p (C.loc p) := by simp
  rcases p with i0 | j0
  · have hF := hI.flag i0
    have hE := hI.excl i0
    have hrd := hI.rd i0
    rw [hloc]
    exact hI.upd_reader i0 _ _ C.mem rfl (fun _ _ => rfl) hF hrd (fun _ => hl) (by simp)
      (by simp) hE
  · obtain rfl := fin_one j0
    rw [hloc]
    exact hI.upd_writer _ _ C.mem hI.wflag (fun _ => rfl) hI.wrl (fun _ => hl) (by simp)
      (by simp) hI.excl

lemma Inv.step {C C' : TCfg n} {ℓ : Label (Proc n 1) mutexObj} (hI : Inv C)
    (h : (toyLock n).step C ℓ = some C') : Inv C' := by
  cases ℓ with
  | inv p o => exact hI.inv h
  | tau p => exact hI.tau h
  | ret p r => exact hI.ret h

lemma inv_of_run {α : List (Label (Proc n 1) mutexObj)} {C : TCfg n}
    (h : (toyLock n).run α = some C) : Inv C :=
  (toyLock n).invariant_of_run Inv.init (fun _ _ _ hC hs => hC.step hs) h

lemma Inv.of_reachable {C : TCfg n} (h : (toyLock n).Reachable C) : Inv C := by
  obtain ⟨α, hα⟩ := h; exact inv_of_run hα

/-! ### Regions -/

/-- The region of a process, read off its pending operation and local state. -/
def regCfg (pd : Option MutexOp) (l : Loc n) : Region :=
  match pd with
  | none => if l = .cs then .cs else .rem
  | some .lock => .trying
  | some .unlock => .exiting

lemma clientWF_of_append {α : List (Label (Proc n 1) mutexObj)} {ℓ : Label (Proc n 1) mutexObj}
    (h : ClientWF (α ++ [ℓ])) : ClientWF α := by
  intro q hq
  apply h q
  rw [regionOf_append_singleton, hq]
  simp

lemma region_of_run {α : List (Label (Proc n 1) mutexObj)} {C : TCfg n}
    (h : (toyLock n).run α = some C) (hwf : ClientWF α) (q : Proc n 1) :
    regionOf α q = some (regCfg (C.pend q) (C.loc q)) := by
  induction α using List.reverseRecOn generalizing C q with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at h; subst h
    simp [regCfg, Impl.initCfg, toyLock]
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at h
    cases hα : (toyLock n).run α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some] at h
      have hI := inv_of_run hα
      have ih' := ih hα (clientWF_of_append hwf)
      have hwq := hwf q
      rw [regionOf_append_singleton] at hwq ⊢
      by_cases hq : ℓ.proc = q
      · simp only [hq, ↓reduceIte] at hwq ⊢
        rw [ih'] at hwq ⊢
        cases ℓ with
        | inv p o =>
          simp only [Label.proc] at hq; subst hq
          obtain ⟨hp, rfl⟩ := step_inv' h
          rw [hp] at hwq ⊢
          rcases hI.idle _ hp with hl | hl <;> cases o <;>
            simp_all [regCfg, Region.next]
        | tau p =>
          simp only [Label.proc] at hq; subst hq
          obtain ⟨hp, x, -, rfl⟩ := step_tau' h
          simp only [Option.bind_some, Region.next]
          obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
          rw [ho]; cases o <;> rfl
        | ret p r =>
          simp only [Label.proc] at hq; subst hq
          obtain ⟨hp, hl, rfl⟩ := step_ret' h
          obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
          rw [ho] at hwq ⊢
          cases o
          · have := (hI.lockL _ ho).1
            rcases hl with hl | hl
            · exact absurd hl this
            · simp [regCfg, Region.next, hl]
          · have := (hI.unlockL _ ho).1
            rcases hl with hl | hl
            · simp [regCfg, Region.next, hl]
            · exact absurd hl this
      · simp only [hq, ↓reduceIte] at hwq ⊢
        rw [ih', (Impl.step_other h hq).1, (Impl.step_other h hq).2]

lemma regCfg_eq_cs {pd : Option MutexOp} {l : Loc n} :
    regCfg pd l = .cs ↔ pd = none ∧ l = .cs := by
  rcases pd with _ | _ | _ <;> simp [regCfg]

/-! ### Mutual exclusion, bounded exit -/

/-- The toy lock satisfies Mutual Exclusion. -/
theorem toyLock_mutualExclusion : RWMutualExclusion (toyLock n) := by
  rintro α ⟨C, hC⟩ hwf j q hj hq
  obtain rfl := fin_one j
  have hI := inv_of_run hC
  unfold InCS at hj hq
  rw [region_of_run hC hwf, Option.some.injEq, regCfg_eq_cs] at hj hq
  rcases q with i | j'
  · have := (hI.excl i (by rw [hj.2]; trivial)).1
    exact absurd hq.2 this
  · rw [fin_one j']

lemma regCfg_eq_exiting {pd : Option MutexOp} {l : Loc n} :
    regCfg pd l = .exiting ↔ pd = some .unlock := by
  rcases pd with _ | _ | _ <;> simp only [regCfg] <;> (try split_ifs) <;> simp

lemma regCfg_eq_trying {pd : Option MutexOp} {l : Loc n} :
    regCfg pd l = .trying ↔ pd = some .lock := by
  rcases pd with _ | _ | _ <;> simp only [regCfg] <;> (try split_ifs) <;> simp

lemma regCfg_eq_rem {pd : Option MutexOp} {l : Loc n} :
    regCfg pd l = .rem ↔ pd = none ∧ l ≠ .cs := by
  rcases pd with _ | _ | _ <;> simp [regCfg]

lemma isTauOf_eq_true {p : Proc n 1} {ℓ : Label (Proc n 1) mutexObj} :
    isTauOf p ℓ = true ↔ ℓ = .tau p := by
  cases ℓ <;> simp [isTauOf]

/-- Bounding the number of internal steps of `p` by a potential. -/
lemma tauCount_le (p : Proc n 1) (G : TCfg n → Prop) (φ : TCfg n → ℕ)
    (Q : Label (Proc n 1) mutexObj → Prop)
    (hs : ∀ C C' ℓ, G C → Q ℓ → (toyLock n).step C ℓ = some C' →
      G C' ∧ φ C' + (if isTauOf p ℓ = true then 1 else 0) ≤ φ C) :
    ∀ (β : List (Label (Proc n 1) mutexObj)) (C C' : TCfg n), G C → (∀ ℓ ∈ β, Q ℓ) →
      (toyLock n).runFrom C β = some C' → tauCount p β ≤ φ C := by
  intro β
  induction β with
  | nil => intros; simp
  | cons ℓ β ih =>
    intro C C' hG hQ hrun
    simp only [Impl.runFrom_cons] at hrun
    cases h1 : (toyLock n).step C ℓ with
    | none => simp [h1] at hrun
    | some C₁ =>
      simp only [h1, Option.bind_some] at hrun
      obtain ⟨hG1, hφ⟩ := hs C C₁ ℓ hG (hQ ℓ List.mem_cons_self) h1
      have := ih C₁ C' hG1 (fun ℓ' h' => hQ ℓ' (List.mem_cons_of_mem _ h')) hrun
      simp only [tauCount, List.countP_cons] at this ⊢
      split_ifs at hφ ⊢ <;> omega

/-- The toy lock satisfies Bounded Exit (with bound `1`). -/
theorem toyLock_boundedExit : BoundedExit (toyLock n) := by
  rintro α p ⟨C, hC⟩ hwf hex
  rw [region_of_run hC hwf, Option.some.injEq, regCfg_eq_exiting] at hex
  refine ⟨1, fun β ⟨C', hC'⟩ hret => ?_⟩
  rw [Impl.run, Impl.runFrom_append] at hC'
  simp only [Impl.run] at hC
  rw [hC, Option.bind_some] at hC'
  refine le_trans (tauCount_le p (fun C => Inv C ∧ C.pend p = some .unlock)
    (fun C => if C.loc p = .rem then 0 else 1) (fun ℓ => ∀ r, ℓ ≠ .ret p r) ?_ β C C'
    ⟨inv_of_run hC, hex⟩ (fun ℓ hℓ r h => hret ⟨r, h ▸ hℓ⟩) hC') (by split_ifs <;> omega)
  rintro C₀ C₁ ℓ ⟨hI, hp⟩ hQ hs
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq
      exact absurd (step_inv' hs).1 (by simp [hp])
    | ret q r => simp only [Label.proc] at hq; subst hq; exact absurd rfl (hQ r)
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, x, hx, rfl⟩ := step_tau' hs
      have hU := hI.unlockL _ hp
      refine ⟨⟨hI.step hs, hp⟩, ?_⟩
      cases hl : C₀.loc q <;> rw [hl] at hx hU <;> simp [tauEff, isEntry] at hx hU <;>
        subst hx <;> simp [isTauOf]
  · have h1 := Impl.step_other hs hq
    have h2 : isTauOf p ℓ = false := by
      cases h : isTauOf p ℓ
      · rfl
      · rw [isTauOf_eq_true] at h; subst h; exact absurd rfl hq
    refine ⟨⟨hI.step hs, h1.2 ▸ hp⟩, ?_⟩
    simp [h1.1, h2]

/-! ### Concurrent entering -/

/-- Number of steps a reader needs to enter while the writer flag is `0`. -/
def ceφ : Loc n → ℕ
  | .r0 => 2
  | .r1 => 1
  | .r2 => 4
  | .r3 => 3
  | _ => 0

lemma isTauOf_of_ne {p : Proc n 1} {ℓ : Label (Proc n 1) mutexObj} (h : ℓ.proc ≠ p) :
    isTauOf p ℓ = false := by
  cases hc : isTauOf p ℓ
  · rfl
  · rw [isTauOf_eq_true] at hc; subst hc; exact absurd rfl h

/-- The toy lock satisfies Concurrent Entering (with bound `4`). -/
theorem toyLock_concurrentEntering : ConcurrentEntering (toyLock n) := by
  rintro α i ⟨C, hC⟩ hwf hw hi
  have hw0 := hw 0
  rw [region_of_run hC hwf, Option.some.injEq, regCfg_eq_rem] at hw0
  rw [region_of_run hC hwf, Option.some.injEq, regCfg_eq_trying] at hi
  have hI := inv_of_run hC
  have hwl : C.loc wr = .rem := by
    rcases hI.idle _ hw0.1 with h | h
    · exact h
    · exact absurd h hw0.2
  refine ⟨4, fun β ⟨C', hC'⟩ hleft hret => ?_⟩
  rw [Impl.run, Impl.runFrom_append] at hC'
  simp only [Impl.run] at hC
  rw [hC, Option.bind_some] at hC'
  refine le_trans (tauCount_le (.inl i)
    (fun C => Inv C ∧ C.pend (.inl i) = some .lock ∧ C.loc wr = .rem)
    (fun C => ceφ (C.loc (.inl i))) (fun ℓ => ℓ.proc.isLeft ∧ ∀ r, ℓ ≠ .ret (.inl i) r) ?_ β C C'
    ⟨hI, hi, hwl⟩ (fun ℓ hℓ => ⟨hleft ℓ hℓ, fun r h => hret ⟨r, h ▸ hℓ⟩⟩) hC') ?_
  · rintro C₀ C₁ ℓ ⟨hI, hp, hwl⟩ ⟨hQl, hQ⟩ hs
    have hwl' : C₁.loc wr = .rem := by
      have : ℓ.proc ≠ wr := by intro h; rw [h] at hQl; simp at hQl
      rw [(Impl.step_other hs this).1, hwl]
    by_cases hq : ℓ.proc = .inl i
    · cases ℓ with
      | inv q o =>
        simp only [Label.proc] at hq; subst hq
        exact absurd (step_inv' hs).1 (by simp [hp])
      | ret q r => simp only [Label.proc] at hq; subst hq; exact absurd rfl (hQ r)
      | tau q =>
        simp only [Label.proc] at hq; subst hq
        obtain ⟨-, x, hx, rfl⟩ := step_tau' hs
        have hL := hI.lockL _ hp
        have hrd := hI.rd i
        have hW := hI.wflag
        rw [hwl] at hW
        simp only [wOn] at hW
        refine ⟨⟨hI.step hs, hp, hwl'⟩, ?_⟩
        cases hl : C₀.loc (.inl i) <;> rw [hl] at hx hL hrd <;>
          simp [tauEff, isExit, isRd, hW] at hx hL hrd <;>
          subst hx <;> simp [isTauOf, ceφ]
    · have h1 := Impl.step_other hs hq
      refine ⟨⟨hI.step hs, h1.2 ▸ hp, hwl'⟩, ?_⟩
      simp [h1.1, isTauOf_of_ne hq]
  · cases C.loc (.inl i) <;> simp [ceφ]

/-! ### Deadlock freedom -/

section DF

variable {e : (toyLock n).InfExec}

lemma inv_cfg (e : (toyLock n).InfExec) (t : ℕ) : Inv (e.cfg t) :=
  Inv.of_reachable (e.reachable_cfg t)

lemma Inv.pend_ne {C : TCfg n} (hI : Inv C) {q : Proc n 1} (h1 : C.loc q ≠ .rem)
    (h2 : C.loc q ≠ .cs) : C.pend q ≠ none := fun h => by
  rcases hI.idle q h with h' | h' <;> contradiction

/-- No response from time `t0` on. -/
def NR (e : (toyLock n).InfExec) (t0 : ℕ) : Prop := ∀ s ≥ t0, ∀ p r, e.lbl s ≠ .ret p r

lemma lbl_tau {t0 : ℕ} (hNR : NR e t0) {s : ℕ} (hs : t0 ≤ s) {q : Proc n 1}
    (hq : (e.lbl s).proc = q) (hp : (e.cfg s).pend q ≠ none) : e.lbl s = .tau q := by
  have h := e.step_eq s
  cases hl : e.lbl s with
  | inv p o =>
    rw [hl] at hq h; simp only [Label.proc] at hq; subst hq
    exact absurd (step_inv' h).1 hp
  | ret p r => exact absurd hl (hNR s hs p r)
  | tau p => rw [hl] at hq; simp only [Label.proc] at hq; rw [hq]

lemma loc_tau {s : ℕ} {q : Proc n 1} (h : e.lbl s = .tau q) :
    ∃ x, tauEff q (e.cfg s).mem ((e.cfg s).loc q) = some x ∧ (e.cfg (s + 1)).loc q = x.2.2 ∧
      (e.cfg (s + 1)).pend = (e.cfg s).pend := by
  have hs := e.step_eq s
  rw [h] at hs
  obtain ⟨-, x, hx, h'⟩ := step_tau' hs
  exact ⟨x, hx, by rw [h']; simp, by rw [h']⟩

/-- A pending process in local state `rem` or `cs` responds at its next step. -/
lemma ret_of_idleLoc (hfair : e.Fair) {q : Proc n 1} {t : ℕ} (hp : (e.cfg t).pend q ≠ none)
    (hl : (e.cfg t).loc q = .rem ∨ (e.cfg t).loc q = .cs) :
    ∃ t' ≥ t, ∃ p r, e.lbl t' = .ret p r := by
  obtain ⟨t', ht', hq, hst, hloc, -⟩ := e.first_act hfair hp
  refine ⟨t', ht', ?_⟩
  cases hlb : e.lbl t' with
  | inv p o => rw [hlb] at hst; exact absurd hst id
  | ret p r => exact ⟨p, r, rfl⟩
  | tau p =>
    rw [hlb] at hq; simp only [Label.proc] at hq; subst hq
    obtain ⟨x, hx, -⟩ := loc_tau hlb
    rw [hloc] at hx; rcases hl with hl | hl <;> rw [hl] at hx <;> simp [tauEff] at hx

/-- A pending process in local state `rem`, `cs`, `rExit` or `wExit` responds within two
steps. -/
lemma ret_of_bad (hfair : e.Fair) {q : Proc n 1} {t : ℕ} (hp : (e.cfg t).pend q ≠ none)
    (hl : (e.cfg t).loc q = .rem ∨ (e.cfg t).loc q = .cs ∨ (e.cfg t).loc q = .rExit ∨
      (e.cfg t).loc q = .wExit) :
    ∃ t' ≥ t, ∃ p r, e.lbl t' = .ret p r := by
  rcases hl with hl | hl | hl
  · exact ret_of_idleLoc hfair hp (Or.inl hl)
  · exact ret_of_idleLoc hfair hp (Or.inr hl)
  obtain ⟨t', ht', hq, hst, hloc, hpend⟩ := e.first_act hfair hp
  cases hlb : e.lbl t' with
  | inv p o => rw [hlb] at hst; exact absurd hst id
  | ret p r => exact ⟨t', ht', p, r, hlb⟩
  | tau p =>
    rw [hlb] at hq; simp only [Label.proc] at hq; subst hq
    obtain ⟨x, hx, hx1, hx2⟩ := loc_tau hlb
    rw [hloc] at hx
    have hrem : (e.cfg (t' + 1)).loc p = .rem := by
      rcases hl with hl | hl <;> rw [hl] at hx <;> simp [tauEff] at hx <;> subst hx <;>
        exact hx1
    obtain ⟨t'', ht'', h⟩ := ret_of_idleLoc hfair (t := t' + 1) (by rw [hx2, hpend]; exact hp)
      (Or.inl hrem)
    exact ⟨t'', by omega, h⟩

lemma pend_persist {t0 : ℕ} (hNR : NR e t0) {q : Proc n 1} {t t' : ℕ} (ht : t0 ≤ t)
    (hp : (e.cfg t).pend q ≠ none) (htt : t ≤ t') : (e.cfg t').pend q ≠ none := by
  intro h
  obtain ⟨s, hs1, -, r, hr⟩ := e.exists_ret_between htt hp h
  exact hNR s (by omega) q r hr

lemma noIdleCS {t0 : ℕ} (hNR : NR e t0)
    (h0 : ∀ q, (e.cfg t0).pend q = none → (e.cfg t0).loc q ≠ .cs) :
    ∀ t ≥ t0, ∀ q, (e.cfg t).pend q = none → (e.cfg t).loc q ≠ .cs := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h0
  | succ t ht ih =>
    intro q hq
    have hs := e.step_eq t
    by_cases hpq : (e.lbl t).proc = q
    · by_cases hpt : (e.cfg t).pend q = none
      · cases hl : e.lbl t with
        | inv p o =>
          rw [hl] at hs hpq; simp only [Label.proc] at hpq; subst hpq
          obtain ⟨-, h'⟩ := step_inv' hs
          rw [h'] at hq; simp at hq
        | ret p r => exact absurd hl (hNR t ht p r)
        | tau p =>
          rw [hl] at hs hpq; simp only [Label.proc] at hpq; subst hpq
          exact absurd hpt (step_tau' hs).1
      · obtain ⟨x, -, -, hx⟩ := loc_tau (lbl_tau hNR ht hpq hpt)
        rw [hx] at hq
        exact absurd hq hpt
    · have h1 := Impl.step_other hs hpq
      rw [h1.1]; rw [h1.2] at hq; exact ih q hq

lemma loc_succ_of_not_step {s : ℕ} {q : Proc n 1} (hp : (e.cfg s).pend q ≠ none)
    (h : ¬((e.lbl s).proc = q ∧ (e.lbl s).IsStep)) : (e.cfg (s + 1)).loc q = (e.cfg s).loc q := by
  have hs := e.step_eq s
  by_cases hq : (e.lbl s).proc = q
  · cases hl : e.lbl s with
    | inv p o =>
      rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
      exact absurd (step_inv' hs).1 hp
    | ret p r => rw [hl] at h; exact absurd ⟨by rw [← hl]; exact hq, trivial⟩ h
    | tau p => rw [hl] at h; exact absurd ⟨by rw [← hl]; exact hq, trivial⟩ h
  · exact (Impl.step_other hs hq).1

/-- The hypotheses of the deadlock-freedom argument: fairness, no response from `t0` on, and
nobody idle in the critical section at `t0`. -/
structure DFHyp (e : (toyLock n).InfExec) (t0 : ℕ) : Prop where
  fair : e.Fair
  nr : NR e t0
  idle : ∀ t ≥ t0, ∀ q, (e.cfg t).pend q = none → (e.cfg t).loc q ≠ .cs

variable {t0 : ℕ}

lemma DFHyp.idle_rem (H : DFHyp e t0) {t : ℕ} (ht : t0 ≤ t) {q : Proc n 1}
    (hq : (e.cfg t).pend q = none) : (e.cfg t).loc q = .rem := by
  rcases (inv_cfg e t).idle q hq with h | h
  · exact h
  · exact absurd h (H.idle t ht q hq)

lemma DFHyp.not_bad (H : DFHyp e t0) {t : ℕ} (ht : t0 ≤ t) {q : Proc n 1}
    (hp : (e.cfg t).pend q ≠ none)
    (hl : (e.cfg t).loc q = .rem ∨ (e.cfg t).loc q = .cs ∨ (e.cfg t).loc q = .rExit ∨
      (e.cfg t).loc q = .wExit) : False := by
  obtain ⟨t', ht', p, r, h⟩ := ret_of_bad H.fair hp hl
  exact H.nr t' (by omega) p r h

/-- If the writer stays idle, a pending reader enters: contradiction. -/
lemma DFHyp.reader_false (H : DFHyp e t0) {i : Fin n} (hp : (e.cfg t0).pend (.inl i) ≠ none)
    (hw : ∀ t ≥ t0, (e.cfg t).pend wr = none) : False := by
  have hW : ∀ t ≥ t0, (e.cfg t).mem none = 0 := by
    intro t ht
    have := (inv_cfg e t).wflag
    rw [H.idle_rem ht (hw t ht)] at this
    simpa [wOn] using this
  have hpp : ∀ t ≥ t0, (e.cfg t).pend (.inl i) ≠ none := fun t ht =>
    pend_persist H.nr le_rfl hp ht
  obtain ⟨t', ht', hg⟩ := e.exists_good (.inl i) (fun t => isEntry ((e.cfg t).loc (.inl i)) = false)
    (fun t => ceφ ((e.cfg t).loc (.inl i))) t0
    (fun t ht _ => H.fair _ t (hpp t ht))
    (fun t ht hg hq hst => by
      have hτ := lbl_tau H.nr ht hq (hpp t ht)
      obtain ⟨x, hx, hx1, -⟩ := loc_tau hτ
      simp only [hx1]
      have hrd := (inv_cfg e t).rd i
      have hW' := hW t ht
      cases hl : (e.cfg t).loc (.inl i) <;> rw [hl] at hx hrd hg <;>
        simp [tauEff, isRd, isEntry, hW'] at hx hrd hg <;> subst hx <;> simp [ceφ, isEntry])
    (fun t ht _ hns => Or.inr (by rw [loc_succ_of_not_step (hpp t ht) hns]))
  have hrd := (inv_cfg e t').rd i
  apply H.not_bad ht' (hpp t' ht')
  cases hl : (e.cfg t').loc (.inl i) <;> rw [hl] at hg hrd <;> simp [isEntry, isRd] at hg hrd ⊢

/-- Potential of a reader while the writer flag is `1`: it reaches `r3`. -/
def rdφ : Loc n → ℕ
  | .rExit => 5
  | .rem => 4
  | .r0 => 3
  | .r1 => 2
  | .r2 => 1
  | _ => 0

/-- While the writer is at `wScan k` (from `t ≥ t0` on), it eventually reads `flag[k] = 0`. -/
lemma DFHyp.scan_progress (H : DFHyp e t0) {t : ℕ} {k : Fin n} (ht : t0 ≤ t)
    (hl : (e.cfg t).loc wr = .wScan k) : ∃ s ≥ t, (e.cfg (s + 1)).loc wr = wNext (k.1 + 1) := by
  by_contra Hc
  push Not at Hc
  -- the writer stays at `wScan k`
  have hstay : ∀ s ≥ t, (e.cfg s).loc wr = .wScan k := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact hl
    | succ s hs ih =>
      have hp := (inv_cfg e s).pend_ne (q := wr) (by simp [ih]) (by simp [ih])
      by_cases hq : (e.lbl s).proc = wr
      · obtain ⟨x, hx, hx1, -⟩ := loc_tau (lbl_tau H.nr (by omega) hq hp)
        rw [ih] at hx; simp only [tauEff, Option.some.injEq] at hx; subst hx
        rw [hx1]; simp only
        split_ifs with h0
        · exact absurd (by rw [hx1]; simp [h0]) (Hc s hs)
        · rfl
      · rw [(Impl.step_other (e.step_eq s) hq).1, ih]
  have hWp : ∀ s ≥ t, (e.cfg s).pend wr ≠ none := fun s hs =>
    (inv_cfg e s).pend_ne (q := wr) (by simp [hstay s hs]) (by simp [hstay s hs])
  have hW : ∀ s ≥ t, (e.cfg s).mem none = 1 := by
    intro s hs
    have := (inv_cfg e s).wflag
    rw [hstay s hs] at this
    simpa [wOn] using this
  -- whenever the writer steps, `flag[k] ≠ 0`
  have hflag : ∀ s ≥ t, (e.lbl s).proc = wr → (e.lbl s).IsStep → (e.cfg s).mem (some k) ≠ 0 := by
    intro s hs hq _ h0
    obtain ⟨x, hx, hx1, -⟩ := loc_tau (lbl_tau H.nr (by omega) hq (hWp s hs))
    rw [hstay s hs] at hx; simp only [tauEff, Option.some.injEq] at hx; subst hx
    exact Hc s hs (by rw [hx1]; simp [h0])
  -- phase 1: reader `k` is pending at some point
  obtain ⟨s1, hs1, hq1, hst1⟩ := H.fair wr t (hWp t le_rfl)
  have hk1 : (e.cfg s1).pend (.inl k) ≠ none := by
    intro hn
    have hF := (inv_cfg e s1).flag k
    rw [H.idle_rem (by omega) hn] at hF
    exact hflag s1 hs1 hq1 hst1 (by simpa [flagOn] using hF)
  have hkp : ∀ s ≥ s1, (e.cfg s).pend (.inl k) ≠ none := fun s hs =>
    pend_persist H.nr (by omega) hk1 hs
  -- phase 2: reader `k` reaches `r3`
  obtain ⟨s2, hs2, hr3⟩ := e.exists_good (.inl k) (fun s => (e.cfg s).loc (.inl k) = .r3)
    (fun s => rdφ ((e.cfg s).loc (.inl k))) s1
    (fun s hs _ => H.fair _ s (hkp s hs))
    (fun s hs hg hq hst => by
      have hτ := lbl_tau H.nr (by omega) hq (hkp s hs)
      obtain ⟨x, hx, hx1, -⟩ := loc_tau hτ
      simp only [hx1]
      have hrd := (inv_cfg e s).rd k
      have hW' := hW s (by omega)
      cases hl : (e.cfg s).loc (.inl k) <;> rw [hl] at hx hrd hg <;>
        simp [tauEff, isRd, hW'] at hx hrd hg <;> subst hx <;> simp [rdφ])
    (fun s hs _ hns => Or.inr (by rw [loc_succ_of_not_step (hkp s hs) hns]))
  -- phase 3: reader `k` stays at `r3`
  have hr3' : ∀ s ≥ s2, (e.cfg s).loc (.inl k) = .r3 := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact hr3
    | succ s hs ih =>
      by_cases hq : (e.lbl s).proc = .inl k
      · obtain ⟨x, hx, hx1, -⟩ := loc_tau (lbl_tau H.nr (by omega) hq (hkp s (by omega)))
        rw [ih] at hx; simp only [tauEff, Option.some.injEq] at hx; subst hx
        rw [hx1]; simp [hW s (by omega)]
      · rw [(Impl.step_other (e.step_eq s) hq).1, ih]
  -- phase 4: the writer reads `flag[k] = 0`
  obtain ⟨s3, hs3, hq3, hst3⟩ := H.fair wr s2 (hWp s2 (by omega))
  have hF := (inv_cfg e s3).flag k
  rw [hr3' s3 hs3] at hF
  exact hflag s3 (by omega) hq3 hst3 (by simpa [flagOn] using hF)

/-- Progress index of the writer's entry section. -/
def wIdx : Loc n → ℕ
  | .w0 => 0
  | .wScan k => k.1 + 1
  | _ => n + 1

lemma wIdx_wNext {k : ℕ} (hk : k ≤ n) : k + 1 ≤ wIdx (wNext (n := n) k) := by
  unfold wNext; split_ifs <;> simp [wIdx]; omega

/-- A pending writer eventually enters: contradiction. -/
lemma DFHyp.writer_false (H : DFHyp e t0) {t : ℕ} (ht : t0 ≤ t)
    (hp : (e.cfg t).pend wr ≠ none) : False := by
  suffices ∀ m t, t0 ≤ t → (e.cfg t).pend wr ≠ none → n + 1 - wIdx ((e.cfg t).loc wr) = m →
      False from this _ t ht hp rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t ht hp hm
    have hwr := (inv_cfg e t).wrl
    cases hl : (e.cfg t).loc wr with
    | rem => exact H.not_bad ht hp (Or.inl hl)
    | cs => exact H.not_bad ht hp (Or.inr (Or.inl hl))
    | wExit => exact H.not_bad ht hp (Or.inr (Or.inr (Or.inr hl)))
    | r0 | r1 | r2 | r3 | rExit => rw [hl] at hwr; simp [isWr] at hwr
    | w0 =>
      rw [hl] at hm; simp only [wIdx] at hm
      obtain ⟨t', ht', hq, hst, hloc, hpend⟩ := e.first_act H.fair hp
      obtain ⟨x, hx, hx1, -⟩ := loc_tau (lbl_tau H.nr (by omega) hq (by rw [hpend]; exact hp))
      rw [hloc, hl] at hx; simp only [tauEff, Option.some.injEq] at hx; subst hx
      have := wIdx_wNext (n := n) (Nat.zero_le n)
      exact ih (n + 1 - wIdx ((e.cfg (t' + 1)).loc wr)) (by rw [hx1]; dsimp only; omega) (t' + 1)
        (by omega) (pend_persist H.nr ht hp (by omega)) rfl
    | wScan k =>
      rw [hl] at hm; simp only [wIdx] at hm
      obtain ⟨s, hs, hs1⟩ := H.scan_progress ht hl
      have := wIdx_wNext (n := n) (k := k.1 + 1) k.2
      exact ih (n + 1 - wIdx ((e.cfg (s + 1)).loc wr)) (by rw [hs1]; omega) (s + 1) (by omega)
        (pend_persist H.nr ht hp (by omega)) rfl

end DF

/-- The toy lock is deadlock-free. -/
theorem toyLock_deadlockFree : (toyLock n).DeadlockFree := by
  intro e hwf hfair t ⟨p, hp⟩ hcs
  by_contra hc
  push Not at hc
  have hNR : NR e t := fun s hs q r h => hc s hs q r h
  have h0 : ∀ q, (e.cfg t).pend q = none → (e.cfg t).loc q ≠ .cs := by
    intro q hq hl
    apply hcs q
    unfold InCS
    rw [region_of_run (e.run_pre t) (hwf t), hq, hl]
    rfl
  have H : DFHyp e t := ⟨hfair, hNR, noIdleCS hNR h0⟩
  rcases p with i | j
  · by_cases hw : ∃ t' ≥ t, (e.cfg t').pend wr ≠ none
    · obtain ⟨t', ht', hw⟩ := hw
      exact H.writer_false ht' hw
    · push Not at hw
      exact H.reader_false hp hw
  · obtain rfl := fin_one j
    exact H.writer_false le_rfl hp

/-- **Non-vacuity of Theorem 5.** The toy lock allows all operations and satisfies Mutual
Exclusion, Bounded Exit, Concurrent Entering and Deadlock Freedom, for every number `n` of
readers. -/
theorem toyLock_spec (n : ℕ) :
    (∀ p o, (toyLock n).allowed p o) ∧ RWMutualExclusion (toyLock n) ∧
      BoundedExit (toyLock n) ∧ ConcurrentEntering (toyLock n) ∧ (toyLock n).DeadlockFree :=
  ⟨fun _ _ => trivial, toyLock_mutualExclusion, toyLock_boundedExit,
    toyLock_concurrentEntering, toyLock_deadlockFree⟩

/-- The hypotheses of Theorem 5 other than the RMR bounds are jointly satisfiable for every
number of readers (with one writer, from read/write registers). -/
example (n : ℕ) : ∃ (ι V L : Type) (_ : DecidableEq ι) (_ : DecidableEq V) (v₀ : V)
    (I : RWAlg n 1 ι V v₀ L), (∀ p o, I.allowed p o) ∧ RWMutualExclusion I ∧ BoundedExit I ∧
      I.DeadlockFree ∧ ConcurrentEntering I :=
  ⟨Option (Fin n), ℕ, Loc n, inferInstance, inferInstance, 0, toyLock n,
    (toyLock_spec n).1, (toyLock_spec n).2.1, (toyLock_spec n).2.2.1, (toyLock_spec n).2.2.2.2,
    (toyLock_spec n).2.2.2.1⟩

end Podc.RWLockRMRTradeoff.NonVacuity
