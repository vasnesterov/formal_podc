import Papers.PODC2019.AnonymousMutex.Alg2Resign
import Cslib.Foundations.Data.Nat.Descent

/-!
# Algorithm 2: the endgame of the deadlock-freedom proof

Two final steps of the proof of Theorem 4 (deadlock-freedom).

* `endgame`: if some process `q` stays forever in the first two loops of `lock()` (lines 2–3)
  and keeps a register `y₀`, then the execution cannot continue without a completion. Indeed,
  every scan of lines 8–10 started later reads `y₀ ≠ ⊥` and fails, so every process eventually
  either owns nothing forever or stays in the first two loops forever; the memory then
  stabilizes, is full (otherwise `q` would fill a `⊥` register), and every owner decides
  (line 6) on the same full view. Since nobody withdraws nor enters, all owners own the same
  number `c ≤ m/2` of registers, so the number `k ≥ 2` of owners divides `m`, contradicting
  `m ∈ M(n)`.
* `zero_case`: if after some time nobody owns any register, the memory is all `⊥` and a pending
  process eventually performs a successful `compare&swap`, a contradiction.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P]
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

namespace Endgame

/-- Program counters of the first two loops of `lock()` (lines 2–3). -/
def CasRead (c : PC) : Prop := (∃ i, c = .cas i) ∨ (∃ i, c = .read i)

lemma busy_of_casRead {c : PC} (h : CasRead c) : Busy c := by
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> trivial

lemma cas0_of_afterRead {s : St Id m} {w : Fin m → Option Id} (h : CasRead (afterRead s w).pc) :
    (afterRead s w).pc = .cas 0 := by
  rcases afterRead_pc s w with ⟨j, h'⟩ | h' | h' | h'
  · rw [h'] at h; simp [CasRead] at h
  · rw [h'] at h; simp [CasRead] at h
  · rw [h'] at h; simp [CasRead] at h
  · exact h'

lemma afterRead_casRead {s : St Id m} {w : Fin m → Option Id} (h : CasRead (afterRead s w).pc) :
    ¬ owned w s.me < mostPresent w ∧ ¬ m < 2 * owned w s.me := by
  unfold afterRead at h
  split_ifs at h with h1 h2
  · unfold wrFrom at h; split_ifs at h <;> simp [CasRead] at h
  · simp [CasRead] at h
  · exact ⟨h1, h2⟩

/-- Distance measures used with `Hyp.eventually_loc`. -/
def wrDist (m : ℕ) : PC → ℕ
  | .wr j => m - j
  | _ => 0

def waitDist (m : ℕ) : PC → ℕ
  | .wait j _ => m - j
  | _ => 0

def readDist (m : ℕ) : PC → ℕ
  | .read j => m - j
  | _ => 0

def scanDist (m : ℕ) : PC → ℕ
  | .cas i => 2 * m - i
  | .read i => m - i
  | _ => 0

def casDist (m k : ℕ) : PC → ℕ
  | .cas i => if i ≤ k then k - i else (m - i) + m + k + 1
  | .read i => (m - i) + k + 1
  | _ => 0

def zDist (m : ℕ) : PC → ℕ
  | .read i => 3 * m - i
  | .wait i ab => if ab then m - i else 2 * m - i
  | _ => 0

/-! ### Finite combinatorics -/

lemma card_comp_perm (σ : Equiv.Perm (Fin m)) (g : Fin m → Option Id) (a : Option Id) :
    (Finset.univ.filter (fun x => g (σ x) = a)).card =
      (Finset.univ.filter (fun y => g y = a)).card := by
  refine Finset.card_bij (fun x _ => σ x) ?_ ?_ ?_
  · intro x hx; simpa using hx
  · intro x _ y _ h; exact σ.injective h
  · intro y hy
    refine ⟨σ.symm y, ?_, by simp⟩
    simpa using hy

/-- The counting argument: a full memory in which every owner sees (through its permutation)
`owned ≥ most_present` and `owned ≤ m/2` contradicts `m ∈ M(n)`. -/
lemma final_contra [Fintype P] (hid : Function.Injective ids) (hm : 0 < m)
    (hM : m ∈ M (Fintype.card P)) (M₀ : Fin m → Option Id) (hval : ∀ y, ∃ r, M₀ y = some (ids r))
    (hdec : ∀ r, (∃ y, M₀ y = some (ids r)) →
      ¬ owned (fun x => M₀ (π r x)) (ids r) < mostPresent (fun x => M₀ (π r x)) ∧
      ¬ m < 2 * owned (fun x => M₀ (π r x)) (ids r)) : False := by
  set cnt : P → ℕ := fun r => (Finset.univ.filter (fun y => M₀ y = some (ids r))).card with hcnt
  have howned : ∀ r a, owned (fun x => M₀ (π r x)) a =
      (Finset.univ.filter (fun y => M₀ y = some a)).card :=
    fun r a => card_comp_perm (π r) M₀ (some a)
  have hmp : ∀ r r', (∃ y, M₀ y = some (ids r')) → cnt r' ≤ mostPresent (fun x => M₀ (π r x)) := by
    rintro r r' ⟨y, hy⟩
    unfold mostPresent
    have := Finset.le_sup (f := fun x => if M₀ (π r x) = none then 0 else
      (Finset.univ.filter (fun y' => M₀ (π r y') = M₀ (π r x))).card)
      (Finset.mem_univ ((π r).symm y))
    simp only [Equiv.apply_symm_apply, hy, reduceCtorEq, ite_false] at this
    refine le_trans ?_ this
    exact (card_comp_perm (π r) M₀ (some (ids r'))).ge
  have hle : ∀ r r', (∃ y, M₀ y = some (ids r)) → (∃ y, M₀ y = some (ids r')) →
      cnt r' ≤ cnt r := by
    intro r r' hr hr'
    have h1 := (hdec r hr).1
    rw [not_lt, howned] at h1
    exact (hmp r r' hr').trans h1
  set A := Finset.univ.filter (fun r : P => ∃ y, M₀ y = some (ids r)) with hA
  obtain ⟨r₀, hr₀⟩ := hval ⟨0, hm⟩
  have hconst : ∀ r ∈ A, cnt r = cnt r₀ := by
    intro r hr
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact le_antisymm (hle r₀ r ⟨_, hr₀⟩ hr) (hle r r₀ hr ⟨_, hr₀⟩)
  have hcover : (Finset.univ : Finset (Fin m)) =
      A.biUnion (fun r => Finset.univ.filter (fun y => M₀ y = some (ids r))) := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff, hA]
    obtain ⟨r, hr⟩ := hval y
    exact ⟨r, ⟨y, hr⟩, hr⟩
  have hdisj : (A : Set P).PairwiseDisjoint
      (fun r => Finset.univ.filter (fun y => M₀ y = some (ids r))) := by
    intro r _ r' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2
    exact hne (hid (Option.some.inj h2))
  have hsum : m = A.card * cnt r₀ := by
    have := Finset.card_biUnion hdisj
    rw [← hcover, Finset.card_univ, Fintype.card_fin] at this
    rw [this, Finset.sum_const_nat hconst]
  have hpos : 1 ≤ cnt r₀ := Finset.card_pos.2 ⟨⟨0, hm⟩, by simp [hr₀]⟩
  have h2 := (hdec r₀ ⟨_, hr₀⟩).2
  rw [not_lt, howned] at h2
  have hA2 : 2 ≤ A.card := by
    by_contra hc
    have h1 : A.card ≤ 1 := by omega
    have : m ≤ cnt r₀ := by
      rw [hsum]; simpa using Nat.mul_le_mul_right (cnt r₀) h1
    have : 2 * cnt r₀ ≤ m := h2
    omega
  have hAP : A.card ≤ Fintype.card P := Finset.card_le_univ A
  have hcop : Nat.Coprime A.card m := hM A.card (by omega) hAP
  have := Nat.Coprime.eq_one_of_dvd hcop ⟨cnt r₀, hsum⟩
  omega

/-! ### Execution lemmas -/

section Exec

variable {e : ((alg2 Id m).impl ids π).InfExec} {t₀ : ℕ}

lemma not_step_of_ne (H : Hyp e t₀) {t : ℕ} (ht : t₀ ≤ t) {p : P} (hl : e.lbl t ≠ .tau p) :
    ¬ ((e.lbl t).proc = p ∧ (e.lbl t).IsStep) := by
  rintro ⟨hproc, hst⟩
  cases h : e.lbl t with
  | inv r o => rw [h] at hst; exact hst
  | ret r o => exact H.noret t ht r o h
  | tau r => rw [h] at hproc; simp only [Label.proc] at hproc; rw [hproc] at h; exact hl h

/-- A property of the local state of a pending process preserved by its own steps holds
forever. -/
lemma loc_forever (H : Hyp e t₀) {t : ℕ} (ht : t₀ ≤ t) {p : P} (hpend : (e.cfg t).pend p ≠ none)
    (Q : St Id m → Prop) (h0 : Q ((e.cfg t).loc p))
    (hstep : ∀ t' ≥ t, Q ((e.cfg t').loc p) → e.lbl t' = .tau p → Q ((e.cfg (t' + 1)).loc p)) :
    ∀ t' ≥ t, Q ((e.cfg t').loc p) := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => exact h0
  | succ t' ht' ih =>
    by_cases hl : e.lbl t' = .tau p
    · exact hstep t' ht' ih hl
    · have hp' : (e.cfg t').pend p ≠ none := by
        rw [pend_persist e t₀ H.noret ht hpend t' ht']; exact hpend
      rw [loc_of_not_step e hp' (not_step_of_ne H (by omega) hl)]
      exact ih

/-- The next internal step of a pending process starts from its current local state. -/
lemma next_tau (H : Hyp e t₀) {t : ℕ} (ht : t₀ ≤ t) {p : P} (hpend : (e.cfg t).pend p ≠ none) :
    ∃ t₂ ≥ t, e.lbl t₂ = .tau p ∧ (e.cfg t₂).loc p = (e.cfg t).loc p := by
  classical
  have hex : ∃ t₂, t ≤ t₂ ∧ e.lbl t₂ = .tau p := by
    obtain ⟨t₂, h1, h2⟩ := H.tau ht hpend t le_rfl
    exact ⟨t₂, h1, h2⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h1, h2, ?_⟩
  have key : ∀ s, t ≤ s → s ≤ Nat.find hex → (e.cfg s).loc p = (e.cfg t).loc p := by
    intro s hs1
    induction s, hs1 using Nat.le_induction with
    | base => intro _; rfl
    | succ s hs ih =>
      intro hs2
      have hne : e.lbl s ≠ .tau p := fun h => Nat.find_min hex (show s < Nat.find hex by omega) ⟨hs, h⟩
      have hp' : (e.cfg s).pend p ≠ none := by
        rw [pend_persist e t₀ H.noret ht hpend s hs]; exact hpend
      rw [loc_of_not_step e hp' (not_step_of_ne H (by omega) hne)]
      exact ih (by omega)
  exact key _ h1 le_rfl

variable (hid : Function.Injective ids) (hm : 0 < m)
include hid hm

lemma step_cas (H : Hyp e t₀) {t : ℕ} {p : P} {i : ℕ} (hl : e.lbl t = .tau p)
    (hpc : ((e.cfg t).loc p).pc = .cas i) :
    ∃ hi : i < m, (e.cfg (t + 1)).loc p =
      (if i + 1 < m then { (e.cfg t).loc p with pc := .cas (i + 1) }
       else { (e.cfg t).loc p with pc := .read 0 }) ∧
      (e.cfg (t + 1)).mem () = Function.update ((e.cfg t).mem ()) (π p ⟨i, hi⟩)
        (if (e.cfg t).mem () (π p ⟨i, hi⟩) = none then some (ids p)
         else (e.cfg t).mem () (π p ⟨i, hi⟩)) := by
  obtain ⟨-, x, f, k, hact, hloc, hmem, -⟩ := tau_step e hl
  have hL := H.locInv hid hm t p
  have hi : i < m := by have := hL.2; rw [hpc] at this; exact this
  rw [act_cas hpc hi] at hact
  simp only [SymAction.rmw.injEq] at hact
  obtain ⟨rfl, rfl, rfl⟩ := hact
  refine ⟨hi, hloc, ?_⟩
  rw [hmem]; simp only [hL.1]

lemma step_read (H : Hyp e t₀) {t : ℕ} {p : P} {i : ℕ} (hl : e.lbl t = .tau p)
    (hpc : ((e.cfg t).loc p).pc = .read i) :
    ∃ hi : i < m, (e.cfg (t + 1)).mem () = (e.cfg t).mem () ∧
      (e.cfg (t + 1)).loc p =
        (if i + 1 < m then { (e.cfg t).loc p with
            view := Function.update ((e.cfg t).loc p).view ⟨i, hi⟩ ((e.cfg t).mem () (π p ⟨i, hi⟩)),
            pc := .read (i + 1) }
         else afterRead ((e.cfg t).loc p)
          (Function.update ((e.cfg t).loc p).view ⟨i, hi⟩ ((e.cfg t).mem () (π p ⟨i, hi⟩)))) := by
  obtain ⟨-, x, f, k, hact, hloc, hmem, -⟩ := tau_step e hl
  have hi : i < m := by have := (H.locInv hid hm t p).2; rw [hpc] at this; exact this.1
  rw [act_read hpc hi] at hact
  simp only [SymAction.rmw.injEq] at hact
  obtain ⟨rfl, rfl, rfl⟩ := hact
  exact ⟨hi, by rw [hmem]; simp, hloc⟩

lemma step_wait (H : Hyp e t₀) {t : ℕ} {p : P} {i : ℕ} {ab : Bool} (hl : e.lbl t = .tau p)
    (hpc : ((e.cfg t).loc p).pc = .wait i ab) :
    ∃ hi : i < m, (e.cfg (t + 1)).mem () = (e.cfg t).mem () ∧
      (e.cfg (t + 1)).loc p =
        (if i + 1 < m then
          { (e.cfg t).loc p with pc := .wait (i + 1) (ab && (e.cfg t).mem () (π p ⟨i, hi⟩) == none) }
        else if ab && (e.cfg t).mem () (π p ⟨i, hi⟩) == none then { (e.cfg t).loc p with pc := .cas 0 }
        else { (e.cfg t).loc p with pc := .wait 0 true }) := by
  obtain ⟨-, x, f, k, hact, hloc, hmem, -⟩ := tau_step e hl
  have hi : i < m := by have := (H.locInv hid hm t p).2; rw [hpc] at this; exact this.1
  rw [act_wait hpc hi] at hact
  simp only [SymAction.rmw.injEq] at hact
  obtain ⟨rfl, rfl, rfl⟩ := hact
  exact ⟨hi, by rw [hmem]; simp, hloc⟩

lemma step_wr (H : Hyp e t₀) {t : ℕ} {p : P} {i : ℕ} (hl : e.lbl t = .tau p)
    (hpc : ((e.cfg t).loc p).pc = .wr i) :
    i < m ∧ (e.cfg (t + 1)).loc p = wrFrom ((e.cfg t).loc p) (i + 1) := by
  obtain ⟨-, x, f, k, hact, hloc, -, -⟩ := tau_step e hl
  have hL := (H.locInv hid hm t p).2
  rw [hpc] at hL
  obtain ⟨hi, -⟩ := hL
  rw [act_wr hpc hi] at hact
  simp only [SymAction.rmw.injEq] at hact
  obtain ⟨rfl, rfl, rfl⟩ := hact
  exact ⟨hi, hloc⟩

lemma own_nonempty_of_wr (H : Hyp e t₀) {t : ℕ} {p : P} {j : ℕ}
    (hpc : ((e.cfg t).loc p).pc = .wr j) : (own ids (e.cfg t) p).Nonempty := by
  have hL := (H.locInv hid hm t p).2
  rw [hpc] at hL
  obtain ⟨hj, hv, hown⟩ := hL
  refine ⟨π p ⟨j, hj⟩, ?_⟩
  simp only [own, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hown _).2 ⟨⟨j, hj⟩, le_rfl, hv, rfl⟩

/-- If nobody erases, non-`⊥` registers keep their values. -/
lemma mem_step_nonbot (H : Hyp e t₀) {t : ℕ} (ht : t₀ ≤ t)
    (hnwr : ∀ p j, e.lbl t = .tau p → ((e.cfg t).loc p).pc ≠ .wr j) (y : Fin m)
    (hy : (e.cfg t).mem () y ≠ none) : (e.cfg (t + 1)).mem () y = (e.cfg t).mem () y := by
  have hstep := e.step_eq t
  cases hl : e.lbl t with
  | inv r o =>
    rw [hl] at hstep
    obtain ⟨-, hC⟩ := SymAlg.impl_step_inv_cases hstep
    rw [hC]
  | ret r o => exact absurd hl (H.noret t ht r o)
  | tau p =>
    have hb := H.busy_of_tau hid hm ht hl
    cases hpc : ((e.cfg t).loc p).pc with
    | cas i =>
      obtain ⟨hi, -, hmem⟩ := step_cas hid hm H hl hpc
      rw [hmem, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; exact absurd h2 hy
      · subst h1; rfl
      · rfl
    | read i => obtain ⟨hi, hmem, -⟩ := step_read hid hm H hl hpc; rw [hmem]
    | wait i ab => obtain ⟨hi, hmem, -⟩ := step_wait hid hm H hl hpc; rw [hmem]
    | wr j => exact absurd hpc (hnwr p j hl)
    | _ => rw [hpc] at hb; exact absurd hb id

/-! ### Stuck waiting processes -/

/-- `r` waits and cannot pass the register `y₀` in its current scan. -/
def WaitInv (π : P → Equiv.Perm (Fin m)) (y₀ : Fin m) (r : P) (s : St Id m) : Prop :=
  ∃ j ab, s.pc = .wait j ab ∧ (ab = false ∨ j ≤ ((π r).symm y₀).val)

/-- `r` erases (line 7) or waits without being able to pass `y₀`. -/
def StuckInv (π : P → Equiv.Perm (Fin m)) (y₀ : Fin m) (r : P) (s : St Id m) : Prop :=
  (∃ j, s.pc = .wr j) ∨ WaitInv π y₀ r s

omit hid hm in
lemma busy_of_stuck {y₀ : Fin m} {r : P} {s : St Id m} (h : StuckInv π y₀ r s) : Busy s.pc := by
  rcases h with ⟨j, hpc⟩ | ⟨j, ab, hpc, -⟩ <;> rw [hpc] <;> trivial

variable (H : Hyp e t₀) {q : P} {y₀ : Fin m} {t : ℕ}
  (hyq : ∀ t' ≥ t, (e.cfg t').mem () y₀ = some (ids q))
include hid hm H hyq

lemma waitInv_step {r : P} {t' : ℕ} (ht' : t ≤ t') (hl : e.lbl t' = .tau r)
    (hW : WaitInv π y₀ r ((e.cfg t').loc r)) : WaitInv π y₀ r ((e.cfg (t' + 1)).loc r) := by
  obtain ⟨j, ab, hpc, hab⟩ := hW
  obtain ⟨hj, -, hloc⟩ := step_wait hid hm H hl hpc
  set v := (e.cfg t').mem () (π r ⟨j, hj⟩) with hv
  set idx := ((π r).symm y₀).val with hidx
  have hidx_lt : idx < m := ((π r).symm y₀).isLt
  have hy0 : j = idx → v ≠ none := by
    intro hji
    have : (⟨j, hj⟩ : Fin m) = (π r).symm y₀ := Fin.ext hji
    rw [hv, this, Equiv.apply_symm_apply, hyq t' ht']; simp
  rw [hloc]
  split_ifs with hj1 hab2
  · refine ⟨_, _, rfl, ?_⟩
    by_cases hji : j = idx
    · left
      rcases Option.ne_none_iff_exists.1 (hy0 hji) with ⟨a, ha⟩
      rw [← ha]; simp
    · rcases hab with hab | hab
      · left; simp [hab]
      · right; omega
  · exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at hab2
    obtain ⟨rfl, hvn⟩ := hab2
    rcases hab with hab | hab
    · cases hab
    · exact hy0 (by omega) hvn
  · exact ⟨0, true, rfl, Or.inr (Nat.zero_le _)⟩

lemma stuckInv_step {r : P} {t' : ℕ} (ht' : t ≤ t') (hl : e.lbl t' = .tau r)
    (hS : StuckInv π y₀ r ((e.cfg t').loc r)) : StuckInv π y₀ r ((e.cfg (t' + 1)).loc r) := by
  rcases hS with ⟨j, hpc⟩ | hW
  · obtain ⟨-, hloc⟩ := step_wr hid hm H hl hpc
    rw [hloc]; unfold wrFrom; split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨0, true, rfl, Or.inr (Nat.zero_le _)⟩
  · exact Or.inr (waitInv_step hid hm H hyq ht' hl hW)

lemma wait_forever (ht0 : t₀ ≤ t) {r : P} {s : ℕ} (hs : t ≤ s)
    (hW : WaitInv π y₀ r ((e.cfg s).loc r)) : ∀ t' ≥ s, WaitInv π y₀ r ((e.cfg t').loc r) := by
  have hpend : (e.cfg s).pend r ≠ none :=
    H.pend_of_busy hid hm (by omega) (busy_of_stuck (Or.inr hW))
  exact loc_forever H (by omega) hpend _ hW
    (fun t' ht' hQ hl => waitInv_step hid hm H hyq (by omega) hl hQ)

lemma stuck_own_empty (ht0 : t₀ ≤ t) {r : P} {s : ℕ} (hs : t ≤ s)
    (hS : StuckInv π y₀ r ((e.cfg s).loc r)) : ∃ T, ∀ t' ≥ T, own ids (e.cfg t') r = ∅ := by
  have hpend : (e.cfg s).pend r ≠ none := H.pend_of_busy hid hm (by omega) (busy_of_stuck hS)
  have hall : ∀ t' ≥ s, StuckInv π y₀ r ((e.cfg t').loc r) :=
    loc_forever H (by omega) hpend _ hS
      (fun t' ht' hQ hl => stuckInv_step hid hm H hyq (by omega) hl hQ)
  obtain ⟨s', hs', hG⟩ := H.eventually_loc (show t₀ ≤ s by omega) hpend
    (fun st => ∃ j ab, st.pc = .wait j ab) (fun st => wrDist m st.pc) (by
      intro t' ht' hnG hl
      try dsimp only at hnG ⊢
      rcases hall t' ht' with ⟨j, hpc⟩ | ⟨j, ab, hpc, -⟩
      · obtain ⟨hj, hloc⟩ := step_wr hid hm H hl hpc
        rw [hloc, hpc]
        unfold wrFrom
        split_ifs with h
        · right
          have := (nextOwn_found _ _ _ h).1
          simp only [wrDist]; omega
        · left; exact ⟨0, true, rfl⟩
      · exact absurd ⟨j, ab, hpc⟩ hnG)
  have hW : WaitInv π y₀ r ((e.cfg s').loc r) := by
    rcases hall s' hs' with ⟨j, hpc⟩ | hW
    · obtain ⟨j', ab, hpc'⟩ := hG; rw [hpc] at hpc'; cases hpc'
    · exact hW
  refine ⟨s', fun t' ht' => ?_⟩
  obtain ⟨j, ab, hpc, -⟩ := wait_forever hid hm H hyq ht0 (by omega) hW t' ht'
  exact own_empty_of_wait hid hm H hpc

/-- **Classification.** Every process eventually owns nothing forever, or stays in the first two
loops forever. -/
lemma classify (ht0 : t₀ ≤ t) (r : P) :
    (∃ T, ∀ t' ≥ T, own ids (e.cfg t') r = ∅) ∨
    (∃ T ≥ t, ∀ t' ≥ T, CasRead ((e.cfg t').loc r).pc) := by
  by_cases hS : ∃ s ≥ t, StuckInv π y₀ r ((e.cfg s).loc r)
  · obtain ⟨s, hs, hst⟩ := hS
    exact Or.inl (stuck_own_empty hid hm H hyq ht0 hs hst)
  have hS' : ∀ s ≥ t, ¬ StuckInv π y₀ r ((e.cfg s).loc r) := fun s hs h => hS ⟨s, hs, h⟩
  by_cases hB : ∃ s ≥ t, Busy ((e.cfg s).loc r).pc
  swap
  · left
    refine ⟨t, fun t' ht' => ?_⟩
    rcases H.phase hid hm (show t₀ ≤ t' by omega) r with ⟨h, -⟩ | ⟨-, h⟩
    · exact own_empty_of_rem hid hm H h
    · exact absurd ⟨t', ht', h⟩ hB
  right
  obtain ⟨s, hs, hb⟩ := hB
  have hpend := H.pend_of_busy hid hm (show t₀ ≤ s by omega) hb
  obtain ⟨s', hs', hG⟩ := H.eventually_loc (show t₀ ≤ s by omega) hpend
    (fun st => CasRead st.pc) (fun st => waitDist m st.pc) (by
      intro t' ht' hnG hl
      try dsimp only at hnG ⊢
      have hb' := H.busy_of_tau hid hm (show t₀ ≤ t' by omega) hl
      cases hpc : ((e.cfg t').loc r).pc with
      | cas i => rw [hpc] at hnG; exact absurd (Or.inl ⟨i, rfl⟩) hnG
      | read i => rw [hpc] at hnG; exact absurd (Or.inr ⟨i, rfl⟩) hnG
      | wr j => exact absurd (Or.inl ⟨j, hpc⟩) (hS' t' (by omega))
      | wait j ab =>
        obtain ⟨hj, -, hloc⟩ := step_wait hid hm H hl hpc
        by_cases h1 : j + 1 < m
        · right; rw [hloc]; simp only [h1, ↓reduceIte, waitDist]; omega
        · by_cases h2 : (ab && (e.cfg t').mem () (π r ⟨j, hj⟩) == none) = true
          · left; rw [hloc]; simp only [h1, h2, ↓reduceIte]; exact Or.inl ⟨0, rfl⟩
          · exfalso
            apply hS' (t' + 1) (by omega)
            rw [hloc]; simp only [h1, h2, ↓reduceIte]
            exact Or.inr ⟨0, true, rfl, Or.inr (Nat.zero_le _)⟩
      | _ => rw [hpc] at hb'; exact absurd hb' id)
  have hpend' : (e.cfg s').pend r ≠ none := by
    rw [pend_persist e t₀ H.noret (by omega) hpend s' hs']; exact hpend
  refine ⟨s', by omega, loc_forever H (show t₀ ≤ s' by omega) hpend' (fun st => CasRead st.pc) hG ?_⟩
  intro t' ht' hQ hl
  try dsimp only at hQ ⊢
  rcases hQ with ⟨i, hpc⟩ | ⟨i, hpc⟩
  · obtain ⟨hi, hloc, -⟩ := step_cas hid hm H hl hpc
    rw [hloc]; split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · obtain ⟨hi, -, hloc⟩ := step_read hid hm H hl hpc
    by_cases h1 : i + 1 < m
    · rw [hloc]; simp only [h1, ↓reduceIte]; exact Or.inr ⟨_, rfl⟩
    · have hph := H.phase hid hm (show t₀ ≤ t' + 1 by omega) r
      have hS1 := hS' (t' + 1) (by omega)
      rw [hloc] at hph hS1 ⊢
      simp only [h1, ↓reduceIte] at hph hS1 ⊢
      rcases afterRead_pc ((e.cfg t').loc r)
        (Function.update ((e.cfg t').loc r).view ⟨i, hi⟩ ((e.cfg t').mem () (π r ⟨i, hi⟩)))
        with ⟨j, h⟩ | h | h | h
      · exact absurd (Or.inl ⟨j, h⟩) hS1
      · exact absurd (Or.inr ⟨0, true, h, Or.inr (Nat.zero_le _)⟩) hS1
      · exfalso; rw [h] at hph
        rcases hph with ⟨h', -⟩ | ⟨-, h'⟩
        · cases h'
        · exact h'
      · exact Or.inl ⟨0, h⟩

end Exec

/-! ### Owners decide on a constant memory -/

section Owner

variable {e : ((alg2 Id m).impl ids π).InfExec} {t₀ : ℕ}
  (hid : Function.Injective ids) (hm : 0 < m) (H : Hyp e t₀)
include hid hm H

/-- The scan invariant for a constant memory `M₀`. -/
def ScanQ (π : P → Equiv.Perm (Fin m)) (M₀ : Fin m → Option Id) (r : P) (st : St Id m) : Prop :=
  (∃ i, st.pc = .cas i) ∨ (∃ i, st.pc = .read i ∧ ∀ x : Fin m, x.val < i → st.view x = M₀ (π r x))

omit hid hm H in
lemma scanQ_def {M₀ : Fin m → Option Id} {r : P} {st : St Id m} :
    ScanQ π M₀ r st ↔ (∃ i, st.pc = .cas i) ∨
      (∃ i, st.pc = .read i ∧ ∀ x : Fin m, x.val < i → st.view x = M₀ (π r x)) := Iff.rfl

/-- A process staying in the first two loops forever while the memory is constant completes a
scan on the constant memory and decides to restart: `owned ≥ most_present` and `owned ≤ m/2`. -/
lemma owner_decision {T₆ : ℕ} (hT₆ : t₀ ≤ T₆)
    (hconst : ∀ t' ≥ T₆, (e.cfg t').mem () = (e.cfg T₆).mem ()) {r : P}
    (hcr : ∀ t' ≥ T₆, CasRead ((e.cfg t').loc r).pc) :
    ¬ owned (fun x => (e.cfg T₆).mem () (π r x)) (ids r) <
        mostPresent (fun x => (e.cfg T₆).mem () (π r x)) ∧
      ¬ m < 2 * owned (fun x => (e.cfg T₆).mem () (π r x)) (ids r) := by
  set M₀ := (e.cfg T₆).mem () with hM₀
  have hpend : ∀ s ≥ T₆, (e.cfg s).pend r ≠ none := fun s hs =>
    H.pend_of_busy hid hm (by omega) (busy_of_casRead (hcr s hs))
  -- reach line 2
  obtain ⟨s₁, hs₁, hG₁⟩ := H.eventually_loc hT₆ (hpend T₆ le_rfl)
    (fun st => ∃ i, st.pc = .cas i) (fun st => readDist m st.pc) (by
      intro t' ht' hnG hl
      try dsimp only at hnG ⊢
      rcases hcr t' ht' with ⟨i, hpc⟩ | ⟨i, hpc⟩
      · exact absurd ⟨i, hpc⟩ hnG
      · obtain ⟨hi, -, hloc⟩ := step_read hid hm H hl hpc
        by_cases h1 : i + 1 < m
        · right; rw [hloc, hpc]; simp only [h1, ↓reduceIte, readDist]; omega
        · left
          have hc := hcr (t' + 1) (by omega)
          rw [hloc] at hc ⊢; simp only [h1, ↓reduceIte] at hc ⊢
          exact ⟨0, cas0_of_afterRead hc⟩)
  -- the scan invariant
  have hQ : ∀ t' ≥ s₁, ScanQ π M₀ r ((e.cfg t').loc r) :=
    loc_forever H (by omega) (hpend s₁ (by omega)) (ScanQ π M₀ r) (Or.inl hG₁) (by
      intro t' ht' hQt hl
      rcases hQt with ⟨i, hpc⟩ | ⟨i, hpc, hview⟩
      · obtain ⟨hi, hloc, -⟩ := step_cas hid hm H hl hpc
        rw [hloc]; split_ifs
        · exact Or.inl ⟨_, rfl⟩
        · exact Or.inr ⟨0, rfl, fun x hx => absurd hx (Nat.not_lt_zero _)⟩
      · obtain ⟨hi, -, hloc⟩ := step_read hid hm H hl hpc
        by_cases h1 : i + 1 < m
        · rw [hloc]; simp only [h1, ↓reduceIte]
          refine Or.inr ⟨i + 1, rfl, fun x hxi => ?_⟩
          dsimp only
          by_cases hx : x = ⟨i, hi⟩
          · subst hx; rw [Function.update_self, hconst t' (by omega)]
          · rw [Function.update_of_ne hx]
            exact hview x (by have : x.val ≠ i := fun h => hx (Fin.ext h); omega)
        · have hc := hcr (t' + 1) (by omega)
          rw [hloc] at hc ⊢; simp only [h1, ↓reduceIte] at hc ⊢
          exact Or.inl ⟨0, cas0_of_afterRead hc⟩)
  -- reach the last read of a scan
  obtain ⟨τ, hτ, hGτ⟩ := H.eventually_loc (show t₀ ≤ s₁ by omega) (hpend s₁ (by omega))
    (fun st => st.pc = .read (m - 1)) (fun st => scanDist m st.pc) (by
      intro t' ht' hnG hl
      try dsimp only at hnG ⊢
      rcases hcr t' (by omega) with ⟨i, hpc⟩ | ⟨i, hpc⟩
      · obtain ⟨hi, hloc, -⟩ := step_cas hid hm H hl hpc
        right; rw [hloc, hpc]; split_ifs <;> simp only [scanDist] <;> omega
      · obtain ⟨hi, -, hloc⟩ := step_read hid hm H hl hpc
        have h1 : i + 1 < m := by
          by_contra h
          exact hnG (by rw [hpc, show i = m - 1 by omega])
        right; rw [hloc, hpc]; simp only [h1, ↓reduceIte, scanDist]; omega)
  have hQτ := hQ τ hτ
  try dsimp only at hGτ
  rcases hQτ with ⟨i, hpc⟩ | ⟨i, hpc, hview⟩
  · rw [hGτ] at hpc; cases hpc
  rw [hGτ] at hpc
  simp only [PC.read.injEq] at hpc
  subst hpc
  obtain ⟨τ₂, hτ₂, hl, hlocτ⟩ := next_tau H (show t₀ ≤ τ by omega) (hpend τ (by omega))
  have hpc2 : ((e.cfg τ₂).loc r).pc = .read (m - 1) := by rw [hlocτ]; exact hGτ
  obtain ⟨hi, -, hloc⟩ := step_read hid hm H hl hpc2
  have h1 : ¬ (m - 1 + 1 < m) := by omega
  have hc := hcr (τ₂ + 1) (by omega)
  rw [hloc] at hc; simp only [h1, ↓reduceIte] at hc
  have hdec := afterRead_casRead hc
  have hme : ((e.cfg τ₂).loc r).me = ids r := (H.locInv hid hm τ₂ r).1
  rw [hme] at hdec
  have hw : Function.update ((e.cfg τ₂).loc r).view ⟨m - 1, hi⟩
      ((e.cfg τ₂).mem () (π r ⟨m - 1, hi⟩)) = fun x => M₀ (π r x) := by
    funext x
    by_cases hx : x = ⟨m - 1, hi⟩
    · subst hx; rw [Function.update_self, hconst τ₂ (by omega)]
    · rw [Function.update_of_ne hx, hlocτ]
      exact hview x (by have : x.val ≠ m - 1 := fun h => hx (Fin.ext h); omega)
  rw [hw] at hdec
  exact hdec

end Owner

end Endgame

open Endgame

variable [Fintype P]

/-- Once some process `q` stays forever in the first two loops (cas/read) of `lock()` and keeps a
register `y₀`, the execution cannot continue without a completion. -/
theorem endgame (hid : Function.Injective ids) (hm : 0 < m) (hM : m ∈ M (Fintype.card P))
    {e : ((alg2 Id m).impl ids π).InfExec} {t₀ : ℕ} (H : Hyp e t₀) {q : P} {t : ℕ} (ht : t₀ ≤ t)
    (hq : ∀ t' ≥ t, (∃ i, ((e.cfg t').loc q).pc = .cas i) ∨ (∃ i, ((e.cfg t').loc q).pc = .read i))
    (hown : ∀ t' ≥ t, own ids (e.cfg t) q ⊆ own ids (e.cfg t') q)
    {y₀ : Fin m} (hy₀ : y₀ ∈ own ids (e.cfg t) q) : False := by
  have hyq : ∀ t' ≥ t, (e.cfg t').mem () y₀ = some (ids q) := by
    intro t' ht'
    have := hown t' ht' hy₀
    simpa [own] using this
  -- a time after which every process is classified
  obtain ⟨T, hT⟩ := Finite.exists_forall_of_monotone
    (p := fun r T => t ≤ T ∧ ((∀ t' ≥ T, own ids (e.cfg t') r = ∅) ∨
      (∀ t' ≥ T, CasRead ((e.cfg t').loc r).pc)))
    (by
      rintro r a b hab ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rcases h2 with h2 | h2
      · exact Or.inl fun t' ht' => h2 t' (by omega)
      · exact Or.inr fun t' ht' => h2 t' (by omega))
    (by
      intro r
      rcases classify hid hm H hyq ht r with ⟨T, hT⟩ | ⟨T, -, hT⟩
      · exact ⟨max T t, by omega, Or.inl fun t' ht' => hT t' (by omega)⟩
      · exact ⟨max T t, by omega, Or.inr fun t' ht' => hT t' (by omega)⟩)
  have hTt : t ≤ T := (hT q).1
  -- nobody erases after `T`
  have hnwr : ∀ t' ≥ T, ∀ r j, ((e.cfg t').loc r).pc ≠ .wr j := by
    intro t' ht' r j hpc
    rcases (hT r).2 with h | h
    · have := own_nonempty_of_wr hid hm H hpc
      rw [h t' ht'] at this; simp at this
    · rcases h t' ht' with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] at hpc <;> cases hpc
  -- the set of non-`⊥` registers grows and stabilizes
  obtain ⟨T₆, hT₆, hstab⟩ := Finset.eventually_const_of_subset_succ_of_finite
    (f := fun t' => Finset.univ.filter (fun y => (e.cfg t').mem () y ≠ none)) (N := T) (by
      intro t' ht' y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [mem_step_nonbot hid hm H (by omega) (fun p j _ => hnwr t' ht' p j) y hy]
      exact hy)
  have hiff : ∀ t' ≥ T₆, ∀ y,
      ((e.cfg t').mem () y ≠ none ↔ (e.cfg T₆).mem () y ≠ none) := by
    intro t' ht' y
    have := Finset.ext_iff.1 (hstab t' ht') y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  -- the memory is constant after `T₆`
  have hconst : ∀ t' ≥ T₆, (e.cfg t').mem () = (e.cfg T₆).mem () := by
    intro t' ht'
    induction t', ht' using Nat.le_induction with
    | base => rfl
    | succ t' ht' ih =>
      funext y
      by_cases hy : (e.cfg t').mem () y = none
      · have h1 : (e.cfg (t' + 1)).mem () y = none := by
          by_contra h
          exact (hiff t' ht' y).2 ((hiff (t' + 1) (by omega) y).1 h) hy
        rw [h1, ← ih, hy]
      · rw [mem_step_nonbot hid hm H (by omega) (fun p j _ => hnwr t' (by omega) p j) y hy, ih]
  -- the memory is full
  have hfull : ∀ y, (e.cfg T₆).mem () y ≠ none := by
    intro y hy
    set k := (π q).symm y with hk
    have hqcr : ∀ t' ≥ T₆, CasRead ((e.cfg t').loc q).pc := fun t' ht' => hq t' (by omega)
    have hpendq : (e.cfg T₆).pend q ≠ none :=
      H.pend_of_busy hid hm (by omega) (busy_of_casRead (hqcr T₆ le_rfl))
    have hklt := k.isLt
    obtain ⟨t₁, ht₁, hG⟩ := H.eventually_loc (show t₀ ≤ T₆ by omega) hpendq
      (fun st => st.pc = .cas k.val) (fun st => casDist m k.val st.pc) (by
        intro t' ht' hnG hl
        try dsimp only at hnG ⊢
        rcases hqcr t' ht' with ⟨i, hpc⟩ | ⟨i, hpc⟩
        · obtain ⟨hi, hloc, -⟩ := step_cas hid hm H hl hpc
          have hik : i ≠ k.val := fun h => hnG (by rw [hpc, h])
          right; rw [hloc, hpc]
          split_ifs with h1 <;> simp only [casDist] <;> split_ifs <;> omega
        · obtain ⟨hi, -, hloc⟩ := step_read hid hm H hl hpc
          by_cases h1 : i + 1 < m
          · right; rw [hloc, hpc]; simp only [h1, ↓reduceIte, casDist]; omega
          · have hc := hqcr (t' + 1) (by omega)
            rw [hloc] at hc ⊢; simp only [h1, ↓reduceIte] at hc ⊢
            right; rw [cas0_of_afterRead hc, hpc]; simp only [casDist]; split_ifs <;> omega)
    try dsimp only at hG
    obtain ⟨t₂, ht₂, hl, hloc2⟩ := next_tau H (show t₀ ≤ t₁ by omega)
      (H.pend_of_busy hid hm (by omega) (busy_of_casRead (hqcr t₁ (by omega))))
    have hpc2 : ((e.cfg t₂).loc q).pc = .cas k.val := by rw [hloc2]; exact hG
    obtain ⟨hi, -, hmem⟩ := step_cas hid hm H hl hpc2
    have hyk : π q ⟨k.val, hi⟩ = y := by simp [hk]
    have h1 := congrFun (hconst (t₂ + 1) (by omega)) y
    have h2 := congrFun (hconst t₂ (by omega)) y
    rw [hmem, ← hyk, Function.update_self, hyk, h2, hy] at h1
    simp at h1
  apply final_contra hid hm hM ((e.cfg T₆).mem ()) (π := π)
  · intro y
    rcases H.valInv hid hm T₆ y with h | h
    · exact absurd h (hfull y)
    · exact h
  · rintro r ⟨y, hy⟩
    have hcr : ∀ t' ≥ T₆, CasRead ((e.cfg t').loc r).pc := by
      rcases (hT r).2 with h | h
      · exfalso
        have hy' : y ∈ own ids (e.cfg T₆) r := by simp [own, hy]
        rw [h T₆ hT₆] at hy'; simp at hy'
      · exact fun t' ht' => h t' (by omega)
    exact owner_decision hid hm H (by omega) hconst hcr

/-- If after some time nobody owns any register, the execution cannot continue without a
completion (a pending process eventually performs a successful compare&swap). -/
theorem zero_case (hid : Function.Injective ids) (hm : 0 < m)
    {e : ((alg2 Id m).impl ids π).InfExec} {t₀ : ℕ} (H : Hyp e t₀) {p₀ : P}
    (hp₀ : (e.cfg t₀).pend p₀ ≠ none) {T : ℕ} (hT : t₀ ≤ T)
    (hzero : ∀ t ≥ T, ∀ r, own ids (e.cfg t) r = ∅) : False := by
  have hbot : ∀ t ≥ T, ∀ y, (e.cfg t).mem () y = none := by
    intro t ht y
    rcases H.valInv hid hm t y with h | ⟨r, h⟩
    · exact h
    · exfalso
      have : y ∈ own ids (e.cfg t) r := by simp [own, h]
      rw [hzero t ht r] at this; simp at this
  have hpend : ∀ t ≥ t₀, (e.cfg t).pend p₀ ≠ none := fun t ht => by
    rw [pend_persist e t₀ H.noret le_rfl hp₀ t ht]; exact hp₀
  have hbusy : ∀ t ≥ t₀, Busy ((e.cfg t).loc p₀).pc := fun t ht => by
    rcases H.phase hid hm ht p₀ with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h (hpend t ht)
    · exact h
  have hnwr : ∀ t ≥ T, ∀ j, ((e.cfg t).loc p₀).pc ≠ .wr j := fun t ht j h => by
    have := own_nonempty_of_wr hid hm H h
    rw [hzero t ht p₀] at this; simp at this
  obtain ⟨t₁, ht₁, hG⟩ := H.eventually_loc hT (hpend T hT)
    (fun st => ∃ i, st.pc = .cas i) (fun st => zDist m st.pc) (by
      intro t' ht' hnG hl
      try dsimp only at hnG ⊢
      have hb := hbusy t' (by omega)
      cases hpc : ((e.cfg t').loc p₀).pc with
      | cas i => rw [hpc] at hnG; exact absurd ⟨i, rfl⟩ hnG
      | wr j => exact absurd hpc (hnwr t' ht' j)
      | read i =>
        obtain ⟨hi, -, hloc⟩ := step_read hid hm H hl hpc
        by_cases h1 : i + 1 < m
        · right; rw [hloc]; simp only [h1, ↓reduceIte, zDist]; omega
        · have hb1 := hbusy (t' + 1) (by omega)
          have hn1 := hnwr (t' + 1) (by omega)
          rw [hloc] at hb1 hn1 ⊢
          simp only [h1, ↓reduceIte] at hb1 hn1 ⊢
          rcases afterRead_pc ((e.cfg t').loc p₀)
            (Function.update ((e.cfg t').loc p₀).view ⟨i, hi⟩ ((e.cfg t').mem () (π p₀ ⟨i, hi⟩)))
            with ⟨j, h⟩ | h | h | h
          · exact absurd h (hn1 j)
          · right; rw [h]; simp only [zDist, ↓reduceIte]; omega
          · exfalso; rw [h] at hb1; exact hb1
          · left; exact ⟨0, h⟩
      | wait i ab =>
        obtain ⟨hi, -, hloc⟩ := step_wait hid hm H hl hpc
        have hv : (e.cfg t').mem () (π p₀ ⟨i, hi⟩) = none := hbot t' ht' _
        rw [hloc, hv]
        by_cases h1 : i + 1 < m
        · right; simp only [h1, ↓reduceIte, zDist]
          cases ab <;> simp <;> omega
        · cases ab
          · right; simp only [h1, ↓reduceIte, zDist]; simp; omega
          · left; simp only [h1, ↓reduceIte]; simp
      | _ => rw [hpc] at hb; exact absurd hb id)
  obtain ⟨i, hpc⟩ := hG
  obtain ⟨t₂, ht₂, hl, hloc2⟩ := next_tau H (show t₀ ≤ t₁ by omega) (hpend t₁ (by omega))
  have hpc2 : ((e.cfg t₂).loc p₀).pc = .cas i := by rw [hloc2]; exact hpc
  obtain ⟨hi, -, hmem⟩ := step_cas hid hm H hl hpc2
  have h1 := hbot (t₂ + 1) (by omega) (π p₀ ⟨i, hi⟩)
  rw [hmem, Function.update_self, hbot t₂ (by omega)] at h1
  simp at h1

end AnonymousMutex.Alg2
