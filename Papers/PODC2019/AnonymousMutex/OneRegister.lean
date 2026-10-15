import Papers.PODC2019.AnonymousMutex.LowerBound
import Cslib.Computability.Distributed.SharedMemory.Indist

/-!
# One read/write register does not suffice for deadlock-free mutual exclusion

Classical fact (Burns–Lynch, reference [3] of Aghazadeh–Imbs–Raynal–Taubenfeld–Woelfel,
PODC 2019), here for a single register: with `m = 1` anonymous register accessed by reads,
writes (and snapshots, which for one register are just reads) there is no deadlock-free mutual
exclusion algorithm for two or more processes. Symmetry is not needed.

Covering argument:
1. by deadlock-freedom, every process `r` running `lock()` solo from the initial configuration
   returns (`solo_lock_returns`): otherwise the execution "`r` invokes `lock` and then takes
   internal steps forever" is fair and client-well-formed, `r` is pending, nobody is in the
   critical section, and no operation completes;
2. cut `p`'s solo `lock()` run before its first write (`split_at_write`): up to there the memory
   is still the initial one, so `q`'s solo `lock()` run can be inserted and returns; then `p`'s
   write overwrites the (only) register with the same value as in the solo run and leaves `p` in
   the same local state, so `p` completes its solo run too: both are in the critical section.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex

section Regions

variable {P : Type} [DecidableEq P]

/-- The region of `p` only depends on the labels of `p`. -/
lemma regionOf_filter (α : List (Label P mutexObj)) (p : P) :
    regionOf α p = regionOf (α.filter (fun ℓ => ℓ.proc = p)) p := by
  unfold regionOf
  generalize (some Region.rem : Option Region) = x
  induction α generalizing x with
  | nil => rfl
  | cons ℓ α ih =>
    by_cases h : ℓ.proc = p
    · simp [h, ih]
    · simp [h, ih]

lemma regionOf_eq_of_filter_eq {α β : List (Label P mutexObj)} {p : P}
    (h : α.filter (fun ℓ => ℓ.proc = p) = β.filter (fun ℓ => ℓ.proc = p)) :
    regionOf α p = regionOf β p := by
  rw [regionOf_filter α, regionOf_filter β, h]

lemma regionOf_of_forall_ne {α : List (Label P mutexObj)} {p : P}
    (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) : regionOf α p = some .rem := by
  rw [regionOf_filter, List.filter_eq_nil_iff.2 (by simpa using h)]
  rfl

lemma regionOf_append_replicate_tau (α : List (Label P mutexObj)) (p q : P) (n : ℕ) :
    regionOf (α ++ List.replicate n (.tau q)) p = regionOf α p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc, regionOf_append_singleton, ih]
    split_ifs
    · rcases regionOf α p with _ | r
      · rfl
      · cases r <;> rfl
    · rfl

/-- `p` invokes `lock()`, takes `n` internal steps and returns. -/
def soloLock (p : P) (n : ℕ) : List (Label P mutexObj) :=
  .inv p .lock :: (List.replicate n (.tau p) ++ [.ret p ()])

lemma soloLock_proc (p : P) (n : ℕ) : ∀ ℓ ∈ soloLock p n, ℓ.proc = p := by
  intro ℓ hℓ
  simp only [soloLock, List.mem_cons, List.mem_append, List.mem_replicate,
    List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | ⟨-, rfl⟩ | rfl <;> rfl

lemma regionOf_soloLock (p : P) (n : ℕ) : regionOf (soloLock p n) p = some .cs := by
  have : soloLock p n = ([.inv p .lock] ++ List.replicate n (.tau p)) ++ [.ret p ()] := by
    simp [soloLock]
  rw [this, regionOf_append_singleton, regionOf_append_replicate_tau]
  simp [regionOf, Label.proc, Region.next]

end Regions

section Agree

variable {O : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]

/-- A run of `p` alone only depends on what `p` observes. -/
lemma runFrom_agree (I : Impl O B P L) {p : P} {C D D' : Config O B P L} (h : Impl.Agree p C D)
    {γ : List (Label P O)} (hγ : ∀ ℓ ∈ γ, ℓ.proc = p) (hD : I.runFrom D γ = some D') :
    ∃ C', I.runFrom C γ = some C' ∧ Impl.Agree p C' D' := by
  induction γ generalizing C D with
  | nil =>
    simp only [Impl.runFrom_nil, Option.some.injEq] at hD
    subst hD; exact ⟨C, rfl, h⟩
  | cons ℓ γ ih =>
    simp only [Impl.runFrom_cons] at hD
    cases hs : I.step D ℓ with
    | none => simp [hs] at hD
    | some D₁ =>
      simp only [hs, Option.bind_some] at hD
      obtain ⟨C₁, hC₁, hag⟩ := Impl.step_agree h.symm (hγ ℓ (by simp)) hs
      obtain ⟨C', h1, h2⟩ := ih hag.symm (fun ℓ' h' => hγ ℓ' (by simp [h'])) hD
      exact ⟨C', by simp [hC₁, h1], h2⟩

end Agree

section OneRegister

variable {Id V S : Type} {P : Type} [DecidableEq P] {A : SymAlg mutexObj Id 1 V S}
  {ids : P → Id} {π : P → Equiv.Perm (Fin 1)}

/-- Step 1: under deadlock-freedom, a solo `lock()` from the initial configuration returns. -/
lemma solo_lock_returns (hDF : (A.impl ids π).DeadlockFree) (r : P) :
    ∃ n D, (A.impl ids π).run (soloLock r n) = some D := by
  by_contra hcon
  push Not at hcon
  have hX : ∀ n, ∃ X, (A.impl ids π).run (.inv r .lock :: List.replicate n (.tau r)) = some X ∧
      X.pend r ≠ none := by
    intro n
    induction n with
    | zero =>
      obtain ⟨X, h1, h2⟩ : ∃ X, (A.impl ids π).step (A.impl ids π).initCfg (.inv r .lock) =
          some X ∧ X.pend r ≠ none :=
        ⟨_, SymAlg.impl_step_inv ids π (C := (A.impl ids π).initCfg) rfl, by simp⟩
      exact ⟨X, by rw [List.replicate_zero, Impl.run, Impl.runFrom_singleton]; exact h1, h2⟩
    | succ n ih =>
      obtain ⟨X, hX, hp⟩ := ih
      rw [List.replicate_succ', ← List.cons_append, Impl.run_append_of_eq _ hX,
        Impl.runFrom_singleton]
      cases hact : A.act (X.loc r) with
      | rmw x f k => exact ⟨_, SymAlg.impl_step_tau_rmw ids π hp hact, hp⟩
      | snap k => exact ⟨_, SymAlg.impl_step_tau_snap ids π hp hact, hp⟩
      | ret r' s =>
        exfalso
        cases r'
        apply hcon n _
        rw [soloLock, ← List.cons_append, Impl.run_append_of_eq _ hX, Impl.runFrom_singleton]
        exact SymAlg.impl_step_ret ids π hp hact
  let E : ℕ → List (Label P mutexObj) := fun k => .inv r .lock :: List.replicate k (.tau r)
  have hEs : ∀ k, E (k + 1) = E k ++ [.tau r] := fun k => by simp [E, List.replicate_succ']
  obtain ⟨ex, hlbl, -⟩ := (A.impl ids π).exists_infExec_of_chain E
    (fun k => by rw [hEs]; exact List.prefix_append _ _)
    (fun k => by simp [E])
    (fun k => by obtain ⟨X, hX, -⟩ := hX k; exact ⟨X, hX⟩)
  have hl : ∀ n, ex.lbl n = if n = 0 then .inv r .lock else .tau r := by
    intro n
    rw [hlbl n n (by simp [E])]
    rcases n with _ | n <;> simp [E]
  have hreg : ∀ t, regionOf (ex.pre t) r = some (if t = 0 then .rem else .trying) ∧
      ∀ q, q ≠ r → regionOf (ex.pre t) q = some .rem := by
    intro t
    induction t with
    | zero => simp [Impl.InfExec.pre]
    | succ t ih =>
      rw [ex.pre_succ, hl]
      refine ⟨?_, fun q hq => ?_⟩
      · rw [regionOf_append_singleton, ih.1]
        rcases t with _ | t <;> simp [Label.proc, Region.next]
      · rw [regionOf_append_singleton_of_ne _ _ (by split_ifs <;> simp [Label.proc, Ne.symm hq]),
          ih.2 q hq]
  have hother : ∀ q, q ≠ r → ∀ t, (ex.cfg t).pend q = none := by
    intro q hq t
    induction t with
    | zero => rw [ex.cfg_zero]; rfl
    | succ t ih =>
      rw [(Impl.step_other (ex.step_eq t)
        (by rw [hl]; split_ifs <;> simp [Label.proc, Ne.symm hq])).2, ih]
  have hfair : ex.Fair := by
    intro q t hq
    by_cases hqr : q = r
    · subst hqr; exact ⟨t + 1, by omega, by rw [hl]; simp [Label.proc, Label.IsStep]⟩
    · exact absurd (hother q hqr t) hq
  have hcfg1 : (ex.cfg 1).pend r ≠ none := by
    obtain ⟨X, hX1, hXp⟩ := hX 0
    have h1 := ex.run_pre 1
    have : ex.pre 1 = .inv r .lock :: List.replicate 0 (.tau r) := by
      simp [Impl.InfExec.pre, hl]
    rw [this, hX1] at h1
    rw [← Option.some.inj h1]; exact hXp
  obtain ⟨t', -, q, x, hret⟩ := hDF ex
    (fun t q => by
      by_cases hq : q = r
      · subst hq; rw [(hreg t).1]; simp
      · rw [(hreg t).2 q hq]; simp)
    hfair 1 ⟨r, hcfg1⟩
    (fun q hq => by
      unfold InCS at hq
      by_cases hqr : q = r
      · subst hqr; rw [(hreg 1).1] at hq; simp at hq
      · rw [(hreg 1).2 q hqr] at hq; simp at hq)
  rw [hl] at hret
  split_ifs at hret

/-- Step 2: cut a run of `p` alone before `p`'s first write. Before the cut the memory is
unchanged; after the cut, the rest of the run is enabled from every configuration in which `p`
has the same local state and pending operation, whatever the memory (the first step of the
rest, if any, is a blind write to the only register). -/
lemma split_at_write (hRW : A.ReadWrite) (p : P) :
    ∀ (γ : List (Label P mutexObj)) (X X' : A.Cfg), (∀ ℓ ∈ γ, ℓ.proc = p) →
      (A.impl ids π).runFrom X γ = some X' →
      ∃ β δ, γ = β ++ δ ∧ ∃ Y, (A.impl ids π).runFrom X β = some Y ∧ Y.mem = X.mem ∧
        ∀ Z : A.Cfg, Z.loc p = Y.loc p → Z.pend p = Y.pend p →
          ∃ Z', (A.impl ids π).runFrom Z δ = some Z' := by
  intro γ
  induction γ with
  | nil => exact fun X _ _ _ => ⟨[], [], rfl, X, rfl, rfl, fun Z _ _ => ⟨Z, rfl⟩⟩
  | cons ℓ γ ih =>
    intro X X' hγ hrun
    simp only [Impl.runFrom_cons] at hrun
    cases hs : (A.impl ids π).step X ℓ with
    | none => simp [hs] at hrun
    | some X₁ =>
      simp only [hs, Option.bind_some] at hrun
      have hγ' : ∀ ℓ' ∈ γ, ℓ'.proc = p := fun ℓ' h => hγ ℓ' (by simp [h])
      -- continue past a step that does not change the memory
      have cont : X₁.mem = X.mem → ∃ β δ, ℓ :: γ = β ++ δ ∧ ∃ Y,
          (A.impl ids π).runFrom X β = some Y ∧ Y.mem = X.mem ∧
          ∀ Z : A.Cfg, Z.loc p = Y.loc p → Z.pend p = Y.pend p →
            ∃ Z', (A.impl ids π).runFrom Z δ = some Z' := by
        intro hm
        obtain ⟨β, δ, h1, Y, h2, h3, h4⟩ := ih X₁ X' hγ' hrun
        exact ⟨ℓ :: β, δ, by rw [h1]; rfl, Y, by simp [hs, h2], h3.trans hm, h4⟩
      cases ℓ with
      | inv p' o => exact cont (Impl.step_inv hs).2.2.2.2
      | ret p' r => exact cont (Impl.step_ret hs).2.2.1
      | tau p' =>
        have hp' : p' = p := hγ (.tau p') (by simp)
        subst hp'
        obtain ⟨hpend, ⟨x, f, k, hact, rfl⟩ | ⟨k, hact, rfl⟩⟩ := SymAlg.impl_step_tau_cases hs
        · rcases hRW _ x f k hact with hid | ⟨w, s', hw, hk⟩
          · apply cont
            simp only [hid, Function.update_eq_self]
          · -- the first write: stop here
            refine ⟨[], .tau p' :: γ, rfl, X, rfl, rfl, fun Z hZl hZp => ?_⟩
            have hZpend : Z.pend p' ≠ none := hZp ▸ hpend
            have hZact : A.act (Z.loc p') = .rmw x f k := hZl ▸ hact
            have hZs := SymAlg.impl_step_tau_rmw ids π hZpend hZact
            have hmem : Function.update Z.mem ()
                  (Function.update (Z.mem ()) (π p' x) (f (Z.mem () (π p' x)))) =
                Function.update X.mem ()
                  (Function.update (X.mem ()) (π p' x) (f (X.mem () (π p' x)))) := by
              funext u y
              cases u
              have hy : y = π p' x := Subsingleton.elim _ _
              subst hy
              simp [hw]
            obtain ⟨Z', hZ', -⟩ := runFrom_agree (A.impl ids π) (D := { X with
                mem := Function.update X.mem ()
                  (Function.update (X.mem ()) (π p' x) (f (X.mem () (π p' x))))
                loc := Function.update X.loc p' (k (X.mem () (π p' x))) })
              (C := { Z with
                mem := Function.update Z.mem ()
                  (Function.update (Z.mem ()) (π p' x) (f (Z.mem () (π p' x))))
                loc := Function.update Z.loc p' (k (Z.mem () (π p' x))) })
              ⟨hmem, by simp [hk], hZp⟩ hγ' hrun
            exact ⟨Z', by simp [hZs, hZ']⟩
        · apply cont
          simp only [Function.update_eq_self]

/-- **One register is not enough** (Burns–Lynch [3], case of one register): with a single
anonymous read/write register (plus snapshots, which are reads here), no algorithm — symmetric
or not — solves deadlock-free mutual exclusion for two processes `p ≠ q`, for any identifiers and
any anonymity permutations. -/
theorem one_register_impossible (A : SymAlg mutexObj Id 1 V S) (hRW : A.ReadWrite)
    (ids : P → Id) (π : P → Equiv.Perm (Fin 1)) {p q : P} (hpq : p ≠ q) :
    ¬ ((A.impl ids π).MutualExclusion ∧ (A.impl ids π).DeadlockFree) := by
  rintro ⟨hME, hDF⟩
  obtain ⟨np, Dp, hp⟩ := solo_lock_returns hDF p
  obtain ⟨nq, Dq, hq⟩ := solo_lock_returns hDF q
  obtain ⟨β, δ, hβδ, Y, hY, hYmem, hδ⟩ :=
    split_at_write hRW p (soloLock p np) _ _ (soloLock_proc p np) hp
  have hβp : ∀ ℓ ∈ β, ℓ.proc = p := fun ℓ h =>
    soloLock_proc p np ℓ (hβδ ▸ List.mem_append_left _ h)
  have hδp : ∀ ℓ ∈ δ, ℓ.proc = p := fun ℓ h =>
    soloLock_proc p np ℓ (hβδ ▸ List.mem_append_right _ h)
  have hβq := (A.impl ids π).runFrom_other hY
    (fun ℓ h => by rw [hβp ℓ h]; exact hpq)
  obtain ⟨Y', hY', -⟩ := runFrom_agree (A.impl ids π)
    (C := Y) (D := (A.impl ids π).initCfg) ⟨hYmem, hβq.1, hβq.2⟩ (soloLock_proc q nq) hq
  have hY'p := (A.impl ids π).runFrom_other hY'
    (fun ℓ h => by rw [soloLock_proc q nq ℓ h]; exact Ne.symm hpq)
  obtain ⟨Z, hZ⟩ := hδ Y' hY'p.1 hY'p.2
  set α := β ++ soloLock q nq ++ δ with hα
  have hval : (A.impl ids π).Valid α :=
    ⟨Z, by rw [hα, Impl.run, Impl.runFrom_append_of_eq _ (Impl.runFrom_append_of_eq _ hY _ |>.trans hY')]; exact hZ⟩
  have hfq : ∀ r, r ≠ q → (soloLock q nq).filter (fun ℓ => ℓ.proc = r) = [] := fun r hr =>
    List.filter_eq_nil_iff.2 (fun ℓ h => by simp [soloLock_proc q nq ℓ h, Ne.symm hr])
  have hfp : ∀ (γ : List (Label P mutexObj)), (∀ ℓ ∈ γ, ℓ.proc = p) →
      ∀ r, r ≠ p → γ.filter (fun ℓ => ℓ.proc = r) = [] := fun γ hγ r hr =>
    List.filter_eq_nil_iff.2 (fun ℓ h => by simp [hγ ℓ h, Ne.symm hr])
  have hcsp : InCS α p := by
    unfold InCS
    rw [← regionOf_soloLock p np]
    apply regionOf_eq_of_filter_eq
    rw [hα, hβδ, List.filter_append, List.filter_append, List.filter_append,
      hfq p hpq, List.append_nil]
  have hcsq : InCS α q := by
    unfold InCS
    rw [← regionOf_soloLock q nq]
    apply regionOf_eq_of_filter_eq
    rw [hα, List.filter_append, List.filter_append, hfp β hβp q (Ne.symm hpq),
      hfp δ hδp q (Ne.symm hpq), List.nil_append, List.append_nil]
  have hwf : ClientWF α := by
    intro r
    by_cases hrp : r = p
    · subst hrp; rw [hcsp]; simp
    by_cases hrq : r = q
    · subst hrq; rw [hcsq]; simp
    rw [regionOf_of_forall_ne]
    · simp
    · intro ℓ h
      simp only [hα, List.mem_append] at h
      rcases h with (h | h) | h
      · rw [hβp ℓ h]; exact Ne.symm hrp
      · rw [soloLock_proc q nq ℓ h]; exact Ne.symm hrq
      · rw [hδp ℓ h]; exact Ne.symm hrp
  exact hpq (hME α hval hwf p q hcsp hcsq)

end OneRegister

end AnonymousMutex
