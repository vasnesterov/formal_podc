import Papers.PODC2016.RWLockRMRTradeoff.Erasure
import Papers.PODC2016.RWLockRMRTradeoff.Lemma1
import Papers.PODC2016.RWLockRMRTradeoff.Lemma2
import Papers.PODC2016.RWLockRMRTradeoff.Solo

/-!
# The executions `E₁` and `E₂` of the proof of Theorem 5

* `exists_E1` (Observation 3, first part): by Concurrent Entering, all readers can enter the CS
  one after the other, writers staying in the remainder section.
* `exists_E2` (the iterative construction of the proof of Theorem 5): starting from `C₁` (all
  readers in the CS), all readers execute their exit sections, scheduled in rounds: first every
  reader runs until it is poised on an expanding step (or has finished), then all poised readers take
  their expanding steps in the order of Lemma 2. After the last round `r`, every awareness set has
  at most `3^r` elements, and (if `r ≥ 1`) some reader performed at least `r` expanding steps.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

section Generic

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq ι] [DecidableEq V] [DecidableEq P] {v₀ : V}
variable {I : Impl A (Regs ι V v₀) P L} {cm : CacheModel P ι}

/-- Configurations and caches along a run do not depend on the knowledge. -/
lemma xrun_congr {X X' Y : Ext I cm} {β : List (Label P A)} (hc : X'.cfg = X.cfg)
    (hca : X'.cache = X.cache) (h : xrun X β = some Y) :
    ∃ Y', xrun X' β = some Y' ∧ Y'.cfg = Y.cfg ∧ Y'.cache = Y.cache := by
  induction β generalizing X X' with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; exact ⟨X', rfl, hc, hca⟩
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, -, h3⟩ := xstep_eq_some.1 hs
      set Z' : Ext I cm := ⟨Z.cfg, kstep I X'.cfg X'.kn ℓ, Z.cache⟩
      have hs' : xstep X' ℓ = some Z' := xstep_eq_some.2 ⟨by rw [hc]; exact h1, rfl,
        by rw [h3, hc, hca]⟩
      obtain ⟨Y', h1', h2', h3'⟩ := ih (X := Z) (X' := Z') rfl rfl h
      exact ⟨Y', by rw [xrun_cons, hs']; exact h1', h2', h3'⟩

/-- Counting RMRs does not depend on the knowledge. -/
lemma xcount_rmr_congr {X X' : Ext I cm} (p : P) (β : List (Label P A)) (hc : X'.cfg = X.cfg)
    (hca : X'.cache = X.cache) : xcount (RMRBy p) X' β = xcount (RMRBy p) X β := by
  induction β generalizing X X' with
  | nil => rfl
  | cons ℓ β ih =>
    simp only [xcount]
    cases hs : xstep X ℓ with
    | none =>
      have h0 : I.step X.cfg ℓ = none := by simpa [xstep] using hs
      have : xstep X' ℓ = none := by simp [xstep, hc, h0]
      rw [this]
    | some Z =>
      obtain ⟨h1, -, h3⟩ := xstep_eq_some.1 hs
      set Z' : Ext I cm := ⟨Z.cfg, kstep I X'.cfg X'.kn ℓ, Z.cache⟩
      have hs' : xstep X' ℓ = some Z' := xstep_eq_some.2 ⟨by rw [hc]; exact h1, rfl,
        by rw [h3, hc, hca]⟩
      rw [hs']; dsimp only
      rw [ih (X := Z) (X' := Z') rfl rfl]
      have : RMRBy p X' ℓ ↔ RMRBy p X ℓ := by simp only [RMRBy, hc, hca]
      by_cases hR : RMRBy p X ℓ
      · rw [if_pos hR, if_pos (this.2 hR)]
      · rw [if_neg hR, if_neg (fun h => hR (this.1 h))]

/-- Internal steps do not change pending operations. -/
lemma xrun_pend_of_tau {X Y : Ext I cm} {β : List (Label P A)} (h : xrun X β = some Y)
    (hβ : ∀ ℓ ∈ β, ∃ q, ℓ = .tau q) : Y.cfg.pend = X.cfg.pend := by
  induction β generalizing X with
  | nil => simp only [xrun_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨q, rfl⟩ := hβ ℓ List.mem_cons_self
      rw [ih h (fun ℓ' h' => hβ ℓ' (List.mem_cons_of_mem _ h')),
        (Impl.step_tau (xstep_eq_some.1 hs).1).2.1]

end Generic

section Regions

variable {P : Type} [DecidableEq P]

/-- Without invocations, from the remainder section one never gets to the exit section. -/
lemma regFold_rem_ne_exiting (γ : List (Label P mutexObj)) (p : P)
    (hγ : ∀ ℓ ∈ γ, ∀ q o, ℓ ≠ .inv q o) : regFold (some .rem) γ p ≠ some .exiting := by
  induction γ with
  | nil => simp
  | cons ℓ γ ih =>
    rw [regFold_cons]
    have ih' := ih (fun ℓ' h' => hγ ℓ' (List.mem_cons_of_mem _ h'))
    split_ifs with h
    · cases ℓ with
      | inv q o => exact absurd rfl (hγ _ List.mem_cons_self q o)
      | ret q r => simp [Region.next]
      | tau q => simpa [Region.next] using ih'
    · exact ih'

/-- A process still in its exit section has not returned. -/
lemma not_returns_of_exiting (γ : List (Label P mutexObj)) (p : P)
    (hγ : ∀ ℓ ∈ γ, ∀ q o, ℓ ≠ .inv q o) (h : regFold (some .exiting) γ p = some .exiting) :
    ¬ Returns p γ := by
  induction γ with
  | nil => rintro ⟨r, hr⟩; simp at hr
  | cons ℓ γ ih =>
    rintro ⟨r, hr⟩
    rw [regFold_cons] at h
    have hγ' := fun ℓ' h' => hγ ℓ' (List.mem_cons_of_mem _ h')
    rcases List.mem_cons.1 hr with rfl | hr'
    · simp only [Label.proc, ite_true, Option.bind_some, Region.next] at h
      exact regFold_rem_ne_exiting γ p hγ' h
    · split_ifs at h with hp
      · cases ℓ with
        | inv q o => exact absurd rfl (hγ _ List.mem_cons_self q o)
        | ret q r' =>
          simp only [Label.proc] at hp; subst hp
          simp only [Option.bind_some, Region.next] at h
          exact regFold_rem_ne_exiting γ q hγ' h
        | tau q =>
          simp only [Option.bind_some, Region.next] at h
          exact ih hγ' h ⟨r, hr'⟩
      · exact ih hγ' h ⟨r, hr'⟩

end Regions

variable {n m : ℕ} {ι V L : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable {I : RWAlg n m ι V v₀ L} {cm : CacheModel (Proc n m) ι}

/-- `α` takes `Ext.init` to `X` and `X` has configuration `C`: `I.run α = some C`. -/
lemma run_of_xrun {α : List (Label (Proc n m) mutexObj)} {X : Ext I cm}
    (h : xrun (Ext.init I cm) α = some X) : I.run α = some X.cfg := xrun_cfg h

/-! ### `E₁`: all readers enter the CS -/

/-- **`E₁`** (Observation 3): by Concurrent Entering, the readers of `s` can enter the CS one
after another while all other processes stay in the remainder section. -/
theorem exists_E1 (hall : ∀ p o, I.allowed p o) (hCE : ConcurrentEntering I) :
    ∀ s : List (Fin n), s.Nodup → ∃ α X, xrun (Ext.init I cm) α = some X ∧ ClientWF α ∧
      (∀ i, regionOf α (.inl i) = some (if i ∈ s then .cs else .rem)) ∧
      (∀ j, regionOf α (.inr j) = some .rem) ∧ (∀ q, X.cfg.pend q = none) ∧
      (∀ ℓ ∈ α, ℓ.proc.isLeft) := by
  intro s
  induction s with
  | nil =>
    intro _
    refine ⟨[], Ext.init I cm, rfl, fun q => by simp [regionOf], fun i => by simp [regionOf],
      fun j => by simp [regionOf], fun q => rfl, by simp⟩
  | cons i s ih =>
    intro hnd
    obtain ⟨his, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨α, X, hX, hwf, hr, hw, hp, hlbl⟩ := ih hnd'
    have hrun := run_of_xrun hX
    -- invoke `lock`
    have hs := Impl.step_inv_eq_some (I := I) (o := MutexOp.lock) (hp (.inl i)) (hall _ _)
    set C₁ := { X.cfg with pend := Function.update X.cfg.pend (.inl i) (some .lock),
                           loc := Function.update X.cfg.loc (.inl i)
                             (I.invoke (.inl i) (X.cfg.loc (.inl i)) .lock) } with hC₁
    have hrun₁ : I.run (α ++ [.inv (.inl i) .lock]) = some C₁ := by
      rw [Impl.run_append_of_eq I hrun, Impl.runFrom_singleton, hs]
    have hreg₁ : ∀ q, regionOf (α ++ [.inv (.inl i) .lock]) q =
        if q = .inl i then some .trying else regionOf α q := by
      intro q
      rw [regionOf_append]
      by_cases hq : q = .inl i
      · subst hq; simp [regFold_cons, Label.proc, hr i, his, Region.next]
      · simp [regFold_cons, Label.proc, Ne.symm hq, hq]
    have hwf₁ : ClientWF (α ++ [.inv (.inl i) .lock]) := by
      intro q; rw [hreg₁ q]; split_ifs
      · simp
      · exact hwf q
    obtain ⟨b, hb⟩ := hCE _ i ⟨_, hrun₁⟩ hwf₁ (fun j => by rw [hreg₁]; simp [hw j])
      (by rw [hreg₁]; simp)
    have hpend₁ : C₁.pend (.inl i) ≠ none := by simp [hC₁]
    -- run solo until the CS
    obtain ⟨k, hk⟩ := exists_solo_return I b (p := .inl i) (C := C₁) (fun k hk' => by
      apply hb
      · exact ⟨_, by rw [Impl.run_append_of_eq I hrun₁, Impl.runFrom_soloLabels]⟩
      · intro ℓ hℓ; rw [I.soloLabels_proc _ _ _ ℓ hℓ]; rfl
      · rintro ⟨r, hr'⟩
        cases soloLabels_tau I (.inl i) k C₁ hk' _ hr')
    set α' := α ++ [.inv (.inl i) .lock] ++ I.soloLabels (.inl i) C₁ k
    have hrun' : I.run α' = some ((I.soloStep (.inl i))^[k] C₁) := by
      rw [Impl.run_append_of_eq I hrun₁, Impl.runFrom_soloLabels]
    obtain ⟨X', hX', hXc⟩ := exists_xrun (X := Ext.init I cm) hrun'
    have hreg' : ∀ q, regionOf α' q =
        if q = .inl i then some .cs else regionOf α q := by
      intro q
      rw [regionOf_append]
      by_cases hq : q = .inl i
      · subst hq
        rw [hreg₁, if_pos rfl, regFold_soloLabels I _ .trying .cs (fun _ => rfl) rfl k C₁
          hpend₁, if_pos hk, if_pos rfl]
      · rw [hreg₁, if_neg hq, if_neg hq, regFold_of_forall_ne]
        intro ℓ hℓ; rw [I.soloLabels_proc _ _ _ ℓ hℓ]; exact Ne.symm hq
    refine ⟨α', X', hX', fun q => ?_, fun i' => ?_, fun j => ?_, fun q => ?_, fun ℓ hℓ => ?_⟩
    · rw [hreg' q]; split_ifs
      · simp
      · exact hwf q
    · rw [hreg' (.inl i')]
      by_cases hi : i' = i
      · subst hi; simp
      · simp [hi, hr i']
    · rw [hreg' (.inr j)]; simp [hw j]
    · rw [hXc]
      by_cases hq : q = .inl i
      · subst hq; exact hk
      · -- solo steps of `i` and the invocation do not touch `q`
        have h1 : ∀ k' (C : Config mutexObj (Regs ι V v₀) (Proc n m) L),
            ((I.soloStep (.inl i))^[k'] C).pend q = C.pend q := by
          intro k'
          induction k' with
          | zero => intro C; rfl
          | succ k' ihk =>
            intro C
            rw [Function.iterate_succ_apply, ihk]
            unfold Impl.soloStep
            split_ifs with h0
            · rfl
            · obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1
                (I.step_nextLabel_isSome C (.inl i) h0)
              rw [hC', Option.getD_some]
              exact (Impl.step_other hC' (by rw [I.nextLabel_proc]; exact Ne.symm hq)).2
        rw [h1, hC₁]; simp [Function.update_of_ne hq, hp q]
    · simp only [α', List.mem_append, List.mem_singleton] at hℓ
      rcases hℓ with (hℓ | rfl) | hℓ
      · exact hlbl ℓ hℓ
      · rfl
      · rw [I.soloLabels_proc _ _ _ ℓ hℓ]; rfl

end Podc.RWLockRMRTradeoff
