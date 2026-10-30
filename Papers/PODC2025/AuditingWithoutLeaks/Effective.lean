import Papers.PODC2025.AuditingWithoutLeaks.Lin

/-!
# Effective reads (Definition 2, Claim 4, Lemma 3 and Lemma 5)

A read by `p_j` is *`v`-effective* after `α` (Definition 2, `Impl.EffectiveFam`) iff it has
returned `v`, or it is pending and `p_j` has either read `SN = prev_sn` (silent read, returning
`prev_val = v`) or applied fetch&xor to `R` (obtaining `R.val = v`) — Claim 4. The "if" direction
holds because the local state of `p_j` (`rCAS _ _ v` or `rRet _ v`) is the same in every
execution indistinguishable to `p_j` and determines the response; the "only if" direction needs a
writer and two distinct values: some writer can complete its pending write and then write `v'`
(or `v''`) until `R.val` changes, after which the read returns `v'` (or `v''`).
-/

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}

variable (W Au v₀) in
/-- Algorithm 1 as a family indexed by the one-time pads. -/
abbrev alg1F (rnd : ℕ → Fin m → Bool) := alg1 (W := W) (Au := Au) rnd v₀

/-- The value a reader's pending read is bound to return (after a fetch&xor or a silent read). -/
def fixedVal : Loc m V → Option V
  | .rCAS _ _ val => some val
  | .rRet _ val => some val
  | _ => none

section Extension

variable {rnd : ℕ → Fin m → Bool}

/-- Once a reader's read is bound to `val`, its next response (if any) is `val`. -/
lemma resp_of_fixed {j : Fin m} {val : V} :
    ∀ (γ : List (Label (Proc m W Au) (auditReg m V v₀))) {D D' : Cfg m W Au V v₀},
      fixedVal (D.loc (.rd j)) = some val → D.pend (.rd j) ≠ none →
      (alg1 rnd v₀).runFrom D γ = some D' →
      respsOf γ (.rd j) = [] ∨ (respsOf γ (.rd j)).head? = some (.val val)
  | [], _, _, _, _, _ => Or.inl rfl
  | ℓ :: γ, D, D', hf, hp, h => by
    simp only [Impl.runFrom] at h
    cases hs : (alg1 rnd v₀).step D ℓ with
    | none => simp [hs] at h
    | some D1 =>
      rw [hs, Option.bind_some] at h
      by_cases hq : ℓ.proc = .rd j
      · cases ℓ with
        | inv q o =>
          simp only [Label.proc] at hq; subst hq
          exact absurd (Impl.step_inv hs).1 hp
        | ret q r =>
          simp only [Label.proc] at hq; subst hq
          obtain ⟨-, -, -, l, hact, -⟩ := Impl.step_ret hs
          right
          cases hl : D.loc (.rd j) <;> rw [hl] at hf hact <;>
            simp only [fixedVal, reduceCtorEq, Option.some.injEq] at hf <;>
            simp only [alg1, readerAct, reduceCtorEq, Action.ret.injEq] at hact
          obtain ⟨rfl, -⟩ := hact
          subst hf
          simp [respsOf_cons]
        | tau q =>
          simp only [Label.proc] at hq; subst hq
          obtain ⟨-, hpend, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
          have hp1 : D1.pend (.rd j) ≠ none := by rw [hpend]; exact hp
          have hf1 : fixedVal (D1.loc (.rd j)) = some val := by
            cases hl : D.loc (.rd j) <;> rw [hl] at hf hact <;>
              simp only [fixedVal, reduceCtorEq, Option.some.injEq] at hf <;>
              simp only [alg1, readerAct, reduceCtorEq] at hact
            simp only [Action.access.injEq] at hact
            obtain ⟨rfl, ho, hk⟩ := hact
            obtain rfl := eq_of_heq ho
            obtain rfl := eq_of_heq hk
            simp [hloc, fixedVal, hf]
          have := resp_of_fixed γ hf1 hp1 h
          simpa [respsOf_cons] using this
      · have h1 := Impl.step_other hs hq
        have := resp_of_fixed γ (by rw [h1.1]; exact hf) (by rw [h1.2]; exact hp) h
        rw [respsOf_cons, Label.retOf_eq_none_of_proc_ne hq]
        simpa using this

end Extension

section Forward

/-- **Claim 4 (if).** A pending read that has applied fetch&xor or read `SN = prev_sn` is
effective: it returns the value it is bound to in every indistinguishable execution. -/
theorem effective_of_fixed {rnd : ℕ → Fin m → Bool}
    {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j : Fin m} {val : V}
    (hf : fixedVal (C.loc (.rd j)) = some val) :
    Impl.EffectiveFam (alg1F W Au v₀) rnd α (curOp α (.rd j)) (.val val) := by
  intro θ' β hβ hind γ hγ r' hr'
  obtain ⟨D, hD⟩ := hβ
  obtain ⟨hloc, -, hresps⟩ := Impl.IndistFam.loc_eq (I := alg1F W Au v₀) hα hD hind
    (fun _ => rfl) (fun _ _ => rfl)
  have hI := Inv.of_run (rnd := θ') hD
  have hfD : fixedVal (D.loc (.rd j)) = some val := by rw [← hloc]; exact hf
  have hpD : D.pend (.rd j) ≠ none := by
    obtain ⟨-, hr⟩ := hI.rd j
    cases hl : D.loc (.rd j) <;> rw [hl] at hfD hr <;> simp [fixedVal] at hfD
    · rw [hr.1]; simp
    · rw [hr.1]; simp
  obtain ⟨D', hD'⟩ := hγ
  have hrun : (alg1 θ' v₀).runFrom D γ = some D' := by
    have := hD'
    rw [Impl.run, Impl.runFrom_append, show (alg1F W Au v₀ θ').runFrom
      (alg1F W Au v₀ θ').initCfg β = some D from hD] at this
    simpa using this
  simp only [respOf, curOp, respsOf_append, hresps] at hr'
  rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hr'
  rcases resp_of_fixed (rnd := θ') γ hfD hpD hrun with h | h
  · rw [h] at hr'; simp at hr'
  · rw [List.head?_eq_getElem?] at h
    rw [h] at hr'
    exact (Option.some.inj hr').symm

/-- A completed operation is effective for its response. -/
theorem effective_of_completed {rnd : ℕ → Fin m → Bool}
    {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {x : OpId (Proc m W Au)} {r : (auditReg m V v₀).Resp}
    (hr : respOf α x = some r) : Impl.EffectiveFam (alg1F W Au v₀) rnd α x r := by
  intro θ' β hβ hind γ hγ r' hr'
  obtain ⟨D, hD⟩ := hβ
  have hresps : respsOf α x.1 = respsOf β x.1 := by
    rw [(alg1 rnd v₀).respsOf_eq_obs hα, (alg1 θ' v₀).respsOf_eq_obs hD]
    have h2 := (Prod.mk.inj hind).2
    simp only [Impl.procView] at h2
    rw [h2]
  have hc : x.2 < (respsOf β x.1).length := by
    rw [← hresps]; exact (completed_iff_respOf.2 (by rw [hr]; rfl))
  simp only [respOf, respsOf_append] at hr' hr
  rw [List.getElem?_append_left hc, ← hresps, hr] at hr'
  exact (Option.some.inj hr').symm

end Forward

end Podc.AuditingWithoutLeaks

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

section Solo

/-- Reachable configurations. -/
def Reach (rnd : ℕ → Fin m → Bool) (C : Cfg m W Au V v₀) : Prop :=
  ∃ α : List (Label (Proc m W Au) (auditReg m V v₀)), (alg1 rnd v₀).run α = some C

lemma Reach.runFrom {C D : Cfg m W Au V v₀} (hC : Reach rnd C)
    {γ : List (Label (Proc m W Au) (auditReg m V v₀))} (h : (alg1 rnd v₀).runFrom C γ = some D) :
    Reach rnd D := by
  obtain ⟨α, hα⟩ := hC
  exact ⟨α ++ γ, by rw [Impl.run, Impl.runFrom_append]; simp [Impl.run] at hα; simp [hα, h]⟩

lemma Reach.step {C D : Cfg m W Au V v₀} (hC : Reach rnd C)
    {ℓ : Label (Proc m W Au) (auditReg m V v₀)} (h : (alg1 rnd v₀).step C ℓ = some D) :
    Reach rnd D := hC.runFrom (γ := [ℓ]) (by simp [Impl.runFrom, h])

lemma sn_mono {C D : Cfg m W Au V v₀} (hC : Reach rnd C)
    {γ : List (Label (Proc m W Au) (auditReg m V v₀))} (h : (alg1 rnd v₀).runFrom C γ = some D) :
    snOf C ≤ snOf D := by
  induction γ generalizing C with
  | nil => simp [Impl.runFrom] at h; subst h; rfl
  | cons ℓ γ ih =>
    simp only [Impl.runFrom] at h
    cases hs : (alg1 rnd v₀).step C ℓ with
    | none => simp [hs] at h
    | some C1 =>
      rw [hs, Option.bind_some] at h
      have hC1 := hC.step hs
      obtain ⟨α, hα⟩ := hC
      have E := (Inv.step (Inv.of_run hα) hs).2
      exact E.sn.trans (ih hC1 h)

/-- Some solo run of a pending process returns. -/
lemma exists_solo_finish {C : Cfg m W Au V v₀} (hC : Reach rnd C) (p : Proc m W Au)
    (hp : C.pend p ≠ none) :
    ∃ γ D, (alg1 rnd v₀).runFrom C γ = some D ∧ (∀ ℓ ∈ γ, ℓ.proc = p) ∧
      (∀ ℓ ∈ γ, ∀ q o, ℓ ≠ .inv q o) ∧ D.pend p = none := by
  have hof := Impl.WaitFree.obstructionFree (I := alg1 (W := W) (Au := Au) rnd v₀) alg1_waitFree
  obtain ⟨k, hk⟩ := hof C p hC hp
  refine ⟨_, _, (alg1 rnd v₀).runFrom_soloLabels p C k, (alg1 rnd v₀).soloLabels_proc p C k,
    fun ℓ hℓ q o he => ?_, hk⟩
  subst he
  have h1 := (alg1 rnd v₀).opsOf_soloLabels p q C k
  have : o ∈ opsOf ((alg1 rnd v₀).soloLabels p C k) q := by
    simp only [opsOf, List.mem_filterMap]; exact ⟨_, hℓ, by simp⟩
  rw [h1] at this; simp at this

/-- Bookkeeping for a solo `write v` of writer `w` started with `SN = s0` and `R = r0`. -/
def Qw (w : W) (v : V) (s0 : ℕ) (r0 : RVal m V) (D : Cfg m W Au V v₀) : Prop :=
  match D.loc (.wr w) with
  | .wSN v' => v' = v ∧ snOf D = s0 ∧ rOf D = r0
  | .wR v' sn => v' = v ∧ sn = s0 + 1 ∧ snOf D = s0 ∧ rOf D = r0
  | .wV v' sn r | .wB v' sn r _ | .wCAS v' sn r =>
      v' = v ∧ sn = s0 + 1 ∧ snOf D = s0 ∧ rOf D = r0 ∧ r = r0 ∧ r0.seq = s0
  | .wHelp sn => sn = s0 + 1 ∧ (rOf D).seq = s0 + 1 ∧ snOf D = s0 ∧ (r0.seq = s0 → (rOf D).val = v)
  | .wRet | .wIdle => snOf D = (rOf D).seq ∧ snOf D = s0 + 1 ∧ (r0.seq = s0 → (rOf D).val = v)
  | _ => False

lemma Qw.step {w : W} {v : V} {s0 : ℕ} {r0 : RVal m V} {D D' : Cfg m W Au V v₀}
    (hI : Inv rnd D) (hQ : Qw w v s0 r0 D) {ℓ : Label (Proc m W Au) (auditReg m V v₀)}
    (hℓ : ℓ.proc = .wr w) (hinv : ∀ q o, ℓ ≠ .inv q o)
    (hs : (alg1 rnd v₀).step D ℓ = some D') : Qw w v s0 r0 D' := by
  have hle := hI.sn_le
  have hle2 := hI.seq_le
  have hW := hI.wr w
  unfold WInv at hW
  cases ℓ with
  | inv q o => exact absurd rfl (hinv q o)
  | ret q r =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret hs
    have hR : rOf D' = rOf D := by simp [rOf, hmem]
    have hS : snOf D' = snOf D := by simp [snOf, hmem]
    unfold Qw at hQ ⊢
    rw [hloc, Function.update_self, hR, hS]
    cases hl : D.loc (.wr w) <;> rw [hl] at hQ hact hW <;>
      simp only [alg1, writerAct, reduceCtorEq, Action.ret.injEq] at hact
    case wB v' sn r' todo =>
      cases todo with
      | nil => exact absurd rfl hW.2.2.2.1
      | cons j rest => simp at hact
    all_goals first
      | (obtain ⟨-, rfl⟩ := hact; exact hQ)
      | exact hQ.elim
  | tau q =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨-, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
    have hnew : D'.loc (.wr w) = k ((BO m V v₀ i).δ (D.mem i) o).2 := by simp [hloc]
    unfold Qw at hQ ⊢
    cases hl : D.loc (.wr w) <;> rw [hl] at hQ hW <;>
      simp only [alg1, writerAct, hl, reduceCtorEq] at hact
    case wSN v' =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact; obtain rfl := eq_of_heq ho; obtain rfl := eq_of_heq hk
      obtain ⟨h1, h2, h3⟩ := hQ
      have hR : rOf D' = rOf D := by simp [rOf, hmem]
      have hS : snOf D' = snOf D := by simp [snOf, hmem]
      have hnew' : D'.loc (.wr w) = .wR v' (snOf D + 1) := by simp [hnew, snOf]
      rw [hnew']
      exact ⟨h1, by rw [h2], by rw [hS, h2], by rw [hR, h3]⟩
    case wR v' sn =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact; obtain rfl := eq_of_heq ho; obtain rfl := eq_of_heq hk
      obtain ⟨h1, h2, h3, h4⟩ := hQ
      have hR : rOf D' = rOf D := by simp [rOf, hmem]
      have hS : snOf D' = snOf D := by simp [snOf, hmem]
      by_cases hb : sn ≤ (rOf D).seq
      · have hnew' : D'.loc (.wr w) = .wHelp sn := by
          have : sn ≤ (D.mem .R : RVal m V).seq := hb
          simp [hnew, this]
        rw [hnew']
        refine ⟨h2, by rw [hR]; omega, by rw [hS, h3], fun h => ?_⟩
        rw [← h4] at h; omega
      · have hnew' : D'.loc (.wr w) = .wV v' sn (rOf D) := by
          have : ¬ sn ≤ (D.mem .R : RVal m V).seq := hb
          simp [hnew, this, rOf]
        rw [hnew']
        exact ⟨h1, h2, by rw [hS, h3], by rw [hR, h4], h4, by
          rw [← h4]; have h3' : snOf D = s0 := h3; omega⟩
    case wV v' sn r =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact; obtain rfl := eq_of_heq ho; obtain rfl := eq_of_heq hk
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hQ
      have hR : rOf D' = rOf D := by simp [rOf, hmem]
      have hS : snOf D' = snOf D := by simp [snOf, hmem]
      have hnew' : D'.loc (.wr w) = wBnext v' sn r (todoOf rnd r) := by simp [hnew]
      rw [hnew']
      cases todoOf rnd r <;>
        exact ⟨h1, h2, by rw [hS, h3], by rw [hR, h4], h5, h6⟩
    case wB v' sn r todo =>
      cases todo with
      | nil => simp at hact
      | cons j rest =>
        simp only [Action.access.injEq] at hact
        obtain ⟨rfl, ho, hk⟩ := hact; obtain rfl := eq_of_heq ho; obtain rfl := eq_of_heq hk
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hQ
        have hR : rOf D' = rOf D := by simp [rOf, hmem]
        have hS : snOf D' = snOf D := by simp [snOf, hmem]
        have hnew' : D'.loc (.wr w) = wBnext v' sn r rest := by simp [hnew]
        rw [hnew']
        cases rest <;>
          exact ⟨h1, h2, by rw [hS, h3], by rw [hR, h4], h5, h6⟩
    case wCAS v' sn r =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact; obtain rfl := eq_of_heq ho; obtain rfl := eq_of_heq hk
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hQ
      have heq : (D.mem .R : RVal m V) = r := by rw [h5]; exact h4
      have hRm : (D'.mem .R : RVal m V) = ⟨sn, v', rnd sn⟩ := by simp [hmem, heq]
      have hS : snOf D' = snOf D := by simp [snOf, hmem]
      have hR : rOf D' = ⟨sn, v', rnd sn⟩ := hRm
      have hnew' : D'.loc (.wr w) = .wHelp sn := by simp [hnew, heq]
      rw [hnew']
      exact ⟨h2, by rw [hR, h2], by rw [hS, h3], fun _ => by rw [hR, h1]⟩
    case wHelp sn =>
      simp only [Action.access.injEq] at hact
      obtain ⟨rfl, ho, hk⟩ := hact; obtain rfl := eq_of_heq ho; obtain rfl := eq_of_heq hk
      obtain ⟨h1, h2, h3, h4⟩ := hQ
      have hR : rOf D' = rOf D := by simp [rOf, hmem]
      have h3' : (D.mem .SN : ℕ) = sn - 1 := by
        have e : snOf D = s0 := h3
        have e2 : sn = s0 + 1 := h1
        simp only [snOf] at e
        rw [e, e2]; simp
      have hS : snOf D' = sn := by simp [snOf, hmem, casObject, h3']
      have hnew' : D'.loc (.wr w) = .wRet := by simp [hnew]
      rw [hnew']
      exact ⟨by rw [hS, hR, h2, h1], by rw [hS, h1], fun h => by rw [hR]; exact h4 h⟩

lemma Qw.run {w : W} {v : V} {s0 : ℕ} {r0 : RVal m V} :
    ∀ (γ : List (Label (Proc m W Au) (auditReg m V v₀))) {D D' : Cfg m W Au V v₀},
      Reach rnd D → Qw w v s0 r0 D → (∀ ℓ ∈ γ, ℓ.proc = .wr w) → (∀ ℓ ∈ γ, ∀ q o, ℓ ≠ .inv q o) →
      (alg1 rnd v₀).runFrom D γ = some D' → Qw w v s0 r0 D'
  | [], _, _, _, hQ, _, _, h => by simp [Impl.runFrom] at h; subst h; exact hQ
  | ℓ :: γ, D, D', hD, hQ, hp, hi, h => by
    simp only [Impl.runFrom] at h
    cases hs : (alg1 rnd v₀).step D ℓ with
    | none => simp [hs] at h
    | some D1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨α, hα⟩ := hD
      have hQ1 := Qw.step (Inv.of_run hα) hQ (hp ℓ (by simp)) (hi ℓ (by simp)) hs
      exact Qw.run γ (Reach.step ⟨α, hα⟩ hs) hQ1 (fun ℓ' h' => hp ℓ' (by simp [h']))
        (fun ℓ' h' => hi ℓ' (by simp [h'])) h

/-- A solo `write v` by an idle writer: afterwards `SN = R.seq`, and if it started in an `E`
phase, it was visible (`R.val = v`, `SN` increased). -/
lemma solo_write {C : Cfg m W Au V v₀} (hC : Reach rnd C) {w : W} (hidle : C.pend (.wr w) = none)
    (v : V) :
    ∃ γ C2, (alg1 rnd v₀).runFrom C γ = some C2 ∧ (∀ ℓ ∈ γ, ℓ.proc = .wr w) ∧
      C2.pend (.wr w) = none ∧ snOf C2 = (rOf C2).seq ∧ snOf C2 = snOf C + 1 ∧
      ((rOf C).seq = snOf C → (rOf C2).val = v) := by
  obtain ⟨α, hα⟩ := hC
  have hI := Inv.of_run hα
  have hl := (hI.wr w).idle hidle
  have hs1 := (alg1 rnd v₀).step_inv_eq_some (o := .write v) hidle trivial
  obtain ⟨C1, hs1', hl1, hm1, hp1⟩ : ∃ C1, (alg1 rnd v₀).step C (.inv (.wr w) (.write v)) = some C1 ∧
      C1.loc (.wr w) = .wSN v ∧ C1.mem = C.mem ∧ C1.pend (.wr w) = some (.write v) :=
    ⟨_, hs1, by simp [hl, alg1, invoke], rfl, by simp⟩
  have hR1 : Reach rnd C1 := Reach.step ⟨α, hα⟩ hs1'
  have hQ1 : Qw w v (snOf C) (rOf C) C1 := by
    simp only [Qw, hl1]
    exact ⟨trivial, by simp [snOf, hm1], by simp [rOf, hm1]⟩
  obtain ⟨γ, D, hD, hp, hi, hpend⟩ := exists_solo_finish hR1 (.wr w) (by simp [hp1])
  have hQ := Qw.run γ hR1 hQ1 hp hi hD
  obtain ⟨α', hα'⟩ := hR1.runFrom hD
  have hlD := ((Inv.of_run hα').wr w).idle hpend
  unfold Qw at hQ
  rw [hlD] at hQ
  obtain ⟨h1, h2, h3⟩ := hQ
  refine ⟨.inv (.wr w) (.write v) :: γ, D, by simp [Impl.runFrom, hs1', hD], ?_, hpend, h1, h2, h3⟩
  intro ℓ hℓ
  rcases List.mem_cons.1 hℓ with rfl | h
  · rfl
  · exact hp ℓ h

lemma reader_readSN {D : Cfg m W Au V v₀} {j : Fin m} {prev : Option (ℕ × V)}
    (hl : D.loc (.rd j) = .rSN prev) (hp : D.pend (.rd j) ≠ none)
    (hne : prev.map Prod.fst ≠ some (snOf D)) :
    ∃ D', (alg1 rnd v₀).step D (.tau (.rd j)) = some D' ∧ D'.loc (.rd j) = .rFX prev (snOf D) ∧
      D'.mem = D.mem ∧ D'.pend = D.pend := by
  cases prev with
  | none =>
    have hact : (alg1 (W := W) (Au := Au) rnd v₀).act (.rd j) (D.loc (.rd j)) =
        .access Obj.SN CASOp.read (fun x => match x with
          | .inl y => if (none : Option (ℕ × V)).map Prod.fst = some y then .rFX none y
            else .rFX none y
          | .inr _ => .rFX none 0) := by rw [hl]; rfl
    exact ⟨_, Impl.step_tau_eq_some hp hact, by simp [snOf], by simp, rfl⟩
  | some xp =>
    obtain ⟨x, pv⟩ := xp
    have hact : (alg1 (W := W) (Au := Au) rnd v₀).act (.rd j) (D.loc (.rd j)) =
        .access Obj.SN CASOp.read (fun z => match z with
          | .inl y => if (some (x, pv)).map Prod.fst = some y then .rRet (some (x, pv)) pv
            else .rFX (some (x, pv)) y
          | .inr _ => .rFX (some (x, pv)) 0) := by rw [hl]; rfl
    refine ⟨_, Impl.step_tau_eq_some hp hact, ?_, by simp, rfl⟩
    have : ¬ (some (x, pv)).map Prod.fst = some (D.mem .SN) := hne
    simp only [Option.map_some] at this
    simp [this, snOf]

lemma reader_fetch {D : Cfg m W Au V v₀} {j : Fin m} {prev : Option (ℕ × V)} {y : ℕ}
    (hl : D.loc (.rd j) = .rFX prev y) (hp : D.pend (.rd j) ≠ none) :
    ∃ D', (alg1 rnd v₀).step D (.tau (.rd j)) = some D' ∧
      D'.loc (.rd j) = .rCAS prev (rOf D).seq (rOf D).val ∧ D'.pend = D.pend := by
  have hact : (alg1 (W := W) (Au := Au) rnd v₀).act (.rd j) (D.loc (.rd j)) =
      .access Obj.R (ROp.fx j) (fun x => match x with
        | .inl r => .rCAS prev r.seq r.val
        | .inr _ => .rIdle prev) := by rw [hl]; rfl
  exact ⟨_, Impl.step_tau_eq_some hp hact, by simp [rOf], rfl⟩

lemma resps_ne_nil {p : Proc m W Au} :
    ∀ (γ : List (Label (Proc m W Au) (auditReg m V v₀))) {D D' : Cfg m W Au V v₀},
      (alg1 rnd v₀).runFrom D γ = some D' → D.pend p ≠ none → D'.pend p = none →
      respsOf γ p ≠ []
  | [], _, _, h, h1, h2 => by simp [Impl.runFrom] at h; subst h; exact absurd h2 h1
  | ℓ :: γ, D, D', h, h1, h2 => by
    simp only [Impl.runFrom] at h
    cases hs : (alg1 rnd v₀).step D ℓ with
    | none => simp [hs] at h
    | some D1 =>
      rw [hs, Option.bind_some] at h
      rw [respsOf_cons]
      by_cases hq : ℓ.proc = p
      · cases ℓ with
        | inv q o =>
          simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv hs).1 h1
        | ret q r => simp only [Label.proc] at hq; subst hq; simp
        | tau q =>
          simp only [Label.proc] at hq; subst hq
          have hp1 : D1.pend q ≠ none := by rw [(Impl.step_tau hs).2.1]; exact h1
          have := resps_ne_nil γ h hp1 h2
          simpa using this
      · have hp1 : D1.pend p ≠ none := by rw [(Impl.step_other hs hq).2]; exact h1
        have := resps_ne_nil γ h hp1 h2
        simpa [Label.retOf_eq_none_of_proc_ne hq] using this

end Solo

end Podc.AuditingWithoutLeaks

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

section Converse

lemma respsOf_of_proc_ne {γ : List (Label (Proc m W Au) (auditReg m V v₀))} {p q : Proc m W Au}
    (h : ∀ ℓ ∈ γ, ℓ.proc = p) (hq : p ≠ q) : respsOf γ q = [] :=
  respsOf_eq_nil_of_proc_ne fun ℓ hℓ => by rw [h ℓ hℓ]; exact hq

/-- From a configuration in which reader `j`'s read has not yet fetched (nor is silent), some
writer can make the read return any value `v`. -/
lemma ext_returns {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j : Fin m} (w : W) (v : V)
    (hpend : C.pend (.rd j) ≠ none)
    (hst : (∃ prev, C.loc (.rd j) = .rSN prev) ∨ (∃ prev y, C.loc (.rd j) = .rFX prev y)) :
    ∃ γ, (alg1 rnd v₀).Valid (α ++ γ) ∧ respOf (α ++ γ) (curOp α (.rd j)) = some (AResp.val v) := by
  have hC : Reach rnd C := ⟨α, hα⟩
  have hne : (Proc.wr w : Proc m W Au) ≠ Proc.rd j := by simp
  -- complete the writer's pending operation
  obtain ⟨γ0, C0, h0, hp0, hw0⟩ : ∃ γ0 C0, (alg1 rnd v₀).runFrom C γ0 = some C0 ∧
      (∀ ℓ ∈ γ0, ℓ.proc = .wr w) ∧ C0.pend (.wr w) = none := by
    by_cases hw : C.pend (.wr w) = none
    · exact ⟨[], C, rfl, by simp, hw⟩
    · obtain ⟨γ0, C0, h0, hp0, -, hw0⟩ := exists_solo_finish hC (.wr w) hw
      exact ⟨γ0, C0, h0, hp0, hw0⟩
  have hC0 := hC.runFrom h0
  obtain ⟨γ1, C1, h1, hp1, hw1, hs1, hs1', -⟩ := solo_write hC0 hw0 v
  have hC1 := hC0.runFrom h1
  obtain ⟨γ2, C2, h2, hp2, hw2, -, hs2, hv2⟩ := solo_write hC1 hw1 v
  have hv2' : (rOf C2).val = v := hv2 hs1.symm
  have hC2 := hC1.runFrom h2
  have hsn0 := sn_mono hC h0
  -- the reader did not move
  have hr0 := Impl.runFrom_other _ h0 (q := .rd j) (fun ℓ hℓ => by rw [hp0 ℓ hℓ]; exact hne)
  have hr1 := Impl.runFrom_other _ h1 (q := .rd j) (fun ℓ hℓ => by rw [hp1 ℓ hℓ]; exact hne)
  have hr2 := Impl.runFrom_other _ h2 (q := .rd j) (fun ℓ hℓ => by rw [hp2 ℓ hℓ]; exact hne)
  have hloc2 : C2.loc (.rd j) = C.loc (.rd j) := by rw [hr2.1, hr1.1, hr0.1]
  have hpend2 : C2.pend (.rd j) = C.pend (.rd j) := by rw [hr2.2, hr1.2, hr0.2]
  -- the reader fetches `R = (_, v, _)`
  obtain ⟨ρ, C4, h4, hρ4, hf4, hp4⟩ : ∃ ρ C4, (alg1 rnd v₀).runFrom C2 ρ = some C4 ∧
      (∀ ℓ ∈ ρ, ℓ = .tau (.rd j)) ∧ fixedVal (C4.loc (.rd j)) = some v ∧
      C4.pend (.rd j) ≠ none := by
    rcases hst with ⟨prev, hl⟩ | ⟨prev, y, hl⟩
    · have hI := Inv.of_run hα
      obtain ⟨-, hr⟩ := hI.rd j
      rw [hl] at hr
      have hnm : prev.map Prod.fst ≠ some (snOf C2) := by
        intro h
        obtain ⟨⟨x, pv⟩, rfl, hx⟩ := Option.map_eq_some_iff.1 h
        have := (hr.2 x pv rfl).1
        simp only at hx
        have := hsn0
        omega
      obtain ⟨C3, h3, hl3, hm3, hpe3⟩ := reader_readSN (rnd := rnd) (by rw [hloc2, hl])
        (by rw [hpend2]; exact hpend) hnm
      obtain ⟨C4, h4, hl4, hpe4⟩ := reader_fetch (rnd := rnd) hl3 (by rw [hpe3, hpend2]; exact hpend)
      refine ⟨[.tau (.rd j), .tau (.rd j)], C4, by simp [Impl.runFrom, h3, h4], by simp,
        ?_, by rw [hpe4, hpe3, hpend2]; exact hpend⟩
      have hR3 : rOf C3 = rOf C2 := by simp [rOf, hm3]
      rw [hl4, hR3, hv2']; rfl
    · obtain ⟨C4, h4, hl4, hpe4⟩ := reader_fetch (rnd := rnd) (by rw [hloc2, hl] : C2.loc (.rd j) = _)
        (by rw [hpend2]; exact hpend)
      exact ⟨[.tau (.rd j)], C4, by simp [Impl.runFrom, h4], by simp,
        by rw [hl4, hv2']; rfl, by rw [hpe4, hpend2]; exact hpend⟩
  have hC4 := hC2.runFrom h4
  obtain ⟨γ5, C5, h5, -, -, hp5⟩ := exists_solo_finish hC4 (.rd j) hp4
  have hhead : (respsOf γ5 (.rd j)).head? = some (.val v) := by
    rcases resp_of_fixed (rnd := rnd) γ5 hf4 hp4 h5 with h | h
    · exact absurd h (resps_ne_nil γ5 h5 hp4 hp5)
    · exact h
  refine ⟨γ0 ++ γ1 ++ γ2 ++ ρ ++ γ5, ⟨C5, ?_⟩, ?_⟩
  · rw [Impl.run, Impl.runFrom_append]
    simp only [Impl.run] at hα
    simp [hα, Impl.runFrom_append, h0, h1, h2, h4, h5]
  · have hρ : respsOf ρ (.rd j) = [] := by
      simp only [respsOf, List.filterMap_eq_nil_iff]
      intro ℓ hℓ; rw [hρ4 ℓ hℓ]; rfl
    have h0r := respsOf_of_proc_ne hp0 hne
    have h1r := respsOf_of_proc_ne hp1 hne
    have h2r := respsOf_of_proc_ne hp2 hne
    simp only [respOf, curOp, respsOf_append, h0r, h1r, h2r, hρ, List.nil_append]
    rw [List.getElem?_append_right le_rfl, Nat.sub_self, ← List.head?_eq_getElem?, hhead]

end Converse

end Podc.AuditingWithoutLeaks

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

section Audit

lemma fetched_le {C : Cfg m W Au V v₀} {j : Fin m} {t : ℕ} (h : Fetched rnd C j t) :
    t ≤ (rOf C).seq := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- What an audit in progress guarantees about a fetch at sequence number `t` (by reader `j`)
that happened before its invocation. -/
def AuP (rnd : ℕ → Fin m → Bool) (j : Fin m) (t : ℕ) (u : V) : Loc m V → Prop
  | .aV _ r _ | .aB _ r _ _ _ | .aCAS _ r => t < r.seq ∨ (t = r.seq ∧ readersOf rnd r j)
  | .aRet A _ => (j, u) ∈ A
  | _ => True

/-- Steps keep the guarantee of a pending audit. -/
lemma AuP.step {C C' : Cfg m W Au V v₀} (hI : Inv rnd C) {a : Au} {j : Fin m} {t : ℕ} {u : V}
    (hf : Fetched rnd C j t) (hu : hv v₀ C t = u) (hP : AuP rnd j t u (C.loc (.au a)))
    (hs : (alg1 rnd v₀).step C (.tau (.au a)) = some C') : AuP rnd j t u (C'.loc (.au a)) := by
  obtain ⟨-, -, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau hs
  have hnew : C'.loc (.au a) = k ((BO m V v₀ i).δ (C.mem i) o).2 := by simp [hloc]
  have hA := hI.au a
  unfold AInv at hA
  have hle := fetched_le hf
  cases hl : C.loc (.au a) <;> rw [hl] at hP hA <;> simp only [alg1, auditorAct, hl, reduceCtorEq] at hact
  all_goals
    simp only [Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact; obtain rfl := eq_of_heq ho; obtain rfl := eq_of_heq hk
  case aR A lsa =>
    have h1 : C'.loc (.au a) = aNext rnd A (rOf C) lsa := by simp [hnew, rOf]
    rw [h1]
    have key : t < (rOf C).seq ∨ (t = (rOf C).seq ∧ readersOf rnd (rOf C) j) := by
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact Or.inl h
      · subst h
        rcases hf with ⟨h, -⟩ | ⟨-, h⟩
        · omega
        · exact Or.inr ⟨rfl, h⟩
    unfold aNext; split_ifs <;> exact key
  case aV A r s =>
    have h1 : C'.loc (.au a) = aVnext rnd A r s (C.mem (.V s)) := by simp [hnew]
    rw [h1]; unfold aVnext; split_ifs
    · exact hP
    · unfold aNext; split_ifs <;> exact hP
  case aB A r s val j' =>
    have h1 : C'.loc (.au a) = aBnext rnd (addPair A j' val (C.mem (.B s j'))) r s val j' := by
      simp [hnew]
    rw [h1]; unfold aBnext; split_ifs
    · exact hP
    · unfold aNext; split_ifs <;> exact hP
  case aCAS A r =>
    have h1 : C'.loc (.au a) = .aRet A r.seq := by simp [hnew]
    rw [h1]
    show (j, u) ∈ A
    obtain ⟨-, hok, hT⟩ := hA
    rw [hT]
    rcases hP with h | ⟨rfl, h⟩
    · exact Or.inl ⟨t, h, hf, hu.symm⟩
    · exact Or.inr ⟨h, by rw [← hu, hok.2.1]⟩

/-- **Lemma 5 (core).** If reader `j` had applied fetch&xor at sequence number `t` by the end of
`α`, then every audit invoked after `α` that returns reports `(j, value of t)`. -/
theorem audit_reports {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j : Fin m} {t : ℕ} (hf : Fetched rnd C j t)
    {a : Au} {n : ℕ} (hy : ¬ Invoked α (.au a, n))
    {γ : List (Label (Proc m W Au) (auditReg m V v₀))} (hγ : (alg1 rnd v₀).Valid (α ++ γ))
    {S : Set (Fin m × V)} (hr : respOf (α ++ γ) (.au a, n) = some (.set S)) :
    (j, hv v₀ C t) ∈ S := by
  set u := hv v₀ C t
  let Q : List (Label (Proc m W Au) (auditReg m V v₀)) → Cfg m W Au V v₀ → Prop := fun δ D =>
    Fetched rnd D j t ∧ hv v₀ D t = u ∧
    (n < (opsOf (α ++ δ) (.au a)).length →
      (n < (respsOf (α ++ δ) (.au a)).length ∧
        ∀ S, respOf (α ++ δ) (.au a, n) = some (.set S) → (j, u) ∈ S) ∨
      ((respsOf (α ++ δ) (.au a)).length = n ∧ D.pend (.au a) ≠ none ∧
        AuP rnd j t u (D.loc (.au a))))
  have key : ∀ δ D, (alg1 rnd v₀).run (α ++ δ) = some D → Q δ D := by
    intro δ
    induction δ using List.reverseRecOn with
    | nil =>
      intro D hD
      rw [List.append_nil, hα] at hD; cases hD
      exact ⟨hf, rfl, fun h => absurd h (by simpa [Invoked] using hy)⟩
    | append_singleton δ ℓ ih =>
      intro D' hD'
      rw [← List.append_assoc, Impl.run_concat] at hD'
      cases hD : (alg1 rnd v₀).run (α ++ δ) with
      | none => simp [hD] at hD'
      | some D =>
        rw [hD, Option.bind_some] at hD'
        obtain ⟨hf1, hu1, hst⟩ := ih D hD
        have hI := Inv.of_run hD
        obtain ⟨-, E⟩ := Inv.step hI hD'
        have hle := fetched_le hf1
        refine ⟨E.fet _ _ hf1, by rw [E.hv _ hle, hu1], ?_⟩
        rw [← List.append_assoc]
        by_cases hq : ℓ.proc = .au a
        · cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq
            obtain ⟨h0, -, hpend, hloc, -⟩ := Impl.step_inv hD'
            have hcnt := (alg1 rnd v₀).run_idle_counts hD h0
            have e1 : opsOf (α ++ δ ++ [Label.inv (Proc.au a) o]) (.au a) =
                opsOf (α ++ δ) (.au a) ++ [o] := by rw [opsOf_append]; simp [opsOf]
            have e2 : respsOf (α ++ δ ++ [Label.inv (Proc.au a) o]) (.au a) =
                respsOf (α ++ δ) (.au a) := by rw [respsOf_append]; simp [respsOf]
            have e3 : respOf (α ++ δ ++ [Label.inv (Proc.au a) o]) (.au a, n) =
                respOf (α ++ δ) (.au a, n) := by simp only [respOf, e2]
            rw [e1, e2, e3]
            intro hn
            simp only [List.length_append, List.length_singleton] at hn
            by_cases hold : n < (opsOf (α ++ δ) (.au a)).length
            · rcases hst hold with h | ⟨-, h, -⟩
              · exact Or.inl h
              · exact absurd h0 h
            · right
              refine ⟨by omega, by rw [hpend]; simp, ?_⟩
              obtain ⟨A, lsa, hl, -⟩ := (hI.au a).idle h0
              rw [hloc, Function.update_self, hl]
              cases o <;> simp [alg1, invoke, AuP]
          | tau q =>
            simp only [Label.proc] at hq; subst hq
            have hpend := (Impl.step_tau hD').2.1
            have e1 : opsOf (α ++ δ ++ [Label.tau (Proc.au a)]) (.au a) =
                opsOf (α ++ δ) (.au a) := by rw [opsOf_append]; simp [opsOf]
            have e2 : respsOf (α ++ δ ++ [Label.tau (Proc.au a)]) (.au a) =
                respsOf (α ++ δ) (.au a) := by rw [respsOf_append]; simp [respsOf]
            have e3 : respOf (α ++ δ ++ [Label.tau (Proc.au a)]) (.au a, n) =
                respOf (α ++ δ) (.au a, n) := by simp only [respOf, e2]
            rw [e1, e2, e3]
            intro hn
            rcases hst hn with h | ⟨h1, h2, h3⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, by rw [hpend]; exact h2, AuP.step hI hf1 hu1 h3 hD'⟩
          | ret q r =>
            simp only [Label.proc] at hq; subst hq
            obtain ⟨h0, -, -, l, hact, -⟩ := Impl.step_ret hD'
            have e1 : opsOf (α ++ δ ++ [Label.ret (Proc.au a) r]) (.au a) =
                opsOf (α ++ δ) (.au a) := by rw [opsOf_append]; simp [opsOf]
            have e2 : respsOf (α ++ δ ++ [Label.ret (Proc.au a) r]) (.au a) =
                respsOf (α ++ δ) (.au a) ++ [r] := by rw [respsOf_append]; simp [respsOf]
            rw [e1, e2, respOf_append_ret]
            intro hn
            left
            simp only [List.length_append, List.length_singleton]
            rcases hst hn with h | ⟨h1, h2, h3⟩
            · refine ⟨by omega, fun S hS => h.2 S ?_⟩
              rw [if_neg (by intro h'; simp only [Prod.mk.injEq] at h'; omega)] at hS
              exact hS
            · refine ⟨by omega, fun S hS => ?_⟩
              rw [if_pos (by rw [h1])] at hS
              cases hS
              have hA := hI.au a
              unfold AInv at hA
              cases hl : D.loc (.au a) <;> rw [hl] at hA h3 hact <;>
                simp only [alg1, auditorAct, reduceCtorEq, Action.ret.injEq] at hact
              case aRet A lsa => obtain ⟨h4, -⟩ := hact; cases h4; exact h3
              case aIdle A lsa => exact absurd hA.1 h2
              all_goals exact hA.elim
        · have h1 := Impl.step_other hD' hq
          have hops : opsOf (α ++ δ ++ [ℓ]) (.au a) = opsOf (α ++ δ) (.au a) := by
            simp [opsOf_append, Label.invOf_eq_none_of_proc_ne hq]
          have hresps : respsOf (α ++ δ ++ [ℓ]) (.au a) = respsOf (α ++ δ) (.au a) := by
            simp [respsOf_append, Label.retOf_eq_none_of_proc_ne hq]
          rw [hops, hresps]
          intro hn
          rcases hst hn with h | ⟨h2, h3, h4⟩
          · left
            refine ⟨h.1, fun S hS => h.2 S ?_⟩
            rwa [respOf, hresps] at hS
          · right
            exact ⟨h2, by rw [h1.2]; exact h3, by rw [h1.1]; exact h4⟩
  obtain ⟨D, hD⟩ := hγ
  obtain ⟨-, -, hst⟩ := key γ D hD
  have hc : n < (respsOf (α ++ γ) (.au a)).length := by
    have := completed_iff_respOf.2 (by rw [hr]; rfl); exact this
  have hinv : n < (opsOf (α ++ γ) (.au a)).length := by
    have := (alg1 rnd v₀).run_resps_le_ops hD (.au a); omega
  rcases hst hinv with h | ⟨h, -, -⟩
  · exact h.2 S hr
  · omega

end Audit

end Podc.AuditingWithoutLeaks

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

section Pairs

variable {K : Type} [DecidableEq K]

/-- A pair in the audit set of the abstract state comes from a read in the sequential history. -/
lemma mem_runOps_set {q : (auditReg m V v₀).State} :
    ∀ {L : List (K × (auditReg m V v₀).Op)}, (L.map Prod.fst).Nodup → ∀ {i : Fin m} {u : V},
      (i, u) ∈ ((auditReg m V v₀).runOps q (L.map Prod.snd)).2 →
      (i, u) ∈ q.2 ∨ ∃ x ∈ L, x.2 = .read i ∧
        (auditReg m V v₀).respIn q L x.1 = some (.val u)
  | [], _, _, _, h => Or.inl h
  | (k, o) :: L, hnd, i, u, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, ObjSpec.runOps_cons] at h
    rcases mem_runOps_set (q := ((auditReg m V v₀).δ q o).1) hnd.2 h with h1 | ⟨x, hx, h2, h3⟩
    · cases o with
      | read j =>
        rcases (Set.mem_insert_iff.1 h1) with he | he
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact Or.inr ⟨(k, .read i), by simp, rfl, by rw [ObjSpec.respIn_cons, if_pos rfl]⟩
        · exact Or.inl he
      | write w => exact Or.inl h1
      | audit => exact Or.inl h1
    · have hne : k ≠ x.1 := fun he => hnd.1 (List.mem_map.2 ⟨x, hx, he.symm⟩)
      exact Or.inr ⟨x, by simp [hx], h2, by rw [ObjSpec.respIn_cons, if_neg hne]; exact h3⟩

/-- A pair in an audit's response comes from a read before it in the sequential history. -/
lemma mem_audit_resp {q : (auditReg m V v₀).State} :
    ∀ {L : List (K × (auditReg m V v₀).Op)}, (L.map Prod.fst).Nodup → ∀ {y : K} {S : Set (Fin m × V)},
      (auditReg m V v₀).respIn q L y = some (.set S) → ∀ {i : Fin m} {u : V}, (i, u) ∈ S →
      (i, u) ∈ q.2 ∨ ∃ x ∈ L, x.2 = .read i ∧
        (auditReg m V v₀).respIn q L x.1 = some (.val u)
  | [], _, _, _, h, _, _, _ => by rw [ObjSpec.respIn_nil] at h; cases h
  | (k, o) :: L, hnd, y, S, h, i, u, hS => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [ObjSpec.respIn_cons] at h
    split_ifs at h with hk
    · cases o <;> simp [auditReg] at h
      subst h; exact Or.inl hS
    · rcases mem_audit_resp (q := ((auditReg m V v₀).δ q o).1) hnd.2 h hS with
        h1 | ⟨x, hx, h2, h3⟩
      · cases o with
        | read j =>
          rcases (Set.mem_insert_iff.1 h1) with he | he
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact Or.inr ⟨(k, .read i), by simp, rfl, by rw [ObjSpec.respIn_cons, if_pos rfl]⟩
          · exact Or.inl he
        | write w => exact Or.inl h1
        | audit => exact Or.inl h1
      · have hne : k ≠ x.1 := fun he => hnd.1 (List.mem_map.2 ⟨x, hx, he.symm⟩)
        exact Or.inr ⟨x, by simp [hx], h2, by rw [ObjSpec.respIn_cons, if_neg hne]; exact h3⟩

end Pairs

theorem LInv.of_run {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (h : (alg1 rnd v₀).run α = some C) : ∃ L Dl, LInv rnd α C L Dl := by
  refine Impl.run_induction (Q := fun α C => ∃ L Dl, LInv rnd α C L Dl) ⟨[], [], LInv.init⟩ ?_ h
  rintro α C ℓ C' hrun ⟨L, Dl, hL⟩ hs
  obtain ⟨M, Dl', h'⟩ := hL.step hrun hs
  exact ⟨_, _, h'⟩

end Podc.AuditingWithoutLeaks

namespace Podc.AuditingWithoutLeaks

open Cslib.SharedMemory

variable {m : ℕ} {W Au V : Type} [DecidableEq V] [DecidableEq W] [DecidableEq Au] {v₀ : V}
  {rnd : ℕ → Fin m → Bool}

section Paper

lemma set_mono {K : Type} {q : (auditReg m V v₀).State} :
    ∀ (L : List (K × (auditReg m V v₀).Op)), q.2 ⊆ ((auditReg m V v₀).runOps q (L.map Prod.snd)).2
  | [] => le_rfl
  | (k, o) :: L => by
    rw [List.map_cons, ObjSpec.runOps_cons]
    refine le_trans ?_ (set_mono (q := ((auditReg m V v₀).δ q o).1) L)
    cases o <;> simp [auditReg, Set.subset_insert]

/-- A read in the sequential history puts its pair into the audit set. -/
lemma mem_set_of_read {K : Type} [DecidableEq K] {q : (auditReg m V v₀).State} :
    ∀ {L : List (K × (auditReg m V v₀).Op)} {x : K} {i : Fin m} {u : V},
      (x, AOp.read i) ∈ L → (L.map Prod.fst).Nodup →
      (auditReg m V v₀).respIn q L x = some (.val u) →
      (i, u) ∈ ((auditReg m V v₀).runOps q (L.map Prod.snd)).2
  | [], _, _, _, h, _, _ => by simp at h
  | (k, o) :: L, x, i, u, hx, hnd, hr => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, ObjSpec.runOps_cons]
    rw [ObjSpec.respIn_cons] at hr
    split_ifs at hr with hk
    · subst hk
      have ho : o = AOp.read i := by
        rcases List.mem_cons.1 hx with h | h
        · exact (Prod.mk.inj h).2.symm
        · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hnd.1
      subst ho
      simp only [auditReg, Option.some.injEq, AResp.val.injEq] at hr
      subst hr
      exact set_mono (q := ((auditReg m V v₀).δ q (AOp.read i)).1) L (by simp [auditReg])
    · have hx' : (x, AOp.read i) ∈ L := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd (Prod.mk.inj h).1.symm hk
        · exact h
      exact mem_set_of_read hx' hnd.2 hr

lemma invoked_not_completed {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    {C : Cfg m W Au V v₀} (hα : (alg1 rnd v₀).run α = some C) {x : OpId (Proc m W Au)}
    (hi : Invoked α x) (hc : ¬ Completed α x) : x = curOp α x.1 ∧ C.pend x.1 ≠ none := by
  have h1 := (alg1 rnd v₀).run_resps_le_ops hα x.1
  simp only [Invoked, Completed] at hi hc
  by_cases hp : C.pend x.1 = none
  · have := (alg1 rnd v₀).run_idle_counts hα hp; omega
  · have := (alg1 rnd v₀).run_pend_counts hα hp
    refine ⟨?_, hp⟩
    obtain ⟨p, k⟩ := x
    simp only [curOp, Prod.mk.injEq, true_and] at *
    omega

/-- A read in the linearization with response `v` is `v`-effective. -/
theorem effective_of_mem_lin {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    {C : Cfg m W Au V v₀} (hα : (alg1 rnd v₀).run α = some C) {L Dl}
    (hL : LInv rnd α C L Dl) {x : OpId (Proc m W Au) × (auditReg m V v₀).Op} (hx : x ∈ L)
    {j : Fin m} (hop : x.2 = .read j) {v : V} (hr : respL v₀ L x.1 = some (.val v)) :
    ∃ k, Invoked α (.rd j, k) ∧
      Impl.EffectiveFam (alg1F W Au v₀) rnd α (.rd j, k) (.val v) := by
  have hinv := hL.lin.invoked_of_mem (List.mem_map_of_mem hx)
  have hopx := hL.lin.op_eq x hx
  rw [hop] at hopx
  have hproc : x.1.1 = .rd j := by
    have := (alg1 rnd v₀).allowed_of_mem_opsOf ⟨C, hα⟩
      (show AOp.read j ∈ opsOf α x.1.1 from List.mem_of_getElem? hopx)
    cases h : x.1.1 <;> simp_all [alg1, allowed]
  obtain ⟨⟨p, k⟩, o⟩ := x
  simp only at hproc hinv hopx hr; subst hproc
  refine ⟨k, hinv, ?_⟩
  by_cases hc : Completed α (.rd j, k)
  · obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
    have : respL v₀ L (Proc.rd j, k) = some r := hL.lin.respIn_eq hr'
    rw [this] at hr; cases hr
    exact effective_of_completed hα hr'
  · obtain ⟨hcur, hp⟩ := invoked_not_completed hα hinv hc
    simp only at hcur
    rw [hcur]
    have hst := hL.rd j
    unfold RSt at hst
    rw [← hcur] at hst
    have hmem : (Proc.rd j, k) ∈ L.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hx
    obtain ⟨-, hR⟩ := hL.inv.rd j
    cases hl : C.loc (.rd j) <;> rw [hl] at hst hR
    all_goals first
      | exact absurd hmem hst
      | skip
    case rIdle => exact absurd hR.1 hp
    case rCAS prev sn val =>
      rcases hst with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [hr] at h1; cases h1
        exact effective_of_fixed hα (by rw [hl]; rfl)
      · exact absurd hmem h1
    case rRet prev val =>
      rw [hr] at hst; cases hst
      exact effective_of_fixed hα (by rw [hl]; rfl)
    all_goals exact hR.elim

/-- A pending read whose value is fixed can be completed (with that value). -/
lemma complete_read {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j : Fin m} {u : V}
    (hf : fixedVal (C.loc (.rd j)) = some u) (hp : C.pend (.rd j) ≠ none) :
    ∃ γ, (alg1 rnd v₀).Valid (α ++ γ) ∧ respOf (α ++ γ) (curOp α (.rd j)) = some (AResp.val u) := by
  obtain ⟨γ, D, hD, -, -, hpD⟩ := exists_solo_finish ⟨α, hα⟩ (.rd j) hp
  have hhead : (respsOf γ (.rd j)).head? = some (.val u) := by
    rcases resp_of_fixed (rnd := rnd) γ hf hp hD with h | h
    · exact absurd h (resps_ne_nil γ hD hp hpD)
    · exact h
  refine ⟨γ, ⟨D, by rw [Impl.run, Impl.runFrom_append]; simp only [Impl.run] at hα; simp [hα, hD]⟩, ?_⟩
  simp only [respOf, curOp, respsOf_append]
  rw [List.getElem?_append_right le_rfl, Nat.sub_self, ← List.head?_eq_getElem?, hhead]

/-- Every fetch&xor of `p_j` (at a sequence number with value `v`) belongs to a `v`-effective
read (Theorem 8 / Lemma 3, "only effective reads are linearized"). -/
theorem effective_of_fetched {α : List (Label (Proc m W Au) (auditReg m V v₀))}
    {C : Cfg m W Au V v₀} (hα : (alg1 rnd v₀).run α = some C) {j : Fin m} {t : ℕ} {v : V}
    (hf : Fetched rnd C j t) (hvt : hv v₀ C t = v) :
    ∃ k, Invoked α (.rd j, k) ∧ Impl.EffectiveFam (alg1F W Au v₀) rnd α (.rd j, k) (.val v) := by
  obtain ⟨L, Dl, hL⟩ := LInv.of_run hα
  have hnd := hL.lin.nodup
  by_cases ht : t ≤ snOf C
  · have hmem : (j, v) ∈ (linState L).2 := by
      rw [hL.abs]; exact ⟨t, ht, hf, hvt.symm⟩
    rcases mem_runOps_set (q := (auditReg m V v₀).init) hnd hmem with h | ⟨x, hx, h1, h2⟩
    · simp [auditReg] at h
    · exact effective_of_mem_lin hα hL hx h1 h2
  · have hle := fetched_le hf
    have hseq := (Inv.of_run hα).seq_le
    have htseq : t = (rOf C).seq := by omega
    have hb : (rOf C).bits j ≠ rnd (rOf C).seq j := by
      rcases hf with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · rw [← htseq]; exact h
    have hj : Proc.rd j ∈ Dl := (hL.dl_readers j).2 ⟨by omega, hb⟩
    obtain ⟨prev, hl, -, hp⟩ := hL.dl_rd_info hj
    have hvv : (rOf C).val = v := by
      rw [← hvt, htseq]; simp [AuditingWithoutLeaks.hv]
    refine ⟨_, (Impl.run_pend_curOp hα hp).1, effective_of_fixed hα ?_⟩
    rw [hl, hvv]; rfl

variable [Nonempty W]

/-- **Claim 4.** With at least one writer and two values, a pending read of `p_j` is
`v`-effective iff `p_j` has applied fetch&xor to `R` obtaining `v`, or has read
`SN = prev_sn` with `prev_val = v`. -/
theorem claim4 (hV : ∃ v1 v2 : V, v1 ≠ v2)
    {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j : Fin m} (hp : C.pend (.rd j) ≠ none) (v : V) :
    Impl.EffectiveFam (alg1F W Au v₀) rnd α (curOp α (.rd j)) (.val v) ↔
      fixedVal (C.loc (.rd j)) = some v := by
  constructor
  · intro heff
    have hresp : ∀ γ u, (alg1 rnd v₀).Valid (α ++ γ) →
        respOf (α ++ γ) (curOp α (.rd j)) = some (AResp.val u) → u = v := by
      intro γ u hγ hr
      have := heff rnd α ⟨C, hα⟩ (Impl.IndistFam.refl _ _ _) γ hγ _ hr
      cases this; rfl
    obtain ⟨w⟩ := ‹Nonempty W›
    obtain ⟨v1, v2, h12⟩ := hV
    obtain ⟨-, hR⟩ := (Inv.of_run hα).rd j
    cases hl : C.loc (.rd j) <;> rw [hl] at hR
    case rIdle prev => exact absurd hR.1 hp
    case rSN prev =>
      obtain ⟨γ1, hv1, hr1⟩ := ext_returns hα w v1 hp (Or.inl ⟨prev, hl⟩)
      obtain ⟨γ2, hv2, hr2⟩ := ext_returns hα w v2 hp (Or.inl ⟨prev, hl⟩)
      exact absurd ((hresp _ _ hv1 hr1).trans (hresp _ _ hv2 hr2).symm) h12
    case rFX prev y =>
      obtain ⟨γ1, hv1, hr1⟩ := ext_returns hα w v1 hp (Or.inr ⟨prev, y, hl⟩)
      obtain ⟨γ2, hv2, hr2⟩ := ext_returns hα w v2 hp (Or.inr ⟨prev, y, hl⟩)
      exact absurd ((hresp _ _ hv1 hr1).trans (hresp _ _ hv2 hr2).symm) h12
    case rCAS prev sn val =>
      obtain ⟨γ, hγ, hr⟩ := complete_read hα (by rw [hl]; rfl : fixedVal (C.loc (.rd j)) = some val) hp
      simp only [fixedVal, hresp _ _ hγ hr]
    case rRet prev val =>
      obtain ⟨γ, hγ, hr⟩ := complete_read hα (by rw [hl]; rfl : fixedVal (C.loc (.rd j)) = some val) hp
      simp only [fixedVal, hresp _ _ hγ hr]
    all_goals exact hR.elim
  · intro hf
    exact effective_of_fixed hα hf

/-- A `v`-effective read by `p_j` exists in `α` iff `p_j` has applied fetch&xor while `R` held a
sequence number `t` whose value is `v`. -/
theorem effective_read_iff (hV : ∃ v1 v2 : V, v1 ≠ v2)
    {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) (j : Fin m) (v : V) :
    (∃ k, Invoked α (.rd j, k) ∧ Impl.EffectiveFam (alg1F W Au v₀) rnd α (.rd j, k) (.val v)) ↔
      ∃ t, Fetched rnd C j t ∧ hv v₀ C t = v := by
  obtain ⟨L, Dl, hL⟩ := LInv.of_run hα
  have hnd := hL.lin.nodup
  constructor
  · rintro ⟨k, hinv, heff⟩
    by_cases hc : Completed α (.rd j, k)
    · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
      have hrv : r = .val v := heff rnd α ⟨C, hα⟩ (Impl.IndistFam.refl _ _ _) []
        (by rw [List.append_nil]; exact ⟨C, hα⟩) r (by simpa using hr)
      subst hrv
      have hrL : respL v₀ L (.rd j, k) = some (.val v) := hL.lin.respIn_eq hr
      obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hL.lin.complete _ hc)
      have hop := hL.lin.op_eq x hx
      have hxread : x.2 = .read j := by
        have hall := (alg1 rnd v₀).allowed_of_mem_opsOf ⟨C, hα⟩
          (show x.2 ∈ opsOf α x.1.1 from List.mem_of_getElem? hop)
        rw [hx1] at hall
        revert hall; cases x.2 <;> simp [alg1, allowed]
      have hmem : ((Proc.rd j, k), (AOp.read j : (auditReg m V v₀).Op)) ∈ L := by
        rw [← hx1, ← hxread]; exact hx
      have := mem_set_of_read hmem hnd hrL
      rw [show (auditReg m V v₀).runOps (auditReg m V v₀).init (L.map Prod.snd) = linState L
        from rfl, hL.abs] at this
      obtain ⟨t, -, hf, hvt⟩ := this
      exact ⟨t, hf, hvt.symm⟩
    · obtain ⟨hcur, hp⟩ := invoked_not_completed hα hinv hc
      simp only at hcur hp
      rw [hcur] at heff
      have hfix := (claim4 hV hα hp v).1 heff
      obtain ⟨-, hR⟩ := (Inv.of_run hα).rd j
      cases hl : C.loc (.rd j) <;> rw [hl] at hR hfix <;> simp only [fixedVal, reduceCtorEq,
        Option.some.injEq] at hfix
      · subst hfix
        exact ⟨_, hR.2.2.2.2.2.2, hR.2.2.2.2.2.1.symm⟩
      · subst hfix
        obtain ⟨-, hprev, x, rfl⟩ := hR
        obtain ⟨-, h1, h2⟩ := hprev x _ rfl
        exact ⟨x, h2, h1.symm⟩
  · rintro ⟨t, hf, hvt⟩
    exact effective_of_fetched hα hf hvt

/-- **Lemma 5.** If `α` contains a `v`-effective read by `p_j`, then every audit invoked after
`α` that returns reports `(j, v)`. -/
theorem lemma5 (hV : ∃ v1 v2 : V, v1 ≠ v2)
    {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {j : Fin m} {v : V}
    (heff : ∃ k, Invoked α (.rd j, k) ∧
      Impl.EffectiveFam (alg1F W Au v₀) rnd α (.rd j, k) (.val v))
    {a : Au} {n : ℕ} (hy : ¬ Invoked α (.au a, n))
    {γ : List (Label (Proc m W Au) (auditReg m V v₀))} (hγ : (alg1 rnd v₀).Valid (α ++ γ))
    {S : Set (Fin m × V)} (hr : respOf (α ++ γ) (.au a, n) = some (.set S)) : (j, v) ∈ S := by
  obtain ⟨t, hf, hvt⟩ := (effective_read_iff hV hα j v).1 heff
  have := audit_reports hα hf hy hγ hr
  rwa [hvt] at this

end Paper

/-- **Theorem 8 (audits report only effective reads).** If an audit returns a set containing
`(j, v)` in `α`, then `α` contains a `v`-effective read by `p_j`. (No assumption on writers or
values is needed for this direction.) -/
theorem audit_sound {α : List (Label (Proc m W Au) (auditReg m V v₀))} {C : Cfg m W Au V v₀}
    (hα : (alg1 rnd v₀).run α = some C) {a : Au} {n : ℕ} {S : Set (Fin m × V)}
    (hr : respOf α (.au a, n) = some (.set S)) {j : Fin m} {v : V} (hjv : (j, v) ∈ S) :
    ∃ k, Invoked α (.rd j, k) ∧ Impl.EffectiveFam (alg1F W Au v₀) rnd α (.rd j, k) (.val v) := by
  obtain ⟨L, Dl, hL⟩ := LInv.of_run hα
  have hrL : respL v₀ L (.au a, n) = some (.set S) := hL.lin.respIn_eq hr
  rcases mem_audit_resp (q := (auditReg m V v₀).init) hL.lin.nodup hrL hjv with h | ⟨x, hx, h1, h2⟩
  · simp [auditReg] at h
  · exact effective_of_mem_lin hα hL hx h1 h2

end Podc.AuditingWithoutLeaks
