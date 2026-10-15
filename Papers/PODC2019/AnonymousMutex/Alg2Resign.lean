import Papers.PODC2019.AnonymousMutex.Alg2Inflation

/-!
# Algorithm 2: withdrawals ("resignations") are caused by bigger owners

A process `p` withdraws (line 6) when `owned < most_present` in its view. Combining the
no-inflation lemma with the exactness of `p`'s own count, a withdrawal of `p` while it owns
`c ≥ 1` registers implies that some other process `q` owned more than `c` registers at some time
of `p`'s last scan (`resign_bound`). We also show where scans start (`scan_start`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P]
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

/-- The view after the step of a process is unchanged or updated at one index with the value
read. -/
lemma view_step {s : St Id m} {x : Fin m} {f : Option Id → Option Id} {k : Option Id → St Id m}
    (h : (alg2 Id m).act s = .rmw x f k) (v : Option Id) :
    (k v).view = s.view ∨ ∃ i, ∃ hi : i < m, (k v).view = Function.update s.view ⟨i, hi⟩ v := by
  cases hpc : s.pc with
  | cas i =>
    by_cases hi : i < m
    · rw [act_cas hpc hi] at h; simp only [SymAction.rmw.injEq] at h; obtain ⟨-, -, rfl⟩ := h
      left; dsimp only; split_ifs <;> rfl
    · simp [alg2, hpc, hi] at h
  | read i =>
    by_cases hi : i < m
    · rw [act_read hpc hi] at h; simp only [SymAction.rmw.injEq] at h; obtain ⟨-, -, rfl⟩ := h
      right; refine ⟨i, hi, ?_⟩; dsimp only; split_ifs
      · rfl
      · unfold afterRead wrFrom; split_ifs <;> rfl
    · simp [alg2, hpc, hi] at h
  | wr i =>
    by_cases hi : i < m
    · rw [act_wr hpc hi] at h; simp only [SymAction.rmw.injEq] at h; obtain ⟨-, -, rfl⟩ := h
      left; dsimp only; unfold wrFrom; split_ifs <;> rfl
    · simp [alg2, hpc, hi] at h
  | wait i ab =>
    by_cases hi : i < m
    · rw [act_wait hpc hi] at h; simp only [SymAction.rmw.injEq] at h; obtain ⟨-, -, rfl⟩ := h
      left; dsimp only; split_ifs <;> rfl
    · simp [alg2, hpc, hi] at h
  | un i =>
    by_cases hi : i < m
    · rw [act_un hpc hi] at h; simp only [SymAction.rmw.injEq] at h; obtain ⟨-, -, rfl⟩ := h
      left; dsimp only; split_ifs <;> rfl
    · simp [alg2, hpc, hi] at h
  | rem => rw [act_rem hpc] at h; cases h
  | cs => rw [act_cs hpc] at h; cases h
  | retLock => rw [act_retLock hpc] at h; cases h
  | retUnlock => rw [act_retUnlock hpc] at h; cases h

lemma invoke_view (s : St Id m) (o : MutexOp) : ((alg2 Id m).invoke s o).view = s.view := by
  simp only [alg2]
  split <;> rfl

/-- The final view of a scan ending at `τ`. -/
def finalView (e : ((alg2 Id m).impl ids π).InfExec) (hm : 0 < m) (p : P) (τ : ℕ) :
    Fin m → Option Id :=
  Function.update ((e.cfg τ).loc p).view ⟨m - 1, by omega⟩ ((e.cfg τ).mem () (π p ⟨m - 1, by omega⟩))

section Exec

variable (hid : Function.Injective ids) (hm : 0 < m) {e : ((alg2 Id m).impl ids π).InfExec}
  {t₀ : ℕ} (H : Hyp e t₀)
include hid hm H

/-- View entries are `⊥` or process identifiers. -/
lemma view_inv (t : ℕ) (p : P) (x : Fin m) :
    ((e.cfg t).loc p).view x = none ∨ ∃ r, ((e.cfg t).loc p).view x = some (ids r) := by
  induction t generalizing p with
  | zero => left; rw [e.cfg_zero]; rfl
  | succ t ih =>
    have hstep := e.step_eq t
    cases hl : e.lbl t with
    | inv r o =>
      rw [hl] at hstep
      obtain ⟨-, hC⟩ := SymAlg.impl_step_inv_cases hstep
      rw [hC]
      by_cases hrp : p = r
      · subst hrp; simp only [Function.update_self, invoke_view]; exact ih p
      · simp only [Function.update_of_ne hrp]; exact ih p
    | ret r o =>
      rw [hl] at hstep
      obtain ⟨-, s, hact, hC⟩ := SymAlg.impl_step_ret_cases hstep
      rw [hC]
      by_cases hrp : p = r
      · subst hrp
        simp only [Function.update_self]
        rcases act_ret_cases ids π (H.locInv hid hm t p) hact with ⟨-, rfl⟩ | ⟨-, rfl⟩ | h | h
        · exact ih p
        · exact ih p
        · rw [act_rem h] at hact; cases hact; exact ih p
        · rw [act_cs h] at hact; cases hact; exact ih p
      · simp only [Function.update_of_ne hrp]; exact ih p
    | tau r =>
      obtain ⟨-, x', f, k, hact, hloc, -, -, hother⟩ := tau_step e hl
      by_cases hrp : p = r
      · subst hrp
        rw [hloc]
        rcases view_step hact ((e.cfg t).mem () (π p x')) with h | ⟨i, hi, h⟩
        · rw [h]; exact ih p
        · rw [h, Function.update_apply]
          split_ifs
          · exact (H.valInv hid hm t) _
          · exact ih p
      · rw [hother p hrp]; exact ih p

variable {p : P}

/-- During a read phase the own registers of `p` do not change. -/
lemma own_const_read {σ τ : ℕ}
    (hread : ∀ t, σ ≤ t → t ≤ τ → ∃ i, ((e.cfg t).loc p).pc = .read i) :
    ∀ t, σ ≤ t → t ≤ τ → own ids (e.cfg t) p = own ids (e.cfg σ) p := by
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base => rfl
  | succ t h1 ih =>
    rw [← ih (by omega)]
    by_cases hl : e.lbl t = .tau p
    · obtain ⟨-, x, f, k, hact, -, hmem, -⟩ := tau_step e hl
      obtain ⟨i, hi⟩ := hread t h1 (by omega)
      have hlt : i < m := by have := (H.locInv hid hm t p).2; rw [hi] at this; exact this.1
      rw [act_read hi hlt] at hact
      simp only [SymAction.rmw.injEq] at hact
      obtain ⟨rfl, rfl, rfl⟩ := hact
      unfold own; rw [hmem]; simp
    · exact H.own_frame hid hm hl

/-- A read phase can only be entered at index `0`. -/
lemma read_entry {s : ℕ} (hs : t₀ ≤ s) (h1 : ∀ i, ((e.cfg s).loc p).pc ≠ .read i) {i : ℕ}
    (h2 : ((e.cfg (s + 1)).loc p).pc = .read i) : i = 0 := by
  have hstep := e.step_eq s
  cases hl : e.lbl s with
  | ret r o => exact absurd hl (H.noret s hs r o)
  | inv r o =>
    rw [hl] at hstep
    obtain ⟨hpend, hC⟩ := SymAlg.impl_step_inv_cases hstep
    by_cases hrp : p = r
    · subst hrp
      rw [hC] at h2
      simp only [Function.update_self] at h2
      rcases H.phase hid hm hs p with ⟨hrem, -⟩ | ⟨hp, -⟩
      · simp [alg2, hrem] at h2
        cases o <;> simp_all
      · rw [hp] at hpend; cases hpend
    · rw [hC] at h2; simp only [Function.update_of_ne hrp] at h2; exact absurd h2 (h1 i)
  | tau r =>
    obtain ⟨-, x, f, k, hact, hloc, -, -, hother⟩ := tau_step e hl
    by_cases hrp : p = r
    · subst hrp
      rw [hloc] at h2
      have hL := (H.locInv hid hm s p).2
      cases hpc : ((e.cfg s).loc p).pc with
      | cas j =>
        rw [hpc] at hL
        rw [act_cas hpc hL] at hact
        simp only [SymAction.rmw.injEq] at hact; obtain ⟨-, -, rfl⟩ := hact
        dsimp only at h2; split_ifs at h2 <;> simp_all
      | read j => exact absurd hpc (h1 j)
      | wr j =>
        rw [hpc] at hL; obtain ⟨hj, -⟩ := hL
        rw [act_wr hpc hj] at hact
        simp only [SymAction.rmw.injEq] at hact; obtain ⟨-, -, rfl⟩ := hact
        dsimp only at h2; unfold wrFrom at h2; split_ifs at h2 <;> simp_all
      | wait j ab =>
        rw [hpc] at hL
        rw [act_wait hpc hL.1] at hact
        simp only [SymAction.rmw.injEq] at hact; obtain ⟨-, -, rfl⟩ := hact
        dsimp only at h2; split_ifs at h2 <;> simp_all
      | un j =>
        rw [hpc] at hL
        rw [act_un hpc hL.1] at hact
        simp only [SymAction.rmw.injEq] at hact; obtain ⟨-, -, rfl⟩ := hact
        dsimp only at h2; split_ifs at h2 <;> simp_all
      | rem => rw [act_rem hpc] at hact; cases hact
      | cs => rw [act_cs hpc] at hact; cases hact
      | retLock => rw [act_retLock hpc] at hact; cases hact
      | retUnlock => rw [act_retUnlock hpc] at hact; cases hact
    · rw [hother p hrp] at h2; exact absurd h2 (h1 i)

/-- The start of the scan containing time `b`, if `p` was not reading at time `a ≤ b`. -/
lemma scan_start {a b : ℕ} (ha0 : t₀ ≤ a) (ha : ∀ i, ((e.cfg a).loc p).pc ≠ .read i) (hab : a ≤ b)
    (hb : ∃ i, ((e.cfg b).loc p).pc = .read i) :
    ∃ σ, a < σ ∧ σ ≤ b ∧ ((e.cfg σ).loc p).pc = .read 0 ∧
      ∀ t, σ ≤ t → t ≤ b → ∃ i, ((e.cfg t).loc p).pc = .read i := by
  classical
  let Q : ℕ → Prop := fun k => ∀ t, b - k ≤ t → t ≤ b → ∃ i, ((e.cfg t).loc p).pc = .read i
  have hex : ∃ k, ¬ Q k := ⟨b - a, fun h => by
    obtain ⟨i, hi⟩ := h a (by omega) hab
    exact ha i hi⟩
  set k₀ := Nat.find hex with hk₀
  have hk₀spec : ¬ Q k₀ := Nat.find_spec hex
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · exfalso; apply hk₀spec; rw [h]; intro t h1 h2
      rw [show t = b by omega]; exact hb
    · exact h
  have hprev : Q (k₀ - 1) := not_not.1 (Nat.find_min hex (by omega))
  have hle : k₀ ≤ b - a := Nat.find_min' hex (fun h => by
    obtain ⟨i, hi⟩ := h a (by omega) hab
    exact ha i hi)
  -- the time `b - k₀` is not a read time
  have hnot : ∀ i, ((e.cfg (b - k₀)).loc p).pc ≠ .read i := by
    intro i hi
    apply hk₀spec
    intro t h1 h2
    by_cases ht : t = b - k₀
    · exact ⟨i, ht ▸ hi⟩
    · exact hprev t (by omega) h2
  refine ⟨b - k₀ + 1, by omega, by omega, ?_, fun t h1 h2 => hprev t (by omega) h2⟩
  obtain ⟨i, hi⟩ := hprev (b - k₀ + 1) (by omega) (by omega)
  have := read_entry hid hm H (by omega) hnot hi
  rw [hi, this]

/-- At the end of a scan, the own count of the view is exact. -/
lemma owned_finalView {τ : ℕ} (hτ : ((e.cfg τ).loc p).pc = .read (m - 1)) :
    owned (finalView e hm p τ) (ids p) = (own ids (e.cfg τ) p).card := by
  apply owned_eq_card_own ids π
  intro x
  have hL := (H.locInv hid hm τ p).2
  rw [hτ] at hL
  unfold finalView
  by_cases hx : x = ⟨m - 1, by omega⟩
  · rw [hx, Function.update_self]
  · rw [Function.update_of_ne hx]
    exact hL.2 x (by have : x.val ≠ m - 1 := fun h => hx (Fin.ext h); omega)

/-- **Withdrawals are caused by bigger owners.** If `p` withdraws at the end of a scan
`[σ, τ]` (with `t₀ ≤ σ`) while owning at least one register, then some process `q` owned more
registers than `p` at some time of the scan. -/
lemma resign_bound {σ τ : ℕ} (hσ : t₀ ≤ σ) (hσ0 : ((e.cfg σ).loc p).pc = .read 0)
    (hread : ∀ t, σ ≤ t → t ≤ τ → ∃ i, ((e.cfg t).loc p).pc = .read i) (hστ : σ ≤ τ)
    (hτ : ((e.cfg τ).loc p).pc = .read (m - 1))
    (hres : owned (finalView e hm p τ) (ids p) < mostPresent (finalView e hm p τ))
    (hpos : 0 < (own ids (e.cfg τ) p).card) :
    ∃ q t'', σ ≤ t'' ∧ t'' ≤ τ ∧ (own ids (e.cfg τ) p).card < (own ids (e.cfg t'') q).card := by
  set w := finalView e hm p τ with hw
  -- a register held by `p` during the whole scan
  obtain ⟨y₀, hy₀⟩ := Finset.card_pos.1 hpos
  have hconst := own_const_read hid hm H hread
  have hy : ∀ t, σ ≤ t → t ≤ τ → (e.cfg t).mem () y₀ = some (ids p) := by
    intro t h1 h2
    have : y₀ ∈ own ids (e.cfg t) p := by rw [hconst t h1 h2, ← hconst τ hστ le_rfl]; exact hy₀
    simpa [own] using this
  -- the most present value
  unfold mostPresent at hres
  rw [Finset.lt_sup_iff] at hres
  obtain ⟨x, -, hx⟩ := hres
  split_ifs at hx with hxn
  · omega
  -- it is the identifier of some process
  have hwx : w x = none ∨ ∃ r, w x = some (ids r) := by
    rw [hw]; unfold finalView
    rw [Function.update_apply]
    split_ifs
    · exact H.valInv hid hm τ _
    · exact view_inv hid hm H τ p x
  rcases hwx with hwx | ⟨q, hq⟩
  · exact absurd hwx hxn
  have hqp : q ≠ p := by
    intro hqp; subst hqp
    rw [hq] at hx
    unfold owned at hx
    omega
  obtain ⟨t'', h1, h2, h3⟩ := no_inflation hid hm H hqp hσ hread hy hσ0 hστ hτ
  refine ⟨q, t'', h1, h2, ?_⟩
  rw [← owned_finalView hid hm H hτ]
  rw [hq] at hx
  exact lt_of_lt_of_le hx h3

end Exec

end AnonymousMutex.Alg2
