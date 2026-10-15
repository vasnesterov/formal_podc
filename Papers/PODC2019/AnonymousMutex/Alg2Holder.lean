import Papers.PODC2019.AnonymousMutex.Alg2Resign

/-!
# Algorithm 2: a permanent owner

Let `c(t)` be the maximal number of registers owned by a process at time `t`, and `c*` its
eventual maximum (`exists_cstar`). If `c* ≥ 1`, then late withdrawals happen only with fewer than
`c*` registers (`claimA`, from `resign_bound`), processes erasing (line 7) late own fewer than
`c*` registers (`claimB`), and a process owning `c*` registers at a late time never withdraws
again: it stays in the first two loops forever and keeps its registers (`exists_holder`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P]
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}

/-- Program counters at which a process is neither reading (line 3) nor erasing (line 7). -/
def Neutral : PC → Prop
  | .cas _ | .wait _ _ | .rem => True
  | _ => False

/-- The latest time in `[a, b)` at which `Pr` fails, if it fails at `a` and holds at `b`. -/
lemma last_entry (Pr : ℕ → Prop) {a b : ℕ} (hab : a ≤ b) (ha : ¬ Pr a) (hb : Pr b) :
    ∃ s, a ≤ s ∧ s < b ∧ ¬ Pr s ∧ ∀ t, s < t → t ≤ b → Pr t := by
  classical
  have hex : ∃ k, ¬ Pr (b - k) := ⟨b - a, by rwa [show b - (b - a) = a by omega]⟩
  set k₀ := Nat.find hex
  have hk₀ : ¬ Pr (b - k₀) := Nat.find_spec hex
  have hle : k₀ ≤ b - a := Nat.find_min' hex (by rwa [show b - (b - a) = a by omega])
  have hpos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · rw [h, Nat.sub_zero] at hk₀; exact absurd hb hk₀
    · exact h
  refine ⟨b - k₀, by omega, by omega, hk₀, fun t h1 h2 => ?_⟩
  have := Nat.find_min hex (show b - t < k₀ by omega)
  rw [show b - (b - t) = t by omega] at this
  exact not_not.1 this

section Exec

variable (hid : Function.Injective ids) (hm : 0 < m) {e : ((alg2 Id m).impl ids π).InfExec}
  {t₀ : ℕ} (H : Hyp e t₀)
include hid hm H

/-- Every process is eventually neutral. -/
lemma exists_neutral {T : ℕ} (hT : t₀ ≤ T) (r : P) : ∃ t ≥ T, Neutral ((e.cfg t).loc r).pc := by
  rcases H.phase hid hm hT r with ⟨hrem, -⟩ | ⟨hp, hb⟩
  · exact ⟨T, le_rfl, by rw [hrem]; trivial⟩
  have hpend : (e.cfg T).pend r ≠ none := by rw [hp]; simp
  obtain ⟨t, ht, hG⟩ := H.eventually_loc hT hpend (fun s => Neutral s.pc)
    (fun s => match s.pc with | .read i => 2 * m + 2 - i | .wr i => m + 1 - i | _ => 0)
    (fun t' ht' hG hl => by
      have hbusy := H.busy_of_tau hid hm (show t₀ ≤ t' by omega) hl
      obtain ⟨-, x, f, k, hact, hloc, -⟩ := tau_step e hl
      have hL := (H.locInv hid hm t' r).2
      have hph := H.phase hid hm (show t₀ ≤ t' + 1 by omega) r
      rw [hloc] at hph ⊢
      cases hpc : ((e.cfg t').loc r).pc with
      | read i =>
        rw [hpc] at hL
        rw [act_read hpc hL.1] at hact
        simp only [SymAction.rmw.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        dsimp only at hph ⊢
        split_ifs with h1
        · right; simp only [hpc]; omega
        · simp only [h1, ite_false] at hph
          rcases afterRead_pc ((e.cfg t').loc r) (Function.update ((e.cfg t').loc r).view
            ⟨i, hL.1⟩ ((e.cfg t').mem () (π r ⟨i, hL.1⟩))) with ⟨j, h⟩ | h | h | h
          · right; simp only [h, hpc]; omega
          · left; rw [h]; trivial
          · exfalso; rw [h] at hph; rcases hph with ⟨h', -⟩ | ⟨-, h'⟩
            · cases h'
            · exact h'
          · left; rw [h]; trivial
      | wr i =>
        rw [hpc] at hL
        obtain ⟨hi, -⟩ := hL
        rw [act_wr hpc hi] at hact
        simp only [SymAction.rmw.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        dsimp only
        unfold wrFrom
        split_ifs with h1
        · right
          have := (nextOwn_found ((e.cfg t').loc r).view ((e.cfg t').loc r).me (i + 1) h1).1
          simp only [hpc]; omega
        · left; trivial
      | _ => rw [hpc] at hG hbusy; first | exact absurd trivial hG | exact absurd hbusy id)
  exact ⟨t, ht, hG⟩

lemma exists_neutral_all [Fintype P] {T : ℕ} (hT : t₀ ≤ T) :
    ∃ T' ≥ T, ∀ r, ∃ t, T ≤ t ∧ t ≤ T' ∧ Neutral ((e.cfg t).loc r).pc := by
  choose f hf1 hf2 using fun r => exists_neutral hid hm H hT r
  refine ⟨T + Finset.univ.sup f, by omega, fun r => ⟨f r, hf1 r, ?_, hf2 r⟩⟩
  have := Finset.le_sup (f := f) (Finset.mem_univ r)
  omega

/-- Late withdrawals (whose scan starts after `T*`) involve fewer than `c*` registers. -/
lemma claimA {c T₃ : ℕ} {Tstar : ℕ} (hT : t₀ ≤ Tstar) (hc1 : 1 ≤ c)
    (hc : ∀ t ≥ Tstar, ∀ q, (own ids (e.cfg t) q).card ≤ c)
    (hneut : ∀ r, ∃ t, Tstar ≤ t ∧ t ≤ T₃ ∧ Neutral ((e.cfg t).loc r).pc)
    {r : P} {ρ : ℕ} (hρ : T₃ ≤ ρ) (hpc : ((e.cfg ρ).loc r).pc = .read (m - 1))
    (hres : owned (finalView e hm r ρ) (ids r) < mostPresent (finalView e hm r ρ)) :
    (own ids (e.cfg ρ) r).card < c := by
  rcases Nat.eq_zero_or_pos (own ids (e.cfg ρ) r).card with h0 | hpos
  · omega
  obtain ⟨tr, h1, h2, hn⟩ := hneut r
  have hnr : ∀ i, ((e.cfg tr).loc r).pc ≠ .read i := by
    intro i hi; rw [hi] at hn; exact hn
  obtain ⟨σ, hσ1, hσ2, hσ0, hread⟩ :=
    scan_start hid hm H (show t₀ ≤ tr by omega) hnr (by omega) ⟨_, hpc⟩
  obtain ⟨q, t'', ht1, ht2, hlt⟩ :=
    resign_bound hid hm H (show t₀ ≤ σ by omega) hσ0 hread hσ2 hpc hres hpos
  have := hc t'' (by omega) q
  omega

/-- Entering the erasing loop (line 7) only happens by withdrawing at the end of a scan. -/
lemma wr_entry {s : ℕ} (hs : t₀ ≤ s) {r : P} (h1 : ∀ j, ((e.cfg s).loc r).pc ≠ .wr j) {j : ℕ}
    (h2 : ((e.cfg (s + 1)).loc r).pc = .wr j) :
    ((e.cfg s).loc r).pc = .read (m - 1) ∧
      owned (finalView e hm r s) (ids r) < mostPresent (finalView e hm r s) ∧
      own ids (e.cfg (s + 1)) r = own ids (e.cfg s) r := by
  have hstep := e.step_eq s
  cases hl : e.lbl s with
  | ret q o => exact absurd hl (H.noret s hs q o)
  | inv q o =>
    rw [hl] at hstep
    obtain ⟨hpend, hC⟩ := SymAlg.impl_step_inv_cases hstep
    by_cases hrq : r = q
    · subst hrq
      rw [hC] at h2
      simp only [Function.update_self] at h2
      rcases H.phase hid hm hs r with ⟨hrem, -⟩ | ⟨hp, -⟩
      · simp [alg2, hrem] at h2
        cases o <;> simp_all
      · rw [hp] at hpend; cases hpend
    · rw [hC] at h2; simp only [Function.update_of_ne hrq] at h2; exact absurd h2 (h1 j)
  | tau q =>
    obtain ⟨-, x, f, k, hact, hloc, hmem, -, hother⟩ := tau_step e hl
    by_cases hrq : r = q
    · subst hrq
      rw [hloc] at h2
      have hL := (H.locInv hid hm s r).2
      cases hpc : ((e.cfg s).loc r).pc with
      | cas i =>
        rw [hpc] at hL
        rw [act_cas hpc hL] at hact
        simp only [SymAction.rmw.injEq] at hact; obtain ⟨-, -, rfl⟩ := hact
        dsimp only at h2; split_ifs at h2 <;> simp_all
      | read i =>
        rw [hpc] at hL
        rw [act_read hpc hL.1] at hact
        simp only [SymAction.rmw.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        dsimp only at h2
        split_ifs at h2 with hi1
        have him : i = m - 1 := by have := hL.1; omega
        subst him
        have hmeq : own ids (e.cfg (s + 1)) r = own ids (e.cfg s) r := by
          unfold own; rw [hmem]; simp
        unfold afterRead at h2
        have hme := (H.locInv hid hm s r).1
        split_ifs at h2 with h3 h4
        all_goals first
          | (rw [hme] at h3; exact ⟨rfl, h3, hmeq⟩)
          | simp at h2
      | wr i => exact absurd hpc (h1 i)
      | wait i ab =>
        rw [hpc] at hL
        rw [act_wait hpc hL.1] at hact
        simp only [SymAction.rmw.injEq] at hact; obtain ⟨-, -, rfl⟩ := hact
        dsimp only at h2; split_ifs at h2 <;> simp_all
      | un i =>
        rw [hpc] at hL
        rw [act_un hpc hL.1] at hact
        simp only [SymAction.rmw.injEq] at hact; obtain ⟨-, -, rfl⟩ := hact
        dsimp only at h2; split_ifs at h2 <;> simp_all
      | rem => rw [act_rem hpc] at hact; cases hact
      | cs => rw [act_cs hpc] at hact; cases hact
      | retLock => rw [act_retLock hpc] at hact; cases hact
      | retUnlock => rw [act_retUnlock hpc] at hact; cases hact
    · rw [hother r hrq] at h2; exact absurd h2 (h1 j)

/-- While erasing, the own registers only shrink. -/
lemma own_mono_wr {s : ℕ} {r : P} {j : ℕ} (hpc : ((e.cfg s).loc r).pc = .wr j) :
    own ids (e.cfg (s + 1)) r ⊆ own ids (e.cfg s) r := by
  by_cases hl : e.lbl s = .tau r
  · obtain ⟨-, x, f, k, hact, -, hmem, -⟩ := tau_step e hl
    have hL := (H.locInv hid hm s r).2
    rw [hpc] at hL
    obtain ⟨hi, -⟩ := hL
    rw [act_wr hpc hi] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    intro y hy
    simp only [own, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [hmem, Function.update_apply] at hy
    split_ifs at hy <;> first | (simp at hy) | exact hy
  · rw [H.own_frame hid hm hl]

/-- Late erasers own fewer than `c*` registers. -/
lemma claimB {c T₃ T₄ : ℕ} {Tstar : ℕ} (hT : t₀ ≤ Tstar) (hc1 : 1 ≤ c)
    (hc : ∀ t ≥ Tstar, ∀ q, (own ids (e.cfg t) q).card ≤ c)
    (hneut : ∀ r, ∃ t, Tstar ≤ t ∧ t ≤ T₃ ∧ Neutral ((e.cfg t).loc r).pc)
    (hneut' : ∀ r, ∃ t, T₃ ≤ t ∧ t ≤ T₄ ∧ Neutral ((e.cfg t).loc r).pc)
    {r : P} {t : ℕ} (ht : T₄ ≤ t) {j : ℕ} (hpc : ((e.cfg t).loc r).pc = .wr j) :
    (own ids (e.cfg t) r).card < c := by
  obtain ⟨tr, h1, h2, hn⟩ := hneut' r
  have hTs : Tstar ≤ T₃ := by obtain ⟨t', h1', h2', -⟩ := hneut r; omega
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := last_entry (fun t' => ∃ j, ((e.cfg t').loc r).pc = .wr j)
    (show tr ≤ t by omega) (by rintro ⟨j', hj'⟩; rw [hj'] at hn; exact hn) ⟨j, hpc⟩
  obtain ⟨j₁, hj₁⟩ := hs4 (s + 1) (by omega) (by omega)
  obtain ⟨hread, hres, hown⟩ := wr_entry hid hm H (show t₀ ≤ s by omega)
    (fun j' h => hs3 ⟨j', h⟩) hj₁
  have hA := claimA hid hm H hT hc1 hc hneut (show T₃ ≤ s by omega) hread hres
  -- the own registers only shrink during the erasing loop
  have hsub : ∀ t', s + 1 ≤ t' → t' ≤ t → own ids (e.cfg t') r ⊆ own ids (e.cfg (s + 1)) r := by
    intro t' h1' h2'
    induction t', h1' using Nat.le_induction with
    | base => exact subset_rfl
    | succ t' h1' ih =>
      obtain ⟨j', hj'⟩ := hs4 t' (by omega) (by omega)
      exact (own_mono_wr hid hm H hj').trans (ih (by omega))
  have := Finset.card_le_card (hsub t (by omega) le_rfl)
  rw [hown] at this
  omega

/-- **A permanent owner.** If the eventual maximum `c*` is positive, some process eventually stays
forever in the first two loops of `lock()` without losing any of its (nonempty set of)
registers. -/
lemma exists_holder [Fintype P] {c Tstar : ℕ} (hT : t₀ ≤ Tstar) (hc1 : 1 ≤ c)
    (hc : ∀ t ≥ Tstar, ∀ q, (own ids (e.cfg t) q).card ≤ c)
    (hinf : ∀ T', ∃ t ≥ T', ∃ q, c ≤ (own ids (e.cfg t) q).card) :
    ∃ q t, t₀ ≤ t ∧
      (∀ t' ≥ t, (∃ i, ((e.cfg t').loc q).pc = .cas i) ∨ (∃ i, ((e.cfg t').loc q).pc = .read i)) ∧
      (∀ t' ≥ t, own ids (e.cfg t) q ⊆ own ids (e.cfg t') q) ∧ (own ids (e.cfg t) q).Nonempty := by
  obtain ⟨T₃, hT₃, hn3⟩ := exists_neutral_all hid hm H hT
  obtain ⟨T₄, hT₄, hn4⟩ := exists_neutral_all hid hm H (show t₀ ≤ T₃ by omega)
  obtain ⟨t, ht, q, hq⟩ := hinf T₄
  have hcq : (own ids (e.cfg t) q).card = c := le_antisymm (hc t (by omega) q) hq
  have hne : (own ids (e.cfg t) q).Nonempty := Finset.card_pos.1 (by omega)
  have hstart : (∃ i, ((e.cfg t).loc q).pc = .cas i) ∨ (∃ i, ((e.cfg t).loc q).pc = .read i) := by
    rcases H.phase hid hm (show t₀ ≤ t by omega) q with ⟨hrem, -⟩ | ⟨-, hb⟩
    · rw [own_empty_of_rem hid hm H hrem] at hcq; simp at hcq; omega
    · cases hpc : ((e.cfg t).loc q).pc with
      | cas i => exact Or.inl ⟨i, rfl⟩
      | read i => exact Or.inr ⟨i, rfl⟩
      | wr j =>
        have := claimB hid hm H hT hc1 hc hn3 hn4 (show T₄ ≤ t by omega) hpc
        omega
      | wait j ab => rw [own_empty_of_wait hid hm H hpc] at hcq; simp at hcq; omega
      | _ => rw [hpc] at hb; exact absurd hb id
  have key : ∀ t' ≥ t, ((∃ i, ((e.cfg t').loc q).pc = .cas i) ∨
      (∃ i, ((e.cfg t').loc q).pc = .read i)) ∧ own ids (e.cfg t) q ⊆ own ids (e.cfg t') q := by
    intro t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact ⟨hstart, subset_rfl⟩
    | succ t' ht' ih =>
      obtain ⟨hpc, hsub⟩ := ih
      by_cases hl : e.lbl t' = .tau q
      · obtain ⟨-, x, f, k, hact, hloc, hmem, -⟩ := tau_step e hl
        have hL := (H.locInv hid hm t' q).2
        rcases hpc with ⟨i, hi⟩ | ⟨i, hi⟩
        · rw [hi] at hL
          rw [act_cas hi hL] at hact
          simp only [SymAction.rmw.injEq] at hact
          obtain ⟨rfl, rfl, rfl⟩ := hact
          refine ⟨?_, hsub.trans ?_⟩
          · rw [hloc]; dsimp only; split_ifs
            · exact Or.inl ⟨_, rfl⟩
            · exact Or.inr ⟨_, rfl⟩
          · intro y hy'
            simp only [own, Finset.mem_filter, Finset.mem_univ, true_and] at hy' ⊢
            rw [hmem, Function.update_apply]
            split_ifs with hyx
            · subst hyx; simp [hy']
            · exact hy'
        · rw [hi] at hL
          rw [act_read hi hL.1] at hact
          simp only [SymAction.rmw.injEq] at hact
          obtain ⟨rfl, rfl, rfl⟩ := hact
          have hmeq : own ids (e.cfg (t' + 1)) q = own ids (e.cfg t') q := by
            unfold own; rw [hmem]; simp
          rw [hmeq]
          refine ⟨?_, hsub⟩
          rw [hloc]; dsimp only
          split_ifs with hi1
          · exact Or.inr ⟨_, rfl⟩
          · have him : i = m - 1 := by have := hL.1; omega
            subst him
            have hme := (H.locInv hid hm t' q).1
            have hph := H.phase hid hm (show t₀ ≤ t' + 1 by omega) q
            rw [hloc] at hph; dsimp only at hph
            simp only [hi1, ite_false] at hph
            unfold afterRead at hph ⊢
            split_ifs at hph ⊢ with h3 h4
            · exfalso
              rw [hme] at h3
              have := claimA hid hm H hT hc1 hc hn3 (show T₃ ≤ t' by omega) hi h3
              have := Finset.card_le_card hsub
              omega
            · exfalso
              rcases hph with ⟨h', -⟩ | ⟨-, h'⟩
              · cases h'
              · exact h'
            · exact Or.inl ⟨0, rfl⟩
      · have hpend : (e.cfg t').pend q ≠ none := H.pend_of_busy hid hm (show t₀ ≤ t' by omega)
          (by rcases hpc with ⟨i, hi⟩ | ⟨i, hi⟩ <;> rw [hi] <;> trivial)
        have hloc : (e.cfg (t' + 1)).loc q = (e.cfg t').loc q := by
          refine loc_of_not_step e hpend (fun ⟨hproc, hst⟩ => ?_)
          cases hl' : e.lbl t' with
          | inv r o => rw [hl'] at hst; exact hst
          | ret r o => exact H.noret t' (by omega) r o hl'
          | tau r =>
            rw [hl'] at hproc; simp only [Label.proc] at hproc; rw [hproc] at hl'; exact hl hl'
        rw [hloc, H.own_frame hid hm hl]
        exact ⟨hpc, hsub⟩
  exact ⟨q, t, by omega, fun t' ht' => (key t' ht').1, fun t' ht' => (key t' ht').2, hne⟩

end Exec

/-- The eventual maximum of the numbers of owned registers. -/
lemma exists_cstar [Fintype P] (e : ((alg2 Id m).impl ids π).InfExec) (t₀ : ℕ) :
    ∃ c T, t₀ ≤ T ∧ (∀ t ≥ T, ∀ q, (own ids (e.cfg t) q).card ≤ c) ∧
      (c = 0 ∨ ∀ T', ∃ t ≥ T', ∃ q, c ≤ (own ids (e.cfg t) q).card) := by
  classical
  have hex : ∃ c, ∃ T, t₀ ≤ T ∧ ∀ t ≥ T, ∀ q, (own ids (e.cfg t) q).card ≤ c :=
    ⟨m, t₀, le_rfl, fun t _ q => (Finset.card_le_univ _).trans (by simp)⟩
  set c := Nat.find hex
  obtain ⟨T, hT, hc⟩ := Nat.find_spec hex
  refine ⟨c, T, hT, hc, ?_⟩
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · exact Or.inl h0
  · right
    intro T'
    by_contra hcon
    push Not at hcon
    have := Nat.find_min hex (show c - 1 < c by omega)
    apply this
    refine ⟨max T T', le_trans hT (le_max_left _ _), fun t ht q => ?_⟩
    have := hcon t (le_trans (le_max_right _ _) ht) q
    omega

end AnonymousMutex.Alg2
