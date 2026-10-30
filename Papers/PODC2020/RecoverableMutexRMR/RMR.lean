import Papers.PODC2020.RecoverableMutexRMR.Skips
import Papers.PODC2020.RecoverableMutexRMR.Safety
import Cslib.Foundations.Data.Finset.SumUpdate

/-!
# Amortized RMR complexity in the DSM model (Theorems 1 and 2)

**DSM model.** Every shared variable lives in the memory segment of one process; an access is a
remote memory reference (RMR) iff the variable is not in the segment of the accessing process.
We put `W[p]` and `Exit[p]` in the segment of `p` (as the busy-wait of line 31 on `W[p]`
requires), and charge *every* access to `C`, `D`, `Token` and `A[·]` as an RMR: this is an upper
bound valid for any placement of these variables. Invocations of `Enter()`/`Exit()` and crashes
cost nothing.

**Result.** In every execution, the total number of RMRs is at most
`25 · (number of Enter() invocations) + 76 · (number of crashes)`.
Since every crash ends a passage and the recovery starts a new one, this is `O(m)` for `m`
passages (Theorem 1/2 of the paper). See `README.md` for the literal reading of "passage".

The proof is a potential argument: `Θ = Σ_p ρ(pc p) + 7 (C − Token) + 25 σ + 25 (2·#crashes −
#skipped)`, where `ρ` is the remaining cost of a process up to its next resting point, `C − Token`
pays for the iterations of `Move_Token()`, and `σ` counts processes holding a skipped ticket (they
will restart `Enter()`); `#skipped ≤ 2 #crashes` is `psi_bound`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

open Safety

/-- RMR cost (DSM) of the next step of `p`. -/
def rmrCost (s : Cfg P) (p : P) : ℕ :=
  match s.pc p with
  | .l4 | .w24 _ | .w25 _ | .w28 _ | .r15 => 1
  | .m34 _ | .m35 _ _ | .m36 _ _ _ | .m38 _ _ _ _ | .m42 _ _ | .m46 _ _ | .m47 _ _
  | .m48 _ _ => 1
  | .m40 _ _ q | .m41 _ _ q => if q = p then 0 else 1
  | _ => 0

/-- RMR cost of an event. -/
def evCost (s : Cfg P) : Ev P → ℕ
  | .step p => rmrCost s p
  | .crash _ => 0

/-- Total number of RMRs in the first `t` events of `e`. -/
def totalRMR (e : ℕ → Ev P) (t : ℕ) : ℕ := ∑ u ∈ Finset.range t, evCost (exec e u) (e u)

/-- Number of invocations of `Enter()` (steps from the remainder section) among the first `t`
events. -/
def numEnter (e : ℕ → Ev P) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun u => ∃ p, e u = .step p ∧ (exec e u).pc p = .rem)).card

/-- Remaining cost of a process to its next resting point. -/
def rho : PC P → ℕ
  | .rem => 0 | .l3 => 25 | .l4 => 25 | .l5 _ => 17 | .w23 => 17 | .w24 _ => 17 | .w25 _ => 16
  | .w26 => 0 | .w28 _ => 15 | .w31 _ => 7 | .cs => 7 | .x9 => 7 | .x10 => 7 | .x12 => 0
  | .r15 => 26 | .r16 => 25 | .r18 => 25
  | .m34 r => 7 + rret r | .m35 r _ => 6 + rret r | .m36 r _ _ => 5 + rret r
  | .m38 r _ _ _ => 4 + rret r | .m40 r _ _ => 3 + rret r | .m46 r _ => 3 + rret r
  | .m41 r _ _ => 2 + rret r | .m47 r _ => 2 + rret r | .m42 r _ => 1 + rret r
  | .m48 r _ => 1 + rret r
where
  /-- the cost after returning from `Move_Token()` -/
  rret : Ret → ℕ
    | .wr _ => 7
    | .ex => 0

lemma rho_retpc (r : Ret) : rho (r.pc : PC P) = rho.rret r := by cases r <;> rfl

/-- `p` holds a skipped ticket that it will try again (it restarts `Enter()` at line 26). -/
def sig (s : Cfg P) (g : Ghost P) (p : P) : Prop :=
  s.A (g.cur p) = .skipped ∧ g.cur p ≠ 0 ∧ ((s.W p).1 = g.cur p ∨ ∃ c, s.pc p = .l5 c)

noncomputable instance (s : Cfg P) (g : Ghost P) : DecidablePred (sig s g) := fun _ => by
  unfold sig; exact Classical.dec _

/-- The potential. -/
noncomputable def Theta (s : Cfg P) (g : Ghost P) : ℤ :=
  (∑ q, (rho (s.pc q) : ℤ)) + 7 * ((s.C : ℤ) - s.T) +
    25 * ((Finset.univ.filter (sig s g)).card : ℤ) + 25 * (2 * (g.ncr : ℤ) - nSkipped s)

lemma Theta_nonneg {s : Cfg P} {g : Ghost P} (hI : Inv s g) : 0 ≤ Theta s g := by
  unfold Theta
  have h1 : (0 : ℤ) ≤ ∑ q, (rho (s.pc q) : ℤ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have h2 : (s.T : ℤ) ≤ s.C := by exact_mod_cast hI.T_le
  have h3 := hI.psi_bound
  have h4 : 0 ≤ Psi s g := by have := hI.phi_nonneg; unfold Psi; positivity
  have h5 : (0 : ℤ) ≤ nR15 s := by positivity
  have h6 : (0 : ℤ) ≤ (Finset.univ.filter (sig s g)).card := by positivity
  nlinarith

lemma Theta_init : Theta (Cfg.init : Cfg P) Ghost.init = 0 := by
  have : Finset.univ.filter (sig (Cfg.init : Cfg P) Ghost.init) = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro q _; simp [sig, Ghost.init]
  unfold Theta; rw [this]
  simp [Cfg.init, Ghost.init, rho, nSkipped]

/-! ### Components of the potential along a step -/

lemma sum_rho_step (s s' : Cfg P) (p : P) (h : ∀ q, q ≠ p → s'.pc q = s.pc q) :
    (∑ q, (rho (s'.pc q) : ℤ)) + rho (s.pc p) = (∑ q, (rho (s.pc q) : ℤ)) + rho (s'.pc p) := by
  have e : s'.pc = Function.update s.pc p (s'.pc p) := by
    funext q; by_cases hq : q = p
    · subst hq; simp
    · simp [Function.update_of_ne hq, h q hq]
  rw [e]
  have := Fintype.sum_comp_update_add (fun k => (rho k : ℤ)) s.pc p (s'.pc p)
  simpa using this

lemma card_sig_le (s s' : Cfg P) (g g' : Ghost P) (p : P)
    (h : ∀ q, q ≠ p → sig s' g' q → sig s g q) :
    ((Finset.univ.filter (sig s' g')).card : ℤ) + (if sig s g p then 1 else 0) ≤
      (Finset.univ.filter (sig s g)).card + (if sig s' g' p then 1 else 0) := by
  have hle : (Finset.univ.filter (fun q => if q = p then sig s' g' p else sig s g q)).card +
      (if sig s g p then 1 else 0) ≤
      (Finset.univ.filter (sig s g)).card + (if sig s' g' p then 1 else 0) := by
    have := card_filter_update (fun q => if q = p then sig s' g' p else sig s g q) (sig s g) p
      (fun q hq => by simp [hq])
    simp only [if_true] at this
    omega
  have hmono : (Finset.univ.filter (sig s' g')).card ≤
      (Finset.univ.filter (fun q => if q = p then sig s' g' p else sig s g q)).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    by_cases e : q = p
    · subst e; simpa using hq
    · simp only [e, if_false]; exact h q e hq
  have : (Finset.univ.filter (sig s' g')).card + (if sig s g p then 1 else 0) ≤
      (Finset.univ.filter (sig s g)).card + (if sig s' g' p then 1 else 0) := by omega
  exact_mod_cast this

/-- Generic step bound: the potential pays for the step, given the local numeric inequality. -/
lemma theta_step_gen {s s' : Cfg P} {g g' : Ghost P} {p : P} (c ch : ℤ)
    (hpc : ∀ q, q ≠ p → s'.pc q = s.pc q) (hsig : ∀ q, q ≠ p → sig s' g' q → sig s g q)
    (hncr : g'.ncr = g.ncr) (hK : nSkipped s ≤ nSkipped s')
    (hnum : c + rho (s'.pc p) + 7 * ((s'.C : ℤ) - s'.T) + 25 * (if sig s' g' p then 1 else 0) ≤
      rho (s.pc p) + 7 * ((s.C : ℤ) - s.T) + 25 * (if sig s g p then 1 else 0) + ch) :
    c + Theta s' g' ≤ Theta s g + ch := by
  have h1 := sum_rho_step s s' p hpc
  have h2 := card_sig_le s s' g g' p hsig
  have h3 : (nSkipped s : ℤ) ≤ nSkipped s' := by exact_mod_cast hK
  unfold Theta
  rw [hncr]
  nlinarith

lemma sig_of_frame {s s' : Cfg P} {g g' : Ghost P} {q : P}
    (hA : ∀ x, s'.A x = .skipped → s.A x = .skipped) (hcur : g'.cur q = g.cur q)
    (hW : (s'.W q).1 = (s.W q).1) (hpc : ∀ c, s'.pc q = .l5 c → ∃ c', s.pc q = .l5 c') :
    sig s' g' q → sig s g q := by
  rintro ⟨h1, h2, h3⟩
  rw [hcur] at h1 h2 h3
  refine ⟨hA _ h1, h2, ?_⟩
  rcases h3 with h3 | ⟨c, hc⟩
  · exact Or.inl (hW ▸ h3)
  · exact Or.inr (hpc c hc)

lemma ite_le_ite {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    (if p then (1 : ℤ) else 0) ≤ if q then 1 else 0 := by
  split_ifs <;> simp_all

lemma ite_nonneg' {p : Prop} [Decidable p] : (0 : ℤ) ≤ if p then 1 else 0 := by
  split_ifs <;> simp

/-- Steps that only move the program counter of `p`. -/
lemma theta_setPc {s : Cfg P} {g : Ghost P} {p : P} {k : PC P} (c ch : ℤ)
    (hk : ∀ c, k ≠ .l5 c) (hnum : c + rho k ≤ rho (s.pc p) + ch) :
    c + Theta (s.setPc p k) g ≤ Theta s g + ch := by
  refine theta_step_gen (p := p) c ch (fun q hq => by simp [Function.update_of_ne hq])
    (fun q hq h => sig_of_frame (s := s) (s' := s.setPc p k) (g := g) (g' := g) (fun _ h => h)
      rfl rfl (fun c hc => ⟨c, by simpa [Function.update_of_ne hq] using hc⟩) h) rfl le_rfl ?_
  have hs : sig (s.setPc p k) g p → sig s g p :=
    sig_of_frame (s := s) (s' := s.setPc p k) (g := g) (g' := g) (fun _ h => h) rfl rfl
      (fun c hc => by simp at hc; exact absurd hc (hk c))
  have := ite_le_ite (hs)
  simp only [setPc_pc, Function.update_self, setPc_C, setPc_T] at this ⊢
  linarith

lemma sig_W_zero {s : Cfg P} {g : Ghost P} {p : P} (h : s.W p = (0, false))
    (hpc : ∀ c, s.pc p ≠ .l5 c) : ¬ sig s g p := by
  rintro ⟨-, h2, h3 | ⟨c, hc⟩⟩
  · rw [h] at h3; exact h2 h3.symm
  · exact hpc c hc

lemma nSkipped_mono {s s' : Cfg P} (hC : s.C ≤ s'.C)
    (hA : ∀ x, s.A x = .skipped → s'.A x = .skipped) : nSkipped s ≤ nSkipped s' := by
  unfold nSkipped
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hA x hx.2⟩

/-- A successful skip (line 46). -/
lemma theta_skip {s : Cfg P} {g : Ghost P} {p : P} {r : Ret} {ℓ : ℕ} (hI : Inv s g)
    (hpc : s.pc p = .m46 r ℓ) (hA : s.A (ℓ + 1) = .empty) :
    (1 : ℤ) + Theta (s.step p) (g.next s (.step p)) ≤ Theta s g := by
  have hL := hI.loc p; simp only [LI, hpc] at hL
  obtain ⟨h1, -, h3, -⟩ := hL
  simp only [Cfg.step, Ghost.next, hpc, hA, if_true]
  set s' : Cfg P := { s with A := Function.update s.A (ℓ + 1) .skipped,
                             pc := Function.update s.pc p (.m47 r ℓ) } with hs'
  have hAx : ∀ x, x ≠ ℓ + 1 → s'.A x = s.A x := fun x hx => by
    simp [hs', Function.update_of_ne hx]
  have hpcq : ∀ q, q ≠ p → s'.pc q = s.pc q := fun q hq => by simp [hs', Function.update_of_ne hq]
  have h1' := sum_rho_step s s' p hpcq
  have hsub : Finset.univ.filter (sig s' g) ⊆
      Finset.univ.filter (sig s g) ∪ Finset.univ.filter (fun q => g.cur q = ℓ + 1) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hq ⊢
    by_cases e : g.cur q = ℓ + 1
    · exact Or.inr e
    · left
      obtain ⟨k1, k2, k3⟩ := hq
      refine ⟨by rwa [hAx _ e] at k1, k2, ?_⟩
      rcases k3 with k3 | ⟨c, hc⟩
      · exact Or.inl k3
      · right; refine ⟨c, ?_⟩
        by_cases eq : q = p
        · subst eq; simp [hs'] at hc
        · rwa [hpcq q eq] at hc
  have hone : (Finset.univ.filter (fun q => g.cur q = ℓ + 1)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have e1 := hI.own_cur a (by omega); have e2 := hI.own_cur b (by omega)
    rw [ha] at e1; rw [hb, e1] at e2; exact Option.some_injective _ e2
  have hS : (Finset.univ.filter (sig s' g)).card ≤ (Finset.univ.filter (sig s g)).card + 1 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  have hK : nSkipped s' = nSkipped s + 1 := by
    unfold nSkipped
    rw [card_filter_split (Finset.range (s'.C + 1)) (fun x => s'.A x = .skipped)
      (fun x => x = ℓ + 1)]
    have e1 : (Finset.range (s'.C + 1)).filter (fun x => s'.A x = .skipped ∧ ¬ x = ℓ + 1) =
        (Finset.range (s.C + 1)).filter (fun x => s.A x = .skipped) := by
      ext x; by_cases e : x = ℓ + 1
      · subst e; simp [hA]
      · simp [e, hAx x e, hs']
    have e2 : (Finset.range (s'.C + 1)).filter (fun x => s'.A x = .skipped ∧ x = ℓ + 1) =
        {ℓ + 1} := by
      ext x; by_cases e : x = ℓ + 1
      · subst e; simp [hs']; omega
      · simp [e]
    rw [e1, e2, Finset.card_singleton]
  have hrho : rho (s'.pc p) + 1 = rho (s.pc p) := by
    simp [hs', hpc, rho]; omega
  unfold Theta
  have hC : s'.C = s.C := rfl
  have hT : s'.T = s.T := rfl
  rw [hC, hT, hK]
  push_cast
  have : ((Finset.univ.filter (sig s' g)).card : ℤ) ≤ (Finset.univ.filter (sig s g)).card + 1 := by
    exact_mod_cast hS
  have : (rho (s'.pc p) : ℤ) + 1 = rho (s.pc p) := by exact_mod_cast hrho
  linarith

/-- Variant of `theta_step_gen` with the stepper's `sig` handled separately. -/
lemma theta_step_gen2 {s s' : Cfg P} {g g' : Ghost P} {p : P} (c ch : ℤ)
    (hpc : ∀ q, q ≠ p → s'.pc q = s.pc q) (hsig : ∀ q, q ≠ p → sig s' g' q → sig s g q)
    (hncr : g'.ncr = g.ncr) (hK : nSkipped s ≤ nSkipped s')
    (hsp : sig s' g' p → sig s g p)
    (hnum : c + rho (s'.pc p) + 7 * ((s'.C : ℤ) - s'.T) ≤ rho (s.pc p) + 7 * ((s.C : ℤ) - s.T) + ch) :
    c + Theta s' g' ≤ Theta s g + ch := by
  refine theta_step_gen c ch hpc hsig hncr hK ?_
  have := ite_le_ite hsp
  linarith

/-- Frame condition for `sig` of other processes. -/
lemma sig_frame_other {s s' : Cfg P} {g g' : Ghost P} {p : P}
    (hA : ∀ x, s'.A x = .skipped → s.A x = .skipped) (hcur : ∀ q, q ≠ p → g'.cur q = g.cur q)
    (hW : ∀ q, q ≠ p → (s'.W q).1 = (s.W q).1) (hpc : ∀ q, q ≠ p → s'.pc q = s.pc q) :
    ∀ q, q ≠ p → sig s' g' q → sig s g q := fun q hq =>
  sig_of_frame hA (hcur q hq) (hW q hq) (fun c hc => ⟨c, by rw [← hpc q hq]; exact hc⟩)

/-- The potential pays for every step; entering from the remainder section costs 25. -/
theorem theta_step {s : Cfg P} {g : Ghost P} (hI : Inv s g) (p : P) :
    (rmrCost s p : ℤ) + Theta (s.step p) (g.next s (.step p)) ≤
      Theta s g + (if s.pc p = .rem then 25 else 0) := by
  by_cases hr : s.pc p = .rem
  · simp only [Cfg.step, Ghost.next, hr, if_true]
    exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hr])
  rw [if_neg hr]
  have hL := hI.loc p
  cases hk : s.pc p with
  | rem => exact absurd hk hr
  | l3 =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs <;> exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk])
  | w23 =>
    simp only [Cfg.step, Ghost.next, hk]
    exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk])
  | w25 w =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs <;> exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk])
  | w31 w =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs <;> exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk])
  | cs =>
    simp only [Cfg.step, Ghost.next, hk]
    exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk])
  | r16 =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs <;> exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk])
  | r18 =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs <;> exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk])
  | m34 r =>
    simp only [Cfg.step, Ghost.next, hk]
    exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk] <;> omega)
  | m35 r ℓ =>
    simp only [Cfg.step, Ghost.next, hk]
    exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk] <;> omega)
  | m36 r ℓ d =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs
    · exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk] <;> omega)
    · refine theta_setPc _ _ (by cases r <;> simp [Ret.pc]) ?_
      rw [rho_retpc]; simp [rho, rmrCost, hk]
  | m38 r ℓ c d =>
    simp only [Cfg.step, Ghost.next, hk]
    split
    · exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk] <;> omega)
    · split_ifs
      · exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk] <;> omega)
      · refine theta_setPc _ _ (by cases r <;> simp [Ret.pc]) ?_
        rw [rho_retpc]; simp [rho, rmrCost, hk] <;> omega
  | m41 r ℓ q =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs
    · refine theta_setPc _ _ (by simp) ?_
      simp only [rho, rmrCost, hk]; split_ifs <;> push_cast <;> omega
    · refine theta_setPc _ _ (by cases r <;> simp [Ret.pc]) ?_
      rw [rho_retpc]; simp only [rho, rmrCost, hk]; split_ifs <;> push_cast <;> omega
  | m47 r ℓ =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs
    · exact theta_setPc _ _ (by simp) (by simp [rho, rmrCost, hk] <;> omega)
    · refine theta_setPc _ _ (by cases r <;> simp [Ret.pc]) ?_
      rw [rho_retpc]; simp [rho, rmrCost, hk] <;> omega
  | m42 r ℓ | m48 r ℓ =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs with hT
    · refine theta_step_gen (p := p) (s := s) (g := g) _ _ (fun q hq => by
        simp [Function.update_of_ne hq])
        (sig_frame_other (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
          (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl ?_
      have hs := ite_le_ite (sig_of_frame (s := s) (g := g) (g' := g) (q := p)
        (s' := { s with T := ℓ + 1, pc := Function.update s.pc p (.m34 r) })
        (fun _ h => h) rfl rfl (fun c hc => by simp at hc))
      have e1 : rho (Function.update s.pc p (PC.m34 r) p) = 7 + rho.rret r := by simp [rho]
      rw [e1]; simp only [hk, rho, rmrCost]
      push_cast; subst hT; linarith
    · refine theta_setPc _ _ (by cases r <;> simp [Ret.pc]) ?_
      rw [rho_retpc]; simp [rho, rmrCost, hk]
  | x9 =>
    simp only [Cfg.step, Ghost.next, hk]
    refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl
      (sig_of_frame (fun _ h => h) rfl rfl (fun c hc => by simp at hc)) ?_
    simp [rho, rho.rret, rmrCost, hk]
  | x12 =>
    simp only [Cfg.step, Ghost.next, hk]
    refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl
      (sig_of_frame (fun _ h => h) rfl rfl (fun c hc => by simp at hc)) ?_
    simp [rho, rho.rret, rmrCost, hk]
  | x10 =>
    simp only [Cfg.step, Ghost.next, hk]
    refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun _ _ => rfl)
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl
      (fun h => absurd h (sig_W_zero (by simp) (fun c => by simp))) ?_
    simp [rho, rho.rret, rmrCost, hk]
  | w26 =>
    simp only [LI, hk] at hL
    obtain ⟨h1, h2, h3, h4⟩ := hL
    simp only [Cfg.step, Ghost.next, hk]
    refine theta_step_gen (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun _ _ => rfl)
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl ?_
    have hs : sig s g p := ⟨h4, h3, Or.inl h2⟩
    have hs' : ¬ sig ({ s with W := Function.update s.W p (0, false), pc := Function.update s.pc p .l3 } : Cfg P) g p :=
      sig_W_zero (by simp) (fun c => by simp)
    simp only [hs, hs', if_true, if_false, rho, rmrCost, hk, Function.update_self]
    simp <;> linarith
  | l5 c =>
    simp only [LI, hk] at hL
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL
    simp only [Cfg.step, Ghost.next, hk, h2, if_true]
    refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun _ _ => rfl)
        (fun q hq => by simp [Function.update_of_ne hq])
        (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl
      (fun h => ⟨h.1, h.2.1, Or.inr ⟨c, hk⟩⟩) ?_
    simp [rho, rho.rret, rmrCost, hk]
  | w28 w =>
    simp only [Cfg.step, Ghost.next, hk]
    refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl
      (sig_of_frame (fun _ h => h) rfl rfl (fun c hc => by simp at hc)) ?_
    simp [rho, rho.rret, rmrCost, hk]
  | r15 =>
    simp only [Cfg.step, Ghost.next, hk]
    refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl
      (sig_of_frame (fun _ h => h) rfl rfl (fun c hc => by simp at hc)) ?_
    simp [rho, rho.rret, rmrCost, hk]
  | l4 =>
    simp only [Cfg.step, Ghost.next, hk]
    have hAC : s.A (s.C + 1) = .empty := by
      by_contra h; have := (hI.A_ne _ h).2; omega
    refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
      (fun q hq => by simp [Function.update_of_ne hq])
      (sig_frame_other (fun _ h => h) (fun q hq => by simp [Function.update_of_ne hq])
        (fun _ _ => rfl) (fun q hq => by simp [Function.update_of_ne hq])) rfl ?_
      (fun h => by have := h.1; simp [hAC] at this) ?_
    · exact nSkipped_mono (s' := { s with C := s.C + 1, pc := Function.update s.pc p (PC.l5 (s.C + 1)) })
        (by simp) (fun _ h => h)
    · simp [rho, rho.rret, rmrCost, hk]; push_cast; ring_nf; omega
  | w24 w =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs with hA
    · have hAsk : ∀ x, (Function.update s.A w (.claimed p)) x = .skipped → s.A x = .skipped := by
        intro x hx; by_cases e : x = w
        · subst e; simp at hx
        · simpa [Function.update_of_ne e] using hx
      refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
        (fun q hq => by simp [Function.update_of_ne hq])
        (sig_frame_other hAsk (fun _ _ => rfl) (fun _ _ => rfl)
          (fun q hq => by simp [Function.update_of_ne hq])) rfl ?_
        (sig_of_frame hAsk rfl rfl (fun c hc => by simp at hc)) ?_
      · refine nSkipped_mono
          (s' := { s with A := Function.update s.A w (Slot.claimed p), pc := Function.update s.pc p (PC.w25 w) })
          le_rfl ?_
        intro x hx; by_cases e : x = w
        · subst e; rw [hA] at hx; cases hx
        · simpa [Function.update_of_ne e] using hx
      · simp [rho, rho.rret, rmrCost, hk]
    · exact theta_setPc _ _ (by simp) (by simp [rho, rho.rret, rmrCost, hk])
  | m40 r ℓ q =>
    simp only [Cfg.step, Ghost.next, hk]
    split_ifs with hW
    · have hWf : ∀ q', ((Function.update s.W q (ℓ + 1, true)) q').1 = (s.W q').1 := by
        intro q'; by_cases e : q' = q
        · subst e; simp [hW]
        · simp [Function.update_of_ne e]
      refine theta_step_gen2 (p := p) (s := s) (g := g) _ _
        (fun q hq => by simp [Function.update_of_ne hq])
        (sig_frame_other (fun _ h => h) (fun _ _ => rfl) (fun q' _ => hWf q')
          (fun q hq => by simp [Function.update_of_ne hq])) rfl le_rfl
        (sig_of_frame (fun _ h => h) rfl (hWf p) (fun c hc => by simp at hc)) ?_
      simp only [rho, rmrCost, hk, Function.update_self]; split_ifs <;> push_cast <;> omega
    · refine theta_setPc _ _ (by simp) ?_
      simp only [rho, rmrCost, hk]; split_ifs <;> push_cast <;> omega
  | m46 r ℓ =>
    by_cases hA : s.A (ℓ + 1) = .empty
    · have := theta_skip hI hk hA
      have e : rmrCost s p = 1 := by simp [rmrCost, hk]
      rw [e]; push_cast; linarith
    · simp only [Cfg.step, Ghost.next, hk, hA, if_false]
      exact theta_setPc _ _ (by simp) (by simp [rho, rho.rret, rmrCost, hk] <;> omega)

/-- A crash costs at most 76 units of potential (and none in the remainder section). -/
theorem theta_crash {s : Cfg P} {g : Ghost P} (p : P) :
    Theta (s.crash p) (g.next s (.crash p)) ≤ Theta s g + (if s.pc p = .rem then 0 else 76) := by
  by_cases h0 : s.pc p = .rem
  · simp only [Cfg.crash, Ghost.next, h0, if_true]; linarith
  simp only [Cfg.crash, Ghost.next, h0, if_false]
  have h1 := theta_setPc (s := s) (g := g) (p := p) (k := .r15) 0 26 (by simp)
    (by have : (0 : ℤ) ≤ rho (s.pc p) := by positivity
        simp only [rho] at this ⊢; push_cast; linarith)
  have e : Theta (s.setPc p .r15) { g with ncr := g.ncr + 1 } = Theta (s.setPc p .r15) g + 50 := by
    have e1 : Finset.univ.filter (sig (s.setPc p .r15) { g with ncr := g.ncr + 1 }) =
        Finset.univ.filter (sig (s.setPc p .r15) g) := rfl
    unfold Theta; rw [e1]; push_cast; ring
  rw [e]; linarith

/-- The charge of an event: 25 for an invocation of `Enter()`, 76 for a crash outside the
remainder section. -/
def charge (s : Cfg P) : Ev P → ℤ
  | .step p => if s.pc p = .rem then 25 else 0
  | .crash p => if s.pc p = .rem then 0 else 76

theorem theta_next {s : Cfg P} {g : Ghost P} (hI : Inv s g) (ev : Ev P) :
    (evCost s ev : ℤ) + Theta (s.next ev) (g.next s ev) ≤ Theta s g + charge s ev := by
  cases ev with
  | step p => exact theta_step hI p
  | crash p => simpa [evCost, charge, Cfg.next] using theta_crash (s := s) (g := g) p

/-- **Theorems 1 and 2 (RMR complexity, DSM model).** In every execution, the total number of
RMRs is at most `25 · #(invocations of Enter()) + 76 · #crashes` (crashes outside the remainder
section); hence it is `O(m)` when `m` passages begin (each crash ends a passage and the recovery
starts a new one). -/
theorem rmr_bound (e : ℕ → Ev P) (t : ℕ) :
    totalRMR e t ≤ 25 * numEnter e t + 76 * numCrashes e t := by
  have key : ∀ t, (totalRMR e t : ℤ) + Theta (exec e t) (ghost e t) ≤
      25 * (numEnter e t : ℤ) + 76 * (numCrashes e t : ℤ) := by
    intro t
    induction t with
    | zero => simp [totalRMR, numEnter, numCrashes, Theta_init]
    | succ t ih =>
      have hstep := theta_next (inv_exec e t) (e t)
      have hR : totalRMR e (t + 1) = totalRMR e t + evCost (exec e t) (e t) := by
        simp [totalRMR, Finset.sum_range_succ]
      have hE : (numEnter e (t + 1) : ℤ) = numEnter e t +
          (if ∃ p, e t = .step p ∧ (exec e t).pc p = .rem then 1 else 0) := by
        unfold numEnter
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs with h
        · rw [Finset.card_insert_of_notMem (by simp)]; push_cast; ring
        · simp
      have hC : (numCrashes e (t + 1) : ℤ) = numCrashes e t +
          (if ∃ p, e t = .crash p ∧ (exec e t).pc p ≠ .rem then 1 else 0) := by
        unfold numCrashes
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs with h
        · rw [Finset.card_insert_of_notMem (by simp)]; push_cast; ring
        · simp
      have hch : charge (exec e t) (e t) ≤
          25 * (if ∃ p, e t = .step p ∧ (exec e t).pc p = .rem then 1 else 0) +
          76 * (if ∃ p, e t = .crash p ∧ (exec e t).pc p ≠ .rem then 1 else 0) := by
        cases he : e t with
        | step p =>
          simp only [charge]
          by_cases hp : (exec e t).pc p = .rem
          · have : ∃ q, Ev.step p = Ev.step q ∧ (exec e t).pc q = .rem := ⟨p, rfl, hp⟩
            simp [hp, this]
          · simp only [hp, if_false]
            split_ifs <;> norm_num
        | crash p =>
          simp only [charge]
          by_cases hp : (exec e t).pc p = .rem
          · simp only [hp, if_true]
            split_ifs <;> norm_num
          · have : ∃ q, (Ev.crash p : Ev P) = Ev.crash q ∧ (exec e t).pc q ≠ .rem := ⟨p, rfl, hp⟩
            simp only [hp, this, if_true, if_false]
            split_ifs <;> norm_num
      rw [hR, hE, hC, exec_succ, ghost_succ]
      push_cast
      linarith
  have h1 := key t
  have h2 := Theta_nonneg (inv_exec e t)
  have : (totalRMR e t : ℤ) ≤ 25 * (numEnter e t : ℤ) + 76 * (numCrashes e t : ℤ) := by linarith
  exact_mod_cast this

end Podc.RecoverableMutexRMR
