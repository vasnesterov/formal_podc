import Papers.PODC2024.HistoryIndependent.UniversalThm
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Task
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Algorithm 5: wait-freedom

With atomic R-LLSC base objects, Algorithm 5 is wait-free (the progress part of Theorem 32,
specialized to atomic base objects: Lemma 31 and Claim 33 become trivial since every `LL` is a
single step).

The proof is a potential argument. Fix a process `p` with a pending state-changing operation.
Its *phase* is

* `0`: before announcing (line 4);
* `1`: announced, not yet applied (`announce[p] ∈ O`, `head ≠ ⟨_, ⟨_, p⟩⟩`);
* `2`: applied, not yet cleared (`announce[p] ∈ O`, `head = ⟨_, ⟨_, p⟩⟩`);
* `3`: cleared (`announce[p] ∈ R`) or after the loop.

In phase 1 the priority-based helping is measured by `Φ = Σ_r φ_r`, where `φ_r` is the
distance from `priority_r` to `p` (mod `n`), or `n` if `r` is *stale*: it is about to apply its
own operation although `priority_r = p` because it read `announce[p]` before `p` announced.
Every transition `A → B` (a successful `SC` in line 14) that does not apply `p`'s operation
decreases `Φ`, and every transition `B → A` decreases the mode bit. The global part `G` of the
potential never increases; it strictly decreases at every write to `head` that removes `p`
from the context of `head`. The local part `pl` decreases at every step of `p` that does not
decrease `G`. Hence `μ = 32 G + pl` never increases and strictly decreases at every step of `p`.

(The paper's argument "after at most `n` successful SCs by `p_j`, `priority_j = π(op)`" overlooks
the stale reads: a process may need `n + 1` of them. This does not affect the result.)
-/

namespace Cslib.SharedMemory

namespace Universal

open List Finset

variable {A : ObjSpec} {n : ℕ}

/-- Distance from priority `pr` to `p`, modulo `n`. -/
def dist (p pr : Fin n) : ℕ := (p.val + n - pr.val) % n

lemma dist_lt (p pr : Fin n) : dist p pr < n := Nat.mod_lt _ (by have := p.isLt; omega)

lemma dist_nextP (p pr : Fin n) (h : pr ≠ p) : dist p (nextP pr) + 1 = dist p pr := by
  have hp := p.isLt; have hpr := pr.isLt
  have hne : pr.val ≠ p.val := fun e => h (Fin.ext e)
  simp only [dist, nextP]
  by_cases hl : pr.val + 1 < n
  · rw [Nat.mod_eq_of_lt hl]
    rcases lt_or_gt_of_ne hne with h1 | h1
    · rw [show p.val + n - (pr.val + 1) = (p.val - pr.val - 1) + n by omega,
        show p.val + n - pr.val = (p.val - pr.val) + n by omega, Nat.add_mod_right,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · have : pr.val + 1 = n := by omega
    rw [this, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt (by omega)]
    omega

lemma dist_self (p : Fin n) : dist p p = 0 := by simp [dist]

lemma dist_pos (p pr : Fin n) (h : pr ≠ p) : 0 < dist p pr := by
  have := dist_nextP p pr h; omega

variable (p : Fin n)

/-- `r` is stale (with respect to `p`). -/
def Stale (C : Config A (B A n) (Fin n) (Loc A n)) (r : Fin n) : Prop :=
  r ≠ p ∧ r ∈ hc C.mem ∧ (C.loc r).prio = p ∧
    ((C.loc r).pc = .own ∨ ∃ o, (C.loc r).pc = .scApply r o)

open Classical in
/-- The helping potential of process `r`. -/
noncomputable def phi (C : Config A (B A n) (Fin n) (Loc A n)) (r : Fin n) : ℕ :=
  if Stale p C r then n else dist p (C.loc r).prio

/-- `Φ = Σ_r φ_r`. -/
noncomputable def Phi (C : Config A (B A n) (Fin n) (Loc A n)) : ℕ := ∑ r, phi p C r

/-- Mode bit: `0` in mode `A` (`head = ⟨q, ⊥⟩`), `1` in mode `B`. -/
def modeBit (C : Config A (B A n) (Fin n) (Loc A n)) : ℕ :=
  if (hv C.mem).2 = none then 0 else 1

/-- The phase of process `p` (`4`: idle or read-only operation). -/
def phase (C : Config A (B A n) (Fin n) (Loc A n)) : ℕ :=
  match (C.loc p).pc with
  | .ann _ => 0
  | .resp | .llHead2 _ | .clear _ | .rlHead _ | .storeBot _ | .retSC _ | .rl18 _ => 3
  | .idle | .ro _ | .roRet _ => 4
  | _ => if isOp (av C.mem p) then (if ownerIs p (hv C.mem).2 then 2 else 1) else 3

/-- Remaining steps until the end of the current iteration of the main loop. -/
def dLoop : PC A n → ℕ
  | .rlAnn => 1
  | .scHead => 2
  | .scAnn => 3
  | .vl => 4
  | .llAnn => 5
  | .scApply _ _ => 1
  | .own => 2
  | .help => 3
  | .llHead => 6
  | _ => 0

/-- Program counters after `LL(head)` at which being in `head.context` matters. -/
def PC.afterLL : PC A n → Bool
  | .help | .own | .scApply _ _ | .llAnn | .vl | .scAnn | .scHead => true
  | _ => false

/-- Local part of the potential in phase 3. -/
def pl3 : PC A n → ℕ
  | .resp => 4
  | .llHead2 _ => 3
  | .clear _ | .rlHead _ => 2
  | .storeBot _ => 1
  | .retSC _ => 0
  | pc => dLoop pc + 5

/-- Local part of the potential in phases 1 and 2. -/
def pl12 (pc : PC A n) (inHC : Prop) [Decidable inHC] : ℕ :=
  if inHC ∧ pc.afterLL = true then dLoop pc + 5
  else match pc with
    | .llHead => 13
    | _ => dLoop pc + 14

/-- The global part of the potential. -/
noncomputable def G (C : Config A (B A n) (Fin n) (Loc A n)) : ℕ :=
  match phase p C with
  | 0 => 2 * n * n + 4
  | 1 => 2 + 2 * Phi p C + modeBit C
  | 2 => 1
  | _ => 0

/-- The local part of the potential. -/
noncomputable def pl (C : Config A (B A n) (Fin n) (Loc A n)) : ℕ :=
  match phase p C with
  | 0 => 0
  | 1 | 2 => pl12 (C.loc p).pc (p ∈ hc C.mem)
  | 3 => pl3 (C.loc p).pc
  | _ => match (C.loc p).pc with
    | .ro _ => 1
    | _ => 0

/-- The potential `μ = 32 G + pl`. -/
noncomputable def mu (C : Config A (B A n) (Fin n) (Loc A n)) : ℕ := 32 * G p C + pl p C

lemma dLoop_le (pc : PC A n) : dLoop pc ≤ 6 := by cases pc <;> simp [dLoop]

lemma pl12_le (pc : PC A n) (P : Prop) [Decidable P] : pl12 pc P ≤ 20 := by
  have := dLoop_le pc
  unfold pl12; split
  · omega
  · split <;> omega

lemma pl3_le (pc : PC A n) : pl3 pc ≤ 11 := by
  have := dLoop_le pc
  unfold pl3; split <;> omega

lemma pl_le (C : Config A (B A n) (Fin n) (Loc A n)) : pl p C ≤ 20 := by
  unfold pl
  split
  · omega
  · exact pl12_le _ _
  · exact pl12_le _ _
  · have := pl3_le (C.loc p).pc; omega
  · split <;> omega

/-! ### Basic properties of the potential -/

section Basic

variable {p}
variable {C C' : Config A (B A n) (Fin n) (Loc A n)}

lemma phi_le_n (r : Fin n) : phi p C r ≤ n := by
  unfold phi; split_ifs
  · exact le_rfl
  · exact (dist_lt _ _).le

lemma Phi_le : Phi p C ≤ n * n := by
  unfold Phi
  calc ∑ r, phi p C r ≤ ∑ _r : Fin n, n := Finset.sum_le_sum fun r _ => phi_le_n r
    _ = n * n := by simp

lemma phi_le_of {r : Fin n} (hprio : (C'.loc r).prio = (C.loc r).prio)
    (hst : Stale p C' r → Stale p C r) : phi p C' r ≤ phi p C r := by
  unfold phi
  by_cases h' : Stale p C' r
  · simp only [h', hst h', ↓reduceIte, le_refl]
  · simp only [h', ↓reduceIte, hprio]; split_ifs
    · exact (dist_lt _ _).le
    · exact le_rfl

lemma phi_le_other {r : Fin n} (hloc : C'.loc r = C.loc r)
    (hhc : r ∈ hc C'.mem → r ∈ hc C.mem) : phi p C' r ≤ phi p C r :=
  phi_le_of (by rw [hloc]) fun ⟨h1, h2, h3, h4⟩ => ⟨h1, hhc h2, hloc ▸ h3, hloc ▸ h4⟩

lemma phi_le_all {q : Fin n} (hloc : ∀ r, r ≠ q → C'.loc r = C.loc r)
    (hhc : ∀ r, r ≠ q → r ∈ hc C'.mem → r ∈ hc C.mem) (hq : phi p C' q ≤ phi p C q) :
    Phi p C' ≤ Phi p C := by
  unfold Phi
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases hr : r = q
  · subst hr; exact hq
  · exact phi_le_other (hloc r hr) (hhc r hr)

lemma Phi_lt_all {q : Fin n} (hloc : ∀ r, r ≠ q → C'.loc r = C.loc r)
    (hhc : ∀ r, r ≠ q → r ∈ hc C'.mem → r ∈ hc C.mem) (hq : phi p C' q < phi p C q) :
    Phi p C' < Phi p C := by
  unfold Phi
  refine Finset.sum_lt_sum (fun r _ => ?_) ⟨q, Finset.mem_univ _, hq⟩
  by_cases hr : r = q
  · subst hr; exact hq.le
  · exact phi_le_other (hloc r hr) (hhc r hr)

lemma phase_eq (hlp : C'.loc p = C.loc p) (hav : av C'.mem p = av C.mem p)
    (hhv : hv C'.mem = hv C.mem) : phase p C' = phase p C := by
  unfold phase; rw [hlp, hav, hhv]

lemma mu_le_same (hlp : C'.loc p = C.loc p) (hav : av C'.mem p = av C.mem p)
    (hhv : hv C'.mem = hv C.mem) (hhc : p ∈ hc C'.mem ↔ p ∈ hc C.mem)
    (hphi : phase p C = 1 → Phi p C' ≤ Phi p C) : mu p C' ≤ mu p C := by
  have hph := phase_eq hlp hav hhv
  have hG : G p C' ≤ G p C := by
    unfold G; rw [hph]
    split
    · exact le_rfl
    · rename_i h1
      have := hphi h1
      have : modeBit C' = modeBit C := by unfold modeBit; rw [hhv]
      omega
    all_goals exact le_rfl
  have hpl : pl p C' = pl p C := by
    unfold pl; rw [hph, hlp]
    simp only [hhc]
  unfold mu; omega

lemma mu_lt_of_G (h : G p C' < G p C) : mu p C' < mu p C := by
  have := pl_le p C'; unfold mu; omega

lemma mu_le_of_G (h : G p C' ≤ G p C) (h' : pl p C' ≤ pl p C) : mu p C' ≤ mu p C := by
  unfold mu; omega

lemma mu_lt_of_pl (h : G p C' ≤ G p C) (h' : pl p C' < pl p C) : mu p C' < mu p C := by
  unfold mu; omega

lemma isOp_iff (a : AnnVal A) : isOp a = true ↔ ∃ o, a = some (.inl o) := by
  rcases a with _ | v
  · simp [isOp]
  · cases v <;> simp [isOp]

lemma phase_one (h : phase p C = 1) : (C.loc p).pc.inLoop = true ∧
    (∃ o, av C.mem p = some (.inl o)) ∧ ownerIs p (hv C.mem).2 = false := by
  rw [← isOp_iff]
  unfold phase at h
  cases hpc : (C.loc p).pc <;> rw [hpc] at h <;> simp only [PC.inLoop] at * <;>
    (try simp at h) <;> (split_ifs at h with h1 h2 <;> simp_all)

lemma phase_two (h : phase p C = 2) : (C.loc p).pc.inLoop = true ∧
    (∃ o, av C.mem p = some (.inl o)) ∧ ownerIs p (hv C.mem).2 = true := by
  rw [← isOp_iff]
  unfold phase at h
  cases hpc : (C.loc p).pc <;> rw [hpc] at h <;> simp only [PC.inLoop] at * <;>
    (try simp at h) <;> (split_ifs at h with h1 h2 <;> simp_all)

lemma phase_of_loop (h : (C.loc p).pc.inLoop = true) : phase p C =
    if isOp (av C.mem p) then (if ownerIs p (hv C.mem).2 then 2 else 1) else 3 := by
  unfold phase
  cases hpc : (C.loc p).pc <;> rw [hpc] at h <;> simp_all [PC.inLoop]

lemma G_of_one (h : phase p C = 1) : G p C = 2 + 2 * Phi p C + modeBit C := by
  unfold G; rw [h]; rfl
lemma G_of_two (h : phase p C = 2) : G p C = 1 := by unfold G; rw [h]; rfl
lemma G_of_three (h : phase p C = 3) : G p C = 0 := by unfold G; rw [h]; rfl
lemma pl_of_three (h : phase p C = 3) : pl p C = pl3 (C.loc p).pc := by unfold pl; rw [h]; rfl
lemma pl_of_12 (h : phase p C = 1 ∨ phase p C = 2) :
    pl p C = pl12 (C.loc p).pc (p ∈ hc C.mem) := by
  unfold pl; rcases h with h | h <;> rw [h] <;> rfl

lemma phase_of_not_loop (h : (C.loc p).pc.inLoop = false) :
    phase p C = match (C.loc p).pc with
      | .ann _ => 0
      | .idle | .ro _ | .roRet _ => 4
      | _ => 3 := by
  unfold phase
  cases hpc : (C.loc p).pc <;> rw [hpc] at h <;> simp_all [PC.inLoop]

lemma mu_eq_of_not_loop (hlp : C'.loc p = C.loc p) (h : (C.loc p).pc.inLoop = false) :
    mu p C' = mu p C := by
  have h' : (C'.loc p).pc.inLoop = false := by rw [hlp]; exact h
  have e1 := phase_of_not_loop h
  have e2 := phase_of_not_loop h'
  rw [hlp] at e2
  have hph : phase p C' = phase p C := by rw [e1, e2]
  have hne : phase p C ≠ 1 ∧ phase p C ≠ 2 := by rw [e1]; split <;> simp
  have hG : G p C' = G p C := by
    unfold G; rw [hph]
    split
    · rfl
    · exact absurd ‹_› hne.1
    · rfl
    · rfl
  have hpl : pl p C' = pl p C := by
    unfold pl; rw [hph, hlp]
    split
    · rfl
    · exact absurd ‹_› hne.1
    · exact absurd ‹_› hne.2
    · rfl
    · rfl
  unfold mu; rw [hG, hpl]

lemma mu_eq_of_not_op (hlp : C'.loc p = C.loc p) (hl : (C.loc p).pc.inLoop = true)
    (h : isOp (av C.mem p) = false) (h' : isOp (av C'.mem p) = false) : mu p C' = mu p C := by
  have e1 := phase_of_loop hl
  have e2 := phase_of_loop (C := C') (by rw [hlp]; exact hl)
  rw [h] at e1; rw [h'] at e2
  simp only [Bool.false_eq_true, ↓reduceIte] at e1 e2
  rw [mu, mu, G_of_three e1, G_of_three e2, pl_of_three e1, pl_of_three e2, hlp]

lemma mu_le_of_inactive (hlp : C'.loc p = C.loc p)
    (hact : ¬((C.loc p).pc.inLoop = true ∧ isOp (av C.mem p) = true))
    (hav : av C'.mem p = av C.mem p) : mu p C' ≤ mu p C := by
  rcases Bool.eq_false_or_eq_true ((C.loc p).pc.inLoop) with hl | hl
  · have hop : isOp (av C.mem p) = false := by simpa [hl] using hact
    exact (mu_eq_of_not_op hlp hl hop (by rw [hav]; exact hop)).le
  · exact (mu_eq_of_not_loop hlp hl).le

lemma mu_lt_BA (hph : phase p C = 1) (hph' : phase p C' = 1) (hmb : modeBit C = 1)
    (hmb' : modeBit C' = 0) (hPhi : Phi p C' ≤ Phi p C) : mu p C' < mu p C := by
  apply mu_lt_of_G
  rw [G_of_one hph, G_of_one hph']
  omega

lemma mu_lt_local (hph : phase p C' = phase p C) (hhv : hv C'.mem = hv C.mem)
    (hlr : ∀ r, r ≠ p → C'.loc r = C.loc r) (hhc : ∀ r, r ≠ p → r ∈ hc C'.mem → r ∈ hc C.mem)
    (hprio : (C'.loc p).prio = (C.loc p).prio) (hpl : pl p C' < pl p C) : mu p C' < mu p C := by
  apply mu_lt_of_pl _ hpl
  unfold G; rw [hph]
  split
  · exact le_rfl
  · have := phi_le_all hlr hhc (phi_le_of hprio (fun hs => absurd rfl hs.1))
    have : modeBit C' = modeBit C := by unfold modeBit; rw [hhv]
    omega
  all_goals exact le_rfl

lemma mu_lt_three (h : phase p C = 3) (h' : phase p C' = 3)
    (hpl : pl3 (C'.loc p).pc < pl3 (C.loc p).pc) : mu p C' < mu p C := by
  rw [mu, mu, G_of_three h, G_of_three h', pl_of_three h, pl_of_three h']; omega

lemma pl_loop (hl : (C.loc p).pc.inLoop = true) : pl p C =
    if phase p C = 3 then pl3 (C.loc p).pc else pl12 (C.loc p).pc (p ∈ hc C.mem) := by
  have := phase_of_loop hl
  split_ifs with h3
  · exact pl_of_three h3
  · apply pl_of_12; rw [this] at h3 ⊢; split_ifs at h3 ⊢ <;> simp_all

end Basic

/-! ### Steps of other processes do not increase the potential -/

variable [DecidablePred A.ReadOnly]

set_option hygiene false in
/-- Close the goal `mu p C' ≤ mu p C` for a step of `q ≠ p` that neither writes `head` nor
`announce[p]` and after which `q` is not stale. -/
local macro "same_tac" : tactic => `(tactic| (
  refine mu_le_same hlp
    (by rw [hmem] <;> first | (simp; done) | simp [av_update_ann, hqp, Ne.symm hqp])
    (by rw [hmem] <;> simp) (by rw [hmem] <;> simp [hqp, Ne.symm hqp]) (fun _ => phi_le_all hlr
      (fun r hr h' => by rw [hmem] at h'; simpa [hr] using h')
      (phi_le_of (by rw [hloc] <;> simp) (fun hs => by
        obtain ⟨-, -, -, h4⟩ := hs; rw [hloc] at h4; simp at h4)))))

theorem mu_tau_other {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n}
    (hI : InvC L cur C.pend C.mem C.loc) (hqp : q ≠ p)
    (h : (alg5 A n).step C (.tau q) = some C') : mu p C' ≤ mu p C := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := fun r hr => by
    rw [hloc]; exact Function.update_of_ne hr _ _
  have hlp := hlr p (Ne.symm hqp)
  have hQ := hI.proc q
  cases hpc : (C.loc q).pc with
  | idle => have := hQ.pinv; rw [hpc] at this; exact absurd this.1 hp
  | roRet r => simp only [alg5, act, hpc] at hact; cases hact
  | retSC r => simp only [alg5, act, hpc] at hact; cases hact
  | ro o => simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc; same_tac
  | ann o => simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc; same_tac
  | loop =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split at hloc <;> same_tac
  | llHead =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split_ifs at hloc <;> same_tac
  | help =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split at hloc
    · rename_i o' hav
      replace hav := Sum.inl.inj hav
      refine mu_le_same hlp (by rw [hmem]) (by rw [hmem]) (by rw [hmem]) fun hph => ?_
      refine phi_le_all hlr (fun r _ h' => by rwa [hmem] at h')
        (phi_le_of (by rw [hloc]; simp) ?_)
      rintro ⟨h1, h2, h3, h4⟩
      rw [hloc, Function.update_self] at h3 h4
      simp only [reduceCtorEq, PC.scApply.injEq, false_or] at h4 h3
      obtain ⟨o'', e, -⟩ := h4
      exact absurd (e.symm.trans h3) h1
    · rename_i hav
      refine mu_le_same hlp (by rw [hmem]) (by rw [hmem]) (by rw [hmem]) fun hph => ?_
      obtain ⟨-, ⟨op, hop⟩, -⟩ := phase_one hph
      refine phi_le_all hlr (fun r _ h' => by rwa [hmem] at h')
        (phi_le_of (by rw [hloc]; simp) ?_)
      rintro ⟨h1, h2, h3, h4⟩
      rw [hloc, Function.update_self] at h3
      simp only at h3
      exact absurd (by rw [h3, hop]) (hav op)
  | own =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split at hloc
    · refine mu_le_same hlp (by rw [hmem]) (by rw [hmem]) (by rw [hmem]) fun hph => ?_
      refine phi_le_all hlr (fun r _ h' => by rwa [hmem] at h')
        (phi_le_of (by rw [hloc]; simp) ?_)
      rintro ⟨h1, h2, h3, h4⟩
      rw [hloc, Function.update_self] at h3
      rw [hmem] at h2
      exact ⟨h1, h2, h3, Or.inl hpc⟩
    · same_tac
  | llAnn =>
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, j⟩, hj⟩ := Option.isSome_iff_exists.1 hl
    simp only [alg5, act, hpc, hj] at hact; cases hact; simp at hmem hloc
    same_tac
  | vl =>
    simp only [alg5, act, hpc] at hact; cases hact
    by_cases hin : q ∈ hc C.mem <;> simp [hin] at hmem hloc <;> split_ifs at hloc <;> same_tac
  | rlAnn => simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc; same_tac
  | resp =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split at hloc
    · same_tac
    · refine mu_le_same hlp (by rw [hmem]) (by rw [hmem]) (by rw [hmem]) (fun _ => phi_le_all hlr
        (fun r hr h' => by rwa [hmem] at h') (phi_le_of (by rw [hloc]; simp) (fun hs => by
          obtain ⟨-, -, -, h4⟩ := hs; rw [hloc] at h4; simp [hpc] at h4)))
  | llHead2 r =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    by_cases hcl : ownerIs q (hv C.mem).2 = true <;>
      simp only [hcl, ↓reduceIte, Bool.false_eq_true] at hloc <;> same_tac
  | rlHead r => simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc; same_tac
  | rl18 j => simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc; same_tac
  | storeBot r => simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc; same_tac
  | scAnn =>
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, hrsp⟩, hop⟩ := hl
    simp only [alg5, act, hpc, hrsp] at hact; cases hact
    by_cases hin : q ∈ ac C.mem (C.loc q).aj
    · simp [hin] at hmem hloc
      by_cases hjp : (C.loc q).aj = p
      · by_cases hlp' : (C.loc p).pc.inLoop = true
        · have hav : av C.mem p = (C.loc q).a := by rw [← hjp]; exact hQ.ca1 _ hin rfl
          have hop' : isOp (av C.mem p) = true := by rw [hav]; exact hop
          have hph12 : phase p C = 1 ∨ phase p C = 2 := by
            rw [phase_of_loop hlp', hop']; simp only [↓reduceIte]; split <;> simp
          have hph' : phase p C' = 3 := by
            rw [phase_of_loop (by rw [hlp]; exact hlp'), hmem, hjp]; simp [isOp]
          apply le_of_lt; apply mu_lt_of_G
          rw [G_of_three hph']
          rcases hph12 with e | e
          · rw [G_of_one e]; omega
          · rw [G_of_two e]; omega
        · exact (mu_eq_of_not_loop hlp (by simpa using hlp')).le
      · refine mu_le_same hlp (by rw [hmem]; simp [av_update_ann, Ne.symm hjp]) (by rw [hmem]; simp)
          (by rw [hmem]; simp) (fun _ => phi_le_all hlr (fun r hr h' => by rw [hmem] at h'; simpa using h')
          (phi_le_of (by rw [hloc]; simp) (fun hs => by
            obtain ⟨-, -, -, h4⟩ := hs; rw [hloc] at h4; simp at h4)))
    · simp [hin] at hmem hloc; same_tac
  | scApply j o =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    by_cases hin : q ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (hQ.ch hin).1
      rw [hhd] at hmem
      have hvn : (hv C.mem).2 = none := by rw [← hhd]; exact hl.1
      by_cases hact' : (C.loc p).pc.inLoop = true ∧ isOp (av C.mem p) = true
      · have hph : phase p C = 1 := by
          rw [phase_of_loop hact'.1, hact'.2, hvn]; simp [ownerIs]
        apply le_of_lt; apply mu_lt_of_G
        rw [G_of_one hph]
        by_cases hjp : j = p
        · have hph' : phase p C' = 2 := by
            rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]; simp [hact'.2, hjp, ownerIs]
          rw [G_of_two hph']; omega
        · have hph' : phase p C' = 1 := by
            rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]
            simp [hact'.2, ownerIs, hjp]
          rw [G_of_one hph']
          have hmb : modeBit C' = 1 := by simp [modeBit, hmem]
          have hmb0 : modeBit C = 0 := by simp [modeBit, hvn]
          have hPhi : Phi p C' < Phi p C := by
            refine Phi_lt_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h') ?_
            have hns : ¬ Stale p C' q := fun ⟨_, h2, _⟩ => by rw [hmem] at h2; simp at h2
            have hprio' : (C'.loc q).prio = nextP (C.loc q).prio := by rw [hloc]; simp
            unfold phi; simp only [hns, ↓reduceIte, hprio']
            split_ifs with hs
            · exact dist_lt _ _
            · have hpr : (C.loc q).prio ≠ p := by
                intro e
                rcases hl.2 with e' | e'
                · exact hjp (e'.trans e)
                · exact hs ⟨hqp, hin, e, Or.inr ⟨o, by rw [hpc, e']⟩⟩
              have := dist_nextP p _ hpr; omega
          omega
      · exact mu_le_of_inactive hlp hact' (by rw [hmem]; simp)
    · simp [hin] at hmem hloc; same_tac
  | scHead =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    by_cases hin : q ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (hQ.ch hin).1
      rw [hhd] at hmem
      have hvj : (hv C.mem).2 = some (rsp, (C.loc q).aj) := by rw [← hhd, hrsp]
      have hnotinl : ∀ o, av C.mem (C.loc q).aj ≠ some (.inl o) := by
        by_cases hac : q ∈ ac C.mem (C.loc q).aj
        · rw [hQ.ca1 _ hac rfl]; intro o e
          exact hQ.k4 hpc (by rw [e]; rfl) hac
        · exact hQ.k3 hin (by rw [hpc]; rfl) hac
      by_cases hact' : (C.loc p).pc.inLoop = true ∧ isOp (av C.mem p) = true
      · have hjp : (C.loc q).aj ≠ p := by
          intro e; obtain ⟨o', ho'⟩ := (isOp_iff _).1 hact'.2
          rw [← e] at ho'; exact hnotinl o' ho'
        have hph : phase p C = 1 := by
          rw [phase_of_loop hact'.1, hact'.2, hvj]; simp [ownerIs, hjp]
        have hph' : phase p C' = 1 := by
          rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]; simp [hact'.2, ownerIs]
        refine (mu_lt_BA hph hph' (by simp [modeBit, hvj]) (by simp [modeBit, hmem])
          (phi_le_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h')
            (phi_le_of (by rw [hloc]; simp) (fun hs => by
              obtain ⟨-, h2, -⟩ := hs; rw [hmem] at h2; simp at h2)))).le
      · exact mu_le_of_inactive hlp hact' (by rw [hmem]; simp)
    · simp [hin] at hmem hloc; split_ifs at hloc <;> same_tac
  | clear r =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hQ.loc; simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    by_cases hin : q ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (hQ.ch hin).1
      rw [hhd] at hmem
      have hvj : (hv C.mem).2 = some (rsp, q) := by rw [← hhd, hrsp]
      by_cases hact' : (C.loc p).pc.inLoop = true ∧ isOp (av C.mem p) = true
      · have hph : phase p C = 1 := by
          rw [phase_of_loop hact'.1, hact'.2, hvj]; simp [ownerIs, hqp]
        have hph' : phase p C' = 1 := by
          rw [phase_of_loop (by rw [hlp]; exact hact'.1), hmem]; simp [hact'.2, ownerIs]
        refine (mu_lt_BA hph hph' (by simp [modeBit, hvj]) (by simp [modeBit, hmem])
          (phi_le_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h')
            (phi_le_of (by rw [hloc]; simp) (fun hs => by
              obtain ⟨-, h2, -⟩ := hs; rw [hmem] at h2; simp at h2)))).le
      · exact mu_le_of_inactive hlp hact' (by rw [hmem]; simp)
    · simp [hin] at hmem hloc; same_tac



theorem mu_inv_other {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {o : A.Op}
    (hqp : q ≠ p) (h : (alg5 A n).step C (.inv q o) = some C') : mu p C' ≤ mu p C := by
  obtain ⟨-, -, -, hloc, hmem⟩ := Impl.step_inv h
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := fun r hr => by
    rw [hloc]; exact Function.update_of_ne hr _ _
  refine mu_le_same (hlr p (Ne.symm hqp)) (by rw [hmem]) (by rw [hmem]) (by rw [hmem])
    (fun _ => phi_le_all hlr (fun r _ h' => by rwa [hmem] at h') (phi_le_of
      (by rw [hloc]; simp [alg5]) (fun hs => ?_)))
  obtain ⟨-, -, -, h4⟩ := hs
  rw [hloc] at h4; simp only [Function.update_self, alg5] at h4
  split_ifs at h4 <;> simp at h4

theorem mu_ret_other {C C' : Config A (B A n) (Fin n) (Loc A n)} {q : Fin n} {r : A.Resp}
    (hqp : q ≠ p) (h : (alg5 A n).step C (.ret q r) = some C') : mu p C' ≤ mu p C := by
  obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := fun r hr => by
    rw [hloc]; exact Function.update_of_ne hr _ _
  refine mu_le_same (hlr p (Ne.symm hqp)) (by rw [hmem]) (by rw [hmem]) (by rw [hmem])
    (fun _ => phi_le_all hlr (fun r _ h' => by rwa [hmem] at h') (phi_le_of ?_ (fun hs => ?_)))
  · rw [hloc]; simp only [Function.update_self]
    simp only [alg5, act] at hact
    split at hact <;> (try split at hact) <;> cases hact <;> rfl
  · obtain ⟨-, -, -, h4⟩ := hs
    rw [hloc] at h4; simp only [Function.update_self] at h4
    simp only [alg5, act] at hact
    split at hact <;> (try split at hact) <;> cases hact <;> simp at h4

/-! ### Steps of `p` decrease the potential -/

set_option hygiene false in
/-- Close `mu p C' < mu p C` for a step of `p` inside the main loop that does not write `head`
or `announce[p]`. -/
local macro "local_tac" : tactic => `(tactic| (
  have hl' : (C'.loc p).pc.inLoop = true := by rw [hloc]; simp [PC.inLoop]
  have hl : (C.loc p).pc.inLoop = true := by rw [hpc]; rfl
  have hph : phase p C' = phase p C := by
    rw [phase_of_loop hl', phase_of_loop hl, hmem] <;> simp
  refine mu_lt_local hph (by rw [hmem] <;> simp) hlr
    (fun r hr h' => by rw [hmem] at h'; simpa [hr] using h') (by rw [hloc]; simp) ?_
  rw [pl_loop hl', pl_loop hl, hph, hloc, hpc, hmem]
  split_ifs <;> simp_all [pl3, pl12, dLoop, PC.afterLL] <;> (try split_ifs) <;> omega))

theorem mu_tau_self {L : List (OpId (Fin n) × A.Op)} {cur : Fin n → OpId (Fin n)}
    {C C' : Config A (B A n) (Fin n) (Loc A n)}
    (hI : InvC L cur C.pend C.mem C.loc) (h : (alg5 A n).step C (.tau p) = some C') :
    mu p C' < mu p C := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  have hlr : ∀ r, r ≠ p → C'.loc r = C.loc r := fun r hr => by
    rw [hloc]; exact Function.update_of_ne hr _ _
  have hP := hI.proc p
  cases hpc : (C.loc p).pc with
  | idle => have := hP.pinv; rw [hpc] at this; exact absurd this.1 hp
  | roRet r => simp only [alg5, act, hpc] at hact; cases hact
  | retSC r => simp only [alg5, act, hpc] at hact; cases hact
  | loop =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    have hl0 : (C.loc p).pc.inLoop = true := by rw [hpc]; rfl
    split at hloc
    · rename_i r hav; replace hav := Sum.inl.inj hav
      have h3 : phase p C = 3 := by rw [phase_of_loop hl0, hav]; rfl
      have h3' : phase p C' = 3 := by unfold phase; rw [hloc]; simp
      apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3, dLoop]
    · rename_i hav
      have hnot3 : phase p C ≠ 3 := by
        have := hP.pinv; rw [hpc, PInv_loop rfl] at this
        obtain ⟨o, -, -, h1 | ⟨r, h1, -⟩⟩ := this
        · rw [phase_of_loop hl0, h1.1]; simp only [isOp, ↓reduceIte]; split <;> simp
        · exact absurd (by rw [h1]) (hav r)
      local_tac
  | llHead =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split_ifs at hloc <;> local_tac
  | help =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split at hloc <;> local_tac
  | own =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    split at hloc
    · local_tac
    · rename_i hav
      have h3 : phase p C = 3 := by
        rw [phase_of_loop (by rw [hpc]; rfl)]
        have : isOp (av C.mem p) = false := by
          rcases e : isOp (av C.mem p)
          · rfl
          · obtain ⟨o, ho⟩ := (isOp_iff _).1 e; exact absurd (by rw [ho]) (hav o)
        rw [this]; rfl
      local_tac
  | llAnn =>
    have hl := hP.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, j⟩, hj⟩ := Option.isSome_iff_exists.1 hl
    simp only [alg5, act, hpc, hj] at hact; cases hact; simp at hmem hloc
    local_tac
  | vl =>
    simp only [alg5, act, hpc] at hact; cases hact
    by_cases hin : p ∈ hc C.mem <;> simp [hin] at hmem hloc <;> split_ifs at hloc <;> local_tac
  | rlAnn => simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc; local_tac
  | ro o =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    have e1 : phase p C = 4 := by unfold phase; rw [hpc]
    have e2 : phase p C' = 4 := by unfold phase; rw [hloc]; simp
    unfold mu G pl; rw [e1, e2, hpc, hloc]; simp
  | ann o =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    have e1 : phase p C = 0 := by unfold phase; rw [hpc]
    apply mu_lt_of_G
    have hG : G p C = 2 * n * n + 4 := by unfold G; rw [e1]; rfl
    rw [hG]
    have hl' : (C'.loc p).pc.inLoop = true := by rw [hloc]; simp [PC.inLoop]
    have := phase_of_loop hl'
    rw [hmem] at this; simp [isOp] at this
    have hPhi := Phi_le (p := p) (C := C')
    have hmb : modeBit C' ≤ 1 := by unfold modeBit; split <;> omega
    split at this
    · rw [G_of_two this]; omega
    · rw [G_of_one this]
      have h2 : 2 * Phi p C' ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 hPhi
      rw [Nat.mul_assoc]; omega
  | resp =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    have h3 : phase p C = 3 := by unfold phase; rw [hpc]
    split at hloc
    · have h3' : phase p C' = 3 := by unfold phase; rw [hloc]; simp
      apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3]
    · rename_i hav
      exfalso
      have := hP.pinv; rw [hpc] at this
      obtain ⟨-, r, h1, -⟩ := this
      exact hav r (by rw [h1])
  | llHead2 r =>
    simp only [alg5, act, hpc] at hact; cases hact; simp at hmem hloc
    have h3 : phase p C = 3 := by unfold phase; rw [hpc]
    by_cases hcl : ownerIs p (hv C.mem).2 = true <;>
      simp only [hcl, ↓reduceIte, Bool.false_eq_true] at hloc
    all_goals
      have h3' : phase p C' = 3 := by unfold phase; rw [hloc]; simp
      apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3]
  | clear r =>
    simp only [alg5, act, hpc] at hact; cases hact
    have h3 : phase p C = 3 := by unfold phase; rw [hpc]
    have h3' : phase p C' = 3 := by unfold phase; rw [hloc]; simp
    apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3]
  | rl18 j =>
    simp only [alg5, act, hpc] at hact; cases hact
    have h3 : phase p C = 3 := by unfold phase; rw [hpc]
    have h3' : phase p C' = 3 := by unfold phase; rw [hloc]; simp
    apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3, dLoop]
  | rlHead r =>
    simp only [alg5, act, hpc] at hact; cases hact
    have h3 : phase p C = 3 := by unfold phase; rw [hpc]
    have h3' : phase p C' = 3 := by unfold phase; rw [hloc]; simp
    apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3]
  | storeBot r =>
    simp only [alg5, act, hpc] at hact; cases hact
    have h3 : phase p C = 3 := by unfold phase; rw [hpc]
    have h3' : phase p C' = 3 := by unfold phase; rw [hloc]; simp
    apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3]
  | scApply j o =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hP.loc; simp only [LocInv, hpc] at hl
    have hl0 : (C.loc p).pc.inLoop = true := by rw [hpc]; rfl
    by_cases hin : p ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (hP.ch hin).1
      rw [hhd] at hmem
      have hvn : (hv C.mem).2 = none := by rw [← hhd]; exact hl.1
      have hl' : (C'.loc p).pc.inLoop = true := by rw [hloc]; simp [PC.inLoop]
      by_cases hop : isOp (av C.mem p) = true
      · have hph : phase p C = 1 := by rw [phase_of_loop hl0, hop, hvn]; simp [ownerIs]
        apply mu_lt_of_G
        rw [G_of_one hph]
        by_cases hjp : j = p
        · have hph' : phase p C' = 2 := by
            rw [phase_of_loop hl', hmem]; simp [hop, hjp, ownerIs]
          rw [G_of_two hph']; omega
        · have hph' : phase p C' = 1 := by
            rw [phase_of_loop hl', hmem]; simp [hop, ownerIs, hjp]
          rw [G_of_one hph']
          have hmb : modeBit C' = 1 := by simp [modeBit, hmem]
          have hmb0 : modeBit C = 0 := by simp [modeBit, hvn]
          have hPhi : Phi p C' < Phi p C := by
            refine Phi_lt_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h') ?_
            have hns : ¬ Stale p C' p := fun hs => hs.1 rfl
            have hns0 : ¬ Stale p C p := fun hs => hs.1 rfl
            have hprio' : (C'.loc p).prio = nextP (C.loc p).prio := by rw [hloc]; simp
            unfold phi; simp only [hns, hns0, ↓reduceIte, hprio']
            have hpr : (C.loc p).prio ≠ p := by
              intro e; rcases hl.2 with e' | e'
              · exact hjp (e'.trans e)
              · exact hjp e'
            have := dist_nextP p _ hpr; omega
          omega
      · have hop' : isOp (av C.mem p) = false := by simpa using hop
        have h3 : phase p C = 3 := by rw [phase_of_loop hl0, hop']; rfl
        have h3' : phase p C' = 3 := by rw [phase_of_loop hl', hmem]; simp [hop']
        apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp [pl3, dLoop]
    · simp [hin] at hmem hloc; local_tac
  | scAnn =>
    have hl := hP.loc; simp only [LocInv, hpc] at hl
    obtain ⟨⟨rsp, hrsp⟩, hop⟩ := hl
    simp only [alg5, act, hpc, hrsp] at hact; cases hact
    have hl0 : (C.loc p).pc.inLoop = true := by rw [hpc]; rfl
    by_cases hin : p ∈ ac C.mem (C.loc p).aj
    · simp [hin] at hmem hloc
      have hl' : (C'.loc p).pc.inLoop = true := by rw [hloc]; simp [PC.inLoop]
      by_cases hjp : (C.loc p).aj = p
      · have hav : av C.mem p = (C.loc p).a := by
          have := hP.ca1 _ hin rfl; rw [hjp] at this; exact this
        have hop' : isOp (av C.mem p) = true := by rw [hav]; exact hop
        have hph12 : phase p C = 1 ∨ phase p C = 2 := by
          rw [phase_of_loop hl0, hop']; simp only [↓reduceIte]; split <;> simp
        have hph' : phase p C' = 3 := by
          rw [phase_of_loop hl', hmem, hjp]; simp [isOp]
        apply mu_lt_of_G
        rw [G_of_three hph']
        rcases hph12 with e | e
        · rw [G_of_one e]; omega
        · rw [G_of_two e]; omega
      · have hav : av C'.mem p = av C.mem p := by rw [hmem, av_update_ann_ne _ (Ne.symm hjp)]
        have hph : phase p C' = phase p C := by
          rw [phase_of_loop hl', phase_of_loop hl0, hav, hmem]; simp
        refine mu_lt_local hph (by rw [hmem]; simp) hlr
          (fun r hr h' => by rw [hmem] at h'; simpa using h') (by rw [hloc]; simp) ?_
        rw [pl_loop hl', pl_loop hl0, hph, hloc, hpc, hmem]
        split_ifs <;> simp_all [pl3, pl12, dLoop, PC.afterLL]
        split_ifs <;> omega
    · simp [hin] at hmem hloc; local_tac
  | scHead =>
    simp only [alg5, act, hpc] at hact; cases hact
    have hl := hP.loc; simp only [LocInv, hpc] at hl
    obtain ⟨rsp, hrsp⟩ := hl
    have hl0 : (C.loc p).pc.inLoop = true := by rw [hpc]; rfl
    by_cases hin : p ∈ hc C.mem
    · simp [hin] at hmem hloc
      have hhd := (hP.ch hin).1
      rw [hhd] at hmem
      have hvj : (hv C.mem).2 = some (rsp, (C.loc p).aj) := by rw [← hhd, hrsp]
      have hnotinl : ∀ o, av C.mem (C.loc p).aj ≠ some (.inl o) := by
        by_cases hac : p ∈ ac C.mem (C.loc p).aj
        · rw [hP.ca1 _ hac rfl]; intro o e
          exact hP.k4 hpc (by rw [e]; rfl) hac
        · exact hP.k3 hin (by rw [hpc]; rfl) hac
      have hl' : (C'.loc p).pc.inLoop = true := by
        rw [hloc]; simp only [Function.update_self]; split <;> rfl
      by_cases hop : isOp (av C.mem p) = true
      · have hjp : (C.loc p).aj ≠ p := by
          intro e; obtain ⟨o', ho'⟩ := (isOp_iff _).1 hop
          rw [← e] at ho'; exact hnotinl o' ho'
        have hph : phase p C = 1 := by
          rw [phase_of_loop hl0, hop, hvj]; simp [ownerIs, hjp]
        have hph' : phase p C' = 1 := by
          rw [phase_of_loop hl', hmem]; simp [hop, ownerIs]
        exact mu_lt_BA hph hph' (by simp [modeBit, hvj]) (by simp [modeBit, hmem])
          (phi_le_all hlr (fun r _ h' => by rw [hmem] at h'; simp at h')
            (phi_le_of (by rw [hloc]; simp) (fun hs => absurd rfl hs.1)))
      · have hop' : isOp (av C.mem p) = false := by simpa using hop
        have h3 : phase p C = 3 := by rw [phase_of_loop hl0, hop']; rfl
        have h3' : phase p C' = 3 := by rw [phase_of_loop hl', hmem]; simp [hop']
        apply mu_lt_three h3 h3'; rw [hloc, hpc]; simp only [Function.update_self]
        split <;> simp [pl3, dLoop]
    · simp [hin] at hmem hloc; split_ifs at hloc <;> local_tac

/-- **Wait-freedom** of Algorithm 5 with atomic R-LLSC base objects (the progress part of
Theorem 32 for atomic base objects): the potential `mu p` never increases while `p` is pending and
decreases at each of its steps. -/
theorem waitFree : (alg5 A n).WaitFree :=
  Impl.waitFreeOn_true_iff.1 <| (alg5 A n).waitFreeOn_of_runPotential (fun p _ C => mu p C)
    fun p _ C ℓ _ hα _ hs hp hp' => by
      have hinv := (inv_run hα).invC
      rcases ℓ with ⟨q, o⟩ | ⟨q, r⟩ | q
      · by_cases hq : q = p
        · subst hq; exact absurd (Impl.step_inv hs).1 hp
        · exact ⟨mu_inv_other p hq hs, fun h => by cases h⟩
      · by_cases hq : q = p
        · subst hq; exact absurd (by rw [(Impl.step_ret hs).2.1]; simp) hp'
        · exact ⟨mu_ret_other p hq hs, fun h => by cases h⟩
      · by_cases hq : q = p
        · subst hq
          have := mu_tau_self q hinv hs
          exact ⟨this.le, fun _ => this⟩
        · exact ⟨mu_tau_other p hinv hq hs, fun h => by cases h; exact absurd rfl hq⟩

/-- **Main result for atomic base objects** (Algorithm 5 with atomic R-LLSC `head` and
`announce[1..n]`, for an arbitrary object `A`): a linearizable, wait-free, state-quiescent
history-independent universal implementation. -/
theorem alg5_main : (alg5 A n).Linearizable ∧ (alg5 A n).WaitFree ∧
    (alg5 A n).StateQuiescentHI :=
  ⟨linearizable, waitFree, stateQuiescentHI⟩

end Universal

end Cslib.SharedMemory
