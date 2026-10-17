import Papers.PODC2020.BezoutElection.Alg2GlobProc
import Papers.PODC2020.BezoutElection.Exec

/-!
# Algorithm 2: safety (Lemma 2)

The invariant of reachable configurations (`RInv`): the global invariant `GInv` for the real
program counters, plus bookkeeping of program counters, pending operations and outputs. Every
output is computed from the final `leaders` fields once all registers are at level `U`.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open Cslib.SharedMemory Finset

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}
  {π : P → Equiv.Perm (Fin m)} {pp : Params} {ids : P → Id} {R : Type} [Inhabited R]
  {out : Id → Finset Id → R}

section Outputs

lemma outputs_snoc (α : List (Label P (elecObj R))) (ℓ : Label P (elecObj R)) (q : P) :
    outputs (α ++ [ℓ]) q = (outputs α q).or (ℓ.retOf q) := by
  simp only [outputs, respsOf_append]
  rw [List.head?_append]
  congr 1
  cases h : ℓ.retOf q <;> simp [respsOf, h]

lemma outputs_snoc_of_not_ret (α : List (Label P (elecObj R))) (ℓ : Label P (elecObj R)) (q : P)
    (h : ∀ r, ℓ ≠ .ret q r) : outputs (α ++ [ℓ]) q = outputs α q := by
  rw [outputs_snoc]
  cases ℓ with
  | ret p r =>
    by_cases hp : p = q
    · subst hp; exact absurd rfl (h r)
    · simp [Label.retOf, hp]
  | _ => simp [Label.retOf]

end Outputs

/-- The virtual program counters of a real configuration. -/
def vpcOf (loc : P → St Id m) : P → VPC Id := fun q => .pc (loc q).pc

variable (π pp ids out)

/-- The invariant of reachable configurations. -/
structure RInv (α : List (Label P (elecObj R)))
    (C : Config (elecObj R) (fun _ : Unit => memObj m (Reg Id) Reg.init) P (St Id m)) : Prop where
  g : ∃ g, GInv π pp ids (C.mem ()) C.loc (vpcOf C.loc) g
  pcok : ∀ q, (∀ k, (C.loc q).pc = .collect k → k < m) ∧ (∀ k w, (C.loc q).pc = .write k w → k < m)
  idle : ∀ q, (C.loc q).pc = .idle → C.pend q = none
  fin : ∀ q, (C.loc q).pc = .fin → outputs α q ≠ none
  out : ∀ q r, outputs α q = some r →
    (∀ x, (C.mem () x).level = pp.U) ∧ r = out (ids q) (univ.sup fun x => (C.mem () x).leaders)

variable {π pp ids out}

/-! ### Actions of Algorithm 2 -/

lemma act_collect (s : St Id m) {j : ℕ} (hpc : s.pc = .collect j) (hj : j < m) :
    (alg2 Id m pp out).act s = .rmw ⟨j, hj⟩ (fun v => v) (fun v =>
      if j + 1 < m then { s.setReg ⟨j, hj⟩ v with pc := .collect (j + 1) }
      else afterCollect pp (s.setReg ⟨j, hj⟩ v)) := by
  obtain ⟨me, pc, regs, phase, disc, loser, level, cand, toWin, fin⟩ := s
  simp only at hpc; subst hpc
  simp only [alg2, dif_pos hj]; rfl

lemma act_write (s : St Id m) {j : ℕ} {w : Reg Id} (hpc : s.pc = .write j w) (hj : j < m) :
    (alg2 Id m pp out).act s = .rmw ⟨j, hj⟩ (fun _ => w) (fun _ => loopFrom pp s (j + 1)) := by
  simp only [alg2, hpc, dif_pos hj]

lemma act_idle (s : St Id m) (hpc : s.pc = .idle) :
    (alg2 Id m pp out).act s = .ret default s := by
  simp only [alg2, hpc]

lemma act_ret (s : St Id m) {L : Finset Id} (hpc : s.pc = .ret L) :
    (alg2 Id m pp out).act s = .ret (out s.me L) { s with pc := .fin } := by
  simp only [alg2, hpc]

lemma act_fin (s : St Id m) (hpc : s.pc = .fin) :
    (alg2 Id m pp out).act s = .ret default s := by
  simp only [alg2, hpc]

lemma loopFrom_pc (s : St Id m) (j : ℕ) :
    (loopFrom pp s j).pc = .collect 0 ∨ ∃ k w, k < m ∧ (loopFrom pp s j).pc = .write k w := by
  rw [loopFrom]
  split_ifs with h
  · rcases e : procReg pp s ⟨j, h⟩ with ⟨s', _ | w⟩
    · simp only; exact loopFrom_pc s' (j + 1)
    · simp only
      exact Or.inr ⟨j, w, h, rfl⟩
  · exact Or.inl rfl
termination_by m - j

lemma vpcOf_update (loc : P → St Id m) (q : P) (s : St Id m) :
    vpcOf (Function.update loc q s) = Function.update (vpcOf loc) q (.pc s.pc) := by
  funext j; by_cases hj : j = q
  · subst hj; simp [vpcOf]
  · simp [vpcOf, Function.update_of_ne hj]

/-- Pending operations and program counters of a process that keeps running. -/
lemma pcok_of (hm : 0 < m) {c : PC Id}
    (h : c = .collect 0 ∨ (∃ k, k < m ∧ c = .collect k) ∨ ∃ k w, k < m ∧ c = .write k w) :
    (∀ k, c = .collect k → k < m) ∧ (∀ k w, c = .write k w → k < m) := by
  rcases h with rfl | ⟨k, hk, rfl⟩ | ⟨k, w, hk, rfl⟩
  · exact ⟨fun k h => (by cases h; exact hm), fun k w h => (by cases h)⟩
  · exact ⟨fun k' h => (by cases h; exact hk), fun k w h => (by cases h)⟩
  · exact ⟨fun k' h => (by cases h), fun k' w' h => (by cases h; exact hk)⟩

variable [Nonempty P]

theorem rinv_init :
    RInv π pp ids out [] ((alg2 Id m pp out).impl ids π).initCfg := by
  have hn11 : n11Count π (fun _ => (Reg.init : Reg Id))
      (vpcOf (fun q => (alg2 Id m pp out).init (ids q))) = 0 := by
    classical
    unfold n11Count
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro q - ⟨x, w, ⟨k, h, -⟩, -⟩
    simp [vpcOf, alg2] at h
  refine ⟨⟨⟨fun _ => 0, fun _ => 0⟩, ⟨fun x => ainv_init, fun q => rfl, ?_, ?_, fun q => Nat.zero_le _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_⟩
  all_goals try simp [Impl.initCfg, SymAlg.impl, alg2, Reg.init, vpcOf, PendAt, outputs, respsOf]
  · exact hn11

/-- Updating the local state and pending operation of `q`: other processes keep their facts. -/
lemma update_ne {α : Type*} (f : P → α) {q j : P} (a : α) (h : j ≠ q) :
    Function.update f q a j = f j := Function.update_of_ne h _ _

theorem rinv_step (hm : 0 < m) (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    {α : List (Label P (elecObj R))}
    {C C' : Config (elecObj R) (fun _ : Unit => memObj m (Reg Id) Reg.init) P (St Id m)}
    {ℓ : Label P (elecObj R)} (hI : RInv π pp ids out α C)
    (h : ((alg2 Id m pp out).impl ids π).step C ℓ = some C') :
    RInv π pp ids out (α ++ [ℓ]) C' := by
  obtain ⟨⟨g, G⟩, hpcok, hidle, hfin, hout⟩ := hI
  cases ℓ with
  | inv q o =>
    obtain ⟨hp, rfl⟩ := SymAlg.impl_step_inv_cases h
    have hout' : ∀ q', outputs (α ++ [.inv q o]) q' = outputs α q' :=
      fun q' => outputs_snoc_of_not_ret _ _ _ (by intro r h; cases h)
    by_cases hpc : (C.loc q).pc = .idle
    · have hinv : (alg2 Id m pp out).invoke (C.loc q) o = { C.loc q with pc := .collect 0 } := by
        simp [alg2, hpc]
      simp only [hinv]
      refine ⟨⟨g, ?_⟩, fun j => ?_, fun j hj => ?_, fun j hj => ?_, fun j r hj => ?_⟩
      · rw [vpcOf_update]; exact ginv_inv G (by simp [vpcOf, hpc])
      · by_cases hjq : j = q
        · subst hjq; simp only [Function.update_self]
          exact pcok_of hm (Or.inl rfl)
        · simp only [update_ne _ _ hjq]; exact hpcok j
      · by_cases hjq : j = q
        · subst hjq; simp at hj
        · simp only [update_ne _ _ hjq] at hj ⊢; exact hidle j hj
      · by_cases hjq : j = q
        · subst hjq; simp at hj
        · simp only [update_ne _ _ hjq] at hj; rw [hout']; exact hfin j hj
      · rw [hout'] at hj; exact hout j r hj
    · have hinv : (alg2 Id m pp out).invoke (C.loc q) o = C.loc q := by
        cases hc : (C.loc q).pc <;> simp_all [alg2]
      simp only [hinv, Function.update_eq_self]
      refine ⟨⟨g, G⟩, hpcok, fun j hj => ?_, fun j hj => by rw [hout']; exact hfin j hj,
        fun j r hj => by rw [hout'] at hj; exact hout j r hj⟩
      by_cases hjq : j = q
      · subst hjq; exact absurd hj hpc
      · simp only [update_ne _ _ hjq]; exact hidle j hj
  | tau q =>
    obtain ⟨hp, ⟨x, f, k, hact, rfl⟩ | ⟨k, hact, -⟩⟩ := SymAlg.impl_step_tau_cases h
    swap
    · exfalso
      simp only [alg2] at hact
      split at hact <;> (try split at hact) <;> simp at hact
    have hout' : ∀ q', outputs (α ++ [.tau q]) q' = outputs α q' :=
      fun q' => outputs_snoc_of_not_ret _ _ _ (by intro r h; cases h)
    rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _
    · rw [act_idle _ hpc] at hact; cases hact
    · -- a read of the collect
      have hj := (hpcok q).1 j hpc
      rw [act_collect _ hpc hj] at hact
      simp only [SymAction.rmw.injEq] at hact
      obtain ⟨rfl, rfl, rfl⟩ := hact
      have hmem : Function.update C.mem () (Function.update (C.mem ()) (π q ⟨j, hj⟩)
          (C.mem () (π q ⟨j, hj⟩))) = C.mem := by simp
      simp only [hmem]
      set v := C.mem () (π q ⟨j, hj⟩) with hv
      have hq : vpcOf C.loc q = .pc (.collect j) := by simp [vpcOf, hpc]
      have G1 := ginv_read G hj hq
      -- the new local state of `q` and its facts
      suffices H : ∃ s' g', (if j + 1 < m then { (C.loc q).setReg ⟨j, hj⟩ v with pc := .collect (j + 1) }
          else afterCollect pp ((C.loc q).setReg ⟨j, hj⟩ v)) = s' ∧
          GInv π pp ids (C.mem ()) (Function.update C.loc q s') (vpcOf (Function.update C.loc q s')) g' ∧
          (s'.pc = .collect 0 ∨ (∃ k, k < m ∧ s'.pc = .collect k) ∨
            (∃ k w, k < m ∧ s'.pc = .write k w) ∨ (∃ L, s'.pc = .ret L)) by
        obtain ⟨s', g', hs', G', hpc'⟩ := H
        simp only [hs']
        refine ⟨⟨g', G'⟩, fun j' => ?_, fun j' hj' => ?_, fun j' hj' => ?_, fun j' r hj' => ?_⟩
        · by_cases hjq : j' = q
          · subst hjq; simp only [Function.update_self]
            rcases hpc' with h1 | ⟨k, hk, h1⟩ | ⟨k, w, hk, h1⟩ | ⟨L, h1⟩
            · exact pcok_of hm (Or.inl h1)
            · exact pcok_of hm (Or.inr (Or.inl ⟨k, hk, h1⟩))
            · exact pcok_of hm (Or.inr (Or.inr ⟨k, w, hk, h1⟩))
            · rw [h1]; exact ⟨fun k h => by simp at h, fun k w h => by simp at h⟩
          · simp only [update_ne _ _ hjq]; exact hpcok j'
        · by_cases hjq : j' = q
          · subst hjq; simp only [Function.update_self] at hj'
            rcases hpc' with h1 | ⟨k, hk, h1⟩ | ⟨k, w, hk, h1⟩ | ⟨L, h1⟩ <;> simp [h1] at hj'
          · simp only [update_ne _ _ hjq] at hj'; exact hidle j' hj'
        · by_cases hjq : j' = q
          · subst hjq; simp only [Function.update_self] at hj'
            rcases hpc' with h1 | ⟨k, hk, h1⟩ | ⟨k, w, hk, h1⟩ | ⟨L, h1⟩ <;> simp [h1] at hj'
          · simp only [update_ne _ _ hjq] at hj'; rw [hout']; exact hfin j' hj'
        · rw [hout'] at hj'; exact hout j' r hj'
      by_cases hjm : j + 1 < m
      · refine ⟨_, g, if_pos hjm, ?_, Or.inr (Or.inl ⟨j + 1, hjm, rfl⟩)⟩
        rw [vpcOf_update]
        refine ginv_congr G1 (fun j' => ?_)
        by_cases hjq : j' = q
        · subst hjq; exact ⟨.collect (j + 1), by simp only [Function.update_self]; rfl⟩
        · exact ⟨(C.loc j').pc, by simp [Function.update_of_ne hjq]⟩
      · have hjm' : j + 1 = m := by omega
        rw [if_neg hjm]
        rw [hjm'] at G1
        set s' := (C.loc q).setReg ⟨j, hj⟩ v with hs'
        have hq1 : Function.update (vpcOf C.loc) q (.pc (.collect m)) q = .pc (.collect m) := by simp
        unfold afterCollect
        dsimp only
        by_cases hsum : ∑ x, (s'.regs x).level = pp.U * m
        · rw [if_pos hsum]
          refine ⟨_, g, rfl, ?_, Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))⟩
          have G2 := ginv_after_ret G1 hq1 (by simpa using hsum)
          simp only [Function.update_idem, Function.update_self] at G2
          rw [vpcOf_update]; exact G2
        · rw [if_neg hsum]
          have G2 := ginv_after_loop hn G1 hq1
          simp only [Function.update_idem, Function.update_self] at G2
          obtain ⟨g3, G3⟩ := ginv_loopFrom hid hn G2 (q := q) (j := 0) (by simp)
          simp only [Function.update_idem, Function.update_self] at G3
          refine ⟨_, g3, rfl, by rw [vpcOf_update]; exact G3, ?_⟩
          rcases loopFrom_pc (pp := pp) (if pp.W * pp.n ≤ ∑ x, (s'.regs x).level ∧
              s'.finishing = false then { s' with finishing := true, toWin := 1 } else s') 0 with
            h1 | ⟨k, w, hk, h1⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inr (Or.inl ⟨k, w, hk, h1⟩))
    · -- a write
      have hj := (hpcok q).2 j w hpc
      rw [act_write _ hpc hj] at hact
      simp only [SymAction.rmw.injEq] at hact
      obtain ⟨rfl, rfl, rfl⟩ := hact
      have hq : vpcOf C.loc q = .pc (.write j w) := by simp [vpcOf, hpc]
      have G1 := ginv_write hid hn G hj hq
      obtain ⟨g2, G2⟩ := ginv_loopFrom hid hn G1 (q := q) (j := j + 1) (by simp)
      simp only [Function.update_idem, Function.update_self, Function.update_eq_self] at G2
      have hlevel : (C.mem () (π q ⟨j, hj⟩)).level < pp.U := by
        have A0 := G.abs (π q ⟨j, hj⟩)
        have hst : ((absAt π (C.mem ()) C.loc (vpcOf C.loc) (π q ⟨j, hj⟩)).loc q).st = .pend w := by
          rw [absAt_loc, hq, Equiv.symm_apply_apply]; simp [locX, vstatus]
        exact (A0.1.pendLv q w hst).2.1
      refine ⟨⟨g2, by rw [vpcOf_update]; exact G2⟩, fun j' => ?_, fun j' hj' => ?_,
        fun j' hj' => ?_, fun j' r hj' => ?_⟩
      · by_cases hjq : j' = q
        · subst hjq; simp only [Function.update_self]
          rcases loopFrom_pc (pp := pp) (C.loc j') (j + 1) with h1 | ⟨k, w', hk, h1⟩
          · exact pcok_of hm (Or.inl h1)
          · exact pcok_of hm (Or.inr (Or.inr ⟨k, w', hk, h1⟩))
        · simp only [update_ne _ _ hjq]; exact hpcok j'
      · by_cases hjq : j' = q
        · subst hjq; simp only [Function.update_self] at hj'
          rcases loopFrom_pc (pp := pp) (C.loc j') (j + 1) with h1 | ⟨k, w', hk, h1⟩ <;>
            rw [h1] at hj' <;> cases hj'
        · simp only [update_ne _ _ hjq] at hj'; exact hidle j' hj'
      · by_cases hjq : j' = q
        · subst hjq; simp only [Function.update_self] at hj'
          rcases loopFrom_pc (pp := pp) (C.loc j') (j + 1) with h1 | ⟨k, w', hk, h1⟩ <;>
            rw [h1] at hj' <;> cases hj'
        · simp only [update_ne _ _ hjq] at hj'; rw [hout']; exact hfin j' hj'
      · rw [hout'] at hj'
        have := (hout j' r hj').1 (π q ⟨j, hj⟩)
        omega
    · rw [act_ret _ hpc] at hact; cases hact
    · rw [act_fin _ hpc] at hact; cases hact
  | ret q r =>
    obtain ⟨hp, s, hact, rfl⟩ := SymAlg.impl_step_ret_cases h
    have hout' : ∀ q', q' ≠ q → outputs (α ++ [.ret q r]) q' = outputs α q' :=
      fun q' hq' => outputs_snoc_of_not_ret _ _ _ (by intro r' h; cases h; exact hq' rfl)
    have houtq : outputs (α ++ [.ret q r]) q = (outputs α q).or (some r) := by
      rw [outputs_snoc]; simp [Label.retOf]
    rcases hpc : (C.loc q).pc with _ | j | ⟨j, w⟩ | L | _
    · exact absurd (hidle q hpc) hp
    · have hj := (hpcok q).1 j hpc
      rw [act_collect _ hpc hj] at hact; cases hact
    · have hj := (hpcok q).2 j w hpc
      rw [act_write _ hpc hj] at hact; cases hact
    · -- the response of `elect()`
      rw [act_ret _ hpc] at hact
      simp only [SymAction.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      have hq : vpcOf C.loc q = .pc (.ret L) := by simp [vpcOf, hpc]
      obtain ⟨hU, hL⟩ := G.ret q L hq
      refine ⟨⟨g, by rw [vpcOf_update]; exact ginv_retStep G hq⟩, fun j' => ?_, fun j' hj' => ?_,
        fun j' hj' => ?_, fun j' r' hj' => ?_⟩
      · by_cases hjq : j' = q
        · subst hjq; simp only [Function.update_self]
          exact ⟨fun k h => (by cases h), fun k w h => (by cases h)⟩
        · simp only [update_ne _ _ hjq]; exact hpcok j'
      · by_cases hjq : j' = q
        · subst hjq; simp at hj'
        · simp only [update_ne _ _ hjq] at hj' ⊢; exact hidle j' hj'
      · by_cases hjq : j' = q
        · subst hjq; rw [houtq]; cases outputs α j' <;> simp
        · simp only [update_ne _ _ hjq] at hj'; rw [hout' j' hjq]; exact hfin j' hj'
      · by_cases hjq : j' = q
        · subst hjq
          rw [houtq] at hj'
          cases ho : outputs α j' with
          | none =>
            rw [ho] at hj'; simp only [Option.none_or, Option.some.injEq] at hj'; subst hj'
            refine ⟨hU, ?_⟩
            rw [G.me j', hL]
          | some r0 =>
            rw [ho] at hj'; simp only [Option.some_or, Option.some.injEq] at hj'; subst hj'
            exact hout j' r0 ho
        · rw [hout' j' hjq] at hj'; exact hout j' r' hj'
    · -- a second response after returning
      rw [act_fin _ hpc] at hact
      simp only [SymAction.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      simp only [Function.update_eq_self]
      have hfq := hfin q hpc
      refine ⟨⟨g, G⟩, hpcok, fun j' hj' => ?_, fun j' hj' => ?_, fun j' r' hj' => ?_⟩
      · by_cases hjq : j' = q
        · subst hjq; rw [hpc] at hj'; cases hj'
        · simp only [update_ne _ _ hjq]; exact hidle j' hj'
      · by_cases hjq : j' = q
        · subst hjq; rw [houtq]; cases ho : outputs α j' <;> simp_all
        · rw [hout' j' hjq]; exact hfin j' hj'
      · by_cases hjq : j' = q
        · subst hjq
          rw [houtq] at hj'
          cases ho : outputs α j' with
          | none => exact absurd ho hfq
          | some r0 =>
            rw [ho] at hj'; simp only [Option.some_or, Option.some.injEq] at hj'; subst hj'
            exact hout j' r0 ho
        · rw [hout' j' hjq] at hj'; exact hout j' r' hj'

theorem rinv_run (hm : 0 < m) (hid : Function.Injective ids) (hn : Fintype.card P = pp.n)
    {α : List (Label P (elecObj R))}
    {C : Config (elecObj R) (fun _ : Unit => memObj m (Reg Id) Reg.init) P (St Id m)}
    (h : ((alg2 Id m pp out).impl ids π).run α = some C) : RInv π pp ids out α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    rw [Impl.run_nil] at h; cases h; exact rinv_init
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : ((alg2 Id m pp out).impl ids π).runFrom ((alg2 Id m pp out).impl ids π).initCfg α with
    | none => simp [hα] at h
    | some C1 =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      exact rinv_step hm hid hn (ih hα) h

end BezoutElection.Alg2

namespace BezoutElection.Alg2

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P] {m : ℕ}
  {R : Type} [Inhabited R]

/-- **Lemma 2 (safety)**, under the assumptions `m ≥ 1` and `W n ≤ U m` (i.e. `d ≥ 0`). -/
theorem alg2_agreement' (p : Params) (out : Id → Finset Id → R) (ids : P → Id)
    (hid : Function.Injective ids) (hn : Fintype.card P = p.n) (π : P → Equiv.Perm (Fin m))
    (hm : 0 < m) (hW : p.W * p.n ≤ p.U * m)
    (α : List (Label P (elecObj R))) (hα : ((alg2 Id m p out).impl ids π).Valid α) :
    ∃ L : Finset Id, (∀ q r, outputs α q = some r → r = out (ids q) L) ∧
      ((∃ q, outputs α q ≠ none) → L.card + p.W * p.n = p.U * m ∧ ∀ a ∈ L, ∃ q, ids q = a) := by
  by_cases hP : Nonempty P
  swap
  · refine ⟨∅, fun q => absurd ⟨q⟩ hP, fun ⟨q, _⟩ => absurd ⟨q⟩ hP⟩
  obtain ⟨C, hC⟩ := hα
  obtain ⟨⟨g, G⟩, -, -, -, hout⟩ := rinv_run hm hid hn hC
  set L := univ.sup fun x => (C.mem () x).leaders with hL
  refine ⟨L, fun q r h => (hout q r h).2, fun ⟨q, hq⟩ => ?_⟩
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hq
  have hU := (hout q r hr).1
  -- no pending writes
  have hnoP : ∀ j x w, ¬PendAt π (vpcOf C.loc) j x w := by
    intro j x w h
    have A := G.abs x
    have := (A.1.pendLv j w (pendAt_iff.1 h)).2.1
    simp only [absAt_reg, hU x] at this; omega
  have hn11 : n11Count π (C.mem ()) (vpcOf C.loc) = 0 := by
    classical
    unfold n11Count
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro j - ⟨x, w, h, -⟩; exact hnoP j x w h
  have h5 : p.U * m = ∑ j, g.wf j + ∑ j, g.wt j := by
    have h5 := G.g5
    rw [hn11, add_zero, Finset.sum_add_distrib] at h5
    rw [← h5]
    simp [hU, mul_comm]
  have hwt1 : ∀ j, g.wt j ≤ 1 := by
    intro j
    cases hf : (C.loc j).finishing
    · rw [(G.g1 j hf).2]; omega
    · have := G.g2 j hf; omega
  have hwf : ∑ j, g.wf j = p.W * p.n := by
    by_cases hex : ∃ j, (C.loc j).finishing = true
    · exact G.g4 hex
    · push Not at hex
      have hwt : ∀ j, g.wt j = 0 := fun j => (G.g1 j (by simpa using hex j)).2
      simp only [hwt, sum_const_zero, add_zero] at h5
      have hle : ∑ j, g.wf j ≤ p.W * p.n := by
        calc ∑ j, g.wf j ≤ ∑ _j : P, p.W := Finset.sum_le_sum fun j _ => G.g3 j
          _ = p.W * p.n := by simp [hn, mul_comm]
      omega
  -- the leaders are the winners with `finishing` set
  have hLeq : L = (univ.filter fun j => g.wt j = 1).image ids := by
    ext a
    simp only [hL, Finset.mem_sup, mem_univ, true_and, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨j, h1, h2⟩ := G.g6a x a hx
      exact ⟨j, h2, h1⟩
    · rintro ⟨j, h1, rfl⟩
      rcases G.g6b j h1 with h | ⟨x, w, h, -⟩
      · exact h
      · exact absurd h (hnoP j x w)
  have hcard : L.card = ∑ j, g.wt j := by
    rw [hLeq, Finset.card_image_of_injective _ hid, Finset.card_filter]
    exact Finset.sum_congr rfl fun j _ => by
      have := hwt1 j
      split_ifs with h <;> omega
  refine ⟨by omega, fun a ha => ?_⟩
  rw [hLeq] at ha
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
  exact ⟨j, rfl⟩

end BezoutElection.Alg2
