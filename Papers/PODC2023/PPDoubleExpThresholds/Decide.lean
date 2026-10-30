import Papers.PODC2023.PPDoubleExpThresholds.Summary
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Set.Infinite

/-!
# Deciding a predicate with restarts

The proof of Theorem 3 (Appendix A.4) argues: every initial configuration that is not "good"
eventually restarts (Lemma 4(c)); by fairness the computation eventually restarts with a good
configuration and stabilises. We make this precise for an arbitrary well-formed program:

* `decides_of_restart`: if (H1) for every total `m` and every value of `OF` some initial
  configuration of total `m` can reach a configuration from which no `restart` is reachable, and
  (H2) from every configuration reachable (without restarts) from an initial configuration of total
  `m` from which no `restart` is reachable, one can reach a configuration all of whose
  (restart-free) successors have `OF = φ(m)`, then the program decides `φ`.

The proof uses that only finitely many configurations are reachable (`finite_reach`: the total
is invariant, and the call stack is bounded by acyclicity of calls).
-/

namespace Podc.PPDoubleExpThresholds

open Cslib.TransitionSystem

variable {R P : Type*} [DecidableEq R] [Fintype R]

namespace Program

variable {prog : Program R P}

theorem total_mv (C : R → ℕ) {x y : R} (hx : 0 < C x) : total (mv C x y) = total C := by
  unfold total mv
  have hC : ∀ r, C r = (C r - if r = x then 1 else 0) + if r = x then 1 else 0 := by
    intro r; split <;> [subst_vars; skip] <;> omega
  conv_rhs => rw [Finset.sum_congr rfl (fun r _ => hC r)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem total_swp (C : R → ℕ) (x y : R) : total (swp C x y) = total C := by
  unfold total swp
  exact Equiv.sum_comp (Equiv.swap x y) C

theorem Step₀.total_eq {s s' : Cfg R P} (h : prog.Step₀ s s') : total s'.C = total s.C := by
  cases h with
  | move _ hx => exact total_mv _ hx
  | swap => exact total_swp _ _ _
  | _ => rfl

theorem Reach₀.total_eq {s s' : Cfg R P} (h : prog.Reach₀ s s') : total s'.C = total s.C := by
  induction h with
  | refl => rfl
  | tail _ h ih => rw [h.total_eq, ih]

theorem Step.total_eq {s s' : Cfg R P} (h : prog.Step s s') : total s'.C = total s.C := by
  rcases h with h | ⟨-, h, -⟩ | ⟨rfl, -⟩
  · exact h.total_eq
  · exact h
  · rfl

/-! ### Finiteness -/

/-- The largest jump target of an instruction. -/
def Instr.tgt : Instr R P → ℕ
  | .detect _ tT tF => max tT tF
  | .call _ tT tF => max tT tF
  | .goto t => t
  | _ => 0

variable (prog) in
/-- A bound on all program counters that can occur. -/
def pcBound : ℕ := ∑ p ∈ prog.procs, ((prog.code p).length + ((prog.code p).map Instr.tgt).sum)

theorem instr_mem {p : P} {pc : ℕ} {ins : Instr R P} (h : prog.instr p pc = some ins) :
    ins ∈ prog.code p := List.mem_of_getElem? h

theorem instr_lt {p : P} {pc : ℕ} {ins : Instr R P} (h : prog.instr p pc = some ins) :
    pc < (prog.code p).length := by
  unfold instr at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

theorem le_pcBound {p : P} (hp : p ∈ prog.procs) {n : ℕ}
    (hn : n ≤ (prog.code p).length + ((prog.code p).map Instr.tgt).sum) : n ≤ prog.pcBound :=
  hn.trans (Finset.single_le_sum (f := fun p => (prog.code p).length +
    ((prog.code p).map Instr.tgt).sum) (by intros; positivity) hp)

theorem tgt_le_sum {l : List (Instr R P)} {ins : Instr R P} (h : ins ∈ l) :
    Instr.tgt ins ≤ (l.map Instr.tgt).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

/-- The invariant of reachable call stacks. -/
def StkInv (prog : Program R P) (rank : P → ℕ) (σ : List (P × ℕ)) : Prop :=
  (∀ f ∈ σ, f.1 ∈ prog.procs ∧ f.2 ≤ prog.pcBound) ∧
    List.IsChain (fun f g => rank f.1 < rank g.1) σ ∧ σ.getLast?.map Prod.fst = some prog.main

theorem chain_length_le {rank : P → ℕ} {main : P} :
    ∀ (σ : List (P × ℕ)) (f : P × ℕ), List.IsChain (fun f g => rank f.1 < rank g.1) (f :: σ) →
      (f :: σ).getLast?.map Prod.fst = some main → (f :: σ).length + rank f.1 ≤ rank main + 1
  | [], f, _, h => by simp at h; simp [h]; omega
  | g :: σ, f, hc, h => by
    obtain ⟨hfg, hc'⟩ := List.isChain_cons_cons.1 hc
    have h' : (g :: σ).getLast?.map Prod.fst = some main := by
      simpa [List.getLast?_cons_cons] using h
    have := chain_length_le σ g hc' h'
    simp only [List.length_cons] at this ⊢
    omega

theorem StkInv.step (hwf : prog.WellFormed) {rank : P → ℕ}
    (hrank : ∀ p ∈ prog.procs, ∀ q tT tF, Instr.call q tT tF ∈ prog.code p → rank q < rank p)
    {s s' : Cfg R P} (h : prog.Step s s') (hs : StkInv prog rank s.stk) :
    StkInv prog rank s'.stk := by
  obtain ⟨hmem, hch, hlast⟩ := hs
  rcases h with h | ⟨-, -, -, h⟩ | ⟨rfl, -⟩
  · -- non-restart steps
    have frame : ∀ {p pc pc' σ}, (p, pc) :: σ = s.stk → prog.instr p pc ≠ none →
        pc' ≤ prog.pcBound → StkInv prog rank ((p, pc') :: σ) := by
      intro p pc pc' σ hst _ hpc'
      rw [← hst] at hmem hch hlast
      refine ⟨fun f hf => ?_, ?_, ?_⟩
      · simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact ⟨(hmem (p, pc) (by simp)).1, hpc'⟩
        · exact hmem f (by simp [hf])
      · cases σ with
        | nil => simp
        | cons g σ => simpa using hch
      · cases σ with
        | nil => simpa using hlast
        | cons g σ => simpa [List.getLast?_cons_cons] using hlast
    have hp : ∀ {p pc σ}, (p, pc) :: σ = s.stk → p ∈ prog.procs := fun {p pc σ} hst =>
      (hmem (p, pc) (by rw [← hst]; simp)).1
    cases h with
    | move hi => exact frame rfl (by simp [hi]) (le_pcBound (hp rfl) (by have := instr_lt hi; omega))
    | swap hi => exact frame rfl (by simp [hi]) (le_pcBound (hp rfl) (by have := instr_lt hi; omega))
    | setOF hi => exact frame rfl (by simp [hi]) (le_pcBound (hp rfl) (by have := instr_lt hi; omega))
    | detectT hi =>
      exact frame rfl (by simp [hi]) (le_pcBound (hp rfl) (by
        have := tgt_le_sum (instr_mem hi); simp [Instr.tgt] at this; omega))
    | detectF hi =>
      exact frame rfl (by simp [hi]) (le_pcBound (hp rfl) (by
        have := tgt_le_sum (instr_mem hi); simp [Instr.tgt] at this; omega))
    | goto hi =>
      exact frame rfl (by simp [hi]) (le_pcBound (hp rfl) (by
        have := tgt_le_sum (instr_mem hi); simp [Instr.tgt] at this; omega))
    | @call C OF p pc σ q tT tF hi =>
      have hpp : p ∈ prog.procs := hp rfl
      have hq : q ∈ prog.procs := hwf.call_mem p hpp q tT tF (instr_mem hi)
      refine ⟨fun f hf => ?_, ?_, ?_⟩
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact ⟨hq, Nat.zero_le _⟩
        · exact hmem f hf
      · exact List.isChain_cons_cons.2 ⟨hrank p hpp q tT tF (instr_mem hi), hch⟩
      · simpa [List.getLast?_cons_cons] using hlast
    | @ret C OF q pc p pc' σ b q' tT tF hi hi' =>
      have hpp : p ∈ prog.procs := (hmem (p, pc') (by simp)).1
      refine ⟨fun f hf => ?_, ?_, ?_⟩
      · rcases List.mem_cons.1 hf with rfl | hf
        · refine ⟨hpp, le_pcBound hpp ?_⟩
          have := tgt_le_sum (instr_mem hi')
          simp [Instr.tgt] at this; cases b <;> simp <;> omega
        · exact hmem f (by simp [hf])
      · cases σ with
        | nil => simp
        | cons g σ =>
          exact List.isChain_cons_cons.2 (List.isChain_cons_cons.1 (List.isChain_cons_cons.1 hch).2)
      · cases σ with
        | nil => simpa [List.getLast?_cons_cons] using hlast
        | cons g σ => simpa [List.getLast?_cons_cons] using hlast
  · rw [h]
    refine ⟨fun f hf => ?_, by simp, by simp⟩
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨hwf.main_mem, Nat.zero_le _⟩
  · exact ⟨hmem, hch, hlast⟩

/-- Only finitely many configurations are reachable from an initial configuration. -/
theorem finite_reach (hwf : prog.WellFormed) (C : R → ℕ) (OF : Bool) :
    {s | Reach prog.Step (prog.init C OF) s}.Finite := by
  classical
  obtain ⟨rank, hrank⟩ := hwf.acyclic
  set m := total C
  set D := rank prog.main + 1
  let T : Set (P × ℕ) := (prog.procs : Set P) ×ˢ Set.Iic prog.pcBound
  have hT : T.Finite := (Finset.finite_toSet _).prod (Set.finite_Iic _)
  have : Finite T := hT.to_subtype
  have hstk : {σ : List (P × ℕ) | σ.length ≤ D ∧ ∀ f ∈ σ, f ∈ T}.Finite := by
    refine ((List.finite_length_le T D).image (List.map Subtype.val)).subset ?_
    rintro σ ⟨hlen, hσ⟩
    refine ⟨σ.attach.map fun f => ⟨f.1, hσ f.1 f.2⟩, by simpa using hlen, ?_⟩
    simp [List.map_attach_eq_pmap]
  have hreg : {C' : R → ℕ | ∀ r, C' r ≤ m}.Finite := by
    have := Set.Finite.pi (t := fun _ : R => Set.Iic m) (fun _ => Set.finite_Iic m)
    simpa [Set.pi, Set.mem_Iic] using this
  have hfin := (hreg.prod (Set.finite_univ (α := Bool))).prod hstk
  refine (hfin.image fun x => (⟨x.1.1, x.1.2, x.2⟩ : Cfg R P)).subset ?_
  intro s hs
  have hinv : total s.C = m ∧ StkInv prog rank s.stk := by
    induction hs with
    | refl =>
      refine ⟨rfl, fun f hf => ?_, by simp [init], by simp [init]⟩
      simp only [init, List.mem_singleton] at hf
      subst hf; exact ⟨hwf.main_mem, Nat.zero_le _⟩
    | tail _ h ih => exact ⟨by rw [h.total_eq, ih.1], ih.2.step hwf hrank h⟩
  obtain ⟨htot, hmem, hch, hlast⟩ := hinv
  refine ⟨((s.C, s.OF), s.stk), ⟨⟨fun r => ?_, trivial⟩, ?_, ?_⟩, rfl⟩
  · rw [← htot]
    exact Finset.single_le_sum (f := s.C) (by simp) (Finset.mem_univ r)
  · cases hσ : s.stk with
    | nil => rw [hσ] at hlast; simp at hlast
    | cons f σ =>
      rw [hσ] at hch hlast
      have := chain_length_le σ f hch hlast
      simp only [List.length_cons] at this ⊢
      omega
  · intro f hf
    exact ⟨Finset.mem_coe.2 (hmem f hf).1, (hmem f hf).2⟩

/-! ### Deciding with restarts -/

/-- **Deciding with restarts.** See the module docstring. -/
theorem decides_of_restart (hwf : prog.WellFormed) (φ : ℕ → Bool)
    (H1 : ∀ m OF, ∃ C, total C = m ∧ ∃ s, prog.Reach₀ (prog.init C OF) s ∧ ¬ prog.CanRestart s)
    (H2 : ∀ C OF s, prog.Reach₀ (prog.init C OF) s → ¬ prog.CanRestart s →
      ∃ s', prog.Reach₀ s s' ∧ ∀ s'', prog.Reach₀ s' s'' → s''.OF = φ (total C)) :
    prog.Decides φ := by
  intro E hE0 hE
  have hst0 : E.st 0 = prog.init (E.st 0).C (E.st 0).OF := by
    rcases h : E.st 0 with ⟨C, OF, stk⟩
    rw [h] at hE0; simp only at hE0; simp [init, hE0]
  set C₀ := (E.st 0).C
  set OF₀ := (E.st 0).OF
  refine Run.GloballyFair.stabilisesTo_of_reach hE (hst0 ▸ finite_reach hwf C₀ OF₀) ?_
  -- the restart-free part of a run
  have hfree : ∀ s, ¬ prog.CanRestart s → ∀ s', Reach prog.Step s s' → prog.Reach₀ s s' := by
    intro s hs s' h
    induction h with
    | refl => exact .refl
    | tail _ h ih =>
      rcases h with h | ⟨hr, -⟩ | ⟨rfl, -⟩
      · exact ih.tail h
      · exact absurd ⟨_, ih, hr⟩ hs
      · exact ih
  have hreach₀ : ∀ {s s'}, prog.Reach₀ s s' → Reach prog.Step s s' := by
    intro s s' h
    induction h with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (.inl h)
  -- case of a restart-free configuration
  have hcase : ∀ C OF s, total C = total C₀ → prog.Reach₀ (prog.init C OF) s →
      ¬ prog.CanRestart s → ∃ y, Reach prog.Step s y ∧ StableOut prog.Step out (φ (total C₀)) y := by
    intro C OF s hC hs hns
    obtain ⟨s', hs', hst⟩ := H2 C OF s hs hns
    refine ⟨s', hreach₀ hs', fun y hy => ?_⟩
    have hns' : ¬ prog.CanRestart s' := fun ⟨z, hz, hr⟩ => hns ⟨z, hs'.trans hz, hr⟩
    simp only [out, hst y (hfree s' hns' y hy), hC]
  intro x hx
  -- invariant: reachable configurations are restart-free reachable from an initial one
  have hinv : ∃ C OF, total C = total C₀ ∧ prog.Reach₀ (prog.init C OF) x := by
    rw [hst0] at hx
    induction hx with
    | refl => exact ⟨C₀, OF₀, rfl, .refl⟩
    | tail _ h ih =>
      obtain ⟨C, OF, hC, hr⟩ := ih
      rcases h with h | ⟨-, htot, hOF, hstk⟩ | ⟨rfl, -⟩
      · exact ⟨C, OF, hC, hr.tail h⟩
      · rename_i b c _
        refine ⟨c.C, c.OF, ?_, ?_⟩
        · rw [htot, ← hC, hr.total_eq]; rfl
        · obtain ⟨cC, cOF, cstk⟩ := c
          simp only at hstk; subst hstk; exact .refl
      · exact ⟨C, OF, hC, hr⟩
  obtain ⟨C, OF, hC, hr⟩ := hinv
  by_cases hx' : prog.CanRestart x
  · obtain ⟨z, hz, hzr⟩ := hx'
    obtain ⟨Cg, hCg, sg, hsg, hnsg⟩ := H1 (total C₀) z.OF
    have hzC : total z.C = total C₀ := by rw [hz.total_eq, hr.total_eq, ← hC]; rfl
    have hstep : prog.Step z (prog.init Cg z.OF) := .inr (.inl ⟨hzr, by show total Cg = total z.C; rw [hCg, hzC], rfl, rfl⟩)
    obtain ⟨y, hy, hys⟩ := hcase Cg z.OF sg hCg hsg hnsg
    exact ⟨y, ((hreach₀ hz).tail hstep).trans ((hreach₀ hsg).trans hy), hys⟩
  · exact hcase C OF x hC hr hx'

end Program

end Podc.PPDoubleExpThresholds
