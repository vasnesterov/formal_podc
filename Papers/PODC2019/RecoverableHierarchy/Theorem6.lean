import Papers.PODC2019.RecoverableHierarchy.Critical

/-!
# Theorem 6 and Corollary 7: generic constructions from `f` consensus objects

**Definition 5 (genericity).** A construction of recoverable consensus from consensus objects
and registers is *generic* if, in all executions, a process that has accessed a consensus object
`C` and then crashed never accesses `C` again (`Generic`).

**Theorem 6.** For every `f`, no generic algorithm using at most `f` consensus objects and any
number of read/write registers solves `n`-process recoverable consensus with independent
failures, even if there are at most `f` failures and at most two processes participate.

The consensus objects are atomic sticky consensus objects `consObj V` (values in an arbitrary
type `V`; every `propose` returns the first proposed value — the paper's "single atomic step"
model of an `n`-consensus object, without a bound on the number of accesses). The proof is the
paper's (Assumption 2: process `a` crashes right after its first access to each consensus
object); Case B uses genericity: after its crash, `a` never accesses the object again, so the
different decisions of the object in the two executions are invisible to it.
-/

namespace Podc.RecoverableHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ}

/-- **Definition 5 (genericity)**, on the executions `Adm`: whenever an admissible execution
from an initial configuration has the form `α · p accesses C · β · crash of p · γ · step of p`
with `C` a consensus object (`isC C`), the last step of `p` is not an access to `C`. -/
def Generic (A : Alg n T) (isC : ι → Prop) (Adm : List (Ev n) → Prop) : Prop :=
  ∀ x (α β γ : List (Ev n)) (p : Fin n) (i : ι), isC i →
    Adm (α ++ [.step p] ++ β ++ [.crash p] ++ γ ++ [.step p]) →
    (run (initCfg A x) α).Poised p i →
    ¬ (run (initCfg A x) (α ++ [.step p] ++ β ++ [.crash p] ++ γ)).Poised p i

/-- Executions with at most `f` failures in which only `p₁ = 0` and `p₂ = 1` take steps. -/
def AtMostTwo (f : ℕ) (γ : List (Ev n)) : Prop := AtMost f γ ∧ ∀ e ∈ γ, e.proc.val < 2

namespace Theorem6

variable {ιR ιS V : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS] {R : ιR → ObjSpec}

/-- The triggering operations of Assumption 2: any access to a consensus object. -/
def trigC : (i : ιR ⊕ ιS) → (withRW (ιS := ιS) R (consObj V) i).Op → Bool
  | .inl _, _ => false
  | .inr _, _ => true

/-- The consensus objects. -/
def consSet : Finset (ιR ⊕ ιS) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

lemma card_consSet : (consSet : Finset (ιR ⊕ ιS)).card = Fintype.card ιS := by
  simp [consSet]

/-- The restricted model of Assumption 2 for processes `a ≠ b`. -/
def restr (A : Alg n (withRW (ιS := ιS) R (consObj V))) (a b : Fin n) (hab : a ≠ b) :
    Restr A where
  a := a
  b := b
  hab := hab
  trig := trigC
  F := consSet
  hF := by
    rintro (j | j) o h
    · simp [trigC] at h
    · simp [consSet]

variable {n : ℕ} {A : Alg n (withRW (ιS := ιS) R (consObj V))} {a b : Fin n} {hab : a ≠ b}

/-- A decided consensus object stays decided. -/
lemma stepP_mem_cons (C : Cfg A) (p : Fin n) (j : ιS)
    (h : (C.mem (.inr j) : Option V).isSome) : ((C.stepP p).mem (.inr j) : Option V).isSome := by
  rcases hact : A.act (C.loc p) with ⟨i, o, k⟩ | v
  · rw [stepP_mem_of_access _ hact]
    by_cases hi : Sum.inr j = i
    · subst hi
      simp only [Function.update_self]
      rfl
    · exact (congrArg Option.isSome (Function.update_of_ne hi _ C.mem)).trans h
  · rw [stepP_of_out _ (show C.Out p v from hact)]; exact h

/-- **Invariant**: every consensus object accessed by `a` is decided. -/
lemma consInv (x : Fin n → Bool) (σ : List Bool) (j : ιS)
    (hj : Sum.inr j ∈ ((restr A a b hab).S x σ).trg) :
    (((restr A a b hab).S x σ).c.mem (.inr j) : Option V).isSome := by
  set Rs := restr A a b hab
  suffices ∀ σ (s : RS A), (∀ j : ιS, Sum.inr j ∈ s.trg → (s.c.mem (.inr j) : Option V).isSome) →
      ∀ j : ιS, Sum.inr j ∈ (Rs.rrun s σ).trg →
        ((Rs.rrun s σ).c.mem (.inr j) : Option V).isSome from
    this σ _ (fun j h => by simp [RS.init] at h) j hj
  intro σ
  induction σ with
  | nil => intro s hs; exact hs
  | cons m σ ih =>
    intro s hs
    apply ih
    intro j hj
    cases m
    · by_cases hp : s.pend
      · rw [Rs.mv_false_pend s hp] at hj ⊢
        exact hs j hj
      · simp only [Bool.not_eq_true] at hp
        rw [Rs.mv_false_npend s hp] at hj ⊢
        rcases hn : Rs.newTrig s with _ | i
        · simp only [hn] at hj ⊢
          exact stepP_mem_cons _ _ _ (hs j hj)
        · simp only [hn, Finset.mem_insert] at hj ⊢
          rcases hj with rfl | hj
          · unfold Restr.newTrig at hn
            rcases hact : A.act (s.c.loc Rs.a) with ⟨i', o, k⟩ | v
            · rw [hact] at hn
              simp only at hn
              split_ifs at hn with hc
              cases hn
              rw [stepP_mem_of_access _ hact, Function.update_self]
              rfl
            · rw [hact] at hn; cases hn
          · exact stepP_mem_cons _ _ _ (hs j hj)
    · exact stepP_mem_cons _ _ _ (hs j hj)

/-- The core of the proof of Theorem 6: no generic algorithm with consensus objects and
read/write-like objects is correct on the restricted executions of Assumption 2. -/
theorem not_rcorrect (hR : ∀ j, (R j).RWLike) {Adm : List (Ev n) → Prop}
    (hAdm : ∀ x σ, Adm ((restr A a b hab).E x σ))
    (hgen : Generic A (fun i => ∃ j, i = Sum.inr j) Adm) : ¬ (restr A a b hab).RCorrect := by
  intro hC
  set Rs := restr A a b hab
  obtain ⟨σ, v, w, hc⟩ := Restr.exists_crit' hC
  set s := Rs.S Rs.x₀ σ with hs
  by_cases hp : s.pend
  · exact hc.false_of_b_absorbs hC (Rs.absorb_b_of_pend s hp)
  simp only [Bool.not_eq_true] at hp
  rcases ha : A.act (s.c.loc Rs.a) with ⟨i, o, k⟩ | u
  swap
  · exact hc.not_out hC Rs.a u ha
  rcases hb : A.act (s.c.loc Rs.b) with ⟨j, o', k'⟩ | u
  swap
  · exact hc.not_out hC Rs.b u hb
  by_cases hij : i = j
  swap
  · exact hc.false_of_commute hC (Rs.commute_of_ne hp ⟨o, k, ha⟩ ⟨o', k', hb⟩ hij)
  subst hij
  rcases i with r | r
  · have hR' : (withRW (ιS := ιS) R (consObj V) (.inl r)).RWLike := hR r
    rcases (ObjSpec.rwLike_iff.1 hR') o with ho | ho
    · exact hc.false_of_b_absorbs hC (Rs.absorb_b_of_absorb hp ha hb (by rw [ho]))
    rcases (ObjSpec.rwLike_iff.1 hR') o' with ho' | ho'
    · exact hc.false_of_a_absorbs hC (Rs.absorb_a_of_absorb hp ha hb (by rw [ho']))
    · exact hc.false_of_b_absorbs hC (Rs.absorb_b_of_absorb hp ha hb (ho' _ _))
  · change V at o o'
    cases hm : (s.c.mem (.inr r) : Option V) with
    | some u =>
      -- Case C: the object is decided; both proposals return its decision
      exact hc.false_of_commute hC
        (Rs.commute_of_commuteAt hp ha hb (by rw [hm]; rfl) (by rw [hm]; rfl) (by rw [hm]; rfl))
    | none =>
      -- Case B: undecided, so `a` has not accessed it; `a` crashes right after its proposal
      have hnot : Sum.inr r ∉ s.trg := fun h => by
        have := consInv (hab := hab) Rs.x₀ σ r h
        rw [hm] at this; cases this
      have ht : Rs.newTrig s = some (.inr r) := by
        unfold Restr.newTrig; rw [ha]; simp [Rs, restr, trigC, hnot]
      have hag := Rs.hide_agA hp ha hb ht {Sum.inr r} (Or.inl rfl)
      refine hc.false_of_hide hC (S := {Sum.inr r}) (by rw [Rs.S_two, Rs.S_three]; exact hag) ?_
      -- by genericity, `a` never accesses the object again
      intro m hpm i hi hpo
      rw [Set.mem_singleton_iff] at hi; subst hi
      have hpend1 : (Rs.mv s false).pend = true := by
        rw [Rs.mv_false_npend s hp, ht]
      have e1 : Rs.ev s false = .step Rs.a := Rs.ev_false_npend s hp
      have e2 : Rs.ev (Rs.mv s false) false = .crash Rs.a := Rs.ev_false_pend _ hpend1
      set τ := σ ++ [false, false] ++ List.replicate m false
      have e3 : Rs.ev (Rs.S Rs.x₀ τ) false = .step Rs.a := Rs.ev_false_npend _ hpm
      have hE : Rs.E Rs.x₀ (τ ++ [false]) = Rs.E Rs.x₀ σ ++ [.step Rs.a] ++ [] ++
          [.crash Rs.a] ++ Rs.evs (Rs.S Rs.x₀ (σ ++ [false, false])) (List.replicate m false) ++
          [.step Rs.a] := by
        show Rs.evs (RS.init A Rs.x₀) (σ ++ [false, false] ++ List.replicate m false ++ [false])
          = _
        rw [Rs.evs_append, Rs.evs_append, Rs.evs_append]
        have h2 : Rs.evs (Rs.rrun (RS.init A Rs.x₀) σ) [false, false] =
            [.step Rs.a, .crash Rs.a] := by
          show [Rs.ev s false, Rs.ev (Rs.mv s false) false] = _
          rw [e1, e2]
        have h4 : Rs.evs (Rs.rrun (RS.init A Rs.x₀) (σ ++ [false, false] ++
            List.replicate m false)) [false] = [.step Rs.a] := by
          show [Rs.ev (Rs.S Rs.x₀ τ) false] = _
          rw [e3]
        rw [h2, h4]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hrun : run (initCfg A Rs.x₀) (Rs.E Rs.x₀ σ ++ [.step Rs.a] ++ [] ++ [.crash Rs.a] ++
          Rs.evs (Rs.S Rs.x₀ (σ ++ [false, false])) (List.replicate m false)) =
          (Rs.S Rs.x₀ τ).c := by
        rw [Rs.S_c]
        have : Rs.E Rs.x₀ (τ ++ [false]) = Rs.E Rs.x₀ τ ++ [Rs.ev (Rs.S Rs.x₀ τ) false] :=
          Rs.evs_concat _ _ _
        rw [hE, e3] at this
        exact congrArg _ (List.append_cancel_right this)
      refine hgen Rs.x₀ (Rs.E Rs.x₀ σ) [] _ Rs.a (.inr r) ⟨r, rfl⟩ (by rw [← hE]; exact hAdm _ _)
        (by rw [← Rs.S_c]; exact ⟨o, k, ha⟩) ?_
      rw [hrun]; exact hpo

end Theorem6

open Theorem6

/-- **Theorem 6** (general form): no generic algorithm using `|ιS|` atomic consensus objects
and any read/write-like objects satisfies the paper's recoverable-consensus specification on a
set of executions `Adm` that contains the restricted executions of Assumption 2 for two
processes `a ≠ b` (only `a`, `b` step, `b` never crashes, `a` crashes at most `|ιS|` times). -/
theorem theorem6_gen {ιR ιS V : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS]
    {R : ιR → ObjSpec} (hR : ∀ j, (R j).RWLike) {n : ℕ}
    (A : Alg n (withRW (ιS := ιS) R (consObj V))) (a b : Fin n) (hab : a ≠ b)
    {Adm : List (Ev n) → Prop} (hAdm : ∀ x σ, Adm ((restr A a b hab).E x σ))
    (hgen : Generic A (fun i => ∃ j, i = Sum.inr j) Adm) : ¬ SolvesP A Adm :=
  fun h => not_rcorrect hR hAdm hgen (h.rcorrect _ hAdm)

/-- **Theorem 6.** For every `f` and `n ≥ 2`, there is no generic algorithm that uses at most `f`
`n`-consensus objects (atomic consensus objects) and any number of read/write registers (more
generally, read/write-like objects) and solves `n`-process recoverable consensus with independent
failures, even if there are at most `f` failures and at most two processes participate.
(Genericity is only required on these executions; the paper states it for `f > 0`.) -/
theorem theorem6 {ιR ιS V : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS]
    {R : ιR → ObjSpec} (hR : ∀ j, (R j).RWLike) {n : ℕ} (hn : 2 ≤ n) (f : ℕ)
    (hf : Fintype.card ιS ≤ f) (A : Alg n (withRW (ιS := ιS) R (consObj V)))
    (hgen : Generic A (fun i => ∃ j, i = Sum.inr j) (AtMostTwo f)) :
    ¬ SolvesP A (AtMostTwo f) := by
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  refine theorem6_gen hR A _ _ hab (fun x σ => ⟨Restr.atMost_E _ ?_ x σ, fun e he => ?_⟩) hgen
  · rw [show (restr A _ _ hab).F = consSet from rfl, card_consSet]; exact hf
  · obtain ⟨m, -, hm⟩ := Restr.mem_evs_proc _ _ _ e he
    rw [hm]; cases m <;> simp [Restr.who, restr]

/-- **Corollary 7.** A generic `n`-process recoverable consensus algorithm from atomic
consensus objects and read/write registers that tolerates executions with up to `f` failures
(even only those with at most two participants) uses more than `f` consensus objects. -/
theorem corollary7 {ιR ιS V : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS]
    {R : ιR → ObjSpec} (hR : ∀ j, (R j).RWLike) {n : ℕ} (hn : 2 ≤ n) (f : ℕ)
    (A : Alg n (withRW (ιS := ιS) R (consObj V)))
    (hgen : Generic A (fun i => ∃ j, i = Sum.inr j) (AtMostTwo f))
    (hA : SolvesP A (AtMostTwo f)) : f < Fintype.card ιS := by
  by_contra h
  exact theorem6 hR hn f (by omega) A hgen hA

end Podc.RecoverableHierarchy
