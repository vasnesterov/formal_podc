import Papers.PODC2019.RecoverableHierarchy.Critical

/-!
# Theorem 3 and Corollary 4: `f` readable test-and-set objects do not suffice

**Theorem 3.** For every `f`, no algorithm using at most `f` readable test-and-set objects and
any number of read/write registers solves 2-process recoverable consensus with independent
crash-recovery failures, even if every execution has at most `f` failures.

We follow the paper's valency argument in the restricted failure model, with a **repaired
Assumption 1**: process `a` (the paper's `p₁`) crashes right after its first **test-and-set
operation** on each rTAS object (the paper says: its first *access*, which includes reads; with
that reading the proof's Case C is wrong, see `Assumption1Gap.lean`). Then a TAS object on which
`a` has applied `tas` holds `1` (`tasInv`), which is what Cases B and C need.

The objects are CSLib's `withRW (ιS := ιS) R rtasObj`: arbitrary read/write-like objects `R j`
(`ObjSpec.RWLike`, e.g. registers of any type) and readable test-and-set objects indexed by a
finite type `ιS` with `|ιS| ≤ f`. The theorem is proved for the paper's specification `SolvesP`
(agreement only between distinct processes), for any number `n ≥ 2` of processes of which only
two participate (`theorem3_gen`), and for every `f` (the paper assumes `f > 0`).
-/

namespace Podc.RecoverableHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

namespace Theorem3

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS] {R : ιR → ObjSpec}
  {n : ℕ}

/-- Is the operation a `tas`? -/
def isTas : RTASOp → Bool
  | .tas => true
  | .read => false

/-- The triggering operations of the repaired Assumption 1: `tas` on a test-and-set object. -/
def trigTAS : (i : ιR ⊕ ιS) → (withRW (ιS := ιS) R rtasObj i).Op → Bool
  | .inl _, _ => false
  | .inr _, o => isTas o

/-- The test-and-set objects. -/
def tasSet : Finset (ιR ⊕ ιS) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

lemma card_tasSet : (tasSet : Finset (ιR ⊕ ιS)).card = Fintype.card ιS := by
  simp [tasSet]

/-- The restricted model of (repaired) Assumption 1 for processes `a ≠ b`. -/
def restr (A : Alg n (withRW (ιS := ιS) R rtasObj)) (a b : Fin n) (hab : a ≠ b) : Restr A where
  a := a
  b := b
  hab := hab
  trig := trigTAS
  F := tasSet
  hF := by
    rintro (j | j) o h
    · simp [trigTAS] at h
    · simp [tasSet]

variable {A : Alg n (withRW (ιS := ιS) R rtasObj)} {a b : Fin n} {hab : a ≠ b}

/-- A test-and-set object holding `1` keeps holding `1`. -/
lemma stepP_mem_tas (C : Cfg A) (p : Fin n) (j : ιS) (h : C.mem (.inr j) = true) :
    (C.stepP p).mem (.inr j) = true := by
  rcases hact : A.act (C.loc p) with ⟨i, o, k⟩ | v
  · rw [stepP_mem_of_access _ hact]
    by_cases hi : Sum.inr j = i
    · subst hi
      simp only [Function.update_self]
      rw [h]
      change (rtasObj.δ true o).1 = true
      cases o <;> rfl
    · exact (Function.update_of_ne hi _ C.mem).trans h
  · rw [stepP_of_out _ (show C.Out p v from hact)]; exact h

/-- **Invariant**: every test-and-set object on which `a` has applied `tas` holds `1`. -/
lemma tasInv (x : Fin n → Bool) (σ : List Bool) (j : ιS)
    (hj : Sum.inr j ∈ ((restr A a b hab).S x σ).trg) :
    ((restr A a b hab).S x σ).c.mem (.inr j) = true := by
  set Rs := restr A a b hab
  suffices ∀ σ (s : RS A), (∀ j : ιS, Sum.inr j ∈ s.trg → s.c.mem (.inr j) = true) →
      ∀ j : ιS, Sum.inr j ∈ (Rs.rrun s σ).trg → (Rs.rrun s σ).c.mem (.inr j) = true from
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
          exact stepP_mem_tas _ _ _ (hs j hj)
        · simp only [hn, Finset.mem_insert] at hj ⊢
          rcases hj with rfl | hj
          · -- `a` just applied `tas` to `inr j`
            unfold Restr.newTrig at hn
            rcases hact : A.act (s.c.loc Rs.a) with ⟨i', o, k⟩ | v
            · rw [hact] at hn
              simp only at hn
              split_ifs at hn with hc
              cases hn
              rw [stepP_mem_of_access _ hact, Function.update_self]
              change RTASOp at o
              cases o
              · rfl
              · simp [Rs, restr, trigTAS, isTas] at hc
            · rw [hact] at hn; cases hn
          · exact stepP_mem_tas _ _ _ (hs j hj)
    · exact stepP_mem_tas _ _ _ (hs j hj)

/-- The core of the proof of Theorem 3: no algorithm with test-and-set objects and
read/write-like objects is correct on the restricted executions. -/
theorem not_rcorrect (hR : ∀ j, (R j).RWLike) : ¬ (restr A a b hab).RCorrect := by
  intro hC
  set Rs := restr A a b hab
  obtain ⟨σ, v, w, hc⟩ := Restr.exists_crit' hC
  set s := Rs.S Rs.x₀ σ with hs
  -- Subcase D-1 (crash): `a`'s next move is a crash
  by_cases hp : s.pend
  · exact hc.false_of_b_absorbs hC (Rs.absorb_b_of_pend s hp)
  simp only [Bool.not_eq_true] at hp
  rcases ha : A.act (s.c.loc Rs.a) with ⟨i, o, k⟩ | u
  swap
  · exact hc.not_out hC Rs.a u ha
  rcases hb : A.act (s.c.loc Rs.b) with ⟨j, o', k'⟩ | u
  swap
  · exact hc.not_out hC Rs.b u hb
  -- Case A: distinct objects
  by_cases hij : i = j
  swap
  · exact hc.false_of_commute hC (Rs.commute_of_ne hp ⟨o, k, ha⟩ ⟨o', k', hb⟩ hij)
  subst hij
  rcases i with r | r
  · -- a read/write-like object (Case D)
    have hR' : (withRW (ιS := ιS) R rtasObj (.inl r)).RWLike := hR r
    rcases (ObjSpec.rwLike_iff.1 hR') o with ho | ho
    · exact hc.false_of_b_absorbs hC (Rs.absorb_b_of_absorb hp ha hb (by rw [ho]))
    rcases (ObjSpec.rwLike_iff.1 hR') o' with ho' | ho'
    · exact hc.false_of_a_absorbs hC (Rs.absorb_a_of_absorb hp ha hb (by rw [ho']))
    · exact hc.false_of_b_absorbs hC (Rs.absorb_b_of_absorb hp ha hb (ho' _ _))
  · -- a readable test-and-set object
    change RTASOp at o o'
    cases o
    · cases o'
      · -- both `tas` (Cases B and C)
        cases hm : s.c.mem (.inr r)
        · -- Case B: the object holds `0`; `a`'s `tas` is its first one (`tasInv`)
          have hnot : Sum.inr r ∉ s.trg := fun h => by
            have := tasInv (hab := hab) Rs.x₀ σ r h
            rw [hm] at this; cases this
          have ht : Rs.newTrig s = some (.inr r) := by
            unfold Restr.newTrig; rw [ha]; simp [Rs, restr, trigTAS, isTas, hnot]
          have hag := Rs.hide_agA hp ha hb ht ∅ (Or.inr (by rw [hm]; rfl))
          refine hc.false_of_hide hC (S := ∅) ?_ (fun _ _ i hi => by simp at hi)
          rw [Rs.S_two, Rs.S_three]; exact hag
        · -- Case C: the object holds `1`; the two `tas` commute
          exact hc.false_of_commute hC
            (Rs.commute_of_commuteAt hp ha hb (by rw [hm]) (by rw [hm]; rfl)
              (by rw [hm]; rfl))
      · -- `b` reads (Subcase D-1)
        exact hc.false_of_a_absorbs hC (Rs.absorb_a_of_absorb hp ha hb rfl)
    · -- `a` reads (Subcase D-1)
      exact hc.false_of_b_absorbs hC (Rs.absorb_b_of_absorb hp ha hb rfl)

end Theorem3

open Theorem3

/-- **Theorem 3** (general form): for any `n` and two distinct processes `a`, `b`, no algorithm
using `|ιS|` readable test-and-set objects and any read/write-like objects satisfies the paper's
recoverable-consensus specification on any set of executions `Adm` that contains the executions
in which only `a` and `b` take steps, `b` never crashes, and `a` crashes at most `|ιS|` times
(once after its first `tas` on each object). -/
theorem theorem3_gen {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS]
    {R : ιR → ObjSpec} (hR : ∀ j, (R j).RWLike) {n : ℕ} (A : Alg n (withRW (ιS := ιS) R rtasObj))
    (a b : Fin n) (hab : a ≠ b) {Adm : List (Ev n) → Prop}
    (hAdm : ∀ x σ, Adm ((restr A a b hab).E x σ)) : ¬ SolvesP A Adm :=
  fun h => not_rcorrect hR (h.rcorrect _ hAdm)

/-- **Theorem 3.** For every `f`, there is no algorithm that uses at most `f` readable
test-and-set objects and any number of read/write registers (more generally, read/write-like
objects) and solves 2-process recoverable consensus with independent crash-recovery failures,
even if there are at most `f` failures. (The paper states it for `f > 0`.) -/
theorem theorem3 {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS]
    {R : ιR → ObjSpec} (hR : ∀ j, (R j).RWLike) (f : ℕ) (hf : Fintype.card ιS ≤ f)
    (A : Alg 2 (withRW (ιS := ιS) R rtasObj)) : ¬ SolvesP A (AtMost f) :=
  theorem3_gen hR A 0 1 (by decide) fun x σ =>
    Restr.atMost_E _ (by rw [show (restr A 0 1 _).F = tasSet from rfl, card_tasSet]; exact hf) x σ

/-- **Corollary 4.** A 2-process recoverable consensus algorithm (independent failures) from
readable test-and-set objects and read/write registers that tolerates executions with up to `f`
failures uses more than `f` test-and-set objects. -/
theorem corollary4 {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS]
    {R : ιR → ObjSpec} (hR : ∀ j, (R j).RWLike) (f : ℕ) (A : Alg 2 (withRW (ιS := ιS) R rtasObj))
    (hA : SolvesP A (AtMost f)) : f < Fintype.card ιS := by
  by_contra h
  exact theorem3 hR f (by omega) A hA

/-- Corollary 4 for CSLib's (stronger) specification `Solves`. -/
theorem corollary4' {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS]
    {R : ιR → ObjSpec} (hR : ∀ j, (R j).RWLike) (f : ℕ) (A : Alg 2 (withRW (ιS := ιS) R rtasObj))
    (hA : Solves A (AtMost f)) : f < Fintype.card ιS :=
  corollary4 hR f A (Solves.solvesP hA)

end Podc.RecoverableHierarchy
