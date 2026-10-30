import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolRep
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The valid states `Q*`: closure under the transitions and the number of states

* `tr_closed`: transitions map valid states to valid states, hence also the broadcast protocol on
  `Q* × {true, false}` (`bcast_closed`).
* `card_U_le`: `|Q*| ≤ |Q| + 7 ∑_X |𝓕_X| + |I| + 3 ≤ 8 n` (the paper: `|Q*| ≤ |Q| + 7 ∑_X |𝓕_X| + L`;
  the `+ 3` accounts for the extra value `L + 1` of `IP`).
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-! ### Membership in `Q*` -/

theorem mem_U_reg (q : Q) : (St.reg q : St Q F) ∈ A.U := by
  simp [U]

theorem mem_U_ptr {X : F} {v : Val Q} {s : Stage} :
    (St.ptr X v s : St Q F) ∈ A.U ↔ v ∈ A.dom' X ∧ s ∈ A.stg X := by
  simp [U]

theorem mem_U_map {X : F} {i : ℕ} :
    (St.map X i : St Q F) ∈ A.U ↔ (1 ≤ i ∧ i ≤ A.instrs.length) ∧ A.asgTarget i = some X := by
  simp [U]

theorem none_mem_stg (X : F) : Stage.none ∈ A.stg X := by
  unfold stg; split_ifs <;> simp

theorem done_mem_stg {X : F} (hX : X ≠ A.IP) : Stage.done ∈ A.stg X := by
  unfold stg; split_ifs <;> simp_all

theorem stg_V (x : Q) {s : Stage} (hs : s ≠ .wait ∧ s ≠ .half) : s ∈ A.stg (A.V (some x)) := by
  unfold stg
  rw [if_neg (A.V_ne_IP _), if_pos ⟨x, rfl⟩]
  cases s <;> simp_all

theorem stg_IP {s : Stage} (hs : s = .none ∨ s = .wait ∨ s = .half) : s ∈ A.stg A.IP := by
  unfold stg; rw [if_pos rfl]; rcases hs with rfl | rfl | rfl <;> simp

theorem mem_dom'_of_dom {X : F} {v : Val Q} (h : v ∈ A.dom X) : v ∈ A.dom' X := by
  by_cases hX : X = A.IP
  · subst hX
    obtain ⟨j, rfl, h1, h2⟩ := A.exists_nat_of_mem_dom_IP h
    rw [A.mem_dom'_IP]; omega
  · rwa [A.dom'_of_ne hX]

theorem v0_mem_dom' (hdom : ∀ X, (A.dom X).Nonempty) (X : F) : A.v0 X ∈ A.dom' X :=
  A.mem_dom'_of_dom (A.v0_mem_dom hdom X)

theorem instr_mem {i : ℕ} {I : MInstr Q F} (h : A.instr i = some I) : I ∈ A.instrs :=
  List.mem_of_getElem? (by unfold instr at h; split_ifs at h; exact h)

theorem initS_mem_U (hdom : ∀ X, (A.dom X).Nonempty) : A.initS ∈ A.U :=
  A.mem_U_ptr.2 ⟨A.v0_mem_dom' hdom _, A.none_mem_stg _⟩

/-! ### Closure -/

/-- The transitions map valid states to valid states. -/
theorem tr_closed (hdom : ∀ X, (A.dom X).Nonempty) {t : Transition (St Q F)} (ht : A.Tr t)
    (hp : t.p ∈ A.U) (hq : t.q ∈ A.U) : t.p' ∈ A.U ∧ t.q' ∈ A.U := by
  have fresh : ∀ X, (St.ptr X (A.v0 X) .none : St Q F) ∈ A.U := fun X =>
    A.mem_U_ptr.2 ⟨A.v0_mem_dom' hdom X, A.none_mem_stg X⟩
  have ipv : ∀ {i : ℕ} {s s'}, (St.ptr A.IP (.nat i) s : St Q F) ∈ A.U →
      (s' = .none ∨ s' = .wait ∨ s' = .half) → (St.ptr A.IP (.nat i) s' : St Q F) ∈ A.U :=
    fun h hs => A.mem_U_ptr.2 ⟨(A.mem_U_ptr.1 h).1, A.stg_IP hs⟩
  have ipsucc : ∀ {i : ℕ} {I : MInstr Q F}, A.instr i = some I →
      (St.ptr A.IP (.nat (i + 1)) .none : St Q F) ∈ A.U := fun hI =>
    A.mem_U_ptr.2 ⟨by have := A.instr_some hI; rw [A.mem_dom'_IP]; omega, A.none_mem_stg _⟩
  have vx : ∀ {x : Q} {v : Val Q} {s : Stage}, v ∈ A.dom (A.V (some x)) →
      s ≠ .wait ∧ s ≠ .half → (St.ptr (A.V (some x)) v s : St Q F) ∈ A.U :=
    fun hv hs => A.mem_U_ptr.2 ⟨A.mem_dom'_of_dom hv, A.stg_V _ hs⟩
  have ptrv : ∀ {X : F} {v : Val Q}, v ∈ A.dom X → (St.ptr X v .none : St Q F) ∈ A.U :=
    fun hv => A.mem_U_ptr.2 ⟨A.mem_dom'_of_dom hv, A.none_mem_stg _⟩
  cases ht with
  | elect => exact ⟨fresh _, fresh _⟩
  | electIP => exact ⟨fresh _, A.mem_U_reg _⟩
  | mvStart hI hv => exact ⟨ipv hp (by simp), vx hv (by simp)⟩
  | mvEmit hI hv => exact ⟨vx hv (by simp), A.mem_U_reg _⟩
  | mvHalf hI hv => exact ⟨ipv hp (by simp), vx hv (by simp)⟩
  | mvTake hI hv => exact ⟨ipv hp (by simp), vx hv (by simp)⟩
  | mvPut hI hv => exact ⟨vx hv (by simp), A.mem_U_reg _⟩
  | mvEnd hI hv => exact ⟨ipsucc hI, vx hv (by simp)⟩
  | tsStart hI hv => exact ⟨ipv hp (by simp), vx hv (by simp)⟩
  | tsYes hI hv => exact ⟨vx hv (by simp), A.mem_U_reg _⟩
  | tsNo hI hv _ => exact ⟨vx hv (by simp), hq⟩
  | tsSet b hI hv =>
    refine ⟨vx hv (by simp), A.mem_U_ptr.2 ⟨?_, A.none_mem_stg _⟩⟩
    rw [A.dom'_of_ne A.CF_ne_IP, A.dom_CF]; cases b <;> simp
  | tsEnd hI hv => exact ⟨ipsucc hI, vx hv (by simp)⟩
  | asStart hI hXY hX hY =>
    refine ⟨ipv hp (by simp), A.mem_U_map.2 ⟨A.instr_some hI, ?_⟩⟩
    simp [asgTarget, hI]
  | asMap hI hXY hX hY hv =>
    refine ⟨A.mem_U_ptr.2 ⟨A.mem_dom'_of_dom (A.assign_mem _ _ _ (A.instr_mem hI) _ hv),
      A.done_mem_stg hX⟩, ptrv hv⟩
  | asEnd hI hXY hX hY hv => exact ⟨ipsucc hI, ptrv hv⟩
  | jmp hI hY hv =>
    exact ⟨ptrv (A.assign_mem _ _ _ (A.instr_mem hI) _ hv), ptrv hv⟩
  | asSelf hI hY hv =>
    exact ⟨ipsucc hI, ptrv (A.assign_mem _ _ _ (A.instr_mem hI) _ hv)⟩
  | asIP hI hX =>
    exact ⟨ipsucc hI, ptrv (A.assign_mem _ _ _ (A.instr_mem hI) _
      (A.mem_dom_IP.2 (A.instr_some hI)))⟩
  | jmpIP hI =>
    exact ⟨ptrv (A.assign_mem _ _ _ (A.instr_mem hI) _ (A.mem_dom_IP.2 (A.instr_some hI))), hq⟩

theorem bcast_closed (hdom : ∀ X, (A.dom X).Nonempty) : PProtocol.Closed A.bcastPP A.U' := by
  rintro t ⟨hδ, -⟩ hp hq
  simp only [U', Finset.mem_product, Finset.mem_univ, and_true] at hp hq ⊢
  rcases hδ with hδ | ⟨h1, h2⟩
  · exact A.tr_closed hdom hδ hp hq
  · exact ⟨h1 ▸ hp, h2 ▸ hq⟩

/-! ### Counting states -/

theorem card_stg_le (X : F) : (A.stg X).card ≤ 7 := by
  unfold stg; split_ifs <;> decide

theorem card_dom_IP : (A.dom A.IP).card = A.instrs.length := by
  rw [A.dom_IP, Finset.card_map, Nat.card_Icc]; omega

theorem card_dom'_IP : (A.dom' A.IP).card ≤ A.instrs.length + 1 := by
  unfold dom'; rw [if_pos rfl]
  exact Finset.card_image_le.trans (by rw [Nat.card_Icc]; omega)

theorem card_stg_IP : (A.stg A.IP).card = 3 := by
  unfold stg; rw [if_pos rfl]; decide

theorem card_U_le :
    A.U.card ≤ Fintype.card Q + 7 * ∑ X, (A.dom X).card + A.instrs.length + 3 := by
  unfold U
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : (Finset.univ.image (St.reg (F := F))).card ≤ Fintype.card Q :=
    Finset.card_image_le.trans (Finset.card_univ (α := Q)).le
  have h3 : (((Finset.univ ×ˢ Finset.Icc 1 A.instrs.length).filter
      (fun p => A.asgTarget p.2 = some p.1)).image (fun p => (St.map p.1 p.2 : St Q F))).card ≤
      A.instrs.length := by
    refine Finset.card_image_le.trans ?_
    refine (Finset.card_le_card_of_injOn (t := Finset.Icc 1 A.instrs.length) (fun p => p.2) ?_ ?_).trans
      (by rw [Nat.card_Icc]; omega)
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp
      exact hp.1
    · intro p hp p' hp' h
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp hp'
      simp only at h
      have : p.1 = p'.1 := by
        have := hp.2.symm.trans (h ▸ hp'.2); exact Option.some_injective _ this
      exact Prod.ext this h
  have h2 : (Finset.univ.biUnion (fun X => (A.dom' X ×ˢ A.stg X).image
      (fun p => (St.ptr X p.1 p.2 : St Q F)))).card ≤ 7 * ∑ X, (A.dom X).card + 3 := by
    refine Finset.card_biUnion_le.trans ?_
    have hX : ∀ X, ((A.dom' X ×ˢ A.stg X).image (fun p => (St.ptr X p.1 p.2 : St Q F))).card ≤
        7 * (A.dom X).card + (if X = A.IP then 3 else 0) := by
      intro X
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]
      by_cases hX : X = A.IP
      · subst hX
        rw [if_pos rfl, A.card_stg_IP, A.card_dom_IP]
        have := A.card_dom'_IP
        nlinarith
      · rw [if_neg hX, A.dom'_of_ne hX]
        have := A.card_stg_le X
        nlinarith
    refine (Finset.sum_le_sum (fun X _ => hX X)).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
    simp
  calc _ ≤ (Finset.univ.image (St.reg (F := F)) ∪ Finset.univ.biUnion (fun X =>
        (A.dom' X ×ˢ A.stg X).image (fun p => (St.ptr X p.1 p.2 : St Q F)))).card +
      (((Finset.univ ×ˢ Finset.Icc 1 A.instrs.length).filter
      (fun p => A.asgTarget p.2 = some p.1)).image (fun p => (St.map p.1 p.2 : St Q F))).card :=
        le_rfl
    _ ≤ _ := by
      have := Finset.card_union_le (Finset.univ.image (St.reg (F := F)))
        (Finset.univ.biUnion (fun X => (A.dom' X ×ˢ A.stg X).image
          (fun p => (St.ptr X p.1 p.2 : St Q F))))
      omega

theorem card_U_le_size : A.U.card ≤ 8 * A.size := by
  have := A.card_U_le
  have := A.card_F_pos
  unfold size
  omega

theorem card_U' : A.U'.card = 2 * A.U.card := by
  simp [U', Finset.card_product, mul_comm]

end Machine

end Podc.PPDoubleExpThresholds
