import Papers.PODC2023.PPDoubleExpThresholds.ProgramToMachineDefs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# From population programs to population machines: the size bound

The machine of `ProgramToMachineDefs` has size at most `20 λ + 20`, where `λ = n + L + S` is the
size of the program (Proposition 14 of the paper claims `O(λ)`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.PPDoubleExpThresholds.ProgramToMachine

open Finset

variable {R P : Type} [Fintype R] [DecidableEq R] [DecidableEq P]

/-- `L`: the total code length of the program. -/
def codeLen (prog : Program R P) : ℕ := ∑ p ∈ prog.procs, (prog.code p).length

variable {prog : Program R P}

omit [Fintype R] in
theorem card_used_le : (used prog).card ≤ 1 + codeLen prog := by
  unfold used codeLen
  refine (card_insert_le prog.main _).trans ?_
  rw [add_comm]
  refine Nat.add_le_add_left (card_biUnion_le.trans (sum_le_sum fun p _ => ?_)) 1
  exact (List.toFinset_card_le ((prog.code p).filterMap callee)).trans (List.length_filterMap_le _ _)

omit [Fintype R] in
theorem sum_used_len_le (hwf : prog.WellFormed) :
    ∑ p ∈ used prog, (prog.code p).length ≤ codeLen prog :=
  sum_le_sum_of_subset (used_subset hwf)

omit [Fintype R] in
theorem off_le (p : P) (pc : ℕ) : off prog p pc ≤ 3 * pc := by
  unfold off
  calc ∑ i ∈ range (min pc (prog.code p).length), mlenAt prog p i
      ≤ ∑ i ∈ range (min pc (prog.code p).length), 3 := sum_le_sum fun i _ => by
        unfold mlenAt; cases (prog.code p)[i]? <;> simp [mlen_le_three]
    _ ≤ 3 * pc := by simp; omega

theorem length_helper [Nonempty R] : (helper prog).length = 8 * (Fintype.card R - 1) + 1 := by
  simp [helper, pairs, rest, Finset.card_erase_of_mem]; omega

theorem length_instrs_le [Nonempty R] (hwf : prog.WellFormed) :
    (instrs prog).length ≤ 4 * codeLen prog + 8 * Fintype.card R + 4 := by
  have h1 : (instrs prog).length = 3 + ∑ p ∈ used prog, blen prog p + (helper prog).length := by
    simp only [instrs, List.length_append, List.length_cons, List.length_nil, length_flatMap_block,
      usedList, Finset.sum_map_toList]
  have h2 : ∑ p ∈ used prog, blen prog p ≤ 3 * codeLen prog + (used prog).card := by
    calc ∑ p ∈ used prog, blen prog p ≤ ∑ p ∈ used prog, (3 * (prog.code p).length + 1) :=
          sum_le_sum fun p _ => by unfold blen; have := off_le (prog := prog) p (prog.code p).length; omega
      _ = 3 * ∑ p ∈ used prog, (prog.code p).length + (used prog).card := by
          simp only [sum_add_distrib, ← Finset.mul_sum, ← card_eq_sum_ones]
      _ ≤ _ := by have := sum_used_len_le hwf; omega
  have := card_used_le (prog := prog)
  rw [h1, length_helper]
  have : 0 < Fintype.card R := Fintype.card_pos
  omega

open Classical in
theorem card_cl [Nonempty R] (x : R) :
    (cl prog x).card = 1 + (univ.filter fun z => z ≠ x ∧ Relation.TransGen prog.SwapEdge x z).card := by
  have : cl prog x = insert x (univ.filter fun z => z ≠ x ∧ Relation.TransGen prog.SwapEdge x z) := by
    ext z; simp only [cl, mem_filter, mem_univ, true_and, mem_insert]; tauto
  rw [this, card_insert_of_notMem (by simp), add_comm]

open Classical in
theorem sum_card_cl [Nonempty R] : ∑ x, (cl prog x).card = Fintype.card R + prog.swapSize := by
  simp only [card_cl, sum_add_distrib, ← card_eq_sum_ones, card_univ]
  congr 1
  unfold Program.swapSize
  rw [Fintype.card_subtype, card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [card_filter]
  refine sum_congr rfl fun y _ => ?_
  simp only [ne_comm]

omit [Fintype R] in
theorem sum_card_sitesOf_le (hwf : prog.WellFormed) :
    ∑ q ∈ used prog, (sitesOf prog q).card ≤ codeLen prog := by
  calc ∑ q ∈ used prog, (sitesOf prog q).card
      ≤ ∑ q ∈ used prog, ∑ p ∈ used prog, ((range (prog.code p).length).filter
          fun pc => (prog.code p)[pc]?.bind callee = some q).card :=
        sum_le_sum fun q _ => card_biUnion_le.trans (sum_le_sum fun p _ => card_image_le)
    _ = ∑ p ∈ used prog, ∑ q ∈ used prog, ((range (prog.code p).length).filter
          fun pc => (prog.code p)[pc]?.bind callee = some q).card := sum_comm
    _ ≤ ∑ p ∈ used prog, (prog.code p).length := sum_le_sum fun p _ => by
        have := sum_card_fiberwise_eq_card_filter (range (prog.code p).length)
          ((used prog).map ⟨some, Option.some_injective _⟩)
          (fun pc => (prog.code p)[pc]?.bind callee)
        rw [sum_map] at this
        simp only [Function.Embedding.coeFn_mk] at this
        rw [this]
        exact (card_filter_le _ _).trans (by simp)
    _ ≤ codeLen prog := sum_used_len_le hwf

theorem card_retDom_le (q : P) : (retDom prog q).card ≤ 1 + (sitesOf prog q).card := by
  unfold retDom
  refine (card_insert_le _ _).trans ?_
  have := card_image_le (s := sitesOf prog q) (f := fun pp => (Val.nat (addr prog pp.1 pp.2 + 2) : Val R))
  omega

/-- The size bound (proof of Proposition 14, last paragraph). -/
theorem size_machine_le [Nonempty R] (hwf : prog.WellFormed) :
    (machine prog hwf).size ≤ 20 * prog.size + 20 := by
  have hsum : ∑ X, (dom prog X).card = 4 + (instrs prog).length + ∑ x, (cl prog x).card +
      (univ.image (Val.reg (Q := R))).card + ∑ q ∈ used prog, (retDom prog q).card := by
    rw [← Fintype.sum_equiv Ptr.equiv.symm _ _ (fun _ => rfl)]
    simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.univ_unit, sum_singleton]
    simp only [Ptr.equiv, Equiv.coe_fn_symm_mk, dom, card_map, Nat.card_Icc, card_image_of_injective _
      (fun _ _ h => Val.reg.inj h)]
    have hret : ∑ a : UP prog, (retDom prog a.1).card = ∑ q ∈ used prog, (retDom prog q).card := by
      convert sum_coe_sort (used prog) (fun q => (retDom prog q).card)
    simp only [show ({Val.bool false, Val.bool true} : Finset (Val R)).card = 2 by
      rw [card_pair (by simp)]]
    omega
  have hn : (univ.image (Val.reg (Q := R))).card ≤ Fintype.card R := card_image_le
  have hrd : ∑ q ∈ used prog, (retDom prog q).card ≤ (used prog).card + codeLen prog := by
    calc _ ≤ ∑ q ∈ used prog, (1 + (sitesOf prog q).card) := sum_le_sum fun q _ => card_retDom_le q
      _ = (used prog).card + ∑ q ∈ used prog, (sitesOf prog q).card := by
          simp only [sum_add_distrib, ← card_eq_sum_ones]
      _ ≤ _ := by have := sum_card_sitesOf_le hwf; omega
  have hI := length_instrs_le hwf
  have hU := card_used_le (prog := prog)
  have hcl := sum_card_cl (prog := prog)
  have hS : prog.size = Fintype.card R + codeLen prog + prog.swapSize := rfl
  have hP : Fintype.card (PtrT prog) = Fintype.card R + (used prog).card + 4 := by
    rw [Ptr.card, Fintype.card_coe]
  simp only [Machine.size, machine]
  rw [hsum, hP]
  omega

end Podc.PPDoubleExpThresholds.ProgramToMachine
