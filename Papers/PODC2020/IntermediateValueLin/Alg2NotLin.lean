import Papers.PODC2020.IntermediateValueLin.BatchedCounter
import Mathlib.Tactic.FinCases

/-!
# Algorithm 2 is not linearizable

Rinberg–Keidar, Section 6.1: "This implementation is not linearizable because the reader may see a
later update and miss an earlier one, as illustrated in Figure 2." We give a concrete execution of
Algorithm 2 with three processes whose read result has no linearization.
-/

open Cslib.SharedMemory

namespace Podc.IntermediateValueLin.Alg2

instance (n : ℕ) (p : Fin n) (o : BCOp) : Decidable ((alg2 n).allowed p o) := isTrue trivial

/-- An execution in the style of Figure 2: process `2` reads `v[0] = 0`, then process `0` adds `1`,
then process `1` adds `2`, then process `2` reads `v[1] = 2` and `v[2] = 0` and returns `2`. -/
def badExec : List (Label (Fin 3) batchedCounter) :=
  [.inv 2 .read, .tau 2, .inv 0 (.update 1), .tau 0, .ret 0 0, .inv 1 (.update 2), .tau 1,
    .ret 1 0, .tau 2, .tau 2, .ret 2 2]

lemma badExec_valid : (alg2 3).Valid badExec := by
  apply Impl.valid_of_crun; decide +kernel

/-- The three entries of a linearization of `badExec`. -/
abbrev e₀ : OpId (Fin 3) × BCOp := ((0, 0), .update 1)
abbrev e₁ : OpId (Fin 3) × BCOp := ((1, 0), .update 2)
abbrev e₂ : OpId (Fin 3) × BCOp := ((2, 0), .read)

lemma opOf_badExec {x : OpId (Fin 3)} {o : BCOp} (h : opOf badExec x = some o) :
    (x, o) = e₀ ∨ (x, o) = e₁ ∨ (x, o) = e₂ := by
  obtain ⟨p, k⟩ := x
  have h0 : opsOf badExec 0 = [.update 1] := by decide
  have h1 : opsOf badExec 1 = [.update 2] := by decide
  have h2 : opsOf badExec 2 = [.read] := by decide
  fin_cases p <;> rcases k with _ | k <;> simp_all [opOf]

/-- The execution `badExec` of Algorithm 2 (three processes) has no linearization: the read
returns `2`, i.e. it sees the update of process `1` but not the earlier update of process `0`. -/
theorem badExec_not_linearizable : ¬ ∃ L, IsLinearization badExec L := by
  rintro ⟨L, hL⟩
  have hE : ∀ y ∈ L, y = e₀ ∨ y = e₁ ∨ y = e₂ := fun y hy => opOf_badExec (hL.op_eq y hy)
  have hin : ∀ e ∈ [e₀, e₁, e₂], e ∈ L := by
    intro e he
    have hc : Completed badExec e.1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl <;> (unfold Completed; decide)
    obtain ⟨y, hy, hye⟩ := List.mem_map.1 (hL.complete _ hc)
    have := hE y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rcases this with rfl | rfl | rfl <;> simp_all
  have hLnd : L.Nodup := List.Nodup.of_map _ hL.nodup
  have hperm : L.Perm [e₀, e₁, e₂] := by
    rw [List.perm_ext_iff_of_nodup hLnd (by decide)]
    intro y
    constructor
    · intro hy; rcases hE y hy with rfl | rfl | rfl <;> simp
    · intro hy; exact hin y hy
  have hprec : Precedes badExec ((0 : Fin 3), 0) ((1 : Fin 3), 0) :=
    ⟨badExec.take 5, badExec.drop 5, (List.take_append_drop _ _).symm, by unfold Completed; decide,
      by unfold Invoked; decide⟩
  have hrt := hL.realtime _ _ hprec (by
    obtain ⟨y, hy, hye⟩ := List.mem_map.1 (hL.complete ((1 : Fin 3), 0) (by unfold Completed; decide))
    exact List.mem_map.2 ⟨y, hy, hye⟩)
  have hresp : batchedCounter.respIn 0 L ((2 : Fin 3), 0) = some 2 :=
    hL.respIn_eq (r := 2) (by decide)
  have hlen := hperm.length_eq
  rcases L with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, _ | ⟨y₄, L⟩⟩⟩⟩ <;> simp at hlen
  have h₁ := hE y₁ (by simp)
  have h₂ := hE y₂ (by simp)
  have h₃ := hE y₃ (by simp)
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    rcases h₃ with rfl | rfl | rfl <;> revert hLnd hrt hresp <;> decide
/-- Section 6.1 (claim before Lemma 2, Figure 2): Algorithm 2 is not linearizable ("the reader may
see a later update and miss an earlier one"). Counterexample with three processes: `badExec`. -/
theorem alg2_not_linearizable : ¬ (alg2 3).Linearizable := by
  rintro ⟨h, hh⟩
  exact badExec_not_linearizable ⟨_, hh _ badExec_valid⟩

end Podc.IntermediateValueLin.Alg2
