import Papers.PODC2020.TightBipartiteMatching.LowerBound

/-!
# The degenerate case `y = Δ`

Theorem 1.2 and the final claim of §6 ("for any combination of integers `x ≥ 0, y ≥ 1, Δ ≥ 2`,
our bound of `T_Δ(x, y)` is truly tight") do not exclude `y = Δ`. But for `y = Δ` putting every
edge into the matching is a valid `x`-maximal `Δ`-matching, so the problem is 0-round solvable,
while `T_Δ(x, Δ) = 1` for every `x < Δ`. (The paper notes the trivial 0-round algorithm after
Theorem 4.5 and in §5, but Theorem 1.2 and §6 still claim tightness.)
-/

namespace TightBipartiteMatching

open Lab

variable {d : ℕ}

theorem replicate_mem_gen_M (n : ℕ) (S S' : Set Lab) (hS : M ∈ S) :
    Multiset.replicate (n + 1) M ∈ Cond.Gen [(S, n), ({M}, 1), (S', 0)] := by
  refine Cond.gen_cons.2 ⟨Multiset.replicate n M, {M}, ?_, by simp, fun x hx => ?_, ?_⟩
  · rw [Multiset.replicate_succ, ← Multiset.singleton_add, add_comm]
  · rw [Multiset.eq_of_mem_replicate hx]; exact hS
  · exact Cond.gen_cons.2 ⟨{M}, 0, by simp, by simp, by simp, Cond.gen_cons.2
      ⟨0, 0, by simp, by simp, by simp, by simp⟩⟩

theorem mset_const_M : mset (fun _ : Fin (d + 1) => M) = Multiset.replicate (d + 1) M := by
  simp [mset, Multiset.map_const']

/-- For `y = Δ`, bipartite `x`-maximal `y`-matching is solvable in 0 rounds (every white node
outputs `M` on all ports). -/
theorem phi_full_zero (x : ℕ) : (Phi d x (d + 1)).WhiteIn d 0 := by
  refine ⟨fun _ _ => M, ?_⟩
  rw [solves_zero_iff]
  refine ⟨?_, fun j => ?_⟩
  · rw [mset_const_M]
    refine ⟨_, List.mem_cons_self .., ?_⟩
    simpa using replicate_mem_gen_M d {M, O, X} {O, X} (by simp)
  · rw [mset_const_M]
    refine ⟨_, List.mem_cons_self .., ?_⟩
    simpa using replicate_mem_gen_M d {M, P, O, X} {P, O, X} (by simp)

theorem tval_full {x : ℕ} (hx : x ≤ d) : Tval (d + 1) x (d + 1) = 1 := by
  have h1 : (d + 1 - x) ⌈/⌉ (d + 1) = 1 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.div_eq_iff (by omega)]; omega
  have h2 : (d + 1) ⌈/⌉ (d + 1) = 1 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.div_eq_iff (by omega)]; omega
  simp [Tval, h1, h2]

/-- **Counterexample to Theorem 1.2 for `y = Δ`.** For every `Δ ≥ 1` and `x < Δ`,
`T_Δ(x, Δ) = 1`, yet bipartite `x`-maximal `Δ`-matching has a white 0-round algorithm. -/
theorem theorem_1_2_false_y_eq_Δ {x : ℕ} (hx : x ≤ d) :
    Tval (d + 1) x (d + 1) = 1 ∧ (Phi d x (d + 1)).WhiteIn d 0 :=
  ⟨tval_full hx, phi_full_zero x⟩

end TightBipartiteMatching
