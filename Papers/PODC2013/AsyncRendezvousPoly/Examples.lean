import Papers.PODC2013.AsyncRendezvousPoly.Main

/-!
# Non-vacuity and the paper's length estimates

* `k2Explorer`: on the two-node graph `K₂`, `R(k, v) = (v, other node)` (one edge, `P ≡ 1`) is an
  exploration family; `idWalk` (`τ i = i`, unit speed) is a walk. So all hypotheses of
  `theorem_3_1_explicit` are satisfiable (`k2_meet`).
* `paperYstar`, `paperAstar`: the paper's estimates `Y*_k = 2P(k)·Q*_k` and `A*_k = 2P(k)·Z*_k`
  (proof of Theorem 3.1) are not upper bounds on `|Y(k)|`, `|A(k)|` in general: for `P ≡ 1`,
  `|Y(1)| = 10 > 6 = Y*_1` and `|A(1)| = 42 > 12 = A*_1` (`paper_Ystar_wrong`,
  `paper_Astar_wrong`). The paper forgets that `Y'(k)` inserts `P(k) + 1` copies of `Q(k)`
  (one at each of the `P(k) + 1` nodes of `R(k)`) plus `P(k)` edges. The theorem is unaffected:
  we use the exact lengths (`lenY`, `lenA`, `piBound`).
-/

namespace Podc.AsyncRendezvousPoly

open Traj

/-- The other node of `K₂`. -/
def other (v : Fin 2) : Fin 2 := if v = 0 then 1 else 0

/-- `R(k, v) = (v, other v)`: an exploration family on `K₂` with `P ≡ 1`. -/
def k2Explorer : Explorer (⊤ : SimpleGraph (Fin 2)) (fun _ => 1) where
  R _ v := ⟨1, fun i => if i = 0 then v else other v⟩
  len_eq _ _ := rfl
  start _ _ := rfl
  walk _ v i hi := by
    simp at hi; subst hi; fin_cases v <;> simp [other]
  covers _ v _ := fun u w huw => by
    refine ⟨0, by simp, ?_⟩
    have huw' : u ≠ w := huw.ne
    clear huw
    simp only [other, zero_add]
    revert u w v; decide
  P_pos _ := le_rfl

/-- The unit-speed walk `τ i = i`, `p t = t`. -/
noncomputable def idWalk : Walk where
  τ i := i
  p t := t
  τ_zero := by simp
  τ_mono := Nat.strictMono_cast
  p_τ _ := rfl
  p_mem _ _ ht := by simpa using ht
  cont _ := continuousOn_id

/-- Theorem 3.1 applies to agents with labels `1` and `2` on `K₂` (non-vacuity). -/
theorem k2_meet : ∃ t, Meet (k2Explorer.route (modLabel 1) 0) (k2Explorer.route (modLabel 2) 1)
    idWalk idWalk t :=
  (theorem_3_1_explicit (SimpleGraph.connected_top) (fun _ _ _ => le_rfl) k2Explorer
    (by norm_num) (by norm_num) (by norm_num) 0 1 idWalk idWalk).imp fun _ h => h.1

/-! ### The paper's estimates -/

section Estimates

variable (P : ℕ → ℕ)

/-- The paper's `X*_k = 2P(k) + 1`. -/
def paperXstar (k : ℕ) : ℕ := 2 * P k + 1
/-- The paper's `Q*_k = Σ_{i ≤ k} X*_i`. -/
def paperQstar (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, paperXstar P (i + 1)
/-- The paper's `Y*_k = 2P(k)·Q*_k`. -/
def paperYstar (k : ℕ) : ℕ := 2 * P k * paperQstar P k
/-- The paper's `Z*_k = Σ_{i ≤ k} Y*_i`. -/
def paperZstar (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, paperYstar P (i + 1)
/-- The paper's `A*_k = 2P(k)·Z*_k`. -/
def paperAstar (k : ℕ) : ℕ := 2 * P k * paperZstar P k

end Estimates

/-- The paper's bound `|Y(k, v)| ≤ Y*_k` fails: on `K₂` with `P ≡ 1`, `|Y(1, v)| = 10 > 6`. -/
theorem paper_Ystar_wrong :
    paperYstar (fun _ => 1) 1 = 6 ∧ (k2Explorer.Y 1 0).len = 10 := by
  refine ⟨by decide, ?_⟩
  rw [Explorer.Y_len]; decide

/-- The paper's bound `|A(k, v)| ≤ A*_k` fails: on `K₂` with `P ≡ 1`, `|A(1, v)| = 42 > 12`. -/
theorem paper_Astar_wrong :
    paperAstar (fun _ => 1) 1 = 12 ∧ (k2Explorer.A 1 0).len = 42 := by
  refine ⟨by decide, ?_⟩
  rw [Explorer.A_len]; decide

end Podc.AsyncRendezvousPoly
