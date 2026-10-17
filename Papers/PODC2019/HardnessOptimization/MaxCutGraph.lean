import Papers.PODC2019.HardnessOptimization.MDSGraph

/-!
# The lower-bound graphs for weighted max-cut (Section 2.4.1)

Bachrach, Censor-Hillel, Dory, Efron, Leitersdorf, Paz. *Hardness of Distributed Optimization.*
PODC 2019 (arXiv:1905.10284), Section 2.4.1.

`k = 2 ^ L`, a row index `j ∈ [k]` is a bit string `j : Idx L = Fin L → Bool`.

Vertices (`CV L`), with `s = false` for the `A` side and `s = true` for the `B` side, and
`z = false` for the first row (`A₁`, `B₁`), `z = true` for the second (`A₂`, `B₂`):
* `row s z j`: `a^j_1, a^j_2, b^j_1, b^j_2`;
* `gad s z h t`: `t^h_S` (`t = true`) and `f^h_S` (`t = false`) for `S = A_z / B_z`;
* `cc s`: `C_A`, `C_B`; `nn s`: `N_A`, `N_B`; `cbar`: `C̄_A`.

Edges (`CE L`, each undirected edge listed once, from `src` to `dst`), with weights `wt x y`:
* `cn s`: `C_s – N_s`, `cbar s`: `C_s – C̄_A`, weight `k⁴`;
* `cyc s z h t`: the 4-cycle `t_{A_z}^h – f_{A_z}^h – t_{B_z}^h – f_{B_z}^h – t_{A_z}^h`,
  weight `k⁴` (`cyc s z h true = t_S – f_S`, `cyc s z h false = f_S – t_{S'}`, `S'` the other side);
* `bin s z j h`: `row s z j – (t^h if j_h = 1 else f^h)` (i.e. `Bin(s^j)`), weight `2k²`;
* `rc s z j`: `row – C_s`, weight `2k² log k − k²`;
* `rn s z j`: `row – N_s`, weight `Σ_j x_{i,j}` (first row) resp. `Σ_j x_{j,i}` (second row)
  (`y` on the `B` side);
* `inp s i j`: `row s false i – row s true j`, weight `1` if `x_{i,j} = 0` (resp. `y`), else `0`.

The weighted graph is the symmetric weight function `W x y : CV L → CV L → ℕ` (`0` = no edge).
Edges of weight `0` (input edges with `x_{i,j} = 1`, and `N`-edges with zero row sum) are thus
absent; this is immaterial for cut weights.
-/

namespace HardnessOptimization

namespace MaxCut

/-- Vertices of the max-cut lower-bound graph. -/
inductive CV (L : ℕ) where
  | row (s z : Bool) (j : Idx L)
  | gad (s z : Bool) (h : Fin L) (t : Bool)
  | cc (s : Bool)
  | nn (s : Bool)
  | cbar
  deriving DecidableEq, Fintype

/-- Edges of the max-cut lower-bound graph (each listed once). -/
inductive CE (L : ℕ) where
  | cn (s : Bool)
  | cbar (s : Bool)
  | cyc (s z : Bool) (h : Fin L) (t : Bool)
  | bin (s z : Bool) (j : Idx L) (h : Fin L)
  | rc (s z : Bool) (j : Idx L)
  | rn (s z : Bool) (j : Idx L)
  | inp (s : Bool) (i j : Idx L)
  deriving DecidableEq, Fintype

variable {L : ℕ}

namespace CE

/-- First endpoint of an edge. -/
def src : CE L → CV L
  | cn s => .cc s
  | cbar s => .cc s
  | cyc s z h t => .gad s z h t
  | bin s z j _ => .row s z j
  | rc s z j => .row s z j
  | rn s z j => .row s z j
  | inp s i _ => .row s false i

/-- Second endpoint of an edge. -/
def dst : CE L → CV L
  | cn s => .nn s
  | cbar _ => .cbar
  | cyc s z h true => .gad s z h false
  | cyc s z h false => .gad (!s) z h true
  | bin s z j h => .gad s z h (j h)
  | rc s _ _ => .cc s
  | rn s _ _ => .nn s
  | inp s _ j => .row s true j

lemma src_ne_dst (e : CE L) : e.src ≠ e.dst := by
  cases e with
  | cyc s z h t => cases t <;> cases s <;> simp [src, dst]
  | _ => simp [src, dst]

end CE

/-- Row sum `Σ_j m_{i,j}`. -/
def rsum (m : Idx L → Idx L → Bool) (i : Idx L) : ℕ := ∑ j, (m i j).toNat

/-- Column sum `Σ_i m_{i,j}`. -/
def csum (m : Idx L → Idx L → Bool) (j : Idx L) : ℕ := ∑ i, (m i j).toNat

/-- Edge weights; `k = 2 ^ L`. -/
def wt (x y : Idx L → Idx L → Bool) : CE L → ℕ
  | .cn _ => (2 ^ L) ^ 4
  | .cbar _ => (2 ^ L) ^ 4
  | .cyc .. => (2 ^ L) ^ 4
  | .bin .. => 2 * (2 ^ L) ^ 2
  | .rc .. => 2 * (2 ^ L) ^ 2 * L - (2 ^ L) ^ 2
  | .rn s false i => rsum (xy x y s) i
  | .rn s true j => csum (xy x y s) j
  | .inp s i j => (!xy x y s i j).toNat

/-- The weighted graph `G_{x,y}` as a symmetric weight function (`0` = no edge). -/
def W (x y : Idx L → Idx L → Bool) (u v : CV L) : ℕ :=
  ∑ e : CE L, if (e.src = u ∧ e.dst = v) ∨ (e.src = v ∧ e.dst = u) then wt x y e else 0

lemma W_comm (x y : Idx L → Idx L → Bool) (u v : CV L) : W x y u v = W x y v u := by
  unfold W
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [or_comm]

/-- The weight of the cut `E(S, V \ S)`. -/
def cutWeight (x y : Idx L → Idx L → Bool) (S : Finset (CV L)) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, W x y u v

/-- The threshold `M = k⁴ (8 log k + 4) + k³ (12 log k − 4) + 4k² + 4k`. -/
def M (L : ℕ) : ℕ :=
  (2 ^ L) ^ 4 * (8 * L + 4) + (2 ^ L) ^ 3 * (12 * L - 4) + 4 * (2 ^ L) ^ 2 + 4 * 2 ^ L

/-- Contribution of edge `e` to the cut given by the 2-colouring `σ`. -/
def ec (x y : Idx L → Idx L → Bool) (σ : CV L → Bool) (e : CE L) : ℕ :=
  if σ e.src = σ e.dst then 0 else wt x y e

/-- Weight of the cut given by a 2-colouring. -/
def cutσ (x y : Idx L → Idx L → Bool) (σ : CV L → Bool) : ℕ := ∑ e, ec x y σ e

private lemma double_sum_pair {V : Type*} [DecidableEq V] [Fintype V] (S : Finset V) (a b : V)
    (hab : a ≠ b) (w : ℕ) :
    ∑ u ∈ S, ∑ v ∈ Sᶜ, (if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then w else 0) =
      if decide (a ∈ S) = decide (b ∈ S) then 0 else w := by
  have h1 : ∀ u v, (if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then w else 0) =
      (if a = u then (if b = v then w else 0) else 0) +
        (if b = u then (if a = v then w else 0) else 0) := by
    intro u v
    by_cases hu : a = u <;> by_cases hv : b = v <;> by_cases hu' : b = u <;>
      by_cases hv' : a = v <;> simp_all
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

lemma cutWeight_eq (x y : Idx L → Idx L → Bool) (S : Finset (CV L)) :
    cutWeight x y S = cutσ x y (fun v => decide (v ∈ S)) := by
  unfold cutWeight W cutσ ec
  calc _ = ∑ u ∈ S, ∑ e : CE L, ∑ v ∈ Sᶜ,
        (if (e.src = u ∧ e.dst = v) ∨ (e.src = v ∧ e.dst = u) then wt x y e else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun e _ => double_sum_pair S _ _ e.src_ne_dst _

/-- Splitting a sum over the edges by edge kind. -/
lemma sum_CE {β : Type*} [AddCommMonoid β] (f : CE L → β) :
    ∑ e, f e = (∑ s, f (.cn s)) + (∑ s, f (.cbar s)) + (∑ s, ∑ z, ∑ h, ∑ t, f (.cyc s z h t)) +
      (∑ s, ∑ z, ∑ j, ∑ h, f (.bin s z j h)) + (∑ s, ∑ z, ∑ j, f (.rc s z j)) +
      (∑ s, ∑ z, ∑ j, f (.rn s z j)) + (∑ s, ∑ i, ∑ j, f (.inp s i j)) := by
  let e : CE L ≃ Bool ⊕ Bool ⊕ (Bool × Bool × Fin L × Bool) ⊕ (Bool × Bool × Idx L × Fin L) ⊕
      (Bool × Bool × Idx L) ⊕ (Bool × Bool × Idx L) ⊕ (Bool × Idx L × Idx L) :=
    { toFun := fun
        | .cn s => .inl s
        | .cbar s => .inr (.inl s)
        | .cyc s z h t => .inr (.inr (.inl (s, z, h, t)))
        | .bin s z j h => .inr (.inr (.inr (.inl (s, z, j, h))))
        | .rc s z j => .inr (.inr (.inr (.inr (.inl (s, z, j)))))
        | .rn s z j => .inr (.inr (.inr (.inr (.inr (.inl (s, z, j))))))
        | .inp s i j => .inr (.inr (.inr (.inr (.inr (.inr (s, i, j))))))
      invFun := fun
        | .inl s => .cn s
        | .inr (.inl s) => .cbar s
        | .inr (.inr (.inl (s, z, h, t))) => .cyc s z h t
        | .inr (.inr (.inr (.inl (s, z, j, h)))) => .bin s z j h
        | .inr (.inr (.inr (.inr (.inl (s, z, j))))) => .rc s z j
        | .inr (.inr (.inr (.inr (.inr (.inl (s, z, j)))))) => .rn s z j
        | .inr (.inr (.inr (.inr (.inr (.inr (s, i, j)))))) => .inp s i j
      left_inv := fun e => by cases e <;> rfl
      right_inv := fun p => by
        rcases p with s | s | ⟨s, z, h, t⟩ | ⟨s, z, j, h⟩ | ⟨s, z, j⟩ | ⟨s, z, j⟩ | ⟨s, i, j⟩ <;>
          rfl }
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, add_assoc]
  rfl

end MaxCut

end HardnessOptimization
