import Papers.PODC2019.HardnessOptimization.MaxCutLemma

/-!
# Theorem 2.8: deterministic CONGEST lower bound for weighted max-cut

Bachrach et al., *Hardness of Distributed Optimization*, PODC 2019, Section 2.4.1.

The graphs `G_{x,y}` of `MaxCutGraph` form a family of lower-bound graphs (Definition 1.1):
* the communication network is the set of positive-weight pairs (`netGraph`);
* the input of node `v` is the weight function `W x y v : CV L → ℕ`, i.e. the weights of its
  incident edges (`0` for non-neighbours);
* `V_A = A₁ ∪ A₂ ∪ T_{A₁} ∪ F_{A₁} ∪ T_{A₂} ∪ F_{A₂} ∪ {C_A, N_A, C̄_A}` (`CV.alice`);
* the cut edges are the `4 log k` gadget-cycle edges `f_{A_z}^h t_{B_z}^h`, `t_{A_z}^h f_{B_z}^h`
  **and the edge `C̄_A C_B`** (the paper forgets the latter): `|E_cut| = 4 log k + 1`.

With Lemma 2.4 (`lemma_2_4`) and Theorem 1.1 (`LBFamily.not_disj_lowerBound`), every `T`-round
algorithm with `B`-bit messages deciding "there is a cut of weight `≥ M`" satisfies
`k² ≤ T · 2 · (4 log k + 1) · B + 2`, i.e. `T = Ω(k² / (B log k)) = Ω(n² / log² n)` for
`B = Θ(log n)`, `n = 4k + 8 log k + 5`.
-/

namespace HardnessOptimization

namespace MaxCut

open Podc.CongestLB

variable {L : ℕ}

/-- Alice's part `V_A` of the vertex partition. -/
def CV.alice : CV L → Bool
  | .row s _ _ => !s
  | .gad s _ _ _ => !s
  | .cc s => !s
  | .nn s => !s
  | .cbar => true

/-- The communication network of `G_{x,y}`: the pairs joined by an edge of positive weight. -/
def netGraph (x y : Idx L → Idx L → Bool) : SimpleGraph (CV L) where
  Adj u v := u ≠ v ∧ 0 < W x y u v
  symm := ⟨fun u v h => ⟨h.1.symm, W_comm x y u v ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (x y : Idx L → Idx L → Bool) : DecidableRel (netGraph x y).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ 0 < W x y u v))

/-- The cut edges `(a, b)`, `a ∈ V_A`, `b ∈ V_B`: the gadget-cycle edges between `A` and `B`, and
`C̄_A C_B`. -/
def Ecut : Finset (CV L × CV L) :=
  insert (.cbar, .cc true) ((Finset.univ : Finset (Bool × Fin L × Bool)).image
    fun p => (.gad false p.1 p.2.1 p.2.2, .gad true p.1 p.2.1 (!p.2.2)))

lemma card_Ecut_le : (Ecut : Finset (CV L × CV L)).card ≤ 4 * L + 1 := by
  unfold Ecut
  refine (Finset.card_insert_le _ _).trans ?_
  have := Finset.card_image_le (s := (Finset.univ : Finset (Bool × Fin L × Bool)))
    (f := fun p => ((.gad false p.1 p.2.1 p.2.2 : CV L), (.gad true p.1 p.2.1 (!p.2.2) : CV L)))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at this
  omega

/-- Edges with an endpoint in `V_A` do not depend on `y`. -/
lemma wt_alice (x y y' : Idx L → Idx L → Bool) (e : CE L)
    (he : e.src.alice = true ∨ e.dst.alice = true) : wt x y e = wt x y' e := by
  cases e with
  | cyc s z h t => rfl
  | rn s z j => cases s <;> cases z <;> simp_all [CE.src, CE.dst, CV.alice, wt, xy]
  | inp s i j => cases s <;> simp_all [CE.src, CE.dst, CV.alice, wt, xy]
  | _ => rfl

/-- Edges with an endpoint in `V_B` do not depend on `x`. -/
lemma wt_bob (x x' y : Idx L → Idx L → Bool) (e : CE L)
    (he : e.src.alice = false ∨ e.dst.alice = false) : wt x y e = wt x' y e := by
  cases e with
  | cyc s z h t => rfl
  | rn s z j => cases s <;> cases z <;> simp_all [CE.src, CE.dst, CV.alice, wt, xy]
  | inp s i j => cases s <;> simp_all [CE.src, CE.dst, CV.alice, wt, xy]
  | _ => rfl

lemma W_alice (x y y' : Idx L → Idx L → Bool) (u v : CV L) (hu : u.alice = true) :
    W x y u v = W x y' u v := by
  unfold W
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with h
  · apply wt_alice
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl (h1 ▸ hu)
    · exact Or.inr (h2 ▸ hu)
  · rfl

lemma W_bob (x x' y : Idx L → Idx L → Bool) (u v : CV L) (hu : u.alice = false) :
    W x y u v = W x' y u v := by
  unfold W
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with h
  · apply wt_bob
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl (h1 ▸ hu)
    · exact Or.inr (h2 ▸ hu)
  · rfl

lemma W_cross (x x' y y' : Idx L → Idx L → Bool) (a b : CV L) (ha : a.alice = true)
    (hb : b.alice = false) : W x y a b = W x' y' a b := by
  rw [W_alice x y y' a b ha, W_comm, W_bob x x' y' b a hb, W_comm]

lemma mem_Ecut_of_W (x y : Idx L → Idx L → Bool) (a b : CV L) (ha : a.alice = true)
    (hb : b.alice = false) (h : 0 < W x y a b) : (a, b) ∈ Ecut := by
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  split_ifs at he with hab
  · rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases e with
      | cyc s z h t => cases s <;> cases t <;> simp_all [CE.src, CE.dst, CV.alice, Ecut]
      | _ => simp_all [CE.src, CE.dst, CV.alice]
    · cases e with
      | cyc s z h t => cases s <;> cases t <;> simp_all [CE.src, CE.dst, CV.alice, Ecut]
      | _ => simp_all [CE.src, CE.dst, CV.alice, Ecut]
  · exact absurd rfl he

/-- Curried view of a `k²`-bit string. -/
def cur (x : Idx L × Idx L → Bool) : Idx L → Idx L → Bool := fun i j => x (i, j)

/-- **The family of lower-bound graphs for weighted max-cut** (Section 2.4.1), indexed by
`x, y ∈ {0,1}^{k²}`. -/
def family (L : ℕ) :
    LBFamily (Idx L × Idx L → Bool) (Idx L × Idx L → Bool) (CV L) (CV L → ℕ) where
  G x y := netGraph (cur x) (cur y)
  inp x y v := W (cur x) (cur y) v
  alice := CV.alice
  Ecut := Ecut
  Ecut_sub p hp := by
    simp only [Ecut, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hp
    rcases hp with rfl | ⟨q, rfl⟩ <;> simp [CV.alice]
  adj_cut x y a b ha hb h := mem_Ecut_of_W _ _ a b ha hb h.2
  adj_alice x y y' a b ha _ := by
    simp only [netGraph, W_alice (cur x) (cur y) (cur y') a b ha]
  adj_bob x x' y a b ha _ := by
    simp only [netGraph, W_bob (cur x) (cur x') (cur y) a b ha]
  adj_fixed x x' y y' a b ha hb := by
    simp only [netGraph, W_cross (cur x) (cur x') (cur y) (cur y') a b ha hb]
  inp_alice x y y' v hv := funext fun u => W_alice _ _ _ v u hv
  inp_bob x x' y v hv := funext fun u => W_bob _ _ _ v u hv

instance (x y : Idx L × Idx L → Bool) : DecidableRel ((family L).G x y).Adj :=
  inferInstanceAs (DecidableRel (netGraph (cur x) (cur y)).Adj)

/-- **Theorem 2.8 (deterministic, decision version).** Let `k = 2 ^ L ≥ 2`. If a deterministic
CONGEST algorithm with `B`-bit messages, run on `G_{x,y}` (each node knowing the weights of its
incident edges), accepts within `T` rounds exactly when `G_{x,y}` has a cut of weight `≥ M`, then
`k² ≤ T · 2 · ((4 log k + 1) · B) + 2`. Since `n = 4k + 8 log k + 5`, this is
`T = Ω(n² / (B log n))`, i.e. `Ω(n² / log² n)` for `B = Θ(log n)`. -/
theorem theorem_2_8 (hL : 1 ≤ L) {σ : Type*} {B : ℕ} (A : Algorithm (CV L) (CV L → ℕ) σ B)
    (T : ℕ)
    (hA : ∀ x y : Idx L → Idx L → Bool,
      A.Accepts (netGraph x y) (W x y) T ↔ ∃ S : Finset (CV L), M L ≤ cutWeight x y S) :
    4 ^ L ≤ T * (2 * ((4 * L + 1) * B)) + 2 := by
  have h := (family L).not_disj_lowerBound A T fun x y => by
    change A.Accepts (netGraph (cur x) (cur y)) (W (cur x) (cur y)) T ↔ _
    rw [hA, lemma_2_4 hL]
    simp [Protocol.disj, cur]
  have hc : Fintype.card (Idx L × Idx L) = 4 ^ L := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← mul_pow]; norm_num
  rw [hc] at h
  refine h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right _ card_Ecut_le))) _)

end MaxCut

end HardnessOptimization
