import Papers.PODC2019.HubLabelingHardness.Main

/-!
# The claim `d_G(u, v) = d_H(u, v)` in the proof of Lemma 2.2 is false

The proof of Lemma 2.2 asserts: "for any `u ∈ V_i` and `v ∈ V_j` with `i < j`, we have
`dist_G(u, v) = dist_H(u, v)`", justified "from the construction of `G_{b,ℓ}` for `j = i + 1`".
This fails for non-adjacent `u ∈ V_0`, `v ∈ V_1`: in `G` a walk may enter the in-tree of an upper
vertex through one leaf and leave it through another leaf *without visiting that vertex*, saving up to
`2b + 2 - 2` steps compared with the corresponding `H`-walk, which has to pass through the vertex.

Concretely, `b = 1`, `ℓ = 2` (so `s = 2`, `A = 24`), `u = v_{0,(0,0)}`, `v = v_{1,(0,1)}`:
* every `H`-walk from `u` to `v` has weight `≥ 3A + 1 = 73` (`le_wlen_cex`; it needs `≥ 3` edges by
  parity and some edge changes coordinate 2);
* `G` has a walk of length `71 = 3A - 1`: `u → v_{1,(0,0)} → v_{2,(0,1)}`'s in-tree (leaf `0`, root, leaf
  `1`) `→ v_{1,(0,1)}`, turning around inside the in-tree of `v_{2,(0,1)}` (`edist_cex_le`).

Only the special case used later (`u = v_{0,x}`, `v = v_{2ℓ,z}`) is needed for Theorem 2.1, and it holds
(`lemma_2_2_G`).
-/

namespace Podc.HubLabelingHardness

open SimpleGraph Finset GV

variable {b ℓ : ℕ}

/-! ## Lower bound on `H`-walks -/

lemma level_parity {u v : Main b ℓ} (q : (H b ℓ).Walk u v) :
    (q.length + u.1.val + v.1.val) % 2 = 0 := by
  induction q with
  | nil => simp only [Walk.length_nil]; omega
  | cons h q ih =>
    simp only [Walk.length_cons]
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

lemma hw_ge {u v : Main b ℓ} : bigA b ℓ + (if u.2 = v.2 then 0 else 1) ≤ hw b ℓ u v := by
  unfold hw
  split_ifs with h
  · simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    have : 1 ≤ sqd (u.2 k) (v.2 k) := by
      have : ((u.2 k : ℕ) : ℤ) ≠ (v.2 k : ℕ) := by
        intro h'; exact hk (Fin.ext (by exact_mod_cast h'))
      have : (1 : ℤ) ≤ ((sqd (u.2 k) (v.2 k) : ℕ) : ℤ) := by
        rw [sqd_cast]
        rcases lt_or_gt_of_ne this with h | h <;> nlinarith
      exact_mod_cast this
    have := Finset.single_le_sum (f := fun k => sqd (u.2 k) (v.2 k)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    omega

lemma wlen_ge {u v : Main b ℓ} (q : (H b ℓ).Walk u v) :
    bigA b ℓ * q.length + (if u.2 = v.2 then 0 else 1) ≤ wlen q := by
  induction q with
  | nil => simp
  | @cons u v w h q ih =>
    have := hw_ge (u := u) (v := v)
    simp only [Walk.length_cons, wlen_cons]
    split_ifs at * <;> simp_all <;> nlinarith

/-! ## The instance `b = 1`, `ℓ = 2` -/

/-- `(0, 0)`. -/
def jA : Vec 1 2 := ![0, 0]
/-- `(0, 1)`. -/
def jB : Vec 1 2 := ![0, 1]

/-- In `H_{1,2}`, every walk from `v_{0,(0,0)}` to `v_{1,(0,1)}` has weight `≥ 73 = 3A + 1`. -/
theorem le_wlen_cex (q : (H 1 2).Walk (0, jA) (1, jB)) : 73 ≤ wlen q := by
  have hpar := level_parity q
  have hge := wlen_ge q
  have hA : bigA 1 2 = 24 := by decide
  have hne : jA ≠ jB := by decide
  rw [hA] at hge
  simp only [hne, ite_false] at hge
  simp only [Fin.val_zero, Fin.val_one] at hpar
  have h1 : q.length ≠ 1 := by
    intro h1
    obtain ⟨hadj, -⟩ : (H 1 2).Adj (0, jA) (1, jB) ∧ True := by
      cases q with
      | cons h q =>
        simp only [Walk.length_cons] at h1
        have : q.length = 0 := by omega
        have := Walk.eq_of_length_eq_zero this
        subst this
        exact ⟨h, trivial⟩
    rcases hadj with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd (h 1 (by decide)) (by decide)
    · simp at h
  omega

lemma wdist_cex : (73 : ENNReal) ≤ (H 1 2).wdist (fun e => (hwS 1 2 e : NNReal)) (0, jA) (1, jB) := by
  refine le_iInf fun q => ?_
  rw [← wlen_eq_wlength]
  exact_mod_cast le_wlen_cex q

lemma tri {V : Type*} {G' : SimpleGraph V} {a c d : V} {x y : ℕ∞} (h1 : G'.edist a c ≤ x)
    (h2 : G'.edist c d ≤ y) : G'.edist a d ≤ x + y :=
  (SimpleGraph.edist_triangle).trans (add_le_add h1 h2)

lemma plen_A : plen 1 2 1 jA 1 = 21 := by decide
lemma plen_B : plen 1 2 1 jB 1 = 20 := by decide

/-- In `G_{1,2}`, `d(v_{0,(0,0)}, v_{1,(0,1)}) ≤ 71 = 3A - 1`. -/
theorem edist_cex_le : (G 1 2).edist (main 0 jA) (main 1 jB) ≤ 71 := by
  have e1 : (G 1 2).edist (main 0 jA) (main 1 jA) ≤ 24 := by
    have := edist_up_le (b := 1) (ℓ := 2) le_rfl (by norm_num) 0 jA 0
    have h1 : Function.update jA (cc (0 : Fin (2 * 2))) 0 = jA := by decide
    rw [h1] at this
    exact this.trans (by decide)
  have e2 := edist_le_one_of_E (E.outRoot (b := 1) (ℓ := 2) 1 jA)
  have e3 := edist_tout_root_le (b := 1) (ℓ := 2) 1 jA (leaf 1)
  rw [dep_leaf] at e3
  have e4 := edist_le_one_of_E (E.pathStart (b := 1) (ℓ := 2) 1 jA 1 ⟨0, by rw [plen_A]; norm_num⟩ rfl)
  have e5 := edist_mid_le (b := 1) (ℓ := 2) 1 jA 1 ⟨0, by rw [plen_A]; norm_num⟩
    ⟨19, by rw [plen_A]; norm_num⟩ (by simp)
  have e6 := edist_le_one_of_E (E.pathEnd (b := 1) (ℓ := 2) 1 jA 1 ⟨19, by rw [plen_A]; norm_num⟩
    (by show (19 : ℕ) + 2 = _; rw [plen_A]))
  have h6 : Function.update jA (cc (1 : Fin (2 * 2))) 1 = jB := by decide
  have h6' : jA (cc (1 : Fin (2 * 2))) = 0 := by decide
  rw [h6, h6'] at e6
  have e7 := edist_le_one_of_E (E.inChild (b := 1) (ℓ := 2) 1 jB (root 1) (leaf 0) (by decide))
  rw [SimpleGraph.edist_comm] at e7
  have e8 := edist_le_one_of_E (E.inChild (b := 1) (ℓ := 2) 1 jB (root 1) (leaf 1) (by decide))
  have e9 := edist_le_one_of_E (E.pathEnd (b := 1) (ℓ := 2) 1 jB 1 ⟨18, by rw [plen_B]; norm_num⟩
    (by show (18 : ℕ) + 2 = _; rw [plen_B]))
  have h9 : Function.update jB (cc (1 : Fin (2 * 2))) 1 = jB := by decide
  have h9' : jB (cc (1 : Fin (2 * 2))) = 1 := by decide
  rw [h9, h9', SimpleGraph.edist_comm] at e9
  have e10 := edist_mid_le (b := 1) (ℓ := 2) 1 jB 1 ⟨0, by rw [plen_B]; norm_num⟩
    ⟨18, by rw [plen_B]; norm_num⟩ (by simp)
  rw [SimpleGraph.edist_comm] at e10
  have e11 := edist_le_one_of_E (E.pathStart (b := 1) (ℓ := 2) 1 jB 1 ⟨0, by rw [plen_B]; norm_num⟩ rfl)
  rw [SimpleGraph.edist_comm] at e11
  have e12 := edist_tout_root_le (b := 1) (ℓ := 2) 1 jB (leaf 1)
  rw [dep_leaf, SimpleGraph.edist_comm] at e12
  have e13 := edist_le_one_of_E (E.outRoot (b := 1) (ℓ := 2) 1 jB)
  rw [SimpleGraph.edist_comm] at e13
  have hc : (Fin.castSucc (1 : Fin (2 * 2))) = (1 : Fin (2 * 2 + 1)) := rfl
  rw [hc] at e2 e13
  have := tri (tri (tri (tri (tri (tri (tri (tri (tri (tri (tri (tri e1 e2) e3) e4) e5) e6) e7) e8)
    e9) e10) e11) e12) e13
  refine this.trans (le_of_eq ?_)
  norm_num

/-- **The claim "`dist_G(u, v) = dist_H(u, v)` for `u ∈ V_i`, `v ∈ V_j`, `i < j`" in the proof of
Lemma 2.2 is false**: for `b = 1`, `ℓ = 2`, `u = v_{0,(0,0)} ∈ V_0`, `v = v_{1,(0,1)} ∈ V_1`,
`d_G(u, v) ≤ 71 < 73 ≤ d_H(u, v)`. -/
theorem dist_claim_false :
    ((G 1 2).edist (main 0 jA) (main 1 jB) : ENNReal) <
      (H 1 2).wdist (fun e => (hwS 1 2 e : NNReal)) (0, jA) (1, jB) := by
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_le (by norm_num : ((71 : ℕ∞) : ENNReal) < 73) wdist_cex)
  exact_mod_cast edist_cex_le

end Podc.HubLabelingHardness
