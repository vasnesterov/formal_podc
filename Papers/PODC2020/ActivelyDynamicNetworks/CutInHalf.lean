import Papers.PODC2020.ActivelyDynamicNetworks.LowerBounds
import Papers.PODC2020.ActivelyDynamicNetworks.PointerJumping
import Mathlib.Data.Nat.Factorization.Basic

/-!
# CutInHalf: a centralized strategy with `O(log n)` rounds and `≤ n` activations
(Appendix D.1, the line case of Theorem 6.3 / D.5)

Michail–Skretas–Spirakis, PODC 2020. On the line `0 - 1 - ⋯ - (N-1)`, in round `i` every node
`a` with `2^(i+1) ∣ a` activates the edge to `a + 2^(i+1)` (via the common neighbour `a + 2^i`),
and `a + 2^i` drops its edge to `a + 2^(i+1)`. Equivalently, node `b ≠ 0` with `2^(i+1) ∣ b`
jumps from its parent `b - 2^i` to its grandparent `b - 2^(i+1)`. So every snapshot is a tree; after
`R = ⌊log₂ (N-1)⌋` rounds the parent of `b` is `b` with its lowest set bit cleared (the binomial
tree), whose depth is at most `R + 1 ≤ ⌈log₂ N⌉`.

* `exec N`: the execution (`isExec`, `exec_zero`: starts from `pathGraph N`).
* `final_isDepthTree`: after `R` rounds the network is a tree of depth `≤ ⌈log₂ N⌉` rooted at `0`.
* `totalActivations_le`: at most `N - 1` activations in total (`Σ_i ⌊(N-1)/2^(i+1)⌋`).

This matches the lower bounds `lemma_6_1` (time `Ω(log n)`) and `lemma_6_2_total` (`Ω(n)`
activations); the paper adds the deactivations implicitly (its CutInHalf only activates edges, so
the final network is not a tree, only of small diameter). The paper's extension to general graphs
(an Euler tour of a spanning tree as a virtual line) is not formalized.
-/

namespace Podc.ActivelyDynamicNetworks.CutInHalf

open SimpleGraph Cslib.DynNet.Active

/-- Parent of node `b` after `i` rounds. -/
def P : ℕ → ℕ → ℕ
  | 0, b => b - 1
  | i + 1, b => if b ≠ 0 ∧ 2 ^ (i + 1) ∣ b then P i (P i b) else P i b

theorem P_le (i b : ℕ) : P i b ≤ b := by
  induction i generalizing b with
  | zero => simp [P]
  | succ i ih =>
    simp only [P]; split_ifs
    · exact (ih _).trans (ih _)
    · exact ih _

theorem P_zero_right (i : ℕ) : P i 0 = 0 := by
  have := P_le i 0; omega

theorem P_lt (i : ℕ) {b : ℕ} (hb : b ≠ 0) : P i b < b := by
  induction i with
  | zero => simp [P]; omega
  | succ i ih =>
    simp only [P]; split_ifs
    · exact (P_le _ _).trans_lt ih
    · exact ih

/-- The closed form: if `2^m ∣ c` (`c ≠ 0`) then `P i c = c - 2^i` for `i ≤ m`, and
`P i c = c - 2^m` for `m ≤ i` when `2^m` is the exact power of two in `c`. -/
theorem P_spec (i : ℕ) : ∀ c m, c ≠ 0 → 2 ^ m ∣ c →
    (i ≤ m → P i c = c - 2 ^ i) ∧ (m ≤ i → ¬ 2 ^ (m + 1) ∣ c → P i c = c - 2 ^ m) := by
  induction i with
  | zero =>
    intro c m _ _
    refine ⟨fun _ => by simp [P], fun hm _ => by rw [Nat.le_zero.1 hm]; simp [P]⟩
  | succ i ih =>
    intro c m hc hdvd
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    constructor
    · intro him
      have h1 : 2 ^ (i + 1) ∣ c := (Nat.pow_dvd_pow 2 him).trans hdvd
      have hge : 2 ^ (i + 1) ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hc) h1
      rw [pow_succ] at hge
      simp only [P, ne_eq, hc, not_false_eq_true, h1, and_self, ite_true]
      have e1 : P i c = c - 2 ^ i := (ih c (i + 1) hc h1).1 (by omega)
      have h2 : 2 ^ i ∣ c - 2 ^ i :=
        Nat.dvd_sub ((Nat.pow_dvd_pow 2 (by omega : i ≤ i + 1)).trans h1) (dvd_refl _)
      rw [e1, (ih (c - 2 ^ i) i (by omega) h2).1 le_rfl, pow_succ]
      omega
    · intro hmi hnd
      rcases Nat.lt_or_ge m (i + 1) with h | h
      · have hn : ¬ 2 ^ (i + 1) ∣ c := fun h' =>
          hnd ((Nat.pow_dvd_pow 2 (by omega : m + 1 ≤ i + 1)).trans h')
        simp only [P, hn, and_false, ite_false]
        exact (ih c m hc hdvd).2 (by omega) hnd
      · have hm : m = i + 1 := by omega
        subst hm
        have := (ih c (i + 1) hc hdvd).1 (by omega)
        have hge : 2 ^ (i + 1) ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hc) hdvd
        rw [pow_succ] at hge
        simp only [P, ne_eq, hc, not_false_eq_true, hdvd, and_self, ite_true]
        have h2 : 2 ^ i ∣ c - 2 ^ i :=
          Nat.dvd_sub ((Nat.pow_dvd_pow 2 (by omega : i ≤ i + 1)).trans hdvd) (dvd_refl _)
        rw [this, (ih (c - 2 ^ i) i (by omega) h2).1 le_rfl, pow_succ]
        omega

variable (N : ℕ)

/-- Parent maps on `Fin N`. -/
def PF (i : ℕ) (b : Fin N) : Fin N := ⟨P i b, (P_le i b).trans_lt b.2⟩

/-- Moving nodes of round `i`. -/
def movers (i : ℕ) (b : Fin N) : Prop := b.val ≠ 0 ∧ 2 ^ (i + 1) ∣ b.val

instance (i : ℕ) : DecidablePred (movers N i) := fun _ => by unfold movers; infer_instance

/-- The snapshots of CutInHalf. -/
def exec (i : ℕ) : SimpleGraph (Fin N) := parentGraph (PF N i)

variable {N}

theorem isRootedMap_PF (i : ℕ) (hN : 0 < N) : IsRootedMap (PF N i) ⟨0, hN⟩ Fin.val where
  map_root := by ext; simp [PF, P_zero_right]
  rk_lt v hv := P_lt i fun h => hv (Fin.ext h)

theorem jump_PF (i : ℕ) : jump (PF N i) (movers N i) = PF N (i + 1) := by
  funext b
  ext
  simp only [jump, movers, PF]
  by_cases h : b.val ≠ 0 ∧ 2 ^ (i + 1) ∣ b.val
  · rw [if_pos h]; simp only [P, if_pos h]
  · rw [if_neg h]; simp only [P, if_neg h]

theorem movers_ne_root (i : ℕ) (hN : 0 < N) :
    ∀ b, movers N i b → PF N i b ≠ ⟨0, hN⟩ := by
  rintro b ⟨h1, h2⟩ h
  have := congrArg Fin.val h
  simp only [PF] at this
  have e := (P_spec i b (i + 1) h1 h2).1 (by omega)
  have hge : 2 ^ (i + 1) ≤ b.val := Nat.le_of_dvd (Nat.pos_of_ne_zero h1) h2
  rw [pow_succ] at hge
  have : 0 < 2 ^ i := Nat.two_pow_pos i
  omega

theorem exec_zero : exec N 0 = pathGraph N := by
  ext a b
  simp only [exec, parentGraph_adj, pathGraph_adj, PF, P, ne_eq, Fin.ext_iff]
  omega

/-- CutInHalf is a valid execution of the actively dynamic model. -/
theorem isExec (hN : 0 < N) : IsExec (exec N) := fun i => by
  rw [exec, exec, ← jump_PF]
  exact validRound_jump (isRootedMap_PF i hN) (movers_ne_root i hN)

theorem isTree (hN : 0 < N) (i : ℕ) : (exec N i).IsTree := (isRootedMap_PF i hN).isTree

/-- The number of moving nodes in round `i` is `⌊(N-1)/2^(i+1)⌋`. -/
theorem ncard_movers (i : ℕ) : {b | movers N i b}.ncard ≤ (N - 1) / 2 ^ (i + 1) := by
  classical
  have : {b | movers N i b} ⊆
      (Fin.val ⁻¹' ↑((Finset.Ioc 0 (N - 1)).filter (2 ^ (i + 1) ∣ ·)) : Set (Fin N)) := by
    rintro b ⟨h1, h2⟩
    simp only [Set.mem_preimage, Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq]
    exact ⟨⟨Nat.pos_of_ne_zero h1, by have := b.2; omega⟩, h2⟩
  calc {b | movers N i b}.ncard ≤ (Fin.val ⁻¹' ↑((Finset.Ioc 0 (N - 1)).filter
        (2 ^ (i + 1) ∣ ·)) : Set (Fin N)).ncard := Set.ncard_le_ncard this (Set.toFinite _)
    _ ≤ (↑((Finset.Ioc 0 (N - 1)).filter (2 ^ (i + 1) ∣ ·)) : Set ℕ).ncard :=
        Set.ncard_preimage_of_injective_subset_range Fin.val_injective (by
          intro x hx
          simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hx
          exact ⟨⟨x, by omega⟩, rfl⟩) |>.le
    _ = (N - 1) / 2 ^ (i + 1) := by
        rw [Set.ncard_coe_finset, Nat.Ioc_filter_dvd_card_eq_div]

theorem numActivated_le (hN : 0 < N) (i : ℕ) :
    numActivated (exec N) i ≤ (N - 1) / 2 ^ (i + 1) := by
  unfold numActivated
  rw [exec, exec, ← jump_PF]
  exact (numActivated_jump_le (isRootedMap_PF i hN) (movers_ne_root i hN)).trans (ncard_movers i)

theorem sum_div_pow_le (m T : ℕ) :
    (∑ i ∈ Finset.range T, m / 2 ^ (i + 1)) + m / 2 ^ T ≤ m := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have : m / 2 ^ (T + 1) = m / 2 ^ T / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [this] at *
    omega

/-- **Total activations of CutInHalf**: at most `N - 1`, over any horizon. -/
theorem totalActivations_le (hN : 0 < N) (T : ℕ) : totalActivations (exec N) T ≤ N - 1 := by
  unfold totalActivations
  calc ∑ i ∈ Finset.range T, numActivated (exec N) i
      ≤ ∑ i ∈ Finset.range T, (N - 1) / 2 ^ (i + 1) := Finset.sum_le_sum fun i _ =>
        numActivated_le hN i
    _ ≤ N - 1 := le_trans (Nat.le_add_right _ _) (sum_div_pow_le (N - 1) T)

/-- Depth bound: adding the binary digits from the top, every node is within `k` of a node
`a` with `2^k ∣ a`, in the final tree. -/
theorem edist_final_le {R : ℕ} (hR : N ≤ 2 ^ (R + 1)) :
    ∀ k a x : ℕ, 2 ^ k ∣ a → x < 2 ^ k → (ha : a + x < N) →
      (exec N R).edist ⟨a, by omega⟩ ⟨a + x, ha⟩ ≤ (k : ℕ∞) := by
  intro k
  induction k with
  | zero => intro a x _ hx ha; simp at hx; subst hx; simp
  | succ k ih =>
    intro a x hdvd hx ha
    have hk : 2 ^ k ∣ a := (Nat.pow_dvd_pow 2 (by omega : k ≤ k + 1)).trans hdvd
    rcases Nat.lt_or_ge x (2 ^ k) with h | h
    · exact (ih a x hk h ha).trans (by norm_cast; omega)
    · -- edge `a — a + 2^k`, then the remaining digits
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hb : a + 2 ^ k < N := by omega
      have hkR : k ≤ R := by
        by_contra hc
        have : 2 ^ (R + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hadj : (exec N R).Adj ⟨a, by omega⟩ ⟨a + 2 ^ k, hb⟩ := by
        rw [exec, parentGraph_adj]
        refine ⟨fun h => by have := congrArg Fin.val h; simp at this, Or.inr ?_⟩
        ext
        simp only [PF]
        have hd : 2 ^ k ∣ a + 2 ^ k := Nat.dvd_add hk (dvd_refl _)
        have hnd : ¬ 2 ^ (k + 1) ∣ a + 2 ^ k := by
          intro h'
          have := (Nat.dvd_add_right hdvd).1 h'
          have := Nat.le_of_dvd (Nat.two_pow_pos k) this
          omega
        rw [(P_spec R (a + 2 ^ k) k (by omega) hd).2 hkR hnd]
        omega
      have h2 := ih (a + 2 ^ k) (x - 2 ^ k) (Nat.dvd_add hk (dvd_refl _)) (by omega)
        (by omega)
      have e : a + 2 ^ k + (x - 2 ^ k) = a + x := by omega
      calc (exec N R).edist ⟨a, by omega⟩ ⟨a + x, ha⟩
          ≤ (exec N R).edist ⟨a, by omega⟩ ⟨a + 2 ^ k, hb⟩ +
            (exec N R).edist ⟨a + 2 ^ k, hb⟩ ⟨a + x, ha⟩ := (exec N R).edist_triangle
        _ ≤ 1 + k := by
            gcongr
            · exact (edist_eq_one_iff_adj.2 hadj).le
            · convert h2 using 3 <;> simp [e]
        _ = (k + 1 : ℕ) := by push_cast; ring

/-- **Theorem 6.3 / D.5 for the line.** After `R = ⌊log₂ (N-1)⌋` rounds of CutInHalf the
network is a tree of depth at most `⌈log₂ N⌉` rooted at `0`. -/
theorem final_isDepthTree (hN : 2 ≤ N) :
    IsDepthTree (exec N (Nat.log 2 (N - 1))) ⟨0, by omega⟩ (Nat.clog 2 N) := by
  have hR : N ≤ 2 ^ (Nat.log 2 (N - 1) + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N - 1); omega
  refine ⟨isTree (by omega) _, fun v => ?_⟩
  have h1 := edist_final_le hR (Nat.log 2 (N - 1) + 1) 0 v (dvd_zero _) (by have := v.2; omega)
    (by simpa using v.2)
  simp only [zero_add] at h1
  refine h1.trans ?_
  norm_cast
  -- `⌊log₂ (N-1)⌋ + 1 ≤ ⌈log₂ N⌉`
  have : 2 ^ Nat.log 2 (N - 1) ≤ N - 1 := Nat.pow_log_le_self 2 (by omega)
  have h3 : 2 ^ Nat.log 2 (N - 1) < N := by omega
  exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by norm_num)).2 h3)

/-- **Tightness of Lemmas 6.1 and 6.2** (centralized setting): from the spanning line on `N ≥ 2`
nodes, `⌊log₂ (N-1)⌋` rounds and at most `N - 1` edge activations suffice to reach a rooted tree of
depth `⌈log₂ N⌉`. -/
theorem theorem_6_3_line (hN : 2 ≤ N) :
    ∃ E : ℕ → SimpleGraph (Fin N), IsExec E ∧ E 0 = pathGraph N ∧
      IsDepthTree (E (Nat.log 2 (N - 1))) ⟨0, by omega⟩ (Nat.clog 2 N) ∧
      ∀ T, totalActivations E T ≤ N - 1 :=
  ⟨exec N, isExec (by omega), exec_zero, final_isDepthTree hN, totalActivations_le (by omega)⟩

end Podc.ActivelyDynamicNetworks.CutInHalf
