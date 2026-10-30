import Papers.PODC2011.UniformLocalAlgorithms.Theorem1

/-!
# Theorem 4: running as fast as the fastest algorithm (Section 4.6)

Given `k ≥ 1` uniform algorithms `U_1, …, U_k` for `Π` and `F`, where the running time of `U_j` is
bounded by a non-decreasing function `f_j` of parameters `Λ_j`, and a pruning algorithm monotone
with respect to all these parameters, the alternating algorithm running `U_1, …, U_k` restricted to
`2^i` rounds in Iteration `i = 0, 1, 2, …` is a uniform algorithm with running time
`O(min_j f_j(Λ_j*))`.

* `theorem_4`: Theorem 4 (with `O(f_min)` made explicit as `C · (f_min + 1)`).
-/

namespace Podc.UniformLocalAlgorithms

variable {V α β : Type*}

section

variable {Pb : Problem V α β} {F : Family V α} (P : Pruning Pb F)

/-- The phases of the algorithm of Theorem 4: Iteration `i` runs every `U_j` for `2^i` rounds. -/
noncomputable def minPhases {k : ℕ} (U : Fin k → Alg V α β) (b₀ : β) (i : ℕ) :
    List (Stage V α β) :=
  List.ofFn fun j => (U j).restrict (2 ^ i) b₀

lemma dur_pre_minPhases_le {k : ℕ} (U : Fin k → Alg V α β) (b₀ : β) (m : ℕ) :
    P.dur (Pruning.pre (minPhases U b₀) (m + 1)) ≤ k * (1 + P.rad) * 2 ^ (m + 1) := by
  induction m with
  | zero =>
    simp [Pruning.pre_succ, minPhases, Pruning.dur, Alg.restrict, List.sum_ofFn]
    nlinarith
  | succ m ih =>
    rw [Pruning.pre_succ, P.dur_append]
    have : P.dur (minPhases U b₀ (m + 1)) = k * (2 ^ (m + 1) + P.rad) := by
      simp [minPhases, Pruning.dur, Alg.restrict, List.sum_ofFn]
    rw [this]
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    calc _ ≤ k * (1 + P.rad) * 2 ^ (m + 1) + k * (2 ^ (m + 1) + P.rad) := Nat.add_le_add_right ih _
      _ ≤ k * (1 + P.rad) * 2 ^ (m + 1 + 1) := by
          have : k * (2 ^ (m + 1) + P.rad) ≤ k * (1 + P.rad) * 2 ^ (m + 1) := by
            rw [mul_assoc]; apply Nat.mul_le_mul_left; nlinarith
          rw [pow_succ 2 (m + 1)]; nlinarith

end

/-- **Theorem 4** of [Korman–Sereni–Viennot]. Let `k ≥ 1`, and for `j < k` let `U_j` be a uniform
algorithm for `Π` and `F` whose running time is bounded with respect to parameters `Λ_j` by a
non-decreasing `f_j ≥ 0`. If `P` is a pruning algorithm monotone with respect to all parameters in
`Λ_1 ∪ ⋯ ∪ Λ_k`, there is a uniform algorithm with running time `O(f_min)`,
`f_min = min_j f_j(Λ_j*)`: its running time is at most `C · (f_j(Λ_j*) + 1)` for every `j`. -/
theorem theorem_4 [Inhabited β] (Pb : Problem V α β) (F : Family V α) (k : ℕ) (hk : 0 < k)
    (ℓ : Fin k → ℕ) (Λ : (j : Fin k) → Fin (ℓ j) → Param V α)
    (f : (j : Fin k) → (Fin (ℓ j) → ℕ) → ℝ) (hf : ∀ j, Monotone (f j)) (hf0 : ∀ j g, 0 ≤ f j g)
    (U : Fin k → Alg V α β)
    (hU : ∀ j G x, F.mem G x → ∀ T : ℕ, f j (correct (Λ j) G x) ≤ T → (U j).SolvesWithin Pb G x T)
    (P : Pruning Pb F) (hP : ∀ j i, P.Monotone (Λ j i)) :
    ∃ U' : Alg V α β, ∃ C : ℝ, ∀ G x, F.mem G x → ∃ T : ℕ,
      (∀ j, (T : ℝ) ≤ C * (f j (correct (Λ j) G x) + 1)) ∧ U'.SolvesWithin Pb G x T := by
  classical
  set K : ℕ := k * (1 + P.rad)
  refine ⟨P.alg (minPhases U default), 2 * (1 + 2 * K), fun G x hx => ?_⟩
  -- the fastest algorithm on this instance
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ
    (fun j => f j (correct (Λ j) G x)) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  set fm := f j₀ (correct (Λ j₀) G x)
  have hex : ∃ s, fm ≤ 2 ^ s := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt fm (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  obtain ⟨s, hfs, hmin⟩ : ∃ s, fm ≤ 2 ^ s ∧ ∀ r < s, ¬ fm ≤ 2 ^ r :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  -- the invariant: instances of `F` whose parameters are at most the original ones
  let Inv : (V → Option α) → Prop := fun x' =>
    F.mem (res G x') x' ∧ ∀ j i, Λ j i (res G x') x' ≤ Λ j i G x
  have hInv : ∀ x' ŷ, Inv x' → Inv (P.prune (res G x') x' ŷ) := by
    intro x' ŷ h
    have hres : res (res G x') (P.prune (res G x') x' ŷ) = res G (P.prune (res G x') x' ŷ) :=
      res_res (P.sub _ _ _)
    refine ⟨hres ▸ P.mem _ _ ŷ h.1, fun j i => ?_⟩
    have := hP j i (res G x') x' ŷ h.1
    rw [hres] at this
    exact this.trans (h.2 j i)
  set B := (U j₀).restrict (2 ^ s) default
  have hBpre : B ∈ Pruning.pre (minPhases U default) (s + 1) :=
    Pruning.mem_pre (by omega) (List.mem_ofFn.2 ⟨j₀, rfl⟩)
  have hB : ∀ x', Inv x' → Pb.sol (res G x') x' (B.run (res G x') x') := by
    intro x' hx'
    have hle : f j₀ (correct (Λ j₀) (res G x') x') ≤ ((2 ^ s : ℕ) : ℝ) := by
      push_cast
      exact (hf j₀ (fun i => hx'.2 j₀ i)).trans hfs
    exact Alg.restrict_run_of_solvesWithin default (hU j₀ _ _ hx'.1 _ hle) le_rfl
  have hinit : Inv (Pruning.act (Pruning.init x : Pruning.State V α β)) := by
    refine ⟨?_, fun j i => ?_⟩
    · show F.mem (res G x) x
      rw [F.res_eq hx]; exact hx
    · show Λ j i (res G x) x ≤ Λ j i G x
      rw [F.res_eq hx]
  have hempty := P.act_runList_eq_none_of_mem (Inv := Inv) hInv (fun x' h => h.1) hBpre hB hinit
  refine ⟨_, ?_, P.solvesWithin_of_runList_empty hx hempty⟩
  -- the running time bound
  have hD := dur_pre_minPhases_le P U default s
  have hs : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have hT : max (s + 1) (P.dur (Pruning.pre (minPhases U default) (s + 1))) ≤ (1 + 2 * K) * 2 ^ s := by
    have : k * (1 + P.rad) * 2 ^ (s + 1) = 2 * K * 2 ^ s := by rw [pow_succ]; ring
    rw [this] at hD
    apply max_le <;> nlinarith
  have hT' : ((max (s + 1) (P.dur (Pruning.pre (minPhases U default) (s + 1))) : ℕ) : ℝ) ≤
      (1 + 2 * K) * 2 ^ s := by exact_mod_cast hT
  have hfm0 : 0 ≤ fm := hf0 _ _
  have hpow : (2 : ℝ) ^ s ≤ 2 * fm + 1 := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0]; simp; linarith
    · have hlt : (2 : ℝ) ^ (s - 1) < fm := lt_of_not_ge (hmin (s - 1) (by omega))
      have : (2 : ℝ) ^ s = 2 * 2 ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
      linarith
  intro j
  have hj : fm ≤ f j (correct (Λ j) G x) := hj₀ j (Finset.mem_univ _)
  calc _ ≤ (1 + 2 * K : ℝ) * 2 ^ s := hT'
    _ ≤ (1 + 2 * K : ℝ) * (2 * fm + 1) := by gcongr
    _ ≤ 2 * (1 + 2 * K) * (f j (correct (Λ j) G x) + 1) := by nlinarith

end Podc.UniformLocalAlgorithms
