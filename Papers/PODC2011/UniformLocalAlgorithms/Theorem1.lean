import Papers.PODC2011.UniformLocalAlgorithms.Model
import Papers.PODC2011.UniformLocalAlgorithms.SeqNumber

/-!
# Theorem 1: the deterministic transformer (Section 4.3)

Given a pruning algorithm `P` for `Π` and `F`, monotone with respect to the parameters `Γ`, and a
non-uniform deterministic algorithm `A_Γ` whose running time with good guesses `g` is at most
`f g`, where `f` has a sequence-number function `s_f`, the alternating algorithm `π` of
Algorithm 1 is a uniform algorithm with running time `O(f* · s_f(f*))`, `f* = f(Γ*)`.

* `DependsWithTime Pb F Γ A f`: `A` depends on `Γ` and its running time is bounded by `f`.
* `algPi`: the algorithm `π` of Algorithm 1 (iteration `i ≥ 1` runs `A` with every guess vector of
  `S_f(2^i)`, each restricted to `⌈c⌉ · 2^i` rounds and followed by `P`).
* `theorem_1`: Theorem 1.
-/

open Cslib.Local SimpleGraph

namespace Podc.UniformLocalAlgorithms

variable {V α β : Type*} {ℓ : ℕ}

/-- The non-uniform algorithm `A` (a uniform algorithm `A g` for each vector `g` of guesses for the
parameters `Γ`) *depends on* `Γ` and its running time is bounded by `f` (Section 2): on every
instance of `F` and for every vector `g` of good guesses (`Γ k (G, x) ≤ g k`), `A g` solves the
instance within `T` rounds for every `T ≥ f g`. Nothing is required for bad guesses. -/
def DependsWithTime (Pb : Problem V α β) (F : Family V α) (Γ : Fin ℓ → Param V α)
    (A : (Fin ℓ → ℕ) → Alg V α β) (f : (Fin ℓ → ℕ) → ℝ) : Prop :=
  ∀ G x, F.mem G x → ∀ g : Fin ℓ → ℕ, (∀ k, Γ k G x ≤ g k) →
    ∀ T : ℕ, f g ≤ T → (A g).SolvesWithin Pb G x T

/-- The vector of correct guesses `Γ*(G, x)`. -/
def correct (Γ : Fin ℓ → Param V α) (G : SimpleGraph V) (x : V → Option α) : Fin ℓ → ℕ :=
  fun k => Γ k G x

namespace Pruning

variable {Pb : Problem V α β} {F : Family V α} (P : Pruning Pb F)

lemma le_dur_of_mem {L : List (Stage V α β)} {B : Stage V α β} (h : B ∈ L) :
    B.rad + P.rad ≤ P.dur L := by
  induction L with
  | nil => simp at h
  | cons B' L ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp only [dur_cons]; omega

lemma mem_pre {phases : ℕ → List (Stage V α β)} {B : Stage V α β} {i m : ℕ} (hi : i < m)
    (hB : B ∈ phases i) : B ∈ pre phases m :=
  List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hB⟩

/-- The invariant of the current instances of a run of an alternating algorithm on `(G, x)`: they
belong to `F` and their parameters `Γ` are at most the correct values `Γ*(G, x)` (by monotonicity
of `P`). -/
def RunInv (F : Family V α) (Γ : Fin ℓ → Param V α) (G : SimpleGraph V) (p : Fin ℓ → ℕ)
    (x' : V → Option α) : Prop :=
  F.mem (res G x') x' ∧ ∀ k, Γ k (res G x') x' ≤ p k

lemma inv_prune {Γ : Fin ℓ → Param V α} (hP : ∀ k, P.Monotone (Γ k)) {G : SimpleGraph V}
    {p : Fin ℓ → ℕ} {x' : V → Option α} (ŷ : V → β) (h : RunInv F Γ G p x') :
    RunInv F Γ G p (P.prune (res G x') x' ŷ) := by
  have hres : res (res G x') (P.prune (res G x') x' ŷ) = res G (P.prune (res G x') x' ŷ) :=
    res_res (P.sub _ _ _)
  refine ⟨hres ▸ P.mem _ _ ŷ h.1, fun k => ?_⟩
  have := hP k (res G x') x' ŷ h.1
  rw [hres] at this
  exact this.trans (h.2 k)

end Pruning

section Theorem1

variable {Pb : Problem V α β} {F : Family V α} (P : Pruning Pb F)

/-- The phases of the algorithm `π` of Algorithm 1: phase `0` is empty, and phase `i ≥ 1`
("Iteration `i`") runs, for every guess vector `g ∈ S(2^i)`, the algorithm `A g` restricted to
`c · 2^i` rounds, each followed by the pruning algorithm. -/
noncomputable def piPhases (A : (Fin ℓ → ℕ) → Alg V α β) (S : ℕ → Finset (Fin ℓ → ℕ)) (c : ℕ)
    (b₀ : β) (i : ℕ) : List (Stage V α β) :=
  if i = 0 then [] else (S (2 ^ i)).toList.map fun g => (A g).restrict (c * 2 ^ i) b₀

/-- The uniform algorithm `π` of Algorithm 1. -/
noncomputable def algPi (A : (Fin ℓ → ℕ) → Alg V α β) (S : ℕ → Finset (Fin ℓ → ℕ)) (c : ℕ)
    (b₀ : β) : Alg V α β :=
  P.alg (piPhases A S c b₀)

lemma dur_piPhases_le (A : (Fin ℓ → ℕ) → Alg V α β) (S : ℕ → Finset (Fin ℓ → ℕ)) (c : ℕ)
    (b₀ : β) (s : ℕ → ℕ) (hS : ∀ i, (S i).card ≤ s i) (i : ℕ) :
    P.dur (piPhases A S c b₀ i) ≤ s (2 ^ i) * ((c + P.rad) * 2 ^ i) := by
  unfold piPhases
  split_ifs with h
  · simp
  · simp only [Pruning.dur, List.map_map, Function.comp_def, Alg.restrict]
    rw [List.map_const', List.sum_replicate, Finset.length_toList, smul_eq_mul]
    have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    calc (S (2 ^ i)).card * (c * 2 ^ i + P.rad) ≤ s (2 ^ i) * (c * 2 ^ i + P.rad) :=
          Nat.mul_le_mul_right _ (hS _)
      _ ≤ s (2 ^ i) * ((c + P.rad) * 2 ^ i) := by
          apply Nat.mul_le_mul_left; nlinarith

lemma dur_pre_piPhases_le (A : (Fin ℓ → ℕ) → Alg V α β) (S : ℕ → Finset (Fin ℓ → ℕ)) (c : ℕ)
    (b₀ : β) (s : ℕ → ℕ) (hs : Monotone s) (hS : ∀ i, (S i).card ≤ s i) (m : ℕ) :
    P.dur (Pruning.pre (piPhases A S c b₀) (m + 1)) ≤ s (2 ^ m) * ((c + P.rad) * 2 ^ (m + 1)) := by
  induction m with
  | zero => simp [Pruning.pre_succ, piPhases]
  | succ m ih =>
    rw [Pruning.pre_succ, P.dur_append]
    have h1 := dur_piPhases_le P A S c b₀ s hS (m + 1)
    have h2 : s (2 ^ m) ≤ s (2 ^ (m + 1)) := hs (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h3 : s (2 ^ m) * ((c + P.rad) * 2 ^ (m + 1)) ≤
        s (2 ^ (m + 1)) * ((c + P.rad) * 2 ^ (m + 1)) := Nat.mul_le_mul_right _ h2
    calc _ ≤ s (2 ^ m) * ((c + P.rad) * 2 ^ (m + 1)) +
          s (2 ^ (m + 1)) * ((c + P.rad) * 2 ^ (m + 1)) := Nat.add_le_add ih h1
      _ ≤ s (2 ^ (m + 1)) * ((c + P.rad) * 2 ^ (m + 1)) +
          s (2 ^ (m + 1)) * ((c + P.rad) * 2 ^ (m + 1)) := Nat.add_le_add_right h3 _
      _ = s (2 ^ (m + 1)) * ((c + P.rad) * 2 ^ (m + 1 + 1)) := by ring

/-- The core of the proof of Theorem 1: on an instance with `f* ≤ 2^s` (`s ≥ 1`), all nodes are
pruned by the end of Iteration `s` of `π`, so `π` solves the instance within the duration of the
first `s` iterations. -/
lemma algPi_solvesWithin {Γ : Fin ℓ → Param V α} (hP : ∀ k, P.Monotone (Γ k))
    {A : (Fin ℓ → ℕ) → Alg V α β} {f : (Fin ℓ → ℕ) → ℝ} (hA : DependsWithTime Pb F Γ A f)
    (S : SetSeq f) {c : ℝ} (hc : S.Bounded c) (b₀ : β) {G : SimpleGraph V} {x : V → Option α}
    (hx : F.mem G x) {s : ℕ} (hs1 : 1 ≤ s) (hfs : f (correct Γ G x) ≤ 2 ^ s) :
    (algPi P A S.S ⌈c⌉₊ b₀).SolvesWithin Pb G x
      (P.dur (Pruning.pre (piPhases A S.S ⌈c⌉₊ b₀) (s + 1))) := by
  set p := correct Γ G x
  obtain ⟨g, hgS, hpg⟩ := S.dom (2 ^ s) p (by exact_mod_cast hfs)
  set B := (A g).restrict (⌈c⌉₊ * 2 ^ s) b₀
  have hBmem : B ∈ piPhases A S.S ⌈c⌉₊ b₀ s := by
    simp only [piPhases, show s ≠ 0 by omega, ite_false]
    exact List.mem_map.2 ⟨g, Finset.mem_toList.2 hgS, rfl⟩
  have hBpre : B ∈ Pruning.pre (piPhases A S.S ⌈c⌉₊ b₀) (s + 1) := Pruning.mem_pre (by omega) hBmem
  -- the guess vector `g` is good for every instance reachable during the run
  have hfg : f g ≤ ((⌈c⌉₊ * 2 ^ s : ℕ) : ℝ) := by
    have := hc.2 (2 ^ s) g hgS
    push_cast at this ⊢
    exact this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (by positivity))
  have hB : ∀ x', Pruning.RunInv F Γ G p x' → Pb.sol (res G x') x' (B.run (res G x') x') := by
    intro x' hx'
    exact Alg.restrict_run_of_solvesWithin b₀
      (hA _ _ hx'.1 g (fun k => (hx'.2 k).trans (hpg k)) _ hfg) le_rfl
  have hinit : Pruning.RunInv F Γ G p (Pruning.act (Pruning.init x : Pruning.State V α β)) := by
    refine ⟨?_, fun k => ?_⟩
    · show F.mem (res G x) x
      rw [F.res_eq hx]; exact hx
    · show Γ k (res G x) x ≤ Γ k G x
      rw [F.res_eq hx]
  have hempty := P.act_runList_eq_none_of_mem (Inv := Pruning.RunInv F Γ G p)
    (fun x' ŷ h => P.inv_prune hP ŷ h) (fun x' h => h.1) hBpre hB hinit
  have hsol := P.solvesWithin_of_runList_empty hx hempty
  have hle : s + 1 ≤ P.dur (Pruning.pre (piPhases A S.S ⌈c⌉₊ b₀) (s + 1)) := by
    have h1 := P.le_dur_of_mem hBpre
    have h2 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
    have h3 : 1 ≤ ⌈c⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; exact hc.1)
    have h4 : 2 ^ s ≤ ⌈c⌉₊ * 2 ^ s := Nat.le_mul_of_pos_left _ h3
    simp only [B, Alg.restrict] at h1
    omega
  rwa [max_eq_right hle] at hsol

/-- **Theorem 1** of [Korman–Sereni–Viennot]. Let `A_Γ` be a deterministic algorithm for `Π` and
`F` depending on parameters `Γ = (p_1, …, p_ℓ)`, whose running time with good guesses is bounded by
`f : ℕ^ℓ → ℝ_{≥0}`. If `f` has a sequence-number function `s_f` and there is a `Γ`-monotone pruning
algorithm `P` for `Π` and `F`, then there is a uniform deterministic algorithm for `Π` and `F`
with running time `O(f* · s_f(f*))`, where `f* = f(Γ*)`.

The `O` is uniform over all instances: the running time is at most `C · (f* · s_f(⌊f*⌋) + 1)`
for a constant `C` (the `+ 1` is needed for instances with `f* < 1`). -/
theorem theorem_1 [Inhabited β] (Pb : Problem V α β) (F : Family V α) (Γ : Fin ℓ → Param V α)
    (A : (Fin ℓ → ℕ) → Alg V α β) (f : (Fin ℓ → ℕ) → ℝ) (hf0 : ∀ g, 0 ≤ f g)
    (hA : DependsWithTime Pb F Γ A f) (sf : ℕ → ℕ) (hsf : IsSeqNumber f sf)
    (P : Pruning Pb F) (hP : ∀ k, P.Monotone (Γ k)) :
    ∃ U : Alg V α β, ∃ C : ℝ, ∀ G x, F.mem G x → ∃ T : ℕ,
      (T : ℝ) ≤ C * (f (correct Γ G x) * sf ⌊f (correct Γ G x)⌋₊ + 1) ∧
      U.SolvesWithin Pb G x T := by
  obtain ⟨⟨hmono, a, ha, hslow⟩, S, c, hc, hcard⟩ := hsf
  set K : ℕ := ⌈c⌉₊ + P.rad with hK
  refine ⟨algPi P A S.S ⌈c⌉₊ default, max (4 * a * K) (4 * K * sf 2), fun G x hx => ?_⟩
  set fs := f (correct Γ G x)
  have hex : ∃ s, 1 ≤ s ∧ fs ≤ 2 ^ s := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt fs (by norm_num : (1 : ℝ) < 2)
    exact ⟨n + 1, by omega, hn.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))⟩
  classical
  obtain ⟨s, ⟨hs1, hfs⟩, hmin⟩ : ∃ s, (1 ≤ s ∧ fs ≤ 2 ^ s) ∧ ∀ r < s, ¬ (1 ≤ r ∧ fs ≤ 2 ^ r) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  refine ⟨_, ?_, algPi_solvesWithin P hP hA S hc default hx hs1 hfs⟩
  have hD := dur_pre_piPhases_le P A S.S ⌈c⌉₊ default sf hmono hcard s
  have hfs0 : 0 ≤ fs := hf0 _
  have hC1 : (4 * a * K : ℝ) ≤ max (4 * a * K : ℝ) (4 * K * sf 2) := le_max_left _ _
  have hC2 : (4 * K * sf 2 : ℝ) ≤ max (4 * a * K : ℝ) (4 * K * sf 2) := le_max_right _ _
  have hD' : (P.dur (Pruning.pre (piPhases A S.S ⌈c⌉₊ default) (s + 1)) : ℝ) ≤
      sf (2 ^ s) * (K * 2 ^ (s + 1)) := by exact_mod_cast hD
  have hmax0 : 0 ≤ max (4 * a * K : ℝ) (4 * K * sf 2) := hC1.trans' (by positivity)
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · -- `s = 1`: a constant number of rounds
    have : s = 1 := by omega
    subst this
    norm_num at hD'
    calc _ ≤ (4 * K * sf 2 : ℝ) := by linarith
      _ ≤ max (4 * a * K : ℝ) (4 * K * sf 2) := hC2
      _ ≤ max (4 * a * K : ℝ) (4 * K * sf 2) * (fs * sf ⌊fs⌋₊ + 1) := by
          apply le_mul_of_one_le_right hmax0; nlinarith [Nat.cast_nonneg (α := ℝ) (sf ⌊fs⌋₊)]
  · -- `s ≥ 2`: then `2^(s-1) < f*` by minimality of `s`
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
    have hr : ¬ (1 ≤ r ∧ fs ≤ 2 ^ r) := hmin r (by omega)
    have hlt : (2 : ℝ) ^ r < fs := by
      rw [not_and, not_le] at hr; exact hr (by omega)
    have hfloor : 2 ^ r ≤ ⌊fs⌋₊ := Nat.le_floor (by exact_mod_cast hlt.le)
    have hsf1 : sf (2 ^ (r + 1)) ≤ a * sf ⌊fs⌋₊ := by
      have h1 : sf (2 * 2 ^ r) ≤ a * sf (2 ^ r) :=
        hslow _ (by have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2; omega)
      rw [pow_succ, mul_comm]
      exact h1.trans (Nat.mul_le_mul_left _ (hmono hfloor))
    have hsf1' : (sf (2 ^ (r + 1)) : ℝ) ≤ a * sf ⌊fs⌋₊ := by exact_mod_cast hsf1
    have hpow : (2 : ℝ) ^ (r + 1 + 1) ≤ 4 * fs := by
      have : (2 : ℝ) ^ (r + 1 + 1) = 4 * 2 ^ r := by ring
      rw [this]; linarith
    calc _ ≤ (sf (2 ^ (r + 1)) : ℝ) * (K * 2 ^ (r + 1 + 1)) := hD'
      _ ≤ (a * sf ⌊fs⌋₊ : ℝ) * (K * (4 * fs)) := by
          apply mul_le_mul hsf1' (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
            (by positivity)
      _ = (4 * a * K : ℝ) * (fs * sf ⌊fs⌋₊) := by ring
      _ ≤ max (4 * a * K : ℝ) (4 * K * sf 2) * (fs * sf ⌊fs⌋₊ + 1) := by
          apply mul_le_mul hC1 (by linarith) (by positivity) hmax0

end Theorem1

end Podc.UniformLocalAlgorithms
