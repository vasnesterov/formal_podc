import Papers.PODC2026.DistinctGathering.TwoPoint

/-!
# Theorems 1 and 4: impossibility of (Distinct) Gathering under Round-Robin

[Frei–Wada, *Distinct Gathering and the Virtue of Self-Consistency*, PODC 2026].

* `theorem_1`: Gathering (arbitrary initial configurations) of `n ≥ 3` robots under Round-Robin
  is impossible, even with a consistent unit length (and a common chirality).
* `theorem_4`: Distinct Gathering of `3` robots under Round-Robin is impossible under the default
  assumptions (variable disorientation), even with a common chirality.

Both hold for *every* movement model in which the adversary may let a robot reach its target, in
particular for rigid movement and for non-rigid movement with any minimum distance `δ`.

Proof of Theorem 4 (much simpler than the sketch in the paper). Gathering must end with a lone
robot jumping onto the point of the other two; normalizing its view, some view `{0, w}` is
answered by jumping onto the other point (`exists_fixed_view`), and the adversary can make every
two-point view look like `{0, w}`. Also, since robots in a distinct configuration must eventually
collide, some robot `x` in some distinct configuration `C` jumps onto another robot `y`
(`exists_merge`). Now start from `C` with the order `x, y, z`: after `x` joins `y`, the activated
robot is always accompanied, so the robots swap sides forever (`run_cycle`).
-/

noncomputable section

namespace Podc.DistinctGathering

open Cslib.MobileRobots

variable {n : ℕ}

/-! ### Theorem 1 -/

/-- Theorem 1 of [Frei–Wada], general form: for `n ≥ 3`, no algorithm solves Gathering under
Round-Robin for any frame restriction that allows all rotations with the true unit length, and
any movement model. -/
theorem theorem_1_general (hn : 3 ≤ n) (A : Algorithm) {frameOK : Frame → Prop}
    (hframe : ∀ a (ha : a ≠ 0), ‖a‖ = 1 → frameOK (Frame.ofCoef a ha)) (M : Movement) :
    ¬ Solves n A IsRoundRobin frameOK M (fun _ => True) := by
  intro hS
  have : NeZero n := ⟨by omega⟩
  set σ : Equiv.Perm (Fin n) := 1
  have hid : frameOK Frame.id := hframe 1 one_ne_zero (by simp)
  -- Step 1: some two-point view `{0, w}` is answered by jumping onto the other point.
  obtain ⟨w, hw, hA⟩ := exists_fixed_view hid hS (isRoundRobin_rr σ) (P₀ := cfg 0 1 σ 0)
    trivial (cfg_not_gathered hn zero_ne_one σ 0)
  -- Step 2: the swapping execution on the points `0` and `w`.
  have huv : (0 : ℂ) ≠ w := Ne.symm hw
  set adv : Adversary n :=
    Adversary.rigidOf fun t P => normFrame 0 w w huv hw (P (rr σ t))
  have hcyc := run_cycle hn hw hA huv σ adv (cfg 0 w σ 0) 0 (fun _ _ _ => ⟨rfl, rfl⟩) rfl
  have hlegal : Legal A (rr σ) adv (cfg 0 w σ 0) frameOK M := by
    intro t
    refine ⟨?_, M.admissible_one _⟩
    show frameOK (normFrame 0 w w huv hw (run A (rr σ) adv (cfg 0 w σ 0) t (rr σ t)))
    rw [hcyc t (Nat.zero_le t)]
    apply hframe
    rcases cfg_mem 0 w σ t (rr σ t) with h | h <;> rw [h] <;> simp [other, hw]
  obtain ⟨T, hT⟩ := hS (rr σ) (isRoundRobin_rr σ) (cfg 0 w σ 0) trivial adv hlegal
  have := hT T le_rfl
  rw [hcyc T (Nat.zero_le T)] at this
  exact cfg_not_gathered hn huv σ T this

/-- **Theorem 1** of [Frei–Wada] (cf. Défago et al., Thm. 14): Gathering under Round-Robin is
infeasible for `n ≥ 3` robots, even if they share a consistent unit length. Stated for every
movement model (rigid or non-rigid). -/
theorem theorem_1 (hn : 3 ≤ n) (A : Algorithm) (M : Movement) :
    ¬ Solves n A IsRoundRobin Frame.UnitLength M (fun _ => True) :=
  theorem_1_general hn A (fun _ _ h => h) M

/-- Theorem 1 in the default model (variable disorientation): a fortiori. -/
theorem theorem_1_default (hn : 3 ≤ n) (A : Algorithm) (M : Movement) :
    ¬ Solves n A IsRoundRobin (fun _ => True) M (fun _ => True) :=
  theorem_1_general hn A (fun _ _ _ => trivial) M

/-! ### Theorem 4 -/

/-- If an algorithm solves Distinct Gathering of `3` robots, then in some distinct configuration
some robot, with some allowed frame, jumps exactly onto another robot. -/
lemma exists_merge {A : Algorithm} {frameOK : Frame → Prop} (hid : frameOK Frame.id)
    {M : Movement} (hS : Solves 3 A IsRoundRobin frameOK M Function.Injective) :
    ∃ C : Config 3, Function.Injective C ∧ ∃ x f, frameOK f ∧ ∃ y, y ≠ x ∧
      step A C x f 1 x = C y := by
  by_contra hno
  push Not at hno
  set adv : Adversary 3 := Adversary.rigidOf fun _ _ => Frame.id
  set P₀ : Config 3 := ![0, 1, 2]
  have hP₀ : Function.Injective P₀ := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [P₀]
  have hinj : ∀ t, Function.Injective (run A (rr 1) adv P₀ t) := by
    intro t
    induction t with
    | zero => exact hP₀
    | succ t ih =>
      rw [run_succ]
      set P := run A (rr 1) adv P₀ t
      show Function.Injective (step A P (rr 1 t) Frame.id 1)
      have hne := hno P ih (rr 1 t) Frame.id hid
      intro a b hab
      by_contra hab'
      have key : ∀ c, c ≠ rr 1 t → step A P (rr 1 t) Frame.id 1 c = P c :=
        fun c hc => step_apply_ne A P _ _ hc
      by_cases ha : a = rr 1 t
      · subst ha
        have hb : b ≠ rr 1 t := Ne.symm hab'
        exact hne b hb (by rw [hab, key b hb])
      · by_cases hb : b = rr 1 t
        · subst hb
          exact hne a ha (by rw [← hab, key a ha])
        · exact hab' (ih (by rw [← key a ha, ← key b hb]; exact hab))
  obtain ⟨T, hT⟩ := hS (rr 1) (isRoundRobin_rr 1) P₀ hP₀ adv
    (legal_rigidOf _ _ _ _ _ fun _ _ => hid)
  exact absurd (hinj T (hT T le_rfl 0 1)) (by decide)

lemma exists_perm_fin3 (x y : Fin 3) (h : x ≠ y) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = x ∧ σ 1 = y := by
  fin_cases x <;> fin_cases y <;> simp at h
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨Equiv.swap 1 2, rfl, rfl⟩
  · exact ⟨Equiv.swap 0 1, rfl, rfl⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 1 2, rfl, rfl⟩
  · exact ⟨Equiv.swap 1 2 * Equiv.swap 0 1, rfl, rfl⟩
  · exact ⟨Equiv.swap 0 2, rfl, rfl⟩

/-- Theorem 4 of [Frei–Wada], general form: no algorithm solves Distinct Gathering of `3` robots
under Round-Robin, for any frame restriction that allows all orientation-preserving similarities
(rotations and scalings), and any movement model. -/
theorem theorem_4_general (A : Algorithm) {frameOK : Frame → Prop}
    (hframe : ∀ a (ha : a ≠ 0), frameOK (Frame.ofCoef a ha)) (M : Movement) :
    ¬ Solves 3 A IsRoundRobin frameOK M Function.Injective := by
  intro hS
  have hid : frameOK Frame.id := hframe 1 one_ne_zero
  -- a two-point view answered by jumping onto the other point
  obtain ⟨w, hw, hA⟩ := exists_fixed_view hid hS (isRoundRobin_rr 1) (P₀ := ![0, 1, 2])
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
    (fun h => by have := h 0 1; norm_num at this)
  -- a distinct configuration in which `x` jumps onto `y`
  obtain ⟨C, hC, x, f, hf, y, hyx, hxy⟩ := exists_merge hid hS
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_fin3 x y (Ne.symm hyx)
  set z := σ 2
  have hzy : z ≠ y := by rw [← hσ1]; exact fun h => absurd (σ.injective h) (by decide)
  have hzx : z ≠ x := by rw [← hσ0]; exact fun h => absurd (σ.injective h) (by decide)
  -- the swapping execution on `u = C z`, `v = C y`, after the first move of `x`
  have huv : C z ≠ C y := fun h => hzy (hC h)
  set adv : Adversary 3 := Adversary.rigidOf fun t P =>
    if t = 0 then f else normFrame (C z) (C y) w huv hw (P (rr σ t))
  have hrr0 : rr σ 0 = x := by simp [rr, ← hσ0]
  have h1 : run A (rr σ) adv C 1 = cfg (C z) (C y) σ 1 := by
    rw [run_succ, run_zero, hrr0]
    show step A C x f 1 = _
    funext j
    have hs : ∀ i, side σ 1 (σ i) = (decide ((i : ℕ) = 1) ^^ decide ((i : ℕ) < 1)) := by
      intro i; simp [side]
    by_cases hjx : j = x
    · subst hjx; rw [hxy, cfg, ← hσ0, hs]; simp
    · rw [step_apply_ne A C f 1 hjx]
      by_cases hjy : j = y
      · subst hjy; rw [cfg, ← hσ1, hs]; simp
      · have hjz : j = z := by
          have : ∀ k : Fin 3, k = σ 0 ∨ k = σ 1 ∨ k = σ 2 := by
            intro k
            obtain ⟨i, rfl⟩ := σ.surjective k
            fin_cases i <;> simp
          rcases this j with h | h | h
          · exact absurd (h.trans hσ0) hjx
          · exact absurd (h.trans hσ1) hjy
          · exact h
        subst hjz; rw [cfg, hs]; simp
  have hcyc := run_cycle le_rfl hw hA huv σ adv C 1
    (fun t ht P => ⟨by simp [adv, Adversary.rigidOf, show t ≠ 0 by omega], rfl⟩) h1
  have hlegal : Legal A (rr σ) adv C frameOK M := by
    intro t
    refine ⟨?_, M.admissible_one _⟩
    show frameOK (if t = 0 then f else _)
    split_ifs
    · exact hf
    · exact hframe _ _
  obtain ⟨T, hT⟩ := hS (rr σ) (isRoundRobin_rr σ) C hC adv hlegal
  have hg := hT (T + 1) (by omega)
  rw [hcyc (T + 1) (by omega)] at hg
  exact cfg_not_gathered le_rfl huv σ (T + 1) hg

/-- **Theorem 4** of [Frei–Wada]: Distinct Gathering under Round-Robin is impossible for `n = 3`
robots under the default assumptions (variable disorientation: the adversary may scale, rotate
and mirror each robot's frame at each activation). Stated for every movement model (rigid or
non-rigid). -/
theorem theorem_4 (A : Algorithm) (M : Movement) :
    ¬ Solves 3 A IsRoundRobin (fun _ => True) M Function.Injective :=
  theorem_4_general A (fun _ _ => trivial) M

/-- Theorem 4 holds even if all robots share the same handedness (chirality). -/
theorem theorem_4_chiral (A : Algorithm) (M : Movement) :
    ¬ Solves 3 A IsRoundRobin Frame.Chiral M Function.Injective :=
  theorem_4_general A (fun _ _ => rfl) M

end Podc.DistinctGathering

end
