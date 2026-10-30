import Podc.Computability.Distributed.MobileRobots.Model

/-!
# Two-point configurations and the swapping execution

Common core of the impossibility proofs of Theorems 1 and 4 of
[Frei–Wada, *Distinct Gathering and the Virtue of Self-Consistency*, PODC 2026].

* `exists_fixed_view`: if an algorithm gathers in *some* execution with the global frame, then for
  some `w ≠ 0` a robot seeing the view `{0, w}` moves exactly to `w`, i.e. onto the other point.
* `step_normFrame`: in a configuration on two points `u ≠ v`, an adversary that rotates and
  scales the frame so that the other point is seen at `w` makes the activated robot jump onto the
  other point. With `‖v - u‖ = ‖w‖` the frames are pure rotations (consistent unit length).
* `run_cycle`: the "swapping" execution. Under the Round-Robin order `σ 0, σ 1, …, σ (n-1)`
  with `n ≥ 3`, starting from `σ 1` alone at one point and everyone else at the other, the robots
  keep swapping sides forever; the activated robot is never alone, so the configuration always
  has two points (`cfg_not_gathered`). The closed form: robot `σ i` is at `v` at time `t` iff
  `[i = 1] xor [⌊t/n⌋ odd] xor [i < t mod n]`.
-/

noncomputable section

namespace Podc.DistinctGathering

open Cslib.MobileRobots

variable {n : ℕ}

/-! ### Round-Robin schedules -/

/-- The Round-Robin schedule activating `σ 0, σ 1, …, σ (n-1), σ 0, …`. -/
def rr [NeZero n] (σ : Equiv.Perm (Fin n)) (t : ℕ) : Fin n :=
  σ ⟨t % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

lemma isRoundRobin_rr [NeZero n] (σ : Equiv.Perm (Fin n)) : IsRoundRobin (rr σ) := by
  refine ⟨fun t => ?_, fun i j hi hj h => ?_⟩
  · simp [rr]
  · have := congrArg Fin.val (σ.injective h)
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this

/-! ### A two-point view that is answered by moving onto the other point -/

lemma view_of_all_eq (P : Config n) (r j : Fin n) (_hj : j ≠ r) (hP : ∀ i, i ≠ r → P i = P j)
    (f : Frame) : view P r f = {0, f.toLocal (P j - P r)} := by
  ext z
  simp only [view, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i = r
    · left; simp [hi]
    · right; rw [hP i hi]
  · rintro (rfl | rfl)
    · exact ⟨r, by simp⟩
    · exact ⟨j, rfl⟩

/-- If an algorithm achieves gathering in some execution with the global frame and rigid moves
(which every legal adversary may use), some two-point view `{0, w}` makes the robot move exactly
to `w`. -/
lemma exists_fixed_view {A : Algorithm} {frameOK : Frame → Prop} (hid : frameOK Frame.id)
    {M : Movement} {init : Config n → Prop} (hS : Solves n A IsRoundRobin frameOK M init)
    {act : ℕ → Fin n} (hact : IsRoundRobin act) {P₀ : Config n} (hP₀ : init P₀)
    (hng : ¬ Gathered P₀) : ∃ w, w ≠ 0 ∧ A {0, w} 1 = w := by
  classical
  set adv : Adversary n := Adversary.rigidOf fun _ _ => Frame.id
  obtain ⟨T, hT⟩ := hS act hact P₀ hP₀ adv (legal_rigidOf _ _ _ _ _ fun _ _ => hid)
  have hex : ∃ t, Gathered (run A act adv P₀ t) := ⟨T, hT T le_rfl⟩
  set t := Nat.find hex with ht
  have hgt : Gathered (run A act adv P₀ t) := Nat.find_spec hex
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0] at hgt; exact hng hgt
  obtain ⟨t', ht'⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  have hng' : ¬ Gathered (run A act adv P₀ t') := Nat.find_min hex (by omega)
  rw [ht', run_succ] at hgt
  set P := run A act adv P₀ t'
  obtain ⟨hothers, hland⟩ := first_gather A hng' hgt
  set r := act t'
  -- some robot other than `r`
  obtain ⟨j, hj⟩ : ∃ j, j ≠ r := by
    by_contra h
    push Not at h
    exact hng' fun a b => by rw [h a, h b]
  obtain ⟨hl, hne⟩ := hland j hj
  have hview := view_of_all_eq P r j hj (fun i hi => hothers i j hi hj) Frame.id
  refine ⟨P j - P r, sub_ne_zero.2 (Ne.symm hne), ?_⟩
  rw [step_apply_self] at hl
  have hf : adv.frame t' P = Frame.id := rfl
  have hs : adv.stop t' P = 1 := rfl
  rw [hf, hs, hview] at hl
  simp only [Frame.id, Frame.ofCoef_toLocal, one_mul, Frame.ofCoef_toGlobal, div_one] at hl
  linear_combination hl

/-! ### Normalizing frames on two points -/

/-- Among the two points `u, v`, the one different from `p` (if `p ∈ {u, v}`). -/
def other (u v p : ℂ) : ℂ := if p = u then v else u

lemma other_sub_ne {u v : ℂ} (huv : u ≠ v) (p : ℂ) : other u v p - p ≠ 0 := by
  unfold other; split_ifs with h
  · subst h; exact sub_ne_zero.2 (Ne.symm huv)
  · exact sub_ne_zero.2 (Ne.symm h)

/-- The orientation-preserving frame in which the other point is seen at `w`. -/
def normFrame (u v w : ℂ) (huv : u ≠ v) (hw : w ≠ 0) (p : ℂ) : Frame :=
  Frame.ofCoef (w / (other u v p - p)) (div_ne_zero hw (other_sub_ne huv p))

lemma step_normFrame {A : Algorithm} {w : ℂ} (hw : w ≠ 0) (hA : A {0, w} 1 = w) {u v : ℂ}
    (huv : u ≠ v) {P : Config n} {r : Fin n} (hP : ∀ j, P j = u ∨ P j = v)
    (hocc : ∃ j, P j = other u v (P r)) :
    step A P r (normFrame u v w huv hw (P r)) 1 = Function.update P r (other u v (P r)) := by
  classical
  have hne := other_sub_ne huv (P r)
  have key : ∀ j, P j = P r ∨ P j = other u v (P r) := by
    intro j
    simp only [other]
    rcases hP j with h | h <;> rcases hP r with h' | h' <;> simp_all
  have hview : view P r (normFrame u v w huv hw (P r)) = {0, w} := by
    ext z
    simp only [view, normFrame, Frame.ofCoef_toLocal, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, rfl⟩
      rcases key j with h | h
      · left; simp [h]
      · right; rw [h]; field_simp
    · rintro (rfl | rfl)
      · exact ⟨r, by simp⟩
      · obtain ⟨j, hj⟩ := hocc
        exact ⟨j, by rw [hj]; field_simp⟩
  unfold step globalTraj
  rw [hview, hA]
  congr 1
  simp only [normFrame, Frame.ofCoef_toGlobal]
  field_simp
  ring

/-! ### The swapping execution -/

/-- Side of robot `j` at time `t` in the swapping execution (`true`: at `v`). -/
def side [NeZero n] (σ : Equiv.Perm (Fin n)) (t : ℕ) (j : Fin n) : Bool :=
  (decide ((σ.symm j : ℕ) = 1) ^^ decide (t / n % 2 = 1)) ^^ decide ((σ.symm j : ℕ) < t % n)

/-- Configuration of the swapping execution at time `t`. -/
def cfg [NeZero n] (u v : ℂ) (σ : Equiv.Perm (Fin n)) (t : ℕ) : Config n :=
  fun j => if side σ t j then v else u

lemma side_succ [NeZero n] (σ : Equiv.Perm (Fin n)) (t : ℕ) :
    side σ (t + 1) = Function.update (side σ t) (rr σ t) (!side σ t (rr σ t)) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  funext j
  set i := σ.symm j with hi
  have hj : j = σ i := by simp [hi]
  have hmod := Nat.mod_lt t hn
  -- arithmetic of `t + 1`
  have hdm : (t + 1) / n = (if t % n + 1 = n then t / n + 1 else t / n) ∧
      (t + 1) % n = (if t % n + 1 = n then 0 else t % n + 1) := by
    rw [Nat.div_mod_unique hn]
    have := Nat.div_add_mod t n
    split_ifs with h
    · refine ⟨?_, hn⟩
      rw [Nat.mul_add]; omega
    · exact ⟨by omega, by omega⟩
  by_cases hji : j = rr σ t
  · subst hji
    simp only [Function.update_self, side, rr, Equiv.symm_apply_apply]
    rw [hdm.1, hdm.2]
    split_ifs with h
    · have h1 : t % n = n - 1 := by omega
      simp only [Nat.lt_irrefl, decide_false, Bool.xor_false, Nat.not_lt_zero]
      rw [Nat.add_mod]
      rcases Nat.mod_two_eq_zero_or_one (t / n) with h2 | h2 <;> simp [h2]
    · simp
  · rw [Function.update_of_ne hji]
    have hik : (i : ℕ) ≠ t % n := by
      intro h; apply hji; rw [hj]; simp only [rr]; congr 1; ext; simp [h]
    simp only [side, ← hi]
    rw [hdm.1, hdm.2]
    split_ifs with h
    · have hlt : (i : ℕ) < t % n := by have := i.isLt; omega
      simp only [hlt, decide_true, Nat.not_lt_zero, decide_false, Bool.xor_false, Bool.xor_true]
      rw [Nat.add_mod]
      rcases Nat.mod_two_eq_zero_or_one (t / n) with h2 | h2 <;> simp [h2]
    · have : ((i : ℕ) < t % n + 1) ↔ ((i : ℕ) < t % n) := by omega
      simp [this]

/-- In the swapping execution both sides are always occupied (`n ≥ 3`). -/
lemma side_surj [NeZero n] (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n)) (t : ℕ) (b : Bool) :
    ∃ j, side σ t j = b := by
  have key : ∀ i : Fin n, side σ t (σ i) =
      ((decide ((i : ℕ) = 1) ^^ decide (t / n % 2 = 1)) ^^ decide ((i : ℕ) < t % n)) := by
    intro i; simp [side]
  have h0 := key ⟨0, by omega⟩
  have h1 := key ⟨1, by omega⟩
  have h2 := key ⟨2, by omega⟩
  simp only at h0 h1 h2
  by_contra hne
  push Not at hne
  have e0 := hne (σ ⟨0, by omega⟩)
  have e1 := hne (σ ⟨1, by omega⟩)
  have e2 := hne (σ ⟨2, by omega⟩)
  rw [h0] at e0
  rw [h1] at e1
  rw [h2] at e2
  rcases Nat.mod_two_eq_zero_or_one (t / n) with hp | hp <;> cases b <;>
    simp [hp] at e0 e1 e2 <;> omega

lemma cfg_not_gathered [NeZero n] (hn : 3 ≤ n) {u v : ℂ} (huv : u ≠ v) (σ : Equiv.Perm (Fin n))
    (t : ℕ) : ¬ Gathered (cfg u v σ t) := by
  intro h
  obtain ⟨i, hi⟩ := side_surj hn σ t true
  obtain ⟨j, hj⟩ := side_surj hn σ t false
  have := h i j
  simp [cfg, hi, hj] at this
  exact huv this.symm

lemma cfg_mem [NeZero n] (u v : ℂ) (σ : Equiv.Perm (Fin n)) (t : ℕ) (j : Fin n) :
    cfg u v σ t j = u ∨ cfg u v σ t j = v := by
  unfold cfg; split_ifs <;> simp

lemma other_cfg [NeZero n] {u v : ℂ} (huv : u ≠ v) (σ : Equiv.Perm (Fin n)) (t : ℕ) (j : Fin n) :
    other u v (cfg u v σ t j) = if !side σ t j then v else u := by
  unfold cfg other
  cases side σ t j <;> simp [Ne.symm huv]

/-- **The swapping execution.** If from time `t₀` on the adversary uses the normalizing frames
and rigid moves, and the configuration at `t₀` is the swapping configuration, then it stays the
swapping configuration forever. -/
lemma run_cycle [NeZero n] (hn : 3 ≤ n) {A : Algorithm} {w : ℂ} (hw : w ≠ 0)
    (hA : A {0, w} 1 = w) {u v : ℂ} (huv : u ≠ v) (σ : Equiv.Perm (Fin n)) (adv : Adversary n)
    (P₀ : Config n) (t₀ : ℕ)
    (hadv : ∀ t, t₀ ≤ t → ∀ P : Config n,
      adv.frame t P = normFrame u v w huv hw (P (rr σ t)) ∧ adv.stop t P = 1)
    (h₀ : run A (rr σ) adv P₀ t₀ = cfg u v σ t₀) :
    ∀ t, t₀ ≤ t → run A (rr σ) adv P₀ t = cfg u v σ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h₀
  | succ t ht ih =>
    rw [run_succ, ih, (hadv t ht _).1, (hadv t ht _).2]
    rw [step_normFrame hw hA huv (cfg_mem u v σ t)]
    · funext j
      rw [other_cfg huv]
      simp only [cfg]
      rw [side_succ]
      by_cases hj : j = rr σ t
      · subst hj; simp
      · simp [Function.update_of_ne hj, cfg]
    · rw [other_cfg huv]
      obtain ⟨j, hj⟩ := side_surj hn σ t (!side σ t (rr σ t))
      exact ⟨j, by simp [cfg, hj]⟩

end Podc.DistinctGathering

end
