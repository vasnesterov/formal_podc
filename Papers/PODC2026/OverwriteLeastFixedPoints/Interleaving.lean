import Papers.PODC2026.OverwriteLeastFixedPoints.Basic

/-!
# Section 2: interleaving semantics (Theorems 2.1/1 and 2)

The execution is `G (t+1) = f (σ t) (G t)` for a schedule `σ : ℕ → ι`.

* `converges_from`: from an arbitrary start `G 0`, a fair execution of monotone inflationary functions
  on a poset without infinite ascending chains terminates at the least common fixed point above `G 0`
  (the paper states this in the proof of Theorem 2 and uses it for the transitive-closure example,
  which starts from `R₀ ≠ ⊥`).
* `theorem_2_1`: Theorem 2.1 (BA) / Theorem 1 (full version), start `⊥`, finite `L`.
* `theorem_2_*`: the counterexamples of Theorem 2 (one per dropped assumption).
* `fixedPoints_not_supClosed`: the paper's remark that the fixed points of each `fᵢ` form a
  sublattice is false (they are only closed under meets, `isCommonFixed_inf`).
* `corollary_4_1`: greatest common fixed points via the order dual.
-/

namespace Podc.OverwriteLeastFixedPoints

variable {L ι : Type*}

section General

variable [PartialOrder L]

/-- The interleaved execution: at step `t` the scheduler picks `σ t` and `G (t+1) = f (σ t) (G t)`. -/
def IsInterleavedExec (f : ι → L → L) (σ : ℕ → ι) (G : ℕ → L) : Prop :=
  ∀ t, G (t + 1) = f (σ t) (G t)

/-- Convergence from an arbitrary initial state: the execution terminates at the least common
fixed point above `G 0`. -/
theorem converges_from [WellFoundedGT L] {f : ι → L → L} (hm : ∀ i, Monotone (f i))
    (hinf : ∀ i, Inflationary (f i)) {σ : ℕ → ι} (hσ : FairSeq σ) {G : ℕ → L}
    (hG : IsInterleavedExec f σ G) :
    ∃ x, TerminatesAt G x ∧ IsLeast {y | IsCommonFixed f y ∧ G 0 ≤ y} x := by
  have hmono : Monotone G := monotone_nat_of_le_succ fun t => by rw [hG t]; exact hinf _ _
  obtain ⟨T, hT⟩ := exists_terminatesAt_of_monotone hmono
  refine ⟨G T, ⟨T, hT⟩, ⟨?_, hmono (Nat.zero_le _)⟩, ?_⟩
  · intro i
    obtain ⟨t, ht, hti⟩ := hσ i T
    have h1 := hT (t + 1) (by omega)
    rw [hG t, hti, hT t ht] at h1
    exact h1
  · rintro y ⟨hy, h0⟩
    have : ∀ t, G t ≤ y := by
      intro t
      induction t with
      | zero => exact h0
      | succ t ih => rw [hG t, ← hy (σ t)]; exact hm _ ih
    exact this T

/-- **Theorem 2.1** of [Garg–Garg, BA] (= Theorem 1 of the full version). Let `L` be a finite
poset with bottom (in the paper: a finite lattice `L ⊆ ℕⁿ`) and `f i` monotone inflationary. An
execution starting from `⊥` that applies, at each step, the function chosen by a fair scheduler
terminates at the least common fixed point. -/
theorem theorem_2_1 [Finite L] [OrderBot L] {f : ι → L → L} (hm : ∀ i, Monotone (f i))
    (hinf : ∀ i, Inflationary (f i)) {σ : ℕ → ι} (hσ : FairSeq σ) {G : ℕ → L}
    (h0 : G 0 = ⊥) (hG : IsInterleavedExec f σ G) :
    ∃ x, TerminatesAt G x ∧ IsLeast {y | IsCommonFixed f y} x := by
  obtain ⟨x, hx, hl⟩ := converges_from hm hinf hσ hG
  refine ⟨x, hx, hl.1.1, fun y hy => hl.2 ⟨hy, by rw [h0]; exact bot_le⟩⟩

end General

/-! ## Theorem 2: each assumption of Theorem 2.1 is needed -/

/-- Theorem 2, finiteness: on `ℕ` (infinite, with bottom `0`) the single function `x ↦ x + 1` is
monotone and inflationary, every schedule is fair, but the execution from `⊥` never terminates and
there is no common fixed point. -/
theorem theorem_2_finite :
    let f : Unit → ℕ → ℕ := fun _ x => x + 1
    let σ : ℕ → Unit := fun _ => ()
    let G : ℕ → ℕ := fun t => t
    (∀ i, Monotone (f i)) ∧ (∀ i, Inflationary (f i)) ∧ FairSeq σ ∧ G 0 = ⊥ ∧
      IsInterleavedExec f σ G ∧ (∀ x, ¬ TerminatesAt G x) ∧ (∀ x, ¬ IsCommonFixed f x) := by
  intro f σ G
  refine ⟨fun _ a b h => by simp [f]; omega, fun _ x => by simp [f], fun i N => ⟨N, le_rfl, rfl⟩,
    rfl, fun t => rfl, ?_, fun x h => by simpa [f] using h ()⟩
  rintro x ⟨T, hT⟩
  have h1 := hT (T + x + 1) (by omega)
  simp [G] at h1
  omega

/-- Theorem 2, fairness: on `Bool × Bool` with `f₀ (x₁, x₂) = (1, x₂)`, `f₁ (x₁, x₂) = (x₁, 1)`, the
unfair schedule applying only `f₀` terminates at `(1, 0)`, which is not a common fixed point. -/
theorem theorem_2_fair :
    let f : Bool → Bool × Bool → Bool × Bool := fun i x => if i then (x.1, true) else (true, x.2)
    let σ : ℕ → Bool := fun _ => false
    let G : ℕ → Bool × Bool := fun t => if t = 0 then (false, false) else (true, false)
    (∀ i, Monotone (f i)) ∧ (∀ i, Inflationary (f i)) ∧ G 0 = ⊥ ∧ IsInterleavedExec f σ G ∧
      TerminatesAt G (true, false) ∧ ¬ IsCommonFixed f (true, false) ∧ ¬ FairSeq σ := by
  intro f σ G
  refine ⟨?_, ?_, rfl, fun t => by by_cases h : t = 0 <;> simp [G, f, σ, h], ⟨1, fun t ht => by simp [G]; omega⟩,
    fun h => by simpa [f] using h true, fun h => by obtain ⟨t, -, ht⟩ := h true 0; simp [σ] at ht⟩
  · rintro (_ | _) ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨h1, h2⟩ <;> simp_all [f, Prod.le_def]
  · rintro (_ | _) ⟨a1, a2⟩ <;> simp [f, Prod.le_def]

/-- Theorem 2, the start state `⊥`: on `Bool` with the single function `id`, the (fair) execution
starting from `⊤ ≠ ⊥` terminates at `true`, a common fixed point that is not the least one. -/
theorem theorem_2_bot :
    let f : Unit → Bool → Bool := fun _ x => x
    let σ : ℕ → Unit := fun _ => ()
    let G : ℕ → Bool := fun _ => true
    (∀ i, Monotone (f i)) ∧ (∀ i, Inflationary (f i)) ∧ FairSeq σ ∧ IsInterleavedExec f σ G ∧
      TerminatesAt G true ∧ IsCommonFixed f true ∧ ¬ IsLeast {y | IsCommonFixed f y} true := by
  intro f σ G
  refine ⟨fun _ => monotone_id, fun _ _ => le_rfl, fun i N => ⟨N, le_rfl, rfl⟩, fun _ => rfl,
    ⟨0, fun _ _ => rfl⟩, fun _ => rfl, fun h => ?_⟩
  exact absurd (h.2 (show IsCommonFixed f false from fun _ => rfl)) (by decide)

/-- The two functions of the monotonicity counterexample of Theorem 2, on `L = {0,1,2}`:
`f₀ = (0 ↦ 2, 1 ↦ 1, 2 ↦ 2)` (not monotone) and `f₁ = (0 ↦ 1, 1 ↦ 1, 2 ↦ 2)`. -/
def monoCexF : Bool → Fin 3 → Fin 3
  | false, x => if x = 1 then 1 else 2
  | true, x => if x = 2 then 2 else 1

/-- Theorem 2, monotonicity: with `monoCexF` and the fair alternating schedule `f₀, f₁, f₀, …`, the
execution from `⊥ = 0` terminates at `2`, a common fixed point, while the least common fixed point
is `1`. Here `f₀` is inflationary but not monotone; `f₁` is monotone and inflationary. -/
theorem theorem_2_monotone :
    let σ : ℕ → Bool := fun t => decide (t % 2 = 1)
    let G : ℕ → Fin 3 := fun t => if t = 0 then 0 else 2
    Monotone (monoCexF true) ∧ ¬ Monotone (monoCexF false) ∧ (∀ i, Inflationary (monoCexF i)) ∧
      FairSeq σ ∧ G 0 = ⊥ ∧ IsInterleavedExec monoCexF σ G ∧ TerminatesAt G 2 ∧
      IsCommonFixed monoCexF 2 ∧ IsLeast {y | IsCommonFixed monoCexF y} 1 := by
  intro σ G
  refine ⟨by decide, fun h => absurd (h (show (0 : Fin 3) ≤ 1 by decide)) (by decide),
    by unfold Inflationary; decide, ?_, rfl, ?_, ⟨1, fun t ht => by simp [G]; omega⟩, by
      unfold IsCommonFixed; decide, ?_⟩
  · intro i N
    cases i
    · exact ⟨2 * N, by omega, by simp [σ]⟩
    · exact ⟨2 * N + 1, by omega, by simp [σ]⟩
  · intro t
    rcases t with _ | t
    · rfl
    · show (2 : Fin 3) = monoCexF (σ (t + 1)) 2
      cases σ (t + 1) <;> rfl
  · refine ⟨by unfold IsCommonFixed; decide, fun y hy => ?_⟩
    simp only [Set.mem_ofPred_eq, IsCommonFixed] at hy
    have := hy false
    revert this
    revert y
    decide

/-- Theorem 2, inflationarity: on `Bool`, `f₀ = const 0` (monotone, not inflationary) and
`f₁ = const 1`; the fair alternating execution from `⊥` toggles forever and there is no common fixed
point. -/
theorem theorem_2_inflationary :
    let f : Bool → Bool → Bool := fun i _ => i
    let σ : ℕ → Bool := fun t => decide (t % 2 = 0)
    let G : ℕ → Bool := fun t => decide (t % 2 = 1)
    (∀ i, Monotone (f i)) ∧ Inflationary (f true) ∧ ¬ Inflationary (f false) ∧ FairSeq σ ∧
      G 0 = ⊥ ∧ IsInterleavedExec f σ G ∧ (∀ x, ¬ TerminatesAt G x) ∧
      (∀ x, ¬ IsCommonFixed f x) := by
  intro f σ G
  refine ⟨fun _ => monotone_const, fun x => le_top, fun h => absurd (h true) (by decide), ?_, rfl,
    fun t => by simp [G, f, σ]; omega, ?_, fun x h => by have := h true; have := h false; simp_all [f]⟩
  · intro i N
    cases i
    · exact ⟨2 * N + 1, by omega, by simp [σ]⟩
    · exact ⟨2 * N, by omega, by simp [σ]⟩
  · rintro x ⟨T, hT⟩
    have h1 := hT T le_rfl
    have h2 := hT (T + 1) (by omega)
    simp only [G] at h1 h2
    rw [← h2] at h1
    simp at h1
    omega

/-! ## The "sublattice" remark -/

/-- The paper observes (before Theorem 2.1) that "the set of fixed points for each of the functions
`fᵢ` is a sublattice of `L`". This is false even for one monotone inflationary function on the
finite distributive lattice `{0,1,2}²`: `f x = if (1,1) ≤ x then ⊤ else x` fixes `(1,0)` and `(0,1)`
but not their join `(1,1)`. (The fixed points are closed under meets, `isCommonFixed_inf`, which is
all the definition of the least common fixed point needs.) -/
theorem fixedPoints_not_supClosed :
    let f : Fin 3 × Fin 3 → Fin 3 × Fin 3 := fun x => if (1, 1) ≤ x then (2, 2) else x
    Monotone f ∧ Inflationary f ∧ f (1, 0) = (1, 0) ∧ f (0, 1) = (0, 1) ∧
      f ((1, 0) ⊔ (0, 1)) ≠ (1, 0) ⊔ (0, 1) := by
  intro f
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · intro x y h
    simp only [f]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (h1.trans h) h2
    · exact le_top
    · exact h
  · intro x
    simp only [f]
    split_ifs
    · exact le_top
    · exact le_rfl

/-! ## Section 5: greatest common fixed points -/

/-- **Corollary 4.1** of [Garg–Garg] (interleaving version): for deflationary monotone functions on
a finite poset with top, a fair execution starting from `⊤` terminates at the greatest common fixed
point. (Proof: Theorem 2.1 on the order dual.) -/
theorem corollary_4_1 [PartialOrder L] [Finite L] [OrderTop L] {f : ι → L → L}
    (hm : ∀ i, Monotone (f i)) (hdef : ∀ i, Deflationary (f i)) {σ : ℕ → ι} (hσ : FairSeq σ)
    {G : ℕ → L} (h0 : G 0 = ⊤) (hG : IsInterleavedExec f σ G) :
    ∃ x, TerminatesAt G x ∧ IsGreatest {y | IsCommonFixed f y} x := by
  have := theorem_2_1 (L := Lᵒᵈ) (f := fun i x => OrderDual.toDual (f i (OrderDual.ofDual x)))
    (fun i => (hm i).dual) (fun i x => hdef i (OrderDual.ofDual x)) hσ
    (G := fun t => OrderDual.toDual (G t)) (by simp [h0]) (fun t => by simp [hG t])
  exact this
end Podc.OverwriteLeastFixedPoints
