import Papers.PODC2025.RendezvousLabeledLine.LocalBasic

/-!
# The greedy extension step of Algorithms 2 and 3

Given a set `Q` and a set `U` of candidates, one greedy step adds every candidate `v ∈ U` that is
at distance `≥ R` from `Q` (`b_v ≥ R`, where `b_v` is the distance to `Q`) and whose `b_v` is
maximal among the candidates at distance `≤ R - 1` from `v` that are also at distance `≥ R`
from `Q`, ties broken by labels (Algorithm 2, lines 6–8; Algorithm 3, lines 7–9).

Distances to `Q` are truncated at `M` (`tdist`), which keeps the step local; as long as every
candidate is within `M` of `Q` this changes nothing.

Main facts (`gIter_spec`): if `Q` is `R`-packed and every candidate is within `B` of `Q`, then the
greedy steps keep `Q` `R`-packed, and after `5` steps (if `B ≤ 3R - 3`, Algorithm 2) or `3` steps
(if `B ≤ 2R - 2`, Algorithm 3) every candidate is within `R - 1` of the current set.
-/

namespace Podc.RendezvousLabeledLine

open Function Classical

/-- Distance from `v` to `Q`, truncated at `M`. -/
noncomputable def tdist (Q : ℤ → Prop) (M : ℕ) (v : ℤ) : ℕ :=
  sInf {r : ℕ | r = M ∨ ∃ q, Q q ∧ |v - q| ≤ (r : ℤ)}

/-- `v` is added by the greedy step. -/
def gAdd (U Q : ℤ → Prop) (lab : ℤ → ℕ) (R M : ℕ) (v : ℤ) : Prop :=
  U v ∧ R ≤ tdist Q M v ∧ ∀ u, u ≠ v → |u - v| ≤ (R : ℤ) - 1 → U u → R ≤ tdist Q M u →
    tdist Q M u < tdist Q M v ∨ (tdist Q M u = tdist Q M v ∧ lab u < lab v)

/-- One greedy step. -/
def gStep (U Q : ℤ → Prop) (lab : ℤ → ℕ) (R M : ℕ) : ℤ → Prop :=
  fun v => Q v ∨ gAdd U Q lab R M v

/-- `m` greedy steps. -/
def gIter (U Q : ℤ → Prop) (lab : ℤ → ℕ) (R M : ℕ) : ℕ → ℤ → Prop
  | 0 => Q
  | m + 1 => gStep U (gIter U Q lab R M m) lab R M

/-! ### Truncated distance -/

section tdist

variable {P P' : ℤ → Prop} {M : ℕ} {x q : ℤ} {r : ℕ}

lemma tdist_le_M (P : ℤ → Prop) (M : ℕ) (x : ℤ) : tdist P M x ≤ M :=
  Nat.sInf_le (Or.inl rfl)

lemma tdist_le_of (hq : P q) (h : |x - q| ≤ (r : ℤ)) : tdist P M x ≤ r :=
  Nat.sInf_le (Or.inr ⟨q, hq, h⟩)

lemma tdist_le_abs (hq : P q) : (tdist P M x : ℤ) ≤ |x - q| := by
  have h2 : ((|x - q|.toNat : ℕ) : ℤ) = |x - q| := Int.toNat_of_nonneg (abs_nonneg _)
  have := tdist_le_of (M := M) (r := |x - q|.toNat) hq h2.ge
  omega

lemma tdist_mem (P : ℤ → Prop) (M : ℕ) (x : ℤ) :
    tdist P M x = M ∨ ∃ q, P q ∧ |x - q| ≤ (tdist P M x : ℤ) :=
  Nat.sInf_mem (s := {r : ℕ | r = M ∨ ∃ q, P q ∧ |x - q| ≤ (r : ℤ)}) ⟨M, Or.inl rfl⟩

lemma exists_near_of_lt (h : tdist P M x < M) : ∃ q, P q ∧ |x - q| ≤ (tdist P M x : ℤ) :=
  (tdist_mem P M x).resolve_left h.ne

lemma exists_eq_tdist (hq : P q) (h : |x - q| ≤ (M : ℤ)) :
    ∃ q, P q ∧ |x - q| = (tdist P M x : ℤ) := by
  rcases (tdist_le_M P M x).lt_or_eq with h1 | h1
  · obtain ⟨q', hq', h'⟩ := exists_near_of_lt h1
    exact ⟨q', hq', le_antisymm h' (tdist_le_abs hq')⟩
  · refine ⟨q, hq, le_antisymm ?_ (tdist_le_abs hq)⟩
    rw [h1]; exact h

lemma le_tdist_iff {R : ℕ} (hRM : R ≤ M) :
    R ≤ tdist P M x ↔ ∀ q, P q → (R : ℤ) - 1 < |x - q| := by
  constructor
  · intro h q hq
    have := tdist_le_abs (M := M) (x := x) hq
    omega
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, h'⟩ := exists_near_of_lt (lt_of_lt_of_le hlt hRM)
    have := h q hq
    omega

lemma tdist_anti (hPP : ∀ y, P y → P' y) : tdist P' M x ≤ tdist P M x := by
  rcases (tdist_le_M P M x).lt_or_eq with h1 | h1
  · obtain ⟨q, hq, h⟩ := exists_near_of_lt h1
    exact tdist_le_of (hPP q hq) h
  · rw [h1]; exact tdist_le_M _ _ _

lemma tdist_congr (h : ∀ y, |y - x| ≤ (M : ℤ) → (P y ↔ P' y)) :
    tdist P M x = tdist P' M x := by
  have key : ∀ P P' : ℤ → Prop, (∀ y, |y - x| ≤ (M : ℤ) → P y → P' y) →
      tdist P' M x ≤ tdist P M x := by
    intro P P' h
    rcases (tdist_le_M P M x).lt_or_eq with h1 | h1
    · obtain ⟨q, hq, h2⟩ := exists_near_of_lt h1
      exact tdist_le_of (h q (by rw [abs_sub_comm]; omega) hq) h2
    · rw [h1]; exact tdist_le_M _ _ _
  exact le_antisymm (key _ _ fun y hy => (h y hy).2) (key _ _ fun y hy => (h y hy).1)

end tdist

/-! ### Transport along isometries -/

lemma frame_surjective (v : ℤ) (ε : ℤˣ) : Surjective (frame v ε) := by
  intro y
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨y - v, by simp [frame]⟩
  · exact ⟨v - y, by simp [frame]⟩

lemma tdist_comp_frame (P : ℤ → Prop) (M : ℕ) (v : ℤ) (ε : ℤˣ) (i : ℤ) :
    tdist (P ∘ frame v ε) M i = tdist P M (frame v ε i) := by
  unfold tdist
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, comp]
  refine or_congr Iff.rfl ⟨fun ⟨q, hq, h⟩ => ⟨_, hq, by rwa [abs_frame_sub_frame]⟩,
    fun ⟨q, hq, h⟩ => ?_⟩
  obtain ⟨q', rfl⟩ := frame_surjective v ε q
  exact ⟨q', hq, by rwa [abs_frame_sub_frame] at h⟩

lemma gAdd_comp_frame (U P : ℤ → Prop) (lab : ℤ → ℕ) (R M : ℕ) (v : ℤ) (ε : ℤˣ) (i : ℤ) :
    gAdd (U ∘ frame v ε) (P ∘ frame v ε) (lab ∘ frame v ε) R M i ↔
      gAdd U P lab R M (frame v ε i) := by
  unfold gAdd
  simp only [tdist_comp_frame]
  rw [(frame_surjective v ε).forall (p := fun u => u ≠ frame v ε i → _)]
  simp only [comp, (frame_injective v ε).ne_iff, abs_frame_sub_frame]

lemma gIter_comp_frame (U Q : ℤ → Prop) (lab : ℤ → ℕ) (R M m : ℕ) (v : ℤ) (ε : ℤˣ) :
    gIter (U ∘ frame v ε) (Q ∘ frame v ε) (lab ∘ frame v ε) R M m =
      gIter U Q lab R M m ∘ frame v ε := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i
    simp only [gIter, gStep, ih]
    exact propext (or_congr Iff.rfl (gAdd_comp_frame _ _ _ _ _ _ _ _))

/-! ### Locality of one step -/

lemma gAdd_congr {U U' P P' : ℤ → Prop} {lab lab' : ℤ → ℕ} {R M : ℕ} {v : ℤ}
    (hU : ∀ y, |y - v| ≤ (R : ℤ) → (U y ↔ U' y))
    (hP : ∀ y, |y - v| ≤ (M : ℤ) + R → (P y ↔ P' y))
    (hl : ∀ y, |y - v| ≤ (R : ℤ) → lab y = lab' y) :
    gAdd U P lab R M v ↔ gAdd U' P' lab' R M v := by
  have ht : ∀ u, |u - v| ≤ (R : ℤ) → tdist P M u = tdist P' M u := by
    intro u hu
    refine tdist_congr fun y hy => hP y ?_
    have := abs_sub_le y u v
    omega
  have h0 : |v - v| ≤ (R : ℤ) := by simp
  unfold gAdd
  rw [hU v h0, ht v h0, hl v h0]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun u => ?_))
  refine imp_congr Iff.rfl (imp_congr_ctx Iff.rfl fun hu => ?_)
  have hu' : |u - v| ≤ (R : ℤ) := by omega
  rw [hU u hu', ht u hu', hl u hu']

/-! ### Invariants of the iteration -/

section iter

variable {U Q : ℤ → Prop} {lab : ℤ → ℕ} {R M : ℕ}

lemma gIter_mono {j m : ℕ} (hjm : j ≤ m) {x : ℤ} (h : gIter U Q lab R M j x) :
    gIter U Q lab R M m x := by
  induction hjm with
  | refl => exact h
  | step _ ih => exact Or.inl ih

lemma gIter_of_Q {m : ℕ} {x : ℤ} (h : Q x) : gIter U Q lab R M m x :=
  gIter_mono (Nat.zero_le m) h

lemma gIter_sub {m : ℕ} {x : ℤ} (h : gIter U Q lab R M m x) : Q x ∨ U x := by
  induction m generalizing x with
  | zero => exact Or.inl h
  | succ m ih =>
    rcases h with h | h
    · exact ih h
    · exact Or.inr h.1

lemma gIter_packed (hRM : R ≤ M) (hpack : Packed Q R) (m : ℕ) :
    Packed (gIter U Q lab R M m) R := by
  induction m with
  | zero => exact hpack
  | succ m ih =>
    intro u w hu hw huw
    rcases hu with hu | hu <;> rcases hw with hw | hw
    · exact ih u w hu hw huw
    · have := (le_tdist_iff hRM).1 hw.2.1 u hu
      rw [abs_sub_comm]; omega
    · have := (le_tdist_iff hRM).1 hu.2.1 w hw
      omega
    · by_contra hlt
      push Not at hlt
      have h1 := hw.2.2 u huw (by omega) hu.1 hu.2.1
      have h2 := hu.2.2 w (Ne.symm huw) (by rw [abs_sub_comm]; omega) hw.1 hw.2.1
      omega

end iter

/-! ### Progress -/

/-- Progress, when a nearest point `s` of `P` to the far candidate `v` lies to its left. -/
lemma progress_left {U P : ℤ → Prop} {lab : ℤ → ℕ} (hlab : Injective lab) {R M B : ℕ}
    (hcov : ∀ x, U x → ∃ q, P q ∧ |x - q| ≤ (B : ℤ)) (hBM : B ≤ M)
    {v s : ℤ} (hv : U v) (hfar : R ≤ tdist P M v) (hs : P s) (hsv : s < v)
    (hsd : v - s = tdist P M v) : ∃ w, gAdd U P lab R M w ∧ |w - v| ≤ (B : ℤ) := by
  have hbB : ∀ x, U x → (tdist P M x : ℤ) ≤ B := by
    intro x hx
    obtain ⟨q, hq, h⟩ := hcov x hx
    exact (tdist_le_abs hq).trans h
  have hvB := hbB v hv
  let C : Finset ℤ := (Finset.Icc (v - B) (v + B)).filter fun x =>
    U x ∧ s < x ∧ (∀ q, P q → s < q → x < q) ∧ R ≤ tdist P M x
  have hvC : v ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, hv, hsv, fun q hq hsq => ?_, hfar⟩
    by_contra hqv
    push Not at hqv
    have := tdist_le_abs (M := M) (x := v) hq
    rw [abs_of_nonneg (by omega)] at this
    omega
  obtain ⟨w, hwC, hmax⟩ := C.exists_max_image (fun x => toLex (tdist P M x, lab x)) ⟨v, hvC⟩
  simp only [C, Finset.mem_filter, Finset.mem_Icc] at hwC
  obtain ⟨⟨hw1, hw2⟩, hwU, hsw, hwG, hwfar⟩ := hwC
  refine ⟨w, ⟨hwU, hwfar, ?_⟩, abs_le.2 ⟨by omega, by omega⟩⟩
  intro u huw hu hUu hufar
  rw [abs_le] at hu
  have hbw : (tdist P M w : ℤ) ≤ w - s := by
    have := tdist_le_abs (M := M) (x := w) hs
    rwa [abs_of_pos (by omega)] at this
  have hsu : s < u := by
    by_contra h
    omega
  have huG : ∀ q, P q → s < q → u < q := by
    intro q hq hsq
    by_contra hqu
    push Not at hqu
    have hwq := hwG q hq hsq
    have := tdist_le_abs (M := M) (x := u) hq
    rw [abs_of_nonneg (by omega)] at this
    omega
  by_cases huv : |u - v| ≤ (B : ℤ)
  · have huC : u ∈ C := by
      simp only [C, Finset.mem_filter, Finset.mem_Icc]
      rw [abs_le] at huv
      exact ⟨⟨by omega, by omega⟩, hUu, hsu, huG, hufar⟩
    have h1 := hmax u huC
    rw [Prod.Lex.toLex_le_toLex] at h1
    have h2 : lab u ≠ lab w := hlab.ne huw
    simp only at h1
    omega
  · rw [abs_le] at huv
    push Not at huv
    have hvu : (v : ℤ) + B < u := by
      by_contra h
      have := huv (by omega)
      omega
    obtain ⟨q0, hq0, hq0d⟩ := hcov w hwU
    obtain ⟨qw, hqw, hqwd⟩ := exists_eq_tdist (M := M) (x := w) hq0 (by omega)
    have hbwB := hbB w hwU
    have huq : u < qw := by
      rcases lt_or_ge s qw with h | h
      · exact huG qw hqw h
      · rw [abs_of_nonneg (by omega)] at hqwd
        omega
    have := tdist_le_abs (M := M) (x := u) hqw
    rw [abs_of_neg (by omega)] at this
    rw [abs_of_neg (by omega)] at hqwd
    left
    omega

lemma progress {U P : ℤ → Prop} {lab : ℤ → ℕ} (hlab : Injective lab) {R M B : ℕ}
    (hR : 1 ≤ R) (hBM : B ≤ M) (hcov : ∀ x, U x → ∃ q, P q ∧ |x - q| ≤ (B : ℤ))
    {v : ℤ} (hv : U v) (hfar : R ≤ tdist P M v) :
    ∃ w, gAdd U P lab R M w ∧ |w - v| ≤ (B : ℤ) := by
  obtain ⟨q0, hq0, hq0d⟩ := hcov v hv
  obtain ⟨s, hs, hsd⟩ := exists_eq_tdist (M := M) (x := v) hq0 (by omega)
  rcases lt_trichotomy s v with h | rfl | h
  · rw [abs_of_pos (by omega)] at hsd
    exact progress_left hlab hcov hBM hv hfar hs h hsd
  · simp at hsd
    omega
  · set f := frame 0 (-1) with hf_def
    have hf : ∀ x, f x = -x := by intro x; simp [f, frame]
    have hcov' : ∀ x, (U ∘ f) x → ∃ q, (P ∘ f) q ∧ |x - q| ≤ (B : ℤ) := by
      intro x hx
      obtain ⟨q, hq, h⟩ := hcov (f x) hx
      obtain ⟨q', rfl⟩ := frame_surjective 0 (-1) q
      exact ⟨q', hq, by rwa [abs_frame_sub_frame] at h⟩
    have hfv : f (-v) = v := by rw [hf, neg_neg]
    have hfs : f (-s) = s := by rw [hf, neg_neg]
    have ht : tdist (P ∘ f) M (-v) = tdist P M v := by rw [tdist_comp_frame, ← hf_def, hfv]
    obtain ⟨w', hw', hw'v⟩ := progress_left (U := U ∘ f) (P := P ∘ f) (lab := lab ∘ f) (R := R)
      (hlab.comp (frame_injective _ _)) hcov' hBM (v := -v) (s := -s)
      (by simp only [comp, hfv]; exact hv) (by rw [ht]; exact hfar)
      (by simp only [comp, hfs]; exact hs) (by omega)
      (by rw [ht]; rw [abs_of_neg (by omega)] at hsd; omega)
    refine ⟨f w', (gAdd_comp_frame _ _ _ _ _ _ _ _).1 hw', ?_⟩
    rw [hf, ← abs_neg]
    convert hw'v using 2
    ring

/-! ### Counting -/

lemma card_bound {m : ℕ} (w : ℕ → ℤ) (v : ℤ) (R B : ℕ)
    (hsep : ∀ j < m, ∀ k < m, j ≠ k → (R : ℤ) ≤ |w j - w k|)
    (hd : ∀ j < m, (R : ℤ) ≤ |w j - v| ∧ |w j - v| ≤ B) :
    (B + 3 ≤ 3 * R → m ≤ 4) ∧ (B + 2 ≤ 2 * R → m ≤ 2) := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range m) (fun j => v < w j)
  simp only [Finset.card_range] at hsplit
  have mem : ∀ {p : ℕ → Prop} [DecidablePred p] {j}, j ∈ (Finset.range m).filter p → j < m ∧ p j :=
    fun h => by simpa using h
  constructor
  · intro hB
    have side : ∀ (p : ℕ → Prop) [DecidablePred p], (p = fun j => v < w j) ∨
        (p = fun j => ¬ v < w j) → ((Finset.range m).filter p).card ≤ 2 := by
      intro p _ hp
      by_contra h
      push Not at h
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h
      obtain ⟨ha, pa⟩ := mem ha
      obtain ⟨hb, pb⟩ := mem hb
      obtain ⟨hc, pc⟩ := mem hc
      have h1 := hsep a ha b hb hab
      have h2 := hsep a ha c hc hac
      have h3 := hsep b hb c hc hbc
      have d1 := hd a ha
      have d2 := hd b hb
      have d3 := hd c hc
      rw [le_abs] at h1 h2 h3
      rw [le_abs, abs_le] at d1 d2 d3
      rcases hp with rfl | rfl
      · omega
      · omega
    have := side _ (Or.inl rfl)
    have := side _ (Or.inr rfl)
    omega
  · intro hB
    have side : ∀ (p : ℕ → Prop) [DecidablePred p], (p = fun j => v < w j) ∨
        (p = fun j => ¬ v < w j) → ((Finset.range m).filter p).card ≤ 1 := by
      intro p _ hp
      by_contra h
      push Not at h
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
      obtain ⟨ha, pa⟩ := mem ha
      obtain ⟨hb, pb⟩ := mem hb
      have h1 := hsep a ha b hb hab
      have d1 := hd a ha
      have d2 := hd b hb
      rw [le_abs] at h1
      rw [le_abs, abs_le] at d1 d2
      rcases hp with rfl | rfl
      · omega
      · omega
    have := side _ (Or.inl rfl)
    have := side _ (Or.inr rfl)
    omega

/-- If a candidate is still far after `m` steps, then each step added a distinct node near it. -/
lemma far_witness {U Q : ℤ → Prop} {lab : ℤ → ℕ} (hlab : Injective lab) {R M B : ℕ}
    (hR : 1 ≤ R) (hRM : R ≤ M) (hBM : B ≤ M) (hcov : ∀ v, U v → ∃ q, Q q ∧ |v - q| ≤ (B : ℤ))
    {v : ℤ} (hv : U v) {m : ℕ} (hfar : R ≤ tdist (gIter U Q lab R M m) M v) (j : ℕ) :
    ∃ w, j < m → gIter U Q lab R M m w ∧ (R : ℤ) ≤ |w - v| ∧ |w - v| ≤ (B : ℤ) ∧
      ¬ gIter U Q lab R M j w ∧ gIter U Q lab R M (j + 1) w := by
  by_cases hj : j < m
  · have hfarj : R ≤ tdist (gIter U Q lab R M j) M v :=
      hfar.trans (tdist_anti fun y hy => gIter_mono hj.le hy)
    have hcovj : ∀ x, U x → ∃ q, gIter U Q lab R M j q ∧ |x - q| ≤ (B : ℤ) := by
      intro x hx
      obtain ⟨q, hq, h⟩ := hcov x hx
      exact ⟨q, gIter_of_Q hq, h⟩
    obtain ⟨w, hw, hwv⟩ := progress hlab hR hBM hcovj hv hfarj
    have hwm : gIter U Q lab R M m w := gIter_mono hj (Or.inr hw)
    refine ⟨w, fun _ => ⟨hwm, ?_, hwv, fun hwj => ?_, Or.inr hw⟩⟩
    · have := (le_tdist_iff hRM).1 hfar w hwm
      rw [abs_sub_comm]; omega
    · have := tdist_le_abs (M := M) (x := w) hwj
      simp at this
      have := hw.2.1
      omega
  · exact ⟨0, fun h => absurd h hj⟩

/-- **Greedy extension** (the covering arguments in the proofs of Lemmas 3.4 and 3.5). -/
theorem gIter_spec (U Q : ℤ → Prop) (lab : ℤ → ℕ) (hlab : Injective lab) (R M B m : ℕ)
    (hR : 1 ≤ R) (hRM : R ≤ M) (hBM : B ≤ M) (hpack : Packed Q R)
    (hcov : ∀ v, U v → ∃ q, Q q ∧ |v - q| ≤ (B : ℤ))
    (hm : (B + 3 ≤ 3 * R ∧ 5 ≤ m) ∨ (B + 2 ≤ 2 * R ∧ 3 ≤ m)) :
    Packed (gIter U Q lab R M m) R ∧ (∀ v, gIter U Q lab R M m v → Q v ∨ U v) ∧
    (∀ v, Q v → gIter U Q lab R M m v) ∧
    (∀ v, U v → ∃ q, gIter U Q lab R M m q ∧ |v - q| ≤ (R : ℤ) - 1) := by
  refine ⟨gIter_packed hRM hpack m, fun v => gIter_sub, fun v => gIter_of_Q, ?_⟩
  intro v hv
  by_contra hno
  push Not at hno
  have hfar : R ≤ tdist (gIter U Q lab R M m) M v :=
    (le_tdist_iff hRM).2 fun q hq => hno q hq
  choose w hw using far_witness hlab hR hRM hBM hcov hv hfar
  have hpm := gIter_packed (U := U) (lab := lab) hRM hpack m
  have hne : ∀ j < m, ∀ k < m, j < k → w j ≠ w k := by
    intro j hj k hk hjk heq
    exact (hw k hk).2.2.2.1 (heq ▸ gIter_mono hjk (hw j hj).2.2.2.2)
  have hsep : ∀ j < m, ∀ k < m, j ≠ k → (R : ℤ) ≤ |w j - w k| := by
    intro j hj k hk hjk
    refine hpm _ _ (hw j hj).1 (hw k hk).1 ?_
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hne j hj k hk h
    · exact (hne k hk j hj h).symm
  have := card_bound w v R B hsep fun j hj => ⟨(hw j hj).2.1, (hw j hj).2.2.1⟩
  omega

/-- The greedy steps as a rule. -/
def gIterRule (U Q : (ℤ → ℕ) → ℤ → Prop) (R M m : ℕ) : (ℤ → ℕ) → ℤ → Prop :=
  fun ℓ => gIter (U ℓ) (Q ℓ) ℓ R M m

theorem gIterRule_isLocal {U Q : (ℤ → ℕ) → ℤ → Prop} {ρ : ℕ} (hU : IsLocal U ρ)
    (hQ : IsLocal Q ρ) (R M m : ℕ) : IsLocal (gIterRule U Q R M m) (ρ + m * (M + R)) := by
  intro ℓ ℓ' hℓ hℓ'
  induction m with
  | zero =>
    intro v hv
    exact hQ ℓ ℓ' hℓ hℓ' v (by simpa using hv)
  | succ m ih =>
    intro v hv
    have hK : ((ρ + (m + 1) * (M + R) : ℕ) : ℤ) = ((ρ + m * (M + R) : ℕ) : ℤ) + M + R := by
      push_cast; ring
    have hK0 : (0 : ℤ) ≤ ((ρ + m * (M + R) : ℕ) : ℤ) := by positivity
    simp only [gIterRule, gIter, gStep] at ih ⊢
    have hrec : ∀ y, |y - v| ≤ (M : ℤ) + R →
        (gIter (U ℓ') (Q ℓ') ℓ' R M m y ↔ gIter (U ℓ) (Q ℓ) ℓ R M m y) := by
      intro y hy
      refine Iff.of_eq (ih y fun x hx => hv x ?_)
      have := abs_sub_le x y v
      omega
    have hUv : ∀ y, |y - v| ≤ (R : ℤ) → (U ℓ' y ↔ U ℓ y) := by
      intro y hy
      refine Iff.of_eq (hU ℓ ℓ' hℓ hℓ' y fun x hx => hv x ?_)
      have := abs_sub_le x y v
      omega
    have hlv : ∀ y, |y - v| ≤ (R : ℤ) → ℓ' y = ℓ y := fun y hy => hv y (by omega)
    refine propext (or_congr (hrec v (by simp; omega)) (gAdd_congr hUv hrec hlv))

theorem gIterRule_isEquivar {U Q : (ℤ → ℕ) → ℤ → Prop} (hU : IsEquivar U) (hQ : IsEquivar Q)
    (R M m : ℕ) : IsEquivar (gIterRule U Q R M m) := by
  intro ℓ v ε i
  have hU' : U (ℓ ∘ frame v ε) = U ℓ ∘ frame v ε := funext fun i => hU ℓ v ε i
  have hQ' : Q (ℓ ∘ frame v ε) = Q ℓ ∘ frame v ε := funext fun i => hQ ℓ v ε i
  simp only [gIterRule, hU', hQ', gIter_comp_frame, comp]

end Podc.RendezvousLabeledLine
