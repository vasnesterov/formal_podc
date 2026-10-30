import Papers.PODC2021.MISTreeLowerBounds.Family

/-!
# Lemmas 5, 11 and 12

* Lemma 5 (`lemma_5`): a `t`-round algorithm for `k`-outdegree dominating sets gives a
  `(t+1)`-round algorithm for `Π_Δ(a, k)`.
* Lemma 11 (`lemma_11`): `Π_Δ(a, x)` is 0-round solvable from `Π_Δ(a', x')` for `a ≤ a'`,
  `x' ≤ x ≤ Δ`.
* Lemma 12 (`lemma_12`): `Π_Δ(a, x)` is not 0-round solvable for `x < Δ` and `a ≥ 1`.
-/

namespace Podc.MISTreeLowerBounds

open Cslib.ColourSystem FreeCox

variable {Δ : ℕ}

theorem exists_eq_of_cnt_pos {α : Type*} [DecidableEq α] {σ : Fin Δ → α} {ℓ : α}
    (h : 0 < cnt σ ℓ) : ∃ i, σ i = ℓ := by
  unfold cnt at h
  obtain ⟨i, hi⟩ := Finset.card_pos.1 h
  exact ⟨i, by simpa using hi⟩

/-! ### Thinning: replacing some occurrences of a label by `X` -/

/-- Keep exactly `n` occurrences of `ℓ` in `σ` (if `n ≤ cnt σ ℓ`) and replace the others by `X`. -/
noncomputable def thin (σ : Fin Δ → L5) (ℓ : L5) (n : ℕ) : Fin Δ → L5 := by
  classical
  exact if h : n ≤ cnt σ ℓ then
    let T := Classical.choose (Finset.exists_subset_card_eq h)
    fun i => if σ i = ℓ ∧ i ∉ T then .X else σ i
  else σ

theorem thin_eq_or (σ : Fin Δ → L5) (ℓ : L5) (n : ℕ) (i : Fin Δ) :
    thin σ ℓ n i = σ i ∨ thin σ ℓ n i = .X := by
  unfold thin
  split_ifs with h
  · dsimp only; split_ifs <;> simp
  · exact Or.inl rfl

theorem cnt_thin {σ : Fin Δ → L5} {ℓ : L5} {n : ℕ} (hℓ : ℓ ≠ .X) (h : n ≤ cnt σ ℓ) :
    cnt (thin σ ℓ n) ℓ = n ∧ cnt (thin σ ℓ n) .X = cnt σ .X + (cnt σ ℓ - n) := by
  classical
  unfold thin
  rw [dif_pos h]
  obtain ⟨hT, hcard⟩ := Classical.choose_spec (Finset.exists_subset_card_eq h)
  set T := Classical.choose (Finset.exists_subset_card_eq h)
  have hT' : ∀ i ∈ T, σ i = ℓ := fun i hi => by simpa using hT hi
  constructor
  · unfold cnt
    rw [← hcard]; congr 1; ext i
    by_cases hi : i ∈ T
    · simp [hi, hT' i hi]
    · by_cases hσ : σ i = ℓ
      · simp [hi, hσ, Ne.symm hℓ]
      · simp [hσ]; exact hi
  · unfold cnt at h ⊢
    have : (Finset.univ.filter fun i =>
        (if σ i = ℓ ∧ i ∉ T then L5.X else σ i) = L5.X) =
        (Finset.univ.filter fun i => σ i = .X) ∪
          ((Finset.univ.filter fun i => σ i = ℓ) \ T) := by
      ext i
      by_cases hσ : σ i = ℓ
      · by_cases hi : i ∈ T <;> simp [hσ, hi, hℓ]
      · simp [hσ]
    rw [this, Finset.card_union_of_disjoint, Finset.card_sdiff_of_subset hT, hcard]
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at h1 h2
    exact hℓ (h2.1.symm.trans h1)

theorem thin_of_ne {σ : Fin Δ → L5} {ℓ : L5} {n : ℕ} {i : Fin Δ} (h : σ i ≠ ℓ) :
    thin σ ℓ n i = σ i := by
  unfold thin
  split_ifs with h0
  · dsimp only; rw [if_neg (fun h' => h h'.1)]
  · rfl

theorem cnt_thin_other {σ : Fin Δ → L5} {ℓ ℓ' : L5} {n : ℕ} (hℓ' : ℓ' ≠ .X) (hne : ℓ' ≠ ℓ) :
    cnt (thin σ ℓ n) ℓ' = cnt σ ℓ' := by
  classical
  unfold cnt; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : σ i = ℓ
  · rcases thin_eq_or σ ℓ n i with h | h
    · rw [h]
    · rw [h, hi]; exact ⟨fun h' => absurd h'.symm hℓ', fun h' => absurd h'.symm hne⟩
  · rw [thin_of_ne hi]

/-- A relabelling that only replaces labels by `X` preserves `E5`. -/
theorem E5_of_eq_or {a b a' b' : L5} (h : E5 a b) (ha : a' = a ∨ a' = .X) (hb : b' = b ∨ b' = .X) :
    E5 a' b' := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | exact h | (cases a' <;> trivial) | (cases b' <;> trivial) | trivial

/-! ### Lemma 11 -/

/-- Lemma 11 of [paper]: `Π_Δ(a, x)` can be solved in 0 rounds given a solution of `Π_Δ(a', x')`,
for all `a ≤ a'` and `x' ≤ x` (with `x ≤ Δ`, as throughout the paper). -/
theorem lemma_11 {a a' x x' : ℕ} (ha : a ≤ a') (hx : x' ≤ x) (hxΔ : x ≤ Δ) :
    ZeroRoundReduction (Pi Δ a' x') (Pi Δ a x) := by
  classical
  refine ⟨fun σ => if cnt σ .M = Δ - x' ∧ cnt σ .X = x' then thin σ .M (Δ - x)
    else if cnt σ .A = a' ∧ cnt σ .X = Δ - a' then thin σ .A a else σ, ?_, ?_⟩
  · rintro σ (hM | hA | hP)
    · simp only [hM, and_self, ite_true]
      have := cnt_thin (σ := σ) (ℓ := .M) (n := Δ - x) (by decide) (by omega)
      left; constructor <;> omega
    · by_cases hM : cnt σ .M = Δ - x' ∧ cnt σ .X = x'
      · simp only [hM, and_self, ite_true]
        have := cnt_thin (σ := σ) (ℓ := .M) (n := Δ - x) (by decide) (by omega)
        left; constructor <;> omega
      · show (if cnt σ .M = Δ - x' ∧ cnt σ .X = x' then thin σ .M (Δ - x)
          else if cnt σ .A = a' ∧ cnt σ .X = Δ - a' then thin σ .A a else σ) ∈ _
        rw [if_neg hM, if_pos hA]
        have h1 := cnt_thin (σ := σ) (ℓ := .A) (n := a) (by decide) (by omega)
        have h2 := cnt_le σ .A
        right; left; constructor <;> omega
    · by_cases hM : cnt σ .M = Δ - x' ∧ cnt σ .X = x'
      · simp only [hM, and_self, ite_true]
        have := cnt_thin (σ := σ) (ℓ := .M) (n := Δ - x) (by decide) (by omega)
        left; constructor <;> omega
      · simp only [hM, ite_false]
        split_ifs with hA
        · have h1 := cnt_thin (σ := σ) (ℓ := .A) (n := a) (by decide) (by omega)
          have h2 := cnt_le σ .A
          right; left; constructor <;> omega
        · exact Or.inr (Or.inr hP)
  · intro σ _ τ _ c h
    have key : ∀ ρ : Fin Δ → L5, ∀ c, (if cnt ρ .M = Δ - x' ∧ cnt ρ .X = x' then thin ρ .M (Δ - x)
        else if cnt ρ .A = a' ∧ cnt ρ .X = Δ - a' then thin ρ .A a else ρ) c = ρ c ∨
        (if cnt ρ .M = Δ - x' ∧ cnt ρ .X = x' then thin ρ .M (Δ - x)
        else if cnt ρ .A = a' ∧ cnt ρ .X = Δ - a' then thin ρ .A a else ρ) c = .X := by
      intro ρ c
      split_ifs
      · exact thin_eq_or _ _ _ _
      · exact thin_eq_or _ _ _ _
      · exact Or.inl rfl
    exact E5_of_eq_or h (key σ c) (key τ c)

/-! ### Lemma 12 -/

/-- Lemma 12 of [paper]: `Π_Δ(a, x)` cannot be solved deterministically in 0 rounds in the
port-numbering model, even with a `Δ`-edge colouring (here: in the family where the port numbers
are the colours), for all `x ≤ Δ - 1` (i.e. `x < Δ`) and `a ≥ 1`. -/
theorem lemma_12 {a x : ℕ} (hx : x < Δ) (ha : 1 ≤ a) : ¬ (Pi Δ a x).SolvableIn 0 := by
  rw [solvableIn_zero_iff]
  rintro ⟨σ, hM | hA | hP, hc⟩
  · obtain ⟨i, hi⟩ := exists_eq_of_cnt_pos (σ := σ) (ℓ := .M) (by omega)
    have := hc i; rw [hi] at this; exact this
  · obtain ⟨i, hi⟩ := exists_eq_of_cnt_pos (σ := σ) (ℓ := .A) (by omega)
    have := hc i; rw [hi] at this; exact this
  · obtain ⟨i, hi⟩ := exists_eq_of_cnt_pos (σ := σ) (ℓ := .P) (by omega)
    have := hc i; rw [hi] at this; exact this

/-! ### Lemma 5 -/

/-- The radius-`t` view of a neighbour is contained in the radius-`(t+1)` view. -/
theorem AgreeOn.shift_gen {t : ℕ} {I J : Orientation Δ} (h : AgreeOn (t + 1) I J) (c : Fin Δ) :
    AgreeOn t (I.shift (gen c)) (J.shift (gen c)) := by
  unfold AgreeOn
  rw [agreeOnSet_shift]
  refine h.mono ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Set.mem_ofPred_eq] at hw ⊢
  exact (len_gen_mul_le w c).trans (by omega)

/-- The 1-round post-processing of Lemma 5: from the `k`-ODS outputs of a node (`o`) and of its
neighbours (`n c` along colour `c`), compute a `Π_Δ(a, k)` configuration. -/
noncomputable def lemma5Out (k : ℕ) (o : Bool × (Fin Δ → Bool)) (n : Fin Δ → Bool × (Fin Δ → Bool)) :
    Fin Δ → L5 := by
  classical
  exact if o.1 then
    -- in `S`: `X` on outgoing edges inside `S`, `M` elsewhere, then more `X` to get exactly `k`
    let σ₀ : Fin Δ → L5 := fun c => if (n c).1 = true ∧ o.2 c = true then .X else .M
    thin σ₀ .M (Δ - k)
  else if h : ∃ c, (n c).1 = true then
    -- not in `S`: point `P` to a neighbour in `S`
    fun c => if c = Classical.choose h then .P else .O
  else fun _ => .O

/-- Lemma 5 of [paper]: given a solution for the `k`-outdegree dominating set problem, `Π_Δ(a, k)`
can be solved in one more round (for all `a`; here `k ≤ Δ`). -/
theorem lemma_5 {k t : ℕ} (hk : k ≤ Δ) (a : ℕ) (h : ODSSolvableIn Δ k t) :
    (Pi Δ a k).SolvableIn (t + 1) := by
  classical
  obtain ⟨A, hA, hS⟩ := h
  refine ⟨fun I => lemma5Out k (A I) (fun c => A (I.shift (gen c))), fun I J hIJ => ?_, ?_⟩
  · simp only
    rw [hA.mono (Nat.le_succ t) I J hIJ]
    congr 1; funext c; exact hA _ _ (hIJ.shift_gen c)
  rw [solves_iff]
  intro I
  have hI := hS I 1
  simp only [Orientation.shift_one, one_mul] at hI
  obtain ⟨hdom, hor, hdeg⟩ := hI
  -- the node configuration
  have hnode : ∀ J : Orientation Δ, (∀ c, (A J).1 = true → (A (J.shift (gen c))).1 = true →
      (A J).2 c ≠ (A (J.shift (gen c))).2 c) → ((A J).1 = true ∨ ∃ c, (A (J.shift (gen c))).1 = true) →
      ((A J).1 = true → (Finset.univ.filter fun c => (A (J.shift (gen c))).1 = true ∧
        (A J).2 c = true).card ≤ k) →
      lemma5Out k (A J) (fun c => A (J.shift (gen c))) ∈ (Pi Δ a k).node := by
    intro J _ hdom hdeg
    unfold lemma5Out
    by_cases hJ : (A J).1 = true
    · simp only [hJ, ite_true]
      set σ₀ : Fin Δ → L5 := fun c =>
        if (A (J.shift (gen c))).1 = true ∧ (A J).2 c = true then .X else .M
      have hX : cnt σ₀ .X = (Finset.univ.filter fun c => (A (J.shift (gen c))).1 = true ∧
          (A J).2 c = true).card := by
        unfold cnt; congr 1; ext c; by_cases hc : (A (J.shift (gen c))).1 = true ∧ (A J).2 c = true
        · simp [σ₀, hc]
        · simp [σ₀, hc]
      have hsum : cnt σ₀ .M + cnt σ₀ .X = Δ := by
        have hM : cnt σ₀ .M = (Finset.univ.filter fun c => ¬ σ₀ c = .X).card := by
          unfold cnt; congr 1; ext c
          simp only [σ₀, Finset.mem_filter, Finset.mem_univ, true_and]; split_ifs <;> simp
        rw [hM, add_comm]
        unfold cnt
        rw [Finset.card_filter_add_card_filter_not]; simp
      have hd := hdeg hJ
      have := cnt_thin (σ := σ₀) (ℓ := .M) (n := Δ - k) (by decide) (by omega)
      left; constructor <;> omega
    · have hex : ∃ c, (A (J.shift (gen c))).1 = true := by
        rcases hdom with h | h
        · exact absurd h hJ
        · exact h
      simp only [hJ, Bool.false_eq_true, ite_false, dif_pos hex]
      right; right
      set c₀ := Classical.choose hex
      constructor
      · unfold cnt; rw [Finset.card_eq_one]; exact ⟨c₀, by ext c; by_cases h : c = c₀ <;> simp [h]⟩
      · unfold cnt
        have : (Finset.univ.filter fun c => (if c = c₀ then L5.P else L5.O) = L5.O) =
            Finset.univ.erase c₀ := by
          ext c; by_cases h : c = c₀ <;> simp [h]
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  refine ⟨hnode I hor hdom hdeg, fun c => ?_⟩
  -- the edge of colour `c` between the root and `gen c`
  set J := I.shift (gen c)
  have hJJ : J.shift (gen c) = I := by simp [J]
  -- labels of the two endpoints
  have lab : ∀ (K L : Orientation Δ), L = K.shift (gen c) → K = L.shift (gen c) →
      ((A K).1 = true → lemma5Out k (A K) (fun c' => A (K.shift (gen c'))) c = .M ∨
        lemma5Out k (A K) (fun c' => A (K.shift (gen c'))) c = .X) ∧
      ((A K).1 = true → (A L).1 = true → (A K).2 c = true →
        lemma5Out k (A K) (fun c' => A (K.shift (gen c'))) c = .X) ∧
      ((A K).1 = false → (lemma5Out k (A K) (fun c' => A (K.shift (gen c'))) c = .P ∧
        (A L).1 = true) ∨ lemma5Out k (A K) (fun c' => A (K.shift (gen c'))) c = .O) := by
    intro K L hL _
    unfold lemma5Out
    refine ⟨fun hK => ?_, fun hK hLS hout => ?_, fun hK => ?_⟩
    · simp only [hK, ite_true]
      rcases thin_eq_or (fun c => if (A (K.shift (gen c))).1 = true ∧ (A K).2 c = true then L5.X
        else L5.M) .M (Δ - k) c with h | h
      · rw [h]; split_ifs <;> simp
      · exact Or.inr h
    · simp only [hK, ite_true]
      rcases thin_eq_or (fun c => if (A (K.shift (gen c))).1 = true ∧ (A K).2 c = true then L5.X
        else L5.M) .M (Δ - k) c with h | h
      · rw [h]; rw [← hL]; simp [hLS, hout]
      · exact h
    · simp only [hK, Bool.false_eq_true, ite_false]
      split_ifs with hex
      · dsimp only
        by_cases hc : c = Classical.choose hex
        · left; refine ⟨by simp [hc], ?_⟩; rw [hL, hc]; exact Classical.choose_spec hex
        · right; simp [hc]
      · right; rfl
  obtain ⟨l1, l2, l3⟩ := lab I J rfl hJJ.symm
  obtain ⟨m1, m2, m3⟩ := lab J I hJJ.symm rfl
  change E5 _ _
  cases hI1 : (A I).1 <;> cases hJ1 : (A J).1
  · -- both outside `S`: both labels are `O`
    rcases l3 hI1 with ⟨-, h⟩ | h
    · rw [hJ1] at h; exact absurd h (by decide)
    rcases m3 hJ1 with ⟨-, h'⟩ | h'
    · rw [hI1] at h'; exact absurd h' (by decide)
    rw [h, h']; trivial
  · rcases l3 hI1 with ⟨h, -⟩ | h <;> rcases m1 hJ1 with h' | h' <;> rw [h, h'] <;> trivial
  · rcases l1 hI1 with h | h <;> rcases m3 hJ1 with ⟨h', -⟩ | h' <;> rw [h, h'] <;> trivial
  · -- both in `S`: one endpoint has the edge as outgoing, hence label `X`
    have hne := hor c hI1 hJ1
    cases hb : (A I).2 c
    · have : (A J).2 c = true := by rw [hb] at hne; simpa using (Ne.symm hne)
      rw [m2 hJ1 hI1 this]
      rcases l1 hI1 with h | h <;> rw [h] <;> trivial
    · rw [l2 hI1 hJ1 hb]
      rcases m1 hJ1 with h | h <;> rw [h] <;> trivial

end Podc.MISTreeLowerBounds
