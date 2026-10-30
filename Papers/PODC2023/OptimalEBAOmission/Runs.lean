import Papers.PODC2023.OptimalEBAOmission.Model

/-!
# Basic facts about runs

Time and initial preference components, the update of `decided` and `jd`, and the behaviour of
protocols that do nothing after deciding (`OneShotOn`): decisions are stable and happen at a
unique time, and an `M⁰`-message reveals that its sender has just decided `0`.
-/

namespace Podc.OptimalEBAOmission

open Classical

namespace Context

variable {n : ℕ} {γ : Context n}

/-- The messages received by `i` in round `k + 1`. -/
noncomputable def rcv (P : γ.Protocol) (c : γ.Config) (k : ℕ) (i : Fin n) : Fin n → Option γ.M :=
  fun j => if c.pat.F k j i then γ.μ j (γ.state P c k j) (P j (γ.state P c k j)) i else none

theorem state_zero (P : γ.Protocol) (c : γ.Config) (i : Fin n) :
    γ.state P c 0 i = (⟨0, c.init i, none, none⟩, c.x0 i) := rfl

theorem state_succ (P : γ.Protocol) (c : γ.Config) (k : ℕ) (i : Fin n) :
    γ.state P c (k + 1) i = γ.δ i (γ.state P c k i) (P i (γ.state P c k i)) (rcv P c k i) := rfl

@[simp] theorem time_state (P : γ.Protocol) (c : γ.Config) (m : ℕ) (i : Fin n) :
    (γ.state P c m i).1.time = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [state_succ, δ, ih]

@[simp] theorem init_state (P : γ.Protocol) (c : γ.Config) (m : ℕ) (i : Fin n) :
    (γ.state P c m i).1.init = c.init i := by
  induction m with
  | zero => rfl
  | succ m ih => simp [state_succ, δ, ih]

theorem dec_zero (P : γ.Protocol) (c : γ.Config) (i : Fin n) : dec P c 0 i = none := rfl

theorem dec_succ (P : γ.Protocol) (c : γ.Config) (m : ℕ) (i : Fin n) :
    dec P c (m + 1) i = newDec (dec P c m i) (P i (γ.state P c m i)) := rfl

theorem jd_zero (P : γ.Protocol) (c : γ.Config) (i : Fin n) : (γ.state P c 0 i).1.jd = none := rfl

theorem jd_succ (P : γ.Protocol) (c : γ.Config) (m : ℕ) (i : Fin n) :
    (γ.state P c (m + 1) i).1.jd = γ.jdOf (rcv P c m i) := rfl

/-- `decided` never returns to `⊥` (for any protocol). -/
theorem dec_none_of_le_any {P : γ.Protocol} {c : γ.Config} {m m' : ℕ} {i : Fin n}
    (hd : dec P c m i = none) (h : m' ≤ m) : dec P c m' i = none := by
  induction m, h using Nat.le_induction with
  | base => exact hd
  | succ k _ ih =>
    apply ih
    rw [dec_succ] at hd
    cases hk : dec P c k i with
    | none => rfl
    | some v =>
      rw [hk] at hd
      cases ha : P i (γ.state P c k i) <;> rw [ha] at hd <;> cases hd

/-- An agent that is undecided at time `k + 1` did nothing at time `k`. -/
theorem act_noop_of_dec_succ {P : γ.Protocol} {c : γ.Config} {k : ℕ} {i : Fin n}
    (hd : dec P c (k + 1) i = none) : P i (γ.state P c k i) = .noop := by
  rw [dec_succ] at hd
  cases ha : P i (γ.state P c k i) with
  | noop => rfl
  | decide v => rw [ha] at hd; cases hd

/-- Two points with the same local state are at the same time. -/
theorem time_eq_of_state_eq {P : γ.Protocol} {c c' : γ.Config} {m m' : ℕ} {i : Fin n}
    (h : γ.state P c' m' i = γ.state P c m i) : m' = m := by
  have := congrArg (fun s => s.1.time) h
  simpa using this

/-- Two points with the same local state of `i` have the same initial preference of `i`. -/
theorem init_eq_of_state_eq {P : γ.Protocol} {c c' : γ.Config} {m m' : ℕ} {i : Fin n}
    (h : γ.state P c' m' i = γ.state P c m i) : c'.init i = c.init i := by
  have := congrArg (fun s => s.1.init) h
  simpa using this

/-- A message with tag `v` reveals the action `decide v` of its sender. -/
theorem act_of_tag {i : Fin n} {s : γ.L} {a : Act} {j : Fin n} {msg : γ.M} {v : Val}
    (h : γ.μ i s a j = some msg) (ht : γ.tag msg = some v) : a = .decide v := by
  cases a with
  | noop => exact absurd (γ.μ_noop i s j msg h) (by simp [ht])
  | decide w =>
    obtain ⟨m', hm', ht'⟩ := γ.μ_decide i s w j
    rw [h] at hm'; cases hm'
    rw [ht] at ht'; cases ht'; rfl

/-- `jdOf` only depends on which tags were received. -/
theorem jdOf_congr {r₁ r₂ : Fin n → Option γ.M}
    (h : ∀ v, (∃ j m, r₁ j = some m ∧ γ.tag m = some v) ↔ (∃ j m, r₂ j = some m ∧ γ.tag m = some v)) :
    γ.jdOf r₁ = γ.jdOf r₂ := by
  unfold jdOf
  simp only [h 0, h 1]

/-- `jdOf` is invariant under permuting the senders. -/
theorem jdOf_comp_equiv (σ : Fin n ≃ Fin n) (r : Fin n → Option γ.M) :
    γ.jdOf (r ∘ σ) = γ.jdOf r :=
  jdOf_congr fun v => ⟨fun ⟨j, m, h⟩ => ⟨σ j, m, h⟩,
    fun ⟨j, m, h⟩ => ⟨σ.symm j, m, by simpa using h⟩⟩

/-- `jd = 0` after a round iff some received message has tag `0`. -/
theorem jdOf_eq_zero_iff (r : Fin n → Option γ.M) :
    γ.jdOf r = some 0 ↔ ∃ j m, r j = some m ∧ γ.tag m = some 0 := by
  unfold jdOf
  by_cases h1 : ∃ j m, r j = some m ∧ γ.tag m = some 0
  · simp only [h1, if_true]
  · by_cases h2 : ∃ j m, r j = some m ∧ γ.tag m = some 1
    · rw [if_neg h1, if_pos h2]; simp only [h1, iff_false]; decide
    · rw [if_neg h1, if_neg h2]; simp only [h1, iff_false]; simp

theorem jdOf_eq_one_iff (r : Fin n → Option γ.M) :
    γ.jdOf r = some 1 ↔ (¬ ∃ j m, r j = some m ∧ γ.tag m = some 0) ∧
      ∃ j m, r j = some m ∧ γ.tag m = some 1 := by
  unfold jdOf
  by_cases h1 : ∃ j m, r j = some m ∧ γ.tag m = some 0
  · rw [if_pos h1]; simp only [h1, not_true, false_and, iff_false]; decide
  · by_cases h2 : ∃ j m, r j = some m ∧ γ.tag m = some 1
    · rw [if_neg h1, if_pos h2]; simp only [h1, h2, not_false_eq_true, and_self]
    · rw [if_neg h1, if_neg h2]; simp only [h2, and_false, iff_false]; simp

theorem jdOf_eq_none_iff (r : Fin n → Option γ.M) :
    γ.jdOf r = none ↔ ∀ j m, r j = some m → γ.tag m = none := by
  unfold jdOf
  constructor
  · intro h j m hm
    split_ifs at h with h1 h2
    push_neg at h1 h2
    cases ht : γ.tag m with
    | none => rfl
    | some v =>
      fin_cases v
      · exact absurd ht (h1 j m hm)
      · exact absurd ht (h2 j m hm)
  · intro h
    have h1 : ¬ ∃ j m, r j = some m ∧ γ.tag m = some 0 := fun ⟨j, m, hm, ht⟩ => by
      simp [h j m hm] at ht
    have h2 : ¬ ∃ j m, r j = some m ∧ γ.tag m = some 1 := fun ⟨j, m, hm, ht⟩ => by
      simp [h j m hm] at ht
    simp [h1, h2]

/-- `jd_i = 0` at time `k + 1` iff some agent deciding `0` at time `k` delivered to `i`. -/
theorem jd_succ_eq_zero_iff (P : γ.Protocol) (c : γ.Config) (k : ℕ) (i : Fin n) :
    (γ.state P c (k + 1) i).1.jd = some 0 ↔
      ∃ j, c.pat.F k j i = true ∧ P j (γ.state P c k j) = .decide 0 := by
  rw [jd_succ, jdOf_eq_zero_iff]
  constructor
  · rintro ⟨j, m, hm, ht⟩
    simp only [rcv] at hm
    split_ifs at hm with hF
    exact ⟨j, hF, act_of_tag hm ht⟩
  · rintro ⟨j, hF, ha⟩
    obtain ⟨m, hm, ht⟩ := γ.μ_decide j (γ.state P c k j) 0 i
    refine ⟨j, m, ?_, ht⟩
    simp only [rcv, hF, if_true, ha, hm]

/-- `jd_i = ⊥` at time `k + 1` iff no agent deciding at time `k` delivered to `i`. -/
theorem jd_succ_eq_none_iff (P : γ.Protocol) (c : γ.Config) (k : ℕ) (i : Fin n) :
    (γ.state P c (k + 1) i).1.jd = none ↔
      ∀ j, c.pat.F k j i = true → P j (γ.state P c k j) = .noop := by
  rw [jd_succ, jdOf_eq_none_iff]
  constructor
  · intro h j hF
    cases ha : P j (γ.state P c k j) with
    | noop => rfl
    | decide v =>
      obtain ⟨m, hm, ht⟩ := γ.μ_decide j (γ.state P c k j) v i
      have := h j m (by simp only [rcv, hF, if_true, ha, hm])
      rw [ht] at this; cases this
  · intro h j m hm
    simp only [rcv] at hm
    split_ifs at hm with hF
    rw [h j hF] at hm
    exact γ.μ_noop _ _ _ _ hm

/-- `jd_i = 1` at time `k + 1` implies some agent decided `1` at time `k` and delivered to `i`. -/
theorem exists_of_jd_succ_eq_one (P : γ.Protocol) (c : γ.Config) (k : ℕ) (i : Fin n)
    (h : (γ.state P c (k + 1) i).1.jd = some 1) :
    ∃ j, c.pat.F k j i = true ∧ P j (γ.state P c k j) = .decide 1 := by
  rw [jd_succ, jdOf_eq_one_iff] at h
  obtain ⟨-, j, m, hm, ht⟩ := h
  simp only [rcv] at hm
  split_ifs at hm with hF
  exact ⟨j, hF, act_of_tag hm ht⟩

/-- A sequence of `n - 1` distinct agents avoiding a given agent. -/
theorem exists_seq_avoid (i : Fin n) : ∃ a : ℕ → Fin n, (∀ k < n - 1, a k ≠ i) ∧
    ∀ k < n - 1, ∀ l < n - 1, a k = a l → k = l := by
  have hcard : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => if h : k < n - 1 then (e.symm ⟨k, h⟩).1 else i, ?_, ?_⟩
  · intro k hk; simp only [dif_pos hk]; exact (e.symm ⟨k, hk⟩).2
  · intro k hk l hl he
    simp only [dif_pos hk, dif_pos hl] at he
    have := e.symm.injective (Subtype.ext he)
    simpa using this

/-- `P` does nothing once it has decided (on the states arising in its system). -/
def OneShotOn (P : γ.Protocol) : Prop :=
  ∀ c : γ.Config, c.Valid → ∀ m i, dec P c m i ≠ none → P i (γ.state P c m i) = .noop

theorem OneShot.oneShotOn {P : γ.Protocol} (h : OneShot P) : OneShotOn P :=
  fun _ _ _ _ hd => h _ _ hd

theorem Implements.oneShotOn {P : γ.Protocol} (h : Implements P) : OneShotOn P := by
  intro c hc m i hd
  rw [h c hc m i, P0, if_pos hd]

section OneShotOn

variable {P : γ.Protocol} (hP : OneShotOn P) {c : γ.Config} (hc : c.Valid)
include hP hc

theorem dec_succ_of_ne_none {m : ℕ} {i : Fin n} (hd : dec P c m i ≠ none) :
    dec P c (m + 1) i = dec P c m i := by
  rw [dec_succ, hP c hc m i hd]; rfl

theorem dec_stable {m : ℕ} {i : Fin n} {v : Val} (hd : dec P c m i = some v) :
    ∀ m' ≥ m, dec P c m' i = some v := by
  intro m' hm'
  induction m', hm' using Nat.le_induction with
  | base => exact hd
  | succ k _ ih => rw [dec_succ_of_ne_none hP hc (by simp [ih]), ih]

theorem dec_none_of_le {m m' : ℕ} {i : Fin n} (hd : dec P c m i = none) (h : m' ≤ m) :
    dec P c m' i = none := by
  by_contra hne
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
  rw [dec_stable hP hc hv m h] at hd
  cases hd

/-- If `i` has decided by time `m`, it first decided at some earlier time. -/
theorem exists_deciding {m : ℕ} {i : Fin n} {v : Val} (hd : dec P c m i = some v) :
    ∃ d < m, Deciding P c d i v := by
  induction m with
  | zero => simp [dec_zero] at hd
  | succ m ih =>
    by_cases h : dec P c m i = none
    · exact ⟨m, by omega, h, hd⟩
    · rw [dec_succ_of_ne_none hP hc h] at hd
      obtain ⟨d, hd', hD⟩ := ih hd
      exact ⟨d, by omega, hD⟩

/-- An agent decides at most once. -/
theorem deciding_unique {d d' : ℕ} {i : Fin n} {v v' : Val} (h : Deciding P c d i v)
    (h' : Deciding P c d' i v') : d = d' ∧ v = v' := by
  have key : ∀ {d d' : ℕ} {v v' : Val}, Deciding P c d i v → Deciding P c d' i v' → ¬ d < d' :=
    fun {d d' v v'} h h' hlt => by
      have := dec_stable hP hc h.2 d' (by omega)
      rw [h'.1] at this; cases this
  have hdd : d = d' := by
    rcases lt_trichotomy d d' with hlt | heq | hgt
    · exact absurd hlt (key h h')
    · exact heq
    · exact absurd hgt (key h' h)
  subst hdd
  refine ⟨rfl, ?_⟩
  have := h.2.symm.trans h'.2
  exact Option.some_injective _ this

/-- `Deciding` is "undecided and performing `decide v`". -/
theorem deciding_iff {m : ℕ} {i : Fin n} {v : Val} :
    Deciding P c m i v ↔ dec P c m i = none ∧ P i (γ.state P c m i) = .decide v := by
  unfold Deciding
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    rw [dec_succ, h0] at h1
    cases ha : P i (γ.state P c m i) with
    | noop => rw [ha] at h1; cases h1
    | decide w => rw [ha] at h1; cases h1; rfl
  · rintro ⟨h0, h1⟩
    exact ⟨h0, by rw [dec_succ, h1]; rfl⟩

/-- Performing `decide v` at a reachable state means deciding (for the first time). -/
theorem deciding_of_act {m : ℕ} {i : Fin n} {v : Val}
    (h : P i (γ.state P c m i) = .decide v) : Deciding P c m i v := by
  have hd : dec P c m i = none := by
    by_contra hne; rw [hP c hc m i hne] at h; cases h
  exact (deciding_iff hP hc).2 ⟨hd, h⟩

/-- `jdecided` is `deciding` one step earlier. -/
theorem jDecided_succ_iff {m : ℕ} {j : Fin n} {v : Val} :
    JDecided P c (m + 1) j v ↔ Deciding P c m j v := by
  simp only [JDecided, Deciding, Nat.add_sub_cancel]
  exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨by omega, h.2, h.1⟩⟩

theorem not_jDecided_zero {j : Fin n} {v : Val} : ¬ JDecided P c 0 j v := fun h => by
  simp [JDecided] at h

end OneShotOn

/-- An agent with `jd = 0` knows that some agent has just decided `0`. -/
theorem knows_of_jd {P : γ.Protocol} (hP : OneShotOn P) {c : γ.Config} {m : ℕ} {i : Fin n}
    (hjd : (γ.state P c m i).1.jd = some 0) :
    Knows P i (γ.state P c m i) (fun c' m' => ∃ j, JDecided P c' m' j 0) := by
  intro c' hc' m' hs
  have hm := time_eq_of_state_eq hs
  subst hm
  cases m' with
  | zero => rw [jd_zero] at hjd; cases hjd
  | succ k =>
    rw [← hs, jd_succ_eq_zero_iff] at hjd
    obtain ⟨j, -, ha⟩ := hjd
    exact ⟨j, (jDecided_succ_iff hP hc').2 (deciding_of_act hP hc' ha)⟩

/-- Agents of a sequence deciding at pairwise different times are distinct. -/
theorem inj_of_deciding {P : γ.Protocol} (hP : OneShotOn P) {c : γ.Config} (hc : c.Valid)
    {m : ℕ} {a : ℕ → Fin n} {v : Val} (h : ∀ k ≤ m, Deciding P c k (a k) v) :
    ∀ k ≤ m, ∀ l ≤ m, a k = a l → k = l := by
  intro k hk l hl he
  have h1 := h k hk
  have h2 := h l hl
  rw [he] at h1
  exact (deciding_unique hP hc h1 h2).1

/-- Pigeonhole: `t + 1` distinct agents are not all faulty. -/
theorem exists_nonfaulty_of_inj {N : Finset (Fin n)} {t : ℕ} (hN : (Finset.univ \ N).card ≤ t)
    {a : ℕ → Fin n} (ha : ∀ k ≤ t, ∀ l ≤ t, a k = a l → k = l) : ∃ k ≤ t, a k ∈ N := by
  by_contra hne
  push_neg at hne
  have hsub : (Finset.range (t + 1)).image a ⊆ Finset.univ \ N := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_range] at hk
    simpa using hne k (by omega)
  have hcard : ((Finset.range (t + 1)).image a).card = t + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl he
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    exact ha k (by omega) l (by omega) he
  have := Finset.card_le_card hsub
  omega

end Context

end Podc.OptimalEBAOmission
