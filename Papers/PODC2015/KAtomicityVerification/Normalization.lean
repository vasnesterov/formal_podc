import Papers.PODC2015.KAtomicityVerification.Basic

/-!
# Theorem 3.5: the normalization procedure (Algorithm 1)

Algorithm 1 of [Golab–Li–López-Ortiz–Nishimura] turns a history satisfying Assumptions 3.2–3.3
into one that also satisfies Assumption 3.4, preserving `k`-atomicity: for every value `v` such
that the read `r(v)` of `v` with the earliest finish time finishes before `w(v)`, the response of
`w(v)` is moved to the position immediately preceding the response of `r(v)`.

## Encoding

Times are natural numbers, and we do not want to rely on the paper's convention that all event
times are distinct. We therefore rescale: an invocation at time `t` goes to `4t`, a response at
time `t` to `4t + 2` (so among events that were simultaneous the invocations come first, which
preserves `<_H` exactly), and a moved response of `w(v)` goes to `4 f(r(v)) + 1`, i.e. *immediately*
before the response `4 f(r(v)) + 2` of `r(v)` — no event can lie strictly between them.

The paper processes the values one by one; since each iteration moves only the response of
`w(v)`, and `r(v)` is computed in the input history `H` and is a read (whose events never move),
the iterations do not interact and the simultaneous version below has the same result: the event
order of `H` with each moved response placed immediately before the response of its `r(v)`.

The trigger for moving `w(v)` is "some read of `v` finishes no later than `w(v)`" (`H.Moved v`);
with distinct event times this is the paper's test `f(r(v)) < f(w(v))`.

## Results

* `History.normalize_time_lt_iff`, `History.normalize_f_moved`: faithfulness to Algorithm 1.
* `History.normalize_isKAtomicOrder_iff`: the `k`-atomic total orders of `H` and `H.normalize`
  coincide (for every history `H`, with no assumption at all).
* `History.theorem_3_5`: Theorem 3.5.
-/

namespace Podc.KAtomicityVerification

variable {V R : Type*}

namespace History

variable (H : History V R)

/-- The time of an event: `.inl o` is the invocation of `o`, `.inr o` its response. -/
def time (e : (V ⊕ R) ⊕ (V ⊕ R)) : ℕ := e.elim H.s H.f

/-- The response of `w(v)` is moved by Algorithm 1: some read of `v` finishes no later than
`w(v)` (with distinct times: the earliest-finishing read `r(v)` of `v` has `f(r(v)) < f(w(v))`). -/
def Moved (v : V) : Prop := ∃ r : R, H.val r = v ∧ H.f (.inr r) ≤ H.f (.inl v)

/-- The finish time `f(r(v))` of the read `r(v)` of `v` with the earliest finish time (line 3 of
Algorithm 1); junk value `0` if `v` is never read. -/
noncomputable def firstReadF (v : V) : ℕ := sInf {n | ∃ r : R, H.val r = v ∧ H.f (.inr r) = n}

lemma firstReadF_le {r : R} {v : V} (h : H.val r = v) : H.firstReadF v ≤ H.f (.inr r) :=
  Nat.sInf_le ⟨r, h, rfl⟩

lemma exists_firstRead {v : V} {r : R} (h : H.val r = v) :
    ∃ r₀ : R, H.val r₀ = v ∧ H.f (.inr r₀) = H.firstReadF v :=
  Nat.sInf_mem (s := {n | ∃ r : R, H.val r = v ∧ H.f (.inr r) = n}) ⟨_, r, h, rfl⟩

open Classical in
/-- The normalized history `H'` produced by Algorithm 1 (see the module docstring for the
encoding of times). The `max` only matters for histories violating Assumption 3.3, where the
paper's procedure is not applicable; it keeps `H'` a well-formed history. -/
noncomputable def normalize : History V R where
  val := H.val
  s x := 4 * H.s x
  f x := match x with
    | .inl v => if H.Moved v then 4 * max (H.s (.inl v)) (H.firstReadF v) + 1
        else 4 * H.f (.inl v) + 2
    | .inr r => 4 * H.f (.inr r) + 2
  s_lt_f x := by
    have := H.s_lt_f x
    rcases x with v | r
    · dsimp only; split_ifs <;> omega
    · dsimp only; omega

variable {H}

@[simp] lemma normalize_val : H.normalize.val = H.val := rfl

@[simp] lemma normalize_s (x : V ⊕ R) : H.normalize.s x = 4 * H.s x := rfl

@[simp] lemma normalize_f_inr (r : R) : H.normalize.f (.inr r) = 4 * H.f (.inr r) + 2 := rfl

lemma normalize_f_inl_of_not_moved {v : V} (hv : ¬ H.Moved v) :
    H.normalize.f (.inl v) = 4 * H.f (.inl v) + 2 := by
  classical
  simp [normalize, hv]

lemma normalize_f_inl_of_moved {v : V} (hv : H.Moved v) :
    H.normalize.f (.inl v) = 4 * max (H.s (.inl v)) (H.firstReadF v) + 1 := by
  classical
  simp [normalize, hv]

/-- If `w(v)` is moved, its earliest read finishes no later than `w(v)`. -/
lemma firstReadF_le_f {v : V} (hv : H.Moved v) : H.firstReadF v ≤ H.f (.inl v) := by
  obtain ⟨r, hr, hle⟩ := hv
  exact le_trans (H.firstReadF_le hr) hle

/-- **Faithfulness (i)**, moved responses: if `w(v)` is moved, then (under Assumption 3.3) its
new response time is `4 f(r(v)) + 1`, immediately before the response `4 f(r(v)) + 2` of the
earliest-finishing read `r(v)` of `v`; nothing can happen strictly in between. -/
theorem normalize_f_moved (h33 : H.Assumption33) {v : V} (hv : H.Moved v) :
    ∃ r : R, H.val r = v ∧ (∀ r' : R, H.val r' = v → H.f (.inr r) ≤ H.f (.inr r')) ∧
      H.f (.inr r) ≤ H.f (.inl v) ∧
      H.normalize.f (.inl v) = 4 * H.f (.inr r) + 1 ∧
      H.normalize.f (.inl v) + 1 = H.normalize.f (.inr r) := by
  obtain ⟨r, hr, hrf⟩ := H.exists_firstRead hv.choose_spec.1
  have h3 := h33 r
  rw [hr] at h3
  simp only [hb, not_lt] at h3
  have hle := firstReadF_le_f hv
  refine ⟨r, hr, fun r' hr' => hrf ▸ H.firstReadF_le hr', hrf ▸ hle, ?_, ?_⟩ <;>
  · rw [normalize_f_inl_of_moved hv, ← hrf, max_eq_right h3]
    try simp only [normalize_f_inr]

/-- An event is a *moved response*: the response of a write `w(v)` with `H.Moved v`. -/
def IsMovedEvent (H : History V R) (e : (V ⊕ R) ⊕ (V ⊕ R)) : Prop :=
  ∃ v, e = .inr (.inl v) ∧ H.Moved v

/-- The time of an event that is not a moved response is just rescaled. -/
lemma normalize_time_of_not_moved {e : (V ⊕ R) ⊕ (V ⊕ R)} (he : ¬ H.IsMovedEvent e) :
    H.normalize.time e = 4 * H.time e + (e.elim (fun _ => 0) (fun _ => 2)) := by
  rcases e with x | x
  · simp [time]
  · rcases x with v | r
    · have hv : ¬ H.Moved v := fun hv => he ⟨v, rfl, hv⟩
      simp [time, normalize_f_inl_of_not_moved hv]
    · simp [time]

/-- **Faithfulness (i)**, other events: with distinct event times (the paper's model), the
relative order of all events other than the moved responses is unchanged. -/
theorem normalize_time_lt_iff (hD : H.DistinctTimes) {e₁ e₂ : (V ⊕ R) ⊕ (V ⊕ R)}
    (h₁ : ¬ H.IsMovedEvent e₁) (h₂ : ¬ H.IsMovedEvent e₂) :
    H.normalize.time e₁ < H.normalize.time e₂ ↔ H.time e₁ < H.time e₂ := by
  rw [normalize_time_of_not_moved h₁, normalize_time_of_not_moved h₂]
  have hc₁ : e₁.elim (fun _ => 0) (fun _ => 2) ≤ 2 := by rcases e₁ <;> simp
  have hc₂ : e₂.elim (fun _ => 0) (fun _ => 2) ≤ 2 := by rcases e₂ <;> simp
  constructor
  · intro h
    rcases lt_trichotomy (H.time e₁) (H.time e₂) with h' | h' | h'
    · exact h'
    · have := hD h'
      subst this; omega
    · omega
  · intro h; omega

/-! ### `<_H` versus `<_{H'}` -/

/-- Normalization only moves responses earlier: `<_H ⊆ <_{H'}`. -/
lemma hb_normalize_of_hb {a b : V ⊕ R} (h : H.hb a b) : H.normalize.hb a b := by
  unfold hb at h ⊢
  simp only [normalize_s]
  rcases a with v | r
  · by_cases hv : H.Moved v
    · rw [normalize_f_inl_of_moved hv]
      have := firstReadF_le_f hv
      have := H.s_lt_f (.inl v)
      omega
    · rw [normalize_f_inl_of_not_moved hv]; omega
  · simp only [normalize_f_inr]; omega

/-- The only new `<_{H'}` relations come from moved writes: if `w(v) <_{H'} b` but not
`w(v) <_H b`, then some read of `v` happens before `b` in `H`. -/
lemma hb_of_hb_normalize {a b : V ⊕ R} (h : H.normalize.hb a b) :
    H.hb a b ∨ ∃ r : R, a = .inl (H.val r) ∧ H.hb (.inr r) b := by
  unfold hb at h ⊢
  simp only [normalize_s] at h
  rcases a with v | r
  · by_cases hv : H.Moved v
    · rw [normalize_f_inl_of_moved hv] at h
      obtain ⟨r₁, hr₁, -⟩ := hv
      obtain ⟨r, hr, hrf⟩ := H.exists_firstRead hr₁
      right
      refine ⟨r, by rw [hr], ?_⟩
      have : H.firstReadF v < H.s b := by omega
      rw [hrf]; exact this
    · rw [normalize_f_inl_of_not_moved hv] at h; left; omega
  · simp only [normalize_f_inr] at h; left; omega

/-- **The `k`-atomic total orders of `H` and of `H.normalize` coincide.** No assumption on `H` is
needed. -/
theorem normalize_isKAtomicOrder_iff (k : ℕ) (lt : V ⊕ R → V ⊕ R → Prop) :
    H.normalize.IsKAtomicOrder k lt ↔ H.IsKAtomicOrder k lt := by
  constructor
  · rintro ⟨hto, hext, hread⟩
    exact ⟨hto, fun a b h => hext a b (hb_normalize_of_hb h), hread⟩
  · rintro ⟨hto, hext, hread⟩
    refine ⟨hto, fun a b h => ?_, hread⟩
    rcases hb_of_hb_normalize h with h | ⟨r, rfl, hr⟩
    · exact hext a b h
    · exact hto.trans _ _ _ (hread r).1 (hext _ _ hr)

lemma normalize_kAtomic_iff (k : ℕ) : H.normalize.KAtomic k ↔ H.KAtomic k :=
  exists_congr fun lt => normalize_isKAtomicOrder_iff k lt

/-- Assumption 3.3 is preserved by normalization (no hypothesis needed: the relative order of a
read's response and its dictating write's invocation does not change). -/
lemma normalize_assumption33_iff : H.normalize.Assumption33 ↔ H.Assumption33 := by
  refine forall_congr' fun r => not_congr ?_
  simp only [hb, normalize_f_inr, normalize_s, normalize_val]
  omega

/-- Under Assumption 3.3, the normalized history satisfies Assumption 3.4. -/
lemma normalize_assumption34 (h33 : H.Assumption33) : H.normalize.Assumption34 := by
  intro r
  simp only [normalize_val, normalize_f_inr]
  set v := H.val r
  by_cases hv : H.Moved v
  · obtain ⟨r₀, -, hmin, -, h', -⟩ := normalize_f_moved h33 hv
    rw [h']
    have := hmin r rfl
    omega
  · rw [normalize_f_inl_of_not_moved hv]
    have : H.f (.inl v) < H.f (.inr r) := by
      by_contra hc
      exact hv ⟨r, rfl, not_lt.1 hc⟩
    omega

/-- Distinct event times are preserved by normalization. -/
lemma normalize_distinctTimes (hD : H.DistinctTimes) : H.normalize.DistinctTimes := by
  -- the response of a moved write lands at `4 * max (s w) (f r₀) + 1` for a read `r₀` of `v`
  have hmv : ∀ v, H.Moved v → ∃ r₀ : R, H.val r₀ = v ∧
      H.normalize.f (.inl v) = 4 * max (H.s (.inl v)) (H.f (.inr r₀)) + 1 := by
    intro v hv
    obtain ⟨r₀, hr₀, hrf⟩ := H.exists_firstRead hv.choose_spec.1
    exact ⟨r₀, hr₀, by rw [normalize_f_inl_of_moved hv, hrf]⟩
  have hs : ∀ x y, H.s x = H.s y → x = y := fun x y h =>
    Sum.inl_injective (hD (a₁ := .inl x) (a₂ := .inl y) h)
  have hf : ∀ x y, H.f x = H.f y → x = y := fun x y h =>
    Sum.inr_injective (hD (a₁ := .inr x) (a₂ := .inr y) h)
  have hsf : ∀ x y, H.s x ≠ H.f y := fun x y h => by
    have := hD (a₁ := .inl x) (a₂ := .inr y) h; simp at this
  -- the response time of a write in `H'`
  have hw : ∀ v, (∃ r₀ : R, H.val r₀ = v ∧
      H.normalize.f (.inl v) = 4 * max (H.s (.inl v)) (H.f (.inr r₀)) + 1) ∨
      H.normalize.f (.inl v) = 4 * H.f (.inl v) + 2 := by
    intro v
    by_cases hv : H.Moved v
    · exact Or.inl (hmv v hv)
    · exact Or.inr (normalize_f_inl_of_not_moved hv)
  intro e₁ e₂ h
  simp only at h
  rcases e₁ with x | x <;> rcases e₂ with y | y
  · simp only [Sum.elim_inl, normalize_s] at h
    exact congrArg _ (hs x y (by omega))
  · exfalso
    simp only [Sum.elim_inl, Sum.elim_inr, normalize_s] at h
    rcases y with v | r
    · rcases hw v with ⟨r₀, -, h'⟩ | h' <;> omega
    · simp only [normalize_f_inr] at h; omega
  · exfalso
    simp only [Sum.elim_inl, Sum.elim_inr, normalize_s] at h
    rcases x with v | r
    · rcases hw v with ⟨r₀, -, h'⟩ | h' <;> omega
    · simp only [normalize_f_inr] at h; omega
  · simp only [Sum.elim_inr] at h
    congr 1
    rcases x with v | r <;> rcases y with v' | r'
    · rcases hw v with ⟨r₀, hr₀, h₁⟩ | h₁ <;> rcases hw v' with ⟨r₀', hr₀', h₂⟩ | h₂
      · rw [h₁, h₂] at h
        have hm : max (H.s (.inl v)) (H.f (.inr r₀)) = max (H.s (.inl v')) (H.f (.inr r₀')) := by
          omega
        rcases max_choice (H.s (.inl v)) (H.f (.inr r₀)) with ha | ha <;>
        rcases max_choice (H.s (.inl v')) (H.f (.inr r₀')) with hb' | hb' <;>
        rw [ha, hb'] at hm
        · exact hs _ _ hm
        · exact absurd hm (hsf _ _)
        · exact absurd hm.symm (hsf _ _)
        · have := hf _ _ hm
          rw [← hr₀, ← hr₀', Sum.inr_injective this]
      · omega
      · omega
      · rw [h₁, h₂] at h; exact hf _ _ (by omega)
    · exfalso
      simp only [normalize_f_inr] at h
      rcases hw v with ⟨r₀, -, h'⟩ | h'
      · omega
      · rw [h'] at h; exact absurd (hf _ _ (by omega : H.f (.inl v) = H.f (.inr r'))) (by simp)
    · exfalso
      simp only [normalize_f_inr] at h
      rcases hw v' with ⟨r₀, -, h'⟩ | h'
      · omega
      · rw [h'] at h; exact absurd (hf _ _ (by omega : H.f (.inr r) = H.f (.inl v'))) (by simp)
    · simp only [normalize_f_inr] at h
      exact hf _ _ (by omega)

/-- **Theorem 3.5** of [Golab–Li–López-Ortiz–Nishimura]. If `H` satisfies Assumption 3.3
(Assumption 3.2 is built into `History`), then the output `H' = H.normalize` of Algorithm 1
satisfies Assumptions 3.3 and 3.4 (and 3.2: `H'.val = H.val`), it has distinct event times if `H`
does, and for every `k`, `H'` is `k`-atomic iff `H` is. (In fact the `k`-atomic total orders of
`H` and `H'` coincide, `normalize_isKAtomicOrder_iff`.) Distinct event times are not needed. -/
theorem theorem_3_5 (h33 : H.Assumption33) :
    H.normalize.val = H.val ∧ H.normalize.Assumption33 ∧ H.normalize.Assumption34 ∧
      (H.DistinctTimes → H.normalize.DistinctTimes) ∧
      ∀ k, (H.normalize.KAtomic k ↔ H.KAtomic k) :=
  ⟨rfl, normalize_assumption33_iff.2 h33, normalize_assumption34 h33,
    normalize_distinctTimes, normalize_kAtomic_iff⟩

end History

end Podc.KAtomicityVerification
