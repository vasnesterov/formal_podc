import Papers.PODC2026.EarlyStabilizingCounting.Basic
import Papers.PODC2026.EarlyStabilizingCounting.Lemma55
import Podc.Foundations.Data.Nat.ModCount

/-!
# The recursion template at the level of traces (Lemmas 5.4, 5.6, Theorem 5.7)

Section 5 of [LL26]. We abstract one execution of Algorithm 1 by the traces of the correct nodes:

* `cv τ v` — the output clock `C_v` at time `τ`;
* `fl b τ v` — the output of the `b`-th filtering instance (`F_v^b`) at time `τ`;
* `ld b τ v` — the leader input of the `b`-th King Consensus instance started in round `τ + 1`
  (computed from `F^b_{v,τ}`, Algorithm 1 line 2);
* `out b τ v` — the output of that instance, available at time `τ + D` (`D` = number of rounds of
  King Consensus).

`TraceHyp` collects what Algorithm 1 guarantees: the update rule of lines 3–9 and 15 (the output of
an instance replaces `C_v`, the `b = 1` instance last, then `C_v` is incremented), and that every
instance started after time `0` satisfies the King Consensus specification (Definition 2.6) with
input `(C_v + δ mod C, ℓ_v^b)`.

**Timing.** An `R`-round subroutine started in round `τ + 1` executes its round `R` in round
`τ + R` (Section 4 conventions), so its output overwrites `C_v` at time `τ + R`, after which `C_v`
is incremented once more. The input must therefore be `C_v + R - 1`, not `C_v + R` as written in
Algorithm 1, line 3 (`δ = D - 1` below; see `Literal.lean` for the failure with `δ = D`).

Constants (`kk`): `k₀ = 4D`, `k₁ = 5D` (the paper's choice `k₀ = ⌈(R+1)/ε⌉`, `k₁ = k₀ + R + 1` with
`ε = 1/4` in our timing), filter window `W ≥ 16 D - 1`.
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

open Finset

/-- The constants `k_b`: `k₀ = 4D`, `k₁ = 5D`. -/
def kk (D : ℕ) (b : Bool) : ℕ := if b then 5 * D else 4 * D

/-- What one execution of Algorithm 1 guarantees, at the level of traces. -/
structure TraceHyp (n C D δ : ℕ) (F : Finset (Fin n)) (cv : ℕ → Fin n → ℕ)
    (ld : Bool → ℕ → Fin n → Option (Fin n)) (out : Bool → ℕ → Fin n → Option ℕ) : Prop where
  /-- Lines 3–9 and 15 of Algorithm 1: the output of the instances started in round `τ + 1`
  replaces `C_v` (`b = 1` last), then `C_v` is incremented. -/
  update : ∀ τ, ∀ v, v ∉ F →
    cv (τ + D) v = (((out true τ v).orElse fun _ => out false τ v).getD (cv (τ + D - 1) v) + 1) % C
  /-- Every instance satisfies King Consensus (Definition 2.6). -/
  kc : ∀ b τ, KCSpec F (fun v => (cv τ v + δ) % C) (ld b τ) (out b τ)

/-- Definition 5.3: the `b`-th instance started in round `τ + 1` runs with the correct leader `ℓ`
and is unimpeded: all other instances started in rounds `τ + 1, …, τ + D` have leader `⊥` at all
correct nodes. -/
def Unimpeded {n : ℕ} (F : Finset (Fin n)) (D : ℕ) (ld : Bool → ℕ → Fin n → Option (Fin n))
    (b : Bool) (τ : ℕ) (ℓ : Fin n) : Prop :=
  ℓ ∉ F ∧ (∀ v, v ∉ F → ld b τ v = some ℓ) ∧
    (∀ d, d < D → ∀ v, v ∉ F → ld (!b) (τ + d) v = none) ∧
    (∀ d, 0 < d → d < D → ∀ v, v ∉ F → ld b (τ + d) v = none)

theorem CountsFrom.mono {n : ℕ} {F : Finset (Fin n)} {C : ℕ} {out : ℕ → Fin n → ℕ} {s s' : ℕ}
    (h : CountsFrom F C out s) (hs : s ≤ s') : CountsFrom F C out s' := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c + (s' - s), fun j v hv => ?_⟩
  have := hc (s' - s + j) v hv
  rw [show s + (s' - s + j) = s' + j by omega] at this
  rw [this]; congr 1; omega

/-- Lemma 5.2 (virtual clock): under crusader agreement with window `W` from time `s`, on every
interval `[r₀, r₀ + W]` with `r₀ ≥ s` there is a single counting value `φ + (τ - r₀)` such that
every correct node outputs `⊥` or this value. -/
theorem lemma_5_2 {n K W s : ℕ} {F : Finset (Fin n)} {fl : ℕ → Fin n → Option ℕ} (hK : 0 < K)
    (hc : Crusader F K W s fl) (r₀ : ℕ) (hr : s ≤ r₀) :
    ∃ φ, ∀ τ, r₀ ≤ τ → τ ≤ r₀ + W → ∀ v, v ∉ F →
      fl τ v = none ∨ fl τ v = some ((φ + (τ - r₀)) % K) := by
  classical
  by_cases h : ∃ τ, r₀ ≤ τ ∧ τ ≤ r₀ + W ∧ ∃ v, v ∉ F ∧ fl τ v ≠ none
  · let τs := Nat.find h
    obtain ⟨h1, h2, v, hv, hne⟩ := Nat.find_spec h
    obtain ⟨c, hcv⟩ := Option.ne_none_iff_exists'.1 hne
    refine ⟨c + K * (τs - r₀) - (τs - r₀), fun τ hτ1 hτ2 w hw => ?_⟩
    by_cases hlt : τ < τs
    · left
      by_contra hne'
      exact Nat.find_min h hlt ⟨hτ1, hτ2, w, hw, hne'⟩
    · have := hc τs (by omega) v hv c hcv (τ - τs) (by omega) w hw
      rw [show τs + (τ - τs) = τ by omega] at this
      rcases this with h3 | h3
      · exact Or.inl h3
      · right
        rw [h3]
        have hle : τs - r₀ ≤ K * (τs - r₀) := Nat.le_mul_of_pos_left _ hK
        rw [show c + K * (τs - r₀) - (τs - r₀) + (τ - r₀) = c + (τ - τs) + K * (τs - r₀) by
          omega, Nat.add_mul_mod_self_left]
  · refine ⟨0, fun τ hτ1 hτ2 v hv => Or.inl ?_⟩
    by_contra hne
    exact h ⟨τ, hτ1, hτ2, v, hv, hne⟩

/-- The applied output when each instance outputs `⊥` or `c`. -/
theorem getD_cases {o₁ o₂ : Option ℕ} {c x : ℕ} (h₁ : o₁ = none ∨ o₁ = some c)
    (h₂ : o₂ = none ∨ o₂ = some c) : (o₁.orElse fun _ => o₂).getD x = c ∨
      (o₁.orElse fun _ => o₂).getD x = x := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp [h₁, h₂]

/-- Lemma 5.4: after an unimpeded instance the output clocks count. -/
theorem lemma_5_4 {n C D : ℕ} {F : Finset (Fin n)} {cv : ℕ → Fin n → ℕ}
    {ld : Bool → ℕ → Fin n → Option (Fin n)} {out : Bool → ℕ → Fin n → Option ℕ}
    (hD : 1 ≤ D) (h : TraceHyp n C D (D - 1) F cv ld out) {b : Bool} {τ : ℕ}
    {ℓ : Fin n} (hu : Unimpeded F D ld b τ ℓ) : CountsFrom F C cv (τ + D) := by
  obtain ⟨hℓ, hlead, hother, hself⟩ := hu
  have hk := (h.kc b τ).king ℓ hℓ hlead
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hk.1
  have hb : ∀ v, v ∉ F → out b τ v = some y := fun v hv => (hk.2 v hv).trans hy
  have hb' : ∀ v, v ∉ F → out (!b) τ v = none :=
    (h.kc (!b) τ).default (fun v hv => by simpa using hother 0 (by omega) v hv)
  have h0 : ∀ v, v ∉ F → cv (τ + D) v = (y + 1) % C := by
    intro v hv
    rw [h.update τ v hv]
    cases b
    · have h1 := hb v hv; have h2 := hb' v hv
      simp only [Bool.not_false] at h2
      simp [h1, h2]
    · have h1 := hb v hv; have h2 := hb' v hv
      simp [h1]
  refine ⟨y + 1, fun j => ?_⟩
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro v hv
    rcases j with _ | j
    · rw [Nat.add_zero, h0 v hv]; simp
    · have hupd := h.update (τ + (j + 1)) v hv
      rw [show τ + (j + 1) + D = τ + D + (j + 1) by omega] at hupd
      rw [show τ + D + (j + 1) - 1 = τ + D + j by omega] at hupd
      rw [hupd, Nat.mod_mod]
      have ihj := ih j (by omega) v hv
      by_cases hjD : j + 1 < D
      · -- both instances started in round `τ + j + 2` have no leader
        have hn1 : out b (τ + (j + 1)) v = none :=
          (h.kc b _).default (fun w hw => hself (j + 1) (by omega) hjD w hw) v hv
        have hn2 : out (!b) (τ + (j + 1)) v = none :=
          (h.kc (!b) _).default (fun w hw => hother (j + 1) hjD w hw) v hv
        have : ((out true (τ + (j + 1)) v).orElse fun _ => out false (τ + (j + 1)) v).getD
            (cv (τ + D + j) v) = cv (τ + D + j) v := by
          cases b
          · simp only [Bool.not_false] at hn2; simp [hn1, hn2]
          · simp only [Bool.not_true] at hn2; simp [hn1, hn2]
        rw [this, Nat.add_mod, ihj, ← Nat.add_mod, Nat.add_assoc (y + 1)]
      · -- the inputs agree: validity
        set i := j + 1 - D with hi
        have hτ : τ + (j + 1) = τ + D + i := by omega
        have hin : ∀ w, w ∉ F → (cv (τ + (j + 1)) w + (D - 1)) % C = (y + 1 + j) % C := by
          intro w hw
          rw [hτ, Nat.add_mod, ih i (by omega) w hw, ← Nat.add_mod]; congr 1; omega
        have hv1 := (h.kc true (τ + (j + 1))).validity _ hin v hv
        have hv2 := (h.kc false (τ + (j + 1))).validity _ hin v hv
        rcases getD_cases (x := cv (τ + D + j) v) hv1 hv2 with h3 | h3
        · rw [h3, Nat.mod_add_mod, Nat.add_assoc (y + 1)]
        · rw [h3, Nat.add_mod, ihj, ← Nat.add_mod, Nat.add_assoc (y + 1)]


/-! ### Helper lemmas for Lemma 5.6 -/

theorem leader_ne_none_iff {a n φ : ℕ} (ha : 0 < a) (hn : 0 < n) :
    leader a n (some φ) ≠ none ↔ φ % a = 0 := by
  have hlt : φ % (a * n) / a < n := Nat.div_lt_of_lt_mul (Nat.mod_lt _ (Nat.mul_pos ha hn))
  unfold leader
  by_cases h : φ % a = 0
  · simp [h, hlt]
  · simp [h]

theorem leader_eq_of_mod {a n φ : ℕ} (ha : 0 < a) (hn : 0 < n) (h : φ % a = 0) :
    ∃ hl, leader a n (some φ) = some ⟨φ % (a * n) / a, hl⟩ := by
  have hlt : φ % (a * n) / a < n := Nat.div_lt_of_lt_mul (Nat.mod_lt _ (Nat.mul_pos ha hn))
  exact ⟨hlt, by unfold leader; simp [h, hlt]⟩

/-- Among `m` consecutive leaders `ℓ₀, ℓ₀ + 1, … (mod n)`, each node occurs at most
`m / n + 1` times. -/
theorem count_residues {n : ℕ} (hn : 0 < n) (F : Finset (Fin n)) (ℓ₀ m : ℕ) :
    ((range m).filter fun J => (⟨(ℓ₀ + J) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ F).card ≤
      F.card * (m / n + 1) := by
  classical
  have hsub : ((range m).filter fun J => (⟨(ℓ₀ + J) % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ F) ⊆
      F.biUnion fun u => (range m).filter fun J => (ℓ₀ + J) % n = u := by
    intro J hJ
    simp only [mem_filter] at hJ
    simp only [mem_biUnion, mem_filter]
    exact ⟨_, hJ.2, hJ.1, rfl⟩
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  refine le_trans (sum_le_card_nsmul _ _ (m / n + 1) fun u _ => ?_) (by rw [smul_eq_mul])
  refine le_trans ?_ (Nat.ceilDiv_le_div_add_one m n)
  rw [← Nat.Ico_zero_eq_range]
  exact Nat.card_le_ceilDiv_of_subset_Ico hn (filter_subset _ _) fun J₁ h₁ J₂ h₂ =>
    Nat.ModEq.add_left_cancel' ℓ₀ ((mem_filter.1 h₁).2.trans (mem_filter.1 h₂).2.symm)

/-- If in each group `{4i, …, 4i+3}` at most one index fails `P`, then at least `3N` of the first
`4N` indices satisfy `P`. -/
theorem group_count (P : ℕ → Prop) [DecidablePred P] (N : ℕ)
    (h : ∀ i, i < N → ∀ k₁ k₂, k₁ < k₂ → k₂ < 4 → P (4 * i + k₁) ∨ P (4 * i + k₂)) :
    3 * N ≤ ((range (4 * N)).filter P).card := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih fun i hi => h i (by omega)
    rw [card_filter] at ih'
    rw [card_filter, show 4 * (N + 1) = 4 * N + 4 by ring, sum_range_add]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    have h01 := h N (by omega) 0 1 (by omega) (by omega)
    have h02 := h N (by omega) 0 2 (by omega) (by omega)
    have h03 := h N (by omega) 0 3 (by omega) (by omega)
    have h12 := h N (by omega) 1 2 (by omega) (by omega)
    have h13 := h N (by omega) 1 3 (by omega) (by omega)
    have h23 := h N (by omega) 2 3 (by omega) (by omega)
    simp only [Nat.add_zero] at h01 h02 h03
    by_cases p0 : P (4 * N) <;> by_cases p1 : P (4 * N + 1) <;> by_cases p2 : P (4 * N + 2) <;>
      by_cases p3 : P (4 * N + 3) <;> simp_all <;> omega

/-- Lemma 5.6 (existence of an unimpeded instance), with the constants `k₀ = 4D`, `k₁ = 5D` and a
filtering window `W ≥ 16 D - 1`: if the `b`-th filtered clock counts from `s₁` and the other
filtered clock satisfies crusader agreement with window `W` from `s₂`, an unimpeded `b`-th
instance with a correct leader starts before `max s₁ s₂ + 20 D (f + 1)`. -/
theorem lemma_5_6 {n D W : ℕ} {F : Finset (Fin n)} (hn : 3 * F.card < n) (hD : 1 ≤ D)
    (hW : 16 * D - 1 ≤ W) (fl : Bool → ℕ → Fin n → Option ℕ) (b : Bool) (s₁ s₂ : ℕ)
    (hb : OCountsFrom F (kk D b * n) (fl b) s₁)
    (hb' : Crusader F (kk D (!b) * n) W s₂ (fl (!b))) :
    ∃ τ ℓ, τ < max s₁ s₂ + 20 * D * (F.card + 1) ∧
      Unimpeded F D (fun b τ v => leader (kk D b) n (fl b τ v)) b τ ℓ := by
  classical
  have hn0 : 0 < n := by omega
  have ha : 4 * D ≤ kk D b ∧ kk D b ≤ 5 * D := by cases b <;> simp [kk] <;> omega
  have ha' : 4 * D ≤ kk D (!b) ∧ kk D (!b) ≤ 5 * D := by cases b <;> simp [kk] <;> omega
  have hkb : (if b then (D - 1 + 1) * 4 + (D - 1) + 1 else (D - 1 + 1) * 4) = kk D b := by
    cases b <;> simp [kk] <;> omega
  have hko : (if b then (D - 1 + 1) * 4 else (D - 1 + 1) * 4 + (D - 1) + 1) = kk D (!b) := by
    cases b <;> simp [kk] <;> omega
  set a := kk D b with ha_def
  set a' := kk D (!b) with ha'_def
  have ha0 : 0 < a := by omega
  have ha0' : 0 < a' := by omega
  obtain ⟨c₀, hc⟩ := hb
  set s := max s₁ s₂ with hs
  have hval : ∀ τ, s₁ ≤ τ → ∀ v, v ∉ F → fl b τ v = some ((c₀ + (τ - s₁)) % (a * n)) := by
    intro τ hτ v hv
    have := hc (τ - s₁) v hv
    rwa [show s₁ + (τ - s₁) = τ by omega] at this
  set τ₀ := s + (a - (c₀ + (s - s₁)) % a) % a with hτ₀
  have hτ₀s : s ≤ τ₀ ∧ τ₀ < s + a := ⟨by omega, by have := Nat.mod_lt (a - (c₀ + (s - s₁)) % a) ha0; omega⟩
  set E := c₀ + (τ₀ - s₁) with hE
  have hEa : E % a = 0 := by
    have h1 : E = (c₀ + (s - s₁)) + (a - (c₀ + (s - s₁)) % a) % a := by omega
    rw [h1, Nat.add_mod, Nat.mod_mod]
    have h2 := Nat.mod_lt (c₀ + (s - s₁)) ha0
    by_cases h3 : (c₀ + (s - s₁)) % a = 0
    · rw [h3]; simp
    · rw [Nat.mod_eq_of_lt (show a - (c₀ + (s - s₁)) % a < a by omega)]
      rw [show (c₀ + (s - s₁)) % a + (a - (c₀ + (s - s₁)) % a) = a by omega, Nat.mod_self]
  set ℓ₀ := E / a with hℓ₀
  have hEeq : E = a * ℓ₀ := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hEa)).symm
  let L : ℕ → Fin n := fun J => ⟨(ℓ₀ + J) % n, Nat.mod_lt _ hn0⟩
  -- the value of the `b`-th filtered clock at `τ₀ + a J + d`
  have hvalJ : ∀ J d, ∀ v, v ∉ F → fl b (τ₀ + a * J + d) v = some ((a * (ℓ₀ + J) + d) % (a * n)) := by
    intro J d v hv
    rw [hval _ (by omega) v hv]
    congr 2
    rw [mul_add, ← hEeq, hE]; omega
  have hlead : ∀ J, ∀ v, v ∉ F → leader a n (fl b (τ₀ + a * J) v) = some (L J) := by
    intro J v hv
    have := hvalJ J 0 v hv
    rw [Nat.add_zero, Nat.add_zero] at this
    rw [this]
    have hmod : a * (ℓ₀ + J) % (a * n) % a = 0 := by
      rw [Nat.mod_mod_of_dvd _ (Dvd.intro n rfl)]; simp
    obtain ⟨hl, hl'⟩ := leader_eq_of_mod ha0 hn0 hmod
    rw [hl']
    congr 1
    apply Fin.ext
    simp only [L, Nat.mod_mod, Nat.mul_mod_mul_left]
    rw [Nat.mul_div_cancel_left _ ha0]
  have hnolead : ∀ J d, 0 < d → d < a → ∀ v, v ∉ F →
      leader a n (fl b (τ₀ + a * J + d) v) = none := by
    intro J d hd hda v hv
    rw [hvalJ J d v hv]
    by_contra hne
    have h1 := (leader_ne_none_iff ha0 hn0).1 hne
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro n rfl), Nat.add_mod,
      Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hda] at h1
    omega
  -- collisions with the other schedule
  let coll : ℕ → Prop := fun J => ∃ d, d < D ∧ ∃ v, v ∉ F ∧
    leader a' n (fl (!b) (τ₀ + a * J + d) v) ≠ none
  have hgood : ∀ J, ¬ coll J → L J ∉ F →
      Unimpeded F D (fun b τ v => leader (kk D b) n (fl b τ v)) b (τ₀ + a * J) (L J) := by
    intro J hc hL
    refine ⟨hL, fun v hv => hlead J v hv, fun d hd v hv => ?_,
      fun d hd0 hdD v hv => hnolead J d hd0 (by omega) v hv⟩
    by_contra hne
    exact hc ⟨d, hd, v, hv, hne⟩
  -- Claim A: two instances at most three apart do not both collide (Lemma 5.5)
  have hA : ∀ J₁ J₂, J₁ < J₂ → J₂ ≤ J₁ + 3 → coll J₁ → coll J₂ → False := by
    rintro J₁ J₂ hlt hle ⟨d₁, hd₁, v₁, hv₁, hl₁⟩ ⟨d₂, hd₂, v₂, hv₂, hl₂⟩
    obtain ⟨Δ, rfl⟩ : ∃ Δ, J₂ = J₁ + Δ := ⟨J₂ - J₁, by omega⟩
    have hP : a * (J₁ + Δ) = a * J₁ + a * Δ := mul_add _ _ _
    have hP1 : a ≤ a * Δ := Nat.le_mul_of_pos_right _ (by omega)
    have hP3 : a * Δ ≤ a * 3 := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨c₁, hc₁⟩ : ∃ c, fl (!b) (τ₀ + a * J₁ + d₁) v₁ = some c := by
      cases h : fl (!b) (τ₀ + a * J₁ + d₁) v₁ with
      | none => rw [h] at hl₁; exact absurd rfl hl₁
      | some c => exact ⟨c, rfl⟩
    rw [hc₁] at hl₁
    have hl₁c := (leader_ne_none_iff ha0' hn0).1 hl₁
    set j := (τ₀ + a * (J₁ + Δ) + d₂) - (τ₀ + a * J₁ + d₁) with hj
    have hcr := hb' (τ₀ + a * J₁ + d₁) (by omega) v₁ hv₁ c₁ hc₁ j (by omega) v₂ hv₂
    rw [show τ₀ + a * J₁ + d₁ + j = τ₀ + a * (J₁ + Δ) + d₂ by omega] at hcr
    rcases hcr with h | h
    · exact hl₂ (by rw [h]; rfl)
    · rw [h] at hl₂
      have h2 := (leader_ne_none_iff ha0' hn0).1 hl₂
      rw [Nat.mod_mod_of_dvd _ (Dvd.intro n rfl), Nat.add_mod, hl₁c, zero_add, Nat.mod_mod] at h2
      have hmul : a' * (j / a') = j := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2)
      have hcol₁ : collides (if b then (D - 1 + 1) * 4 + (D - 1) + 1 else (D - 1 + 1) * 4)
          (if b then (D - 1 + 1) * 4 else (D - 1 + 1) * 4 + (D - 1) + 1) (D - 1)
          ((a * J₁ + d₁ : ℕ) : ℤ) J₁ := by
        rw [hkb, hko]; exact ⟨d₁, by omega, 0, by push_cast; ring⟩
      have hcol₂ : collides (if b then (D - 1 + 1) * 4 + (D - 1) + 1 else (D - 1 + 1) * 4)
          (if b then (D - 1 + 1) * 4 else (D - 1 + 1) * 4 + (D - 1) + 1) (D - 1)
          ((a * J₁ + d₁ : ℕ) : ℤ) (J₁ + Δ) := by
        rw [hkb, hko]
        refine ⟨d₂, by omega, ((j / a' : ℕ) : ℤ), ?_⟩
        have : a * (J₁ + Δ) + d₂ = a' * (j / a') + (a * J₁ + d₁) := by omega
        exact_mod_cast this
      have := collides_sep (D - 1) 4 (by norm_num) b _ hcol₁ hcol₂ (by omega)
      omega
  -- counting faulty leaders
  by_contra hno
  push Not at hno
  set f := F.card with hf
  have hbad : ∀ J, J < 4 * (f + 1) → L J ∈ F ∨ coll J := by
    intro J hJ
    by_contra hcon
    push Not at hcon
    refine hno (τ₀ + a * J) (L J) ?_ (hgood J hcon.2 hcon.1)
    have h1 : a * J ≤ a * (4 * f + 3) := Nat.mul_le_mul_left _ (by omega)
    have h2 : a * (4 * f + 3) + a ≤ 20 * D * (f + 1) := by nlinarith
    omega
  have hgc := group_count (fun J => L J ∈ F) (f + 1) (fun i hi k₁ k₂ hk hk2 => by
    by_contra hcon
    push Not at hcon
    have c1 := (hbad (4 * i + k₁) (by omega)).resolve_left hcon.1
    have c2 := (hbad (4 * i + k₂) (by omega)).resolve_left hcon.2
    exact hA _ _ (by omega) (by omega) c1 c2)
  have hcr := count_residues hn0 F ℓ₀ (4 * (f + 1))
  have h3 : 3 * (f * (4 * (f + 1) / n)) ≤ 4 * (f + 1) := by
    calc 3 * (f * (4 * (f + 1) / n)) = (3 * f) * (4 * (f + 1) / n) := by ring
      _ ≤ n * (4 * (f + 1) / n) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ 4 * (f + 1) := Nat.mul_div_le _ _
  have h4 : f * (4 * (f + 1) / n + 1) = f * (4 * (f + 1) / n) + f := by ring
  have h5 : ((range (4 * (f + 1))).filter fun J => L J ∈ F).card ≤
      f * (4 * (f + 1) / n + 1) := hcr
  omega

/-- Theorem 5.7 at the level of traces (second statement): if the `b`-th filtered clock counts from
`s₁` (e.g. `s₁ = S_C^b + S_F^b` when `V_b` has fewer than `|V_b|/3` faults, Lemma 5.1) and the other
filtered clock satisfies crusader agreement from `s₂ = S_F^{1-b}`, the output clocks count from
`max s₁ s₂ + 20 D (f + 1) + D`. -/
theorem theorem_5_7_trace {n C D W : ℕ} {F : Finset (Fin n)} {cv : ℕ → Fin n → ℕ}
    {fl : Bool → ℕ → Fin n → Option ℕ} {out : Bool → ℕ → Fin n → Option ℕ}
    (hn : 3 * F.card < n) (hD : 1 ≤ D) (hW : 16 * D - 1 ≤ W)
    (h : TraceHyp n C D (D - 1) F cv (fun b τ v => leader (kk D b) n (fl b τ v)) out)
    (b : Bool) (s₁ s₂ : ℕ) (hb : OCountsFrom F (kk D b * n) (fl b) s₁)
    (hb' : Crusader F (kk D (!b) * n) W s₂ (fl (!b))) :
    CountsFrom F C cv (max s₁ s₂ + 20 * D * (F.card + 1) + D) := by
  obtain ⟨τ, ℓ, hτ, hu⟩ := lemma_5_6 hn hD hW fl b s₁ s₂ hb hb'
  exact (lemma_5_4 hD h hu).mono (by omega)

end EarlyStabilizingCounting
