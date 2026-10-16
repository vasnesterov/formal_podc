import Papers.PODC2018.AtomicCrossChainSwaps.Protocol

/-!
# Basic facts about runs of the protocol model
-/

namespace AtomicSwap

namespace Setting

variable {V : Type*} [DecidableEq V] [Fintype V] (P : Setting V) (C : Finset V)
  (sch : ℕ → Moves V)

local notation "S" t => P.run C sch t

@[simp] lemma run_zero : P.run C sch 0 = St.init := rfl
lemma run_succ (t : ℕ) : P.run C sch (t + 1) = P.step C t (P.run C sch t) (sch t) := rfl

/-! ### Monotonicity -/

lemma con_succ {t : ℕ} {u v : V} {c : ℕ} (h : (S t).con u v = some c) :
    (S (t + 1)).con u v = some c := by
  simp [run_succ, step, h]

lemma unl_succ {t : ℕ} {u v ℓ : V} {x : ℕ × List V} (h : (S t).unl u v ℓ = some x) :
    (S (t + 1)).unl u v ℓ = some x := by
  simp [run_succ, step, h]

lemma rel_succ {t : ℕ} {v : V} {r : ℕ} (h : (S t).rel v = some r) :
    (S (t + 1)).rel v = some r := by
  simp [run_succ, step, h]

lemma con_mono {t t' : ℕ} (htt : t ≤ t') {u v : V} {c : ℕ} (h : (S t).con u v = some c) :
    (S t').con u v = some c := by
  induction htt with
  | refl => exact h
  | step _ ih => exact P.con_succ C sch ih

lemma unl_mono {t t' : ℕ} (htt : t ≤ t') {u v ℓ : V} {x : ℕ × List V}
    (h : (S t).unl u v ℓ = some x) : (S t').unl u v ℓ = some x := by
  induction htt with
  | refl => exact h
  | step _ ih => exact P.unl_succ C sch ih

lemma unl_isSome_mono {t t' : ℕ} (htt : t ≤ t') {u v ℓ : V}
    (h : ((S t).unl u v ℓ).isSome) : ((S t').unl u v ℓ).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  simp [P.unl_mono C sch htt hx]

lemma con_isSome_mono {t t' : ℕ} (htt : t ≤ t') {u v : V}
    (h : ((S t).con u v).isSome) : ((S t').con u v).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  simp [P.con_mono C sch htt hx]

lemma rel_mono {t t' : ℕ} (htt : t ≤ t') {v : V} {r : ℕ} (h : (S t).rel v = some r) :
    (S t').rel v = some r := by
  induction htt with
  | refl => exact h
  | step _ ih => exact P.rel_succ C sch ih

lemma sub_succ (t : ℕ) (u v ℓ : V) :
    (S (t + 1)).sub u v ℓ = (S t).sub u v ℓ ++ P.roundKeys C t (S t) (sch t) u v ℓ := rfl

lemma sub_mono {t t' : ℕ} (htt : t ≤ t') {u v ℓ : V} {p : List V}
    (h : p ∈ (S t).sub u v ℓ) : p ∈ (S t').sub u v ℓ := by
  induction htt with
  | refl => exact h
  | step _ ih => rw [sub_succ]; exact List.mem_append_left _ ih

lemma known_mono {t t' : ℕ} (htt : t ≤ t') {ℓ : V} {q : List V} (h : (S t).Known ℓ q) :
    (S t').Known ℓ q := by
  obtain ⟨u, v, p, hp, hq⟩ := h
  exact ⟨u, v, p, P.sub_mono C sch htt hp, hq⟩

/-! ### Contracts -/

lemma con_succ_iff {t : ℕ} {u v : V} {c : ℕ} :
    (S (t + 1)).con u v = some c ↔ (S t).con u v = some c ∨ ((S t).con u v = none ∧
      c = t + 1 ∧ P.D.Adj u v ∧ (P.Publishes C t (S t) u ∨ (u ∈ C ∧ (u, v) ∈ (sch t).pubs))) := by
  rw [run_succ]
  simp only [step]
  cases h : (S t).con u v with
  | some c' => simp
  | none =>
    simp only [Option.none_or, reduceCtorEq, false_or, true_and]
    split_ifs with h1 <;> simp [h1, eq_comm]

lemma con_le {t : ℕ} {u v : V} {c : ℕ} (h : (S t).con u v = some c) : 1 ≤ c ∧ c ≤ t := by
  induction t generalizing c with
  | zero => simp [St.init] at h
  | succ t ih =>
    rcases (P.con_succ_iff C sch).mp h with h | ⟨-, rfl, -⟩
    · have := ih h; omega
    · omega

/-- Where a contract came from: its arc, and the round in which it was submitted. -/
lemma con_origin {t : ℕ} {u v : V} {c : ℕ} (h : (S t).con u v = some c) :
    (S (c - 1)).con u v = none ∧ P.D.Adj u v ∧
      (P.Publishes C (c - 1) (S (c - 1)) u ∨ (u ∈ C ∧ (u, v) ∈ (sch (c - 1)).pubs)) := by
  induction t generalizing c with
  | zero => simp [St.init] at h
  | succ t ih =>
    rcases (P.con_succ_iff C sch).mp h with h | ⟨h0, rfl, ha, hp⟩
    · exact ih h
    · simpa using ⟨h0, ha, hp⟩

/-- The state at the publication time of a contract already shows it. -/
lemma con_at_landing {t : ℕ} {u v : V} {c : ℕ} (h : (S t).con u v = some c) :
    (S c).con u v = some c := by
  obtain ⟨h0, ha, hp⟩ := P.con_origin C sch h
  have h1 := (P.con_le C sch h).1
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  simp only [add_tsub_cancel_right] at h0 hp
  exact (P.con_succ_iff C sch).mpr (Or.inr ⟨h0, rfl, ha, hp⟩)

/-- A conforming party publishes a contract only on its leaving arcs; a conforming follower only
after all its entering arcs carry contracts; a conforming leader in round `0`. -/
lemma con_conforming {t : ℕ} {u v : V} {c : ℕ} (h : (S t).con u v = some c) (hu : u ∉ C) :
    P.D.Adj u v ∧ (u ∈ P.L → c = 1) ∧ (u ∉ P.L → P.AllIn (S (c - 1)) u) := by
  obtain ⟨-, ha, hp | ⟨hu', -⟩⟩ := P.con_origin C sch h
  · have := P.con_le C sch h
    refine ⟨ha, fun hl => ?_, fun hl => hp.2.2 hl⟩
    have := hp.2.1 hl; omega
  · exact absurd hu' hu

/-! ### Unlocks -/

lemma newKey_ok {t : ℕ} {s : St V} {m : Moves V} {u v ℓ : V} {p : List V}
    (h : P.newKey C t s m u v ℓ = some p) : P.Ok t s u v ℓ p := by
  unfold newKey at h
  split_ifs at h
  · have := List.find?_some h; simpa using this
  · simp only [Option.filter_eq_some_iff] at h
    simpa using h.2

lemma newKey_mem {t : ℕ} {s : St V} {m : Moves V} {u v ℓ : V} {p : List V}
    (h : P.newKey C t s m u v ℓ = some p) : p ∈ P.roundKeys C t s m u v ℓ := by
  unfold newKey at h
  unfold roundKeys
  split_ifs at h
  · exact List.mem_append_right _ (List.mem_of_find?_eq_some h)
  · simp only [Option.filter_eq_some_iff] at h
    simp [h.1]

lemma unl_succ_iff {t : ℕ} {u v ℓ : V} {x : ℕ × List V} :
    (S (t + 1)).unl u v ℓ = some x ↔ (S t).unl u v ℓ = some x ∨ ((S t).unl u v ℓ = none ∧
      x.1 = t + 1 ∧ P.newKey C t (S t) (sch t) u v ℓ = some x.2) := by
  rw [run_succ]
  simp only [step]
  cases h : (S t).unl u v ℓ with
  | some c' => simp
  | none =>
    simp only [Option.none_or, reduceCtorEq, false_or, true_and, Option.map_eq_some_iff]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨rfl, hp⟩
    · rintro ⟨h1, h2⟩; exact ⟨x.2, h2, by ext <;> simp [h1]⟩

/-- Where an unlock came from: it was a successful call in round `τ - 1`. -/
lemma unl_origin {t : ℕ} {u v ℓ : V} {τ : ℕ} {p : List V} (h : (S t).unl u v ℓ = some (τ, p)) :
    1 ≤ τ ∧ τ ≤ t ∧ (S (τ - 1)).unl u v ℓ = none ∧
      P.newKey C (τ - 1) (S (τ - 1)) (sch (τ - 1)) u v ℓ = some p := by
  induction t with
  | zero => simp [St.init] at h
  | succ t ih =>
    rcases (P.unl_succ_iff C sch).mp h with h | ⟨h0, h1, h2⟩
    · have := ih h; exact ⟨this.1, by omega, this.2.2⟩
    · simp only at h1 h2; subst h1; simpa using ⟨h0, h2⟩

/-- The state at the landing time of an unlock already shows it. -/
lemma unl_at_landing {t : ℕ} {u v ℓ : V} {τ : ℕ} {p : List V}
    (h : (S t).unl u v ℓ = some (τ, p)) : (S τ).unl u v ℓ = some (τ, p) := by
  obtain ⟨h1, -, h0, hk⟩ := P.unl_origin C sch h
  obtain ⟨k, rfl⟩ : ∃ k, τ = k + 1 := ⟨τ - 1, by omega⟩
  simp only [add_tsub_cancel_right] at h0 hk
  exact (P.unl_succ_iff C sch).mpr (Or.inr ⟨h0, rfl, hk⟩)

/-- Properties of a successful unlock. -/
lemma unl_ok {t : ℕ} {u v ℓ : V} {τ : ℕ} {p : List V} (h : (S t).unl u v ℓ = some (τ, p)) :
    1 ≤ τ ∧ τ ≤ t ∧ P.Ok (τ - 1) (S (τ - 1)) u v ℓ p ∧ p ∈ (S τ).sub u v ℓ := by
  obtain ⟨h1, h2, -, hk⟩ := P.unl_origin C sch h
  refine ⟨h1, h2, P.newKey_ok C hk, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, τ = k + 1 := ⟨τ - 1, by omega⟩
  rw [sub_succ]
  simp only [add_tsub_cancel_right] at hk
  exact List.mem_append_right _ (P.newKey_mem C hk)

lemma unl_known {t : ℕ} {u v ℓ : V} {τ : ℕ} {p : List V} (h : (S t).unl u v ℓ = some (τ, p)) :
    (S t).Known ℓ p := by
  obtain ⟨-, hτ, -, hp⟩ := P.unl_ok C sch h
  exact ⟨u, v, p, P.sub_mono C sch hτ hp, List.suffix_refl p⟩

/-- An unlocked hashlock lies on an arc that has a contract (published before the unlock). -/
lemma unl_con {t : ℕ} {u v ℓ : V} {τ : ℕ} {p : List V} (h : (S t).unl u v ℓ = some (τ, p)) :
    ∃ c, c < τ ∧ (S t).con u v = some c := by
  obtain ⟨h1, hτ, ⟨hc, -⟩, -⟩ := P.unl_ok C sch h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
  have := P.con_le C sch hc
  exact ⟨c, by omega, P.con_mono C sch (by omega) hc⟩

/-! ### Stabilization -/

omit [DecidableEq V] in
lemma key_length_le {ℓ v : V} {p : List V} (h : IsKey P.D ℓ v p) :
    p.length ≤ Fintype.card V + 1 := h.1.length_le

/-- No unlock can succeed after time `B + |V|`. -/
lemma unl_stable {t : ℕ} (ht : P.B + Fintype.card V ≤ t) (u v ℓ : V) :
    (S t).unl u v ℓ = (S (P.B + Fintype.card V)).unl u v ℓ := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [← ih]
    cases h : (S (t + 1)).unl u v ℓ with
    | none =>
      cases h' : (S t).unl u v ℓ with
      | none => rfl
      | some x => rw [P.unl_succ C sch h'] at h; cases h
    | some x =>
      rcases (P.unl_succ_iff C sch).mp h with h | ⟨-, -, hk⟩
      · exact h.symm
      · have hok := P.newKey_ok C hk
        have := P.key_length_le hok.2.2.1
        have := hok.2.2.2
        unfold dl at this
        omega

lemma final_iff (u v : V) :
    P.Final C sch u v ↔ P.Trig (S (P.B + Fintype.card V)) u v := by
  constructor
  · rintro ⟨t, ht⟩ ℓ hℓ
    rcases le_total t (P.B + Fintype.card V) with h | h
    · exact P.unl_isSome_mono C sch h (ht ℓ hℓ)
    · rw [← P.unl_stable C sch h]; exact ht ℓ hℓ
  · exact fun h => ⟨_, h⟩

end Setting

end AtomicSwap
