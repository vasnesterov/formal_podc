import Papers.PODC2025.TwoStepConsensusLB.Model

/-!
# Generic facts about runs (used for the upper bounds)

* `Run.mem_inbox`: the messages delivered to `x` at time `τ` are exactly those sent at some
  `τ' < τ` with delivery time `τ`.
* `Run.mem_inbox_of_gst`: after GST, a message between correct processes sent at `τ` is delivered
  at `τ + 1`.
* `Run.invariant`: induction principle for system invariants (a state invariant `SI` and a
  message invariant `MI` indexed by the sending time).
* `Run.st_mono`: a property preserved by every step of a process persists.
-/

set_option linter.unusedSectionVars false

-- CSLib candidate: generic facts about `Cslib.CrashPartialSync` runs (kept in that namespace so
-- that dot notation `R.mem_inbox` works).
namespace Cslib.CrashPartialSync.Run

variable {P V M S : Type*} [Fintype P] [DecidableEq P]
variable (A : Protocol P V M S) (R : Run P V M)

theorem mem_canon {x : P} {τ : ℕ} {q : P} {m : M} :
    (q, m) ∈ R.canon A x τ ↔ ∃ τ' < τ, R.dl q τ' x = τ ∧ m ∈ R.out A q τ' x := by
  rw [canon_eq_flatMap]
  simp only [List.mem_flatMap, List.mem_range, Finset.mem_toList, Finset.mem_univ, true_and,
    List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨τ', hτ', q', ⟨m', hm', rfl, rfl⟩⟩
    unfold dlv at hm'
    split_ifs at hm' with h
    · exact ⟨τ', hτ', h, hm'⟩
    · simp at hm'
  · rintro ⟨τ', hτ', hd, hm⟩
    exact ⟨τ', hτ', q, m, by simpa [dlv, hd] using hm, rfl, rfl⟩

theorem mem_inbox (hR : IsOrder R.ord) {x : P} {τ : ℕ} {q : P} {m : M} :
    (q, m) ∈ R.inbox A x τ ↔ ∃ τ' < τ, R.dl q τ' x = τ ∧ m ∈ R.out A q τ' x := by
  unfold inbox
  rw [(hR x τ _).mem_iff, mem_canon]

theorem mem_inbox_of_gst {f : ℕ} (hR : R.Valid f) {q x : P} (hq : R.crash q = none)
    (hx : R.crash x = none) {τ : ℕ} (hτ : R.gst ≤ τ) {m : M} (hm : m ∈ R.out A q τ x) :
    (q, m) ∈ R.inbox A x (τ + 1) := by
  rw [mem_inbox A R hR.ord_perm]
  refine ⟨τ, by omega, ?_, hm⟩
  have h1 := hR.dl_ge q τ x hq hx
  have h2 := hR.dl_le q τ x hq hx
  rw [max_eq_left hτ] at h2
  omega

/-- **Invariant principle.** A state invariant `SI τ p` (for the state of `p` at time `τ`) and a
message invariant `MI τ q` (for the messages sent by `q` at time `τ`), established by every step,
hold throughout the run. -/
theorem invariant (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m) :
    ∀ τ, (∀ p, SI τ p (R.st A τ p)) ∧ ∀ τ' < τ, ∀ q x m, m ∈ R.out A q τ' x → MI τ' q m := by
  intro τ
  induction τ with
  | zero => exact ⟨h0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ τ ih =>
    obtain ⟨ihS, ihM⟩ := ih
    have hin : ∀ p q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m := by
      intro p q m h
      obtain ⟨τ', hτ', -, hm⟩ := (mem_inbox A R hR).1 h
      exact ⟨τ', hτ', ihM τ' hτ' q p m hm⟩
    refine ⟨fun p => ?_, fun τ' hτ' q x m hm => ?_⟩
    · by_cases ha : R.alive p τ
      · exact (hstep τ p ha (ihS p) (hin p)).1
      · rw [st_succ_of_not_alive A R (by simpa using ha)]
        exact hmono _ _ _ (ihS p)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hτ' with h | rfl
      · exact ihM τ' h q x m hm
      · by_cases ha : R.alive q τ'
        · exact (hstep τ' q ha (ihS q) (hin q)).2 x m hm
        · rw [out_of_not_alive A R (by simpa using ha)] at hm
          simp at hm

theorem invariant_st (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m)
    (τ : ℕ) (p : P) : SI τ p (R.st A τ p) :=
  (invariant A R hR SI MI h0 hmono hstep τ).1 p

theorem invariant_out (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m)
    {τ : ℕ} {q x : P} {m : M} (hm : m ∈ R.out A q τ x) : MI τ q m :=
  (invariant A R hR SI MI h0 hmono hstep (τ + 1)).2 τ (by omega) q x m hm

/-- Messages in an inbox satisfy the message invariant at some earlier time. -/
theorem invariant_inbox (hR : IsOrder R.ord) (SI : ℕ → P → S → Prop) (MI : ℕ → P → M → Prop)
    (h0 : ∀ p, SI 0 p (A.init p))
    (hmono : ∀ τ p s, SI τ p s → SI (τ + 1) p s)
    (hstep : ∀ τ p, R.alive p τ → SI τ p (R.st A τ p) →
      (∀ q m, (q, m) ∈ R.inbox A p τ → ∃ τ' < τ, MI τ' q m) →
      SI (τ + 1) p (R.st A (τ + 1) p) ∧ ∀ x, ∀ m ∈ R.out A p τ x, MI τ p m)
    {τ : ℕ} {q x : P} {m : M} (hm : (q, m) ∈ R.inbox A x τ) : ∃ τ' < τ, MI τ' q m := by
  obtain ⟨τ', hτ', -, h⟩ := (mem_inbox A R hR).1 hm
  exact ⟨τ', hτ', invariant_out A R hR SI MI h0 hmono hstep h⟩

/-- A property of local states preserved by every step of `p` persists. -/
theorem st_mono (Φ : S → Prop) {p : P}
    (h : ∀ τ s inv l, Φ s → Φ (A.step p τ s inv l)) {τ τ' : ℕ} (hle : τ ≤ τ')
    (hΦ : Φ (R.st A τ p)) : Φ (R.st A τ' p) := by
  induction hle with
  | refl => exact hΦ
  | step _ ih =>
    rw [st_succ]
    split_ifs
    · exact h _ _ _ _ ih
    · exact ih

end Cslib.CrashPartialSync.Run
