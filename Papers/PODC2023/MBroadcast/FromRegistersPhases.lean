import Papers.PODC2023.MBroadcast.FromRegisters

/-!
# The control skeleton of Algorithm 2 and of its causal variant

Both algorithms have the same control structure: a process is `idle` or inside `catch_up` at
loop index `j` (`Phase.catchUp own j`); its local step `tick` moves `idle → catchUp none 0`,
`catchUp o j → catchUp o (j+1)` for `j < n`, `catchUp o n → idle`; only an invocation
`idle → catchUp (some m) 0` changes its phase otherwise. This file proves, for any such sequence of
phases in which a process `r` takes infinitely many local steps, that `r` reaches every loop
index (and the end of every `catch_up`) infinitely often.
-/

namespace Podc.MBroadcast.FromRegisters

variable {n : ℕ} {M : Type}

/-- The effect of a local step on the phase of the process. -/
def tickPhase (n : ℕ) : Phase M → Phase M
  | .idle => .catchUp none 0
  | .catchUp o j => if j < n then .catchUp o (j + 1) else .idle

/-- The control skeleton of an execution: the phases and the actions. -/
structure Skeleton (n : ℕ) (M : Type) where
  phase : ℕ → Fin n → Phase M
  act : ℕ → Act n M
  /-- Other actions only change the phase of `r` by an invocation, from `idle`. -/
  other : ∀ k r, act k ≠ .tick r → phase (k + 1) r = phase k r ∨
    (phase k r = .idle ∧ ∃ m, phase (k + 1) r = .catchUp (some m) 0)
  /-- The effect of a local step. -/
  tick : ∀ k r, act k = .tick r → phase (k + 1) r = tickPhase n (phase k r)
  /-- The loop index is at most `n`. -/
  jle : ∀ k r o j, phase k r = .catchUp o j → j ≤ n

namespace Skeleton

variable (s : Skeleton n M) {r : Fin n}

/-- `r` takes infinitely many local steps. -/
def Ticks (r : Fin n) : Prop := ∀ k, ∃ k' ≥ k, s.act k' = .tick r

variable {s}

lemma next_tick (hf : s.Ticks r) (k : ℕ) :
    ∃ k' ≥ k, s.act k' = .tick r ∧ ∀ i, k ≤ i → i < k' → s.act i ≠ .tick r := by
  have hex : ∃ d, s.act (k + d) = .tick r := by
    obtain ⟨k', hk', h⟩ := hf k; exact ⟨k' - k, by rw [Nat.add_sub_cancel' hk']; exact h⟩
  classical
  refine ⟨k + Nat.find hex, by omega, Nat.find_spec hex, fun i hi hi' => ?_⟩
  have := Nat.find_min hex (m := i - k) (by omega)
  rwa [Nat.add_sub_cancel' hi] at this

lemma persist_cu {o : Option M} {j k k' : ℕ} (hph : s.phase k r = .catchUp o j)
    (hk : k ≤ k') (hno : ∀ i, k ≤ i → i < k' → s.act i ≠ .tick r) :
    s.phase k' r = .catchUp o j := by
  induction hk with
  | refl => exact hph
  | @step k' hk ih =>
    have ih := ih (fun i hi hi' => hno i hi (by omega))
    rcases s.other k' r (hno k' hk (by omega)) with h | ⟨h, _⟩
    · rw [h, ih]
    · rw [ih] at h; cases h

lemma persist_idle {k k' : ℕ} (hph : s.phase k r = .idle)
    (hk : k ≤ k') (hno : ∀ i, k ≤ i → i < k' → s.act i ≠ .tick r) :
    s.phase k' r = .idle ∨ ∃ m, s.phase k' r = .catchUp (some m) 0 ∧
      ∃ k2, k ≤ k2 ∧ k2 < k' ∧ s.phase k2 r = .idle ∧ s.phase (k2 + 1) r = .catchUp (some m) 0 := by
  induction hk with
  | refl => exact Or.inl hph
  | @step k' hk ih =>
    have ih := ih (fun i hi hi' => hno i hi (by omega))
    rcases s.other k' r (hno k' hk (by omega)) with h | ⟨h0, m, h⟩
    · rw [h]
      rcases ih with ih | ⟨m, h1, k2, hk2, hk2', h2, h3⟩
      · exact Or.inl ih
      · exact Or.inr ⟨m, h1, k2, hk2, by omega, h2, h3⟩
    · exact Or.inr ⟨m, h, k', hk, by omega, h0, h⟩

variable (hf : s.Ticks r)
include hf

/-- From inside `catch_up` at index `j ≤ q`, `r` eventually executes the iteration `q`. -/
lemma reach_index {q : ℕ} (hq : q < n) : ∀ (d : ℕ) {o : Option M} {j k : ℕ}, q - j = d → j ≤ q →
    s.phase k r = .catchUp o j →
    ∃ k' ≥ k, s.act k' = .tick r ∧ s.phase k' r = .catchUp o q := by
  intro d
  induction d with
  | zero =>
    intro o j k hd hj hph
    obtain ⟨k1, hk1, ht, hno⟩ := next_tick hf k
    have := persist_cu hph hk1 hno
    exact ⟨k1, hk1, ht, by rw [this]; congr; omega⟩
  | succ d ih =>
    intro o j k hd hj hph
    obtain ⟨k1, hk1, ht, hno⟩ := next_tick hf k
    have h1 := persist_cu hph hk1 hno
    have h2 : s.phase (k1 + 1) r = .catchUp o (j + 1) := by
      rw [s.tick k1 r ht, h1, tickPhase, ite_eq_left (by omega)]
    obtain ⟨k', hk', h⟩ := ih (by omega) (by omega) h2
    exact ⟨k', by omega, h⟩

/-- From inside `catch_up`, `r` eventually executes the end of this `catch_up`. -/
lemma reach_end : ∀ (d : ℕ) {o : Option M} {j k : ℕ}, n - j = d → j ≤ n →
    s.phase k r = .catchUp o j → ∃ k' ≥ k, s.act k' = .tick r ∧ s.phase k' r = .catchUp o n := by
  intro d
  induction d with
  | zero =>
    intro o j k hd hj hph
    obtain ⟨k1, hk1, ht, hno⟩ := next_tick hf k
    have := persist_cu hph hk1 hno
    exact ⟨k1, hk1, ht, by rw [this]; congr; omega⟩
  | succ d ih =>
    intro o j k hd hj hph
    obtain ⟨k1, hk1, ht, hno⟩ := next_tick hf k
    have h1 := persist_cu hph hk1 hno
    have h2 : s.phase (k1 + 1) r = .catchUp o (j + 1) := by
      rw [s.tick k1 r ht, h1, tickPhase, ite_eq_left (by omega)]
    obtain ⟨k', hk', h⟩ := ih (by omega) (by omega) h2
    exact ⟨k', by omega, h⟩

/-- `r` is eventually idle. -/
lemma reach_idle (k : ℕ) : ∃ k' ≥ k, s.phase k' r = .idle := by
  cases hph : s.phase k r with
  | idle => exact ⟨k, le_rfl, hph⟩
  | catchUp o j =>
    obtain ⟨k1, hk1, ht, h1⟩ := reach_end hf _ rfl (s.jle k r o j hph) hph
    refine ⟨k1 + 1, by omega, ?_⟩
    rw [s.tick k1 r ht, h1, tickPhase, ite_eq_right (by omega)]

/-- From `idle`, `r` eventually starts a `catch_up`; if it is the one of an `mbroadcast(m)`, the
invocation happened after `k`. -/
lemma reach_start {k : ℕ} (hph : s.phase k r = .idle) :
    ∃ k' ≥ k, ∃ o, s.phase k' r = .catchUp o 0 ∧ ∀ m, o = some m →
      ∃ k2, k ≤ k2 ∧ k2 < k' ∧ s.phase k2 r = .idle ∧ s.phase (k2 + 1) r = .catchUp (some m) 0 := by
  obtain ⟨k1, hk1, ht, hno⟩ := next_tick hf k
  rcases persist_idle hph hk1 hno with h | ⟨m, h, hk2⟩
  · refine ⟨k1 + 1, by omega, none, ?_, fun m hm => by cases hm⟩
    rw [s.tick k1 r ht, h, tickPhase]
  · exact ⟨k1, hk1, some m, h, fun m' hm' => by cases hm'; exact hk2⟩

/-- After any time `k`, `r` executes the iteration `q` of a `catch_up`; if this `catch_up` is the
one of an `mbroadcast(m)`, the invocation happened after `k`. -/
lemma eventually_index {q : ℕ} (hq : q < n) (k : ℕ) :
    ∃ k' ≥ k, ∃ o, s.act k' = .tick r ∧ s.phase k' r = .catchUp o q ∧ ∀ m, o = some m →
      ∃ k2, k ≤ k2 ∧ k2 < k' ∧ s.phase k2 r = .idle ∧ s.phase (k2 + 1) r = .catchUp (some m) 0 := by
  obtain ⟨k0, hk0, h0⟩ := reach_idle hf k
  obtain ⟨k1, hk1, o, h1, hfresh⟩ := reach_start hf h0
  obtain ⟨k', hk', ht, h⟩ := reach_index hf hq _ rfl (Nat.zero_le _) h1
  refine ⟨k', by omega, o, ht, h, fun m hm => ?_⟩
  obtain ⟨k2, hk2, hk2', h2⟩ := hfresh m hm
  exact ⟨k2, by omega, by omega, h2⟩

end Skeleton

end Podc.MBroadcast.FromRegisters
