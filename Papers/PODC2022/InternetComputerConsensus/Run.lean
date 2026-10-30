import Papers.PODC2022.InternetComputerConsensus.Deadlock

/-!
# Runs with the "wait for" semantics, and step analysis

A run is a sequence of global states starting in the initial state, consecutive states being
related by `UStep` (time advances only when every honest party is settled).
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

set_option linter.unusedSectionVars false

variable {P V : Type*} [Fintype P] [DecidableEq P] {π : Params P} {F : Finset P}

/-- A run with the "wait for" semantics. -/
structure IsRun (π : Params P) (F : Finset P) (σ : ℕ → GState P V) : Prop where
  init : σ 0 = GState.init F
  step : ∀ i, UStep π F (σ i) (σ (i + 1))

/-- Party `q` has entered round `k` (it has computed the round-`k` beacon). -/
def Entered (s : GState P V) (q : P) (k : ℕ) : Prop :=
  k < (s.loc q).round ∨ ((s.loc q).round = k ∧ (s.loc q).active = true)

/-! ### Step analysis -/

theorem UStep.step' {s s' : GState P V} (h : UStep π F s s') : Step π F s s' := by
  cases h with
  | step _ h _ => exact h
  | tick _ => exact Step.tick _

theorem UStep.cases' {s s' : GState P V} (h : UStep π F s s') :
    s'.now = s.now ∨ ((∀ p ∉ F, Settled π s p) ∧ s' = { s with now := s.now + 1 }) := by
  cases h with
  | step _ _ h => exact Or.inl h
  | tick h => exact Or.inr ⟨h, rfl⟩

theorem Step.sent_mono {s s' : GState P V} (h : Step π F s s') : s.sent ⊆ s'.sent := by
  cases h with
  | deliver => exact le_rfl
  | act => exact Set.subset_union_left
  | tick => exact le_rfl

/-- The effect of a step on a local state: unchanged, or a delivery, or a clause. -/
theorem Step.loc_cases {s s' : GState P V} (h : Step π F s s') (q : P) :
    s'.loc q = s.loc q ∨ (∃ m, s'.loc q = { s.loc q with pool := insert m (s.loc q).pool }) ∨
    (q ∉ F ∧ ∃ l M, LStep π s.now q (s.loc q) l M ∧ s'.loc q = { l with pool := l.pool ∪ M } ∧
      s'.sent = s.sent ∪ M) := by
  cases h with
  | deliver p m hp hm =>
    by_cases hq : q = p
    · subst hq; right; left; exact ⟨m, by simp⟩
    · left; simp [Function.update_of_ne hq]
  | act p l M hp hl =>
    by_cases hq : q = p
    · subst hq; right; right; exact ⟨hp, l, M, hl, by simp, rfl⟩
    · left; simp [Function.update_of_ne hq]
  | tick => left; rfl

theorem LStep.pool_eq {now : ℕ} {q : P} {l l' : LState P V} {M : Set (Msg P V)}
    (h : LStep π now q l l' M) : l'.pool = l.pool := by
  cases h <;> rfl

theorem Step.pool_mono {s s' : GState P V} (h : Step π F s s') (q : P) :
    (s.loc q).pool ⊆ (s'.loc q).pool := by
  rcases h.loc_cases q with e | ⟨m, e⟩ | ⟨-, l, M, hl, e, -⟩ <;> rw [e]
  · exact Set.subset_insert _ _
  · rw [hl.pool_eq]; exact Set.subset_union_left

theorem Step.now_le {s s' : GState P V} (h : Step π F s s') : s.now ≤ s'.now := by
  cases h with
  | deliver => exact le_rfl
  | act => exact le_rfl
  | tick => exact Nat.le_succ _

theorem LStep.round_le {now : ℕ} {q : P} {l l' : LState P V} {M : Set (Msg P V)}
    (h : LStep π now q l l' M) : l.round ≤ l'.round := by
  cases h <;> simp [LState.start]

theorem LStep.entered_mono {now : ℕ} {q : P} {l l' : LState P V} {M : Set (Msg P V)}
    (h : LStep π now q l l' M) {k : ℕ}
    (hk : k < l.round ∨ (l.round = k ∧ l.active = true)) :
    k < l'.round ∨ (l'.round = k ∧ l'.active = true) := by
  cases h with
  | beacon => simpa [LState.start] using hk.imp id (fun h => h.1)
  | finish B ha => left; simp only; rcases hk with h | ⟨h, _⟩ <;> omega
  | _ => exact hk

theorem Step.entered_mono {s s' : GState P V} (h : Step π F s s') {q : P} {k : ℕ}
    (hk : Entered s q k) : Entered s' q k := by
  unfold Entered at *
  rcases h.loc_cases q with e | ⟨m, e⟩ | ⟨-, l, M, hl, e, -⟩ <;> rw [e]
  · exact hk
  · exact hk
  · exact hl.entered_mono hk

/-- Once round `k` has been entered, its start time no longer changes. -/
theorem Step.t0_stable {s s' : GState P V} (h : Step π F s s') {q : P} {k : ℕ}
    (hk : Entered s q k) : (s'.loc q).t0 k = (s.loc q).t0 k := by
  rcases h.loc_cases q with e | ⟨m, e⟩ | ⟨-, l, M, hl, e, -⟩ <;> rw [e]
  cases hl with
  | beacon ha _ =>
    simp only [LState.start]
    rw [Function.update_of_ne]
    rintro rfl
    unfold Entered at hk; rw [ha] at hk; simp at hk
  | _ => rfl

/-- Entering round `k` sets its start time to the current time. -/
theorem Step.t0_of_enter {s s' : GState P V} (h : Step π F s s') {q : P} {k : ℕ}
    (hk : ¬ Entered s q k) (hk' : Entered s' q k) : (s'.loc q).t0 k = s.now := by
  unfold Entered at hk hk'
  rcases h.loc_cases q with e | ⟨m, e⟩ | ⟨-, l, M, hl, e, -⟩ <;> rw [e] at hk' ⊢
  · exact absurd hk' hk
  · exact absurd hk' hk
  · cases hl with
    | beacon ha _ =>
      simp only [LState.start] at hk' ⊢
      rcases hk' with hk' | ⟨rfl, -⟩
      · exact absurd (Or.inl hk') hk
      · simp
    | finish B ha =>
      simp only at hk'
      exfalso
      rcases hk' with h | ⟨-, h⟩
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h | h
        exacts [hk (Or.inl h), hk (Or.inr ⟨h.symm, ha⟩)]
      · simp at h
    | _ => exact absurd hk' hk

/-- A new notarization share is cast by an echo whose guards hold. -/
theorem Step.new_share {s s' : GState P V} (h : Step π F s s') {B : Block P V} {q : P}
    (h' : Msg.notarShare B q ∈ s'.sent) (hn : Msg.notarShare B q ∉ s.sent) :
    q ∉ F ∧ (s.loc q).active = true ∧ B.round = (s.loc q).round ∧
    Valid (s.loc q).pool B ∧ B.rk π.rank ∉ (s.loc q).D ∧
    (s.loc q).t0 (s.loc q).round + π.Δntry (B.rk π.rank) ≤ s.now ∧
    (∀ B', Valid (s.loc q).pool B' → B'.round = (s.loc q).round →
      B'.rk π.rank < B.rk π.rank → B'.rk π.rank ∈ (s.loc q).D) := by
  cases h with
  | deliver => exact absurd h' hn
  | tick => exact absurd h' hn
  | act p l M hp hl =>
    rcases h' with h' | h'
    · exact absurd h' hn
    cases hl with
    | echoShare B₀ h1 h2 h3 h4 h5 h6 h7 h8 =>
      simp only [Set.mem_ofPred_eq, reduceCtorEq, false_or, or_false, and_false,
        Msg.notarShare.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨hp, h1, h2, h3, h5, h6, h7⟩
    | beacon => simp at h'
    | finish => simp at h'
    | propose => simp at h'
    | echoDisq => simp at h'
    | final => simp at h'

/-- A round increase is clause (a). -/
theorem Step.finish_of_round_lt {s s' : GState P V} (h : Step π F s s') {q : P}
    (hlt : (s.loc q).round < (s'.loc q).round) :
    q ∉ F ∧ (s'.loc q).round = (s.loc q).round + 1 ∧ (s.loc q).active = true ∧
    ∃ B : Block P V, B.round = (s.loc q).round ∧ Valid (s.loc q).pool B ∧
      (Msg.notar B ∈ (s.loc q).pool ∨ NotarShares π (s.loc q).pool B) ∧
      ((s.loc q).N ⊆ {B} → Msg.finalShare B q ∈ s'.sent) := by
  rcases h.loc_cases q with e | ⟨m, e⟩ | ⟨hq, l, M, hl, e, hs⟩
  · rw [e] at hlt; omega
  · rw [e] at hlt; simp at hlt
  · rw [e] at hlt ⊢
    cases hl with
    | finish B h1 h2 h3 h4 =>
      refine ⟨hq, rfl, h1, B, h2, h3, h4, fun hN => ?_⟩
      rw [hs]; exact Or.inr (Or.inr ⟨hN, rfl⟩)
    | beacon => simp [LState.start] at hlt
    | _ => simp at hlt

/-! ### Runs -/

variable {σ : ℕ → GState P V}

theorem IsRun.reachable (hσ : IsRun π F σ) : ∀ i, Reachable π F (σ i)
  | 0 => by rw [hσ.init]; exact Relation.ReflTransGen.refl
  | i + 1 => (hσ.reachable i).tail (hσ.step i).step'

theorem IsRun.mono {X : GState P V → α} {r : α → α → Prop} [IsPreorder α r]
    (hσ : IsRun π F σ) (hX : ∀ s s', Step π F s s' → r (X s) (X s')) {i j : ℕ} (hij : i ≤ j) :
    r (X (σ i)) (X (σ j)) := by
  induction j, hij using Nat.le_induction with
  | base => exact refl _
  | succ j _ ih => exact _root_.trans ih (hX _ _ (hσ.step j).step')

theorem IsRun.now_mono (hσ : IsRun π F σ) {i j : ℕ} (hij : i ≤ j) : (σ i).now ≤ (σ j).now :=
  hσ.mono (X := GState.now) (fun _ _ h => h.now_le) hij

theorem IsRun.sent_mono (hσ : IsRun π F σ) {i j : ℕ} (hij : i ≤ j) :
    (σ i).sent ⊆ (σ j).sent :=
  hσ.mono (X := GState.sent) (r := (· ⊆ ·)) (fun _ _ h => h.sent_mono) hij

theorem IsRun.pool_mono (hσ : IsRun π F σ) (q : P) {i j : ℕ} (hij : i ≤ j) :
    ((σ i).loc q).pool ⊆ ((σ j).loc q).pool :=
  hσ.mono (X := fun s => (s.loc q).pool) (r := (· ⊆ ·)) (fun _ _ h => h.pool_mono q) hij

theorem IsRun.entered_mono (hσ : IsRun π F σ) {q : P} {k : ℕ} {i j : ℕ} (hij : i ≤ j)
    (h : Entered (σ i) q k) : Entered (σ j) q k := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j _ ih => exact (hσ.step j).step'.entered_mono ih

theorem IsRun.t0_stable (hσ : IsRun π F σ) {q : P} {k : ℕ} {i j : ℕ} (hij : i ≤ j)
    (h : Entered (σ i) q k) : ((σ j).loc q).t0 k = ((σ i).loc q).t0 k := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih => rw [(hσ.step j).step'.t0_stable (hσ.entered_mono hij h), ih]

/-- Before time `X ≥ 1` is reached, there is a tick from `X - 1` to `X`, taken from a state in
which every honest party is settled. -/
theorem IsRun.exists_tick (hσ : IsRun π F σ) {X : ℕ} (hX : 1 ≤ X) :
    ∀ j, X ≤ (σ j).now → ∃ i < j, (σ i).now + 1 = X ∧ (∀ p ∉ F, Settled π (σ i) p) ∧
      σ (i + 1) = { σ i with now := (σ i).now + 1 }
  | 0, h => by rw [hσ.init] at h; simp [GState.init] at h; omega
  | j + 1, h => by
    by_cases hj : X ≤ (σ j).now
    · obtain ⟨i, hi, h1, h2, h3⟩ := hσ.exists_tick hX j hj
      exact ⟨i, by omega, h1, h2, h3⟩
    · rcases (hσ.step j).cases' with he | ⟨hset, he⟩
      · omega
      · refine ⟨j, by omega, ?_, hset, he⟩
        rw [he] at h; simp only at h; omega
