/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Inv

/-!
# Consequences of the invariant: persistence and uniqueness of accepted entries

Pure consequences of the invariant `Inv` (no protocol steps involved):

* Invariant 2 in its "persistence" form (`Inv.accL_persist`, `Inv.accL_le`): an accepted entry is
  in the base state of every later started epoch, together with the prefix of its log;
* Invariant 11 (`Inv.accL_unique_slot`, `Inv.accL_unique_txn`): accepted entries of a shard are
  unique per slot, and a transaction is accepted in at most one slot;
* uniqueness of possible decisions (`Inv.decided_unique`);
* the prefix property (`Inv.accL_prefix`): entries accepted below an accepted entry are in the log
  of its origin epoch.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq Pl] [DecidableEq S] [DecidableEq P] [Fintype S]

theorem meetOver_eq_commit {sh : Finset S} {ds : S → Dec} :
    meetOver sh ds = .commit ↔ ∀ s ∈ sh, ds s = .commit := by
  unfold meetOver
  split_ifs with h
  · simpa using h
  · simpa using h

namespace Inv

variable {Pa : Params T Pl S P} {st : State T Pl S P}

/-- A started epoch is configured. -/
theorem cfg_of_started (hI : Inv Pa st) {s : S} {E : ℕ} (h : st.started s E = true) :
    ∃ c, cfg st s E = some c :=
  ⟨_, List.getElem?_eq_getElem (hI.started_cfg s E h)⟩

omit [DecidableEq Pl] [DecidableEq S] [Fintype S] in
/-- An accepted slot is alive. -/
theorem aliveK_of_accL {s : S} {e k : ℕ} {v : Entry T Pl × ℕ} (h : AccL st s e k v) :
    AliveK st s e k := by
  obtain ⟨-, c, hc, hq⟩ := h
  intro c' hc' q hq'
  rw [hc] at hc'
  cases hc'
  exact Or.inl ⟨_, _, hq q hq'⟩

/-- Invariant 2 (persistence): an entry accepted at epoch `e` is in the base state of every
later started epoch `E`, and the base state of `E` below it is contained in the log of `e`. -/
theorem accL_persist (hI : Inv Pa st) {s : S} {e E k : ℕ} {v : Entry T Pl × ℕ}
    (h : AccL st s e k v) (hlt : e < E) (hE : st.started s E = true) :
    st.base s E k = some v ∧ ∀ j < k, ∀ y, st.base s E j = some y → st.elog s e j = some y := by
  obtain ⟨c, hc⟩ := hI.cfg_of_started hE
  have := hI.inv2 s E c hc (Or.inl hE) e hlt k v h.1 (aliveK_of_accL h)
  simpa [cand, hE] using this

/-- An accepted entry is in the log of every later started epoch, in the same slot. -/
theorem accL_le (hI : Inv Pa st) {s : S} {e E k : ℕ} {v : Entry T Pl × ℕ} (h : AccL st s e k v)
    (hle : e ≤ E) (hE : st.started s E = true) : st.elog s E k = some v := by
  rcases hle.lt_or_eq with hlt | rfl
  · exact hI.base_elog _ _ _ _ (hI.accL_persist h hlt hE).1
  · exact h.1

/-- Invariant 11 (first part): accepted entries in the same slot coincide. -/
theorem accL_unique_slot (hI : Inv Pa st) {s : S} {e₁ e₂ k : ℕ} {v₁ v₂ : Entry T Pl × ℕ}
    (h₁ : AccL st s e₁ k v₁) (h₂ : AccL st s e₂ k v₂) : v₁ = v₂ := by
  wlog hle : e₁ ≤ e₂ generalizing e₁ e₂ v₁ v₂
  · exact (this h₂ h₁ (le_of_not_ge hle)).symm
  have := hI.accL_le h₁ hle (hI.elog_started _ _ _ _ h₂.1)
  rw [h₂.1] at this
  exact (Option.some.inj this).symm

/-- Invariant 11 (second part): a transaction is accepted in at most one slot. -/
theorem accL_unique_txn (hI : Inv Pa st) {s : S} {e₁ e₂ k₁ k₂ : ℕ} {v₁ v₂ : Entry T Pl × ℕ}
    (h₁ : AccL st s e₁ k₁ v₁) (h₂ : AccL st s e₂ k₂ v₂) (ht : v₁.1.1 = v₂.1.1) : k₁ = k₂ := by
  wlog hle : e₁ ≤ e₂ generalizing e₁ e₂ k₁ k₂ v₁ v₂
  · exact (this h₂ h₁ ht.symm (le_of_not_ge hle)).symm
  have := hI.accL_le h₁ hle (hI.elog_started _ _ _ _ h₂.1)
  exact hI.elog_dist _ _ _ _ _ _ this h₂.1 ht

/-- Entries accepted below an accepted entry are in the log of its origin epoch. -/
theorem accL_prefix (hI : Inv Pa st) {s : S} {e e' k j : ℕ} {v w : Entry T Pl × ℕ}
    (h : AccL st s e k v) (h' : AccL st s e' j w) (hjk : j < k) : st.elog s v.2 j = some w := by
  obtain ⟨-, -, hpre⟩ := hI.elog_origin s e k v.1 v.2 h.1
  apply hpre j hjk
  rcases le_or_gt e' e with hle | hlt
  · exact hI.accL_le h' hle (hI.elog_started _ _ _ _ h.1)
  · have hE := hI.elog_started _ _ _ _ h'.1
    obtain ⟨hk, hpre'⟩ := hI.accL_persist h hlt hE
    cases hb : st.base s e' j with
    | none =>
      have := hI.elog_above s e' j w h'.1 hb k hjk.le
      rw [hk] at this
      cases this
    | some y =>
      have hy := hI.base_elog _ _ _ _ hb
      rw [h'.1] at hy
      cases hy
      exact hpre' j hjk _ hb

/-- Decisions are unique. -/
theorem decided_unique (hI : Inv Pa st) {t : T} {d₁ d₂ : Dec} (h₁ : Decided Pa st t d₁)
    (h₂ : Decided Pa st t d₂) : d₁ = d₂ := by
  obtain ⟨es, ks, vs, hv, rfl⟩ := h₁
  obtain ⟨es', ks', vs', hv', rfl⟩ := h₂
  have heq : ∀ s ∈ Pa.σ.shards t, vs s = vs' s := by
    intro s hs
    obtain ⟨h1, ht1⟩ := hv s hs
    obtain ⟨h2, ht2⟩ := hv' s hs
    have hk := hI.accL_unique_txn h1 h2 (ht1.trans ht2.symm)
    rw [hk] at h1
    exact hI.accL_unique_slot h1 h2
  have hiff : (∀ s ∈ Pa.σ.shards t, (vs s).1.2.2 = .commit) ↔
      (∀ s ∈ Pa.σ.shards t, (vs' s).1.2.2 = .commit) :=
    forall₂_congr fun s hs => by rw [heq s hs]
  simp only [meetOver, hiff]

end Inv

end Podc.ReconfigurableCommit
