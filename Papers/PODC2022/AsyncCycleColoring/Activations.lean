import Papers.PODC2022.AsyncCycleColoring.Model
import Papers.PODC2022.AsyncCycleColoring.Changes

/-!
# Generic facts about activations

* registers and local states are constant on time intervals in which a process is not active;
* a process acts at most once more than the number of its failed (non-returning) activations;
* the last activation before a given time.
-/

namespace AsyncCycle

variable {n : ℕ} {S O : Type*} (A : Alg S O) (init : ZMod n → S) (σ : ℕ → Finset (ZMod n))

/-- `p` fails (does not return) at time `t + 1`. -/
def FailsAt (t : ℕ) (p : ZMod n) : Prop := ActsAt A init σ t p ∧ ∃ s, resAt A init σ t p = Sum.inl s

/-- `p` returns at time `t + 1`. -/
def RetAt (t : ℕ) (p : ZMod n) : Prop := ActsAt A init σ t p ∧ ∃ o, resAt A init σ t p = Sum.inr o

lemma failsAt_or_retAt {t : ℕ} {p : ZMod n} (h : ActsAt A init σ t p) :
    FailsAt A init σ t p ∨ RetAt A init σ t p := by
  rcases hr : resAt A init σ t p with s | o
  · exact Or.inl ⟨h, s, hr⟩
  · exact Or.inr ⟨h, o, hr⟩

/-- After returning, a process never acts again. -/
lemma not_actsAt_of_retAt {t t' : ℕ} {p : ZMod n} (h : RetAt A init σ t p) (htt' : t < t') :
    ¬ ActsAt A init σ t' p := by
  obtain ⟨ha, o, ho⟩ := h
  have h1 := out_succ_of_inr A init σ ha ho
  have h2 := out_mono A init σ (Nat.succ_le_of_lt htt') h1
  exact not_acts_of_out A init σ h2

/-- An activation followed by a later activation is a failure. -/
lemma failsAt_of_actsAt_later {t t' : ℕ} {p : ZMod n} (h : ActsAt A init σ t p) (htt' : t < t')
    (h' : ActsAt A init σ t' p) : FailsAt A init σ t p := by
  rcases failsAt_or_retAt A init σ h with hf | hr
  · exact hf
  · exact absurd h' (not_actsAt_of_retAt A init σ hr htt')

/-- Registers and local states do not change while a process is inactive. -/
lemma reg_loc_const {p : ZMod n} {a : ℕ} :
    ∀ b, a ≤ b → (∀ s, a ≤ s → s < b → ¬ ActsAt A init σ s p) →
      (run A init σ b).reg p = (run A init σ a).reg p ∧
        (run A init σ b).loc p = (run A init σ a).loc p := by
  intro b hab h
  induction b, hab using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ b hab ih =>
    have hb : ¬ ActsAt A init σ b p := h b hab (Nat.lt_succ_self b)
    obtain ⟨ih1, ih2⟩ := ih (fun s h1 h2 => h s h1 (Nat.lt_succ_of_lt h2))
    exact ⟨(reg_succ_of_not_acts A init σ hb).trans ih1, (loc_succ_of_not_acts A init σ hb).trans ih2⟩

/-- Once written, a register is never `⊥` again. -/
lemma reg_ne_none_mono {p : ZMod n} {a b : ℕ} (hab : a ≤ b) (h : (run A init σ a).reg p ≠ none) :
    (run A init σ b).reg p ≠ none := by
  induction b, hab using Nat.le_induction with
  | base => exact h
  | succ b _ ih =>
    rw [reg_succ]; split_ifs
    · simp
    · exact ih

/-- The last activation of `p` in `[t₀, t)`, given one at `t₀ < t`. -/
lemma exists_last_act {p : ZMod n} {t₀ t : ℕ} (h₀ : ActsAt A init σ t₀ p) (ht : t₀ < t) :
    ∃ t'', t₀ ≤ t'' ∧ t'' < t ∧ ActsAt A init σ t'' p ∧
      ∀ s, t'' < s → s < t → ¬ ActsAt A init σ s p := by
  induction t, ht using Nat.le_induction with
  | base => exact ⟨t₀, le_rfl, Nat.lt_succ_self _, h₀, fun s h1 h2 => by omega⟩
  | succ t hle ih =>
    by_cases ht : ActsAt A init σ t p
    · exact ⟨t, Nat.le_of_succ_le hle, Nat.lt_succ_self _, ht, fun s h1 h2 => by omega⟩
    · obtain ⟨t'', h1, h2, h3, h4⟩ := ih
      refine ⟨t'', h1, Nat.lt_succ_of_lt h2, h3, fun s hs1 hs2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs2 with hs | rfl
      · exact h4 s hs1 hs
      · exact ht

open Classical in
/-- Working activations are the failures plus at most one return. -/
lemma workActs_le_fails (p : ZMod n) (T : ℕ) :
    workActs A init σ p T ≤
      ((Finset.range T).filter (fun t => FailsAt A init σ t p)).card + 1 := by
  unfold workActs
  have hsub : (Finset.range T).filter (fun t => ActsAt A init σ t p) ⊆
      (Finset.range T).filter (fun t => FailsAt A init σ t p) ∪
        (Finset.range T).filter (fun t => RetAt A init σ t p) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_union] at ht ⊢
    rcases failsAt_or_retAt A init σ ht.2 with h | h
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨ht.1, h⟩
  have hret : ((Finset.range T).filter (fun t => RetAt A init σ t p)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact not_actsAt_of_retAt A init σ ha.2 h hb.2.1
    · exact not_actsAt_of_retAt A init σ hb.2 h ha.2.1
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

end AsyncCycle
