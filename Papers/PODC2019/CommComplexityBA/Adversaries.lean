import Papers.PODC2019.CommComplexityBA.Basic

/-!
# The two adversaries of the proof of Theorem 4

* `deafAdv V` (the paper's adversary `A`): statically corrupts `V`; nodes of `V` behave honestly
  except that they ignore *every* message they receive (the paper only lets them ignore the first
  `f/2` messages from `U` and the messages from `V`; ignoring all of them is simpler and the proof is
  unchanged, see `differencies.md`).
* `blockAdv V p k` (the paper's adversary `A'` for a fixed choice of `p`): corrupts `V \ {p}`
  statically, lets them ignore all messages and not talk to `p`; and as long as at most `k` messages
  from `U = Vᶜ` to `p` have been sent so far (counting the current round), it corrupts the senders of
  these messages and removes them **after the fact**. It corrupts at most `|V| - 1 + k` nodes.

`deaf_run_eq_block_run`: if under `deafAdv V` at most `k` messages from `U` to `p` are sent in the
whole execution, the two executions coincide.
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA

variable {P I M Ω : Type*} [Fintype P] [DecidableEq P] {f : ℕ}

/-- Raise the corruption budget of an adversary. -/
def Adversary.mono {f f' : ℕ} (A : Adversary P f) (h : f ≤ f') : Adversary P f' where
  corrupt := A.corrupt
  drop := A.drop
  corrupt_mono := A.corrupt_mono
  card_corrupt l := (A.card_corrupt l).trans h
  drop_spec := A.drop_spec

/-- The paper's adversary `A`: `V` is corrupted and deaf. -/
def deafAdv (V : Finset P) (hV : V.card ≤ f) : Adversary P f where
  corrupt _ := V
  drop _ _ q := decide (q ∈ V)
  corrupt_mono _ _ := le_rfl
  card_corrupt _ := hV
  drop_spec _ _ _ h := Or.inr (by simpa using h)

/-! ### Counting messages from `U = Vᶜ` to `p` -/

section Count

variable (V : Finset P) (p : P)

/-- Senders outside `V` that send to `p` in a round with pattern `pat`. -/
def sendersTo (pat : Pattern P) : Finset P := Finset.univ.filter fun s => s ∉ V ∧ pat s p = true

/-- Number of messages from `Vᶜ` to `p` in the rounds `l`. -/
def cum : List (Pattern P) → ℕ
  | [] => 0
  | x :: l => (sendersTo V p x).card + cum l

/-- All senders outside `V` that sent to `p` in the rounds `l`. -/
def allSenders : List (Pattern P) → Finset P
  | [] => ∅
  | x :: l => sendersTo V p x ∪ allSenders l

lemma cum_append (l₁ l₂ : List (Pattern P)) : cum V p (l₁ ++ l₂) = cum V p l₁ + cum V p l₂ := by
  induction l₁ with
  | nil => simp [cum]
  | cons x l ih => simp [cum, ih]; omega

lemma allSenders_append (l₁ l₂ : List (Pattern P)) :
    allSenders V p (l₁ ++ l₂) = allSenders V p l₁ ∪ allSenders V p l₂ := by
  induction l₁ with
  | nil => simp [allSenders]
  | cons x l ih => simp [allSenders, ih, Finset.union_assoc]

lemma card_allSenders_le (l : List (Pattern P)) : (allSenders V p l).card ≤ cum V p l := by
  induction l with
  | nil => simp [allSenders, cum]
  | cons x l ih => exact (Finset.card_union_le _ _).trans (by simp [cum]; omega)

lemma allSenders_mono {l₁ l₂ : List (Pattern P)} (h : l₁ <+: l₂) :
    allSenders V p l₁ ⊆ allSenders V p l₂ := by
  obtain ⟨t, rfl⟩ := h
  rw [allSenders_append]; exact Finset.subset_union_left

lemma not_mem_allSenders (l : List (Pattern P)) {s : P} (hs : s ∈ V) : s ∉ allSenders V p l := by
  induction l with
  | nil => simp [allSenders]
  | cons x l ih => simp [allSenders, sendersTo, hs, ih]

variable (k : ℕ)

/-- Length of the longest prefix of `l` with at most `k` messages from `Vᶜ` to `p`. -/
def jmax (l : List (Pattern P)) : ℕ := Nat.findGreatest (fun j => cum V p (l.take j) ≤ k) l.length

/-- Senders blocked so far by `blockAdv`. -/
def blocked (l : List (Pattern P)) : Finset P := allSenders V p (l.take (jmax V p k l))

lemma card_blocked_le (l : List (Pattern P)) : (blocked V p k l).card ≤ k :=
  (card_allSenders_le V p _).trans
    (Nat.findGreatest_spec (P := fun j => cum V p (l.take j) ≤ k) (Nat.zero_le _) (by simp [cum]))

lemma blocked_mono (l : List (Pattern P)) (x : Pattern P) :
    blocked V p k l ⊆ blocked V p k (l ++ [x]) := by
  have hle : jmax V p k l ≤ l.length := Nat.findGreatest_le _
  have hj : jmax V p k l ≤ jmax V p k (l ++ [x]) := by
    apply Nat.le_findGreatest (by simp; omega)
    rw [List.take_append_of_le_length hle]
    exact Nat.findGreatest_spec (P := fun j => cum V p (l.take j) ≤ k) (Nat.zero_le _)
      (by simp [cum])
  unfold blocked
  rw [← List.take_append_of_le_length (l₂ := [x]) hle]
  exact allSenders_mono V p (List.take_prefix_take_left hj)

lemma blocked_of_cum_le (l : List (Pattern P)) (h : cum V p l ≤ k) :
    blocked V p k l = allSenders V p l := by
  unfold blocked jmax
  rw [Nat.findGreatest_eq (P := fun j => cum V p (l.take j) ≤ k) (by simpa using h)]
  simp

end Count

/-- The paper's adversary `A'` (for a fixed `p ∈ V`). -/
def blockAdv (V : Finset P) (p : P) (k : ℕ) : Adversary P ((V.erase p).card + k) where
  corrupt l := V.erase p ∪ blocked V p k l
  drop l s q := decide (q ∈ V.erase p ∨ (s ∈ V.erase p ∧ q = p) ∨
    (q = p ∧ cum V p l ≤ k ∧ s ∈ allSenders V p l))
  corrupt_mono l x := Finset.union_subset_union le_rfl (blocked_mono V p k l x)
  card_corrupt l := (Finset.card_union_le _ _).trans
    (add_le_add le_rfl (card_blocked_le V p k l))
  drop_spec l s q h := by
    simp only [decide_eq_true_eq] at h
    rcases h with h | ⟨h, -⟩ | ⟨-, hc, hs⟩
    · exact Or.inr (Finset.mem_union_left _ h)
    · exact Or.inl (Finset.mem_union_left _ h)
    · exact Or.inl (Finset.mem_union_right _ (by rw [blocked_of_cum_le V p k l hc]; exact hs))

lemma blockAdv_card_corrupt (V : Finset P) (p : P) (k : ℕ) (l : List (Pattern P)) :
    ((blockAdv V p k).corrupt l).card ≤ (V.erase p).card + k := (blockAdv V p k).card_corrupt l

lemma not_mem_blockAdv_corrupt (V : Finset P) {p : P} (hp : p ∈ V) (k : ℕ)
    (l : List (Pattern P)) : p ∉ (blockAdv V p k).corrupt l := by
  simp only [blockAdv, blocked, Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false,
    false_and, false_or]
  exact not_mem_allSenders V p _ hp

namespace Protocol

variable (π : Protocol P I M Ω) (inp : P → I) (ω : Ω)

/-- Messages from `Vᶜ` to `p` in round `r` of the execution under `deafAdv`. -/
def cntRound (V : Finset P) (hV : V.card ≤ f) (p : P) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun s => s ∉ V ∧ π.sentAt inp ω (deafAdv V hV) r s p = true).card

lemma cum_run (V : Finset P) (hV : V.card ≤ f) (p : P) (r : ℕ) :
    cum V p (π.run inp ω (deafAdv V hV) r).2 = ∑ i ∈ Finset.range r, π.cntRound inp ω V hV p i := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [run]
    rw [runD_pats_succ, cum_append]
    simp [cum, cntRound, sendersTo, sentAt, run]
    rfl

/-- Total number of messages from `Vᶜ` to `p` under `deafAdv V`. -/
noncomputable def cntTo (V : Finset P) (hV : V.card ≤ f) (p : P) : ENNReal :=
  ∑' r, (π.cntRound inp ω V hV p r : ENNReal)

lemma cum_run_le (V : Finset P) (hV : V.card ≤ f) (p : P) (r : ℕ) :
    (cum V p (π.run inp ω (deafAdv V hV) r).2 : ENNReal) ≤ π.cntTo inp ω V hV p := by
  rw [cum_run, Nat.cast_sum]
  exact ENNReal.sum_le_tsum _

/-- **Coupling** (the heart of the paper's indistinguishability argument): if under `deafAdv V`
fewer than `k + 1` messages from `Vᶜ` reach `p ∈ V`, the executions under `deafAdv V` and
`blockAdv V p k` are identical. -/
lemma deaf_run_eq_block_run (V : Finset P) (hV : V.card ≤ f) {p : P} (hp : p ∈ V) (k : ℕ)
    (hcnt : π.cntTo inp ω V hV p < k + 1) (r : ℕ) :
    π.run inp ω (deafAdv V hV) r = π.run inp ω (blockAdv V p k) r := by
  refine π.runD_congr inp ω _ _ (fun r s q hsq => ?_) r
  have hcum : cum V p (π.runD inp ω (deafAdv V hV).drop (r + 1)).2 ≤ k := by
    have h1 := π.cum_run_le inp ω V hV p (r + 1)
    have h2 : (cum V p (π.runD inp ω (deafAdv V hV).drop (r + 1)).2 : ENNReal) < k + 1 :=
      lt_of_le_of_lt h1 hcnt
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h2)
  have hs_mem : s ∉ V → q = p → s ∈ allSenders V p (π.runD inp ω (deafAdv V hV).drop (r + 1)).2 := by
    rintro hs rfl
    rw [runD_pats_succ, allSenders_append]
    refine Finset.mem_union_right _ ?_
    simp [allSenders, sendersTo, hs, hsq]
  have hne : s ≠ q := by
    rintro rfl; simp [msg] at hsq
  simp only [deafAdv, blockAdv, Finset.mem_erase, ne_eq]
  by_cases hq : q ∈ V
  · by_cases hqp : q = p
    · subst hqp
      by_cases hs : s ∈ V
      · simp [hq, hs, hne]
      · simp only [hq, hs, hne]
        simp
        exact ⟨hcum, hs_mem hs rfl⟩
    · simp [hq, hqp]
  · have hqp : q ≠ p := fun h => hq (h ▸ hp)
    simp [hq, hqp]

/-- Under `deafAdv V`, nodes of `V` never receive anything. -/
lemma deaf_hist (V : Finset P) (hV : V.card ≤ f) {p : P} (hp : p ∈ V) (r : ℕ) :
    (π.run inp ω (deafAdv V hV) r).1 p = List.replicate r fun _ => none := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [run] at ih ⊢
    rw [runD_hist_succ, ih, List.replicate_succ']
    simp [deafAdv, hp]

lemma deaf_output (V : Finset P) (hV : V.card ≤ f) {p : P} (hp : p ∈ V) :
    π.output inp ω (deafAdv V hV) p = π.silentOut p (inp p) ω := by
  simp only [output, silentOut, π.deaf_hist inp ω V hV hp]

lemma deaf_honest_iff (V : Finset P) (hV : V.card ≤ f) (u : P) :
    π.Honest inp ω (deafAdv V hV) u ↔ u ∉ V := by
  simp [Honest, deafAdv]

end Protocol

end CommComplexityBA
