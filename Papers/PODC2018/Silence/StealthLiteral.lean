import Papers.PODC2018.Silence.Stealth

/-!
# Literal readings of STEALTH's Figure 1 are not AC protocols

`stealthWith K ES f` is STEALTH (`Stealth.lean`) with the predicate "knows `all[1]`" replaced by
`K` and the predicate "saw `err`" (which decides the commit at time 3) replaced by `ES`; with
`K = hasAll1`, `ES = errSeen f` it is `stealth n f` (`stealthWith_eq`).

* `literal0_not_solvesAC`: process `0` checks only the `n − 1` first-round messages of the others
  (ignoring its own value, as in "n − 1 first-round messages in the case of process 0", §4.2).
* `literalErr_not_solvesAC`: a process commits at time 3 iff it *received* no `err` (its own `err`
  is not counted, as in Figure 1, round 4).

Both violate Commit Validity in `γ_1` with `n = 3`.
-/

namespace Papers.PODC2018.Silence.Stealth

open Cslib.SyncCrash Classical

variable {n : ℕ} [NeZero n]

/-- History predicates. -/
abbrev HPred (n : ℕ) := Fin n → Bool → Cslib.Byzantine.LockStep.History (Fin n) Unit → Prop

variable (n) in
/-- STEALTH with "knows `all[1]`" := `K` and "saw `err`" := `ES`. -/
noncomputable def stealthWith (K ES : HPred n) (f : ℕ) : ACProtocol (Fin n) Unit where
  send p x h q :=
    if h.length = 0 then (if x = true ∧ q = 0 then some () else none)
    else if h.length = 1 then
      (if p = 0 ∧ K p x h ∧ 1 ≤ q.val ∧ q.val ≤ f then some () else none)
    else if h.length = 2 then (if choir f p ∧ ¬ K p x h then some () else none)
    else if h.length = 3 then (if ES p x h then some () else none)
    else if h.length ≤ f + 3 then
      (if (ES p x h ∨ ∃ j, rcv h 3 j ≠ none) ∧
          ((¬ ES p x h ∨ K p x h) ∨ ∃ t', 4 ≤ t' ∧ t' < h.length ∧ ∃ j, rcv h t' j ≠ none)
        then some () else none)
    else none
  decide p x h :=
    if h.length = 3 ∧ ¬ ES p x h then some .commit
    else if h.length = f + 4 ∧ ES p x h then
      (if (¬ ES p x h ∨ K p x h) ∨ ∃ t', 4 ≤ t' ∧ t' < h.length ∧ ∃ j, rcv h t' j ≠ none
        then some .commit else some .abort)
    else none

/-- With the paper's intended predicates, `stealthWith` is exactly `stealth`. -/
lemma stealthWith_eq (f : ℕ) : stealthWith n hasAll1 (errSeen f) f = stealth n f := by
  unfold stealthWith stealth part bit vhat; congr!

variable {K ES : HPred n} {f : ℕ} {r : Run (Fin n) Bool} {j p : Fin n}

section Eqns
variable {x : Bool} {h : Cslib.Byzantine.LockStep.History (Fin n) Unit} {q : Fin n}

lemma W_len0 (hh : h.length = 0) :
    (stealthWith n K ES f).send p x h q = if x = true ∧ q = 0 then some () else none := by
  show (if h.length = 0 then _ else _) = _
  rw [if_pos hh]

lemma W_len1 (hh : h.length = 1) :
    (stealthWith n K ES f).send p x h q =
      if p = 0 ∧ K p x h ∧ 1 ≤ q.val ∧ q.val ≤ f then some () else none := by
  show (if h.length = 0 then _ else _) = _
  rw [if_neg (by omega), if_pos hh]

lemma W_len2 (hh : h.length = 2) :
    (stealthWith n K ES f).send p x h q = if choir f p ∧ ¬ K p x h then some () else none := by
  show (if h.length = 0 then _ else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos hh]

lemma W_dec3 (hh : h.length = 3) (hES : ¬ ES p x h) :
    (stealthWith n K ES f).decide p x h = some .commit := by
  show (if h.length = 3 ∧ ¬ ES p x h then _ else _) = _
  rw [if_pos ⟨hh, hES⟩]

end Eqns

lemma W_sent0 : Sent (stealthWith n K ES f) r j p 0 ↔
    j ≠ p ∧ r.Deliv j p 0 ∧ r.input j = true ∧ p = 0 := by
  rw [sent_iff_deliv, W_len0 (length_hist _ _ _)]
  by_cases h : r.input j = true ∧ p = 0
  · simp [h]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]; tauto

lemma W_sent1 : Sent (stealthWith n K ES f) r j p 1 ↔
    j ≠ p ∧ r.Deliv j p 1 ∧ j = 0 ∧ K j (r.input j) (hist (stealthWith n K ES f) r 1 j) ∧
      1 ≤ p.val ∧ p.val ≤ f := by
  rw [sent_iff_deliv, W_len1 (length_hist _ _ _)]
  by_cases h : j = 0 ∧ K j (r.input j) (hist (stealthWith n K ES f) r 1 j) ∧ 1 ≤ p.val ∧
      p.val ≤ f
  · simp [h]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]; tauto

lemma W_sent2 : Sent (stealthWith n K ES f) r j p 2 ↔
    j ≠ p ∧ r.Deliv j p 2 ∧ choir f j ∧ ¬ K j (r.input j) (hist (stealthWith n K ES f) r 2 j) := by
  rw [sent_iff_deliv, W_len2 (length_hist _ _ _)]
  by_cases h : choir f j ∧ ¬ K j (r.input j) (hist (stealthWith n K ES f) r 2 j)
  · simp [h]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]; tauto

lemma W_commit3 (ha : r.Alive p 3) (hES : ¬ ES p (r.input p) (hist (stealthWith n K ES f) r 3 p)) :
    DecidesAt (stealthWith n K ES f) r p 3 .commit := by
  rw [decidesAt_iff]
  exact ⟨ha, W_dec3 (length_hist _ _ _) hES⟩

/-- Process `0` checks only the others' first-round messages (ignores its own value). -/
def hasAll1Literal (p : Fin n) (_ : Bool) (h : Cslib.Byzantine.LockStep.History (Fin n) Unit) :
    Prop :=
  (p = 0 ∧ ∀ j, j ≠ 0 → rcv h 0 j ≠ none) ∨ (p ≠ 0 ∧ rcv h 1 0 ≠ none)

/-- "Saw `err`" with `hasAll1Literal` in place of `hasAll1`. -/
def errSeenLiteral (f : ℕ) (p : Fin n) (x : Bool)
    (h : Cslib.Byzantine.LockStep.History (Fin n) Unit) : Prop :=
  (∃ j, rcv h 2 j ≠ none) ∨ (choir f p ∧ ¬ hasAll1Literal p x h)

variable (n) in
/-- STEALTH read literally: process `0` sends `all[1]` after `n − 1` first-round messages. -/
noncomputable def stealthLiteral0 (f : ℕ) : ACProtocol (Fin n) Unit :=
  stealthWith n hasAll1Literal (errSeenLiteral f) f

/-- **Literal reading 1 fails.** If process `0` ignores its own value (it only checks the `n − 1`
first-round messages of the others), then in `γ_1` with `n = 3`, in the failure-free run with
`v₀ = 0` and `v₁ = v₂ = 1`, process `2` commits at time 3: Commit Validity is violated. -/
theorem literal0_not_solvesAC : ¬ SolvesAC (stealthLiteral0 3 1) 1 := by
  intro hAC
  let r : Run (Fin 3) Bool := ⟨fun p => decide (p ≠ 0), fun _ => none, fun _ => ∅⟩
  have hnf : ∀ p, ¬ r.Faulty p := fun p => by simp [Run.Faulty, r]
  have hr : r.Admissible 1 := by
    refine ⟨?_, by simp [r]⟩
    have : r.faulty = ∅ := by ext p; simp [hnf p]
    simp [this]
  have hs0 : ∀ j : Fin 3, j ≠ 0 → Sent (stealthLiteral0 3 1) r j 0 0 := fun j hj =>
    W_sent0.2 ⟨hj, Run.deliv_of_not_faulty (hnf j) 0 0, by simp [r, hj], rfl⟩
  have hK0 : ∀ m, 1 ≤ m →
      hasAll1Literal (0 : Fin 3) (r.input 0) (hist (stealthLiteral0 3 1) r m 0) := by
    intro m hm
    refine Or.inl ⟨rfl, fun j hj => ?_⟩
    rw [rcv_hist r 0 j (show 0 < m by omega)]
    exact hs0 j hj
  have hs01 : Sent (stealthLiteral0 3 1) r 0 1 1 :=
    W_sent1.2 ⟨by decide, Run.deliv_of_not_faulty (hnf 0) 1 1, rfl, hK0 1 le_rfl, by decide,
      by decide⟩
  have hK1 : hasAll1Literal (1 : Fin 3) (r.input 1) (hist (stealthLiteral0 3 1) r 2 1) := by
    refine Or.inr ⟨by decide, ?_⟩
    rw [rcv_hist r 1 0 (show 1 < 2 by omega)]
    exact hs01
  have hno : ∀ j : Fin 3, ¬ Sent (stealthLiteral0 3 1) r j 2 2 := by
    intro j hj
    obtain ⟨-, -, hc, hK⟩ := W_sent2.1 hj
    fin_cases j
    · exact hK (hK0 2 (by omega))
    · exact hK hK1
    · exact absurd hc (by simp [choir])
  have hES : ¬ errSeenLiteral 1 (2 : Fin 3) (r.input 2) (hist (stealthLiteral0 3 1) r 3 2) := by
    rintro (⟨j, hj⟩ | ⟨hc, -⟩)
    · rw [rcv_hist r 2 j (show 2 < 3 by omega)] at hj
      exact hno j hj
    · exact absurd hc (by simp [choir])
  have hcommit : DecidesAt (stealthLiteral0 3 1) r 2 3 .commit :=
    W_commit3 (Run.alive_of_not_faulty (hnf 2) 3) hES
  have := (hAC r hr).commit_validity 2 3 hcommit 0
  simp [r] at this

variable (n) in
/-- STEALTH read literally: commit at time 3 iff no `err` was *received* (own `err` not counted). -/
noncomputable def stealthLiteralErr (f : ℕ) : ACProtocol (Fin n) Unit :=
  stealthWith n hasAll1 (fun _ _ h => ∃ j, rcv h 2 j ≠ none) f

/-- **Literal reading 2 fails.** If a process commits at time 3 iff it *received* no `err` (its own
`err` does not count), then in `γ_1` with `n = 3`, choir `{0, 1}`, `v₂ = 0`, `v₀ = v₁ = 1`, and
process `0` crashing in round 3 before sending its `err`, process `1` sends `err` but receives none,
and commits at time 3: Commit Validity is violated. -/
theorem literalErr_not_solvesAC : ¬ SolvesAC (stealthLiteralErr 3 1) 1 := by
  intro hAC
  let r : Run (Fin 3) Bool :=
    ⟨fun p => decide (p ≠ 2), fun p => if p = 0 then some 3 else none, fun _ => ∅⟩
  have hr : r.Admissible 1 := by
    refine ⟨?_, ?_⟩
    · have : r.faulty ⊆ {0} := by
        intro z hz
        simp only [Run.mem_faulty, Run.Faulty, r] at hz
        simp only [Finset.mem_singleton]
        by_contra h; simp [h] at hz
      exact (Finset.card_le_card this).trans (by simp)
    · intro z c hc; simp only [r] at hc; split_ifs at hc <;> (simp at hc; omega)
  have h1 : ¬ r.Faulty 1 := by simp [Run.Faulty, r]
  have hno : ∀ j : Fin 3, ¬ Sent (stealthLiteralErr 3 1) r j 1 2 := by
    intro j hj
    obtain ⟨hj1, hd, hc, -⟩ := W_sent2.1 hj
    fin_cases j
    · exact hd.2 ⟨by simp [r], by simp [r]⟩
    · exact hj1 rfl
    · exact absurd hc (by simp [choir])
  have hcommit : DecidesAt (stealthLiteralErr 3 1) r 1 3 .commit := by
    refine W_commit3 (Run.alive_of_not_faulty h1 3) ?_
    rintro ⟨j, hj⟩
    rw [rcv_hist r 1 j (show 2 < 3 by omega)] at hj
    exact hno j hj
  have := (hAC r hr).commit_validity 1 3 hcommit 2
  simp [r] at this

end Papers.PODC2018.Silence.Stealth
