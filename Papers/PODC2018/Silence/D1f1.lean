import Papers.PODC2018.Silence.Defs

/-!
# The protocol D1f1 (Appendix C of Goren–Moses): `f = 1`, `D = 1`, `M = n² − n`

* Round 1: every process with value `1` sends `'1'` to all.
* Time 1: a process with value `1` that received `'1'` from all others commits; otherwise it sends
  `huh?` to all in round 2.
* Round 3: a committed process that received `huh?` from `j` in round 2 sends `all[1]` to `j`.
* Time 3: a process that did not commit at time 1 commits if it received `all[1]` in round 3, and
  aborts otherwise.

All messages are a single bit (`Unit`).
-/

namespace Papers.PODC2018.Silence.D1f1

open Cslib.SyncCrash Classical

variable {P : Type*} [Fintype P]

/-- `p` (value `x`, history `h`) has value `1` and heard `'1'` from every other process in round 1. -/
def ok (p : P) (x : Bool) (h : Cslib.Byzantine.LockStep.History P Unit) : Prop :=
  x = true ∧ ∀ j, j ≠ p → rcv h 0 j ≠ none

/-- The protocol D1f1. -/
noncomputable def alg : ACProtocol P Unit where
  send p x h q :=
    if h.length = 0 then (if x = true then some () else none)
    else if h.length = 1 then (if ok p x h then none else some ())
    else if h.length = 2 then (if ok p x h ∧ rcv h 1 q ≠ none then some () else none)
    else none
  decide p x h :=
    if h.length = 1 ∧ ok p x h then some .commit
    else if h.length = 3 ∧ ¬ ok p x h then
      (if ∃ j, rcv h 2 j ≠ none then some .commit else some .abort)
    else none

lemma send_def (p : P) (x : Bool) (h : Cslib.Byzantine.LockStep.History P Unit) (q : P) :
    (alg (P := P)).send p x h q =
      if h.length = 0 then (if x = true then some () else none)
      else if h.length = 1 then (if ok p x h then none else some ())
      else if h.length = 2 then (if ok p x h ∧ rcv h 1 q ≠ none then some () else none)
      else none := rfl

lemma decide_def (p : P) (x : Bool) (h : Cslib.Byzantine.LockStep.History P Unit) :
    (alg (P := P)).decide p x h =
      if h.length = 1 ∧ ok p x h then some .commit
      else if h.length = 3 ∧ ¬ ok p x h then
        (if ∃ j, rcv h 2 j ≠ none then some .commit else some .abort)
      else none := rfl

variable {r : Run P Bool}

lemma ok_hist {p : P} {m : ℕ} (hm : 1 ≤ m) :
    ok p (r.input p) (hist alg r m p) ↔ r.input p = true ∧ ∀ j, j ≠ p → Sent alg r j p 0 := by
  simp only [ok, rcv_hist r p _ (show 0 < m by omega), Sent]

lemma send_len2 {p : P} {x : Bool} {h : Cslib.Byzantine.LockStep.History P Unit} {q : P}
    (hh : h.length = 2) :
    (alg (P := P)).send p x h q = if ok p x h ∧ rcv h 1 q ≠ none then some () else none := by
  rw [send_def, hh]; simp

lemma sent0 {j p : P} : Sent alg r j p 0 ↔ j ≠ p ∧ r.Deliv j p 0 ∧ r.input j = true := by
  rw [sent_iff_deliv, send_def]; simp only [length_hist]; simp

lemma sent1 {j p : P} :
    Sent alg r j p 1 ↔ j ≠ p ∧ r.Deliv j p 1 ∧ ¬ ok j (r.input j) (hist alg r 1 j) := by
  rw [sent_iff_deliv, send_def]; simp only [length_hist]
  by_cases h : ok j (r.input j) (hist alg r 1 j) <;> simp [h]

lemma sent2 {j p : P} :
    Sent alg r j p 2 ↔ j ≠ p ∧ r.Deliv j p 2 ∧ ok j (r.input j) (hist alg r 2 j) ∧
      Sent alg r p j 1 := by
  rw [sent_iff_deliv, send_len2 (length_hist _ _ _), rcv_hist r j p (show 1 < 2 by omega)]
  by_cases h : ok j (r.input j) (hist alg r 2 j) ∧ msg alg r p j 1 ≠ none
  · rw [if_pos h]; simp [Sent, h.1, h.2]
  · rw [if_neg h]
    simp only [ne_eq, not_true_eq_false, and_false, false_iff]
    rintro ⟨_, _, h1, h2⟩; exact h ⟨h1, h2⟩

lemma not_sent_ge3 {j p : P} {t : ℕ} (ht : 3 ≤ t) : ¬ Sent alg r j p t := by
  rw [sent_iff_deliv, send_def]
  simp only [length_hist]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

lemma decidesAt_iff' {p : P} {m : ℕ} {d : Decision} :
    DecidesAt alg r p m d ↔ r.Alive p m ∧
      ((m = 1 ∧ ok p (r.input p) (hist alg r m p) ∧ d = .commit) ∨
       (m = 3 ∧ ¬ ok p (r.input p) (hist alg r m p) ∧
        d = if ∃ j, Sent alg r j p 2 then .commit else .abort)) := by
  rw [decidesAt_iff]
  apply and_congr_right
  intro _
  rw [decide_def]
  simp only [length_hist]
  by_cases h1 : m = 1
  · subst h1
    by_cases hok : ok p (r.input p) (hist alg r 1 p)
    · simp only [hok, and_self, if_true]; simp [eq_comm]
    · simp [hok]
  · by_cases h3 : m = 3
    · subst h3
      simp only [rcv_hist r p _ (show 2 < 3 by omega)]
      by_cases hok : ok p (r.input p) (hist alg r 3 p)
      · simp [hok]
      · have he : (∃ j, msg alg r j p 2 ≠ none) ↔ ∃ j, Sent alg r j p 2 := Iff.rfl
        by_cases he' : ∃ j, Sent alg r j p 2
        · rw [if_neg (by omega), if_pos (by simp [hok]), if_pos (he.2 he'), if_pos he']
          simp [hok, eq_comm]
        · rw [if_neg (by omega), if_pos (by simp [hok]), if_neg (fun h => he' (he.1 h)), if_neg he']
          simp [hok, eq_comm]
    · simp [h1, h3]

/-- An `ok` process at time `m ≥ 1` certifies that all inputs are `1`. -/
lemma all_one_of_ok {p : P} {m : ℕ} (hm : 1 ≤ m) (h : ok p (r.input p) (hist alg r m p)) (j : P) :
    r.input j = true := by
  rw [ok_hist hm] at h
  by_cases hj : j = p
  · subst hj; exact h.1
  · exact (sent0.1 (h.2 j hj)).2.2

/-- **D1f1 solves AC in `γ_1`** (Claim 6 of Goren–Moses). -/
theorem solvesAC : SolvesAC (alg (P := P)) 1 := by
  intro r hr
  -- with at most one crash
  have hone : ∀ a b, r.Faulty a → r.Faulty b → a = b := by
    intro a b ha hb
    by_contra hab
    have : ({a, b} : Finset P) ⊆ r.faulty := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simpa
    have := (Finset.card_le_card this).trans hr.1
    rw [Finset.card_pair hab] at this
    omega
  -- a process that commits had an `ok` process alive at time 1
  have commit_ok : ∀ i m, DecidesAt alg r i m .commit →
      ∃ c, r.Alive c 1 ∧ ok c (r.input c) (hist alg r 1 c) ∧
        (∀ m', 1 ≤ m' → ok c (r.input c) (hist alg r m' c)) := by
    intro i m h
    rw [decidesAt_iff'] at h
    rcases h with ⟨ha, ⟨rfl, hok, -⟩ | ⟨rfl, -, hd⟩⟩
    · exact ⟨i, ha, hok, fun m' hm' => (ok_hist hm').2 ((ok_hist le_rfl).1 hok)⟩
    · split_ifs at hd with he
      · obtain ⟨c, hc⟩ := he
        obtain ⟨-, hdc, hokc, -⟩ := sent2.1 hc
        exact ⟨c, hdc.1.mono (by omega), (ok_hist le_rfl).2 ((ok_hist (by omega)).1 hokc),
          fun m' hm' => (ok_hist hm').2 ((ok_hist (by omega)).1 hokc)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Decision
    intro i hi
    by_cases hok : ok i (r.input i) (hist alg r 1 i)
    · exact ⟨1, .commit, decidesAt_iff'.2 ⟨Run.alive_of_not_faulty hi 1, Or.inl ⟨rfl, hok, rfl⟩⟩⟩
    · have hok3 : ¬ ok i (r.input i) (hist alg r 3 i) := fun h =>
        hok ((ok_hist le_rfl).2 ((ok_hist (by omega)).1 h))
      exact ⟨3, _, decidesAt_iff'.2 ⟨Run.alive_of_not_faulty hi 3, Or.inr ⟨rfl, hok3, rfl⟩⟩⟩
  · -- Agreement: a commit and an abort cannot coexist
    have no_abort : ∀ i m, DecidesAt alg r i m .abort → ∀ k m', ¬ DecidesAt alg r k m' .commit := by
      intro i m hab k m' hck
      obtain ⟨c, hc1, hokc, hokc'⟩ := commit_ok k m' hck
      rw [decidesAt_iff'] at hab
      rcases hab with ⟨ha, ⟨-, -, h⟩ | ⟨rfl, hnok, hd⟩⟩
      · cases h
      by_cases he : ∃ j, Sent alg r j i 2
      · rw [if_pos he] at hd; cases hd
      have hall := fun j => all_one_of_ok le_rfl hokc j
      have hci : c ≠ i := by
        intro h; subst h; exact hnok (hokc' 3 (by omega))
      -- `i` sent `huh?` to `c` in round 2
      have hnok1 : ¬ ok i (r.input i) (hist alg r 1 i) := fun h =>
        hnok ((ok_hist (by omega)).2 ((ok_hist le_rfl).1 h))
      have hi_alive : r.Alive i 3 := ha
      have hsent1 : Sent alg r i c 1 :=
        sent1.2 ⟨hci.symm, ⟨ha.mono (by omega), fun hc => by have := ha _ hc.1; omega⟩, hnok1⟩
      -- so `c` must have crashed, without answering
      have hcf : r.Faulty c := by
        by_contra hcn
        apply he
        exact ⟨c, sent2.2 ⟨hci, Run.deliv_of_not_faulty hcn i 2, hokc' 2 (by omega), hsent1⟩⟩
      -- then `i` heard from everybody in round 1, so it is `ok`: contradiction
      apply hnok
      rw [ok_hist (by omega)]
      refine ⟨hall i, fun j hji => sent0.2 ⟨hji, ?_, hall j⟩⟩
      by_cases hjc : j = c
      · subst hjc
        refine ⟨hc1.mono (by omega), fun h => ?_⟩
        have := hc1 1 h.1; omega
      · have hjn : ¬ r.Faulty j := fun hj => hjc (hone j c hj hcf)
        exact Run.deliv_of_not_faulty hjn i 0
    intro i m d i' m' d' h h'
    cases d <;> cases d'
    · rfl
    · exact absurd h (no_abort i' m' h' i m)
    · exact absurd h' (no_abort i m h i' m')
    · rfl
  · -- Commit Validity
    intro i m h j
    obtain ⟨c, -, hokc, -⟩ := commit_ok i m h
    exact all_one_of_ok le_rfl hokc j
  · -- Abort Validity
    intro i m h
    by_contra hc
    push Not at hc
    obtain ⟨hin, hnf⟩ := hc
    rw [decidesAt_iff'] at h
    rcases h with ⟨ha, ⟨-, -, h⟩ | ⟨rfl, hnok, -⟩⟩
    · cases h
    apply hnok
    rw [ok_hist (by omega)]
    refine ⟨by simpa using hin i, fun j hji => sent0.2 ⟨hji, Run.deliv_of_not_faulty (by
      simpa [Run.Faulty] using hnf j) i 0, by simpa using hin j⟩⟩

/-! ### The nice run -/

lemma nice_ok (p : P) {m : ℕ} (hm : 1 ≤ m) : ok p ((nice : Run P Bool).input p) (hist alg nice m p) :=
  (ok_hist hm).2 ⟨rfl, fun j hj => sent0.2 ⟨hj, Run.deliv_of_not_faulty (nice_not_faulty j) p 0, rfl⟩⟩

/-- **Claim 5** of Goren–Moses: in the nice run all processes commit at time `1`... -/
theorem nice_commit (p : P) : DecidesAt alg nice p 1 .commit :=
  decidesAt_iff'.2 ⟨nice_alive p 1, Or.inl ⟨rfl, nice_ok p le_rfl, rfl⟩⟩

/-- … and exactly `n(n − 1)` messages are sent. -/
theorem nice_msgs :
    (msgs (alg (P := P)) nice).encard = (Fintype.card P * (Fintype.card P - 1) : ℕ) := by
  have hset : msgs (alg (P := P)) nice =
      ((Finset.univ : Finset P).offDiag.image (fun e => (e.1, e.2, 0)) : Set (P × P × ℕ)) := by
    ext ⟨a, b, t⟩
    simp only [msgs, Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_offDiag, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · intro h
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ 3 ≤ t by omega) with rfl | rfl | rfl | ht
      · exact ⟨(a, b), h.ne, rfl, rfl, rfl⟩
      · exact absurd (nice_ok a le_rfl) (sent1.1 h).2.2
      · exact absurd (sent2.1 h).2.2.2 (fun h1 => (sent1.1 h1).2.2 (nice_ok b le_rfl))
      · exact absurd h (not_sent_ge3 ht)
    · rintro ⟨⟨a', b'⟩, hab, rfl, rfl, rfl⟩
      exact sent0.2 ⟨hab, Run.deliv_of_not_faulty (nice_not_faulty _) _ 0, rfl⟩
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ (fun a b hab => by
      simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 hab.2.1), Finset.offDiag_card,
    Finset.card_univ, Nat.mul_sub_one]

end Papers.PODC2018.Silence.D1f1
