import Papers.PODC2020.NullMessagesByzantine.Run
import Papers.PODC2020.NullMessagesByzantine.Counting

/-!
# The layer in a run: what correct processes compute

In a reliable run with at most `t` Byzantine processes and `2t < n`:
* a correct council member reconstructs the votes of correct processes exactly (`values_honest`),
  so it recommends the honest value when the correct processes agree (`recOf_honest_of_unanimous`);
* a correct process attributes to a correct council member exactly its recommendation, null
  messages included (`recFrom_honest`);
* hence all correct processes with a unanimous recommendation have the same one
  (`unanimous_agree`), and under unanimous inputs every correct estimate is the input
  (`est_honest_of_inputs`);
* the `err` round is a silent validation round: one correct `err` reaches all correct processes
  (`gotErr_of_err`), and so does one correct `help!` (`participates_of_gotErr`).
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep

variable {n : ℕ} {M₂ : Type*} (sr : Bool) (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool)
  (s : Scenario (Fin n) Bool (Msg M₂))

/-- Line 04 is correct for correct senders: a correct council member `j` reconstructs the input
of every correct `i` (from `i`'s message or null message). -/
lemma values_honest (hrel : s.Reliable) {r : ℕ} (hr : 0 < r) {j i : Fin n} (hj : council t j)
    (hi : i ∉ s.byz) : values j (s.input j) (H sr t B s r j) i = s.input i := by
  unfold values
  by_cases hij : i = j
  · subst hij; simp
  · rw [ite_eq_right hij, lmsg0_honest sr t B s hrel hr hi hij]
    unfold send0
    by_cases hp : par j = s.input i
    · simp [hj, hp]
    · simp only [hj, ne_eq, hp, not_false_eq_true, and_self, ↓reduceIte, Option.isSome_some]
      cases h : par j <;> cases h' : s.input i <;> simp_all

/-- A correct process attributes to a correct council member its actual recommendation (null
messages included). -/
lemma recFrom_honest (hrel : s.Reliable) {r : ℕ} (hr : 1 < r) {p j : Fin n} (hp : p ∉ s.byz)
    (hjc : council t j) (hj : j ∉ s.byz) :
    recFrom p (s.input p) (H sr t B s r p) j = recOf j (s.input j) (H sr t B s 1 j) := by
  unfold recFrom
  by_cases hjp : j = p
  · subst hjp
    rw [ite_eq_left rfl]
    exact recOf_congr (lEq_hist sr t B s (by omega) (by omega) j) _ _
  · rw [ite_eq_right hjp, lmsg1_honest sr t B s hrel hr hj hjp]
    unfold send1
    by_cases hv : values j (s.input j) (H sr t B s 1 j) p ≠ recOf j (s.input j) (H sr t B s 1 j)
    · simp [hjc, hv]
    · simp only [hjc, hv, and_false, ↓reduceIte, Option.getD_none]
      push Not at hv
      rw [← hv, values_honest sr t B s hrel (by norm_num) hjc hp]

/-- Two correct processes with unanimous recommendations have the same one. -/
lemma unanimous_agree (hrel : s.Reliable) (htn : t < n) (hF : s.byz.ncard ≤ t) {r r' : ℕ}
    (hr : 1 < r) (hr' : 1 < r') {p q : Fin n} (hp : p ∉ s.byz) (hq : q ∉ s.byz) {c d : Bool}
    (hc : Unanimous t p (s.input p) (H sr t B s r p) c)
    (hd : Unanimous t q (s.input q) (H sr t B s r' q) d) : c = d := by
  obtain ⟨j, hjc, hj⟩ := exists_council_notMem t htn s.byz hF
  have h1 := hc j hjc
  have h2 := hd j hjc
  rw [recFrom_honest sr t B s hrel hr hp hjc hj] at h1
  rw [recFrom_honest sr t B s hrel hr' hq hjc hj] at h2
  rw [← h1, ← h2]

/-- A process cannot receive two different unanimous recommendations. -/
lemma unanimous_unique {p : Fin n} {x : Bool} {h : History (Fin n) (Msg M₂)} {c d : Bool}
    (hc : Unanimous t p x h c) (hd : Unanimous t p x h d) : c = d := by
  have hn : 0 < n := Fin.pos p
  exact (hc ⟨0, hn⟩ (Nat.zero_le t)).symm.trans (hd ⟨0, hn⟩ (Nat.zero_le t))

/-- The estimate of a process with a unanimous recommendation is that recommendation. -/
lemma est_of_unanimous {p : Fin n} {x : Bool} {h : History (Fin n) (Msg M₂)} {c : Bool}
    (hc : Unanimous t p x h c) : est t p x h = c := by
  unfold est
  cases c with
  | true => simp [hc]
  | false =>
    have : ¬ Unanimous t p x h true := fun h' => by
      have := unanimous_unique t h' hc; simp at this
    simp [this, hc]

/-- The estimate of a process without unanimous recommendation is its input. -/
lemma est_of_err {p : Fin n} {x : Bool} {h : History (Fin n) (Msg M₂)} (he : Err t p x h) :
    est t p x h = x := by
  unfold est; simp [he.1, he.2]

/-- No `err` means a unanimous recommendation. -/
lemma exists_unanimous_of_not_err {p : Fin n} {x : Bool} {h : History (Fin n) (Msg M₂)}
    (he : ¬ Err t p x h) : ∃ c, Unanimous t p x h c := by
  unfold Err at he
  by_contra hc
  push Not at hc
  exact he ⟨hc true, hc false⟩

/-- If all correct inputs are `v`, every correct council member recommends `v`. -/
lemma recOf_honest_of_inputs (hrel : s.Reliable) (h2t : 2 * t < n) (hF : s.byz.ncard ≤ t)
    {v : Bool} (hv : ∀ i, i ∉ s.byz → s.input i = v) {j : Fin n} (hjc : council t j) :
    recOf j (s.input j) (H sr t B s 1 j) = v := by
  unfold recOf
  apply maj_eq_of_forall_notMem _ s.byz v (by omega)
  intro i hi
  rw [values_honest sr t B s hrel (by norm_num) hjc hi, hv i hi]

/-- If all correct inputs are `v`, every correct estimate is `v`. -/
lemma est_honest_of_inputs (hrel : s.Reliable) (h2t : 2 * t < n) (hF : s.byz.ncard ≤ t)
    {v : Bool} (hv : ∀ i, i ∉ s.byz → s.input i = v) {r : ℕ} (hr : 1 < r) {p : Fin n}
    (hp : p ∉ s.byz) : est t p (s.input p) (H sr t B s r p) = v := by
  by_cases he : Err t p (s.input p) (H sr t B s r p)
  · rw [est_of_err t he, hv p hp]
  · obtain ⟨c, hc⟩ := exists_unanimous_of_not_err t he
    rw [est_of_unanimous t hc]
    obtain ⟨j, hjc, hj⟩ := exists_council_notMem t (by omega) s.byz hF
    rw [← hc j hjc, recFrom_honest sr t B s hrel hr hp hjc hj,
      recOf_honest_of_inputs sr t B s hrel h2t hF hv hjc]

/-! ### The silent validation rounds 3 and 4 -/

/-- Round 3 is a silent validation round: an `err` of a correct process reaches every correct
process (including itself, under the paper's convention `sr = true`). -/
lemma gotErr_of_err (hrel : s.Reliable) {r : ℕ} (hr : 2 < r) {p q : Fin n} (hq : q ∉ s.byz)
    (he : Err t q (s.input q) (H true t B s 2 q)) :
    GotErr true t p (s.input p) (H true t B s r p) := by
  by_cases hpq : q = p
  · subst hpq
    left
    exact ⟨rfl, (err_congr (lEq_hist true t B s (by omega) (by omega) q) _ _).1 he⟩
  · right
    refine ⟨q, ?_⟩
    rw [lmsg2_honest true t B s hrel hr hq hpq, ite_eq_left he]
    rfl

/-- Round 4 is a silent validation round: a `help!` of a correct process reaches every correct
process. -/
lemma participates_of_gotErr (hrel : s.Reliable) {r : ℕ} (hr : 3 < r) {p q : Fin n}
    (hq : q ∉ s.byz) (he : GotErr true t q (s.input q) (H true t B s 3 q)) :
    Participates true t p (s.input p) (H true t B s r p) := by
  by_cases hpq : q = p
  · subst hpq
    left
    exact ⟨rfl, (gotErr_congr true (lEq_hist true t B s (by omega) (by omega) q) _ _).1 he⟩
  · right
    refine ⟨q, ?_⟩
    rw [lmsg3_honest true t B s hrel hr hq hpq, ite_eq_left he]
    rfl

/-- A correct process that got no `err` had a unanimous recommendation, and so did every correct
process. -/
lemma not_err_of_not_gotErr (hrel : s.Reliable) {r : ℕ} (hr : 2 < r) {p q : Fin n}
    (hq : q ∉ s.byz) (hp : ¬ GotErr true t p (s.input p) (H true t B s r p)) :
    ¬ Err t q (s.input q) (H true t B s 2 q) :=
  fun he => hp (gotErr_of_err t B s hrel hr hq he)

end Podc.NullMessagesByzantine
