import Papers.PODC2020.NullMessagesByzantine.Protocol

/-!
# Runs of SmallCouncil: basic lemmas

Congruence of the layer's local computations (they only depend on the layer messages of rounds
`0, …, 3`), the messages sent in each round, and what honest processes receive from honest
processes.
-/

namespace Podc.NullMessagesByzantine

open Cslib.Byzantine.LockStep

variable {n : ℕ} {M₂ : Type*}

/-- Two histories carry the same layer messages in rounds `0, …, k`. -/
def LEq (k : ℕ) (h h' : History (Fin n) (Msg M₂)) : Prop := ∀ i ≤ k, lmsg h i = lmsg h' i

section Congr

variable {t : ℕ} {h h' : History (Fin n) (Msg M₂)} {k : ℕ}

lemma LEq.mono {k' : ℕ} (H : LEq k h h') (hk : k' ≤ k) : LEq k' h h' :=
  fun i hi => H i (hi.trans hk)

lemma values_congr (H : LEq 0 h h') (j : Fin n) (x : Bool) : values j x h = values j x h' := by
  funext i; simp [values, H 0 le_rfl]

lemma recOf_congr (H : LEq 0 h h') (j : Fin n) (x : Bool) : recOf j x h = recOf j x h' := by
  simp [recOf, values_congr H]

lemma recFrom_congr (H : LEq 1 h h') (p : Fin n) (x : Bool) :
    recFrom p x h = recFrom p x h' := by
  funext j; simp [recFrom, recOf_congr (H.mono (Nat.zero_le 1)), H 1 le_rfl]

lemma unanimous_congr (H : LEq 1 h h') (p : Fin n) (x c : Bool) :
    Unanimous t p x h c ↔ Unanimous t p x h' c := by
  simp [Unanimous, recFrom_congr H]

lemma err_congr (H : LEq 1 h h') (p : Fin n) (x : Bool) : Err t p x h ↔ Err t p x h' := by
  simp [Err, unanimous_congr H]

lemma est_congr (H : LEq 1 h h') (p : Fin n) (x : Bool) : est t p x h = est t p x h' := by
  have h1 := unanimous_congr (t := t) H p x true
  have h2 := unanimous_congr (t := t) H p x false
  unfold est; split_ifs <;> simp_all

lemma gotErr_congr (sr : Bool) (H : LEq 2 h h') (p : Fin n) (x : Bool) :
    GotErr sr t p x h ↔ GotErr sr t p x h' := by
  simp [GotErr, err_congr (H.mono (by norm_num)), H 2 le_rfl]

lemma participates_congr (sr : Bool) (H : LEq 3 h h') (p : Fin n) (x : Bool) :
    Participates sr t p x h ↔ Participates sr t p x h' := by
  simp [Participates, gotErr_congr sr (H.mono (by norm_num)), H 3 le_rfl]

end Congr

section Run

variable (sr : Bool) (t : ℕ) (B : Protocol (Fin n) Bool M₂ Bool)
  (s : Scenario (Fin n) Bool (Msg M₂))

/-- Shorthand for the history of `p` after `r` rounds of the composed protocol. -/
noncomputable abbrev H (r : ℕ) (p : Fin n) : History (Fin n) (Msg M₂) :=
  hist ⊤ (smallCouncilGen sr t B) s r p

lemma lmsg_hist {k r : ℕ} (hk : k < r) (p q : Fin n) :
    lmsg (H sr t B s r p) k q =
      (deliver ⊤ (smallCouncilGen sr t B) s (H sr t B s k) k q p).bind Sum.getLeft? := by
  simp [lmsg, getElem?_hist _ _ _ hk]

lemma lEq_hist {k r r' : ℕ} (hr : k < r) (hr' : k < r') (p : Fin n) :
    LEq k (H sr t B s r p) (H sr t B s r' p) := by
  intro i hi
  funext q
  rw [lmsg_hist sr t B s (by omega), lmsg_hist sr t B s (by omega)]

/-! ### What is sent in each round -/

variable {sr t B}

lemma send_round0 (q : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (hl : h.length = 0)
    (p : Fin n) : (smallCouncilGen sr t B).send q x h p = (send0 t x p).map Sum.inl := by
  simp only [smallCouncilGen]; rw [ite_eq_left hl]

lemma send_round1 (q : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (hl : h.length = 1)
    (p : Fin n) : (smallCouncilGen sr t B).send q x h p = (send1 t q x h p).map Sum.inl := by
  simp only [smallCouncilGen]; rw [ite_eq_right (by omega), ite_eq_left hl]

open Classical in
lemma send_round2 (q : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (hl : h.length = 2)
    (p : Fin n) : (smallCouncilGen sr t B).send q x h p =
      if Err t q x h then some (Sum.inl true) else none := by
  simp only [smallCouncilGen]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hl]

open Classical in
lemma send_round3 (q : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (hl : h.length = 3)
    (p : Fin n) : (smallCouncilGen sr t B).send q x h p =
      if GotErr sr t q x h then some (Sum.inl true) else none := by
  simp only [smallCouncilGen]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hl]

open Classical in
lemma send_round4 (q : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) (hl : 4 ≤ h.length)
    (p : Fin n) : (smallCouncilGen sr t B).send q x h p =
      if Participates sr t q x h then
        (B.send q (est t q x h) (histR (h.drop 4)) p).map Sum.inr else none := by
  simp only [smallCouncilGen]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

open Classical in
lemma decide_eq (p : Fin n) (x : Bool) (h : History (Fin n) (Msg M₂)) :
    (smallCouncilGen sr t B).decide p x h =
      if h.length < 3 then none
      else if ¬ GotErr sr t p x h then some (est t p x h)
      else if h.length < 4 then none
      else if Participates sr t p x h then B.decide p (est t p x h) (histR (h.drop 4))
      else none := rfl

/-! ### Layer messages between honest processes -/

variable (sr t B)

/-- A layer message from an honest `q` (reliable run, `q ≠ p`). -/
lemma lmsg_honest (hrel : s.Reliable) {k r : ℕ} (hk : k < r) {p q : Fin n} (hq : q ∉ s.byz)
    (hpq : q ≠ p) :
    lmsg (H sr t B s r p) k q =
      ((smallCouncilGen sr t B).send q (s.input q) (H sr t B s k q) p).bind Sum.getLeft? := by
  rw [lmsg_hist sr t B s hk, deliver_honest _ _ _ hrel hq (by simpa using hpq)]

lemma lmsg0_honest (hrel : s.Reliable) {r : ℕ} (hr : 0 < r) {p q : Fin n} (hq : q ∉ s.byz)
    (hpq : q ≠ p) : lmsg (H sr t B s r p) 0 q = send0 t (s.input q) p := by
  rw [lmsg_honest sr t B s hrel hr hq hpq, send_round0 _ _ _ (by simp)]
  cases send0 t (s.input q) p <;> rfl

lemma lmsg1_honest (hrel : s.Reliable) {r : ℕ} (hr : 1 < r) {p q : Fin n} (hq : q ∉ s.byz)
    (hpq : q ≠ p) : lmsg (H sr t B s r p) 1 q = send1 t q (s.input q) (H sr t B s 1 q) p := by
  rw [lmsg_honest sr t B s hrel hr hq hpq, send_round1 _ _ _ (by simp)]
  cases send1 t q (s.input q) (H sr t B s 1 q) p <;> rfl

open Classical in
lemma lmsg2_honest (hrel : s.Reliable) {r : ℕ} (hr : 2 < r) {p q : Fin n} (hq : q ∉ s.byz)
    (hpq : q ≠ p) : lmsg (H sr t B s r p) 2 q =
      if Err t q (s.input q) (H sr t B s 2 q) then some true else none := by
  rw [lmsg_honest sr t B s hrel hr hq hpq, send_round2 _ _ _ (by simp)]
  split_ifs <;> rfl

open Classical in
lemma lmsg3_honest (hrel : s.Reliable) {r : ℕ} (hr : 3 < r) {p q : Fin n} (hq : q ∉ s.byz)
    (hpq : q ≠ p) : lmsg (H sr t B s r p) 3 q =
      if GotErr sr t q (s.input q) (H sr t B s 3 q) then some true else none := by
  rw [lmsg_honest sr t B s hrel hr hq hpq, send_round3 _ _ _ (by simp)]
  split_ifs <;> rfl

end Run

end Podc.NullMessagesByzantine
