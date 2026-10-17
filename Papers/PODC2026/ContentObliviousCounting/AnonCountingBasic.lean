import Papers.PODC2026.ContentObliviousCounting.AnonCounting

/-!
# Anonymous counting: arithmetic and position-level abstraction

* `tri j = j(j-1)/2`, `phaseOf p` (the phase in which position `p ≥ 1` is probed), the final phase
  `lastPhase n`, the final `count` `lastCount n`, the exact pulse count `totalPulses n`.
* Positions: node `w` has position `pos ℓ w = (w - ℓ).val` (clockwise distance from the leader).
  `Abs` describes a configuration by functions of positions (local states, pulses in transit,
  total number of pulses sent); `Matches` relates it to a configuration; `Abs.step` is the effect
  of delivering a pulse (`matches_step`).
-/

namespace Podc.ContentOblivious.AnonCounting

open Cslib.ContentOblivious Finset

set_option linter.unusedSectionVars false

/-! ## Triangular numbers and phases -/

@[simp] lemma tri_zero : tri 0 = 0 := rfl
@[simp] lemma tri_succ (j : ℕ) : tri (j + 1) = tri j + j := rfl

lemma two_mul_tri (j : ℕ) : 2 * tri j = j * (j - 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [tri_succ, mul_add, ih]
    rcases j with _ | j
    · rfl
    · simp only [Nat.add_sub_cancel]; ring

lemma tri_eq (j : ℕ) : tri j = j * (j - 1) / 2 := by
  rw [← two_mul_tri]; omega

lemma tri_succ_eq (m : ℕ) : tri (m + 1) = m * (m + 1) / 2 := by
  rw [tri_eq, Nat.add_sub_cancel, mul_comm]

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => simp only [tri_succ]; omega

lemma le_tri_succ (k : ℕ) : k ≤ tri (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [tri_succ] at *; omega

lemma tri_lt_tri {a b : ℕ} (h : a < b) (ha : 1 ≤ a) : tri a < tri b := by
  have := tri_mono (show a + 1 ≤ b from h)
  simp only [tri_succ] at this; omega

private lemma exists_le_tri (p : ℕ) : ∃ k, p ≤ tri (k + 1) := ⟨p, le_tri_succ p⟩

/-- The phase in which position `p ≥ 1` is probed: the `k` with `tri k < p ≤ tri (k + 1)`. -/
noncomputable def phaseOf (p : ℕ) : ℕ := Nat.find (exists_le_tri p)

lemma le_tri_phaseOf (p : ℕ) : p ≤ tri (phaseOf p + 1) := Nat.find_spec (exists_le_tri p)

lemma tri_phaseOf_lt {p : ℕ} (hp : 1 ≤ p) : tri (phaseOf p) < p := by
  rcases h : phaseOf p with _ | k
  · have := le_tri_phaseOf p; rw [h] at this; simp at this; omega
  · have := Nat.find_min (exists_le_tri p) (show k < phaseOf p by omega)
    omega

lemma one_le_phaseOf {p : ℕ} (hp : 1 ≤ p) : 1 ≤ phaseOf p := by
  by_contra h
  have := le_tri_phaseOf p
  rw [show phaseOf p = 0 by omega] at this; simp at this; omega

lemma phaseOf_eq {p k : ℕ} (h1 : tri k < p) (h2 : p ≤ tri (k + 1)) : phaseOf p = k := by
  have hp : 1 ≤ p := by omega
  have a := le_tri_phaseOf p
  have b := tri_phaseOf_lt hp
  rcases lt_trichotomy (phaseOf p) k with h | h | h
  · have := tri_mono (show phaseOf p + 1 ≤ k by omega); omega
  · exact h
  · have := tri_mono (show k + 1 ≤ phaseOf p by omega); omega

lemma phaseOf_lt {p j : ℕ} (hp : 1 ≤ p) (h : p ≤ tri j) : phaseOf p < j := by
  by_contra hc
  have := tri_mono (show j ≤ phaseOf p by omega)
  have := tri_phaseOf_lt hp
  omega

/-- The final phase `i`: `tri i < n ≤ tri (i + 1)`, i.e. `i(i-1)/2 < n ≤ i(i+1)/2`. -/
noncomputable def lastPhase (n : ℕ) : ℕ := phaseOf n

/-- The final value of `count` at the last leader. -/
noncomputable def lastCount (n : ℕ) : ℕ := n - 1 - tri (lastPhase n)

/-- Pulses sent in phases `1, …, j - 1` (each complete phase `k` sends `k(k+1) + 2n` pulses). -/
def phasesCost (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => phasesCost n j + if j = 0 then 0 else j * (j + 1) + 2 * n

/-- The exact number of pulses sent in every execution. -/
noncomputable def totalPulses (n : ℕ) : ℕ :=
  phasesCost n (lastPhase n) + lastCount n * (lastCount n + 1) + 4 * n +
    2 * n * (Nat.digits 2 (lastCount n)).length + 2 * n

/-! ## Positions -/

/-- Clockwise successor of a position. -/
def nxt (n q : ℕ) : ℕ := if q + 1 = n then 0 else q + 1

/-- Counter-clockwise successor of a position. -/
def prv (n q : ℕ) : ℕ := if q = 0 then n - 1 else q - 1

variable {n : ℕ} [NeZero n] (ℓ : ZMod n)

/-- Position of node `w`: its clockwise distance from `ℓ`. -/
def pos (w : ZMod n) : ℕ := (w - ℓ).val

lemma pos_lt (w : ZMod n) : pos ℓ w < n := ZMod.val_lt _

lemma pos_inj {w w' : ZMod n} (h : pos ℓ w = pos ℓ w') : w = w' := by
  have := ZMod.val_injective n h
  simpa using this

lemma pos_self : pos ℓ ℓ = 0 := by simp [pos]

lemma pos_eq_zero {w : ZMod n} : pos ℓ w = 0 ↔ w = ℓ := by
  simp [pos, ZMod.val_eq_zero, sub_eq_zero]

lemma pos_add_one (w : ZMod n) : pos ℓ (w + 1) = nxt n (pos ℓ w) := by
  unfold pos nxt
  rw [show w + 1 - ℓ = (w - ℓ) + 1 by ring]
  rcases Nat.lt_or_ge 1 n with hn | hn
  · have : Fact (1 < n) := ⟨hn⟩
    rw [ZMod.val_add, ZMod.val_one]
    have := ZMod.val_lt (w - ℓ)
    split_ifs with h
    · rw [h, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  · have : n = 1 := by have := NeZero.ne n; omega
    subst this
    have h1 := ZMod.val_lt (w - ℓ + 1)
    have h2 := ZMod.val_lt (w - ℓ)
    split_ifs <;> omega

lemma pos_sub_one (w : ZMod n) : pos ℓ (w - 1) = prv n (pos ℓ w) := by
  have h := pos_add_one ℓ (w - 1)
  rw [sub_add_cancel] at h
  have := pos_lt ℓ (w - 1)
  simp only [nxt, prv] at *; split_ifs at * <;> omega

lemma pos_natCast {p : ℕ} (hp : p < n) : pos ℓ (ℓ + (p : ZMod n)) = p := by
  simp [pos, ZMod.val_natCast, Nat.mod_eq_of_lt hp]

/-! ## Abstract configurations -/

/-- A configuration described by positions: local states, pulses in transit towards each port, and
the total number of pulses sent. -/
structure Abs where
  st : ℕ → St
  tr : ℕ → Bool → ℕ
  tot : ℕ

/-- Configurations of the counting algorithm on the oriented ring of size `n`. -/
abbrev Cfg (n : ℕ) := Config (ZMod n) anonCount.toAlgo.State

/-- `c` is described by `A`. -/
def Matches (c : Cfg n) (A : Abs) : Prop :=
  (∀ w, c.st w = A.st (pos ℓ w)) ∧
  (∀ w b, c.sent ((oriented n).peer (w, b)) = c.recvd (w, b) + A.tr (pos ℓ w) b) ∧
  totalSent c = A.tot

/-- Two abstract configurations agree on the positions `0, …, n - 1`. -/
def Agree (n : ℕ) (A B : Abs) : Prop :=
  (∀ p < n, A.st p = B.st p) ∧ (∀ p < n, ∀ b, A.tr p b = B.tr p b) ∧ A.tot = B.tot

/-- The effect of delivering a pulse at port `j` of the node at position `q`. -/
def Abs.step (n : ℕ) (A : Abs) (q : ℕ) (j : Bool) : Abs :=
  let r := recv (A.st q) j
  { st := fun p => if p = q then r.1 else A.st p
    tr := fun p b => A.tr p b - (if p = q ∧ b = j then 1 else 0) +
      (if b = false ∧ p = nxt n q then r.2 true else 0) +
      (if b = true ∧ p = prv n q then r.2 false else 0)
    tot := A.tot + r.2 false + r.2 true }

/-- The node at position `q` can consume a pulse from port `j`. -/
def Abs.En (n : ℕ) (A : Abs) (q : ℕ) (j : Bool) : Prop :=
  q < n ∧ 0 < A.tr q j ∧ ready (A.st q) j = true ∧ terminated (A.st q) = false

variable {ℓ}

lemma Matches.agree {c : Cfg n} {A B : Abs} (h : Matches ℓ c A) (hAB : Agree n A B) :
    Matches ℓ c B := by
  refine ⟨fun w => ?_, fun w b => ?_, ?_⟩
  · rw [h.1, hAB.1 _ (pos_lt ℓ w)]
  · rw [h.2.1, hAB.2.1 _ (pos_lt ℓ w)]
  · rw [h.2.2, hAB.2.2]

lemma Agree.refl (A : Abs) : Agree n A A := ⟨fun _ _ => rfl, fun _ _ _ => rfl, rfl⟩

lemma Agree.trans {A B C : Abs} (h1 : Agree n A B) (h2 : Agree n B C) : Agree n A C :=
  ⟨fun p hp => (h1.1 p hp).trans (h2.1 p hp), fun p hp b => (h1.2.1 p hp b).trans (h2.2.1 p hp b),
    h1.2.2.trans h2.2.2⟩

@[simp] lemma ac_recv : (anonCount.toAlgo).recv = recv := rfl
@[simp] lemma ac_ready : (anonCount.toAlgo).ready = ready := rfl
@[simp] lemma ac_terminated : (anonCount.toAlgo).terminated = terminated := rfl

@[simp] lemma ac_recv' : anonCount.recv = recv := rfl
@[simp] lemma ac_ready' : anonCount.ready = ready := rfl
@[simp] lemma ac_terminated' : anonCount.terminated = terminated := rfl

omit [NeZero n] in
lemma totalSent_deliver {V : Type*} [Fintype V] [DecidableEq V] (A : Algo) (c : Config V A.State)
    (v : V) (j : Bool) :
    totalSent (deliver A c v j) =
      totalSent c + (A.recv (c.st v) j).2 false + (A.recv (c.st v) j).2 true := by
  unfold totalSent
  simp only [deliver_sent]
  rw [Finset.sum_add_distrib, add_assoc]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma sub_one_eq_iff (w v : ZMod n) : w - 1 = v ↔ pos ℓ w = nxt n (pos ℓ v) := by
  constructor
  · rintro rfl; rw [← pos_add_one, sub_add_cancel]
  · intro e; apply pos_inj ℓ; rw [pos_sub_one, e]
    have := pos_lt ℓ v; simp only [nxt, prv] at *; split_ifs at * <;> omega

lemma add_one_eq_iff (w v : ZMod n) : w + 1 = v ↔ pos ℓ w = prv n (pos ℓ v) := by
  constructor
  · rintro rfl; rw [← pos_sub_one, add_sub_cancel_right]
  · intro e; apply pos_inj ℓ; rw [pos_add_one, e]
    have := pos_lt ℓ v; simp only [nxt, prv] at *; split_ifs at * <;> omega

/-- Delivering a pulse, at the level of abstract configurations. -/
lemma matches_step {c c' : Cfg n} {A : Abs} (h : Matches ℓ c A)
    (hs : anonCount.Step (oriented n) c c') :
    ∃ q j, A.En n q j ∧ Matches ℓ c' (A.step n q j) := by
  obtain ⟨v, j, hen⟩ := hs
  obtain ⟨hst, htr, htot⟩ := h
  have hrv : c.st v = A.st (pos ℓ v) := hst v
  refine ⟨pos ℓ v, j, ⟨pos_lt ℓ v, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have := hen.2.2; have := htr v j; omega
  · have := hen.2.1; rw [hrv] at this; exact this
  · have := hen.1; rw [hrv] at this; exact this
  · intro w
    simp only [Abs.step, deliver]
    by_cases hw : w = v
    · subst hw; simp [hrv]
    · have : pos ℓ w ≠ pos ℓ v := fun e => hw (pos_inj ℓ e)
      rw [Function.update_of_ne hw, ite_eq_right_iff.2 (fun h => absurd h this)]; exact hst w
  · intro w b
    have e1 := htr w b
    have hle : c.recvd (v, j) < c.sent ((oriented n).peer (v, j)) := hen.2.2
    have e2 := htr v j
    have key : (if ((oriented n).peer (w, b)).1 = v then
        (recv (c.st v) j).2 ((oriented n).peer (w, b)).2 else 0) =
        (if b = false ∧ pos ℓ w = nxt n (pos ℓ v) then (recv (c.st v) j).2 true else 0) +
        (if b = true ∧ pos ℓ w = prv n (pos ℓ v) then (recv (c.st v) j).2 false else 0) := by
      cases b
      · simp only [oriented_peer_false, sub_one_eq_iff (ℓ := ℓ)]; simp
      · simp only [oriented_peer_true, add_one_eq_iff (ℓ := ℓ)]; simp
    have key2 : (if (w, b) = (v, j) then 1 else 0) =
        (if pos ℓ w = pos ℓ v ∧ b = j then 1 else 0) := by
      by_cases h : w = v
      · subst h; simp
      · have : pos ℓ w ≠ pos ℓ v := fun e => h (pos_inj ℓ e)
        simp [h, this]
    rw [deliver_sent, deliver_recvd]
    simp only [ac_recv']
    rw [key, key2]
    simp only [Abs.step, ← hrv]
    by_cases hb : pos ℓ w = pos ℓ v ∧ b = j
    · obtain ⟨h1, rfl⟩ := hb
      have := pos_inj ℓ h1; subst this
      simp only [and_self, ite_true]; omega
    · rw [ite_eq_right_iff.2 (fun h => absurd h hb)]; omega
  · have := totalSent_deliver anonCount.toAlgo c v j
    rw [this, htot, hst v]
    simp [Abs.step]

/-- The initial configuration. -/
def absInit (n : ℕ) : Abs where
  st p := if p = 0 then leaderInit else nonLeaderInit
  tr p b := if b = false ∧ p = nxt n 0 then 1 else 0
  tot := 1

lemma matches_init : Matches ℓ (anonCount.initCfg (leaderInput ℓ)) (absInit n) := by
  refine ⟨fun w => ?_, fun w b => ?_, ?_⟩
  · simp only [Prog.initCfg, absInit, leaderInput, pos_eq_zero]
    by_cases h : w = ℓ <;> simp [h, anonCount]
  · cases b
    · simp only [Prog.initCfg, absInit, leaderInput, oriented_peer_false, sub_one_eq_iff (ℓ := ℓ),
        pos_self]
      by_cases h : w - 1 = ℓ
      · have h' := (sub_one_eq_iff (ℓ := ℓ) w ℓ).1 h
        rw [pos_self] at h'
        simp [h', anonCount]
      · have h' : ¬ pos ℓ w = nxt n 0 := fun e => h ((sub_one_eq_iff (ℓ := ℓ) w ℓ).2 (by rwa [pos_self]))
        simp [h', anonCount]
    · simp only [Prog.initCfg, absInit, leaderInput, oriented_peer_true]
      by_cases h : w + 1 = ℓ <;> simp [h, anonCount]
  · simp only [totalSent, Prog.initCfg, absInit, leaderInput, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [anonCount]
    rw [Finset.sum_congr rfl (g := fun x => if x = ℓ then 1 else 0)
      (fun x _ => by split_ifs <;> simp_all)]
    simp

end Podc.ContentOblivious.AnonCounting
