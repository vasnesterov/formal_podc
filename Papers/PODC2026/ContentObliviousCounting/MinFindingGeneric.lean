import Cslib.Computability.Distributed.ContentOblivious.Staged
import Mathlib

/-!
# Minimum finding by repeated ComputeOR (Algorithm 10, Theorem 5), from an abstract ComputeOR

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260), §9.1, Algorithm 10 (`MinFinding`) and Theorem 5.

Every node holds a bit string (MSB first) and an `active` flag (the participants). The algorithm
first finds the minimum length `m` of the participants' strings by calls
`ComputeOR(active ∧ B ≥ len)` for `B = 1, 2, …`, keeps active the participants of length `m`, and
then determines the minimum bit by bit: in phase `p` the call `ComputeOR(active ∧ bits[p] = 0)`
tells whether some remaining candidate has a `0`; if so the candidates with a `1` drop out.

**Pseudo-code fix.** Line 8 of Algorithm 10 loops `while phase < len(bits)`, with the node's *own*
length: nodes whose strings are longer than `m` would call `ComputeOR` more often than the others,
so the calls would no longer match. The text says "we assume that every input is represented as a
bit string of equal length B"; we loop `while phase < B` (the common value `m`).

The ComputeOR procedure is abstract here (`ORSpec`); see `MinFinding.lean` for the instance.
-/

namespace Podc.ContentOblivious.MinFinding

open Cslib.ContentOblivious Finset

/-- Node input: leader flag, participation flag, bit string (MSB first, `false` = 0). -/
abbrev Input := Bool × Bool × List Bool

/-- Local variables of Algorithm 10. `lenPhase`: still in the length-search loop (lines 1–4). -/
structure St where
  leader : Bool
  active : Bool
  bits : List Bool
  B : ℕ
  lenPhase : Bool
  p : ℕ
  minBits : List Bool

/-- Input of `ComputeOR` in bit phase `p`: `hasZero = active ∧ bits[p] = 0`. -/
def hasZero (a : Bool) (bits : List Bool) (p : ℕ) : Bool := a && (bits[p]? == some false)

/-- The driver of Algorithm 10 (with the fix `while phase < B`). -/
def driver : Driver Input (Bool × Bool) Bool St where
  start i := (⟨i.1, i.2.1, i.2.2, 1, true, 0, []⟩,
    some (i.1, i.2.1 && decide (i.2.2.length ≤ 1)))
  next d r :=
    if d.lenPhase then
      if r then
        let a := d.active && decide (d.bits.length = d.B)
        (⟨d.leader, a, d.bits, d.B, false, 0, []⟩, some (d.leader, hasZero a d.bits 0))
      else
        (⟨d.leader, d.active, d.bits, d.B + 1, true, 0, []⟩,
          some (d.leader, d.active && decide (d.bits.length ≤ d.B + 1)))
    else
      let a := if r then d.active && (d.bits[d.p]? != some true) else d.active
      (⟨d.leader, a, d.bits, d.B, false, d.p + 1, d.minBits ++ [!r]⟩,
        if d.p + 1 < d.B then some (d.leader, hasZero a d.bits (d.p + 1)) else none)

/-- The minimum-finding program. -/
abbrev prog (OR : Proc (Bool × Bool) Bool) : Proc Input St := OR.staged driver

variable {n : ℕ} [NeZero n]

/-- Hypotheses on the ComputeOR procedure (Theorem 21). -/
structure ORSpec (OR : Proc (Bool × Bool) Bool) (lead : ZMod n → Bool) : Prop where
  init : ∀ a, OR.result (OR.init a).1 = none
  comp : ∀ b : ZMod n → Bool, OR.Composable (oriented n) (fun v => (lead v, b v))
  ret : ∀ b : ZMod n → Bool,
    OR.Returns (oriented n) (fun v => (lead v, b v)) (fun _ => decide (∃ v, b v = true))
  bound : ∀ b : ZMod n → Bool, ∀ c, OR.Reach (oriented n) (fun v => (lead v, b v)) c →
    totalSent c ≤ 3 * n

section schedule

variable (a0 : ZMod n → Bool) (bits : ZMod n → List Bool)

/-- Value of a bit string, MSB first. -/
def val (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + b.toNat) 0

lemma val_append (l : List Bool) (b : Bool) : val (l ++ [b]) = 2 * val l + b.toNat := by
  simp [val, List.foldl_append]

/-- Existence of a participant: needed for the length search to stop. -/
lemma exists_len (h : ∃ v, a0 v = true) : ∃ B, ∃ v, a0 v = true ∧ (bits v).length ≤ B := by
  obtain ⟨v, hv⟩ := h
  exact ⟨_, v, hv, le_rfl⟩

variable (hex : ∃ v, a0 v = true)

/-- `m`: the minimum length of a participant's string. -/
noncomputable def minLen : ℕ := by
  classical exact Nat.find (exists_len a0 bits hex)

/-- Participants of minimum length (line 5). -/
noncomputable def a1 (v : ZMod n) : Bool := a0 v && decide ((bits v).length = minLen a0 bits hex)

/-- The prefix of the minimum after `p` bit phases. -/
noncomputable def mb : ℕ → List Bool
  | 0 => []
  | p + 1 => mb p ++ [!(decide (∃ v, hasZero (a1 a0 bits hex v &&
      decide ((bits v).take p = mb p)) (bits v) p = true))]

/-- The candidates after `p` bit phases. -/
noncomputable def actP (p : ℕ) (v : ZMod n) : Bool :=
  a1 a0 bits hex v && decide ((bits v).take p = mb a0 bits hex p)

/-- Whether some candidate has a `0` at position `p` (the result of `ComputeOR` in phase `p`). -/
noncomputable def eP (p : ℕ) : Bool :=
  decide (∃ v, hasZero (actP a0 bits hex p v) (bits v) p = true)

lemma mb_succ (p : ℕ) : mb a0 bits hex (p + 1) = mb a0 bits hex p ++ [!eP a0 bits hex p] := rfl

variable {a0 bits hex}

lemma mb_length (p : ℕ) : (mb a0 bits hex p).length = p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [mb_succ]; simp [ih]

lemma minLen_le_iff (B : ℕ) :
    minLen a0 bits hex ≤ B ↔ ∃ v, a0 v = true ∧ (bits v).length ≤ B := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv, hl⟩ : ∃ v, a0 v = true ∧ (bits v).length ≤ minLen a0 bits hex := by
      unfold minLen; exact Nat.find_spec (exists_len a0 bits hex)
    exact ⟨v, hv, hl.trans h⟩
  · intro h; unfold minLen; exact Nat.find_min' _ h

lemma actP_succ {p : ℕ} (hp : p < minLen a0 bits hex) (v : ZMod n) :
    actP a0 bits hex (p + 1) v = if eP a0 bits hex p then
      (actP a0 bits hex p v && ((bits v)[p]? != some true)) else actP a0 bits hex p v := by
  unfold actP
  rw [mb_succ]
  by_cases ha : a1 a0 bits hex v = true
  · have hlen : (bits v).length = minLen a0 bits hex := by
      simp only [a1, Bool.and_eq_true, decide_eq_true_eq] at ha; exact ha.2
    have hpl : p < (bits v).length := hlen ▸ hp
    rw [List.take_add_one, List.getElem?_eq_getElem hpl]
    simp only [Option.toList_some, ha, Bool.true_and]
    have _key : ((bits v).take p ++ [(bits v)[p]] = mb a0 bits hex p ++ [!eP a0 bits hex p]) ↔
        ((bits v).take p = mb a0 bits hex p ∧ (bits v)[p] = !eP a0 bits hex p) := by
      constructor
      · intro h
        obtain ⟨h1, h2⟩ := List.append_inj' h rfl
        exact ⟨h1, by simpa using h2⟩
      · rintro ⟨h1, h2⟩; rw [h1, h2]
    have hne : ∀ b, (bits v).take p ≠ mb a0 bits hex p →
        ¬ ((bits v).take p ++ [b] = mb a0 bits hex p ++ [!eP a0 bits hex p]) :=
      fun b ht h => ht (List.append_inj' h rfl).1
    by_cases he : eP a0 bits hex p = true
    · rw [ite_eq_left he]
      by_cases ht : (bits v).take p = mb a0 bits hex p
      · by_cases hb : (bits v)[p] = true <;> simp [ht, hb, he]
      · simp [ht]
        rw [List.take_add_one, List.getElem?_eq_getElem hpl]; exact hne _ ht
    · rw [ite_eq_right he]
      simp only [Bool.not_eq_true] at he
      by_cases ht : (bits v).take p = mb a0 bits hex p
      · have hb : (bits v)[p] = true := by
          by_contra hb
          simp only [Bool.not_eq_true] at hb
          have : eP a0 bits hex p = true := by
            unfold eP
            refine decide_eq_true ⟨v, ?_⟩
            simp [hasZero, actP, ha, ht, List.getElem?_eq_getElem hpl, hb]
          rw [he] at this; exact absurd this (by simp)
        simp [ht, hb, he]
      · simp [ht]
        rw [List.take_add_one, List.getElem?_eq_getElem hpl]; exact hne _ ht
  · simp only [Bool.not_eq_true] at ha
    simp [ha]

variable (a0 bits hex) (lead : ZMod n → Bool)

/-- Scheduled local states. -/
noncomputable def dS (k : ℕ) (v : ZMod n) : St :=
  if k < minLen a0 bits hex then ⟨lead v, a0 v, bits v, k + 1, true, 0, []⟩
  else ⟨lead v, actP a0 bits hex (k - minLen a0 bits hex) v, bits v, minLen a0 bits hex, false,
    k - minLen a0 bits hex, mb a0 bits hex (k - minLen a0 bits hex)⟩

/-- Scheduled `ComputeOR` inputs. -/
noncomputable def jS (k : ℕ) (v : ZMod n) : Bool × Bool :=
  if k < minLen a0 bits hex then (lead v, a0 v && decide ((bits v).length ≤ k + 1))
  else (lead v, hasZero (actP a0 bits hex (k - minLen a0 bits hex) v) (bits v)
    (k - minLen a0 bits hex))

/-- Scheduled `ComputeOR` results. -/
noncomputable def rS (k : ℕ) (_v : ZMod n) : Bool :=
  if k < minLen a0 bits hex then decide (minLen a0 bits hex ≤ k + 1)
  else eP a0 bits hex (k - minLen a0 bits hex)

variable {a0 bits hex lead}

lemma one_le_minLen (hne : ∀ v, a0 v = true → bits v ≠ []) : 1 ≤ minLen a0 bits hex := by
  by_contra h
  have h0 : minLen a0 bits hex ≤ 0 := by omega
  obtain ⟨v, hv, hl⟩ := (minLen_le_iff 0).1 h0
  exact hne v hv (List.eq_nil_of_length_eq_zero (by omega))

lemma schedule {OR : Proc (Bool × Bool) Bool} (hOR : ORSpec OR lead)
    (hne : ∀ v, a0 v = true → bits v ≠ []) :
    Schedule OR driver (oriented n) (fun v => (lead v, a0 v, bits v)) (2 * minLen a0 bits hex)
      (dS a0 bits hex lead) (jS a0 bits hex lead) (rS a0 bits hex) := by
  have hm := one_le_minLen (hex := hex) hne
  set m := minLen a0 bits hex with hm_def
  refine ⟨hOR.init, fun v => ?_, fun k hk v => ?_, fun k _ => ?_, fun k _ => ?_⟩
  · simp [driver, dS, jS, ← hm_def, show 0 < m by omega, show 0 < 2 * m by omega]
  · by_cases hkm : k < m
    · by_cases hk1 : k + 1 < m
      · simp [driver, dS, jS, rS, ← hm_def, hkm, hk1, show ¬ m ≤ k + 1 by omega,
          show k + 1 < 2 * m by omega]
      · have e : k + 1 - m = 0 := by omega
        have hB : k + 1 = m := by omega
        simp only [rS, dS, jS, ← hm_def, hkm, hk1, ite_true, ite_false, e, driver,
          show m ≤ k + 1 by omega, decide_true, show k + 1 < 2 * m by omega]
        refine Prod.ext ?_ ?_
        · simp [actP, a1, mb, hB, ← hm_def]
        · simp [actP, a1, mb, hB, ← hm_def]
    · have hp : k - m < m := by omega
      have e : k + 1 - m = k - m + 1 := by omega
      simp only [rS, dS, jS, ← hm_def, hkm, ite_false, show ¬ k + 1 < m by omega, e, driver,
        Bool.false_eq_true]
      refine Prod.ext ?_ ?_
      · simp only
        rw [actP_succ hp v, mb_succ]
      · simp only
        rw [actP_succ hp v]
        by_cases h : k - m + 1 < m
        · simp [h, show k + 1 < 2 * m by omega]
        · simp [h, show ¬ k + 1 < 2 * m by omega]
  · have e : jS a0 bits hex lead k = fun v => (lead v, (jS a0 bits hex lead k v).2) := by
      funext v; simp [jS]; split_ifs <;> rfl
    rw [e]; exact hOR.comp _
  · have e : jS a0 bits hex lead k = fun v => (lead v, (jS a0 bits hex lead k v).2) := by
      funext v; simp [jS]; split_ifs <;> rfl
    have er : rS a0 bits hex k = fun _ => decide (∃ v, (jS a0 bits hex lead k v).2 = true) := by
      funext v
      by_cases hkm : k < m
      · simp only [rS, jS, ← hm_def, hkm, ite_true, Bool.and_eq_true, decide_eq_true_eq]
        exact decide_eq_decide.2 (minLen_le_iff _)
      · simp only [rS, jS, ← hm_def, hkm, ite_false, eP]
    rw [e, er]; exact hOR.ret _

lemma minLen_le_len {v : ZMod n} (hv : a0 v = true) : minLen a0 bits hex ≤ (bits v).length :=
  (minLen_le_iff _).2 ⟨v, hv, le_rfl⟩

/-- Invariant of the bit phases: some candidate is left, and every participant of minimum length
either matches the prefix found so far or has a strictly larger prefix. -/
lemma mb_spec {p : ℕ} (hp : p ≤ minLen a0 bits hex) :
    (∃ w, actP a0 bits hex p w = true) ∧ ∀ v, a1 a0 bits hex v = true →
      (bits v).take p = mb a0 bits hex p ∨ val (mb a0 bits hex p) < val ((bits v).take p) := by
  induction p with
  | zero =>
    refine ⟨?_, fun v _ => Or.inl (by simp [mb])⟩
    obtain ⟨w, hw, hl⟩ := (minLen_le_iff (hex := hex) (minLen a0 bits hex)).1 le_rfl
    have := minLen_le_len (bits := bits) (hex := hex) hw
    exact ⟨w, by simp [actP, a1, hw, mb, show (bits w).length = minLen a0 bits hex by omega]⟩
  | succ p ih =>
    have hp' : p < minLen a0 bits hex := by omega
    obtain ⟨⟨w, hw⟩, hord⟩ := ih (by omega)
    refine ⟨?_, fun v hv => ?_⟩
    · by_cases he : eP a0 bits hex p = true
      · obtain ⟨u, hu⟩ := of_decide_eq_true he
        refine ⟨u, ?_⟩
        rw [actP_succ hp', ite_eq_left he]
        simp only [hasZero, Bool.and_eq_true, beq_iff_eq] at hu
        simp [hu.1, hu.2]
      · exact ⟨w, by rw [actP_succ hp', ite_eq_right he]; exact hw⟩
    · have hlen : (bits v).length = minLen a0 bits hex := by
        simp only [a1, Bool.and_eq_true, decide_eq_true_eq] at hv; exact hv.2
      have hpl : p < (bits v).length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hpl, mb_succ]
      simp only [Option.toList_some, val_append]
      rcases hord v hv with heq | hlt
      · rw [heq]
        by_cases hb : (bits v)[p] = !eP a0 bits hex p
        · left; rw [hb]
        · right
          by_cases he : eP a0 bits hex p = true
          · have : (bits v)[p] = true := by rw [he] at hb; simpa using hb
            rw [he, this]; simp
          · exfalso
            simp only [Bool.not_eq_true] at he
            have hb' : (bits v)[p] = false := by rw [he] at hb; simpa using hb
            have : eP a0 bits hex p = true := by
              unfold eP
              refine decide_eq_true ⟨v, ?_⟩
              simp [hasZero, actP, hv, heq, List.getElem?_eq_getElem hpl, hb']
            rw [he] at this; exact absurd this (by simp)
      · right
        have h1 : (!eP a0 bits hex p).toNat ≤ 1 := Bool.toNat_le _
        omega

/-- The final prefix is the minimum of the participants' strings of minimum length. -/
lemma mb_final :
    (∃ w, a1 a0 bits hex w = true ∧ bits w = mb a0 bits hex (minLen a0 bits hex)) ∧
    ∀ v, a1 a0 bits hex v = true → bits v = mb a0 bits hex (minLen a0 bits hex) ∨
      val (mb a0 bits hex (minLen a0 bits hex)) < val (bits v) := by
  obtain ⟨⟨w, hw⟩, hord⟩ := mb_spec (hex := hex) (le_refl (minLen a0 bits hex))
  have htake : ∀ v, a1 a0 bits hex v = true → (bits v).take (minLen a0 bits hex) = bits v := by
    intro v hv
    simp only [a1, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact List.take_of_length_le hv.2.le
  refine ⟨?_, fun v hv => by rw [← htake v hv]; exact hord v hv⟩
  simp only [actP, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨w, hw.1, by rw [← htake w hw.1]; exact hw.2⟩

/-- **Theorem 5 (bit strings, abstract ComputeOR).** Algorithm 10 (with the loop bound fixed to the
common length) on an oriented ring with a leader, at least one participant and non-empty strings:
every final configuration is quiescent; every node outputs the same string `mb m`, which is the
minimum (as a binary number) among the participants' strings of minimum length `m`; a node stays
active iff it is a participant whose string is that minimum. At most `6·n·m` pulses are sent, and
the procedure is composable. -/
theorem theorem_5_bits {OR : Proc (Bool × Bool) Bool} (hOR : ORSpec OR lead)
    (hne : ∀ v, a0 v = true → bits v ≠ []) :
    (∀ c, (prog OR).Reach (oriented n) (fun v => (lead v, a0 v, bits v)) c →
      (prog OR).Final (oriented n) c → (prog OR).Quiescent (oriented n) c ∧ ∀ v,
        (c.st v).2 = none ∧ (c.st v).1.minBits = mb a0 bits hex (minLen a0 bits hex) ∧
        ((c.st v).1.active = true ↔ a0 v = true ∧ bits v = mb a0 bits hex (minLen a0 bits hex))) ∧
    (∀ c, (prog OR).Reach (oriented n) (fun v => (lead v, a0 v, bits v)) c →
      totalSent c ≤ 6 * n * minLen a0 bits hex) ∧
    (prog OR).Composable (oriented n) (fun v => (lead v, a0 v, bits v)) := by
  have hS := schedule (hex := hex) hOR hne
  have hm := one_le_minLen (hex := hex) hne
  have hB : ∀ k < 2 * minLen a0 bits hex, ∀ c, OR.Reach (oriented n) (jS a0 bits hex lead k) c →
      totalSent c ≤ 3 * n := by
    intro k _ c hc
    have e : jS a0 bits hex lead k = fun v => (lead v, (jS a0 bits hex lead k v).2) := by
      funext v; simp [jS]; split_ifs <;> rfl
    rw [e] at hc; exact hOR.bound _ c hc
  refine ⟨fun c hc hfin => ?_, fun c hc => ?_, hS.composable hB⟩
  · obtain ⟨hq, hst⟩ := hS.final hc hfin
    refine ⟨hq, fun v => ⟨by rw [hst v], ?_, ?_⟩⟩
    · rw [hst v]; simp [dS, show ¬ 2 * minLen a0 bits hex < minLen a0 bits hex by omega,
        show 2 * minLen a0 bits hex - minLen a0 bits hex = minLen a0 bits hex by omega]
    · rw [hst v]
      simp only [dS, show ¬ 2 * minLen a0 bits hex < minLen a0 bits hex by omega, ite_false,
        show 2 * minLen a0 bits hex - minLen a0 bits hex = minLen a0 bits hex by omega, actP, a1,
        Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, by rw [← h3]; exact (List.take_of_length_le h2.le).symm⟩
      · rintro ⟨h1, h2⟩
        have hl : (bits v).length = minLen a0 bits hex := by
          rw [h2, mb_length]
        exact ⟨⟨h1, hl⟩, by rw [List.take_of_length_le hl.le, h2]⟩
  · have := hS.totalSent_le hB hc
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    calc totalSent c ≤ 2 * minLen a0 bits hex * (3 * n) := this
      _ = 6 * n * minLen a0 bits hex := by ring

/-! ## Natural-number inputs -/

/-- Binary representation of a natural number, MSB first (`enc 0 = [0]`); its length is the bit
length `|x| = ⌊log₂ x⌋ + 1`. -/
def enc (x : ℕ) : List Bool :=
  if x < 2 then [decide (x = 1)] else enc (x / 2) ++ [decide (x % 2 = 1)]
termination_by x
decreasing_by omega

lemma val_enc (x : ℕ) : val (enc x) = x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [enc]
    split_ifs with h
    · interval_cases x <;> rfl
    · rw [val_append, ih _ (by omega)]
      by_cases h2 : x % 2 = 1 <;> simp [h2] <;> omega

lemma length_enc (x : ℕ) : (enc x).length = Nat.log 2 x + 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [enc]
    split_ifs with h
    · interval_cases x <;> simp
    · rw [List.length_append, ih _ (by omega), List.length_singleton, Nat.log_div_base]
      have : 1 ≤ Nat.log 2 x := Nat.log_pos (by norm_num) (by omega)
      omega

lemma enc_ne_nil (x : ℕ) : enc x ≠ [] := by
  intro h; have := length_enc x; rw [h] at this; simp at this

include hex in
/-- **Theorem 5.** On an oriented ring with a leader, if every process `v` holds `x v ∈ ℕ` and the
participants (`a0`, at least one) run Algorithm 10 (loop bound fixed) on the binary
representations, every final configuration is quiescent, every process outputs
`xmin = min {x v | a0 v}` (and stays active iff it is a participant holding `xmin`), and at most
`6·n·|xmin|` pulses are sent, `|xmin| = ⌊log₂ xmin⌋ + 1`. Anonymous: only the leader is
distinguished. -/
theorem theorem_5 {OR : Proc (Bool × Bool) Bool} (hOR : ORSpec OR lead) (x : ZMod n → ℕ) :
    ∃ xmin, (∃ w, a0 w = true ∧ x w = xmin) ∧ (∀ v, a0 v = true → xmin ≤ x v) ∧
    (∀ c, (prog OR).Reach (oriented n) (fun v => (lead v, a0 v, enc (x v))) c →
      (prog OR).Final (oriented n) c → (prog OR).Quiescent (oriented n) c ∧ ∀ v,
        (c.st v).2 = none ∧ val (c.st v).1.minBits = xmin ∧
        ((c.st v).1.active = true ↔ a0 v = true ∧ x v = xmin)) ∧
    (∀ c, (prog OR).Reach (oriented n) (fun v => (lead v, a0 v, enc (x v))) c →
      totalSent c ≤ 6 * n * (Nat.log 2 xmin + 1)) := by
  set bits : ZMod n → List Bool := fun v => enc (x v)
  have hne : ∀ v, a0 v = true → bits v ≠ [] := fun v _ => enc_ne_nil _
  obtain ⟨hfin, hbound, -⟩ := theorem_5_bits (bits := bits) (hex := hex) hOR hne
  obtain ⟨⟨w, hw, hwe⟩, hord⟩ := mb_final (bits := bits) (hex := hex)
  set M := mb a0 bits hex (minLen a0 bits hex) with hM
  have hw' : a0 w = true ∧ (bits w).length = minLen a0 bits hex := by
    simpa [a1] using hw
  have hvalw : val M = x w := by rw [← hwe]; exact val_enc _
  have hmin : ∀ v, a0 v = true → val M ≤ x v := by
    intro v hv
    by_cases hl : (bits v).length = minLen a0 bits hex
    · rcases hord v (by simp [a1, hv, hl]) with h | h
      · rw [← val_enc (x v)]; exact le_of_eq (by rw [show enc (x v) = bits v from rfl, h])
      · rw [← val_enc (x v)]; exact h.le
    · by_contra hlt
      push Not at hlt
      have h1 := minLen_le_len (bits := bits) (hex := hex) hv
      have h2 : Nat.log 2 (x v) ≤ Nat.log 2 (x w) := Nat.log_mono_right (by omega)
      have h3 := length_enc (x v)
      have h4 := length_enc (x w)
      have : (bits v).length ≤ (bits w).length := by
        simp only [bits]; omega
      omega
  refine ⟨val M, ⟨w, hw'.1, hvalw.symm⟩, hmin, fun c hc hf => ?_, fun c hc => ?_⟩
  · obtain ⟨hq, hst⟩ := hfin c hc hf
    refine ⟨hq, fun v => ⟨(hst v).1, by rw [(hst v).2.1], ?_⟩⟩
    rw [(hst v).2.2]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← val_enc (x v)]; exact congrArg val h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      -- equal values and equal minimal lengths give equal strings
      have hl : (bits v).length = minLen a0 bits hex := by
        rw [← hw'.2]; show (enc (x v)).length = (enc (x w)).length; rw [h2, hvalw]
      rcases hord v (by simp [a1, h1, hl]) with h | h
      · exact h
      · exfalso; rw [show bits v = enc (x v) from rfl, val_enc] at h; omega
  · have := hbound c hc
    have hm : minLen a0 bits hex = Nat.log 2 (val M) + 1 := by
      rw [hvalw, ← hw'.2]; exact length_enc _
    rwa [hm] at this

end schedule

end Podc.ContentOblivious.MinFinding
