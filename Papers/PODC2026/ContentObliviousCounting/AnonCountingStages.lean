import Papers.PODC2026.ContentObliviousCounting.AnonCountingBasic

/-!
# Anonymous counting: the stages of an execution

Every reachable configuration of the counting algorithm (leader at position `0`) is described by
one of the following *stages* (`Stage.abs`), a function of positions:

* `out j m t` / `back j m t`: phase `j`, the leader at position `tri j` probes for the `m`-th time;
  the probe is on its way out (in transit to `Port0` of position `tri j + t`) or back (in transit to
  `Port1` of position `tri j + t`).
* `xfer j x y`: leadership transfer at the end of phase `j`: the CCW transfer pulse is in transit to
  the node at CCW distance `x` from the leader, the CW confirmation pulse to the node at CW distance
  `y` from the new leader.
* `pipe κ a b`: in the last phase, a *wave* of `κ.K` pulses sent by the last leader around the
  whole ring (completion probe, the three CCW traversals, the two traversals of each bit of `count`,
  the two final traversals); `a p` pulses of the wave have been relayed by position `p`, `b`
  received back by the leader.
* `final`: everyone has terminated.

`relF j F p` / `mphF j F p` are the values of `relayed` / `myPhase` of position `p` during phase `j`
when positions `1, …, F` have been probed.
-/

namespace Podc.ContentOblivious.AnonCounting

open Podc.ContentOblivious Finset

set_option linter.unusedSectionVars false

/-! ## Node data -/

/-- `relayed` of a non-leader at position `p` in phase `j` with positions `1..F` probed. -/
noncomputable def relF (j F p : ℕ) : ℕ :=
  if p = 0 then 0 else if p ≤ tri j then tri (phaseOf p + 1) - p else if p ≤ F then F - p else 0

/-- `myPhase` of the node at position `p` in phase `j` with positions `1..F` probed. -/
noncomputable def mphF (j F p : ℕ) : Option ℕ :=
  if p = 0 then none else if p ≤ tri j then some (phaseOf p) else if p ≤ F then some j else none

/-- Canonical local state (with `relayed` increased by `x`). -/
noncomputable def nst (pc : PC) (ph j F p x : ℕ) : St :=
  ⟨pc, ph, decide (p ≤ F), relF j F p + x, mphF j F p, 0, []⟩

/-- Canonical local state of a leader with `count = cnt`. -/
noncomputable def lst (pc : PC) (ph j F p cnt : ℕ) : St := { nst pc ph j F p 0 with count := cnt }

lemma relF_lead (j F : ℕ) : relF j F (tri j) = 0 := by
  unfold relF
  by_cases h0 : tri j = 0
  · simp [h0]
  rcases j with _ | j
  · simp at h0
  rcases j with _ | j
  · simp at h0
  rw [phaseOf_eq (k := j + 1) (by simp only [tri_succ]; omega) le_rfl]
  simp

lemma relF_succ (j p : ℕ) : relF (j + 1) (tri (j + 1)) p = relF j (tri (j + 1)) p := by
  unfold relF
  have := tri_succ j
  by_cases h : tri j < p ∧ p ≤ tri (j + 1)
  · rw [phaseOf_eq h.1 h.2]; split_ifs <;> omega
  · split_ifs <;> omega

lemma mphF_succ (j p : ℕ) : mphF (j + 1) (tri (j + 1)) p = mphF j (tri (j + 1)) p := by
  unfold mphF
  have := tri_succ j
  by_cases h : tri j < p ∧ p ≤ tri (j + 1)
  · rw [phaseOf_eq h.1 h.2]; split_ifs <;> first | rfl | (exfalso; omega)
  · split_ifs <;> first | rfl | (exfalso; omega)

lemma relF_old {j F F' p : ℕ} (h : p ≤ tri j) : relF j F p = relF j F' p := by
  unfold relF; split_ifs <;> rfl

lemma mphF_old {j F F' p : ℕ} (h : p ≤ tri j) : mphF j F p = mphF j F' p := by
  unfold mphF; split_ifs <;> rfl

/-! ### Evaluation of `relF` and `mphF` (for `simp (disch := omega)`) -/

lemma relF_zero' {j F p : ℕ} (h : p = 0) : relF j F p = 0 := by simp [relF, h]
lemma relF_le {j F p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ tri j) : relF j F p = tri (phaseOf p + 1) - p := by
  simp [relF, show p ≠ 0 by omega, h2]
lemma relF_mid {j F p : ℕ} (h1 : tri j < p) (h2 : p ≤ F) : relF j F p = F - p := by
  simp [relF, show p ≠ 0 by omega, show ¬ p ≤ tri j by omega, h2]
lemma relF_gt {j F p : ℕ} (h1 : tri j < p) (h2 : F < p) : relF j F p = 0 := by
  simp [relF, show p ≠ 0 by omega, show ¬ p ≤ tri j by omega, show ¬ p ≤ F by omega]
lemma mphF_zero' {j F p : ℕ} (h : p = 0) : mphF j F p = none := by simp [mphF, h]
lemma mphF_le {j F p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ tri j) : mphF j F p = some (phaseOf p) := by
  simp [mphF, show p ≠ 0 by omega, h2]
lemma mphF_mid {j F p : ℕ} (h1 : tri j < p) (h2 : p ≤ F) : mphF j F p = some j := by
  simp [mphF, show p ≠ 0 by omega, show ¬ p ≤ tri j by omega, h2]
lemma mphF_gt {j F p : ℕ} (h1 : tri j < p) (h2 : F < p) : mphF j F p = none := by
  simp [mphF, show p ≠ 0 by omega, show ¬ p ≤ tri j by omega, show ¬ p ≤ F by omega]

lemma relF_le0 {j F p : ℕ} (h : p ≤ tri j) :
    relF j F p = if p = 0 then 0 else tri (phaseOf p + 1) - p := by
  unfold relF; split_ifs <;> first | rfl | omega
lemma mphF_le0 {j F p : ℕ} (h : p ≤ tri j) :
    mphF j F p = if p = 0 then none else some (phaseOf p) := by
  unfold mphF; split_ifs <;> first | rfl | omega

lemma nst_eq_iff {pc pc' : PC} {ph ph' j j' F F' p x x' : ℕ} :
    nst pc ph j F p x = nst pc' ph' j' F' p x' ↔
      pc = pc' ∧ ph = ph' ∧ (p ≤ F ↔ p ≤ F') ∧ relF j F p + x = relF j' F' p + x' ∧
        mphF j F p = mphF j' F' p := by
  simp [nst]

lemma lst_eq_iff {pc pc' : PC} {ph ph' j j' F F' p c c' : ℕ} :
    lst pc ph j F p c = lst pc' ph' j' F' p c' ↔
      pc = pc' ∧ ph = ph' ∧ (p ≤ F ↔ p ≤ F') ∧ relF j F p = relF j' F' p ∧
        mphF j F p = mphF j' F' p ∧ c = c' := by
  simp [lst, nst]

/-! ## Distances on the ring -/

/-- CCW distance from `L` to `p`. -/
def ccwD (n L p : ℕ) : ℕ := if p ≤ L then L - p else L + n - p

/-- CW distance from `R` to `p`. -/
def cwD (n R p : ℕ) : ℕ := if R ≤ p then p - R else p + n - R

lemma ccwD_le {n L p : ℕ} (h : p ≤ L) : ccwD n L p = L - p := by simp [ccwD, h]
lemma ccwD_gt {n L p : ℕ} (h : L < p) : ccwD n L p = L + n - p := by
  simp [ccwD, show ¬ p ≤ L by omega]
lemma cwD_ge {n R p : ℕ} (h : R ≤ p) : cwD n R p = p - R := by simp [cwD, h]
lemma cwD_lt {n R p : ℕ} (h : p < R) : cwD n R p = p + n - R := by
  simp [cwD, show ¬ R ≤ p by omega]

/-! ## Probing stages -/

/-- Phase `j`, `m`-th probe, on its way out, in transit to `Port0` of position `tri j + t`. -/
noncomputable def absOut (n j m t : ℕ) : Abs where
  st p := if p = tri j then lst .probe j j (tri j + m - 1) p (m - 1)
    else if tri j < p ∧ p < tri j + t then nst .relay j j (tri j + m) p 0
    else nst .main j j (tri j + m - 1) p 0
  tr p b := if p = tri j + t ∧ b = false then 1 else 0
  tot := phasesCost n j + m * (m - 1) + t

/-- Phase `j`, `m`-th probe, on its way back, in transit to `Port1` of position `tri j + t`. -/
noncomputable def absBack (n j m t : ℕ) : Abs where
  st p := if p = tri j then lst .probe j j (tri j + m) p (m - 1)
    else if tri j < p ∧ p ≤ tri j + t then nst .relay j j (tri j + m) p 0
    else nst .main j j (tri j + m) p 0
  tr p b := if p = tri j + t ∧ b = true then 1 else 0
  tot := phasesCost n j + m * (m - 1) + 2 * m - t

/-- Leadership transfer at the end of phase `j` (from `tri j` to `tri (j + 1)`). -/
noncomputable def absXfer (n j x y : ℕ) : Abs where
  st p :=
    if p = tri j then
      (if x ≤ n then lst .tr1 j j (tri (j + 1)) p j
       else if y ≤ n - j then lst .tr2 j j (tri (j + 1)) p j
       else nst .main (j + 1) j (tri (j + 1)) p 0)
    else if p = tri (j + 1) then
      (if x ≤ n - j then nst .main j j (tri (j + 1)) p 0
       else nst .newLeader j j (tri (j + 1)) p 0)
    else if x ≤ ccwD n (tri j) p then nst .main j j (tri (j + 1)) p 0
    else if cwD n (tri (j + 1)) p < y then nst .main (j + 1) j (tri (j + 1)) p 0
    else nst .wait2 j j (tri (j + 1)) p 0
  tr p b :=
    if b = true then (if x ≤ n ∧ (if p = tri j then n else ccwD n (tri j) p) = x then 1 else 0)
    else (if 1 ≤ y ∧ (if p = tri (j + 1) then n else cwD n (tri (j + 1)) p) = y then 1 else 0)
  tot := phasesCost n j + j * (j + 1) + min x n + y

/-! ## Waves of the last phase -/

/-- Position from which a wave travelling clockwise (`cw`) or counter-clockwise reaches `p`. -/
def src (n : ℕ) (cw : Bool) (p : ℕ) : ℕ := if cw then prv n p else nxt n p

/-- Pulses in transit in a wave of `K` pulses sent by `L`: position `p ≠ L` has relayed `a p`
of them, `L` has received `b` back. -/
def pipeTr (n L K : ℕ) (cw : Bool) (a : ℕ → ℕ) (b p : ℕ) (b' : Bool) : ℕ :=
  if b' = !cw then
    (if src n cw p = L then K else a (src n cw p)) - (if p = L then b else a p)
  else 0

/-- Consistency of a wave profile. -/
def PipeOk (n L K : ℕ) (cw : Bool) (a : ℕ → ℕ) (b : ℕ) : Prop :=
  b < K ∧ (∀ p < n, p ≠ L → a p ≤ K ∧ a p ≤ (if src n cw p = L then K else a (src n cw p))) ∧
    b ≤ (if src n cw L = L then K else a (src n cw L))

/-- The kinds of waves of the last phase. -/
inductive Kind where
  /-- the completion probe (one CW traversal, Algorithm 2 line 3 with all nodes counted) -/
  | comp
  /-- the three CCW traversals (Algorithm 2 lines 8–9) -/
  | fin3
  /-- the two traversals for bit `k` of `count` (Algorithm 3, lines 2–7) -/
  | bit (k : ℕ)
  /-- the CW traversal of Algorithm 3, lines 8–9 -/
  | end1
  /-- the CCW traversal of Algorithm 3, lines 10–11 -/
  | end2

/-- Position of the last leader. -/
noncomputable def lead (n : ℕ) : ℕ := tri (lastPhase n)

/-- The binary digits of the final `count`, least significant first. -/
noncomputable def D (n : ℕ) : List ℕ := Nat.digits 2 (lastCount n)

/-- Number of pulses of a wave. -/
def Kind.K : Kind → ℕ
  | .comp => 1
  | .fin3 => 3
  | .bit _ => 2
  | .end1 => 1
  | .end2 => 1

/-- Direction of a wave. -/
noncomputable def Kind.cw (n : ℕ) : Kind → Bool
  | .comp => true
  | .fin3 => false
  | .bit k => decide ((D n).getD k 0 = 1)
  | .end1 => true
  | .end2 => false

/-- State of a non-leader in the last phase, after the completion probe has passed. -/
noncomputable def fst (n : ℕ) (pc : PC) (p : ℕ) (l : List ℕ) : St :=
  { nst pc (lastPhase n) (lastPhase n) (n - 1) p 1 with bits := l }

/-- State of the last leader. -/
noncomputable def gst (n : ℕ) (pc : PC) (l : List ℕ) : St :=
  { lst pc (lastPhase n) (lastPhase n) (n - 1) (lead n) (lastCount n) with bits := l }

lemma gst_nil (n : ℕ) (pc : PC) :
    gst n pc [] = lst pc (lastPhase n) (lastPhase n) (n - 1) (lead n) (lastCount n) := rfl

/-- State of a non-leader at position `p` that has relayed `k` pulses of the wave. -/
noncomputable def Kind.f (n : ℕ) : Kind → ℕ → ℕ → St
  | .comp, p, k =>
    if k = 0 then nst .main (lastPhase n) (lastPhase n) (n - 1) p 0 else fst n .relay p []
  | .fin3, p, k =>
    fst n (if k = 0 then .relay else if k = 1 then .main else if k = 2 then .wait2 else .rcvQ) p []
  | .bit i, p, k =>
    fst n (if k = 1 then .rcvU (!decide ((D n).getD i 0 = 1)) else .rcvQ) p
      (if k ≤ 1 then (D n).take i else (D n).take (i + 1))
  | .end1, p, k => fst n (if k = 0 then .rcvQ else .rcvU false) p (D n)
  | .end2, p, k => fst n (if k = 0 then .rcvU false else .doneN) p (D n)

/-- State of the last leader that has received `b` pulses of the wave. -/
noncomputable def Kind.g (n : ℕ) : Kind → ℕ → St
  | .comp, _ => gst n .probe []
  | .fin3, b => gst n (.fin b) []
  | .bit i, b => gst n (.sndBit b) ((D n).drop i)
  | .end1, _ => gst n .sndEnd1 []
  | .end2, _ => gst n .sndEnd2 []

/-- Pulses sent in phases `1, …, i - 1` and by the probes of phase `i` before the completion
probe. -/
noncomputable def lastBase (n : ℕ) : ℕ :=
  phasesCost n (lastPhase n) + lastCount n * (lastCount n + 1)

/-- Pulses sent before the wave, plus the `K` pulses sent by the leader to start it. -/
noncomputable def Kind.base (n : ℕ) : Kind → ℕ
  | .comp => lastBase n + 1
  | .fin3 => lastBase n + n + 3
  | .bit i => lastBase n + 4 * n + 2 * n * i + 2
  | .end1 => lastBase n + 4 * n + 2 * n * (D n).length + 1
  | .end2 => lastBase n + 4 * n + 2 * n * (D n).length + n + 1

/-- Side condition of a wave kind. -/
def Kind.Ok (n : ℕ) : Kind → Prop
  | .bit i => i < (D n).length
  | _ => True

/-- A wave stage. -/
noncomputable def absPipe (n : ℕ) (κ : Kind) (a : ℕ → ℕ) (b : ℕ) : Abs where
  st p := if p = lead n then κ.g n b else κ.f n p (a p)
  tr := pipeTr n (lead n) κ.K (κ.cw n) a b
  tot := κ.base n + ∑ p ∈ (range n).erase (lead n), a p

/-- The final configuration. -/
noncomputable def absFinal (n : ℕ) : Abs where
  st p := if p = lead n then gst n .doneL [] else fst n .doneN p (D n)
  tr _ _ := 0
  tot := totalPulses n

/-! ## Stages -/

/-- Stages of an execution. -/
inductive Stage where
  | out (j m t : ℕ)
  | back (j m t : ℕ)
  | xfer (j x y : ℕ)
  | pipe (κ : Kind) (a : ℕ → ℕ) (b : ℕ)
  | final

/-- Side conditions of the stages. -/
def Stage.Ok (n : ℕ) : Stage → Prop
  | .out j m t => 1 ≤ j ∧ 1 ≤ m ∧ m ≤ j ∧ tri j + m < n ∧ 1 ≤ t ∧ t ≤ m
  | .back j m t => 1 ≤ j ∧ 1 ≤ m ∧ m ≤ j ∧ tri j + m < n ∧ t < m
  | .xfer j x y => 1 ≤ j ∧ tri (j + 1) < n ∧ 1 ≤ x ∧ x ≤ n + 1 ∧ y ≤ n ∧
      (1 ≤ y ↔ n - j < x) ∧ (n - j < y → x = n + 1)
  | .pipe κ a b => κ.Ok n ∧ PipeOk n (lead n) κ.K (κ.cw n) a b
  | .final => True

/-- The configuration described by a stage. -/
noncomputable def Stage.abs (n : ℕ) : Stage → Abs
  | .out j m t => absOut n j m t
  | .back j m t => absBack n j m t
  | .xfer j x y => absXfer n j x y
  | .pipe κ a b => absPipe n κ a b
  | .final => absFinal n

/-- The step relation between stages: every enabled delivery leads to another stage. -/
def StepOk (n : ℕ) (s : Stage) : Prop :=
  ∀ q j, (s.abs n).En n q j → ∃ s' : Stage, s'.Ok n ∧ Agree n ((s.abs n).step n q j) (s'.abs n)

end Podc.ContentOblivious.AnonCounting
