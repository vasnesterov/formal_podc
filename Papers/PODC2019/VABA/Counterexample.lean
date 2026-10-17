import Papers.PODC2019.VABA.Safety

/-!
# VABA: the thresholds `2f + 1` need `n = 3f + 1`

The paper allows any `f < n/3` but hard-codes the threshold `2f + 1` for signatures and for the
number of view-change messages. Its proof of PB-provability (Lemma 3) says: two sets of `2f + 1`
signers each contain `f + 1` honest parties, "and thus there is an honest party in both". This
needs `2(f + 1) > n - f`, i.e. `n = 3f + 1`.

For `n = 5`, `f = 1` (so `f < n/3`) and threshold `2f + 1 = 3` we exhibit a reachable state of the
protocol model with two stage-1 certificates on different values in the broadcast of the corrupted
party `4` in view 1: honest parties `0, 1` deliver `true`, honest parties `2, 3` deliver `false`,
and party `4` signs both. (If party `4` is elected, continuing the same equivocation through
stages 2–4 lets `0, 1` decide `true` and `2, 3` decide `false`.) With the threshold `n - f = 4`
instead, `n + f < 2Q` holds and `Safety.lean` applies.
-/

namespace VABA.Counterexample

open Finset

/-- `n = 5` parties, `f = 1`, threshold `Q = 2f + 1 = 3`. -/
def C5 : Cfg (Fin 5) Bool where
  f := 1
  Q := 3
  valid := fun _ => True
  input := fun _ => true

lemma step_eq {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V} {c : ℕ → P}
    {a : Act P V} {s : Glob P V} (h : Enabled C a s) : step C c a s = eff c a s := by
  unfold step; simp [h]

lemma reach_eff {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V} (c : ℕ → P)
    {a : Act P V} {s : Glob P V} (hR : Reach C s) (h : Enabled C a s) : Reach C (eff c a s) := by
  rw [← step_eq (c := c) h]; exact Reach.step c a hR

/-- The coin sequence (irrelevant here). -/
def c0 : ℕ → Fin 5 := fun _ => 0

def s1 : Glob (Fin 5) Bool := eff c0 (.corrupt 4) (init C5)
def s2 : Glob (Fin 5) Bool := eff c0 (.byzSign 4 (.pb 1 4 1 true)) s1
def s3 : Glob (Fin 5) Bool := eff c0 (.byzSign 4 (.pb 1 4 1 false)) s2
def s4 : Glob (Fin 5) Bool := eff c0 (.deliver 0 4 1 true 0) s3
def s5 : Glob (Fin 5) Bool := eff c0 (.deliver 1 4 1 true 0) s4
def s6 : Glob (Fin 5) Bool := eff c0 (.deliver 2 4 1 false 0) s5
def s7 : Glob (Fin 5) Bool := eff c0 (.deliver 3 4 1 false 0) s6

lemma corrupt_s3 : s3.corrupt = {4} := by simp [s3, s2, s1, eff, init]

lemma reach_s7 : Reach C5 s7 := by
  have r1 : Reach C5 s1 := reach_eff c0 Reach.init (by simp [Enabled, init, C5])
  have r2 : Reach C5 s2 := reach_eff c0 r1 (by simp [Enabled, s1, eff, init])
  have r3 : Reach C5 s3 := reach_eff c0 r2 (by simp [Enabled, s2, s1, eff, init])
  have r4 : Reach C5 s4 := reach_eff c0 r3 (by
    simp [Enabled, Valid, SentBy, s3, s2, s1, eff, init, C5])
  have r5 : Reach C5 s5 := reach_eff c0 r4 (by
    simp [Enabled, Valid, SentBy, s4, s3, s2, s1, eff, init, C5])
  have r6 : Reach C5 s6 := reach_eff c0 r5 (by
    simp [Enabled, Valid, SentBy, s5, s4, s3, s2, s1, eff, init, C5])
  exact reach_eff c0 r6 (by
    simp [Enabled, Valid, SentBy, s6, s5, s4, s3, s2, s1, eff, init, C5])

lemma qc_of_subset {s : Glob (Fin 5) Bool} {st : Stmt (Fin 5) Bool} {A : Finset (Fin 5)}
    (hA : 3 ≤ A.card) (h : ∀ p ∈ A, s.tok p st) : QC C5.Q s st :=
  hA.trans (card_le_card (fun p hp => Cslib.Byzantine.mem_signers.mpr (h p hp)))

/-- **PB-provability fails for `n = 5`, `f = 1` with threshold `2f + 1`**: a reachable state with
two stage-1 certificates on different values in one broadcast instance. -/
theorem provability_fails :
    3 * C5.f < Fintype.card (Fin 5) ∧ C5.Q = 2 * C5.f + 1 ∧
    ∃ s, Reach C5 s ∧ QC C5.Q s (.pb 1 4 1 true) ∧ QC C5.Q s (.pb 1 4 1 false) := by
  refine ⟨by simp [C5], rfl, s7, reach_s7, ?_, ?_⟩
  · refine qc_of_subset (A := {0, 1, 4}) (by decide) ?_
    simp [s7, s6, s5, s4, s3, s2, s1, eff, init]
  · refine qc_of_subset (A := {2, 3, 4}) (by decide) ?_
    simp [s7, s6, s5, s4, s3, s2, s1, eff, init]

/-! ### Disagreement for `n = 5`, `f = 1`, threshold `2f + 1`

A full run (58 steps) in which honest parties `0` and `2` decide different values. Party `4` is
corrupted, is elected leader of view 1, and equivocates in all four stages of its broadcast
(`0, 1` deliver `true`, `2, 3` deliver `false`, and `4` signs both). The broadcasts of `0` and `1`
complete normally, so with `4`'s broadcast there are three completed broadcasts and the skip
certificate forms. -/

/-- The coin: party `4` leads every view. -/
def cc : ℕ → Fin 5 := fun _ => 4

lemma en_deliver1 {s : Glob (Fin 5) Bool} {p k : Fin 5} {v : Bool}
    (h1 : p ∉ s.corrupt) (h2 : (s.loc p).ph = .bc) (h3 : (s.loc p).d (s.loc p).view k 1 = none)
    (h4 : (s.loc p).lock = 0) (h5 : SentBy s k (s.loc p).view 1 v 0) :
    Enabled C5 (.deliver p k 1 v 0) s :=
  ⟨h1, h2, le_rfl, by norm_num, h3, by simp [Valid, C5, h4], h5⟩

lemma en_deliver {s : Glob (Fin 5) Bool} {p k : Fin 5} {st : ℕ} {v : Bool} {A : Finset (Fin 5)}
    (hA : 3 ≤ A.card) (hst : 2 ≤ st ∧ st ≤ 4) (h1 : p ∉ s.corrupt) (h2 : (s.loc p).ph = .bc)
    (hv : (s.loc p).view = 1) (h3 : (s.loc p).d 1 k st = none)
    (hq : ∀ q ∈ A, s.tok q (.pb 1 k (st - 1) v)) (h5 : SentBy s k 1 st v 0) :
    Enabled C5 (.deliver p k st v 0) s := by
  refine ⟨h1, h2, by omega, hst.2, by rw [hv]; exact h3, ?_, by rw [hv]; exact h5⟩
  have hne : st ≠ 1 := by omega
  simp only [Valid, hne, ite_false, hv]
  exact qc_of_subset hA hq

lemma en_skip {s : Glob (Fin 5) Bool} {p : Fin 5} (h1 : p ∉ s.corrupt)
    (h : ∀ k ∈ ({0, 1, 4} : Finset (Fin 5)), ∀ q ∈ ({0, 1, 4} : Finset (Fin 5)),
      s.tok q (.pb 1 k 4 true)) :
    Enabled C5 (.skipShare p 1) s := by
  refine ⟨h1, (show 3 ≤ ({0, 1, 4} : Finset (Fin 5)).card by decide).trans (card_le_card ?_)⟩
  intro k hk
  exact mem_completed.mpr ⟨true, qc_of_subset (A := {0, 1, 4}) (by decide) (h k hk)⟩

lemma en_invoke {s : Glob (Fin 5) Bool} {p : Fin 5} (h1 : p ∉ s.corrupt)
    (h2 : (s.loc p).ph = .bc) (hv : (s.loc p).view = 1)
    (h : ∀ q ∈ ({0, 1, 4} : Finset (Fin 5)), s.tok q (.skip 1)) :
    Enabled C5 (.invokeElect p) s :=
  ⟨h1, h2, by rw [hv]; exact qc_of_subset (by decide) h⟩

-- 58 steps
def t1 : Glob (Fin 5) Bool := eff cc (.corrupt 4) (init C5)
def t2 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 1 true)) t1
def t3 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 1 false)) t2
def t4 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 0 1 true)) t3
def t5 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 1 1 true)) t4
def t6 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 2 true)) t5
def t7 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 2 false)) t6
def t8 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 0 2 true)) t7
def t9 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 1 2 true)) t8
def t10 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 3 true)) t9
def t11 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 3 false)) t10
def t12 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 0 3 true)) t11
def t13 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 1 3 true)) t12
def t14 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 4 true)) t13
def t15 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 4 4 false)) t14
def t16 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 0 4 true)) t15
def t17 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.pb 1 1 4 true)) t16
def t18 : Glob (Fin 5) Bool := eff cc (.byzSign 4 (.skip 1)) t17
def t19 : Glob (Fin 5) Bool := eff cc (.deliver 0 4 1 true 0) t18
def t20 : Glob (Fin 5) Bool := eff cc (.deliver 1 4 1 true 0) t19
def t21 : Glob (Fin 5) Bool := eff cc (.deliver 2 4 1 false 0) t20
def t22 : Glob (Fin 5) Bool := eff cc (.deliver 3 4 1 false 0) t21
def t23 : Glob (Fin 5) Bool := eff cc (.deliver 0 0 1 true 0) t22
def t24 : Glob (Fin 5) Bool := eff cc (.deliver 1 0 1 true 0) t23
def t25 : Glob (Fin 5) Bool := eff cc (.deliver 0 1 1 true 0) t24
def t26 : Glob (Fin 5) Bool := eff cc (.deliver 1 1 1 true 0) t25
def t27 : Glob (Fin 5) Bool := eff cc (.deliver 0 4 2 true 0) t26
def t28 : Glob (Fin 5) Bool := eff cc (.deliver 1 4 2 true 0) t27
def t29 : Glob (Fin 5) Bool := eff cc (.deliver 2 4 2 false 0) t28
def t30 : Glob (Fin 5) Bool := eff cc (.deliver 3 4 2 false 0) t29
def t31 : Glob (Fin 5) Bool := eff cc (.deliver 0 0 2 true 0) t30
def t32 : Glob (Fin 5) Bool := eff cc (.deliver 1 0 2 true 0) t31
def t33 : Glob (Fin 5) Bool := eff cc (.deliver 0 1 2 true 0) t32
def t34 : Glob (Fin 5) Bool := eff cc (.deliver 1 1 2 true 0) t33
def t35 : Glob (Fin 5) Bool := eff cc (.deliver 0 4 3 true 0) t34
def t36 : Glob (Fin 5) Bool := eff cc (.deliver 1 4 3 true 0) t35
def t37 : Glob (Fin 5) Bool := eff cc (.deliver 2 4 3 false 0) t36
def t38 : Glob (Fin 5) Bool := eff cc (.deliver 3 4 3 false 0) t37
def t39 : Glob (Fin 5) Bool := eff cc (.deliver 0 0 3 true 0) t38
def t40 : Glob (Fin 5) Bool := eff cc (.deliver 1 0 3 true 0) t39
def t41 : Glob (Fin 5) Bool := eff cc (.deliver 0 1 3 true 0) t40
def t42 : Glob (Fin 5) Bool := eff cc (.deliver 1 1 3 true 0) t41
def t43 : Glob (Fin 5) Bool := eff cc (.deliver 0 4 4 true 0) t42
def t44 : Glob (Fin 5) Bool := eff cc (.deliver 1 4 4 true 0) t43
def t45 : Glob (Fin 5) Bool := eff cc (.deliver 2 4 4 false 0) t44
def t46 : Glob (Fin 5) Bool := eff cc (.deliver 3 4 4 false 0) t45
def t47 : Glob (Fin 5) Bool := eff cc (.deliver 0 0 4 true 0) t46
def t48 : Glob (Fin 5) Bool := eff cc (.deliver 1 0 4 true 0) t47
def t49 : Glob (Fin 5) Bool := eff cc (.deliver 0 1 4 true 0) t48
def t50 : Glob (Fin 5) Bool := eff cc (.deliver 1 1 4 true 0) t49
def t51 : Glob (Fin 5) Bool := eff cc (.skipShare 0 1) t50
def t52 : Glob (Fin 5) Bool := eff cc (.skipShare 1 1) t51
def t53 : Glob (Fin 5) Bool := eff cc (.invokeElect 0) t52
def t54 : Glob (Fin 5) Bool := eff cc (.electReturn 0) t53
def t55 : Glob (Fin 5) Bool := eff cc (.invokeElect 2) t54
def t56 : Glob (Fin 5) Bool := eff cc (.electReturn 2) t55
def t57 : Glob (Fin 5) Bool := eff cc (.recvVC 0 0 1 true) t56
def t58 : Glob (Fin 5) Bool := eff cc (.recvVC 2 2 1 true) t57

attribute [local simp] t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26 t27 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48 t49 t50 t51 t52 t53 t54 t55 t56 t57 t58 eff init

set_option maxHeartbeats 4000000 in
lemma reach_final : Reach C5 t58 := by
  have r0 : Reach C5 (init C5) := Reach.init
  have r1 : Reach C5 t1 := reach_eff cc r0 (by simp [Enabled, C5])
  have r2 : Reach C5 t2 := reach_eff cc r1 (by simp [Enabled, C5])
  have r3 : Reach C5 t3 := reach_eff cc r2 (by simp [Enabled, C5])
  have r4 : Reach C5 t4 := reach_eff cc r3 (by simp [Enabled, C5])
  have r5 : Reach C5 t5 := reach_eff cc r4 (by simp [Enabled, C5])
  have r6 : Reach C5 t6 := reach_eff cc r5 (by simp [Enabled, C5])
  have r7 : Reach C5 t7 := reach_eff cc r6 (by simp [Enabled, C5])
  have r8 : Reach C5 t8 := reach_eff cc r7 (by simp [Enabled, C5])
  have r9 : Reach C5 t9 := reach_eff cc r8 (by simp [Enabled, C5])
  have r10 : Reach C5 t10 := reach_eff cc r9 (by simp [Enabled, C5])
  have r11 : Reach C5 t11 := reach_eff cc r10 (by simp [Enabled, C5])
  have r12 : Reach C5 t12 := reach_eff cc r11 (by simp [Enabled, C5])
  have r13 : Reach C5 t13 := reach_eff cc r12 (by simp [Enabled, C5])
  have r14 : Reach C5 t14 := reach_eff cc r13 (by simp [Enabled, C5])
  have r15 : Reach C5 t15 := reach_eff cc r14 (by simp [Enabled, C5])
  have r16 : Reach C5 t16 := reach_eff cc r15 (by simp [Enabled, C5])
  have r17 : Reach C5 t17 := reach_eff cc r16 (by simp [Enabled, C5])
  have r18 : Reach C5 t18 := reach_eff cc r17 (by simp [Enabled, C5])
  have r19 : Reach C5 t19 := reach_eff cc r18 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r20 : Reach C5 t20 := reach_eff cc r19 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r21 : Reach C5 t21 := reach_eff cc r20 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r22 : Reach C5 t22 := reach_eff cc r21 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r23 : Reach C5 t23 := reach_eff cc r22 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r24 : Reach C5 t24 := reach_eff cc r23 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r25 : Reach C5 t25 := reach_eff cc r24 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r26 : Reach C5 t26 := reach_eff cc r25 (en_deliver1 (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r27 : Reach C5 t27 := reach_eff cc r26 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r28 : Reach C5 t28 := reach_eff cc r27 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r29 : Reach C5 t29 := reach_eff cc r28 (en_deliver (A := {2, 3, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r30 : Reach C5 t30 := reach_eff cc r29 (en_deliver (A := {2, 3, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r31 : Reach C5 t31 := reach_eff cc r30 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r32 : Reach C5 t32 := reach_eff cc r31 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r33 : Reach C5 t33 := reach_eff cc r32 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r34 : Reach C5 t34 := reach_eff cc r33 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r35 : Reach C5 t35 := reach_eff cc r34 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r36 : Reach C5 t36 := reach_eff cc r35 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r37 : Reach C5 t37 := reach_eff cc r36 (en_deliver (A := {2, 3, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r38 : Reach C5 t38 := reach_eff cc r37 (en_deliver (A := {2, 3, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r39 : Reach C5 t39 := reach_eff cc r38 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r40 : Reach C5 t40 := reach_eff cc r39 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r41 : Reach C5 t41 := reach_eff cc r40 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r42 : Reach C5 t42 := reach_eff cc r41 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r43 : Reach C5 t43 := reach_eff cc r42 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r44 : Reach C5 t44 := reach_eff cc r43 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r45 : Reach C5 t45 := reach_eff cc r44 (en_deliver (A := {2, 3, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r46 : Reach C5 t46 := reach_eff cc r45 (en_deliver (A := {2, 3, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r47 : Reach C5 t47 := reach_eff cc r46 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r48 : Reach C5 t48 := reach_eff cc r47 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r49 : Reach C5 t49 := reach_eff cc r48 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r50 : Reach C5 t50 := reach_eff cc r49 (en_deliver (A := {0, 1, 4}) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [SentBy, C5]))
  have r51 : Reach C5 t51 := reach_eff cc r50 (en_skip (by simp) (by simp))
  have r52 : Reach C5 t52 := reach_eff cc r51 (en_skip (by simp) (by simp))
  have r53 : Reach C5 t53 := reach_eff cc r52 (en_invoke (by simp) (by simp) (by simp) (by simp))
  have r54 : Reach C5 t54 := reach_eff cc r53 (by simp [Enabled])
  have r55 : Reach C5 t55 := reach_eff cc r54 (en_invoke (by simp) (by simp) (by simp) (by simp))
  have r56 : Reach C5 t56 := reach_eff cc r55 (by simp [Enabled])
  have r57 : Reach C5 t57 := reach_eff cc r56 (by simp [Enabled, Past])
  have r58 : Reach C5 t58 := reach_eff cc r57 (by simp [Enabled, Past])
  exact r58

/-- **Disagreement with `n = 5`, `f = 1` and threshold `2f + 1 = 3`**: in a reachable state the
honest parties `0` and `2` have decided `true` and `false`. -/
theorem agreement_fails :
    3 * C5.f < Fintype.card (Fin 5) ∧ C5.Q = 2 * C5.f + 1 ∧
    ∃ s, Reach C5 s ∧ (0 : Fin 5) ∉ s.corrupt ∧ (2 : Fin 5) ∉ s.corrupt ∧
      true ∈ (s.loc 0).decs ∧ false ∈ (s.loc 2).decs := by
  refine ⟨by simp [C5], rfl, t58, reach_final, by simp, by simp, ?_, ?_⟩ <;>
    simp [procVC, proc, cc]

end VABA.Counterexample
