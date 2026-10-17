import Papers.PODC2020.BezoutElection.Alg2AbsLead
import Podc.Foundations.Data.Nat.Descent
import Podc.Computability.Distributed.SharedMemory.Progress

/-!
# Algorithm 2: abstract runs of one register

An *abstract run* of a register is a sequence of per-register abstract states `A t` in which, at
every time `t`, only the process `who t` acts on the register, by one transition `tr t`: nothing,
a read, the processing of its copy, a read immediately followed by the processing of the copy
(the last read of a collect), or a write. The liveness of a competition is proved on abstract
runs (`Alg2ALive*.lean`); concrete fair executions give abstract runs (`Alg2ASim.lean`).
-/

set_option linter.unusedSectionVars false

namespace BezoutElection.Alg2

open AState

variable {Id : Type} [DecidableEq Id] {P : Type} [DecidableEq P] [Fintype P]
  {n U : ℕ} {ids : P → Id}

/-- The transitions of one process at one register. -/
inductive ATr
  | none
  | read
  | proc (ok fin : Bool)
  | readProc (ok fin : Bool)
  | write

/-- The effect of a transition of `j`. -/
def ATrRel (n U : ℕ) (ids : P → Id) (A : AState Id P) (j : P) : ATr → AState Id P → Prop
  | .none, A' => A' = A
  | .read, A' => (A.loc j).st = .fresh ∧ A' = A.setSt j (.copy A.reg)
  | .proc ok fin, A' => ∃ v, (A.loc j).st = .copy v ∧
      A' = A.upd j (procL n U (ids j) (A.loc j) v ok fin)
  | .readProc ok fin, A' => (A.loc j).st = .fresh ∧
      A' = A.upd j (procL n U (ids j) (A.loc j) A.reg ok fin)
  | .write, A' => ∃ w, (A.loc j).st = .pend w ∧ A' = A.wr j w

lemma procL_st (me : Id) (l : ALoc Id) (a : AStatus Id) (r : Reg Id) (ok fin : Bool) :
    procL n U me { l with st := a } r ok fin = procL n U me l r ok fin := by
  unfold procL procX
  split_ifs <;> rfl

lemma astep_read' {A : AState Id P} {j : P} (h : (A.loc j).st = .fresh) :
    AStep n U ids A (A.setSt j (.copy A.reg)) := AStep.read A j h

lemma astep_proc' {A : AState Id P} {j : P} {v : Reg Id} (ok fin : Bool)
    (h : (A.loc j).st = .copy v) :
    AStep n U ids A (A.upd j (procL n U (ids j) (A.loc j) v ok fin)) := AStep.proc A j v ok fin h

lemma astep_write' {A : AState Id P} {j : P} {w : Reg Id} (h : (A.loc j).st = .pend w) :
    AStep n U ids A (A.wr j w) := AStep.write A j w h

lemma setSt_upd_procL (A : AState Id P) (j : P) (r : Reg Id) (ok fin : Bool) :
    (A.setSt j (.copy r)).upd j (procL n U (ids j) ((A.setSt j (.copy r)).loc j) r ok fin) =
      A.upd j (procL n U (ids j) (A.loc j) r ok fin) := by
  simp only [setSt, upd, Function.update_idem, Function.update_self]
  rw [procL_st]

/-- An abstract run of a register. -/
structure ARun (n U : ℕ) (ids : P → Id) where
  A : ℕ → AState Id P
  who : ℕ → P
  tr : ℕ → ATr
  step : ∀ t, ATrRel n U ids (A t) (who t) (tr t) (A (t + 1))
  inv : ∀ t, AInv n U ids (A t)

namespace ARun

variable (R : ARun n U ids)

lemma other {t : ℕ} {q : P} (h : q ≠ R.who t) : (R.A (t + 1)).loc q = (R.A t).loc q := by
  have hs := R.step t
  generalize R.tr t = tr at hs
  cases tr with
  | none => rw [hs]
  | read => rw [hs.2]; simp [setSt, upd_loc_ne _ _ h]
  | proc ok fin => obtain ⟨v, -, hs⟩ := hs; rw [hs, upd_loc_ne _ _ h]
  | readProc ok fin => rw [hs.2, upd_loc_ne _ _ h]
  | write => obtain ⟨w, -, hs⟩ := hs; rw [hs]; simp [wr, setSt, upd_loc_ne _ _ h]

lemma other_iter {t k : ℕ} {q : P} (h : ∀ j < k, R.who (t + j) ≠ q ∨ R.tr (t + j) = .none) :
    (R.A (t + k)).loc q = (R.A t).loc q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih (fun j hj => h j (by omega)), ← Nat.add_assoc]
    rcases h k (by omega) with h1 | h1
    · exact R.other (Ne.symm h1)
    · have hs := R.step (t + k); rw [h1] at hs; rw [hs]

/-- The register changes only by writes. -/
lemma reg_step (t : ℕ) : (R.A (t + 1)).reg = (R.A t).reg ∨
    (R.tr t = .write ∧ ∃ w, ((R.A t).loc (R.who t)).st = .pend w ∧ (R.A (t + 1)).reg = w) := by
  have hs := R.step t
  generalize hg : R.tr t = tr at hs
  cases tr with
  | none => left; rw [hs]
  | read => left; rw [hs.2]; rfl
  | proc ok fin => obtain ⟨v, -, hs⟩ := hs; left; rw [hs]; rfl
  | readProc ok fin => left; rw [hs.2]; rfl
  | write => obtain ⟨w, h1, hs⟩ := hs; right; exact ⟨rfl, w, h1, by rw [hs]; rfl⟩

lemma reg_write {t : ℕ} (h : R.tr t = .write) :
    ∃ w, ((R.A t).loc (R.who t)).st = .pend w ∧ (R.A (t + 1)).reg = w := by
  rcases R.reg_step t with h1 | ⟨-, h2⟩
  · have hs := R.step t
    rw [h] at hs
    obtain ⟨w, h3, h4⟩ := hs
    exact ⟨w, h3, by rw [h4]; rfl⟩
  · exact h2

/-- A transition is a sequence of abstract steps. -/
lemma steps (t : ℕ) : Relation.ReflTransGen (AStep n U ids) (R.A t) (R.A (t + 1)) := by
  have hs := R.step t
  generalize R.tr t = tr at hs
  cases tr with
  | none => rw [hs]
  | read =>
    rw [hs.2]; exact Relation.ReflTransGen.single (AStep.read _ _ hs.1)
  | proc ok fin =>
    obtain ⟨v, h1, hs⟩ := hs; rw [hs]
    exact Relation.ReflTransGen.single (astep_proc' ok fin h1)
  | readProc ok fin =>
    rw [hs.2]
    have h1 := astep_read' (n := n) (U := U) (ids := ids) hs.1
    have h2 := astep_proc' (n := n) (U := U) (ids := ids) (A := (R.A t).setSt (R.who t)
      (.copy (R.A t).reg)) (j := R.who t) (v := (R.A t).reg) ok fin (by simp)
    rw [setSt_upd_procL] at h2
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2
  | write =>
    obtain ⟨w, h1, hs⟩ := hs; rw [hs]
    exact Relation.ReflTransGen.single (astep_write' h1)

/-- The leader of a competition stays the leader as long as the level does not change. -/
lemma lead_next (hid : Function.Injective ids) (hn : Fintype.card P = n) {t : ℕ} {ℓ : P}
    (E : Lead n ids (R.A t) ℓ) (hlev : (R.A (t + 1)).reg.level = (R.A t).reg.level) :
    Lead n ids (R.A (t + 1)) ℓ := by
  have hs := R.step t
  generalize R.tr t = tr at hs
  cases tr with
  | none => rw [hs]; exact E
  | read => rw [hs.2]; rw [hs.2] at hlev; exact lead_step hid hn (R.inv t) E (astep_read' hs.1) hlev
  | proc ok fin =>
    obtain ⟨v, h1, hs⟩ := hs; rw [hs]; rw [hs] at hlev
    exact lead_step hid hn (R.inv t) E (astep_proc' ok fin h1) hlev
  | readProc ok fin =>
    rw [hs.2]
    have h1 := astep_read' (n := n) (U := U) (ids := ids) hs.1
    have h2 := astep_proc' (n := n) (U := U) (ids := ids) (A := (R.A t).setSt (R.who t)
      (.copy (R.A t).reg)) (j := R.who t) (v := (R.A t).reg) ok fin (by simp)
    rw [setSt_upd_procL] at h2
    have E1 := lead_step hid hn (R.inv t) E h1 (by simp)
    exact lead_step hid hn (ainv_step hid hn (R.inv t) h1) E1 h2 (by simp [upd])
  | write =>
    obtain ⟨w, h1, hs⟩ := hs; rw [hs]; rw [hs] at hlev
    exact lead_step hid hn (R.inv t) E (astep_write' h1) hlev

/-- The next action of `q` at the register. -/
lemma next_act (q : P) (t : ℕ)
    (hfair : ∀ t, ∃ t' ≥ t, R.who t' = q ∧ R.tr t' ≠ .none) :
    ∃ t' ≥ t, (R.A t').loc q = (R.A t).loc q ∧ R.who t' = q ∧ R.tr t' ≠ .none := by
  classical
  have hex : ∃ k, R.who (t + k) = q ∧ R.tr (t + k) ≠ .none := by
    obtain ⟨t', ht', h⟩ := hfair t
    exact ⟨t' - t, by rw [Nat.add_sub_cancel' ht']; exact h⟩
  refine ⟨t + Nat.find hex, by omega, ?_, Nat.find_spec hex⟩
  apply R.other_iter
  intro j hj
  have := Nat.find_min hex hj
  by_cases h1 : R.who (t + j) = q
  · right; by_contra h2; exact this ⟨h1, h2⟩
  · left; exact h1

lemma act_copy {t : ℕ} {q : P} {v : Reg Id} (hc : ((R.A t).loc q).st = .copy v)
    (hw : R.who t = q) (ha : R.tr t ≠ .none) :
    ∃ ok fin, R.tr t = .proc ok fin ∧
      R.A (t + 1) = (R.A t).upd q (procL n U (ids q) ((R.A t).loc q) v ok fin) := by
  have hs := R.step t
  subst hw
  generalize hg : R.tr t = tr at hs ha
  cases tr with
  | none => exact absurd rfl ha
  | read => have h1 := hs.1; rw [hc] at h1; cases h1
  | proc ok fin =>
    obtain ⟨v', h1, hs⟩ := hs; rw [hc] at h1; cases h1; exact ⟨ok, fin, rfl, hs⟩
  | readProc ok fin => have h1 := hs.1; rw [hc] at h1; cases h1
  | write => obtain ⟨w, h1, -⟩ := hs; rw [hc] at h1; cases h1

lemma act_pend {t : ℕ} {q : P} {w : Reg Id} (hc : ((R.A t).loc q).st = .pend w)
    (hw : R.who t = q) (ha : R.tr t ≠ .none) :
    R.tr t = .write ∧ R.A (t + 1) = (R.A t).wr q w := by
  have hs := R.step t
  subst hw
  generalize hg : R.tr t = tr at hs ha
  cases tr with
  | none => exact absurd rfl ha
  | read => have h1 := hs.1; rw [hc] at h1; cases h1
  | proc ok fin => obtain ⟨v', h1, -⟩ := hs; rw [hc] at h1; cases h1
  | readProc ok fin => have h1 := hs.1; rw [hc] at h1; cases h1
  | write => obtain ⟨w', h1, hs⟩ := hs; rw [hc] at h1; cases h1; exact ⟨rfl, hs⟩

lemma act_fresh {t : ℕ} {q : P} (hc : ((R.A t).loc q).st = .fresh)
    (hw : R.who t = q) (ha : R.tr t ≠ .none) :
    (R.tr t = .read ∧ R.A (t + 1) = (R.A t).setSt q (.copy (R.A t).reg)) ∨
    (∃ ok fin, R.tr t = .readProc ok fin ∧
      R.A (t + 1) = (R.A t).upd q (procL n U (ids q) ((R.A t).loc q) (R.A t).reg ok fin)) := by
  have hs := R.step t
  subst hw
  generalize hg : R.tr t = tr at hs ha
  cases tr with
  | none => exact absurd rfl ha
  | read => exact Or.inl ⟨rfl, hs.2⟩
  | proc ok fin => obtain ⟨v', h1, -⟩ := hs; rw [hc] at h1; cases h1
  | readProc ok fin => exact Or.inr ⟨ok, fin, rfl, hs.2⟩
  | write => obtain ⟨w', h1, -⟩ := hs; rw [hc] at h1; cases h1

end ARun

/-- Hypotheses for the liveness of the current competition of a register: its level `L < U`
never changes (no write of line N(11) is ever pending) and every process keeps reading the
register. -/
structure LCtx0 (R : ARun n U ids) where
  hid : Function.Injective ids
  hn : Fintype.card P = n
  L : ℕ
  hLU : L < U
  lev : ∀ t, (R.A t).reg.level = L
  nowin : ∀ t q w, ((R.A t).loc q).st = .pend w → w.level = L
  fair : ∀ q t, ∃ t' ≥ t, R.who t' = q ∧ (R.tr t' = .read ∨ ∃ ok fin, R.tr t' = .readProc ok fin)

/-- Moreover, from time `T` on every process processes its copies with fixed values `okc`, `fc`
of the global part of the candidacy predicate and of `finishing`, and candidates are eligible. -/
structure LCtx (R : ARun n U ids) extends LCtx0 R where
  T : ℕ
  okc : P → Bool
  fc : P → Bool
  stab : ∀ t ≥ T, ∀ ok fin, (R.tr t = .proc ok fin ∨ R.tr t = .readProc ok fin) →
    ok = okc (R.who t) ∧ fin = fc (R.who t)
  caok : ∀ t ≥ T, ∀ q, ((R.A t).loc q).ca = true → okc q = true

namespace LCtx0

variable {R : ARun n U ids} (X : LCtx0 R)
include X

lemma fair_act (q : P) (t : ℕ) : ∃ t' ≥ t, R.who t' = q ∧ R.tr t' ≠ .none := by
  obtain ⟨t', ht', h1, h2⟩ := X.fair q t
  refine ⟨t', ht', h1, ?_⟩
  rcases h2 with h2 | ⟨ok, fin, h2⟩ <;> rw [h2] <;> exact fun h => by cases h

lemma next_act (q : P) (t : ℕ) :
    ∃ t' ≥ t, (R.A t').loc q = (R.A t).loc q ∧ R.who t' = q ∧ R.tr t' ≠ .none :=
  R.next_act q t (X.fair_act q)

lemma next_write {t : ℕ} {q : P} {w : Reg Id} (hc : ((R.A t).loc q).st = .pend w) :
    ∃ t' ≥ t, (R.A t').loc q = (R.A t).loc q ∧ R.who t' = q ∧ R.tr t' = .write ∧
      R.A (t' + 1) = (R.A t').wr q w := by
  obtain ⟨t', ht', hl, hw, ha⟩ := X.next_act q t
  obtain ⟨h1, h2⟩ := R.act_pend (by rw [hl]; exact hc) hw ha
  exact ⟨t', ht', hl, hw, h1, h2⟩

end LCtx0

namespace LCtx

variable {R : ARun n U ids} (X : LCtx R)
include X

/-- The next processing of a copy (from time `T` on, with the stable `okc`, `fc`). -/
lemma next_proc {t : ℕ} (ht : X.T ≤ t) {q : P} {v : Reg Id} (hc : ((R.A t).loc q).st = .copy v) :
    ∃ t' ≥ t, (R.A t').loc q = (R.A t).loc q ∧ R.who t' = q ∧
      R.A (t' + 1) = (R.A t').upd q (procL n U (ids q) ((R.A t).loc q) v (X.okc q) (X.fc q)) := by
  obtain ⟨t', ht', hl, hw, ha⟩ := X.next_act q t
  obtain ⟨ok, fin, h1, h2⟩ := R.act_copy (by rw [hl]; exact hc) hw ha
  obtain ⟨rfl, rfl⟩ := X.stab t' (by omega) ok fin (Or.inl h1)
  rw [hw] at h2
  exact ⟨t', ht', hl, hw, by rw [h2, hl]⟩

/-- The next read (possibly immediately followed by the processing of the copy). -/
lemma next_read {t : ℕ} (ht : X.T ≤ t) {q : P} (hc : ((R.A t).loc q).st = .fresh) :
    ∃ t' ≥ t, (R.A t').loc q = (R.A t).loc q ∧ R.who t' = q ∧
      (R.A (t' + 1) = (R.A t').setSt q (.copy (R.A t').reg) ∨
       R.A (t' + 1) = (R.A t').upd q
        (procL n U (ids q) ((R.A t).loc q) (R.A t').reg (X.okc q) (X.fc q))) := by
  obtain ⟨t', ht', hl, hw, ha⟩ := X.next_act q t
  rcases R.act_fresh (by rw [hl]; exact hc) hw ha with ⟨-, h2⟩ | ⟨ok, fin, h1, h2⟩
  · exact ⟨t', ht', hl, hw, Or.inl (by rw [h2])⟩
  · obtain ⟨rfl, rfl⟩ := X.stab t' (by omega) ok fin (Or.inr h1)
    rw [hw] at h2
    exact ⟨t', ht', hl, hw, Or.inr (by rw [h2, hl])⟩

end LCtx

end BezoutElection.Alg2
