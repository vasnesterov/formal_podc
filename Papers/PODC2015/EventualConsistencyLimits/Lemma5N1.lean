import Papers.PODC2015.EventualConsistencyLimits.Lemma5

/-!
# Lemma 5 fails with a single replica

Lemma 5 of [AEM15] does not assume that there are at least two replicas. With a single replica
nothing ever needs to be sent: the store `D1` below (one replica, which keeps the last value
written to each object and never sends anything) is eventually consistent, has invisible reads
and op-driven messages, is highly available, and after the first write the replica has no
message pending — contradicting the conclusion of Lemma 5 (all other hypotheses of Lemma 5 are
vacuous for the empty prefix `α = []`). This is why `lemma5` assumes a second replica `R' ≠ R`.
-/

namespace Podc.EventualConsistencyLimits

variable {Obj V : Type*}

namespace OneReplica

open scoped Classical in
/-- One replica, messages `Unit`; the state is the last value written to each object. Writes
return `ok`, reads return the last value written (or `∅`), nothing is ever sent, receipts do
not change the state. -/
noncomputable def D1 : Store Unit Obj V Unit (Obj → Option V) where
  init _ := fun _ => none
  step _ σ e := match e with
    | .do_ ⟨o, .write v, .ok⟩ => some (Function.update σ o (some v))
    | .do_ ⟨_, .write _, .vals _⟩ => none
    | .do_ ⟨o, .read, .vals S⟩ => if S = {v | σ o = some v} then some σ else none
    | .do_ ⟨_, .read, .ok⟩ => none
    | .send _ => none
    | .recv _ => some σ

lemma step_send (σ : Obj → Option V) (m : Unit) :
    (D1 : Store Unit Obj V Unit _).step () σ (.send m) = none := rfl

lemma not_pending (σ : Obj → Option V) : ¬ (D1 : Store Unit Obj V Unit _).Pending () σ := by
  rintro ⟨m, σ', h⟩
  simp [step_send] at h

/-- Inversion for the last step of an execution. -/
lemma isExec_snoc_inv {ι Obj V M St : Type*} [DecidableEq ι] {D : Store ι Obj V M St}
    {α : List (ι × Ev Obj V M)} {x : ι × Ev Obj V M} (h : D.IsExec (α ++ [x])) :
    ∃ σ σ', D.state x.1 α = some σ ∧ D.step x.1 σ x.2 = some σ' ∧
      ∀ m, x.2 = .recv m → ∃ j, j ≠ x.1 ∧ (j, .send m) ∈ α := by
  generalize hβ : α ++ [x] = β at h
  cases h with
  | nil => simp at hβ
  | @snoc α' i e σ σ' _ h2 h3 h4 =>
    obtain ⟨rfl, h⟩ := List.append_inj' hβ rfl
    simp only [List.cons.injEq, and_true] at h
    subst h
    exact ⟨σ, σ', h2, h3, h4⟩

/-- In an infinite execution of `D1` every event is a client operation. -/
lemma isDo {s : ℕ → Unit × Ev Obj V Unit} (hs : (D1 : Store Unit Obj V Unit _).IsInfExec s)
    (p : ℕ) : ∃ d, (s p).2 = .do_ d := by
  have h := hs (p + 1)
  rw [Store.pre_succ] at h
  obtain ⟨σ, σ', -, hst, hr⟩ := isExec_snoc_inv h
  rcases hsp : (s p).2 with d | m | m
  · exact ⟨d, rfl⟩
  · rw [hsp] at hst; simp [D1] at hst
  · obtain ⟨j, hj, -⟩ := hr m hsp
    exact absurd rfl hj

section Last

variable (ev : ℕ → DoEv Obj V)

/-- The writes to `o` among the first `p` operations. -/
def W (p : ℕ) (o : Obj) : Set ℕ := {a | a < p ∧ (ev a).obj = o ∧ ∃ v, (ev a).op = .write v}

/-- `v` is the value of the last write to `o` among the first `p` operations. -/
def Last (p : ℕ) (o : Obj) (v : V) : Prop :=
  ∃ a ∈ W ev p o, (ev a).op = .write v ∧ ∀ b ∈ W ev p o, ¬ a < b

lemma last_zero (o : Obj) (v : V) : ¬ Last ev 0 o v := by
  rintro ⟨a, ⟨ha, -⟩, -⟩; omega

lemma last_succ_write {p : ℕ} {o : Obj} {u v : V} (hp : (ev p).obj = o)
    (hw : (ev p).op = .write u) : Last ev (p + 1) o v ↔ v = u := by
  constructor
  · rintro ⟨a, ⟨ha, hoa, -⟩, hav, hmax⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | rfl
    · exact absurd h (hmax p ⟨by omega, hp, u, hw⟩)
    · rw [hw] at hav; cases hav; rfl
  · rintro rfl
    refine ⟨p, ⟨by omega, hp, v, hw⟩, hw, fun b hb => by have := hb.1; omega⟩

lemma last_succ_other {p : ℕ} {o : Obj} (v : V)
    (hp : ¬ ((ev p).obj = o ∧ ∃ u, (ev p).op = .write u)) :
    Last ev (p + 1) o v ↔ Last ev p o v := by
  constructor
  · rintro ⟨a, ⟨ha, hoa, hwa⟩, hav, hmax⟩
    have hap : a ≠ p := by rintro rfl; exact hp ⟨hoa, hwa⟩
    refine ⟨a, ⟨by omega, hoa, hwa⟩, hav, fun b ⟨hb, hob, hwb⟩ => hmax b ⟨by omega, hob, hwb⟩⟩
  · rintro ⟨a, ⟨ha, hoa, hwa⟩, hav, hmax⟩
    refine ⟨a, ⟨by omega, hoa, hwa⟩, hav, fun b ⟨hb, hob, hwb⟩ => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | rfl
    · exact hmax b ⟨h, hob, hwb⟩
    · exact absurd ⟨hob, hwb⟩ hp

end Last

/-- The abstract execution of an infinite execution of `D1`: all events, in execution order,
each one seeing all earlier ones. -/
def ae (ev : ℕ → DoEv Obj V) : AE Unit Obj V where
  dom _ := True
  rep _ := ()
  ev := ev
  ord a b := a < b
  vis a b := a < b

lemma ae_wf (ev : ℕ → DoEv Obj V) : (ae ev).WF where
  ord_dom _ := ⟨trivial, trivial⟩
  ord_irrefl a := lt_irrefl a
  ord_trans h h' := lt_trans h h'
  ord_total _ _ h := lt_or_gt_of_ne h
  ord_fin b := Set.finite_lt_nat b
  vis_ord h := h
  vis_sess h _ := h
  vis_mono h h' _ := lt_trans h h'

lemma ae_ec (ev : ℕ → DoEv Obj V) : (ae ev).EC := by
  intro e _
  apply (Set.finite_le_nat e).subset
  rintro e' ⟨-, -, h⟩
  exact not_lt.1 h

lemma ae_ctxW (ev : ℕ → DoEv Obj V) (p : ℕ) : (ae ev).ctxW p = W ev p (ev p).obj := by
  ext a
  simp [AE.ctxW, AE.IsWrite, W, ae]

/-- The state invariant: after `p` events the state maps `o` to the last value written to `o`. -/
lemma state_pre {s : ℕ → Unit × Ev Obj V Unit} (hs : (D1 : Store Unit Obj V Unit _).IsInfExec s)
    {ev : ℕ → DoEv Obj V} (hev : ∀ p, (s p).2 = .do_ (ev p)) (p : ℕ) :
    ∃ σ, (D1 : Store Unit Obj V Unit _).state () (Store.pre s p) = some σ ∧
      ∀ o v, σ o = some v ↔ Last ev p o v := by
  classical
  induction p with
  | zero => exact ⟨fun _ => none, rfl, fun o v => by simp [last_zero]⟩
  | succ p ih =>
    obtain ⟨σ, hσ, hinv⟩ := ih
    have h := hs (p + 1)
    rw [Store.pre_succ] at h ⊢
    obtain ⟨σ₀, σ', h0, hst, -⟩ := isExec_snoc_inv h
    rw [hσ] at h0; cases h0
    rw [Store.state_snoc_self _ hσ, hst]
    refine ⟨σ', rfl, ?_⟩
    rw [hev p] at hst
    rcases hevp : ev p with ⟨o', op, r⟩
    rw [hevp] at hst
    cases op with
    | write u =>
      cases r with
      | vals S => simp [D1] at hst
      | ok =>
        simp only [D1, Option.some.injEq] at hst
        subst hst
        intro o v
        by_cases ho : o = o'
        · subst ho
          rw [last_succ_write ev (by rw [hevp]) (by rw [hevp])]
          simp [eq_comm]
        · rw [last_succ_other ev v (by rw [hevp]; exact fun h => ho h.1.symm),
            Function.update_of_ne ho, hinv]
    | read =>
      cases r with
      | ok => simp [D1] at hst
      | vals S =>
        simp only [D1] at hst
        split_ifs at hst
        cases hst
        intro o v
        rw [last_succ_other ev v (by rw [hevp]; rintro ⟨-, u, hu⟩; cases hu), hinv]

theorem eventuallyConsistent :
    (D1 : Store Unit Obj V Unit _).EventuallyConsistent (fun _ => True) := by
  intro s hs _
  choose ev hev using isDo hs
  refine ⟨ae ev, ⟨fun p => ?_, fun p i d hp => ?_, fun p q _ _ _ h => h⟩, ae_wf ev, ?_,
    ae_ec ev, trivial⟩
  · simp only [ae, Option.some.injEq, true_iff]
    exact ⟨(s p).1, ev p, by rw [← hev p]⟩
  · simp only [Option.some.injEq] at hp
    refine ⟨rfl, ?_⟩
    have := hev p
    rw [hp] at this
    cases this
    rfl
  · intro p _
    obtain ⟨σ, hσ, hinv⟩ := state_pre hs hev p
    have h := hs (p + 1)
    rw [Store.pre_succ] at h
    obtain ⟨σ₀, σ', h0, hst, -⟩ := isExec_snoc_inv h
    rw [hσ] at h0; cases h0
    rw [hev p] at hst
    show (ev p).rv = (ae ev).mvr p
    rcases hevp : ev p with ⟨o', op, r⟩
    rw [hevp] at hst
    cases op with
    | write u =>
      cases r with
      | vals S => simp [D1] at hst
      | ok => simp [AE.mvr, ae, hevp]
    | read =>
      cases r with
      | ok => simp [D1] at hst
      | vals S =>
        simp only [D1] at hst
        split_ifs at hst with hS
        rw [AE.mvr_of_read (by simp [ae, hevp]), ae_ctxW]
        simp only [hevp, hS]
        congr 1
        ext v
        exact hinv o' v

theorem invisibleReads : (D1 : Store Unit Obj V Unit _).InvisibleReads := by
  intro i σ o r σ' h
  cases r with
  | ok => simp [D1] at h
  | vals S =>
    simp only [D1] at h
    split_ifs at h
    exact (Option.some.inj h).symm

theorem opDriven : (D1 : Store Unit Obj V Unit _).OpDriven :=
  ⟨fun _ => not_pending _, fun _ _ _ σ' _ _ => not_pending σ'⟩

open scoped Classical in
theorem available : (D1 : Store Unit Obj V Unit _).Available := by
  intro i σ o op
  cases op with
  | write v => exact ⟨.ok, _, rfl⟩
  | read => exact ⟨.vals {v | σ o = some v}, σ, by simp [D1]⟩

theorem recvEnabled : (D1 : Store Unit Obj V Unit _).RecvEnabled :=
  fun _ σ _ => ⟨σ, rfl⟩

theorem sendClears : (D1 : Store Unit Obj V Unit _).SendClears :=
  fun _ _ _ σ' _ => not_pending σ'

end OneReplica

open OneReplica

/-- **Lemma 5 of [AEM15] is false with a single replica.** Lemma 5 of [AEM15] does not assume
`n ≥ 2`; with one replica nothing ever needs to be sent. The one-replica store `D1` is
eventually consistent, has invisible reads and op-driven messages, is highly available, enables
receipts, and sends clear pending messages; yet after the first write `w = do(o, write v, ok)`
(the execution `[w]`, whose prefix `α = []` trivially satisfies all the other hypotheses of
Lemma 5) the replica has no message pending. -/
theorem lemma5_false_one_replica (o : Obj) (v : V) :
    (D1 : Store Unit Obj V Unit _).EventuallyConsistent (fun _ => True) ∧
    (D1 : Store Unit Obj V Unit _).InvisibleReads ∧
    (D1 : Store Unit Obj V Unit _).OpDriven ∧
    (D1 : Store Unit Obj V Unit _).Available ∧
    (D1 : Store Unit Obj V Unit _).RecvEnabled ∧
    (D1 : Store Unit Obj V Unit _).SendClears ∧
    (D1 : Store Unit Obj V Unit _).IsExec [((), .do_ ⟨o, .write v, .ok⟩)] ∧
    ∃ σw, (D1 : Store Unit Obj V Unit _).step () ((D1 : Store Unit Obj V Unit _).init ())
        (.do_ ⟨o, .write v, .ok⟩) = some σw ∧
      (D1 : Store Unit Obj V Unit _).state () [((), .do_ ⟨o, .write v, .ok⟩)] = some σw ∧
      ¬ (D1 : Store Unit Obj V Unit _).Pending () σw := by
  refine ⟨eventuallyConsistent, invisibleReads, opDriven, available, recvEnabled, sendClears,
    ?_, _, rfl, rfl, not_pending _⟩
  exact Store.IsExec.snoc (α := []) .nil rfl rfl (fun m h => by cases h)

end Podc.EventualConsistencyLimits
