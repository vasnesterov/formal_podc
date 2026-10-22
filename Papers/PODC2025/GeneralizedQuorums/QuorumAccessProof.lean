import Papers.PODC2025.GeneralizedQuorums.QuorumAccess

/-!
# Safety of the quorum access functions (Lemma 1, Theorem 3, Validity)

Proofs by invariants over reachable configurations of `qaAlg RR WW`.

* A step of a process is split into two micro-steps: the local transition (`pre`, before the
  waits are re-evaluated; configuration `mid`) and the re-evaluation of the waits (`adv`).
* `GRP C l u cu` (ghost-free form of "`l` applied `u` when its clock became `cu`"): `u` is in the
  state of `l`, the clock of `l` is `≥ cu`, and every `GET_RESP` of `l` with clock `≥ cu` (in transit
  or stored by a receiver) incorporates `u`. It is stable under every step.
* `Inv` is the global invariant; `RInv` is the invariant used for real-time ordering: it is
  established at the configuration where the `quorum_set` has completed and the `quorum_get` is not
  yet invoked, and maintained from there on.
-/

namespace Podc.GeneralizedQuorums.QA

open Cslib.ChannelFailures Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Configurations of `qaAlg`. -/
abbrev Cfg (P : Type) := Config P (qaObj P) (QMsg P) (QState P)

/-- Histories of `qaAlg`. -/
abbrev Hist (P : Type) := List (Label P (qaObj P))

/-! ### Local transitions -/

open Classical in
/-- The local transition of Figure 3 before the waits are re-evaluated. -/
noncomputable def pre (l : QState P) : Input P QOp (QMsg P) → QState P × List (P × QMsg P)
  | .invoke .get => ({ l with seq := l.seq + 1, phase := .getClk, clockResps := fun _ => none },
      bcast (.clockReq (l.seq + 1)))
  | .invoke .set => ({ l with seq := l.seq + 1, phase := .setAck, setResps := fun _ => none },
      bcast (.setReq (l.seq + 1)))
  | .tick _ => ({ l with clock := l.clock + 1 }, bcast (.getResp l.st (l.clock + 1)))
  | .recv j (.clockReq k) => (l, [(j, .clockResp k l.clock)])
  | .recv j (.clockResp k c) =>
    (if k = l.seq ∧ l.phase = .getClk then
      { l with clockResps := Function.update l.clockResps j (some c) } else l, [])
  | .recv j (.getResp s c) =>
    (if ∀ s' c', l.latest j = some (s', c') → c' ≤ c then
      { l with latest := Function.update l.latest j (some (s, c)) } else l, [])
  | .recv j (.setReq k) =>
    ({ l with st := insert (j, k) l.st, clock := l.clock + 1 }, [(j, .setResp k (l.clock + 1))])
  | .recv j (.setResp k c) =>
    (if k = l.seq ∧ l.phase = .setAck then
      { l with setResps := Function.update l.setResps j (some c) } else l, [])

variable (RR WW : Set (Set P))

lemma handle_eq (p : P) (i : Input P QOp (QMsg P)) (l : QState P) :
    (qaAlg RR WW).handle p i l = finish RR WW (pre l i).1 (pre l i).2 := by
  rcases i with (_ | _) | c | ⟨j, (k | ⟨k, c⟩ | ⟨s, c⟩ | k | ⟨k, c⟩)⟩ <;>
    simp only [qaAlg, pre] <;> split_ifs <;> rfl

/-- Local transition of `p` without re-evaluating the waits. -/
def mid (C : Cfg P) (p : P) (l0 : QState P) (out : List (P × QMsg P)) : Cfg P :=
  { C with
    loc := Function.update C.loc p l0
    chan := fun a b => if a = p then C.chan a b ++ msgsTo out b else C.chan a b
    sent := fun a b => if a = p then C.sent a b + (msgsTo out b).length else C.sent a b }

/-- Re-evaluation of the waits of `p`. -/
noncomputable def adv (C : Cfg P) (p : P) : Cfg P × Hist P :=
  ({ C with
     loc := Function.update C.loc p (advance RR WW (C.loc p)).1
     pend := Function.update C.pend p (pendAfter (C.pend p) (advance RR WW (C.loc p)).2) },
   respOut p (C.pend p) (advance RR WW (C.loc p)).2)

lemma apply_finish (C : Cfg P) (p : P) (l0 : QState P) (out : List (P × QMsg P)) :
    C.apply p (finish RR WW l0 out) = adv RR WW (mid C p l0 out) p := by
  simp [Config.apply, adv, mid, finish]

lemma step_cases (C : Cfg P) (e : Event P (qaObj P)) :
    (qaAlg RR WW).step C e = (C, []) ∨
    (∃ p o, C.pend p = none ∧ (qaAlg RR WW).step C e =
      ((adv RR WW (mid { C with pend := Function.update C.pend p (some o) } p
          (pre (C.loc p) (.invoke o)).1 (pre (C.loc p) (.invoke o)).2) p).1,
       .inv p o :: (adv RR WW (mid { C with pend := Function.update C.pend p (some o) } p
          (pre (C.loc p) (.invoke o)).1 (pre (C.loc p) (.invoke o)).2) p).2)) ∨
    (∃ p c, (qaAlg RR WW).step C e =
      adv RR WW (mid C p (pre (C.loc p) (.tick c)).1 (pre (C.loc p) (.tick c)).2) p) ∨
    (∃ q p m rest, C.chan q p = m :: rest ∧ (qaAlg RR WW).step C e =
      adv RR WW (mid (C.pop q p rest) p (pre (C.loc p) (.recv q m)).1
        (pre (C.loc p) (.recv q m)).2) p) := by
  rcases e with ⟨p, o⟩ | ⟨p, c⟩ | ⟨q, p⟩
  · simp only [Algorithm.step]
    split
    · exact Or.inl rfl
    · rename_i h
      refine Or.inr (Or.inl ⟨p, o, h, ?_⟩)
      rw [handle_eq, apply_finish]
  · refine Or.inr (Or.inr (Or.inl ⟨p, c, ?_⟩))
    simp only [Algorithm.step]
    rw [handle_eq, apply_finish]
  · simp only [Algorithm.step]
    split
    · exact Or.inl rfl
    · rename_i m rest h
      refine Or.inr (Or.inr (Or.inr ⟨q, p, m, rest, h, ?_⟩))
      rw [handle_eq, apply_finish]

/-! ### Re-evaluation of the waits -/

/-- The `quorum_get` of `l` has passed line 6 with `c_get ≤ c` (or is about to). -/
def GetGate (l : QState P) (c : ℕ) : Prop :=
  l.phase = .getWait c ∨
    (l.phase = .getClk ∧ ∃ W ∈ WW, ∀ x ∈ W, ∃ c', l.clockResps x = some c' ∧ c' ≤ c)

/-- The `quorum_set` of `l` has passed line 18 with `c_set ≤ c` (or is about to). -/
def SetGate (l : QState P) (c : ℕ) : Prop :=
  l.phase = .setWait c ∨
    (l.phase = .setAck ∧ ∃ W ∈ WW, ∀ x ∈ W, ∃ c', l.setResps x = some c' ∧ c' ≤ c)

/-- All members of `R` sent `GET_RESP`s with clock `≥ c` to `l`. -/
def ReadOK (l : QState P) (c : ℕ) (R : Set P) : Prop :=
  ∀ x ∈ R, ∃ s c', l.latest x = some (s, c') ∧ c ≤ c'

lemma le_sup_filter {R : Set P} (f : P → ℕ) {x : P} (hx : x ∈ R) [DecidablePred (· ∈ R)] :
    f x ≤ (Finset.univ.filter (· ∈ R)).sup f :=
  Finset.le_sup (f := f) (by simpa using hx)

open Classical in
lemma advance_spec (l : QState P) :
    advance RR WW l = (l, none) ∨
    (∃ c, l.phase = .getClk ∧ GetGate WW l c ∧
      advance RR WW l = ({ l with phase := .getWait c }, none)) ∨
    (∃ c, l.phase = .setAck ∧ SetGate WW l c ∧
      advance RR WW l = ({ l with phase := .setWait c }, none)) ∨
    (∃ c, GetGate WW l c ∧ ∃ R ∈ RR, ReadOK l c R ∧ ∃ S,
      (∀ x ∈ R, ∀ s c', l.latest x = some (s, c') → s ∈ S) ∧
      (∀ s ∈ S, ∃ x c', l.latest x = some (s, c')) ∧
      advance RR WW l = ({ l with phase := .idle }, some S)) ∨
    (∃ c, SetGate WW l c ∧ ∃ R ∈ RR, ReadOK l c R ∧
      advance RR WW l = ({ l with phase := .idle }, some [])) := by
  have hread : ∀ l' : QState P, (l'.phase = .idle ∨ (∃ c, l'.phase = .getWait c) ∨
      ∃ c, l'.phase = .setWait c) → advanceRead RR l' = (l', none) ∨
      (∃ c, GetGate WW l' c ∧ ∃ R ∈ RR, ReadOK l' c R ∧ ∃ S,
        (∀ x ∈ R, ∀ s c', l'.latest x = some (s, c') → s ∈ S) ∧
        (∀ s ∈ S, ∃ x c', l'.latest x = some (s, c')) ∧
        advanceRead RR l' = ({ l' with phase := .idle }, some S)) ∨
      (∃ c, SetGate WW l' c ∧ ∃ R ∈ RR, ReadOK l' c R ∧
        advanceRead RR l' = ({ l' with phase := .idle }, some [])) := by
    intro l' hl'
    unfold advanceRead
    split
    · rename_i c hc
      split_ifs with h
      · refine Or.inr (Or.inl ⟨c, Or.inl hc, h.choose, h.choose_spec.1, h.choose_spec.2, _, ?_, ?_, rfl⟩)
        · intro x hx s c' hs
          simp only [List.mem_filterMap, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨x, hx, by simp [hs]⟩
        · intro s hs
          simp only [List.mem_filterMap, Option.map_eq_some_iff] at hs
          obtain ⟨x, -, ⟨s', c'⟩, h1, rfl⟩ := hs
          exact ⟨x, c', h1⟩
      · exact Or.inl rfl
    · rename_i c hc
      split_ifs with h
      · exact Or.inr (Or.inr ⟨c, Or.inl hc, h.choose, h.choose_spec.1, h.choose_spec.2, rfl⟩)
      · exact Or.inl rfl
    · exact Or.inl rfl
  unfold advance
  split
  · rename_i hc
    split_ifs with h
    · have hW : ∀ x ∈ h.choose, ∃ c', l.clockResps x = some c' ∧
          c' ≤ (Finset.univ.filter (· ∈ h.choose)).sup fun j => (l.clockResps j).getD 0 := by
        intro x hx
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (h.choose_spec.2 x hx)
        refine ⟨c', hc', ?_⟩
        have := le_sup_filter (fun j => (l.clockResps j).getD 0) hx
        simpa [hc'] using this
      have hg : GetGate WW l ((Finset.univ.filter (· ∈ h.choose)).sup
          fun j => (l.clockResps j).getD 0) := Or.inr ⟨hc, h.choose, h.choose_spec.1, hW⟩
      rcases hread { l with phase := .getWait ((Finset.univ.filter (· ∈ h.choose)).sup
          fun j => (l.clockResps j).getD 0) } (Or.inr (Or.inl ⟨_, rfl⟩)) with h' | h' | h'
      · exact Or.inr (Or.inl ⟨_, hc, hg, h'⟩)
      · obtain ⟨c, hc1, R, hR, h2⟩ := h'
        rcases hc1 with hc1 | hc1
        · cases hc1
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hg, R, hR, h2⟩)))
        · cases hc1.1
      · obtain ⟨c, hc1, -⟩ := h'
        rcases hc1 with hc1 | hc1
        · cases hc1
        · cases hc1.1
    · exact Or.inl rfl
  · rename_i hc
    split_ifs with h
    · have hW : ∀ x ∈ h.choose, ∃ c', l.setResps x = some c' ∧
          c' ≤ (Finset.univ.filter (· ∈ h.choose)).sup fun j => (l.setResps j).getD 0 := by
        intro x hx
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (h.choose_spec.2 x hx)
        refine ⟨c', hc', ?_⟩
        have := le_sup_filter (fun j => (l.setResps j).getD 0) hx
        simpa [hc'] using this
      have hg : SetGate WW l ((Finset.univ.filter (· ∈ h.choose)).sup
          fun j => (l.setResps j).getD 0) := Or.inr ⟨hc, h.choose, h.choose_spec.1, hW⟩
      rcases hread { l with phase := .setWait ((Finset.univ.filter (· ∈ h.choose)).sup
          fun j => (l.setResps j).getD 0) } (Or.inr (Or.inr ⟨_, rfl⟩)) with h' | h' | h'
      · exact Or.inr (Or.inr (Or.inl ⟨_, hc, hg, h'⟩))
      · obtain ⟨c, hc1, -⟩ := h'
        rcases hc1 with hc1 | hc1
        · cases hc1
        · cases hc1.1
      · obtain ⟨c, hc1, R, hR, h2⟩ := h'
        rcases hc1 with hc1 | hc1
        · cases hc1
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hg, R, hR, h2⟩)))
        · cases hc1.1
    · exact Or.inl rfl
  · rename_i h1 h2
    have hph : l.phase = .idle ∨ (∃ c, l.phase = .getWait c) ∨ ∃ c, l.phase = .setWait c := by
      cases hp : l.phase with
      | getClk => exact absurd hp h1
      | setAck => exact absurd hp h2
      | idle => exact Or.inl rfl
      | getWait c => exact Or.inr (Or.inl ⟨c, rfl⟩)
      | setWait c => exact Or.inr (Or.inr ⟨c, rfl⟩)
    rcases hread l hph with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

lemma advance_fst (l : QState P) : ∃ ph, (advance RR WW l).1 = { l with phase := ph } := by
  rcases advance_spec RR WW l with h | ⟨c, -, -, h⟩ | ⟨c, -, -, h⟩ | ⟨c, -, R, -, -, S, -, -, h⟩ |
      ⟨c, -, R, -, -, h⟩ <;> rw [h]
  · exact ⟨l.phase, rfl⟩
  all_goals exact ⟨_, rfl⟩

@[simp] lemma advance_st (l : QState P) : (advance RR WW l).1.st = l.st := by
  obtain ⟨ph, h⟩ := advance_fst RR WW l; rw [h]
@[simp] lemma advance_clock (l : QState P) : (advance RR WW l).1.clock = l.clock := by
  obtain ⟨ph, h⟩ := advance_fst RR WW l; rw [h]
@[simp] lemma advance_seq (l : QState P) : (advance RR WW l).1.seq = l.seq := by
  obtain ⟨ph, h⟩ := advance_fst RR WW l; rw [h]
@[simp] lemma advance_latest (l : QState P) : (advance RR WW l).1.latest = l.latest := by
  obtain ⟨ph, h⟩ := advance_fst RR WW l; rw [h]
@[simp] lemma advance_clockResps (l : QState P) :
    (advance RR WW l).1.clockResps = l.clockResps := by
  obtain ⟨ph, h⟩ := advance_fst RR WW l; rw [h]
@[simp] lemma advance_setResps (l : QState P) : (advance RR WW l).1.setResps = l.setResps := by
  obtain ⟨ph, h⟩ := advance_fst RR WW l; rw [h]

/-! ### Invariants -/

/-- `l` has incorporated the update `u` into its state no later than when its clock became `cu`:
`u` is in the state of `l`, the clock of `l` is `≥ cu`, and every `GET_RESP` of `l` with clock
`≥ cu` (in transit, or stored by its receiver) incorporates `u`. -/
def GRP (C : Cfg P) (l : P) (u : P × ℕ) (cu : ℕ) : Prop :=
  u ∈ (C.loc l).st ∧ cu ≤ (C.loc l).clock ∧
  (∀ x s c, QMsg.getResp s c ∈ C.chan l x → cu ≤ c → u ∈ s) ∧
  (∀ x s c, (C.loc x).latest l = some (s, c) → cu ≤ c → u ∈ s)

/-- All updates of `s` are updates of invoked `quorum_set`s. -/
def ValidSt (h : Hist P) (s : Finset (P × ℕ)) : Prop :=
  ∀ u ∈ s, ∃ k, u.2 = k + 1 ∧ opOf h (u.1, k) = some .set

/-- Facts about a message in transit on the channel `a → b`. -/
def MsgOK (C : Cfg P) (h : Hist P) (a b : P) : QMsg P → Prop
  | .clockReq k => k ≤ (C.loc a).seq
  | .clockResp k _ => k ≤ (C.loc b).seq
  | .getResp s c => c ≤ (C.loc a).clock ∧ ValidSt h s
  | .setReq k => ∃ k', k = k' + 1 ∧ opOf h (a, k') = some .set
  | .setResp k c => ∃ cu ≤ c, GRP C a (b, k) cu

/-- The update `(p, n)` has been applied by a write quorum at clocks `≤ c` and the clocks of a
read quorum are `≥ c` (the state after the `quorum_set` with update `(p, n)` completed). -/
def SetDone (C : Cfg P) (p : P) (n : ℕ) : Prop :=
  ∃ c, (∃ W ∈ WW, ∀ l ∈ W, ∃ cu ≤ c, GRP C l (p, n) cu) ∧
    (∃ R ∈ RR, ∀ i ∈ R, c ≤ (C.loc i).clock)

/-- The phase matches the pending operation. -/
def PhaseOK : Option QOp → Phase → Prop
  | none, .idle => True
  | some .get, .getClk => True
  | some .get, .getWait _ => True
  | some .set, .setAck => True
  | some .set, .setWait _ => True
  | _, _ => False

/-- The global invariant. -/
structure Inv (C : Cfg P) (h : Hist P) : Prop where
  phase : ∀ p, PhaseOK (C.pend p) (C.loc p).phase
  seq : ∀ p, (opsOf h p).length = (C.loc p).seq
  idle : ∀ p, C.pend p = none → (respsOf h p).length = (C.loc p).seq
  busy : ∀ p o, C.pend p = some o →
    (respsOf h p).length + 1 = (C.loc p).seq ∧ opOf h (p, (respsOf h p).length) = some o
  msg : ∀ a b m, m ∈ C.chan a b → MsgOK C h a b m
  latest : ∀ x l s c, (C.loc x).latest l = some (s, c) → c ≤ (C.loc l).clock ∧ ValidSt h s
  st : ∀ l, ValidSt h (C.loc l).st
  setResps : ∀ p l c, (C.loc p).phase = .setAck → (C.loc p).setResps l = some c →
    ∃ cu ≤ c, GRP C l (p, (C.loc p).seq) cu
  setWait : ∀ p c, (C.loc p).phase = .setWait c →
    ∃ W ∈ WW, ∀ l ∈ W, ∃ cu ≤ c, GRP C l (p, (C.loc p).seq) cu
  setDone : ∀ p k, opOf h (p, k) = some .set → Completed h (p, k) → SetDone RR WW C p (k + 1)
  ret : ∀ q S, Label.ret q S ∈ h → ∀ s ∈ S, ValidSt h s

/-- `C'` extends `C`: states and clocks grow, new `GET_RESP`s incorporate the sender's state, and
stored `GET_RESP`s were stored before or were in transit. -/
structure Grows (C C' : Cfg P) : Prop where
  st : ∀ l, (C.loc l).st ⊆ (C'.loc l).st
  clock : ∀ l, (C.loc l).clock ≤ (C'.loc l).clock
  seq : ∀ l, (C.loc l).seq ≤ (C'.loc l).seq
  getResp : ∀ l x s c, QMsg.getResp s c ∈ C'.chan l x →
    QMsg.getResp s c ∈ C.chan l x ∨ (C.loc l).st ⊆ s
  latest : ∀ x l s c, (C'.loc x).latest l = some (s, c) →
    (C.loc x).latest l = some (s, c) ∨ QMsg.getResp s c ∈ C.chan l x

lemma Grows.refl (C : Cfg P) : Grows C C :=
  ⟨fun _ => subset_rfl, fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ _ h => Or.inl h,
    fun _ _ _ _ h => Or.inl h⟩

lemma GRP.mono {C C' : Cfg P} (hg : Grows C C') {l : P} {u : P × ℕ} {cu : ℕ}
    (h : GRP C l u cu) : GRP C' l u cu := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hg.st l h1, h2.trans (hg.clock l), fun x s c hm hc => ?_, fun x s c hm hc => ?_⟩
  · rcases hg.getResp l x s c hm with hm | hm
    · exact h3 x s c hm hc
    · exact hm h1
  · rcases hg.latest x l s c hm with hm | hm
    · exact h4 x s c hm hc
    · exact h3 x s c hm hc

lemma ValidSt.mono {h : Hist P} {s : Finset (P × ℕ)} (hs : ValidSt h s) (ls : Hist P) :
    ValidSt (h ++ ls) s := by
  intro u hu
  obtain ⟨k, hk, ho⟩ := hs u hu
  exact ⟨k, hk, opOf_append_of_eq_some ho ls⟩

lemma MsgOK.mono {C C' : Cfg P} (hg : Grows C C') {h : Hist P} (ls : Hist P) {a b : P}
    {m : QMsg P} (hm : MsgOK C h a b m) : MsgOK C' (h ++ ls) a b m := by
  cases m with
  | clockReq k => exact le_trans hm (hg.seq a)
  | clockResp k c => exact le_trans hm (hg.seq b)
  | getResp s c => exact ⟨hm.1.trans (hg.clock a), hm.2.mono ls⟩
  | setReq k =>
    obtain ⟨k', rfl, h'⟩ := hm
    exact ⟨k', rfl, opOf_append_of_eq_some h' ls⟩
  | setResp k c =>
    obtain ⟨cu, hcu, h'⟩ := hm
    exact ⟨cu, hcu, h'.mono hg⟩

lemma SetDone.mono {C C' : Cfg P} (hg : Grows C C') {p : P} {n : ℕ} (h : SetDone RR WW C p n) :
    SetDone RR WW C' p n := by
  obtain ⟨c, ⟨W, hW, h1⟩, ⟨R, hR, h2⟩⟩ := h
  refine ⟨c, ⟨W, hW, fun l hl => ?_⟩, ⟨R, hR, fun i hi => (h2 i hi).trans (hg.clock i)⟩⟩
  obtain ⟨cu, hcu, h3⟩ := h1 l hl
  exact ⟨cu, hcu, h3.mono hg⟩

lemma MsgOK.mono' {C C' : Cfg P} (hg : Grows C C') {h : Hist P} {a b : P}
    {m : QMsg P} (hm : MsgOK C h a b m) : MsgOK C' h a b m := by
  simpa using hm.mono hg []

/-! ### Local transitions preserve the invariant -/

@[simp] lemma mid_loc (C : Cfg P) (p : P) (l0 : QState P) (out : List (P × QMsg P)) (x : P) :
    (mid C p l0 out).loc x = if x = p then l0 else C.loc x := by
  simp [mid, Function.update_apply]

@[simp] lemma mid_pend (C : Cfg P) (p : P) (l0 : QState P) (out : List (P × QMsg P)) :
    (mid C p l0 out).pend = C.pend := rfl

lemma mem_mid_chan {C : Cfg P} {p : P} {l0 : QState P} {out : List (P × QMsg P)} {a b : P}
    {m : QMsg P} : m ∈ (mid C p l0 out).chan a b ↔ m ∈ C.chan a b ∨ (a = p ∧ m ∈ msgsTo out b) := by
  simp only [mid]
  split_ifs with h <;> simp [h]

@[simp] lemma msgsTo_bcast (m : QMsg P) (b : P) : msgsTo (bcast m) b = [m] := by
  simp [msgsTo, bcast, List.filter_map, Function.comp_def, List.filter_eq,
    List.count_eq_one_of_mem (Finset.nodup_toList _)]

@[simp] lemma msgsTo_single (j : P) (m : QMsg P) (b : P) :
    msgsTo [(j, m)] b = if j = b then [m] else [] := by
  by_cases h : j = b <;> simp [msgsTo, h]

lemma grows_mid {C C₀ : Cfg P} (hloc : C₀.loc = C.loc)
    (hchan : ∀ a b m, m ∈ C₀.chan a b → m ∈ C.chan a b) (p : P) (l0 : QState P)
    (out : List (P × QMsg P)) (hst : (C.loc p).st ⊆ l0.st) (hclock : (C.loc p).clock ≤ l0.clock)
    (hseq : (C.loc p).seq ≤ l0.seq)
    (hout : ∀ b s c, QMsg.getResp s c ∈ msgsTo out b → (C.loc p).st ⊆ s)
    (hlat : ∀ l s c, l0.latest l = some (s, c) →
      (C.loc p).latest l = some (s, c) ∨ QMsg.getResp s c ∈ C.chan l p) :
    Grows C (mid C₀ p l0 out) := by
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l x s c hm => ?_, fun x l s c hm => ?_⟩
  · by_cases hl : l = p
    · subst hl; simpa using hst
    · simp [hl, hloc]
  · by_cases hl : l = p
    · subst hl; simpa using hclock
    · simp [hl, hloc]
  · by_cases hl : l = p
    · subst hl; simpa using hseq
    · simp [hl, hloc]
  · rcases mem_mid_chan.1 hm with hm1 | ⟨rfl, hm2⟩
    · exact Or.inl (hchan _ _ _ hm1)
    · exact Or.inr (hout _ _ _ hm2)
  · by_cases hx : x = p
    · subst hx
      simp only [mid_loc] at hm
      exact hlat l s c hm
    · simp only [mid_loc, ite_eq_right hx, hloc] at hm
      exact Or.inl hm

lemma inv_mid {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) {C₀ : Cfg P} (hloc : C₀.loc = C.loc)
    (hpend : C₀.pend = C.pend) (hchan : ∀ a b m, m ∈ C₀.chan a b → m ∈ C.chan a b)
    {p : P} {l0 : QState P} {out : List (P × QMsg P)} (hg : Grows C (mid C₀ p l0 out))
    (hph : l0.phase = (C.loc p).phase) (hseq : l0.seq = (C.loc p).seq)
    (hout : ∀ b m, m ∈ msgsTo out b → MsgOK (mid C₀ p l0 out) h p b m)
    (hst : ValidSt h l0.st)
    (hsr : l0.phase = .setAck → ∀ l c, l0.setResps l = some c →
      ∃ cu ≤ c, GRP (mid C₀ p l0 out) l (p, l0.seq) cu) :
    Inv RR WW (mid C₀ p l0 out) h := by
  constructor
  · intro x
    by_cases hx : x = p
    · subst hx; simpa [hph, hpend] using hI.phase x
    · simpa [hx, hloc, hpend] using hI.phase x
  · intro x
    by_cases hx : x = p
    · subst hx; simpa [hseq] using hI.seq x
    · simpa [hx, hloc] using hI.seq x
  · intro x hx'
    rw [mid_pend, hpend] at hx'
    by_cases hx : x = p
    · subst hx; simpa [hseq] using hI.idle x hx'
    · simpa [hx, hloc] using hI.idle x hx'
  · intro x o hx'
    rw [mid_pend, hpend] at hx'
    by_cases hx : x = p
    · subst hx; simpa [hseq] using hI.busy x o hx'
    · simpa [hx, hloc] using hI.busy x o hx'
  · intro a b m hm
    rcases mem_mid_chan.1 hm with hm1 | ⟨rfl, hm2⟩
    · exact (hI.msg a b m (hchan a b m hm1)).mono' hg
    · exact hout b m hm2
  · intro x l s c hm
    rcases hg.latest x l s c hm with hm | hm
    · exact ⟨(hI.latest x l s c hm).1.trans (hg.clock l), (hI.latest x l s c hm).2⟩
    · exact ⟨(hI.msg l x _ hm).1.trans (hg.clock l), (hI.msg l x _ hm).2⟩
  · intro x
    by_cases hx : x = p
    · subst hx; simpa using hst
    · simpa [hx, hloc] using hI.st x
  · intro x l c hx1 hx2
    by_cases hx : x = p
    · subst hx
      simp only [mid_loc] at hx1 hx2 ⊢
      exact hsr hx1 l c hx2
    · simp only [mid_loc, ite_eq_right hx, hloc] at hx1 hx2 ⊢
      obtain ⟨cu, hcu, h'⟩ := hI.setResps x l c hx1 hx2
      exact ⟨cu, hcu, h'.mono hg⟩
  · intro x c hx1
    have : ∃ W ∈ WW, ∀ l ∈ W, ∃ cu ≤ c, GRP C l (x, (C.loc x).seq) cu := by
      by_cases hx : x = p
      · subst hx
        rw [mid_loc, ite_eq_left rfl, hph] at hx1
        exact hI.setWait x c hx1
      · simp only [mid_loc, ite_eq_right hx, hloc] at hx1
        exact hI.setWait x c hx1
    obtain ⟨W, hW, hW'⟩ := this
    refine ⟨W, hW, fun l hl => ?_⟩
    obtain ⟨cu, hcu, h'⟩ := hW' l hl
    refine ⟨cu, hcu, ?_⟩
    have hs : ((mid C₀ p l0 out).loc x).seq = (C.loc x).seq := by
      by_cases hx : x = p
      · subst hx; simp [hseq]
      · simp [hx, hloc]
    rw [hs]; exact h'.mono hg
  · intro x k h1 h2
    exact (hI.setDone x k h1 h2).mono RR WW hg
  · exact hI.ret

variable {RR WW} in
lemma inv_tick {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) (p : P) (c : ℕ) :
    Inv RR WW (mid C p (pre (C.loc p) (.tick c)).1 (pre (C.loc p) (.tick c)).2) h := by
  have hg : Grows C (mid C p (pre (C.loc p) (.tick c)).1 (pre (C.loc p) (.tick c)).2) :=
    grows_mid rfl (fun _ _ _ h => h) p _ _ subset_rfl (by simp [pre]) le_rfl
      (by simp only [pre, msgsTo_bcast, List.mem_singleton, QMsg.getResp.injEq]
          rintro b s c' ⟨rfl, rfl⟩; exact subset_rfl) (fun l s c h => Or.inl h)
  refine inv_mid RR WW hI rfl rfl (fun _ _ _ h => h) hg rfl rfl ?_ (hI.st p) ?_
  · intro b m hm
    simp only [pre, msgsTo_bcast, List.mem_singleton] at hm; subst hm
    exact ⟨by simp [pre], hI.st p⟩
  · intro hph l c' hc'
    obtain ⟨cu, hcu, h'⟩ := hI.setResps p l c' hph hc'
    exact ⟨cu, hcu, h'.mono hg⟩

lemma pop_chan_sub {C : Cfg P} {q p : P} {m : QMsg P} {rest : List (QMsg P)}
    (hc : C.chan q p = m :: rest) (a b : P) (m' : QMsg P) (h : m' ∈ (C.pop q p rest).chan a b) :
    m' ∈ C.chan a b := by
  simp only [Config.pop] at h
  split_ifs at h with hab
  · obtain ⟨rfl, rfl⟩ := hab
    rw [hc]; exact List.mem_cons_of_mem _ h
  · exact h

variable {RR WW} in
lemma inv_deliver {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) {q p : P} {m : QMsg P}
    {rest : List (QMsg P)} (hc : C.chan q p = m :: rest) :
    Inv RR WW (mid (C.pop q p rest) p (pre (C.loc p) (.recv q m)).1
      (pre (C.loc p) (.recv q m)).2) h := by
  have hm : MsgOK C h q p m := hI.msg q p m (by rw [hc]; exact List.mem_cons_self ..)
  have hsub := pop_chan_sub hc
  have hsame : ∀ {l0 : QState P} {out : List (P × QMsg P)},
      Grows C (mid (C.pop q p rest) p l0 out) → l0.phase = (C.loc p).phase →
      l0.seq = (C.loc p).seq → l0.setResps = (C.loc p).setResps →
      l0.phase = .setAck → ∀ l c, l0.setResps l = some c →
        ∃ cu ≤ c, GRP (mid (C.pop q p rest) p l0 out) l (p, l0.seq) cu := by
    intro l0 out hg h1 h2 h3 h4 l c h5
    rw [h3] at h5; rw [h1] at h4; rw [h2]
    obtain ⟨cu, hcu, h'⟩ := hI.setResps p l c h4 h5
    exact ⟨cu, hcu, h'.mono hg⟩
  cases m with
  | clockReq k =>
    have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p (pre (C.loc p) (.recv q (.clockReq k))).1
      (pre (C.loc p) (.recv q (.clockReq k))).2 subset_rfl le_rfl le_rfl
      (by intro b s c h; simp [pre] at h) (fun l s c h => Or.inl h)
    refine inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl ?_ (hI.st p) (hsame hg rfl rfl rfl)
    intro b m' hm'
    simp only [pre, msgsTo_single] at hm'
    split_ifs at hm' with hb
    · subst hb; simp only [List.mem_singleton] at hm'; subst hm'
      exact le_trans hm (hg.seq q)
    · simp at hm'
  | clockResp k c =>
    simp only [pre]
    split_ifs with hk
    · have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p
        { C.loc p with clockResps := Function.update (C.loc p).clockResps q (some c) } []
        subset_rfl le_rfl le_rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
      exact inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl (by simp [msgsTo]) (hI.st p)
        (hsame hg rfl rfl rfl)
    · have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p (C.loc p) []
        subset_rfl le_rfl le_rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
      exact inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl (by simp [msgsTo]) (hI.st p)
        (hsame hg rfl rfl rfl)
  | getResp s c =>
    simp only [pre]
    split_ifs with hk
    · have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p
        { C.loc p with latest := Function.update (C.loc p).latest q (some (s, c)) } []
        subset_rfl le_rfl le_rfl (by simp [msgsTo]) (by
          intro l s' c' h'
          by_cases hl : l = q
          · subst hl
            simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            exact Or.inr (by rw [hc]; exact List.mem_cons_self ..)
          · simp only [Function.update_of_ne hl] at h'
            exact Or.inl h')
      exact inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl (by simp [msgsTo]) (hI.st p)
        (hsame hg rfl rfl rfl)
    · have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p (C.loc p) []
        subset_rfl le_rfl le_rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
      exact inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl (by simp [msgsTo]) (hI.st p)
        (hsame hg rfl rfl rfl)
  | setReq k =>
    obtain ⟨k', rfl, hk'⟩ := hm
    have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p
      (pre (C.loc p) (.recv q (.setReq (k' + 1)))).1 (pre (C.loc p) (.recv q (.setReq (k' + 1)))).2
      (by simp [pre]) (by simp [pre]) le_rfl
      (by intro b s c h; simp [pre] at h) (fun l s c h => Or.inl h)
    refine inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl ?_ ?_ (hsame hg rfl rfl rfl)
    · intro b m' hm'
      simp only [pre, msgsTo_single] at hm'
      split_ifs at hm' with hb
      · subst hb; simp only [List.mem_singleton] at hm'; subst hm'
        refine ⟨(C.loc p).clock + 1, le_rfl, by simp [pre], by simp [pre], ?_, ?_⟩
        · intro x s c h1 h2
          rcases mem_mid_chan.1 h1 with h1 | ⟨-, h1⟩
          · have := (hI.msg p x _ (hsub _ _ _ h1)).1; omega
          · simp [pre] at h1
        · intro x s c h1 h2
          rcases hg.latest x p s c h1 with h1 | h1
          · have := (hI.latest x p s c h1).1; omega
          · have := (hI.msg p x _ h1).1; omega
      · simp at hm'
    · intro u hu
      simp only [pre, Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact ⟨k', rfl, hk'⟩
      · exact hI.st p u hu
  | setResp k c =>
    simp only [pre]
    split_ifs with hk
    · have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p
        { C.loc p with setResps := Function.update (C.loc p).setResps q (some c) } []
        subset_rfl le_rfl le_rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
      refine inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl (by simp [msgsTo]) (hI.st p) ?_
      intro hph l c' hc'
      by_cases hl : l = q
      · subst hl
        simp only [Function.update_self, Option.some.injEq] at hc'
        subst hc'
        obtain ⟨cu, hcu, h'⟩ := hm
        rw [hk.1] at h'
        exact ⟨cu, hcu, h'.mono hg⟩
      · simp only [Function.update_of_ne hl] at hc'
        obtain ⟨cu, hcu, h'⟩ := hI.setResps p l c' hph hc'
        exact ⟨cu, hcu, h'.mono hg⟩
    · have hg := grows_mid (C := C) (C₀ := C.pop q p rest) rfl hsub p (C.loc p) []
        subset_rfl le_rfl le_rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
      exact inv_mid RR WW hI (C₀ := C.pop q p rest) rfl rfl hsub hg rfl rfl (by simp [msgsTo]) (hI.st p)
        (hsame hg rfl rfl rfl)

lemma Inv.resps_le {RR WW : Set (Set P)} {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) (x : P) :
    (respsOf h x).length ≤ (opsOf h x).length := by
  rw [hI.seq x]
  cases hx : C.pend x with
  | none => exact (hI.idle x hx).le
  | some o => have := (hI.busy x o hx).1; omega

lemma Inv.opOf_of_completed {RR WW : Set (Set P)} {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h)
    {x : P × ℕ} (hx : Completed h x) (ls : Hist P) : opOf (h ++ ls) x = opOf h x :=
  opOf_append_of_invoked (lt_of_lt_of_le hx (hI.resps_le x.1))

@[simp] lemma respsOf_append_inv (h : Hist P) (p : P) (o : QOp) (x : P) :
    respsOf (h ++ [Label.inv p o]) x = respsOf h x := by
  simp

lemma completed_append_inv {h : Hist P} {p : P} {o : QOp} {x : P × ℕ} :
    Completed (h ++ [Label.inv p o]) x ↔ Completed h x := by
  simp [Completed]

variable {RR WW} in
lemma inv_invoke_gen {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) {p : P} (hp : C.pend p = none)
    (o : QOp) (l0 : QState P) (out : List (P × QMsg P)) (hst : l0.st = (C.loc p).st)
    (hclock : l0.clock = (C.loc p).clock) (hseq : l0.seq = (C.loc p).seq + 1)
    (hlat : l0.latest = (C.loc p).latest) (hph : PhaseOK (some o) l0.phase)
    (hsr : l0.phase = .setAck → ∀ l, l0.setResps l = none) (hsw : ∀ c, l0.phase ≠ .setWait c)
    (hout : ∀ b m, m ∈ msgsTo out b →
      m = .clockReq ((C.loc p).seq + 1) ∨ (o = .set ∧ m = .setReq ((C.loc p).seq + 1))) :
    Inv RR WW (mid { C with pend := Function.update C.pend p (some o) } p l0 out)
      (h ++ [.inv p o]) := by
  set C' := mid { C with pend := Function.update C.pend p (some o) } p l0 out with hC'
  have hg : Grows C C' :=
    grows_mid (C := C) (C₀ := { C with pend := Function.update C.pend p (some o) }) rfl
      (fun _ _ _ h => h) p l0 out (by rw [hst]) (by rw [hclock]) (by rw [hseq]; omega)
      (by intro b s c hm; rcases hout b _ hm with h | ⟨-, h⟩ <;> cases h)
      (by intro l s c h; rw [hlat] at h; exact Or.inl h)
  have hops : ∀ x, opsOf (h ++ [Label.inv p o]) x = opsOf h x ++ if p = x then [o] else [] := by
    intro x; rw [opsOf_concat]; by_cases hx : p = x <;> simp [hx]
  have hopOf : ∀ y, opOf (h ++ [Label.inv p o]) y =
      if y = (p, (C.loc p).seq) then some o else opOf h y := by
    intro y; rw [opOf_concat_inv, hI.seq p]
  have hloc : ∀ x, x ≠ p → C'.loc x = C.loc x := by intro x hx; simp [hC', hx]
  have hlocp : C'.loc p = l0 := by simp [hC']
  have hpend : ∀ x, C'.pend x = if x = p then some o else C.pend x := by
    intro x; simp [hC', Function.update_apply]
  constructor
  · intro x
    rw [hpend]
    by_cases hx : x = p
    · subst hx; simpa [hlocp] using hph
    · simpa [hx, hloc x hx] using hI.phase x
  · intro x
    rw [hops]
    by_cases hx : x = p
    · subst hx; simp [hlocp, hseq, hI.seq x]
    · simp [Ne.symm hx, hloc x hx, hI.seq x]
  · intro x hx'
    rw [hpend] at hx'
    by_cases hx : x = p
    · simp [hx] at hx'
    · simp only [ite_eq_right hx] at hx'
      simpa [hloc x hx] using hI.idle x hx'
  · intro x o' hx'
    rw [hpend] at hx'
    by_cases hx : x = p
    · subst hx
      rw [ite_eq_left rfl, Option.some.injEq] at hx'
      subst hx'
      have h1 := hI.idle x hp
      refine ⟨by simp [hlocp, hseq, h1], ?_⟩
      rw [hopOf]; simp [h1]
    · simp only [ite_eq_right hx] at hx'
      obtain ⟨h1, h2⟩ := hI.busy x o' hx'
      refine ⟨by simpa [hloc x hx] using h1, ?_⟩
      rw [hopOf]; simpa [hx] using h2
  · intro a b m hm
    rcases mem_mid_chan.1 hm with hm1 | ⟨rfl, hm2⟩
    · exact (hI.msg a b m hm1).mono hg _
    · rcases hout b m hm2 with rfl | ⟨rfl, rfl⟩
      · show (C.loc a).seq + 1 ≤ (C'.loc a).seq
        rw [hlocp, hseq]
      · exact ⟨(C.loc a).seq, rfl, by rw [hopOf]; simp⟩
  · intro x l s c hm
    rcases hg.latest x l s c hm with hm | hm
    · exact ⟨(hI.latest x l s c hm).1.trans (hg.clock l), (hI.latest x l s c hm).2.mono _⟩
    · exact ⟨(hI.msg l x _ hm).1.trans (hg.clock l), (hI.msg l x _ hm).2.mono _⟩
  · intro x
    by_cases hx : x = p
    · subst hx; rw [hlocp, hst]; exact (hI.st x).mono _
    · rw [hloc x hx]; exact (hI.st x).mono _
  · intro x l c hx1 hx2
    by_cases hx : x = p
    · subst hx
      rw [hlocp] at hx1 hx2
      rw [hsr hx1 l] at hx2; cases hx2
    · rw [hloc x hx] at hx1 hx2 ⊢
      obtain ⟨cu, hcu, h'⟩ := hI.setResps x l c hx1 hx2
      exact ⟨cu, hcu, h'.mono hg⟩
  · intro x c hx1
    by_cases hx : x = p
    · subst hx; rw [hlocp] at hx1; exact absurd hx1 (hsw c)
    · rw [hloc x hx] at hx1 ⊢
      obtain ⟨W, hW, hW'⟩ := hI.setWait x c hx1
      refine ⟨W, hW, fun l hl => ?_⟩
      obtain ⟨cu, hcu, h'⟩ := hW' l hl
      exact ⟨cu, hcu, h'.mono hg⟩
  · intro x k h1 h2
    rw [completed_append_inv] at h2
    rw [hI.opOf_of_completed h2] at h1
    exact (hI.setDone x k h1 h2).mono RR WW hg
  · intro q S hq s hs
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hq
    exact (hI.ret q S hq s hs).mono _

variable {RR WW} in
lemma inv_invoke {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) {p : P} (hp : C.pend p = none)
    (o : QOp) :
    Inv RR WW (mid { C with pend := Function.update C.pend p (some o) } p
      (pre (C.loc p) (.invoke o)).1 (pre (C.loc p) (.invoke o)).2) (h ++ [.inv p o]) := by
  cases o with
  | get =>
    refine inv_invoke_gen hI hp _ _ _ rfl rfl rfl rfl trivial (fun h => by cases h)
      (fun c h => by cases h) ?_
    intro b m hm; simp only [pre, msgsTo_bcast, List.mem_singleton] at hm; exact Or.inl hm
  | set =>
    refine inv_invoke_gen hI hp _ _ _ rfl rfl rfl rfl trivial (fun _ _ => rfl)
      (fun c h => by cases h) ?_
    intro b m hm; simp only [pre, msgsTo_bcast, List.mem_singleton] at hm; exact Or.inr ⟨rfl, hm⟩

/-! ### Re-evaluating the waits preserves the invariant -/

lemma grows_phase (C : Cfg P) (p : P) (ph : Phase) (pd : P → Option QOp) :
    Grows C { C with loc := Function.update C.loc p { C.loc p with phase := ph }, pend := pd } := by
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l x s c hm => Or.inl hm, fun x l s c hm => ?_⟩
  · by_cases hl : l = p
    · subst hl; simp
    · simp [hl]
  · by_cases hl : l = p
    · subst hl; simp
    · simp [hl]
  · by_cases hl : l = p
    · subst hl; simp
    · simp [hl]
  · left
    by_cases hx : x = p
    · subst hx; simpa using hm
    · simpa [hx] using hm

variable {RR WW} in
lemma inv_phase {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) (p : P) (ph : Phase)
    (hph : PhaseOK (C.pend p) ph) (hsr : ph = .setAck → (C.loc p).phase = .setAck)
    (hsw : ∀ c, ph = .setWait c →
      ∃ W ∈ WW, ∀ l ∈ W, ∃ cu ≤ c, GRP C l (p, (C.loc p).seq) cu) :
    Inv RR WW { C with loc := Function.update C.loc p { C.loc p with phase := ph } } h := by
  have hg := grows_phase C p ph C.pend
  set C' : Cfg P := { C with loc := Function.update C.loc p { C.loc p with phase := ph } }
    with hC'
  have hloc : ∀ x, x ≠ p → C'.loc x = C.loc x := by intro x hx; simp [hC', hx]
  have hlocp : C'.loc p = { C.loc p with phase := ph } := by simp [hC']
  constructor
  · intro x
    by_cases hx : x = p
    · subst hx; rw [hlocp]; exact hph
    · rw [hloc x hx]; exact hI.phase x
  · intro x
    by_cases hx : x = p
    · subst hx; rw [hlocp]; exact hI.seq x
    · rw [hloc x hx]; exact hI.seq x
  · intro x hx'
    by_cases hx : x = p
    · subst hx; rw [hlocp]; exact hI.idle x hx'
    · rw [hloc x hx]; exact hI.idle x hx'
  · intro x o hx'
    by_cases hx : x = p
    · subst hx; rw [hlocp]; exact hI.busy x o hx'
    · rw [hloc x hx]; exact hI.busy x o hx'
  · intro a b m hm; exact (hI.msg a b m hm).mono' hg
  · intro x l s c hm
    have := hI.latest x l s c (by
      by_cases hx : x = p
      · subst hx; rw [hlocp] at hm; exact hm
      · rw [hloc x hx] at hm; exact hm)
    exact ⟨this.1.trans (hg.clock l), this.2⟩
  · intro x
    by_cases hx : x = p
    · subst hx; rw [hlocp]; exact hI.st x
    · rw [hloc x hx]; exact hI.st x
  · intro x l c hx1 hx2
    have : ∃ cu ≤ c, GRP C l (x, (C.loc x).seq) cu := by
      by_cases hx : x = p
      · subst hx; rw [hlocp] at hx1 hx2; exact hI.setResps x l c (hsr hx1) hx2
      · rw [hloc x hx] at hx1 hx2; exact hI.setResps x l c hx1 hx2
    obtain ⟨cu, hcu, h'⟩ := this
    refine ⟨cu, hcu, ?_⟩
    have hs : (C'.loc x).seq = (C.loc x).seq := by
      by_cases hx : x = p
      · subst hx; rw [hlocp]
      · rw [hloc x hx]
    rw [hs]; exact h'.mono hg
  · intro x c hx1
    have : ∃ W ∈ WW, ∀ l ∈ W, ∃ cu ≤ c, GRP C l (x, (C.loc x).seq) cu := by
      by_cases hx : x = p
      · subst hx; rw [hlocp] at hx1; exact hsw c hx1
      · rw [hloc x hx] at hx1; exact hI.setWait x c hx1
    obtain ⟨W, hW, hW'⟩ := this
    refine ⟨W, hW, fun l hl => ?_⟩
    obtain ⟨cu, hcu, h'⟩ := hW' l hl
    refine ⟨cu, hcu, ?_⟩
    have hs : (C'.loc x).seq = (C.loc x).seq := by
      by_cases hx : x = p
      · subst hx; rw [hlocp]
      · rw [hloc x hx]
    rw [hs]; exact h'.mono hg
  · intro x k h1 h2; exact (hI.setDone x k h1 h2).mono RR WW hg
  · exact hI.ret

lemma respsOf_append_ret (h : Hist P) (p : P) (S : List (Finset (P × ℕ))) (x : P) :
    respsOf (h ++ [Label.ret p S]) x = respsOf h x ++ if p = x then [S] else [] := by
  rw [respsOf_concat]; by_cases hx : p = x <;> simp [hx]

lemma opOf_append_ret (h : Hist P) (p : P) (S : List (Finset (P × ℕ))) (y : P × ℕ) :
    opOf (h ++ [Label.ret p S]) y = opOf h y :=
  opOf_concat_of_ne (by intro o h; cases h)

variable {RR WW} in
lemma inv_ret {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) (p : P) (o : QOp)
    (hp : C.pend p = some o) (S : List (Finset (P × ℕ)))
    (hdone : o = .set → SetDone RR WW C p (C.loc p).seq) (hS : ∀ s ∈ S, ValidSt h s) :
    Inv RR WW { C with
      loc := Function.update C.loc p ({ C.loc p with phase := .idle } : QState P)
      pend := Function.update C.pend p none } (h ++ [.ret p S]) := by
  have hg := grows_phase C p .idle (Function.update C.pend p none)
  set C' : Cfg P := { C with
      loc := Function.update C.loc p ({ C.loc p with phase := .idle } : QState P)
      pend := Function.update C.pend p none } with hC'
  have hloc : ∀ x, x ≠ p → C'.loc x = C.loc x := by intro x hx; simp [hC', hx]
  have hlocp : C'.loc p = { C.loc p with phase := .idle } := by simp [hC']
  have hpend : ∀ x, x ≠ p → C'.pend x = C.pend x := by intro x hx; simp [hC', hx]
  have hpendp : C'.pend p = none := by simp [hC']
  have hops : ∀ x, opsOf (h ++ [Label.ret p S]) x = opsOf h x := by
    intro x; simp
  obtain ⟨hb1, hb2⟩ := hI.busy p o hp
  constructor
  · intro x
    by_cases hx : x = p
    · subst hx; rw [hlocp, hpendp]; trivial
    · rw [hloc x hx, hpend x hx]; exact hI.phase x
  · intro x
    rw [hops]
    by_cases hx : x = p
    · subst hx; rw [hlocp]; exact hI.seq x
    · rw [hloc x hx]; exact hI.seq x
  · intro x hx'
    rw [respsOf_append_ret]
    by_cases hx : x = p
    · subst hx; rw [hlocp]; simpa using hb1
    · rw [hloc x hx, hpend x hx] at *; simpa [Ne.symm hx] using hI.idle x hx'
  · intro x o' hx'
    by_cases hx : x = p
    · subst hx; rw [hpendp] at hx'; cases hx'
    · rw [hpend x hx] at hx'
      rw [respsOf_append_ret, hloc x hx, opOf_append_ret]
      simpa [Ne.symm hx] using hI.busy x o' hx'
  · intro a b m hm; exact (hI.msg a b m hm).mono hg _
  · intro x l s c hm
    have := hI.latest x l s c (by
      by_cases hx : x = p
      · subst hx; rw [hlocp] at hm; exact hm
      · rw [hloc x hx] at hm; exact hm)
    exact ⟨this.1.trans (hg.clock l), this.2.mono _⟩
  · intro x
    by_cases hx : x = p
    · subst hx; rw [hlocp]; exact (hI.st x).mono _
    · rw [hloc x hx]; exact (hI.st x).mono _
  · intro x l c hx1 hx2
    by_cases hx : x = p
    · subst hx; rw [hlocp] at hx1; cases hx1
    · rw [hloc x hx] at hx1 hx2 ⊢
      obtain ⟨cu, hcu, h'⟩ := hI.setResps x l c hx1 hx2
      exact ⟨cu, hcu, h'.mono hg⟩
  · intro x c hx1
    by_cases hx : x = p
    · subst hx; rw [hlocp] at hx1; cases hx1
    · rw [hloc x hx] at hx1 ⊢
      obtain ⟨W, hW, hW'⟩ := hI.setWait x c hx1
      refine ⟨W, hW, fun l hl => ?_⟩
      obtain ⟨cu, hcu, h'⟩ := hW' l hl
      exact ⟨cu, hcu, h'.mono hg⟩
  · intro x k h1 h2
    rw [opOf_append_ret] at h1
    simp only [Completed, respsOf_append_ret, List.length_append] at h2
    by_cases hx : x = p ∧ k = (respsOf h p).length
    · obtain ⟨rfl, rfl⟩ := hx
      rw [hb2] at h1
      cases h1
      have := hdone rfl
      rw [← hb1] at this
      exact this.mono RR WW hg
    · have h2' : Completed h (x, k) := by
        simp only [Completed]
        by_cases hpx : p = x
        · subst hpx; simp at h2 hx; omega
        · simpa [hpx] using h2
      exact (hI.setDone x k h1 h2').mono RR WW hg
  · intro q S' hq s hs
    simp only [List.mem_append, List.mem_singleton, Label.ret.injEq] at hq
    rcases hq with hq | ⟨rfl, rfl⟩
    · exact (hI.ret q S' hq s hs).mono _
    · exact (hS s hs).mono _

lemma phaseOK_get {pd : Option QOp} {ph : Phase} (h : PhaseOK pd ph)
    (hph : ph = .getClk ∨ ∃ c, ph = .getWait c) : pd = some .get := by
  rcases hph with rfl | ⟨c, rfl⟩ <;> rcases pd with _ | _ | _ <;> first | rfl | exact h.elim

lemma phaseOK_set {pd : Option QOp} {ph : Phase} (h : PhaseOK pd ph)
    (hph : ph = .setAck ∨ ∃ c, ph = .setWait c) : pd = some .set := by
  rcases hph with rfl | ⟨c, rfl⟩ <;> rcases pd with _ | _ | _ <;> first | rfl | exact h.elim

lemma GetGate.phase {l : QState P} {c : ℕ} (h : GetGate WW l c) :
    l.phase = .getClk ∨ ∃ c, l.phase = .getWait c := by
  rcases h with h | h
  · exact Or.inr ⟨c, h⟩
  · exact Or.inl h.1

lemma SetGate.phase {l : QState P} {c : ℕ} (h : SetGate WW l c) :
    l.phase = .setAck ∨ ∃ c, l.phase = .setWait c := by
  rcases h with h | h
  · exact Or.inr ⟨c, h⟩
  · exact Or.inl h.1

lemma adv_eq {C : Cfg P} {p : P} {l' : QState P} {r : Option (List (Finset (P × ℕ)))}
    (hA : advance RR WW (C.loc p) = (l', r)) :
    adv RR WW C p = ({ C with
      loc := Function.update C.loc p l'
      pend := Function.update C.pend p (pendAfter (C.pend p) r) }, respOut p (C.pend p) r) := by
  simp [adv, hA]

lemma adv_eq_none {C : Cfg P} {p : P} {l' : QState P}
    (hA : advance RR WW (C.loc p) = (l', none)) :
    adv RR WW C p = ({ C with loc := Function.update C.loc p l' }, []) := by
  rw [adv_eq RR WW hA]
  cases hp : C.pend p <;> simp [pendAfter, respOut, ← hp]

lemma adv_eq_some {C : Cfg P} {p : P} {l' : QState P} {S : List (Finset (P × ℕ))} {o : QOp}
    (hA : advance RR WW (C.loc p) = (l', some S)) (hp : C.pend p = some o) :
    adv RR WW C p = ({ C with
      loc := Function.update C.loc p l'
      pend := Function.update C.pend p none }, [.ret p S]) := by
  rw [adv_eq RR WW hA, hp]; rfl

variable {RR WW} in
lemma setW_of_gate {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) {p : P} {c : ℕ}
    (hgate : SetGate WW (C.loc p) c) :
    ∃ W ∈ WW, ∀ l ∈ W, ∃ cu ≤ c, GRP C l (p, (C.loc p).seq) cu := by
  rcases hgate with hg | ⟨hg, W, hW, hW'⟩
  · exact hI.setWait p c hg
  · refine ⟨W, hW, fun l hl => ?_⟩
    obtain ⟨c', hc', hle⟩ := hW' l hl
    obtain ⟨cu, hcu, h'⟩ := hI.setResps p l c' hg hc'
    exact ⟨cu, hcu.trans hle, h'⟩

variable {RR WW} in
/-- If `C.loc p` passes the write-quorum wait of a `quorum_set` with bound `c` (Lemma 1's
`c_set`) and a read quorum has clocks `≥ c`, then the update of `p` is `SetDone`. -/
lemma setDone_of_gate {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) {p : P} {c : ℕ}
    (hgate : SetGate WW (C.loc p) c) {R : Set P} (hR : R ∈ RR) (hread : ReadOK (C.loc p) c R) :
    SetDone RR WW C p (C.loc p).seq := by
  refine ⟨c, setW_of_gate hI hgate, R, hR, fun i hi => ?_⟩
  · obtain ⟨s, c', h1, h2⟩ := hread i hi
    exact h2.trans (hI.latest p i s c' h1).1

variable {RR WW} in
lemma inv_adv {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) (p : P) :
    Inv RR WW (adv RR WW C p).1 (h ++ (adv RR WW C p).2) := by
  rcases advance_spec RR WW (C.loc p) with hA | ⟨c, hc, hgate, hA⟩ | ⟨c, hc, hgate, hA⟩ |
      ⟨c, hgate, R, hR, hread, S, hS1, hS2, hA⟩ | ⟨c, hgate, R, hR, hread, hA⟩
  · rw [adv_eq_none RR WW hA]
    simp only [Function.update_eq_self, List.append_nil]
    exact hI
  · rw [adv_eq_none RR WW hA, List.append_nil]
    have hpd := phaseOK_get (hI.phase p) (Or.inl hc)
    refine inv_phase hI p (.getWait c) (by rw [hpd]; trivial) (fun h => by cases h)
      (fun c h => by cases h)
  · rw [adv_eq_none RR WW hA, List.append_nil]
    have hpd := phaseOK_set (hI.phase p) (Or.inl hc)
    refine inv_phase hI p (.setWait c) (by rw [hpd]; trivial) (fun h => by cases h) ?_
    intro c' hc'
    cases hc'
    exact setW_of_gate hI hgate
  · have hpd := phaseOK_get (hI.phase p) hgate.phase
    rw [adv_eq_some RR WW hA hpd]
    refine inv_ret hI p .get hpd S (fun h => by cases h) ?_
    intro s hs
    obtain ⟨x, c', hx⟩ := hS2 s hs
    exact (hI.latest p x s c' hx).2
  · have hpd := phaseOK_set (hI.phase p) hgate.phase
    rw [adv_eq_some RR WW hA hpd]
    exact inv_ret hI p .set hpd [] (fun _ => setDone_of_gate hI hgate hR hread) (by simp)

/-! ### The global invariant holds in every reachable configuration -/

lemma inv_init : Inv RR WW (qaAlg RR WW).initCfg [] := by
  constructor
  · intro p; trivial
  · intro p; rfl
  · intro p _; rfl
  · intro p o h; cases h
  · intro a b m h; cases h
  · intro x l s c h; cases h
  · intro l u hu; cases hu
  · intro p l c h; cases h
  · intro p c h; cases h
  · intro p k h; simp [opOf] at h
  · intro q S h; cases h

variable {RR WW} in
lemma inv_step {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) (e : Event P (qaObj P)) :
    Inv RR WW ((qaAlg RR WW).step C e).1 (h ++ ((qaAlg RR WW).step C e).2) := by
  rcases step_cases RR WW C e with heq | ⟨p, o, hp, heq⟩ | ⟨p, c, heq⟩ |
      ⟨q, p, m, rest, hc, heq⟩ <;> rw [heq]
  · simpa using hI
  · rw [← List.singleton_append, ← List.append_assoc]
    exact inv_adv (inv_invoke hI hp o) p
  · exact inv_adv (inv_tick hI p c) p
  · exact inv_adv (inv_deliver hI hc) p

variable {RR WW} in
lemma inv_run (E : List (Event P (qaObj P))) {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h) :
    Inv RR WW ((qaAlg RR WW).run C E) (h ++ (qaAlg RR WW).hist C E) := by
  induction E generalizing C h with
  | nil => simpa using hI
  | cons e E ih =>
    simp only [Algorithm.run_cons, Algorithm.hist_cons, ← List.append_assoc]
    exact ih (inv_step hI e)

lemma inv_reachable (E : List (Event P (qaObj P))) :
    Inv RR WW ((qaAlg RR WW).run (qaAlg RR WW).initCfg E)
      ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E) := by
  simpa using inv_run E (inv_init RR WW)

/-! ### The invariant for real-time ordering -/

/-- The invariant used for Theorem 3, from the completion of a `quorum_set` with update `u`
(write quorum `W0` applied `u` at clocks `≤ c0`, read quorum `R0` has clocks `≥ c0`) on, for the
`j`-th operation of `q`, invoked after that completion. -/
structure RInv (q : P) (j : ℕ) (u : P × ℕ) (c0 : ℕ) (R0 W0 : Set P) (C : Cfg P) (h : Hist P) :
    Prop where
  clk : ∀ i ∈ R0, c0 ≤ (C.loc i).clock
  grp : ∀ l ∈ W0, ∃ cu ≤ c0, GRP C l u cu
  chan : (C.loc q).seq = j + 1 → ∀ i ∈ R0, ∀ c, QMsg.clockResp (j + 1) c ∈ C.chan i q → c0 ≤ c
  resps : (C.loc q).seq = j + 1 → (C.loc q).phase = .getClk → ∀ i ∈ R0, ∀ c,
    (C.loc q).clockResps i = some c → c0 ≤ c
  wait : (C.loc q).seq = j + 1 → ∀ c, (C.loc q).phase = .getWait c → c0 ≤ c
  done : opOf h (q, j) = some .get → ∀ S, respOf h (q, j) = some S → ∃ s ∈ S, u ∈ s

variable {q : P} {j : ℕ} {u : P × ℕ} {c0 : ℕ} {R0 W0 : Set P}

lemma RInv.mono_grows {C C' : Cfg P} {h : Hist P} (hR : RInv q j u c0 R0 W0 C h)
    (hg : Grows C C') :
    (∀ i ∈ R0, c0 ≤ (C'.loc i).clock) ∧ (∀ l ∈ W0, ∃ cu ≤ c0, GRP C' l u cu) :=
  ⟨fun i hi => (hR.clk i hi).trans (hg.clock i), fun l hl => by
    obtain ⟨cu, hcu, h'⟩ := hR.grp l hl; exact ⟨cu, hcu, h'.mono hg⟩⟩

lemma RInv.done_of_noret {RR WW : Set (Set P)} {C : Cfg P} {h : Hist P}
    (hI : Inv RR WW C h) (hR : RInv q j u c0 R0 W0 C h) (ls : Hist P)
    (hls : respOf (h ++ ls) (q, j) = respOf h (q, j)) :
    opOf (h ++ ls) (q, j) = some .get → ∀ S, respOf (h ++ ls) (q, j) = some S →
      ∃ s ∈ S, u ∈ s := by
  intro h1 S h2
  rw [hls] at h2
  rw [hI.opOf_of_completed (Completed.of_respOf_eq_some h2)] at h1
  exact hR.done h1 S h2

lemma RInv.gate_le {RR WW : Set (Set P)} (hcons : ∀ R ∈ RR, ∀ W ∈ WW, (R ∩ W).Nonempty)
    (hR0 : R0 ∈ RR) {C : Cfg P} {h : Hist P} (hR : RInv q j u c0 R0 W0 C h)
    (hseq : (C.loc q).seq = j + 1) {c : ℕ} (hg : GetGate WW (C.loc q) c) : c0 ≤ c := by
  rcases hg with hg | ⟨hg, W, hW, hW'⟩
  · exact hR.wait hseq c hg
  · obtain ⟨i, hi1, hi2⟩ := hcons R0 hR0 W hW
    obtain ⟨c', hc', hle⟩ := hW' i hi2
    exact (hR.resps hseq hg i hi1 c' hc').trans hle

lemma rinv_mid {C : Cfg P} {h : Hist P} (hR : RInv q j u c0 R0 W0 C h)
    {C₀ : Cfg P} (hloc : C₀.loc = C.loc)
    (hchan : ∀ a b m, m ∈ C₀.chan a b → m ∈ C.chan a b)
    {p : P} {l0 : QState P} {out : List (P × QMsg P)} (hg : Grows C (mid C₀ p l0 out))
    (hph : l0.phase = (C.loc p).phase) (hseq : l0.seq = (C.loc p).seq)
    (hcr : p = q → l0.seq = j + 1 → l0.phase = .getClk → ∀ i ∈ R0, ∀ c,
      l0.clockResps i = some c → c0 ≤ c)
    (hout : ∀ c, QMsg.clockResp (j + 1) c ∈ msgsTo out q → p ∈ R0 → c0 ≤ c) :
    RInv q j u c0 R0 W0 (mid C₀ p l0 out) h := by
  obtain ⟨h1, h2⟩ := hR.mono_grows hg
  have hsq : ((mid C₀ p l0 out).loc q).seq = (C.loc q).seq := by
    by_cases hq : q = p
    · subst hq; simp [hseq]
    · simp [hq, hloc]
  refine ⟨h1, h2, ?_, ?_, ?_, hR.done⟩
  · intro hs i hi c hm
    rw [hsq] at hs
    rcases mem_mid_chan.1 hm with hm1 | ⟨rfl, hm2⟩
    · exact hR.chan hs i hi c (hchan _ _ _ hm1)
    · exact hout c hm2 hi
  · intro hs hp i hi c hc
    by_cases hq : q = p
    · subst hq
      rw [mid_loc, ite_eq_left rfl] at hs hp hc
      exact hcr rfl hs hp i hi c hc
    · simp only [mid_loc, ite_eq_right hq, hloc] at hs hp hc
      exact hR.resps hs hp i hi c hc
  · intro hs c hp
    by_cases hq : q = p
    · subst hq
      rw [mid_loc, ite_eq_left rfl] at hs hp
      rw [hph] at hp; rw [hseq] at hs
      exact hR.wait hs c hp
    · simp only [mid_loc, ite_eq_right hq, hloc] at hs hp
      exact hR.wait hs c hp

lemma rinv_tick {C : Cfg P} {h : Hist P}
    (hR : RInv q j u c0 R0 W0 C h) (p : P) (c : ℕ) :
    RInv q j u c0 R0 W0 (mid C p (pre (C.loc p) (.tick c)).1 (pre (C.loc p) (.tick c)).2) h := by
  have hg : Grows C (mid C p (pre (C.loc p) (.tick c)).1 (pre (C.loc p) (.tick c)).2) :=
    grows_mid rfl (fun _ _ _ h => h) p _ _ subset_rfl (by simp [pre]) le_rfl
      (by simp only [pre, msgsTo_bcast, List.mem_singleton, QMsg.getResp.injEq]
          rintro b s c' ⟨rfl, rfl⟩; exact subset_rfl) (fun l s c h => Or.inl h)
  refine rinv_mid hR rfl (fun _ _ _ h => h) hg rfl rfl ?_ ?_
  · rintro rfl hs hp i hi c' hc'; exact hR.resps hs hp i hi c' hc'
  · intro c' hm; simp [pre] at hm

lemma rinv_deliver {C : Cfg P} {h : Hist P}
    (hR : RInv q j u c0 R0 W0 C h) {a p : P} {m : QMsg P} {rest : List (QMsg P)}
    (hc : C.chan a p = m :: rest) :
    RInv q j u c0 R0 W0 (mid (C.pop a p rest) p (pre (C.loc p) (.recv a m)).1
      (pre (C.loc p) (.recv a m)).2) h := by
  have hsub := pop_chan_sub hc
  have hsame : ∀ {l0 : QState P}, l0.seq = (C.loc p).seq → l0.phase = (C.loc p).phase →
      l0.clockResps = (C.loc p).clockResps → p = q → l0.seq = j + 1 → l0.phase = .getClk →
      ∀ i ∈ R0, ∀ c, l0.clockResps i = some c → c0 ≤ c := by
    rintro l0 h1 h2 h3 rfl hs hp i hi c hc
    rw [h1] at hs; rw [h2] at hp; rw [h3] at hc
    exact hR.resps hs hp i hi c hc
  have hgen : ∀ l0 : QState P, ∀ out : List (P × QMsg P), (C.loc p).st ⊆ l0.st →
      (C.loc p).clock ≤ l0.clock → l0.seq = (C.loc p).seq → l0.phase = (C.loc p).phase →
      (∀ b s c, QMsg.getResp s c ∈ msgsTo out b → (C.loc p).st ⊆ s) →
      (∀ l s c, l0.latest l = some (s, c) →
        (C.loc p).latest l = some (s, c) ∨ QMsg.getResp s c ∈ C.chan l p) →
      (p = q → l0.seq = j + 1 → l0.phase = .getClk → ∀ i ∈ R0, ∀ c,
        l0.clockResps i = some c → c0 ≤ c) →
      (∀ c, QMsg.clockResp (j + 1) c ∈ msgsTo out q → p ∈ R0 → c0 ≤ c) →
      RInv q j u c0 R0 W0 (mid (C.pop a p rest) p l0 out) h := by
    intro l0 out h1 h2 h3 h4 h5 h6 h7 h8
    have hg := grows_mid (C := C) (C₀ := C.pop a p rest) rfl hsub p l0 out h1 h2 h3.ge h5 h6
    exact rinv_mid hR (C₀ := C.pop a p rest) rfl hsub hg h4 h3 h7 h8
  cases m with
  | clockReq k =>
    refine hgen _ _ subset_rfl le_rfl rfl rfl (by intro b s c h; simp [pre] at h)
      (fun l s c h => Or.inl h) (hsame rfl rfl rfl) ?_
    intro c hm hp
    simp only [pre, msgsTo_single] at hm
    split_ifs at hm with hb
    · simp only [List.mem_singleton, QMsg.clockResp.injEq] at hm
      rw [hm.2]; exact hR.clk p hp
    · simp at hm
  | clockResp k c =>
    simp only [pre]
    split_ifs with hk
    · refine hgen _ [] subset_rfl le_rfl rfl rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
        ?_ (by simp [msgsTo])
      rintro rfl hs hp i hi c' hc'
      by_cases hi' : i = a
      · subst hi'
        simp only [Function.update_self, Option.some.injEq] at hc'
        subst hc'
        have hs' : (C.loc p).seq = j + 1 := hs
        refine hR.chan hs' i hi _ ?_
        rw [hc, hk.1, hs']; exact List.mem_cons_self ..
      · simp only [Function.update_of_ne hi'] at hc'
        exact hR.resps hs hp i hi c' hc'
    · exact hgen _ [] subset_rfl le_rfl rfl rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
        (hsame rfl rfl rfl) (by simp [msgsTo])
  | getResp s c =>
    simp only [pre]
    split_ifs with hk
    · refine hgen _ [] subset_rfl le_rfl rfl rfl (by simp [msgsTo]) ?_
        (hsame rfl rfl rfl) (by simp [msgsTo])
      intro l s' c' h'
      by_cases hl : l = a
      · subst hl
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact Or.inr (by rw [hc]; exact List.mem_cons_self ..)
      · simp only [Function.update_of_ne hl] at h'
        exact Or.inl h'
    · exact hgen _ [] subset_rfl le_rfl rfl rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
        (hsame rfl rfl rfl) (by simp [msgsTo])
  | setReq k =>
    exact hgen _ _ (by simp [pre]) (by simp [pre]) rfl rfl (by intro b s c h; simp [pre] at h)
      (fun l s c h => Or.inl h) (hsame rfl rfl rfl) (by intro c h; simp [pre] at h)
  | setResp k c =>
    simp only [pre]
    split_ifs with hk
    · exact hgen _ [] subset_rfl le_rfl rfl rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
        (hsame rfl rfl rfl) (by simp [msgsTo])
    · exact hgen _ [] subset_rfl le_rfl rfl rfl (by simp [msgsTo]) (fun l s c h => Or.inl h)
        (hsame rfl rfl rfl) (by simp [msgsTo])

lemma rinv_invoke_gen {RR WW : Set (Set P)} {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h)
    (hR : RInv q j u c0 R0 W0 C h) {p : P} (o : QOp) (l0 : QState P)
    (out : List (P × QMsg P)) (hst : l0.st = (C.loc p).st)
    (hclock : l0.clock = (C.loc p).clock) (hseq : l0.seq = (C.loc p).seq + 1)
    (hlat : l0.latest = (C.loc p).latest)
    (hcr : l0.phase = .getClk → ∀ i, l0.clockResps i = none) (hgw : ∀ c, l0.phase ≠ .getWait c)
    (hout : ∀ b m, m ∈ msgsTo out b →
      m = .clockReq ((C.loc p).seq + 1) ∨ (o = .set ∧ m = .setReq ((C.loc p).seq + 1))) :
    RInv q j u c0 R0 W0 (mid { C with pend := Function.update C.pend p (some o) } p l0 out)
      (h ++ [.inv p o]) := by
  have hg : Grows C (mid { C with pend := Function.update C.pend p (some o) } p l0 out) :=
    grows_mid (C := C) (C₀ := { C with pend := Function.update C.pend p (some o) }) rfl
      (fun _ _ _ h => h) p l0 out (by rw [hst]) (by rw [hclock]) (by rw [hseq]; omega)
      (by intro b s c hm; rcases hout b _ hm with h | ⟨-, h⟩ <;> cases h)
      (by intro l s c h; rw [hlat] at h; exact Or.inl h)
  obtain ⟨h1, h2⟩ := hR.mono_grows hg
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · intro hs i hi c hm
    rcases mem_mid_chan.1 hm with hm1 | ⟨rfl, hm2⟩
    · by_cases hq : q = p
      · subst hq
        rw [mid_loc, ite_eq_left rfl, hseq] at hs
        have := hI.msg i q _ hm1
        simp only [MsgOK] at this
        omega
      · rw [mid_loc, ite_eq_right hq] at hs
        exact hR.chan hs i hi c hm1
    · rcases hout q _ hm2 with h | ⟨-, h⟩ <;> cases h
  · intro hs hp i hi c hc
    by_cases hq : q = p
    · subst hq
      rw [mid_loc, ite_eq_left rfl] at hs hp hc
      rw [hcr hp i] at hc; cases hc
    · rw [mid_loc, ite_eq_right hq] at hs hp hc
      exact hR.resps hs hp i hi c hc
  · intro hs c hp
    by_cases hq : q = p
    · subst hq
      rw [mid_loc, ite_eq_left rfl] at hp
      exact absurd hp (hgw c)
    · rw [mid_loc, ite_eq_right hq] at hs hp
      exact hR.wait hs c hp
  · exact hR.done_of_noret hI _ (respOf_append_of_not_ret (by intro p r h; cases h) _)

lemma rinv_invoke {RR WW : Set (Set P)} {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h)
    (hR : RInv q j u c0 R0 W0 C h) (p : P) (o : QOp) :
    RInv q j u c0 R0 W0 (mid { C with pend := Function.update C.pend p (some o) } p
      (pre (C.loc p) (.invoke o)).1 (pre (C.loc p) (.invoke o)).2) (h ++ [.inv p o]) := by
  cases o with
  | get =>
    refine rinv_invoke_gen hI hR _ _ _ rfl rfl rfl rfl (fun _ _ => rfl) (fun c h => by cases h) ?_
    intro b m hm; simp only [pre, msgsTo_bcast, List.mem_singleton] at hm; exact Or.inl hm
  | set =>
    refine rinv_invoke_gen hI hR _ _ _ rfl rfl rfl rfl (fun h => by cases h)
      (fun c h => by cases h) ?_
    intro b m hm; simp only [pre, msgsTo_bcast, List.mem_singleton] at hm; exact Or.inr ⟨rfl, hm⟩

lemma rinv_phase {C : Cfg P} {h : Hist P} (hR : RInv q j u c0 R0 W0 C h) (p : P) (ph : Phase)
    (pd : P → Option QOp) (ls : Hist P)
    (hw : p = q → (C.loc q).seq = j + 1 → ∀ c, ph = .getWait c → c0 ≤ c)
    (hc : p = q → ph = .getClk → (C.loc p).phase = .getClk)
    (hdone : opOf (h ++ ls) (q, j) = some .get → ∀ S, respOf (h ++ ls) (q, j) = some S →
      ∃ s ∈ S, u ∈ s) :
    RInv q j u c0 R0 W0
      { C with loc := Function.update C.loc p { C.loc p with phase := ph }, pend := pd }
      (h ++ ls) := by
  have hg := grows_phase C p ph pd
  obtain ⟨h1, h2⟩ := hR.mono_grows hg
  refine ⟨h1, h2, ?_, ?_, ?_, hdone⟩
  · intro hs i hi c hm
    have : (C.loc q).seq = j + 1 := by
      by_cases hq : q = p
      · subst hq; simpa using hs
      · simpa [hq] using hs
    exact hR.chan this i hi c hm
  · intro hs hp i hi c hcr
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self] at hs hp hcr
      exact hR.resps hs (hc rfl hp) i hi c hcr
    · simp only [Function.update_of_ne hq] at hs hp hcr
      exact hR.resps hs hp i hi c hcr
  · intro hs c hp
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self] at hs hp
      exact hw rfl hs c hp
    · simp only [Function.update_of_ne hq] at hs hp
      exact hR.wait hs c hp

lemma respOf_append_ret_cases {h : Hist P} {p : P} {S S' : List (Finset (P × ℕ))} {x : P × ℕ}
    (hx : respOf (h ++ [Label.ret p S]) x = some S') :
    respOf h x = some S' ∨ (p = x.1 ∧ x.2 = (respsOf h x.1).length ∧ S' = S) := by
  obtain ⟨y, k⟩ := x
  simp only [respOf, respsOf_append_ret] at hx ⊢
  by_cases hp : p = y
  · subst hp
    simp only at hx
    rcases lt_trichotomy k (respsOf h p).length with hk | rfl | hk
    · left; rwa [List.getElem?_append_left hk] at hx
    · right; simp at hx; exact ⟨rfl, rfl, hx.symm⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at hx; cases hx
  · left; simpa [hp] using hx

lemma rinv_adv {RR WW : Set (Set P)} (hcons : ∀ R ∈ RR, ∀ W ∈ WW, (R ∩ W).Nonempty)
    (hR0 : R0 ∈ RR) (hW0 : W0 ∈ WW) {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h)
    (hR : RInv q j u c0 R0 W0 C h) (p : P) :
    RInv q j u c0 R0 W0 (adv RR WW C p).1 (h ++ (adv RR WW C p).2) := by
  rcases advance_spec RR WW (C.loc p) with hA | ⟨c, hc, hgate, hA⟩ | ⟨c, hc, hgate, hA⟩ |
      ⟨c, hgate, R, hRR, hread, S, hS1, hS2, hA⟩ | ⟨c, hgate, R, hRR, hread, hA⟩
  · rw [adv_eq_none RR WW hA]
    simp only [Function.update_eq_self, List.append_nil]
    exact hR
  · rw [adv_eq_none RR WW hA]
    refine rinv_phase hR p (.getWait c) C.pend [] ?_ (fun _ h => by cases h)
      (by simpa using hR.done)
    rintro rfl hs c' h; cases h
    exact hR.gate_le hcons hR0 hs hgate
  · rw [adv_eq_none RR WW hA]
    exact rinv_phase hR p (.setWait c) C.pend [] (fun _ _ _ h => by cases h)
      (fun _ h => by cases h) (by simpa using hR.done)
  · have hpd := phaseOK_get (hI.phase p) hgate.phase
    rw [adv_eq_some RR WW hA hpd]
    refine rinv_phase hR p .idle _ _ (fun _ _ _ h => by cases h) (fun _ h => by cases h) ?_
    intro h1 S' h2
    rw [opOf_append_ret] at h1
    rcases respOf_append_ret_cases h2 with h2 | ⟨rfl, hj, rfl⟩
    · exact hR.done h1 S' h2
    · simp only at hj
      obtain ⟨hb1, -⟩ := hI.busy p .get hpd
      have hc0 := hR.gate_le hcons hR0 (by omega) hgate
      obtain ⟨l, hl1, hl2⟩ := hcons R hRR W0 hW0
      obtain ⟨s, c', hs, hcc⟩ := hread l hl1
      obtain ⟨cu, hcu, hgrp⟩ := hR.grp l hl2
      exact ⟨s, hS1 l hl1 s c' hs, hgrp.2.2.2 p s c' hs (by omega)⟩
  · have hpd := phaseOK_set (hI.phase p) hgate.phase
    rw [adv_eq_some RR WW hA hpd]
    refine rinv_phase hR p .idle _ _ (fun _ _ _ h => by cases h) (fun _ h => by cases h) ?_
    intro h1 S' h2
    rw [opOf_append_ret] at h1
    rcases respOf_append_ret_cases h2 with h2 | ⟨rfl, hj, rfl⟩
    · exact hR.done h1 S' h2
    · simp only at hj
      obtain ⟨-, hb2⟩ := hI.busy p .set hpd
      rw [← hj, h1] at hb2; cases hb2

lemma rinv_step {RR WW : Set (Set P)} (hcons : ∀ R ∈ RR, ∀ W ∈ WW, (R ∩ W).Nonempty)
    (hR0 : R0 ∈ RR) (hW0 : W0 ∈ WW) {C : Cfg P} {h : Hist P} (hI : Inv RR WW C h)
    (hR : RInv q j u c0 R0 W0 C h) (e : Event P (qaObj P)) :
    RInv q j u c0 R0 W0 ((qaAlg RR WW).step C e).1 (h ++ ((qaAlg RR WW).step C e).2) := by
  rcases step_cases RR WW C e with heq | ⟨p, o, hp, heq⟩ | ⟨p, c, heq⟩ |
      ⟨a, p, m, rest, hc, heq⟩ <;> rw [heq]
  · simpa using hR
  · rw [← List.singleton_append, ← List.append_assoc]
    exact rinv_adv hcons hR0 hW0 (inv_invoke hI hp o) (rinv_invoke hI hR p o) p
  · exact rinv_adv hcons hR0 hW0 (inv_tick hI p c) (rinv_tick hR p c) p
  · exact rinv_adv hcons hR0 hW0 (inv_deliver hI hc) (rinv_deliver hR hc) p

lemma rinv_run {RR WW : Set (Set P)} (hcons : ∀ R ∈ RR, ∀ W ∈ WW, (R ∩ W).Nonempty)
    (hR0 : R0 ∈ RR) (hW0 : W0 ∈ WW) (E : List (Event P (qaObj P))) {C : Cfg P} {h : Hist P}
    (hI : Inv RR WW C h) (hR : RInv q j u c0 R0 W0 C h) :
    RInv q j u c0 R0 W0 ((qaAlg RR WW).run C E) (h ++ (qaAlg RR WW).hist C E) := by
  induction E generalizing C h with
  | nil => simpa using hR
  | cons e E ih =>
    simp only [Algorithm.run_cons, Algorithm.hist_cons, ← List.append_assoc]
    exact ih (inv_step hI e) (rinv_step hcons hR0 hW0 hI hR e)

/-! ### Splitting an execution at a real-time precedence -/

lemma respsOf_respOut {A : ObjSpec} (p : P) (o : Option A.Op) (r : Option A.Resp) :
    (respOut p o r).length ≤ 1 := by
  rcases o with _ | o <;> rcases r with _ | r <;> simp [respOut]

lemma step_labels_shape (C : Cfg P) (e : Event P (qaObj P)) :
    ∃ pre post : Hist P, ((qaAlg RR WW).step C e).2 = pre ++ post ∧ post.length ≤ 1 ∧
      ∀ x, respsOf pre x = [] := by
  rcases step_cases RR WW C e with heq | ⟨p, o, hp, heq⟩ | ⟨p, c, heq⟩ |
      ⟨a, p, m, rest, hc, heq⟩ <;> rw [heq]
  · exact ⟨[], [], rfl, by simp, fun _ => rfl⟩
  · exact ⟨[.inv p o], _, rfl, respsOf_respOut _ _ _, fun x => by simp⟩
  · exact ⟨[], _, rfl, respsOf_respOut _ _ _, fun _ => rfl⟩
  · exact ⟨[], _, rfl, respsOf_respOut _ _ _, fun _ => rfl⟩

lemma precedes_split (C : Cfg P) (E : List (Event P (qaObj P))) {a b : OpId P}
    (hp : Precedes ((qaAlg RR WW).hist C E) a b) :
    ∃ E₁ E₂, E = E₁ ++ E₂ ∧ Completed ((qaAlg RR WW).hist C E₁) a ∧
      ¬ Invoked ((qaAlg RR WW).hist C E₁) b := by
  induction E using List.reverseRecOn with
  | nil =>
    obtain ⟨β, γ, hβ, h1, -⟩ := hp
    rw [Algorithm.hist_nil, eq_comm, List.append_eq_nil_iff] at hβ
    rw [hβ.1] at h1
    simp [Completed] at h1
  | append_singleton E e ih =>
    obtain ⟨β, γ, hβ, h1, h2⟩ := hp
    rw [Algorithm.hist_append, Algorithm.hist_cons, Algorithm.hist_nil, List.append_nil,
      eq_comm, List.append_eq_append_iff] at hβ
    rcases hβ with ⟨a', hE, -⟩ | ⟨c', rfl, hls⟩
    · obtain ⟨E₁, E₂, rfl, h3, h4⟩ := ih ⟨β, a', hE, h1, h2⟩
      exact ⟨E₁, E₂ ++ [e], by simp, h3, h4⟩
    · by_cases hγ : γ = []
      · subst hγ
        refine ⟨E ++ [e], [], by simp, ?_, ?_⟩ <;>
          rw [Algorithm.hist_append, Algorithm.hist_cons, Algorithm.hist_nil, List.append_nil]
        · simpa [hls] using h1
        · simpa [hls] using h2
      · refine ⟨E, [e], rfl, ?_, fun h => h2 h.mono⟩
        obtain ⟨pre, post, hpp, hpost, hpre⟩ := step_labels_shape RR WW
          ((qaAlg RR WW).run C E) e
        rw [hpp, eq_comm, List.append_eq_append_iff] at hls
        have hc' : ∀ x, respsOf c' x = [] := by
          rcases hls with ⟨a'', rfl, -⟩ | ⟨c'', rfl, hpost'⟩
          · intro x; have := hpre x; simp only [respsOf_append, List.append_eq_nil_iff] at this
            exact this.1
          · have : c'' = [] := by
              rw [hpost'] at hpost; simp only [List.length_append] at hpost
              have : γ.length ≠ 0 := by simpa using hγ
              exact List.length_eq_zero_iff.1 (by omega)
            subst this; simpa using hpre
        simpa [Completed, hc'] using h1

/-! ### Main theorems -/

/-- **Theorem 3 (Real-time ordering)**, with Lemma 1. In every finite execution, if a
`quorum_set` (the `k`-th operation of `p`) completes before a `quorum_get` (the `j`-th operation of
`q`) is invoked, then one of the states returned by the `quorum_get` has incorporated the
update of the `quorum_set`. Only Consistency of the quorum families is used. -/
theorem realtime_ordering (hcons : ∀ R ∈ RR, ∀ W ∈ WW, (R ∩ W).Nonempty)
    (E : List (Event P (qaObj P))) {p q : P} {k j : ℕ} {S : List (Finset (P × ℕ))}
    (hset : opOf ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E) (p, k) = some .set)
    (hget : opOf ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E) (q, j) = some .get)
    (hpre : Precedes ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E) (p, k) (q, j))
    (hS : respOf ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E) (q, j) = some S) :
    ∃ s ∈ S, (p, k + 1) ∈ s := by
  obtain ⟨E₁, E₂, rfl, h1, h2⟩ := precedes_split RR WW _ E hpre
  have hI := inv_reachable RR WW E₁
  rw [Algorithm.hist_append] at hset hget hS
  have hset₁ : opOf ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E₁) (p, k) = some .set := by
    rwa [hI.opOf_of_completed h1] at hset
  obtain ⟨c0, ⟨W0, hW0, hgrp⟩, ⟨R0, hR0, hclk⟩⟩ := hI.setDone p k hset₁ h1
  have hseq : (((qaAlg RR WW).run (qaAlg RR WW).initCfg E₁).loc q).seq ≤ j := by
    rw [← hI.seq q]; simpa [Invoked] using h2
  have hR : RInv q j (p, k + 1) c0 R0 W0 ((qaAlg RR WW).run (qaAlg RR WW).initCfg E₁)
      ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E₁) :=
    ⟨hclk, hgrp, fun hs => by omega, fun hs => by omega, fun hs => by omega,
      fun ho => absurd (Invoked.of_opOf_eq_some ho) h2⟩
  exact (rinv_run hcons hR0 hW0 E₂ hI hR).done hget S hS

/-- **Validity** of the quorum access functions: every state returned by a `quorum_get` consists
of updates of previously invoked `quorum_set`s. -/
theorem validity (E : List (Event P (qaObj P))) {q : P} {S : List (Finset (P × ℕ))}
    (hlast : ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E).getLast? = some (.ret q S)) :
    ∀ s ∈ S, ∀ u ∈ s, ∃ k, u.2 = k + 1 ∧
      opOf ((qaAlg RR WW).hist (qaAlg RR WW).initCfg E) (u.1, k) = some .set :=
  (inv_reachable RR WW E).ret q S (List.mem_of_getLast? hlast)

end Podc.GeneralizedQuorums.QA
