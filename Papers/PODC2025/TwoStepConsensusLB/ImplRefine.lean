import Papers.PODC2025.TwoStepConsensusLB.ImplSelect
import Papers.PODC2025.TwoStepConsensusLB.ImplTwoStep

/-!
# Refinement: every handler of the implementation is a step of the abstract system of Fig. 1

The abstraction of a concrete local state `s` of process `p` is `absLoc cfg p g s` (same Fig. 1
variables; ghost invocation `g`; in the task version `initial_val` is the input). The messages of
the outbox map to abstract messages by `absMsg p`; a message `(q, m)` received by `p` is
`rcvMsg p (q, m)`.

`simSt L M p g s` is the abstract global state in which process `p` is in state `s` (the other
processes in `L`), and the messages are `M` plus those of the outbox of `s`. The main lemmas:
* `sim_handle`: processing one received message (`handle`) is a sequence of abstract steps, and
  the local invariant `LocI` is preserved;
* `sim_timer`, `sim_invoke_obj`, `sim_invoke_task`: the timer and the invocation.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

open Relation

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

section Abs

variable (cfg : Fig1.Config P V)

/-- Abstraction of a local state of `p` with ghost invocation `g`. -/
def absLoc (p : P) (g : Option V) (s : St P V) : Fig1.Loc P V :=
  ⟨s.bal, s.vbal, s.val, s.proposer, s.decided,
    if cfg.ver = .task then some (cfg.input p) else s.initVal, g⟩

/-- Abstraction of an outbox entry of `p`. -/
def absMsg (p : P) : Dest P × Msg P V → Fig1.Msg P V
  | (_, .propose v) => .propose p v
  | (.to r, .twoB b v) => .twoB p r b v
  | (_, .twoB b v) => .twoB p p b v
  | (_, .decide b v) => .decide p b v
  | (_, .oneA b) => .oneA b
  | (_, .oneB b d) => .oneB p b (toSnap d)
  | (_, .twoA b v) => .twoA b v

/-- Abstraction of a message `(sender, content)` received by `p`. -/
def rcvMsg (p : P) : P × Msg P V → Fig1.Msg P V
  | (q, .propose v) => .propose q v
  | (q, .twoB b v) => .twoB q p b v
  | (q, .decide b v) => .decide q b v
  | (_, .oneA b) => .oneA b
  | (q, .oneB b d) => .oneB q b (toSnap d)
  | (_, .twoA b v) => .twoA b v

/-- The abstract state with `p` in state `s`, other processes in `L`, messages `M` and the outbox
of `s`. -/
def simSt (L : P → Fig1.Loc P V) (M : Set (Fig1.Msg P V)) (p : P) (g : Option V)
    (s : St P V) : Fig1.State P V :=
  ⟨Function.update L p (absLoc cfg p g s), M ∪ {m | m ∈ s.out.map (absMsg p)}⟩

variable {cfg}

@[simp] theorem absLoc_bal (p : P) (g : Option V) (s : St P V) :
    (absLoc cfg p g s).bal = s.bal := rfl
@[simp] theorem absLoc_vbal (p : P) (g : Option V) (s : St P V) :
    (absLoc cfg p g s).vbal = s.vbal := rfl
@[simp] theorem absLoc_val (p : P) (g : Option V) (s : St P V) :
    (absLoc cfg p g s).val = s.val := rfl
@[simp] theorem absLoc_proposer (p : P) (g : Option V) (s : St P V) :
    (absLoc cfg p g s).proposer = s.proposer := rfl
@[simp] theorem absLoc_decided (p : P) (g : Option V) (s : St P V) :
    (absLoc cfg p g s).decided = s.decided := rfl
@[simp] theorem absLoc_inv (p : P) (g : Option V) (s : St P V) : (absLoc cfg p g s).inv = g := rfl

theorem state_ext {A B : Fig1.State P V} (h1 : A.loc = B.loc) (h2 : A.msgs = B.msgs) : A = B := by
  cases A; cases B; simp_all

@[simp] theorem simSt_loc_self {L : P → Fig1.Loc P V} {M : Set (Fig1.Msg P V)} {p : P}
    {g : Option V} {s : St P V} : (simSt cfg L M p g s).loc p = absLoc cfg p g s := by
  simp [simSt]

theorem mem_simSt_msgs {L : P → Fig1.Loc P V} {M : Set (Fig1.Msg P V)} {p : P} {g : Option V}
    {s : St P V} {m : Fig1.Msg P V} (h : m ∈ M) : m ∈ (simSt cfg L M p g s).msgs :=
  Or.inl h

theorem simSt_send {L : P → Fig1.Loc P V} {M : Set (Fig1.Msg P V)} {p : P} {g : Option V}
    {s s' : St P V} {dm : Dest P × Msg P V} (h : s'.out = s.out ++ [dm]) :
    simSt cfg L M p g s' =
      ((simSt cfg L M p g s).set p (absLoc cfg p g s')).send (absMsg p dm) := by
  refine state_ext ?_ ?_
  · simp [simSt, Fig1.State.set, Fig1.State.send]
  · ext m
    simp only [simSt, Fig1.State.send, Fig1.State.set, h, List.map_append, List.map_cons,
      List.map_nil, Set.mem_union, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
      Set.mem_insert_iff]
    tauto

theorem simSt_send' {L : P → Fig1.Loc P V} {M : Set (Fig1.Msg P V)} {p : P} {g : Option V}
    {s s' : St P V} {dm : Dest P × Msg P V} (h : s'.out = s.out ++ [dm])
    (h1 : absLoc cfg p g s' = absLoc cfg p g s) :
    simSt cfg L M p g s' = (simSt cfg L M p g s).send (absMsg p dm) := by
  rw [simSt_send h, h1]
  refine state_ext ?_ rfl
  simp [simSt, Fig1.State.set, Fig1.State.send]

theorem simSt_set {L : P → Fig1.Loc P V} {M : Set (Fig1.Msg P V)} {p : P} {g : Option V}
    {s s' : St P V} (h : s'.out = s.out) :
    simSt cfg L M p g s' = (simSt cfg L M p g s).set p (absLoc cfg p g s') := by
  refine state_ext ?_ ?_
  · simp [simSt, Fig1.State.set]
  · simp [simSt, Fig1.State.set, h]

theorem simSt_eq {L : P → Fig1.Loc P V} {M : Set (Fig1.Msg P V)} {p : P} {g : Option V}
    {s s' : St P V} (h1 : absLoc cfg p g s' = absLoc cfg p g s) (h : s'.out = s.out) :
    simSt cfg L M p g s' = simSt cfg L M p g s := by
  simp [simSt, h1, h]

/-- One abstract step. -/
theorem rt_of_step {A B C : Fig1.State P V} {p : P} {k : Fig1.Kind} (h : Fig1.Step cfg p k A B)
    (hB : C = B) : ReflTransGen (Fig1.Next cfg) A C :=
  hB ▸ ReflTransGen.single ⟨p, k, h⟩

end Abs

/-! ### Local invariant and received messages -/

theorem nodup_fst_filter {l : List (P × ℕ × OneB P V)} (h : (l.map fun x => (x.1, x.2.1)).Nodup)
    (b : ℕ) : ((l.filter fun x => x.2.1 = b).map Prod.fst).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.filter_cons]
    split_ifs with hab
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => h.1 ?_, ih h.2⟩
      obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hmem
      rw [List.mem_filter] at hy
      simp only [decide_eq_true_eq] at hy hab
      exact List.mem_map.2 ⟨y, hy.1, by rw [hy1, hy.2, hab]⟩
    · exact ih h.2

/-- Shape of an outbox entry of `p`. -/
structure Shape (c : Cfg P) (p : P) (dm : Dest P × Msg P V) : Prop where
  twoB : ∀ b v, dm.2 = .twoB b v → ∃ r, dm.1 = .to r
  propose : ∀ v, dm.2 = .propose v → dm.1 = .others
  oneB : ∀ b d, dm.2 = .oneB b d → dm.1 = .to (c.owner b)
  twoA : ∀ b w, dm.2 = .twoA b w → c.owner b = p ∧ dm.1 = .all

/-- Local invariant of a concrete state `s` of `p`: the received messages are in `Mr`, and no
`2A` of a ballot owned by `p` is in `M` (or the outbox) unless `p` has `n - f` `1B`s for it. -/
structure LocI (cfg : Fig1.Config P V) (c : Cfg P) (p : P) (Mr M : Set (Fig1.Msg P V))
    (s : St P V) : Prop where
  twoBs : ∀ x ∈ s.twoBs, Fig1.Msg.twoB x.1 p x.2.1 x.2.2 ∈ Mr
  oneBs : ∀ x ∈ s.oneBs, Fig1.Msg.oneB x.1 x.2.1 (toSnap x.2.2) ∈ Mr
  key : (s.oneBs.map fun x => (x.1, x.2.1)).Nodup
  owner : ∀ x ∈ s.oneBs, c.owner x.2.1 = p
  twoA : ∀ b w, c.owner b = p → Fig1.Msg.twoA b w ∈ M ∪ {m | m ∈ s.out.map (absMsg p)} →
    Fintype.card P - c.f ≤ (senders1B s b).card
  shape : ∀ dm ∈ s.out, Shape c p dm

/-- Conditions on a message `(q, m)` received by `p`. -/
structure RcvOK (c : Cfg P) (p : P) (M : Set (Fig1.Msg P V)) (qm : P × Msg P V) : Prop where
  mem : rcvMsg p qm ∈ M
  propose : ∀ v, qm.2 = .propose v → qm.1 ≠ p
  oneB : ∀ b d, qm.2 = .oneB b d → c.owner b = p
  twoA : ∀ b w, qm.2 = .twoA b w → c.owner b = qm.1
  oneA : ∀ b, qm.2 = .oneA b → c.owner b = qm.1

/-- The parameters of the abstract system match those of the implementation. -/
structure Match (cfg : Fig1.Config P V) (c : Cfg P) : Prop where
  e : cfg.e = c.e
  f : cfg.f = c.f
  owner : cfg.owner = c.owner
  mode : (cfg.ver = .task ∧ c.obj = false ∧ cfg.fallbackVal = false) ∨
    (cfg.ver = .object ∧ c.obj = true ∧ cfg.fallbackVal = true)
  hN : 1 ≤ Fintype.card P - c.f - c.e

section Sim

variable {cfg : Fig1.Config P V} {c : Cfg P} (hm : Match cfg c) {L : P → Fig1.Loc P V}
  {Mr M : Set (Fig1.Msg P V)} (hsub : Mr ⊆ M) {p : P} {g : Option V}
include hm hsub

omit hsub in
theorem absLoc_initVal {s : St P V} (hI : cfg.ver = .task → s.initVal = some (cfg.input p)) :
    (absLoc cfg p g s).initVal = s.initVal := by
  simp only [absLoc]
  split_ifs with h
  · exact (hI h).symm
  · rfl

omit hsub in
theorem accepts_iff {s : St P V} (hI : cfg.ver = .task → s.initVal = some (cfg.input p)) (v : V) :
    okProp c.obj s.initVal v = true ↔ Fig1.Accepts cfg.ver (absLoc cfg p g s).initVal v := by
  rw [absLoc_initVal hm hI]
  unfold okProp Fig1.Accepts
  rcases hm.mode with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · rw [h1, h2]
    cases s.initVal <;> simp
  · rw [h1, h2]
    cases s.initVal
    · simp
    · simp only [Option.some.injEq, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        decide_eq_true_eq, forall_const, forall_eq']
      constructor
      · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
      · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩

omit hsub in
theorem leaderIv_eq {s : St P V} (hI : cfg.ver = .task → s.initVal = some (cfg.input p)) :
    Fig1.leaderIv cfg (absLoc cfg p g s) = fallback c s := by
  unfold Fig1.leaderIv fallback
  rw [absLoc_initVal hm hI]
  rcases hm.mode with ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩
  · simp [h2, h3]
  · simp only [h2, h3, ite_true]
    cases s.initVal <;> rfl

/-- The decision handler `tryDecide` (lines 9–13) refines `fastDecide`/`slowDecide`. -/
theorem sim_tryDecide {s : St P V} (hI : LocI cfg c p Mr M s) :
    ReflTransGen (Fig1.Next cfg) (simSt cfg L M p g s) (simSt cfg L M p g (tryDecide c p s)) ∧
      LocI cfg c p Mr M (tryDecide c p s) := by
  unfold tryDecide
  by_cases hd : s.decided = none
  swap
  · simp only [hd, ite_false]; exact ⟨ReflTransGen.refl, hI⟩
  simp only [hd, ite_true]
  split
  swap
  · exact ⟨ReflTransGen.refl, hI⟩
  rename_i x hx
  have hx1 := List.mem_of_find?_eq_some hx
  have hx2 := List.find?_some hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx2
  obtain ⟨hb, hcan⟩ := hx2
  set v := x.2.2
  have hloc : ∀ v', absLoc cfg p g (decideV v' s) =
      { absLoc cfg p g s with val := some v', decided := some v' } := fun _ => rfl
  have hmem : ∀ q ∈ senders2B s s.bal v, Fig1.Msg.twoB q p s.bal v ∈
      (simSt cfg L M p g s).msgs := by
    intro q hq
    simp only [senders2B, List.mem_toFinset, List.mem_map, List.mem_filter] at hq
    obtain ⟨y, ⟨hy, hy2⟩, rfl⟩ := hq
    simp only [decide_eq_true_eq] at hy2
    have := hI.twoBs y hy
    rw [show y.2 = (s.bal, v) from hy2] at this
    exact Or.inl (hsub this)
  have hne : (senders2B s s.bal v).Nonempty := by
    refine ⟨x.1, ?_⟩
    simp only [senders2B, List.mem_toFinset, List.mem_map, List.mem_filter]
    exact ⟨x, ⟨hx1, by simp only [decide_eq_true_eq]; exact Prod.ext hb rfl⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · unfold canDecide at hcan
    split_ifs at hcan with h0
    · simp only [decide_eq_true_eq] at hcan
      refine rt_of_step (Fig1.Step.fastDecide (s := simSt cfg L M p g s) (v := v)
        (senders2B s 0 v) (h0 ▸ hne) (fun q hq => h0 ▸ hmem q (h0 ▸ hq))
        (by rw [hm.e]; exact hcan.1)
        (by simpa using h0) (by simpa using hcan.2)) ?_
      rw [simSt_send (dm := (.others, .decide s.bal v)) rfl, simSt_loc_self, hloc, h0]
      rfl
    · simp only [decide_eq_true_eq] at hcan
      refine rt_of_step (Fig1.Step.slowDecide (s := simSt cfg L M p g s) (p := p) (v := v)
        (senders2B s s.bal v) hne (fun q hq => by simpa using hmem q hq)
        (by rw [hm.f]; exact hcan) (by simpa using h0)) ?_
      rw [simSt_send (dm := (.others, .decide s.bal v)) rfl, simSt_loc_self, hloc]
      rfl
  · refine ⟨hI.twoBs, hI.oneBs, hI.key, hI.owner, fun b w hb' hw => ?_, ?_⟩
    · refine hI.twoA b w hb' ?_
      simp only [decideV, List.map_append, List.map_cons, List.map_nil, Set.mem_union,
        Set.mem_ofPred_eq, List.mem_append, List.mem_singleton] at hw ⊢
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
      · simp [absMsg] at hw
    · intro dm hdm
      simp only [decideV, List.mem_append, List.mem_singleton] at hdm
      rcases hdm with hdm | rfl
      · exact hI.shape dm hdm
      · exact ⟨by simp, by simp, by simp, by simp⟩

omit hm hsub in
theorem LocI.mono_out {s s' : St P V} (hI : LocI cfg c p Mr M s)
    (h2 : s'.twoBs = s.twoBs) (h1 : s'.oneBs = s.oneBs) (dm : Dest P × Msg P V)
    (hout : s'.out = s.out ++ [dm]) (hsh : Shape c p dm) (hA : ∀ b w, dm.2 ≠ .twoA b w) :
    LocI cfg c p Mr M s' := by
  have hs : senders1B s' = senders1B s := by funext b; simp [senders1B, h1]
  refine ⟨h2 ▸ hI.twoBs, h1 ▸ hI.oneBs, h1 ▸ hI.key, h1 ▸ hI.owner,
    fun b w hb hw => ?_, fun d hd => ?_⟩
  · rw [hs]
    refine hI.twoA b w hb ?_
    simp only [hout, List.map_append, List.map_cons, List.map_nil, Set.mem_union,
      Set.mem_ofPred_eq, List.mem_append, List.mem_singleton] at hw ⊢
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · exfalso
      obtain ⟨d, m⟩ := dm
      cases m <;> simp_all [absMsg]
      all_goals (split at hw <;> simp_all)
  · rw [hout, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact hI.shape d hd
    · exact hsh

omit hm hsub in
theorem LocI.of_eq {s s' : St P V} (hI : LocI cfg c p Mr M s)
    (h2 : s'.twoBs = s.twoBs) (h1 : s'.oneBs = s.oneBs) (hout : s'.out = s.out) :
    LocI cfg c p Mr M s' := by
  have hs : senders1B s' = senders1B s := by funext b; simp [senders1B, h1]
  exact ⟨h2 ▸ hI.twoBs, h1 ▸ hI.oneBs, h1 ▸ hI.key, h1 ▸ hI.owner,
    fun b w hb hw => hs ▸ hI.twoA b w hb (hout ▸ hw), hout ▸ hI.shape⟩

/-- Every message handler (without `tryDecide`) refines abstract steps. -/
theorem sim_handleRaw {s : St P V} (hI : LocI cfg c p Mr M s)
    (hiv : cfg.ver = .task → s.initVal = some (cfg.input p)) {qm : P × Msg P V}
    (hr : RcvOK c p Mr qm) :
    ReflTransGen (Fig1.Next cfg) (simSt cfg L M p g s) (simSt cfg L M p g (handleRaw c s qm)) ∧
      LocI cfg c p Mr M (handleRaw c s qm) := by
  obtain ⟨q, m⟩ := qm
  have hmem : rcvMsg p (q, m) ∈ (simSt cfg L M p g s).msgs := Or.inl (hsub hr.mem)
  cases m with
  | propose v =>
    simp only [handleRaw, onPropose]
    split_ifs with h
    · obtain ⟨h1, h2, h3⟩ := h
      refine ⟨rt_of_step (Fig1.Step.recvPropose (s := simSt cfg L M p g s) (p := p) hmem
        (hr.propose v rfl) (by simpa using h1) (by simpa using h2)
        (by rw [simSt_loc_self]; exact (accepts_iff hm hiv v).1 h3)) ?_, ?_⟩
      · rw [simSt_send (dm := (.to q, .twoB 0 v)) rfl, simSt_loc_self]; rfl
      · exact hI.mono_out rfl rfl _ rfl
          ⟨fun _ _ _ => ⟨q, rfl⟩, by simp, by simp, by simp⟩ (by simp)
    · exact ⟨ReflTransGen.refl, hI⟩
  | twoB b v =>
    refine ⟨?_, ?_⟩
    · rw [simSt_eq (s := s) (s' := handleRaw c s (q, .twoB b v)) rfl rfl]
    · refine ⟨fun x hx => ?_, hI.oneBs, hI.key, hI.owner, hI.twoA, hI.shape⟩
      simp only [handleRaw, onTwoB, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hI.twoBs x hx
      · exact hr.mem
  | decide b v =>
    refine ⟨rt_of_step (Fig1.Step.recvDecide (s := simSt cfg L M p g s) (p := p) hmem) ?_,
      hI.of_eq rfl rfl rfl⟩
    rw [simSt_set (s := s) (s' := handleRaw c s (q, .decide b v)) rfl, simSt_loc_self]; rfl
  | oneA b =>
    simp only [handleRaw, onOneA]
    split_ifs with h
    · refine ⟨rt_of_step (Fig1.Step.recv1A (s := simSt cfg L M p g s) (p := p) hmem
        (by simpa using h)) ?_, ?_⟩
      · rw [simSt_send (dm := (.to q, .oneB b ⟨s.vbal, s.val, s.proposer, s.decided⟩)) rfl,
          simSt_loc_self]; rfl
      · exact hI.mono_out rfl rfl _ rfl
          ⟨by simp, by simp, fun b' d h' => by
            simp only [Msg.oneB.injEq] at h'; obtain ⟨rfl, -⟩ := h'
            rw [hr.oneA b rfl], by simp⟩ (by simp)
    · exact ⟨ReflTransGen.refl, hI⟩
  | oneB b d =>
    simp only [handleRaw, onOneB]
    by_cases hq : q ∈ senders1B s b
    · simp only [hq, ite_true]; exact ⟨ReflTransGen.refl, hI⟩
    simp only [hq, ite_false]
    set s1 : St P V := { s with oneBs := s.oneBs ++ [(q, b, d)] } with hs1
    have hown := hr.oneB b d rfl
    have hcard1 : (senders1B s1 b).card = (senders1B s b).card + 1 := by
      rw [senders1B_append, ite_eq_left rfl, Finset.card_insert_of_notMem hq]
    have hI1 : LocI cfg c p Mr M s1 := by
      refine ⟨hI.twoBs, fun x hx => ?_, ?_, fun x hx => ?_,
        fun b' w hb' hw => ?_, hI.shape⟩
      · simp only [hs1, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hI.oneBs x hx
        · exact hr.mem
      · simp only [hs1, List.map_append, List.map_cons, List.map_nil]
        refine List.Nodup.append hI.key (List.nodup_singleton _) ?_
        intro k hk hk'
        rw [List.mem_singleton] at hk'
        subst hk'
        obtain ⟨y, hy, hyk⟩ := List.mem_map.1 hk
        simp only [Prod.mk.injEq] at hyk
        obtain ⟨y1, y2, y3⟩ := y
        simp only at hyk; obtain ⟨rfl, rfl⟩ := hyk
        exact hq (mem_senders1B.2 ⟨y3, hy⟩)
      · simp only [hs1, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hI.owner x hx
        · exact hown
      · exact (hI.twoA b' w hb' hw).trans (Finset.card_le_card (senders1B_mono (s := s) (s' := s1)
          ⟨le_rfl, id, id, id, fun _ h => h, fun _ h => by simp [hs1, h], List.prefix_refl _⟩ b'))
    have hsim1 : simSt cfg L M p g s1 = simSt cfg L M p g s := simSt_eq rfl rfl
    split_ifs with hfire
    · unfold lead
      split
      · rename_i w hw
        -- the abstract `send2A`
        set Lq := quorum1B s1 b with hLq
        have hkeys : Lq.map Prod.fst = (s1.oneBs.filter fun x => x.2.1 = b).map Prod.fst := by
          simp [hLq, quorum1B, Function.comp_def]
        have hnd : (Lq.map Prod.fst).Nodup := by
          rw [hkeys]; exact nodup_fst_filter hI1.key b
        have hQ : (Lq.map Prod.fst).toFinset = senders1B s1 b := by
          rw [hkeys]; rfl
        set rep : P → Fig1.Snap P V := fun q' =>
          match Lq.find? (fun x => x.1 = q') with
          | some x => toSnap x.2
          | none => ⟨0, none, none, none⟩ with hrepdef
        have hrep : ∀ x ∈ Lq, rep x.1 = toSnap x.2 := by
          intro x hx
          have : (Lq.find? fun y => y.1 = x.1).isSome := by
            rw [List.find?_isSome]; exact ⟨x, hx, by simp⟩
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 this
          have hy1 := List.mem_of_find?_eq_some hy
          have hy2 := List.find?_some hy
          simp only [decide_eq_true_eq] at hy2
          have : y = x := List.inj_on_of_nodup_map hnd hy1 hx hy2
          simp only [hrepdef, hy, this]
        have hsel := proposal_select cfg hnd hrep (by rw [hm.f, hm.e]; exact hm.hN)
          (fb := Fig1.leaderIv cfg (absLoc cfg p g s1)) (w := w)
          (by rw [leaderIv_eq hm (s := s1) hiv, hm.f, hm.e]; exact hw)
        rw [hQ] at hsel
        have hno : ∀ w', Fig1.Msg.twoA b w' ∉ (simSt cfg L M p g s1).msgs := by
          intro w' hw'
          have := hI.twoA b w' hown (by rw [hsim1] at hw'; exact hw')
          omega
        refine ⟨?_, ?_⟩
        · rw [← hsim1]
          refine rt_of_step (Fig1.Step.send2A (s := simSt cfg L M p g s1) (p := p) (b := b)
            (senders1B s1 b) rep (by rw [hm.owner]; exact hown) hno
            (by rw [hm.f]; omega) (fun q' hq' => ?_) (by rw [simSt_loc_self]; exact hsel)) ?_
          · rw [← hQ] at hq'
            obtain ⟨x, hx, rfl, hr'⟩ := rep_of_mem_Q hnd hrep hq'
            rw [hr']
            simp only [hLq, quorum1B, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
            obtain ⟨y, ⟨hy, hyb⟩, rfl⟩ := hx
            have := hI1.oneBs y hy
            rw [hyb] at this
            exact Or.inl (hsub this)
          · exact simSt_send' (s := s1) (dm := (.all, .twoA b w)) rfl rfl
        · refine ⟨hI1.twoBs, hI1.oneBs, hI1.key, hI1.owner, fun b' w' hb' hw' => ?_,
            fun dm hdm => ?_⟩
          · simp only [List.map_append, List.map_cons, List.map_nil, Set.mem_union,
              Set.mem_ofPred_eq, List.mem_append, List.mem_singleton] at hw'
            rcases hw' with hw' | hw' | hw'
            · exact hI1.twoA b' w' hb' (Or.inl hw')
            · exact hI1.twoA b' w' hb' (Or.inr hw')
            · simp only [absMsg, Fig1.Msg.twoA.injEq] at hw'
              obtain ⟨rfl, -⟩ := hw'
              show Fintype.card P - c.f ≤ (senders1B s1 b').card
              omega
          · rw [List.mem_append, List.mem_singleton] at hdm
            rcases hdm with hdm | rfl
            · exact hI1.shape dm hdm
            · exact ⟨by simp, by simp, by simp, fun b' w' h' => by
                simp only [Msg.twoA.injEq] at h'; obtain ⟨rfl, -⟩ := h'; exact ⟨hown, rfl⟩⟩
      · exact ⟨by rw [hsim1], hI1⟩
    · exact ⟨by rw [hsim1], hI1⟩
  | twoA b v =>
    simp only [handleRaw, onTwoA]
    split_ifs with h
    · have hq := hr.twoA b v rfl
      refine ⟨rt_of_step (Fig1.Step.recv2A (s := simSt cfg L M p g s) (p := p) hmem
        (by simpa using h)) ?_, ?_⟩
      · rw [simSt_send (dm := (.to q, .twoB b v)) rfl, simSt_loc_self, hm.owner, hq]; rfl
      · exact hI.mono_out rfl rfl _ rfl
          ⟨fun _ _ _ => ⟨q, rfl⟩, by simp, by simp, by simp⟩ (by simp)
    · exact ⟨ReflTransGen.refl, hI⟩

theorem sim_handle {s : St P V} (hI : LocI cfg c p Mr M s)
    (hiv : cfg.ver = .task → s.initVal = some (cfg.input p)) {qm : P × Msg P V}
    (hr : RcvOK c p Mr qm) :
    ReflTransGen (Fig1.Next cfg) (simSt cfg L M p g s) (simSt cfg L M p g (handle c p s qm)) ∧
      LocI cfg c p Mr M (handle c p s qm) := by
  obtain ⟨h1, h2⟩ := sim_handleRaw hm hsub (L := L) (g := g) hI hiv hr
  obtain ⟨h3, h4⟩ := sim_tryDecide hm hsub (L := L) (g := g) h2
  exact ⟨h1.trans h3, h4⟩

theorem sim_foldl {s : St P V} (hI : LocI cfg c p Mr M s)
    (hiv : cfg.ver = .task → s.initVal = some (cfg.input p)) {l : List (P × Msg P V)}
    (hl : ∀ qm ∈ l, RcvOK c p Mr qm) :
    ReflTransGen (Fig1.Next cfg) (simSt cfg L M p g s)
        (simSt cfg L M p g (l.foldl (handle c p) s)) ∧
      LocI cfg c p Mr M (l.foldl (handle c p) s) ∧
      (cfg.ver = .task → (l.foldl (handle c p) s).initVal = some (cfg.input p)) := by
  induction l generalizing s with
  | nil => exact ⟨ReflTransGen.refl, hI, hiv⟩
  | cons qm l ih =>
    obtain ⟨h1, h2⟩ := sim_handle hm hsub (L := L) (g := g) hI hiv (hl qm List.mem_cons_self)
    obtain ⟨h3, h4, h5⟩ := ih h2 (fun h => by rw [handle_initVal]; exact hiv h)
      (fun qm' hqm' => hl qm' (List.mem_cons_of_mem _ hqm'))
    exact ⟨h1.trans h3, h4, h5⟩

theorem sim_timer {s : St P V} (hI : LocI cfg c p Mr M s) (τ : ℕ) :
    ReflTransGen (Fig1.Next cfg) (simSt cfg L M p g s) (simSt cfg L M p g (timer c p τ s)) ∧
      LocI cfg c p Mr M (timer c p τ s) := by
  unfold timer
  split_ifs with h
  · obtain ⟨-, -, hown, hlt⟩ := h
    refine ⟨rt_of_step (Fig1.Step.start1A (s := simSt cfg L M p g s) (p := p)
      (b := (τ + 3) / 5) (by rw [hm.owner]; exact hown) (by simpa using hlt)) ?_, ?_⟩
    · exact simSt_send' (s := s) (dm := (.all, .oneA ((τ + 3) / 5))) rfl rfl
    · exact hI.mono_out rfl rfl _ rfl ⟨by simp, by simp, by simp, by simp⟩ (by simp)
  · exact ⟨ReflTransGen.refl, hI⟩

/-- The invocation: object version (`invoke`, then `sendPropose` if `val = ⊥`), task version at
startup (`sendPropose`), or no invocation. -/
theorem sim_invoke {s : St P V} (hI : LocI cfg c p Mr M s) {inv : Option V} {g g' : Option V}
    (H : (inv = none ∧ g' = g ∧ (cfg.ver = .task → s.initVal = some (cfg.input p))) ∨
      (cfg.ver = .object ∧ g = none ∧ inv = g' ∧ inv.isSome) ∨
      (cfg.ver = .task ∧ inv = some (cfg.input p) ∧ s.val = none ∧ g' = g)) :
    ReflTransGen (Fig1.Next cfg) (simSt cfg L M p g s) (simSt cfg L M p g' (invoke inv s)) ∧
      LocI cfg c p Mr M (invoke inv s) ∧
      (cfg.ver = .task → (invoke inv s).initVal = some (cfg.input p)) := by
  rcases H with ⟨rfl, rfl, hiv⟩ | ⟨hver, rfl, rfl, hsome⟩ | ⟨hver, rfl, hval, hg⟩
  · exact ⟨ReflTransGen.refl, hI, hiv⟩
  · obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.1 hsome
    have hstep := Fig1.Step.invoke (cfg := cfg) (s := simSt cfg L M p none s) (p := p) v hver
      (by simp)
    have hiv : (absLoc cfg p none s).initVal = s.initVal := by simp [absLoc, hver]
    by_cases hv : s.val = none
    · have h2 := Fig1.Step.sendPropose (cfg := cfg) (p := p) (v := v)
        (s := (simSt cfg L M p none s).set p
          { (simSt cfg L M p none s).loc p with
            inv := some v,
            initVal := if ((simSt cfg L M p none s).loc p).val = none then some v
              else ((simSt cfg L M p none s).loc p).initVal })
        (by simp [hv])
      refine ⟨(rt_of_step hstep rfl).trans (rt_of_step h2 ?_), ?_, fun h => by simp [hver] at h⟩
      · simp only [invoke, onInv, hv, ite_true]
        refine state_ext ?_ ?_
        · simp [simSt, Fig1.State.set, Fig1.State.send, absLoc, hver, hv]
        · ext m
          simp only [simSt, Fig1.State.send, Fig1.State.set, List.map_append, List.map_cons,
            List.map_nil, Set.mem_union, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton,
            Set.mem_insert_iff]
          simp only [absMsg]
          tauto
      · simp only [invoke, onInv, hv, ite_true]
        exact hI.mono_out rfl rfl _ rfl ⟨by simp, by simp, by simp, by simp⟩ (by simp)
    · refine ⟨rt_of_step hstep ?_, ?_, fun h => by simp [hver] at h⟩
      · simp only [invoke, onInv, hv, ite_false]
        refine state_ext ?_ rfl
        simp [simSt, Fig1.State.set, absLoc, hver, hv]
      · simp only [invoke, onInv, hv, ite_false]; exact hI
  · rw [hg]
    have h2 := Fig1.Step.sendPropose (cfg := cfg) (p := p) (v := cfg.input p)
      (s := simSt cfg L M p g s) (by simp [absLoc, hver])
    refine ⟨rt_of_step h2 ?_, ?_, fun _ => by simp [invoke, onInv, hval]⟩
    · simp only [invoke, onInv, hval, ite_true]
      exact simSt_send' (s := s) (dm := (.others, .propose (cfg.input p))) rfl
        (by simp [absLoc, hver, hval])
    · simp only [invoke, onInv, hval, ite_true]
      exact hI.mono_out rfl rfl _ rfl ⟨by simp, by simp, by simp, by simp⟩ (by simp)

/-- **A whole step of the implementation is a sequence of abstract steps.** -/
theorem sim_stepFn (τ : ℕ) {s : St P V} (hI : LocI cfg c p Mr M { s with out := [] })
    {inv g' : Option V}
    (H : (inv = none ∧ g' = g ∧ (cfg.ver = .task → s.initVal = some (cfg.input p))) ∨
      (cfg.ver = .object ∧ g = none ∧ inv = g' ∧ inv.isSome) ∨
      (cfg.ver = .task ∧ inv = some (cfg.input p) ∧ s.val = none ∧ g' = g))
    {l : List (P × Msg P V)} (hl : ∀ qm ∈ l, RcvOK c p Mr qm) :
    ReflTransGen (Fig1.Next cfg) (simSt cfg L M p g { s with out := [] })
        (simSt cfg L M p g' (stepFn c p τ s inv l)) ∧
      LocI cfg c p Mr M (stepFn c p τ s inv l) ∧
      (cfg.ver = .task → (stepFn c p τ s inv l).initVal = some (cfg.input p)) := by
  obtain ⟨h1, h2, h3⟩ := sim_invoke hm hsub (L := L) (s := { s with out := [] }) (g := g) (g' := g')
    hI H
  obtain ⟨h4, h5, h6⟩ := sim_foldl hm hsub (L := L) (g := g') h2 h3 hl
  obtain ⟨h7, h8⟩ := sim_timer hm hsub (L := L) (g := g') h5 τ
  refine ⟨h1.trans (h4.trans h7), h8, fun h => ?_⟩
  have : ∀ t : St P V, (timer c p τ t).initVal = t.initVal := by
    intro t; unfold timer; split_ifs <;> rfl
  rw [stepFn, this]; exact h6 h

end Sim

end TwoStepConsensus.Impl
