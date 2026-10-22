import Podc.Computability.Distributed.AbstractMAC.Basic

/-!
# Two-phase consensus (Section 4.1, Algorithm 1 of Newport, PODC 2014)

Model: `Cslib.AbstractMAC` on the clique `⊤` (single hop), unique ids `id : V → ℕ`, no crashes,
no knowledge of `n`. A node's state (`TwoPhase.St`) holds the pseudocode's variables `v`, `R1`,
`R2`, `status`, `W` and a program counter `phase` (`1`/`2`: waiting for the ack of the
phase-1/phase-2 broadcast, `3`: loop of line 20, `4`: decided).

* `twoPhase`: Algorithm 1, with line 23 looking for `⟨phase 2, *, decided(0)⟩` in `R1 ∪ R2`.
* `theorem_4_1`: it solves consensus (agreement, validity, termination).
* `theorem_4_1_time`: every node decides by time `2 F_ack`.
* `twoPhaseLit_not_solvesConsensus`: with line 23 read literally (`∈ R2`), agreement fails
  on two nodes — a `decided(0)` message received during phase 1 lands in `R1` and is ignored.

Proof: one invariant over reachable configurations (`TwoPhase.Inv'`), preserved by receives
(`Inv'.recv`) and by the two kinds of acks (`Inv'.ack1`, `Inv'.ack2`). Its key clauses are the
paper's: `p1` (a node that finished phase 1 was heard by every node still in phases 1–2),
`agreeA` (`decided(0)` and `decided(1)` never coexist), `wit` (for every node `u`, a node `x`
past phase 2 has `u` as witness, or `u` heard `x`'s phase-2 message during its phase 1).
Agreement is then `Inv'.agreeB`, the paper's two-case argument.
-/

namespace Podc.AbstractMACConsensus

open Cslib.AbstractMAC

namespace TwoPhase

/-- The status chosen at the end of phase 1. -/
inductive Status
  | bivalent
  | decided (b : Bool)
  deriving DecidableEq

/-- Messages: `⟨phase 1, id, v⟩` and `⟨phase 2, id, status⟩`. -/
inductive Msg
  | p1 (i : ℕ) (b : Bool)
  | p2 (i : ℕ) (t : Status)
  deriving DecidableEq

/-- The id carried by a message. -/
def Msg.id : Msg → ℕ
  | .p1 i _ => i
  | .p2 i _ => i

/-- Phase-2 messages. -/
def Msg.IsP2 : Msg → Prop
  | .p1 .. => False
  | .p2 .. => True

/-- Local state of a node. `phase`: `1`, `2` (waiting for the ack of the phase-1, resp. phase-2,
broadcast), `3` (waiting for the phase-2 messages of the witnesses `W`), `4` (decided). -/
structure St where
  /-- Own id. -/
  myid : ℕ
  /-- Initial value. -/
  v : Bool
  /-- Current phase. -/
  phase : ℕ
  /-- Messages received in phase 1 (and the own phase-1 message). -/
  R1 : Set Msg
  /-- Messages received later (and the own phase-2 message). -/
  R2 : Set Msg
  /-- Status (meaningful from phase 2 on). -/
  status : Status
  /-- Witness ids (meaningful from phase 3 on). -/
  W : Set ℕ

/-- `R1 ∪ R2`. -/
def R (s : St) : Set Msg := s.R1 ∪ s.R2

open Classical in
/-- Lines 8–12: the status chosen from `R1`. -/
noncomputable def statusOf (R1 : Set Msg) (v : Bool) : Status :=
  if (∃ i, Msg.p1 i (!v) ∈ R1) ∨ (∃ i, Msg.p2 i .bivalent ∈ R1) then .bivalent else .decided v

/-- The waiting condition of line 20 is over: every witness sent its phase-2 message. -/
def Ready (s : St) : Prop := ∀ i ∈ s.W, ∃ t, Msg.p2 i t ∈ R s

open Classical in
/-- Leave the loop of line 20 when possible. -/
noncomputable def check (s : St) : St := if s.phase = 3 ∧ Ready s then { s with phase := 4 } else s

open Classical in
/-- Recording a received message (lines 6, 17, 21). -/
noncomputable def addMsg (s : St) (m : Msg) : St :=
  if s.phase = 1 then { s with R1 := insert m s.R1 }
  else if s.phase = 2 ∨ (s.phase = 3 ∧ m.IsP2) then { s with R2 := insert m s.R2 } else s

/-- Receive transition. -/
noncomputable def recv (s : St) (m : Msg) : St := check (addMsg s m)

/-- Ack transition: end of phase 1 (lines 8–15) or of phase 2 (line 19, then line 20). -/
noncomputable def ack (s : St) : St :=
  if s.phase = 1 then
    { s with phase := 2, status := statusOf s.R1 s.v, R2 := {.p2 s.myid (statusOf s.R1 s.v)} }
  else if s.phase = 2 then check { s with phase := 3, W := Msg.id '' R s } else s

/-- The message being broadcast. -/
def bcast (s : St) : Option Msg :=
  if s.phase = 1 then some (.p1 s.myid s.v)
  else if s.phase = 2 then some (.p2 s.myid s.status) else none

open Classical in
/-- Lines 23–27, looking for `decided(0)` in `R1 ∪ R2` (the pseudocode only looks at `R2`). -/
noncomputable def decRule (s : St) : Bool :=
  if ∃ i, Msg.p2 i (.decided false) ∈ R s then false else true

open Classical in
/-- The decision. -/
noncomputable def out (s : St) : Option Bool := if s.phase = 4 then some (decRule s) else none

/-- Initial state (lines 1–2). -/
def init (i : ℕ) (b : Bool) : St := ⟨i, b, 1, {.p1 i b}, ∅, .bivalent, ∅⟩

/-! ### Per-node transitions -/

section Local

open Classical

variable (s : St) (m : Msg)

@[simp] lemma check_myid : (check s).myid = s.myid := by unfold check; split_ifs <;> rfl
@[simp] lemma check_v : (check s).v = s.v := by unfold check; split_ifs <;> rfl
@[simp] lemma check_R1 : (check s).R1 = s.R1 := by unfold check; split_ifs <;> rfl
@[simp] lemma check_R2 : (check s).R2 = s.R2 := by unfold check; split_ifs <;> rfl
@[simp] lemma check_status : (check s).status = s.status := by unfold check; split_ifs <;> rfl
@[simp] lemma check_W : (check s).W = s.W := by unfold check; split_ifs <;> rfl
@[simp] lemma R_check : R (check s) = R s := by simp [R]
@[simp] lemma ready_check : Ready (check s) ↔ Ready s := by simp [Ready]

lemma check_phase : (check s).phase = if s.phase = 3 ∧ Ready s then 4 else s.phase := by
  unfold check; split_ifs <;> rfl

lemma check_of_ne (h : s.phase ≠ 3) : check s = s := by simp [check, h]

@[simp] lemma addMsg_myid : (addMsg s m).myid = s.myid := by unfold addMsg; split_ifs <;> rfl
@[simp] lemma addMsg_v : (addMsg s m).v = s.v := by unfold addMsg; split_ifs <;> rfl
@[simp] lemma addMsg_phase : (addMsg s m).phase = s.phase := by unfold addMsg; split_ifs <;> rfl
@[simp] lemma addMsg_status : (addMsg s m).status = s.status := by
  unfold addMsg; split_ifs <;> rfl
@[simp] lemma addMsg_W : (addMsg s m).W = s.W := by unfold addMsg; split_ifs <;> rfl

lemma addMsg_R1_sub : s.R1 ⊆ (addMsg s m).R1 := by
  unfold addMsg; split_ifs <;> simp [Set.subset_insert]
lemma addMsg_R2_sub : s.R2 ⊆ (addMsg s m).R2 := by
  unfold addMsg; split_ifs <;> simp [Set.subset_insert]
lemma addMsg_R1 (h : s.phase ≠ 1) : (addMsg s m).R1 = s.R1 := by
  simp only [addMsg, h, ite_false]; split_ifs <;> rfl
lemma addMsg_R2 (h : s.phase = 1) : (addMsg s m).R2 = s.R2 := by
  simp [addMsg, h]
lemma addMsg_mem (h0 : 1 ≤ s.phase) (h : s.phase ≤ 2 ∨ (s.phase = 3 ∧ m.IsP2)) :
    m ∈ R (addMsg s m) := by
  unfold addMsg R
  split_ifs with h1 h2 <;> simp
  exfalso
  rcases h with h | h
  · exact h2 (Or.inl (by omega))
  · exact h2 (Or.inr h)

@[simp] lemma recv_myid : (recv s m).myid = s.myid := by simp [recv]
@[simp] lemma recv_v : (recv s m).v = s.v := by simp [recv]
@[simp] lemma recv_status : (recv s m).status = s.status := by simp [recv]
@[simp] lemma recv_W : (recv s m).W = s.W := by simp [recv]
lemma recv_R1_sub : s.R1 ⊆ (recv s m).R1 := by simpa [recv] using addMsg_R1_sub s m
lemma recv_R2_sub : s.R2 ⊆ (recv s m).R2 := by simpa [recv] using addMsg_R2_sub s m
lemma recv_R_sub : R s ⊆ R (recv s m) :=
  Set.union_subset_union (recv_R1_sub s m) (recv_R2_sub s m)
lemma recv_R1 (h : s.phase ≠ 1) : (recv s m).R1 = s.R1 := by simp [recv, addMsg_R1 s m h]
lemma recv_R2 (h : s.phase = 1) : (recv s m).R2 = s.R2 := by simp [recv, addMsg_R2 s m h]
lemma recv_mem (h0 : 1 ≤ s.phase) (h : s.phase ≤ 2 ∨ (s.phase = 3 ∧ m.IsP2)) :
    m ∈ R (recv s m) := by
  simpa [recv] using addMsg_mem s m h0 h

lemma recv_phase : (recv s m).phase =
    if s.phase = 3 ∧ Ready (addMsg s m) then 4 else s.phase := by
  simp [recv, check_phase]

lemma recv_of_four (h : s.phase = 4) : recv s m = s := by
  simp [recv, addMsg, check, h]

lemma recv_phase_cases :
    (recv s m).phase = s.phase ∨ (s.phase = 3 ∧ (recv s m).phase = 4) := by
  rw [recv_phase]; split_ifs with h <;> simp [h]

lemma recv_R_sub_insert : R (recv s m) ⊆ insert m (R s) := by
  simp only [recv, R, addMsg]
  split_ifs <;> simp [Set.insert_union, Set.union_insert, Set.subset_insert]

lemma recv_ready3 (h : (recv s m).phase = 3) : ¬ Ready (recv s m) := by
  rw [recv_phase] at h
  simp only [recv, ready_check]
  split_ifs at h with h1
  · omega
  · exact fun h2 => h1 ⟨h, h2⟩

lemma recv_ready4 (h4 : s.phase = 4 → Ready s) (h : (recv s m).phase = 4) :
    Ready (recv s m) := by
  by_cases hs : s.phase = 4
  · rw [recv_of_four s m hs]; exact h4 hs
  rw [recv_phase] at h
  simp only [recv, ready_check]
  split_ifs at h with h1
  · exact h1.2
  · exact absurd h hs

lemma bcast_recv : bcast (recv s m) = bcast s := by
  rcases recv_phase_cases s m with h | ⟨h3, h4⟩
  · simp [bcast, h]
  · simp [bcast, h3, h4]

lemma out_recv : (out s).or (out (recv s m)) = out (recv s m) := by
  by_cases h : s.phase = 4
  · rw [recv_of_four s m h]; simp
  · simp [out, h]

lemma bcast_some {s : St} {m : Msg} (h : bcast s = some m) :
    (s.phase = 1 ∧ m = .p1 s.myid s.v) ∨ (s.phase = 2 ∧ m = .p2 s.myid s.status) := by
  unfold bcast at h
  split_ifs at h with h1 h2 <;> cases h
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨h2, rfl⟩

lemma statusOf_decided {R1 : Set Msg} {v b : Bool} (h : statusOf R1 v = .decided b) :
    b = v ∧ (∀ i, Msg.p1 i (!v) ∉ R1) ∧ ∀ i, Msg.p2 i .bivalent ∉ R1 := by
  unfold statusOf at h
  split_ifs at h with h1
  push Not at h1
  cases h
  exact ⟨rfl, h1.1, h1.2⟩

lemma statusOf_bivalent {R1 : Set Msg} {v : Bool} (h : statusOf R1 v = .bivalent) :
    (∃ i, Msg.p1 i (!v) ∈ R1) ∨ ∃ i, Msg.p2 i .bivalent ∈ R1 := by
  unfold statusOf at h
  split_ifs at h with h1
  exact h1

end Local

/-! ### Invariants -/

section Inv

open Function

variable {V : Type*} [DecidableEq V] (id : V → ℕ) (inp : V → Bool)

/-- A message that was actually sent (given the current states `S`; phase-2 messages carry the
current status of their sender). -/
def Valid (S : V → St) : Msg → Prop
  | .p1 i b => ∃ w, id w = i ∧ inp w = b
  | .p2 i t => ∃ w, id w = i ∧ 2 ≤ (S w).phase ∧ (S w).status = t

/-- The invariant, on the components of a configuration: states `S`, current broadcasts `cur`,
decisions `dec`, receivers of the current broadcasts `got`, ack counters `acks`. -/
structure Inv' (S : V → St) (cur : V → Option Msg) (dec : V → Option Bool) (got : V → Set V)
    (acks : V → ℕ) : Prop where
  myid : ∀ x, (S x).myid = id x
  v : ∀ x, (S x).v = inp x
  ph1 : ∀ x, 1 ≤ (S x).phase
  ph4 : ∀ x, (S x).phase ≤ 4
  cur : ∀ x, cur x = bcast (S x)
  dec : ∀ x, dec x = out (S x)
  acks : ∀ x, acks x = min (S x).phase 3 - 1
  r2 : ∀ x, (S x).phase = 1 → (S x).R2 = ∅
  own2 : ∀ x, 2 ≤ (S x).phase → Msg.p2 (id x) (S x).status ∈ (S x).R2
  status : ∀ x, 2 ≤ (S x).phase → (S x).status = statusOf (S x).R1 (inp x)
  wid : ∀ x, 3 ≤ (S x).phase → ∀ i ∈ (S x).W, ∃ w, id w = i
  ready3 : ∀ x, (S x).phase = 3 → ¬ Ready (S x)
  ready4 : ∀ x, (S x).phase = 4 → Ready (S x)
  valid : ∀ x, ∀ m ∈ R (S x), Valid id inp S m
  got : ∀ u x m, x ∈ got u → bcast (S u) = some m →
    ((S x).phase ≤ 2 ∨ ((S x).phase = 3 ∧ m.IsP2)) → m ∈ R (S x)
  p1 : ∀ u x, u ≠ x → 2 ≤ (S u).phase → (S x).phase ≤ 2 → Msg.p1 (id u) (inp u) ∈ R (S x)
  p2 : ∀ w u, w ≠ u → 3 ≤ (S w).phase → (S u).phase ≤ 3 → ∃ t, Msg.p2 (id w) t ∈ R (S u)
  agreeA : ∀ u x b b', 2 ≤ (S u).phase → 2 ≤ (S x).phase → (S u).status = .decided b →
    (S x).status = .decided b' → b = b'
  wit : ∀ x u, u ≠ x → 3 ≤ (S x).phase →
    id u ∈ (S x).W ∨ Msg.p2 (id x) (S x).status ∈ (S u).R1
  bival : ∀ u, 2 ≤ (S u).phase → (S u).status = .bivalent →
    (∃ a, inp a = true) ∧ ∃ a, inp a = false

variable {id inp}

omit [DecidableEq V] in
lemma Valid.mono {S S' : V → St} {m : Msg} (h : Valid id inp S m)
    (hS : ∀ w, 2 ≤ (S w).phase → 2 ≤ (S' w).phase ∧ (S' w).status = (S w).status) :
    Valid id inp S' m := by
  cases m with
  | p1 i b => exact h
  | p2 i t =>
    obtain ⟨w, h1, h2, h3⟩ := h
    obtain ⟨h4, h5⟩ := hS w h2
    exact ⟨w, h1, h4, h5.trans h3⟩

omit [DecidableEq V] in
lemma Valid.exists_id {S : V → St} {m : Msg} (h : Valid id inp S m) : ∃ w, id w = m.id := by
  cases m with
  | p1 i b => obtain ⟨w, h1, -⟩ := h; exact ⟨w, h1⟩
  | p2 i t => obtain ⟨w, h1, -⟩ := h; exact ⟨w, h1⟩

section Pres

variable {S : V → St} {cur : V → Option Msg} {dec : V → Option Bool} {got : V → Set V}
  {acks : V → ℕ}

omit [DecidableEq V] in
lemma Inv'.bcast_valid (hI : Inv' id inp S cur dec got acks) {u : V} {m : Msg}
    (h : bcast (S u) = some m) : Valid id inp S m := by
  rcases bcast_some h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact ⟨u, (hI.myid u).symm, (hI.v u).symm⟩
  · exact ⟨u, (hI.myid u).symm, by omega, rfl⟩

/-- Receiving preserves the invariant. -/
theorem Inv'.recv (hI : Inv' id inp S cur dec got acks) {u x : V} {m : Msg}
    (hm : cur u = some m) :
    Inv' id inp (update S x (TwoPhase.recv (S x) m))
      (update cur x ((cur x).or (bcast (TwoPhase.recv (S x) m))))
      (update dec x ((dec x).or (out (TwoPhase.recv (S x) m))))
      (update got u (insert x (got u))) acks := by
  set s' := TwoPhase.recv (S x) m with hs'
  set S' := update S x s' with hS'
  have hbm : bcast (S u) = some m := (hI.cur u).symm.trans hm
  have hph : ∀ w, (S' w).phase = (S w).phase ∨ ((S w).phase = 3 ∧ (S' w).phase = 4) := by
    intro w; rcases eq_or_ne w x with rfl | hw
    · simpa [hS'] using recv_phase_cases (S w) m
    · simp [hS', update_of_ne hw]
  have hfix : ∀ w, (S' w).myid = (S w).myid ∧ (S' w).v = (S w).v ∧
      (S' w).status = (S w).status ∧ (S' w).W = (S w).W := by
    intro w; rcases eq_or_ne w x with rfl | hw
    · simp [hS', hs']
    · simp [hS', update_of_ne hw]
  have hR1 : ∀ w, (S w).R1 ⊆ (S' w).R1 := by
    intro w; rcases eq_or_ne w x with rfl | hw
    · simpa [hS'] using recv_R1_sub (S w) m
    · simp [hS', update_of_ne hw]
  have hR2 : ∀ w, (S w).R2 ⊆ (S' w).R2 := by
    intro w; rcases eq_or_ne w x with rfl | hw
    · simpa [hS'] using recv_R2_sub (S w) m
    · simp [hS', update_of_ne hw]
  have hR : ∀ w, R (S w) ⊆ R (S' w) := fun w => Set.union_subset_union (hR1 w) (hR2 w)
  have hR1e : ∀ w, (S w).phase ≠ 1 → (S' w).R1 = (S w).R1 := by
    intro w h; rcases eq_or_ne w x with rfl | hw
    · simpa [hS'] using recv_R1 (S w) m h
    · simp [hS', update_of_ne hw]
  have hR2e : ∀ w, (S w).phase = 1 → (S' w).R2 = (S w).R2 := by
    intro w h; rcases eq_or_ne w x with rfl | hw
    · simpa [hS'] using recv_R2 (S w) m h
    · simp [hS', update_of_ne hw]
  have hval : ∀ m', Valid id inp S m' → Valid id inp S' m' := fun m' h =>
    h.mono fun w hw => ⟨by rcases hph w with h | h <;> omega, (hfix w).2.2.1⟩
  have hbc : ∀ w, bcast (S' w) = bcast (S w) := by
    intro w; rcases eq_or_ne w x with rfl | hw
    · simpa [hS'] using bcast_recv (S w) m
    · simp [hS', update_of_ne hw]
  have hcond : ∀ w (m' : Msg), ((S' w).phase ≤ 2 ∨ ((S' w).phase = 3 ∧ m'.IsP2)) →
      ((S w).phase ≤ 2 ∨ ((S w).phase = 3 ∧ m'.IsP2)) := by
    intro w m' h; rcases hph w with h' | h'
    · rw [h'] at h; exact h
    · rcases h with h | ⟨h, -⟩ <;> omega
  refine
    { myid := fun w => (hfix w).1.trans (hI.myid w)
      v := fun w => (hfix w).2.1.trans (hI.v w)
      ph1 := fun w => by have := hI.ph1 w; rcases hph w with h | h <;> omega
      ph4 := fun w => by have := hI.ph4 w; rcases hph w with h | h <;> omega
      cur := ?_
      dec := ?_
      acks := fun w => by
        rcases hph w with h | h
        · rw [h]; exact hI.acks w
        · rw [hI.acks w, h.1, h.2]; rfl
      r2 := fun w h => by
        have h1 : (S w).phase = 1 := by rcases hph w with h' | h' <;> omega
        rw [hR2e w h1]; exact hI.r2 w h1
      own2 := fun w h => by
        have h1 : 2 ≤ (S w).phase := by rcases hph w with h' | h' <;> omega
        rw [(hfix w).2.2.1]; exact hR2 w (hI.own2 w h1)
      status := fun w h => by
        have h1 : 2 ≤ (S w).phase := by rcases hph w with h' | h' <;> omega
        rw [(hfix w).2.2.1, hR1e w (by omega)]; exact hI.status w h1
      wid := fun w h => by
        have h1 : 3 ≤ (S w).phase := by rcases hph w with h' | h' <;> omega
        rw [(hfix w).2.2.2]; exact hI.wid w h1
      ready3 := ?_
      ready4 := ?_
      valid := ?_
      got := ?_
      p1 := fun u₁ x₁ h h2 h3 => by
        have a : 2 ≤ (S u₁).phase := by rcases hph u₁ with h' | h' <;> omega
        have b : (S x₁).phase ≤ 2 := by rcases hph x₁ with h' | h' <;> omega
        exact hR x₁ (hI.p1 u₁ x₁ h a b)
      p2 := fun w u₁ h h2 h3 => by
        have a : 3 ≤ (S w).phase := by rcases hph w with h' | h' <;> omega
        have b : (S u₁).phase ≤ 3 := by rcases hph u₁ with h' | h' <;> omega
        obtain ⟨t, ht⟩ := hI.p2 w u₁ h a b
        exact ⟨t, hR u₁ ht⟩
      agreeA := fun u₁ x₁ b b' h1 h2 h3 h4 => by
        have a : 2 ≤ (S u₁).phase := by rcases hph u₁ with h' | h' <;> omega
        have c : 2 ≤ (S x₁).phase := by rcases hph x₁ with h' | h' <;> omega
        rw [(hfix u₁).2.2.1] at h3; rw [(hfix x₁).2.2.1] at h4
        exact hI.agreeA u₁ x₁ b b' a c h3 h4
      wit := fun x₁ u₁ h h3 => by
        have a : 3 ≤ (S x₁).phase := by rcases hph x₁ with h' | h' <;> omega
        rw [(hfix x₁).2.2.2, (hfix x₁).2.2.1]
        rcases hI.wit x₁ u₁ h a with h' | h'
        · exact Or.inl h'
        · exact Or.inr (hR1 u₁ h')
      bival := fun w h1 h2 => by
        have a : 2 ≤ (S w).phase := by rcases hph w with h' | h' <;> omega
        rw [(hfix w).2.2.1] at h2
        exact hI.bival w a h2 }
  · intro w; rcases eq_or_ne w x with rfl | hw
    · simp only [update_self]; rw [hI.cur w, ← hbc w]; simp [hS']
    · simp [hS', update_of_ne hw, hI.cur w]
  · intro w; rcases eq_or_ne w x with rfl | hw
    · simp only [hS', update_self]; rw [hI.dec w]; exact out_recv _ _
    · simp [hS', update_of_ne hw, hI.dec w]
  · intro w h; rcases eq_or_ne w x with rfl | hw
    · simp only [hS', update_self] at h ⊢; exact recv_ready3 _ _ h
    · simp only [hS', update_of_ne hw] at h ⊢; exact hI.ready3 w h
  · intro w h; rcases eq_or_ne w x with rfl | hw
    · simp only [hS', update_self] at h ⊢; exact recv_ready4 _ _ (hI.ready4 w) h
    · simp only [hS', update_of_ne hw] at h ⊢; exact hI.ready4 w h
  · intro w m' hm'; rcases eq_or_ne w x with rfl | hw
    · simp only [hS', update_self] at hm'
      rcases recv_R_sub_insert _ _ hm' with rfl | h
      · exact hval _ (hI.bcast_valid hbm)
      · exact hval _ (hI.valid w m' h)
    · simp only [hS', update_of_ne hw] at hm'
      exact hval _ (hI.valid w m' hm')
  · intro u₁ w m' hw hb hc
    rw [hbc] at hb
    have hc' := hcond w m' hc
    by_cases hnew : u₁ = u ∧ w = x
    · obtain ⟨rfl, rfl⟩ := hnew
      rw [hbm] at hb; cases hb
      simp only [hS', update_self]
      exact recv_mem _ _ (hI.ph1 w) hc'
    · have hw' : w ∈ got u₁ := by
        rcases eq_or_ne u₁ u with rfl | hu
        · simp only [update_self, Set.mem_insert_iff] at hw
          rcases hw with rfl | hw
          · exact absurd ⟨rfl, rfl⟩ hnew
          · exact hw
        · simpa [update_of_ne hu] using hw
      exact hR w (hI.got u₁ w m' hw' hb hc')

/-- The acknowledgment of a phase-1 broadcast preserves the invariant. -/
theorem Inv'.ack1 (hI : Inv' id inp S cur dec got acks) {x : V} (hp : (S x).phase = 1)
    (hall : ∀ w, w ≠ x → w ∈ got x) :
    Inv' id inp (update S x (TwoPhase.ack (S x)))
      (update cur x (bcast (TwoPhase.ack (S x))))
      (update dec x ((dec x).or (out (TwoPhase.ack (S x)))))
      (update got x ∅) (update acks x (acks x + 1)) := by
  set st0 := statusOf (S x).R1 (S x).v with hst0
  have hs' : TwoPhase.ack (S x) =
      { S x with phase := 2, status := st0, R2 := {Msg.p2 (S x).myid st0} } := by
    simp [TwoPhase.ack, hp, hst0]
  set S' := update S x (TwoPhase.ack (S x)) with hS'
  have hx : S' x = { S x with phase := 2, status := st0, R2 := {Msg.p2 (S x).myid st0} } := by
    simp [hS', hs']
  have ho : ∀ w, w ≠ x → S' w = S w := fun w hw => by simp [hS', update_of_ne hw]
  have hRx : R (S' x) = (S x).R1 ∪ {Msg.p2 (id x) st0} := by
    rw [hx, hI.myid]; rfl
  have hRx0 : R (S x) = (S x).R1 := by simp [R, hI.r2 x hp]
  have hRsub : ∀ w, R (S w) ⊆ R (S' w) := by
    intro w; rcases eq_or_ne w x with rfl | hw
    · rw [hRx, hRx0]; exact Set.subset_union_left
    · rw [ho w hw]
  have hval : ∀ m', Valid id inp S m' → Valid id inp S' m' := by
    intro m' h; refine h.mono fun w hw => ?_
    rcases eq_or_ne w x with rfl | hw'
    · omega
    · rw [ho w hw']; exact ⟨hw, rfl⟩
  have hbx : bcast (S x) = some (Msg.p1 (id x) (inp x)) := by
    simp [bcast, hp, hI.myid, hI.v]
  -- the new status agrees with every decided status
  have hagr : ∀ u b b', u ≠ x → 2 ≤ (S u).phase → (S u).status = .decided b →
      st0 = .decided b' → b = b' := by
    intro u b b' hu h2 h3 h4
    have hmem := hI.p1 u x hu h2 (by omega)
    rw [hRx0] at hmem
    rw [hI.status u h2] at h3
    obtain ⟨hb, -, -⟩ := statusOf_decided h3
    obtain ⟨hb', hn, -⟩ := statusOf_decided h4
    rw [hb, hb', hI.v]
    by_contra hne
    have : inp u = !inp x := by cases h : inp u <;> cases h' : inp x <;> simp_all
    rw [hI.v] at hn
    exact hn _ (this ▸ hmem)
  refine
    { myid := ?_, v := ?_, ph1 := ?_, ph4 := ?_, cur := ?_, dec := ?_, acks := ?_, r2 := ?_,
      own2 := ?_, status := ?_, wid := ?_, ready3 := ?_, ready4 := ?_, valid := ?_, got := ?_,
      p1 := ?_, p2 := ?_, agreeA := ?_, wit := ?_, bival := ?_ }
  all_goals intro w; rcases eq_or_ne w x with rfl | hw
  -- myid
  · rw [hx]; exact hI.myid w
  · rw [ho w hw]; exact hI.myid w
  -- v
  · rw [hx]; exact hI.v w
  · rw [ho w hw]; exact hI.v w
  -- ph1
  · rw [hx]; simp
  · rw [ho w hw]; exact hI.ph1 w
  -- ph4
  · rw [hx]; simp
  · rw [ho w hw]; exact hI.ph4 w
  -- cur
  · simp [hS']
  · simp [hS', update_of_ne hw, hI.cur w]
  -- dec
  · simp only [update_self, hS', hI.dec w, hs']; simp [out, hp]
  · simp [hS', update_of_ne hw, hI.dec w]
  -- acks
  · simp only [update_self, hI.acks w, hx, hp]; rfl
  · simp only [update_of_ne hw, ho w hw]; exact hI.acks w
  -- r2
  · rw [hx]; simp
  · rw [ho w hw]; exact hI.r2 w
  -- own2
  · rw [hx]; simp [hI.myid]
  · rw [ho w hw]; exact hI.own2 w
  -- status
  · rw [hx]; simp [hst0, hI.v]
  · rw [ho w hw]; exact hI.status w
  -- wid
  · rw [hx]; simp
  · rw [ho w hw]; exact hI.wid w
  -- ready3
  · rw [hx]; simp
  · rw [ho w hw]; exact hI.ready3 w
  -- ready4
  · rw [hx]; simp
  · rw [ho w hw]; exact hI.ready4 w
  -- valid
  · intro m hm
    rw [hRx] at hm
    rcases hm with hm | hm
    · exact hval _ (hI.valid w m (hRx0 ▸ hm))
    · rw [Set.mem_singleton_iff] at hm; subst hm
      exact ⟨w, rfl, by rw [hx], by rw [hx]⟩
  · intro m hm; rw [ho w hw] at hm; exact hval _ (hI.valid w m hm)
  -- got
  · intro w m hw hb hc; simp at hw
  · intro y m hy hb hc
    rw [update_of_ne hw] at hy
    rw [ho w hw] at hb
    refine hRsub y (hI.got w y m hy hb ?_)
    rcases eq_or_ne y x with rfl | hyx
    · exact Or.inl (by omega)
    · rwa [ho y hyx] at hc
  -- p1
  · intro y hy h2 h3
    rw [ho y (Ne.symm hy)] at h3 ⊢
    exact hI.got w y _ (hall y (Ne.symm hy)) hbx (Or.inl h3)
  · intro y hy h2 h3
    rw [ho w hw] at h2
    refine hRsub y (hI.p1 w y hy h2 ?_)
    rcases eq_or_ne y x with rfl | hyx
    · omega
    · rwa [ho y hyx] at h3
  -- p2
  · intro y _ h3; rw [hx] at h3; simp at h3
  · intro y hy h3 h4
    rw [ho w hw] at h3
    have h4' : (S y).phase ≤ 3 := by
      rcases eq_or_ne y x with rfl | hyx
      · omega
      · rwa [ho y hyx] at h4
    obtain ⟨t, ht⟩ := hI.p2 w y hy h3 h4'
    exact ⟨t, hRsub y ht⟩
  -- agreeA
  · intro y b b' _ h2 h3 h4
    rw [hx] at h3
    rcases eq_or_ne y w with rfl | hy
    · rw [hx] at h4; simp only at h3 h4; rw [h3] at h4; cases h4; rfl
    · rw [ho y hy] at h2 h4
      exact (hagr y b' b hy h2 h4 h3).symm
  · intro y b b' h1 h2 h3 h4
    rw [ho w hw] at h1 h3
    rcases eq_or_ne y x with rfl | hy
    · rw [hx] at h4; exact hagr w b b' hw h1 h3 h4
    · rw [ho y hy] at h2 h4; exact hI.agreeA w y b b' h1 h2 h3 h4
  -- wit
  · intro y _ h3; rw [hx] at h3; simp at h3
  · intro y hy h3
    rw [ho w hw] at h3 ⊢
    rcases eq_or_ne y x with rfl | hyx
    · rw [hx]; exact hI.wit w y hy h3
    · rw [ho y hyx]; exact hI.wit w y hy h3
  -- bival
  · intro _ h; rw [hx] at h; simp only at h
    rcases statusOf_bivalent h with ⟨i, hi⟩ | ⟨i, hi⟩
    · obtain ⟨a, -, ha⟩ := hI.valid w _ (Or.inl hi)
      rw [hI.v] at ha
      cases hw : inp w <;> rw [hw] at ha
      · exact ⟨⟨a, ha⟩, ⟨w, hw⟩⟩
      · exact ⟨⟨w, hw⟩, ⟨a, ha⟩⟩
    · obtain ⟨a, -, ha2, ha3⟩ := hI.valid w _ (Or.inl hi)
      exact hI.bival a ha2 ha3
  · intro h1 h2; rw [ho w hw] at h1 h2; exact hI.bival w h1 h2


/-- The acknowledgment of a phase-2 broadcast preserves the invariant. -/
theorem Inv'.ack2 (hI : Inv' id inp S cur dec got acks) {x : V} (hp : (S x).phase = 2)
    (hall : ∀ w, w ≠ x → w ∈ got x) :
    Inv' id inp (update S x (TwoPhase.ack (S x)))
      (update cur x (bcast (TwoPhase.ack (S x))))
      (update dec x ((dec x).or (out (TwoPhase.ack (S x)))))
      (update got x ∅) (update acks x (acks x + 1)) := by
  classical
  set s₁ : St := { S x with phase := 3, W := Msg.id '' R (S x) } with hs₁
  have hs' : TwoPhase.ack (S x) = check s₁ := by simp [TwoPhase.ack, hp, hs₁]
  set S' := update S x (TwoPhase.ack (S x)) with hS'
  have ho : ∀ w, w ≠ x → S' w = S w := fun w hw => by simp [hS', update_of_ne hw]
  have hsame : ∀ w, (S' w).myid = (S w).myid ∧ (S' w).v = (S w).v ∧ (S' w).R1 = (S w).R1 ∧
      (S' w).R2 = (S w).R2 ∧ (S' w).status = (S w).status := by
    intro w; rcases eq_or_ne w x with rfl | hw
    · simp [hS', hs', hs₁]
    · simp [ho w hw]
  have hRe : ∀ w, R (S' w) = R (S w) := fun w => by
    simp only [R, (hsame w).2.2.1, (hsame w).2.2.2.1]
  have hWx : (S' x).W = Msg.id '' R (S x) := by simp [hS', hs', hs₁]
  have hrx : Ready (S' x) ↔ Ready s₁ := by simp [hS', hs']
  have hxp : ((S' x).phase = 3 ∧ ¬ Ready (S' x)) ∨ ((S' x).phase = 4 ∧ Ready (S' x)) := by
    have hph' : (S' x).phase = if Ready s₁ then 4 else 3 := by
      rw [show S' x = check s₁ by simp [hS', hs'], check_phase]
      simp only [show s₁.phase = 3 from rfl, true_and]
    rw [hrx, hph']
    by_cases h : Ready s₁ <;> simp [h]
  have hx3 : 3 ≤ (S' x).phase ∧ (S' x).phase ≤ 4 := by omega
  have hval : ∀ m', Valid id inp S m' → Valid id inp S' m' := by
    intro m' h; refine h.mono fun w hw => ?_
    rcases eq_or_ne w x with rfl | hw'
    · exact ⟨by omega, (hsame w).2.2.2.2⟩
    · rw [ho w hw']; exact ⟨hw, rfl⟩
  have hbx : bcast (S x) = some (Msg.p2 (id x) (S x).status) := by
    simp [bcast, hp, hI.myid]
  refine
    { myid := ?_, v := ?_, ph1 := ?_, ph4 := ?_, cur := ?_, dec := ?_, acks := ?_, r2 := ?_,
      own2 := ?_, status := ?_, wid := ?_, ready3 := ?_, ready4 := ?_, valid := ?_, got := ?_,
      p1 := ?_, p2 := ?_, agreeA := ?_, wit := ?_, bival := ?_ }
  all_goals intro w; rcases eq_or_ne w x with rfl | hw
  -- myid
  · rw [(hsame w).1]; exact hI.myid w
  · rw [ho w hw]; exact hI.myid w
  -- v
  · rw [(hsame w).2.1]; exact hI.v w
  · rw [ho w hw]; exact hI.v w
  -- ph1
  · omega
  · rw [ho w hw]; exact hI.ph1 w
  -- ph4
  · omega
  · rw [ho w hw]; exact hI.ph4 w
  -- cur
  · simp [hS']
  · simp [hS', update_of_ne hw, hI.cur w]
  -- dec
  · simp only [update_self, hS', hI.dec w]; simp [out, hp]
  · simp [hS', update_of_ne hw, hI.dec w]
  -- acks
  · simp only [update_self, hI.acks w, hp]
    rcases hxp with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
  · simp only [update_of_ne hw, ho w hw]; exact hI.acks w
  -- r2
  · intro h; omega
  · rw [ho w hw]; exact hI.r2 w
  -- own2
  · intro _; rw [(hsame w).2.2.2.1, (hsame w).2.2.2.2]; exact hI.own2 w (by omega)
  · rw [ho w hw]; exact hI.own2 w
  -- status
  · intro _; rw [(hsame w).2.2.1, (hsame w).2.2.2.2]; exact hI.status w (by omega)
  · rw [ho w hw]; exact hI.status w
  -- wid
  · intro _ i hi
    rw [hWx] at hi
    obtain ⟨m, hm, rfl⟩ := hi
    exact (hI.valid w m hm).exists_id
  · rw [ho w hw]; exact hI.wid w
  -- ready3
  · intro h; rcases hxp with ⟨-, h'⟩ | ⟨h', -⟩
    · exact h'
    · omega
  · rw [ho w hw]; exact hI.ready3 w
  -- ready4
  · intro h; rcases hxp with ⟨h', -⟩ | ⟨-, h'⟩
    · omega
    · exact h'
  · rw [ho w hw]; exact hI.ready4 w
  -- valid
  · intro m hm; rw [hRe] at hm; exact hval _ (hI.valid w m hm)
  · intro m hm; rw [ho w hw] at hm; exact hval _ (hI.valid w m hm)
  -- got
  · intro w m hw hb hc; simp at hw
  · intro y m hy hb hc
    rw [update_of_ne hw] at hy
    rw [ho w hw] at hb
    rw [hRe]
    refine hI.got w y m hy hb ?_
    rcases eq_or_ne y x with rfl | hyx
    · exact Or.inl (by omega)
    · rwa [ho y hyx] at hc
  -- p1
  · intro y hy _ h3
    rw [ho y (Ne.symm hy)] at h3 ⊢
    exact hI.p1 w y hy (by omega) h3
  · intro y hy h2 h3
    rw [ho w hw] at h2
    rcases eq_or_ne y x with rfl | hyx
    · omega
    · rw [ho y hyx] at h3 ⊢; exact hI.p1 w y hy h2 h3
  -- p2
  · intro y hy _ h4
    rw [ho y (Ne.symm hy)] at h4 ⊢
    refine ⟨_, hI.got w y _ (hall y (Ne.symm hy)) hbx ?_⟩
    rcases Nat.lt_or_ge (S y).phase 3 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, trivial⟩
  · intro y hy h3 h4
    rw [ho w hw] at h3
    rcases eq_or_ne y x with rfl | hyx
    · rw [hRe]; exact hI.p2 w y hy h3 (by omega)
    · rw [ho y hyx] at h4 ⊢; exact hI.p2 w y hy h3 h4
  -- agreeA
  · intro y b b' _ h2 h3 h4
    rw [(hsame w).2.2.2.2] at h3
    rcases eq_or_ne y w with rfl | hy
    · rw [(hsame y).2.2.2.2] at h4; exact hI.agreeA y y b b' (by omega) (by omega) h3 h4
    · rw [ho y hy] at h2 h4; exact hI.agreeA w y b b' (by omega) h2 h3 h4
  · intro y b b' h1 h2 h3 h4
    rw [ho w hw] at h1 h3
    rcases eq_or_ne y x with rfl | hy
    · rw [(hsame y).2.2.2.2] at h4; exact hI.agreeA w y b b' h1 (by omega) h3 h4
    · rw [ho y hy] at h2 h4; exact hI.agreeA w y b b' h1 h2 h3 h4
  -- wit
  · intro y hy _
    rw [hWx, (hsame w).2.2.2.2, ho y hy]
    by_cases h2 : 2 ≤ (S y).phase
    · exact Or.inl ⟨_, hI.p1 y w hy h2 (by omega), rfl⟩
    · right
      have h1 : (S y).phase = 1 := by have := hI.ph1 y; omega
      have := hI.got w y _ (hall y hy) hbx (Or.inl (by omega))
      simpa [R, hI.r2 y h1] using this
  · intro y hy h3
    rw [ho w hw] at h3 ⊢
    rcases eq_or_ne y x with rfl | hyx
    · rw [(hsame y).2.2.1]; exact hI.wit w y hy h3
    · rw [ho y hyx]; exact hI.wit w y hy h3
  -- bival
  · intro _ h; rw [(hsame w).2.2.2.2] at h; exact hI.bival w (by omega) h
  · intro h1 h2; rw [ho w hw] at h1 h2; exact hI.bival w h1 h2


/-! ### Consequences of the invariant -/

omit [DecidableEq V] in
lemma decRule_eq_false {s : St} (h : decRule s = false) :
    ∃ i, Msg.p2 i (.decided false) ∈ R s := by
  unfold decRule at h; split_ifs at h with h1; exact h1

omit [DecidableEq V] in
lemma out_eq_some {s : St} {b : Bool} (h : out s = some b) : s.phase = 4 ∧ decRule s = b := by
  unfold out at h; split_ifs at h with h1; cases h; exact ⟨h1, rfl⟩

omit [DecidableEq V] in
/-- A node that holds a `decided(b)` message decides `b` (`decided(0)` and `decided(1)` do not
coexist). -/
lemma Inv'.decRule_of_mem (hI : Inv' id inp S cur dec got acks) {x : V} {i : ℕ} {b : Bool}
    (h : Msg.p2 i (.decided b) ∈ R (S x)) : decRule (S x) = b := by
  cases b with
  | false => unfold decRule; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨i, h⟩)]
  | true =>
    by_contra hne
    obtain ⟨j, hj⟩ := decRule_eq_false (Bool.eq_false_iff.2 hne)
    obtain ⟨w, -, hw2, hw3⟩ := hI.valid x _ h
    obtain ⟨w', -, hw2', hw3'⟩ := hI.valid x _ hj
    exact absurd (hI.agreeA w w' true false hw2 hw2' hw3 hw3') (by decide)

omit [DecidableEq V] in
/-- The core of the paper's agreement argument: a node that has decided decided the value of
every `decided(b)` status. -/
lemma Inv'.agreeB (hI : Inv' id inp S cur dec got acks) (hid : Function.Injective id) {x u : V}
    {b : Bool} (hx : (S x).phase = 4) (hu : 2 ≤ (S u).phase) (hs : (S u).status = .decided b) :
    decRule (S x) = b := by
  by_cases hux : u = x
  · subst hux; exact hI.decRule_of_mem (Or.inr (hs ▸ hI.own2 u hu))
  rcases hI.wit x u hux (by omega) with h | h
  · -- `u` is a witness of `x`: `x` waited for the phase-2 message of `u`
    obtain ⟨t, ht⟩ := hI.ready4 x hx _ h
    obtain ⟨w, hw1, -, hw3⟩ := hI.valid x _ ht
    obtain rfl := hid hw1
    rw [hs] at hw3; subst hw3
    exact hI.decRule_of_mem ht
  · -- `u` heard the phase-2 message of `x` during its phase 1
    have hsu := hI.status u hu
    rw [hs] at hsu
    obtain ⟨-, -, hnb⟩ := statusOf_decided hsu.symm
    cases hsx : (S x).status with
    | bivalent => rw [hsx] at h; exact absurd h (hnb _)
    | decided c =>
      rw [hI.decRule_of_mem (x := x) (Or.inr (hsx ▸ hI.own2 x (by omega)))]
      exact hI.agreeA x u c b (by omega) hu hsx hs

omit [DecidableEq V] in
lemma Inv'.agree (hI : Inv' id inp S cur dec got acks) (hid : Function.Injective id) {x y : V}
    (hx : (S x).phase = 4) (hy : (S y).phase = 4) : decRule (S x) = decRule (S y) := by
  have key : ∀ x y, (S x).phase = 4 → (S y).phase = 4 → decRule (S x) = false →
      decRule (S y) = false := by
    intro x y hx hy h
    obtain ⟨i, hi⟩ := decRule_eq_false h
    obtain ⟨w, -, hw2, hw3⟩ := hI.valid x _ hi
    exact hI.agreeB hid hy hw2 hw3
  cases h : decRule (S x)
  · exact (key x y hx hy h).symm
  · cases h' : decRule (S y)
    · rw [key y x hy hx h'] at h; exact h.symm
    · rfl

omit [DecidableEq V] in
lemma Inv'.valid_dec (hI : Inv' id inp S cur dec got acks) {x : V} (hx : (S x).phase = 4) :
    ∃ w, inp w = decRule (S x) := by
  cases h : decRule (S x)
  · obtain ⟨i, hi⟩ := decRule_eq_false h
    obtain ⟨w, -, hw2, hw3⟩ := hI.valid x _ hi
    have := hI.status w hw2
    rw [hw3] at this
    exact ⟨w, (statusOf_decided this.symm).1.symm⟩
  · have hown := hI.own2 x (by omega)
    cases hsx : (S x).status with
    | bivalent => exact (hI.bival x (by omega) hsx).1
    | decided c =>
      rw [hsx] at hown
      have h1 := hI.decRule_of_mem (Or.inr hown)
      have h2 := hI.status x (by omega)
      rw [hsx] at h2
      refine ⟨x, ?_⟩
      rw [← (statusOf_decided h2.symm).1, ← h1, h]

omit [DecidableEq V] in
lemma Inv'.phase_four (hI : Inv' id inp S cur dec got acks) (hall : ∀ w, 3 ≤ (S w).phase)
    (u : V) : (S u).phase = 4 := by
  have h4 := hI.ph4 u
  by_contra hne
  have h3 : (S u).phase = 3 := by have := hall u; omega
  apply hI.ready3 u h3
  intro i hi
  obtain ⟨w, rfl⟩ := hI.wid u (by omega) i hi
  by_cases hwu : w = u
  · subst hwu; exact ⟨_, Or.inr (hI.own2 w (by omega))⟩
  · exact hI.p2 w u hwu (hall w) (by omega)

end Pres

end Inv

end TwoPhase


open TwoPhase

/-- **Algorithm 1** (two-phase consensus), with ids in `ℕ`. The decision rule looks for a
`decided(0)` message in `R1 ∪ R2` (see `TwoPhase.decRule`). -/
noncomputable def twoPhase : Algorithm ℕ Msg St :=
  ⟨TwoPhase.init, TwoPhase.recv, TwoPhase.ack, bcast, out⟩

namespace TwoPhase

open Function

variable {V : Type*} [DecidableEq V] {id : V → ℕ} {inp : V → Bool}

variable (id inp) in
/-- The invariant on configurations. -/
def Inv (c : Config V Msg St) : Prop :=
  Inv' id inp (fun x => (c.loc x).st) (fun x => (c.loc x).cur) (fun x => (c.loc x).dec) c.got
    c.acks

omit [DecidableEq V] in
lemma inv_init : Inv id inp (Config.init twoPhase id inp) := by
  refine
    { myid := fun _ => rfl, v := fun _ => rfl, ph1 := fun _ => le_rfl, ph4 := ?_
      cur := fun _ => rfl, dec := fun _ => rfl, acks := fun _ => rfl, r2 := fun _ _ => rfl
      own2 := ?_, status := ?_, wid := ?_, ready3 := ?_, ready4 := ?_, valid := ?_, got := ?_
      p1 := ?_, p2 := ?_, agreeA := ?_, wit := ?_, bival := ?_ } <;>
  simp [Config.init, Algorithm.initNode, twoPhase, TwoPhase.init, R, Valid]
  exact fun x => ⟨x, rfl, rfl⟩

lemma update_comp {β : Type*} (l : V → Node Msg St) (x : V) (N : Node Msg St)
    (f : Node Msg St → β) :
    (fun w => f (update l x N w)) = update (fun w => f (l w)) x (f N) := by
  funext w; rcases eq_or_ne w x with rfl | hw <;> simp [*]

lemma update_st (l : V → Node Msg St) (x : V) (N : Node Msg St) :
    (fun w => (update l x N w).st) = update (fun w => (l w).st) x N.st :=
  update_comp l x N Node.st

lemma update_cur (l : V → Node Msg St) (x : V) (N : Node Msg St) :
    (fun w => (update l x N w).cur) = update (fun w => (l w).cur) x N.cur :=
  update_comp l x N Node.cur

lemma update_dec (l : V → Node Msg St) (x : V) (N : Node Msg St) :
    (fun w => (update l x N w).dec) = update (fun w => (l w).dec) x N.dec :=
  update_comp l x N Node.dec

lemma down_step (c : Config V Msg St) (e : Event V) :
    c.down ⊆ (step twoPhase ⊤ c e).down := by
  rcases e with ⟨u, v⟩ | u | u | _ <;> simp only [step]
  · split
    · split_ifs <;> exact subset_rfl
    · exact subset_rfl
  · split_ifs <;> exact subset_rfl
  · exact Set.subset_insert _ _
  · exact subset_rfl

lemma inv_step {c : Config V Msg St} (hI : Inv id inp c) (e : Event V)
    (hd : (step twoPhase ⊤ c e).down = ∅) : Inv id inp (step twoPhase ⊤ c e) := by
  have hc : c.down = ∅ := Set.subset_eq_empty (down_step c e) hd
  rcases e with ⟨u, x⟩ | x | u | _
  · simp only [step]
    split
    · rename_i m hm
      by_cases hen : u ∉ c.down ∧ (⊤ : SimpleGraph V).Adj u x ∧ x ∉ c.got u
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hen), ite_eq_right_of_eq_false _ _ (eq_false (by simp [hc]))]
        have := hI.recv (x := x) hm
        unfold Inv
        simp only [update_st, update_cur, update_dec]
        exact this
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hen)]; exact hI
    · exact hI
  · simp only [step]
    split_ifs with hen
    · obtain ⟨hl, -, hall⟩ := hen
      have hall' : ∀ w, w ≠ x → w ∈ c.got x := fun w hw => hall w (Ne.symm hw)
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hl
      have hb : bcast (c.loc x).st = some m := (hI.cur x).symm.trans hm
      unfold Inv
      simp only [update_st, update_cur, update_dec]
      rcases bcast_some hb with ⟨h1, -⟩ | ⟨h2, -⟩
      · exact hI.ack1 h1 hall'
      · exact hI.ack2 h2 hall'
    · exact hI
  · exact absurd hd (Set.insert_nonempty _ _).ne_empty
  · exact hI

lemma inv_foldl (l : List (Event V)) {c : Config V Msg St} (hI : Inv id inp c)
    (hd : (l.foldl (step twoPhase ⊤) c).down = ∅) : Inv id inp (l.foldl (step twoPhase ⊤) c) := by
  induction l generalizing c with
  | nil => exact hI
  | cons e l ih =>
    have hsub : ∀ c' : Config V Msg St, c'.down ⊆ (l.foldl (step twoPhase ⊤) c').down := by
      clear ih hI hd
      induction l with
      | nil => exact fun _ => subset_rfl
      | cons e' l ih' => exact fun c' => (down_step c' e').trans (ih' _)
    exact ih (inv_step hI e (Set.subset_eq_empty (hsub _) hd)) hd

lemma inv_run (σ : ℕ → List (Event V))
    (hd : ∀ i, (run twoPhase ⊤ (Config.init twoPhase id inp) σ i).down = ∅) (i : ℕ) :
    Inv id inp (run twoPhase ⊤ (Config.init twoPhase id inp) σ i) := by
  induction i with
  | zero => exact inv_init
  | succ i ih => exact inv_foldl _ ih (hd (i + 1))

end TwoPhase


/-! ### Theorem 4.1 -/

open TwoPhase Filter

/-- **Theorem 4.1 (time).** In a crash-free timely execution on the clique, with unique ids,
every node decides by time `2 F_ack`. -/
theorem theorem_4_1_time {V : Type*} [Fintype V] [DecidableEq V] (id : V → ℕ)
    (_hid : Function.Injective id) (inp : V → Bool) (σ : ℕ → List (Event V)) (T : ℕ → ℝ) (F : ℝ)
    (hT : Timely twoPhase ⊤ (Config.init twoPhase id inp) σ T F)
    (hcf : ∀ i, (run twoPhase ⊤ (Config.init twoPhase id inp) σ i).down = ∅) (u : V) :
    ∃ i, ((run twoPhase ⊤ (Config.init twoPhase id inp) σ i).loc u).dec.isSome ∧ T i ≤ 2 * F := by
  set c := run twoPhase ⊤ (Config.init twoPhase id inp) σ with hc
  have hI : ∀ i, Inv id inp (c i) := inv_run σ hcf
  obtain ⟨hmono, hT0, hfr⟩ := hT
  -- every node completes its phase-2 broadcast by time `2 F`
  have key : ∀ w, ∃ j, T j ≤ 2 * F ∧ 2 ≤ (c j).acks w := by
    intro w
    have hlive0 : (c 0).Live w := by
      simp [hc, Config.Live, Config.init, Algorithm.initNode, twoPhase, TwoPhase.init, bcast]
    obtain ⟨j₁, -, hTj₁, hp₁⟩ := hfr w 0 hlive0
    have ha0 : (c 0).acks w = 0 := rfl
    have hj₁ : 1 ≤ (c j₁).acks w := by
      rcases hp₁ with h | h
      · rw [ha0] at h; exact h
      · rw [hcf j₁] at h; exact absurd h (Set.notMem_empty w)
    have hF : 0 ≤ F := by
      have := hmono (Nat.zero_le j₁); rw [hT0] at hTj₁ this; linarith
    have hex : ∃ k, 1 ≤ (c k).acks w := ⟨j₁, hj₁⟩
    set i₁ := Nat.find hex with hi₁
    have hi₁j : i₁ ≤ j₁ := Nat.find_min' hex hj₁
    have hTi₁ : T i₁ ≤ F := by have := hmono hi₁j; rw [hT0] at hTj₁; linarith
    have hspec : 1 ≤ (c i₁).acks w := Nat.find_spec hex
    obtain ⟨k, hk⟩ : ∃ k, i₁ = k + 1 := by
      rcases h : i₁ with _ | k
      · rw [h, ha0] at hspec; omega
      · exact ⟨k, rfl⟩
    have hak : (c k).acks w = 0 := by
      have := Nat.find_min hex (show k < i₁ by omega); omega
    by_cases h2 : 2 ≤ (c i₁).acks w
    · exact ⟨i₁, by linarith, h2⟩
    · have ha1 : (c i₁).acks w = 1 := by omega
      have hph : ((c i₁).loc w).st.phase = 2 := by
        have h1 := (hI i₁).acks w; have h2 := (hI i₁).ph1 w
        omega
      have hlive : (c i₁).Live w := by
        unfold Config.Live; rw [(hI i₁).cur w]; simp [bcast, hph]
      have hfresh : Fresh twoPhase ⊤ (Config.init twoPhase id inp) σ w (k + 1) := by
        refine ⟨hk ▸ hlive, fun h => ?_⟩
        have := h.2; rw [← hc, ← hk] at this; omega
      obtain ⟨j₂, hj₂, hTj₂, hp₂⟩ := hfr w (k + 1) hfresh
      refine ⟨j₂, by rw [← hk] at hTj₂; linarith, ?_⟩
      rcases hp₂ with h | h
      · rw [← hc, ← hk, ha1] at h; exact h
      · rw [hcf j₂] at h; exact absurd h (Set.notMem_empty w)
  choose J hJ using key
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_max_image Finset.univ J ⟨u, Finset.mem_univ u⟩
  refine ⟨J w₀, ?_, (hJ w₀).1⟩
  have hall : ∀ w, 3 ≤ ((c (J w₀)).loc w).st.phase := by
    intro w
    have h1 := (mono_run twoPhase ⊤ w (Config.init twoPhase id inp) σ
      (hw₀ w (Finset.mem_univ w))).acks_le
    have h2 := (hI (J w₀)).acks w
    have h3 := (hJ w).2
    rw [← hc] at h1
    omega
  have h4 := (hI (J w₀)).phase_four hall u
  rw [(hI (J w₀)).dec u]
  simp [out, h4]

/-- **Theorem 4.1 (correctness).** Two-phase consensus solves consensus on single-hop networks
(the clique) with unique ids and no crashes, without knowledge of `n`. -/
theorem theorem_4_1 {V : Type*} [Fintype V] [DecidableEq V] (id : V → ℕ)
    (hid : Function.Injective id) : SolvesConsensus twoPhase (⊤ : SimpleGraph V) id 0 := by
  intro inp σ T F hT _ hf
  set c := run twoPhase ⊤ (Config.init twoPhase id inp) σ with hc
  have hcf : ∀ i, (c i).down = ∅ := fun i =>
    Set.encard_eq_zero.1 (nonpos_iff_eq_zero.1 (by exact_mod_cast hf i))
  have hI : ∀ i, Inv id inp (c i) := inv_run σ hcf
  have hdec : ∀ i u b, ((c i).loc u).dec = some b →
      ((c i).loc u).st.phase = 4 ∧ decRule ((c i).loc u).st = b := fun i u b h =>
    out_eq_some (((hI i).dec u).symm.trans h)
  refine ⟨?_, ?_, ?_⟩
  · intro i j u v b b' hu hv
    have hu' := (mono_run twoPhase ⊤ u _ σ (le_max_left i j)).dec_eq b hu
    have hv' := (mono_run twoPhase ⊤ v _ σ (le_max_right i j)).dec_eq b' hv
    obtain ⟨hu4, rfl⟩ := hdec _ u b hu'
    obtain ⟨hv4, rfl⟩ := hdec _ v b' hv'
    exact (hI _).agree hid hu4 hv4
  · intro i u b h
    obtain ⟨h4, rfl⟩ := hdec i u b h
    exact (hI i).valid_dec h4
  · intro u _
    obtain ⟨i, hi, -⟩ := theorem_4_1_time id hid inp σ T F hT hcf u
    exact ⟨i, hi⟩


/-! ### The literal decision rule of the pseudocode is wrong -/

namespace TwoPhase

open Classical in
/-- Line 23 of Algorithm 1, literally: look for `decided(0)` in `R2` only. -/
noncomputable def decRuleLit (s : St) : Bool :=
  if ∃ i, Msg.p2 i (.decided false) ∈ s.R2 then false else true

open Classical in
/-- The literal decision. -/
noncomputable def outLit (s : St) : Option Bool := if s.phase = 4 then some (decRuleLit s) else none

end TwoPhase

/-- Algorithm 1 with the literal line 23. -/
noncomputable def twoPhaseLit : Algorithm ℕ Msg St :=
  ⟨TwoPhase.init, TwoPhase.recv, TwoPhase.ack, bcast, TwoPhase.outLit⟩

namespace TwoPhase

/-- The schedule of the counterexample: node `false` (id 0, input 0) and node `true` (id 1,
input 1). -/
def cexSched : ℕ → List (Event Bool)
  | 0 => [.recv false true]
  | 1 => [.ack false]
  | 2 => [.recv false true]
  | 3 => [.recv true false]
  | 4 => [.ack true]
  | 5 => [.recv true false]
  | 6 => [.ack false]
  | 7 => [.ack true]
  | _ => []

/-- The run of the counterexample. -/
noncomputable def cex : ℕ → Config Bool Msg St :=
  run twoPhaseLit ⊤ (Config.init twoPhaseLit Bool.toNat id) cexSched

lemma cex_succ (k : ℕ) : cex (k + 1) = (cexSched k).foldl (step twoPhaseLit ⊤) (cex k) := rfl

/-- A configuration of the two-node network. -/
def mkC (Nu Nx : Node Msg St) (gu gx : Set Bool) (au ax : ℕ) : Config Bool Msg St :=
  ⟨fun b => cond b Nx Nu, fun b => cond b gx gu, ∅, fun b => cond b ax au⟩

section Steps

variable {Nu Nx : Node Msg St} {gu gx : Set Bool} {au ax : ℕ} {m : Msg}

lemma step_recv_ft (h : Nu.cur = some m) (hg : true ∉ gu) :
    step twoPhaseLit ⊤ (mkC Nu Nx gu gx au ax) (.recv false true) =
      mkC Nu (twoPhaseLit.recvNode Nx m) (insert true gu) gx au ax := by
  have h' : ((mkC Nu Nx gu gx au ax).loc false).cur = some m := h
  simp only [step, h']
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by simp [mkC], by simp, by simpa [mkC] using hg⟩),
    ite_eq_right_of_eq_false _ _ (eq_false (by simp [mkC]))]
  simp only [mkC, Config.mk.injEq, and_true]
  constructor <;> funext b <;> cases b <;> simp

lemma step_recv_tf (h : Nx.cur = some m) (hg : false ∉ gx) :
    step twoPhaseLit ⊤ (mkC Nu Nx gu gx au ax) (.recv true false) =
      mkC (twoPhaseLit.recvNode Nu m) Nx gu (insert false gx) au ax := by
  have h' : ((mkC Nu Nx gu gx au ax).loc true).cur = some m := h
  simp only [step, h']
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by simp [mkC], by simp, by simpa [mkC] using hg⟩),
    ite_eq_right_of_eq_false _ _ (eq_false (by simp [mkC]))]
  simp only [mkC, Config.mk.injEq, and_true]
  constructor <;> funext b <;> cases b <;> simp

lemma step_ack_f (h : Nu.cur.isSome) (hg : true ∈ gu) :
    step twoPhaseLit ⊤ (mkC Nu Nx gu gx au ax) (.ack false) =
      mkC (twoPhaseLit.ackNode Nu) Nx ∅ gx (au + 1) ax := by
  simp only [step]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by simpa [mkC] using h, by simp [mkC], fun v hv => by
    cases v <;> simp_all [mkC]⟩)]
  simp only [mkC, Config.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> funext b <;> cases b <;> simp

lemma step_ack_t (h : Nx.cur.isSome) (hg : false ∈ gx) :
    step twoPhaseLit ⊤ (mkC Nu Nx gu gx au ax) (.ack true) =
      mkC Nu (twoPhaseLit.ackNode Nx) gu ∅ au (ax + 1) := by
  simp only [step]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by simpa [mkC] using h, by simp [mkC], fun v hv => by
    cases v <;> simp_all [mkC]⟩)]
  simp only [mkC, Config.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> funext b <;> cases b <;> simp

end Steps

/-- Messages of the counterexample. -/
abbrev p1u : Msg := .p1 0 false
abbrev p1x : Msg := .p1 1 true
abbrev p2u : Msg := .p2 0 (.decided false)
abbrev p2x : Msg := .p2 1 .bivalent

/-- Node states of the counterexample (`u = false`, `x = true`). -/
def N0u : Node Msg St := ⟨⟨0, false, 1, {p1u}, ∅, .bivalent, ∅⟩, none, some p1u⟩
def N0x : Node Msg St := ⟨⟨1, true, 1, {p1x}, ∅, .bivalent, ∅⟩, none, some p1x⟩
def N1x : Node Msg St := ⟨⟨1, true, 1, insert p1u {p1x}, ∅, .bivalent, ∅⟩, none, some p1x⟩
def N2u : Node Msg St := ⟨⟨0, false, 2, {p1u}, {p2u}, .decided false, ∅⟩, none, some p2u⟩
def N3x : Node Msg St :=
  ⟨⟨1, true, 1, insert p2u (insert p1u {p1x}), ∅, .bivalent, ∅⟩, none, some p1x⟩
def N4u : Node Msg St :=
  ⟨⟨0, false, 2, {p1u}, insert p1x {p2u}, .decided false, ∅⟩, none, some p2u⟩
def N5x : Node Msg St :=
  ⟨⟨1, true, 2, insert p2u (insert p1u {p1x}), {p2x}, .bivalent, ∅⟩, none, some p2x⟩
def N6u : Node Msg St :=
  ⟨⟨0, false, 2, {p1u}, insert p2x (insert p1x {p2u}), .decided false, ∅⟩, none, some p2u⟩

lemma cex_0 : cex 0 = mkC N0u N0x ∅ ∅ 0 0 := by
  simp only [cex, run_zero, Config.init, mkC, Config.mk.injEq]
  refine ⟨?_, ?_, trivial, ?_⟩ <;> funext b <;> cases b <;>
    simp [N0u, N0x, Algorithm.initNode, twoPhaseLit, TwoPhase.init, outLit, bcast]

lemma cex_1 : cex 1 = mkC N0u N1x {true} ∅ 0 0 := by
  rw [cex_succ, cex_0]
  simp only [cexSched, List.foldl]
  rw [step_recv_ft rfl (by simp)]
  congr 1
  simp

lemma cex_2 : cex 2 = mkC N2u N1x ∅ ∅ 1 0 := by
  rw [cex_succ, cex_1]
  simp only [cexSched, List.foldl]
  rw [step_ack_f rfl (by simp)]
  congr 1
  simp [N0u, N2u, Algorithm.ackNode, twoPhaseLit, TwoPhase.ack, outLit, bcast, statusOf]

lemma cex_3 : cex 3 = mkC N2u N3x {true} ∅ 1 0 := by
  rw [cex_succ, cex_2]
  simp only [cexSched, List.foldl]
  rw [step_recv_ft rfl (by simp)]
  congr 1
  simp

lemma cex_4 : cex 4 = mkC N4u N3x {true} {false} 1 0 := by
  rw [cex_succ, cex_3]
  simp only [cexSched, List.foldl]
  rw [step_recv_tf rfl (by simp)]
  congr 1
  simp

lemma cex_5 : cex 5 = mkC N4u N5x {true} ∅ 1 1 := by
  rw [cex_succ, cex_4]
  simp only [cexSched, List.foldl]
  rw [step_ack_t rfl (by simp)]
  congr 1
  simp [N3x, N5x, Algorithm.ackNode, twoPhaseLit, TwoPhase.ack, outLit, bcast, statusOf]

lemma cex_6 : cex 6 = mkC N6u N5x {true} {false} 1 1 := by
  rw [cex_succ, cex_5]
  simp only [cexSched, List.foldl]
  rw [step_recv_tf rfl (by simp)]
  congr 1
  simp

lemma cex_7 : cex 7 = mkC (twoPhaseLit.ackNode N6u) N5x ∅ {false} 2 1 := by
  rw [cex_succ, cex_6]
  simp only [cexSched, List.foldl]
  rw [step_ack_f rfl (by simp)]

lemma cex_8 : cex 8 = mkC (twoPhaseLit.ackNode N6u) (twoPhaseLit.ackNode N5x) ∅ ∅ 2 2 := by
  rw [cex_succ, cex_7]
  simp only [cexSched, List.foldl]
  rw [step_ack_t rfl (by simp)]

lemma ack_two_ready {s : St} (h : s.phase = 2)
    (hr : Ready { s with phase := 3, W := Msg.id '' R s }) :
    TwoPhase.ack s = { s with phase := 4, W := Msg.id '' R s } := by
  simp only [TwoPhase.ack, h]
  simp only [OfNat.ofNat_ne_one, ite_false, ite_true]
  unfold check
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hr⟩)]

lemma ackNode_N6u : (twoPhaseLit.ackNode N6u).dec = some false ∧
    (twoPhaseLit.ackNode N6u).cur = none := by
  have hR : Ready { N6u.st with phase := 3, W := Msg.id '' R N6u.st } := by
    simp [Ready, R, N6u, Msg.id]
  have h := ack_two_ready (s := N6u.st) rfl hR
  simp only [Algorithm.ackNode, twoPhaseLit, h]
  simp [N6u, outLit, decRuleLit, bcast]

lemma ackNode_N5x : (twoPhaseLit.ackNode N5x).dec = some true ∧
    (twoPhaseLit.ackNode N5x).cur = none := by
  have hR : Ready { N5x.st with phase := 3, W := Msg.id '' R N5x.st } := by
    simp [Ready, R, N5x, Msg.id]
  have h := ack_two_ready (s := N5x.st) rfl hR
  simp only [Algorithm.ackNode, twoPhaseLit, h]
  simp [N5x, outLit, decRuleLit, bcast]

lemma cexSched_ge {j : ℕ} (hj : 8 ≤ j) : cexSched j = [] := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | omega | rfl

lemma cex_ge (k : ℕ) : cex (8 + k) = cex 8 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, cex_succ, cexSched_ge (by omega), List.foldl_nil, ih]

lemma cex_eq_of_ge {i : ℕ} (hi : 8 ≤ i) : cex i = cex 8 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi; exact cex_ge k

lemma cex_down (i : ℕ) : (cex i).down = ∅ := by
  by_cases hi : 8 ≤ i
  · rw [cex_eq_of_ge hi, cex_8]; rfl
  · interval_cases i <;>
      simp only [cex_0, cex_1, cex_2, cex_3, cex_4, cex_5, cex_6, cex_7] <;> rfl

lemma cex_timely : Timely twoPhaseLit ⊤ (Config.init twoPhaseLit Bool.toNat id) cexSched
    (fun i => (i : ℝ)) 8 := by
  refine ⟨Nat.mono_cast, Nat.cast_zero, fun w i hfr => ?_⟩
  have hl : (cex i).Live w := hfr.live
  by_cases hi : 8 ≤ i
  · exfalso
    rw [cex_eq_of_ge hi, cex_8] at hl
    cases w <;> simp [Config.Live, mkC, ackNode_N6u.2, ackNode_N5x.2] at hl
  · refine ⟨8, by omega, by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)], Or.inl ?_⟩
    show (cex i).acks w < (cex 8).acks w
    rw [cex_8]
    have h7 := ackNode_N6u.2
    interval_cases i <;> cases w <;>
      simp_all [Config.Live, mkC, cex_0, cex_1, cex_2, cex_3, cex_4, cex_5, cex_6, cex_7]

end TwoPhase

open TwoPhase in
/-- **The literal pseudocode is wrong.** With line 23 read literally (`decided(0)` looked up in
`R2` only), Algorithm 1 violates agreement on two nodes: node `u` (id 0, input 0) completes
phase 1 while `x` (id 1, input 1) is still in phase 1, so `u` has status `decided(0)`; `x`
receives `⟨phase 2, 0, decided(0)⟩` during *its phase 1* (so in `R1`), becomes bivalent, and
decides `1` because `R2 = {⟨phase 2, 1, bivalent⟩}`, while `u` decides `0`. -/
theorem twoPhaseLit_not_solvesConsensus :
    ¬ SolvesConsensus twoPhaseLit (⊤ : SimpleGraph Bool) Bool.toNat 0 := by
  intro h
  obtain ⟨hA, -, -⟩ := h id cexSched (fun i => (i : ℝ)) 8 cex_timely
    tendsto_natCast_atTop_atTop (fun i => by
      rw [show run twoPhaseLit ⊤ (Config.init twoPhaseLit Bool.toNat id) cexSched i = cex i
        from rfl, cex_down]; simp)
  have hu : ((cex 8).loc false).dec = some false := by
    rw [cex_8]; exact ackNode_N6u.1
  have hx : ((cex 8).loc true).dec = some true := by
    rw [cex_8]; exact ackNode_N5x.1
  exact absurd (hA 8 8 false true false true hu hx) (by decide)

end Podc.AbstractMACConsensus
