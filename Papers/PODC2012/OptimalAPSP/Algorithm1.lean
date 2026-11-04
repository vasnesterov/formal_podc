import Papers.PODC2012.OptimalAPSP.Pebble
import Podc.Computability.Distributed.Congest.Typed
import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree

/-!
# Algorithm 1 of [HW12] as a CONGEST algorithm: APSP in `O(n)` rounds (Theorem 1)

The algorithm `apsp r` (for a root `r`, "the node with ID 1"; `n = |V|` is known to all nodes)
runs in three stages, switched by a round counter:

1. rounds `1 … n`: a BFS from `r` builds the tree `T₁` (every node learns its parent; in the last
   round every node learns its children from its neighbours' messages);
2. from round `n + 1` on: the pebble traverses `T₁` depth-first (`Pebble.lean`); when it enters a
   node `v` for the first time, it waits one slot and `v` starts `BFS_v`: a wave carrying the
   token `(v, distance)` that every node forwards to all neighbours once, in the round after it
   first receives it. By Lemma 1 a node never has to forward two tokens in the same round, so a
   message carries at most one token;
3. from round `5n` on: eccentricities are flooded (max and min) for `n` more rounds, giving the
   diameter and the radius (Lemmas 2–6).

Messages: one tree-message (`Option (Option V)`), one pebble bit, one token (ID and a distance
`< n + 1`), two numbers `< n + 1`; i.e. `O(log n)` bits (`msgBits_le`).
-/

namespace Podc.OptimalAPSP

open Finset Cslib.Congest

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Messages of Algorithm 1 (`k = n + 1` bounds the numbers). -/
structure Msg1 (V : Type*) (k : ℕ) where
  /-- Stage 1: `none` = not yet in `T₁`; `some p` = in `T₁` with parent `p` (`none` at the root). -/
  tr : Option (Option V)
  /-- Stage 2: the pebble is sent to the receiver. -/
  peb : Bool
  /-- Stage 2: a BFS token `(u, d(u, sender))`. -/
  tok : Option (V × Fin k)
  /-- Stage 3: the largest eccentricity seen. -/
  mx : Fin k
  /-- Stage 3: the smallest eccentricity seen. -/
  mn : Fin k
  deriving Fintype

/-- Local state of Algorithm 1. -/
structure St (V : Type*) where
  /-- Round counter. -/
  clk : ℕ
  /-- Joined `T₁`. -/
  inT : Bool
  /-- Parent in `T₁` (`none` at the root). -/
  par : Option V
  /-- Children in `T₁` (valid from round `n`). -/
  kids : Finset V
  /-- The pebble has entered this node. -/
  ent : Bool
  /-- `some false`: the pebble is here and waits; `some true`: here and ready; `none`: not here. -/
  peb : Option Bool
  /-- Children the pebble has not been sent to yet. -/
  pend : Finset V
  /-- Distances learned so far: `dist u = some d(u, v)` (the APSP output). -/
  dist : V → Option ℕ
  /-- The token to forward in the next round. -/
  fwd : Option (V × ℕ)
  /-- Stage 3: largest eccentricity seen. -/
  mx : ℕ
  /-- Stage 3: smallest eccentricity seen. -/
  mn : ℕ

variable (V) in
/-- The message type. -/
abbrev M1 := Msg1 V (Fintype.card V + 1)

instance : Nonempty (M1 V) := ⟨⟨none, false, none, 0, 0⟩⟩

/-- Numbers are sent capped at `n` (we show no capping ever happens). -/
def cap (d : ℕ) : Fin (Fintype.card V + 1) := ⟨min d (Fintype.card V), by omega⟩

/-- Target of a ready pebble at a node with state `s`: the smallest pending child, else the
parent. -/
def tgt (s : St V) : Option V :=
  if h : s.pend.Nonempty then some (s.pend.min' h) else s.par

/-- The message from a node in state `s` to neighbour `w`. -/
def sendFn (s : St V) (w : V) : M1 V where
  tr := if s.inT then some s.par else none
  peb := decide (s.peb = some true ∧ tgt s = some w)
  tok := s.fwd.map fun p => (p.1, cap p.2)
  mx := cap s.mx
  mn := cap s.mn

/-- Eccentricity estimate from a distance table. -/
def eccOf (d : V → Option ℕ) : ℕ := univ.sup fun u => (d u).getD 0

/-- Pebble field after a round without arrival. -/
def pebKeep (s : St V) : Option Bool :=
  match s.peb with
  | some false => some true
  | some true => if tgt s = none then some true else none
  | none => none

/-- Pending children after a round (when not re-initialised). -/
def pendKeep (s : St V) : Finset V :=
  if s.peb = some true then (match tgt s with | some x => s.pend.erase x | none => s.pend)
  else s.pend

/-- Stage 1: senders that have joined `T₁`. -/
def joinedSet (m : V → Option (M1 V)) : Finset V :=
  univ.filter fun w => (m w).any fun x => x.tr.isSome

/-- Stage 1: senders whose parent is `v`. -/
def kidSet (v : V) (m : V → Option (M1 V)) : Finset V :=
  univ.filter fun w => (m w).any fun x => decide (x.tr = some (some v))

/-- Stage 2: the pebble arrives. -/
def RecvP (m : V → Option (M1 V)) : Prop :=
  (univ.filter fun w => (m w).any fun x => x.peb).Nonempty

/-- Stage 2: the pebble enters `v` for the first time in this round (or `v = r` and stage 2
begins), so `BFS_v` starts. -/
def StartP (r v : V) (s : St V) (m : V → Option (M1 V)) : Prop :=
  (s.clk + 1 = Fintype.card V ∧ v = r) ∨ (RecvP m ∧ s.ent = false)

/-- Stage 2: token `(u, d)` received from some neighbour. -/
def TokR (m : V → Option (M1 V)) (u : V) (d : ℕ) : Prop :=
  ∃ w x p, m w = some x ∧ x.tok = some p ∧ p.1 = u ∧ p.2.val = d

open Classical in
/-- Stage 2: updated distance table. -/
noncomputable def distUpd (r v : V) (s : St V) (m : V → Option (M1 V)) (u : V) : Option ℕ :=
  match s.dist u with
  | some k => some k
  | none => if StartP r v s m ∧ u = v then some 0 else
      if h : ∃ d, TokR m u d then some (Nat.find h + 1) else none

/-- Stage 2: some token not known before arrives. -/
def NewTok (s : St V) (m : V → Option (M1 V)) : Prop := ∃ u, s.dist u = none ∧ ∃ d, TokR m u d

open Classical in
/-- Stage 2: the token to forward next. -/
noncomputable def fwdUpd (r v : V) (s : St V) (m : V → Option (M1 V)) : Option (V × ℕ) :=
  if StartP r v s m then some (v, 0) else if h : NewTok s m then
    some (Classical.choose h, (distUpd r v s m (Classical.choose h)).getD 0) else none

open Classical in
/-- The state update of node `v` (root `r`). -/
noncomputable def stepFn (r v : V) (s : St V) (m : V → Option (M1 V)) : St V where
  clk := s.clk + 1
  inT := s.inT || decide (joinedSet m).Nonempty
  par := if s.inT then s.par else if h : (joinedSet m).Nonempty then some ((joinedSet m).min' h)
    else none
  kids := kidSet v m
  ent := s.ent || decide (StartP r v s m)
  peb := if StartP r v s m then some false else if RecvP m then some true else pebKeep s
  pend := if s.clk + 1 = Fintype.card V then kidSet v m else pendKeep s
  dist := distUpd r v s m
  fwd := fwdUpd r v s m
  mx := if s.clk + 1 = 5 * Fintype.card V then eccOf (distUpd r v s m) else
    univ.fold max s.mx fun w => match m w with | some x => x.mx.val | none => 0
  mn := if s.clk + 1 = 5 * Fintype.card V then eccOf (distUpd r v s m) else
    univ.fold min s.mn fun w => match m w with | some x => x.mn.val | none => s.mn

/-- **Algorithm 1** of [HW12] (with the aggregation of Lemmas 2–6), as a typed CONGEST algorithm
with root `r`. Node inputs are ignored (every node learns its neighbours from the messages). -/
noncomputable def apsp (I : Type*) (r : V) : TAlgorithm V I (St V) (M1 V) where
  init v _ := ⟨0, decide (v = r), none, ∅, false, none, ∅, fun _ => none, none, 0, 0⟩
  send _ s w := sendFn s w
  step v s m := stepFn r v s m

/-- Messages of Algorithm 1 have `O(log n)` bits: at most `5 ⌈log₂ (n + 1)⌉ + 2`. -/
theorem msgBits_le : TAlgorithm.msgBits (M1 V) ≤ 5 * Nat.clog 2 (Fintype.card V + 1) + 2 := by
  classical
  set n := Fintype.card V
  set c := Nat.clog 2 (n + 1)
  have hinj : Function.Injective fun m : M1 V => (m.tr, m.peb, m.tok, m.mx, m.mn) := by
    rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  have h1 := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_fin] at h1
  have hc : n + 1 ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have h2 : Fintype.card (M1 V) ≤ 2 ^ (5 * c + 2) := by
    have e1 : (n + 1 + 1) * (2 * ((n * (n + 1) + 1) * ((n + 1) * (n + 1)))) ≤
        4 * (n + 1) ^ 5 := by
      have : n * (n + 1) + 1 ≤ (n + 1) ^ 2 := by nlinarith
      have : n + 1 + 1 ≤ 2 * (n + 1) := by omega
      calc (n + 1 + 1) * (2 * ((n * (n + 1) + 1) * ((n + 1) * (n + 1))))
          ≤ (2 * (n + 1)) * (2 * ((n + 1) ^ 2 * ((n + 1) * (n + 1)))) := by gcongr
        _ = 4 * (n + 1) ^ 5 := by ring
    have e2 : 4 * (n + 1) ^ 5 ≤ 2 ^ (5 * c + 2) := by
      rw [pow_add, pow_mul, mul_comm]
      have : (n + 1) ^ 5 ≤ (2 ^ c) ^ 5 := Nat.pow_le_pow_left hc 5
      calc (n + 1) ^ 5 * 4 ≤ (2 ^ c) ^ 5 * 4 := by gcongr
        _ = (2 ^ 5) ^ c * 2 ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm c 5]; norm_num
    exact h1.trans (e1.trans e2)
  unfold TAlgorithm.msgBits
  have := Nat.clog_le_of_le_pow h2
  omega

section Analysis

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbours of `v` one step closer to `r`. -/
noncomputable def closer (r v : V) : Finset V := by
  classical exact univ.filter fun w => G.Adj w v ∧ G.dist r w + 1 = G.dist r v

/-- The parent of `v` in `T₁`: its smallest neighbour one step closer to `r`. -/
noncomputable def bpar (r v : V) : V :=
  if h : (closer G r v).Nonempty then (closer G r v).min' h else r

lemma mem_closer {r v w : V} : w ∈ closer G r v ↔ G.Adj w v ∧ G.dist r w + 1 = G.dist r v := by
  classical simp [closer]

variable {G}

lemma closer_nonempty (hconn : G.Connected) (r : V) {v : V} (hv : v ≠ r) :
    (closer G r v).Nonempty := by
  obtain ⟨w, hw, hd⟩ := hconn.exists_adj_dist_succ r hv
  exact ⟨w, (mem_closer G).2 ⟨hw.symm, hd⟩⟩

lemma bpar_spec (hconn : G.Connected) (r : V) {v : V} (hv : v ≠ r) :
    G.Adj (bpar G r v) v ∧ G.dist r (bpar G r v) + 1 = G.dist r v := by
  unfold bpar
  rw [dif_pos (closer_nonempty hconn r hv)]
  exact (mem_closer G).1 (min'_mem _ _)

lemma dist_lt_card (hconn : G.Connected) (u v : V) : G.dist u v < Fintype.card V := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  rw [← hp]
  exact (p.isPath_of_length_eq_dist hp).length_lt

/-- The tree `T₁` built in stage 1. -/
noncomputable def tree1 (hconn : G.Connected) (r : V) : RTree V where
  root := r
  par v := if v = r then r else bpar G r v
  dep v := G.dist r v
  par_root := by simp
  dep_par v hv := by rw [if_neg hv]; exact (bpar_spec hconn r hv).2

lemma exists_ite_some {α β : Type*} {c : Prop} [Decidable c] {y : α} {P : α → Prop} :
    (∃ x, (if c then some y else none) = some x ∧ P x) ↔ c ∧ P y := by
  split_ifs with h <;> simp [h]

variable (I : Type*) (inp : V → I) (r : V)

/-- Shorthand for the execution. -/
noncomputable abbrev S (t : ℕ) (v : V) : St V := (apsp I r).run G inp t v

lemma S_succ (t : ℕ) (v : V) :
    S (G := G) I inp r (t + 1) v = stepFn r v (S (G := G) I inp r t v)
      (fun w => if G.Adj w v then some (sendFn (S (G := G) I inp r t w) v) else none) := rfl

lemma clk_S : ∀ t v, (S (G := G) I inp r t v).clk = t
  | 0, _ => rfl
  | t + 1, v => by rw [S_succ, stepFn]; simp only [clk_S t v]

lemma dist_le_of_adj (hconn : G.Connected) {u w v : V} (h : G.Adj w v) :
    G.dist u v ≤ G.dist u w + 1 := by
  have := hconn.dist_triangle (u := u) (v := w) (w := v)
  rwa [SimpleGraph.dist_eq_one_iff_adj.2 h] at this

/-- Reaching distance `t + 1` from `u`: through a neighbour at distance `t`. -/
lemma dist_le_succ_iff (hconn : G.Connected) (u v : V) (t : ℕ) :
    G.dist u v ≤ t + 1 ↔ G.dist u v ≤ t ∨ ∃ w, G.Adj w v ∧ G.dist u w ≤ t := by
  constructor
  · intro h
    by_cases h' : G.dist u v ≤ t
    · exact Or.inl h'
    · right
      have hv : v ≠ u := by rintro rfl; simp at h'
      obtain ⟨w, hw, hd⟩ := hconn.exists_adj_dist_succ u hv
      exact ⟨w, hw.symm, by omega⟩
  · rintro (h | ⟨w, hw, hd⟩)
    · omega
    · have := dist_le_of_adj hconn (u := u) hw; omega

/-- **Stage 1**: after `t` rounds, exactly the nodes at distance `≤ t` from `r` have joined `T₁`,
each with its parent `bpar`. -/
lemma stage1 (hconn : G.Connected) : ∀ t v,
    (S (G := G) I inp r t v).inT = decide (G.dist r v ≤ t) ∧
      (S (G := G) I inp r t v).par = if v ≠ r ∧ G.dist r v ≤ t then some (bpar G r v) else none
  | 0, v => by
    have h0 : G.dist r v = 0 ↔ v = r := by
      rw [(hconn.preconnected r v).dist_eq_zero_iff]; exact eq_comm
    refine ⟨?_, ?_⟩
    · show decide (v = r) = _
      simp [h0]
    · show none = _
      rw [if_neg]; rintro ⟨h1, h2⟩; exact h1 (h0.1 (by omega))
  | t + 1, v => by
    have ih := fun w => stage1 hconn t w
    have hJ : joinedSet (fun w => if G.Adj w v then some (sendFn (S (G := G) I inp r t w) v)
        else none) =
        univ.filter fun w => G.Adj w v ∧ G.dist r w ≤ t := by
      ext w
      simp only [joinedSet, mem_filter, mem_univ, true_and]
      by_cases h : G.Adj w v <;> simp [h, sendFn, (ih w).1]
    rw [S_succ, stepFn]
    simp only
    rw [hJ, (ih v).1, (ih v).2]
    have key := dist_le_succ_iff hconn r v t
    by_cases hle : G.dist r v ≤ t
    · simp only [hle, decide_true, Bool.true_or, true_and, ↓reduceIte]
      refine ⟨by symm; simp only [decide_eq_true_eq]; omega, ?_⟩
      by_cases hvr : v = r
      · simp [hvr]
      · rw [if_pos ⟨hvr, trivial⟩, if_pos ⟨hvr, by omega⟩]
    · simp only [hle, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      by_cases hne : (univ.filter fun w => G.Adj w v ∧ G.dist r w ≤ t).Nonempty
      · obtain ⟨w, hw⟩ := hne
        simp only [mem_filter, mem_univ, true_and] at hw
        have hd : G.dist r v = t + 1 := by have := key.2 (Or.inr ⟨w, hw⟩); omega
        have hvr : v ≠ r := by rintro rfl; simp at hd
        have hJc : (univ.filter fun w => G.Adj w v ∧ G.dist r w ≤ t) = closer G r v := by
          ext x
          rw [mem_closer]
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2⟩; have := dist_le_of_adj hconn (u := r) h1; exact ⟨h1, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        refine ⟨by simp only [decide_eq_decide]; exact ⟨fun _ => by omega, fun _ => ⟨w, by simpa using hw⟩⟩, ?_⟩
        rw [dif_pos ⟨w, by simpa using hw⟩, if_pos ⟨hvr, by omega⟩]
        simp only [Option.some.injEq, bpar]
        rw [dif_pos (closer_nonempty hconn r hvr)]
        congr 1
      · rw [dif_neg hne]
        have : ¬ G.dist r v ≤ t + 1 := by
          rw [key]; push_neg
          refine ⟨by omega, fun w hw => ?_⟩
          by_contra h; exact hne ⟨w, by simp [hw]; omega⟩
        refine ⟨by simp only [decide_eq_decide]; exact ⟨fun h => absurd h hne, fun h => absurd h this⟩, ?_⟩
        rw [if_neg]; rintro ⟨-, h⟩; exact this h

/-- The messages received by `v` in round `t + 1`. -/
noncomputable abbrev inbox (t : ℕ) (v : V) : V → Option (M1 V) :=
  fun w => if G.Adj w v then some (sendFn (S (G := G) I inp r t w) v) else none

lemma recvP_inbox (t : ℕ) (v : V) :
    RecvP (inbox (G := G) I inp r t v) ↔
      ∃ w, G.Adj w v ∧ (S (G := G) I inp r t w).peb = some true ∧
        tgt (S (G := G) I inp r t w) = some v := by
  unfold RecvP
  constructor
  · rintro ⟨w, hw⟩
    simp only [mem_filter, mem_univ, true_and] at hw
    by_cases h : G.Adj w v
    · simp only [inbox, h, ↓reduceIte, Option.any_some, sendFn, decide_eq_true_eq] at hw
      exact ⟨w, h, hw⟩
    · simp [inbox, h] at hw
  · rintro ⟨w, h, hw⟩
    exact ⟨w, by simp [inbox, h, sendFn, hw]⟩

lemma kidSet_inbox (hconn : G.Connected) {t : ℕ} (ht : Fintype.card V ≤ t + 1) (v : V) :
    kidSet v (inbox (G := G) I inp r t v) = PState.kids (tree1 hconn r) v := by
  ext w
  rw [PState.mem_kids]
  simp only [kidSet, mem_filter, mem_univ, true_and, RTree.IsKid, tree1]
  have h1 := stage1 I inp r hconn t w
  have hd := dist_lt_card hconn r w
  by_cases hw : w = r
  · subst hw; by_cases h : G.Adj w v <;> simp [inbox, h, sendFn, h1.2]
  · have hb := bpar_spec hconn r hw
    have hle : G.dist r w ≤ t := by omega
    by_cases h : G.Adj w v
    · simp [inbox, h, sendFn, h1.1, h1.2, hw, hle]
    · simp only [inbox, h, ↓reduceIte, Option.any_none, Bool.false_eq_true, false_iff, not_and, hw,
        not_false_eq_true, true_implies, ne_eq]
      rintro rfl; exact h hb.1.symm

/-- Before stage 2 there is no pebble. -/
lemma pre_pebble : ∀ t, t < Fintype.card V → ∀ v,
    (S (G := G) I inp r t v).ent = false ∧ (S (G := G) I inp r t v).peb = none
  | 0, _, v => ⟨rfl, rfl⟩
  | t + 1, ht, v => by
    have ih := fun w => pre_pebble t (by omega) w
    have hR : ¬ RecvP (inbox (G := G) I inp r t v) := by
      rw [recvP_inbox]; rintro ⟨w, -, h, -⟩; rw [(ih w).2] at h; simp at h
    have hS : ¬ StartP r v (S (G := G) I inp r t v) (inbox (G := G) I inp r t v) := by
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · rw [clk_S] at h; omega
      · exact hR h
    rw [S_succ]
    simp only [stepFn, hS, hR, decide_false, Bool.or_false, (ih v).1, ↓reduceIte, pebKeep, (ih v).2,
      and_self]

/-- In stage 2 every node knows its parent. -/
lemma par_S (hconn : G.Connected) {t : ℕ} (ht : Fintype.card V ≤ t + 1) (w : V) :
    (S (G := G) I inp r t w).par = if w = r then none else some (bpar G r w) := by
  rw [(stage1 I inp r hconn t w).2]
  have := dist_lt_card hconn r w
  by_cases hw : w = r
  · simp [hw]
  · rw [if_pos ⟨hw, by omega⟩, if_neg hw]

lemma tgt_eq (hconn : G.Connected) {s : St V} {w : V}
    (hpar : s.par = if w = r then none else some (bpar G r w)) :
    tgt s = target (tree1 hconn r) s.pend w := by
  unfold tgt target
  split_ifs with h1 h2 <;> simp_all [tree1]

lemma target_adj (hconn : G.Connected) (k : ℕ) {x : V}
    (h : target (tree1 hconn r) ((PState.iter (tree1 hconn r) k).pend
      (PState.iter (tree1 hconn r) k).pos) (PState.iter (tree1 hconn r) k).pos = some x) :
    x ≠ (PState.iter (tree1 hconn r) k).pos ∧ G.Adj (PState.iter (tree1 hconn r) k).pos x := by
  set T := tree1 hconn r
  set g := PState.iter T k
  have hinv := PState.iter_inv T k
  unfold target at h
  split_ifs at h with hne hroot
  · simp only [Option.some.injEq] at h
    have hk := (hinv.pend_kid _ _ (h ▸ min'_mem _ _)).1
    obtain ⟨hxr, hpx⟩ := hk
    have hxr' : x ≠ r := hxr
    have hb := bpar_spec hconn r hxr'
    simp only [T, tree1, if_neg hxr'] at hpx
    rw [hpx] at hb
    exact ⟨fun he => hb.1.ne he.symm, hb.1⟩
  · simp only [Option.some.injEq] at h
    have hroot' : g.pos ≠ r := hroot
    have hb := bpar_spec hconn r hroot'
    simp only [T, tree1, if_neg hroot'] at h
    rw [h] at hb
    exact ⟨hb.1.ne, hb.1.symm⟩

/-- **Stage 2, pebble**: from round `n` on, the distributed pebble follows the global traversal
of `Pebble.lean` on `T₁`, slot by slot. -/
lemma pebble_corr (hconn : G.Connected) : ∀ k v,
    (S (G := G) I inp r (Fintype.card V + k) v).ent =
        decide (v ∈ (PState.iter (tree1 hconn r) k).ent) ∧
      (S (G := G) I inp r (Fintype.card V + k) v).peb =
        (if (PState.iter (tree1 hconn r) k).pos = v then
          some (PState.iter (tree1 hconn r) k).ready else none) ∧
      (S (G := G) I inp r (Fintype.card V + k) v).pend = (PState.iter (tree1 hconn r) k).pend v
  | 0, v => by
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 :=
      ⟨Fintype.card V - 1, by have := Fintype.card_pos_iff.2 ⟨r⟩; omega⟩
    have hpre := fun w => pre_pebble (G := G) I inp r m (by omega) w
    have hR : ¬ RecvP (inbox (G := G) I inp r m v) := by
      rw [recvP_inbox]; rintro ⟨w, -, h, -⟩; rw [(hpre w).2] at h; simp at h
    have hS : StartP r v (S (G := G) I inp r m v) (inbox (G := G) I inp r m v) ↔ v = r := by
      simp only [StartP, clk_S, hm, true_and, hR, false_and, or_false]
    rw [add_zero, hm, S_succ]
    have h0 : PState.iter (tree1 hconn r) 0 = PState.init (tree1 hconn r) := rfl
    rw [h0, show (PState.init (tree1 hconn r)).pos = r from rfl,
      show (PState.init (tree1 hconn r)).ent = {r} from rfl,
      show (PState.init (tree1 hconn r)).ready = false from rfl,
      show (PState.init (tree1 hconn r)).pend = PState.kids (tree1 hconn r) from rfl]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [stepFn]
      rw [(hpre v).1, Bool.false_or]
      exact decide_eq_decide.2 (hS.trans mem_singleton.symm)
    · dsimp only [stepFn]
      by_cases hv : v = r
      · rw [if_pos (hS.2 hv), if_pos hv.symm]
      · rw [if_neg (fun h => hv (hS.1 h)), if_neg hR, if_neg (Ne.symm hv)]
        simp [pebKeep, (hpre v).2]
    · dsimp only [stepFn]
      rw [clk_S, if_pos hm.symm]
      exact kidSet_inbox I inp r hconn (by omega) v
  | k + 1, v => by
    classical
    set T := tree1 hconn r with hT
    have ih := fun w => pebble_corr hconn k w
    set g := PState.iter T k with hg
    have hge : PState.iter T (k + 1) = PState.step T g := PState.iter_succ T k
    have hclk : ∀ w, (S (G := G) I inp r (Fintype.card V + k) w).clk + 1 ≠ Fintype.card V := by
      intro w; rw [clk_S]; have := Fintype.card_pos_iff.2 ⟨r⟩; omega
    have htgt : ∀ w, tgt (S (G := G) I inp r (Fintype.card V + k) w) = target T (g.pend w) w := by
      intro w
      rw [tgt_eq r hconn (par_S (G := G) I inp r hconn (by omega) w), (ih w).2.2]
    have hR : ∀ v, RecvP (inbox (G := G) I inp r (Fintype.card V + k) v) ↔
        g.ready = true ∧ target T (g.pend g.pos) g.pos = some v := by
      intro v
      rw [recvP_inbox]
      constructor
      · rintro ⟨w, -, h1, h2⟩
        rw [(ih w).2.1] at h1
        split_ifs at h1 with hw
        · simp only [Option.some.injEq] at h1
          subst hw
          exact ⟨h1, by rw [← htgt]; exact h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨g.pos, (target_adj r hconn k h2).2, ?_, ?_⟩
        · rw [(ih _).2.1, if_pos rfl, h1]
        · rw [htgt]; exact h2
    have hS : ∀ v, StartP r v (S (G := G) I inp r (Fintype.card V + k) v) (inbox (G := G) I inp r (Fintype.card V + k) v) ↔
        RecvP (inbox (G := G) I inp r (Fintype.card V + k) v) ∧ v ∉ g.ent := by
      intro v
      simp only [StartP, hclk v, false_and, false_or, (ih v).1, decide_eq_false_iff_not]
    rw [show Fintype.card V + (k + 1) = Fintype.card V + k + 1 by ring, S_succ, hge]
    have hpk : pebKeep (S (G := G) I inp r (Fintype.card V + k) v) =
        if g.pos = v then (if g.ready = false then some true
          else if target T (g.pend v) v = none then some true else none) else none := by
      unfold pebKeep
      rw [(ih v).2.1, htgt]
      split_ifs <;> simp_all
    have hpd : pendKeep (S (G := G) I inp r (Fintype.card V + k) v) =
        if g.pos = v ∧ g.ready = true then
          (match target T (g.pend v) v with | some x => (g.pend v).erase x | none => g.pend v)
        else g.pend v := by
      unfold pendKeep
      rw [(ih v).2.1, htgt, (ih v).2.2]
      split_ifs <;> simp_all
    cases hr : g.ready with
    | false =>
      have hst : PState.step T g = { g with ready := true } := by simp [PState.step, hr]
      have hRv : ¬ RecvP (inbox (G := G) I inp r (Fintype.card V + k) v) := by rw [hR]; simp [hr]
      have hSv : ¬ StartP r v (S (G := G) I inp r (Fintype.card V + k) v)
          (inbox (G := G) I inp r (Fintype.card V + k) v) := by
        rw [hS]; exact fun h => hRv h.1
      rw [hst]
      refine ⟨?_, ?_, ?_⟩ <;> dsimp only [stepFn]
      · rw [(ih v).1, decide_eq_false hSv, Bool.or_false]
      · rw [if_neg hSv, if_neg hRv, hpk, hr]; by_cases h : g.pos = v <;> simp [h]
      · rw [if_neg (hclk v), hpd, hr]; simp
    | true =>
      cases ht : target T (g.pend g.pos) g.pos with
      | none =>
        have hst : PState.step T g = g := by simp [PState.step, hr, ht]
        have hRv : ¬ RecvP (inbox (G := G) I inp r (Fintype.card V + k) v) := by rw [hR]; simp [ht]
        have hSv : ¬ StartP r v (S (G := G) I inp r (Fintype.card V + k) v)
            (inbox (G := G) I inp r (Fintype.card V + k) v) := by
          rw [hS]; exact fun h => hRv h.1
        rw [hst]
        refine ⟨?_, ?_, ?_⟩ <;> dsimp only [stepFn]
        · rw [(ih v).1, decide_eq_false hSv, Bool.or_false]
        · rw [if_neg hSv, if_neg hRv, hpk, hr]
          by_cases h : g.pos = v
          · subst h; simp [ht]
          · simp [h]
        · rw [if_neg (hclk v), hpd, hr]
          by_cases h : g.pos = v
          · subst h; simp [ht]
          · simp [h]
      | some x =>
        have hst : PState.step T g = g.move x := by simp [PState.step, hr, ht]
        obtain ⟨hxp, -⟩ := target_adj r hconn k ht
        have hRv : RecvP (inbox (G := G) I inp r (Fintype.card V + k) v) ↔ v = x := by
          rw [hR, hr, ht]; simp [eq_comm]
        rw [hst]
        by_cases hvx : v = x
        · subst hvx
          have hvp : g.pos ≠ v := Ne.symm hxp
          have hSv := hS v
          rw [hRv] at hSv
          simp only [true_and] at hSv
          refine ⟨?_, ?_, ?_⟩ <;> dsimp only [stepFn]
          · rw [(ih v).1, PState.move_ent]
            by_cases he : v ∈ g.ent
            · simp [he]
            · rw [decide_eq_true (hSv.2 he)]; simp
          · rw [PState.move_pos, PState.move_ready, if_pos rfl]
            by_cases he : v ∈ g.ent
            · rw [if_neg (fun h => hSv.1 h he), if_pos (hRv.2 rfl)]; simp [he]
            · rw [if_pos (hSv.2 he)]; simp [he]
          · rw [if_neg (hclk v), hpd, PState.move_pend, if_neg (fun h => hvp h.1),
              Function.update_of_ne (Ne.symm hvp)]
        · have hRv' : ¬ RecvP (inbox (G := G) I inp r (Fintype.card V + k) v) :=
            fun h => hvx (hRv.1 h)
          have hSv : ¬ StartP r v (S (G := G) I inp r (Fintype.card V + k) v)
              (inbox (G := G) I inp r (Fintype.card V + k) v) := by
            rw [hS]; exact fun h => hRv' h.1
          refine ⟨?_, ?_, ?_⟩ <;> dsimp only [stepFn]
          · rw [(ih v).1, decide_eq_false hSv, Bool.or_false, PState.move_ent]; simp [hvx]
          · rw [if_neg hSv, if_neg hRv', hpk, PState.move_pos, if_neg (Ne.symm hvx)]
            by_cases h : g.pos = v
            · subst h; simp [hr, ht]
            · simp [h]
          · rw [if_neg (hclk v), hpd, PState.move_pend]
            by_cases h : g.pos = v
            · subst h; simp [hr, ht]
            · simp [h, Function.update_of_ne (Ne.symm h)]

/-- The round at the end of which the pebble enters `v` (so `v` knows `d(v, v) = 0` and starts
`BFS_v` in the next round). -/
noncomputable def arr (hconn : G.Connected) (v : V) : ℕ :=
  Fintype.card V + PState.firstVisit (tree1 hconn r) v

lemma tree1_adj (hconn : G.Connected) :
    ∀ v, v ≠ (tree1 hconn r).root → G.Adj v ((tree1 hconn r).par v) := by
  intro v hv
  have hv' : v ≠ r := hv
  simp only [tree1, if_neg hv']
  exact (bpar_spec hconn r hv').1.symm

/-- Lemma 1 for the arrival rounds of Algorithm 1. -/
lemma arr_sep (hconn : G.Connected) {u u' w : V}
    (h : arr r hconn u + G.dist u w = arr r hconn u' + G.dist u' w) : u = u' := by
  by_contra hne
  have := PState.lemma1 (T := tree1 hconn r) G hconn (tree1_adj r hconn) hne w
  unfold arr at h; omega

lemma arr_ge (hconn : G.Connected) (v : V) : Fintype.card V ≤ arr r hconn v := by
  unfold arr; omega

/-- `BFS_v` starts exactly in the round after the pebble enters `v`. -/
lemma start_iff (hconn : G.Connected) (t : ℕ) (v : V) :
    StartP r v (S (G := G) I inp r t v) (inbox (G := G) I inp r t v) ↔ arr r hconn v = t + 1 := by
  classical
  have hpos := Fintype.card_pos_iff.2 ⟨r⟩
  rcases lt_trichotomy (t + 1) (Fintype.card V) with h | h | h
  · have hpre := fun w => pre_pebble (G := G) I inp r t (by omega) w
    have hR : ¬ RecvP (inbox (G := G) I inp r t v) := by
      rw [recvP_inbox]; rintro ⟨w, -, h, -⟩; rw [(hpre w).2] at h; simp at h
    have := arr_ge r hconn v
    simp only [StartP, clk_S, hR, false_and, or_false]
    omega
  · have hpre := fun w => pre_pebble (G := G) I inp r t (by omega) w
    have hR : ¬ RecvP (inbox (G := G) I inp r t v) := by
      rw [recvP_inbox]; rintro ⟨w, -, h, -⟩; rw [(hpre w).2] at h; simp at h
    simp only [StartP, clk_S, hR, false_and, or_false, h, true_and, arr]
    constructor
    · intro hv; rw [hv]; have := PState.firstVisit_root (tree1 hconn r); simp only [tree1] at this ⊢; omega
    · intro h'
      have h0 : PState.firstVisit (tree1 hconn r) v = 0 := by omega
      rw [← PState.firstVisit_root (tree1 hconn r)] at h0
      exact PState.firstVisit_injective (tree1 hconn r) h0
  · obtain ⟨k, rfl⟩ : ∃ k, t = Fintype.card V + k := ⟨t - Fintype.card V, by omega⟩
    have h1 := (pebble_corr I inp r hconn k v).1
    have h2 := (pebble_corr I inp r hconn (k + 1) v).1
    rw [show Fintype.card V + (k + 1) = Fintype.card V + k + 1 by ring, S_succ] at h2
    dsimp only [stepFn] at h2
    rw [h1] at h2
    have hS : StartP r v (S (G := G) I inp r (Fintype.card V + k) v)
        (inbox (G := G) I inp r (Fintype.card V + k) v) → v ∉ (PState.iter (tree1 hconn r) k).ent := by
      rintro (⟨hc, -⟩ | ⟨-, he⟩)
      · rw [clk_S] at hc; omega
      · rw [h1] at he; simpa using he
    rw [arr, add_assoc, add_right_inj]
    constructor
    · intro hs
      have hn := hS hs
      have hm : v ∈ (PState.iter (tree1 hconn r) (k + 1)).ent := by
        have : decide (v ∈ (PState.iter (tree1 hconn r) (k + 1)).ent) = true := by rw [← h2]; simp [hs]
        simpa using this
      have a1 := (PState.mem_iff_firstVisit_le (tree1 hconn r)).1 hm
      have a2 : ¬ PState.firstVisit (tree1 hconn r) v ≤ k := fun h => hn ((PState.mem_iff_firstVisit_le (tree1 hconn r)).2 h)
      omega
    · intro hf
      have hm : v ∈ (PState.iter (tree1 hconn r) (k + 1)).ent := (PState.mem_iff_firstVisit_le (tree1 hconn r)).2 (by omega)
      have hn : v ∉ (PState.iter (tree1 hconn r) k).ent := fun h' => by
        have := (PState.mem_iff_firstVisit_le (tree1 hconn r)).1 h'; omega
      by_contra hs
      have : decide (v ∈ (PState.iter (tree1 hconn r) (k + 1)).ent) = false := by
        rw [← h2]; simp [hn, hs]
      simp [hm] at this

lemma tokR_inbox (hconn : G.Connected) (t : ℕ) (w : V)
    (ih : ∀ x u e, (S (G := G) I inp r t x).fwd = some (u, e) ↔
      arr r hconn u + G.dist u x = t ∧ e = G.dist u x) (u : V) (e : ℕ) :
    TokR (inbox (G := G) I inp r t w) u e ↔
      ∃ x, G.Adj x w ∧ arr r hconn u + G.dist u x = t ∧ e = G.dist u x := by
  constructor
  · rintro ⟨x, y, p, hy, hp, rfl, rfl⟩
    by_cases hx : G.Adj x w
    · simp only [inbox, hx, ↓reduceIte, Option.some.injEq] at hy
      subst hy
      simp only [sendFn, Option.map_eq_some_iff] at hp
      obtain ⟨⟨u', e'⟩, h1, h2⟩ := hp
      subst h2
      obtain ⟨h3, rfl⟩ := (ih x u' e').1 h1
      refine ⟨x, hx, h3, ?_⟩
      have := dist_lt_card hconn u' x
      simp [cap]; omega
    · simp [inbox, hx] at hy
  · rintro ⟨x, hx, h1, rfl⟩
    refine ⟨x, _, (u, cap (G.dist u x)), by simp [inbox, hx]; rfl, ?_, rfl, ?_⟩
    · simp [sendFn, (ih x u (G.dist u x)).2 ⟨h1, rfl⟩]
    · have := dist_lt_card hconn u x
      simp [cap]; omega

/-- **Stage 2, BFS waves** (the heart of Theorem 1): node `w` learns `d(u, w)` exactly in round
`arr u + d(u, w)` and forwards the token of `u` in the next round; it never has to forward two
tokens at once (by Lemma 1). -/
lemma bfs_inv (hconn : G.Connected) : ∀ t w,
    (∀ u, (S (G := G) I inp r t w).dist u =
      if arr r hconn u + G.dist u w ≤ t then some (G.dist u w) else none) ∧
    (∀ u e, (S (G := G) I inp r t w).fwd = some (u, e) ↔
      arr r hconn u + G.dist u w = t ∧ e = G.dist u w)
  | 0, w => by
    refine ⟨fun u => ?_, fun u e => ?_⟩
    · have := arr_ge r hconn u
      have hp := Fintype.card_pos_iff.2 ⟨r⟩
      rw [if_neg (by omega)]; rfl
    · have := arr_ge r hconn u
      have hp := Fintype.card_pos_iff.2 ⟨r⟩
      simp only [S, TAlgorithm.run, apsp, reduceCtorEq, false_iff, not_and]
      omega
  | t + 1, w => by
    classical
    have ihd := fun x => (bfs_inv hconn t x).1
    have ihf : ∀ x u e, (S (G := G) I inp r t x).fwd = some (u, e) ↔
        arr r hconn u + G.dist u x = t ∧ e = G.dist u x := fun x => (bfs_inv hconn t x).2
    have hT := tokR_inbox I inp r hconn t w ihf
    have hst := start_iff I inp r hconn t w
    -- tokens arriving in round `t + 1` are exactly the ones with `arr u + d(u, w) = t + 1`
    have hA : ∀ u, arr r hconn u + G.dist u w = t + 1 → u ≠ w →
        TokR (inbox (G := G) I inp r t w) u (G.dist u w - 1) := by
      intro u h hne
      obtain ⟨x, hx, hd⟩ := hconn.exists_adj_dist_succ u (Ne.symm hne)
      rw [hT]; exact ⟨x, hx.symm, by omega, by omega⟩
    have hB : ∀ u e, TokR (inbox (G := G) I inp r t w) u e →
        arr r hconn u + G.dist u w ≤ t + 1 ∧ (t < arr r hconn u + G.dist u w → e + 1 = G.dist u w) := by
      intro u e he
      rw [hT] at he
      obtain ⟨x, hx, h1, rfl⟩ := he
      have := dist_le_of_adj hconn (u := u) hx
      constructor
      · omega
      · intro h
        have h2 := dist_le_of_adj hconn (u := u) hx.symm
        omega
    -- the new distance table
    have hdist : ∀ u, distUpd r w (S (G := G) I inp r t w) (inbox (G := G) I inp r t w) u =
        if arr r hconn u + G.dist u w ≤ t + 1 then some (G.dist u w) else none := by
      intro u
      unfold distUpd
      rw [ihd w u]
      by_cases h1 : arr r hconn u + G.dist u w ≤ t
      · rw [if_pos h1, if_pos (show arr r hconn u + G.dist u w ≤ t + 1 by omega)]
      · rw [if_neg h1]
        dsimp only
        by_cases h2 : StartP r w (S (G := G) I inp r t w) (inbox (G := G) I inp r t w) ∧ u = w
        · rw [if_pos h2]
          obtain ⟨h3, rfl⟩ := h2
          rw [hst] at h3
          simp [h3]
        · rw [if_neg h2]
          by_cases h4 : ∃ d, TokR (inbox (G := G) I inp r t w) u d
          · rw [dif_pos h4]
            obtain ⟨hle, hd⟩ := hB u _ (Nat.find_spec h4)
            rw [if_pos hle]
            have := hd (by omega)
            simp only [Option.some.injEq]; omega
          · rw [dif_neg h4, if_neg]
            intro hle
            have heq : arr r hconn u + G.dist u w = t + 1 := by omega
            by_cases huw : u = w
            · subst huw
              exact h2 ⟨by rw [hst]; simpa using heq, rfl⟩
            · exact h4 ⟨_, hA u heq huw⟩
    refine ⟨fun u => ?_, fun u e => ?_⟩
    · rw [S_succ]; exact hdist u
    · rw [S_succ]
      show fwdUpd r w _ _ = _ ↔ _
      unfold fwdUpd
      by_cases hs : StartP r w (S (G := G) I inp r t w) (inbox (G := G) I inp r t w)
      · rw [if_pos hs]
        rw [hst] at hs
        simp only [Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; simp [hs]
        · rintro ⟨h1, rfl⟩
          have : u = w := arr_sep r hconn (by rw [h1, SimpleGraph.dist_self, add_zero, hs])
          subst this; simp
      · rw [if_neg hs]
        by_cases hn : NewTok (S (G := G) I inp r t w) (inbox (G := G) I inp r t w)
        · rw [dif_pos hn]
          set u0 := Classical.choose hn
          obtain ⟨hu0, d0, hd0⟩ := Classical.choose_spec hn
          have hnew : arr r hconn u0 + G.dist u0 w = t + 1 := by
            rw [ihd w u0] at hu0
            have := (hB u0 d0 hd0).1
            split_ifs at hu0 with hh
            omega
          rw [hdist u0, if_pos hnew.le]
          simp only [Option.getD_some, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨rfl, rfl⟩; exact ⟨hnew, rfl⟩
          · rintro ⟨h1, rfl⟩
            have : u = u0 := arr_sep r hconn (by rw [h1, hnew])
            subst this; exact ⟨rfl, rfl⟩
        · rw [dif_neg hn]
          simp only [reduceCtorEq, false_iff, not_and]
          intro h1 _
          by_cases huw : u = w
          · subst huw; apply hs; rw [hst]; simpa using h1
          · apply hn
            refine ⟨u, ?_, _, hA u h1 huw⟩
            rw [ihd w u, if_neg (by omega)]

/-- The eccentricity of `w` as a natural number. -/
noncomputable def eccN (w : V) : ℕ := univ.sup fun u => G.dist u w

lemma arr_le (hconn : G.Connected) (v : V) : arr r hconn v ≤ 4 * Fintype.card V - 1 := by
  have := PState.firstVisit_le (tree1 hconn r) v
  have hp := Fintype.card_pos_iff.2 ⟨r⟩
  unfold arr; omega

/-- **Theorem 1 of [HW12]** (correctness and running time of Algorithm 1): after `5n` rounds every
node `w` knows its distance to every node `u`. -/
theorem theorem1_dist (hconn : G.Connected) {t : ℕ} (ht : 5 * Fintype.card V ≤ t) (u w : V) :
    (S (G := G) I inp r t w).dist u = some (G.dist u w) := by
  rw [(bfs_inv I inp r hconn t w).1 u, if_pos]
  have := arr_le r hconn u
  have := dist_lt_card hconn u w
  omega

lemma eccOf_S (hconn : G.Connected) {t : ℕ} (ht : 5 * Fintype.card V ≤ t) (w : V) :
    eccOf (S (G := G) I inp r t w).dist = eccN (G := G) w := by
  unfold eccOf eccN
  congr 1; funext u; rw [theorem1_dist I inp r hconn ht]; rfl

lemma eccN_lt (hconn : G.Connected) (w : V) : eccN (G := G) w < Fintype.card V := by
  unfold eccN
  have hp := Fintype.card_pos_iff.2 ⟨w⟩
  rw [Finset.sup_lt_iff (by omega)]
  exact fun u _ => dist_lt_card hconn u w

/-- **Stage 3**: `j` rounds after round `5n`, `mx` is the largest and `mn` the smallest
eccentricity within distance `j`. -/
lemma stage3 (hconn : G.Connected) : ∀ j w,
    (∀ c, (S (G := G) I inp r (5 * Fintype.card V + j) w).mx ≤ c ↔
      ∀ x, G.dist x w ≤ j → eccN (G := G) x ≤ c) ∧
    (∀ c, c ≤ (S (G := G) I inp r (5 * Fintype.card V + j) w).mn ↔
      ∀ x, G.dist x w ≤ j → c ≤ eccN (G := G) x)
  | 0, w => by
    have hp := Fintype.card_pos_iff.2 ⟨r⟩
    obtain ⟨m, hm⟩ : ∃ m, 5 * Fintype.card V = m + 1 := ⟨5 * Fintype.card V - 1, by omega⟩
    have hd : ∀ x, G.dist x w ≤ 0 ↔ x = w := fun x => by
      rw [Nat.le_zero, (hconn.preconnected x w).dist_eq_zero_iff]
    have he : eccOf (distUpd r w (S (G := G) I inp r m w) (inbox (G := G) I inp r m w)) =
        eccN (G := G) w := by
      have := eccOf_S I inp r hconn (t := m + 1) (by omega) w
      rw [S_succ] at this; exact this
    rw [add_zero, hm, S_succ]
    dsimp only [stepFn]
    rw [clk_S, if_pos hm.symm, if_pos hm.symm, he]
    refine ⟨fun c => ?_, fun c => ?_⟩
    · constructor
      · intro h x hx; rw [(hd x).1 hx]; exact h
      · intro h; exact h w (by simp)
    · constructor
      · intro h x hx; rw [(hd x).1 hx]; exact h
      · intro h; exact h w (by simp)
  | j + 1, w => by
    have ih := fun y => stage3 hconn j y
    have hp := Fintype.card_pos_iff.2 ⟨r⟩
    have hmxle : ∀ y, (S (G := G) I inp r (5 * Fintype.card V + j) y).mx ≤ Fintype.card V := by
      intro y; rw [(ih y).1]; intro x _; exact (eccN_lt hconn x).le
    have hmnle : ∀ y, (S (G := G) I inp r (5 * Fintype.card V + j) y).mn ≤ Fintype.card V := by
      intro y
      have := (ih y).2 (S (G := G) I inp r (5 * Fintype.card V + j) y).mn
      have h2 := (this.1 le_rfl) y (by simp)
      have := eccN_lt hconn y; omega
    rw [show 5 * Fintype.card V + (j + 1) = 5 * Fintype.card V + j + 1 by ring, S_succ]
    dsimp only [stepFn]
    rw [clk_S, if_neg (by omega), if_neg (by omega)]
    refine ⟨fun c => ?_, fun c => ?_⟩
    · rw [Finset.fold_max_le, (ih w).1]
      simp only [mem_univ, true_implies, inbox]
      constructor
      · rintro ⟨h1, h2⟩ x hx
        rcases (dist_le_succ_iff hconn x w j).1 hx with hx | ⟨y, hy, hxy⟩
        · exact h1 x hx
        · have := h2 y
          simp only [hy, ↓reduceIte, sendFn, cap, Fin.val_mk] at this
          rw [min_eq_left (hmxle y), (ih y).1] at this
          exact this x hxy
      · intro h
        refine ⟨fun x hx => h x (by omega), fun y => ?_⟩
        by_cases hy : G.Adj y w
        · simp only [hy, ↓reduceIte, sendFn, cap, Fin.val_mk]
          rw [min_eq_left (hmxle y), (ih y).1]
          intro x hx; exact h x ((dist_le_succ_iff hconn x w j).2 (Or.inr ⟨y, hy, hx⟩))
        · simp [hy]
    · rw [Finset.le_fold_min, (ih w).2]
      simp only [mem_univ, true_implies, inbox]
      constructor
      · rintro ⟨h1, h2⟩ x hx
        rcases (dist_le_succ_iff hconn x w j).1 hx with hx | ⟨y, hy, hxy⟩
        · exact h1 x hx
        · have := h2 y
          simp only [hy, ↓reduceIte, sendFn, cap, Fin.val_mk] at this
          rw [min_eq_left (hmnle y), (ih y).2] at this
          exact this x hxy
      · intro h
        refine ⟨fun x hx => h x (by omega), fun y => ?_⟩
        by_cases hy : G.Adj y w
        · simp only [hy, ↓reduceIte, sendFn, cap, Fin.val_mk]
          rw [min_eq_left (hmnle y), (ih y).2]
          intro x hx; exact h x ((dist_le_succ_iff hconn x w j).2 (Or.inr ⟨y, hy, hx⟩))
        · simp only [hy, ↓reduceIte]; rw [(ih w).2]; exact fun x hx => h x (by omega)

lemma eccN_eq (hconn : G.Connected) (w : V) : (eccN (G := G) w : ℕ∞) = G.eccent w := by
  apply le_antisymm
  · obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup univ ⟨w, mem_univ _⟩ fun u => G.dist u w
    rw [eccN, hu, SimpleGraph.dist_comm, (hconn.preconnected w u).coe_dist_eq_edist]
    exact SimpleGraph.edist_le_eccent
  · rw [SimpleGraph.eccent_le_iff]
    intro v
    rw [← (hconn.preconnected w v).coe_dist_eq_edist, SimpleGraph.dist_comm, Nat.cast_le]
    exact Finset.le_sup (f := fun u => G.dist u w) (mem_univ v)

lemma stage3_final (hconn : G.Connected) {t : ℕ} (ht : 6 * Fintype.card V ≤ t) (w : V) :
    (∀ c, (S (G := G) I inp r t w).mx ≤ c ↔ ∀ x, eccN (G := G) x ≤ c) ∧
    (∀ c, c ≤ (S (G := G) I inp r t w).mn ↔ ∀ x, c ≤ eccN (G := G) x) := by
  obtain ⟨j, rfl⟩ : ∃ j, t = 5 * Fintype.card V + j := ⟨t - 5 * Fintype.card V, by omega⟩
  have h := stage3 I inp r hconn j w
  have hd : ∀ x, G.dist x w ≤ j := fun x => by have := dist_lt_card hconn x w; omega
  exact ⟨fun c => by rw [h.1]; simp [hd], fun c => by rw [h.2]; simp [hd]⟩

/-- **Lemma 2 of [HW12]**: after `5n` rounds every node knows its eccentricity. -/
theorem lemma2 (hconn : G.Connected) {t : ℕ} (ht : 5 * Fintype.card V ≤ t) (w : V) :
    (eccOf (S (G := G) I inp r t w).dist : ℕ∞) = G.eccent w := by
  rw [eccOf_S I inp r hconn ht, eccN_eq hconn]

/-- **Lemma 3 of [HW12]**: after `6n` rounds every node knows the diameter. -/
theorem lemma3 (hconn : G.Connected) {t : ℕ} (ht : 6 * Fintype.card V ≤ t) (w : V) :
    ((S (G := G) I inp r t w).mx : ℕ∞) = G.ediam ∧ (S (G := G) I inp r t w).mx = G.diam := by
  have h := (stage3_final I inp r hconn ht w).1
  have h1 : ((S (G := G) I inp r t w).mx : ℕ∞) = G.ediam := by
    apply le_antisymm
    · obtain ⟨x, hx⟩ : ∃ x, (S (G := G) I inp r t w).mx ≤ eccN (G := G) x := by
        by_contra hc
        push_neg at hc
        have := (h _).1 le_rfl
        obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup univ ⟨w, mem_univ _⟩ (eccN (G := G))
        have h2 := (h (univ.sup (eccN (G := G)))).2 (fun y => Finset.le_sup (mem_univ y))
        rw [hx] at h2; exact absurd h2 (not_le.2 (hc x))
      calc ((S (G := G) I inp r t w).mx : ℕ∞) ≤ eccN (G := G) x := by exact_mod_cast hx
        _ = G.eccent x := eccN_eq hconn x
        _ ≤ G.ediam := SimpleGraph.eccent_le_ediam
    · rw [SimpleGraph.ediam_le_iff]
      intro u v
      calc G.edist u v ≤ G.eccent u := SimpleGraph.edist_le_eccent
        _ = eccN (G := G) u := (eccN_eq hconn u).symm
        _ ≤ _ := by exact_mod_cast (h _).1 le_rfl u
  refine ⟨h1, ?_⟩
  have hne : G.ediam ≠ ⊤ := by rw [← h1]; exact ENat.natCast_ne_top _
  have := SimpleGraph.natCast_diam_eq_ediam_iff.2 hne
  rw [← h1] at this; exact_mod_cast this.symm

/-- **Lemma 4 of [HW12]**: after `6n` rounds every node knows the radius. -/
theorem lemma4 (hconn : G.Connected) {t : ℕ} (ht : 6 * Fintype.card V ≤ t) (w : V) :
    ((S (G := G) I inp r t w).mn : ℕ∞) = G.radius := by
  have h := (stage3_final I inp r hconn ht w).2
  have : Nonempty V := ⟨r⟩
  apply le_antisymm
  · obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
    rw [← hu, ← eccN_eq hconn u]
    exact_mod_cast (h _).1 le_rfl u
  · obtain ⟨x, hx⟩ : ∃ x, eccN (G := G) x ≤ (S (G := G) I inp r t w).mn := by
      by_contra hc
      push_neg at hc
      have := (h _).2 (fun x => hc x)
      omega
    calc G.radius ≤ G.eccent x := SimpleGraph.radius_le_eccent
      _ = eccN (G := G) x := (eccN_eq hconn x).symm
      _ ≤ _ := by exact_mod_cast hx

/-- **Lemma 5 of [HW12]**: after `6n` rounds every node knows whether it is a center vertex. -/
theorem lemma5 (hconn : G.Connected) {t : ℕ} (ht : 6 * Fintype.card V ≤ t) (w : V) :
    eccOf (S (G := G) I inp r t w).dist = (S (G := G) I inp r t w).mn ↔ w ∈ G.center := by
  rw [SimpleGraph.mem_center_iff, ← lemma2 I inp r hconn (t := t) (by omega) w,
    ← lemma4 I inp r hconn ht w, Nat.cast_inj]

/-- **Lemma 6 of [HW12]**: after `6n` rounds every node knows whether it is a peripheral
vertex. -/
theorem lemma6 (hconn : G.Connected) {t : ℕ} (ht : 6 * Fintype.card V ≤ t) (w : V) :
    eccOf (S (G := G) I inp r t w).dist = (S (G := G) I inp r t w).mx ↔ G.eccent w = G.ediam := by
  rw [← lemma2 I inp r hconn (t := t) (by omega) w, ← (lemma3 I inp r hconn ht w).1, Nat.cast_inj]

end Analysis

/-- **Theorem 1 of [HW12]**: Algorithm 1 computes APSP in `O(n)` rounds of the CONGEST model with
`O(log n)`-bit messages. Concretely: there is a deterministic CONGEST algorithm with
`B ≤ 5 ⌈log₂ (n + 1)⌉ + 2` bits per message (it only needs to know `n` and the ID `r` of some
node) such that on every connected graph, after `5n` rounds, every node `w` knows `d(u, w)` for
all `u`; one more stage of `n` rounds gives every node the diameter and the radius. -/
theorem theorem1 (I : Type*) (r : V) :
    ∃ B ≤ 5 * Nat.clog 2 (Fintype.card V + 1) + 2, ∃ A : Algorithm V I (St V) B,
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → ∀ (inp : V → I) t,
        5 * Fintype.card V ≤ t → ∀ u w, (A.run G inp t w).dist u = some (G.dist u w) := by
  refine ⟨_, msgBits_le, (apsp I r).toAlgorithm (fun _ _ => true), ?_⟩
  intro G _ hconn inp t ht u w
  rw [TAlgorithm.run_toAlgorithm]
  exact theorem1_dist I inp r hconn ht u w

/-- **Lemmas 2–6 of [HW12]** for the same CONGEST algorithm: after `6n` rounds every node knows its
eccentricity, the diameter, the radius, and whether it is a center / peripheral vertex. -/
theorem lemmas2to6 (I : Type*) (r : V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (inp : V → I) {t : ℕ} (ht : 6 * Fintype.card V ≤ t) (w : V) :
    let s := ((apsp I r).toAlgorithm (fun _ _ => true)).run G inp t w
    (eccOf s.dist : ℕ∞) = G.eccent w ∧ s.mx = G.diam ∧ (s.mn : ℕ∞) = G.radius ∧
      (eccOf s.dist = s.mn ↔ w ∈ G.center) ∧ (eccOf s.dist = s.mx ↔ G.eccent w = G.ediam) := by
  simp only [TAlgorithm.run_toAlgorithm]
  exact ⟨lemma2 I inp r hconn (t := t) (by omega) w, (lemma3 I inp r hconn ht w).2,
    lemma4 I inp r hconn ht w, lemma5 I inp r hconn ht w, lemma6 I inp r hconn ht w⟩

end Podc.OptimalAPSP
