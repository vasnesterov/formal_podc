import Papers.PODC2020.SSLERegular.EulerLiteral
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Error-detected configurations reach every configuration (SS-EulerCycle)

Chen–Chen, *Self-Stabilizing Leader Election in Regular Graphs*, PODC 2020, Section 2 (the fact
used with Lemma 2.1: "an error-detected configuration can reach all possible configurations"),
for protocol SS-EulerCycle (`ssEuler`, both the printed and the repaired variant).

`err_reach_all`: on a connected graph with at least two nodes, from any configuration in which some
node has `errFlag = true`, every configuration is reachable. Proof:

1. *Spread*: a flagged initiator may raise the flag of its responder (`RandBit2 = true`) while
   staying flagged (`RandBit1 = true`); along walks, all nodes become flagged.
2. *Prepare the root*: pick an edge `r — v`; let `r` take a state whose colour is `D v`'s
   `prevColor` and whose predecessor/successor colours all avoid `D v`'s colour (`RootOK`).
3. *Finalize* every node `x ≠ r` in order of decreasing distance from `r`, as initiator with a
   neighbour closer to `r` as responder: `x` takes the state `D x`; the responder stays flagged and
   (SS-TwoHop keeps colours) keeps its skeleton, so `r` stays `RootOK`.
4. *Last interaction* `(r, v)`: there is no virtual edge between `r` and `v`, so the ring part
   leaves `v` untouched and flags `r`; `r` takes `D r` and `v` gets exactly `D v`'s SS-TwoHop
   memory.
-/

open Finset

namespace SSLERegular

variable {RS : Type*} {k : ℕ}

/-- A choice that keeps the colours of initiator `u` and responder `v` in SS-TwoHop (shared bit
`rb`) and prescribes `RandState = rand`, `RandBit1 = b1`, `RandBit2 = b2`. -/
def EChoice.keepRand (ch0 : EChoice k RS) (u v rand : EState k RS) (rb b1 b2 : Bool) :
    EChoice k RS :=
  { ch0 with rc1 := v.color, rc2 := u.color, rb := rb, rand := rand, b1 := b1, b2 := b2 }

lemma EChoice.keepRand_valid {R : RingProtocol RS} {ch0 : EChoice k RS} (h : ch0.Valid R)
    (u v rand : EState k RS) (rb b1 b2 : Bool) : (ch0.keepRand u v rand rb b1 b2).Valid R := h

/-- An interaction with a flagged initiator and colour-keeping SS-TwoHop: the initiator takes
`{rand with errFlag := b1}`, the responder gets `errFlag = b2` and keeps its skeleton. -/
lemma eulerStep_keepRand (bidir : Bool) (R : RingProtocol RS) (ch0 : EChoice k RS)
    {u : EState k RS} (hu : u.errFlag = true) (v rand : EState k RS) (rb b1 b2 : Bool) :
    (eulerStep bidir R (ch0.keepRand u v rand rb b1 b2) u v).1 = { rand with errFlag := b1 } ∧
    (eulerStep bidir R (ch0.keepRand u v rand rb b1 b2) u v).2.errFlag = b2 ∧
    skel (eulerStep bidir R (ch0.keepRand u v rand rb b1 b2) u v).2 = skel v := by
  set ch := ch0.keepRand u v rand rb b1 b2 with hch
  set w := twoHopE ch.rc1 ch.rc2 ch.rb u v with hw
  have ht : w = ({ u with prevColor := v.color, colorBit := rb },
      { v with prevColor := u.color, colorBit := rb }) := twoHopE_keep rb u v
  have h1 : w.1.errFlag = true := by rw [ht]; exact hu
  have hc := (tokenDetect_frame (ringPart bidir R ch w.1 w.2)).2.2
    ((ringPart_frame bidir R ch w.1 w.2).2.2.1 h1)
  rw [eulerStep_err bidir R ch u v hc]
  refine ⟨rfl, rfl, ?_⟩
  show skel (tokenDetect (ringPart bidir R ch w.1 w.2)).2 = skel v
  rw [(tokenDetect_frame (ringPart bidir R ch w.1 w.2)).2.1,
    (ringPart_frame bidir R ch w.1 w.2).2.1.1, ht]
  rfl

/-- The root is ready for the last interaction with a neighbour whose final state is `dv`: flagged,
coloured `dv.prevColor`, and no predecessor/successor colour equals `dv.color`. -/
def RootOK (dv s : EState k RS) : Prop :=
  s.errFlag = true ∧ s.color = dv.prevColor ∧
    ∀ i, (s.node i).succ ≠ dv.color ∧ (s.node i).pred ≠ dv.color

lemma RootOK.of_skel {dv s s' : EState k RS} (h : RootOK dv s) (hs : skel s' = skel s)
    (he : s'.errFlag = true) : RootOK dv s' := by
  simp only [skel, Prod.mk.injEq] at hs
  obtain ⟨hc, hn⟩ := hs
  refine ⟨he, hc ▸ h.2.1, fun i => ?_⟩
  have := congrFun hn i
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2]
  exact h.2.2 i

/-- Set both the predecessor and the successor colour of a virtual node. -/
def VNode.setPS (a : VNode k RS) (c : Fin (4 * k ^ 2)) : VNode k RS :=
  { a with pred := c, succ := c }

/-- A state that is `RootOK` for `dv` (given a colour `c ≠ dv.color`). -/
def rootState (dv : EState k RS) (c : Fin (4 * k ^ 2)) : EState k RS :=
  { dv with node := (fun i => (dv.node i).setPS c), color := dv.prevColor, errFlag := true }

lemma rootState_ok (dv : EState k RS) {c : Fin (4 * k ^ 2)} (hc : c ≠ dv.color) :
    RootOK dv (rootState dv c) :=
  ⟨rfl, rfl, fun _ => ⟨hc, hc⟩⟩

/-- The last interaction: a `RootOK` initiator and the responder's final state `dv`. -/
lemma eulerStep_final (bidir : Bool) (R : RingProtocol RS) (ch0 : EChoice k RS)
    {s dv dr : EState k RS} (hs : RootOK dv s) :
    eulerStep bidir R (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag) s dv = (dr, dv) := by
  have ht : twoHopE (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rc1
      (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rc2
      (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rb s dv =
      ({ s with prevColor := dv.color, colorBit := dv.colorBit },
        { dv with prevColor := s.color, colorBit := dv.colorBit }) := twoHopE_keep _ s dv
  have hno1 : ¬ ∃ i j, FMatch { s with prevColor := dv.color, colorBit := dv.colorBit }
      { dv with prevColor := s.color, colorBit := dv.colorBit } i j := by
    rintro ⟨i, j, h, -⟩; exact (hs.2.2 i).1 h
  have hno2 : ¬ ∃ i j, FMatch { dv with prevColor := s.color, colorBit := dv.colorBit }
      { s with prevColor := dv.color, colorBit := dv.colorBit } i j := by
    rintro ⟨i, j, -, h⟩; exact (hs.2.2 j).2 h
  have hr : ringPart bidir R (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag)
      (twoHopE (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rc1
        (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rc2
        (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rb s dv).1
      (twoHopE (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rc1
        (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rc2
        (ch0.keepRand s dv dr dv.colorBit dr.errFlag dv.errFlag).rb s dv).2 =
      ({ s with prevColor := dv.color, colorBit := dv.colorBit, errFlag := true },
        { dv with prevColor := s.color, colorBit := dv.colorBit }) := by
    rw [ht]; unfold ringPart
    rw [ite_eq_right hno1, ite_eq_right (by rintro ⟨-, h⟩; exact hno2 h)]
  have hc := (tokenDetect_frame _).2.2 (show (ringPart bidir R _ _ _).1.errFlag = true by
    rw [hr])
  rw [eulerStep_err bidir R _ s dv hc, (tokenDetect_frame _).2.1, hr]
  have hcol : s.color = dv.prevColor := hs.2.1
  simp only [hcol]
  rfl

section Graph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {R : RingProtocol RS}

/-- A flagged node flags a neighbour; flags are never lowered. -/
lemma spread_step (bidir : Bool) {ch0 : EChoice k RS} (hch0 : ch0.Valid R) (C : V → EState k RS)
    {x y : V} (hxy : G.Adj x y) (hx : (C x).errFlag = true) :
    ∃ C', (ssEuler bidir k R).Step G C C' ∧
      (∀ z, (C z).errFlag = true → (C' z).errFlag = true) ∧ (C' y).errFlag = true := by
  obtain ⟨e1, e2, -⟩ := eulerStep_keepRand bidir R ch0 hx (C y) (C x) false true true
  refine ⟨_, step_of_choice bidir C hxy _ (EChoice.keepRand_valid hch0 (C x) (C y) (C x)
    false true true), ?_, ?_⟩
  · intro z hz
    by_cases hzy : z = y
    · subst hzy; rw [upd_right]; exact e2
    by_cases hzx : z = x
    · subst hzx; rw [upd_left _ (G.ne_of_adj hxy), e1]
    · rw [upd_other _ hzx hzy]; exact hz
  · rw [upd_right]; exact e2

lemma spread_to (bidir : Bool) {ch0 : EChoice k RS} (hch0 : ch0.Valid R) {u : V} (z : V)
    (hz : G.Reachable z u) (C : V → EState k RS) (hu : (C u).errFlag = true) :
    ∃ C', (ssEuler bidir k R).Reachable G C C' ∧
      (∀ w, (C w).errFlag = true → (C' w).errFlag = true) ∧ (C' z).errFlag = true := by
  obtain ⟨p⟩ := hz
  induction p with
  | nil => exact ⟨C, Relation.ReflTransGen.refl, fun _ h => h, hu⟩
  | cons h p ih =>
    obtain ⟨C1, r1, m1, f1⟩ := ih hu
    obtain ⟨C2, s2, m2, f2⟩ := spread_step bidir hch0 C1 h.symm f1
    exact ⟨C2, r1.tail s2, fun w hw => m2 w (m1 w hw), f2⟩

/-- From a configuration with a flagged node, all nodes can be flagged. -/
lemma spread_all [Fintype V] (bidir : Bool) {ch0 : EChoice k RS} (hch0 : ch0.Valid R)
    (hconn : G.Connected) (C : V → EState k RS) {u : V} (hu : (C u).errFlag = true) :
    ∃ C', (ssEuler bidir k R).Reachable G C C' ∧ ∀ z, (C' z).errFlag = true := by
  have key : ∀ s : Finset V, ∃ C', (ssEuler bidir k R).Reachable G C C' ∧
      (C' u).errFlag = true ∧ ∀ z ∈ s, (C' z).errFlag = true := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C, Relation.ReflTransGen.refl, hu, by simp⟩
    | insert a s ha ih =>
      obtain ⟨C1, r1, h1u, h1⟩ := ih
      obtain ⟨C2, r2, m2, f2⟩ := spread_to bidir hch0 a (hconn.preconnected a u) C1 h1u
      refine ⟨C2, r1.trans r2, m2 u h1u, fun z hz => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact f2
      · exact m2 z (h1 z hz)
  obtain ⟨C', r, -, h⟩ := key Finset.univ
  exact ⟨C', r, fun z => h z (Finset.mem_univ z)⟩

omit [DecidableEq V] in
/-- Every node other than `r` has a neighbour closer to `r`. -/
lemma exists_parent (hconn : G.Connected) {r a : V} (h : a ≠ r) :
    ∃ p, G.Adj a p ∧ G.dist r p < G.dist r a := by
  obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist a r
  cases w with
  | nil => exact absurd rfl h
  | cons hap q =>
    refine ⟨_, hap, ?_⟩
    have h1 := SimpleGraph.dist_le q
    have h2 : G.dist r a = q.length + 1 := by
      rw [SimpleGraph.dist_comm, ← hw, SimpleGraph.Walk.length_cons]
    rw [SimpleGraph.dist_comm, h2]
    omega

/-- Finalize the nodes of `F` (not containing the root `r`), farthest from `r` first. -/
lemma finalize (bidir : Bool) {ch0 : EChoice k RS} (hch0 : ch0.Valid R) (hconn : G.Connected)
    (D : V → EState k RS) {r : V} (dv : EState k RS) (C2 : V → EState k RS)
    (h2 : RootOK dv (C2 r)) (hflag : ∀ x, (C2 x).errFlag = true) (F : Finset V) :
    r ∉ F → ∃ C', (ssEuler bidir k R).Reachable G C2 C' ∧ RootOK dv (C' r) ∧
      (∀ x ∈ F, C' x = D x) ∧ ∀ x ∉ F, (C' x).errFlag = true := by
  refine Finset.induction_on_min_value (fun x => G.dist r x) F ?_ ?_
  · intro _
    exact ⟨C2, Relation.ReflTransGen.refl, h2, by simp, fun x _ => hflag x⟩
  · intro a s ha hmin ih hr
    have har : a ≠ r := fun h => hr (h ▸ Finset.mem_insert_self a s)
    obtain ⟨C1, r1, o1, f1, g1⟩ := ih (fun h => hr (Finset.mem_insert_of_mem h))
    obtain ⟨p, hap, hdp⟩ := exists_parent hconn har
    have hps : p ∉ s := fun h => absurd (hmin p h) (not_le.2 hdp)
    have hpa : a ≠ p := G.ne_of_adj hap
    obtain ⟨e1, e2, e3⟩ :=
      eulerStep_keepRand bidir R ch0 (g1 a ha) (C1 p) (D a) false (D a).errFlag true
    refine ⟨_, r1.tail (step_of_choice bidir C1 hap _
      (EChoice.keepRand_valid hch0 (C1 a) (C1 p) (D a) false (D a).errFlag true)), ?_, ?_, ?_⟩
    · by_cases hpr : p = r
      · subst hpr; rw [upd_right]; exact o1.of_skel e3 e2
      · rw [upd_other _ (Ne.symm har) (Ne.symm hpr)]; exact o1
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [upd_left _ hpa, e1]
      · have hxa : x ≠ a := fun h => ha (h ▸ hx)
        have hxp : x ≠ p := fun h => hps (h ▸ hx)
        rw [upd_other _ hxa hxp]; exact f1 x hx
    · intro x hx
      have hxa : x ≠ a := fun h => hx (h ▸ Finset.mem_insert_self a s)
      by_cases hxp : x = p
      · subst hxp; rw [upd_right]; exact e2
      · rw [upd_other _ hxa hxp]; exact g1 x (fun h => hx (Finset.mem_insert_of_mem h))

/-- **An error-detected configuration can reach all configurations** (Section 2, used with
Lemma 2.1 of Chen–Chen, PODC 2020) for SS-EulerCycle, printed (`bidir = false`) or repaired
(`bidir = true`), on any connected graph with at least two nodes. -/
theorem err_reach_all {RS : Type*} {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected) (hV : 2 ≤ Fintype.card V)
    {R : RingProtocol RS} (hR : ∀ a b, (R.δ a b).Nonempty) (hk : 1 ≤ k) (bidir : Bool)
    (C : V → EState k RS) {u : V} (hu : (C u).errFlag = true) (D : V → EState k RS) :
    (ssEuler bidir k R).Reachable G C D := by
  obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (C u).color (C u)
  -- 1. flag everybody
  obtain ⟨C1, r1, h1⟩ := spread_all bidir hch0 hconn C hu
  -- an edge `r — v`
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  obtain ⟨v, hrv, -⟩ := exists_parent hconn (r := y) hxy
  set r := x
  -- 2. prepare the root
  obtain ⟨c, hc⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; nlinarith : 1 < Fintype.card (Fin (4 * k ^ 2))) (D v).color
  obtain ⟨e1, e2, -⟩ :=
    eulerStep_keepRand bidir R ch0 (h1 r) (C1 v) (rootState (D v) c) false true true
  have st2 := step_of_choice bidir C1 hrv _
    (EChoice.keepRand_valid hch0 (C1 r) (C1 v) (rootState (D v) c) false true true)
  set C2 := upd C1 r v (eulerStep bidir R
    (ch0.keepRand (C1 r) (C1 v) (rootState (D v) c) false true true) (C1 r) (C1 v)) with hC2
  have hrv' : r ≠ v := G.ne_of_adj hrv
  have o2 : RootOK (D v) (C2 r) := by
    rw [hC2, upd_left _ hrv', e1]; exact rootState_ok (D v) hc
  have g2 : ∀ z, (C2 z).errFlag = true := by
    intro z
    by_cases hzv : z = v
    · rw [hzv, hC2, upd_right]; exact e2
    by_cases hzr : z = r
    · rw [hzr]; exact o2.1
    · rw [hC2, upd_other _ hzr hzv]; exact h1 z
  -- 3. finalize all other nodes
  obtain ⟨C3, r3, o3, f3, -⟩ :=
    finalize bidir hch0 hconn D (D v) C2 o2 g2 (Finset.univ.erase r) (by simp)
  have hv3 : C3 v = D v := f3 v (by simp [Ne.symm hrv'])
  -- 4. the last interaction
  have st4 := step_of_choice bidir C3 hrv _ (EChoice.keepRand_valid hch0 (C3 r) (D v) (D r)
    (D v).colorBit (D r).errFlag (D v).errFlag)
  rw [hv3, eulerStep_final bidir R ch0 o3] at st4
  have hfin : upd C3 r v (D r, D v) = D := by
    funext z
    by_cases hzv : z = v
    · rw [hzv, upd_right]
    by_cases hzr : z = r
    · rw [hzr, upd_left _ hrv']
    · rw [upd_other _ hzr hzv]; exact f3 z (by simp [hzr])
  rw [hfin] at st4
  exact (r1.tail st2).trans (r3.tail st4)

end Graph

end SSLERegular
