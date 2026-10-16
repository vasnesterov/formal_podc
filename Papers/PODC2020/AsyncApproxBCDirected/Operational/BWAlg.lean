import Papers.PODC2020.AsyncApproxBCDirected.Operational.HistAlg
import Papers.PODC2020.AsyncApproxBCDirected.Round

/-!
# Algorithm BW + Filter-and-Average as an operational algorithm

The algorithm of Section 4 as a full-information `HistSpec` in the asynchronous model of
`AsyncModel.lean`, run for `N` asynchronous rounds (round `r < N` computes `x_v[r+1]`; the output
is `x_v[N]`).

* Messages (`BMsg`): `val r x p` (RedundantFlood of the value `x` of round `r` along path `p`) and
  `comp r c M^c F' k p` (FIFO-Flood of `COMPLETE(F')` with content `M^c`, initiator `c`,
  FIFO counter `k`, along the simple path `p`). Paths end at the sender; the receiver checks it.
* RedundantFlood (Appendix E): a node forwards the *first* `val` message received on a path `p`
  to every out-neighbour `w` such that `p ‖ v ‖ w` is redundant.
* FIFO-Flood / FIFO-Receive (Appendix F): `COMPLETE` messages carry the counter `k` of their
  initiator (number of earlier `COMPLETE`s of that round) and are forwarded along simple paths;
  a message is FIFO-received along a path once all smaller counters were received along it.
* The protocol logic (Maximal-Consistency, FIFO-Receive-All, Verify, Filter-and-Average) is the
  same as in `RoundModel.lean`, evaluated on the history (all conditions are re-evaluated after
  every reception; "for the first time" = first prefix of the history).
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

/-- Messages of the operational algorithm. -/
inductive BMsg (V : Type*) where
  | val (r : ℕ) (x : ℝ) (p : List V)
  | comp (r : ℕ) (c : V) (Mc : Finset (Msg V)) (F' : Finset V) (k : ℕ) (p : List V)

namespace BWOp

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Histories of received messages `(sender, message)`. -/
abbrev Hist (V : Type*) := List (V × BMsg V)

/-! ## First index -/

/-- The first `k ≤ n` with `P k`. -/
noncomputable def firstIdx (P : ℕ → Prop) (n : ℕ) : Option ℕ := by
  classical
  exact if h : ∃ k, k ≤ n ∧ P k then some (Nat.find (⟨h.choose, h.choose_spec.2⟩ : ∃ k, P k))
    else none

theorem firstIdx_eq_some {P : ℕ → Prop} {n k : ℕ} :
    firstIdx P n = some k ↔ k ≤ n ∧ P k ∧ ∀ j < k, ¬ P j := by
  classical
  unfold firstIdx
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      refine ⟨(Nat.find_min' _ h.choose_spec.2).trans h.choose_spec.1, Nat.find_spec _,
        fun j hj => Nat.find_min _ hj⟩
    · rintro ⟨-, hk, hmin⟩
      exact le_antisymm (Nat.find_min' _ hk) (not_lt.mp fun hlt => hmin _ hlt (Nat.find_spec _))
  · simp only [false_iff]
    rintro ⟨hk, hP, -⟩; exact h ⟨k, hk, hP⟩

theorem firstIdx_eq_none {P : ℕ → Prop} {n : ℕ} :
    firstIdx P n = none ↔ ∀ k ≤ n, ¬ P k := by
  classical
  unfold firstIdx
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩
  · simp only [true_iff]; intro k hk hP; exact h ⟨k, hk, hP⟩

theorem firstIdx_mono {P : ℕ → Prop} {n n' k : ℕ} (h : firstIdx P n = some k) (hn : n ≤ n') :
    firstIdx P n' = some k := by
  obtain ⟨h1, h2, h3⟩ := firstIdx_eq_some.mp h
  exact firstIdx_eq_some.mpr ⟨h1.trans hn, h2, h3⟩

/-! ## Received messages -/

/-- A valid `val` message of round `r` received by `v`: path extended by `v`. -/
def valOf (v : V) (r : ℕ) : V × BMsg V → Option (Msg V)
  | (u, .val r' x p) => if r' = r ∧ p.getLast? = some u then some (x, p ++ [v]) else none
  | _ => none

/-- A valid `comp` message of round `r` received by `v`: `(c, p ‖ v, M^c, F', k)`. -/
def compOf (v : V) (r : ℕ) :
    V × BMsg V → Option (V × List V × Finset (Msg V) × Finset V × ℕ)
  | (u, .comp r' c Mc F' k p) =>
    if r' = r ∧ p.getLast? = some u then some (c, p ++ [v], Mc, F', k) else none
  | _ => none

/-- The own value, if the round has started. -/
def ownSet (v : V) : Option ℝ → Finset (Msg V)
  | some x => {(x, [v])}
  | none => ∅

/-- `M_v` of round `r`: received values plus the own value. -/
noncomputable def recvM (v : V) (r : ℕ) (own : Option ℝ) (h : Hist V) : Finset (Msg V) := by
  classical exact (h.filterMap (valOf v r)).toFinset ∪ ownSet v own

variable (G : Digraph V) (f N : ℕ)

/-- Maximal-Consistency (line 10). -/
def MCop (v : V) (r : ℕ) (own : Option ℝ) (h : Hist V) (F' : Finset V) : Prop :=
  Consistent (excl (recvM v r own h) F') ∧ Full G (excl (recvM v r own h) F') F' v

/-- Threads of `v`. -/
noncomputable def threadL (v : V) : List (Finset V) := by
  classical exact (univ.filter fun F' : Finset V => v ∉ F' ∧ F'.card ≤ f).toList

/-- Out-neighbours of `v`. -/
noncomputable def outL [DecidableRel G.Adj] (v : V) : List V :=
  (univ.filter fun w => G.Adj v w ∧ v ≠ w).toList

section Round

variable (v : V) (r : ℕ) (own : Hist V → Option ℝ)

/-- The first prefix length at which Maximal-Consistency holds for thread `F'`. -/
noncomputable def mcK (h : Hist V) (F' : Finset V) : Option ℕ :=
  firstIdx (fun k => MCop G v r (own (h.take k)) (h.take k) F') h.length

/-- The content of `COMPLETE(F')`. -/
noncomputable def mcContent (h : Hist V) (F' : Finset V) : Finset (Msg V) :=
  match mcK G v r own h F' with
  | some k => excl (recvM v r (own (h.take k)) (h.take k)) F'
  | none => ∅

/-- The `COMPLETE` messages of `v` in round `r`, in sending order. -/
noncomputable def compSeq (h : Hist V) : List (Finset V) := by
  classical
  exact (List.range (h.length + 1)).flatMap fun k =>
    (threadL f v).filter fun F' => mcK G v r own h F' = some k

/-- The FIFO counter of `COMPLETE(F')`. -/
noncomputable def counter (h : Hist V) (F' : Finset V) : ℕ := by
  classical exact (compSeq G f v r own h).idxOf F'

/-- `v`'s own `COMPLETE` messages (received by itself along the path `[v]`). -/
noncomputable def ownCR (h : Hist V) : Finset (V × List V × Finset (Msg V) × Finset V) := by
  classical
  exact ((threadL f v).filter fun F' => (mcK G v r own h F').isSome).toFinset.image
    fun F' => (v, [v], mcContent G v r own h F', F')

/-- FIFO-received `COMPLETE` messages: all smaller counters received along the same path. -/
noncomputable def fifoCR (h : Hist V) : Finset (V × List V × Finset (Msg V) × Finset V) := by
  classical
  exact ((h.filterMap (compOf v r)).filter fun e => ∀ j < e.2.2.2.2,
    ∃ e' ∈ h.filterMap (compOf v r), e'.1 = e.1 ∧ e'.2.1 = e.2.1 ∧ e'.2.2.2.2 = j).toFinset.image
      fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1)

/-- All `COMPLETE` messages FIFO-received by `v` in round `r`. -/
noncomputable def CRop (h : Hist V) : Finset (V × List V × Finset (Msg V) × Finset V) := by
  classical exact fifoCR v r h ∪ ownCR G f v r own h

/-- FIFO-Receive-All (line 12). -/
def FIFORecAllOp (h : Hist V) (Fv : Finset V) : Prop :=
  ∀ c, ∃ Mc, ∀ p, IsSimplePath G p c v → (∀ y ∈ p, Reaches G Fv y v) →
    (c, p, Mc, Fv) ∈ CRop G f v r own h

/-- `Verify` (lines 20–26). -/
def VerifyOp (h : Hist V) (Fv : Finset V) : Prop :=
  (∃ k ≤ h.length, FIFORecAllOp G f v r own (h.take k) Fv) ∧
  ∀ c p Mc Fu, (c, p, Mc, Fu) ∈ CRop G f v r own h → (∀ y ∈ p, Reaches G Fv y v) →
    Consistent Mc → Completeness G f v (recvM v r (own h) h) Mc Fu

/-- The first prefix length at which some thread verifies (Filter-and-Average, line 17). -/
noncomputable def faK (h : Hist V) : Option ℕ :=
  firstIdx (fun k => ∃ Fv : Finset V, v ∉ Fv ∧ Fv.card ≤ f ∧ VerifyOp G f v r own (h.take k) Fv)
    h.length

end Round

/-- A deterministic choice of the output of Filter-and-Average. -/
noncomputable def faOut (v : V) (Mv : Finset (Msg V)) : ℝ := by
  classical exact if hx : ∃ y, IsFA f v Mv y then Classical.choose hx else 0

/-- `x_v[r]` as a function of the history (`none` if round `r` has not started). -/
noncomputable def xv (v : V) (x : ℝ) : ℕ → Hist V → Option ℝ
  | 0 => fun _ => some x
  | r + 1 => fun h =>
    if r < N then
      match faK G f v r (xv v x r) h with
      | some k => some (faOut f v (recvM v r (xv v x r (h.take k)) (h.take k)))
      | none => none
    else none

/-! ## Sends -/

section Sends

variable [DecidableRel G.Adj]

/-- Relaying of the last received message. -/
noncomputable def relay (v : V) (h : Hist V) : List (V × BMsg V) := by
  classical
  exact match h.getLast? with
  | some (u, .val r y p) =>
    if r < N ∧ p.getLast? = some u ∧ ∀ e' ∈ h.dropLast, ∀ m ∈ valOf v r e', m.2 ≠ p ++ [v] then
      (outL G v).filterMap fun w =>
        if IsRedundant G (p ++ [v, w]) then some (w, .val r y (p ++ [v])) else none
    else []
  | some (u, .comp r c Mc F' k p) =>
    if r < N ∧ p.getLast? = some u ∧ (p ++ [v]).Nodup then
      (outL G v).filterMap fun w =>
        if (p ++ [v, w]).Nodup then some (w, .comp r c Mc F' k (p ++ [v])) else none
    else []
  | none => []

/-- Flooding of the own value of every round that starts now. -/
noncomputable def newVals (v : V) (x : ℝ) (h : Hist V) : List (V × BMsg V) := by
  classical
  exact (List.range N).flatMap fun r =>
    match xv G f N v x r h with
    | some y =>
      if h = [] ∨ xv G f N v x r h.dropLast = none then (outL G v).map fun w => (w, .val r y [v])
      else []
    | none => []

/-- Flooding of the `COMPLETE` messages of every thread whose Maximal-Consistency holds now for
the first time. -/
noncomputable def newComps (v : V) (x : ℝ) (h : Hist V) : List (V × BMsg V) := by
  classical
  exact (List.range N).flatMap fun r =>
    (threadL f v).flatMap fun F' =>
      if mcK G v r (xv G f N v x r) h F' = some h.length then
        (outL G v).map fun w => (w, .comp r v (mcContent G v r (xv G f N v x r) h F') F'
          (counter G f v r (xv G f N v x r) h F') [v])
      else []

/-- The operational Algorithm BW + Filter-and-Average with `N` rounds. -/
noncomputable def spec : HistSpec V (BMsg V) where
  react v x h := relay G N v h ++ newVals G f N v x h ++ newComps G f N v x h
  out v x h := xv G f N v x N h

/-- The algorithm. -/
noncomputable def alg : Algorithm V (BMsg V) (ℝ × Hist V) := (spec G f N).toAlg

end Sends

end BWOp

end AsyncApproxBCDirected
