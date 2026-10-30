import Papers.PODC2025.ByzantineDownload.Model

/-!
# Algorithm 7 (Rapid Download) and a counterexample to Lemmas 5.13, 5.15 and Theorem 5.16

We encode Algorithm 7 of the paper as a `Protocol` of the synchronous DR crash model and exhibit
an execution with `k = 4` peers, `n = 4` bits and `f = 2` crashes (`β = 1/2`) in which a nonfaulty
peer finishes (its index passes `n`) without ever learning bit 2 (1-based; bit `1 : Fin 4` here).

## Timing (the only interpretation choices)

The pseudocode is event driven; we fix the synchronous timing of the paper's own Remarks in §5.2:
a message sent in round `r` is received at the end of round `r`.

* A peer that invokes `view change` at the end of round `r` sends its `⟨view change v', I⟩` message
  in round `r + 1` and is *idle* at the end of round `r + 1` (it does not expect a view message in
  that round); from the end of round `r + 2` on it suspects `lead(view)` at the end of every round in
  which it receives nothing from it (line 26).
* A peer that receives `view change v` messages for the first time at the end of round `r` (line 7)
  takes the highest index among the ones received *in that round* (line 8), queries in round `r + 1`
  if needed, and sends its view message in rounds `r + 1` and `r + 2` (to every peer, itself
  included).
* View messages are processed as in lines 16–24: `res[i] ← b` only if `v ≥ view(M)`, and the second
  view-`v` message increments `I(M)` whatever its index was.
* Initialisation (not specified in the paper): `lead(1)` starts view 1 at time 0 with index 1, i.e.
  sends `⟨view 1, 1, b₁⟩` in rounds 1 and 2; nobody is idle initially.
* A peer whose index exceeds `n` has finished (it no longer suspects or changes views, and ignores
  leadership requests); this only matters after the failure has happened.

Indices are 0-based in Lean (`I = 0` is the paper's `I = 1`); views and `lead(v) = v mod k` are as in
the paper.
-/

namespace Podc.ByzantineDownload.Rapid

/-- The messages of Algorithm 7: an optional view message `⟨view v, i, b⟩` and an optional
`⟨view change v, i⟩` message (a peer may send both in the same round to the same peer). -/
structure Msg where
  /-- `⟨view v, i, b⟩`. -/
  view : Option (ℕ × ℕ × Bool)
  /-- `⟨view change v, i⟩`. -/
  vc : Option (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Local state of a peer in Algorithm 7. -/
structure St (k n : ℕ) where
  /-- `view(M)`. -/
  view : ℕ
  /-- `I(M)` (0-based). -/
  I : ℕ
  /-- `F`: the peers `M` believes crashed. -/
  F : Finset (Fin k)
  /-- `res`. -/
  res : Fin n → Option Bool
  /-- Idle at the end of the current round (line 33). -/
  idle : Bool
  /-- The view entered at the end of the idle round (line 34). -/
  target : ℕ
  /-- The `view change` message to send in the current round. -/
  vcOut : Option (ℕ × ℕ)
  /-- Views of the view messages received so far (with multiplicity). -/
  got : List ℕ
  /-- Views this peer has started leading (line 7: "for the first time"). -/
  led : List ℕ
  /-- Leader duty: view, index, number of view messages still to send. -/
  duty : Option (ℕ × ℕ × ℕ)
  deriving DecidableEq

variable {k n : ℕ} [NeZero k]

/-- Procedure `view change` (lines 30–34), invoked at the end of a round. -/
def invokeVC (s : St k n) : St k n :=
  let v' := nextView s.F s.view
  { s with vcOut := some (v', s.I), idle := true, target := v' }

/-- The bit carried by the leader's view message (after its query, if any). -/
def dutyBit (s : St k n) (a : Fin n → Option Bool) : Option (ℕ × ℕ × Bool) :=
  match s.duty with
  | some (v, i, r) =>
    if 0 < r then
      match get s.res i <|> get a i with
      | some b => some (v, i, b)
      | none => none
    else none
  | none => none

/-- Lines 7–14 for one view `v` with `view change` messages of indices `idx` in this round. -/
def startLead (s : St k n) (v : ℕ) (idx : List ℕ) : St k n :=
  if v ∈ s.led then s else
  let I' := max s.I (idx.foldl max 0)
  let s := { s with led := v :: s.led, I := I' }
  if I' < n then { s with duty := some (v, I', 2) } else s

/-- Lines 16–24 for one received view message. Returns the new state and whether `view change`
was invoked. -/
def onView (s : St k n) (m : ℕ × ℕ × Bool) : St k n × Bool :=
  let (v, i, b) := m
  let s := if s.view ≤ v then
      { s with view := v, I := if s.I ≤ i then i else s.I, res := set s.res i b }
    else s
  let s := { s with idle := false, got := v :: s.got }
  if s.got.count v = 2 then
    let s := { s with I := s.I + 1 }
    if s.I < n then (invokeVC s, true) else (s, false)
  else (s, false)

/-- Algorithm 7 as a protocol of the DR model. -/
def alg (k n : ℕ) [NeZero k] : Protocol k n (St k n) Msg where
  init p :=
    { view := 1, I := 0, F := ∅, res := fun _ => none, idle := false, target := 1, vcOut := none,
      got := [], led := if p = lead 1 then [1] else [],
      duty := if p = lead 1 ∧ 0 < n then some (1, 0, 2) else none }
  query _ s :=
    match s.duty with
    | some (_, i, 2) => if h : i < n then (if s.res ⟨i, h⟩ = none then {⟨i, h⟩} else ∅) else ∅
    | _ => ∅
  send _ s a q :=
    let vw := dutyBit s a
    let vc := match s.vcOut with
      | some (v', i) => if lead v' = q then some (v', i) else none
      | none => none
    if vw.isSome || vc.isSome then some ⟨vw, vc⟩ else none
  step _ s a inbox :=
    -- the leader's query answer and the bookkeeping of its sends
    let s0 : St k n :=
      { s with
        res := (match s.duty with
          | some (_, i, _) => match get a i with
            | some b => set s.res i b
            | none => s.res
          | none => s.res),
        duty := (match s.duty with
          | some (v, i, r) => if 1 < r then some (v, i, r - 1) else none
          | none => none),
        vcOut := none }
    let senders := List.finRange k
    -- lines 7–14: view change messages
    let vcs : List (ℕ × ℕ) := senders.filterMap (fun p => (inbox p).bind Msg.vc)
    let views := (vcs.map Prod.fst).dedup.mergeSort (· ≤ ·)
    let s1 := views.foldl (fun s v =>
      startLead s v ((vcs.filter (fun x => x.1 = v)).map Prod.snd)) s0
    -- lines 16–24: view messages, in the order of the senders
    let oldView := s.view
    let heard := senders.any (fun p => (inbox p).isSome && p == lead oldView) ||
      senders.any (fun p => match (inbox p).bind Msg.view with
        | some (v, _, _) => decide (oldView ≤ v)
        | none => false)
    let (s2, inv) := senders.foldl (fun (acc : St k n × Bool) p =>
      match (inbox p).bind Msg.view with
      | some m => let r := onView acc.1 m; (r.1, acc.2 || r.2)
      | none => acc) (s1, false)
    -- lines 26–28 and the end of the idle round (line 34)
    if inv then s2
    else if s2.idle then
      { s2 with idle := false, view := if s2.view ≤ s2.target then s2.target else s2.view }
    else if !heard && decide (s2.I < n) then
      invokeVC { s2 with F := insert (lead s2.view) s2.F }
    else s2
  res s := s.res

/-! ### A memoized simulator (used to evaluate executions in the kernel) -/

/-- The configurations of `A`, tabulated as lists (`tab A X π t = [cfg t 0, …, cfg t (k-1)]`). -/
def tab {S M : Type} {n k : ℕ} (A : Protocol k n S M) (X : Fin n → Bool) (π : Pattern k) (d : S) :
    ℕ → List S
  | 0 => List.ofFn A.init
  | t + 1 => let l := tab A X π d t
    List.ofFn (A.round X π (t + 1) (fun p => l.getD p.val d))

omit [NeZero k] in
lemma cfg_eq_tab {S M : Type} (A : Protocol k n S M) (X : Fin n → Bool) (π : Pattern k) (d : S)
    (t : ℕ) (p : Fin k) : A.cfg X π t p = (tab A X π d t).getD p.val d := by
  induction t generalizing p with
  | zero => simp [tab, Protocol.cfg, List.getD_eq_getElem?_getD]
  | succ t ih =>
    have : A.cfg X π t = fun p => (tab A X π d t).getD p.val d := funext ih
    simp [tab, Protocol.cfg, this, List.getD_eq_getElem?_getD]

/-! ### The counterexample -/

/-- The counterexample's crash pattern (`k = 4`, `f = 2`): peer 1 (= `lead(1)`) crashes in round 2,
its second view-1 message reaching only peer 2; peer 2 (= `lead(2)`) crashes in round 4, its first
view-2 message reaching only peers 0 and 1. Peers 0 and 3 are nonfaulty. -/
def badPattern : Pattern 4 where
  crash p := if p = 1 then some 2 else if p = 2 then some 4 else none
  reach p q := (p = 1 ∧ q = 2) || (p = 2 ∧ (q = 0 ∨ q = 1))

lemma badPattern_admissible : badPattern.Admissible 2 := by
  unfold Pattern.Admissible Pattern.faulty; decide

lemma badPattern_nonfaulty_0 : badPattern.Nonfaulty 0 := rfl
lemma badPattern_nonfaulty_3 : badPattern.Nonfaulty 3 := rfl

/-- The input of the counterexample (any input works: only whether a bit is known matters). -/
def X₀ : Fin 4 → Bool := fun _ => true

/-- The configuration of the counterexample at time `t`. -/
def badCfg (t : ℕ) : Fin 4 → St 4 4 := (alg 4 4).cfg X₀ badPattern t

lemma badCfg_eq (t : ℕ) (p : Fin 4) :
    badCfg t p = (tab (alg 4 4) X₀ badPattern ((alg 4 4).init 0) t).getD p.val ((alg 4 4).init 0) :=
  cfg_eq_tab _ _ _ _ _ _

/-- The tabulated configuration at time `t`. -/
abbrev badTab (t : ℕ) : Fin 4 → St 4 4 :=
  fun p => (tab (alg 4 4) X₀ badPattern ((alg 4 4).init 0) t).getD p.val ((alg 4 4).init 0)

lemma badCfg_eq_tab (t : ℕ) : badCfg t = badTab t := funext (badCfg_eq t)

lemma badPattern_alive (p : Fin 4) {r : ℕ} (hr : 4 ≤ r) :
    badPattern.alive p r = badPattern.alive p 4 := by
  fin_cases p <;> simp [Pattern.alive, badPattern] <;> omega

lemma badPattern_delivers (p q : Fin 4) {r : ℕ} (hr : 5 ≤ r) :
    badPattern.delivers p q r = badPattern.delivers p q 5 := by
  fin_cases p <;> simp [Pattern.delivers, badPattern] <;> omega

lemma round_eq_five {r : ℕ} (hr : 5 ≤ r) (c : Fin 4 → St 4 4) :
    (alg 4 4).round X₀ badPattern r c = (alg 4 4).round X₀ badPattern 5 c := by
  funext q
  have hi : (alg 4 4).inbox X₀ badPattern r c q = (alg 4 4).inbox X₀ badPattern 5 c q := by
    funext p; simp only [Protocol.inbox, badPattern_delivers p q hr]
  simp only [Protocol.round, hi, badPattern_alive q (by omega : 4 ≤ r),
    badPattern_alive q (by omega : 4 ≤ 5)]

set_option maxRecDepth 100000 in
/-- The configuration at time 13 is a fixed point of all later rounds. -/
lemma round_badTab_13 : (alg 4 4).round X₀ badPattern 5 (badTab 13) = badTab 13 := by
  funext p
  revert p
  decide +kernel

/-- From time 13 on, nothing changes. -/
lemma badCfg_stable (t : ℕ) (ht : 13 ≤ t) : badCfg t = badCfg 13 := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    change (alg 4 4).round X₀ badPattern (t + 1) (badCfg t) = badCfg 13
    rw [ih, round_eq_five (by omega), badCfg_eq_tab, round_badTab_13]

set_option maxRecDepth 100000 in
lemma badCfg_7 : (badCfg 7 0).I = 2 ∧ (badCfg 7 3).res 1 = none := by
  rw [badCfg_eq_tab]; decide +kernel

set_option maxRecDepth 100000 in
lemma badCfg_13 : (badCfg 13 3).I = 4 ∧ (badCfg 13 3).res 1 = none ∧ (badCfg 13 3).F = {1, 2} := by
  rw [badCfg_eq_tab]; decide +kernel

/-- **Lemma 5.13 is false.** "For every two nonfaulty peers `M, M'` and index `i`, if `i < I(M)` then
`res_{M'}[i] = b_i`": at time 7 of the counterexample, the nonfaulty peer 0 has `I = 2` (0-based;
the paper's `I = 3`), but the nonfaulty peer 3 has `res[1] = ⊥` (the paper's bit 2). -/
theorem lemma_5_13_false :
    ∃ (X : Fin 4 → Bool) (π : Pattern 4), π.Admissible 2 ∧ ∃ (t : ℕ) (M M' : Fin 4) (i : Fin 4),
      π.Nonfaulty M ∧ π.Nonfaulty M' ∧ i.val < ((alg 4 4).cfg X π t M).I ∧
      ((alg 4 4).cfg X π t M').res i ≠ some (X i) := by
  refine ⟨X₀, badPattern, badPattern_admissible, 7, 0, 3, 1, badPattern_nonfaulty_0,
    badPattern_nonfaulty_3, ?_, ?_⟩
  · change 1 < (badCfg 7 0).I
    rw [badCfg_7.1]; decide
  · change (badCfg 7 3).res 1 ≠ _
    rw [badCfg_7.2]; simp

/-- **Lemma 5.15 is false.** In the counterexample (`k = n = 4`, `f = 2`), the nonfaulty peer 3
has finished (`I(3) > n` in the paper's 1-based indexing, `= 4` here) and never changes state
again from time 13 on, but never learns bit 1 (the paper's bit 2): no number of views suffices. -/
theorem lemma_5_15_false :
    ∃ (X : Fin 4 → Bool) (π : Pattern 4), π.Admissible 2 ∧ ∃ M : Fin 4, π.Nonfaulty M ∧
      ∀ t ≥ 13, 4 ≤ ((alg 4 4).cfg X π t M).I ∧ ((alg 4 4).cfg X π t M).res 1 = none := by
  refine ⟨X₀, badPattern, badPattern_admissible, 3, badPattern_nonfaulty_3, fun t ht => ?_⟩
  change 4 ≤ (badCfg t 3).I ∧ (badCfg t 3).res 1 = none
  rw [badCfg_stable t ht]
  exact ⟨badCfg_13.1.ge, badCfg_13.2.1⟩

/-- **Algorithm 7 does not solve Download** with `k = 4` peers, `n = 4` bits and `f = 2` crash
faults (`f ≤ βk` with `β = 1/2 < 1`), contrary to the proof of Theorem 5.16, at any time bound. -/
theorem rapid_not_solves (T : ℕ) : ¬ (alg 4 4).SolvesWithin 2 T := by
  intro h
  obtain ⟨X, π, hπ, M, hM, hfin⟩ := lemma_5_15_false
  have := congrFun (h X π hπ M hM (max T 13) (le_max_left _ _)) 1
  have h2 := (hfin (max T 13) (le_max_right _ _)).2
  change ((alg 4 4).cfg X π (max T 13) M).res 1 = some (X 1) at this
  rw [h2] at this
  exact absurd this (by simp)

/-- Sanity check of the encoding: without crashes, Algorithm 7 downloads all 4 bits with 4 peers
within 12 rounds (3 rounds per view), each peer querying one bit. -/
def noCrash : Pattern 4 := ⟨fun _ => none, fun _ _ => false⟩

set_option maxRecDepth 100000 in
theorem rapid_crashFree :
    (∀ p, (alg 4 4).res ((alg 4 4).cfg X₀ noCrash 12 p) = fun i => some (X₀ i)) ∧
    ∀ p, (alg 4 4).queries X₀ noCrash p 12 = 1 := by
  simp only [Protocol.queries, cfg_eq_tab _ _ _ ((alg 4 4).init 0)]
  constructor
  · intro p; funext i; revert p i; decide +kernel
  · decide +kernel

end Podc.ByzantineDownload.Rapid
