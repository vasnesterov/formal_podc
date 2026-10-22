import Papers.PODC2022.FullyDefective.Robbins.Model

/-!
# Lemma 11 of [CCGS22] (safety part): the invariant of Algorithm 3

An inductive invariant of Algorithm 3 (`Robbins/Model.lean`). The paper proves Lemma 11 by
"repeating the proof of Lemma 5" for the occurrences of the nodes; here the invariant is stated
directly on positions of the Robbins cycle.

## The common part (`Common`)

* `netEq` — channel accounting: on every channel `x → y` the pulses in transit are the `request`
  pulses sent by `x` and not yet counted by `y`, plus possibly the unique token/data/end pulse
  (the ghost `wv`). Request pulses are counted per epoch: `x` sends `mult x y` of them on `x → y`
  in each epoch (one per link `x → y` of the cycle) and `y` expects as many;
* `reqLe` — `y` never counted more `request` pulses from `x` than `x` has sent;
* `rot` — Challenge 1 of the paper: **every node's segment `0` contains the token**, i.e. its
  occurrence `0` is the first occurrence at or after the token position `τ`.

## The stages of an epoch

`H = C τ` is the token holder (or the last node that held the token).

* `TokStage` — every node completed all started epochs and is in its token phase; the token is
  either held by `H` (lines 1–3 of `H`) or travels counterclockwise on the link `τ → τ - 1`;
* `DataStage pre d s` — epoch `|pre| + 1` with payload `d`: the data pulses travel clockwise one by
  one; `s < d·L` links have been traversed so far and the current pulse is on the link
  `τ + s → τ + s + 1`. Every non-holder `u` has received `cntF u τ s` data pulses (the number of
  its occurrences among `τ + 1, …, τ + s`) and waits at its next occurrence;
* `EndStage pre d r` — the `end` pulse travels counterclockwise on the link `τ + r + 1 → τ + r`;
  non-holders whose occurrences are all at clockwise distance `≤ r` from `τ` are still in their
  data phase, those with all occurrences beyond `r` have completed the epoch, the others are in
  their `end` loop.
-/

set_option linter.unusedSectionVars false

namespace Podc.FullyDefective.RobbinsSim

variable {V : Type*} {L : ℕ}

/-- Whether the node already broadcast its `request` pulses in its current epoch (`fend`: the epoch
is already counted as completed). -/
def Phase.sent : Phase V L → ℕ
  | .idle | .fend _ => 0
  | _ => 1

/-- Request pulses from `x` counted in the current epoch, `m` being the multiplicity of `x → u`. -/
def Phase.rIn (m : ℕ) (x : V) : Phase V L → ℕ
  | .idle | .fend _ => 0
  | .waitReq need => m - need x
  | _ => m

/-- Program points of the token phase (lines 1–17). -/
def Phase.IsTok : Phase V L → Prop
  | .idle | .waitReq _ | .ready => True
  | _ => False

/-- Number of epochs completed by `u`. -/
abbrev Config.ep (c : Config V L) (u : V) : ℕ := (c.node u).log.length

/-- The token/data/end pulse in transit on `x → y` (`0` or `1`). -/
def Config.wave [DecidableEq V] (c : Config V L) (x y : V) : ℕ := if c.wv = some (x, y) then 1 else 0

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} {R : RobbinsCycle G}

variable (R) in
/-- Request pulses counted by `y` on the channel `x → y`, over all epochs. -/
def rcv (c : Config V R.L) (y x : V) : ℕ := mult R x y * c.ep y + (c.node y).ph.rIn (mult R x y) x

variable (R) in
/-- Request pulses sent by `x` on the channel `x → y`, over all epochs. -/
def snt (c : Config V R.L) (x y : V) : ℕ := mult R x y * (c.ep x + (c.node x).ph.sent)

/-- The part of the invariant common to all stages. -/
structure Common (c : Config V R.L) : Prop where
  netEq : ∀ x y, c.net x y + rcv R c y x = snt R c x y + c.wave x y
  reqLe : ∀ x y, rcv R c y x ≤ snt R c x y
  needLe : ∀ u need, (c.node u).ph = .waitReq need → ∀ x, need x ≤ mult R x u
  needPos : ∀ u need, (c.node u).ph = .waitReq need → ∃ x, 0 < need x
  posq : ∀ u, ∀ a ∈ (c.node u).q, 0 < a
  rot : ∀ u, (c.node u).o = firstOcc R u c.τ

/-- Token stage: everybody completed the started epochs and is in its token phase. -/
structure TokStage (c : Config V R.L) : Prop where
  log : ∀ u, (c.node u).log = c.ds
  isTok : ∀ u, (c.node u).ph.IsTok
  tok : ((c.node (R.C c.τ)).tok = true ∧ (c.node (R.C c.τ)).ph.isReq = true ∧
      (∀ u, u ≠ R.C c.τ → (c.node u).tok = false) ∧ c.wv = none) ∨
    ((∀ u, (c.node u).tok = false) ∧ c.wv = some (R.C c.τ, R.C (c.τ - 1)) ∧
      (c.node (R.C c.τ)).ph = .ready)

/-- The state of a non-holder in the data stage, `k` = data pulses received so far. -/
def DataNode (s : Node V R.L) (k : ℕ) (p : ZMod R.L) : Prop :=
  (k = 0 ∧ s.ph.IsTok) ∨ (0 < k ∧ s.ph = .fdata k p)

/-- Data stage of epoch `|pre| + 1` (payload `d`): the data pulses have traversed `s` links. -/
structure DataStage (c : Config V R.L) (pre : List ℕ) (d s : ℕ) : Prop where
  ds_eq : c.ds = pre ++ [d]
  s_lt : s < d * R.L
  wv : c.wv = some (R.C (c.τ + s), R.C (c.τ + s + 1))
  hph : (c.node (R.C c.τ)).ph = .hdata d (s / R.L + 1) (firstOcc R (R.C c.τ) (c.τ + s + 1))
  htok : (c.node (R.C c.τ)).tok = true
  hlog : (c.node (R.C c.τ)).log = pre
  others : ∀ u, u ≠ R.C c.τ → (c.node u).tok = false ∧ (c.node u).log = pre ∧
    DataNode (c.node u) (cntF R u c.τ s) (firstOcc R u (c.τ + s + 1))

/-- The state of a non-holder in the end stage at distance `r` from `τ`. -/
def EndNode (s : Node V R.L) (τ : ZMod R.L) (u : V) (pre : List ℕ) (d r : ℕ) : Prop :=
  (dist τ (lastOcc R u (τ - 1)) ≤ r ∧ s.ph = .fdata (d * occ R u) (firstOcc R u τ) ∧ s.log = pre) ∨
  (dist τ (firstOcc R u τ) ≤ r ∧ r < dist τ (lastOcc R u (τ - 1)) ∧
    s.ph = .fend (lastOcc R u (τ + r)) ∧ s.log = pre ++ [d]) ∨
  (r < dist τ (firstOcc R u τ) ∧ s.ph.IsTok ∧ s.log = pre ++ [d])

/-- End stage of epoch `|pre| + 1` (payload `d`): the `end` pulse is on the link
`τ + r + 1 → τ + r`. -/
structure EndStage (c : Config V R.L) (pre : List ℕ) (d r : ℕ) : Prop where
  ds_eq : c.ds = pre ++ [d]
  r_lt : r < R.L
  wv : c.wv = some (R.C (c.τ + r + 1), R.C (c.τ + r))
  hph : (c.node (R.C c.τ)).ph = .hend d (lastOcc R (R.C c.τ) (c.τ + r))
  htok : (c.node (R.C c.τ)).tok = true
  hlog : (c.node (R.C c.τ)).log = pre
  others : ∀ u, u ≠ R.C c.τ → (c.node u).tok = false ∧ EndNode (c.node u) c.τ u pre d r

/-- The invariant of Algorithm 3. -/
def Inv (c : Config V R.L) : Prop :=
  Common c ∧ (TokStage c ∨ (∃ pre d s, DataStage c pre d s) ∨ ∃ pre d r, EndStage c pre d r)

/-! ### Reactions -/

section react

variable (u x : V) (s : Node V R.L)

lemma release_s (req : Bool) : (release R s req).s = { s with ph := .ready, tok := false } ∨
    ((release R s req).s = { s with ph := .ready } ∧ (release R s req).dst = none) := by
  unfold release; split_ifs <;> simp

@[simp] lemma release_req (req : Bool) : (release R s req).req = req := by
  unfold release; split_ifs <;> rfl

lemma onReq_cases (need : V → ℕ) (req : Bool) :
    ((onReq R s need req).s.ph = .ready ∧ ∀ y, need y = 0) ∨
      ((onReq R s need req).s.ph = .waitReq need ∧ (onReq R s need req).dst = none) := by
  unfold onReq; split_ifs with h
  · left; rcases release_s (R := R) s req with h' | ⟨h', -⟩ <;> rw [h'] <;> exact ⟨rfl, h⟩
  · right; exact ⟨rfl, rfl⟩

@[simp] lemma onReq_req (need : V → ℕ) (req : Bool) : (onReq R s need req).req = req := by
  unfold onReq; split_ifs <;> simp

@[simp] lemma onReq_log (need : V → ℕ) (req : Bool) : (onReq R s need req).s.log = s.log := by
  unfold onReq; split_ifs
  · rcases release_s (R := R) s req with h | ⟨h, -⟩ <;> rw [h]
  · rfl

@[simp] lemma onReq_q (need : V → ℕ) (req : Bool) : (onReq R s need req).s.q = s.q := by
  unfold onReq; split_ifs
  · rcases release_s (R := R) s req with h | ⟨h, -⟩ <;> rw [h]
  · rfl

@[simp] lemma onReq_o (need : V → ℕ) (req : Bool) : (onReq R s need req).s.o = s.o := by
  unfold onReq; split_ifs
  · rcases release_s (R := R) s req with h | ⟨h, -⟩ <;> rw [h]
  · rfl

lemma onReq_rIn (need : V → ℕ) (req : Bool) (m : ℕ) (a : V) :
    (onReq R s need req).s.ph.rIn m a = m - need a := by
  rcases onReq_cases (R := R) s need req with ⟨h, h0⟩ | ⟨h, -⟩ <;> rw [h]
  · simp [Phase.rIn, h0]
  · rfl

lemma onReq_sent (need : V → ℕ) (req : Bool) : (onReq R s need req).s.ph.sent = 1 := by
  rcases onReq_cases (R := R) s need req with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl

lemma onReq_isTok (need : V → ℕ) (req : Bool) : (onReq R s need req).s.ph.IsTok := by
  rcases onReq_cases (R := R) s need req with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> trivial

/-- A `token`/`data`/`end` pulse is sent upon a `request` pulse only by a token holder releasing
the token. -/
lemma onReq_dst (need : V → ℕ) (req : Bool) {y : V} (h : (onReq R s need req).dst = some y) :
    s.tok = true ∧ y = R.C (s.o - 1) ∧ (onReq R s need req).s = { s with ph := .ready, tok := false } := by
  unfold onReq at h ⊢; split_ifs at h ⊢
  unfold release at h ⊢; split_ifs at h ⊢ with ht
  simp at h; exact ⟨ht, h.symm, rfl⟩

lemma onReq_tok (need : V → ℕ) (req : Bool) (h : (onReq R s need req).dst = none) :
    (onReq R s need req).s.tok = s.tok := by
  unfold onReq at h ⊢; split_ifs at h ⊢
  · unfold release at h ⊢; split_ifs at h ⊢ <;> simp_all
  · rfl

@[simp] lemma react_req : (react R u s x).req = s.ph.isIdle := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph <;> simp only [react, onReq_req, Phase.isIdle] <;> (try split_ifs) <;> (try split) <;> rfl

lemma react_sent :
    (react R u s x).s.log.length + (react R u s x).s.ph.sent =
      s.log.length + s.ph.sent + if s.ph.isIdle then 1 else 0 := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | idle => simp only [react]; rw [onReq_sent, onReq_log]; simp [Phase.sent, Phase.isIdle]
  | waitReq need => simp only [react]; rw [onReq_sent, onReq_log]; simp [Phase.sent, Phase.isIdle]
  | ready =>
    simp only [react, Phase.isIdle, Bool.false_eq_true, ite_false]
    split_ifs <;> [split; skip] <;> simp [Phase.sent]
  | _ =>
    simp only [react, Phase.isIdle, Bool.false_eq_true, ite_false]
    split_ifs <;> simp [Phase.sent]

lemma react_rcv (hneed : ∀ need, s.ph = .waitReq need → ∀ a, need a ≤ mult R a u)
    (hw : waits R u s x) (a : V) :
    mult R a u * (react R u s x).s.log.length + (react R u s x).s.ph.rIn (mult R a u) a =
      mult R a u * s.log.length + s.ph.rIn (mult R a u) a +
        if a = x ∧ s.ph.isReq = true then 1 else 0 := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | idle =>
    simp only [waits] at hw
    simp only [react]; rw [onReq_log, onReq_rIn]
    simp only [Phase.rIn, Phase.isReq, and_true]
    by_cases hax : a = x
    · subst hax; simp; omega
    · simp [hax]
  | waitReq need =>
    simp only [waits] at hw
    have := hneed need rfl
    simp only [react]; rw [onReq_log, onReq_rIn]
    simp only [Phase.rIn, Phase.isReq, and_true]
    by_cases hax : a = x
    · subst hax; simp; have := this a; omega
    · simp [hax]
  | ready =>
    simp only [react, Phase.isReq, Bool.false_eq_true, and_false, ite_false, add_zero]
    split_ifs <;> [split; skip] <;> simp [Phase.rIn]
  | _ =>
    simp only [react, Phase.isReq, Bool.false_eq_true, and_false, ite_false, add_zero]
    split_ifs <;> simp [Phase.rIn] <;> ring

/-- The queue only loses its head, upon taking the token. -/
lemma react_q : (react R u s x).s.q = s.q ∨ s.q = (s.q.headD 0) :: (react R u s x).s.q := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | ready => simp only [react]; split_ifs <;> [split; skip] <;> simp_all
  | idle | waitReq need => simp [react]
  | _ => simp only [react]; (try split_ifs) <;> simp

lemma react_need (hneed : ∀ need, s.ph = .waitReq need → ∀ a, need a ≤ mult R a u) (need : V → ℕ)
    (h : (react R u s x).s.ph = .waitReq need) (a : V) : need a ≤ mult R a u := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | idle =>
    simp only [react] at h
    rcases onReq_cases (R := R) ⟨.idle, tok, q, log, o⟩
      (Function.update (fun y => mult R y u) x (mult R x u - 1)) true with ⟨h', -⟩ | ⟨h', -⟩ <;>
      rw [h'] at h
    · cases h
    · cases h; by_cases hax : a = x
      · subst hax; simp
      · simp [hax]
  | waitReq n =>
    simp only [react] at h
    rcases onReq_cases (R := R) ⟨.waitReq n, tok, q, log, o⟩
      (Function.update n x (n x - 1)) false with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] at h
    · cases h
    · cases h; have := hneed n rfl a; by_cases hax : a = x
      · subst hax; simp; omega
      · simp [hax]; exact this
  | ready => simp only [react] at h; split_ifs at h <;> (try split at h) <;> simp at h
  | fdata k p =>
    simp only [react] at h; split_ifs at h <;> simp at h
  | _ => simp only [react] at h; split_ifs at h <;> simp at h

lemma react_need_pos (need : V → ℕ) (h : (react R u s x).s.ph = .waitReq need) : ∃ a, 0 < need a := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | idle | waitReq n =>
    simp only [react, onReq] at h
    split_ifs at h with h0
    · unfold release at h; split_ifs at h <;> simp at h
    · cases h; push Not at h0; obtain ⟨y, hy⟩ := h0; exact ⟨y, Nat.pos_of_ne_zero hy⟩
  | ready => simp only [react] at h; split_ifs at h <;> (try split at h) <;> simp at h
  | _ => simp only [react] at h; split_ifs at h <;> simp at h

end react

/-! ### Steps -/

section next

variable (c : Config V R.L) (u x v a b : V)

lemma next_recv_node : (next R c (.recv u x)).node v =
    if v = u then (react R u (c.node u) x).s else c.node v := by
  simp [next, Function.update_apply]

@[simp] lemma next_recv_node_self : (next R c (.recv u x)).node u = (react R u (c.node u) x).s := by
  simp [next]

lemma next_recv_node_ne {v u : V} (h : v ≠ u) : (next R c (.recv u x)).node v = c.node v := by
  simp [next, h]

lemma next_recv_net : (next R c (.recv u x)).net a b = c.net a b - (if a = x ∧ b = u then 1 else 0) +
    (if a = u then (if (react R u (c.node u) x).req then mult R u b else 0) +
      (if (react R u (c.node u) x).dst = some b then 1 else 0) else 0) := rfl

lemma next_recv_τ : (next R c (.recv u x)).τ =
    if tokRecv R u (c.node u) x then prevOcc R (c.node u).o else c.τ := rfl

lemma next_recv_ds : (next R c (.recv u x)).ds = if tokRecv R u (c.node u) x then
    (match (c.node u).q with | a :: _ => c.ds ++ [a] | [] => c.ds) else c.ds := rfl

lemma next_recv_wv : (next R c (.recv u x)).wv = match (react R u (c.node u) x).dst with
    | some y => some (u, y)
    | none => if (c.node u).ph.isReq then c.wv else none := rfl

omit [Fintype V] in
lemma wave_aux (o : Option V) (w : Option (V × V)) (q : Bool) :
    (if (match o with | some y => some (u, y) | none => if q then w else none) = some (a, b) then 1
      else 0) =
    if o = some b ∧ a = u then 1 else if o = none ∧ q = true then (if w = some (a, b) then 1 else 0)
      else 0 := by
  rcases o with _ | y
  · cases q <;> simp
  · have : (u = a ∧ y = b) ↔ (y = b ∧ a = u) := ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
    simp [this]

lemma next_recv_wave : (next R c (.recv u x)).wave a b =
    if (react R u (c.node u) x).dst = some b ∧ a = u then 1
    else if (react R u (c.node u) x).dst = none ∧ (c.node u).ph.isReq = true then c.wave a b
    else 0 := by
  simp only [Config.wave, next_recv_wv]; exact wave_aux _ _ _ _ _ _

lemma ep_next_recv : (next R c (.recv u x)).ep v =
    if v = u then (react R u (c.node u) x).s.log.length else c.ep v := by
  simp only [Config.ep, next_recv_node]; split_ifs <;> rfl

end next

/-- A non-request pulse read by `u` from `x` must be the token/data/end pulse when `u` has counted
all request pulses from `x` of its epoch and `x` is not ahead by an epoch. -/
lemma wave_of_read {c : Config V R.L} (hC : Common c) {u x : V} (hnet : 0 < c.net x u)
    (hr : (c.node u).ph.rIn (mult R x u) x = mult R x u)
    (hs : mult R x u * (c.ep x + (c.node x).ph.sent) ≤ mult R x u * (c.ep u + 1)) :
    c.wv = some (x, u) := by
  have h := hC.netEq x u
  simp only [rcv, snt, hr] at h
  rw [mul_add (mult R x u) (c.ep u), mul_one] at hs
  have : 0 < c.wave x u := by omega
  simp only [Config.wave] at this; split_ifs at this with h' <;> [exact h'; omega]

/-- The common part of the invariant is preserved by reading a pulse, provided that a pulse read
as a non-request pulse is the token/data/end pulse in transit, that a request pulse is never
read in place of the token/data/end pulse, and that a token/data/end pulse is sent upon a request
pulse only when none is in transit. -/
theorem common_recv {c : Config V R.L} (hC : Common c) {u x : V} (hen : Enabled R c (.recv u x))
    (hw : (c.node u).ph.isReq = false → c.wv = some (x, u))
    (hreq : (c.node u).ph.isReq = true → c.wv = some (x, u) → rcv R c u x < snt R c x u)
    (hdst : ∀ y, (react R u (c.node u) x).dst = some y → (c.node u).ph.isReq = true → c.wv = none)
    (hrot : ∀ v, ((next R c (.recv u x)).node v).o = firstOcc R v (next R c (.recv u x)).τ) :
    Common (next R c (.recv u x)) := by
  obtain ⟨hwt, hnet⟩ := hen
  have hneed : ∀ need, (c.node u).ph = .waitReq need → ∀ a, need a ≤ mult R a u := hC.needLe u
  have hrcv : ∀ a b, rcv R (next R c (.recv u x)) b a = rcv R c b a +
      if b = u ∧ a = x ∧ (c.node u).ph.isReq = true then 1 else 0 := by
    intro a b
    by_cases hb : b = u
    · subst hb
      simp only [rcv, ep_next_recv, next_recv_node, ite_true]
      rw [react_rcv _ _ _ hneed hwt a]; simp [and_assoc]
    · simp [rcv, ep_next_recv, next_recv_node, hb]
  have hsnt : ∀ a b, snt R (next R c (.recv u x)) a b = snt R c a b +
      if a = u ∧ (c.node u).ph.isIdle = true then mult R u b else 0 := by
    intro a b
    by_cases ha : a = u
    · subst ha
      simp only [snt, ep_next_recv, next_recv_node, ite_true]
      rw [react_sent]; split_ifs <;> simp_all <;> ring
    · simp [snt, ep_next_recv, next_recv_node, ha]
  have hreqidle : (c.node u).ph.isIdle = true → (c.node u).ph.isReq = true := by
    intro h; revert h; cases (c.node u).ph <;> simp [Phase.isIdle, Phase.isReq]
  refine ⟨fun a b => ?_, fun a b => ?_, fun v need hv a => ?_, fun v need hv => ?_, fun v a ha => ?_,
    hrot⟩
  · have h0 := hC.netEq a b
    have hI1 : (if a = x ∧ b = u then 1 else 0) ≤ c.net a b := by
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact hnet
      · exact Nat.zero_le _
    have e2 : (if a = u then (if (react R u (c.node u) x).req then mult R u b else 0) +
        (if (react R u (c.node u) x).dst = some b then 1 else 0) else 0) =
        (if a = u ∧ (c.node u).ph.isIdle = true then mult R u b else 0) +
          (if (react R u (c.node u) x).dst = some b ∧ a = u then 1 else 0) := by
      rw [react_req]; by_cases ha : a = u <;> simp [ha]
    have e3 : (if b = u ∧ a = x ∧ (c.node u).ph.isReq = true then 1 else 0) =
        if (c.node u).ph.isReq = true then (if a = x ∧ b = u then 1 else 0) else 0 := by
      by_cases h1 : a = x <;> by_cases h2 : b = u <;> by_cases hq : (c.node u).ph.isReq = true <;>
        simp [h1, h2, hq]
    rw [hrcv, hsnt, next_recv_wave, next_recv_net, e2, e3]
    by_cases hq : (c.node u).ph.isReq = true
    · simp only [hq, ite_true, and_true]
      rcases hd : (react R u (c.node u) x).dst with _ | y
      · simp only [reduceCtorEq, false_and, ite_false, ite_true, add_zero]; omega
      · have hwv := hdst y hd hq
        have h0' : c.wave a b = 0 := by simp [Config.wave, hwv]
        simp only [reduceCtorEq, false_and, ite_false, add_zero]; omega
    · simp only [Bool.not_eq_true] at hq
      have hwv := hw hq
      have h0' : c.wave a b = if a = x ∧ b = u then 1 else 0 := by
        have : (x = a ∧ u = b) ↔ (a = x ∧ b = u) :=
          ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
        unfold Config.wave; rw [hwv]; simp only [Option.some.injEq, Prod.mk.injEq, this]
      rw [h0'] at h0
      simp only [hq, Bool.false_eq_true, and_false, ite_false, add_zero]
      omega
  · rw [hrcv, hsnt]
    have h1 := hC.reqLe a b
    by_cases hI : b = u ∧ a = x ∧ (c.node u).ph.isReq = true
    · rw [ite_eq_left hI]
      obtain ⟨rfl, rfl, hq⟩ := hI
      have : rcv R c b a < snt R c a b := by
        by_cases hwv : c.wv = some (a, b)
        · exact hreq hq hwv
        · have h0 := hC.netEq a b
          simp [Config.wave, hwv] at h0; omega
      omega
    · rw [ite_eq_right hI]; omega
  · by_cases hvu : v = u
    · subst hvu; rw [next_recv_node_self] at hv; exact react_need _ _ _ hneed need hv a
    · rw [next_recv_node_ne _ _ hvu] at hv; exact hC.needLe v need hv a
  · by_cases hvu : v = u
    · subst hvu; rw [next_recv_node_self] at hv; exact react_need_pos _ _ _ need hv
    · rw [next_recv_node_ne _ _ hvu] at hv; exact hC.needPos v need hv
  · by_cases hvu : v = u
    · subst hvu; rw [next_recv_node_self] at ha
      rcases react_q (R := R) v x (c.node v) with h | h
      · rw [h] at ha; exact hC.posq v a ha
      · exact hC.posq v a (by rw [h]; exact List.mem_cons_of_mem _ ha)
    · rw [next_recv_node_ne _ _ hvu] at ha; exact hC.posq v a ha

end Podc.FullyDefective.RobbinsSim
