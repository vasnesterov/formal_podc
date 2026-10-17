import Mathlib

/-!
# Algorithms, steps and executions (Jayanti, PODC 2025, §3–§4 and §6.1)

A distributed algorithm (Definition 4.1) is a family of state machines; a *step* (Definition 4.2)
is a quadruple `(π, σ, e, σ')` allowed by the transition relation of `π`. An execution is a set
`S` of steps together with an order on it. The three kinds of executions of the paper only differ
in the order:

* classical executions (Definition 4.4): a strict total order induced by real times;
* relativistic executions (Definition 4.4): a strict partial order induced by spacetime events
  (`Spacetime.lean`);
* computational executions (Definition 6.1): Lamport's happens-before order.

Orders are relations on the subtype `↥S`, so an execution is a pair `(S, r)` with
`r : S → S → Prop` and nothing outside `S` matters.

The order-independent part of the conditions on executions is `MsgValid` (validity and
at-most-once delivery of messages, principle Φ3 / axiom A3). The order-dependent parts are

* `ProcSeq S r` — for every processor `π`, the steps `S_π` of `π`, ordered by `r`, form a *rooted,
  consecutively permissible sequence* `s₁, s₂, …` (finite or of order type `ω`; we express "is a
  sequence" as: `r` is a strict total order on `S_π` in which every step has finitely many
  predecessors). This is principle Φ2 / property P2 / axiom A2;
* `MsgForward S r` — messages are oriented forward: if `m` is sent in `s` and received in `s'`
  then `r s s'` (CP2 / RP3 / A3).
-/

namespace RelativisticComputing

/-- **Definition 4.1** (distributed algorithm), for a set of processors `Proc` and a universe of
messages `Msg`. All processors share the types of states and events; `init π` is the set of
initial states `Σ⁰_π` and `δ π` is the transition relation of `π`. The function `sendTo` recognises
send events: `sendTo e = some (m, π')` iff `e` is the event `(π, send, m, π')` (sending `m` to the
intended recipient `π'`); `recv e = some m` iff `e` is the event `(π', receive, m)`. -/
structure Algorithm (Proc Msg : Type) where
  /-- States of the processors. -/
  State : Type
  /-- Computational events. -/
  Event : Type
  /-- Initial states of each processor. -/
  init : Proc → Set State
  /-- Transition relation `δ_π(σ, e, σ')`. -/
  δ : Proc → State → Event → State → Prop
  /-- Send events: the message and its intended recipient. -/
  sendTo : Event → Option (Msg × Proc)
  /-- Receive events: the received message. -/
  recv : Event → Option Msg

variable {Proc Msg : Type}

/-- **Definition 4.2** (computational step): a quadruple `(π, σ, e, σ')` with `δ_π(σ, e, σ')`. -/
structure Step (A : Algorithm Proc Msg) where
  /-- The processor at which the step occurs. -/
  proc : Proc
  /-- The state the step starts at. -/
  pre : A.State
  /-- The event of the step. -/
  ev : A.Event
  /-- The state the step ends at. -/
  post : A.State
  /-- The step is allowed by the transition relation of its processor. -/
  valid : A.δ proc pre ev post

variable {A : Algorithm Proc Msg}

/-- The step `s` sends the message `m` (to some intended recipient). -/
def Sends (s : Step A) (m : Msg) : Prop := ∃ π', A.sendTo s.ev = some (m, π')

/-- The step `s` receives the message `m`. -/
def Receives (s : Step A) (m : Msg) : Prop := A.recv s.ev = some m

/-- Message edge: some message is sent in `a` and received in `b`. -/
def MsgEdge {S : Set (Step A)} (a b : S) : Prop := ∃ m, Sends a.1 m ∧ Receives b.1 m

/-- Order-independent message conditions (Φ3, P3, A3): message transmissions are *valid* (only the
intended recipient receives a message) and satisfy *at-most-once* semantics (a message is received
at most once). -/
structure MsgValid (S : Set (Step A)) : Prop where
  /-- Validity: only the intended recipient receives a message. -/
  valid : ∀ (a b : S) (m : Msg) (π' : Proc), A.sendTo a.1.ev = some (m, π') →
    Receives b.1 m → b.1.proc = π'
  /-- At-most-once semantics. -/
  atMostOnce : ∀ (a b : S) (m : Msg), Receives a.1 m → Receives b.1 m → a = b

/-- Messages are oriented forward by `r`. -/
def MsgForward (S : Set (Step A)) (r : S → S → Prop) : Prop :=
  ∀ a b : S, MsgEdge a b → r a b

/-- For every processor `π`, the steps of `S` at `π`, ordered by `r`, form a rooted, consecutively
permissible sequence `s₁, s₂, …` (finite or infinite). "Sequence" = strict total order on `S_π` in
which every element has finitely many predecessors (i.e. order type `≤ ω`); *rooted*: the first
step starts at an initial state; *consecutively permissible*: each step starts at the state in which
its immediate predecessor ends. -/
structure ProcSeq (S : Set (Step A)) (r : S → S → Prop) : Prop where
  irrefl : ∀ a, ¬ r a a
  trans : ∀ a b c : S, a.1.proc = b.1.proc → b.1.proc = c.1.proc → r a b → r b c → r a c
  total : ∀ a b : S, a.1.proc = b.1.proc → a ≠ b → r a b ∨ r b a
  finite_pred : ∀ a : S, {b : S | b.1.proc = a.1.proc ∧ r b a}.Finite
  rooted : ∀ a : S, (∀ b : S, b.1.proc = a.1.proc → ¬ r b a) → a.1.pre ∈ A.init a.1.proc
  consec : ∀ a b : S, a.1.proc = b.1.proc → r a b →
    (∀ c : S, c.1.proc = a.1.proc → ¬ (r a c ∧ r c b)) → b.1.pre = a.1.post

/-- A strict total order (irreflexive, transitive, total on distinct elements) on `S`. -/
structure IsSTO {S : Type} (lt : S → S → Prop) : Prop where
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, a ≠ b → lt a b ∨ lt b a

lemma IsSTO.asymm {S : Type} {lt : S → S → Prop} (h : IsSTO lt) {a b : S} (hab : lt a b) :
    ¬ lt b a := fun hba => h.irrefl a (h.trans a b a hab hba)

lemma IsSTO.toMathlib {S : Type} {lt : S → S → Prop} (h : IsSTO lt) : IsStrictTotalOrder S lt where
  trichotomous a b h1 h2 := by
    by_contra hne
    rcases h.total a b hne with h3 | h3
    · exact h1 h3
    · exact h2 h3
  irrefl := h.irrefl
  trans := h.trans

/-- `lt` is a *total ordering* of `R`: a strict total order refining `R`. -/
def IsTotalOrderingOf {S : Type} (R lt : S → S → Prop) : Prop :=
  IsSTO lt ∧ ∀ a b, R a b → lt a b

/-! ### Classical executions -/

/-- **Definition 4.3** (classical physical execution `𝒳 = (S, t)`): `t` maps each step to the
distinct real time at which it occurs (CP1), the steps of each processor, in chronological order,
form a rooted consecutively permissible sequence (Φ1, Φ2), messages are valid and received at most
once (Φ3), and each message is received at a later time than it is sent (CP2). -/
structure IsClassicalPhys (A : Algorithm Proc Msg) (S : Set (Step A)) (t : S → ℝ) : Prop where
  inj : Function.Injective t
  procSeq : ProcSeq S (fun a b => t a < t b)
  msgValid : MsgValid S
  msgForward : MsgForward S (fun a b => t a < t b)

/-- **Definition 4.4** (classical execution): `(S, <_S)` is extracted from a classical physical
execution `(S, t)`, i.e. `s <_S s' ↔ t s < t s'`. -/
def IsClassical (A : Algorithm Proc Msg) (S : Set (Step A)) (lt : S → S → Prop) : Prop :=
  ∃ t : S → ℝ, IsClassicalPhys A S t ∧ ∀ a b, lt a b ↔ t a < t b

/-! ### Computational executions -/

/-- The generating relation of computational causality for a given order `r`: steps of the same
processor related by `r` (item (a)), and message edges (item (b)). -/
def CausalGen {S : Set (Step A)} (r : S → S → Prop) (a b : S) : Prop :=
  (a.1.proc = b.1.proc ∧ r a b) ∨ MsgEdge a b

/-- **Definition 6.1** (computational execution `Z = (S, ◁_S)`):
A1: `◁_S` is the transitive closure of the relations of A2 and A3 (program order and messages);
A2: the steps of each processor form a rooted, consecutively permissible sequence under `◁_S`;
A3: messages are valid, received at most once, and oriented forward by `◁_S`. -/
structure IsComputational (A : Algorithm Proc Msg) (S : Set (Step A)) (R : S → S → Prop) :
    Prop where
  closure : R = Relation.TransGen (CausalGen R)
  procSeq : ProcSeq S R
  msgValid : MsgValid S
  msgForward : MsgForward S R

/-! ### Basic lemmas -/

namespace ProcSeq

variable {S : Set (Step A)} {r r' : S → S → Prop}

/-- `ProcSeq` only depends on the restriction of the order to pairs of steps of the same
processor. -/
lemma congr (h : ProcSeq S r) (hrr : ∀ a b : S, a.1.proc = b.1.proc → (r a b ↔ r' a b)) :
    ProcSeq S r' where
  irrefl a ha := h.irrefl a ((hrr a a rfl).2 ha)
  trans a b c hab hbc h1 h2 :=
    (hrr a c (hab.trans hbc)).1 (h.trans a b c hab hbc ((hrr a b hab).2 h1) ((hrr b c hbc).2 h2))
  total a b hab hne := (h.total a b hab hne).imp (hrr a b hab).1 (hrr b a hab.symm).1
  finite_pred a := by
    refine (h.finite_pred a).subset ?_
    rintro b ⟨hb, hba⟩
    exact ⟨hb, (hrr b a hb).2 hba⟩
  rooted a ha := h.rooted a fun b hb hba => ha b hb ((hrr b a hb).1 hba)
  consec a b hab h1 hc := h.consec a b hab ((hrr a b hab).2 h1) fun c hc' ⟨h2, h3⟩ =>
    hc c hc' ⟨(hrr a c hc'.symm).1 h2, (hrr c b (hc'.trans hab)).1 h3⟩

/-- With countably many processors, every set of steps whose per-processor parts are sequences is
countable: the map `s ↦ (proc s, #predecessors of s at its processor)` is injective. -/
lemma countable [Countable Proc] (h : ProcSeq S r) : Countable S := by
  classical
  let g : S → Proc × ℕ := fun a => (a.1.proc, {b : S | b.1.proc = a.1.proc ∧ r b a}.ncard)
  refine Function.Injective.countable (f := g) ?_
  intro a b hab
  simp only [g, Prod.mk.injEq] at hab
  obtain ⟨hp, hn⟩ := hab
  by_contra hne
  have key : ∀ x y : S, x.1.proc = y.1.proc → r x y →
      {c : S | c.1.proc = x.1.proc ∧ r c x}.ncard <
        {c : S | c.1.proc = y.1.proc ∧ r c y}.ncard := by
    intro x y hxy hr
    apply Set.ncard_lt_ncard _ (h.finite_pred y)
    refine ⟨fun c ⟨hc, hcx⟩ => ⟨hc.trans hxy, h.trans c x y hc hxy hcx hr⟩, fun hsub => ?_⟩
    exact h.irrefl x (hsub ⟨hxy, hr⟩).2
  rcases h.total a b hp hne with hr | hr
  · exact (key a b hp hr).ne hn
  · have : b.1.proc = a.1.proc := hp.symm
    exact (key b a this hr).ne (by rw [hn])

end ProcSeq

/-- Every countable strict total order embeds into `(ℝ, <)` (via Cantor's theorem on countable
dense linear orders). -/
lemma exists_real_embedding {S : Type} [Countable S] {lt : S → S → Prop} (h : IsSTO lt) :
    ∃ t : S → ℝ, ∀ a b, lt a b ↔ t a < t b := by
  classical
  have : IsStrictTotalOrder S lt := h.toMathlib
  let : LinearOrder S := linearOrderOfSTO lt
  obtain ⟨f⟩ := Order.embedding_from_countable_to_dense S ℝ
  exact ⟨f, fun a b => f.lt_iff_lt.symm⟩

lemma injective_of_embedding {S : Type} {lt : S → S → Prop} (h : IsSTO lt) {t : S → ℝ}
    (ht : ∀ a b, lt a b ↔ t a < t b) : Function.Injective t := by
  intro a b hab
  by_contra hne
  rcases h.total a b hne with h1 | h1
  · exact ((ht a b).1 h1).ne hab
  · exact ((ht b a).1 h1).ne hab.symm

/-- The order induced by a real-valued injective map is a strict total order. -/
lemma isSTO_of_real {S : Type} (t : S → ℝ) (ht : Function.Injective t) :
    IsSTO (fun a b : S => t a < t b) where
  irrefl a := lt_irrefl (t a)
  trans _ _ _ := lt_trans
  total _ _ hne := lt_or_gt_of_ne (fun h => hne (ht h))

/-- **Computational executions from refined orders.** If `r` is a transitive order on `S` under
which the per-processor steps are sequences and messages go forward, then the transitive closure
`◁` of (`r` on same-processor pairs) ∪ (message edges) is a computational execution refined by
`r`. This is the construction in the proofs of Lemmas 6.2 and 6.4. -/
lemma isComputational_of_refined {S : Set (Step A)} {r : S → S → Prop}
    (htrans : ∀ a b c, r a b → r b c → r a c) (hseq : ProcSeq S r) (hv : MsgValid S)
    (hfwd : MsgForward S r) :
    IsComputational A S (Relation.TransGen (CausalGen r)) ∧
      ∀ a b, Relation.TransGen (CausalGen r) a b → r a b := by
  set R := Relation.TransGen (CausalGen r) with hR
  have hsub : ∀ a b, R a b → r a b := by
    intro a b hab
    induction hab with
    | single h => rcases h with ⟨_, h⟩ | h
                  · exact h
                  · exact hfwd _ _ h
    | tail _ h ih =>
      rcases h with ⟨_, h⟩ | h
      · exact htrans _ _ _ ih h
      · exact htrans _ _ _ ih (hfwd _ _ h)
  have hsame : ∀ a b : S, a.1.proc = b.1.proc → (r a b ↔ R a b) :=
    fun a b hab => ⟨fun h => Relation.TransGen.single (Or.inl ⟨hab, h⟩), hsub a b⟩
  refine ⟨⟨?_, hseq.congr hsame, hv, fun a b h => Relation.TransGen.single (Or.inr h)⟩, hsub⟩
  funext a b
  apply propext
  constructor
  · intro h
    refine Relation.TransGen.mono (fun x y hxy => ?_) a b h
    rcases hxy with ⟨hp, hxy⟩ | hxy
    · exact Or.inl ⟨hp, (hsame x y hp).1 hxy⟩
    · exact Or.inr hxy
  · intro h
    refine Relation.TransGen.closed (fun x y hxy => ?_) a b h
    rcases hxy with ⟨_, hxy⟩ | hxy
    · exact hxy
    · exact Relation.TransGen.single (Or.inr hxy)

end RelativisticComputing
