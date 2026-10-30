import Papers.PODC2021.BFTInBlockDAG.Interpret

/-!
# Executions of a protocol over authenticated perfect point-to-point links

The paper's Theorem 5.1 transfers every property that holds for `P` "using the reliable
point-to-point link abstraction" (Lemma 4.3, which claims the properties of an *authenticated
perfect point-to-point link* of Cachin–Guerraoui–Rodrigues, Module 2.5: reliable delivery, no
duplication, authenticity). We model the safety part of this abstraction for one protocol instance
(label `ℓ`) in the asynchronous model with Byzantine servers `Byz`.

An execution is a finite list of events `(s, inp)`: correct server `s` handles input `inp`
(a request from the user, or the delivery of a message). Byzantine servers have no events; the
messages they send are arbitrary (any message with a Byzantine sender may be delivered).
`exec P ℓ tr` replays the events: the process states, the messages sent so far (with their senders)
and the interface trace (requests and indications, with the server).

* `LinkSafe`: every event is at a correct server, a delivered message is addressed to the receiving
  server, and (APL3, authenticity) a delivered message whose sender is correct was previously sent
  by that sender.
* `NoDup` (APL2, no duplication): no correct server delivers the same message twice.
* `NoDupCorrect`: the same, restricted to messages with a correct sender.
* `HoldsOverAPL P ℓ Byz Φ`: the interface trace of every execution over authenticated perfect
  links satisfies `Φ`.
-/

-- CSLib candidate: executions of a black-box protocol over authenticated point-to-point links
-- (`Cslib/Computability/Distributed/Links/Authenticated.lean`).

namespace Podc.BFTInBlockDAG

variable {S L R M I σ : Type} [DecidableEq S]

namespace Input
/-- Is this input a delivery? -/
def IsRecv {R M : Type} : Input R M → Prop
  | .req _ => False
  | .recv _ => True

instance {R M : Type} (i : Input R M) : Decidable i.IsRecv := by
  cases i <;> unfold IsRecv <;> infer_instance
end Input

/-- One event of the replay: update the state of the server, record the sent messages and the
interface events (the request, then the indications). -/
def execStep (P : Protocol S L R M I σ) (x : (S → σ) × List (S × M) × List (S × (R ⊕ I)))
    (e : S × Input R M) : (S → σ) × List (S × M) × List (S × (R ⊕ I)) :=
  let r := P.step (x.1 e.1) e.2
  (Function.update x.1 e.1 r.1, x.2.1 ++ r.2.1.map fun m => (e.1, m),
    x.2.2 ++ (match e.2 with | .req q => [(e.1, Sum.inl q)] | .recv _ => []) ++
      r.2.2.map fun i => (e.1, Sum.inr i))

/-- Replay a list of events from the initial states `P.init ℓ`. -/
def exec (P : Protocol S L R M I σ) (ℓ : L) (tr : List (S × Input R M)) :
    (S → σ) × List (S × M) × List (S × (R ⊕ I)) :=
  tr.foldl (execStep P) (P.init ℓ, [], [])

theorem exec_append (P : Protocol S L R M I σ) (ℓ : L) (t₁ t₂ : List (S × Input R M)) :
    exec P ℓ (t₁ ++ t₂) = t₂.foldl (execStep P) (exec P ℓ t₁) := by
  simp [exec, List.foldl_append]

theorem exec_concat (P : Protocol S L R M I σ) (ℓ : L) (t : List (S × Input R M))
    (e : S × Input R M) : exec P ℓ (t ++ [e]) = execStep P (exec P ℓ t) e := by
  simp [exec_append]

/-- The safety part of the authenticated perfect link abstraction. -/
def LinkSafe (P : Protocol S L R M I σ) (ℓ : L) (Byz : Set S) (tr : List (S × Input R M)) :
    Prop :=
  (∀ e ∈ tr, e.1 ∉ Byz) ∧
  ∀ t₁ s m t₂, tr = t₁ ++ (s, Input.recv m) :: t₂ →
    P.receiver m = s ∧ (P.sender m ∉ Byz → (P.sender m, m) ∈ (exec P ℓ t₁).2.1)

/-- The deliveries of a trace. -/
def recvs (tr : List (S × Input R M)) : List (S × Input R M) := tr.filter fun e => decide e.2.IsRecv

/-- APL2 (no duplication): no server delivers the same message twice. -/
def NoDup (tr : List (S × Input R M)) : Prop := (recvs tr).Nodup

/-- No duplication for messages with a correct sender. -/
def NoDupCorrect (P : Protocol S L R M I σ) (Byz : Set S) (tr : List (S × Input R M)) : Prop :=
  ((recvs tr).filter fun e => @decide (∃ m, e.2 = .recv m ∧ P.sender m ∉ Byz)
    (Classical.propDecidable _)).Nodup

/-- A property `Φ` of interface traces holds for `P` over authenticated perfect links. -/
def HoldsOverAPL (P : Protocol S L R M I σ) (ℓ : L) (Byz : Set S)
    (Φ : List (S × (R ⊕ I)) → Prop) : Prop :=
  ∀ tr, LinkSafe P ℓ Byz tr → NoDup tr → Φ (exec P ℓ tr).2.2

end Podc.BFTInBlockDAG
