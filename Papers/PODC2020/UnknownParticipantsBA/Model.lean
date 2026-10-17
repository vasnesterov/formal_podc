import Mathlib
import Podc.Foundations.Count

/-!
# The id-only model (Khanchandani–Wattenhofer, PODC 2020, Section 3)

A synchronous (lock-step) message-passing system with Byzantine failures in which every node knows
only its own identifier (and its input):

* identifiers come from an arbitrary type `I` (in the examples `ℕ`); they are unique but not
  necessarily consecutive. The set of existing nodes is `G ∪ F` (correct and faulty, disjoint and
  finite); neither `n = |G ∪ F|` nor `f = |F|` is known to the nodes — a protocol is a single state
  machine, parameterised by nothing but the node's own id and input;
* in every round every correct node *broadcasts* a finite set of messages (to all nodes, including
  itself), computed from its state;
* the receiver sees a finite set of pairs `(sender, message)` with the **true** sender id
  (a Byzantine node cannot forge its identifier when communicating directly); duplicates of the same
  message from the same sender in a round are discarded automatically (sets);
* a faulty node `q` may send an arbitrary finite set of messages `adv s q v` to every node `v` in
  every round (different sets to different nodes, possibly none — so it may "get itself known to
  only a subset of the nodes"); messages may *mention* arbitrary, even non-existent identifiers.

`run A E s v` is the state of node `v` after `s` steps; step `s + 1` consumes the messages
broadcast at the end of step `s` (by correct nodes: `A.out (run A E s q)`; by faulty nodes:
`E.adv s q v`). The states of faulty nodes are meaningless.

-- CSLib candidate (synchronous broadcast model with unknown participants).
-/

namespace UnknownBA

/-- A deterministic protocol of the id-only model: initial state from the own id and the input,
the set of messages broadcast at the end of a round, and the transition on the set of received
`(sender, message)` pairs. -/
structure Protocol (I X M S : Type*) where
  init : I → X → S
  out : S → Finset M
  step : S → Finset (I × M) → S

/-- The environment of a run: correct nodes `G`, Byzantine nodes `F`, inputs, and the messages
`adv s q v` sent by the Byzantine node `q` to `v` at the end of step `s`. -/
structure Env (I X M : Type*) where
  G : Finset I
  F : Finset I
  disj : Disjoint G F
  input : I → X
  adv : ℕ → I → I → Finset M

variable {I X M S : Type*} [DecidableEq I] [DecidableEq M]

/-- The messages received by `v` in step `s + 1`, given the states `st` after step `s`. -/
def inbox (A : Protocol I X M S) (E : Env I X M) (st : I → S) (s : ℕ) (v : I) :
    Finset (I × M) :=
  E.G.biUnion (fun q => (A.out (st q)).image (fun m => (q, m))) ∪
    E.F.biUnion (fun q => (E.adv s q v).image (fun m => (q, m)))

/-- The run of protocol `A` in environment `E`: `run A E s v` is the state of `v` after `s`
steps. -/
def run (A : Protocol I X M S) (E : Env I X M) : ℕ → I → S
  | 0, v => A.init v (E.input v)
  | s + 1, v => A.step (run A E s v) (inbox A E (run A E s) s v)

@[simp] lemma run_zero (A : Protocol I X M S) (E : Env I X M) (v : I) :
    run A E 0 v = A.init v (E.input v) := rfl

lemma run_succ (A : Protocol I X M S) (E : Env I X M) (s : ℕ) (v : I) :
    run A E (s + 1) v = A.step (run A E s v) (inbox A E (run A E s) s v) := rfl

/-- Number of (distinct) senders of message `m` in a received set. -/
abbrev cnt (B : Finset (I × M)) (m : M) : ℕ := B.countEq Prod.snd m

/-- The senders of a received set. -/
def senders (B : Finset (I × M)) : Finset I := B.image Prod.fst

section counting

variable (A : Protocol I X M S) (E : Env I X M) (st : I → S) (s : ℕ) (v : I)

lemma filter_inbox (m : M) :
    (inbox A E st s v).filter (fun e => e.2 = m) =
      (E.G.filter (fun q => m ∈ A.out (st q))).image (fun q => (q, m)) ∪
        (E.F.filter (fun q => m ∈ E.adv s q v)).image (fun q => (q, m)) := by
  ext ⟨q, m'⟩
  simp only [inbox, Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h | h, rfl⟩
    · obtain ⟨q', hq', m'', hm, rfl, rfl⟩ := h
      exact Or.inl ⟨_, ⟨hq', hm⟩, rfl, rfl⟩
    · obtain ⟨q', hq', m'', hm, rfl, rfl⟩ := h
      exact Or.inr ⟨_, ⟨hq', hm⟩, rfl, rfl⟩
  · rintro (⟨q', ⟨hq', hm⟩, rfl, rfl⟩ | ⟨q', ⟨hq', hm⟩, rfl, rfl⟩)
    · exact ⟨Or.inl ⟨q', hq', m, hm, rfl, rfl⟩, rfl⟩
    · exact ⟨Or.inr ⟨q', hq', m, hm, rfl, rfl⟩, rfl⟩

/-- The number of copies of `m` received by `v` = (correct senders of `m`, the same for every
receiver) + (faulty senders of `m` to `v`). -/
lemma cnt_inbox (m : M) :
    cnt (inbox A E st s v) m =
      (E.G.filter (fun q => m ∈ A.out (st q))).card +
        (E.F.filter (fun q => m ∈ E.adv s q v)).card := by
  rw [cnt, Finset.countEq, filter_inbox, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective]
  · intro a b h; simpa using h
  · intro a b h; simpa using h
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_filter]
    rintro _ ⟨q, ⟨hq, -⟩, rfl⟩ ⟨q', ⟨hq', -⟩, h⟩
    simp only [Prod.mk.injEq, and_true] at h
    subst h
    exact Finset.disjoint_left.mp E.disj hq hq'

lemma senders_inbox_subset : senders (inbox A E st s v) ⊆ E.G ∪ E.F := by
  intro q hq
  simp only [senders, inbox, Finset.mem_image, Finset.mem_union, Finset.mem_biUnion] at hq
  obtain ⟨⟨q', m⟩, (⟨q'', h1, m', -, h2⟩ | ⟨q'', h1, m', -, h2⟩), rfl⟩ := hq <;>
    simp only [Prod.mk.injEq] at h2 <;> obtain ⟨rfl, rfl⟩ := h2 <;> simp [h1]

lemma mem_senders_inbox_of_correct {q : I} (hq : q ∈ E.G) {m : M} (hm : m ∈ A.out (st q)) :
    q ∈ senders (inbox A E st s v) := by
  simp only [senders, inbox, Finset.mem_image]
  exact ⟨(q, m), Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, hq, by simp [hm]⟩), rfl⟩

/-- Messages from a correct sender in the inbox are exactly its broadcast. -/
lemma mem_inbox_correct {q : I} (hq : q ∈ E.G) (m : M) :
    (q, m) ∈ inbox A E st s v ↔ m ∈ A.out (st q) := by
  simp only [inbox, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro (⟨q', -, m', hm, rfl, rfl⟩ | ⟨q', hq', m', -, rfl, rfl⟩)
    · exact hm
    · exact absurd hq' (Finset.disjoint_left.mp E.disj hq)
  · intro hm; exact Or.inl ⟨q, hq, m, hm, rfl, rfl⟩

end counting

/-! ### Threshold arithmetic (Lemmas 1, 2 of the BA; Lemmas 2, 4, 9 of the full version)

Notation: `g = |G|`, `h` = number of faulty nodes heard of by the receiver (so `n_v = g + h`),
`a` = number of correct senders of the message (the same at every receiver, since correct nodes
broadcast), `b ≤ h` = number of faulty senders of the message to the receiver. -/

/-- Lemma 1 (BA): `n_v / 3` copies contain a copy from a correct node. -/
lemma lemma1_arith {g h a b : ℕ} (hb : b ≤ h) (hh : 2 * h < g) (hc : g + h ≤ 3 * (a + b)) :
    0 < a := by omega

/-- Lemma 2 (BA): `2 n_v / 3` copies at one correct node give more than `(g + f) / 3`
correct senders, hence `n_u / 3` copies at every correct node `u`. -/
lemma lemma2_arith {g h f a b : ℕ} (hb : b ≤ h) (hh : h ≤ f) (hf : 2 * f < g)
    (hc : 2 * (g + h) ≤ 3 * (a + b)) : g + f < 3 * a := by omega

/-- Lemma 9 (full version): `2n_u/3` copies of `m` at `u` and `2n_v/3` copies of `m'` at `v`
come from more than `g` correct senders in total. -/
lemma lemma9_arith {g h h' f a b a' b' : ℕ} (hb : b ≤ h) (hb' : b' ≤ h') (hh : h ≤ f)
    (hh' : h' ≤ f) (hf : 2 * f < g) (hc : 2 * (g + h) ≤ 3 * (a + b))
    (hc' : 2 * (g + h') ≤ 3 * (a' + b')) : g < a + a' := by omega

end UnknownBA
