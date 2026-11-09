import Papers.PODC2020.SelfStabHighDynamics.Model
import Mathlib.Order.Lex

/-!
# Algorithm 1 (self-stabilizing leader election for `TC_B(Δ)`, `Δ` known)

Local state `⟨lid(p), ttl(p)⟩` with `ttl(p) ∈ {0, …, 2Δ - 1}`; the possible local states do not
depend on the system (the algorithm knows nothing about `n`). Each round, `p` sends
`⟨lid(p), ttl(p)⟩` (line 2) and processes the set `mb` of messages received from its current
in-neighbours (lines 3–17). The lexicographic minimum of line 7 is `lexMin`.
-/

namespace Podc.SelfStabHighDynamics.Alg1

variable {ι : Type*} [LinearOrder ι]

/-- The local state of Algorithm 1. -/
@[ext]
structure St (ι : Type*) where
  /-- The output `lid(p)`. -/
  lid : ι
  /-- The degree of suspicion `ttl(p)`. -/
  ttl : ℕ

/-- Macro `updateTTL(v)` (lines u1–u4), for process `me` in state `s`. -/
def updateTTL (Δ : ℕ) (me : ι) (s : St ι) (v : ℕ) : St ι :=
  if 2 * Δ ≤ v then ⟨me, 0⟩ else if s.lid ≠ me then ⟨s.lid, v⟩ else s

/-- The lexicographic minimum (lowest identifier, then lowest `ttl`) of a nonempty finite set of
messages (line 7). -/
def lexMin (mb : Finset (ι × ℕ)) (h : mb.Nonempty) : ι × ℕ :=
  ofLex ((mb.map toLex.toEmbedding).min' (h.map))

/-- Lines 4–14. -/
def body (Δ : ℕ) (me : ι) (s : St ι) (mb : Finset (ι × ℕ)) : St ι :=
  if h : mb.Nonempty then
    let m := lexMin mb h
    if m.1 < s.lid then updateTTL Δ me ⟨m.1, s.ttl⟩ (m.2 + 1)
    else if m.1 = s.lid then updateTTL Δ me s (min s.ttl m.2 + 1)
    else updateTTL Δ me s (s.ttl + 1)
  else updateTTL Δ me s (s.ttl + 1)

/-- One round of process `me` from state `s`, with mailbox `mb` (lines 3–17). -/
def round (Δ : ℕ) (me : ι) (s : St ι) (mb : Finset (ι × ℕ)) : St ι :=
  let s' := body Δ me s mb
  if me ≤ s'.lid then ⟨me, 0⟩ else s'

/-- The message sent by a process in state `s` (line 2). -/
def sent (s : St ι) : Set (ι × ℕ) := {(s.lid, s.ttl)}

/-- Algorithm 1, for `Δ ≥ 1`. -/
noncomputable def alg (Δ : ℕ) (hΔ : 0 < Δ) : SAlg ι (St ι) where
  step me m := round Δ me ((m me).getD ⟨me, 0⟩) (rfin sent me m)
  lid _ s := s.lid
  S _ _ := {s | s.ttl < 2 * Δ}
  S_nonempty _ p _ := ⟨⟨p, 0⟩, by simp only [Set.mem_setOf_eq]; omega⟩

end Podc.SelfStabHighDynamics.Alg1
