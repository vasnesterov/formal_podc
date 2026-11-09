import Papers.PODC2020.SelfStabHighDynamics.Model
import Mathlib.Data.List.MinMax

/-!
# Algorithm 3 (self-stabilizing leader election for `TC_R`, `n` known)

Local state `MSt`: the input `n` (so the possible local states of `p` in the system `V` are those
with `n = |V|`), the map `members(p)` (a list of pairs `⟨id, t⟩` with distinct identifiers, at most
`n` of them, unbounded timestamps), and `lid(p)`.

The received pairs (line 4) are processed in the order of the list `mb`; the algorithm uses the
order of `Finset.toList`, which is arbitrary, and every lemma about `round` holds for every list.
Ties in macro `max(p)` are broken by `List.argmax` (the first maximal pair); the proofs only use
that the chosen pair has a maximal timestamp.

Line 7 reads `insert(p, ⟨id(0), 0⟩)` in the paper; this is a typo for `insert(p, ⟨id(p), 0⟩)`.
-/

namespace Podc.SelfStabHighDynamics.Alg3

variable {ι : Type*} [LinearOrder ι]

/-- Macros `max(p)` and `insert(p, ⟨id, t⟩)` (lines m1–m2, i1–i7) on the map `q`, with capacity
`n`. -/
def insert (n : ℕ) (q : List (ι × ℕ)) (x : ι × ℕ) : List (ι × ℕ) :=
  match q.lookup x.1 with
  | some t' => q.map fun y => if y.1 = x.1 then (y.1, min x.2 t') else y
  | none =>
    if q.length < n then q ++ [x] else
      match q.argmax Prod.snd with
      | some y => if x.2 < y.2 then q.erase y ++ [x] else q
      | none => q

/-- One round of process `me` from state `s`, processing the received pairs in the order of `mb`
(lines 4–8). -/
def round (me : ι) (s : MSt ι) (mb : List (ι × ℕ)) : MSt ι :=
  let q1 := mb.foldl (fun q x => if x.1 ≠ me then insert s.n q x else q) s.mem
  let q3 := insert s.n (q1.map fun x => (x.1, x.2 + 1)) (me, 0)
  ⟨s.n, q3, minKey q3 me⟩

/-- The pairs sent by a process in state `s` (line 2). -/
def sent (s : MSt ι) : Set (ι × ℕ) := {x | x ∈ s.mem}

/-- Algorithm 3. -/
noncomputable def alg : SAlg ι (MSt ι) where
  step me m := round me ((m me).getD ⟨0, [], me⟩) (rfin sent me m).toList
  lid _ s := s.lid
  S V _ := {s | s.n = V.card ∧ s.mem.length ≤ s.n ∧ (keys s.mem).Nodup}
  S_nonempty V p _ := ⟨⟨V.card, [], p⟩, by simp [keys]⟩

end Podc.SelfStabHighDynamics.Alg3
