import Papers.PODC2020.SelfStabHighDynamics.Model

/-!
# Algorithm 2 (self-stabilizing leader election for `TC_Q(Δ)`, `n` and `Δ` known)

Local state `MSt`: the input `n` (so the possible local states of `p` in the system `V` are those
with `n = |V|`), the FIFO queue `members(p)` (a list, head first) of at most `n` pairs
`⟨id, t⟩` with distinct identifiers and `t ∈ {0, …, Δ}`, and `lid(p)`.

The received pairs (line 4) are processed in the order of the list `mb`; the algorithm uses the
order of `Finset.toList`, which is arbitrary, and every lemma about `round` holds for every list.
-/

namespace Podc.SelfStabHighDynamics.Alg2

variable {ι : Type*} [LinearOrder ι]

/-- Macro `insert(p, ⟨id, t⟩)` (lines i1–i6) on the queue `q`, with capacity `n`. -/
def insert (n : ℕ) (q : List (ι × ℕ)) (x : ι × ℕ) : List (ι × ℕ) :=
  match q.lookup x.1 with
  | some t' => q.filter (fun y => y.1 != x.1) ++ [(x.1, min x.2 t')]
  | none => (if q.length = n then q.tail else q) ++ [x]

/-- Line 6: increment the timestamps smaller than `Δ`. -/
def incr (Δ : ℕ) (q : List (ι × ℕ)) : List (ι × ℕ) :=
  q.map fun x => if x.2 < Δ then (x.1, x.2 + 1) else x

/-- One round of process `me` from state `s`, processing the received pairs in the order of `mb`
(lines 4–8). -/
def round (Δ : ℕ) (me : ι) (s : MSt ι) (mb : List (ι × ℕ)) : MSt ι :=
  let q1 := mb.foldl (fun q x => if x.1 ≠ me then insert s.n q x else q) s.mem
  let q3 := insert s.n (incr Δ q1) (me, 0)
  ⟨s.n, q3, minKey q3 me⟩

/-- The pairs sent by a process in state `s` (line 2). -/
def sent (Δ : ℕ) (s : MSt ι) : Set (ι × ℕ) := {x | x ∈ s.mem ∧ x.2 < Δ}

/-- Algorithm 2. -/
noncomputable def alg (Δ : ℕ) : SAlg ι (MSt ι) where
  step me m := round Δ me ((m me).getD ⟨0, [], me⟩) (rfin (sent Δ) me m).toList
  lid _ s := s.lid
  S V _ := {s | s.n = V.card ∧ s.mem.length ≤ s.n ∧ (keys s.mem).Nodup ∧ ∀ x ∈ s.mem, x.2 ≤ Δ}
  S_nonempty V p _ := ⟨⟨V.card, [], p⟩, by simp [keys]⟩

end Podc.SelfStabHighDynamics.Alg2
