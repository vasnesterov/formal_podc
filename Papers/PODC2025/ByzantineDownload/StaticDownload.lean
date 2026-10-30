import Papers.PODC2025.ByzantineDownload.Model

/-!
# Algorithm 6 (Static Download) and Theorem 5.9

Algorithm 6 of the paper, as a `Protocol` of the synchronous DR crash model with `k` peers, `n`
bits and the resilience parameter `f` (known to the peers). Indices are 0-based (`I = 0` is the
paper's `I(M) = 1`); a peer is active while `I < n` (`while I(M) ≤ n`).

Views last `f + 1` rounds; the local counter `j ∈ {0, …, f}` is the iteration of the message step.
In the first round of a view (`j = 0`) the leader `lead(view)` queries `b_I` (query step); in every
round of the view each peer that knows `res[I]` sends `⟨view, I, res[I]⟩` to every peer, and a peer
that receives a view-`view` message `⟨view, i, b⟩` sets `res[i] ← b`. At the end of the `(f+1)`-st
round (view change step) a peer that still has `res[I] = ⊥` adds `lead(view)` to `F`, otherwise it
increments `I`; then it moves to the least later view whose leader is not in `F`.
-/

namespace Podc.ByzantineDownload.Static

/-- Local state of a peer in Algorithm 6. -/
structure St (k n : ℕ) where
  /-- `res`. -/
  res : Fin n → Option Bool
  /-- `F`. -/
  F : Finset (Fin k)
  /-- `I(M)` (0-based). -/
  I : ℕ
  /-- `view(M)`. -/
  view : ℕ
  /-- The iteration `t - 1 ∈ {0, …, f}` of the message step within the view. -/
  j : ℕ

variable {k n : ℕ} [NeZero k]

/-- What the peer knows about `b_I` after the query sub-round. -/
def known (s : St k n) (a : Fin n → Option Bool) : Option Bool := get s.res s.I <|> get a s.I

/-- The first received view-`v` message `⟨v, i, b⟩`, as `(i, b)`. -/
def recv (v : ℕ) (inbox : Fin k → Option (ℕ × ℕ × Bool)) : Option (ℕ × Bool) :=
  (List.finRange k).findSome? (fun p => match inbox p with
    | some (v', i, b) => if v' = v then some (i, b) else none
    | none => none)

/-- Algorithm 6 (Static Download) with resilience parameter `f`. -/
def alg (k n f : ℕ) [NeZero k] : Protocol k n (St k n) (ℕ × ℕ × Bool) where
  init _ := { res := fun _ => none, F := ∅, I := 0, view := 1, j := 0 }
  query p s :=
    if h : s.I < n then (if s.j = 0 ∧ lead s.view = p then {⟨s.I, h⟩} else ∅) else ∅
  send _ s a _ := if s.I < n then (known s a).map (fun b => (s.view, s.I, b)) else none
  step _ s a inbox :=
    if s.I < n then
      let res1 := match known s a with
        | some b => set s.res s.I b
        | none => s.res
      let res2 := match recv s.view inbox with
        | some (i, b) => set res1 i b
        | none => res1
      if s.j < f then { s with res := res2, j := s.j + 1 }
      else if get res2 s.I = none then
        let F' := insert (lead s.view) s.F
        { res := res2, F := F', I := s.I, view := nextView F' s.view, j := 0 }
      else { res := res2, F := s.F, I := s.I + 1, view := nextView s.F s.view, j := 0 }
    else s
  res s := s.res

end Podc.ByzantineDownload.Static
