import Papers.PODC2016.CollaborativeListSpec.RGA

/-!
# The literal RGA of the paper violates condition (1c)

Section 4.2 builds the node of `ins(a, k)` "as described in the Insert procedure of Section 4.1",
which takes the parent `a_{k-1}` of `s(N) = a₀ … a_{n-1}`, i.e. it counts positions in the list
**including tombstones**. The positions of `ins(a, k)` in the specification (Section 3, condition
(1c) of Definition 7) refer to the user-visible list `s(N) \ T`. As soon as a tombstone precedes
the insertion point the two disagree.

`RGA.literalProtocol` is `RGA.protocol` with the literal parent (`a_{min k n - 1}` of `s(N)`, or the
root if `min k n = 0`, so that `k > n` behaves as `k = n`). `RGA.literal_not_weak`: for any number
of replicas, in the
execution `ins(x, 0); ins(y, 1); del(x); ins(b, 1)` (well formed, causal broadcast,
user assumptions) the last response is `[b, y]`, while (1c) demands `b` at position
`min(1, 2 - 1) = 1`. So no abstract execution of this execution is in `A_weak` (hence none in
`A_strong`): Theorem 1 fails for the protocol as literally written. `RGA.lean` proves it for the
corrected protocol (parent taken in the visible list), which is the original RGA.
-/

namespace Podc.CollaborativeListSpec

namespace RGA

variable {U : Type} [DecidableEq U] {n : ℕ}

/-- The parent of `ins(a, k)` in the literal Insert procedure of Section 4.1: the element at
position `min k n - 1` of `s(N)` (tombstones included), or the root. -/
def literalParent (q : St U) (k : ℕ) : Option U :=
  if min k (s q.1).length = 0 then none else (s q.1)[min k (s q.1).length - 1]?

/-- The node created by `ins(a, k)` in the literal protocol. -/
def literalNode (q : St U) (i : Fin n) (a : U) (k : ℕ) : Node U :=
  ⟨a, newTS q.1 i, literalParent q k⟩

/-- The protocol `R_rga^n` of Section 4.2 as literally written. -/
def literalProtocol (U : Type) [DecidableEq U] (n : ℕ) :
    Protocol (Fin n) (LOp U) (List U) (St U) (Msg U) where
  init _ := ([], [])
  resp i σ
    | .ins a k => visible (literalNode σ.1 i a k :: σ.1.1, σ.1.2)
    | .del a => visible (σ.1.1, a :: σ.1.2)
    | .read => visible σ.1
  doStep i σ
    | .ins a k =>
      let m := literalNode σ.1 i a k
      ((m :: σ.1.1, σ.1.2), some ((σ.2.getD ([], [])).1 ++ [m], (σ.2.getD ([], [])).2))
    | .del a => ((σ.1.1, a :: σ.1.2), some ((σ.2.getD ([], [])).1, (σ.2.getD ([], [])).2 ++ [a]))
    | .read => σ
  sendStep _ σ := σ.1
  recvStep _ σ m := ((m.1.union σ.1.1, σ.1.2 ++ m.2), σ.2)

/-- `ins(x, 0); ins(y, 1); del(x); ins(b, 1)` at replica `0` of `m + 1` replicas, with
`x, y, b = 0, 1, 2`. -/
def literalExec (m : ℕ) : List (Act (Fin (m + 1)) (LOp ℕ)) :=
  [.doOp 0 (.ins 0 0), .doOp 0 (.ins 1 1), .doOp 0 (.del 0), .doOp 0 (.ins 2 1)]

theorem s_x : s [(⟨0, toLex (1, 0), none⟩ : Node ℕ)] = [0] := by
  rw [s_cons_max (N := []) (by constructor <;> decide) (by simp), s_nil]; rfl

theorem s_yx : s [(⟨1, toLex (2, 0), some 0⟩ : Node ℕ), ⟨0, toLex (1, 0), none⟩] = [0, 1] := by
  rw [s_cons_max (by constructor <;> decide) (by decide), s_x]; decide

theorem s_byx : s [(⟨2, toLex (3, 0), some 0⟩ : Node ℕ), ⟨1, toLex (2, 0), some 0⟩,
    ⟨0, toLex (1, 0), none⟩] = [0, 2, 1] := by
  rw [s_cons_max (by constructor <;> decide) (by decide), s_yx]; decide

variable (m : ℕ)

theorem literal_hist1 :
    (literalProtocol ℕ (m + 1)).hist (literalExec m) 1 = some (0, .ins 1 1, [0, 1]) := by
  simp [Protocol.hist, literalExec, Protocol.stBefore, Protocol.exec, Protocol.step,
    Protocol.init₀, literalProtocol, literalNode, literalParent, newTS, maxX, visible, s_x, s_yx]

/-- The response of the last insert `ins(b, 1)` is `[b, y]`. -/
theorem literal_hist3 :
    (literalProtocol ℕ (m + 1)).hist (literalExec m) 3 = some (0, .ins 2 1, [2, 1]) := by
  simp [Protocol.hist, literalExec, Protocol.stBefore, Protocol.exec, Protocol.step,
    Protocol.init₀, literalProtocol, literalNode, literalParent, newTS, maxX, visible, s_x, s_yx,
    s_byx]

theorem literalExec_wf : (literalProtocol ℕ (m + 1)).WF (literalExec m) := by
  intro p hp
  simp only [literalExec, List.length_cons, List.length_nil] at hp
  interval_cases p <;> trivial

theorem literalExec_causal : CausalBroadcast (literalExec m) := by
  rintro s s' r q ⟨r₁, h₁⟩
  rcases s with _ | _ | _ | _ | s <;> simp [literalExec] at h₁

theorem literalExec_userOK : UserOK (literalProtocol ℕ (m + 1)) (literalExec m) := by
  refine ⟨?_, ?_⟩
  · intro p q r r' a k k' hp hq
    rcases p with _ | _ | _ | _ | p <;> rcases q with _ | _ | _ | _ | q <;>
      simp [literalExec] at hp hq <;> omega
  · intro p r a hp
    rcases p with _ | _ | _ | _ | p <;> simp [literalExec] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨1, by omega, _, _, literal_hist1 m, by simp, fun q' h1 h2 => by omega⟩

/-- **The literal RGA violates (1c).** The execution (all at replica `0`)
`ins(x, 0); ins(y, 1); del(x); ins(b, 1)` of the protocol of Section 4.2 as literally written is
well formed, satisfies causal broadcast and the user assumptions, but no visibility relation puts
it in `A_weak`: the response of `ins(b, 1)` is `[b, y]`, while (1c) requires `b` at position
`min(1, 2 - 1) = 1`. -/
theorem literal_not_weak : (literalProtocol ℕ (m + 1)).WF (literalExec m) ∧ CausalBroadcast (literalExec m) ∧
    UserOK (literalProtocol ℕ (m + 1)) (literalExec m) ∧
    ∀ vis, ¬ Weak ((literalProtocol ℕ (m + 1)).hist (literalExec m)) vis := by
  refine ⟨literalExec_wf m, literalExec_causal m, literalExec_userOK m, ?_⟩
  rintro vis ⟨lo, -, hc, -⟩
  have := (hc 3 0 _ _ (literal_hist3 m)).2.2 2 1 rfl
  simp at this

/-- Hence the literal protocol satisfies neither the weak nor the strong list specification
(Definition 6), for any number `m + 1` of replicas. -/
theorem literal_not_satisfies :
    ¬ Satisfies (literalProtocol ℕ (m + 1)) Weak
        (fun α => CausalBroadcast α ∧ UserOK (literalProtocol ℕ (m + 1)) α) ∧
      ¬ Satisfies (literalProtocol ℕ (m + 1)) Strong
        (fun α => CausalBroadcast α ∧ UserOK (literalProtocol ℕ (m + 1)) α) := by
  obtain ⟨hwf, hC, hU, hW⟩ := literal_not_weak m
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨vis, -, hw⟩ := h (literalExec m) hwf ⟨hC, hU⟩
    exact hW vis hw
  · obtain ⟨vis, -, hs⟩ := h (literalExec m) hwf ⟨hC, hU⟩
    exact hW vis hs.weak

end RGA

end Podc.CollaborativeListSpec
