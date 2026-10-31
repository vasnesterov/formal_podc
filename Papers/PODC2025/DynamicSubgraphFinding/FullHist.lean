import Papers.PODC2025.DynamicSubgraphFinding.Model

/-!
# Full-history algorithms

A convenient way to define concrete algorithms (Theorems 1.4 and 1.7): the state of a node is its
whole local history — its identifier, `G⁰`, the number `r` of completed rounds, its local inputs
`locH k` (rounds `0..r`) and the messages `inbH k` received in rounds `1..r`. An algorithm is then
given by a message function `snd r h x w` (round, history, current local input, recipient) and an
output function of the history. `histAlg_state` identifies the state with the actual history of
the node in the network, so reasoning about such algorithms is reasoning about the network.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

variable {V M O : Type}

-- CSLib candidate (together with `Model.lean`).
/-- The local history of a node. -/
structure Hist (V M : Type) where
  id : V
  g0p : V → Prop
  g0a : V → V → Prop
  r : ℕ
  locH : ℕ → Option (Set V)
  inbH : ℕ → V → Option M

/-- The algorithm with full-history states, messages `snd` and outputs `out`. -/
noncomputable def histAlg (snd : ℕ → Hist V M → Option (Set V) → V → M) (out : Hist V M → O) :
    Algorithm V M O where
  State := Hist V M
  init P0 G0 v := ⟨v, P0, G0, 0,
    fun k => if k = 0 then (if P0 v then some {u | G0 u v} else none) else none, fun _ _ => none⟩
  send r h x w := snd r h x w
  recv r h x inb := ⟨h.id, h.g0p, h.g0a, r, Function.update h.locH r x, Function.update h.inbH r inb⟩
  out := out

variable (snd : ℕ → Hist V M → Option (Set V) → V → M) (out : Hist V M → O) (D : InsNet V)

/-- The state of a full-history algorithm is the true local history. -/
theorem histAlg_state (r : ℕ) (v : V) :
    (histAlg snd out).state D r v =
      ⟨v, D.pres 0, D.adj 0, r, fun k => if k ≤ r then D.loc k v else none,
        fun k => if 1 ≤ k ∧ k ≤ r then
          (histAlg snd out).inbox D ((histAlg snd out).state D (k - 1)) k v else fun _ => none⟩ := by
  induction r with
  | zero =>
    simp only [Algorithm.state, histAlg, InsNet.loc, Nat.le_zero, Hist.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · funext k; split_ifs <;> simp_all
    · funext k; split_ifs with h <;> simp_all; omega
  | succ r ih =>
    rw [Algorithm.state_succ]
    simp only [histAlg] at ih ⊢
    rw [ih]
    simp only [Hist.mk.injEq, true_and]
    refine ⟨?_, ?_⟩
    · funext k
      by_cases hk : k = r + 1
      · subst hk; simp
      · rw [Function.update_of_ne hk]
        split_ifs <;> first | rfl | omega
    · funext k
      by_cases hk : k = r + 1
      · subst hk; simp
      · rw [Function.update_of_ne hk]
        split_ifs <;> first | rfl | omega

lemma histAlg_id (r : ℕ) (v : V) : ((histAlg snd out).state D r v).id = v := by
  rw [histAlg_state]

lemma histAlg_r (r : ℕ) (v : V) : ((histAlg snd out).state D r v).r = r := by
  rw [histAlg_state]

lemma histAlg_locH {r k : ℕ} (hk : k ≤ r) (v : V) :
    ((histAlg snd out).state D r v).locH k = D.loc k v := by
  rw [histAlg_state]; simp [hk]

lemma histAlg_inbH {r k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ r) (v : V) :
    ((histAlg snd out).state D r v).inbH k =
      (histAlg snd out).inbox D ((histAlg snd out).state D (k - 1)) k v := by
  rw [histAlg_state]; simp [hk1, hk]

/-- Messages received in round `k` by `v`, unfolded. -/
lemma histAlg_inbox (k : ℕ) (v u : V) :
    (histAlg snd out).inbox D ((histAlg snd out).state D k) (k + 1) v u =
      if D.adj (k + 1) u v then some (snd (k + 1) ((histAlg snd out).state D k u) (D.loc (k + 1) u) v)
      else none := rfl

end Podc.DynamicSubgraphFinding
