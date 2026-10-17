import Papers.PODC2011.KCoreDecomposition.Trajectory

/-!
# Algorithm 1 (one host, one node): local state and message handler

Each node `u` keeps
* `core` — its current estimate of its own coreness (initially `d(u)`),
* `est v` — the most recent estimate of neighbour `v` it knows (initially `+∞ = ⊤`),
* `changed` — whether `core` changed since the last broadcast.

`receive G u s ⟨v, k⟩` is the handler `on receive ⟨v, k⟩` of Algorithm 1:
```
if k < est[v] then
  est[v] ← k
  t ← computeIndex(est, u, core)
  if t < core then core ← t; changed ← true
```
`foldl_receive` describes the effect of processing any list of messages in any order.
-/

open Finset

set_option linter.unusedSectionVars false

namespace KCoreDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Local state of a node in Algorithm 1. -/
structure NodeState (V : Type*) where
  /-- local estimate of the node's own coreness -/
  core : ℕ
  /-- `est v`: latest known estimate of the coreness of neighbour `v` (`⊤` = `+∞`) -/
  est : V → ℕ∞
  /-- `core` was modified since the last broadcast -/
  changed : Bool

/-- `on initialization`: `core ← d(u)`, `est[v] ← +∞` (the initial broadcast is part of the run). -/
def initState (u : V) : NodeState V := ⟨G.degree u, fun _ => ⊤, false⟩

/-- The handler `on receive ⟨v, k⟩` of Algorithm 1, executed by node `u`. -/
noncomputable def receive (u : V) (s : NodeState V) (m : V × ℕ) : NodeState V :=
  if (m.2 : ℕ∞) < s.est m.1 then
    if computeIndex G (Function.update s.est m.1 (m.2 : ℕ∞)) u s.core < s.core then
      ⟨computeIndex G (Function.update s.est m.1 (m.2 : ℕ∞)) u s.core,
        Function.update s.est m.1 (m.2 : ℕ∞), true⟩
    else ⟨s.core, Function.update s.est m.1 (m.2 : ℕ∞), s.changed⟩
  else s

variable {G}

theorem receive_est_le (u : V) (s : NodeState V) (m : V × ℕ) (v : V) :
    (receive G u s m).est v ≤ s.est v := by
  unfold receive
  split_ifs with h1 h2
  · simp only [Function.update_apply]; split_ifs with h; · subst h; exact h1.le
    exact le_rfl
  · simp only [Function.update_apply]; split_ifs with h; · subst h; exact h1.le
    exact le_rfl
  · exact le_rfl

theorem receive_core_le (u : V) (s : NodeState V) (m : V × ℕ) :
    (receive G u s m).core ≤ s.core := by
  unfold receive; split_ifs with h1 h2
  · exact h2.le
  · exact le_rfl
  · exact le_rfl

/-- `receive` either leaves the state untouched, or sets `core` to `computeIndex` of the new
estimates with the old `core` as cap. -/
theorem receive_cases (u : V) (s : NodeState V) (m : V × ℕ) :
    receive G u s m = s ∨
      (receive G u s m).core = computeIndex G (receive G u s m).est u s.core := by
  unfold receive
  split_ifs with h1 h2
  · exact Or.inr rfl
  · refine Or.inr ?_
    simp only
    exact le_antisymm (not_lt.1 h2) (computeIndex_le _ _ _)
  · exact Or.inl rfl

theorem receive_changed (u : V) (s : NodeState V) (m : V × ℕ) :
    (receive G u s m).changed = true ↔ s.changed = true ∨ (receive G u s m).core < s.core := by
  unfold receive
  split_ifs with h1 h2 <;> simp_all

/-- The effect of processing a list of messages, in any order: `core` is either unchanged together
with `est`, or it is `computeIndex` of the final estimates capped by the initial `core`. -/
theorem foldl_receive (u : V) (l : List (V × ℕ)) (s : NodeState V) :
    (∀ v, (l.foldl (receive G u) s).est v ≤ s.est v) ∧
    (l.foldl (receive G u) s).core ≤ s.core ∧
    (l.foldl (receive G u) s = s ∨
      (l.foldl (receive G u) s).core =
        computeIndex G (l.foldl (receive G u) s).est u s.core) ∧
    ((l.foldl (receive G u) s).changed = true ↔
      s.changed = true ∨ (l.foldl (receive G u) s).core < s.core) := by
  induction l generalizing s with
  | nil => simp
  | cons m l ih =>
    simp only [List.foldl_cons]
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih (receive G u s m)
    have hc1 := receive_core_le (G := G) u s m
    refine ⟨fun v => (ih1 v).trans (receive_est_le (G := G) u s m v), ih2.trans hc1, ?_, ?_⟩
    · rcases receive_cases (G := G) u s m with h | h
      · rw [show receive G u s m = s from h] at ih3 ⊢; exact ih3
      · refine Or.inr ?_
        rcases ih3 with h' | h'
        · rw [h']; exact h
        · rw [h', h, computeIndex_comp (fun v _ => ih1 v)]
    · rw [ih4, receive_changed]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · by_cases h' : (receive G u s m).core < s.core
          · exact Or.inl (Or.inr h')
          · exact Or.inr (by omega)

/-- The estimate entry for `v` after processing a list of messages, when all messages from `v`
carry the value `val v`. -/
theorem foldl_receive_est (u : V) (l : List (V × ℕ)) (val : V → ℕ)
    (hl : ∀ m ∈ l, m.2 = val m.1) (s : NodeState V) (v : V) :
    (l.foldl (receive G u) s).est v =
      if ∃ m ∈ l, m.1 = v then min (s.est v) (val v : ℕ∞) else s.est v := by
  induction l generalizing s with
  | nil => simp
  | cons m l ih =>
    simp only [List.foldl_cons]
    rw [ih (fun m hm => hl m (List.mem_cons_of_mem _ hm))]
    have hm := hl m List.mem_cons_self
    have hest : (receive G u s m).est v =
        if m.1 = v then min (s.est v) (val v : ℕ∞) else s.est v := by
      unfold receive
      split_ifs with h1 h2 h3 h3 h3 <;>
        simp_all [eq_comm (a := v), le_of_lt]
    rw [hest]
    by_cases hmv : m.1 = v
    · simp only [hmv, ite_true, List.mem_cons, exists_eq_or_imp, true_or, min_assoc,
        min_self]
      split_ifs <;> rfl
    · simp only [hmv, ite_false, List.mem_cons, exists_eq_or_imp, false_or]

end KCoreDecomposition
