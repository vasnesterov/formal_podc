import Papers.PODC2013.CubicBitsBA.Correctness

/-!
# Agreement fails: `n = 7`, `t = 2` (refutes Lemma 5 and Theorem 2)

Processes `0, …, 4` are correct, `b₁ = 5` and `b₂ = 6` are Byzantine (`n = 7 > 3t = 6`). Values are
`Bool`; the construction is parametrized by `f : Bool` (all values are xor-ed with `f`) so that it
works for both choices of the default value `v0 = !f`. With `f = false`:

* inputs: `0, 1, 2 ↦ false`, `3, 4 ↦ true`;
* round 1: `b₁` sends `false` to the group `A = {0, 1, 2}` and `true` to `3, 4`; `b₂` sends `true`
  to everybody;
* round 2: both Byzantine processes echo the round-1 values "as the receiver saw them": to `i` they
  report `b₁`'s value as the one `i` received (`false` in `A`, `true` outside), and the correct
  inputs truthfully. So `b₂` tells `A` that `b₁` proposed `false` and tells `3, 4` that `b₁`
  proposed `true`;
* round 3: both Byzantine processes report no suspicion and echo the round-2 arrays as the
  receiver saw them.

`b₂`'s round-2 equivocation can only be detected at the end of round 3 = `t + 1`, so it is never
reported; `b₂` is in the top set of the node `b₁` everywhere. At the node `b₁` the correct
children's echoes are `false, false, false, true, true`, and `b₂`'s echo tips the strict majority
to `false` in `A` but leaves a tie (→ `⊥`) at `3, 4`. At the root, `A` sees four `false` among
seven children and decides `false`; `3, 4` see only three and fall back to `v0 = true`.

Everything is checked by kernel evaluation (`decide +kernel`, no `native_decide`).
-/

namespace Podc.CubicBitsBA.Counterexample

open Podc.CubicBitsBA

/-- Inputs (xor `f`): `0, 1, 2 ↦ false`, `3, 4 ↦ true`, and `true` for the Byzantine ids. -/
def inp (f : Bool) (j : Fin 7) : Bool := xor (decide (3 ≤ j.val)) f

/-- The group `A = {0, 1, 2}`. -/
def grpA (i : Fin 7) : Bool := decide (i.val < 3)

/-- Round 1 messages to `i`: correct senders send their input, `b₁ = 5` sends `false` to `A` and
`true` otherwise, `b₂ = 6` sends `true` (all xor `f`). -/
def V1 (f : Bool) (i : Fin 7) : View 7 Bool := fun r j =>
  if r = 1 then
    (if j.val < 5 then some { v1 := some (inp f j) }
     else if j = 5 then some { v1 := some (xor (!grpA i) f) } else some { v1 := some (inp f j) })
  else none

/-- Round 2 message of a correct process. -/
def msg2 (f : Bool) (j : Fin 7) : Msg 7 Bool := out 2 (inp f j) (V1 f j) 2

/-- Round 2: the Byzantine processes report `b₁`'s value as `i` received it. -/
def V2 (f : Bool) (i : Fin 7) : View 7 Bool := fun r j =>
  if r = 2 then
    (if j.val < 5 then some (msg2 f j)
     else some { e2 := fun k => if k = 5 then some (xor (!grpA i) f) else some (inp f k) })
  else V1 f i r j

/-- Round 3 message of a correct process. -/
def msg3 (f : Bool) (j : Fin 7) : Msg 7 Bool := out 2 (inp f j) (V2 f j) 3

/-- Round 3: the Byzantine processes suspect nobody and echo the round-2 arrays as `i` saw them. -/
def V3 (f : Bool) (i : Fin 7) : View 7 Bool := fun r j =>
  if r = 3 then
    (if j.val < 5 then some (msg3 f j)
     else some { e3 := fun k => (V2 f i 2 k).map (·.e2) })
  else V2 f i r j

lemma correct_iff (j : Fin 7) : j ∉ ({5, 6} : Finset (Fin 7)) ↔ j.val < 5 := by
  revert j; decide

/-- The execution (`t = 2`, Byzantine set `{5, 6}`). -/
def exec (f : Bool) : Exec 7 2 Bool where
  byz := {5, 6}
  input := inp f
  view := V3 f
  honest := by
    intro j hj i r h1 h3
    rw [correct_iff] at hj
    interval_cases r
    · simp [V3, V2, V1, hj, out]
    · have h : V3 f i 2 j = some (msg2 f j) := by simp [V3, V2, hj]
      rw [h, msg2, out_congr]
      intro r' _ hr'
      funext k
      simp [V3, V2, show r' ≠ 3 by omega, show r' ≠ 2 by omega]
    · have h : V3 f i 3 j = some (msg3 f j) := by simp [V3, hj]
      rw [h, msg3, out_congr]
      intro r' _ hr'
      funext k
      simp [V3, show r' ≠ 3 by omega]

/-- The decisions of the correct processes: `A = {0, 1, 2}` decides `false`, `3, 4` decide the
default `true` (all xor `f`; the default value is `!f`). -/
theorem decide_exec (f : Bool) (i : Fin 7) (hi : i.val < 5) :
    (exec f).decide (!f) i = xor (!grpA i) f := by
  revert f i
  decide +kernel

/-- The level-1 node of `b₁ = 5` is not common: `newval(b₁)` is `false` in `A` and `⊥` at `3`. -/
theorem newval1_b1 (f : Bool) :
    newval1 2 ((exec f).view 0) 5 = some f ∧ newval1 2 ((exec f).view 3) 5 = none := by
  revert f
  decide +kernel

lemma card_byz (f : Bool) : (exec f).byz.card = 2 := rfl

lemma correct_0 (f : Bool) : (0 : Fin 7) ∉ (exec f).byz := by simp [exec]
lemma correct_3 (f : Bool) : (3 : Fin 7) ∉ (exec f).byz := by simp [exec]

/-- Agreement fails for every default value `v0`: in `exec (!v0)` (`n = 7`, `t = 2`, two Byzantine
processes) the correct processes `0` and `3` decide differently. -/
theorem agreement_fails (v0 : Bool) :
    ∃ E : Exec 7 2 Bool, E.byz.card = 2 ∧ ∃ i ∉ E.byz, ∃ i' ∉ E.byz,
      E.decide v0 i ≠ E.decide v0 i' := by
  refine ⟨exec (!v0), card_byz _, 0, correct_0 _, 3, correct_3 _, ?_⟩
  have h0 := decide_exec (!v0) 0 (by decide)
  have h3 := decide_exec (!v0) 3 (by decide)
  rw [Bool.not_not] at h0 h3
  rw [h0, h3]
  cases v0 <;> decide

/-- **Theorem 2** (agreement) of [Kowalski–Mostéfaoui] is false: the protocol of Section 4 does not
guarantee agreement for `t < n/3` (counterexample `n = 7`, `t = 2`, binary values, either default
value). -/
theorem theorem_2_false :
    ¬ ∀ (n t : ℕ) (v0 : Bool) (E : Exec n t Bool), 3 * t < n → E.byz.card ≤ t →
      ∀ i ∉ E.byz, ∀ i' ∉ E.byz, E.decide v0 i = E.decide v0 i' := by
  intro h
  obtain ⟨E, hE, i, hi, i', hi', hne⟩ := agreement_fails true
  exact hne (h 7 2 true E (by norm_num) hE.le i hi i' hi')

/-- **Lemma 5** of [Kowalski–Mostéfaoui] for an execution `E`: if the subtree rooted at `z` has a
common path covering, then `z` or one of its ancestors (`z.drop k`, `1 ≤ k ≤ |z|`) is common. -/
def Lemma5 {n t : ℕ} {V : Type} [DecidableEq V] (E : Exec n t V) (v0 : V) : Prop :=
  ∀ z : List (Fin n), z.Nodup → z.length ≤ t + 1 →
    (∃ C : Set (List (Fin n)), PathCoveringAt t C z ∧ ∀ x ∈ C, Common E v0 x) →
    Common E v0 z ∨ ∃ k, 1 ≤ k ∧ k ≤ z.length ∧ Common E v0 (z.drop k)

/-- **Lemma 5** of [Kowalski–Mostéfaoui] is false (for either default value): the whole tree has a
common path covering (`lemma_4`), but the root is not common. -/
theorem lemma_5_false (v0 : Bool) : ∃ E : Exec 7 2 Bool, E.byz.card = 2 ∧ ¬ Lemma5 E v0 := by
  obtain ⟨E, hE, i, hi, i', hi', hne⟩ := agreement_fails v0
  refine ⟨E, hE, fun h => ?_⟩
  rcases h [] List.nodup_nil (by simp) (lemma_4 E (by norm_num) hE.le v0) with hc | ⟨k, hk, hk', _⟩
  · exact hne ((hc i hi i' hi').1 rfl)
  · simp at hk'; omega

/-- The step of the paper's proof of Lemma 5 that fails: the level-1 node `b₁ = 5`, whose children
are all common (`newvalB` of `[k, 5]` agrees at all correct processes), is not common. -/
theorem node_b1_not_common (f : Bool) : ¬ Common (exec f) (!f) [5] := by
  intro h
  have := ((h 0 (correct_0 f) 3 (correct_3 f)).2.1 5 rfl)
  rw [(newval1_b1 f).1, (newval1_b1 f).2] at this
  exact Option.some_ne_none _ this

theorem children_b1_common (f : Bool) (k : Fin 7) (hk : k ≠ 5) :
    ∀ i ∉ (exec f).byz, ∀ i' ∉ (exec f).byz,
      newvalB 2 ((exec f).view i) [k, 5] = newvalB 2 ((exec f).view i') [k, 5] := by
  revert f k
  decide +kernel

end Podc.CubicBitsBA.Counterexample
