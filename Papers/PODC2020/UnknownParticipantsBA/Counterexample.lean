import Papers.PODC2020.UnknownParticipantsBA.Rotor

/-!
# Lemma 4 and Theorem 1 of the BA are false (`n = 7`, `f = 2`)

Correct nodes `2, 3, 4, 5, 6`, Byzantine nodes `0, 1` (`n = 7 > 3f = 6`). The Byzantine nodes
make themselves known to everybody in round 1 (so `n_v = 7` at every correct node from round 2
on; the thresholds are `n_v/3 ↦ 3` and `2n_v/3 ↦ 5` copies) and play:

* round 1: `1` sends `init` to `2, 3, 4`; `0` sends `init` to `3, 4`;
* round 2: `0, 1` send `echo(1)` to `2`; `1` sends `echo(0)` to `3, 4, 5`;
* round 3: `0, 1` send `echo(0)` to `2`.

Iteration `r = 0`: node `2` gets `5` copies of `echo(1)` (from `2, 3, 4, 0, 1`) and adds `1` to
`C_2 = {1,2,3,4,5,6}`, so it selects `C_2[0] = 1`; the others get only `3` copies and keep
`C = {2,…,6}`, so they select `C[0] = 2`. Everybody echoes `1`; nodes `3, 4, 5` echo `0`.
Node `2` does not broadcast an opinion (it selected `1`, not itself).

Iteration `r = 1`: the others add `1` (5 echoes) and select `C[1] = 2` again; node `2` gets `5`
copies of `echo(0)` (from `3, 4, 5, 0, 1`), adds `0`, and selects `C_2[1] = 1` again: inserting a
*smaller* identifier shifted the indices. All correct nodes have reselected their coordinator
and `break`. No good round ever happened, and no correct node ever accepted any opinion.

The flaw in the proof of Lemma 4: the final step ("a node that was already selected is in
`{C_v[r mod |C_v|] : r < r_c}`, so reselection needs `r > |C_v|`") treats `C_v` as fixed, but
`C_v` grows and new identifiers can be inserted *before* the current index.
-/

namespace UnknownBA.Cex

/-- Byzantine messages: `adv s q v` is sent by `q` to `v` in round `s + 1`. -/
def adv : ℕ → ℕ → ℕ → Finset (Msg ℕ ℕ)
  | 0, 1, v => if v ∈ ({2, 3, 4} : Finset ℕ) then {.init} else {.app 7}
  | 0, 0, v => if v ∈ ({3, 4} : Finset ℕ) then {.init} else {.app 7}
  | 1, 0, v => if v = 2 then {.echo 1} else ∅
  | 1, 1, v => if v = 2 then {.echo 1} else if v ∈ ({3, 4, 5} : Finset ℕ) then {.echo 0} else ∅
  | 2, _, v => if v = 2 then {.echo 0} else ∅
  | _, _, _ => ∅

/-- The environment: ids `2,…,6` correct, `0, 1` Byzantine, the input (opinion) of `v` is `v`. -/
def env : Env ℕ ℕ (Msg ℕ ℕ) where
  G := {2, 3, 4, 5, 6}
  F := {0, 1}
  disj := by decide
  input v := v
  adv := adv

/-- The resilience hypothesis `n > 3f` holds. -/
theorem resilience : 3 * env.F.card < env.G.card + env.F.card := by decide

/-- Every correct node terminates in iteration `1`. -/
theorem halts : ∀ v ∈ env.G, HaltsAt paperRule env v 1 := by
  unfold HaltsAt; decide +kernel

/-- The selections: node `2` selects `1, 1`, the others `2, 2`. -/
theorem selections :
    Selects paperRule env 2 0 1 ∧ Selects paperRule env 2 1 1 ∧
      ∀ v ∈ ({3, 4, 5, 6} : Finset ℕ), Selects paperRule env v 0 2 ∧ Selects paperRule env v 1 2 := by
  unfold Selects; decide +kernel

lemma halted_late (v : ℕ) (hv : v ∈ env.G) (r : ℕ) :
    (run (rotor paperRule) env (r + 3) v).ext.halted = true := by
  have h3 : (run (rotor paperRule) env 3 v).ext.halted = true := (halts v hv).2
  have := run_add_of_halted (rotorExt paperRule) env h3 r
  rw [Nat.add_comm r 3, rotor] at *
  rw [this]; exact h3

/-- No iteration is a good round. -/
theorem no_good (r : ℕ) : ¬ GoodIter paperRule env r := by
  rintro ⟨p, hp, h⟩
  obtain ⟨h1, h2⟩ := h 2 (by decide)
  match r, h1, h2 with
  | 0, _, h2 =>
    have : (run (rotor paperRule) env 2 2).ext.sel = {1} := by decide +kernel
    rw [this, Finset.singleton_inj] at h2; subst h2; exact absurd hp (by decide)
  | 1, _, h2 =>
    have : (run (rotor paperRule) env 3 2).ext.sel = {1} := by decide +kernel
    rw [this, Finset.singleton_inj] at h2; subst h2; exact absurd hp (by decide)
  | r + 2, h1, _ =>
    have := halted_late 2 (by decide) r
    rw [show r + 2 + 1 = r + 3 by omega, this] at h1; exact absurd h1 (by decide)

/-- No correct node ever accepts any opinion. -/
theorem no_accept (v : ℕ) (hv : v ∈ env.G) (r : ℕ) (x : ℕ) : ¬ Accepts paperRule env v r x := by
  rintro ⟨h1, h2⟩
  match r, h1, h2 with
  | 0, _, h2 =>
    have : ∀ v ∈ env.G, (run (rotor paperRule) env 2 v).ext.acc = ∅ := by decide +kernel
    rw [this v hv] at h2; simp at h2
  | 1, _, h2 =>
    have : ∀ v ∈ env.G, (run (rotor paperRule) env 3 v).ext.acc = ∅ := by decide +kernel
    rw [this v hv] at h2; simp at h2
  | r + 2, h1, _ =>
    have := halted_late v hv r
    rw [show r + 2 + 1 = r + 3 by omega, this] at h1; exact absurd h1 (by decide)

/-- **Lemma 4 of the BA (Lemma 7 of the full version) is false**: a correct node terminates
without having witnessed a good round (here: every correct node, in iteration 1). -/
theorem lemma4_false :
    ∃ v ∈ env.G, ∃ rt, HaltsAt paperRule env v rt ∧ ∀ r ≤ rt, ¬ GoodIter paperRule env r :=
  ⟨2, by decide, 1, halts 2 (by decide), fun r _ => no_good r⟩

/-- The claim of Theorem 1 of the BA (Theorem 2 of the full version): with `n > 3f`, there is a
round in which every correct node accepts the opinion of a common correct coordinator. -/
def Theorem1Claim (rule : Rule ℕ) : Prop :=
  ∀ E : Env ℕ ℕ (Msg ℕ ℕ), 3 * E.F.card < E.G.card + E.F.card →
    ∃ r, ∃ p ∈ E.G, ∀ v ∈ E.G, Accepts rule E v r (E.input p)

/-- **Theorem 1 of the BA is false** for Algorithm 1 as stated. -/
theorem theorem1_false : ¬ Theorem1Claim paperRule := by
  intro h
  obtain ⟨r, p, hp, hacc⟩ := h env resilience
  exact no_accept p hp r p (hacc p hp)

end UnknownBA.Cex

/-!
## The minimal case `n = 4`, `f = 1`: Theorem 1 still fails

Correct nodes `1, 2, 3`, Byzantine node `0`, which sends `init` to `1, 2` (and a junk message to
`3`) in round 1 and `echo(0)` to `1` in round 2. In iteration 0 node `1` adds `0` and selects it,
nodes `2, 3` select `1`. In iteration 1 everybody has `C = {0,1,2,3}` and selects `C[1] = 1`
(a good round in the sense of the paper), but nodes `2, 3` reselect `1` and `break` before they
could accept `1`'s opinion in the next iteration; node `1` did not broadcast an opinion in
iteration 0. So nodes `2, 3` never accept any opinion. (For `f = 1` Lemma 4 itself holds; a
bounded search over all abstract schedules with `f ≤ 2` finds `n = 7`, `f = 2` as the smallest
violation of Lemma 4.)
-/

namespace UnknownBA.Cex4

def adv : ℕ → ℕ → ℕ → Finset (Msg ℕ ℕ)
  | 0, 0, v => if v ∈ ({1, 2} : Finset ℕ) then {.init} else {.app 7}
  | 1, 0, v => if v = 1 then {.echo 0} else ∅
  | _, _, _ => ∅

def env : Env ℕ ℕ (Msg ℕ ℕ) where
  G := {1, 2, 3}
  F := {0}
  disj := by decide
  input v := v
  adv := adv

theorem resilience : 3 * env.F.card < env.G.card + env.F.card := by decide

/-- Iteration 1 is a good round (everybody selects the correct node `1`) ... -/
theorem good_one : GoodIter paperRule env 1 :=
  ⟨1, by decide, by unfold Selects; decide +kernel⟩

/-- ... but nodes `2` and `3` terminate in it. -/
theorem halts : ∀ v ∈ ({2, 3} : Finset ℕ), HaltsAt paperRule env v 1 := by
  unfold HaltsAt; decide +kernel

theorem no_accept (v : ℕ) (hv : v ∈ ({2, 3} : Finset ℕ)) (r x : ℕ) :
    ¬ Accepts paperRule env v r x := by
  rintro ⟨h1, h2⟩
  have h3 : (run (rotor paperRule) env 3 v).ext.halted = true := (halts v hv).2
  match r, h1, h2 with
  | 0, _, h2 =>
    have : ∀ v ∈ ({2, 3} : Finset ℕ), (run (rotor paperRule) env 2 v).ext.acc = ∅ := by
      decide +kernel
    rw [this v hv] at h2; simp at h2
  | 1, _, h2 =>
    have : ∀ v ∈ ({2, 3} : Finset ℕ), (run (rotor paperRule) env 3 v).ext.acc = ∅ := by
      decide +kernel
    rw [this v hv] at h2; simp at h2
  | r + 2, h1, _ =>
    have := run_add_of_halted (rotorExt paperRule) env h3 r
    rw [Nat.add_comm 3 r] at this
    rw [show r + 2 + 1 = r + 3 by omega, rotor, this] at h1
    have h1' : (run (rotor paperRule) env 3 v).ext.halted = false := h1
    rw [h1'] at h3; exact absurd h3 (by decide)

/-- Theorem 1 of the BA fails already for `n = 4`, `f = 1`. -/
theorem theorem1_false : ¬ Cex.Theorem1Claim paperRule := by
  intro h
  obtain ⟨r, p, hp, hacc⟩ := h env resilience
  exact no_accept 2 (by decide) r p (hacc 2 (by decide))

end UnknownBA.Cex4
