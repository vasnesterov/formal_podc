import Papers.PODC2015.MinimalSynchronyBC.Basic

/-!
# Eventual agreement: Figure 3, first part, and Lemma 1 (EA-Validity)

One round `r` of Figure 3, abstracted to what EA-Validity depends on. A correct process `i`
with input `x i`:
1. `aux_i ← CB[r].CB_broadcast EA_PROP1(x i)` (any CB-broadcast implementation, `CBSpec`);
2. broadcasts `EA_PROP2[r](aux_i)` (plain broadcast over authenticated channels: a message
   received from a correct `j` carries `aux_j`; `rcv i τ j` is the first one received by time `τ`);
3. waits until `EA_PROP2[r]` messages were received from a set `Q` of `n − t` processes with
   values in `CB[r].cb_valid_i` (`w3`);
4. returns `v` if all of them carry `v` (`line4`); otherwise lines 5–10 return some value
   (unconstrained here).

The second part (lines 5–19: timers, coordinator, relays) is formalized operationally in
`Machine.lean`; Lemma 2 and the proof of Lemma 3 fail there (`Counterexample.lean`).
-/

namespace MinimalSynchronyBC

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- An execution of one round of Figure 3 (lines 1–4). -/
structure Fig3 (P V : Type*) where
  /-- `CB[r]`. -/
  cb : CBObs P V
  /-- `rcv i τ j`: the first `EA_PROP2[r]` message received by `i` from `j` by time `τ`. -/
  rcv : P → ℕ → P → Option V
  /-- Completion of line 3: time and the `n − t` senders. -/
  w3 : P → Option (ℕ × Finset P)
  /-- Return value of `EA_propose(r, -)`. -/
  ret : P → Option V

/-- The rules of lines 1–4 of Figure 3 for correct processes. -/
structure Fig3.Follows (t : ℕ) (B : Finset P) (x : P → Option V) (E : Fig3 P V) : Prop where
  /-- Line 1 uses a CB-broadcast instance with inputs `x`. -/
  cb : CBSpec t B x E.cb
  /-- Line 2: a message received from a correct process carries its `aux`. -/
  rcv_correct : ∀ {i j τ a}, i ∉ B → j ∉ B → E.rcv i τ j = some a →
    (E.cb.ret j).map Prod.snd = some a
  /-- Line 3. -/
  w3 : ∀ {i τ Q}, i ∉ B → E.w3 i = some (τ, Q) →
    Q.card = Fintype.card P - t ∧ ∀ j ∈ Q, ∃ a, E.rcv i τ j = some a ∧ a ∈ E.cb.valid i τ
  /-- Line 4. -/
  line4 : ∀ {i τ Q v}, i ∉ B → E.w3 i = some (τ, Q) → (∀ j ∈ Q, E.rcv i τ j = some v) →
    E.ret i = some v
  /-- A process returns only after line 3. -/
  ret_w3 : ∀ {i v}, i ∉ B → E.ret i = some v → (E.w3 i).isSome

/-- **Lemma 1 (EA-Validity).** If every correct process that invokes `EA_propose(r, -)`
proposes `v`, no correct process returns a value different from `v`. -/
theorem lemma1 {t : ℕ} {B : Finset P} {x : P → Option V} {E : Fig3 P V}
    (hE : E.Follows t B x) : EAValidity B x E.ret := by
  intro v hv i hi w hw
  obtain ⟨⟨τ, Q⟩, hQ⟩ := Option.isSome_iff_exists.1 (hE.ret_w3 hi hw)
  obtain ⟨hcard, hQv⟩ := hE.w3 hi hQ
  -- every value in `cb_valid_i` is `v`
  have hval : ∀ a ∈ E.cb.valid i τ, a = v := fun a ha => by
    obtain ⟨j, hj, hxj⟩ := hE.cb.set_validity hi ha
    rcases hv j hj with h | h
    · rw [h] at hxj; exact absurd hxj (by simp)
    · rw [h] at hxj; exact (Option.some_injective _ hxj).symm
  have hall : ∀ j ∈ Q, E.rcv i τ j = some v := fun j hj => by
    obtain ⟨a, ha, hav⟩ := hQv j hj
    rw [ha, hval a hav]
  have := hE.line4 hi hQ hall
  rw [hw] at this
  exact Option.some_injective _ this

/-- In particular, if all correct processes propose `v` and line 3 completes at a correct
process, it returns `v` at line 4 (it never reaches line 5). -/
theorem lemma1_line4 {t : ℕ} {B : Finset P} {x : P → Option V} {E : Fig3 P V}
    (hE : E.Follows t B x) {v : V} (hv : ∀ j ∉ B, x j = none ∨ x j = some v) {i : P}
    (hi : i ∉ B) (h3 : (E.w3 i).isSome) : E.ret i = some v := by
  obtain ⟨⟨τ, Q⟩, hQ⟩ := Option.isSome_iff_exists.1 h3
  obtain ⟨_, hQv⟩ := hE.w3 hi hQ
  refine hE.line4 hi hQ fun j hj => ?_
  obtain ⟨a, ha, hav⟩ := hQv j hj
  obtain ⟨k, hk, hxk⟩ := hE.cb.set_validity hi hav
  rcases hv k hk with h | h
  · rw [h] at hxk; exact absurd hxk (by simp)
  · rw [h] at hxk; rw [ha, Option.some_injective _ hxk]

end MinimalSynchronyBC
