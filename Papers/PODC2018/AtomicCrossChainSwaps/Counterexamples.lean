import Papers.PODC2018.AtomicCrossChainSwaps.Liveness

/-!
# Counterexamples for the protocol of §4.5 read literally

1. `literal_not_live`: on the paper's own three-party example (3-cycle `A → B → C → A`, leader
   `A`), with the paper's hashkey timeouts `(diam(D) + |p|)Δ` (`B = diam D = 3`, or `B = 2` under
   the reading "longest path between distinct vertices"), the all-conforming execution triggers
   no arc at all: Alice can present her own hashkey `(s, (A), sig)` only at `4Δ`, after it expired
   at `3Δ`. (Lemma 4.6 / Theorem 4.7 / the first clause of uniformity fail.)
2. `literal_unsafe_refwd` (an *ambiguity*, not an error of the paper: it relies on a leader forwarding
   foreign keys while still in Phase One, which the proof of Theorem 4.9 rules out): even with the timeouts enlarged by one `Δ` (`B = diam + 1 = 4`), on the
   two-leader digraph of Figure 7 (complete digraph on `A, B, C`, leaders `A, B`), a single
   deviating leader `A` (no front-running) makes the conforming leader `B` end Underwater: `A`
   unlocks its hashlock on `B → A` before publishing its contract `A → B`, so `B` forwards `A`'s
   key "the first time" while `(A, B)` has no contract yet, and never again.
3. `literal_unsafe_late`: with `B = diam + 1 = 4` on the three-party example, a coalition
   `{B, C}` publishes `C → A` at the last moment; Alice (conforming) releases her secret too late,
   her own call fails, but it is public, and `B` uses it with a longer (later-expiring) hashkey
   path `(B, C, A)` to collect Alice's asset (no front-running needed).

The repaired protocol (`fixed = true`) is safe in all these situations by `Setting.safety`.
-/

namespace AtomicSwap

namespace Setting

variable {V : Type*} [DecidableEq V] [Fintype V] {P : Setting V} {C : Finset V}
  {sch : ℕ → Moves V}

/-- To check that a finite schedule is admissible it suffices to check rounds `< H`, provided the
adversary is idle afterwards and every conforming party has noticed every unlock by time `H`. -/
theorem validSched_of {H : ℕ} (hH : P.B + Fintype.card V ≤ H)
    (hlt : ∀ t < H, P.Valid C t (P.run C sch t) (sch t))
    (hemp : ∀ t, H ≤ t → (sch t).pubs = [] ∧ (sch t).calls = [])
    (hfin : ∀ v ℓ, v ∉ C → ℓ ∈ P.L → ℓ ≠ v → (P.run C sch H).first v ℓ = none →
      ∀ w, P.D.Adj v w → (P.run C sch H).unl v w ℓ = none) : P.ValidSched C sch := by
  intro t
  rcases Nat.lt_or_ge t H with ht | ht
  · exact hlt t ht
  refine ⟨by simp [(hemp t ht).1], by simp [(hemp t ht).2], ?_⟩
  intro v ℓ hv hℓ hℓv h0 ⟨w, hw, hu⟩
  exfalso
  have h0H : (P.run C sch H).first v ℓ = none := by
    cases h : (P.run C sch H).first v ℓ with
    | none => rfl
    | some p => rw [P.first_mono C sch ht h] at h0; cases h0
  have := hfin v ℓ hv hℓ hℓv h0H w hw
  rw [P.unl_stable C sch (by omega), ← P.unl_stable C sch hH] at hu
  simp [this] at hu

end Setting

/-! ### The three-party example of §1 -/

/-- The 3-cycle `0 → 1 → 2 → 0` (Alice `0` pays Bob `1`, Bob pays Carol `2`, Carol pays Alice). -/
def cyc3 : Digraph (Fin 3) where
  Adj a b := b = a + 1

instance : DecidableRel cyc3.Adj := fun a b => by unfold cyc3; infer_instance

lemma cyc3_isPath_length {p : List (Fin 3)} (hp : IsPath cyc3 p) : p.length ≤ 4 := by
  have := hp.length_le; simpa using this

/-- `diam` of the 3-cycle is `3` (the cycle `(A, B, C, A)`), as in the paper's example. -/
theorem diam_cyc3 : diam cyc3 = 3 :=
  diam_eq (p := [0, 1, 2, 0]) (by decide) rfl (fun _ hp => cyc3_isPath_length hp)

/-- The paper's protocol on the 3-cycle with leader `A = 0` and base timeout `B`. -/
def lit3 (B : ℕ) : Setting (Fin 3) := ⟨cyc3, {0}, B, false, false⟩

/-- Nobody deviates; each party takes its first key from its unique leaving arc. -/
def idle3 : ℕ → Moves (Fin 3) := fun _ => ⟨[], [], fun v _ => v + 1⟩

lemma idle3_valid (B : ℕ) : (lit3 B).ValidSched ∅ idle3 := by
  intro t
  refine ⟨by simp [idle3], by simp [idle3], ?_⟩
  intro v ℓ _ hℓ _ _ ⟨w, hw, hu⟩
  have hw' : w = v + 1 := hw
  subst hw'
  exact ⟨rfl, hu⟩

/-- **Counterexample to Lemma 4.6 / Theorem 4.7 (literal timeouts).** In the paper's three-party
swap with hashkey timeouts `(diam(D) + |p|)Δ` (`B = diam D = 3`, or `B = 2` if `diam` is read as
the longest path between distinct vertices), if all parties conform no arc is ever triggered
(everybody ends NoDeal instead of Deal). -/
theorem literal_not_live :
    diam cyc3 = 3 ∧ ∀ B ∈ ({2, 3} : Finset ℕ), (lit3 B).ValidSched ∅ idle3 ∧
      ∀ u v, ¬ (lit3 B).Final ∅ idle3 u v := by
  refine ⟨diam_cyc3, fun B hB => ⟨idle3_valid B, fun u v => ?_⟩⟩
  rw [Setting.final_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl <;> revert u v <;> decide +kernel

/-- With one more `Δ` (`B = diam D + 1 = 4`), the literal protocol does complete the example. -/
theorem literal_live_four : ∀ u v, cyc3.Adj u v → (lit3 4).Final ∅ idle3 u v := by
  intro u v h
  rw [Setting.final_iff]
  revert u v; decide +kernel

/-! ### Figure 7: two leaders on the complete digraph on three vertices -/

/-- The complete digraph on `{A, B, C} = {0, 1, 2}` (the two-leader digraph of Figures 7–8). -/
def k3 : Digraph (Fin 3) where
  Adj a b := a ≠ b

instance : DecidableRel k3.Adj := fun a b => by unfold k3; infer_instance

theorem diam_k3 : diam k3 = 3 :=
  diam_eq (p := [0, 1, 2, 0]) (by decide) rfl (fun _ hp => by have := hp.length_le; simpa using this)

/-- The paper's protocol on `k3` with leaders `A = 0`, `B = 1`, base timeout `diam + 1 = 4`. -/
def litK3 : Setting (Fin 3) := ⟨k3, {0, 1}, 4, false, false⟩

/-- Alice (`0`) deviates: she publishes `A → C` at once, unlocks her hashlock on `B → A` with her
bare secret in round 1, publishes `A → B` only in round 2 (after Bob has already forwarded her
key, to the entering arcs that existed then), and finally uses Bob's released secret. -/
def advK3 : ℕ → Moves (Fin 3)
  | 0 => ⟨[(0, 2)], [], fun _ ℓ => ℓ⟩
  | 1 => ⟨[], [(1, 0, 0, [0])], fun _ ℓ => ℓ⟩
  | 2 => ⟨[(0, 1)], [(2, 0, 0, [0])], fun _ ℓ => ℓ⟩
  | 4 => ⟨[], [(1, 0, 1, [0, 1]), (2, 0, 1, [0, 1])], fun _ ℓ => ℓ⟩
  | _ => ⟨[], [], fun _ ℓ => ℓ⟩

theorem advK3_valid : litK3.ValidSched {0} advK3 := by
  refine Setting.validSched_of (H := 7) (by decide) ?_ ?_ ?_
  · decide +kernel
  · intro t ht
    match t, ht with
    | t + 7, _ => simp [advK3]
  · decide +kernel

/-- **Counterexample to Theorem 4.9 (literal protocol, even with timeouts `(diam + 1 + |p|)Δ`).**
On the two-leader digraph of Figure 7, the deviation of the single party `A` leaves the conforming
leader `B` Underwater: `B → A` and `B → C` are triggered, `A → B` is not (its hashlock `h_A` is
never unlocked: `B` forwarded `A`'s key only once, before `A → B` existed). No front-running. -/
theorem literal_unsafe_refwd :
    diam k3 = 3 ∧ litK3.B = diam k3 + 1 ∧ litK3.ValidSched {0} advK3 ∧ (1 : Fin 3) ∉ ({0} : Finset (Fin 3)) ∧
      Underwater k3 {1} (litK3.Final {0} advK3) := by
  refine ⟨diam_k3, by rw [diam_k3]; rfl, advK3_valid, by decide, ?_, ?_⟩
  · refine ⟨0, 1, ⟨by decide, by simp, rfl⟩, ?_⟩
    rw [Setting.final_iff]; decide +kernel
  · refine ⟨1, 0, ⟨by decide, rfl, by simp⟩, ?_⟩
    rw [Setting.final_iff]; decide +kernel

/-! ### Late release on the three-party example -/

/-- Bob (`1`) and Carol (`2`) collude: Bob publishes `B → C` at once, Carol publishes `C → A` only
in round 3 (landing at time 4 = Alice's own deadline `B + 0`); Alice releases in round 4, her calls
fail but reveal her signed secret; Bob then presents the key `(B, C, A)` (deadline `4 + 2 = 6`) on
`A → B`. -/
def advLate : ℕ → Moves (Fin 3)
  | 0 => ⟨[(1, 2)], [], fun v _ => v + 1⟩
  | 3 => ⟨[(2, 0)], [], fun v _ => v + 1⟩
  | 5 => ⟨[], [(0, 1, 0, [1, 2, 0])], fun v _ => v + 1⟩
  | _ => ⟨[], [], fun v _ => v + 1⟩

theorem advLate_valid : (lit3 4).ValidSched {1, 2} advLate := by
  refine Setting.validSched_of (H := 7) (by decide) ?_ ?_ ?_
  · decide +kernel
  · intro t ht
    match t, ht with
    | t + 7, _ => simp [advLate]
  · decide +kernel

/-- **Counterexample to Theorem 4.9 (literal protocol, late release).** In the paper's three-party
swap with timeouts `(diam + 1 + |p|)Δ`, the coalition `{B, C}` leaves the conforming leader Alice
Underwater: her contract `A → B` is triggered, `C → A` is not. -/
theorem literal_unsafe_late :
    (lit3 4).B = diam cyc3 + 1 ∧ (lit3 4).ValidSched {1, 2} advLate ∧
      Underwater cyc3 {0} ((lit3 4).Final {1, 2} advLate) := by
  refine ⟨by rw [diam_cyc3]; rfl, advLate_valid, ?_, ?_⟩
  · refine ⟨2, 0, ⟨rfl, by simp, rfl⟩, ?_⟩
    rw [Setting.final_iff]; decide +kernel
  · refine ⟨0, 1, ⟨rfl, rfl, by simp⟩, ?_⟩
    rw [Setting.final_iff]; decide +kernel

end AtomicSwap
