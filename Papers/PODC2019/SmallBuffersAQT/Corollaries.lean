import Papers.PODC2019.SmallBuffersAQT.Counterexample

/-!
# Non-vacuity of `Run`, and Propositions 3.1 and 3.2 (PTS, PPTS) as the case `ℓ = 1`

For `ℓ = 1` and `m = n` every packet is at level 0 with intermediate destination equal to its
destination, `ActivatePreBad` never runs, and `FormPaths` is exactly Algorithm 2 (PPTS) on the
whole path: node `v` forwards from the pseudo-buffer of the largest destination `> v` among the
bad pseudo-buffers at nodes `≤ v`. With a single destination this is Algorithm 1 (PTS). Packets
are accepted in the round of their injection (batches = rounds, `b = A`).
-/

namespace Podc.SmallBuffersAQT

open Finset Cslib.AQT

variable {m ℓ : ℕ}

/-- The execution with the canonical choice of packets. -/
def canonCfg (m ℓ : ℕ) (sched : ℕ → ℕ → ℕ) (b : ℕ → ℕ → ℕ → ℕ) : ℕ → Config
  | 0 => addBatch m ℓ b 0 (fun _ _ => 0)
  | r + 1 =>
    if (r + 1) % ℓ = 0 then
      addBatch m ℓ b ((r + 1) / ℓ)
        (hptsStep m ℓ (sched ℓ (r % ℓ)) (canonCfg m ℓ sched b r) (canonSel m ℓ (canonCfg m ℓ sched b r)))
    else hptsStep m ℓ (sched ℓ (r % ℓ)) (canonCfg m ℓ sched b r) (canonSel m ℓ (canonCfg m ℓ sched b r))

/-- Non-vacuity: HPTS has an execution against every batched adversary, for every schedule. -/
def canonRun (m ℓ : ℕ) (sched : ℕ → ℕ → ℕ) (b : ℕ → ℕ → ℕ → ℕ) : Run m ℓ sched b where
  cfg := canonCfg m ℓ sched b
  sel r := canonSel m ℓ (canonCfg m ℓ sched b r)
  valid _ := canonSel_valid m ℓ _
  init := rfl
  step _ := rfl

theorem run_nonempty (sched : ℕ → ℕ → ℕ) (b : ℕ → ℕ → ℕ → ℕ) : Nonempty (Run m ℓ sched b) :=
  ⟨canonRun m ℓ sched b⟩

/-- Packets keep their destinations: if the adversary only uses destinations in `D`, so does
every configuration. -/
lemma Run.dest_mem {sched : ℕ → ℕ → ℕ} {b : ℕ → ℕ → ℕ → ℕ} (R : Run m ℓ sched b) {D : Finset ℕ}
    (hD : ∀ t a w, b t a w ≠ 0 → w ∈ D) : ∀ r i w, R.cfg r i w ≠ 0 → w ∈ D := by
  have hadd : ∀ φ (c : Config), (∀ i w, c i w ≠ 0 → w ∈ D) →
      ∀ i w, addBatch m ℓ b φ c i w ≠ 0 → w ∈ D := by
    intro φ c hc i w h
    unfold addBatch at h
    by_cases h' : c i w = 0
    · rw [h', zero_add] at h
      split_ifs at h
      · exact hD _ _ _ h
      · exact absurd rfl h
    · exact hc i w h'
  have hstep : ∀ r, (∀ i w, R.cfg r i w ≠ 0 → w ∈ D) → ∀ lam i w,
      hptsStep m ℓ lam (R.cfg r) (R.sel r) i w ≠ 0 → w ∈ D := by
    intro r hc lam i w h
    unfold hptsStep fwd at h
    by_cases h' : R.cfg r i w = 0
    · rw [h'] at h
      split_ifs at h with h1 h2 h2
      · obtain ⟨-, hF, -⟩ := arrival_spec h2
        have := (F_valid (R.valid r) hF).1
        exact hc (i - 1) w (by omega)
      · simp at h
      · obtain ⟨-, hF, -⟩ := arrival_spec h2
        have := (F_valid (R.valid r) hF).1
        exact hc (i - 1) w (by omega)
      · simp at h
    · exact hc i w h'
  intro r
  induction r with
  | zero => rw [R.init]; exact hadd 0 _ (fun _ _ h => absurd rfl h)
  | succ r ih =>
    rw [R.step r]
    split_ifs
    · exact hadd _ _ (hstep r ih _)
    · exact hstep r ih _

/-- **Proposition 3.2** of [MPR19] (PPTS): on the path with `n` nodes, against a
`(ρ, σ)`-bounded adversary with `ρ ≤ 1` whose packets have destinations in `W`, every buffer
holds at most `|W| + σ + 1` packets. (PPTS is HPTS with `ℓ = 1`, `m = n`.) -/
theorem prop_3_2 {n : ℕ} {A : ℕ → ℕ → ℕ → ℕ} {ρ σ : ℝ} (hA : IsBounded A (n ^ 1) ρ σ)
    (hρ : ρ ≤ 1) {W : Finset ℕ} (hW : ∀ t a w, A t a w ≠ 0 → w ∈ W)
    (R : Run n 1 fixedSched A) (r : ℕ) {i : ℕ} (hi : i < n ^ 1) :
    (occ n 1 (R.cfg r) i : ℝ) ≤ W.card + σ + 1 := by
  have h := R.occ_le_keys rfl le_rfl hA hρ r hi
  have hk : ((keysAt n 1 (R.cfg r) i).card : ℝ) ≤ W.card := by
    exact_mod_cast card_keysAt_le_dest (R.cfg r) i W (fun w hw => R.dest_mem hW r i w hw)
  linarith

/-- **Proposition 3.1** of [MPR19] (PTS): with a single destination `w`, every buffer holds at
most `2 + σ` packets. -/
theorem prop_3_1 {n : ℕ} {A : ℕ → ℕ → ℕ → ℕ} {ρ σ : ℝ} (hA : IsBounded A (n ^ 1) ρ σ)
    (hρ : ρ ≤ 1) {w : ℕ} (hw : ∀ t a w', A t a w' ≠ 0 → w' = w)
    (R : Run n 1 fixedSched A) (r : ℕ) {i : ℕ} (hi : i < n ^ 1) :
    (occ n 1 (R.cfg r) i : ℝ) ≤ 2 + σ := by
  have := prop_3_2 hA hρ (W := {w}) (fun t a w' h => by rw [hw t a w' h]; simp) R r hi
  simp at this
  linarith

/-- For `ℓ = 1` the level of every packet is `0` and its intermediate destination is its
destination, so HPTS is PPTS. -/
lemma key_one {n i w : ℕ} (hiw : i < w) (hw : w < n ^ 1) : key n 1 i w = (0, w) := by
  have h := (lv_spec hiw hw).1
  have h0 : lv n 1 i w = 0 := by omega
  simp [key, xd, h0]

end Podc.SmallBuffersAQT
