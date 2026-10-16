import Papers.PODC2011.CoordinatedConsensusDynamic.Model

/-!
# Lemma 6.4: walks in the similarity graph block `Δ`-coordinated decisions

If some node decides `v` at time `t` in `G`, and `(G, T)` is joined to an execution `G'` in which
all inputs are `¬v` by a walk of length `ℓ` in the similarity graph at time `T ≥ t + ℓΔ`, then
some node of `G'` decides `v` by time `t + ℓΔ`, violating validity. With `Δ = 0`
(simultaneous consensus) the length of the walk is irrelevant, which is the classical
common-knowledge argument (Section 6.1).
-/

namespace CoordCons

open DGraph

variable {S : DGraph Bool → Prop} {D : Decision Bool} {Δ : ℕ}

/-- Decisions propagate along walks, losing `Δ` rounds per step. -/
theorem decided_along_walk (hD : Consensus S D) (hC : Coordinated S Δ D) {T ℓ t : ℕ}
    {G H : DGraph Bool} (hw : Walk S T ℓ G H) (hT : t + ℓ * Δ ≤ T) {u : ℕ} (hu : u ∈ G.V)
    {v : Bool} (hdec : D G u t = some v) : ∃ w ∈ H.V, D H w (t + ℓ * Δ) = some v := by
  induction hw with
  | nil => exact ⟨u, hu, by simpa using hdec⟩
  | @snoc ℓ G' H' K hw' hs ih =>
    obtain ⟨w, hw, hdw⟩ := ih (by nlinarith) hu hdec
    obtain ⟨hH', hK, u', hind⟩ := hs
    have hu' := hind.mem_left
    have hsome := hC H' hH' w hw (t + ℓ * Δ) (by simp [hdw]) u' hu'
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
    have hbv : b = v := hD.agreement H' hH' u' hu' w hw _ _ b v hb hdw
    subst hbv
    refine ⟨u', hind.mem_right, ?_⟩
    have e : t + (ℓ + 1) * Δ = t + ℓ * Δ + Δ := by ring
    rw [e, ← hD.loc _ _ _ _ (hind.mono (by nlinarith)), hb]

/-- **Lemma 6.4** (simplified form, as used for Theorems 6.7 and 6.8): if `(G, T)` is joined by
walks of lengths `ℓ₀, ℓ₁` to executions where all inputs are `0`, resp. `1`, and
`t + ℓᵢΔ ≤ T`, then no node has decided by time `t` in `G`. -/
theorem lemma_6_4 (hD : Consensus S D) (hC : Coordinated S Δ D) {T t ℓ₀ ℓ₁ : ℕ}
    {G G₀ G₁ : DGraph Bool} (hS : S G) (h₀ : Walk S T ℓ₀ G G₀) (h₁ : Walk S T ℓ₁ G G₁)
    (hT₀ : t + ℓ₀ * Δ ≤ T) (hT₁ : t + ℓ₁ * Δ ≤ T)
    (hG₀ : ∀ w ∈ G₀.V, G₀.input w = false) (hG₁ : ∀ w ∈ G₁.V, G₁.input w = true) :
    ∀ u ∈ G.V, D G u t = none := by
  intro u hu
  -- the end of a walk is admissible
  have hend : ∀ {ℓ} {K : DGraph Bool}, Walk S T ℓ G K → S K := by
    intro ℓ K hw
    cases hw with
    | nil => exact hS
    | snoc _ hs => exact hs.2.1
  cases hdec : D G u t with
  | none => rfl
  | some v =>
    exfalso
    cases v with
    | true =>
      obtain ⟨w, hw, hd⟩ := decided_along_walk hD hC h₀ hT₀ hu hdec
      obtain ⟨x, hx, hxi⟩ := hD.validity _ (hend h₀) w hw _ _ hd
      simp [hG₀ x hx] at hxi
    | false =>
      obtain ⟨w, hw, hd⟩ := decided_along_walk hD hC h₁ hT₁ hu hdec
      obtain ⟨x, hx, hxi⟩ := hD.validity _ (hend h₁) w hw _ _ hd
      simp [hG₁ x hx] at hxi

/-- The common-knowledge argument for simultaneous (`0`-coordinated) consensus: if `(G, t)` is in
the same similarity component as an all-`0` and an all-`1` execution, no node decides at time
`t` in `G`. -/
theorem no_simultaneous_decision (hD : Consensus S D) (hC : Coordinated S 0 D) {t : ℕ}
    {G G₀ G₁ : DGraph Bool} (hS : S G) (h₀ : Sim S t G G₀) (h₁ : Sim S t G G₁)
    (hG₀ : ∀ w ∈ G₀.V, G₀.input w = false) (hG₁ : ∀ w ∈ G₁.V, G₁.input w = true) :
    ∀ u ∈ G.V, D G u t = none := by
  obtain ⟨ℓ₀, h₀⟩ := h₀.exists_walk
  obtain ⟨ℓ₁, h₁⟩ := h₁.exists_walk
  exact lemma_6_4 hD hC hS h₀ h₁ (by simp) (by simp) hG₀ hG₁

/-- The walks of Lemma 6.4 as stated in the paper: the `i`-th step of the walk is an
indistinguishability at time `t + iΔ`. -/
inductive StagWalk (S : DGraph Bool → Prop) (t Δ : ℕ) : ℕ → DGraph Bool → DGraph Bool → Prop
  | nil (G : DGraph Bool) : StagWalk S t Δ 0 G G
  | snoc {ℓ : ℕ} {G H K : DGraph Bool} {u : ℕ} : StagWalk S t Δ ℓ G H → S H → S K →
      Indist H K u (t + (ℓ + 1) * Δ) → StagWalk S t Δ (ℓ + 1) G K

theorem decided_along_stagWalk (hD : Consensus S D) (hC : Coordinated S Δ D) {t ℓ : ℕ}
    {G H : DGraph Bool} (hw : StagWalk S t Δ ℓ G H) {u : ℕ} (hu : u ∈ G.V) {v : Bool}
    (hdec : D G u t = some v) : ∃ w ∈ H.V, D H w (t + ℓ * Δ) = some v := by
  induction hw with
  | nil => exact ⟨u, hu, by simpa using hdec⟩
  | @snoc ℓ G' H' K u' hw' hH' hK hind ih =>
    obtain ⟨w, hw, hdw⟩ := ih hu hdec
    have hu' := hind.mem_left
    have hsome := hC H' hH' w hw (t + ℓ * Δ) (by simp [hdw]) u' hu'
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hsome
    have hbv : b = v := hD.agreement H' hH' u' hu' w hw _ _ b v hb hdw
    subst hbv
    refine ⟨u', hind.mem_right, ?_⟩
    have e : t + (ℓ + 1) * Δ = t + ℓ * Δ + Δ := by ring
    rw [← hD.loc _ _ _ _ hind, e, hb]

/-- **Lemma 6.4** (general form, as stated in the paper): if there are walks
`(G, t+Δ) ∼_{u₁} (H₁, t+Δ), (H₁, t+2Δ) ∼_{u₂} (H₂, t+2Δ), …, (H_{ℓ-1}, t+ℓΔ) ∼_{u_ℓ} (G₀, t+ℓΔ)` and
likewise to `G₁` (all inputs `0`, resp. `1`), then no node decides by time `t` in `G`. -/
theorem lemma_6_4_general (hD : Consensus S D) (hC : Coordinated S Δ D) {t ℓ₀ ℓ₁ : ℕ}
    {G G₀ G₁ : DGraph Bool} (hS : S G) (h₀ : StagWalk S t Δ ℓ₀ G G₀)
    (h₁ : StagWalk S t Δ ℓ₁ G G₁)
    (hG₀ : ∀ w ∈ G₀.V, G₀.input w = false) (hG₁ : ∀ w ∈ G₁.V, G₁.input w = true) :
    ∀ u ∈ G.V, D G u t = none := by
  intro u hu
  have hend : ∀ {ℓ} {K : DGraph Bool}, StagWalk S t Δ ℓ G K → S K := by
    intro ℓ K hw
    cases hw with
    | nil => exact hS
    | snoc _ _ hK _ => exact hK
  cases hdec : D G u t with
  | none => rfl
  | some v =>
    exfalso
    cases v with
    | true =>
      obtain ⟨w, hw, hd⟩ := decided_along_stagWalk hD hC h₀ hu hdec
      obtain ⟨x, hx, hxi⟩ := hD.validity _ (hend h₀) w hw _ _ hd
      simp [hG₀ x hx] at hxi
    | false =>
      obtain ⟨w, hw, hd⟩ := decided_along_stagWalk hD hC h₁ hu hdec
      obtain ⟨x, hx, hxi⟩ := hD.validity _ (hend h₁) w hw _ _ hd
      simp [hG₁ x hx] at hxi

end CoordCons
