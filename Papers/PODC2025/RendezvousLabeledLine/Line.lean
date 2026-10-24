import Papers.PODC2025.RendezvousLabeledLine.Model

/-!
# Agents on the infinite labelled line

**The line.** Nodes are the integers `ℤ`; a labelling is an injective `ℓ : ℤ → ℕ`
(the paper uses labels in `ℕ*`; `0` is harmless here).

**Agents (frame model).** An agent does not know the orientation of the line nor its position.
Port numbers are adversarial, but an agent always knows through which port it entered the current
node, hence it can keep walking in the same direction or turn back; it can therefore maintain its
position relative to its start node in *its own frame*, in which "port 0 at the start node" is the
positive direction. We model a deterministic algorithm by its trajectory in its own frame:
`pos μ t : ℤ` is the agent's position after `t` rounds of its own clock when the labels seen in its
frame are `μ` (`μ i` = label of the node at frame position `i`). The algorithm must be
*causal*: the move in round `t + 1` depends only on the labels of the nodes visited up to round
`t`. Both agents run the same algorithm; agent `α` starts at `v` with frame orientation `ε = ±1`,
so its global position is `v + ε * pos (ℓ ∘ (v + ε * ·)) t` (`Algo.traj`).

Proposition 3.2 (two ways to force a meeting on the line) and the line form of Theorem 3.1
(`thm_3_1`) are proved here.
-/

namespace Podc.RendezvousLabeledLine

open Function

/-! ### Proposition 3.2 -/

/-- Meeting (at a node, or by crossing an edge in opposite directions) in some round of
`[T, T']`; a crossing in round `t` uses rounds `t - 1, t`, both inside the window. -/
def MeetOrCrossIn (x y : ℕ → ℤ) (T T' : ℕ) : Prop :=
  ∃ t, T ≤ t ∧ t ≤ T' ∧ (x t = y t ∨ (T < t ∧ x t = y (t - 1) ∧ y t = x (t - 1)))

/-- A trajectory on the line moves by at most one edge per round. -/
def Lip (x : ℕ → ℤ) : Prop := ∀ t, |x (t + 1) - x t| ≤ 1

lemma MeetOrCrossIn.symm {x y : ℕ → ℤ} {T T' : ℕ} (h : MeetOrCrossIn x y T T') :
    MeetOrCrossIn y x T T' := by
  obtain ⟨t, h1, h2, h | ⟨h3, h4, h5⟩⟩ := h
  · exact ⟨t, h1, h2, Or.inl h.symm⟩
  · exact ⟨t, h1, h2, Or.inr ⟨h3, h5, h4⟩⟩

lemma MeetOrCrossIn.mono {x y : ℕ → ℤ} {T T' S S' : ℕ} (h : MeetOrCrossIn x y T T')
    (hS : S ≤ T) (hS' : T' ≤ S') : MeetOrCrossIn x y S S' := by
  obtain ⟨t, h1, h2, h | ⟨h3, h4, h5⟩⟩ := h
  · exact ⟨t, by omega, by omega, Or.inl h⟩
  · exact ⟨t, by omega, by omega, Or.inr ⟨by omega, h4, h5⟩⟩

lemma MeetOrCrossIn.meetOrCross {x y : ℕ → ℤ} {T T' : ℕ} (h : MeetOrCrossIn x y T T') :
    ∃ t ≤ T', MeetOrCross x y t := by
  obtain ⟨t, h1, h2, h | ⟨h3, h4, h5⟩⟩ := h
  · exact ⟨t, h2, Or.inl h⟩
  · exact ⟨t, h2, Or.inr ⟨by omega, h4, h5⟩⟩

/-- Discrete intermediate value theorem for two walkers on the line: if `x ≤ y` in round `t₁` and
`x ≥ y` in round `t₂ ≥ t₁`, they meet or cross in between. -/
lemma meetOrCrossIn_of_le_of_ge {x y : ℕ → ℤ} (hx : Lip x) (hy : Lip y) {t₁ t₂ : ℕ}
    (h12 : t₁ ≤ t₂) (h1 : x t₁ ≤ y t₁) (h2 : y t₂ ≤ x t₂) : MeetOrCrossIn x y t₁ t₂ := by
  obtain ⟨n, rfl⟩ : ∃ n, t₂ = t₁ + n := ⟨t₂ - t₁, by omega⟩
  induction n generalizing t₁ with
  | zero => exact ⟨t₁, le_rfl, by omega, Or.inl (by simp at h2; omega)⟩
  | succ n ih =>
    by_cases he : x t₁ = y t₁
    · exact ⟨t₁, le_rfl, by omega, Or.inl he⟩
    by_cases h' : x (t₁ + 1) ≤ y (t₁ + 1)
    · exact (ih (t₁ := t₁ + 1) (h12 := by omega) (h1 := h')
        (h2 := by rwa [show t₁ + 1 + n = t₁ + (n + 1) by ring])).mono (by omega) (by omega)
    · have a1 := abs_le.1 (hx t₁)
      have a2 := abs_le.1 (hy t₁)
      exact ⟨t₁ + 1, by omega, by omega, Or.inr ⟨by omega, by simp; omega, by simp; omega⟩⟩

/-- Same as `meetOrCrossIn_of_le_of_ge`, in either temporal order. -/
lemma meetOrCrossIn_of_le_of_ge' {x y : ℕ → ℤ} (hx : Lip x) (hy : Lip y) {t₁ t₂ T T' : ℕ}
    (h1 : x t₁ ≤ y t₁) (h2 : y t₂ ≤ x t₂) (hT1 : T ≤ t₁) (hT2 : T ≤ t₂) (hT1' : t₁ ≤ T')
    (hT2' : t₂ ≤ T') : MeetOrCrossIn x y T T' := by
  rcases le_total t₁ t₂ with h | h
  · exact (meetOrCrossIn_of_le_of_ge hx hy h h1 h2).mono hT1 hT2'
  · exact ((meetOrCrossIn_of_le_of_ge hy hx h h2 h1).mono hT2 hT1').symm

/-- **Proposition 3.2 (1)** (agents swap positions). -/
theorem prop_3_2_swap {x y : ℕ → ℤ} (hx : Lip x) (hy : Lip y) {a b c d : ℤ} {T T' : ℕ}
    (hTT : T ≤ T') (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) (hxT : x T = a) (hxT' : x T' = c)
    (hyT : y T = d) (hyT' : y T' = b) : MeetOrCrossIn x y T T' :=
  meetOrCrossIn_of_le_of_ge hx hy hTT (by omega) (by omega)

/-- **Proposition 3.2 (2)** (an agent scans an interval that the other agent stays in). Only the
two endpoints of the scanned interval matter (`prop_3_2_scan'`). -/
theorem prop_3_2_scan {x y : ℕ → ℤ} (hx : Lip x) (hy : Lip y) {a b c d : ℤ} {T T' : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hscan : ∀ z, a ≤ z → z ≤ d → ∃ t, T ≤ t ∧ t ≤ T' ∧ x t = z)
    (hstay : ∀ t, T ≤ t → t ≤ T' → b ≤ y t ∧ y t ≤ c) : MeetOrCrossIn x y T T' := by
  obtain ⟨t₁, h1, h1', hx1⟩ := hscan a le_rfl (by omega)
  obtain ⟨t₂, h2, h2', hx2⟩ := hscan d (by omega) le_rfl
  have := hstay t₁ h1 h1'
  have := hstay t₂ h2 h2'
  exact meetOrCrossIn_of_le_of_ge' hx hy (t₁ := t₁) (t₂ := t₂) (by omega) (by omega) h1 h2 h1' h2'

/-- Endpoint form of Proposition 3.2 (2): `x` visits `a` and `d` in the window, and `y` stays in
`[a, d]` there. -/
theorem prop_3_2_scan' {x y : ℕ → ℤ} (hx : Lip x) (hy : Lip y) {a d : ℤ} {T T' t₁ t₂ : ℕ}
    (h1 : T ≤ t₁) (h1' : t₁ ≤ T') (h2 : T ≤ t₂) (h2' : t₂ ≤ T') (hx1 : x t₁ = a) (hx2 : x t₂ = d)
    (hstay : ∀ t, T ≤ t → t ≤ T' → a ≤ y t ∧ y t ≤ d) : MeetOrCrossIn x y T T' := by
  have := hstay t₁ h1 h1'
  have := hstay t₂ h2 h2'
  exact meetOrCrossIn_of_le_of_ge' hx hy (t₁ := t₁) (t₂ := t₂) (by omega) (by omega) h1 h2 h1' h2'

/-! ### Agents in their own frame -/

/-- The node at position `i` of the frame of an agent started at `v` with orientation `ε`. -/
def frame (v : ℤ) (ε : ℤˣ) (i : ℤ) : ℤ := v + ε * i

lemma frame_injective (v : ℤ) (ε : ℤˣ) : Injective (frame v ε) := by
  intro i j h; simp only [frame, add_right_inj] at h; exact (Units.mul_right_inj ε).1 h

lemma abs_frame_sub (v : ℤ) (ε : ℤˣ) (i : ℤ) : |frame v ε i - v| = |i| := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [frame]

lemma abs_frame_sub_frame (v : ℤ) (ε : ℤˣ) (i j : ℤ) : |frame v ε i - frame v ε j| = |i - j| := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [frame]
  rw [← abs_neg]; congr 1; ring

/-- A deterministic agent algorithm, as a trajectory in the agent's own frame depending on the
labels `μ` seen in that frame. -/
structure Algo where
  /-- frame position after `t` rounds of the agent's clock -/
  pos : (ℤ → ℕ) → ℕ → ℤ
  pos_zero : ∀ μ, pos μ 0 = 0
  step : ∀ μ, Injective μ → ∀ t, |pos μ (t + 1) - pos μ t| ≤ 1
  /-- the next move depends only on the labels of the nodes visited so far -/
  causal : ∀ μ μ', Injective μ → Injective μ' → ∀ t,
    (∀ s ≤ t, μ' (pos μ s) = μ (pos μ s)) → pos μ' (t + 1) = pos μ (t + 1)

namespace Algo

variable (A : Algo)

/-- Global trajectory of an agent started at node `v` with frame orientation `ε` on the line
labelled by `ℓ`. -/
def traj (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) (t : ℕ) : ℤ := frame v ε (A.pos (ℓ ∘ frame v ε) t)

lemma traj_zero (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) : A.traj ℓ v ε 0 = v := by
  simp [traj, frame, A.pos_zero]

lemma lip_pos {μ : ℤ → ℕ} (hμ : Injective μ) : Lip (A.pos μ) := A.step μ hμ

lemma lip_traj {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (v : ℤ) (ε : ℤˣ) : Lip (A.traj ℓ v ε) := by
  intro t; simp only [traj]; rw [abs_frame_sub_frame]
  exact A.step _ (hℓ.comp (frame_injective v ε)) t

lemma lip_delayed {x : ℕ → ℤ} (hx : Lip x) (τ : ℕ) : Lip (delayed τ x) := by
  intro t; simp only [delayed]
  by_cases h : τ ≤ t
  · rw [show t + 1 - τ = (t - τ) + 1 by omega]; exact hx _
  · rw [show t + 1 - τ = 0 by omega, show t - τ = 0 by omega]; simp

/-- Causality, iterated: agreement on the nodes visited up to round `m` gives the same trajectory
up to round `m + 1`. -/
lemma pos_eq_of_agree {μ μ' : ℤ → ℕ} (hμ : Injective μ) (hμ' : Injective μ') {m : ℕ}
    (h : ∀ s ≤ m, μ' (A.pos μ s) = μ (A.pos μ s)) : ∀ s ≤ m + 1, A.pos μ' s = A.pos μ s := by
  intro s hs
  rcases s with _ | s
  · simp [A.pos_zero]
  · exact A.causal μ μ' hμ hμ' s (fun s' hs' => h s' (by omega))

/-! ### The `care` transformation on the line (Theorem 3.1) -/

/-- `care(A)`: every edge crossing of `A` is replaced by a CarefulWalk, every stay by 4 stays. -/
def care : Algo where
  pos μ := careTraj μ (A.pos μ)
  pos_zero μ := by simp [careTraj, A.pos_zero]
  step μ hμ t := by
    have hs := fun k => abs_le.1 (A.step μ hμ k)
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 4 ∧ t = 4 * k + j := ⟨t / 4, t % 4, by omega, by omega⟩
    have := hs k
    obtain ⟨a0, a1, a2, a3, a4, -⟩ := careTraj_block μ (A.pos μ) k
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [show 4 * k + 0 + 1 = 4 * k + 1 by ring, a1, Nat.add_zero, a0]; simp
    · rw [show 4 * k + 1 + 1 = 4 * k + 2 by ring, a2, a1]; exact abs_le.2 ⟨by omega, by omega⟩
    · rw [show 4 * k + 2 + 1 = 4 * k + 3 by ring, a3, a2]
      split_ifs <;> simp; exact abs_le.2 ⟨by omega, by omega⟩
    · rw [show 4 * k + 3 + 1 = 4 * k + 4 by ring, a4, a3]
      split_ifs <;> simp; exact abs_le.2 ⟨by omega, by omega⟩
  causal μ μ' hμ hμ' t h := by
    have a0 := fun k => (careTraj_block μ (A.pos μ) k).1
    have a1 := fun k => (careTraj_block μ (A.pos μ) k).2.1
    have a2 := fun k => (careTraj_block μ (A.pos μ) k).2.2.1
    have a3 := fun k => (careTraj_block μ (A.pos μ) k).2.2.2.1
    -- visited positions of `A` before round `t` of `care A`
    have hvis : ∀ s, 4 * s ≤ t → μ' (A.pos μ s) = μ (A.pos μ s) := fun s hs => by
      have := h (4 * s) hs; rwa [show careTraj μ (A.pos μ) (4 * s) = A.pos μ s from a0 s] at this
    obtain ⟨k, j, hj, ht⟩ : ∃ k j, j < 4 ∧ t + 1 = 4 * k + j := ⟨(t + 1) / 4, (t + 1) % 4,
      by omega, by omega⟩
    show careTraj μ' (A.pos μ') (t + 1) = careTraj μ (A.pos μ) (t + 1)
    obtain ⟨b0, b1, b2, b3, -, -⟩ := careTraj_block μ' (A.pos μ') k
    rw [ht]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_zero, (careTraj_block μ' (A.pos μ') (k + 1)).1, a0]
      exact A.pos_eq_of_agree hμ hμ' (m := k) (fun s hs => hvis s (by omega)) _ le_rfl
    · rw [b1, a1]
      exact A.pos_eq_of_agree hμ hμ' (m := k) (fun s hs => hvis s (by omega)) _ (by omega)
    · rw [b2, a2]
      exact A.pos_eq_of_agree hμ hμ' (m := k) (fun s hs => hvis s (by omega)) _ le_rfl
    · have e := A.pos_eq_of_agree hμ hμ' (m := k) (fun s hs => hvis s (by omega))
      have hq : μ' (A.pos μ (k + 1)) = μ (A.pos μ (k + 1)) := by
        have := h (4 * k + 2) (by omega); rwa [a2] at this
      rw [b3, a3, e k (by omega), e (k + 1) le_rfl, hq, hvis k (by omega)]

lemma traj_care (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ) :
    A.care.traj ℓ v ε = careTraj ℓ (A.traj ℓ v ε) := by
  funext t
  exact (congrFun (careTraj_comp (frame v ε) ℓ (A.pos (ℓ ∘ frame v ε))) t).symm

end Algo

/-- **Theorem 3.1** (on the labelled line). If `A` achieves rendezvous within `T` rounds for every
wake-up delay when simultaneous edge crossings count as rendezvous, then `care(A)` achieves
rendezvous at a node within `4 T` rounds for every delay. -/
theorem thm_3_1 (A : Algo) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (vα vβ : ℤ) (εα εβ : ℤˣ) (T : ℕ)
    (hA : ∀ τ, ∃ t ≤ T, MeetOrCross (A.traj ℓ vα εα) (delayed τ (A.traj ℓ vβ εβ)) t) (τ : ℕ) :
    ∃ t ≤ 4 * T, A.care.traj ℓ vα εα t = delayed τ (A.care.traj ℓ vβ εβ) t := by
  obtain ⟨t, ht, h⟩ := hA ((τ + 3) / 4)
  obtain ⟨s, hs, e⟩ := care_meet hℓ _ _ τ t h
  refine ⟨s, by omega, ?_⟩
  rw [A.traj_care, A.traj_care]; exact e

end Podc.RendezvousLabeledLine
