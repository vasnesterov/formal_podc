import Papers.PODC2025.MinimalistLE.Basic

/-!
# Deterministic properties of the flow (Section 3 of the paper)

All results hold for every coin field `c` (i.e. for every rule deciding `W• → B•`), as the paper
remarks. `e t = exec G init c t` is the configuration in round `t`.
-/

set_option linter.unusedSectionVars false

namespace MinimalistLE

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

section step
variable {C : V → St} {coin : V → Bool} {u v : V}

theorem phase_next (C : V → St) (coin : V → Bool) (v : V) :
    (next G C coin v).phase = match (C v).phase with
      | .B => .F
      | .F => .W
      | .W => if Heard G C v ∨ ((C v).leader && coin v) then .B else .W := by
  rcases h : (C v).phase
  · rw [next_of_W h]; split_ifs <;> simp_all
  · simp [h]
  · simp [h]

theorem heard_of_adj (h : G.Adj v u) (hu : (C u).phase = .B) : Heard G C v := ⟨u, h, hu⟩

/-- The one-edge version of the conservation of flow (Lemma 7): from round `t` to round `t+1` the flow
along an edge changes by `1{u beeps} − 1{v beeps}` (beeps in round `t+1`). -/
theorem flow_next (h : G.Adj u v) :
    flow (next G C coin) u v = flow C u v + (if (next G C coin u).phase = .B then 1 else 0)
      - (if (next G C coin v).phase = .B then 1 else 0) := by
  have hu : (C v).phase = .B → Heard G C u := heard_of_adj h
  have hv : (C u).phase = .B → Heard G C v := heard_of_adj h.symm
  unfold flow
  rw [phase_next, phase_next]
  rcases hpu : (C u).phase <;> rcases hpv : (C v).phase <;> simp_all <;> split_ifs <;> simp_all

end step

variable (G) in
/-- Shorthand: `v` beeps in round `t`. -/
abbrev Beeps (init : V → St) (c : ℕ → V → Bool) (t : ℕ) (v : V) : Prop :=
  (exec G init c t v).phase = .B

variable {init : V → St} {c : ℕ → V → Bool}

@[simp] theorem exec_zero : exec G init c 0 = init := rfl
theorem exec_succ (t : ℕ) : exec G init c (t + 1) = next G (exec G init c t) (c t) := rfl

theorem nbeep_succ (t : ℕ) (v : V) :
    nbeep G init c (t + 1) v = nbeep G init c t v + if Beeps G init c (t + 1) v then 1 else 0 := by
  unfold nbeep
  rw [Finset.range_add_one (n := t + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem nbeep_zero (hW : ∀ v, (init v).phase = .W) (v : V) : nbeep G init c 0 v = 0 := by
  simp [nbeep, hW]

theorem nbeep_succ_le (t : ℕ) (v : V) : nbeep G init c (t + 1) v ≤ nbeep G init c t v + 1 := by
  rw [nbeep_succ]; split_ifs <;> simp

theorem nbeep_le_succ (t : ℕ) (v : V) : nbeep G init c t v ≤ nbeep G init c (t + 1) v := by
  rw [nbeep_succ]; split_ifs <;> simp

theorem nbeep_mono {s t : ℕ} (h : s ≤ t) (v : V) : nbeep G init c s v ≤ nbeep G init c t v := by
  induction h with
  | refl => rfl
  | step _ ih => exact ih.trans (nbeep_le_succ _ _)

theorem nbeep_succ_of_beeps {t : ℕ} {v : V} (h : Beeps G init c (t + 1) v) :
    nbeep G init c (t + 1) v = nbeep G init c t v + 1 := by
  simp [nbeep_succ, h]

theorem nbeep_succ_of_not_beeps {t : ℕ} {v : V} (h : ¬ Beeps G init c (t + 1) v) :
    nbeep G init c (t + 1) v = nbeep G init c t v := by
  simp [nbeep_succ, h]

/-- If `v` does not beep in rounds `t+1, …, t+k`, its beep count does not change. -/
theorem nbeep_const {t k : ℕ} {v : V} (h : ∀ s, t < s → s ≤ t + k → ¬ Beeps G init c s v) :
    nbeep G init c (t + k) v = nbeep G init c t v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, nbeep_succ_of_not_beeps (h _ (by omega) (by omega)),
      ih fun s h1 h2 => h s h1 (by omega)]

/-! ### Claim 6 (basic observations) -/

section claim6
variable {t : ℕ} {u v : V}

/-- Claim 6, Eq. (3). -/
theorem claim6_3 (h : (exec G init c t u).phase = .W) : (exec G init c (t + 1) u).phase ≠ .F := by
  rw [exec_succ, phase_next, h]; split_ifs <;> simp

/-- Claim 6, Eq. (4). -/
theorem claim6_4 (h : (exec G init c t u).phase = .B) : (exec G init c (t + 1) u).phase = .F := by
  rw [exec_succ, phase_next, h]

/-- Claim 6, Eq. (5). -/
theorem claim6_5 (h : (exec G init c t u).phase = .F) : (exec G init c (t + 1) u).phase = .W := by
  rw [exec_succ, phase_next, h]

/-- Claim 6, Eq. (6). -/
theorem claim6_6 (hadj : G.Adj u v) (hu : (exec G init c t u).phase = .B)
    (hv : (exec G init c t v).phase = .W) : exec G init c (t + 1) v = ⟨.B, false⟩ := by
  rw [exec_succ, next_of_W hv]; simp [heard_of_adj hadj.symm hu]

/-- Claim 6, Eq. (7). -/
theorem claim6_7 (h : (exec G init c (t + 1) u).phase = .W) : (exec G init c t u).phase ≠ .B := by
  intro hB; rw [claim6_4 hB] at h; cases h

/-- Claim 6, Eq. (8). -/
theorem claim6_8 (h : (exec G init c (t + 1) u).phase = .B) : (exec G init c t u).phase = .W := by
  rw [exec_succ, phase_next] at h
  rcases h' : (exec G init c t u).phase <;> simp_all

/-- Claim 6, Eq. (9). -/
theorem claim6_9 (h : (exec G init c (t + 1) u).phase = .F) : (exec G init c t u).phase = .B := by
  rw [exec_succ, phase_next] at h
  rcases h' : (exec G init c t u).phase <;> simp_all
  split_ifs at h

/-- Claim 6, Eq. (10). -/
theorem claim6_10 (hadj : G.Adj u v) (hu : (exec G init c (t + 1) u).phase = .F)
    (hv : (exec G init c (t + 1) v).phase = .W) : (exec G init c t v).phase = .F := by
  have hB := claim6_9 hu
  rcases h' : (exec G init c t v).phase
  · rw [claim6_6 hadj hB h'] at hv; cases hv
  · exact absurd h' (claim6_7 hv)
  · rfl

/-- Claim 6, Eq. (11): a node that becomes a beeping non-leader was waiting and heard a beep. -/
theorem claim6_11 (h : exec G init c (t + 1) u = ⟨.B, false⟩) :
    (exec G init c t u).phase = .W ∧ ∃ w, G.Adj u w ∧ (exec G init c t w).phase = .B := by
  have hW := claim6_8 (u := u) (t := t) (by rw [h])
  rw [exec_succ, next_of_W hW] at h
  split_ifs at h with h1 h2
  · exact ⟨hW, h1⟩
  · cases h
  · simp at h

end claim6

/-! ### Leaders are never created -/

theorem leader_of_succ {t : ℕ} {v : V} (h : (exec G init c (t + 1) v).leader = true) :
    (exec G init c t v).leader = true := by
  rw [exec_succ] at h
  rcases h' : (exec G init c t v).phase
  · rw [next_of_W h'] at h; split_ifs at h with h1 h2 <;> simp_all
  · simpa [h'] using h
  · simpa [h'] using h

theorem leader_anti {s t : ℕ} (hst : s ≤ t) {v : V} (h : (exec G init c t v).leader = true) :
    (exec G init c s v).leader = true := by
  induction hst with
  | refl => exact h
  | step _ ih => exact ih (leader_of_succ h)

/-- A leader that stays a leader beeps in round `t+1` only by its own coin: it was waiting. -/
theorem eliminated_of_heard {t : ℕ} {v : V} (hW : (exec G init c t v).phase = .W)
    (hH : Heard G (exec G init c t) v) : exec G init c (t + 1) v = ⟨.B, false⟩ := by
  rw [exec_succ, next_of_W hW]; simp [hH]


/-! ### Conservation of flow and Ohm's law -/

section ohm
variable {u v : V}

/-- Lemma 7 for a single oriented edge. -/
theorem flow_succ (hadj : G.Adj u v) (t : ℕ) :
    flow (exec G init c (t + 1)) u v = flow (exec G init c t) u v
      + (if Beeps G init c (t + 1) u then 1 else 0) - (if Beeps G init c (t + 1) v then 1 else 0) :=
  flow_next hadj

/-- **Lemma 7 (conservation of flow).** For a path `ω` from `u` to `v`,
`ν_{t+1}(ω) = ν_t(ω) + 1{u ∈ B_{t+1}} − 1{v ∈ B_{t+1}}`. -/
theorem lemma7 (p : G.Walk u v) (t : ℕ) :
    walkFlow G (exec G init c (t + 1)) p = walkFlow G (exec G init c t) p
      + (if Beeps G init c (t + 1) u then 1 else 0) - (if Beeps G init c (t + 1) v then 1 else 0) := by
  induction p with
  | nil => simp [walkFlow]
  | cons h p ih => simp only [walkFlow]; rw [flow_succ h, ih]; ring

theorem flow_of_waiting {C : V → St} (hW : ∀ v, (C v).phase = .W) (u v : V) : flow C u v = 0 := by
  simp [flow, hW]

/-- Ohm's law for one edge. -/
theorem ohm_edge (hW : ∀ v, (init v).phase = .W) (hadj : G.Adj u v) (t : ℕ) :
    flow (exec G init c t) u v = (nbeep G init c t u : ℤ) - nbeep G init c t v := by
  induction t with
  | zero => simp [flow_of_waiting hW, nbeep_zero hW]
  | succ t ih =>
    rw [flow_succ hadj, ih, nbeep_succ, nbeep_succ]
    push_cast; split_ifs <;> ring

/-- **Corollary 8 (Ohm's law).** Under Eq. (2), the flow along any path from `u` to `v` in round `t`
equals `N_t(u) − N_t(v)`. -/
theorem corollary8 (hW : ∀ v, (init v).phase = .W) (p : G.Walk u v) (t : ℕ) :
    walkFlow G (exec G init c t) p = (nbeep G init c t u : ℤ) - nbeep G init c t v := by
  induction p with
  | nil => simp [walkFlow]
  | cons h p ih => simp only [walkFlow]; rw [ohm_edge hW h, ih]; ring

theorem abs_flow_le (C : V → St) (u v : V) : |flow C u v| ≤ 1 := by
  unfold flow; split_ifs <;> simp

/-- Eq. (1): `|ν_t(ω)| ≤ k` for a path of length `k`. -/
theorem abs_walkFlow_le (C : V → St) (p : G.Walk u v) : |walkFlow G C p| ≤ p.length := by
  induction p with
  | nil => simp [walkFlow]
  | @cons a b _ h p ih =>
    simp only [walkFlow, SimpleGraph.Walk.length_cons]; push_cast
    exact (abs_add_le _ _).trans (by linarith [abs_flow_le C a b])

/-- **Lemma 11.** `|N_t(u) − N_t(v)| ≤ dis(u, v)` (here: `≤` the length of any path). -/
theorem lemma11_walk (hW : ∀ v, (init v).phase = .W) (p : G.Walk u v) (t : ℕ) :
    |(nbeep G init c t u : ℤ) - nbeep G init c t v| ≤ p.length := by
  rw [← corollary8 hW p]; exact abs_walkFlow_le _ p

/-- **Lemma 11.** For a connected graph, `|N_t(u) − N_t(v)| ≤ dis(u, v)`. -/
theorem lemma11 (hconn : G.Connected) (hW : ∀ v, (init v).phase = .W) (u v : V) (t : ℕ) :
    |(nbeep G init c t u : ℤ) - nbeep G init c t v| ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  rw [← hp]; exact lemma11_walk hW p t

end ohm

/-! ### Lemma 9: there is always a leader -/

/-- A node loses its leader bit only by hearing a beep while waiting (`W• → B°`). -/
theorem eliminated {t : ℕ} {v : V} (h1 : (exec G init c t v).leader = true)
    (h2 : (exec G init c (t + 1) v).leader = false) : exec G init c (t + 1) v = ⟨.B, false⟩ := by
  rw [exec_succ] at h2 ⊢
  rcases h' : (exec G init c t v).phase
  · rw [next_of_W h'] at h2 ⊢; split_ifs at h2 ⊢ with h3 h4 <;> simp_all
  · simp_all
  · simp_all

/-- **Claim 10.** A node that is a beeping non-leader in round `t+1` has a neighbour that had beeped
strictly more often by round `t`. -/
theorem claim10 (hW : ∀ v, (init v).phase = .W) {t : ℕ} {u : V}
    (h : exec G init c (t + 1) u = ⟨.B, false⟩) :
    ∃ v, G.Adj u v ∧ nbeep G init c t u < nbeep G init c t v := by
  obtain ⟨huW, w, hw, hwB⟩ := claim6_11 h
  refine ⟨w, hw, ?_⟩
  have := ohm_edge (c := c) hW hw t
  have hf : flow (exec G init c t) u w = -1 := by simp [flow, huW, hwB]
  omega

/-- **Lemma 9 (strong form).** In every round some leader has the maximal number of beeps among all
nodes (the set `M⋆_t` of the paper is nonempty). -/
theorem lemma9_strong (hI : GoodInit init) (t : ℕ) :
    ∃ u, (exec G init c t u).leader = true ∧ ∀ w, nbeep G init c t w ≤ nbeep G init c t u := by
  induction t with
  | zero =>
    obtain ⟨u, hu⟩ := hI.leader
    exact ⟨u, hu, fun w => by simp [nbeep_zero hI.waiting]⟩
  | succ t ih =>
    obtain ⟨u, hul, humax⟩ := ih
    have hul' : (exec G init c (t + 1) u).leader = true := by
      by_contra hne
      obtain ⟨w, -, hw⟩ := claim10 hI.waiting (eliminated hul (by simpa using hne))
      exact absurd (humax w) (by omega)
    by_cases hall : ∀ w, nbeep G init c (t + 1) w ≤ nbeep G init c (t + 1) u
    · exact ⟨u, hul', hall⟩
    push Not at hall
    obtain ⟨v, hv⟩ := hall
    have h1 := nbeep_succ_le (init := init) (c := c) (G := G) t v
    have h2 := nbeep_le_succ (init := init) (c := c) (G := G) t u
    have h3 := humax v
    have hvB : Beeps G init c (t + 1) v := by
      by_contra hn; rw [nbeep_succ_of_not_beeps hn] at hv; omega
    refine ⟨v, ?_, fun w => ?_⟩
    · by_contra hne
      have hel : exec G init c (t + 1) v = (⟨.B, false⟩ : St) := by
        have : (exec G init c (t + 1) v).leader = false := by simpa using hne
        rw [St.mk.injEq]; exact ⟨hvB, this⟩
      obtain ⟨w, -, hw⟩ := claim10 hI.waiting hel
      have := humax w
      omega
    · have := nbeep_succ_le (init := init) (c := c) (G := G) t w
      have := humax w
      omega

/-- **Lemma 9.** There is always at least one leader in the population. -/
theorem lemma9 (hI : GoodInit init) (t : ℕ) : ∃ u, (exec G init c t u).leader = true := by
  obtain ⟨u, hu, -⟩ := lemma9_strong (G := G) (c := c) hI t; exact ⟨u, hu⟩

/-! ### Lemma 12: propagation of beeps -/

/-- **Lemma 12 (strengthened).** If `N_t(u) > N_t(v)` and `ω` is a path from `u` to `v` of length `k`,
then `v` beeps in some round `s` with `t < s ≤ t + k`. (The paper states only `s ≤ t + dis(u,v)`;
its proof gives `s > t`, which is what the proof of Lemma 19 needs.) -/
theorem lemma12_walk (hW : ∀ v, (init v).phase = .W) {u v : V} (p : G.Walk u v) (t : ℕ)
    (h : nbeep G init c t v < nbeep G init c t u) :
    ∃ s, t < s ∧ s ≤ t + p.length ∧ Beeps G init c s v := by
  induction p generalizing t with
  | nil => omega
  | @cons u u' v hadj q ih =>
    simp only [SimpleGraph.Walk.length_cons]
    by_cases h' : nbeep G init c t v < nbeep G init c t u'
    · obtain ⟨s, hs1, hs2, hs⟩ := ih t h'
      exact ⟨s, hs1, by omega, hs⟩
    · have hf := ohm_edge (c := c) hW hadj t
      have hle : nbeep G init c t u ≤ nbeep G init c t u' + 1 := by
        have := abs_flow_le (exec G init c t) u u'; rw [hf] at this
        have := (abs_le.mp this).2; omega
      have hf1 : flow (exec G init c t) u u' = 1 := by rw [hf]; omega
      have hB : (exec G init c t u).phase = .B ∧ (exec G init c t u').phase = .W := by
        unfold flow at hf1; split_ifs at hf1 with h1 h2 <;> simp_all
      have hu'B : Beeps G init c (t + 1) u' := by
        show (exec G init c (t + 1) u').phase = .B
        rw [claim6_6 hadj hB.1 hB.2]
      by_cases hvB : Beeps G init c (t + 1) v
      · exact ⟨t + 1, by omega, by omega, hvB⟩
      · have : nbeep G init c (t + 1) v < nbeep G init c (t + 1) u' := by
          rw [nbeep_succ_of_not_beeps hvB, nbeep_succ_of_beeps hu'B]; omega
        obtain ⟨s, hs1, hs2, hs⟩ := ih (t + 1) this
        exact ⟨s, by omega, by omega, hs⟩

/-- **Lemma 12.** On a connected graph, if `N_t(u) > N_t(v)` then `v` beeps in some round `s` with
`t < s ≤ t + dis(u, v)`. -/
theorem lemma12 (hconn : G.Connected) (hW : ∀ v, (init v).phase = .W) {u v : V} {t : ℕ}
    (h : nbeep G init c t v < nbeep G init c t u) :
    ∃ s, t < s ∧ s ≤ t + G.dist u v ∧ Beeps G init c s v := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  rw [← hp]; exact lemma12_walk hW p t h

end MinimalistLE
