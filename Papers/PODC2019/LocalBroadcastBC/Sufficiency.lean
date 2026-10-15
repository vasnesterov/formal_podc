import Papers.PODC2019.LocalBroadcastBC.Flooding
import Papers.PODC2019.LocalBroadcastBC.Paths

/-!
# Sufficiency: correctness of Algorithm 1 (Theorem 5.1 of [KNV19])

`alg1_solves`: under minimum degree `≥ 2f` and `(⌊3f/2⌋ + 1)`-connectivity, Algorithm 1 (with any
path selection satisfying `SelSpec`) solves Byzantine consensus under local broadcast against at
most `f` faults. `theorem_5_1`: hence consensus is solvable.
-/

open Finset Cslib.Byzantine.LockStep

namespace LocalBroadcastBC

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : ℕ}
  {sel : Finset V → V → V → List V}

open Classical in
/-- Algorithm 1 is correct. -/
theorem alg1_solves [DecidableRel G.Adj] (hdeg : 2 * f ≤ G.minDegree)
    (hconn : G.IsVertexConnected (3 * f / 2 + 1)) (hsel : SelSpec G f sel) :
    SolvesLB G (alg1 G f sel) (atMost f) (Consensus : Spec V Bool Bool) := by
  intro s hZ hrel hlb
  have hR : 0 < rounds (V := V) := by have := hconn.1; unfold rounds; omega
  set Bz := s.byz.toFinset with hBzdef
  have hBz : Bz.card ≤ f := by
    rw [hBzdef, ← Set.ncard_eq_toFinset_card']; exact hZ
  have hmemBz : ∀ x, x ∈ Bz ↔ x ∈ s.byz := fun x => Set.mem_toFinset
  set R := rounds (V := V) with hRdef
  let γ : ℕ → V → Bool := fun k v => (stAt G f sel s (k * R) v).γ
  have hpaths := pathsExist hdeg hconn
  -- one phase
  have hstep : ∀ k v, γ (k + 1) v =
      phaseUpdate G f sel k v (γ k v) (accAt G f sel s (k * R + (R - 1)) v) :=
    fun k v => γ_phase_end hR k v
  have hO := fun k => floodOutcome (G := G) (f := f) (sel := sel) hR hrel hlb k
  have hfv : ∀ k u, u ∉ Bz → fv G f sel s k u = γ k u := fun k u hu =>
    fv_honest ((hmemBz u).not.1 hu)
  -- Lemma 5.2 for every phase
  have h52 : ∀ k v, v ∉ Bz → ∃ u, u ∉ Bz ∧ γ (k + 1) v = γ k u := by
    intro k v hv
    rw [hstep]
    unfold phaseUpdate
    split
    · exact ⟨v, hv, rfl⟩
    · exact lemma_5_2 hBz (hO k) (hfv k) _ hv
  -- validity invariant
  have hval : ∀ k v, v ∉ Bz → ∃ u, u ∉ Bz ∧ γ k v = s.input u := by
    intro k
    induction k with
    | zero => intro v hv; exact ⟨v, hv, by simp [γ, stAt_zero, initState]⟩
    | succ k ih =>
      intro v hv
      obtain ⟨u, hu, h⟩ := h52 k v hv
      obtain ⟨w, hw, h'⟩ := ih u hu
      exact ⟨w, hw, h.trans h'⟩
  -- the phase with `F = Bz`
  have hBzmem : Bz ∈ phases (V := V) f := mem_phases.2 hBz
  obtain ⟨k₀, hk₀, hget⟩ := List.getElem_of_mem hBzmem
  have hagree0 : ∃ α, ∀ v, v ∉ Bz → γ (k₀ + 1) v = α := by
    have hk : (phases (V := V) f)[k₀]? = some Bz := by rw [List.getElem?_eq_getElem hk₀, hget]
    obtain ⟨α, hα⟩ := lemma_5_3 (sel := sel) (subset_refl Bz) hBz hsel hpaths (hO k₀) (hfv k₀)
    refine ⟨α, fun v hv => ?_⟩
    rw [hstep]
    unfold phaseUpdate
    rw [hk]
    exact hα v hv
  have hagree : ∀ k, k₀ + 1 ≤ k → ∃ α, ∀ v, v ∉ Bz → γ k v = α := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hagree0
    | succ k _ ih =>
      obtain ⟨α, hα⟩ := ih
      refine ⟨α, fun v hv => ?_⟩
      obtain ⟨u, hu, h⟩ := h52 k v hv
      rw [h, hα u hu]
  set L := (phases (V := V) f).length with hL
  obtain ⟨α, hα⟩ := hagree L (by omega)
  -- decisions
  have hdec : ∀ v, Decides G (alg1 G f sel) s v (γ L v) := by
    intro v
    refine ⟨L * R, ?_, fun r hr => ?_⟩
    · simp [status, alg1, hL, hRdef, stAt, γ]
    · simp only [status, alg1, length_hist]
      split_ifs with h
      · rw [← hL, ← hRdef] at h; omega
      · rfl
  have hdec' : ∀ v o, Decides G (alg1 G f sel) s v o → o = γ L v := fun v o h =>
    Decides.unique G _ h (hdec v)
  have hhon : ∀ v, v ∈ s.honest ↔ v ∉ Bz := fun v => by
    rw [hmemBz]; rfl
  refine ⟨fun v _ => ⟨_, hdec v⟩, fun v hv o ho => ?_, fun v hv w hw o o' ho ho' => ?_⟩
  · rw [hdec' v o ho]
    obtain ⟨u, hu, h⟩ := hval L v ((hhon v).1 hv)
    exact ⟨u, (hhon u).2 hu, h.symm⟩
  · rw [hdec' v o ho, hdec' w o' ho', hα v ((hhon v).1 hv), hα w ((hhon w).1 hw)]

/-- **Theorem 5.1** of [KNV19] (sufficiency): if `G` has minimum degree at least `2f` and is
`(⌊3f/2⌋ + 1)`-connected, then Byzantine consensus tolerating at most `f` faults is achievable
under the local broadcast model (by Algorithm 1). -/
theorem theorem_5_1 [DecidableRel G.Adj] (hdeg : 2 * f ≤ G.minDegree)
    (hconn : G.IsVertexConnected (3 * f / 2 + 1)) :
    SolvableLB G (atMost f) (Consensus : Spec V Bool Bool) := by
  obtain ⟨sel, hsel⟩ := exists_selSpec hconn
  exact ⟨Msg V, alg1 G f sel, alg1_isBroadcast G f sel, alg1_solves hdeg hconn hsel⟩

end LocalBroadcastBC
