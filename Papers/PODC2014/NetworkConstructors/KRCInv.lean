import Papers.PODC2014.NetworkConstructors.KRC

/-!
# Protocol 8 (kRC): invariant and the output-stable set

* `Inv`: every agent's index is its degree, and every non-isolated agent is connected (in the
  active graph) to a leader. It holds initially and is preserved by every interaction.
* `S`: configurations satisfying `Inv`, without `l_{k+1}`, with a connected active graph, exactly
  one leader, and in which any two deficient agents (degree `< k`) are adjacent. `S` is closed,
  the active graph never changes inside `S` (only the leader moves), and every configuration of `S`
  outputs a network as in Theorem 12 (`S_almostRegular`).
-/

namespace Podc.NetworkConstructors.KRC

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

section General

variable {V Q : Type*} [Fintype V] [DecidableEq V]

-- Candidate for `Podc/Computability/Distributed/NetworkConstructors/Graph.lean`
theorem deg_pos_of_adj {C : Config V Q} {u v : V} (h : C.active.Adj u v) : 0 < C.deg u := by
  unfold Config.deg
  exact Finset.card_pos.2 ⟨v, by simpa [Finset.mem_filter, ne_comm] using h⟩

-- Candidate for `Podc/Computability/Distributed/NetworkConstructors/Graph.lean`
theorem exists_adj_of_deg_pos {C : Config V Q} {u : V} (h : 0 < C.deg u) :
    ∃ v, C.active.Adj u v := by
  unfold Config.deg at h
  obtain ⟨v, hv⟩ := Finset.card_pos.1 h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact ⟨v, hv.1.symm, hv.2⟩

-- Candidate for `Podc/Computability/Distributed/NetworkConstructors/Graph.lean`
theorem eq_of_reachable_of_deg_eq_zero {C : Config V Q} {x v : V} (h0 : C.deg v = 0)
    (h : C.active.Reachable x v) : x = v := by
  by_contra hne
  obtain ⟨p⟩ := h.symm
  have := deg_pos_of_adj (p.adj_snd (p.not_nil_of_ne (Ne.symm hne)))
  omega

end General

variable {k : ℕ} (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem kRC_δ : (kRC k hk).δ = δ k hk := rfl

@[simp] theorem kRC_out (s : St k) : (kRC k hk).out s = true := rfl

/-- The invariant of kRC: the index of every agent is its degree, and every non-isolated agent
is connected to a leader. -/
def Inv (C : Config V (St k)) : Prop :=
  (∀ x, C.deg x = (C.st x).idx) ∧
    ∀ x, 0 < C.deg x → ∃ y, (C.st y).isL = true ∧ C.active.Reachable x y

theorem inv_interact {C : Config V (St k)} (hC : Inv C) {u v : V} (huv : u ≠ v) :
    Inv ((kRC k hk).interact C u v) := by
  obtain ⟨h1, h2⟩ := hC
  set D := (kRC k hk).interact C u v with hD
  have hsu : D.st u = (δ k hk (C.st u) (C.st v) (C.edge u v)).1 := Protocol.interact_st_left C u v
  have hsv : D.st v = (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1 :=
    Protocol.interact_st_right C huv
  have hso : ∀ x, x ≠ u → x ≠ v → D.st x = C.st x := fun x hu hv =>
    Protocol.interact_st_other C hu hv
  have hdo : ∀ x, x ≠ u → x ≠ v → D.deg x = C.deg x := fun x hu hv =>
    Protocol.deg_interact_other hu hv
  rcases δ_kind hk (C.st u) (C.st v) (C.edge u v) with
    ⟨he, hiu, hiv, hrr⟩ | ⟨hc, he, hiu, hiv, -, hL⟩ | ⟨hc, he, hiu, hiv, -, hLu, hLv⟩
  · have hact : D.active = C.active := Protocol.interact_active_of_edge_eq he
    have hdeg : ∀ x, D.deg x = C.deg x := fun x => Protocol.deg_interact_of_edge_eq he
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [hdeg]
      by_cases hxu : x = u
      · rw [hxu, hsu, hiu, h1]
      by_cases hxv : x = v
      · rw [hxv, hsv, hiv, h1]
      rw [hso x hxu hxv, h1]
    · rw [hdeg] at hx
      obtain ⟨y, hy, hxy⟩ := h2 x hx
      rw [hact]
      by_cases hyuv : y = u ∨ y = v
      · rcases hrr with hrr | ⟨hc, -, -, hLv⟩
        · refine ⟨y, ?_, hxy⟩
          rcases hyuv with rfl | rfl
          · rw [hsu, hrr]; exact hy
          · rw [hsv, hrr]; exact hy
        · refine ⟨v, by rw [hsv]; exact hLv, hxy.trans ?_⟩
          rcases hyuv with rfl | rfl
          · exact (show C.active.Adj y v from ⟨huv, hc⟩).reachable
          · rfl
      · push Not at hyuv
        exact ⟨y, by rw [hso y hyuv.1 hyuv.2]; exact hy, hxy⟩
  · have hact : D.active = C.active ⊔ SimpleGraph.edge u v :=
      Protocol.interact_active_of_edge_true huv he
    have hdu : D.deg u = C.deg u + 1 := Protocol.deg_interact_activate_left huv hc he
    have hdv : D.deg v = C.deg v + 1 := Protocol.deg_interact_activate_right huv hc he
    have hI1 : ∀ x, D.deg x = (D.st x).idx := by
      intro x
      by_cases hxu : x = u
      · rw [hxu, hdu, hsu, hiu, h1]
      by_cases hxv : x = v
      · rw [hxv, hdv, hsv, hiv, h1]
      rw [hdo x hxu hxv, hso x hxu hxv, h1]
    refine ⟨hI1, fun x hx => ?_⟩
    rw [hact]
    have hle : ∀ a b, C.active.Reachable a b → (C.active ⊔ SimpleGraph.edge u v).Reachable a b :=
      fun a b h => h.mono le_sup_left
    have hUV : (C.active ⊔ SimpleGraph.edge u v).Reachable u v :=
      SimpleGraph.reachable_sup_edge_iff.2 (.inr (.inl ⟨.rfl, .rfl⟩))
    have hcase : ∀ z, (D.st z).isL = true → (C.active ⊔ SimpleGraph.edge u v).Reachable u z →
        ∃ y, (D.st y).isL = true ∧ (C.active ⊔ SimpleGraph.edge u v).Reachable x y := by
      intro z hz huz
      by_cases hx' : C.active.Reachable x u ∨ C.active.Reachable x v
      · refine ⟨z, hz, ?_⟩
        rcases hx' with h | h
        · exact (hle _ _ h).trans huz
        · exact (hle _ _ h).trans (hUV.symm.trans huz)
      · push Not at hx'
        have hxu : x ≠ u := fun h => hx'.1 (h ▸ .rfl)
        have hxv : x ≠ v := fun h => hx'.2 (h ▸ .rfl)
        rw [hdo x hxu hxv] at hx
        obtain ⟨y, hy, hxy⟩ := h2 x hx
        have hyu : y ≠ u := fun h => hx'.1 (h ▸ hxy)
        have hyv : y ≠ v := fun h => hx'.2 (h ▸ hxy)
        exact ⟨y, by rw [hso y hyu hyv]; exact hy, hle _ _ hxy⟩
    rcases hL with hL | hL | ⟨hsL, htL, hiu1⟩
    · exact hcase u (by rw [hsu]; exact hL) .rfl
    · exact hcase v (by rw [hsv]; exact hL) hUV
    · have hnot : ∀ y, (C.st y).isL = true → y ≠ u ∧ y ≠ v := by
        refine fun y hy => ⟨?_, ?_⟩ <;> rintro rfl <;> simp_all
      by_cases hx0 : 0 < C.deg x
      · obtain ⟨y, hy, hxy⟩ := h2 x hx0
        obtain ⟨hyu, hyv⟩ := hnot y hy
        exact ⟨y, by rw [hso y hyu hyv]; exact hy, hle _ _ hxy⟩
      · have hxuv : x = u ∨ x = v := by
          by_contra h
          push Not at h
          rw [hdo x h.1 h.2] at hx
          exact hx0 hx
        have hu0 : 0 < C.deg u := by rw [h1]; omega
        obtain ⟨y, hy, hxy⟩ := h2 u hu0
        obtain ⟨hyu, hyv⟩ := hnot y hy
        refine ⟨y, by rw [hso y hyu hyv]; exact hy, ?_⟩
        rcases hxuv with rfl | rfl
        · exact hle _ _ hxy
        · exact hUV.symm.trans (hle _ _ hxy)
  · have hact : D.active = C.active \ SimpleGraph.edge u v :=
      Protocol.interact_active_of_edge_false he
    have hdu : D.deg u + 1 = C.deg u := Protocol.deg_interact_deactivate_left huv hc he
    have hdv : D.deg v + 1 = C.deg v := Protocol.deg_interact_deactivate_right huv hc he
    have hI1 : ∀ x, D.deg x = (D.st x).idx := by
      intro x
      by_cases hxu : x = u
      · rw [hxu, hsu]; have := h1 u; omega
      by_cases hxv : x = v
      · rw [hxv, hsv]; have := h1 v; omega
      rw [hdo x hxu hxv, hso x hxu hxv, h1]
    refine ⟨hI1, fun x hx => ?_⟩
    have hxC : 0 < C.deg x := by
      by_cases hxu : x = u
      · subst hxu; omega
      by_cases hxv : x = v
      · subst hxv; omega
      rwa [hdo x hxu hxv] at hx
    obtain ⟨y, hy, hxy⟩ := h2 x hxC
    rw [hact]
    have hv' : (C.active \ SimpleGraph.edge u v).Reachable x v →
        ∃ y, (D.st y).isL = true ∧ (C.active \ SimpleGraph.edge u v).Reachable x y := by
      intro h
      rcases hLv with hLv | hLv
      · exact ⟨v, by rw [hsv]; exact hLv, h⟩
      · have h0 : D.deg v = 0 := by rw [hI1, hsv]; exact hLv
        have := eq_of_reachable_of_deg_eq_zero (x := x) h0 (by rw [hact]; exact h)
        subst this
        omega
    rcases hxy.sdiff_edge (u := u) (v := v) with h | h | h
    · by_cases hyu : y = u
      · subst hyu; exact ⟨y, by rw [hsu]; exact hLu, h⟩
      by_cases hyv : y = v
      · subst hyv; exact hv' h
      exact ⟨y, by rw [hso y hyu hyv]; exact hy, h⟩
    · exact ⟨u, by rw [hsu]; exact hLu, h⟩
    · exact hv' h

theorem inv_init : Inv ((kRC k hk).initConfig : Config V (St k)) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · simp [Config.deg, Protocol.initConfig, kRC]
  · simp [Config.deg, Protocol.initConfig] at hx

theorem inv_step {C D : Config V (St k)} (hC : Inv C) (h : (kRC k hk).Step C D) : Inv D := by
  obtain ⟨u, v, huv, rfl⟩ := h
  exact inv_interact hk hC huv

theorem inv_reach {C D : Config V (St k)} (hC : Inv C) (h : (kRC k hk).Reachable C D) : Inv D := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact inv_step hk ih hst

/-- The set of output-stable configurations: `Inv`, no `l_{k+1}`, a connected active graph, a
unique leader, and deficient agents (degree `< k`) pairwise adjacent. -/
def S (k : ℕ) : Set (Config V (St k)) :=
  {C | Inv C ∧ (∀ x, (C.st x).idx ≤ k) ∧ C.active.Connected ∧
    (∃ ℓ, ∀ x, (C.st x).isL = true ↔ x = ℓ) ∧
    ∀ u v, u ≠ v → C.deg u < k → C.deg v < k → C.edge u v = true}

/-- In `S`, every interaction keeps the edges and stays in `S` (only the leader moves). -/
theorem S_interact {C : Config V (St k)} (hC : C ∈ S k) {u v : V} (huv : u ≠ v) :
    ((kRC k hk).interact C u v).edge = C.edge ∧ (kRC k hk).interact C u v ∈ S k := by
  obtain ⟨hI, hN, hconn, ⟨ℓ, hℓ⟩, hcl⟩ := hC
  set D := (kRC k hk).interact C u v with hD
  have hsu : D.st u = (δ k hk (C.st u) (C.st v) (C.edge u v)).1 := Protocol.interact_st_left C u v
  have hsv : D.st v = (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1 :=
    Protocol.interact_st_right C huv
  have hso : ∀ x, x ≠ u → x ≠ v → D.st x = C.st x := fun x hu hv =>
    Protocol.interact_st_other C hu hv
  rcases δ_kind hk (C.st u) (C.st v) (C.edge u v) with
    ⟨he, hiu, hiv, hrr⟩ | ⟨hc, he, hiu, hiv, hwhy, -⟩ | ⟨hc, he, hiu, hiv, htop, -⟩
  · have hedge : D.edge = C.edge := Protocol.interact_edge_of_edge_eq he
    have hact : D.active = C.active := Protocol.interact_active_of_edge_eq he
    have hdeg : ∀ x, D.deg x = C.deg x := fun x => Protocol.deg_interact_of_edge_eq he
    have hidx : ∀ x, (D.st x).idx = (C.st x).idx := by
      intro x
      by_cases hxu : x = u
      · rw [hxu, hsu, hiu]
      by_cases hxv : x = v
      · rw [hxv, hsv, hiv]
      rw [hso x hxu hxv]
    refine ⟨hedge, inv_interact hk hI huv, fun x => hidx x ▸ hN x, hact ▸ hconn, ?_,
      fun a b hab ha hb => ?_⟩
    · rcases hrr with hrr | ⟨-, hsL, hrL, hrL2⟩
      · have hDC : D = C := Protocol.interact_eq_self C hrr
        rw [hDC]
        exact ⟨ℓ, hℓ⟩
      · have hu : u = ℓ := (hℓ u).1 hsL
        refine ⟨v, fun x => ?_⟩
        by_cases hxu : x = u
        · rw [hxu, hsu, hrL]; simp [huv]
        by_cases hxv : x = v
        · rw [hxv, hsv, hrL2]; simp
        rw [hso x hxu hxv, hℓ x]
        exact ⟨fun h => absurd (h.trans hu.symm) hxu, fun h => absurd h hxv⟩
    · rw [hdeg] at ha hb
      rw [hedge]
      exact hcl a b hab ha hb
  · exfalso
    rcases hwhy with ⟨hs, ht⟩ | ⟨hsL, -, ht⟩
    · rw [← hI.1] at hs ht
      rw [hcl u v huv hs ht] at hc
      exact absurd hc (by decide)
    · rcases ht with ht | ht
      · rw [← hI.1] at ht
        obtain ⟨p⟩ := hconn.preconnected v u
        have := deg_pos_of_adj (p.adj_snd (p.not_nil_of_ne huv.symm))
        omega
      · exact huv (((hℓ u).1 hsL).trans ((hℓ v).1 ht).symm)
  · exfalso
    have := hN u
    omega

theorem S_trap : IsTrap (kRC k hk).Step (S k : Set (Config V (St k))) := by
  rintro C D hC ⟨u, v, huv, rfl⟩
  exact (S_interact hk hC huv).2

theorem S_output {C D : Config V (St k)} (hC : C ∈ S k) (h : (kRC k hk).Step C D) :
    (kRC k hk).output D = (kRC k hk).output C := by
  obtain ⟨u, v, huv, rfl⟩ := h
  exact Protocol.output_eq_of _ (fun _ => rfl) (S_interact hk hC huv).1

/-- Every configuration of `S` outputs a network as in Theorem 12. -/
theorem S_almostRegular (hn : k + 1 ≤ Fintype.card V) {C : Config V (St k)} (hC : C ∈ S k) :
    IsAlmostRegular k ((kRC k hk).output C) := by
  obtain ⟨hI, hN, hconn, -, hcl⟩ := hC
  have hout : ∀ q, (kRC k hk).out q = true := fun _ => rfl
  have hdegk : ∀ x, C.deg x ≤ k := fun x => (hI.1 x) ▸ hN x
  set D := Finset.univ.filter fun v => C.deg v < k with hD
  have hN' : ∀ v, C.deg v = (Finset.univ.filter fun w => w ≠ v ∧ C.edge v w = true).card :=
    fun v => rfl
  have hsub : ∀ v ∈ D,
      D.erase v ⊆ Finset.univ.filter fun w => w ≠ v ∧ C.edge v w = true := by
    intro v hv w hw
    rw [Finset.mem_erase] at hw
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw ⊢
    exact ⟨hw.1, hcl v w (Ne.symm hw.1) hv hw.2⟩
  have hlow : ∀ v ∈ D, D.card - 1 ≤ C.deg v := by
    intro v hv
    rw [hN', ← Finset.card_erase_of_mem hv]
    exact Finset.card_le_card (hsub v hv)
  have hmemD : ∀ v, v ∈ D ↔ C.deg v < k := by simp [hD]
  have hcard : D.card ≤ k - 1 := by
    by_contra hcon
    have hclosed : ∀ v ∈ D, ∀ w, C.active.Adj v w → w ∈ D := by
      intro v hv w hw
      have heq := Finset.eq_of_subset_of_card_le (hsub v hv) (by
        rw [← hN', Finset.card_erase_of_mem hv]
        have := (hmemD v).1 hv
        omega)
      have : w ∈ Finset.univ.filter fun w => w ≠ v ∧ C.edge v w = true := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hw.1.symm, hw.2⟩
      rw [← heq] at this
      exact Finset.mem_of_mem_erase this
    have hwalk : ∀ {a b : V} (p : C.active.Walk a b), a ∈ D → b ∈ D := by
      intro a b p
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun ha => ih (hclosed _ ha _ h)
    obtain ⟨v₀, hv₀⟩ : D.Nonempty := Finset.card_pos.1 (by omega)
    have hall : D = Finset.univ := Finset.eq_univ_of_forall fun w =>
      hwalk (hconn.preconnected v₀ w).some hv₀
    have h1 := hlow v₀ hv₀
    have h2 := (hmemD v₀).1 hv₀
    rw [hall, Finset.card_univ] at h1
    omega
  refine ⟨Protocol.output_verts_univ hout C, (Protocol.output_connected_iff hout C).2 hconn, D,
    hcard, fun v hv => ?_, fun v hv => ?_⟩
  · rw [Protocol.ncard_neighborSet_output hout C v]
    have := hdegk v
    rw [hmemD] at hv
    omega
  · rw [Protocol.ncard_neighborSet_output hout C v]
    have := (hmemD v).1 hv
    exact ⟨hlow v hv, by omega⟩

end Podc.NetworkConstructors.KRC
