import Papers.PODC2025.DynamicSubgraphFinding.Scenarios

/-!
# Neighbourhoods of creation endpoints

Helper lemmas for the indistinguishability arguments of Section 4: the neighbourhood of an
endpoint of a creation depends only on its side in the creation and on the final edges.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Hard

variable {V : Type} {q t : ℕ} {K : Fin t → Fin q → V} {sp : Spec V t}

lemma adj_fst_iff (hw : WF K sp) {i : Fin t} {x y : V} (hc : sp.cr i = some (x, y)) (r : ℕ)
    (u : V) : (net K sp).adj r u x ↔ (∃ k, u = K i k ∧ ct q i 0 k ≤ r) ∨
      (u ≠ x ∧ 2 * q * t + 1 ≤ r ∧ (sp.fin u x ∨ sp.fin x u)) := by
  obtain ⟨hx, -, hxy⟩ := hw.cr_I _ _ _ hc
  rw [adj_I_iff _ _ _ hx]
  constructor
  · rintro (⟨j, x', y', k, hc2, rfl, h⟩ | h)
    · by_cases hij : j = i
      · subst hij
        rw [hc] at hc2
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc2)
        rcases h with ⟨-, h⟩ | ⟨h1, -⟩
        · exact Or.inl ⟨k, rfl, h⟩
        · exact absurd h1 hxy
      · have := hw.cr_disj _ _ _ _ _ _ (Ne.symm hij) hc hc2
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 this.1
        · exact absurd h1 this.2.1
    · exact Or.inr h
  · rintro (⟨k, rfl, h⟩ | h)
    · exact Or.inl ⟨i, x, y, k, hc, rfl, Or.inl ⟨rfl, h⟩⟩
    · exact Or.inr h

lemma adj_snd_iff (hw : WF K sp) {i : Fin t} {x y : V} (hc : sp.cr i = some (x, y)) (r : ℕ)
    (u : V) : (net K sp).adj r u y ↔ (∃ k, u = K i k ∧ ct q i 1 k ≤ r) ∨
      (u ≠ y ∧ 2 * q * t + 1 ≤ r ∧ (sp.fin u y ∨ sp.fin y u)) := by
  obtain ⟨-, hy, hxy⟩ := hw.cr_I _ _ _ hc
  rw [adj_I_iff _ _ _ hy]
  constructor
  · rintro (⟨j, x', y', k, hc2, rfl, h⟩ | h)
    · by_cases hij : j = i
      · subst hij
        rw [hc] at hc2
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc2)
        rcases h with ⟨h1, -⟩ | ⟨-, h⟩
        · exact absurd h1.symm hxy
        · exact Or.inl ⟨k, rfl, h⟩
      · have := hw.cr_disj _ _ _ _ _ _ (Ne.symm hij) hc hc2
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 this.2.2.1
        · exact absurd h1 this.2.2.2
    · exact Or.inr h
  · rintro (⟨k, rfl, h⟩ | h)
    · exact Or.inl ⟨i, x, y, k, hc, rfl, Or.inr ⟨rfl, h⟩⟩
    · exact Or.inr h

/-- Before round `T`, the first endpoint `x` of `create(x, K^i, ·)` has the same neighbourhood in
every well-formed scenario containing such a creation (whatever the second endpoint). -/
lemma adj_fst_eq {sp' : Spec V t} (hw : WF K sp) (hw' : WF K sp') {i : Fin t} {x y y' : V}
    (hc : sp.cr i = some (x, y)) (hc' : sp'.cr i = some (x, y')) {r : ℕ} (hr : r ≤ 2 * q * t)
    (u : V) : (net K sp).adj r u x ↔ (net K sp').adj r u x := by
  rw [adj_fst_iff hw hc, adj_fst_iff hw' hc']
  constructor <;> rintro (h | ⟨-, h, -⟩) <;> first | exact Or.inl h | omega

lemma adj_snd_eq {sp' : Spec V t} (hw : WF K sp) (hw' : WF K sp') {i : Fin t} {x x' y : V}
    (hc : sp.cr i = some (x, y)) (hc' : sp'.cr i = some (x', y)) {r : ℕ} (hr : r ≤ 2 * q * t)
    (u : V) : (net K sp).adj r u y ↔ (net K sp').adj r u y := by
  rw [adj_snd_iff hw hc, adj_snd_iff hw' hc']
  constructor <;> rintro (h | ⟨-, h, -⟩) <;> first | exact Or.inl h | omega

section Exec

variable {M O : Type} (A : Algorithm V M O)

lemma send_eq_of_inbox_eq' {D D' : InsNet V} {k : ℕ} {u w : V} (h : D.adj (k + 1) u w)
    (h' : D'.adj (k + 1) u w)
    (he : A.inbox D (A.state D k) (k + 1) w u = A.inbox D' (A.state D' k) (k + 1) w u) :
    A.send (k + 1) (A.state D k u) (D.loc (k + 1) u) w =
      A.send (k + 1) (A.state D' k u) (D'.loc (k + 1) u) w := by
  unfold Algorithm.inbox at he
  rw [ite_eq_left h, ite_eq_left h'] at he
  exact Option.some.inj he

lemma inbox_eq_of_send_eq {D D' : InsNet V} {k : ℕ} {u w : V} (h : D.adj (k + 1) u w)
    (h' : D'.adj (k + 1) u w)
    (he : A.send (k + 1) (A.state D k u) (D.loc (k + 1) u) w =
      A.send (k + 1) (A.state D' k u) (D'.loc (k + 1) u) w) :
    A.inbox D (A.state D k) (k + 1) w u = A.inbox D' (A.state D' k) (k + 1) w u := by
  unfold Algorithm.inbox
  rw [ite_eq_left h, ite_eq_left h', he]

/-- The first endpoint `x` of `create(x, K^i, ·)` is in the same state after round `r ≤ R` in two
scenarios, if it received the same messages from `K^i` in rounds `1..r`. -/
lemma state_fst_of_msgs (hK : KInj K) {sp sp' : Spec V t} (hw : WF K sp) (hw' : WF K sp')
    (hf : sp.full ↔ sp'.full) {i : Fin t} {x y y' : V} (hc : sp.cr i = some (x, y))
    (hc' : sp'.cr i = some (x, y')) {r : ℕ} (hr : r ≤ 2 * q * t)
    (h : ∀ k, k + 1 ≤ r → ∀ p, A.inbox (net K sp) (A.state (net K sp) k) (k + 1) x (K i p) =
      A.inbox (net K sp') (A.state (net K sp') k) (k + 1) x (K i p)) :
    A.state (net K sp) r x = A.state (net K sp') r x := by
  have hadj : ∀ k ≤ r, ∀ u, (net K sp).adj k u x ↔ (net K sp').adj k u x :=
    fun k hk u => adj_fst_eq hw hw' hc hc' (by omega) u
  refine A.state_eq_of_msgs (g0_eq hK hw hw' hf) x r
    (fun k hk => loc_eq_of_adj hf k x (hadj k hk)) hadj (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_fst_iff hw hc] at hu0
  rcases hu0 with ⟨p, rfl, -⟩ | ⟨-, h1, -⟩
  · exact send_eq_of_inbox_eq' A hu ((hadj (k + 1) hk _).1 hu) (h k hk p)
  · omega

lemma state_snd_of_msgs (hK : KInj K) {sp sp' : Spec V t} (hw : WF K sp) (hw' : WF K sp')
    (hf : sp.full ↔ sp'.full) {i : Fin t} {x x' y : V} (hc : sp.cr i = some (x, y))
    (hc' : sp'.cr i = some (x', y)) {r : ℕ} (hr : r ≤ 2 * q * t)
    (h : ∀ k, k + 1 ≤ r → ∀ p, A.inbox (net K sp) (A.state (net K sp) k) (k + 1) y (K i p) =
      A.inbox (net K sp') (A.state (net K sp') k) (k + 1) y (K i p)) :
    A.state (net K sp) r y = A.state (net K sp') r y := by
  have hadj : ∀ k ≤ r, ∀ u, (net K sp).adj k u y ↔ (net K sp').adj k u y :=
    fun k hk u => adj_snd_eq hw hw' hc hc' (by omega) u
  refine A.state_eq_of_msgs (g0_eq hK hw hw' hf) y r
    (fun k hk => loc_eq_of_adj hf k y (hadj k hk)) hadj (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_snd_iff hw hc] at hu0
  rcases hu0 with ⟨p, rfl, -⟩ | ⟨-, h1, -⟩
  · exact send_eq_of_inbox_eq' A hu ((hadj (k + 1) hk _).1 hu) (h k hk p)
  · omega

/-- Messages sent inside a creation component before round `T` agree. -/
lemma comp_send (hK : KInj K) {sp sp' : Spec V t} (hw : WF K sp) (hw' : WF K sp')
    (hf : sp.full ↔ sp'.full) {i : Fin t} {x y : V} (hc : sp.cr i = some (x, y))
    (hc' : sp'.cr i = some (x, y)) {k : ℕ} (hk : k + 1 ≤ 2 * q * t) {u : V}
    (hu : Comp K i x y u) (w : V) :
    A.send (k + 1) (A.state (net K sp) k u) ((net K sp).loc (k + 1) u) w =
      A.send (k + 1) (A.state (net K sp') k u) ((net K sp').loc (k + 1) u) w := by
  rw [comp_state A hK hw hw' hf hc hc' (by omega) u hu,
    loc_eq_of_adj hf _ _ (fun v => (comp_adj hK hw hw' hc hc' hk v u hu).1)]

/-- An untouched clique evolves identically in all scenarios. -/
lemma K_state_none (hK : KInj K) {sp sp' : Spec V t} (hw : WF K sp) (hw' : WF K sp')
    (hf : sp.full ↔ sp'.full) {j : Fin t} (hc : sp.cr j = none) (hc' : sp'.cr j = none)
    (r : ℕ) (p : Fin q) : A.state (net K sp) r (K j p) = A.state (net K sp') r (K j p) := by
  have hadj : ∀ k u (p : Fin q), (net K sp).adj k u (K j p) ↔ (net K sp').adj k u (K j p) := by
    intro k u p
    rw [adj_K_iff hK hw, adj_K_iff hK hw', hc, hc']
  refine A.state_eq_of_closed (g0_eq hK hw hw' hf) (fun v => ∃ p, v = K j p) r
    (fun k _ v ⟨p, hv⟩ => hv ▸ loc_eq_of_adj hf k _ (fun u => hadj k u p))
    (fun k _ u v ⟨p, hv⟩ => hv ▸ hadj k u p) (fun k _ u v ⟨p, hv⟩ huv => ?_) r le_rfl _ ⟨p, rfl⟩
  subst hv
  rw [adj_K_iff hK hw, hc] at huv
  rcases huv with ⟨p', -, rfl⟩ | ⟨x, y, h, -⟩
  · exact ⟨p', rfl⟩
  · exact absurd h (by simp)

end Exec

end Hard

end Podc.DynamicSubgraphFinding
