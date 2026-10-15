import Papers.PODC2025.ByzantineStableMatching.PiBSM
import Papers.PODC2025.ByzantineStableMatching.Necessity
import Cslib.Computability.Distributed.Byzantine.LockStep.Relay

/-!
# Main results: Theorems 2–7 (and Lemma 9)

Tight solvability characterizations of Byzantine stable matching for `k ≥ 2` parties per side.
Sufficiency uses the classical BB/BA results as explicit hypotheses (`Hypotheses.lean`); the
reductions (Lemmas 1, 6, 8, 9–12) and all impossibility results are proved.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum PiBSM

variable {k : ℕ}

/-! ## Relay sets -/

/-- Embedding of `R` into the parties. -/
def inrEmb : Fin k ↪ Party k := ⟨inr, inr_injective⟩
/-- Embedding of `L` into the parties. -/
def inlEmb : Fin k ↪ Party k := ⟨inl, inl_injective⟩

/-- Relays for a pair of parties on the same side: all parties of the other side. -/
def otherSide (u _v : Party k) : Finset (Party k) :=
  if u.isLeft then Finset.univ.map inrEmb else Finset.univ.map inlEmb

open Classical in
lemma card_filter_map_inr (B : Set (Party k)) :
    ((Finset.univ.map (inrEmb (k := k))).filter (· ∈ B)).card = (inr ⁻¹' B).ncard := by
  classical
  rw [Finset.filter_map, Finset.card_map, Set.ncard_eq_toFinset_card']
  congr 1; ext j; exact Finset.mem_filter.trans (by simp; rfl)

open Classical in
lemma card_filter_map_inl (B : Set (Party k)) :
    ((Finset.univ.map (inlEmb (k := k))).filter (· ∈ B)).card = (inl ⁻¹' B).ncard := by
  classical
  rw [Finset.filter_map, Finset.card_map, Set.ncard_eq_toFinset_card']
  congr 1; ext j; exact Finset.mem_filter.trans (by simp; rfl)

lemma ncard_preimage_le (f : Fin k → Party k) (B : Set (Party k)) : (f ⁻¹' B).ncard ≤ k := by
  calc (f ⁻¹' B).ncard ≤ (Set.univ : Set (Fin k)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = k := by simp [Set.ncard_univ]

lemma thresholds_mono {tL tR tL' tR' : ℕ} (hL : tL ≤ tL') (hR : tR ≤ tR') {B : Set (Party k)}
    (h : B ∈ thresholds k tL tR) : B ∈ thresholds k tL' tR' := ⟨h.1.trans hL, h.2.trans hR⟩

lemma bSM_honestOnly : (bSM k).HonestOnly := fun _ _ _ _ hd h => PiBSM.bSM_congr hd h

/-- Same-side pairs of a network `G' ≤ fully` without edges inside a side are relayed through the other
side (both endpoints are adjacent to every party of the other side in `oneSided`/`bipartite`). -/
lemma otherSide_rel (G G' : SimpleGraph (Party k)) (hG' : bipartite k ≤ G')
    (hsame : ∀ u v, G.Adj u v → ¬ G'.Adj u v → u.isLeft = v.isLeft) :
    ∀ u v w, G.Adj u v → ¬ G'.Adj u v → w ∈ otherSide u v → G'.Adj u w ∧ G'.Adj w v := by
  intro u v w huv hn hw
  have hs := hsame u v huv hn
  unfold otherSide at hw
  split_ifs at hw with hu
  · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hw
    refine ⟨hG' ?_, hG' ?_⟩ <;> simp [inrEmb, hu, ← hs]
  · obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hw
    refine ⟨hG' ?_, hG' ?_⟩ <;> simp_all [inlEmb]

/-! ## The `L`-protocol data from Theorems 8/9 -/

lemma SolvesWithOmissions.mono {P I M O : Type*} {G : SimpleGraph P} {alg : Protocol P I M O}
    {Z : AdvStructure P} {spec specOm : Spec P I O} {T T' : ℕ} (hT : T ≤ T')
    (h : SolvesWithOmissions G alg Z spec specOm T) : SolvesWithOmissions G alg Z spec specOm T' :=
  fun s hs => ⟨(h s hs).1, (h s hs).2.1, fun p hp => by
    obtain ⟨r, hr, o, ho⟩ := (h s hs).2.2 p hp
    exact ⟨r, hr.trans hT, o, ho⟩⟩

/-- Building blocks of `ΠbSM` from Theorems 8 and 9. -/
noncomputable def mkLData {tL : ℕ} (hBA : OmissionBA k tL) (hBB : OmissionBB k tL) : LData k tL :=
  let ba := hBA (Pref k)
  let bb := fun s => hBB (Pref k) s
  { M := Sum.elim (fun s => (bb s).choose) (fun _ => ba.choose)
    alg := fun i => match i with
      | inl s => (bb s).choose_spec.choose
      | inr _ => ba.choose_spec.choose
    T := ba.choose_spec.choose_spec.choose ⊔
      Finset.univ.sup fun s => (bb s).choose_spec.choose_spec.choose
    solves := fun i => match i with
      | inl s => SolvesWithOmissions.mono
          (le_sup_of_le_right (Finset.le_sup (f := fun s => (bb s).choose_spec.choose_spec.choose)
            (Finset.mem_univ s)))
          (bb s).choose_spec.choose_spec.choose_spec
      | inr _ => SolvesWithOmissions.mono le_sup_left ba.choose_spec.choose_spec.choose_spec }

/-! ## Lemma 9 -/

/-- **Lemma 9** (also on the one-sided network): with signatures, `tL < k/3` suffices for bSM in a
bipartite (or one-sided) network, whatever `tR` — assuming Theorems 8 and 9. -/
theorem lemma9 {tL tR : ℕ} (G' : SimpleGraph (Party k)) (hG' : G' = bipartite k ∨ G' = oneSided k)
    (h3 : 3 * tL < k) (hBA : OmissionBA k tL) (hBB : OmissionBB k tL) :
    SolvableAuth G' (thresholds k tL tR) (bSM k) := by
  set D := mkLData hBA hBB
  have hbip : bipartite k ≤ G' := by
    rcases hG' with rfl | rfl
    · exact le_rfl
    · exact bipartite_le_oneSided
  have hsame : ∀ u v, (oneSidedR k).Adj u v → ¬ G'.Adj u v → u.isLeft ∧ v.isLeft := by
    intro u v huv hn
    rcases hG' with rfl | rfl <;> rcases u with i | i <;> rcases v with j | j <;> simp_all
  have hRel := otherSide_rel (oneSidedR k) G' hbip
    (fun u v h1 h2 => by rw [(hsame u v h1 h2).1, (hsame u v h1 h2).2])
  refine ⟨_, _, (Auth.none (Party k) (Msg k (LMsg D))).relay, (phi D).relay (oneSidedR k) G'
    (sigRule otherSide), (Protocol.unforging_none _).relay _ (sigRule_sound _),
    fun s' hZ hrel hav => relay_sig_omissions _ (phi D) hRel bSM_honestOnly ?_ s' hZ hrel hav⟩
  intro s hZs _ hdrop
  have hZk : s.byz ∈ thresholds k tL k := ⟨hZs.1, ncard_preimage_le _ _⟩
  refine phi_bSM D h3 hZk (fun r p q hd => hsame p q (hdrop r p q hd).2.2.1 (hdrop r p q hd).2.2.2.1)
    (fun ⟨j, hj⟩ r p q hd => ?_)
  obtain ⟨-, -, h1, h2, hall⟩ := hdrop r p q hd
  have hpL := (hsame p q h1 h2).1
  apply hj (hall (inr j) _)
  simp [otherSide, hpL, inrEmb]

/-! ## Theorems -/

/-- **Theorem 2** (for `k ≥ 2`; false for `k = 1`, see `theorem2_only_if_false_k1`): bSM is solvable
in a fully-connected unauthenticated network iff `tL < k/3` or `tR < k/3` (sufficiency assuming the
Fitzi–Maurer theorem). -/
theorem theorem2 (hFM : FitziMaurerBB) {tL tR : ℕ} (hk : 2 ≤ k) :
    Solvable (fully k) (thresholds k tL tR) (bSM k) ↔ 3 * tL < k ∨ 3 * tR < k := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact bSM_not_solvable_third _ hk hc.1 hc.2 h
  · intro h
    exact lemma1 fun s => lemma4 hFM h _ s

/-- Lemma 6 / Corollary 2: in a bipartite unauthenticated network with `tL, tR < k/2` we may assume a
fully-connected network. -/
theorem corollary2 {tL tR : ℕ} (hL : 2 * tL < k) (hR : 2 * tR < k)
    (h : Solvable (fully k) (thresholds k tL tR) (bSM k)) :
    Solvable (bipartite k) (thresholds k tL tR) (bSM k) := by
  refine Solvable.relay_majority (Rel := otherSide) (otherSide_rel _ _ le_rfl ?_) ?_
    bSM_honestOnly h
  · intro u v _ hn; simpa using hn
  · intro B hB u v _ _ _ hn
    have hs : u.isLeft = v.isLeft := by simpa using hn
    unfold otherSide
    split_ifs
    · rw [card_filter_map_inr, Finset.card_map, Finset.card_univ, Fintype.card_fin]; have := hB.2; omega
    · rw [card_filter_map_inl, Finset.card_map, Finset.card_univ, Fintype.card_fin]; have := hB.1; omega

/-- Corollary 1 (corrected: the condition is `tR < k/2`): in a one-sided unauthenticated network with
`tR < k/2` we may assume a fully-connected network. -/
theorem corollary1 {tL tR : ℕ} (hR : 2 * tR < k)
    (h : Solvable (fully k) (thresholds k tL tR) (bSM k)) :
    Solvable (oneSided k) (thresholds k tL tR) (bSM k) := by
  have hsame : ∀ u v, (fully k).Adj u v → ¬ (oneSided k).Adj u v → u.isLeft ∧ v.isLeft := by
    intro u v h1 h2; rcases u with i | i <;> rcases v with j | j <;> simp_all
  refine Solvable.relay_majority (Rel := otherSide)
    (otherSide_rel _ _ bipartite_le_oneSided ?_) ?_ bSM_honestOnly h
  · intro u v h1 h2; rw [(hsame u v h1 h2).1, (hsame u v h1 h2).2]
  · intro B hB u v _ _ h1 h2
    unfold otherSide
    rw [ite_eq_left (hsame u v h1 h2).1, card_filter_map_inr, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
    have := hB.2; omega

/-- **Theorem 3** (for `k ≥ 2`): bSM is solvable in a bipartite unauthenticated network iff
(i) `tL, tR < k/2` and (ii) `tL < k/3` or `tR < k/3`. -/
theorem theorem3 (hFM : FitziMaurerBB) {tL tR : ℕ} (hk : 2 ≤ k) :
    Solvable (bipartite k) (thresholds k tL tR) (bSM k) ↔
      (2 * tL < k ∧ 2 * tR < k) ∧ (3 * tL < k ∨ 3 * tR < k) := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_contra hc; push Not at hc
      exact bSM_not_solvable_halfL _ (fun j j' => by simp) hk hc h
    · by_contra hc; push Not at hc
      exact bSM_not_solvable_halfR _ (fun i i' => by simp) hk hc h
    · by_contra hc; push Not at hc
      exact bSM_not_solvable_third _ hk hc.1 hc.2 h
  · rintro ⟨⟨hL, hR⟩, h⟩
    exact corollary2 hL hR ((theorem2 hFM hk).2 h)

/-- **Theorem 4** (for `k ≥ 2`): bSM is solvable in a one-sided unauthenticated network iff
(i) `tR < k/2` and (ii) `tL < k/3` or `tR < k/3`. -/
theorem theorem4 (hFM : FitziMaurerBB) {tL tR : ℕ} (hk : 2 ≤ k) :
    Solvable (oneSided k) (thresholds k tL tR) (bSM k) ↔
      2 * tR < k ∧ (3 * tL < k ∨ 3 * tR < k) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc; push Not at hc
      exact bSM_not_solvable_halfR _ (fun i i' => by simp) hk hc h
    · by_contra hc; push Not at hc
      exact bSM_not_solvable_third _ hk hc.1 hc.2 h
  · rintro ⟨hR, h⟩
    exact corollary1 hR ((theorem2 hFM hk).2 h)

/-- **Theorem 5**: bSM is solvable in a fully-connected authenticated network (against any adversary
structure), assuming Dolev–Strong. -/
theorem theorem5 (hDS : DolevStrongBB) (Z : AdvStructure (Party k)) :
    SolvableAuth (fully k) Z (bSM k) :=
  lemma1_auth fun s => hDS (Party k) _ Z s

/-- Lemma 8 / Corollaries 3, 4: with signatures, a side whose pairs are disconnected may be assumed
fully connected as long as the other side has an honest party. -/
theorem corollary34 {tL tR : ℕ} (G' : SimpleGraph (Party k)) (hG' : bipartite k ≤ G')
    (hL : ∀ i i', ¬ G'.Adj (inl i) (inl i') → tR < k)
    (hR : ∀ j j', j ≠ j' → ¬ G'.Adj (inr j) (inr j') → tL < k)
    (h : SolvableAuth (fully k) (thresholds k tL tR) (bSM k)) :
    SolvableAuth G' (thresholds k tL tR) (bSM k) := by
  have hsame : ∀ u v, (fully k).Adj u v → ¬ G'.Adj u v → u.isLeft = v.isLeft := by
    intro u v h1 h2
    by_contra hc
    exact h2 (hG' (by simpa using hc))
  refine SolvableAuth.relay_sig (Rel := otherSide) (otherSide_rel _ _ hG' hsame) ?_
    bSM_honestOnly h
  intro B hB u v _ _ h1 h2
  have hs := hsame u v h1 h2
  unfold otherSide
  rcases u with i | j <;> rcases v with i' | j'
  · have := hL i i' h2
    have hc := hB.2
    by_contra hcon
    push Not at hcon
    have : (inr ⁻¹' B : Set (Fin k)) = Set.univ := by
      ext j; simpa [inrEmb] using hcon (inr j)
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hc
    omega
  · simp at hs
  · simp at hs
  · have hne : j ≠ j' := fun e => h1.ne (by rw [e])
    have := hR j j' hne h2
    have hc := hB.1
    by_contra hcon
    push Not at hcon
    have : (inl ⁻¹' B : Set (Fin k)) = Set.univ := by
      ext i; simpa [inlEmb] using hcon (inl i)
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hc
    omega

/-- **Theorem 6** (for `k ≥ 2`): bSM is solvable in a bipartite authenticated network iff
(i) `tL, tR < k` or (ii) `tL < k/3` or `tR < k/3` (sufficiency assuming Dolev–Strong and
Theorems 8, 9). -/
theorem theorem6 (hDS : DolevStrongBB) (hOm : ∀ t, 3 * t < k → OmissionBA k t ∧ OmissionBB k t)
    {tL tR : ℕ} (hk : 2 ≤ k) :
    SolvableAuth (bipartite k) (thresholds k tL tR) (bSM k) ↔
      (tL < k ∧ tR < k) ∨ (3 * tL < k ∨ 3 * tR < k) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2, h3⟩ := hc
    by_cases hR : k ≤ tR
    · exact bSM_not_solvableAuth_R _ (fun i i' => by simp) hk h2 hR h
    · have hL : k ≤ tL := by
        by_contra hc; exact hR (h1 (by omega))
      exact bSM_not_solvableAuth_L _ (fun j j' => by simp) hk h3 hL h
  · rintro (⟨hL, hR⟩ | hL | hR)
    · exact corollary34 _ le_rfl (fun _ _ _ => hR) (fun _ _ _ _ => hL) (theorem5 hDS _)
    · exact lemma9 _ (Or.inl rfl) hL (hOm tL hL).1 (hOm tL hL).2
    · have := bSM_solvableAuth_swap (lemma9 (tR := tL) _ (Or.inl rfl) hR (hOm tR hR).1 (hOm tR hR).2)
      rwa [bipartite_comap_swap] at this

/-- **Theorem 7** (for `k ≥ 2`): bSM is solvable in a one-sided authenticated network iff `tR < k` or
`tL < k/3` (sufficiency assuming Dolev–Strong and Theorems 8, 9). The paper's proof of the case
`tR = k, tL < k/3` cites Theorem 4, which does not apply; we use `ΠbSM` (Lemma 9) instead. -/
theorem theorem7 (hDS : DolevStrongBB) (hOm : ∀ t, 3 * t < k → OmissionBA k t ∧ OmissionBB k t)
    {tL tR : ℕ} (hk : 2 ≤ k) :
    SolvableAuth (oneSided k) (thresholds k tL tR) (bSM k) ↔ tR < k ∨ 3 * tL < k := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact bSM_not_solvableAuth_R _ (fun i i' => by simp) hk hc.2 hc.1 h
  · rintro (hR | hL)
    · refine corollary34 _ bipartite_le_oneSided (fun _ _ _ => hR) (fun j j' hne hn => ?_)
        (theorem5 hDS _)
      exact absurd ⟨by simpa using hne, Or.inl rfl⟩ hn
    · exact lemma9 _ (Or.inr rfl) hL (hOm tL hL).1 (hOm tL hL).2

end Papers.PODC2025.ByzantineStableMatching
