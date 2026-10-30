import Papers.PODC2023.AmortizedByzantineBroadcast.DishonestMajorityValidity

/-!
# Section 5 of [WXMRS23]: TrustCast termination/transferability and Lemma 5 (consistency)

Charitable reading (`Reading.charitable`), whole multi-slot execution, `|N \ H| ≤ f`.

* `dist_invariant`, `termination` — TrustCast property 2: an honest node that has no proposal of
  slot `k` by the end of round `n` of the slot has disconnected `S_k`;
* `transferability` — TrustCast property 1: for honest `u, v`, `G_v` after round `r + 1` is a
  subgraph of `G_u` after round `r`; `not_reachable_transfer` is the form used for `S_k ∉ G_u`;
* `vote_spread`, `voted_spread` — the Dolev–Strong argument: if an honest node votes for the
  corruption of `c` during a slot, all honest nodes have voted by the end of that slot;
* `consistency` — Lemma 5.
-/

namespace Podc.AmortizedByzantineBroadcast.DishonestMajority

open SimpleGraph

variable {N V : Type*} [Fintype N] (P : Setup N V) {H : Set N} {adv : ℕ → N → Set (Msg N V)}

namespace Setup

/-! ### Graph lemmas -/

omit [Fintype N] in
lemma succ_le_edist_of_adj {G : SimpleGraph N} {u s : N} {t : ℕ∞} (hus : u ≠ s)
    (h : ∀ y, G.Adj u y → t ≤ G.edist y s) : t + 1 ≤ G.edist u s := by
  by_cases hr : G.Reachable u s
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    cases p with
    | nil => exact absurd rfl hus
    | cons hadj q =>
      rw [← hp, Walk.length_cons]
      push_cast
      exact add_le_add_left ((h _ hadj).trans (edist_le q)) 1
  · rw [edist_eq_top_of_not_reachable hr]
    exact le_top

omit [Fintype N] in
lemma not_reachable_of_isolated {G : SimpleGraph N} {v c : N} (hvc : v ≠ c)
    (h : ∀ a, ¬ G.Adj a c) : ¬ G.Reachable v c := by
  intro hr
  obtain ⟨p⟩ := hr.symm
  cases p with
  | nil => exact hvc rfl
  | cons hadj _ => exact h _ hadj.symm

lemma edist_lt_card_of_reachable {G : SimpleGraph N} {a b : N} (h : G.Reachable a b) :
    G.edist a b < Fintype.card N := by
  classical
  obtain ⟨p⟩ := h
  calc G.edist a b ≤ p.bypass.length := edist_le _
    _ < Fintype.card N := by exact_mod_cast p.bypass_isPath.length_lt

/-! ### TrustCast termination -/

/-- The distance invariant behind TrustCast termination: if honest `u` has no proposal of the
current slot in round `t ∈ [1, n]`, then `u` is at distance `≥ t` from the sender in its graph. -/
theorem dist_invariant (hR : P.R = Reading.charitable) {u : N} (hu : u ∈ H) {r : ℕ}
    (ht1 : 1 ≤ P.loc r) (htn : P.loc r ≤ P.n)
    (hnp : ¬ HasProp (P.cfg H adv (r + 1) u).know (P.slot r)) :
    (P.loc r : ℕ∞) ≤ (P.Gacc H adv u r).edist u (P.S (P.slot r)) := by
  have hus : u ≠ P.S (P.slot r) := by
    intro h
    apply hnp
    refine ⟨_, P.deliver_le (h ▸ hu) u ?_ (P.sender_out (P.slot r))⟩
    have := P.slot_mul_add r
    omega
  rcases Nat.lt_or_ge (P.loc r) 2 with h1 | h2
  · have : P.loc r = 1 := by omega
    rw [this, Nat.cast_one]
    exact Order.one_le_iff_pos.mpr (edist_pos_of_ne hus)
  · obtain ⟨r0, rfl⟩ : ∃ r0, r = r0 + 1 := ⟨r - 1, by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp [loc] at ht1
      · omega⟩
    have hsl : P.slot r0 = P.slot (r0 + 1) := by
      simpa using P.slot_pred (r := r0 + 1) ht1
    have hlc : P.loc r0 = P.loc (r0 + 1) - 1 := by
      simpa using P.loc_pred (r := r0 + 1) ht1
    have hle : P.Gacc H adv u (r0 + 1) ≤ P.Gacc H adv u r0 :=
      (P.Gacc_le u (r0 + 1)).trans (P.G_succ_le_Gacc u r0)
    have key : ∀ y, (P.Gacc H adv u (r0 + 1)).Adj u y →
        ((P.loc r0 : ℕ) : ℕ∞) ≤ (P.Gacc H adv u (r0 + 1)).edist y (P.S (P.slot (r0 + 1))) := by
      intro y hy
      refine le_trans ?_ (edist_anti hle)
      by_contra hlt
      push Not at hlt
      have hnp0 : ¬ HasProp (P.cfg H adv (r0 + 1) u).know (P.slot r0) := by
        rintro ⟨m, hm⟩
        exact hnp ⟨m, by rw [← hsl]; exact P.know_mono u (by omega) hm⟩
      have hacc : Msg.accuse y u ∈ (P.cfg H adv (r0 + 1) u).out := by
        rw [out_succ]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨y, rfl, by omega, by omega, hnp0, (hle hy).reachable, ?_⟩))))
        rw [hsl]; exact hlt
      exact P.not_adj_Gacc_of_accuse hR (P.deliver hu u hacc) ((P.Gacc_le u _) hy).reachable
        (Reachable.refl u) hy.symm
    have e : (P.loc (r0 + 1) : ℕ∞) = (P.loc r0 : ℕ∞) + 1 := by
      rw [hlc]; norm_cast; omega
    rw [e]
    exact succ_le_edist_of_adj hus key

/-- **TrustCast property 2 (termination)** in slot `k`: by the end of round `n` of the slot, an
honest node has received a proposal of slot `k` or has removed `S_k` from its trust graph. -/
theorem termination (hR : P.R = Reading.charitable) {u : N} (hu : u ∈ H) (k : ℕ) :
    HasProp (P.cfg H adv (k * P.T + P.n + 1) u).know k ∨
      ¬ (P.Gacc H adv u (k * P.T + P.n)).Reachable u (P.S k) := by
  by_cases hp : HasProp (P.cfg H adv (k * P.T + P.n + 1) u).know k
  · exact Or.inl hp
  · right
    intro hr
    have hn : 1 ≤ P.n := Fintype.card_pos_iff.mpr ⟨u⟩
    have hlt : P.n < P.T := by unfold T; omega
    have hs : P.slot (k * P.T + P.n) = k := P.slot_of_eq hlt
    have hl : P.loc (k * P.T + P.n) = P.n := P.loc_of_eq hlt
    have h := P.dist_invariant hR hu (r := k * P.T + P.n) (by omega) (by omega) (by rwa [hs])
    rw [hs, hl] at h
    exact absurd (lt_of_le_of_lt h (edist_lt_card_of_reachable hr)) (lt_irrefl _)

/-! ### Transferability -/

/-- **TrustCast property 1 (transferability)**: for honest `u` (and any `v`), the trust graph
`G_v` after round `r + 1` (the component of `v`) is a subgraph of `G_u` after round `r`. -/
theorem transferability (hR : P.R = Reading.charitable) {u : N} (hu : u ∈ H) (v : N) (r : ℕ)
    {a b : N} (ha : (P.cfg H adv (r + 2) v).G.Reachable v a)
    (hb : (P.cfg H adv (r + 2) v).G.Reachable v b) (hab : (P.cfg H adv (r + 2) v).G.Adj a b) :
    (P.cfg H adv (r + 1) u).G.Adj a b := by
  have ha' := ha.mono (P.G_succ_le v (r + 1))
  have hb' := hb.mono (P.G_succ_le v (r + 1))
  have hacc : (P.Gacc H adv v (r + 1)).Adj a b := P.G_succ_le_Gacc v (r + 1) hab
  have hg := P.gacc_transfer hR hu v r a b ha' hb' hacc
  rw [G_succ]
  unfold G2
  rw [deleteEdges_adj]
  refine ⟨hg, ?_⟩
  rintro ⟨j, hj, hSj⟩
  have hj' := hj
  rw [P.equivocated_charitable hR] at hj'
  obtain ⟨m, m', hne, hm, hm'⟩ := hj'
  have hk := P.deliver hu v (P.out_of_equiv hm hj)
  have hk' := P.deliver hu v (P.out_of_equiv hm' hj)
  exact P.not_adj_G_of_equiv hR hne hk hk' (Sym2.mem_iff.mp hSj) hab

/-- Vertex form of transferability: if `c ∉ G_u` after round `r`, then `c ∉ G_v` after round
`r + 1` (honest `u, v`). -/
theorem not_reachable_transfer (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv)
    {u v : N} (hu : u ∈ H) (hv : v ∈ H) (r : ℕ) {c : N}
    (h : ¬ (P.cfg H adv (r + 1) u).G.Reachable u c) : ¬ (P.cfg H adv (r + 2) v).G.Reachable v c := by
  rintro ⟨p⟩
  obtain ⟨q, -⟩ := exists_walk_transfer (G'' := (P.cfg H adv (r + 1) u).G) le_rfl
    (fun a b ha hb hab => P.transferability hR hu v r ha hb hab) p (Reachable.refl v)
  apply h
  refine Reachable.trans ?_ q.reachable
  by_cases huv : u = v
  · rw [huv]
  · exact (P.integrity hR hadv (r + 1) hu hu hv huv).reachable

/-! ### The Dolev–Strong phase -/

/-- If an honest node votes for the corruption of `c` in round `r`, every honest node votes for it in
some round `≤ r + 1`, and in some round `≤ r` if `r` is the last round of its slot. -/
theorem vote_spread (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv)
    (hf : Hᶜ.ncard ≤ P.f) :
    ∀ r, ∀ w ∈ H, ∀ c, Msg.corrupt c w ∈ (P.cfg H adv (r + 1) w).out → ∀ v ∈ H,
      ∃ r'' ≤ r + 1, Msg.corrupt c v ∈ (P.cfg H adv (r'' + 1) v).out ∧
        (P.loc r = P.n + P.f + 2 → r'' ≤ r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro w hw c hc v hv
    have early : ∀ r' < r, ∀ w' ∈ H, Msg.corrupt c w' ∈ (P.cfg H adv (r' + 1) w').out →
        ∃ r'' ≤ r + 1, Msg.corrupt c v ∈ (P.cfg H adv (r'' + 1) v).out ∧
          (P.loc r = P.n + P.f + 2 → r'' ≤ r) := by
      intro r' hr' w' hw' h
      obtain ⟨r'', h1, h2, -⟩ := ih r' hr' w' hw' c h v hv
      exact ⟨r'', by omega, h2, fun _ => by omega⟩
    have hc' := hc
    rw [out_succ] at hc'
    rcases P.out_cases hc' with hk | ⟨h, -⟩ | ⟨x, h, -⟩ | ⟨h, hds⟩
    · obtain ⟨r', h1, h2⟩ := P.origin hadv (r + 1) w hw _ hk hw
      exact early r' (by omega) w hw h2
    · cases h
    · cases h
    · injection h with hc1
      subst hc1
      have hds' := hds
      obtain ⟨hl1, hl2, hnr, hcnt⟩ := hds
      by_cases hlast : P.loc r = P.n + P.f + 2
      · obtain ⟨w', hw', hk⟩ : ∃ w' ∈ H,
            Msg.corrupt (P.S (P.slot r)) w' ∈ (P.cfg H adv (r + 1) w).know := by
          by_contra hcon
          push Not at hcon
          have hsub : {w' | Msg.corrupt (P.S (P.slot r)) w' ∈ (P.cfg H adv (r + 1) w).know} ⊆ Hᶜ :=
            fun w' hw' hH => hcon w' hH hw'
          have := Set.ncard_le_ncard hsub
          unfold nSigners at hcnt
          omega
        obtain ⟨r', h1, h2⟩ := P.origin hadv (r + 1) w hw _ hk hw'
        exact early r' (by omega) w' hw' h2
      · by_cases hprev : ∃ r' < r, Msg.corrupt (P.S (P.slot r)) w ∈ (P.cfg H adv (r' + 1) w).out
        · obtain ⟨r', hr', h⟩ := hprev
          exact early r' hr' w hw h
        · push Not at hprev
          refine ⟨r + 1, le_rfl, ?_, fun h => absurd h hlast⟩
          have hTl := P.loc_lt r
          have hTe : P.T = P.n + P.f + 3 := rfl
          have hsl : P.slot (r + 1) = P.slot r := P.slot_add (by omega)
          have hlc : P.loc (r + 1) = P.loc r + 1 := P.loc_add (by omega)
          have hwnot : Msg.corrupt (P.S (P.slot r)) w ∉ (P.cfg H adv (r + 1) w).know := by
            intro hk
            obtain ⟨r', h1, h2⟩ := P.origin hadv (r + 1) w hw _ hk hw
            exact hprev r' (by omega) h2
          rw [out_succ]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hsl], ?_⟩)))))
          refine ⟨by omega, by omega, ?_, ?_⟩
          · rw [hsl]
            exact P.not_reachable_transfer hR hadv hw hv r hnr
          · rw [hsl, hlc]
            unfold nSigners
            have hw1 : w ∈ {w' | Msg.corrupt (P.S (P.slot r)) w' ∈
                (P.cfg H adv (r + 1 + 1) v).know} := P.deliver hw v hc
            rcases Nat.lt_or_ge (P.loc r) (P.n + 2) with hτ | hτ
            · have := Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hw1)
              rw [Set.ncard_singleton] at this
              omega
            · have hsub : insert w {w' | Msg.corrupt (P.S (P.slot r)) w' ∈
                  (P.cfg H adv (r + 1) w).know} ⊆
                  {w' | Msg.corrupt (P.S (P.slot r)) w' ∈ (P.cfg H adv (r + 1 + 1) v).know} := by
                intro w' hw'
                rcases hw' with rfl | hw'
                · exact hw1
                · refine P.deliver hw v ?_
                  rw [out_succ]
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w', rfl, hw', hds', hτ⟩)))))
              have := Set.ncard_le_ncard hsub
              rw [Set.ncard_insert_of_notMem (show w ∉ {w' | Msg.corrupt (P.S (P.slot r)) w' ∈
                (P.cfg H adv (r + 1) w).know} from hwnot)] at this
              unfold nSigners at hcnt
              omega

/-- If an honest node has voted for the corruption of `c` by the last round `e` of a slot, so has
every honest node. -/
theorem voted_spread (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv)
    (hf : Hᶜ.ncard ≤ P.f) {u v : N} (hu : u ∈ H) (hv : v ∈ H) {c : N} {e : ℕ}
    (he : P.loc e = P.n + P.f + 2) (h : P.Voted H adv u c e) : P.Voted H adv v c e := by
  obtain ⟨r, hr, hc⟩ := h
  obtain ⟨r'', h1, h2, h3⟩ := P.vote_spread hR hadv hf r u hu c hc v hv
  refine ⟨r'', ?_, h2⟩
  rcases Nat.lt_or_ge r e with hlt | hge
  · omega
  · have : r = e := le_antisymm hr hge
    subst this
    exact h3 he

/-! ### Lemma 5 -/

/-- **Lemma 5 (Consistency) of [WXMRS23]**, for every slot of the multi-shot execution (charitable
reading, at most `f` Byzantine nodes): two honest nodes commit the same value (possibly `⊥`) at
slot `k`. -/
theorem consistency (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv)
    (hf : Hᶜ.ncard ≤ P.f) (k : ℕ) {u v : N} (hu : u ∈ H) (hv : v ∈ H) :
    P.commit H adv u k = P.commit H adv v k := by
  by_cases hS : P.S k ∈ H
  · rw [P.validity hR hadv k hS hu, P.validity hR hadv k hS hv]
  have hTe : P.T = P.n + P.f + 3 := rfl
  have hn : 1 ≤ P.n := Fintype.card_pos_iff.mpr ⟨u⟩
  have he : P.loc (k * P.T + (P.n + P.f + 2)) = P.n + P.f + 2 := P.loc_of_eq (by omega)
  by_cases hvu : P.Voted H adv u (P.S k) (k * P.T + (P.n + P.f + 2))
  · have hvv := P.voted_spread hR hadv hf hu hv he hvu
    simp only [commit, hvu, hvv, ↓reduceIte]
  by_cases hvv : P.Voted H adv v (P.S k) (k * P.T + (P.n + P.f + 2))
  · exact absurd (P.voted_spread hR hadv hf hv hu he hvv) hvu
  have hs1 : P.slot (k * P.T + P.n + 1) = k := by
    rw [add_assoc]; exact P.slot_of_eq (by omega)
  have hl1 : P.loc (k * P.T + P.n + 1) = P.n + 1 := by
    rw [add_assoc]; exact P.loc_of_eq (by omega)
  have reach : ∀ w ∈ H, ¬ P.Voted H adv w (P.S k) (k * P.T + (P.n + P.f + 2)) →
      (P.cfg H adv (k * P.T + P.n + 2) w).G.Reachable w (P.S k) := by
    intro w hw hnv
    by_contra hnr
    apply hnv
    refine ⟨k * P.T + P.n + 1, by omega, ?_⟩
    rw [out_succ]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hs1], ?_⟩)))))
    refine ⟨by omega, by omega, ?_, by rw [hl1]; omega⟩
    rw [hs1]
    exact hnr
  have prop_of : ∀ w ∈ H, ¬ P.Voted H adv w (P.S k) (k * P.T + (P.n + P.f + 2)) →
      HasProp (P.cfg H adv (k * P.T + P.n + 1) w).know k := by
    intro w hw hnv
    rcases P.termination hR hw k with h | h
    · exact h
    · exact absurd ((reach w hw hnv).mono ((P.G_anti w (by omega)).trans
        (P.G_succ_le_Gacc w (k * P.T + P.n)))) h
  have hpu := prop_of u hu hvu
  have hpv := prop_of v hv hvv
  rw [commit, commit, ite_eq_right_of_eq_false _ _ (eq_false hvu),
    ite_eq_right_of_eq_false _ _ (eq_false hvv), dite_eq_left_of_eq_true (eq_true hpu),
    dite_eq_left_of_eq_true (eq_true hpv)]
  congr 1
  by_contra hne
  have hs0 : P.slot (k * P.T + P.n) = k := P.slot_of_eq (by omega)
  have hl0 : P.loc (k * P.T + P.n) = P.n := P.loc_of_eq (by omega)
  have hfw : Msg.prop hpu.choose k ∈ (P.cfg H adv (k * P.T + P.n + 1) u).out := by
    rw [out_succ]
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hpu.choose, by rw [hs0], ?_, by omega, by omega⟩)))
    rw [hs0]; exact hpu.choose_spec
  have hk1 := P.deliver hu v hfw
  have hk2 := P.know_succ_sub v _ hpv.choose_spec
  have hvS : v ≠ P.S k := fun h => hS (h ▸ hv)
  exact not_reachable_of_isolated hvS
    (fun a hadj => P.not_adj_G_of_equiv hR (r := k * P.T + P.n + 1) hne hk1 hk2 (Or.inr rfl) hadj)
    (reach v hv hvv)

end Setup

end Podc.AmortizedByzantineBroadcast.DishonestMajority
