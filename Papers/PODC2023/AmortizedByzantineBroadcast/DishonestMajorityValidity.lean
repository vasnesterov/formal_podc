import Papers.PODC2023.AmortizedByzantineBroadcast.DishonestMajorityBasic

/-!
# Section 5 of [WXMRS23]: TrustCast integrity and Lemma 4 (validity) of Algorithm 5.2

Under the charitable reading (`Reading.charitable`: graph maintenance in every round, equivocation
evidence of every slot), for the whole multi-slot execution with one shared trust graph per node:

* `gacc_transfer` — transferability (TrustCast property 1) at the level of the graph used for
  accusing by distance: for honest `x`, edges of `G_u` after round `r + 1` are edges of `G_x` after
  round `r` (restricted to `u`'s component);
* `good_out` — integrity: every atom an honest node multicasts and that is signed by an honest node
  is *good*: proposals of an honest sender carry its input, honest nodes never accuse honest nodes
  (TrustCast property 3) and never vote for the corruption of honest nodes;
* `honest_edges` — hence honest nodes never remove the edge between two honest nodes;
* `validity` — Lemma 4.
-/

namespace Podc.AmortizedByzantineBroadcast.DishonestMajority

open SimpleGraph

variable {N V : Type*} [Fintype N] (P : Setup N V) {H : Set N} {adv : ℕ → N → Set (Msg N V)}

namespace Setup

/-! ### Removal and forwarding -/

lemma processed_charitable (hR : P.R = Reading.charitable) {u : N} {r : ℕ} {G : SimpleGraph N}
    {K : Set (Msg N V)} {a b : N} :
    P.processed u r G K a b ↔ Msg.accuse a b ∈ K ∧ G.Reachable u a ∧ G.Reachable u b := by
  simp [processed, hR, Reading.charitable]

lemma equivocated_charitable (hR : P.R = Reading.charitable) {r : ℕ} {K : Set (Msg N V)} {j : ℕ} :
    P.equivocated r K j ↔ ∃ m m', m ≠ m' ∧ Msg.prop m j ∈ K ∧ Msg.prop m' j ∈ K := by
  simp [equivocated, hR, Reading.charitable]

/-- A known accusation between two vertices of `G_u` removes the edge. -/
lemma not_adj_Gacc_of_accuse (hR : P.R = Reading.charitable) {u p q : N} {r : ℕ}
    (hk : Msg.accuse p q ∈ (P.cfg H adv (r + 1) u).know)
    (hp : (P.cfg H adv r u).G.Reachable u p) (hq : (P.cfg H adv r u).G.Reachable u q) :
    ¬ (P.Gacc H adv u r).Adj p q := by
  unfold Gacc G1
  rw [deleteEdges_adj]
  rintro ⟨-, h⟩
  exact h ⟨p, q, (P.processed_charitable hR).2 ⟨hk, hp, hq⟩, rfl⟩

/-- A known equivocation of `S_j` removes all edges at `S_j`. -/
lemma not_adj_G_of_equiv (hR : P.R = Reading.charitable) {u : N} {r j : ℕ} {m m' : V}
    (hne : m ≠ m') (hm : Msg.prop m j ∈ (P.cfg H adv (r + 1) u).know)
    (hm' : Msg.prop m' j ∈ (P.cfg H adv (r + 1) u).know) {a b : N} (hab : P.S j = a ∨ P.S j = b) :
    ¬ (P.cfg H adv (r + 1) u).G.Adj a b := by
  rw [G_succ]
  unfold G2
  rw [deleteEdges_adj]
  rintro ⟨-, h⟩
  refine h ⟨j, (P.equivocated_charitable hR).2 ⟨m, m', hne, hm, hm'⟩, ?_⟩
  rcases hab with h | h <;> simp [h]

lemma out_of_processed (hR : P.R = Reading.charitable) {x p q : N} {r : ℕ}
    (hk : Msg.accuse p q ∈ (P.cfg H adv (r + 1) x).know)
    (hp : (P.cfg H adv r x).G.Reachable x p) (hq : (P.cfg H adv r x).G.Reachable x q) :
    Msg.accuse p q ∈ (P.cfg H adv (r + 1) x).out := by
  rw [out_succ]
  exact Or.inl ⟨p, q, rfl, (P.processed_charitable hR).2 ⟨hk, hp, hq⟩⟩

lemma out_of_equiv {x : N} {r j : ℕ} {m : V} (hm : Msg.prop m j ∈ (P.cfg H adv (r + 1) x).know)
    (hj : P.equivocated r (P.cfg H adv (r + 1) x).know j) :
    Msg.prop m j ∈ (P.cfg H adv (r + 1) x).out := by
  rw [out_succ]
  exact Or.inr (Or.inl ⟨m, j, rfl, hm, hj⟩)

/-! ### Transferability -/

/-- Transferability (TrustCast property 1), at the level of the graphs used for accusing by
distance: for honest `x` and any `u`, an edge of `u`'s graph after processing the accusations of
round `r + 1`, between two vertices of `G_u` (after round `r`), is an edge of `x`'s graph after
processing the accusations of round `r`. -/
theorem gacc_transfer (hR : P.R = Reading.charitable) {x : N} (hx : x ∈ H) (u : N) :
    ∀ r a b, (P.cfg H adv (r + 1) u).G.Reachable u a → (P.cfg H adv (r + 1) u).G.Reachable u b →
      (P.Gacc H adv u (r + 1)).Adj a b → (P.Gacc H adv x r).Adj a b := by
  have key : ∀ r a b, (P.cfg H adv (r + 1) u).G.Reachable u a →
      (P.cfg H adv (r + 1) u).G.Reachable u b → (P.Gacc H adv u (r + 1)).Adj a b →
      (P.cfg H adv r x).G.Adj a b → (P.Gacc H adv x r).Adj a b := by
    intro r a b ha hb hab hprev
    unfold Gacc G1
    rw [deleteEdges_adj]
    refine ⟨hprev, ?_⟩
    rintro ⟨p, q, hpq, he⟩
    rw [P.processed_charitable hR] at hpq
    have hk := P.deliver hx u (P.out_of_processed hR hpq.1 hpq.2.1 hpq.2.2)
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      exact P.not_adj_Gacc_of_accuse hR hk ha hb hab
    · subst h1 h2
      exact P.not_adj_Gacc_of_accuse hR hk hb ha hab.symm
  intro r
  induction r with
  | zero =>
    intro a b ha hb hab
    exact key 0 a b ha hb hab (by simp [cfg_zero, State.init, hab.ne])
  | succ r ih =>
    intro a b ha hb hab
    refine key (r + 1) a b ha hb hab ?_
    have ha' := ha.mono (P.G_succ_le u (r + 1))
    have hb' := hb.mono (P.G_succ_le u (r + 1))
    have hab' : (P.Gacc H adv u (r + 1)).Adj a b :=
      (P.G_succ_le_Gacc u (r + 1)) ((P.Gacc_le u (r + 2)) hab)
    rw [G_succ]
    unfold G2
    rw [deleteEdges_adj]
    refine ⟨ih a b ha' hb' hab', ?_⟩
    rintro ⟨j, hj, hSj⟩
    have hj' := hj
    rw [P.equivocated_charitable hR] at hj'
    obtain ⟨m, m', hne, hm, hm'⟩ := hj'
    have hk := P.deliver hx u (P.out_of_equiv hm hj)
    have hk' := P.deliver hx u (P.out_of_equiv hm' hj)
    have hS : P.S j = a ∨ P.S j = b := Sym2.mem_iff.mp hSj
    exact P.not_adj_G_of_equiv hR hne hk hk' hS ((P.Gacc_le u (r + 2)) hab)

/-! ### A walk lemma -/

omit [Fintype N] in
/-- Transport a walk along an edge-inclusion that is only known inside the component of `u`. -/
lemma exists_walk_transfer {G G' G'' : SimpleGraph N} {u : N} (hle : G ≤ G')
    (hT : ∀ a b, G'.Reachable u a → G'.Reachable u b → G.Adj a b → G''.Adj a b) :
    ∀ {x y : N} (p : G.Walk x y), G'.Reachable u x → ∃ q : G''.Walk x y, q.length = p.length
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, .cons h p, hux => by
    have hz := hux.trans (hle h).reachable
    obtain ⟨q, hq⟩ := exists_walk_transfer hle hT p hz
    exact ⟨.cons (hT _ _ hux hz h) q, by simp [hq]⟩

/-! ### Integrity -/

/-- The core of TrustCast integrity: if the sender of the current slot is Byzantine, an honest `u`
cannot accuse (by distance) an honest `x` that is in `G_u`. -/
theorem accuse_absurd (hR : P.R = Reading.charitable) {u x : N} (hx : x ∈ H) {r : ℕ}
    (ht1 : 1 ≤ P.loc r) (htn : P.loc r ≤ P.n)
    (hnp : ¬ HasProp (P.cfg H adv (r + 1) u).know (P.slot r))
    (hd : (P.Gacc H adv u r).edist x (P.S (P.slot r)) < P.loc r)
    (hS : P.S (P.slot r) ∉ H) (hux : (P.cfg H adv r u).G.Reachable u x) : False := by
  have hxs : x ≠ P.S (P.slot r) := fun h => hS (h ▸ hx)
  obtain ⟨p, hp⟩ := (reachable_of_edist_ne_top (ne_top_of_lt hd)).exists_walk_length_eq_edist
  cases p with
  | nil => exact hxs rfl
  | @cons _ z _ h q =>
    have hlen : q.length + 1 < P.loc r := by
      rw [← hp] at hd
      simp only [Walk.length_cons] at hd
      exact_mod_cast hd
    obtain ⟨r0, rfl⟩ : ∃ r0, r = r0 + 1 := ⟨r - 1, by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp [loc] at ht1
      · omega⟩
    have hsl : P.slot r0 = P.slot (r0 + 1) := by
      simpa using P.slot_pred (r := r0 + 1) ht1
    have hlc : P.loc r0 = P.loc (r0 + 1) - 1 := by
      simpa using P.loc_pred (r := r0 + 1) ht1
    have hT := P.gacc_transfer (adv := adv) hR hx u r0
    have hz : (P.cfg H adv (r0 + 1) u).G.Reachable u z := hux.trans ((P.Gacc_le u _) h).reachable
    have hxz : (P.Gacc H adv x r0).Adj x z := hT x z hux hz h
    obtain ⟨q', hq'⟩ := exists_walk_transfer (P.Gacc_le u (r0 + 1)) hT q hz
    have hdz : (P.Gacc H adv x r0).edist z (P.S (P.slot r0)) ≤ q.length := by
      rw [hsl, ← hq']; exact edist_le q'
    have hnpx : ¬ HasProp (P.cfg H adv (r0 + 1) x).know (P.slot r0) := by
      rintro ⟨m, hm⟩
      apply hnp ⟨m, ?_⟩
      have : Msg.prop m (P.slot r0) ∈ (P.cfg H adv (r0 + 1) x).out := by
        rw [out_succ]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl, hm, by omega, by omega⟩)))
      rw [← hsl]
      exact P.deliver hx u this
    have hacc : Msg.accuse z x ∈ (P.cfg H adv (r0 + 1) x).out := by
      rw [out_succ]
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨z, rfl, by omega, by omega, hnpx, hxz.reachable, ?_⟩))))
      refine lt_of_le_of_lt hdz ?_
      rw [hlc]
      exact_mod_cast (by omega : q.length < P.loc (r0 + 1) - 1)
    exact P.not_adj_Gacc_of_accuse hR (P.deliver hx u hacc) hz hux h.symm

/-- Atoms signed by an honest node are *good*: an honest sender's proposals carry its input, and
honest nodes neither accuse nor vote against honest nodes. -/
def Good (H : Set N) : Msg N V → Prop
  | .prop m j => m = P.input j
  | .accuse x _ => x ∉ H
  | .corrupt v _ => v ∉ H

/-- All honestly signed atoms multicast by honest nodes in round `r` are good. -/
def GoodOut (H : Set N) (adv : ℕ → N → Set (Msg N V)) (r : ℕ) : Prop :=
  ∀ w ∈ H, ∀ a ∈ (P.cfg H adv (r + 1) w).out, a.signer P.S ∈ H → P.Good H a

lemma good_know (hadv : P.AdvValid H adv) {r : ℕ} (hg : ∀ r', r' + 1 < r → P.GoodOut H adv r')
    {v : N} (hv : v ∈ H) {a : Msg N V} (ha : a ∈ (P.cfg H adv r v).know)
    (hs : a.signer P.S ∈ H) : P.Good H a := by
  obtain ⟨r', h1, h2⟩ := P.origin hadv r v hv a ha hs
  exact hg r' h1 _ hs a h2 hs

/-- If all honestly signed atoms are good so far, honest nodes keep all edges between honest
nodes (holds for every reading). -/
theorem honest_edges (hadv : P.AdvValid H adv) :
    ∀ r, (∀ r', r' + 1 < r → P.GoodOut H adv r') →
      ∀ u ∈ H, ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (P.cfg H adv r u).G.Adj a b := by
  intro r
  induction r with
  | zero => intro _ u _ a _ b _ hab; simpa [cfg_zero, State.init] using hab
  | succ r ih =>
    intro hg u hu a ha b hb hab
    rw [G_succ]
    unfold G2 G1
    simp only [deleteEdges_adj]
    refine ⟨⟨ih (fun r' h => hg r' (by omega)) u hu a ha b hb hab, ?_⟩, ?_⟩
    · rintro ⟨p, q, ⟨-, hk, -, -⟩, he⟩
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2
        exact (P.good_know hadv hg hu hk hb : a ∉ H) ha
      · subst h1 h2
        exact (P.good_know hadv hg hu hk ha : b ∉ H) hb
    · rintro ⟨j, ⟨-, -, m, m', hne, hm, hm'⟩, hSj⟩
      have hSH : P.S j ∈ H := by
        rcases Sym2.mem_iff.mp hSj with h | h <;> rw [h] <;> assumption
      have e1 : m = P.input j := P.good_know hadv hg hu hm hSH
      have e2 : m' = P.input j := P.good_know hadv hg hu hm' hSH
      exact hne (e1.trans e2.symm)

/-- Integrity of TrustCast in the multi-slot execution (charitable reading): every honestly
signed atom multicast by an honest node is good. In particular honest nodes never accuse honest
nodes (TrustCast property 3) and never vote for the corruption of an honest node. -/
theorem good_out (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv) :
    ∀ r, P.GoodOut H adv r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro w hw a ha hs
    rw [out_succ] at ha
    rcases P.out_cases ha with hk | ⟨rfl, -, -⟩ | ⟨x, rfl, ht1, htn, hnp, -, hd⟩ | ⟨rfl, hds⟩
    · exact P.good_know hadv (fun r' h => ih r' (by omega)) hw hk hs
    · rfl
    · show x ∉ H
      intro hxH
      have hS : P.S (P.slot r) ∉ H := by
        intro hSH
        apply hnp
        refine ⟨_, P.deliver_le hSH w ?_ (P.sender_out (P.slot r))⟩
        have := P.slot_mul_add r
        omega
      have hux : (P.cfg H adv r w).G.Reachable w x := by
        by_cases hxw : x = w
        · subst hxw; rfl
        · exact (P.honest_edges hadv r (fun r' h => ih r' (by omega)) w hw w hw x hxH
            (Ne.symm hxw)).reachable
      exact P.accuse_absurd hR hxH ht1 htn hnp hd hS hux
    · show P.S (P.slot r) ∉ H
      intro hSH
      apply hds.2.2.1
      by_cases hSw : P.S (P.slot r) = w
      · rw [hSw]
      · exact (P.honest_edges hadv (r + 1) (fun r' h => ih r' (by omega)) w hw w hw _ hSH
          (Ne.symm hSw)).reachable

/-- Integrity, as stated in the paper (TrustCast property 3): honest nodes never remove the edge
between two honest nodes from their trust graphs (charitable reading, whole multi-slot
execution). -/
theorem integrity (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv) (r : ℕ)
    {u a b : N} (hu : u ∈ H) (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) :
    (P.cfg H adv r u).G.Adj a b :=
  P.honest_edges hadv r (fun r' _ => P.good_out hR hadv r') u hu a ha b hb hab

/-- Honest nodes never accuse honest nodes (charitable reading). -/
theorem honest_never_accuses_honest (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv)
    (r : ℕ) {u x : N} (hu : u ∈ H) (hx : x ∈ H) :
    Msg.accuse x u ∉ (P.cfg H adv (r + 1) u).out :=
  fun h => (P.good_out hR hadv r u hu _ h hu : x ∉ H) hx

/-- **Lemma 4 (Validity) of [WXMRS23]**, for every slot of the multi-shot execution (charitable
reading): if the sender `S_k` of slot `k` is honest, every honest node commits `S_k`'s message at
slot `k`. No bound on the number of Byzantine nodes is needed. -/
theorem validity (hR : P.R = Reading.charitable) (hadv : P.AdvValid H adv) (k : ℕ)
    (hS : P.S k ∈ H) {u : N} (hu : u ∈ H) : P.commit H adv u k = some (P.input k) := by
  have hgood := P.good_out hR hadv
  have hnv : ¬ P.Voted H adv u (P.S k) (k * P.T + (P.n + P.f + 2)) := by
    rintro ⟨r', -, h⟩
    exact (hgood r' u hu _ h hu : P.S k ∉ H) hS
  have hn : 1 ≤ P.n := Fintype.card_pos_iff.mpr ⟨u⟩
  have hprop : Msg.prop (P.input k) k ∈ (P.cfg H adv (k * P.T + P.n + 1) u).know :=
    P.deliver_le hS u (by omega) (P.sender_out k)
  have hhp : HasProp (P.cfg H adv (k * P.T + P.n + 1) u).know k := ⟨_, hprop⟩
  rw [commit, ite_eq_right_of_eq_false _ _ (eq_false hnv), dite_eq_left_of_eq_true (eq_true hhp)]
  exact congrArg some (P.good_know hadv (fun r' _ => hgood r') hu hhp.choose_spec hS)

end Setup

end Podc.AmortizedByzantineBroadcast.DishonestMajority
