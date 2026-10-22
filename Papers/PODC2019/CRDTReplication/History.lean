import Papers.PODC2019.CRDTReplication.UpdInv

/-!
# Theorems 1, 2, 4, 5 (the claims relating learned states to the real-time order)

* Theorem 1 (Validity), Theorem 2 (Stability) and Theorem 5 (Update Visibility) hold for
  Algorithm 2 as written.
* Theorem 4 (Update Stability) holds for the repaired protocol (`Variant.fixed`); for the paper's
  protocol it is false (`Counterexample.lean`).

The history-dependent parts are proved by induction over executions, using that the relevant
facts are *established at the moment the earlier operation completes* (`Precedes h x y` with `y`
not yet invoked) and preserved afterwards (`GoodQ.step`, `Good4.step`).
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-! ## Learned records are written once, at the response -/

lemma learned_step (hcons : ∀ s t, V.cons s t = true → s = t)
    {C C' : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    {st : Step P D.spec (Msg P D) Act} {ℓ : Option (Label P D.spec)}
    (hr : (alg V QS).Reach C h) (hs : (alg V QS).step C st = some (C', ℓ)) (p : P) (k : ℕ) :
    (C'.loc p).learned k = (C.loc p).learned k ∨
      ((C.loc p).learned k = none ∧ ∃ r, ℓ = some (.ret p r) ∧ k = (respsOf h p).length) := by
  have hP := (procInv_of_reach hcons hr).2
  rcases reach_step_cases hr hs with ⟨hloc, -, -⟩ | ⟨q, l, out, htr, hloc, -⟩
  · rw [hloc]; exact Or.inl rfl
  · rw [hloc]
    by_cases hpq : p = q
    · subst hpq
      rw [Function.update_self]
      cases htr with
      | inv hst =>
        left; unfold invokeStep at hst; split at hst
        · rename_i o _ _; cases o <;> simp only [startAttempt, Option.some.injEq, Prod.mk.injEq] at hst <;>
            obtain ⟨rfl, rfl⟩ := hst <;> rfl
        · simp at hst
      | recv hm =>
        left; rename_i src m
        cases m <;> simp only [receiveStep] <;> (try split_ifs) <;> (try split) <;> (try split_ifs) <;> rfl
      | internal hst =>
        rename_i act r
        have hb := internalStep_busy hst
        have hlen := (hP p).busy hb
        have hnone : (C.loc p).learned (respsOf h p).length = none := by
          by_contra hne
          obtain ⟨⟨s, v⟩, hsv⟩ := Option.ne_none_iff_exists'.1 hne
          have := ((hP p).learned _ s v hsv).1
          simp only [Completed] at this; omega
        unfold internalStep at hst
        split at hst
        · split_ifs at hst
          simp only [Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl⟩ := hst; exact Or.inl rfl
        · rename_i q i acks hph
          obtain ⟨-, hi2, -⟩ := (hP p).ph_prep q i acks hph
          have hi : i.2.1 = (respsOf h p).length := by omega
          split_ifs at hst
          · simp only [Option.some.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl⟩ := hst
            by_cases hk : k = i.2.1
            · subst hk; rw [← hi] at hnone; exact Or.inr ⟨hnone, _, rfl, hi⟩
            · left; simp [Function.update_of_ne hk]
          · simp only [Option.some.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl⟩ := hst; exact Or.inl rfl
          · simp only [Option.some.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl⟩ := hst; exact Or.inl rfl
        · rename_i q i n s M hph
          obtain ⟨-, hi2, -⟩ := (hP p).ph_vote q i n s M hph
          have hi : i.2.1 = (respsOf h p).length := by omega
          split_ifs at hst
          simp only [Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl⟩ := hst
          by_cases hk : k = i.2.1
          · subst hk; rw [← hi] at hnone; exact Or.inr ⟨hnone, _, rfl, hi⟩
          · left; simp [Function.update_of_ne hk]
        · simp only [Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl⟩ := hst; exact Or.inl rfl
        · simp only [Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, rfl, rfl⟩ := hst; exact Or.inl rfl
        · simp at hst
    · rw [Function.update_of_ne hpq]; exact Or.inl rfl

lemma learned_of_precedes (hcons : ∀ s t, V.cons s t = true → s = t)
    {C C' : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    {st : Step P D.spec (Msg P D) Act} {ℓ : Option (Label P D.spec)}
    (hr : (alg V QS).Reach C h) (hs : (alg V QS).step C st = some (C', ℓ)) {x : OpId P}
    (hx : Completed h x) : (C'.loc x.1).learned x.2 = (C.loc x.1).learned x.2 := by
  rcases learned_step hcons hr hs x.1 x.2 with h1 | ⟨-, r, -, hk⟩
  · exact h1
  · exfalso; simp only [Completed] at hx; omega

/-- A `VOTED` sent in a step of the repaired protocol carries a state above the payload of the
acceptor before the step. -/
lemma new_voted_ge (hfix : V.fix = true) {C C' : Config P (Loc P D) (Msg P D)}
    {h : List (Label P D.spec)} {st : Step P D.spec (Msg P D) Act} {ℓ : Option (Label P D.spec)}
    (hr : (alg V QS).Reach C h) (hs : (alg V QS).step C st = some (C', ℓ))
    {a p : P} {n : ℕ} {i : Rid P} {s : D.S} (hm : (a, p, Msg.voted n i s) ∈ C'.sent)
    (hnm : (a, p, Msg.voted n i s) ∉ C.sent) : (C.loc a).s ≤ s := by
  rcases reach_step_cases hr hs with ⟨-, hsent, -⟩ | ⟨q, l, out, htr, -, hsent⟩
  · rw [hsent] at hm; exact absurd hm hnm
  · rw [hsent] at hm
    rcases Multiset.mem_add.1 hm with hm | hm
    · exact absurd hm hnm
    · have hq : a = q := (mem_outMsgs.1 hm).1
      subst hq
      have hout := (mem_outMsgs.1 hm).2
      rcases trans_acc htr with ⟨_, _, _, hacc⟩ | ⟨_, _, _, _, _, _, _, _, _, hout'⟩ |
        ⟨_, _, _, _, _, _, _, hf, _, _, _, hout'⟩
      · exact absurd trivial (hacc _ hout)
      · rw [hout'] at hout; simp at hout
      · rw [hout'] at hout
        simp only [Multiset.mem_singleton, Prod.mk.injEq, Msg.voted.injEq] at hout
        rw [hout.2.2.2]; exact hf hfix

/-! ## Quorums whose acceptors satisfy an upward-closed property -/

/-- A quorum of acceptors whose payloads, and whose `ACK`s to the attempts of operation `y`,
satisfy `φ`. -/
def GoodQ (QS : Finset (Finset P)) (C : Config P (Loc P D) (Msg P D)) (y : OpId P)
    (φ : D.S → Prop) : Prop :=
  ∃ Q ∈ QS, ∀ a ∈ Q, φ (C.loc a).s ∧
    ∀ n (i : Rid P) σ, i.2.1 = y.2 → (a, y.1, Msg.ack n i σ) ∈ C.sent → φ σ

lemma GoodQ.step {C C' : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    {st : Step P D.spec (Msg P D) Act} {ℓ : Option (Label P D.spec)}
    (hr : (alg V QS).Reach C h) (hs : (alg V QS).step C st = some (C', ℓ)) {y : OpId P}
    {φ : D.S → Prop} (hφ : ∀ s t, s ≤ t → φ s → φ t) (hg : GoodQ QS C y φ) : GoodQ QS C' y φ := by
  obtain ⟨Q, hQ, hQa⟩ := hg
  refine ⟨Q, hQ, fun a ha => ⟨hφ _ _ (lemma1 C h C' st ℓ hr hs a) (hQa a ha).1,
    fun n i σ hi hm => ?_⟩⟩
  by_cases hm₀ : (a, y.1, Msg.ack n i σ) ∈ C.sent
  · exact (hQa a ha).2 n i σ hi hm₀
  · exact hφ _ _ (new_ack_ge hr hs hm hm₀) (hQa a ha).1

lemma GoodQ.direct (hcons : ∀ s t, V.cons s t = true → s = t) {C : Config P (Loc P D) (Msg P D)}
    {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h) {y : OpId P} (hy : ¬ Invoked h y)
    {φ : D.S → Prop} {Q : Finset P} (hQ : Q ∈ QS) (hQa : ∀ a ∈ Q, φ (C.loc a).s) :
    GoodQ QS C y φ := by
  refine ⟨Q, hQ, fun a ha => ⟨hQa a ha, fun n i σ hi hm => ?_⟩⟩
  obtain ⟨-, hlt⟩ := ack_fresh hcons hr hm
  exact absurd (by simp only [Invoked]; omega) hy

lemma GoodQ.learned (hcons : ∀ s t, V.cons s t = true → s = t) (hQS : IsQuorumSystem QS)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h)
    {y : OpId P} {φ : D.S → Prop} (hφ : ∀ s t, s ≤ t → φ s → φ t) (hg : GoodQ QS C y φ)
    {s : D.S} (hy : learnedOf C y = some s) : φ s := by
  simp only [learnedOf, Option.map_eq_some_iff] at hy
  obtain ⟨⟨s', v⟩, hy, rfl⟩ := hy
  obtain ⟨-, -, i, hi1, hi2, hv, hc⟩ := learned_ok hcons hr hy
  obtain ⟨Q, hQ, hQa⟩ := hg
  have hQ' : HasQuorum QS Q := ⟨Q, hQ, subset_rfl⟩
  cases v with
  | true =>
    obtain ⟨n, ⟨A, hA, hAa⟩, -⟩ := hv rfl
    obtain ⟨a, haQ, haA⟩ := hQ'.inter hQS hA
    obtain ⟨σ, hσ, hσs⟩ := hAa a haA
    rw [hi1] at hσ
    exact hφ _ _ hσs ((hQa a haQ).2 n i σ hi2 hσ)
  | false =>
    obtain ⟨A, hA, hAa⟩ := hc rfl
    obtain ⟨a, haQ, haA⟩ := hQ'.inter hQS hA
    obtain ⟨n, hσ⟩ := hAa a haA
    rw [hi1] at hσ
    exact (hQa a haQ).2 n i _ hi2 hσ

/-! ## Theorem 2 (Stability) -/

theorem good2_of_reach (hcons : ∀ s t, V.cons s t = true → s = t)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h) :
    ∀ x y s₁, learnedOf C x = some s₁ → Precedes h x y → GoodQ QS C y (s₁ ≤ ·) := by
  induction hr with
  | init => intro x y s₁ hx; simp [learnedOf, Protocol.initCfg, alg, initLoc] at hx
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    intro x y s₁ hx hp
    have hr' : (alg V QS).Reach C' (h₀ ++ ℓ.toList) := Protocol.Reach.step hr hs
    have hφ : ∀ s t, s ≤ t → s₁ ≤ s → s₁ ≤ t := fun s t hst h1 => h1.trans hst
    have hold : Precedes h₀ x y → GoodQ QS C' y (s₁ ≤ ·) := fun hp₀ => by
      have := learned_of_precedes hcons hr hs hp₀.completed
      exact (ih x y s₁ (by simpa [learnedOf, this] using hx) hp₀).step hr hs hφ
    cases ℓ with
    | none => simp only [Option.toList_none, List.append_nil] at hp; exact hold hp
    | some z =>
      simp only [Option.toList_some] at hp hr'
      rcases precedes_concat hp with hp | ⟨-, hy⟩
      · exact hold hp
      · obtain ⟨Q, hQ, hQa⟩ := lemma2 hcons C' _ hr' s₁ ⟨x, hx⟩
        exact GoodQ.direct hcons hr' hy hQ hQa

/-- **Theorem 2 (Stability).** If query `x` precedes query `y`, the state learned by `x` is
below the state learned by `y`. Holds for Algorithm 2 as written. -/
theorem theorem2 (hcons : ∀ s t, V.cons s t = true → s = t) (hQS : IsQuorumSystem QS) :
    Theorem2 V QS := by
  intro C h hr x y s₁ s₂ hp hx hy
  exact (good2_of_reach hcons hr x y s₁ hx hp).learned hcons hQS hr
    (fun s t hst h1 => h1.trans hst) hy

/-! ## Theorem 5 (Update Visibility) -/

theorem good5_of_reach (hcons : ∀ s t, V.cons s t = true → s = t) (H : D.CausalHistory)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h) :
    ∀ x y u, opOf h x = some (CRDT.Cmd.upd u) → Precedes h x y → GoodQ QS C y (u ∈ H.C ·) := by
  induction hr with
  | init => intro x y u hx; simp [opOf] at hx
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    intro x y u hx hp
    have hr' : (alg V QS).Reach C' (h₀ ++ ℓ.toList) := Protocol.Reach.step hr hs
    have hφ : ∀ s t, s ≤ t → u ∈ H.C s → u ∈ H.C t := fun s t hst h1 => H.C_mono hst h1
    have hwf := (procInv_of_reach hcons hr).1
    have hold : Precedes h₀ x y → GoodQ QS C' y (u ∈ H.C ·) := fun hp₀ => by
      have hi := hwf.invoked_of_completed hp₀.completed
      rw [opOf_append_of_invoked hi] at hx
      exact (ih x y u hx hp₀).step hr hs hφ
    cases ℓ with
    | none => simp only [Option.toList_none, List.append_nil] at hp; exact hold hp
    | some z =>
      simp only [Option.toList_some] at hp hr' hx
      rcases precedes_concat hp with hp | ⟨hc, hy⟩
      · exact hold hp
      · obtain ⟨Q, hQ, hQa⟩ := (updInv_of_reach hcons H hr').done x u hx hc
        exact GoodQ.direct hcons hr' hy hQ hQa

/-- **Theorem 5 (Update Visibility).** If update `u` precedes query `y`, the state learned by `y`
includes `u`. Holds for Algorithm 2 as written. -/
theorem theorem5 (hcons : ∀ s t, V.cons s t = true → s = t) (hQS : IsQuorumSystem QS)
    (H : D.CausalHistory) : Theorem5 V QS H := by
  intro C h hr x y u s hp hx hy
  exact (good5_of_reach hcons H hr x y u hx hp).learned hcons hQS hr
    (fun s t hst h1 => H.C_mono hst h1) hy

/-! ## Theorem 1 (Validity) -/

/-- A learned state is generated by the updates invoked so far. -/
lemma learned_gen (hcons : ∀ s t, V.cons s t = true → s = t) (hQS : IsQuorumSystem QS)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h)
    {s : D.S} (hs : Learned C s) : Gen D (invUpd h) s := by
  obtain ⟨v, hv⟩ := learned_iff.1 hs
  obtain ⟨A, ⟨Q, hQ, hQA⟩, hA⟩ := learned_snap hcons hr hv
  obtain ⟨a, ha⟩ := hQS Q hQ Q hQ
  have ha' : a ∈ A := hQA (Finset.mem_inter.1 ha).1
  have hg := (allGen_of_reach hr).2
  rcases hA a ha' with ⟨p, n, i, hm⟩ | ⟨p, n, i, hm⟩
  · exact hg _ hm s rfl
  · exact hg _ hm s rfl

theorem thm1_of_reach (hcons : ∀ s t, V.cons s t = true → s = t) (hQS : IsQuorumSystem QS)
    (H : D.CausalHistory) {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) :
    ∀ x s, learnedOf C x = some s → ∀ u ∈ H.C s,
      ∃ y, opOf h y = some (CRDT.Cmd.upd u) ∧ ¬ Precedes h x y := by
  induction hr with
  | init => intro x s hx; simp [learnedOf, Protocol.initCfg, alg, initLoc] at hx
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    intro x s hx u hu
    have hr' : (alg V QS).Reach C' (h₀ ++ ℓ.toList) := Protocol.Reach.step hr hs
    rcases learned_step hcons hr hs x.1 x.2 with heq | ⟨hnone, r, rfl, hk⟩
    · obtain ⟨y, hy, hny⟩ := ih x s (by simpa [learnedOf, heq] using hx) u hu
      exact ⟨y, opOf_append_of_eq_some hy _, not_precedes_append (Invoked.of_opOf_eq_some hy) hny⟩
    · have hg := learned_gen hcons hQS hr' ⟨x, hx⟩
      obtain ⟨y, hy⟩ := C_subset_of_gen H hg hu
      simp only [Option.toList_some, opOf_append_ret] at hy ⊢
      refine ⟨y, hy, Precedes.not_of_invoked (Invoked.of_opOf_eq_some hy) ?_⟩
      simp only [Completed]; omega

/-- **Theorem 1 (Validity).** The causal history of a learned state consists of updates invoked
before the query returned. Holds for Algorithm 2 as written. -/
theorem theorem1 (hcons : ∀ s t, V.cons s t = true → s = t) (hQS : IsQuorumSystem QS)
    (H : D.CausalHistory) : Theorem1 V QS H :=
  fun _ _ hr => thm1_of_reach hcons hQS H hr

/-! ## Theorem 4 (Update Stability) for the repaired protocol -/

/-- A quorum of acceptors that include `u₁`, and all of whose snapshots including `u₂` also
include `u₁`. -/
def Good4 (QS : Finset (Finset P)) (H : D.CausalHistory) (C : Config P (Loc P D) (Msg P D))
    (u₁ u₂ : D.U) : Prop :=
  ∃ Q ∈ QS, ∀ a ∈ Q, u₁ ∈ H.C (C.loc a).s ∧ ∀ σ, Snap C.sent a σ → u₂ ∈ H.C σ → u₁ ∈ H.C σ

lemma Good4.step (hfix : V.fix = true) {H : D.CausalHistory}
    {C C' : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    {st : Step P D.spec (Msg P D) Act} {ℓ : Option (Label P D.spec)}
    (hr : (alg V QS).Reach C h) (hs : (alg V QS).step C st = some (C', ℓ)) {u₁ u₂ : D.U}
    (hg : Good4 QS H C u₁ u₂) : Good4 QS H C' u₁ u₂ := by
  obtain ⟨Q, hQ, hQa⟩ := hg
  refine ⟨Q, hQ, fun a ha => ⟨H.C_mono (lemma1 C h C' st ℓ hr hs a) (hQa a ha).1,
    fun σ hσ hu₂ => ?_⟩⟩
  rcases hσ with ⟨p, n, i, hm⟩ | ⟨p, n, i, hm⟩
  · by_cases hm₀ : (a, p, Msg.ack n i σ) ∈ C.sent
    · exact (hQa a ha).2 σ (Or.inl ⟨p, n, i, hm₀⟩) hu₂
    · exact H.C_mono (new_ack_ge hr hs hm hm₀) (hQa a ha).1
  · by_cases hm₀ : (a, p, Msg.voted n i σ) ∈ C.sent
    · exact (hQa a ha).2 σ (Or.inr ⟨p, n, i, hm₀⟩) hu₂
    · exact H.C_mono (new_voted_ge hfix hr hs hm hm₀) (hQa a ha).1

lemma Good4.direct (hcons : ∀ s t, V.cons s t = true → s = t) {H : D.CausalHistory}
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h)
    {x : OpId P} {u₁ u₂ : D.U} (hx : opOf h x = some (CRDT.Cmd.upd u₁)) (hc : Completed h x)
    (hu₂ : u₂ ∉ invUpd h) : Good4 QS H C u₁ u₂ := by
  obtain ⟨Q, hQ, hQa⟩ := (updInv_of_reach hcons H hr).done x u₁ hx hc
  refine ⟨Q, hQ, fun a ha => ⟨hQa a ha, fun σ hσ hσ₂ => absurd ?_ hu₂⟩⟩
  have hg := (allGen_of_reach hr).2
  rcases hσ with ⟨p, n, i, hm⟩ | ⟨p, n, i, hm⟩
  · exact C_subset_of_gen H (hg _ hm σ rfl) hσ₂
  · exact C_subset_of_gen H (hg _ hm σ rfl) hσ₂

lemma UniqueUpd.of_append {h β : List (Label P D.spec)} (hu : UniqueUpd (h ++ β)) :
    UniqueUpd h := fun x y u hx hy =>
  hu x y u (opOf_append_of_eq_some hx β) (opOf_append_of_eq_some hy β)

theorem good4_of_reach (hcons : ∀ s t, V.cons s t = true → s = t) (hfix : V.fix = true)
    (H : D.CausalHistory) {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) : UniqueUpd h → ∀ x u₁ u₂, opOf h x = some (CRDT.Cmd.upd u₁) →
      Completed h x → (u₂ ∉ invUpd h ∨ ∃ y, Precedes h x y ∧ opOf h y = some (CRDT.Cmd.upd u₂)) →
      Good4 QS H C u₁ u₂ := by
  induction hr with
  | init => intro _ x u₁ u₂ hx; simp [opOf] at hx
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    intro huniq x u₁ u₂ hx hc hcase
    have hr' : (alg V QS).Reach C' (h₀ ++ ℓ.toList) := Protocol.Reach.step hr hs
    have hwf := (procInv_of_reach hcons hr).1
    rcases hcase with hu₂ | ⟨y, hp, hy⟩
    · exact Good4.direct hcons hr' hx hc hu₂
    · -- the old history
      have hc₀ : Completed h₀ x := by
        cases ℓ with
        | none => simpa using hp.completed
        | some z =>
          simp only [Option.toList_some] at hp
          exact hp.completed_of_append_singleton (Invoked.of_opOf_eq_some hy)
      have hx₀ : opOf h₀ x = some (CRDT.Cmd.upd u₁) := by
        rwa [opOf_append_of_invoked (hwf.invoked_of_completed hc₀)] at hx
      have hcase₀ : u₂ ∉ invUpd h₀ ∨ ∃ y, Precedes h₀ x y ∧ opOf h₀ y = some (CRDT.Cmd.upd u₂) := by
        by_cases hyi : Invoked h₀ y
        · right
          refine ⟨y, (precedes_append_iff_of_invoked hyi).1 hp, ?_⟩
          rwa [opOf_append_of_invoked hyi] at hy
        · left
          rintro ⟨y', hy'⟩
          have := huniq y' y u₂ (opOf_append_of_eq_some hy' _) hy
          subst this
          exact hyi (Invoked.of_opOf_eq_some hy')
      exact (ih huniq.of_append x u₁ u₂ hx₀ hc₀ hcase₀).step hfix hr hs

/-- **Theorem 4 (Update Stability)** for the repaired protocol: if update `u₁` precedes update
`u₂`, every learned state that includes `u₂` also includes `u₁`. -/
theorem theorem4_fixed (hcons : ∀ s t, V.cons s t = true → s = t) (hfix : V.fix = true)
    (hQS : IsQuorumSystem QS) (H : D.CausalHistory) : Theorem4 V QS H := by
  intro C h hr huniq x y u₁ u₂ s hp hx hy hs hu₂
  have hwf := (procInv_of_reach hcons hr).1
  obtain ⟨Q, hQ, hQa⟩ := good4_of_reach hcons hfix H hr huniq x u₁ u₂ hx hp.completed
    (Or.inr ⟨y, hp, hy⟩)
  obtain ⟨v, hv⟩ := learned_iff.1 hs
  obtain ⟨A, hA, hAs⟩ := learned_snap hcons hr hv
  obtain ⟨a, haQ, haA⟩ := HasQuorum.inter hQS (A := Q) ⟨Q, hQ, subset_rfl⟩ hA
  exact (hQa a haQ).2 s (hAs a haA) hu₂

end Podc.CRDTReplication
