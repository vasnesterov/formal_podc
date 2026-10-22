import Papers.PODC2019.CRDTReplication.Validity

/-!
# Auxiliary invariants: fresh `ACK`s, completed updates, stability of learned records
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-- Every `ACK` answers a `PREPARE` of the same attempt. -/
theorem ack_has_prepare {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) :
    ∀ a p n i σ, (a, p, Msg.ack n i σ) ∈ C.sent → ∃ n' σ', (p, a, Msg.prepare i n' σ') ∈ C.sent := by
  induction hr with
  | init => simp [Protocol.initCfg]
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    intro a p n i σ hm
    rcases reach_step_cases hr hs with ⟨-, hsent, -⟩ | ⟨q, l, out, htr, -, hsent⟩
    · rw [hsent] at hm ⊢; exact ih a p n i σ hm
    · rw [hsent] at hm ⊢
      rcases Multiset.mem_add.1 hm with hm | hm
      · obtain ⟨n', σ', h'⟩ := ih a p n i σ hm
        exact ⟨n', σ', Multiset.mem_add.2 (Or.inl h')⟩
      · obtain ⟨rfl, hout⟩ := mem_outMsgs.1 hm
        rcases trans_acc htr with ⟨_, _, _, hacc⟩ | ⟨src, i', n', s', hm', _, _, _, _, hout'⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, hout'⟩
        · exact absurd trivial (hacc _ hout)
        · rw [hout'] at hout
          simp only [Multiset.mem_singleton, Prod.mk.injEq, Msg.ack.injEq] at hout
          obtain ⟨rfl, -, rfl, -⟩ := hout
          exact ⟨n', s', Multiset.mem_add.2 (Or.inl hm')⟩
        · rw [hout'] at hout; simp at hout

/-- `ACK`s concern attempts of operations already invoked. -/
theorem ack_fresh (hcons : ∀ s t, V.cons s t = true → s = t) {C : Config P (Loc P D) (Msg P D)}
    {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h) {a p : P} {n : ℕ} {i : Rid P}
    {σ : D.S} (hm : (a, p, Msg.ack n i σ) ∈ C.sent) : i.1 = p ∧ i.2.1 < (opsOf h p).length := by
  obtain ⟨n', σ', hp⟩ := ack_has_prepare hr a p n i σ hm
  exact ((procInv_of_reach hcons hr).2 p).prep_id a i n' σ' hp

/-! ## Messages sent by a transition -/

/-- Classification of the messages sent by a local transition. -/
lemma trans_out {sent : Multiset (P × P × Msg P D)} {p : P} {l₀ l : Loc P D}
    {out : Multiset (P × Msg P D)} {ℓ : Option (Label P D.spec)}
    (htr : Trans V QS sent p l₀ l out ℓ) {x : P × Msg P D} (hx : x ∈ out) :
    (∃ u, ℓ = some (.inv p (CRDT.Cmd.upd u)) ∧ x.2 = .merge l₀.nOps (D.app u l₀.s)) ∨
    (∃ k σ, x.2 = .merged k ∧ (x.1, p, Msg.merge k σ) ∈ sent ∧ σ ≤ l.s) ∨
    (∃ i n σ, x.2 = .prepare i n σ) ∨ (∃ n i σ, x.2 = .vote n i σ) ∨ x.2.IsAcc := by
  obtain ⟨a, m⟩ := x
  cases htr with
  | inv hst =>
    rename_i o
    unfold invokeStep at hst
    split at hst
    · cases o with
      | upd u =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        rw [mem_toOthers] at hx
        exact Or.inl ⟨u, rfl, hx.2⟩
      | qry q =>
        simp only [startAttempt, Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        rw [mem_toAll] at hx
        exact Or.inr (Or.inr (Or.inl ⟨_, _, _, hx⟩))
    · simp at hst
  | internal hst =>
    unfold internalStep at hst
    split at hst <;> (try split_ifs at hst) <;>
      simp only [startAttempt, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hst <;>
      (try obtain ⟨rfl, rfl, -⟩ := hst) <;> simp_all
  | recv hm =>
    rename_i src m'
    cases m' with
    | merge k σ =>
      simp only [receiveStep, Multiset.mem_singleton, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact Or.inr (Or.inl ⟨k, σ, rfl, hm, le_sup_right⟩)
    | _ =>
      simp only [receiveStep] at hx
      (try split_ifs at hx) <;> simp_all [Msg.IsAcc]

/-- After a reception, a pending update phase was there before, or the reception was a
`MERGED` for it. -/
lemma recv_phase_upd {p src : P} {m : Msg P D} {l : Loc P D} {k : ℕ} {M : Finset P}
    (h : (receiveStep V p src m l).1.phase = .upd k M) :
    l.phase = .upd k M ∨ ∃ M', l.phase = .upd k M' ∧ M = insert src M' ∧ m = .merged k := by
  cases m with
  | merged k' =>
    simp only [receiveStep] at h
    split at h
    · rename_i k₁ M₁ hph
      split_ifs at h with hkk
      · simp only [Phase.upd.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨M₁, hph, rfl, by rw [hkk]⟩
      · exact Or.inl h
    · exact Or.inl h
  | ack n i s' =>
    left; simp only [receiveStep] at h
    split at h
    · split_ifs at h; simp_all
    · exact h
  | voted n i s' =>
    left; simp only [receiveStep] at h
    split at h
    · split_ifs at h; simp_all
    · exact h
  | merge k' s' => exact Or.inl h
  | prepare i n s' =>
    left; simp only [receiveStep] at h; split_ifs at h <;> exact h
  | vote n i s' =>
    left; simp only [receiveStep] at h; split_ifs at h <;> exact h

/-! ## Completed updates are included in a quorum -/

/-- The invariant behind Theorem 5: an update is included in the payloads of the acceptors that
merged it. -/
structure UpdInv (QS : Finset (Finset P)) (H : D.CausalHistory) (C : Config P (Loc P D) (Msg P D))
    (h : List (Label P D.spec)) : Prop where
  merge_has : ∀ p a k σ u, (p, a, Msg.merge k σ) ∈ C.sent →
    opOf h (p, k) = some (CRDT.Cmd.upd u) → u ∈ H.C σ
  merged_le : ∀ a p k, (a, p, Msg.merged k) ∈ C.sent →
    ∃ σ, (p, a, Msg.merge k σ) ∈ C.sent ∧ σ ≤ (C.loc a).s
  phase_has : ∀ p k M u, (C.loc p).phase = .upd k M → opOf h (p, k) = some (CRDT.Cmd.upd u) →
    ∀ a ∈ M, u ∈ H.C (C.loc a).s
  done : ∀ x u, opOf h x = some (CRDT.Cmd.upd u) → Completed h x →
    ∃ Q ∈ QS, ∀ a ∈ Q, u ∈ H.C (C.loc a).s

/-- **Update completion.** In every reachable configuration, a completed update is included in
the payloads of a quorum. -/
theorem updInv_of_reach (hcons : ∀ s t, V.cons s t = true → s = t) (H : D.CausalHistory)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) : UpdInv QS H C h := by
  induction hr with
  | init =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Protocol.initCfg, alg, initLoc, opOf, Completed]
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    have hP := (procInv_of_reach hcons hr).2
    have hmono : ∀ a, (C₀.loc a).s ≤ (C'.loc a).s := lemma1 C₀ h₀ C' st ℓ hr hs
    have hCm : ∀ a u, u ∈ H.C (C₀.loc a).s → u ∈ H.C (C'.loc a).s :=
      fun a u hu => H.C_mono (hmono a) hu
    have hop : ∀ x o, opOf (h₀ ++ ℓ.toList) x = some o → Invoked h₀ x → opOf h₀ x = some o := by
      intro x o hx hi; rwa [opOf_append_of_invoked hi] at hx
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rcases reach_step_cases hr hs with ⟨hloc, hsent, rfl⟩ | ⟨p, l, out, htr, hloc, hsent⟩
    · simp only [Option.toList_none, List.append_nil]
      refine ⟨fun p a k σ u hm => h1 p a k σ u (hsent ▸ hm), fun a p k hm => ?_,
        fun p k M u hph hu a ha => ?_, fun x u hx hc => ?_⟩
      · rw [hloc, hsent]; exact h2 a p k (hsent ▸ hm)
      · rw [hloc] at hph ⊢; exact h3 p k M u hph hu a ha
      · rw [hloc]; exact h4 x u hx hc
    · have hle : C₀.sent ≤ C'.sent := by rw [hsent]; exact Multiset.le_add_right _ _
      have hnew : ∀ y ∈ C'.sent, y ∈ C₀.sent ∨ (y.1 = p ∧ (y.2.1, y.2.2) ∈ out) := by
        intro y hy; rw [hsent] at hy
        rcases Multiset.mem_add.1 hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr (mem_outMsgs.1 hy)
      have hlp : C'.loc p = l := by rw [hloc, Function.update_self]
      have hlq : ∀ q, q ≠ p → C'.loc q = C₀.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- merge messages
        intro q a k σ u hm hu
        rcases hnew _ hm with hm | ⟨rfl, hout⟩
        · obtain ⟨u', hu'⟩ := (hP q).merge_id a k σ hm
          exact h1 q a k σ u hm (hop _ _ hu (Invoked.of_opOf_eq_some hu'))
        · rcases trans_out htr hout with ⟨u', rfl, hx⟩ | ⟨_, _, hx, _⟩ | ⟨_, _, _, hx⟩ |
            ⟨_, _, _, hx⟩ | hx <;> simp only [Msg.merge.injEq, reduceCtorEq, Msg.IsAcc] at hx
          obtain ⟨rfl, rfl⟩ := hx
          rw [(hP q).nOps, Option.toList_some, opOf_concat_inv, ite_eq_left rfl] at hu
          cases hu
          rw [H.C_app]; exact Set.mem_insert _ _
      · -- merged messages
        intro a q k hm
        rcases hnew _ hm with hm | ⟨rfl, hout⟩
        · obtain ⟨σ, hσ, hle'⟩ := h2 a q k hm
          exact ⟨σ, Multiset.mem_of_le hle hσ, hle'.trans (hmono a)⟩
        · rcases trans_out htr hout with ⟨u', -, hx⟩ | ⟨k', σ, hx, hσ, hσl⟩ | ⟨_, _, _, hx⟩ |
            ⟨_, _, _, hx⟩ | hx <;> simp only [Msg.merged.injEq, reduceCtorEq, Msg.IsAcc] at hx
          subst hx
          exact ⟨σ, Multiset.mem_of_le hle hσ, by rw [hlp]; exact hσl⟩
      · -- the phase of a pending update
        intro q k M u hph hu a ha
        by_cases hq : q = p
        · subst hq
          rw [hlp] at hph
          cases htr with
          | inv hst =>
            rename_i o
            unfold invokeStep at hst
            split at hst
            · cases o with
              | upd u' =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hst
                obtain ⟨rfl, rfl⟩ := hst
                simp only [Phase.upd.injEq] at hph
                obtain ⟨rfl, rfl⟩ := hph
                rw [(hP q).nOps, Option.toList_some, opOf_concat_inv, ite_eq_left rfl] at hu
                cases hu
                rw [Finset.mem_singleton] at ha; subst ha
                rw [hlp, H.C_app]; exact Set.mem_insert _ _
              | qry q' =>
                simp only [startAttempt, Option.some.injEq, Prod.mk.injEq] at hst
                obtain ⟨rfl, rfl⟩ := hst
                simp at hph
            · simp at hst
          | internal hst =>
            exfalso
            unfold internalStep at hst
            split at hst <;> (try split_ifs at hst) <;>
              simp only [startAttempt, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hst <;>
              (try obtain ⟨rfl, rfl, -⟩ := hst) <;> simp_all
          | recv hm =>
            rename_i src m
            have hinv : ∀ M', (C₀.loc q).phase = .upd k M' → Invoked h₀ (q, k) := fun M' h' => by
              obtain ⟨-, u₁, hu₁⟩ := (hP q).ph_upd k M' h'
              exact Invoked.of_opOf_eq_some hu₁
            rcases recv_phase_upd hph with h0 | ⟨M', h0, rfl, rfl⟩
            · exact hCm a u (h3 q k M u h0 (hop _ _ hu (hinv M h0)) a ha)
            · rcases Finset.mem_insert.1 ha with rfl | ha
              · obtain ⟨σ, hσ, hσle⟩ := h2 _ _ _ hm
                have := h1 _ _ _ _ u hσ (hop _ _ hu (hinv M' h0))
                exact hCm _ u (H.C_mono hσle this)
              · exact hCm a u (h3 q k M' u h0 (hop _ _ hu (hinv M' h0)) a ha)
        · rw [hlq q hq] at hph
          have hinv : Invoked h₀ (q, k) := by
            obtain ⟨-, u₁, hu₁⟩ := (hP q).ph_upd k M hph
            exact Invoked.of_opOf_eq_some hu₁
          exact hCm a u (h3 q k M u hph (hop _ _ hu hinv) a ha)
      · -- completed updates
        intro x u hx hc
        by_cases hc₀ : Completed h₀ x
        · have hwf := (procInv_of_reach hcons hr).1
          obtain ⟨Q, hQ, hQa⟩ := h4 x u (hop _ _ hx (hwf.invoked_of_completed hc₀)) hc₀
          exact ⟨Q, hQ, fun a ha => hCm a u (hQa a ha)⟩
        · have hbusy := fun hb => (hP p).busy hb
          cases htr with
          | inv hst =>
            rw [Option.toList_some, completed_append_of_not_ret (fun _ _ => by simp)] at hc
            exact absurd hc hc₀
          | recv hm => simp only [Option.toList_none, List.append_nil] at hc; exact absurd hc hc₀
          | internal hst =>
            rename_i act r
            cases r with
            | none => simp only [Option.map_none, Option.toList_none, List.append_nil] at hc
                      exact absurd hc hc₀
            | some res =>
              simp only [Option.map_some, Option.toList_some] at hc hx
              rw [completed_append_ret] at hc
              rcases hc with hc | rfl
              · exact absurd hc hc₀
              rw [opOf_append_ret] at hx
              have hb := internalStep_busy hst
              have hlen := hbusy hb
              unfold internalStep at hst
              split at hst
              · rename_i k M hph
                split_ifs at hst with hQ
                obtain ⟨hk, -⟩ := (hP p).ph_upd k M hph
                obtain rfl : k = (respsOf h₀ p).length := by omega
                obtain ⟨Q, hQ, hQM⟩ := hQ
                exact ⟨Q, hQ, fun a ha => hCm a u (h3 p _ M u hph hx a (hQM ha))⟩
              · rename_i q i acks hph
                obtain ⟨-, hi2, hq, -⟩ := (hP p).ph_prep q i acks hph
                have : i.2.1 = (respsOf h₀ p).length := by omega
                rw [← this, hq] at hx; cases hx
              · rename_i q i n s M hph
                obtain ⟨-, hi2, hq, -⟩ := (hP p).ph_vote q i n s M hph
                have : i.2.1 = (respsOf h₀ p).length := by omega
                rw [← this, hq] at hx; cases hx
              · simp at hst
              · simp at hst
              · simp at hst


end Podc.CRDTReplication
