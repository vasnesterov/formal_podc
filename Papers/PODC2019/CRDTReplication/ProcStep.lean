import Papers.PODC2019.CRDTReplication.PropInv

/-!
# Preservation of the proposer invariant by the steps of the process itself
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

lemma ProcInv.not_completed_cur {sent : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)}
    {p : P} {l : Loc P D} (hI : ProcInv QS sent h p l) (hb : l.phase ≠ .idle) {k : ℕ}
    (hk : k + 1 = (opsOf h p).length) : ¬ Completed h (p, k) := by
  have := hI.busy hb; simp only [Completed]; omega

/-- Invocation steps preserve the invariant of the invoking process. -/
lemma ProcInv.inv {sent : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)} {p : P}
    {l₀ l : Loc P D} {out : Multiset (P × Msg P D)} {o : D.spec.Op}
    (hI : ProcInv QS sent h p l₀) (hst : invokeStep p o l₀ = some (l, out)) :
    ProcInv QS (sent + outMsgs p out) (h ++ [.inv p o]) p l := by
  have hle : sent ≤ sent + outMsgs p out := Multiset.le_add_right _ _
  unfold invokeStep at hst
  split at hst
  case h_2 => simp at hst
  rename_i hidle
  have hlen := hI.idle hidle
  have hops : opsOf (h ++ [.inv p o]) p = opsOf h p ++ [o] := by simp
  have hresps : respsOf (h ++ [.inv p o]) p = respsOf h p := by simp
  have hlen' : (opsOf (h ++ [.inv p o]) p).length = (opsOf h p).length + 1 := by
    rw [hops, List.length_append]; rfl
  have hop : ∀ k, opOf (h ++ [.inv p o]) (p, k) =
      if k = (opsOf h p).length then some o else opOf h (p, k) := fun k => by
    rw [opOf_concat_inv]; simp
  have hresp : ∀ k, respOf (h ++ [.inv p o]) (p, k) = respOf h (p, k) := fun k => by
    simp [respOf, hresps]
  have hcomp : ∀ k, Completed (h ++ [.inv p o]) (p, k) ↔ Completed h (p, k) := fun k => by
    simp [Completed, hresps]
  have hcomp_lt : ∀ k, Completed h (p, k) → k < (opsOf h p).length := fun k hk => by
    simp only [Completed] at hk; omega
  have hold : ∀ k x, opOf h (p, k) = some x → opOf (h ++ [.inv p o]) (p, k) = some x :=
    fun k x hk => opOf_append_of_eq_some hk _
  have hnew : ∀ x, x ∈ sent + outMsgs p out → x.1 = p → x ∈ sent ∨ (x.2.1, x.2.2) ∈ out := by
    intro x hx _
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (mem_outMsgs.1 hx).2
  -- common fields
  have learned' : ∀ k s v, l₀.learned k = some (s, v) → Completed (h ++ [.inv p o]) (p, k) ∧
      LearnedOK QS (sent + outMsgs p out) (h ++ [.inv p o]) p k s v := fun k s v hk =>
    ⟨(hI.learned k s v hk).1.mono, (hI.learned k s v hk).2.mono hle _⟩
  have learned_some' : ∀ k q, opOf (h ++ [.inv p o]) (p, k) = some (CRDT.Cmd.qry q) →
      Completed (h ++ [.inv p o]) (p, k) → l₀.learned k ≠ none := by
    intro k q hk hc
    rw [hcomp] at hc
    rw [hop, ite_eq_right (by have := hcomp_lt k hc; omega)] at hk
    exact hI.learned_some k q hk hc
  have resp_upd' : ∀ k u r, opOf (h ++ [.inv p o]) (p, k) = some (CRDT.Cmd.upd u) →
      respOf (h ++ [.inv p o]) (p, k) = some r → r = CRDT.Res.done := by
    intro k u r hk hr
    rw [hresp] at hr
    have hc := Completed.of_respOf_eq_some hr
    rw [hop, ite_eq_right (by have := hcomp_lt k hc; omega)] at hk
    exact hI.resp_upd k u r hk hr
  cases o with
  | upd u =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    refine ⟨by rw [hlen', hI.nOps], by simp, fun _ => by rw [hlen', hresps, hlen], ?_, by simp, by simp,
      learned', learned_some', resp_upd', ?_, ?_, ?_⟩
    · intro k M hk
      simp only [Phase.upd.injEq] at hk; obtain ⟨rfl, -⟩ := hk
      refine ⟨by rw [hlen', hI.nOps], u, ?_⟩
      exact (hop _).trans (ite_eq_left hI.nOps)
    · intro a i n σ hm
      rcases hnew _ hm rfl with hm | hm
      · have := hI.prep_id a i n σ hm; exact ⟨this.1, by rw [hlen']; omega⟩
      · simp at hm
    · intro a n i σ hm
      rcases hnew _ hm rfl with hm | hm
      · have := hI.vote_id a n i σ hm; exact ⟨this.1, by rw [hlen']; omega⟩
      · simp at hm
    · intro a k σ hm
      rcases hnew _ hm rfl with hm | hm
      · obtain ⟨u', hu'⟩ := hI.merge_id a k σ hm; exact ⟨u', hold _ _ hu'⟩
      · simp only [mem_toOthers, Msg.merge.injEq] at hm
        obtain ⟨-, rfl, -⟩ := hm
        exact ⟨u, (hop _).trans (ite_eq_left hI.nOps)⟩
  | qry q =>
    simp only [startAttempt, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    refine ⟨by rw [hlen', hI.nOps], by simp, fun _ => by rw [hlen', hresps, hlen], by simp, ?_, by simp,
      learned', learned_some', resp_upd', ?_, ?_, ?_⟩
    · intro q' i acks hk
      simp only [Phase.prep.injEq] at hk; obtain ⟨rfl, rfl, rfl⟩ := hk
      refine ⟨rfl, by rw [hlen']; simp [hI.nOps], ?_, by simp⟩
      simp only [Nat.add_sub_cancel]; exact (hop _).trans (ite_eq_left hI.nOps)
    · intro a i n σ hm
      rcases hnew _ hm rfl with hm | hm
      · have := hI.prep_id a i n σ hm; exact ⟨this.1, by rw [hlen']; omega⟩
      · simp only [mem_toAll, Msg.prepare.injEq] at hm
        obtain ⟨rfl, -, -⟩ := hm
        exact ⟨rfl, by rw [hlen']; simp [hI.nOps]⟩
    · intro a n i σ hm
      rcases hnew _ hm rfl with hm | hm
      · have := hI.vote_id a n i σ hm; exact ⟨this.1, by rw [hlen']; omega⟩
      · simp at hm
    · intro a k σ hm
      rcases hnew _ hm rfl with hm | hm
      · obtain ⟨u', hu'⟩ := hI.merge_id a k σ hm; exact ⟨u', hold _ _ hu'⟩
      · simp at hm

/-- Steps that do not respond and do not change `nOps` and `learned` preserve the invariant,
provided the new phase satisfies its clauses. -/
lemma ProcInv.keep {sent sent' : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)} {p : P}
    {l₀ l : Loc P D} (hI : ProcInv QS sent h p l₀) (hle : sent ≤ sent')
    (hn : l.nOps = l₀.nOps) (hl : l.learned = l₀.learned)
    (hph : l.phase = .idle ↔ l₀.phase = .idle)
    (hupd : ∀ k M, l.phase = .upd k M → k + 1 = (opsOf h p).length ∧
      ∃ u, opOf h (p, k) = some (CRDT.Cmd.upd u))
    (hprep : ∀ q i acks, l.phase = .prep q i acks → i.1 = p ∧ i.2.1 + 1 = (opsOf h p).length ∧
      opOf h (p, i.2.1) = some (CRDT.Cmd.qry q) ∧
      ∀ a n σ, acks a = some (n, σ) → (a, p, Msg.ack n i σ) ∈ sent')
    (hvote : ∀ q i n s M, l.phase = .vote q i n s M → i.1 = p ∧
      i.2.1 + 1 = (opsOf h p).length ∧ opOf h (p, i.2.1) = some (CRDT.Cmd.qry q) ∧
      AckQ QS sent' n i s ∧ ∀ a ∈ M, (a, p, Msg.voted n i s) ∈ sent')
    (hpid : ∀ a i n σ, (p, a, Msg.prepare i n σ) ∈ sent' → (p, a, Msg.prepare i n σ) ∈ sent ∨
      (i.1 = p ∧ i.2.1 < (opsOf h p).length))
    (hvid : ∀ a n i σ, (p, a, Msg.vote n i σ) ∈ sent' → (p, a, Msg.vote n i σ) ∈ sent ∨
      (i.1 = p ∧ i.2.1 < (opsOf h p).length))
    (hmid : ∀ a k σ, (p, a, Msg.merge k σ) ∈ sent' → (p, a, Msg.merge k σ) ∈ sent) :
    ProcInv QS sent' h p l := by
  refine ⟨hn.trans hI.nOps, fun e => hI.idle (hph.1 e), fun e => hI.busy (mt hph.2 e), hupd,
    hprep, hvote, ?_, ?_, hI.resp_upd, ?_, ?_, ?_⟩
  · intro k s v hk; rw [hl] at hk
    obtain ⟨h1, h2⟩ := hI.learned k s v hk
    have := h2.mono hle []; rw [List.append_nil] at this; exact ⟨h1, this⟩
  · intro k q hk hc; rw [hl]; exact hI.learned_some k q hk hc
  · intro a i n σ hm; rcases hpid a i n σ hm with hm | hm
    · exact hI.prep_id a i n σ hm
    · exact hm
  · intro a n i σ hm; rcases hvid a n i σ hm with hm | hm
    · exact hI.vote_id a n i σ hm
    · exact hm
  · intro a k σ hm; exact hI.merge_id a k σ (hmid a k σ hm)

/-- A response step of a busy process: the phase becomes `idle`, nothing is sent, and the
learned record is extended for the current operation (if it is a query). -/
lemma ProcInv.respond {sent : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)} {p : P}
    {l₀ l : Loc P D} {res : D.spec.Resp} (hI : ProcInv QS sent h p l₀)
    (hb : l₀.phase ≠ .idle) (hn : l.nOps = l₀.nOps) (hph : l.phase = .idle)
    (hcur : ∀ k, k + 1 = (opsOf h p).length →
      ((∃ u, opOf h (p, k) = some (CRDT.Cmd.upd u)) ∧ res = CRDT.Res.done ∧
        l.learned = l₀.learned) ∨
      (∃ q s v, opOf h (p, k) = some (CRDT.Cmd.qry q) ∧ res = CRDT.Res.val (D.query q s) ∧
        l.learned = Function.update l₀.learned k (some (s, v)) ∧
        ∃ i : Rid P, i.1 = p ∧ i.2.1 = k ∧
          (v = true → ∃ n, AckQ QS sent n i s ∧ VotedQ QS sent n i s) ∧
          (v = false → ConsQ QS sent i s))) :
    ProcInv QS (sent + outMsgs p 0) (h ++ [.ret p res]) p l := by
  rw [show outMsgs p (0 : Multiset (P × Msg P D)) = 0 from rfl, add_zero]
  have hbusy := hI.busy hb
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = (opsOf h p).length := ⟨(respsOf h p).length, hbusy⟩
  have hkr : k = (respsOf h p).length := by omega
  have hops : opsOf (h ++ [.ret p res]) p = opsOf h p := by simp
  have hresps : (respsOf (h ++ [.ret p res]) p).length = (respsOf h p).length + 1 := by simp
  have hop : ∀ j, opOf (h ++ [.ret p res]) (p, j) = opOf h (p, j) := fun j => by simp
  have hcomp : ∀ j, Completed (h ++ [.ret p res]) (p, j) ↔ Completed h (p, j) ∨ j = k := by
    intro j; rw [completed_append_ret]; simp [hkr]
  have hresp : ∀ j, respOf (h ++ [.ret p res]) (p, j) =
      if j = k then some res else respOf h (p, j) := by
    intro j; rw [respOf_append_ret]; simp [hkr]
  have hnotk : ¬ Completed h (p, k) := hI.not_completed_cur hb hk
  have hlearnk : l₀.learned k = none := by
    by_contra hne
    obtain ⟨⟨s, v⟩, hsv⟩ := Option.ne_none_iff_exists'.1 hne
    exact hnotk (hI.learned k s v hsv).1
  -- old learned entries
  have hold : ∀ j s v, l₀.learned j = some (s, v) →
      Completed (h ++ [.ret p res]) (p, j) ∧ LearnedOK QS sent (h ++ [.ret p res]) p j s v := by
    intro j s v hj
    obtain ⟨h1, h2⟩ := hI.learned j s v hj
    have := h2.mono (le_refl sent) [.ret p res]
    exact ⟨h1.mono, this⟩
  refine ⟨by rw [hn, hI.nOps, hops], fun _ => by rw [hresps, hops]; omega,
    fun e => absurd hph e, fun _ _ e => (by simp [hph] at e),
    fun _ _ _ e => (by simp [hph] at e), fun _ _ _ _ _ e => (by simp [hph] at e),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j s v hj
    rcases hcur k hk with ⟨-, -, hl⟩ | ⟨q, s', v', hq, hres, hl, i, hi1, hi2, hv, hc⟩
    · rw [hl] at hj; exact hold j s v hj
    · rw [hl] at hj
      by_cases hjk : j = k
      · subst hjk
        rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        refine ⟨(hcomp j).2 (Or.inr rfl), ⟨q, by rw [hop]; exact hq, ?_⟩, i, hi1, hi2, hv, hc⟩
        rw [hresp, ite_eq_left rfl, hres]
      · rw [Function.update_of_ne hjk] at hj; exact hold j s v hj
  · intro j q hj hc
    rw [hop] at hj
    rcases (hcomp j).1 hc with hc | rfl
    · rcases hcur k hk with ⟨-, -, hl⟩ | ⟨_, _, _, _, _, hl, _⟩ <;> rw [hl]
      · exact hI.learned_some j q hj hc
      · have : j ≠ k := fun e => hnotk (e ▸ hc)
        rw [Function.update_of_ne this]; exact hI.learned_some j q hj hc
    · rcases hcur j hk with ⟨⟨u, hu⟩, -, -⟩ | ⟨_, _, _, _, _, hl, _⟩
      · rw [hu] at hj; cases hj
      · rw [hl, Function.update_self]; simp
  · intro j u r hj hr
    rw [hop] at hj; rw [hresp] at hr
    split_ifs at hr with hjk
    · subst hjk; rw [Option.some.injEq] at hr; subst hr
      rcases hcur j hk with ⟨-, hres, -⟩ | ⟨q, -, -, hq, -⟩
      · exact hres
      · rw [hq] at hj; cases hj
    · exact hI.resp_upd j u r hj hr
  · intro a i n σ hm; rw [hops]; exact hI.prep_id a i n σ hm
  · intro a n i σ hm; rw [hops]; exact hI.vote_id a n i σ hm
  · intro a j σ hm; rw [hop]; exact hI.merge_id a j σ hm

/-! ## Received states -/

lemma mem_ackers {acks : P → Option (ℕ × D.S)} {a : P} :
    a ∈ ackers acks ↔ (acks a).isSome := by simp [ackers]

lemma acks_eq_of_mem_ackers {acks : P → Option (ℕ × D.S)} {a : P} (ha : a ∈ ackers acks) :
    acks a = some (ackNr acks a, ackState acks a) := by
  rw [mem_ackers] at ha
  obtain ⟨⟨n, s⟩, hx⟩ := Option.isSome_iff_exists.1 ha
  simp [ackNr, ackState, hx]

lemma lub_le_iff (acks : P → Option (ℕ × D.S)) (t : D.S) :
    lub acks ≤ t ↔ D.s₀ ≤ t ∧ ∀ x, ackState acks x ≤ t := by
  unfold lub
  suffices ∀ s : Finset P, Finset.fold _ D.s₀ (ackState acks) s ≤ t ↔
      D.s₀ ≤ t ∧ ∀ x ∈ s, ackState acks x ≤ t by
    rw [this]; simp
  intro s
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.fold_cons, sup_le_iff, ih]
    simp only [Finset.mem_cons, forall_eq_or_imp]
    tauto

lemma ackState_le_lub (acks : P → Option (ℕ × D.S)) (a : P) : ackState acks a ≤ lub acks :=
  ((lub_le_iff _ _).1 (le_refl (lub acks))).2 a

lemma lub_le {acks : P → Option (ℕ × D.S)} {t : D.S} (h0 : D.s₀ ≤ t)
    (h : ∀ a, ackState acks a ≤ t) : lub acks ≤ t :=
  (lub_le_iff _ _).2 ⟨h0, h⟩

/-! ## Internal steps -/

/-- Starting a new attempt of the current query preserves the invariant. -/
lemma ProcInv.start {sent : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)} {p : P}
    {l₀ : Loc P D} {q : D.Q} {n : Option ℕ} {s : D.S} (hI : ProcInv QS sent h p l₀)
    (hb : l₀.phase ≠ .idle) (hq : opOf h (p, l₀.nOps - 1) = some (CRDT.Cmd.qry q)) :
    ProcInv QS (sent + outMsgs p (startAttempt p l₀ q n s).2) h p (startAttempt p l₀ q n s).1 := by
  have hbusy := hI.busy hb
  have hn := hI.nOps
  refine hI.keep (Multiset.le_add_right _ _) rfl rfl
    ⟨fun e => by simp [startAttempt] at e, fun e => absurd e hb⟩
    (fun k M e => by simp [startAttempt] at e) ?_ (fun _ _ _ _ _ e => by simp [startAttempt] at e)
    ?_ ?_ ?_
  · intro q' i acks e
    simp only [startAttempt, Phase.prep.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨rfl, by simp only; omega, hq, by simp⟩
  · intro a i n' σ hm
    rcases Multiset.mem_add.1 hm with hm | hm
    · exact Or.inl hm
    · right
      simp only [startAttempt, mem_outMsgs, mem_toAll, Msg.prepare.injEq] at hm
      obtain ⟨-, rfl, -, -⟩ := hm
      exact ⟨rfl, by simp only; omega⟩
  · intro a n' i σ hm
    rcases Multiset.mem_add.1 hm with hm | hm
    · exact Or.inl hm
    · simp [startAttempt, mem_outMsgs] at hm
  · intro a k σ hm
    rcases Multiset.mem_add.1 hm with hm | hm
    · exact hm
    · simp [startAttempt, mem_outMsgs] at hm

/-- Internal steps preserve the invariant of the process (if the test of line 13 implies
equality). -/
lemma ProcInv.internal (hcons : ∀ s t, V.cons s t = true → s = t)
    {sent : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)} {p : P}
    {l₀ l : Loc P D} {act : Act} {out : Multiset (P × Msg P D)} {r : Option D.spec.Resp}
    (hI : ProcInv QS sent h p l₀) (hst : internalStep V QS p act l₀ = some (l, out, r)) :
    ProcInv QS (sent + outMsgs p out) (h ++ (r.map (Label.ret p)).toList) p l := by
  unfold internalStep at hst
  split at hst
  · -- update completes
    rename_i k M hph
    split_ifs at hst with hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl, rfl⟩ := hst
    have hb : l₀.phase ≠ .idle := by rw [hph]; simp
    refine hI.respond hb rfl rfl fun j hj => Or.inl ?_
    obtain ⟨hk, u, hu⟩ := hI.ph_upd k M hph
    obtain rfl : j = k := by omega
    exact ⟨⟨u, hu⟩, rfl, rfl⟩
  · -- prepare phase
    rename_i q i acks hph
    have hb : l₀.phase ≠ .idle := by rw [hph]; simp
    obtain ⟨hi1, hi2, hq, hacks⟩ := hI.ph_prep q i acks hph
    split_ifs at hst with hQ hC hR
    · -- learned by consistent quorum
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      refine hI.respond hb rfl rfl fun j hj => Or.inr ⟨q, lub acks, false, ?_⟩
      obtain rfl : j = i.2.1 := by omega
      refine ⟨hq, rfl, rfl, i, hi1, rfl, by simp, fun _ => ?_⟩
      obtain ⟨Q, hQ, hQA⟩ := hQ
      refine ⟨ackers acks, ⟨Q, hQ, hQA⟩, fun a ha => ⟨ackNr acks a, ?_⟩⟩
      have := hacks a _ _ (acks_eq_of_mem_ackers ha)
      rw [hcons _ _ (hC a ha), hi1]; exact this
    · -- vote
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      simp only [Option.map_none, Option.toList_none, List.append_nil]
      refine hI.keep (Multiset.le_add_right _ _) rfl rfl ⟨fun e => by simp at e, fun e => absurd e hb⟩
        (fun k M e => by simp at e) (fun _ _ _ e => by simp at e) ?_ ?_ ?_ ?_
      · intro q' i' n s M e
        simp only [Phase.vote.injEq] at e
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
        refine ⟨hi1, hi2, hq, ⟨ackers acks, hQ, fun a ha => ⟨ackState acks a, ?_, ackState_le_lub _ _⟩⟩,
          by simp⟩
        have := hacks a _ _ (acks_eq_of_mem_ackers ha)
        rw [hR a ha] at this; rw [hi1]
        exact Multiset.mem_add.2 (Or.inl this)
      · intro a i' n' σ hm
        rcases Multiset.mem_add.1 hm with hm | hm
        · exact Or.inl hm
        · simp [mem_outMsgs] at hm
      · intro a n' i' σ hm
        rcases Multiset.mem_add.1 hm with hm | hm
        · exact Or.inl hm
        · right
          simp only [mem_outMsgs, mem_toAll, Msg.vote.injEq] at hm
          obtain ⟨-, -, rfl, -⟩ := hm
          exact ⟨hi1, by omega⟩
      · intro a k σ hm
        rcases Multiset.mem_add.1 hm with hm | hm
        · exact hm
        · simp [mem_outMsgs] at hm
    · -- retry with a fixed prepare
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      simp only [Option.map_none, Option.toList_none, List.append_nil]
      have : l₀.nOps - 1 = i.2.1 := by have := hI.nOps; omega
      exact hI.start hb (by rw [this]; exact hq)
  · -- learned by vote
    rename_i q i n s M hph
    have hb : l₀.phase ≠ .idle := by rw [hph]; simp
    obtain ⟨hi1, hi2, hq, hack, hM⟩ := hI.ph_vote q i n s M hph
    split_ifs at hst with hQ
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl, rfl⟩ := hst
    refine hI.respond hb rfl rfl fun j hj => Or.inr ⟨q, s, true, ?_⟩
    obtain rfl : j = i.2.1 := by omega
    refine ⟨hq, rfl, rfl, i, hi1, rfl, fun _ => ⟨n, hack, M, hQ, fun a ha => ?_⟩, by simp⟩
    rw [hi1]; exact hM a ha
  · -- retry from the prepare phase
    rename_i n q i acks hph
    have hb : l₀.phase ≠ .idle := by rw [hph]; simp
    obtain ⟨hi1, hi2, hq, -⟩ := hI.ph_prep q i acks hph
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl, rfl⟩ := hst
    simp only [Option.map_none, Option.toList_none, List.append_nil]
    have : l₀.nOps - 1 = i.2.1 := by have := hI.nOps; omega
    exact hI.start hb (by rw [this]; exact hq)
  · -- retry from the vote phase
    rename_i n q i n' s M hph
    have hb : l₀.phase ≠ .idle := by rw [hph]; simp
    obtain ⟨hi1, hi2, hq, -⟩ := hI.ph_vote q i n' s M hph
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl, rfl⟩ := hst
    simp only [Option.map_none, Option.toList_none, List.append_nil]
    have : l₀.nOps - 1 = i.2.1 := by have := hI.nOps; omega
    exact hI.start hb (by rw [this]; exact hq)
  · simp at hst

/-! ## Receptions -/

/-- Receptions preserve the invariant of the receiving process. -/
lemma ProcInv.recv {sent : Multiset (P × P × Msg P D)} {h : List (Label P D.spec)} {p src : P}
    {l₀ : Loc P D} {m : Msg P D} (hI : ProcInv QS sent h p l₀) (hm : (src, p, m) ∈ sent) :
    ProcInv QS (sent + outMsgs p (receiveStep V p src m l₀).2) h p (receiveStep V p src m l₀).1 := by
  have hle : sent ≤ sent + outMsgs p (receiveStep V p src m l₀).2 := Multiset.le_add_right _ _
  -- the messages sent by a reception are acceptor replies
  have hout : ∀ x ∈ (receiveStep V p src m l₀).2, x.2.IsAcc ∨ ∃ k, x.2 = .merged k := by
    intro x hx
    cases m <;> simp only [receiveStep] at hx <;> (try split_ifs at hx) <;> simp_all [Msg.IsAcc]
  have hpid : ∀ a i n σ, (p, a, Msg.prepare i n σ) ∈ sent + outMsgs p (receiveStep V p src m l₀).2 →
      (p, a, Msg.prepare i n σ) ∈ sent ∨ (i.1 = p ∧ i.2.1 < (opsOf h p).length) := by
    intro a i n σ hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact Or.inl hx
    · rcases hout _ (mem_outMsgs.1 hx).2 with h' | ⟨k, h'⟩ <;> simp [Msg.IsAcc] at h'
  have hvid : ∀ a n i σ, (p, a, Msg.vote n i σ) ∈ sent + outMsgs p (receiveStep V p src m l₀).2 →
      (p, a, Msg.vote n i σ) ∈ sent ∨ (i.1 = p ∧ i.2.1 < (opsOf h p).length) := by
    intro a n i σ hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact Or.inl hx
    · rcases hout _ (mem_outMsgs.1 hx).2 with h' | ⟨k, h'⟩ <;> simp [Msg.IsAcc] at h'
  have hmid : ∀ a k σ, (p, a, Msg.merge k σ) ∈ sent + outMsgs p (receiveStep V p src m l₀).2 →
      (p, a, Msg.merge k σ) ∈ sent := by
    intro a k σ hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact hx
    · rcases hout _ (mem_outMsgs.1 hx).2 with h' | ⟨k, h'⟩ <;> simp [Msg.IsAcc] at h'
  -- messages that do not change the proposer part
  have hsame : ∀ l : Loc P D, l.nOps = l₀.nOps → l.learned = l₀.learned → l.phase = l₀.phase →
      ProcInv QS (sent + outMsgs p (receiveStep V p src m l₀).2) h p l := by
    intro l hn hl hph
    refine hI.keep hle hn hl (by rw [hph]) ?_ ?_ ?_ hpid hvid hmid
    · intro k M e; rw [hph] at e; exact hI.ph_upd k M e
    · intro q i acks e; rw [hph] at e
      obtain ⟨h1, h2, h3, h4⟩ := hI.ph_prep q i acks e
      exact ⟨h1, h2, h3, fun a n σ ha => Multiset.mem_of_le hle (h4 a n σ ha)⟩
    · intro q i n s M e; rw [hph] at e
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI.ph_vote q i n s M e
      exact ⟨h1, h2, h3, h4.mono hle, fun a ha => Multiset.mem_of_le hle (h5 a ha)⟩
  cases m with
  | merge k s' => exact hsame _ rfl rfl rfl
  | prepare i n s' =>
    refine hsame _ ?_ ?_ ?_ <;> simp only [receiveStep] <;> split_ifs <;> rfl
  | vote n i s' =>
    refine hsame _ ?_ ?_ ?_ <;> simp only [receiveStep] <;> split_ifs <;> rfl
  | merged k =>
    simp only [receiveStep] at hsame hpid hvid hmid ⊢
    split
    · rename_i k₁ M hph
      split_ifs with hk
      · refine hI.keep hle rfl rfl ⟨fun e => by simp at e, fun e => by simp [hph] at e⟩ ?_
          (fun _ _ _ e => by simp at e) (fun _ _ _ _ _ e => by simp at e) hpid hvid hmid
        intro k₂ M₂ e
        simp only [Phase.upd.injEq] at e; obtain ⟨rfl, rfl⟩ := e
        exact hI.ph_upd _ M hph
      · exact hsame _ rfl rfl rfl
    · exact hsame _ rfl rfl rfl
  | ack n i s' =>
    simp only [receiveStep] at hsame hpid hvid hmid ⊢
    split
    · rename_i q i₁ acks hph
      split_ifs with hi
      · subst hi
        obtain ⟨h1, h2, h3, h4⟩ := hI.ph_prep q i acks hph
        refine hI.keep hle rfl rfl ⟨fun e => by simp at e, fun e => by simp [hph] at e⟩
          (fun _ _ e => by simp at e) ?_ (fun _ _ _ _ _ e => by simp at e) hpid hvid hmid
        intro q₂ i₂ acks₂ e
        simp only [Phase.prep.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
        refine ⟨h1, h2, h3, fun a n₂ σ ha => ?_⟩
        by_cases has : a = src
        · subst has
          rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          exact Multiset.mem_of_le hle hm
        · rw [Function.update_of_ne has] at ha
          exact Multiset.mem_of_le hle (h4 a n₂ σ ha)
      · exact hsame _ rfl rfl rfl
    · exact hsame _ rfl rfl rfl
  | voted n i s' =>
    simp only [receiveStep] at hsame hpid hvid hmid ⊢
    split
    · rename_i q i₁ n₁ s₁ M hph
      split_ifs with hi
      · obtain ⟨rfl, rfl, rfl⟩ := hi
        obtain ⟨h1, h2, h3, h4, h5⟩ := hI.ph_vote q i n s' M hph
        refine hI.keep hle rfl rfl ⟨fun e => by simp at e, fun e => by simp [hph] at e⟩
          (fun _ _ e => by simp at e) (fun _ _ _ e => by simp at e) ?_ hpid hvid hmid
        intro q₂ i₂ n₂ s₂ M₂ e
        simp only [Phase.vote.injEq] at e; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := e
        refine ⟨h1, h2, h3, h4.mono hle, fun a ha => ?_⟩
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact Multiset.mem_of_le hle hm
        · exact Multiset.mem_of_le hle (h5 a ha)
      · exact hsame _ rfl rfl rfl
    · exact hsame _ rfl rfl rfl

end Podc.CRDTReplication

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

lemma internalStep_busy {p : P} {a : Act} {l₀ l : Loc P D} {out : Multiset (P × Msg P D)}
    {r : Option D.spec.Resp} (hst : internalStep V QS p a l₀ = some (l, out, r)) :
    l₀.phase ≠ .idle := by
  intro hph
  unfold internalStep at hst
  rw [hph] at hst
  cases a <;> simp at hst

lemma trans_ofProc {sent : Multiset (P × P × Msg P D)} {p : P} {l₀ l : Loc P D}
    {out : Multiset (P × Msg P D)} {ℓ : Option (Label P D.spec)}
    (htr : Trans V QS sent p l₀ l out ℓ) : OfProc p ℓ.toList := by
  cases htr with
  | inv => simp [OfProc, Label.proc]
  | internal => rename_i r _; cases r <;> simp [OfProc, Label.proc]
  | recv => simp [OfProc]

/-- The process invariant of every process, and well-formedness of the history, hold in every
reachable configuration (if the test of line 13 implies equality). -/
theorem procInv_of_reach (hcons : ∀ s t, V.cons s t = true → s = t)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) : WellFormed h ∧ ∀ p, ProcInv QS C.sent h p (C.loc p) := by
  induction hr with
  | init =>
    refine ⟨fun β ℓ γ he => by simp at he, fun p => ?_⟩
    refine ⟨rfl, fun _ => rfl, fun e => absurd rfl e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Protocol.initCfg, alg, initLoc, opOf, Completed]
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    obtain ⟨hwf, hI⟩ := ih
    rcases reach_step_cases hr hs with ⟨hloc, hsent, rfl⟩ | ⟨p, l, out, htr, hloc, hsent⟩
    · simp only [Option.toList_none, List.append_nil]
      rw [hloc, hsent]; exact ⟨hwf, hI⟩
    · have hβ := trans_ofProc htr
      refine ⟨?_, fun q => ?_⟩
      · cases htr with
        | inv hst =>
          rename_i o
          have hidle : (C₀.loc p).phase = .idle := by
            unfold invokeStep at hst; split at hst
            · assumption
            · simp at hst
          exact hwf.append_inv ((hI p).idle hidle).symm
        | internal hst =>
          rename_i r
          cases r with
          | none => simpa using hwf
          | some res =>
            exact hwf.append_ret ((hI p).busy (internalStep_busy hst)).symm
        | recv => simpa using hwf
      · rw [hloc, hsent]
        by_cases hq : q = p
        · subst hq
          rw [Function.update_self]
          cases htr with
          | inv hst => exact (hI q).inv hst
          | internal hst => exact (hI q).internal hcons hst
          | recv hm => simpa using (hI q).recv hm
        · rw [Function.update_of_ne hq]
          refine (hI q).other (Multiset.le_add_right _ _) (fun x hx => ?_) hβ hq
          rcases Multiset.mem_add.1 hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (mem_outMsgs.1 hx).1

end Podc.CRDTReplication
