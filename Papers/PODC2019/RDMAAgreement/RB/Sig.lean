import Papers.PODC2019.RDMAAgreement.RB.Mono

/-!
# Algorithm 2 — unforgeability invariants

Every value in the system contains only signatures of correct processes that they actually
produced, and what a correct process signs tells us about its history.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

lemma SigOK.mono {S S' : Set (P × Sig P M)} {v : Val P M} (h : SigOK F S v) (hS : S ⊆ S') :
    SigOK F S' v := fun x hx hF => hS (h x hx hF)

lemma mem_copy_sigs {c : Copy P M} {x : P × Sig P M} :
    x ∈ c.sigs ↔ x = (c.base.sender, .base c.base) ∨ x = (c.signer, .endorse c.base) := by
  simp [Copy.sigs]

lemma sigOK_cp {S : Set (P × Sig P M)} {c : Copy P M} :
    SigOK F S (.cp c) ↔ (c.base.sender ∉ F → (c.base.sender, .base c.base) ∈ S) ∧
      (c.signer ∉ F → (c.signer, .endorse c.base) ∈ S) := by
  constructor
  · intro h; exact ⟨fun hF => h _ (by simp [Val.sigs, Copy.sigs]) hF,
      fun hF => h _ (by simp [Val.sigs, Copy.sigs]) hF⟩
  · rintro ⟨h1, h2⟩ x hx hF
    simp only [Val.sigs, Copy.sigs, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h1 hF
    · exact h2 hF

lemma sigOK_p1 {S : Set (P × Sig P M)} {π : L1 P M} :
    SigOK F S (.p1 π) ↔ (π.author ∉ F → (π.author, .l1 π) ∈ S) ∧
      ∀ c ∈ π.copies, SigOK F S (.cp c) := by
  constructor
  · intro h
    refine ⟨fun hF => h _ (by simp [Val.sigs, L1.sigs]) hF, fun c hc x hx hF => ?_⟩
    exact h x (by simp only [Val.sigs, L1.sigs, Set.mem_setOf_eq]; exact Or.inr ⟨c, hc, hx⟩) hF
  · rintro ⟨h1, h2⟩ x hx hF
    simp only [Val.sigs, L1.sigs, Set.mem_setOf_eq] at hx
    rcases hx with rfl | ⟨c, hc, hx⟩
    · exact h1 hF
    · exact h2 c hc x hx hF

lemma sigOK_p2 {S : Set (P × Sig P M)} {ρ : L2 P M} :
    SigOK F S (.p2 ρ) ↔ (ρ.author ∉ F → (ρ.author, .l2 ρ) ∈ S) ∧
      ∀ π ∈ ρ.proofs, SigOK F S (.p1 π) := by
  constructor
  · intro h
    refine ⟨fun hF => h _ (by simp [Val.sigs, L2.sigs]) hF, fun π hπ x hx hF => ?_⟩
    exact h x (by simp only [Val.sigs, L2.sigs, Set.mem_setOf_eq]; exact Or.inr ⟨π, hπ, hx⟩) hF
  · rintro ⟨h1, h2⟩ x hx hF
    simp only [Val.sigs, L2.sigs, Set.mem_setOf_eq] at hx
    rcases hx with rfl | ⟨π, hπ, hx⟩
    · exact h1 hF
    · exact h2 π hπ x hx hF

/-- Unforgeability invariants. -/
structure InvB (F : Finset P) (s : St P M) : Prop where
  reg : RegInv s (fun _ v => SigOK F s.signed v)
  accV : ∀ p q i todo acc, s.pc p q = .rdVal i todo acc → ∀ c ∈ acc,
    SigOK F s.signed (.cp c) ∧ c.base.sender = q ∧ c.base.key = s.key p q
  accL : ∀ p q i todo acc, s.pc p q = .rdL1 i todo acc → ∀ π ∈ acc, SigOK F s.signed (.p1 π)
  sBase : ∀ j ∉ F, ∀ b, (j, Sig.base b) ∈ s.signed → b.sender = j ∧ s.bc j b.key = some b.msg
  sEnd : ∀ j ∉ F, ∀ b, (j, Sig.endorse b) ∈ s.signed → canon s j b.sender b.key b
  sL1 : ∀ j ∉ F, ∀ π, (j, Sig.l1 π) ∈ s.signed → π.author = j ∧
    ∀ c ∈ π.copies, ∃ t, s.l1 j c.base.sender c.base.key = some (c.base, t)
  echo : ∀ j ∉ F, ∀ q k b, s.echo j q k = some b →
    b.sender = q ∧ b.key = k ∧ (q ∉ F → s.bc q k = some b.msg)

lemma InvB.init [Inhabited P] : InvB F (St.init : St P M) := by
  refine ⟨⟨fun r => ?_, fun r x hx => ?_, fun p q r _ x hx => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [St.init, SigOK, Val.sigs]
  · rcases hx with ⟨p, q, h⟩ | ⟨p, b, h, _⟩ <;> simp [St.init, PC.start, PC.wr] at h
  · simp only [St.init, Set.mem_singleton_iff] at hx; subst hx; simp [SigOK, Val.sigs]
  · intro p q i todo acc h; simp [St.init, PC.start] at h
  · intro p q i todo acc h; simp [St.init, PC.start] at h
  · intro j _ b h; simp [St.init] at h
  · intro j _ b h; simp [St.init] at h
  · intro j _ π h; simp [St.init] at h
  · intro j _ q k b h; simp [St.init] at h

/-- The candidate values read by a pending read are unforgeable. -/
lemma InvB.cand_sig {s : St P M} (I : InvB F s) {p q : P} {r : Reg P}
    (hr : (s.pc p q).rd q (s.key p q) = some r) {v : Val P M} (hv : v ∈ s.cand p q) :
    SigOK F s.signed v := I.reg.cand p q r hr v hv

/-- The values written by a thread step are unforgeable. -/
lemma InvB.newWrite {s s' : St P M} {p q : P} (IA : InvA F s) (I : InvB F s)
    (h : Step F f s (.thr p q) s') :
    ∀ r x, (s'.pc p q).wr p q (s'.key p q) = some (r, x) → SigOK F s'.signed x := by
  have G := h.grows IA
  intro r x hx
  cases h with
  | @l2Found _ _ i todo v ρ m hp hpc hv hρ hval =>
    simp [St.tick, PC.wr] at hx; obtain ⟨-, rfl⟩ := hx
    subst hρ; exact (I.cand_sig (by rw [hpc]; rfl) hv).mono G.signed
  | @sndOk _ _ v c hp hpc hv hc hs hk =>
    simp [St.tick, St.sign, PC.wr] at hx; obtain ⟨-, rfl⟩ := hx
    have hv' := I.cand_sig (by rw [hpc]; rfl) hv
    subst hc
    rw [sigOK_cp] at hv' ⊢
    refine ⟨fun hF => G.signed (hv'.1 hF), fun _ => ?_⟩
    simp [St.tick, St.sign]
  | @valOk _ _ i acc v b hp hpc hv hcard hb =>
    simp [St.tick, St.sign, PC.wr] at hx; obtain ⟨-, rfl⟩ := hx
    rw [sigOK_p1]
    refine ⟨fun _ => by simp [St.tick, St.sign], fun c hc => ?_⟩
    unfold addVal at hc
    split at hc
    · rename_i c'
      split_ifs at hc with hcc
      · rcases Finset.mem_insert.1 hc with rfl | hc
        · exact (I.cand_sig (by rw [hpc]; rfl) hv).mono G.signed
        · exact (I.accV p q i ∅ acc hpc c hc).1.mono G.signed
      · exact (I.accV p q i ∅ acc hpc c hc).1.mono G.signed
    · exact (I.accV p q i ∅ acc hpc c hc).1.mono G.signed
  | @l1Ok _ _ i acc v S m hp hpc hv hS hval =>
    simp [St.tick, St.sign, PC.wr] at hx; obtain ⟨-, rfl⟩ := hx
    rw [sigOK_p2]
    refine ⟨fun _ => by simp [St.tick, St.sign], fun π hπ => ?_⟩
    have hπ' := hS hπ
    unfold addL1 at hπ'
    split at hπ'
    · rcases Finset.mem_insert.1 hπ' with rfl | hπ'
      · exact (I.cand_sig (by rw [hpc]; rfl) hv).mono G.signed
      · exact (I.accL p q i ∅ acc hpc π hπ').mono G.signed
    · exact (I.accL p q i ∅ acc hpc π hπ').mono G.signed
  | _ => simp [St.tick, St.write, St.sign, St.deliver, St.setPhase, PC.wr, PC.start] at hx

/-- New signatures in a step come from specific transitions. -/
lemma Step.signed_new {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s')
    {x : P × Sig P M} (hx : x ∈ s'.signed) : x ∈ s.signed ∨
      (∃ p q v c, ℓ = .thr p q ∧ s.pc p q = .rdSnd ∧ v ∈ s.cand p q ∧ v = .cp c ∧
        c.base.sender = q ∧ c.base.key = s.key p q ∧ x = (p, .endorse c.base) ∧
        s'.echo p q (s.key p q) = some c.base) ∨
      (∃ p q i acc v b, ℓ = .thr p q ∧ s.pc p q = .rdVal i ∅ acc ∧ v ∈ s.cand p q ∧
        (∀ c ∈ addVal i q (s.key p q) v acc, c.base = b) ∧
        f + 1 ≤ (addVal i q (s.key p q) v acc).card ∧
        x = (p, .l1 ⟨p, addVal i q (s.key p q) v acc⟩) ∧
        s'.l1 p q (s.key p q) = some (b, s.scanT p q)) ∨
      (∃ p ρ, x = (p, .l2 ρ)) ∨
      (∃ p m, ℓ = .bcast p m ∧ (x = (p, .base ⟨p, s.bnext p + 1, m⟩) ∨
        x = (p, .endorse ⟨p, s.bnext p + 1, m⟩)) ∧ s'.bc p (s.bnext p + 1) = some m) := by
  cases h with
  | @sndOk _ _ v c hp hpc hv hc hs hk =>
    simp only [St.tick, St.sign, go_signed, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact Or.inr (Or.inl ⟨_, _, v, c, rfl, hpc, hv, hc, hs, hk, rfl, by simp [St.tick, St.sign]⟩)
    · exact Or.inl hx
  | @valOk _ _ i acc v b hp hpc hv hcard hb =>
    simp only [St.tick, St.sign, go_signed, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact Or.inr (Or.inr (Or.inl ⟨_, _, i, acc, v, b, rfl, hpc, hv, hb, hcard, rfl,
        by simp [St.tick, St.sign]⟩))
    · exact Or.inl hx
  | l1Ok =>
    simp only [St.tick, St.sign, go_signed, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
    · exact Or.inl hx
  | bcast hp hidle =>
    simp only [St.tick, St.doBcast, Set.mem_insert_iff] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl, Or.inl rfl, by simp [St.tick, St.doBcast]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl, Or.inr rfl, by simp [St.tick, St.doBcast]⟩)))
    · exact Or.inl hx
  | _ => left; simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase] using hx

/-- New echo entries only come from line 40. -/
lemma Step.echo_new {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {j q : P} {k : ℕ}
    {b : Base P M} (hb : s'.echo j q k = some b) : s.echo j q k = some b ∨
      ∃ v c, ℓ = .thr j q ∧ s.pc j q = .rdSnd ∧ v ∈ s.cand j q ∧ v = .cp c ∧
        c.base.sender = q ∧ c.base.key = s.key j q ∧ k = s.key j q ∧ b = c.base := by
  cases h with
  | @sndOk p q' v c hp hpc hv hc hs hk =>
    simp only [St.tick, St.sign, go_echo, upd3_apply2, upd2_apply] at hb
    split_ifs at hb with hjq
    · obtain ⟨rfl, rfl⟩ := hjq
      by_cases hk' : k = s.key j q
      · subst hk'; simp at hb; exact Or.inr ⟨v, c, rfl, hpc, hv, hc, hs, hk, rfl, hb.symm⟩
      · rw [Function.update_of_ne hk'] at hb; exact Or.inl hb
    · exact Or.inl hb
  | _ => left; simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase, St.doBcast] using hb

lemma InvB.step {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (I : InvB F s)
    (h : Step F f s ℓ s') : InvB F s' := by
  have G := h.grows IA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine I.reg.step h (fun r x hx => hx.mono G.signed) ?_ ?_ ?_
    · rintro p q rfl; exact I.newWrite IA h
    · rintro p m rfl
      cases h with
      | bcast => rw [sigOK_cp]; exact ⟨fun _ => by simp [St.tick, St.doBcast],
          fun _ => by simp [St.tick, St.doBcast]⟩
    · rintro p r v rfl
      cases h with
      | byz _ _ hv => exact hv.mono G.signed
  · intro p' q' i todo acc hpc c hc
    by_cases hℓ : ∃ p q, ℓ = .thr p q
    · obtain ⟨p, q, rfl⟩ := hℓ
      obtain ⟨hfr, -⟩ := h.frame_thr
      by_cases hpq : p' = p ∧ q' = q
      · obtain ⟨rfl, rfl⟩ := hpq
        cases h with
        | @valNext _ _ i0 j todo0 acc0 v hp hpc0 hv hj =>
          simp [St.tick] at hpc; obtain ⟨-, -, rfl⟩ := hpc
          simp only [St.tick, key_go]
          unfold addVal at hc
          split at hc
          · split_ifs at hc with hcc
            · rcases Finset.mem_insert.1 hc with rfl | hc
              · exact ⟨(I.cand_sig (by rw [hpc0]; rfl) hv).mono G.signed, hcc.2.1, hcc.2.2⟩
              · obtain ⟨h1, h2, h3⟩ := I.accV _ _ _ _ _ hpc0 c hc
                exact ⟨h1.mono G.signed, h2, h3⟩
            · obtain ⟨h1, h2, h3⟩ := I.accV _ _ _ _ _ hpc0 c hc
              exact ⟨h1.mono G.signed, h2, h3⟩
          · obtain ⟨h1, h2, h3⟩ := I.accV _ _ _ _ _ hpc0 c hc
            exact ⟨h1.mono G.signed, h2, h3⟩
        | l2EndV =>
          simp [St.tick] at hpc; obtain ⟨-, -, rfl⟩ := hpc; simp at hc
        | _ => simp [St.tick, St.write, St.sign, St.deliver, St.setPhase, PC.start] at hpc
      · have hl := hfr p' q' hpq
        simp only [St.loc, Loc.mk.injEq] at hl
        rw [hl.1] at hpc
        obtain ⟨h1, h2, h3⟩ := I.accV _ _ _ _ _ hpc c hc
        exact ⟨h1.mono G.signed, h2, by rw [h3]; simp [St.key, hl.2.1]⟩
    · push_neg at hℓ
      obtain ⟨hfr, -⟩ := h.frame_other hℓ
      have hl := hfr p' q'
      simp only [St.loc, Loc.mk.injEq] at hl
      rw [hl.1] at hpc
      obtain ⟨h1, h2, h3⟩ := I.accV _ _ _ _ _ hpc c hc
      exact ⟨h1.mono G.signed, h2, by rw [h3]; simp [St.key, hl.2.1]⟩
  · intro p' q' i todo acc hpc π hπ
    by_cases hℓ : ∃ p q, ℓ = .thr p q
    · obtain ⟨p, q, rfl⟩ := hℓ
      obtain ⟨hfr, -⟩ := h.frame_thr
      by_cases hpq : p' = p ∧ q' = q
      · obtain ⟨rfl, rfl⟩ := hpq
        cases h with
        | @l1Next _ _ i0 j todo0 acc0 v hp hpc0 hv hj =>
          simp [St.tick] at hpc; obtain ⟨-, -, rfl⟩ := hpc
          unfold addL1 at hπ
          split at hπ
          · rcases Finset.mem_insert.1 hπ with rfl | hπ
            · exact (I.cand_sig (by rw [hpc0]; rfl) hv).mono G.signed
            · exact (I.accL _ _ _ _ _ hpc0 π hπ).mono G.signed
          · exact (I.accL _ _ _ _ _ hpc0 π hπ).mono G.signed
        | l2EndL =>
          simp [St.tick] at hpc; obtain ⟨-, -, rfl⟩ := hpc; simp at hπ
        | _ => simp [St.tick, St.write, St.sign, St.deliver, St.setPhase, PC.start] at hpc
      · have hl := hfr p' q' hpq
        simp only [St.loc, Loc.mk.injEq] at hl
        rw [hl.1] at hpc
        exact (I.accL _ _ _ _ _ hpc π hπ).mono G.signed
    · push_neg at hℓ
      obtain ⟨hfr, -⟩ := h.frame_other hℓ
      have hl := hfr p' q'
      simp only [St.loc, Loc.mk.injEq] at hl
      rw [hl.1] at hpc
      exact (I.accL _ _ _ _ _ hpc π hπ).mono G.signed
  · intro j hj b hb
    rcases h.signed_new hb with hb | ⟨_, _, _, _, _, _, _, _, _, _, h1, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, h1, _⟩ | ⟨_, _, h1⟩ | ⟨p, m, rfl, h1, h2⟩
    · obtain ⟨e1, e2⟩ := I.sBase j hj b hb; exact ⟨e1, G.bc j hj _ _ e2⟩
    · cases h1
    · cases h1
    · cases h1
    · rcases h1 with h1 | h1 <;> cases h1; exact ⟨rfl, h2⟩
  · intro j hj b hb
    rcases h.signed_new hb with hb | ⟨p, q, v, c, rfl, hpc, hv, hc, hs, hk, h1, h2⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, h1, _⟩ | ⟨_, _, h1⟩ | ⟨p, m, rfl, h1, h2⟩
    · exact G.canon hj (I.sEnd j hj b hb)
    · cases h1; exact ⟨rfl, rfl, Or.inr (by rw [hs, hk]; exact h2)⟩
    · cases h1
    · cases h1
    · rcases h1 with h1 | h1 <;> cases h1; exact ⟨rfl, rfl, Or.inl ⟨rfl, h2⟩⟩
  · intro j hj π hπ
    rcases h.signed_new hπ with hπ | ⟨_, _, _, _, _, _, _, _, _, _, h1, _⟩ |
      ⟨p, q, i, acc, v, b, rfl, hpc, hv, hb, hcard, h1, h2⟩ | ⟨_, _, h1⟩ | ⟨p, m, rfl, h1, h2⟩
    · obtain ⟨e1, e2⟩ := I.sL1 j hj π hπ
      exact ⟨e1, fun c hc => by obtain ⟨t, ht⟩ := e2 c hc; exact ⟨t, G.l1 j hj _ _ _ ht⟩⟩
    · cases h1
    · cases h1
      refine ⟨rfl, fun c hc => ⟨s.scanT j q, ?_⟩⟩
      have hcb := hb c hc
      have hsk : c.base.sender = q ∧ c.base.key = s.key j q := by
        unfold addVal at hc
        split at hc
        · split_ifs at hc with hcc
          · rcases Finset.mem_insert.1 hc with rfl | hc
            · exact ⟨hcc.2.1, hcc.2.2⟩
            · exact ⟨(I.accV _ _ _ _ _ hpc c hc).2.1, (I.accV _ _ _ _ _ hpc c hc).2.2⟩
          · exact ⟨(I.accV _ _ _ _ _ hpc c hc).2.1, (I.accV _ _ _ _ _ hpc c hc).2.2⟩
        · exact ⟨(I.accV _ _ _ _ _ hpc c hc).2.1, (I.accV _ _ _ _ _ hpc c hc).2.2⟩
      rw [hsk.1, hsk.2, hcb]; exact h2
    · cases h1
    · rcases h1 with h1 | h1 <;> cases h1
  · intro j hj q k b hb
    rcases h.echo_new hb with hb | ⟨v, c, rfl, hpc, hv, hc, hs, hk, rfl, rfl⟩
    · obtain ⟨e1, e2, e3⟩ := I.echo j hj q k b hb
      exact ⟨e1, e2, fun hq => G.bc q hq _ _ (e3 hq)⟩
    · refine ⟨hs, hk, fun hq => ?_⟩
      have hv' := I.cand_sig (by rw [hpc]; rfl) hv
      subst hc
      have := (sigOK_cp.1 hv').1 (by rw [hs]; exact hq)
      obtain ⟨-, e⟩ := I.sBase _ (by rw [hs]; exact hq) _ this
      rw [hs] at e; rw [← hk]; exact G.bc q hq _ _ e

lemma InvB.reach [Inhabited P] {s : St P M} (h : Reachable F f s) : InvB F s := by
  induction h with
  | init => exact InvB.init
  | step hr hs ih => exact ih.step (InvA.reach hr) hs

end Podc.RDMAAgreement.RB
