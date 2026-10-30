import Papers.PODC2019.RDMAAgreement.RB.Totality
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Algorithm 2 — invariants used for Property (1) (validity)
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- A step that is not of thread `(r,q)` adds to its candidate set only values of pending writes
to the register it reads (or values written by a Byzantine owner). -/
lemma Step.cand_other {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {r q : P}
    (hℓ : ℓ ≠ .thr r q) {x : Val P M} (hx : x ∈ s'.cand r q) : x ∈ s.cand r q ∨
      ∃ rr, (s.pc r q).rd q (s.key r q) = some rr ∧ (x ∈ s'.pendW rr ∨ rr.owner ∈ F) := by
  by_cases hT : ∃ p' q', ℓ = .thr p' q'
  · obtain ⟨p', q', rfl⟩ := hT
    rcases h.thrEffect.cand_other r q (by rintro ⟨rfl, rfl⟩; exact hℓ rfl) x hx with
      h1 | ⟨rr, e1, e2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨rr, e2, Or.inl (Or.inl ⟨p', q', e1⟩)⟩
  · push_neg at hT
    cases h with
    | @bcast p m hp hidle =>
      simp only [St.tick, St.doBcast, mem_addCand, St.key] at hx
      rcases hx with hx | ⟨e, rfl⟩
      · exact Or.inl hx
      · refine Or.inr ⟨_, by simpa [St.key] using e, Or.inl (Or.inr ⟨p, _, ?_, rfl, rfl⟩)⟩
        simp [St.tick, St.doBcast]
    | byz hp hr0 =>
      simp only [St.tick, St.write, mem_addCand, St.key] at hx
      rcases hx with hx | ⟨e, -⟩
      · exact Or.inl hx
      · exact Or.inr ⟨_, by simpa [St.key] using e, Or.inr (hr0 ▸ hp)⟩
    | bret => exact Or.inl (by simpa [St.tick, St.write] using hx)
    | bretIdle => exact Or.inl (by simpa [St.tick] using hx)
    | _ => exact absurd rfl (hT _ _)

/-- Broadcast invariants of correct processes. -/
structure InvG (F : Finset P) (s : St P M) : Prop where
  bcIff : ∀ p ∉ F, ∀ k, s.bc p k ≠ none ↔ 1 ≤ k ∧ k ≤ s.bnext p
  written : ∀ p ∉ F, ∀ k, 1 ≤ k → k ≤ s.bnext p →
    (∃ b, s.bpend p = some b ∧ b.key = k) ∨ s.mem ⟨.val, p, k, p⟩ ≠ .bot

lemma InvG.init [Inhabited P] : InvG F (St.init : St P M) :=
  ⟨fun p _ k => by simp [St.init]; omega, fun p _ k h1 h2 => by simp [St.init] at h2; omega⟩

lemma InvG.step {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (I : InvG F s)
    (h : Step F f s ℓ s') : InvG F s' := by
  refine ⟨fun p hp k => ?_, fun p hp k h1 h2 => ?_⟩
  · cases h with
    | @bcast p' m hp' hidle =>
      simp only [St.tick, St.doBcast]
      by_cases hpp : p = p'
      · subst hpp; simp only [Function.update_self]
        by_cases hk : k = s.bnext p + 1
        · subst hk; simp
        · rw [Function.update_of_ne hk, I.bcIff p hp k]; omega
      · rw [Function.update_of_ne hpp, Function.update_of_ne hpp]; exact I.bcIff p hp k
    | _ => simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase] using I.bcIff p hp k
  · have hmem : s.mem ⟨.val, p, k, p⟩ ≠ .bot → s'.mem ⟨.val, p, k, p⟩ ≠ .bot :=
      h.mem_ne_bot (r := ⟨.val, p, k, p⟩) hp
    cases h with
    | @bcast p' m hp' hidle =>
      simp only [St.tick, St.doBcast] at h2 ⊢
      by_cases hpp : p = p'
      · subst hpp; simp only [Function.update_self] at h2 ⊢
        by_cases hk : k = s.bnext p + 1
        · subst hk; exact Or.inl ⟨_, rfl, rfl⟩
        · rcases I.written p hp k h1 (by omega) with ⟨b, hb, -⟩ | hm
          · rw [hidle] at hb; cases hb
          · exact Or.inr hm
      · rw [Function.update_of_ne hpp] at h2 ⊢; exact I.written p hp k h1 h2
    | @bret p' b hp' hb =>
      simp only [St.tick, St.write] at h2 ⊢
      by_cases hpp : p = p'
      · subst hpp; right
        by_cases hk : k = b.key
        · subst hk; simp
        · rcases I.written p hp k h1 h2 with ⟨b', hb', hk'⟩ | hm
          · rw [hb] at hb'; cases hb'; exact absurd hk'.symm hk
          · rw [Function.update_of_ne (by intro e; cases e; exact hk rfl)]; exact hm
      · rw [Function.update_of_ne hpp]
        rcases I.written p hp k h1 h2 with hb' | hm
        · exact Or.inl hb'
        · right; rw [Function.update_of_ne (by intro e; cases e; exact hpp rfl)]; exact hm
    | _ =>
      simp only [St.tick, St.write, St.sign, St.deliver, St.setPhase] at h2 hmem ⊢
      rcases I.written p hp k h1 h2 with hb' | hm
      · exact Or.inl hb'
      · exact Or.inr (hmem hm)

lemma InvG.reach [Inhabited P] {s : St P M} (h : Reachable F f s) : InvG F s := by
  induction h with
  | init => exact InvG.init
  | step hr hs ih => exact ih.step (InvA.reach hr) hs

lemma TStep.new_wrL1 {s s' : St P M} {r q : P} (T : TStep F f s s' r q) {π : L1 P M}
    (h : s'.pc r q = .wrL1 π) : ∃ i acc v b, s.pc r q = .rdVal i ∅ acc ∧ v ∈ s.cand r q ∧
      f + 1 ≤ (addVal i q (s.key r q) v acc).card ∧
      (∀ c ∈ addVal i q (s.key r q) v acc, c.base = b) ∧
      π = ⟨r, addVal i q (s.key r q) v acc⟩ ∧ s'.key r q = s.key r q := by
  cases T with
  | valOk i acc v b hpc hv hcard hb hpc' hk =>
    rw [hpc'] at h; cases h; exact ⟨i, acc, v, b, hpc, hv, hcard, hb, rfl, hk⟩
  | _ => simp_all [PC.start]

lemma TStep.new_wrL2 {s s' : St P M} {r q : P} (T : TStep F f s s' r q) {ρ : L2 P M}
    (h : s'.pc r q = .wrL2 ρ) : (∃ m, L2Valid f q (s.key r q) m ρ ∧ s'.key r q = s.key r q) ∨
      (s.pc r q = .wrL2 ρ ∧ s'.key r q = s.key r q) := by
  cases T with
  | l1Ok i acc v S m hpc hv hS hval hpc' hk =>
    rw [hpc'] at h; cases h; exact Or.inl ⟨m, hval, hk⟩
  | _ => simp_all [PC.start]

lemma TStep.new_wfl2 {s s' : St P M} {r q : P} (T : TStep F f s s' r q)
    (h : s'.phase r q = .wfl2) : (∃ π j, s.pc r q = .wrL1 π ∧ s'.pc r q = PC.start j) ∨
      (s.phase r q = .wfl2 ∧ (∀ π, s.pc r q ≠ .wrL1 π)) := by
  cases T with
  | l1Done j π hpc hpc' => exact Or.inl ⟨π, j, hpc, hpc'⟩
  | copy => simp_all
  | echo => simp_all
  | valOk i acc v b hpc _ _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | valNext i j todo acc v hpc _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | valBad i j acc v hpc _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | found i todo ρ m hpc _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | next i j todo v hpc _ _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | endS i v hpc _ _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | endV i j v hpc _ _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | endL i j v hpc _ _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | sndOk v c hpc _ _ _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | sndBad j v hpc _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | l1Next i j todo acc v hpc _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | l1Ok i acc v S m hpc _ _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | l1Bad i j acc v hpc _ _ _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩
  | l2Done j ρ hpc _ _ hph => right; rw [hph] at h; exact ⟨h, by simp [hpc]⟩

lemma TStep.key_eq_or {s s' : St P M} {r q : P} (T : TStep F f s s' r q) :
    s'.key r q = s.key r q ∨ s'.last r q = s.last r q + 1 := by
  cases T <;> first | (left; assumption) | (right; assumption)

/-- A register `X[x,κ,q]` (`X ≠ Value`) of a correct `x` changes only by steps of thread
`(x,q)`. -/
lemma Step.mem_own {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {kd : Kind} {x q : P}
    {κ : ℕ} (hx : x ∉ F) (hℓ : ℓ ≠ .thr x q) (hkd : kd ≠ .val) :
    s'.mem ⟨kd, x, κ, q⟩ = s.mem ⟨kd, x, κ, q⟩ := by
  by_cases hT : ∃ p' q', ℓ = .thr p' q'
  · obtain ⟨p', q', rfl⟩ := hT
    rcases h.thrEffect.mem ⟨kd, x, κ, q⟩ with e | e
    · exact e
    · exfalso
      cases hc : s.pc p' q' <;> simp [hc, PC.wr] at e <;>
        (obtain ⟨⟨rfl, rfl, -, rfl⟩, -⟩ := e; exact hℓ rfl)
  · push_neg at hT
    cases h with
    | bret => simp [St.tick, St.write, hkd]
    | byz hp hr =>
      rename_i p r0 v
      simp only [St.tick, St.write]
      rw [Function.update_of_ne]; rintro rfl; simp only at hr; exact hx (hr ▸ hp)
    | bcast => simp [St.tick, St.doBcast]
    | bretIdle => simp [St.tick]
    | _ => exact absurd rfl (hT _ _)

/-- L1 slots and pending L2 writes of correct processes. -/
structure InvH (F : Finset P) (f : ℕ) (s : St P M) : Prop where
  wrL1 : ∀ r ∉ F, ∀ q π, s.pc r q = .wrL1 π → π.author = r ∧
    ∃ b : Base P M, b.sender = q ∧ b.key = s.key r q ∧ L1Valid f q (s.key r q) b.msg π
  l1slot : ∀ r ∉ F, ∀ q, s.phase r q = .wfl2 → ∃ π, s.mem ⟨.l1, r, s.key r q, q⟩ = .p1 π ∧
    π.author = r ∧ ∃ b : Base P M, b.sender = q ∧ b.key = s.key r q ∧
      L1Valid f q (s.key r q) b.msg π
  wrL2 : ∀ r ∉ F, ∀ q ρ, s.pc r q = .wrL2 ρ → ∃ m, L2Valid f q (s.key r q) m ρ

lemma InvH.init [Inhabited P] : InvH F f (St.init : St P M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r _ q π h; simp [St.init, PC.start] at h
  · intro r _ q h; simp [St.init] at h
  · intro r _ q ρ h; simp [St.init, PC.start] at h

lemma InvH.step {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (IB : InvB F s) (I : InvH F f s)
    (h : Step F f s ℓ s') : InvH F f s' := by
  have hloc : ∀ r q, ℓ ≠ .thr r q → s'.loc r q = s.loc r q := fun r q hself => by
    by_cases hT : ∃ p q, ℓ = .thr p q
    · obtain ⟨p, q', rfl⟩ := hT
      exact h.frame_thr.1 r q (by rintro ⟨rfl, rfl⟩; exact hself rfl)
    · push_neg at hT; exact (h.frame_other hT).1 r q
  refine ⟨fun r hr q π hpc => ?_, fun r hr q hph => ?_, fun r hr q ρ hpc => ?_⟩
  · by_cases hself : ℓ = .thr r q
    · subst hself
      obtain ⟨i, acc, v, b, hpc0, hv, hcard, hb, rfl, hk⟩ := h.tstep.new_wrL1 hpc
      obtain ⟨c, hc⟩ := Finset.card_pos.1 (by omega : 0 < (addVal i q (s.key r q) v acc).card)
      have hsk : c.base.sender = q ∧ c.base.key = s.key r q := by
        unfold addVal at hc
        split at hc
        · split_ifs at hc with hcc
          · rcases Finset.mem_insert.1 hc with rfl | hc
            · exact ⟨hcc.2.1, hcc.2.2⟩
            · exact ⟨(IB.accV _ _ _ _ _ hpc0 c hc).2.1, (IB.accV _ _ _ _ _ hpc0 c hc).2.2⟩
          · exact ⟨(IB.accV _ _ _ _ _ hpc0 c hc).2.1, (IB.accV _ _ _ _ _ hpc0 c hc).2.2⟩
        · exact ⟨(IB.accV _ _ _ _ _ hpc0 c hc).2.1, (IB.accV _ _ _ _ _ hpc0 c hc).2.2⟩
      rw [hb c hc] at hsk
      obtain ⟨hs1, hs2⟩ := hsk
      refine ⟨rfl, b, hs1, by rw [hk]; exact hs2, ?_⟩
      rw [hk]
      refine ⟨hcard, fun c' hc' => ?_⟩
      rw [hb c' hc']; cases b; simp_all
    · have hl := hloc r q hself
      simp only [St.loc, Loc.mk.injEq] at hl
      have hk : s'.key r q = s.key r q := by simp [St.key, hl.2.1]
      rw [hl.1] at hpc; rw [hk]; exact I.wrL1 r hr q π hpc
  · by_cases hself : ℓ = .thr r q
    · subst hself
      have E := h.thrEffect
      have T := h.tstep
      have hk : s'.key r q = s.key r q := by
        rcases T.key_or_copy with hk | ⟨-, hk⟩
        · exact hk
        · rw [hk] at hph; cases hph
      rcases T.new_wfl2 hph with ⟨π, j, hpc0, hpc'⟩ | ⟨hph0, hnw⟩
      · obtain ⟨ha, b, hb1, hb2, hb3⟩ := I.wrL1 r hr q π hpc0
        refine ⟨π, ?_, ha, b, hb1, by rw [hk]; exact hb2, by rw [hk]; exact hb3⟩
        cases T with
        | l1Done _ _ hpc1 _ _ _ hmem => rw [hpc0] at hpc1; cases hpc1; rw [hk]; exact hmem
        | _ => simp_all [PC.start]
      · obtain ⟨π, hm, ha, b, hb⟩ := I.l1slot r hr q hph0
        refine ⟨π, ?_, ha, b, by rw [hk]; exact hb⟩
        rcases E.mem ⟨.l1, r, s'.key r q, q⟩ with e | e
        · rw [e, hk]; exact hm
        · rw [hk] at e
          cases hc : s.pc r q <;> simp [hc, PC.wr] at e
          exact absurd hc (hnw _)
    · have hl := hloc r q hself
      simp only [St.loc, Loc.mk.injEq] at hl
      have hk : s'.key r q = s.key r q := by simp [St.key, hl.2.1]
      rw [hl.2.2.1] at hph
      obtain ⟨π, hm, hrest⟩ := I.l1slot r hr q hph
      refine ⟨π, ?_, by rw [hk]; exact hrest⟩
      rw [hk]
      rw [h.mem_own hr hself (by simp)]; exact hm
  · by_cases hself : ℓ = .thr r q
    · subst hself
      rcases h.tstep.new_wrL2 hpc with ⟨m, hm, hk⟩ | ⟨hpc0, hk⟩
      · exact ⟨m, by rw [hk]; exact hm⟩
      · rw [hk]; exact I.wrL2 r hr q ρ hpc0
    · have hl := hloc r q hself
      simp only [St.loc, Loc.mk.injEq] at hl
      have hk : s'.key r q = s.key r q := by simp [St.key, hl.2.1]
      rw [hl.1] at hpc; rw [hk]; exact I.wrL2 r hr q ρ hpc

lemma InvH.reach [Inhabited P] {s : St P M} (h : Reachable F f s) : InvH F f s := by
  induction h with
  | init => exact InvH.init
  | step hr hs ih => exact ih.step (InvA.reach hr) (InvB.reach hr) hs

/-- Pending writes to L2 slots of correct processes carry valid L2 proofs. -/
lemma pend_l2_valid {s : St P M} (IE : InvE F f s) (IH : InvH F f s) {x q : P} {κ : ℕ}
    (hx : x ∉ F) {v : Val P M} (hv : v ∈ s.pendW ⟨.l2, x, κ, q⟩) :
    ∃ ρ m, v = .p2 ρ ∧ L2Valid f q κ m ρ := by
  rcases hv with ⟨p', q', hw⟩ | ⟨p', b, -, hr, -⟩
  · cases hc : s.pc p' q' <;> simp [hc, PC.wr] at hw
    · obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hw
      exact ⟨_, _, rfl, IE.wrCopy _ hx _ _ _ hc⟩
    · obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hw
      obtain ⟨m, hm⟩ := IH.wrL2 _ hx _ _ hc
      exact ⟨_, m, rfl, hm⟩
  · cases hr

/-- Once the L2 slot of a correct process holds a valid proof, it always does. -/
lemma Step.slotOK {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') (IE : InvE F f s)
    (IH : InvH F f s) (IE' : InvE F f s') (IH' : InvH F f s') {x q : P} {κ : ℕ} (hx : x ∉ F)
    (hs : SlotOK f s x κ q) : SlotOK f s' x κ q := by
  refine ⟨?_, fun v hv => pend_l2_valid IE' IH' hx hv⟩
  by_cases hT : ∃ p' q', ℓ = .thr p' q'
  · obtain ⟨p', q', rfl⟩ := hT
    rcases h.thrEffect.mem ⟨.l2, x, κ, q⟩ with e | e
    · rw [e]; exact hs.1
    · exact pend_l2_valid IE IH hx (Or.inl ⟨p', q', e⟩)
  · push_neg at hT
    have : s'.mem ⟨.l2, x, κ, q⟩ = s.mem ⟨.l2, x, κ, q⟩ := by
      cases h with
      | bret => simp [St.tick, St.write]
      | byz hp hr =>
        rename_i p r0 v
        simp only [St.tick, St.write]
        rw [Function.update_of_ne]; rintro rfl; simp only at hr; exact hx (hr ▸ hp)
      | bcast => simp [St.tick, St.doBcast]
      | bretIdle => simp [St.tick]
      | _ => exact absurd rfl (hT _ _)
    rw [this]; exact hs.1

/-- A correct sender's signature on `(k, m')` means it broadcast `(k, m')`. -/
lemma bc_of_sig {s : St P M} (IB : InvB F s) {c : Copy P M} (hs : SigOK F s.signed (.cp c))
    (hp : c.base.sender ∉ F) : s.bc c.base.sender c.base.key = some c.base.msg :=
  (IB.sBase _ hp _ ((sigOK_cp.1 hs).1 hp)).2

/-- The canonical pair of a correct process for a correct sender is that sender's broadcast. -/
lemma bc_of_canon {s : St P M} (IB : InvB F s) {j p : P} {k : ℕ} {b : Base P M} (hj : j ∉ F)
    (hp : p ∉ F) (hc : canon s j p k b) : b = ⟨p, k, b.msg⟩ ∧ s.bc p k = some b.msg := by
  obtain ⟨hs, hk, h | h⟩ := hc
  · obtain ⟨rfl, h⟩ := h; refine ⟨?_, h⟩; cases b; simp_all
  · obtain ⟨-, -, e⟩ := IB.echo j hj p k b h
    refine ⟨?_, e hp⟩; cases b; simp_all

/-- Finitely many eventual monotone properties hold simultaneously eventually. -/
lemma eventually_all {Q : P → ℕ → Prop} (hmono : ∀ r ∉ F, ∀ t t', t ≤ t' → Q r t → Q r t')
    (h : ∀ r ∉ F, ∃ t, Q r t) : ∃ T, ∀ r ∉ F, ∀ t ≥ T, Q r t := by
  classical
  choose! g hg using h
  refine ⟨(Finset.univ.filter (· ∉ F)).sup g, fun r hr t ht => hmono r hr _ _ ?_ (hg r hr)⟩
  exact le_trans (Finset.le_sup (f := g) (by simpa using hr)) ht

end Podc.RDMAAgreement.RB
