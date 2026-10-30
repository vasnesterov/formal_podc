import Papers.PODC2019.RDMAAgreement.RB.Good

/-!
# Algorithm 2 — the core lemma: L1 proofs of correct processes agree

The paper's argument (Appendix A, Property 2): two correct processes `r, r'` that built L1 proofs
for `(k, q)` both wrote their `Value` slot and *afterwards* read all `Value` slots; with regular
registers, the one whose echo write completed later sees the other's echo. We record, as ghost
state, the time `echoT` at which each echo write completed and the time `scanT` at which the scan
leading to an L1 proof started, and maintain:

* during a scan of `p` (started at `scanT`, after `p`'s own echo completed), every correct slot
  `j` already read either contributed `j`'s echo to `checkedVals`, or `j`'s echo completed only
  after `scanT` (`Late`);
* hence an L1 proof of correct `j` supports `j`'s echo `b`, and every correct process whose echo
  differs from `b` completed its echo after the scan of `j` started.

Two L1 proofs of correct processes for different values then give
`echoT j < scanT j < echoT j' < scanT j' < echoT j`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- The echo of `j` for `(q,k)` completed (if at all) after time `t`. -/
def Late (s : St P M) (j q : P) (k t : ℕ) : Prop := ∀ e, s.echoT j q k = some e → t < e

/-- Slot `j` was seen with `j`'s echo, or `j`'s echo completed after `t`. -/
def Seen (s : St P M) (q : P) (k t : ℕ) (acc : Finset (Copy P M)) (j : P) : Prop :=
  (∃ b, canon s j q k b ∧ (⟨j, b⟩ : Copy P M) ∈ acc) ∨ Late s j q k t

/-- Invariant of a scan of the `Value` slots in progress (lines 45–48). -/
def ScanOK (F : Finset P) (s : St P M) (p q i : P) (todo : Finset P) (acc : Finset (Copy P M)) :
    Prop :=
  (∃ e, s.echoT p q (s.key p q) = some e ∧ e < s.scanT p q) ∧ i ∉ todo ∧
  (∀ j ∉ F, j ∉ todo → j ≠ i → Seen s q (s.key p q) (s.scanT p q) acc j) ∧
  (i ∉ F → .bot ∈ s.cand p q → Late s i q (s.key p q) (s.scanT p q))

/-- What an L1 proof of a correct process `j` for `(q,k)`, supporting `b` and built from a scan
started at `sc`, guarantees. -/
def L1OK (F : Finset P) (s : St P M) (j q : P) (k : ℕ) (b : Base P M) (sc : ℕ) : Prop :=
  (∃ e, s.echoT j q k = some e ∧ e < sc) ∧ canon s j q k b ∧
  ∀ j' ∉ F, ∀ b', canon s j' q k b' → b' ≠ b → Late s j' q k sc

/-- The core invariants. -/
structure InvD (F : Finset P) (s : St P M) : Prop where
  scan : ∀ p ∉ F, ∀ q i todo acc, s.pc p q = .rdVal i todo acc → ScanOK F s p q i todo acc
  l1 : ∀ j ∉ F, ∀ q k b sc, s.l1 j q k = some (b, sc) → L1OK F s j q k b sc

lemma InvD.init [Inhabited P] : InvD F (St.init : St P M) := by
  refine ⟨?_, ?_⟩
  · intro p _ q i todo acc h; simp [St.init, PC.start] at h
  · intro j _ q k b sc h; simp [St.init] at h

/-! ### How ghost entries appear -/

lemma Step.echoT_new {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {j q : P} {k e : ℕ}
    (he : s'.echoT j q k = some e) : s.echoT j q k = some e ∨ e = s.now := by
  cases h with
  | echoDone hp hpc =>
    simp only [St.tick, St.write, St.setPhase, go_echoT, upd3_apply2, upd2_apply] at he
    split_ifs at he with hjq
    · by_cases hk : k = s.key j q
      · obtain ⟨rfl, rfl⟩ := hjq; subst hk; simp at he; exact Or.inr he.symm
      · obtain ⟨rfl, rfl⟩ := hjq; rw [Function.update_of_ne hk] at he; exact Or.inl he
    · exact Or.inl he
  | _ => left; simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase, St.doBcast] using he

lemma Step.l1_new {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {j q : P} {k : ℕ}
    {x : Base P M × ℕ} (hx : s'.l1 j q k = some x) : s.l1 j q k = some x ∨
      ∃ i acc v b, ℓ = .thr j q ∧ s.pc j q = .rdVal i ∅ acc ∧ v ∈ s.cand j q ∧
        (∀ c ∈ addVal i q (s.key j q) v acc, c.base = b) ∧
        f + 1 ≤ (addVal i q (s.key j q) v acc).card ∧ k = s.key j q ∧ x = (b, s.scanT j q) := by
  cases h with
  | @valOk p q' i acc v b hp hpc hv hcard hb =>
    simp only [St.tick, St.sign, go_l1, upd3_apply2, upd2_apply] at hx
    split_ifs at hx with hjq
    · obtain ⟨rfl, rfl⟩ := hjq
      by_cases hk : k = s.key j q
      · subst hk; simp at hx; exact Or.inr ⟨i, acc, v, b, rfl, hpc, hv, hb, hcard, rfl, hx.symm⟩
      · rw [Function.update_of_ne hk] at hx; exact Or.inl hx
    · exact Or.inl hx
  | _ => left; simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase, St.doBcast] using hx

/-- A pair becomes canonical for `(j,q,k)` only while `j`'s echo for `(q,k)` has not completed. -/
lemma Step.canon_new {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (IB : InvB F s)
    (h : Step F f s ℓ s') {j q : P} {k : ℕ} {b : Base P M} (hj : j ∉ F) (hc : canon s' j q k b) :
    canon s j q k b ∨ (s.echoT j q k = none ∧ s'.echoT j q k = none) := by
  obtain ⟨hs, hk, h1 | h1⟩ := hc
  · obtain ⟨rfl, h1⟩ := h1
    cases h with
    | @bcast p m hp hidle =>
      simp only [St.tick, St.doBcast] at h1
      by_cases hjp : q = p
      · subst hjp
        by_cases hkk : k = s.bnext q + 1
        · subst hkk
          right
          have hnone : s.echoT q q (s.bnext q + 1) = none := by
            rcases ho : s.echoT q q (s.bnext q + 1) with _ | e
            · rfl
            · obtain ⟨-, hne⟩ := (IA.thr q hj q).echoT _ e (by simpa [St.loc] using ho)
              rcases he : s.echo q q (s.bnext q + 1) with _ | b'
              · exact absurd he (by simpa [St.loc] using hne)
              · have := (IB.echo q hj q _ b' he).2.2 hj
                rw [(IA.bcast q hj).bcNone _ (by omega)] at this; cases this
          exact ⟨hnone, by simpa [St.tick, St.doBcast] using hnone⟩
        · left; simp only [Function.update_self] at h1
          rw [Function.update_of_ne hkk] at h1; exact ⟨hs, hk, Or.inl ⟨rfl, h1⟩⟩
      · left; rw [Function.update_of_ne hjp] at h1; exact ⟨hs, hk, Or.inl ⟨rfl, h1⟩⟩
    | _ =>
      left; refine ⟨hs, hk, Or.inl ⟨rfl, ?_⟩⟩
      simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase] using h1
  · rcases h.echo_new h1 with h1 | ⟨v, c, rfl, hpc, hv, hc, hs', hk', rfl, rfl⟩
    · exact Or.inl ⟨hs, hk, Or.inr h1⟩
    · right
      have hph : s.phase j q = .wfs := (IA.thr j hj q).ph .wfs (by simp [St.loc, hpc, PC.ph])
      have hnone : s.echoT j q (s.key j q) = none := by
        simpa [St.loc, St.key] using ((IA.thr j hj q).wfs hph).1
      cases h with
      | echoDone _ hpc' => rw [hpc] at hpc'; cases hpc'
      | _ =>
        exact ⟨hnone, by simpa [St.tick, St.sign, St.write, St.deliver, St.setPhase] using hnone⟩

/-! ### Transport of the auxiliary predicates -/

lemma Late.step {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {j q : P} {k t : ℕ}
    (hl : Late s j q k t) (ht : t < s.now) : Late s' j q k t := fun e he => by
  rcases h.echoT_new he with he | rfl
  · exact hl e he
  · exact ht

lemma Seen.step {s s' : St P M} {ℓ : Label P M} (G : Grows F s s') (h : Step F f s ℓ s')
    {q j : P} {k t : ℕ} {acc : Finset (Copy P M)} (hj : j ∉ F) (hs : Seen s q k t acc j)
    (ht : t < s.now) : Seen s' q k t acc j := by
  rcases hs with ⟨b, hb, hm⟩ | hl
  · exact Or.inl ⟨b, G.canon hj hb, hm⟩
  · exact Or.inr (hl.step h ht)

lemma L1OK.step {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (IB : InvB F s)
    (h : Step F f s ℓ s') {j q : P} {k : ℕ} {b : Base P M} {sc : ℕ} (hj : j ∉ F)
    (hl : L1OK F s j q k b sc) (ht : sc < s.now) : L1OK F s' j q k b sc := by
  have G := h.grows IA
  obtain ⟨⟨e, he, hlt⟩, hc, hlate⟩ := hl
  refine ⟨⟨e, G.echoT j hj _ _ _ he, hlt⟩, G.canon hj hc, fun j' hj' b' hb' hne => ?_⟩
  rcases h.canon_new IA IB hj' hb' with hb' | ⟨-, hnone⟩
  · exact (hlate j' hj' b' hb' hne).step h ht
  · intro e he; rw [hnone] at he; cases he

/-- The value returned by a read of a correct `Value` slot during a scan is "seen". -/
lemma read_seen {s : St P M} (IC : InvC F s) {p q i : P} {todo : Finset P}
    {acc : Finset (Copy P M)} (hpc : s.pc p q = .rdVal i todo acc) (hi : i ∉ F)
    (hd : .bot ∈ s.cand p q → Late s i q (s.key p q) (s.scanT p q)) {v : Val P M}
    (hv : v ∈ s.cand p q) :
    Seen s q (s.key p q) (s.scanT p q) (addVal i q (s.key p q) v acc) i := by
  rcases IC.good.cand p q _ (by rw [hpc]; rfl) v hv rfl hi with rfl | ⟨b, rfl, hb⟩
  · exact Or.inr (hd hv)
  · left; refine ⟨b, hb, ?_⟩
    obtain ⟨h1, h2, -⟩ := hb
    simp [addVal, h1, h2]

lemma Seen.mono_acc {s : St P M} {q j : P} {k t : ℕ} {acc acc' : Finset (Copy P M)}
    (hs : Seen s q k t acc j) (hsub : acc ⊆ acc') : Seen s q k t acc' j := by
  rcases hs with ⟨b, hb, hm⟩ | hl
  · exact Or.inl ⟨b, hb, hsub hm⟩
  · exact Or.inr hl

lemma subset_addVal (i q : P) (k : ℕ) (v : Val P M) (acc : Finset (Copy P M)) :
    acc ⊆ addVal i q k v acc := by
  unfold addVal; split
  · split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl
  · exact le_rfl

/-- A step not of thread `(p',q')` adds no `⊥` candidate to its pending read of a correct
register. -/
lemma Step.bot_cand {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {p' q' : P}
    (hℓ : ℓ ≠ .thr p' q') {r : Reg P} (hr : (s.pc p' q').rd q' (s.key p' q') = some r)
    (ho : r.owner ∉ F) (hb : (.bot : Val P M) ∈ s'.cand p' q') : .bot ∈ s.cand p' q' := by
  by_cases hT : ∃ p q, ℓ = .thr p q
  · obtain ⟨p, q, rfl⟩ := hT
    have hpq : ¬ (p' = p ∧ q' = q) := by rintro ⟨rfl, rfl⟩; exact hℓ rfl
    rcases h.thrEffect.cand_other p' q' hpq _ hb with hb | ⟨r', e1, -⟩
    · exact hb
    · exact absurd rfl (PC.wr_spec e1).1
  · push_neg at hT
    cases h with
    | bcast =>
      simp only [St.tick, St.doBcast, mem_addCand] at hb
      rcases hb with hb | ⟨-, hb⟩
      · exact hb
      · cases hb
    | byz hp hr0 =>
      rename_i p r0 v
      simp only [St.tick, St.write, mem_addCand] at hb
      rcases hb with hb | ⟨e, -⟩
      · exact hb
      · simp only [St.key] at hr e; rw [hr] at e; cases e; exact absurd (hr0 ▸ hp) ho
    | bret => simpa [St.tick, St.write] using hb
    | bretIdle => simpa [St.tick] using hb
    | _ => exact absurd rfl (hT _ _)

/-- After invoking a read of a correct `Value` slot, a `⊥` candidate means the owner's echo has
not completed. -/
private lemma late_of_fresh {s' : St P M} (IC' : InvC F s') {p q j : P} {k t : ℕ}
    (hself : ∀ x ∈ s'.cand p q, x = s'.mem ⟨.val, j, k, q⟩ ∨ x ∈ s'.pendW ⟨.val, j, k, q⟩)
    (hj : j ∉ F) (hb : (.bot : Val P M) ∈ s'.cand p q) : Late s' j q k t := by
  intro e he
  rcases hself _ hb with hb | hb
  · exact absurd hb.symm (IC'.nb j hj q k e he)
  · exact absurd hb (bot_not_mem_pendW _ _)

lemma InvD.step {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (IB : InvB F s) (IC : InvC F s)
    (I : InvD F s) (h : Step F f s ℓ s') : InvD F s' := by
  have G := h.grows IA
  have IC' := IC.step IA IB h
  refine ⟨?_, ?_⟩
  · intro p' hp' q' i todo acc hpc
    by_cases hself : ℓ = .thr p' q'
    · subst hself
      have E := h.thrEffect
      have h0 := h
      cases h with
      | @valNext _ _ i0 j todo0 acc0 v hp hpc0 hv hj =>
        simp [St.tick] at hpc; obtain ⟨rfl, rfl, rfl⟩ := hpc
        obtain ⟨⟨e, he, hlt⟩, hi, hseen, hd⟩ := I.scan p' hp' q' i0 todo0 acc0 hpc0
        have ht : s.scanT p' q' < s.now :=
          (IA.thr p' hp' q').scan _ _ _ (by simpa [St.loc] using hpc0)
        simp only [St.tick, key_go, go_scanT, go_echoT]
        refine ⟨⟨e, he, hlt⟩, Finset.notMem_erase _ _, fun j' hj' h1 h2 => ?_, fun hjF hb => ?_⟩
        · by_cases hji : j' = i0
          · subst hji
            exact (read_seen IC hpc0 hj' (hd hj') hv).step G h0 hj' ht
          · have h1' : j' ∉ todo0 := fun hm => h1 (Finset.mem_erase.2 ⟨h2, hm⟩)
            exact ((hseen j' hj' h1' hji).mono_acc (subset_addVal _ _ _ _ _)).step G h0 hj' ht
        · exact late_of_fresh IC' (E.cand_self _ (by simp [St.tick, PC.rd, St.key])) hjF
            (by simpa [St.tick] using hb)
      | @l2EndV _ _ i0 j v hp hpc0 hv hnv hph =>
        simp [St.tick] at hpc; obtain ⟨rfl, rfl, rfl⟩ := hpc
        have T := IA.thr p' hp' q'
        obtain ⟨e, he⟩ := T.echoed (by simp [St.loc, hph])
        simp only [St.loc] at he
        have hlt := (T.echoT _ e he).1
        unfold ScanOK
        simp only [St.tick, key_go, go_scanT, go_echoT, upd2_apply, and_self, if_true, St.key,
          go_last]
        refine ⟨⟨e, by simpa [St.key] using he, hlt⟩, Finset.notMem_erase _ _,
          fun j' _ h1 h2 => absurd (Finset.mem_erase.2 ⟨h2, Finset.mem_univ _⟩) h1,
          fun hjF hb => ?_⟩
        exact late_of_fresh IC' (E.cand_self _ (by simp [St.tick, PC.rd, St.key])) hjF
          (by simpa [St.tick] using hb)
      | _ => simp [St.tick, St.write, St.sign, St.deliver, St.setPhase, PC.start] at hpc
    · -- another thread's scan
      have hl : s'.loc p' q' = s.loc p' q' := by
        by_cases hT : ∃ p q, ℓ = .thr p q
        · obtain ⟨p, q, rfl⟩ := hT
          exact h.frame_thr.1 p' q' (by rintro ⟨rfl, rfl⟩; exact hself rfl)
        · push_neg at hT; exact (h.frame_other hT).1 p' q'
      simp only [St.loc, Loc.mk.injEq] at hl
      obtain ⟨hpc_eq, hlast, -, hscan, -, hechoT, -, -⟩ := hl
      rw [hpc_eq] at hpc
      have hk : s'.key p' q' = s.key p' q' := by simp [St.key, hlast]
      obtain ⟨⟨e, he, hlt⟩, hi, hseen, hd⟩ := I.scan p' hp' q' i todo acc hpc
      have ht : s.scanT p' q' < s.now := (IA.thr p' hp' q').scan _ _ _ (by simpa [St.loc] using hpc)
      unfold ScanOK
      rw [hk, hscan]
      refine ⟨⟨e, by rw [hechoT]; exact he, hlt⟩, hi, fun j hj h1 h2 =>
        (hseen j hj h1 h2).step G h hj ht, fun hiF hb => ?_⟩
      exact (hd hiF (h.bot_cand hself (by rw [hpc]; rfl) hiF hb)).step h ht
  · intro j hj q k b sc hl
    rcases h.l1_new hl with hl | ⟨i, acc, v, b0, rfl, hpc, hv, hb, hcard, rfl, hx⟩
    · exact (I.l1 j hj q k b sc hl).step IA IB h hj
        ((IA.thr j hj q).l1T _ _ _ (by simpa [St.loc] using hl))
    · cases hx
      obtain ⟨⟨e, he, hlt⟩, -, hseen, hd⟩ := I.scan j hj q i ∅ acc hpc
      have ht : s.scanT j q < s.now := (IA.thr j hj q).scan _ _ _ (by simpa [St.loc] using hpc)
      have D : ∀ j' ∉ F, Seen s q (s.key j q) (s.scanT j q) (addVal i q (s.key j q) v acc) j' := by
        intro j' hj'
        by_cases hji : j' = i
        · subst hji; exact read_seen IC hpc hj' (hd hj') hv
        · exact (hseen j' hj' (Finset.notMem_empty _) hji).mono_acc (subset_addVal _ _ _ _ _)
      have hcan : canon s j q (s.key j q) b := by
        rcases D j hj with ⟨b', hb', hm⟩ | hlate
        · have e1 : b' = b := hb _ hm
          rw [e1] at hb'; exact hb'
        · exact absurd (hlate e he) (by omega)
      refine ⟨⟨e, G.echoT j hj _ _ _ he, hlt⟩, G.canon hj hcan, fun j' hj' b' hb' hne => ?_⟩
      rcases h.canon_new IA IB hj' hb' with hb' | ⟨-, hnone⟩
      · rcases D j' hj' with ⟨b1, hb1, hm⟩ | hlate
        · have e1 : b1 = b := hb _ hm
          rw [e1] at hb1
          exact absurd (canon_unique IB hj' hb' hb1) hne
        · exact hlate.step h ht
      · intro e he; rw [hnone] at he; cases he

lemma InvD.reach [Inhabited P] {s : St P M} (h : Reachable F f s) : InvD F s := by
  induction h with
  | init => exact InvD.init
  | step hr hs ih => exact ih.step (InvA.reach hr) (InvB.reach hr) (InvC.reach hr) hs

/-- **Core lemma.** L1 proofs of correct processes for the same `(q,k)` support the same pair. -/
theorem l1_agree [Inhabited P] {s : St P M} (h : Reachable F f s) {j j' q : P} {k : ℕ}
    {b b' : Base P M} {sc sc' : ℕ} (hj : j ∉ F) (hj' : j' ∉ F) (hl : s.l1 j q k = some (b, sc))
    (hl' : s.l1 j' q k = some (b', sc')) : b = b' := by
  have ID := InvD.reach h
  obtain ⟨⟨e, he, hlt⟩, hc, hlate⟩ := ID.l1 j hj q k b sc hl
  obtain ⟨⟨e', he', hlt'⟩, hc', hlate'⟩ := ID.l1 j' hj' q k b' sc' hl'
  by_contra hne
  have h1 := hlate j' hj' b' hc' (Ne.symm hne) e' he'
  have h2 := hlate' j hj b hc hne e he
  omega

end Podc.RDMAAgreement.RB
