import Papers.PODC2019.RDMAAgreement.RB.Safety

/-!
# Algorithm 2 — liveness infrastructure

* `eventually_of_measure`: in a fair execution, if every step of a correct thread decreases a
  measure (or reaches the goal) and other steps do not increase it, the goal is reached.
* monotonicity of `last`, and the delivery invariants `InvF` (deliveries are consecutive and
  every delivered key has a valid L2 proof in the deliverer's slot forever).
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- Measure argument for one correct thread `(p,q)` in a fair execution. -/
theorem eventually_of_measure [Inhabited P] (e : Exec (M := M) F f) (hfair : e.Fair) {p q : P}
    (hp : p ∉ F) (G : ℕ → Prop) (μ : ℕ → ℕ) (t0 : ℕ)
    (hstep : ∀ t ≥ t0, ¬ G t → G (t + 1) ∨
      (e.ℓ t = .thr p q → μ (t + 1) < μ t) ∧ μ (t + 1) ≤ μ t) :
    ∃ t ≥ t0, G t := by
  induction hμ : μ t0 using Nat.strong_induction_on generalizing t0 with
  | _ n ih =>
    by_cases hG : G t0
    · exact ⟨t0, le_rfl, hG⟩
    obtain ⟨t1, ht1, hl⟩ := hfair.1 p hp q t0
    -- between `t0` and `t1` the measure does not increase (or the goal is reached)
    have key : ∀ d, t0 + d ≤ t1 → (∃ t ≥ t0, G t) ∨ μ (t0 + d) ≤ μ t0 := by
      intro d
      induction d with
      | zero => intro _; exact Or.inr le_rfl
      | succ d ihd =>
        intro hd
        rcases ihd (by omega) with h | h
        · exact Or.inl h
        · by_cases hGd : G (t0 + d)
          · exact Or.inl ⟨t0 + d, by omega, hGd⟩
          · rcases hstep (t0 + d) (by omega) hGd with h' | ⟨-, h'⟩
            · exact Or.inl ⟨t0 + d + 1, by omega, h'⟩
            · exact Or.inr (le_trans h' h)
    rcases key (t1 - t0) (by omega) with h | h
    · exact h
    · rw [show t0 + (t1 - t0) = t1 by omega] at h
      by_cases hG1 : G t1
      · exact ⟨t1, ht1, hG1⟩
      rcases hstep t1 ht1 hG1 with h' | ⟨h', -⟩
      · exact ⟨t1 + 1, by omega, h'⟩
      · have hlt : μ (t1 + 1) < n := by have := h' hl; omega
        obtain ⟨t, ht, hGt⟩ := ih _ hlt (t1 + 1) (fun t ht => hstep t (by omega)) rfl
        exact ⟨t, by omega, hGt⟩

/-! ### `last` and deliveries -/

lemma Step.last_mono {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') (p q : P) :
    s.last p q ≤ s'.last p q ∧ (s'.last p q ≠ s.last p q → ℓ = .thr p q ∧
      s'.last p q = s.last p q + 1) := by
  by_cases hT : ∃ p' q', ℓ = .thr p' q'
  · obtain ⟨p', q', rfl⟩ := hT
    by_cases hpq : p = p' ∧ q = q'
    · obtain ⟨rfl, rfl⟩ := hpq
      cases h with
      | copyDone =>
        simp [St.tick, St.deliver, St.write]
      | _ => simp [St.tick, St.write, St.sign, St.setPhase]
    · have hl := h.frame_thr.1 p q hpq
      simp only [St.loc, Loc.mk.injEq] at hl
      rw [hl.2.1]; exact ⟨le_rfl, fun h => absurd rfl h⟩
  · push_neg at hT
    have hl := (h.frame_other hT).1 p q
    simp only [St.loc, Loc.mk.injEq] at hl
    rw [hl.2.1]; exact ⟨le_rfl, fun h => absurd rfl h⟩

lemma Exec.last_mono [Inhabited P] (e : Exec (M := M) F f) (p q : P) {t t' : ℕ} (h : t ≤ t') :
    (e.s t).last p q ≤ (e.s t').last p q := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih ((e.step _).last_mono p q).1

/-- The L2 proof that justified a delivery of correct `p` stays in `p`'s slot. -/
def SlotOK (f : ℕ) (s : St P M) (x : P) (κ : ℕ) (q : P) : Prop :=
  (∃ ρ m, s.mem ⟨.l2, x, κ, q⟩ = .p2 ρ ∧ L2Valid f q κ m ρ) ∧
  ∀ v ∈ s.pendW ⟨.l2, x, κ, q⟩, ∃ ρ m, v = .p2 ρ ∧ L2Valid f q κ m ρ

lemma ThreadOK.dlv_le {now : ℕ} {l : Loc P M} (T : ThreadOK now l) {k : ℕ} {m : M}
    (h : l.dlv k = some m) : k ≤ l.last := by
  by_contra hk
  rcases Nat.lt_or_ge (l.last + 1) k with hk' | hk'
  · rw [(T.future k hk').2.2.2] at h; cases h
  · rw [show k = l.last + 1 by omega, T.dlvCur] at h; cases h

/-- A register `X[x,κ,q]` with `κ` different from the current key of thread `(x,q)` of a correct
`x` is not modified (it can only be written by that thread, at its current key). -/
lemma Step.mem_frame {s s' : St P M} {ℓ : Label P M} (h : Step F f s ℓ s') {kd : Kind} {x q : P}
    {κ : ℕ} (hx : x ∉ F) (hκ : κ ≠ s.key x q) (hkd : kd ≠ .val) :
    s'.mem ⟨kd, x, κ, q⟩ = s.mem ⟨kd, x, κ, q⟩ := by
  by_cases hT : ∃ p' q', ℓ = .thr p' q'
  · obtain ⟨p', q', rfl⟩ := hT
    rcases h.thrEffect.mem ⟨kd, x, κ, q⟩ with e | e
    · exact e
    · exfalso
      cases hc : s.pc p' q' <;> simp [hc, PC.wr] at e <;>
        (obtain ⟨⟨rfl, rfl, rfl, rfl⟩, -⟩ := e; exact hκ rfl)
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

/-- Delivery invariants of correct processes. -/
structure InvF (F : Finset P) (f : ℕ) (s : St P M) : Prop where
  dlvIff : ∀ p ∉ F, ∀ q k, s.dlv p q k ≠ none ↔ 1 ≤ k ∧ k ≤ s.last p q
  slot : ∀ p ∉ F, ∀ q k m, s.dlv p q k = some m →
    ∃ ρ, s.mem ⟨.l2, p, k, q⟩ = .p2 ρ ∧ L2Valid f q k m ρ

lemma InvF.init [Inhabited P] : InvF F f (St.init : St P M) := by
  refine ⟨fun p _ q k => ?_, fun p _ q k m h => ?_⟩
  · simp [St.init]; omega
  · simp [St.init] at h

lemma InvF.step {s s' : St P M} {ℓ : Label P M} (IA : InvA F s) (IE : InvE F f s)
    (I : InvF F f s) (h : Step F f s ℓ s') : InvF F f s' := by
  have IA' := IA.step h
  refine ⟨fun p hp q k => ?_, fun p hp q k m hd => ?_⟩
  · by_cases hself : ℓ = .thr p q
    · subst hself
      cases h with
      | @copyDone _ _ j ρ m0 _ hpc =>
        simp only [St.tick, St.write, St.deliver, go_dlv, go_last, upd3_apply2, upd2_apply,
          and_self, if_true, St.key]
        by_cases hk : k = s.last p q + 1
        · subst hk; simp
        · rw [Function.update_of_ne hk, I.dlvIff p hp q k]; omega
      | _ =>
        simpa [St.tick, St.write, St.sign, St.setPhase, St.key] using I.dlvIff p hp q k
    · have hl : s'.loc p q = s.loc p q := by
        by_cases hT : ∃ p' q', ℓ = .thr p' q'
        · obtain ⟨p', q', rfl⟩ := hT
          exact h.frame_thr.1 p q (by rintro ⟨rfl, rfl⟩; exact hself rfl)
        · push_neg at hT; exact (h.frame_other hT).1 p q
      simp only [St.loc, Loc.mk.injEq] at hl
      rw [hl.2.1, hl.2.2.2.2.2.2.2]; exact I.dlvIff p hp q k
  · by_cases hold : s.dlv p q k = some m
    · obtain ⟨ρ, hρ, hv⟩ := I.slot p hp q k m hold
      have hk := (IA.thr p hp q).dlv_le (by simpa [St.loc] using hold)
      refine ⟨ρ, ?_, hv⟩
      rw [h.mem_frame hp (by simp only [St.loc] at hk; simp [St.key]; omega) (by simp)]
      exact hρ
    · cases h with
      | @copyDone p' q' j ρ m0 _ hpc =>
        simp only [St.tick, St.write, St.deliver, go_dlv, upd3_apply2, upd2_apply, St.key] at hd
        split_ifs at hd with hpq
        · obtain ⟨rfl, rfl⟩ := hpq
          by_cases hk : k = s.last p q + 1
          · subst hk; simp at hd; subst hd
            refine ⟨ρ, by simp [St.tick, St.write, St.deliver, St.key], ?_⟩
            simpa [St.key] using IE.wrCopy p hp q ρ m0 hpc
          · rw [Function.update_of_ne hk] at hd; exact absurd hd hold
        · exact absurd hd hold
      | _ => exact absurd (by simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase,
          St.doBcast] using hd) hold

lemma InvF.reach [Inhabited P] (hF : F.card ≤ f) {s : St P M} (h : Reachable F f s) :
    InvF F f s := by
  induction h with
  | init => exact InvF.init
  | step hr hs ih => exact ih.step (InvA.reach hr) (InvE.reach hF hr) hs

/-- Summary of a step of delivery thread `(r,q)`: old and new program counter, key and phase. -/
inductive TStep (F : Finset P) (f : ℕ) (s s' : St P M) (r q : P) : Prop
  | found (i : P) (todo : Finset P) (ρ : L2 P M) (m : M) (hpc : s.pc r q = .rdL2 i todo)
      (hv : .p2 ρ ∈ s.cand r q) (hval : L2Valid f q (s.key r q) m ρ)
      (hpc' : s'.pc r q = .wrCopy ρ m) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | next (i j : P) (todo : Finset P) (v : Val P M) (hpc : s.pc r q = .rdL2 i todo)
      (hv : v ∈ s.cand r q) (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key r q) m ρ)
      (hj : j ∈ todo) (hpc' : s'.pc r q = .rdL2 j (todo.erase j)) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | endS (i : P) (v : Val P M) (hpc : s.pc r q = .rdL2 i ∅) (hv : v ∈ s.cand r q)
      (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key r q) m ρ) (hph0 : s.phase r q = .wfs)
      (hpc' : s'.pc r q = .rdSnd) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | endV (i j : P) (v : Val P M) (hpc : s.pc r q = .rdL2 i ∅) (hv : v ∈ s.cand r q)
      (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key r q) m ρ) (hph0 : s.phase r q = .wfl1)
      (hpc' : s'.pc r q = .rdVal j (Finset.univ.erase j) ∅) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | endL (i j : P) (v : Val P M) (hpc : s.pc r q = .rdL2 i ∅) (hv : v ∈ s.cand r q)
      (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key r q) m ρ) (hph0 : s.phase r q = .wfl2)
      (hpc' : s'.pc r q = .rdL1 j (Finset.univ.erase j) ∅) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | copy (j : P) (ρ : L2 P M) (m : M) (hpc : s.pc r q = .wrCopy ρ m)
      (hlast : s'.last r q = s.last r q + 1) (hpc' : s'.pc r q = PC.start j)
      (hph : s'.phase r q = .wfs)
  | sndOk (v : Val P M) (c : Copy P M) (hpc : s.pc r q = .rdSnd) (hv : v ∈ s.cand r q)
      (hc : v = .cp c) (hs : c.base.sender = q) (hk0 : c.base.key = s.key r q)
      (hpc' : s'.pc r q = .wrEcho c.base) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | sndBad (j : P) (v : Val P M) (hpc : s.pc r q = .rdSnd) (hv : v ∈ s.cand r q)
      (hbad : ¬ ∃ c, v = .cp c ∧ c.base.sender = q ∧ c.base.key = s.key r q)
      (hpc' : s'.pc r q = PC.start j) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | echo (j : P) (b : Base P M) (hpc : s.pc r q = .wrEcho b) (hpc' : s'.pc r q = PC.start j)
      (hk : s'.key r q = s.key r q) (hph : s'.phase r q = .wfl1)
  | valNext (i j : P) (todo : Finset P) (acc : Finset (Copy P M)) (v : Val P M)
      (hpc : s.pc r q = .rdVal i todo acc) (hv : v ∈ s.cand r q) (hj : j ∈ todo)
      (hpc' : s'.pc r q = .rdVal j (todo.erase j) (addVal i q (s.key r q) v acc))
      (hk : s'.key r q = s.key r q) (hph : s'.phase r q = s.phase r q)
  | valOk (i : P) (acc : Finset (Copy P M)) (v : Val P M) (b : Base P M)
      (hpc : s.pc r q = .rdVal i ∅ acc) (hv : v ∈ s.cand r q)
      (hcard : f + 1 ≤ (addVal i q (s.key r q) v acc).card)
      (hb : ∀ c ∈ addVal i q (s.key r q) v acc, c.base = b)
      (hpc' : s'.pc r q = .wrL1 ⟨r, addVal i q (s.key r q) v acc⟩)
      (hk : s'.key r q = s.key r q) (hph : s'.phase r q = s.phase r q)
  | valBad (i j : P) (acc : Finset (Copy P M)) (v : Val P M) (hpc : s.pc r q = .rdVal i ∅ acc)
      (hv : v ∈ s.cand r q)
      (hbad : ¬ (f + 1 ≤ (addVal i q (s.key r q) v acc).card ∧
                ∃ b, ∀ c ∈ addVal i q (s.key r q) v acc, c.base = b))
      (hpc' : s'.pc r q = PC.start j) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | l1Done (j : P) (π : L1 P M) (hpc : s.pc r q = .wrL1 π) (hpc' : s'.pc r q = PC.start j)
      (hk : s'.key r q = s.key r q) (hph : s'.phase r q = .wfl2)
      (hmem : s'.mem ⟨.l1, r, s.key r q, q⟩ = .p1 π)
  | l1Next (i j : P) (todo : Finset P) (acc : Finset (L1 P M)) (v : Val P M)
      (hpc : s.pc r q = .rdL1 i todo acc) (hv : v ∈ s.cand r q) (hj : j ∈ todo)
      (hpc' : s'.pc r q = .rdL1 j (todo.erase j) (addL1 v acc))
      (hk : s'.key r q = s.key r q) (hph : s'.phase r q = s.phase r q)
  | l1Ok (i : P) (acc : Finset (L1 P M)) (v : Val P M) (S : Finset (L1 P M)) (m : M)
      (hpc : s.pc r q = .rdL1 i ∅ acc) (hv : v ∈ s.cand r q) (hS : S ⊆ addL1 v acc)
      (hval : L2Valid f q (s.key r q) m ⟨r, S⟩) (hpc' : s'.pc r q = .wrL2 ⟨r, S⟩)
      (hk : s'.key r q = s.key r q) (hph : s'.phase r q = s.phase r q)
  | l1Bad (i j : P) (acc : Finset (L1 P M)) (v : Val P M) (hpc : s.pc r q = .rdL1 i ∅ acc)
      (hv : v ∈ s.cand r q)
      (hbad : ¬ ∃ S m, S ⊆ addL1 v acc ∧ L2Valid f q (s.key r q) m ⟨r, S⟩)
      (hpc' : s'.pc r q = PC.start j) (hk : s'.key r q = s.key r q)
      (hph : s'.phase r q = s.phase r q)
  | l2Done (j : P) (ρ : L2 P M) (hpc : s.pc r q = .wrL2 ρ) (hpc' : s'.pc r q = PC.start j)
      (hk : s'.key r q = s.key r q) (hph : s'.phase r q = s.phase r q)
      (hmem : s'.mem ⟨.l2, r, s.key r q, q⟩ = .p2 ρ)

lemma Step.tstep {s s' : St P M} {r q : P} (h : Step F f s (.thr r q) s') : TStep F f s s' r q := by
  cases h with
  | l2Found _ hpc hv hρ hval =>
    subst hρ; exact .found _ _ _ _ hpc hv hval (by simp [St.tick]) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | l2Next _ hpc hv hnv hj =>
    exact .next _ _ _ _ hpc hv hnv hj (by simp [St.tick]) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | l2EndS _ hpc hv hnv hph =>
    exact .endS _ _ hpc hv hnv hph (by simp [St.tick]) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | l2EndV _ hpc hv hnv hph =>
    exact .endV _ _ _ hpc hv hnv hph (by simp [St.tick]; exact ⟨rfl, rfl⟩)
      (by simp [St.key, St.tick])
      (by simp [St.tick])
  | l2EndL _ hpc hv hnv hph =>
    exact .endL _ _ _ hpc hv hnv hph (by simp [St.tick]; exact ⟨rfl, rfl⟩)
      (by simp [St.key, St.tick])
      (by simp [St.tick])
  | copyDone _ hpc =>
    exact .copy _ _ _ hpc (by simp [St.tick, St.deliver, St.write])
      (by simp [St.tick, St.deliver, St.write]; rfl) (by simp [St.tick, St.deliver, St.write])
  | sndOk _ hpc hv hc hs hk =>
    exact .sndOk _ _ hpc hv hc hs hk (by simp [St.tick, St.sign])
      (by simp [St.key, St.tick, St.sign]) (by simp [St.tick, St.sign])
  | sndBad _ hpc hv hbad =>
    exact .sndBad _ _ hpc hv hbad (by simp [St.tick]; rfl) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | echoDone _ hpc =>
    exact .echo _ _ hpc (by simp [St.tick, St.write, St.setPhase]; rfl)
      (by simp [St.key, St.tick, St.write, St.setPhase]) (by simp [St.tick, St.write, St.setPhase])
  | valNext _ hpc hv hj =>
    exact .valNext _ _ _ _ _ hpc hv hj (by simp [St.tick]) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | valOk _ hpc hv hcard hb =>
    exact .valOk _ _ _ _ hpc hv hcard hb (by simp [St.tick, St.sign])
      (by simp [St.key, St.tick, St.sign]) (by simp [St.tick, St.sign])
  | valBad _ hpc hv hbad =>
    exact .valBad _ _ _ _ hpc hv hbad (by simp [St.tick]; rfl) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | l1Done _ hpc =>
    exact .l1Done _ _ hpc (by simp [St.tick, St.write, St.setPhase]; rfl)
      (by simp [St.key, St.tick, St.write, St.setPhase]) (by simp [St.tick, St.write, St.setPhase])
      (by simp [St.tick, St.write, St.setPhase])
  | l1Next _ hpc hv hj =>
    exact .l1Next _ _ _ _ _ hpc hv hj (by simp [St.tick]) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | l1Ok _ hpc hv hS hval =>
    exact .l1Ok _ _ _ _ _ hpc hv hS hval (by simp [St.tick, St.sign])
      (by simp [St.key, St.tick, St.sign]) (by simp [St.tick, St.sign])
  | l1Bad _ hpc hv hbad =>
    exact .l1Bad _ _ _ _ hpc hv hbad (by simp [St.tick]; rfl) (by simp [St.key, St.tick])
      (by simp [St.tick])
  | l2Done _ hpc =>
    exact .l2Done _ _ hpc (by simp [St.tick, St.write]; rfl) (by simp [St.key, St.tick, St.write])
      (by simp [St.tick, St.write]) (by simp [St.tick, St.write])

lemma TStep.key_or_copy {s s' : St P M} {r q : P} (T : TStep F f s s' r q) :
    s'.key r q = s.key r q ∨ (s'.last r q = s.last r q + 1 ∧ s'.phase r q = .wfs) := by
  cases T with
  | copy _ _ _ _ hlast _ hph => exact Or.inr ⟨hlast, hph⟩
  | _ => left; assumption

end Podc.RDMAAgreement.RB
