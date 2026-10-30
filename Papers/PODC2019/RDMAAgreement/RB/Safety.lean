import Papers.PODC2019.RDMAAgreement.RB.Core

/-!
# Algorithm 2 — safety: Properties (2) and (3) of Definition 1

* `agreement` (Property 2): two correct processes never deliver different messages for the same
  sender and key.
* `integrity` (Property 3): if a correct process delivers `(k, m)` from a correct process `q`,
  then `q` broadcast `(k, m)`.

Both hold in every reachable state, assuming only `|F| ≤ f` (no fairness, no `n ≥ 2f+1`).
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- Some correct process built an L1 proof for `(q,k)` supporting `m`. -/
def Supported (F : Finset P) (s : St P M) (q : P) (k : ℕ) (m : M) : Prop :=
  ∃ j ∉ F, ∃ t, s.l1 j q k = some (⟨q, k, m⟩, t)

/-- A valid, unforgeable L2 proof contains an L1 proof by a correct process. -/
lemma supported_of_valid {s : St P M} (IB : InvB F s) (hF : F.card ≤ f) {q : P} {k : ℕ} {m : M}
    {ρ : L2 P M} (hval : L2Valid f q k m ρ) (hsig : SigOK F s.signed (.p2 ρ)) :
    Supported F s q k m := by
  obtain ⟨hcard, hall⟩ := hval
  obtain ⟨a, ha, haF⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := F) (t := ρ.proofs.image L1.author) (by omega)
  obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.1 ha
  have hsig1 := (sigOK_p2.1 hsig).2 π hπ
  have hsigned := (sigOK_p1.1 hsig1).1 haF
  obtain ⟨-, hl1⟩ := IB.sL1 _ haF π hsigned
  obtain ⟨hc, hb⟩ := hall π hπ
  obtain ⟨c, hcm⟩ := Finset.card_pos.1 (by omega : 0 < π.copies.card)
  obtain ⟨t, ht⟩ := hl1 c hcm
  rw [hb c hcm] at ht
  exact ⟨π.author, haF, t, ht⟩

lemma Supported.grows {s s' : St P M} (G : Grows F s s') {q : P} {k : ℕ} {m : M}
    (h : Supported F s q k m) : Supported F s' q k m := by
  obtain ⟨j, hj, t, ht⟩ := h
  exact ⟨j, hj, t, G.l1 j hj _ _ _ ht⟩

/-- Deliveries are backed by L1 proofs of correct processes. -/
structure InvE (F : Finset P) (f : ℕ) (s : St P M) : Prop where
  wrCopy : ∀ p ∉ F, ∀ q ρ m, s.pc p q = .wrCopy ρ m → L2Valid f q (s.key p q) m ρ
  dlv : ∀ p ∉ F, ∀ q k m, s.dlv p q k = some m → Supported F s q k m

lemma InvE.init [Inhabited P] : InvE F f (St.init : St P M) := by
  refine ⟨?_, ?_⟩
  · intro p _ q ρ m h; simp [St.init, PC.start] at h
  · intro p _ q k m h; simp [St.init] at h

lemma InvE.step {s s' : St P M} {ℓ : Label P M} (hF : F.card ≤ f) (IA : InvA F s)
    (IB : InvB F s) (I : InvE F f s) (h : Step F f s ℓ s') : InvE F f s' := by
  have G := h.grows IA
  refine ⟨fun p' hp' q' ρ m hpc => ?_, fun p' hp' q' k m hd => ?_⟩
  · by_cases hself : ℓ = .thr p' q'
    · subst hself
      cases h with
      | l2Found _ _ _ _ hval =>
        simp [St.tick] at hpc; obtain ⟨rfl, rfl⟩ := hpc; simpa [St.key, St.tick] using hval
      | _ => simp [St.tick, St.write, St.sign, St.deliver, St.setPhase, PC.start] at hpc
    · have hl : s'.loc p' q' = s.loc p' q' := by
        by_cases hT : ∃ p q, ℓ = .thr p q
        · obtain ⟨p, q, rfl⟩ := hT
          exact h.frame_thr.1 p' q' (by rintro ⟨rfl, rfl⟩; exact hself rfl)
        · push_neg at hT; exact (h.frame_other hT).1 p' q'
      simp only [St.loc, Loc.mk.injEq] at hl
      rw [hl.1] at hpc
      have := I.wrCopy p' hp' q' ρ m hpc
      simpa [St.key, hl.2.1] using this
  · by_cases hold : s.dlv p' q' k = some m
    · exact (I.dlv p' hp' q' k m hold).grows G
    · cases h with
      | @copyDone p q j ρ m0 hp hpc =>
        simp only [St.tick, St.write, St.deliver, go_dlv, upd3_apply2, upd2_apply, St.key] at hd
        split_ifs at hd with hpq
        · obtain ⟨rfl, rfl⟩ := hpq
          by_cases hk : k = s.last p' q' + 1
          · subst hk; simp at hd; subst hd
            have hval := I.wrCopy p' hp' q' ρ m0 hpc
            have hsig : SigOK F s.signed (.p2 ρ) :=
              IB.reg.pend _ _ (Or.inl ⟨p', q', by rw [hpc]; rfl⟩)
            exact (supported_of_valid IB hF hval hsig).grows G
          · rw [Function.update_of_ne hk] at hd; exact absurd hd hold
        · exact absurd hd hold
      | _ => exact absurd (by simpa [St.tick, St.write, St.sign, St.deliver, St.setPhase,
          St.doBcast] using hd) hold

lemma InvE.reach [Inhabited P] (hF : F.card ≤ f) {s : St P M} (h : Reachable F f s) :
    InvE F f s := by
  induction h with
  | init => exact InvE.init
  | step hr hs ih => exact ih.step hF (InvA.reach hr) (InvB.reach hr) hs

/-- **Property (2) of Definition 1 (agreement)**, for reachable states: if correct `p` delivers
`(k, m)` from `r` and correct `p'` delivers `(k, m')` from `r`, then `m = m'`. -/
theorem agreement [Inhabited P] (hF : F.card ≤ f) {s : St P M} (h : Reachable F f s)
    {p p' r : P} {k : ℕ} {m m' : M} (hp : p ∉ F) (hp' : p' ∉ F) (h1 : s.dlv p r k = some m)
    (h2 : s.dlv p' r k = some m') : m = m' := by
  have IE := InvE.reach hF h
  obtain ⟨j, hj, t, ht⟩ := IE.dlv p hp r k m h1
  obtain ⟨j', hj', t', ht'⟩ := IE.dlv p' hp' r k m' h2
  have := l1_agree h hj hj' ht ht'
  simpa using this

/-- **Property (3) of Definition 1 (integrity)**, for reachable states: if correct `p` delivers
`(k, m)` from a correct process `q`, then `q` broadcast `(k, m)`. -/
theorem integrity [Inhabited P] (hF : F.card ≤ f) {s : St P M} (h : Reachable F f s)
    {p q : P} {k : ℕ} {m : M} (hp : p ∉ F) (hq : q ∉ F) (hd : s.dlv p q k = some m) :
    s.bc q k = some m := by
  obtain ⟨j, hj, t, ht⟩ := (InvE.reach hF h).dlv p hp q k m hd
  obtain ⟨-, ⟨-, -, hc | hc⟩, -⟩ := (InvD.reach h).l1 j hj q k _ t ht
  · obtain ⟨rfl, hc⟩ := hc; exact hc
  · exact ((InvB.reach h).echo j hj q k _ hc).2.2 hq

/-! ### Executions -/

lemma Exec.reach [Inhabited P] (e : Exec (M := M) F f) (t : ℕ) : Reachable F f (e.s t) := by
  induction t with
  | zero => rw [e.init]; exact .init
  | succ t ih => exact .step ih (e.step t)

lemma Exec.grows [Inhabited P] (e : Exec (M := M) F f) {t t' : ℕ} (h : t ≤ t') :
    (∀ j ∉ F, ∀ q k m, (e.s t).dlv j q k = some m → (e.s t').dlv j q k = some m) ∧
    (∀ j ∉ F, ∀ k m, (e.s t).bc j k = some m → (e.s t').bc j k = some m) := by
  induction h with
  | refl => exact ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ h => h⟩
  | @step m _ ih =>
    have G := (e.step m).grows (InvA.reach (e.reach m))
    exact ⟨fun j hj q k m h => G.dlv j hj _ _ _ (ih.1 j hj q k m h),
      fun j hj k m h => G.bc j hj _ _ (ih.2 j hj k m h)⟩

/-- **Property (2) of Definition 1 (agreement)** along an execution. -/
theorem Exec.agreement [Inhabited P] (hF : F.card ≤ f) (e : Exec (M := M) F f) {p p' r : P}
    {k : ℕ} {m m' : M} {t t' : ℕ} (hp : p ∉ F) (hp' : p' ∉ F) (h1 : (e.s t).dlv p r k = some m)
    (h2 : (e.s t').dlv p' r k = some m') : m = m' :=
  Podc.RDMAAgreement.RB.agreement hF (e.reach (max t t')) hp hp'
    ((e.grows (le_max_left t t')).1 p hp r k m h1)
    ((e.grows (le_max_right t t')).1 p' hp' r k m' h2)

/-- **Property (3) of Definition 1 (integrity)** along an execution: the broadcast happened no
later than the delivery. -/
theorem Exec.integrity [Inhabited P] (hF : F.card ≤ f) (e : Exec (M := M) F f) {p q : P} {k : ℕ}
    {m : M} {t : ℕ} (hp : p ∉ F) (hq : q ∉ F) (hd : (e.s t).dlv p q k = some m) :
    (e.s t).bc q k = some m :=
  Podc.RDMAAgreement.RB.integrity hF (e.reach t) hp hq hd

end Podc.RDMAAgreement.RB
