import Papers.PODC2020.SSLERegular.EulerReach
import Papers.PODC2020.SSLERegular.GoodExists
import Papers.PODC2020.SSLERegular.ErrorReach

/-!
# Theorem 3.3 for the repaired SS-EulerCycle

* `good_validStable`: legitimate configurations (`Good`) are valid output-stable (Lemma 3.1,
  stability part): every interaction keeps the configuration legitimate, the ring leader never
  moves, and there is exactly one token, so the multiple-leader detection never fires.
* `single_reach` / `multi_reach` (Lemma 3.2): from a coherent configuration with a single virtual
  ring a legitimate configuration is reachable (or an error); with several virtual rings an error
  is reachable (each ring elects a leader, the tokens are moved to two adjacent nodes).
* `repaired_selfStab` (**Theorem 3.3, repaired**): on every connected `2k`-regular graph,
  `k ≥ 1`, for every ring protocol satisfying `RingSpec`, the repaired SS-EulerCycle solves SSLE:
  from every configuration a valid output-stable configuration is reachable; hence every globally
  fair execution stabilizes (`repaired_solvesSSLE`) and so does the random scheduler with
  probability 1 (`Cslib.TransitionSystem.tendsto_compl_of_reach`).
-/

set_option linter.unusedSectionVars false

open Finset

namespace SSLERegular

universe u

variable {RS : Type*} {k : ℕ} {V : Type u} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj] {R : RingProtocol RS}

section Coherent

variable {S : V → Skel k} (hdeg : ∀ v, G.degree v = 2 * k) (hinj : InjCol G S) (hok : EdgeOK G S)

lemma vperm_ne (w : V × Fin k) : vperm hdeg hinj hok w ≠ w :=
  fun h => node_ne_vperm hdeg hinj hok w (congrArg Prod.fst h).symm

lemma vperm_vperm_ne (w : V × Fin k) : vperm hdeg hinj hok (vperm hdeg hinj hok w) ≠ w := by
  intro h
  have e2 := vedge_vperm hdeg hinj hok (vperm hdeg hinj hok w)
  rw [h] at e2
  exact edge_not_rev hdeg hinj hok (vedge_vperm hdeg hinj hok w) _ _ e2

/-- The cycle of `w0`. -/
abbrev Cyc (w0 : V × Fin k) := {x // (vperm hdeg hinj hok).SameCycle w0 x}

/-- The virtual ring through `w0` as a directed ring. -/
noncomputable def cycτ (w0 : V × Fin k) : Equiv.Perm (Cyc hdeg hinj hok w0) :=
  (vperm hdeg hinj hok).subtypePerm (fun _ => Equiv.Perm.sameCycle_apply_right)

lemma cycτ_val (w0 : V × Fin k) (x : Cyc hdeg hinj hok w0) :
    vperm hdeg hinj hok x.val = (cycτ hdeg hinj hok w0 x).val := rfl

lemma cycτ_single (w0 : V × Fin k) (x y : Cyc hdeg hinj hok w0) :
    (cycτ hdeg hinj hok w0).SameCycle x y := by
  obtain ⟨i, hi⟩ := x.2.symm.trans y.2
  refine ⟨i, Subtype.ext ?_⟩
  rw [cycτ, Equiv.Perm.subtypePerm_zpow]
  simpa using hi

lemma three_le_cycle (w : V × Fin k) : 3 ≤ Fintype.card (Cyc hdeg hinj hok w) := by
  classical
  set σ := vperm hdeg hinj hok
  have h1 := vperm_ne hdeg hinj hok w
  have h2 := vperm_vperm_ne hdeg hinj hok w
  have h3 : σ (σ w) ≠ σ w := fun h => h1 (σ.injective h)
  let a : Cyc hdeg hinj hok w := ⟨w, Equiv.Perm.SameCycle.refl _ _⟩
  let b : Cyc hdeg hinj hok w := ⟨σ w, Equiv.Perm.sameCycle_apply_right.2 a.2⟩
  let c : Cyc hdeg hinj hok w := ⟨σ (σ w), Equiv.Perm.sameCycle_apply_right.2 b.2⟩
  have hinj3 : Function.Injective ![a, b, c] := by
    intro i j hij
    have := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp only [a, b, c, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] at this ⊢ <;>
      first | rfl | exact absurd this h1.symm | exact absurd this h2.symm | exact absurd this h1 |
        exact absurd this h2 | exact absurd this h3 | exact absurd this h3.symm
  simpa using Fintype.card_le_of_injective _ hinj3

lemma period_eq_card {W : Type*} [Fintype W] [DecidableEq W] (σ : Equiv.Perm W) (w : W)
    (h : ∀ w', σ.SameCycle w w') : Function.minimalPeriod σ w = Fintype.card W := by
  have hb : Function.Bijective (fun t : Fin (Function.minimalPeriod σ w) => (σ ^ (t : ℕ)) w) := by
    refine ⟨fun a b hab => Fin.ext (pow_inj_period σ w a.2 b.2 hab), fun w' => ?_⟩
    obtain ⟨t, ht, htw⟩ := (sameCycle_iff_exists_lt σ w).1 (h w')
    exact ⟨⟨t, ht⟩, htw⟩
  rw [← Fintype.card_of_bijective hb, Fintype.card_fin]

end Coherent

lemma good_of (hdeg : ∀ v, G.degree v = 2 * k) {D : V → EState k RS} {S : V → Skel k}
    (hinj : InjCol G S) (hok : EdgeOK G S) (hSD : skelOf D = S) (hB : Base G S D)
    (hs : ∀ w w', (vperm hdeg hinj hok).SameCycle w w')
    (hr : RingValidOn R (vperm hdeg hinj hok) (fun w => (vn D w).ringState)) (w0 : V × Fin k)
    (hl : R.lead (vn D w0).ringState = true) (ht : TokLegit (vperm hdeg hinj hok) (vn D) w0) :
    Good G R hdeg D := by
  subst hSD; exact ⟨hinj, hok, hB, hs, hr, w0, hl, ht⟩

/-! ### Legitimate configurations are valid output-stable -/

/-- **Closure** (Lemma 3.1, stability): one interaction keeps a legitimate configuration
legitimate and does not change any ring-leader output. -/
lemma good_step (hdeg : ∀ v, G.degree v = 2 * k) {D D' : V → EState k RS} (hD : Good G R hdeg D)
    (h : (ssEuler true k R).Step G D D') :
    Good G R hdeg D' ∧ ∀ w, R.lead (vn D' w).ringState = R.lead (vn D w).ringState := by
  classical
  obtain ⟨hinj, hok, hB, hs, hr, w0, hl, m, hm, b, htl⟩ := hD
  set σ := vperm hdeg hinj hok with hσ
  have hN : Function.minimalPeriod σ w0 = Fintype.card (V × Fin k) := period_eq_card σ w0 (hs w0)
  set N := Fintype.card (V × Fin k) with hNdef
  have hNpos : 0 < N := hN ▸ period_pos σ w0
  have hpos : ∀ w, ∃ t < N, (σ ^ t) w0 = w := fun w => by
    rw [← hN]; exact (sameCycle_iff_exists_lt σ w0).1 (hs w0 w)
  -- leaders: only `w0`
  have hlead : ∀ t < N, R.lead (vn D ((σ ^ t) w0)).ringState = decide (t = 0) := by
    intro t ht
    obtain ⟨-, x, -, hu⟩ := hr
    by_cases h0 : t = 0
    · subst h0; simpa using hl
    · rw [decide_eq_false h0]
      by_contra hne
      have h1 : R.lead (vn D ((σ ^ t) w0)).ringState = true := by simpa using hne
      have := (hu _ h1).trans (hu _ hl).symm
      exact h0 (pow_inj_period σ w0 (hN ▸ ht) (hN ▸ hNpos) (by simpa using this))
  -- the common part: after the edge step on `w`
  have after : ∀ (w : V × Fin k) (ρ : RS → RS → RS × RS),
      ρ (vn D w).ringState (vn D (σ w)).ringState ∈ R.δ (vn D w).ringState (vn D (σ w)).ringState →
      (∀ a c, a ≠ c → ¬ TokBoth (vnAfter hdeg hinj hok R D ρ w) a c) ∧
      ∀ D' : V → EState k RS, Base G (skelOf D) D' → vn D' = vnAfter hdeg hinj hok R D ρ w →
        Good G R hdeg D' ∧ ∀ w, R.lead (vn D' w).ringState = R.lead (vn D w).ringState := by
    intro w ρ hρ
    obtain ⟨t, ht, rfl⟩ := hpos w
    have hrs : RingStepOn R σ (fun w => (vn D w).ringState)
        (fun w' => (vnAfter hdeg hinj hok R D ρ ((σ ^ t) w0) w').ringState) := by
      refine ⟨(σ ^ t) w0, _, hρ, ?_⟩
      have := ring_vnAfter (R := R) hdeg hinj hok σ id Function.injective_id (fun _ => rfl) D ρ
        ((σ ^ t) w0)
      simpa using this
    have hlead' := hr.1 _ (Relation.ReflTransGen.single hrs)
    have hlb : R.lead (ρ (vn D ((σ ^ t) w0)).ringState
        (vn D (σ ((σ ^ t) w0))).ringState).2 =
          decide (TokenRing.succP (Function.minimalPeriod σ w0) t = 0) := by
      have h1 := hlead' (σ ((σ ^ t) w0))
      have hv2 : vnAfter hdeg hinj hok R D ρ ((σ ^ t) w0) (σ ((σ ^ t) w0)) =
          (vEdge R ρ (vn D ((σ ^ t) w0)) (vn D (σ ((σ ^ t) w0)))).2 := by
        simp [vnAfter, hσ]
      simp only at h1
      rw [hv2, (vEdge_ringState (R := R) ρ _ _).2] at h1
      rw [h1, apply_pow_succP σ w0 t (hN ▸ ht), hlead _ (by
        rw [← hN]; unfold TokenRing.succP; split_ifs <;> omega), hN]
    have htok := vnAfter_tok (R := R) hdeg hinj hok D ρ w0 (t := t) (hN ▸ ht) hlb
    rw [hN] at htok
    have hL : TokenRing.Legit N m b (fun s => (vn D ((σ ^ s) w0)).token,
        fun s => (vn D ((σ ^ s) w0)).bit) := fun s hs => htl s hs
    have hN2 : 2 ≤ N := by
      have h3 := three_le_cycle hdeg hinj hok w0
      have h4 : Fintype.card (Cyc hdeg hinj hok w0) ≤ N :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      omega
    obtain ⟨m', hm', b', hL'⟩ : ∃ m' < N, ∃ b', TokenRing.Legit N m' b'
        (TokenRing.stepT N (fun s => (vn D ((σ ^ s) w0)).token,
          fun s => (vn D ((σ ^ s) w0)).bit) t) := by
      obtain ⟨h1, h2⟩ := hL.step hN2 hm ht
      by_cases htm : t = m
      · refine ⟨_, ?_, _, h2 htm⟩
        unfold TokenRing.succP; split_ifs <;> omega
      · exact ⟨m, hm, b, by rw [h1 htm]; exact hL⟩
    have hFtok : ∀ s < N, (vnAfter hdeg hinj hok R D ρ ((σ ^ t) w0) ((σ ^ s) w0)).token =
        decide (s = m') := fun s hs => ((htok s hs).1.trans (hL' s hs).1)
    refine ⟨fun a c hac ⟨p, q, hp, hq⟩ => ?_, fun D' hB' hvn => ?_⟩
    · obtain ⟨s1, hs1, e1⟩ := hpos (c, p)
      obtain ⟨s2, hs2, e2⟩ := hpos (a, q)
      rw [← e1, hFtok s1 hs1] at hp
      rw [← e2, hFtok s2 hs2] at hq
      simp only [decide_eq_true_eq] at hp hq
      subst hp hq
      exact hac (congrArg Prod.fst (e2.symm.trans e1))
    · have hleadD : ∀ w, R.lead (vn D' w).ringState = R.lead (vn D w).ringState := by
        rw [hvn]; exact hlead'
      refine ⟨good_of hdeg hinj hok (funext hB'.1) hB' hs ?_ w0 (by rw [hleadD]; exact hl)
        ⟨m', hm', b', fun s hs => ?_⟩, hleadD⟩
      · rw [hvn]; exact hr.step hrs
      · rw [hvn]; exact ⟨(htok s hs).1.trans (hL' s hs).1, (htok s hs).2.trans (hL' s hs).2⟩
  obtain ⟨u, x, hux, o, ⟨ch, hch, rfl⟩, rfl⟩ := h
  rcases exists_vperm_of_adj hdeg hinj hok hux with ⟨i, hi⟩ | ⟨j, hj⟩
  · subst hi
    obtain ⟨hT, hG⟩ := after (u, i) ch.ρ (hch.1 _ _)
    obtain ⟨-, h2⟩ := interact_fwd hdeg hinj hok R hB (u, i) ch hch
    obtain ⟨hB', hvn⟩ := h2 (hT _ _ (node_ne_vperm hdeg hinj hok (u, i)))
    exact hG _ hB' hvn
  · subst hj
    obtain ⟨hT, hG⟩ := after (x, j) ch.ρ (hch.1 _ _)
    obtain ⟨-, h2⟩ := interact_bwd hdeg hinj hok R hB (x, j) ch hch
    obtain ⟨hB', hvn⟩ := h2 (hT _ _ (node_ne_vperm hdeg hinj hok (x, j)).symm)
    exact hG _ hB' hvn

lemma good_reach (hdeg : ∀ v, G.degree v = 2 * k) {D D' : V → EState k RS}
    (hD : Good G R hdeg D) (h : (ssEuler true k R).Reachable G D D') :
    Good G R hdeg D' ∧ ∀ w, R.lead (vn D' w).ringState = R.lead (vn D w).ringState := by
  induction h with
  | refl => exact ⟨hD, fun _ => rfl⟩
  | tail _ hst ih =>
    obtain ⟨h1, h2⟩ := good_step hdeg ih.1 hst
    exact ⟨h1, fun w => (h2 w).trans (ih.2 w)⟩

/-- **Lemma 3.1 (repaired), stability**: legitimate configurations are valid output-stable. -/
theorem good_validStable (hdeg : ∀ v, G.degree v = 2 * k) {D : V → EState k RS}
    (hD : Good G R hdeg D) : (ssEuler true k R).ValidStable G (EState.out R) D := by
  classical
  refine ⟨fun D' hD' v => ?_, ?_⟩
  · have := (good_reach hdeg hD hD').2
    simp only [EState.out]
    congr 1
    apply propext
    exact exists_congr fun i => by rw [show (D' v).node i = vn D' (v, i) from rfl, this]; rfl
  · obtain ⟨hinj, hok, -, -, ⟨-, xl, hxl, hu⟩, -⟩ := hD
    unfold GProtocol.numLeaders
    rw [Finset.card_eq_one]
    refine ⟨xl.1, Finset.ext fun v => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, EState.out,
      decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact congrArg Prod.fst (hu (v, i) hi)
    · rintro rfl
      exact ⟨xl.2, hxl⟩

/-! ### Reaching a legitimate configuration or an error (Lemma 3.2) -/

section Reach

variable {S : V → Skel k} (hdeg : ∀ v, G.degree v = 2 * k) (hinj : InjCol G S) (hok : EdgeOK G S)

/-- **Single virtual ring**: elect a ring leader, then let the token circulate twice. -/
lemma single_reach (hR : ∀ a b, (R.δ a b).Nonempty) (hRS : RingSpec.{u} R)
    {C : V → EState k RS} (hB : Base G S C)
    (hs : ∀ w w', (vperm hdeg hinj hok).SameCycle w w') (w : V × Fin k) :
    ∃ D, (ssEuler true k R).Reachable G C D ∧ (Err D ∨ Good G R hdeg D) := by
  classical
  set σ := vperm hdeg hinj hok with hσ
  have hcard : 3 ≤ Fintype.card (V × Fin k) := (three_le_cycle hdeg hinj hok w).trans
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  obtain ⟨c', hc', hv⟩ := hRS (V × Fin k) σ hs hcard (fun w => (vn C w).ringState)
  obtain ⟨D1, h1, hD1⟩ := lift_ring (R := R) hdeg hinj hok σ id Function.injective_id
    (fun _ => rfl) hR C hB c' hc'
  rcases hD1 with hE | ⟨hB1, hr1, -⟩
  · exact ⟨D1, h1, Or.inl hE⟩
  have hv1 : RingValidOn R σ (fun x => (vn D1 (id x)).ringState) := by rw [hr1]; exact hv
  obtain ⟨xl, hxl, -⟩ := hv.2
  have hxl1 : R.lead (vn D1 (id xl)).ringState = true := by
    have := congrFun hr1 xl; rw [this]; exact hxl
  have hN : Function.minimalPeriod σ (id xl) = Fintype.card (V × Fin k) :=
    period_eq_card σ _ (hs _)
  obtain ⟨D2, h2, hD2⟩ := token_run (R := R) hdeg hinj hok σ id Function.injective_id
    (fun _ => rfl) hR D1 hB1 hv1 xl hxl1 (fun t => ⟨_, rfl⟩)
    (2 * Function.minimalPeriod σ (id xl) + 0)
  rcases hD2 with hE | ⟨hB2, hr2, hl2, -, ht2⟩
  · exact ⟨D2, h1.trans h2, Or.inl hE⟩
  have hL := TokenRing.run_legit (N := Function.minimalPeriod σ (id xl)) (by omega)
    (fun t => (vn D1 ((σ ^ t) (id xl))).token, fun t => (vn D1 ((σ ^ t) (id xl))).bit)
    (p := 0) (by omega)
  refine ⟨D2, h1.trans h2, Or.inr (good_of hdeg hinj hok (funext hB2.1) hB2 hs hr2 xl
    (by rw [show vn D2 xl = vn D2 (id xl) from rfl, hl2 xl]; exact hxl1)
    ⟨0, by omega, (vn D1 ((σ ^ 0) (id xl))).bit, fun t ht => ?_⟩)⟩
  rw [← hN] at ht
  exact ⟨(ht2 t ht).1.trans (hL t ht).1, (ht2 t ht).2.trans (hL t ht).2⟩

/-- **Several virtual rings**: elect a leader on two rings sharing a node, move their tokens to
adjacent nodes; the multiple-leader detection fires. -/
lemma multi_reach (hconn : G.Connected) (hR : ∀ a b, (R.δ a b).Nonempty)
    (hRS : RingSpec.{u} R) {C : V → EState k RS} (hB : Base G S C)
    (hm : ¬ ∀ w w', (vperm hdeg hinj hok).SameCycle w w') :
    ∃ D, (ssEuler true k R).Reachable G C D ∧ Err D := by
  classical
  set σ := vperm hdeg hinj hok with hσ
  -- a node with virtual nodes on two different rings
  obtain ⟨v, i, j, hij⟩ : ∃ v i j, ¬ σ.SameCycle (v, i) (v, j) := by
    by_contra hcon
    push Not at hcon
    apply hm
    have key : ∀ u x, G.Reachable u x → ∀ i j, σ.SameCycle (u, i) (x, j) := by
      intro u x hr
      obtain ⟨p⟩ := hr
      induction p with
      | nil => exact hcon _
      | @cons a b c hadj p ih =>
        intro i j
        rcases exists_vperm_of_adj hdeg hinj hok hadj with ⟨i0, hi0⟩ | ⟨j0, hj0⟩
        · have h1 : σ.SameCycle (a, i0) (σ (a, i0)) :=
            Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
          have he : σ (a, i0) = (b, (σ (a, i0)).2) := Prod.ext hi0 rfl
          rw [he] at h1
          exact (hcon a i i0).trans (h1.trans (ih _ j))
        · have h1 : σ.SameCycle (b, j0) (σ (b, j0)) :=
            Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
          have he : σ (b, j0) = (a, (σ (b, j0)).2) := Prod.ext hj0 rfl
          rw [he] at h1
          exact (hcon a i _).trans (h1.symm.trans (ih j0 j))
    intro w w'
    exact key w.1 w'.1 (hconn.preconnected w.1 w'.1) w.2 w'.2
  set a : V × Fin k := (v, i) with ha
  set b : V × Fin k := (v, j) with hb
  have hnotB : ∀ x : Cyc hdeg hinj hok b, x.val ≠ a := fun x hx => hij (by
    have := x.2; rw [hx] at this; exact this.symm)
  have hnotA : ∀ x : Cyc hdeg hinj hok a, x.val ≠ σ b := fun x hx => hij (by
    have := x.2; rw [hx] at this; exact this.trans (Equiv.Perm.sameCycle_apply_right.1
      (Equiv.Perm.SameCycle.refl _ _)))
  -- 1. ring of `a`
  obtain ⟨cA, hcA, hvA⟩ := hRS (Cyc hdeg hinj hok a) (cycτ hdeg hinj hok a)
    (cycτ_single hdeg hinj hok a) (three_le_cycle hdeg hinj hok a)
    (fun x => (vn C x.val).ringState)
  obtain ⟨D1, h1, hD1⟩ := lift_ring (R := R) hdeg hinj hok (cycτ hdeg hinj hok a) Subtype.val
    Subtype.val_injective (cycτ_val hdeg hinj hok a) hR C hB cA hcA
  rcases hD1 with hE | ⟨hB1, hr1, -⟩
  · exact ⟨D1, h1, hE⟩
  -- 2. ring of `b`
  obtain ⟨cB, hcB, hvB⟩ := hRS (Cyc hdeg hinj hok b) (cycτ hdeg hinj hok b)
    (cycτ_single hdeg hinj hok b) (three_le_cycle hdeg hinj hok b)
    (fun x => (vn D1 x.val).ringState)
  obtain ⟨D2, h2, hD2⟩ := lift_ring (R := R) hdeg hinj hok (cycτ hdeg hinj hok b) Subtype.val
    Subtype.val_injective (cycτ_val hdeg hinj hok b) hR D1 hB1 cB hcB
  rcases hD2 with hE | ⟨hB2, hr2, hout2⟩
  · exact ⟨D2, h1.trans h2, hE⟩
  have outB : ∀ x : Cyc hdeg hinj hok a, ∀ y : Cyc hdeg hinj hok b, y.val ≠ x.val :=
    fun x y hxy => hij (x.2.trans (by rw [← hxy]; exact y.2.symm))
  have hvA2 : RingValidOn R (cycτ hdeg hinj hok a) (fun x => (vn D2 x.val).ringState) := by
    have : (fun x : Cyc hdeg hinj hok a => (vn D2 x.val).ringState) = cA := by
      funext x; rw [hout2 x.val (fun y => outB x y)]; exact congrFun hr1 x
    rw [this]; exact hvA
  -- 3. token of ring `a` to `a`
  obtain ⟨xlA, hxlA, -⟩ := hvA2.2
  obtain ⟨p, hp, hpa⟩ := (sameCycle_iff_exists_lt σ xlA.val).1 (xlA.2.symm)
  obtain ⟨D3, h3, hD3⟩ := token_run (R := R) hdeg hinj hok (cycτ hdeg hinj hok a) Subtype.val
    Subtype.val_injective (cycτ_val hdeg hinj hok a) hR D2 hB2 hvA2 xlA hxlA
    (fun t => ⟨⟨_, xlA.2.trans ⟨t, by simp⟩⟩, rfl⟩)
    (2 * Function.minimalPeriod σ xlA.val + p)
  rcases hD3 with hE | ⟨hB3, -, -, hout3, ht3⟩
  · exact ⟨D3, (h1.trans h2).trans h3, hE⟩
  have hNA : 2 ≤ Function.minimalPeriod σ xlA.val := by
    by_contra hlt
    have hpos := period_pos σ xlA.val
    have h1' : Function.minimalPeriod σ xlA.val = 1 := by omega
    have := pow_period σ xlA.val
    rw [h1', pow_one] at this
    exact vperm_ne hdeg hinj hok _ this
  have hLA := TokenRing.run_legit hNA
    (fun t => (vn D2 ((σ ^ t) xlA.val)).token, fun t => (vn D2 ((σ ^ t) xlA.val)).bit) hp
  have htokA : (vn D3 a).token = true := by
    rw [← hpa, (ht3 p hp).1, (hLA p hp).1]; simp
  -- 4. token of ring `b` to `σ b`
  have hvB3 : RingValidOn R (cycτ hdeg hinj hok b) (fun x => (vn D3 x.val).ringState) := by
    have : (fun x : Cyc hdeg hinj hok b => (vn D3 x.val).ringState) = cB := by
      funext y; rw [hout3 y.val (fun x hx => outB x y hx.symm)]; exact congrFun hr2 y
    rw [this]; exact hvB
  obtain ⟨xlB, hxlB, -⟩ := hvB3.2
  have hσb : σ.SameCycle xlB.val (σ b) :=
    xlB.2.symm.trans (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))
  obtain ⟨q, hq, hqb⟩ := (sameCycle_iff_exists_lt σ xlB.val).1 hσb
  obtain ⟨D4, h4, hD4⟩ := token_run (R := R) hdeg hinj hok (cycτ hdeg hinj hok b) Subtype.val
    Subtype.val_injective (cycτ_val hdeg hinj hok b) hR D3 hB3 hvB3 xlB hxlB
    (fun t => ⟨⟨_, xlB.2.trans ⟨t, by simp⟩⟩, rfl⟩)
    (2 * Function.minimalPeriod σ xlB.val + q)
  rcases hD4 with hE | ⟨hB4, -, -, hout4, ht4⟩
  · exact ⟨D4, ((h1.trans h2).trans h3).trans h4, hE⟩
  have hNB : 2 ≤ Function.minimalPeriod σ xlB.val := by
    by_contra hlt
    have hpos := period_pos σ xlB.val
    have h1' : Function.minimalPeriod σ xlB.val = 1 := by omega
    have := pow_period σ xlB.val
    rw [h1', pow_one] at this
    exact vperm_ne hdeg hinj hok _ this
  have hLB := TokenRing.run_legit hNB
    (fun t => (vn D3 ((σ ^ t) xlB.val)).token, fun t => (vn D3 ((σ ^ t) xlB.val)).bit) hq
  have htokB : (vn D4 (σ b)).token = true := by
    rw [← hqb, (ht4 q hq).1, (hLB q hq).1]; simp
  have htokA4 : (vn D4 a).token = true := by
    rw [hout4 a (fun y => hnotB y)]; exact htokA
  -- 5. the interaction on the virtual edge `b → σ b` detects two tokens
  obtain ⟨ch0, hch0, -⟩ := exists_valid_choice R hR (D4 v).color (D4 v)
  let ch : EChoice k RS := { ch0 with b1 := true }
  have hch : ch.Valid R := hch0
  obtain ⟨hT1, -⟩ := interact_fwd hdeg hinj hok R hB4 b ch hch
  have hab : a ≠ b := fun h => hij (by rw [h])
  have haσ : a ≠ σ b := fun h => hnotA ⟨a, Equiv.Perm.SameCycle.refl _ _⟩ h
  have hT : TokBoth (vnAfter hdeg hinj hok R D4 ch.ρ b) b.1 (σ b).1 := by
    refine ⟨(σ b).2, i, ?_, ?_⟩
    · have hv : vnAfter hdeg hinj hok R D4 ch.ρ b ((σ b).1, (σ b).2) =
          (vEdge R ch.ρ (vn D4 b) (vn D4 (σ b))).2 := by simp [vnAfter, hσ]
      rw [hv]
      obtain ⟨hF1, hF2⟩ := vEdge_tok (R := R) ch.ρ (vn D4 b) (vn D4 (σ b))
      by_cases hf : (R.lead (ch.ρ (vn D4 b).ringState (vn D4 (σ b)).ringState).2 = false ∧
          (vn D4 (σ b)).bit ≠ (vn D4 b).bit) ∨
          (R.lead (ch.ρ (vn D4 b).ringState (vn D4 (σ b)).ringState).2 = true ∧
          (vn D4 b).bit = (vn D4 (σ b)).bit)
      · exact (hF1 hf).2.2.1
      · rw [(hF2 hf).2.2.1]; exact htokB
    · have hv : vnAfter hdeg hinj hok R D4 ch.ρ b (b.1, i) = vn D4 a := by
        simp only [vnAfter]
        rw [Function.update_of_ne haσ, Function.update_of_ne hab]
      rw [hv]; exact htokA4
  exact ⟨_, (((h1.trans h2).trans h3).trans h4).tail
    (step_of_choice true D4 (adj_vperm hdeg hinj hok b) ch hch), b.1, (hT1 hT).trans rfl⟩

end Reach

/-- **Theorem 3.3 (repaired SS-EulerCycle)**, reachability form. On every connected `2k`-regular
graph (`k ≥ 1`) and for every ring protocol with nonempty transition sets satisfying `RingSpec`
(SSLE on directed rings, the property of the Ring-Protocol of [11]), from every configuration of
the repaired SS-EulerCycle a valid output-stable configuration is reachable. -/
theorem repaired_selfStab (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2 * k) (hk : 1 ≤ k)
    (hR : ∀ a b, (R.δ a b).Nonempty) (hRS : RingSpec.{u} R) (r0 : RS) :
    (ssEuler true k R).SelfStab G (EState.out R) := by
  classical
  obtain ⟨Dg, hDg⟩ := exists_good hconn hdeg hk hRS r0
  have hV : 2 ≤ Fintype.card V := by
    obtain ⟨v⟩ := hconn.nonempty
    have := G.degree_lt_card_verts v
    rw [hdeg v] at this; omega
  refine GProtocol.derc_lemma' Err ?_ ?_
  · rintro C ⟨u, hu⟩
    exact ⟨Dg, good_validStable hdeg hDg, err_reach_all hconn hV hR hk true C hu Dg⟩
  · intro C _
    rcases error_or_coherent (G := G) hR hk C with ⟨D, hD, hE⟩ | ⟨hinj, hok, hB⟩
    · exact Or.inl ⟨D, hE, hD⟩
    by_cases hs : ∀ w w', (vperm hdeg hinj hok).SameCycle w w'
    · obtain ⟨v⟩ := hconn.nonempty
      obtain ⟨D, hD, hD'⟩ := single_reach hdeg hinj hok hR hRS hB hs (v, ⟨0, hk⟩)
      rcases hD' with hE | hG
      · exact Or.inl ⟨D, hE, hD⟩
      · exact Or.inr ⟨D, good_validStable hdeg hG, hD⟩
    · obtain ⟨D, hD, hE⟩ := multi_reach hdeg hinj hok hconn hR hRS hB hs
      exact Or.inl ⟨D, hE, hD⟩

/-- **Theorem 3.3 (repaired SS-EulerCycle)**, the paper's formulation: every globally fair
execution reaches a valid output-stable configuration (exactly one leader, forever). -/
theorem repaired_solvesSSLE [Finite RS] (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 2 * k)
    (hk : 1 ≤ k) (hR : ∀ a b, (R.δ a b).Nonempty) (hRS : RingSpec.{u} R) (r0 : RS) :
    (ssEuler true k R).SolvesSSLE G (EState.out R) := by
  have := EState.finite (k := k) (RS := RS)
  have hedge : ∃ u v, G.Adj u v := by
    obtain ⟨v⟩ := hconn.nonempty
    have : 0 < G.degree v := by rw [hdeg v]; omega
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).1 this
    exact ⟨v, w, hw⟩
  exact (GProtocol.solvesSSLE_iff hedge (ssEuler_nonempty true R hR) _).2
    (repaired_selfStab hconn hdeg hk hR hRS r0)

end SSLERegular
