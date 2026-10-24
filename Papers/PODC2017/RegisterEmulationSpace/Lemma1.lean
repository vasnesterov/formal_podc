import Papers.PODC2017.RegisterEmulationSpace.Round

/-!
# Lemma 1 (Section 3.2): `k` sequential writes leave `k f` registers covered outside `F`

`round_main` is one induction step of Lemma 1 (Lemmas 2–4, Claim 1, Corollaries 1–2): after a
sequential run, a fresh writer completes a write while the adversary keeps `f` servers outside `F`
covered by its pending writes. Then the writer's pending writes on `F` are allowed to take effect
(`flushF`), so that no register on `F` is covered (Lemma 1(b)).

`lemma1`: for every set `F` of at most `f + 1` servers there are runs `r₀ ⊑ r₁ ⊑ … ⊑ r_k`, `rᵢ` a
sequential run of `i` writes by the distinct writers `w 0, …, w (i-1)` of alternating values, with
`|Cov(tᵢ)| ≥ i f`, `δ(Cov(tᵢ)) ∩ F = ∅`, `Cov(tᵢ) ⊆ Cov(tᵢ₊₁)`, and `f` servers outside `F` each
holding a register of `Cov(tᵢ₊₁) \ Cov(tᵢ)` (the paper's extended Lemma 1 (a), (b), (d), (e)).
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace

variable {C B V W L S : Type*} [DecidableEq C] [DecidableEq B] [DecidableEq S] [Fintype B]
  [Fintype S]

open Function

namespace Alg

variable (A : Alg C B V W L)

/-- **Induction step of Lemma 1** (Lemmas 2–4, Claim 1, Corollaries 1–2 of the paper). -/
theorem round_main {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ : V}
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr) {F : Finset S} (hF : F.card ≤ f + 1)
    {E₀ : List (Ev C V)} (hE₀ : ∀ d v, Ev.inv d (.write v) ∈ E₀ → d ∈ Wr)
    {Ls : List (C × HOp V × V)} (hL : (A.run E₀).hist = seqHist Ls)
    (hLw : ∀ e ∈ Ls, ∀ v, e.2.1 = .write v → e.1 ∈ Wr)
    (hidle : ∀ c, (A.run E₀).cur c = none)
    {a rd : C} (ha : a ∈ Wr) (hrd : rd ≠ a) (ha0 : (A.run E₀).pend a = [])
    {v : V} (hv : v ≠ lastVal v₀ Ls) :
    ∃ E₁ : List (Ev C V), (∀ e ∈ E₁, e.IsOf a) ∧ ∃ x : V,
      (A.run (E₀ ++ .inv a (.write v) :: E₁)).hist =
        (A.run E₀).hist ++ [.inv a (.write v), .ret a x] ∧
      (A.run (E₀ ++ .inv a (.write v) :: E₁)).cur a = none ∧
      ∃ Q P : Finset S, Q.card = f ∧ Disjoint Q F ∧ f < P.card ∧ Disjoint Q P ∧
        ∀ s ∈ Q, ∃ p ∈ (A.run (E₀ ++ .inv a (.write v) :: E₁)).pend a,
          p.op.IsWrite ∧ p.reg ∉ Cov (A.run E₀) ∧ δ p.reg = s := by
  set X₀ := A.run E₀
  set K := Cov X₀
  set X₁ := A.run (E₀ ++ [.inv a (.write v)])
  have hX₁ : X₁ = A.doInv X₀ a (.write v) := by simp [X₁, run_append, X₀]
  set st := rseq δ F a K A f X₁
  have hpend₁ : X₁.pend a = [] := by rw [hX₁, doInv_pend]; exact ha0
  have hcovF₁ : covF δ F a K X₁ = ∅ := by
    ext s; simp [mem_covF, hpend₁]
  have hinv0 : RInv δ F a K f X₀ v (st 0) := by
    obtain ⟨hc, hh⟩ := A.doInv_of_idle X₀ a (.write v) (hidle a)
    have hst0 : (st 0).X = A.doInv X₀ a (.write v) := hX₁
    refine ⟨fun c hc' => by rw [hst0]; exact A.doInv_other X₀ (.write v) hc',
      fun b _ => by rw [hst0]; simp,
      by simp [st, rseq], by simp [st, rseq], by simp [st, rseq, frSet], ?_, by simp [st, rseq],
      Or.inl ⟨by rw [hst0]; exact hc, by rw [hst0]; exact hh⟩, A.wf_run _⟩
    intro _
    simp [st, rseq, hcovF₁, frSet]
  have hinv : ∀ t, RInv δ F a K f X₀ v (st t) := by
    intro t; induction t with
    | zero => exact hinv0
    | succ t ih => exact (A.rInv_step ih).1
  have hmonoQ : ∀ t ≥ 0, (st t).Q ⊆ (st (t + 1)).Q := fun t _ => (A.rInv_step (hinv t)).2.1
  have hmonoW : ∀ t ≥ 0, (st t).Wd ⊆ (st (t + 1)).Wd := fun t _ => (A.rInv_step (hinv t)).2.2
  obtain ⟨T₁, -, hT₁⟩ := Finset.eventually_const_of_subset_succ_of_finite
    (f := fun t => (st t).Q) hmonoQ
  obtain ⟨T₂, -, hT₂⟩ := Finset.eventually_const_of_subset_succ_of_finite
    (f := fun t => (st t).Wd) hmonoW
  set T := max T₁ T₂
  set Zs := zSet δ F K (st T).Q (st T).Wd
  have hZ : ∀ t ≥ T, zSet δ F K (st t).Q (st t).Wd = Zs := by
    intro t ht
    simp only [Zs]
    rw [hT₁ t (le_of_max_le_left ht), hT₂ t (le_of_max_le_right ht),
      hT₁ T (le_max_left _ _), hT₂ T (le_max_right _ _)]
  have hZs : Zs.card ≤ f := zSet_card_le hF (hinv T).qcard (hinv T).fcard
  -- Lemma 3: the write returns
  obtain ⟨u, hu⟩ := A.exists_ret_of_solo hOF (P₀ := E₀) (c := a) (o := .write v)
    (e := fun t => soloEv δ a (zSet δ F K (st t).Q (st t).Wd) (st t).X) (X := fun t => (st t).X)
    (Z := fun t => zSet δ F K (st t).Q (st t).Wd) (T := T) hZs
    (by
      intro d w hd
      rcases List.mem_append.1 hd with hd | hd
      · exact hE₀ d w hd
      · simp at hd; rw [hd.1]; exact ha)
    (hidle a) rfl (fun t => rfl) (fun t => rfl) hZ
  set E₁ := (List.range u).map fun t => soloEv δ a (zSet δ F K (st t).Q (st t).Wd) (st t).X
  have hE₁ : ∀ e ∈ E₁, e.IsOf a := by
    intro e he; obtain ⟨t, -, rfl⟩ := List.mem_map.1 he; exact soloEv_isOf _ _ _ _
  have hY : (st u).X = A.run (E₀ ++ .inv a (.write v) :: E₁) := by
    rw [A.seq_exec (X := fun t => (st t).X) (fun t => rfl) u]
    rw [show E₀ ++ Ev.inv a (.write v) :: E₁ = (E₀ ++ [.inv a (.write v)]) ++ E₁ by simp,
      run_append]
    rfl
  obtain ⟨x, hx⟩ : ∃ x, (st u).X.hist = X₀.hist ++ [.inv a (.write v), .ret a x] := by
    rcases (hinv u).ret with ⟨h1, -⟩ | ⟨-, x, h2⟩
    · rw [hu] at h1; cases h1
    · exact ⟨x, by rw [h2]; simp⟩
  -- Lemma 4: more than `f` servers with a fresh written register
  have hfresh := A.fresh_resp hOF hS hE₀ hL hLw hidle ha hrd ha0 hv hE₁ (x := x) (by rw [← hY]; exact hx)
  rw [← hY] at hfresh
  have hdiff : diffSrv δ (Cov X₀) X₀ (st u).X ⊆ frSet δ K (st u).Wd := by
    intro s hs
    obtain ⟨b, hbK, hne, rfl⟩ := mem_diffSrv.1 hs
    refine mem_frSet.2 ⟨b, ?_, hbK, rfl⟩
    by_contra hb
    exact hne ((hinv u).val b hb)
  have hfr : f < (frSet δ K (st u).Wd).card := lt_of_lt_of_le hfresh (Finset.card_le_card hdiff)
  -- Corollary 2: `|Q| = f`
  have hQ : (st u).Q.card = f := by
    by_contra hne
    have hl : (st u).Q.card < f := lt_of_le_of_ne (hinv u).qcard hne
    have hsub := ((hinv u).small hl).2
    have : frSet δ K (st u).Wd ∩ F = frSet δ K (st u).Wd := Finset.inter_eq_left.2 hsub
    have := (hinv u).fcard
    rw [‹frSet δ K (st u).Wd ∩ F = _›] at this
    omega
  refine ⟨E₁, hE₁, x, hY ▸ hx, hY ▸ hu, (st u).Q, frSet δ K (st u).Wd, hQ, ?_, hfr, (hinv u).disj,
    ?_⟩
  · rw [Finset.disjoint_left]
    intro s hs
    exact (mem_covF.1 ((hinv u).qsub hs)).1
  · intro s hs
    obtain ⟨-, p, hp, hw, hK, rfl⟩ := mem_covF.1 ((hinv u).qsub hs)
    exact ⟨p, hY ▸ hp, hw, hK, rfl⟩

/-- Letting the pending writes of `a` in `l` take effect. -/
lemma flush_mem {a : C} (q : POp B W) :
    ∀ (l : List (POp B W)), l.Nodup → ∀ {X : Cfg C B V W L}, WF X → (∀ p ∈ l, p ∈ X.pend a) →
    (q ∈ (A.exec X (l.map fun p => .resp a p.n)).pend a ↔ q ∈ X.pend a ∧ q ∉ l) := by
  intro l
  induction l with
  | nil => intro _ X _ _; simp
  | cons p l ih =>
    intro hnd X hwf hl
    obtain ⟨hpl, hnd'⟩ := List.nodup_cons.1 hnd
    have hp := hl p (by simp)
    simp only [List.map_cons, exec_cons, step_resp, A.doResp_of_mem hwf hp]
    rw [ih hnd' (A.wf_apply hwf a p) ?_, apply_pend_self, mem_filter_ne hwf hp]
    · simp only [List.mem_cons, not_or]
      tauto
    · intro p' hp'
      rw [apply_pend_self, mem_filter_ne hwf hp]
      exact ⟨hl p' (by simp [hp']), fun h => hpl (h ▸ hp')⟩

end Alg

/-- Alternating values: `val v₀ v' i ≠ val v₀ v' (i+1)`, `val v₀ v' 0 = v' ≠ v₀`. -/
def altVal (v₀ v' : V) (i : ℕ) : V := if i % 2 = 0 then v' else v₀

/-- The value of the register after `i` writes of `altVal`. -/
def altLast (v₀ v' : V) (i : ℕ) : V := if i = 0 then v₀ else altVal v₀ v' (i - 1)

lemma altVal_ne_altLast {v₀ v' : V} (h : v' ≠ v₀) (i : ℕ) : altVal v₀ v' i ≠ altLast v₀ v' i := by
  unfold altLast
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa [altVal] using h
  · rw [if_neg hi.ne']
    unfold altVal
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
    · rw [if_pos h2, if_neg (by omega)]; exact h
    · rw [if_neg (by omega), if_pos (by omega)]; exact Ne.symm h

namespace Alg

variable (A : Alg C B V W L)

/-- Properties of the run `rᵢ` used in the induction of Lemma 1. -/
structure Good (δ : B → S) (F : Finset S) (Wr : Set C) (w : ℕ → C) (v₀ v' : V) (i : ℕ)
    (E : List (Ev C V)) : Prop where
  wr : ∀ d v, Ev.inv d (.write v) ∈ E → d ∈ Wr
  hist : ∃ Ls : List (C × HOp V × V), (A.run E).hist = seqHist Ls ∧
    Ls.map (fun e => (e.1, e.2.1)) = (List.range i).map (fun j => (w j, .write (altVal v₀ v' j))) ∧
    lastVal v₀ Ls = altLast v₀ v' i
  idle : ∀ c, (A.run E).cur c = none
  fresh : ∀ c, (∀ j < i, c ≠ w j) → (A.run E).pend c = []
  offF : ∀ b ∈ Cov (A.run E), δ b ∉ F

/-- One step of Lemma 1, including the final flush of the writer's pending writes on `F`. -/
theorem lemma1_step {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ v' : V} (hv' : v' ≠ v₀)
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr) {F : Finset S} (hF : F.card ≤ f + 1)
    {w : ℕ → C} {i : ℕ} (hwW : ∀ j ≤ i, w j ∈ Wr) (hwinj : ∀ j < i, w i ≠ w j) {rd : C} (hrd : rd ≠ w i)
    {E : List (Ev C V)} (hE : A.Good δ F Wr w v₀ v' i E) :
    ∃ E', E <+: E' ∧ A.Good δ F Wr w v₀ v' (i + 1) E' ∧ Cov (A.run E) ⊆ Cov (A.run E') ∧
      (Cov (A.run E)).card + f ≤ (Cov (A.run E')).card ∧
      ∃ Q : Finset S, Q.card = f ∧ Disjoint Q F ∧
        ∀ s ∈ Q, ∃ b ∈ Cov (A.run E') \ Cov (A.run E), δ b = s := by
  classical
  obtain ⟨Ls, hL, hLmap, hLlast⟩ := hE.hist
  set a := w i
  have hLw : ∀ e ∈ Ls, ∀ v, e.2.1 = .write v → e.1 ∈ Wr := by
    intro e he v _
    have : (e.1, e.2.1) ∈ (List.range i).map (fun j => (w j, HOp.write (altVal v₀ v' j))) :=
      hLmap ▸ List.mem_map_of_mem he
    obtain ⟨j, hj, hj'⟩ := List.mem_map.1 this
    rw [← (Prod.mk.inj hj').1]
    exact hwW j (by simp at hj; omega)
  have ha0 : (A.run E).pend a = [] := hE.fresh a (fun j hj => hwinj j hj)
  have hv : altVal v₀ v' i ≠ lastVal v₀ Ls := hLlast ▸ altVal_ne_altLast hv' i
  obtain ⟨E₁, hE₁, x, hhist, hcur, Q, P, hQc, hQF, -, -, hQw⟩ :=
    A.round_main hOF hS hF hE.wr hL hLw hE.idle (hwW i le_rfl) hrd ha0 hv
  set X₀ := A.run E
  set Y := A.run (E ++ .inv a (.write (altVal v₀ v' i)) :: E₁)
  have hYwf : WF Y := A.wf_run _
  -- `Y` agrees with `X₀` on all clients but `a`
  have hYrel : ∀ c ≠ a, Y.pend c = X₀.pend c ∧ Y.cur c = X₀.cur c := by
    intro c hc
    have hYe : Y = A.exec (A.doInv X₀ a (.write (altVal v₀ v' i))) E₁ := by
      simp only [Y, run_append, exec_cons, step_inv]; rfl
    obtain ⟨h1, -, h3, -⟩ := A.exec_other (A.doInv X₀ a (.write (altVal v₀ v' i))) hE₁ hc
    obtain ⟨g1, -, g3, -⟩ := A.doInv_other X₀ (.write (altVal v₀ v' i)) hc
    rw [hYe]
    exact ⟨h1.trans g1, h3.trans g3⟩
  set l := (Y.pend a).filter (fun p => decide (p.op.IsWrite ∧ δ p.reg ∈ F))
  set G : List (Ev C V) := l.map fun p => .resp a p.n
  have hlnd : l.Nodup := (((hYwf a).1.of_map _)).filter _
  have hlmem : ∀ p ∈ l, p ∈ Y.pend a := fun p hp => List.mem_of_mem_filter hp
  have hGa : ∀ e ∈ G, e.IsOf a := by
    intro e he; obtain ⟨p, -, rfl⟩ := List.mem_map.1 he; rfl
  have hGr : ∀ e ∈ G, e.IsResp := by
    intro e he; obtain ⟨p, -, rfl⟩ := List.mem_map.1 he; trivial
  set E' := E ++ .inv a (.write (altVal v₀ v' i)) :: E₁ ++ G
  have hY' : A.run E' = A.exec Y G := run_append _ _ _
  have hpa : ∀ q, q ∈ (A.run E').pend a ↔ q ∈ Y.pend a ∧ q ∉ l := fun q => by
    rw [hY']; exact A.flush_mem q l hlnd hYwf hlmem
  have hpo : ∀ c ≠ a, (A.run E').pend c = X₀.pend c ∧ (A.run E').cur c = X₀.cur c := by
    intro c hc
    rw [hY', (A.exec_other Y hGa hc).1, (A.exec_other Y hGa hc).2.2.1]
    exact hYrel c hc
  obtain ⟨hcurG, hhistG⟩ := A.exec_resp_cur_hist Y hGr
  have hcovmono : Cov X₀ ⊆ Cov (A.run E') := by
    intro b hb
    obtain ⟨c, p, hp, rfl, hw⟩ := mem_Cov.1 hb
    have hc : c ≠ a := by rintro rfl; rw [ha0] at hp; simp at hp
    exact mem_Cov.2 ⟨c, p, by rw [(hpo c hc).1]; exact hp, rfl, hw⟩
  have hnew : ∀ s ∈ Q, ∃ b ∈ Cov (A.run E') \ Cov X₀, δ b = s := by
    intro s hs
    obtain ⟨p, hp, hw, hK, rfl⟩ := hQw s hs
    have hpl : p ∉ l := by
      intro h
      have := (List.mem_filter.1 h).2
      simp only [decide_eq_true_eq] at this
      exact Finset.disjoint_left.1 hQF hs this.2
    exact ⟨p.reg, Finset.mem_sdiff.2 ⟨mem_Cov.2 ⟨a, p, (hpa p).2 ⟨hp, hpl⟩, rfl, hw⟩, hK⟩, rfl⟩
  refine ⟨E', ?_, ?_, hcovmono, ?_, Q, hQc, hQF, hnew⟩
  · exact ⟨.inv a (.write (altVal v₀ v' i)) :: E₁ ++ G, by simp [E']⟩
  · refine ⟨?_, ⟨Ls ++ [(a, .write (altVal v₀ v' i), x)], ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro d u hd
      simp only [E', List.mem_append, List.mem_cons] at hd
      rcases hd with ((hd | hd | hd) | hd)
      · exact hE.wr d u hd
      · cases hd; exact hwW i le_rfl
      · exact (hE₁ _ hd).elim
      · exact (hGr _ hd).elim
    · rw [hY', hhistG, hhist, hL, seqHist_append]; rfl
    · rw [List.map_append, hLmap, List.range_succ, List.map_append]; rfl
    · rw [lastVal_append_write]; simp [altLast]
    · intro c
      by_cases hc : c = a
      · subst hc; rw [hY', hcurG]; exact hcur
      · rw [(hpo c hc).2]; exact hE.idle c
    · intro c hc
      have hca : c ≠ a := hc i (Nat.lt_succ_self i)
      rw [(hpo c hca).1]
      exact hE.fresh c (fun j hj => hc j (Nat.lt_succ_of_lt hj))
    · intro b hb
      obtain ⟨c, p, hp, rfl, hw⟩ := mem_Cov.1 hb
      by_cases hc : c = a
      · subst hc
        obtain ⟨hp1, hp2⟩ := (hpa p).1 hp
        intro hF'
        exact hp2 (List.mem_filter.2 ⟨hp1, by simp [hw, hF']⟩)
      · exact hE.offF _ (mem_Cov.2 ⟨c, p, by rw [← (hpo c hc).1]; exact hp, rfl, hw⟩)
  · have hsub : Q ⊆ (Cov (A.run E') \ Cov X₀).image δ := by
      intro s hs
      obtain ⟨b, hb, rfl⟩ := hnew s hs
      exact Finset.mem_image_of_mem _ hb
    have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
    have h2 := Finset.card_sdiff_add_card_eq_card hcovmono
    omega

lemma good_zero {δ : B → S} {F : Finset S} {Wr : Set C} {w : ℕ → C} {v₀ v' : V} :
    A.Good δ F Wr w v₀ v' 0 [] := by
  refine ⟨by simp, ⟨[], rfl, by simp, rfl⟩, fun c => rfl, fun c _ => rfl, fun b hb => ?_⟩
  obtain ⟨c, p, hp, -⟩ := mem_Cov.1 hb
  exact absurd hp (by simp [run, exec, initCfg])

/-- **Lemma 1** of the paper, extended version (Appendix C) items (a), (b), (d), (e): for every set
`F` of at most `f + 1` servers there are runs `E 0 = [] ⊑ E 1 ⊑ … ⊑ E k`, where `E i` is a
sequential (failure-free, write-only) run of `i` complete writes by the distinct writers
`w 0, …, w (i-1)` (of alternating values), such that (a) `|Cov(tᵢ)| ≥ i f`,
(b) `δ(Cov(tᵢ)) ∩ F = ∅`, (e) `Cov(tᵢ) ⊆ Cov(tᵢ₊₁)` and (d) `f` servers outside `F` hold a register of
`Cov(tᵢ₊₁) \ Cov(tᵢ)`.

Hypotheses: `A` is `f`-tolerant obstruction-free and safe in sequential runs (implied by WS-Safe), only
the clients in `Wr` write, there is a reader `rd` distinct from the writers, and a value `v' ≠ v₀`. -/
theorem lemma1 {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ v' : V} (hv' : v' ≠ v₀)
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr) {F : Finset S} (hF : F.card ≤ f + 1)
    {k : ℕ} {w : ℕ → C} (hwW : ∀ j < k, w j ∈ Wr) (hwinj : ∀ i < k, ∀ j < k, w i = w j → i = j)
    {rd : C} (hrd : ∀ j < k, rd ≠ w j) :
    ∃ E : ℕ → List (Ev C V), E 0 = [] ∧
      (∀ i ≤ k, (∃ Ls : List (C × HOp V × V), (A.run (E i)).hist = seqHist Ls ∧
          Ls.map (fun e => (e.1, e.2.1)) = (List.range i).map (fun j => (w j, .write (altVal v₀ v' j)))) ∧
        i * f ≤ (Cov (A.run (E i))).card ∧ ∀ b ∈ Cov (A.run (E i)), δ b ∉ F) ∧
      ∀ i < k, E i <+: E (i + 1) ∧ Cov (A.run (E i)) ⊆ Cov (A.run (E (i + 1))) ∧
        ∃ Q : Finset S, Q.card = f ∧ Disjoint Q F ∧
          ∀ s ∈ Q, ∃ b ∈ Cov (A.run (E (i + 1))) \ Cov (A.run (E i)), δ b = s := by
  suffices h : ∀ m ≤ k, ∃ E : ℕ → List (Ev C V), E 0 = [] ∧
      (∀ i ≤ m, A.Good δ F Wr w v₀ v' i (E i) ∧ i * f ≤ (Cov (A.run (E i))).card) ∧
      ∀ i < m, E i <+: E (i + 1) ∧ Cov (A.run (E i)) ⊆ Cov (A.run (E (i + 1))) ∧
        ∃ Q : Finset S, Q.card = f ∧ Disjoint Q F ∧
          ∀ s ∈ Q, ∃ b ∈ Cov (A.run (E (i + 1))) \ Cov (A.run (E i)), δ b = s by
    obtain ⟨E, h0, hg, hc⟩ := h k le_rfl
    refine ⟨E, h0, fun i hi => ?_, hc⟩
    obtain ⟨hG, hcard⟩ := hg i hi
    obtain ⟨Ls, h1, h2, -⟩ := hG.hist
    exact ⟨⟨Ls, h1, h2⟩, hcard, hG.offF⟩
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ => [], rfl, fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    exact ⟨A.good_zero, by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨E, h0, hg, hc⟩ := ih (by omega)
    obtain ⟨E', hpre, hG', hmono, hcard, Q, hQ⟩ := A.lemma1_step hv' hOF hS hF
      (w := w) (i := m) (fun j hj => hwW j (by omega))
      (fun j hj h => by have := hwinj m (by omega) j (by omega) h; omega)
      (hrd m (by omega)) (hg m le_rfl).1
    refine ⟨fun i => if i ≤ m then E i else E', by simp [h0], fun i hi => ?_, fun i hi => ?_⟩
    · by_cases him : i ≤ m
      · simp only [him, ite_true]; exact hg i him
      · obtain rfl : i = m + 1 := by omega
        simp only [show ¬ m + 1 ≤ m by omega, ite_false]
        refine ⟨hG', ?_⟩
        have := (hg m le_rfl).2
        rw [Nat.succ_mul]; omega
    · by_cases him : i + 1 ≤ m
      · simp only [him, show i ≤ m by omega, ite_true]; exact hc i (by omega)
      · obtain rfl : i = m := by omega
        simp only [le_rfl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false]
        exact ⟨hpre, hmono, Q, hQ⟩

end Alg

end Podc.RegisterEmulationSpace
