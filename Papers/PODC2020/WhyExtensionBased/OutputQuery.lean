import Papers.PODC2020.WhyExtensionBased.Actions

/-!
# The adversary's answers to output queries in phase 1

An output query `(C, Q, y)` asks for a `Q`-only schedule from `C` after which some process of `Q`
has output `y`. Our (repaired) adversary answers:

* **(S)** if some `Q`-descendant of `C` has already terminated with `y`: a schedule to it (restricted to
  its causal past, so that only decided states are passed);
* **(U)** otherwise, if some undecided `Q`-descendant `x` with at least `t` rounds is *unprotected*
  (it has seen `y` and is not adjacent to a vertex that terminated with another value): let the
  process of `x` run alone until it is ahead of everybody, subdivide, and terminate its next state
  `s₁` (which has seen only its own previous state) with `y` — `s₁` is safe (`safe_solo`);
* **(N)** otherwise `none`, recording the query: all its descendants are protected (`RecOK`).

The paper's cases 1 and 2 are instances of (U) (with `x` of exactly `t` rounds); its case 3 may answer
`none` although deeper descendants are unprotected, see `differencies.md`.
-/

namespace Podc.WhyExtensionBased

open Cslib.NIS Cslib.NIS.Subdiv St
open scoped Classical

variable {P X : Type} [DecidableEq P]

/-- `δ` agrees with the adversary state `A` on all states decided by `A`. -/
def Agree (A : AState P X) (δ : Protocol P X X) : Prop :=
  ∀ s, Fixd A s → decided δ s = decided A.term s

lemma Agree.of_le {A A' : AState P X} {δ : Protocol P X X} (h : Le A A') (hδ : Agree A' δ) :
    Agree A δ := fun s hs => by rw [hδ s (h.fixd hs), h.2.2 s hs]

/-- A correct "some" answer that stays correct for every protocol extending the adversary state. -/
def GoodSome (A : AState P X) (C : Config P X) (Q : Finset P) (y : X) (μ : List P) : Prop :=
  (∀ p ∈ μ, p ∈ Q) ∧ ∀ δ, Agree A δ → IsSched δ C μ ∧ ∃ p ∈ Q, outs δ (exec C μ) p = some y

/-- A good reaction to an output query: a new adversary state and a lasting "some" answer. -/
def OQGood (A A' : AState P X) (C : Config P X) (Q : Finset P) (y : X) (μ : List P) : Prop :=
  AInv A' ∧ Le A A' ∧ (∀ C', RC A.term A.t C' → RC A'.term A'.t C') ∧ GoodSome A' C Q y μ

/-- The undecided `Q`-descendants that would make a `none` answer unsafe. -/
def Unprot (δ : Protocol P X X) (t : ℕ) (y : X) (x : St P X) : Prop :=
  t ≤ x.rounds ∧ x.Settled ∧ decided δ x = none ∧ ¬ Prot δ y x

/-- The adversary's answer to the output query `(C, Q, y)` in phase 1. -/
noncomputable def oq (A : AState P X) (C : Config P X) (Q : Finset P) (y : X) :
    AState P X × Option (List P) :=
  if h : ∃ A' μ, OQGood A A' C Q y μ then (Classical.choose h, some (Classical.choose
    (Classical.choose_spec h)))
  else ({ A with recs := (C, Q, y) :: A.recs }, none)

/-! ## Helpers -/

lemma occ_own_pid {δ : Protocol P X X} {r : ℕ} {z : St P X} (hz : Occ δ z) (hzs : z.Settled)
    (hzr : z.rounds = r + 1) : (own r z).pid = z.pid := by
  obtain ⟨E, hE, hEz⟩ := hz
  have hmem : z ∈ (E z.pid).anc := by rw [hEz]; exact St.mem_anc_self _
  have hv := Occ.own_view ⟨E, hE, hEz⟩ hzs hzr
  cases z with
  | init i x => simp [rounds] at hzr
  | upd w => exact absurd hzs id
  | scan s v =>
    obtain ⟨s', rfl, -, hv'⟩ := Rch.scan_shape hE.rch hmem
    simp only [view_scan] at hv
    have hown : own r (scan (upd s') v) = s' := Option.some_injective _ (hv.symm.trans hv')
    rw [hown]
    have : upd s' ∈ (E (scan (upd s') v).pid).anc := by
      rw [hEz]; simp [St.anc, St.mem_anc_self]
    have := Rch.pid_anc hE.rch this
    simpa [St.pid] using this

lemma decided_eq_none_of_not_settled {δ : Protocol P X X} {z : St P X} (h : ¬ z.Settled) :
    decided δ z = none := by
  cases z <;> simp_all [Settled, decided]

/-- If the strict past of `x` is decided by `A` (fewer than `t` rounds) and active, it is active for
every protocol agreeing with `A`. -/
lemma past_active_of_agree {A : AState P X} {δ : Protocol P X X} (hδ : Agree A δ) {x : St P X}
    (hx : Occ A.term x) (hxs : x.Settled) (hxt : x.rounds ≤ A.t) :
    ∀ z, InPast z x → z ≠ x → decided δ z = none := by
  intro z hz hne
  by_cases hzs : z.Settled
  · have h1 := hx.past_active hz hne
    have h2 := Occ.past_rounds hx hz hne hzs hxs
    rw [hδ z (Or.inl (by omega)), h1]
  · exact decided_eq_none_of_not_settled hzs

/-! ## (S): a descendant already output `y` -/

lemma oq_some_of_terminated {A : AState P X} (hA : AInv A) {C : Config P X}
    (hC : RC A.term A.t C) {Q : Finset P} {y : X} {x : St P X} (hx : QDesc A.term C Q x)
    (hxy : decided A.term x = some y) : ∃ A' μ, OQGood A A' C Q y μ := by
  obtain ⟨μ, hμQ, hμ, p, hp, hpx⟩ := hx
  obtain ⟨u, β, hβ, rfl⟩ := hC.1
  obtain ⟨μ', hsub, hA1, -, hsched⟩ := exists_sched_restrict (x := u) (β := β) (μ := μ) {p}
  have hxe : exec (initC u) (β ++ μ) p = x := by rw [exec_append]; exact hpx
  have hxs : x.Settled := by cases x <;> simp_all [decided, Settled]
  have hxo : Occ A.term x := by
    have hR := (hC.1).run hμ
    exact ⟨_, hR, by rw [← hpx, hR.pid]⟩
  have hxt : x.rounds ≤ A.t := hA.dec_le x (by rw [hxy]; simp)
  refine ⟨A, μ', hA, Le.refl A, fun C' h => h, fun q hq => hμQ q (hsub.subset hq), fun δ hδ => ?_⟩
  have hpast := past_active_of_agree hδ hxo hxs hxt
  refine ⟨hsched δ fun i hi => by simp at hi; subst hi; rw [hxe]; exact hpast, p, hp, ?_⟩
  rw [outs, hA1 p rfl, hxe, hδ x (Or.inr (by rw [hxy]; simp)), hxy]

/-! ## (U): the safe solo vertex -/

/-- **Safety of a solo vertex.** If nothing is terminated at level `t`, `x` has `t - 1` rounds, is
active, has seen `y`, and is not adjacent to a vertex terminated with another value, then a vertex
`s₁` of `t` rounds whose carrier is `{x}` (the process of `x` scanned alone) is safe for `y`. -/
lemma safe_solo {δ : Protocol P X X} {r : ℕ} {y : X}
    (h0 : ∀ s, decided δ s ≠ none → s.rounds ≤ r)
    (h4 : Far (Adj δ (r + 1)) (Tset δ (r + 1) y) (Uset δ (r + 1) y) 2)
    (h5 : ∀ b, b ≠ y → Far (Adj δ (r + 1)) (Tset δ (r + 1) y) (Tset δ (r + 1) b) 3)
    {x s₁ : St P X} (hxd : decided δ x = none) (hxy : Seen y x)
    (hxp : ¬ ∃ w b, b ≠ y ∧ decided δ w = some b ∧ Adj δ r x w)
    (hs₁o : Occ δ s₁) (hs₁s : s₁.Settled) (hs₁r : s₁.rounds = r + 1)
    (hcar : ∀ c ∈ car r s₁, c = x) : Safe δ (r + 1) s₁ y := by
  have hxc : x ∈ car r s₁ := by rw [← hcar _ (own_mem_car s₁)]; exact own_mem_car s₁
  have hs₁y : Seen y s₁ := hxy.mono (hs₁o.mem_car hs₁s hs₁r hxc).2.2.2.2
  have hs₁d : decided δ s₁ = none := by
    by_contra h; have := h0 _ h; omega
  -- neighbours of `s₁`: new ones contain `x` in their carrier, old ones terminated with `y`
  have hnb : ∀ z, Adj δ (r + 1) s₁ z →
      (z.rounds = r + 1 ∧ x ∈ car r z ∧ decided δ z = none) ∨ z ∈ Tset δ (r + 1) y := by
    intro z hz
    have ⟨hpid, _, hzv, _⟩ := hz
    by_cases hzr : z.rounds = r + 1
    · left
      have hzd : decided δ z = none := by by_contra h; have := h0 _ h; omega
      refine ⟨hzr, ?_, hzd⟩
      have hzo := hz.occ_right
      have hown : decided δ (own r z) = none :=
        (hzo.mem_car hzv.1 hzr (own_mem_car z)).2.2.1
      have hown1 : own r s₁ = x := hcar _ (own_mem_car s₁)
      rcases hz.nested (by rw [hown1]; exact hxd) hown with h | h
      · exact h hxc
      · have := hcar _ (h (own_mem_car z))
        exfalso; apply hpid
        rw [← occ_own_pid hzo hzv.1 hzr, this, ← hown1, occ_own_pid hs₁o hs₁s hs₁r]
    · right
      have hzt : z.rounds < r + 1 := by rcases hzv.2 with h | h <;> omega
      have hzd : decided δ z ≠ none := by rcases hzv.2 with h | h; omega; exact h.2
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hzd
      have hzc : car r z = {z} := by simp [car, hzr]
      rcases hz.car_cases hxc (by rw [hzc]; rfl) with h | h
      · subst h; rw [hxd] at hb; simp at hb
      · by_cases hby : b = y
        · subst hby; exact mem_Tset_of_adj hz hb
        · exact absurd ⟨z, b, hby, hb, h⟩ hxp
  refine ⟨far_of_neighbors (fun h => h.2.2 hs₁y) fun z hz => ?_, fun b hb => ?_⟩
  · refine far_of_neighbors (fun hzU => ?_) fun _ _ => far_zero _ _
    rcases hnb z hz with ⟨hzr, hzx, -⟩ | hzT
    · exact hzU.2.2 ((hzU.2.1.seen_iff_car hzU.1.1 hzr y).2 ⟨x, hzx, hxy⟩)
    · exact far_not_mem h4 (by norm_num) hzT hzU
  · refine far_of_neighbors (fun h => by rw [h.2.2] at hs₁d; simp at hs₁d) fun z hz => ?_
    rcases hnb z hz with ⟨hzr, hzx, hzd⟩ | hzT
    · refine far_of_neighbors (fun h => by rw [h.2.2] at hzd; simp at hzd) fun w hw => ?_
      refine far_of_neighbors (fun hwT => ?_) fun _ _ => far_zero _ _
      have hwr : w.rounds ≠ r + 1 := fun h => by
        have := h0 w (by rw [hwT.2.2]; simp); omega
      have hwc : car r w = {w} := by simp [car, hwr]
      rcases hw.car_cases hzx (by rw [hwc]; rfl) with h | h
      · subst h; exact absurd (hwT.2.2.symm.trans hxd) (by simp)
      · exact hxp ⟨w, b, hb, hwT.2.2, h⟩
    · refine far_of_neighbors (fun h => ?_) fun w hw => ?_
      · exact hb (Option.some_injective _ (hzT.2.2.symm.trans h.2.2)).symm
      · exact far_of_neighbors (fun hwT => far_not_adj (h5 b hb) (by norm_num) hzT hwT hw)
          fun _ _ => far_zero _ _

/-! ## (U): letting an unprotected descendant run alone -/

lemma own_of_scan {δ : Protocol P X X} {r : ℕ} {s : St P X} {v : P → Option (St P X)}
    (hz : Occ δ (scan (upd s) v)) (hr : (scan (upd s) v).rounds = r + 1) :
    own r (scan (upd s) v) = s := by
  have hv := Occ.own_view hz trivial hr
  obtain ⟨E, hE, hEz⟩ := hz
  have hmem : scan (upd s) v ∈ (E (scan (upd s) v).pid).anc := by rw [hEz]; exact St.mem_anc_self _
  obtain ⟨s', hs', -, hv'⟩ := Rch.scan_shape hE.rch hmem
  cases hs'
  simp only [view_scan] at hv
  exact Option.some_injective _ (hv.symm.trans hv')

lemma stepState_of_settled {C : Config P X} {q : P} (h : (C q).Settled) :
    stepState C q = upd (C q) := by
  rcases stepState_cases C q with ⟨s, h1, -⟩ | ⟨-, h2⟩
  · rw [h1] at h; exact absurd h id
  · exact h2

lemma stepState_upd {C : Config P X} {q : P} {s : St P X} (h : C q = upd s) :
    stepState C q = scan (upd s) (fun j => (C j).hist[s.rounds]?) := by
  rcases stepState_cases C q with ⟨s', h1, h2⟩ | ⟨h1, -⟩
  · rw [h1] at h; cases h; exact h2
  · exact absurd h (h1 s)

/-- One more round of the process of an unprotected undecided descendant: still unprotected. -/
lemma unprot_round {A : AState P X} (hA : AInv A) {y : X} {E : Config P X}
    (hE : Reach A.term E) {p : P} (hu : Unprot A.term A.t y (E p)) :
    Reach A.term (exec E [p, p]) ∧ Unprot A.term A.t y (exec E [p, p] p) ∧
      (exec E [p, p] p).rounds = (E p).rounds + 1 ∧ (∀ j, j ≠ p → exec E [p, p] j = E j) ∧
      IsSched A.term E [p, p] := by
  obtain ⟨ht, hset, hd, hnp⟩ := hu
  have h1 : step E p p = upd (E p) := by rw [step_self, stepState_of_settled hset]
  have hsched : IsSched A.term E [p, p] := by
    refine ⟨hd, ?_, trivial⟩
    show decided A.term (step E p p) = none
    rw [h1]; rfl
  have hR := hE.run hsched
  set x' := exec E [p, p] p with hx'
  have hx'eq : x' = scan (upd (E p)) (fun j => (step E p j).hist[(E p).rounds]?) := by
    rw [hx']; simp only [exec_cons, exec_nil, step_self]; exact stepState_upd h1
  have hxr : x'.rounds = (E p).rounds + 1 := by rw [hx'eq]; simp [rounds]
  have hxo : Occ A.term x' := ⟨_, hR, by rw [hR.pid]⟩
  have hxd : decided A.term x' = none := by
    by_contra h; have := hA.dec_le _ h; omega
  refine ⟨hR, ⟨by omega, by rw [hx'eq]; trivial, hxd, ?_⟩, hxr, fun j hj => ?_, hsched⟩
  · rintro (h | ⟨w, b, hb, hwb, hadj⟩)
    · apply h
      have : InPast (E p) x' := by
        rw [hx'eq]; exact InPast.scanSelf (InPast.upd (InPast.refl _))
      have hsy : Seen y (E p) := by
        by_contra hns; exact hnp (Or.inl hns)
      exact hsy.mono this
    · rw [hxr] at hadj
      have hown : own (E p).rounds x' = E p := by
        rw [hx'eq]; rw [hx'eq] at hxo hxr; exact own_of_scan hxo hxr
      have hwr : w.rounds ≠ (E p).rounds + 1 := fun h => by
        have := hA.dec_le w (by rw [hwb]; simp); omega
      have hwc : car (E p).rounds w = {w} := by simp [car, hwr]
      rcases hadj.car_cases (own_mem_car x') (by rw [hwc]; rfl) with h | h
      · rw [hown] at h; rw [← h, hd] at hwb; simp at hwb
      · rw [hown] at h; exact hnp (Or.inr ⟨w, b, hb, hwb, h⟩)
  · simp only [exec_cons, exec_nil]; rw [step_ne _ hj, step_ne _ hj]

lemma unprot_rounds {A : AState P X} (hA : AInv A) {y : X} {E : Config P X}
    (hE : Reach A.term E) {p : P} (hu : Unprot A.term A.t y (E p)) (m : ℕ) :
    ∃ γ : List P, (∀ q ∈ γ, q = p) ∧ IsSched A.term E γ ∧ Unprot A.term A.t y (exec E γ p) ∧
      (exec E γ p).rounds = (E p).rounds + m ∧ (∀ j, j ≠ p → exec E γ j = E j) := by
  induction m with
  | zero => exact ⟨[], by simp, trivial, hu, rfl, fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨γ, hγp, hγ, hγu, hγr, hγo⟩ := ih
    obtain ⟨-, hu', hr', ho', hs'⟩ := unprot_round hA (hE.run hγ) hγu
    refine ⟨γ ++ [p, p], fun q hq => ?_, (isSched_append _ _ _).2 ⟨hγ, hs'⟩, ?_, ?_, fun j hj => ?_⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with h | h | h
      · exact hγp q h
      · exact h
      · exact h
    · rw [exec_append]; exact hu'
    · rw [exec_append, hr', hγr]; ring
    · rw [exec_append, ho' j hj, hγo j hj]



/-- **(U)**: an unprotected undecided descendant yields a good "some" answer. -/
lemma oq_some_of_unprot [Fintype P] {A : AState P X} (hA : AInv A) {C : Config P X}
    (hC : RC A.term A.t C) {Q : Finset P} {y : X} {x : St P X} (hx : QDesc A.term C Q x)
    (hu : Unprot A.term A.t y x) : ∃ A' μ, OQGood A A' C Q y μ := by
  obtain ⟨μ, hμQ, hμ, p, hp, hpx⟩ := hx
  have hR0 : Reach A.term (exec C μ) := hC.1.run hμ
  -- run `p` alone until it is ahead of everybody
  obtain ⟨N, hN⟩ : ∃ N, N = (Finset.univ.erase p).sup (fun j => (exec C μ j).hist.length) :=
    ⟨_, rfl⟩
  obtain ⟨γ, hγp, hγ, hγu, hγr, hγo⟩ :=
    unprot_rounds hA hR0 (p := p) (by rw [hpx]; exact hu) N
  have hRE : Reach A.term (exec (exec C μ) γ) := hR0.run hγ
  obtain ⟨E, hE⟩ : ∃ E, E = exec (exec C μ) γ := ⟨_, rfl⟩
  rw [← hE] at hRE hγu hγr hγo
  obtain ⟨x', hx'⟩ : ∃ x', E p = x' := ⟨_, rfl⟩
  rw [hx'] at hγu hγr
  obtain ⟨hx't, hx's, hx'd, hx'np⟩ := hγu
  obtain ⟨r, hr⟩ : ∃ r, x'.rounds = r := ⟨_, rfl⟩
  rw [hr] at hx't hγr
  have hrN : N ≤ r := by omega
  have h1 : step E p p = upd x' := by rw [step_self, stepState_of_settled (by rw [hx']; exact hx's),
    hx']
  have hpp : IsSched A.term E [p, p] := by
    refine ⟨by rw [Active, hx']; exact hx'd, ?_, trivial⟩
    show decided A.term (step E p p) = none
    rw [h1]; rfl
  have hRF : Reach A.term (exec E [p, p]) := hRE.run hpp
  obtain ⟨F, hF⟩ : ∃ F, F = exec E [p, p] := ⟨_, rfl⟩
  rw [← hF] at hRF
  have hFp : F p = scan (upd x') (fun j => (step E p j).hist[r]?) := by
    rw [hF]; simp only [exec_cons, exec_nil, step_self]; rw [stepState_upd h1, hr]
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, F p = s₁ := ⟨_, rfl⟩
  have hs₁r : s₁.rounds = r + 1 := by rw [← hs₁, hFp]; simp [rounds, hr]
  have hs₁o : Occ A.term s₁ := ⟨F, hRF, by rw [← hs₁, hRF.pid]⟩
  have hs₁s : s₁.Settled := by rw [← hs₁, hFp]; trivial
  have hs₁p : s₁.pid = p := by rw [← hs₁, hRF.pid]
  have hown : own r s₁ = x' := by
    have := hs₁o; rw [← hs₁, hFp] at this ⊢
    exact own_of_scan this (by rw [← hFp, hs₁]; exact hs₁r)
  have hcar : ∀ c ∈ car r s₁, c = x' := by
    intro c hc
    simp only [car, hs₁r, if_true, Set.mem_setOf_eq] at hc
    rcases hc with hc | ⟨k, hk⟩
    · rw [hc, hown]
    · by_cases hkp : k = p
      · subst hkp
        have hv := Occ.own_view hs₁o hs₁s hs₁r
        rw [hown, hs₁p] at hv
        exact Option.some_injective _ (hk.symm.trans hv)
      · exfalso
        rw [← hs₁, hFp] at hk
        simp only [view_scan] at hk
        rw [step_ne _ hkp, hγo k hkp] at hk
        have hle : (exec C μ k).hist.length ≤ N := by
          rw [hN]; exact Finset.le_sup (f := fun j => (exec C μ j).hist.length) (by simp [hkp])
        rw [List.getElem?_eq_none (by omega)] at hk
        simp at hk
  -- subdivide up to level `r + 1` and terminate `s₁` with `y`
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = subdivide^[r + 1 - A.t] A := ⟨_, rfl⟩
  have hA1t : A1.t = r + 1 := by rw [hA1, subdivide_iter_t]; omega
  have hA1term : A1.term = A.term := by rw [hA1, subdivide_iter_term]
  have hInv1 : AInv A1 := by rw [hA1]; exact hA.subdiv_iter _
  have hsafe : Safe A.term (r + 1) s₁ y := by
    have h4 := hInv1.far4 y
    rw [hA1t, hA1term] at h4
    refine safe_solo (fun z hz => by have := hA.dec_le z hz; omega) h4
      (fun b hb => by have := hInv1.far5 y b (Ne.symm hb); rwa [hA1t, hA1term] at this)
      hx'd ?_ ?_ hs₁o hs₁s hs₁r hcar
    · by_contra hns; exact hx'np (Or.inl hns)
    · rintro ⟨w, b, hb, hwb, hadj⟩; exact hx'np (Or.inr ⟨w, b, hb, hwb, by rw [hr]; exact hadj⟩)
  have hs₁d : decided A.term s₁ = none := by
    by_contra h; have := hA.dec_le _ h; omega
  have hs₀ : ¬ s₁.IsInit := Settled.not_isInit_of_rounds (by omega)
  have hst1 : s₁.rounds = A1.t := by rw [hA1t, hs₁r]
  refine ⟨{ A1 with term := setTerm A1.term s₁ y }, ?_⟩
  have hInv' : AInv { A1 with term := setTerm A1.term s₁ y } :=
    hInv1.terminate hs₁s hst1 (by rw [hA1term]; exact hs₁d)
      (by rw [hA1term]; exact hs₁o) (by rw [hA1term, hA1t]; exact hsafe)
  have hLe : Le A { A1 with term := setTerm A1.term s₁ y } := by
    have := Le.subdiv_iter A (r + 1 - A.t); rw [← hA1] at this
    exact this.trans (Le.terminate hst1 (by rw [hA1term]; exact hs₁d) hs₁s hs₀)
  -- the answer: the causal past of `s₁`
  obtain ⟨u, β, hβ, hCeq⟩ := hC.1
  obtain ⟨μ', hsub, hfin, -, hsched⟩ :=
    exists_sched_restrict (x := u) (β := β) (μ := μ ++ γ ++ [p, p]) {p}
  have hFeq : exec (initC u) (β ++ (μ ++ γ ++ [p, p])) = F := by
    rw [exec_append, ← hCeq, exec_append, exec_append, hF, hE]
  have hdec' : ∀ z, decided (setTerm A1.term s₁ y) z =
      if z = s₁ then some y else decided A.term z := by
    intro z; rw [decided_setTerm hs₁s hs₀, hA1term]
  refine ⟨μ', hInv', hLe, fun C' hC' => ?_, fun q hq => ?_, fun δ hδ => ?_⟩
  · have := hC'.mono_t (t' := A1.t) (by rw [hA1t]; omega)
    rw [← hA1term] at this
    exact RC.setTerm this hs₁s hst1 hs₀
  · have := hsub.subset hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with (h | h) | h | h
    · exact hμQ q h
    · rw [hγp q h]; exact hp
    · rw [h]; exact hp
    · rw [h]; exact hp
  · have hpast : ∀ z, InPast z s₁ → z ≠ s₁ → decided δ z = none := by
      intro z hz hne
      by_cases hzs : z.Settled
      · have h1 := hs₁o.past_active hz hne
        have h2 := Occ.past_rounds hs₁o hz hne hzs hs₁s
        rw [hδ z (Or.inl (by show z.rounds < A1.t; omega))]
        show decided (setTerm A1.term s₁ y) z = none
        rw [hdec', if_neg hne, h1]
      · exact decided_eq_none_of_not_settled hzs
    have hC0 : exec (initC u) β = C := hCeq.symm
    refine ⟨?_, p, hp, ?_⟩
    · have := hsched δ fun i hi => by
        simp at hi; subst hi; rw [hFeq, hs₁]; exact hpast
      rwa [hC0] at this
    · have := hfin p rfl
      rw [hC0, hFeq, hs₁] at this
      have hdy : decided (setTerm A1.term s₁ y) s₁ = some y := by rw [hdec']; simp
      rw [outs, this, hδ s₁ (Or.inr (by rw [hdy]; simp))]
      exact hdy


/-! ## The answer to an output query keeps the invariants -/

/-- The reaction `oq` to an output query keeps the invariants; a `some` answer is correct for every
protocol extending the new state, and a `none` answer is recorded. -/
lemma oq_spec [Fintype P] {A : AState P X} (hA : AInv A) {C : Config P X}
    (hC : RC A.term A.t C) (Q : Finset P) (y : X) :
    AInv (oq A C Q y).1 ∧ Le A (oq A C Q y).1 ∧
    (∀ C', RC A.term A.t C' → RC (oq A C Q y).1.term (oq A C Q y).1.t C') ∧
    (∀ μ, (oq A C Q y).2 = some μ → GoodSome (oq A C Q y).1 C Q y μ) ∧
    ((oq A C Q y).2 = none → (C, Q, y) ∈ (oq A C Q y).1.recs) := by
  unfold oq
  split_ifs with h
  · have hs := Classical.choose_spec (Classical.choose_spec h)
    exact ⟨hs.1, hs.2.1, hs.2.2.1, fun μ hμ => by simp at hμ; rw [← hμ]; exact hs.2.2.2,
      fun h' => by simp at h'⟩
  · refine ⟨⟨hA.one_le, hA.dec_le, hA.far4, hA.far5, fun rec hrec => ?_⟩,
      ⟨le_rfl, fun r hr => List.mem_cons_of_mem _ hr, fun _ _ => rfl⟩, fun C' hC' => hC',
      fun μ hμ => by simp at hμ, fun _ => List.mem_cons_self⟩
    simp only [List.mem_cons] at hrec
    rcases hrec with rfl | hrec
    · refine ⟨hC, fun x hx => ⟨fun hxy => h (oq_some_of_terminated hA hC hx hxy),
        fun h1 h2 h3 => ?_⟩⟩
      by_contra hp
      exact h (oq_some_of_unprot hA hC hx ⟨h1, h2, h3, hp⟩)
    · exact hA.recs rec hrec

end Podc.WhyExtensionBased
