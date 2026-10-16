import Papers.PODC2013.ByzantineVectorConsensus.Spec

/-!
# Lower bounds: Theorems 1 and 4 of Vaidya–Garg (PODC 2013)

* `approxSync_lower_bound`: even *approximate* BVC in **synchrony** needs `n ≥ (d + 1) t + 1`
  (for `n ≥ 2`, `d ≥ 1`, and an input domain containing a configuration of width `c > ε`).
* `theorem_1`: **Theorem 1** — exact BVC in synchrony needs `n ≥ max(3t + 1, (d + 1) t + 1)`
  (for `n ≥ 2`, `d ≥ 1`). The `3t + 1` part is reduced to the Fischer–Lynch–Merritt bound for
  weak consensus (CSLib, `weakValidity_not_solvesConsensusSync_of_ne`) by restricting to inputs on
  the diagonal of `ℝ^d`; the `(d + 1) t + 1` part is the direct argument below.
* `theorem_4`: **Theorem 4** — approximate BVC in the partially synchronous (hence also in the
  asynchronous) model needs `n ≥ (d + 2) t + 1`.

Instead of the paper's "`f = 1` first, then simulation of `f` processes by one", we partition the
processes directly into `d + 1` (resp. `d + 2`) groups of size `≤ t` by the residue of their index
(`card_mod_class_le`); group `l ∈ [0, d]` gets input `a + lbPoint d c l` (`0` and the scaled
standard basis vectors), group `d + 1` is the *slow* group of Theorem 4. A process of group `m`
cannot exclude that group `l ≠ m` is Byzantine but behaves correctly (synchrony: `Run.enlarge`;
partial synchrony: `Run.extend`, where in addition the slow group is correct but its messages are
delayed past the decision time), so its decision lies in the hull of the inputs of the groups
`≠ l` for every such `l`; by `eq_add_lbPoint_of_mem_convexHull` it must decide its own input.
Processes of groups `0` and `1` then decide points at distance `c > ε`.
-/

open Cslib.Byzantine.PartialSync Finset

namespace ByzantineVectorConsensus

set_option linter.unusedSectionVars false

variable {P M S : Type*} [Fintype P] [DecidableEq P] {d : ℕ}

/-! ### Combinatorial and geometric helpers -/

/-- The residue classes modulo `m` of the indices of `n ≤ m t` processes have at most `t`
elements. -/
theorem card_mod_class_le {m t : ℕ} (_hm : 0 < m) (hn : Fintype.card P ≤ m * t) (r : ℕ) :
    (univ.filter fun p : P => ((Fintype.equivFin P p : ℕ) % m = r)).card ≤ t := by
  set e := Fintype.equivFin P
  have h := card_le_card_of_injOn (s := univ.filter fun p : P => ((e p : ℕ) % m = r))
    (t := range t) (fun p => (e p : ℕ) / m) (fun p _ => by
      simp only [coe_range, Set.mem_Iio]
      have := (e p).isLt
      exact Nat.div_lt_of_lt_mul (by linarith [mul_comm m t]))
    (fun p hp q hq hpq => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      have h1 := Nat.div_add_mod (e p : ℕ) m
      have h2 := Nat.div_add_mod (e q : ℕ) m
      simp only at hpq
      rw [hp, hpq] at h1; rw [hq] at h2
      exact e.injective (Fin.ext (by omega)))
  simpa using h

/-- Validity constraints of the lower-bound configurations pin the decision to the own input. -/
theorem pin_of_validity {g : P → ℕ} {a : Vec d} {c : ℝ} {p : P} (hp : g p ≤ d) {z : Vec d}
    (h : ∀ l ≤ d, l ≠ g p →
      z ∈ convexHull ℝ {v | ∃ q, g q ≠ l ∧ g q ≤ d ∧ a + lbPoint d c (g q) = v}) :
    z = a + lbPoint d c (g p) := by
  refine eq_add_lbPoint_of_mem_convexHull hp fun l hl hlp => convexHull_mono ?_ (h l hl hlp)
  rintro _ ⟨q, hq1, hq2, rfl⟩
  exact ⟨g q, ⟨hq1, hq2⟩, rfl⟩

/-- Two decisions pinned to groups `0` and `1` violate `ε`-agreement. -/
theorem not_close_lbPoint (hd : 1 ≤ d) {a : Vec d} {c ε : ℝ} (hcε : ε < c) :
    ¬ Close ε (a + lbPoint d c 0) (a + lbPoint d c 1) := by
  intro h
  have := h ⟨0, hd⟩
  simp [lbPoint] at this
  linarith [le_abs_self c]

theorem equivFin_symm_mod {m : ℕ} (k : Fin (Fintype.card P)) (hk : k.val < m) :
    ((Fintype.equivFin P ((Fintype.equivFin P).symm k) : ℕ) % m) = k.val := by
  simp [Nat.mod_eq_of_lt hk]

/-! ### Synchronous lower bound `(d + 1) t + 1` -/

variable {t δ : ℕ} {ε : ℝ} {K : Set (Vec d)} {A : Algorithm P M S (Vec d) (Vec d)}

/-- **Approximate BVC in synchrony needs `n ≥ (d + 1) t + 1`** (the second part of Theorem 1,
which the paper proves for exact BVC; the argument only uses `ε`-agreement). Hypotheses: `n ≥ 2`,
`d ≥ 1`, and the input domain contains `a` and `a + c e_i` for all `i`, with `c > ε`. -/
theorem approxSync_lower_bound (hd : 1 ≤ d) (hn2 : 2 ≤ Fintype.card P) {a : Vec d} {c : ℝ}
    (hcε : ε < c) (hK : ∀ l ≤ d, a + lbPoint d c l ∈ K) (hA : SolvesApproxBVCSync t δ ε K A) :
    (d + 1) * t < Fintype.card P := by
  by_contra hn
  push Not at hn
  set e := Fintype.equivFin P
  set g : P → ℕ := fun p => (e p : ℕ) % (d + 1) with hg
  have hgd : ∀ p, g p ≤ d := fun p => Nat.lt_succ_iff.1 (Nat.mod_lt _ (by omega))
  set x : P → Vec d := fun p => a + lbPoint d c (g p)
  set R0 : Run P M (Vec d) := canonRun (fun p => some (x p)) 0
  have hcfg : IsInputConfig t (fun p => some (x p) : Config P (Vec d)) := by
    unfold IsInputConfig
    have : (Config.procs (fun p => some (x p) : Config P (Vec d))) = univ := by ext; simp
    rw [this, card_univ]; omega
  have hR0 : R0.Valid t δ := canonRun.valid _ _ hcfg δ
  have hR0f : R0.faulty = ∅ := by
    simp only [R0, canonRun]
    ext p; simp
  have hR0i : ∀ p, R0.inp p = x p := fun p => rfl
  have hR0K : InputsIn K R0 := fun p _ => by rw [hR0i]; exact hK _ (hgd p)
  -- every decision is pinned to the own input
  have pinned : ∀ p z, R0.Decides A p z → z = x p := by
    intro p z hz
    refine pin_of_validity (hgd p) fun l hl hlp => ?_
    set G := univ.filter fun q => g q = l
    have hGt : G.card ≤ t := card_mod_class_le (by omega) hn l
    have hF : R0.faulty ⊆ G := by rw [hR0f]; exact empty_subset _
    have hpG : p ∉ G := by simp [G, Ne.symm hlp]
    have hV := Run.enlarge_valid (A := A) hR0 hF hGt
    have hval := hA.validity _ hV (by simp [R0, canonRun]) (fun q _ => hR0K q (by simp [hR0f]))
      p (by simpa using hpG) z ((Run.enlarge_decides hF hpG).2 hz)
    refine convexHull_mono ?_ hval
    rintro _ ⟨q, hq⟩
    rw [Run.enlarge_inputConf] at hq
    by_cases hqG : q ∈ G
    · simp [hqG] at hq
    · simp only [hqG, ite_false, Option.some.injEq] at hq
      refine ⟨q, by simpa [G] using hqG, hgd q, ?_⟩
      rw [← hq, hR0i]
  set p0 := e.symm ⟨0, by omega⟩
  set p1 := e.symm ⟨1, by omega⟩
  have hg0 : g p0 = 0 := equivFin_symm_mod _ (by simp)
  have hg1 : g p1 = 1 := equivFin_symm_mod _ (by simp; omega)
  have hp0 : p0 ∉ R0.faulty := by simp [hR0f]
  have hp1 : p1 ∉ R0.faulty := by simp [hR0f]
  obtain ⟨z0, hz0⟩ := hA.termination R0 hR0 rfl hR0K p0 hp0
  obtain ⟨z1, hz1⟩ := hA.termination R0 hR0 rfl hR0K p1 hp1
  have hc := hA.agreement R0 hR0 rfl hR0K p0 hp0 p1 hp1 z0 z1 hz0 hz1
  rw [pinned p0 z0 hz0, pinned p1 z1 hz1] at hc
  simp only [x, hg0, hg1] at hc
  exact not_close_lbPoint hd hcε hc

/-! ### Theorem 1 -/

section Diagonal

variable (A)

/-- The scalar algorithm obtained from a vector algorithm by proposing the diagonal vector
`(v, …, v)` and reading off coordinate `i` of the decision. -/
def diagAlg (i : Fin d) : Algorithm P M S ℝ ℝ where
  init p v := A.init p (fun _ => v)
  step := A.step
  send := A.send
  decide p s := (A.decide p s).map (· i)

/-- The vector run with the diagonal inputs of a scalar run. -/
def diagRun (R : Run P M ℝ) : Run P M (Vec d) :=
  { faulty := R.faulty, inp := fun p _ => R.inp p, gst := R.gst, byz := R.byz, dl := R.dl }

variable {A}

theorem diag_stUpTo (i : Fin d) (R : Run P M ℝ) (τ : ℕ) :
    (diagRun R).stUpTo A τ = R.stUpTo (diagAlg A i) τ := by
  induction τ with
  | zero => funext σ p; rfl
  | succ τ ih =>
    funext σ p
    simp only [Run.stUpTo, ih]
    rfl

theorem diag_st (i : Fin d) (R : Run P M ℝ) : (diagRun R).st A = R.st (diagAlg A i) := by
  funext τ p; simp [Run.st, diag_stUpTo i]

/-- A solution of exact BVC in synchrony yields a solution of scalar consensus with weak validity
(restricting to diagonal inputs). -/
theorem weak_of_bvc (i : Fin d) (hA : SolvesConsensusSync t δ A (bvcValidity P d)) :
    SolvesConsensusSync t δ (diagAlg A i) (weakValidity P ℝ) := by
  have hvalid : ∀ R : Run P M ℝ, R.Valid t δ → (diagRun (d := d) R).Valid t δ := fun R hR =>
    ⟨hR.card_faulty, hR.dl_ge, hR.dl_le⟩
  have hdec : ∀ (R : Run P M ℝ) p w, R.Decides (diagAlg A i) p w ↔
      ∃ u, (diagRun R).Decides A p u ∧ u i = w := by
    intro R p w
    simp only [Run.Decides, diag_st i]
    constructor
    · rintro ⟨τ, hτ⟩
      simp only [diagAlg, Option.map_eq_some_iff] at hτ
      obtain ⟨u, hu, rfl⟩ := hτ
      exact ⟨u, ⟨τ, hu⟩, rfl⟩
    · rintro ⟨u, ⟨τ, hu⟩, rfl⟩
      exact ⟨τ, by simp only [diagAlg, Option.map_eq_some_iff]; exact ⟨u, hu, rfl⟩⟩
  refine ⟨fun R hR _ h0 p hp => ?_, fun R hR _ h0 p hp q hq v w hv hw => ?_,
    fun R hR _ h0 p hp w hw => ?_⟩
  · obtain ⟨u, hu⟩ := hA.termination (diagRun R) (hvalid R hR) (Run.authValid_none A _) h0 p hp
    exact ⟨u i, (hdec R p _).2 ⟨u, hu, rfl⟩⟩
  · obtain ⟨u, hu, rfl⟩ := (hdec R p v).1 hv
    obtain ⟨u', hu', rfl⟩ := (hdec R q w).1 hw
    rw [hA.agreement (diagRun R) (hvalid R hR) (Run.authValid_none A _) h0 p hp q hq u u' hu hu']
  · obtain ⟨u, hu, rfl⟩ := (hdec R p w).1 hw
    have hval := hA.validity (diagRun R) (hvalid R hR) (Run.authValid_none A _) h0 p hp u hu
    intro v hv
    have hsub : {x : Vec d | ∃ q, (diagRun (d := d) R).inputConf q = some x} ⊆ {fun _ => v} := by
      rintro _ ⟨q, hq⟩
      have := hv q
      simp only [Run.inputConf, diagRun] at this hq ⊢
      split_ifs at this with hqf
      simp only [hqf, ite_false, Option.some.injEq] at this hq
      rw [← hq, this, Set.mem_singleton_iff]
    have := convexHull_mono hsub hval
    rw [convexHull_singleton] at this
    rw [Set.mem_singleton_iff.1 this]

end Diagonal

/-- **Theorem 1** of the paper: exact BVC in a synchronous system requires
`n ≥ max(3t + 1, (d + 1) t + 1)`. Here for `n ≥ 2` processes (the paper assumes `n > 1`; for
`n = 1` the problem is trivially solvable) and dimension `d ≥ 1`. -/
theorem theorem_1 (hd : 1 ≤ d) (hn2 : 2 ≤ Fintype.card P)
    (hA : SolvesConsensusSync t δ A (bvcValidity P d)) :
    3 * t < Fintype.card P ∧ (d + 1) * t < Fintype.card P := by
  have h2 : (d + 1) * t < Fintype.card P :=
    approxSync_lower_bound (ε := 0) (K := Set.univ) (a := 0) (c := 1) hd hn2 one_pos
      (fun _ _ => Set.mem_univ _) (approx_of_exact hA le_rfl)
  refine ⟨?_, h2⟩
  by_contra h3
  push Not at h3
  rcases Nat.lt_or_ge (Fintype.card P) 3 with hlt | hge
  · -- `n = 2`: then `(d + 1) t < 2` forces `t = 0`
    have : t = 0 := by nlinarith
    omega
  · exact weakValidity_not_solvesConsensusSync_of_ne (zero_ne_one (α := ℝ)) _ hge h3
      (weak_of_bvc ⟨0, hd⟩ hA)

/-! ### Theorem 4 -/

/-- **Theorem 4** of the paper: approximate BVC in the partially synchronous model (and hence in
the asynchronous model) requires `n ≥ (d + 2) t + 1`. Hypotheses: `n ≥ 2`, `d ≥ 1`, and the input
domain contains `a` and `a + c e_i` for all `i`, with `c > ε` (e.g. `K = ℝ^d`, or a box
`[ν, U]^d` with `U - ν > ε`). -/
theorem theorem_4 (hd : 1 ≤ d) (hn2 : 2 ≤ Fintype.card P) {a : Vec d} {c : ℝ}
    (hcε : ε < c) (hK : ∀ l ≤ d, a + lbPoint d c l ∈ K) (hA : SolvesApproxBVC t δ ε K A) :
    (d + 2) * t < Fintype.card P := by
  by_contra hn
  push Not at hn
  set e := Fintype.equivFin P
  set g : P → ℕ := fun p => (e p : ℕ) % (d + 2) with hg
  have hgd : ∀ p, g p ≤ d + 1 := fun p => Nat.lt_succ_iff.1 (Nat.mod_lt _ (by omega))
  set x : P → Vec d := fun p => a + lbPoint d c (g p)
  -- `R0`: the slow group `d + 1` is faulty and silent; everybody else is correct
  set c0 : Config P (Vec d) := fun p => if g p = d + 1 then none else some (x p)
  set R0 : Run P M (Vec d) := canonRun c0 0
  have hcard : ∀ l, Fintype.card P - t ≤ (univ.filter fun q => g q ≠ l).card := by
    intro l
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset P)) (fun q => g q = l)
    have h2 : (univ.filter fun q => g q = l).card ≤ t := card_mod_class_le (by omega) hn l
    rw [card_univ] at h1
    simp only [ne_eq]
    omega
  have hcfg : IsInputConfig t c0 := by
    unfold IsInputConfig
    have : c0.procs = univ.filter fun q => g q ≠ d + 1 := by
      ext q; by_cases hq : g q = d + 1 <;> simp [c0, hq]
    rw [this]; exact hcard _
  have hR0 : R0.Valid t δ := canonRun.valid _ _ hcfg δ
  have hR0f : ∀ p, p ∉ R0.faulty ↔ g p ≠ d + 1 := by
    intro p; by_cases hp : g p = d + 1 <;> simp [R0, canonRun, c0, hp]
  have hR0i : ∀ p, g p ≠ d + 1 → R0.inp p = x p := by
    intro p hp; simp [R0, canonRun, c0, hp]
  have hR0K : InputsIn K R0 := fun p hp => by
    have hp' := (hR0f p).1 hp
    rw [hR0i p hp']; exact hK _ (by have := hgd p; omega)
  have pinned : ∀ p, g p ≠ d + 1 → ∀ z, R0.Decides A p z → z = x p := by
    intro p hp z ⟨τ, hτ⟩
    have hpd : g p ≤ d := by have := hgd p; omega
    refine pin_of_validity hpd fun l hl hlp => ?_
    -- `R'`: group `l` is Byzantine (replaying `R0`), the slow group is correct with input
    -- `x p` but its messages arrive after time `τ`
    set cl : Config P (Vec d) := fun q =>
      if g q = l then none else if g q = d + 1 then some (x p) else some (x q)
    set R' := R0.extend A cl τ
    have hcl : IsInputConfig t cl := by
      unfold IsInputConfig
      have : cl.procs = univ.filter fun q => g q ≠ l := by
        ext q
        by_cases hq : g q = l
        · simp [cl, hq]
        · by_cases hq' : g q = d + 1 <;> simp [cl, hq, hq']
      rw [this]; exact hcard _
    have hV : R'.Valid t δ := Run.extend_valid hR0 hcl τ
    have hK' : InputsIn K R' := by
      intro q hq
      have hq' : cl q ≠ none := by simpa [R', Run.extend] using hq
      simp only [R', Run.extend]
      by_cases h1 : g q = l
      · simp [cl, h1] at hq'
      · by_cases h2 : g q = d + 1
        · simp only [cl, h2, show ¬ (d + 1 = l) from h2 ▸ h1, ite_false, ite_true,
            Option.getD_some]
          exact hK _ hpd
        · simp only [cl, h1, h2, ite_false, Option.getD_some]
          exact hK _ (by have := hgd q; omega)
    have hsim : ∀ q ∉ R0.faulty, cl q ≠ none → cl q = some (R0.inp q) := by
      intro q hq hq'
      have hq2 := (hR0f q).1 hq
      have hq1 : g q ≠ l := by intro h; simp [cl, h] at hq'
      simp [cl, hq1, hq2, hR0i q hq2]
    have hpl : cl p ≠ none := by simp [cl, Ne.symm hlp, hp]
    have hst := Run.extend_st (A := A) (canonRun.canonical _ _) hsim τ τ le_rfl p
      ((hR0f p).2 hp) hpl
    have hpR' : p ∉ R'.faulty := by
      simp only [R', Run.extend, mem_compl, Config.mem_procs_iff_ne_none]
      exact not_not.2 hpl
    have hdec : R'.Decides A p z := ⟨τ, by rw [hst]; exact hτ⟩
    have hval := hA.validity R' hV hK' p hpR' z hdec
    rw [Run.extend_inputConf] at hval
    refine convexHull_mono ?_ hval
    rintro _ ⟨q, hq⟩
    by_cases h1 : g q = l
    · simp [cl, h1] at hq
    · by_cases h2 : g q = d + 1
      · simp only [cl, h2, show ¬ (d + 1 = l) from h2 ▸ h1, ite_false, ite_true,
          Option.some.injEq] at hq
        exact ⟨p, Ne.symm hlp, hpd, hq⟩
      · simp only [cl, h1, h2, ite_false, Option.some.injEq] at hq
        exact ⟨q, h1, by have := hgd q; omega, hq⟩
  set p0 := e.symm ⟨0, by omega⟩
  set p1 := e.symm ⟨1, by omega⟩
  have hg0 : g p0 = 0 := equivFin_symm_mod _ (by simp)
  have hg1 : g p1 = 1 := equivFin_symm_mod _ (by simp)
  have hp0 : p0 ∉ R0.faulty := (hR0f p0).2 (by omega)
  have hp1 : p1 ∉ R0.faulty := (hR0f p1).2 (by omega)
  obtain ⟨z0, hz0⟩ := hA.termination R0 hR0 hR0K p0 hp0
  obtain ⟨z1, hz1⟩ := hA.termination R0 hR0 hR0K p1 hp1
  have hc := hA.agreement R0 hR0 hR0K p0 hp0 p1 hp1 z0 z1 hz0 hz1
  rw [pinned p0 (by omega) z0 hz0, pinned p1 (by omega) z1 hz1] at hc
  simp only [x, hg0, hg1] at hc
  exact not_close_lbPoint hd hcε hc

end ByzantineVectorConsensus
