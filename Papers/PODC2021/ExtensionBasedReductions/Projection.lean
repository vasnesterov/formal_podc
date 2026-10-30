import Papers.PODC2021.ExtensionBasedReductions.Composite

/-!
# Projecting configurations of `h ∘ A ∘ A₁` to configurations of `A`

For a reachable configuration `C` of the composition, `trunc t C` is its `A₁`-part and `toA C` its
`A`-part, where the processes that have not yet finished `A₁` get as input their output in a fixed
completion of the `A₁`-part (`ucan`). This is the configuration `D₀ γ'` of the paper (Section 7),
with a canonical choice of `D₀` (the paper keeps `D₀` arbitrary on these processes; the canonical
choice is what makes "if `D₀ γ'` satisfies `S`, then `C` satisfies `T`" true for configurations in
which not all processes have finished `A₁`).
-/

namespace Podc.ExtensionBasedReductions

open Cslib.NIS

open St

variable {P XT M ZS ZT : Type} [DecidableEq P] [Inhabited M]

section Gen
variable {X Y : Type} {δ : Protocol P X Y}

lemma reinit_inputs_reinit (B : Config P X) (u : P → X) :
    reinit B (inputs (reinit B u)) = reinit B u := by
  funext j; unfold reinit inputs; split_ifs with h <;> simp [h, St.input]

lemma reinit_inputs_self {B : Config P X} (hB : Reach δ B) : reinit B (inputs B) = B := by
  funext j; unfold reinit; split_ifs with h
  · rw [hB.isInit_eq h]; rfl
  · rfl

end Gen

variable {δ1 : Protocol P XT M} {t : ℕ}

lemma truncS_input (s : St P XT) : (truncS t s).input = s.input := by
  match s with
  | init i x => rfl
  | upd s => simp only [truncS]; split_ifs
             · rfl
             · rw [truncS_input s]; rfl
  | scan s v => simp only [truncS]; split_ifs
                · rfl
                · rw [truncS_input s]; rfl

lemma input_of_good {C1 : Config P XT} :
    ∀ (s : St P M), Good δ1 C1 s → decided δ1 (C1 s.pid) = some s.input
  | init k y, hg => hg
  | upd s, hg => input_of_good s hg
  | scan s v, hg => input_of_good s hg.1

lemma Inv.input_fin {C1 : Config P XT} {CA : Config P M} {u : P → M} (hI : Inv δ1 C1 CA u)
    {j : P} (hj : (decided δ1 (C1 j)).isSome) : (CA j).input = u j := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hj
  obtain ⟨h1, h2, h3⟩ := hI.fin j y hy
  have := input_of_good _ h2
  rw [h3, hy] at this; cases this; exact h1

lemma Inv.init_fin {C1 : Config P XT} {CA : Config P M} {u : P → M} (hI : Inv δ1 C1 CA u)
    {j : P} (hj : (decided δ1 (C1 j)).isSome) (hi : (CA j).IsInit) : CA j = St.init j (u j) := by
  obtain ⟨k, y, hk⟩ := (St.isInit_iff _).1 hi
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hj
  have hp := (hI.fin j y' hy').2.2
  have hin := hI.input_fin hj
  rw [hk] at hp hin ⊢; simp only [St.pid] at hp; simp only [St.input] at hin; rw [hp, hin]

lemma inputs_of_inv {C1 : Config P XT} {CA : Config P M} {u : P → M} (hI : Inv δ1 C1 CA u) :
    inputs CA = u := by
  funext j
  by_cases hj : (decided δ1 (C1 j)).isSome
  · exact hI.input_fin hj
  · rw [inputs, hI.unfin j (by simpa using hj)]; rfl

section Defs
variable (δ1 t)

open Classical in
/-- A fixed final extension of an `A₁`-configuration. -/
noncomputable def comp1 (C1 : Config P XT) : Config P XT :=
  if hc : ∃ μ, IsSched δ1 C1 μ ∧ Final δ1 (exec C1 μ) then exec C1 hc.choose else C1

/-- Canonical inputs for `A`: the outputs in the fixed completion of the `A₁`-part. -/
noncomputable def ucan (C : Config P XT) : P → M :=
  fun j => (decided δ1 (comp1 δ1 (trunc t C) j)).getD default

/-- The `A`-part of a configuration of the composition (with canonical inputs). -/
noncomputable def toA (C : Config P XT) : Config P M := toAC δ1 t C (ucan δ1 t C)

end Defs

section Proj
variable (hIS : IsIS δ1 t) (ht : 0 < t) (hw : WaitFree δ1) {δA : Protocol P M ZS}
  {post : P → ZS → ZT}

include hw in
lemma ucan_fin {C : Config P XT} (hC1 : Reach δ1 (trunc t C)) {j : P} {y : M}
    (hj : decided δ1 (trunc t C j) = some y) : ucan δ1 t C j = y := by
  obtain ⟨μ, hμ, hfin⟩ := hw.exists_final hC1
  have hc : ∃ μ, IsSched δ1 (trunc t C) μ ∧ Final δ1 (exec (trunc t C) μ) := ⟨μ, hμ, hfin⟩
  unfold ucan comp1
  rw [dif_pos hc, exec_of_terminated hc.choose_spec.1 (by rw [hj]; simp), hj]; rfl

include hIS ht hw

/-- Every reachable configuration of the composition is `Ycfg (trunc C) (toA C)`. -/
lemma canonY {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) :
    Inv δ1 (trunc t C) (toA δ1 t C) (ucan δ1 t C) ∧ C = Ycfg δ1 (trunc t C) (toA δ1 t C) := by
  obtain ⟨C1, CA, u, hI, rfl⟩ := reach_decomp hIS ht hC
  have htr := trunc_Ycfg hIS ht hI
  exact canonical hIS ht hI _ (fun j y hj => ucan_fin hw (by rw [htr]; exact hI.reach)
    (by rw [htr]; exact hj))

lemma reach_trunc {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) : Reach δ1 (trunc t C) :=
  (canonY hIS ht hw hC).1.reach

lemma outs_toA {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) (j : P) :
    outs (compP δ1 t δA post) C j = (outs δA (toA δ1 t C) j).map (post j) := by
  obtain ⟨hI, hE⟩ := canonY hIS ht hw hC
  conv_lhs => rw [hE]
  exact outs_Ycfg hIS ht hI j

lemma inputs_toA {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) :
    inputs (toA δ1 t C) = ucan δ1 t C := inputs_of_inv (canonY hIS ht hw hC).1

/-- A step of `A` in the composition. -/
lemma toA_stepA {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) {q : P}
    (hq : (decided δ1 (trunc t C q)).isSome) :
    toA δ1 t (step C q) = step (toA δ1 t C) q ∧
      (Active (compP δ1 t δA post) C q ↔ Active δA (toA δ1 t C) q) ∧
      trunc t (step C q) = trunc t C := by
  obtain ⟨hI, hE⟩ := canonY hIS ht hw hC
  obtain ⟨h1, h2⟩ := stepY_A hIS ht hI hq
  have hS : step C q = Ycfg δ1 (trunc t C) (step (toA δ1 t C) q) := by
    conv_lhs => rw [hE]
    exact h1
  have htr : trunc t (step C q) = trunc t C := by rw [hS, trunc_Ycfg hIS ht h2]
  refine ⟨funext fun j => ?_, ?_, htr⟩
  · have hu : ucan δ1 t (step C q) = ucan δ1 t C := by unfold ucan; rw [htr]
    show toAC δ1 t (step C q) (ucan δ1 t (step C q)) j = step (toA δ1 t C) q j
    rw [hu]
    by_cases hj : (decided δ1 (trunc t C j)).isSome
    · rw [hS, toAC_Ycfg hIS ht h2 hj]
    · rw [hS, toAC_Ycfg_unfin hIS ht h2 hj]
      have hjq : j ≠ q := by rintro rfl; exact hj hq
      rw [step_ne _ hjq, hI.unfin j (by simpa using hj)]
  · conv_lhs => rw [hE]
    exact active_Ycfg_iff_of_fin hIS ht hI hq

/-- Steps of `A₁` in the composition. -/
lemma toA_execA1 {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) {μ : List P}
    (hμ : IsSched δ1 (trunc t C) μ) :
    IsSched (compP δ1 t δA post) C μ ∧ trunc t (exec C μ) = exec (trunc t C) μ ∧
      toA δ1 t (exec C μ) = reinit (toA δ1 t C) (ucan δ1 t (exec C μ)) := by
  obtain ⟨hI, hE⟩ := canonY hIS ht hw hC
  set C1 := trunc t C
  set CA := toA δ1 t C
  set u := ucan δ1 t C
  let u'' : P → M := fun j => (decided δ1 (exec C1 μ j)).getD (u j)
  have hag : ∀ j, (decided δ1 (C1 j)).isSome → u'' j = u j := fun j hj => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hj
    simp only [u'']
    rw [exec_of_terminated hμ (by rw [hy]; simp), hy, (hI.fin j y hy).1]; rfl
  obtain ⟨hI', hY', hfin'⟩ := inv_reinit hIS hI hag
  obtain ⟨h1, h2, h3⟩ := execY_A1 (δA := δA) (h := post) hIS ht μ hI' hμ
    (fun j y hy => by simp [u'', hy])
  rw [hY'] at h1 h2
  have hEx : exec C μ = Ycfg δ1 (exec C1 μ) (reinit CA u'') := by
    conv_lhs => rw [hE]
    exact h2
  have htr : trunc t (exec C μ) = exec C1 μ := by rw [hEx, trunc_Ycfg hIS ht h3]
  refine ⟨by rw [hE]; exact h1, htr, funext fun j => ?_⟩
  unfold toA
  by_cases hj : (decided δ1 (exec C1 μ j)).isSome
  · rw [hEx, toAC_Ycfg hIS ht h3 hj, ← hEx]
    unfold reinit; split_ifs with hi
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hj
      have := ucan_fin hw (C := exec C μ) (by rw [htr]; exact h3.reach) (by rw [htr]; exact hy)
      rw [this]; simp [u'', hy]
    · rfl
  · rw [hEx, toAC_Ycfg_unfin hIS ht h3 hj, ← hEx]
    have hj1 : decided δ1 (C1 j) = none := by
      by_contra hne
      exact hj (by rw [exec_of_terminated hμ hne]; exact Option.isSome_iff_ne_none.2 hne)
    rw [reinit_of_isInit (by rw [hI.unfin j hj1]; trivial)]

lemma truncS_isInit_iff (s : St P XT) : (truncS t s).IsInit ↔ s.IsInit := by
  match s with
  | init i x => simp [truncS]
  | upd s =>
    simp only [truncS]; split_ifs with h
    · rfl
    · simp only [St.not_isInit_upd, iff_false]
      intro hi
      have hd : s.depth = 0 := (St.isInit_iff_depth _).1 ((truncS_isInit_iff s).1 hi)
      simp [St.depth] at h; omega
  | scan s v =>
    simp only [truncS]; split_ifs with h
    · rfl
    · simp only [St.not_isInit_scan, iff_false]
      intro hi
      have hd : s.depth = 0 := (St.isInit_iff_depth _).1 ((truncS_isInit_iff s).1 hi)
      simp [St.depth] at h; omega

/-- Changing the inputs of processes that took no step. -/
lemma toA_reinit {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) (x : P → XT) :
    toA δ1 t (reinit C x) = reinit (toA δ1 t C) (ucan δ1 t (reinit C x)) := by
  have hC' := reach_reinit hC x
  obtain ⟨hI', hE'⟩ := canonY (δA := δA) (post := post) hIS ht hw hC'
  funext j
  by_cases hi : (C j).IsInit
  · have h1 : reinit C x j = init j (x j) := reinit_of_isInit hi x
    have h2 : decided δ1 (trunc t (reinit C x) j) = none := by simp [trunc, h1, truncS]
    have h3 : decided δ1 (trunc t C j) = none := by
      obtain ⟨i, y, hy⟩ := (St.isInit_iff _).1 hi; simp [trunc, hy, truncS]
    have e1 : toA δ1 t (reinit C x) j = init j (ucan δ1 t (reinit C x) j) := by
      unfold toA toAC
      rw [if_neg (by rw [show truncS t (reinit C x j) = trunc t (reinit C x) j from rfl, h2]; simp)]
    have e2 : toA δ1 t C j = init j (ucan δ1 t C j) := by
      unfold toA toAC
      rw [if_neg (by rw [show truncS t (C j) = trunc t C j from rfl, h3]; simp)]
    rw [e1, reinit_of_isInit (by rw [e2]; trivial)]
  · have h1 : reinit C x j = C j := reinit_of_not_isInit hi x
    have htr : trunc t (reinit C x) j = trunc t C j := by simp [trunc, h1]
    have htr' : truncS t (reinit C x j) = trunc t C j := htr
    by_cases hf : (decided δ1 (trunc t C j)).isSome
    · have e1 : toA δ1 t (reinit C x) j = toAS δ1 t (C j) := by
        unfold toA toAC
        rw [htr', if_pos hf, h1]
      have e2 : toA δ1 t C j = toAS δ1 t (C j) := by
        unfold toA toAC; rw [show truncS t (C j) = trunc t C j from rfl, if_pos hf]
      rw [e1]; unfold reinit; rw [e2]; split_ifs with hi2
      · have := hI'.init_fin (j := j) (by rw [htr]; exact hf) (by rw [e1]; exact hi2)
        rw [e1] at this; exact this
      · rfl
    · have e1 : toA δ1 t (reinit C x) j = init j (ucan δ1 t (reinit C x) j) := by
        unfold toA toAC
        rw [htr', if_neg hf]
      have e2 : toA δ1 t C j = init j (ucan δ1 t C j) := by
        unfold toA toAC; rw [show truncS t (C j) = trunc t C j from rfl, if_neg hf]
      rw [e1, reinit_of_isInit (by rw [e2]; trivial)]

lemma measure_split [Fintype P] {C : Config P XT} (hC : Reach (compP δ1 t δA post) C) :
    totalDepth C = ∑ j, (trunc t C j).depth + totalDepth (toA δ1 t C) ∧
      ∀ j, (trunc t C j).depth ≤ 2 * t := by
  obtain ⟨hI, hE⟩ := canonY hIS ht hw hC
  have hd := fun j => depth_Ycfg hIS ht hI j
  refine ⟨?_, fun j => (hd j).2⟩
  unfold totalDepth
  rw [← Finset.sum_add_distrib]
  congr 1; funext j
  rw [← (hd j).1]; conv_lhs => rw [hE]

lemma ucan_mem {R1 : Task P XT M} (hR1 : Solves δ1 R1) {C : Config P XT}
    (hC : Reach (compP δ1 t δA post) C) (hx : inputs C ∈ R1.inputs) :
    ucan δ1 t C ∈ R1.spec (inputs C) := by
  have hC1 := reach_trunc (δA := δA) (post := post) hIS ht hw hC
  obtain ⟨x0, α, hα, hEq⟩ := hC1
  have hin : inputs C = x0 := by
    funext j
    have := congrFun (congrArg inputs hEq) j
    simp only [inputs, trunc, truncS_input] at this
    rw [inputs, this, input_exec]; rfl
  obtain ⟨μ, hμ, hfin⟩ := hw.exists_final (C := trunc t C) ⟨x0, α, hα, hEq⟩
  have hc : ∃ μ, IsSched δ1 (trunc t C) μ ∧ Final δ1 (exec (trunc t C) μ) := ⟨μ, hμ, hfin⟩
  have key : ∀ j, ucan δ1 t C j = (decided δ1 (exec (trunc t C) hc.choose j)).getD default :=
    fun j => by unfold ucan comp1; rw [dif_pos hc]
  obtain ⟨hs1, hs2⟩ := hc.choose_spec
  generalize hc.choose = μ0 at key hs1 hs2
  rw [hEq, ← exec_append] at key hs2
  rw [hEq] at hs1
  rw [hin] at hx ⊢
  obtain ⟨y, hy, hout⟩ := hR1.2 x0 hx _ ((isSched_append _ _ _).2 ⟨hα, hs1⟩) hs2
  convert hy using 1
  funext j
  rw [key j]
  have := hout j
  unfold outs at this
  rw [this]; rfl

end Proj

end Podc.ExtensionBasedReductions
