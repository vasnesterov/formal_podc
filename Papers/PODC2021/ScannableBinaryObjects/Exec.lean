import Papers.PODC2021.ScannableBinaryObjects.Basic
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Foundations.Data.Nat.Descent

/-!
# Scannable binary objects: building executions

* `flipOp`, `opsTo` — the updates by which `p₀` changes the value from `u` to `w`, component by
  component in ascending order (non-monotonicity provides the flipping invocations);
* `goTo_exec` — the corresponding `p₀`-only execution (paper: `λ`, `λ_j`, `κ`), with the values of
  the object along the way: the top live component `top` is changed last;
* the processes of a list complete their pending operations (paper: `τ'`, `τ''`) by the
  library's `Impl.exists_finish`;
* `solo_scan` — a solo scan from a `p₀`-idle configuration returns the current value.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

/-! ### Flipping updates -/

section Flip

variable (hnm : ∀ c, (O c).NonMonotonic)

/-- An invocation of component `c` that changes its value from `b` to `!b`. -/
noncomputable def flipOp (c : Fin k) (b : Bool) : (O c).Op :=
  if b then Classical.choose (hnm c).2 else Classical.choose (hnm c).1

lemma flipOp_spec (c : Fin k) (b : Bool) : ((O c).δ b (flipOp hnm c b)).1 = !b := by
  cases b
  · simpa [flipOp] using Classical.choose_spec (hnm c).1
  · simpa [flipOp] using Classical.choose_spec (hnm c).2

/-- Updates turning the components `cs` from `u` to `w` (only differing components). -/
noncomputable def opsTo (u w : Fin k → Bool) (cs : List (Fin k)) : List (ScanOp O) :=
  cs.filterMap (fun c => if u c = w c then none else some (.update c (flipOp hnm c (u c))))

lemma mem_opsTo {u w : Fin k → Bool} {cs : List (Fin k)} {o : ScanOp O}
    (h : o ∈ opsTo hnm u w cs) : ∃ c ∈ cs, ∃ o', o = .update c o' := by
  simp only [opsTo, List.mem_filterMap] at h
  obtain ⟨c, hc, he⟩ := h
  split_ifs at he
  cases he; exact ⟨c, hc, _, rfl⟩

lemma runOps_opsTo (u w : Fin k → Bool) (cs : List (Fin k)) (hcs : cs.Nodup)
    (v : Fin k → Bool) (hv : ∀ c ∈ cs, v c = u c) :
    (scannable O).runOps v (opsTo hnm u w cs) = fun c => if c ∈ cs then w c else v c := by
  induction cs generalizing v with
  | nil => funext c; simp [opsTo]; rfl
  | cons c cs ih =>
    have hc : c ∉ cs := (List.nodup_cons.1 hcs).1
    by_cases huw : u c = w c
    · have : opsTo hnm u w (c :: cs) = opsTo hnm u w cs := by simp [opsTo, huw]
      rw [this, ih (List.nodup_cons.1 hcs).2 v (fun c' h' => hv c' (by simp [h']))]
      funext c'
      by_cases h1 : c' = c
      · subst h1; simp [hc, hv c' (by simp), huw]
      · simp [h1]
    · have : opsTo hnm u w (c :: cs) = .update c (flipOp hnm c (u c)) :: opsTo hnm u w cs := by
        simp [opsTo, huw]
      rw [this, ObjSpec.runOps_cons]
      have hvc : v c = u c := hv c (by simp)
      have hδ : ((O c).δ (v c) (flipOp hnm c (u c))).1 = w c := by
        rw [hvc, flipOp_spec]; revert huw; cases u c <;> cases w c <;> simp
      simp only [scannable, hδ]
      rw [ih (List.nodup_cons.1 hcs).2]
      · funext c'
        by_cases h1 : c' = c
        · subst h1; simp [hc]
        · simp [h1, Function.update_of_ne h1]
      · intro c' h'
        have hne : c' ≠ c := fun e => hc (e ▸ h')
        rw [Function.update_of_ne hne]; exact hv c' (by simp [h'])

end Flip

/-- Running operations that do not update component `c` leaves `c` unchanged. -/
lemma runOps_apply_of_noTouch (os : List (ScanOp O)) (c : Fin k)
    (h : ∀ o ∈ os, ∀ i o', o = .update i o' → i ≠ c) (v : Fin k → Bool) :
    (scannable O).runOps v os c = v c := by
  induction os generalizing v with
  | nil => rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons, ih (fun o' h' => h o' (by simp [h']))]
    cases o with
    | scan => rfl
    | update i o' =>
      have := h _ (by simp) i o' rfl
      simp [scannable, Function.update_of_ne (Ne.symm this)]

/-! ### Going to a target value -/

section GoTo

variable (hnm : ∀ c, (O c).NonMonotonic)

/-- Components below the top live component `k' - 1`, ascending. -/
def lowComps (k' : ℕ) : List (Fin k) := (List.finRange k).filter (fun c => c.val + 1 < k')

lemma lowComps_nodup (k' : ℕ) : (lowComps (k := k) k').Nodup :=
  (List.nodup_finRange k).filter _

lemma mem_lowComps {k' : ℕ} {c : Fin k} : c ∈ lowComps k' ↔ c.val + 1 < k' := by
  simp [lowComps]

/-- The updates of `p₀` changing the value from `u` to `w`: first the components below `top`,
then `top`. -/
noncomputable def goOps (k' : ℕ) (top : Fin k) (u w : Fin k → Bool) : List (ScanOp O) :=
  opsTo hnm u w (lowComps k') ++ opsTo hnm u w [top]

variable {k' : ℕ} {top : Fin k} (htop : top.val + 1 = k')

include htop

lemma goOps_final {u w : Fin k → Bool} (hw : ∀ c : Fin k, k' ≤ c.val → u c = w c) :
    (scannable O).runOps u (goOps hnm k' top u w) = w := by
  have htl : top ∉ lowComps k' := by rw [mem_lowComps]; omega
  rw [goOps, ObjSpec.runOps_append, runOps_opsTo hnm u w _ (lowComps_nodup k') u (fun _ _ => rfl),
    runOps_opsTo hnm u w [top] (by simp) _ (by simp [htl])]
  funext c
  by_cases h1 : c = top
  · subst h1; simp
  · by_cases h2 : c ∈ lowComps k'
    · simp [h1, h2]
    · simp only [List.mem_singleton, h1, ↓reduceIte, h2]
      rw [mem_lowComps] at h2
      have : c.val ≠ top.val := fun e => h1 (Fin.ext e)
      exact hw c (by omega)

lemma goOps_mem {u w : Fin k → Bool} {o : ScanOp O} (h : o ∈ goOps hnm k' top u w) :
    ∃ c : Fin k, c.val < k' ∧ ∃ o', o = .update c o' := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨c, hc, o', rfl⟩ := mem_opsTo hnm h
    exact ⟨c, by rw [mem_lowComps] at hc; omega, o', rfl⟩
  · obtain ⟨c, hc, o', rfl⟩ := mem_opsTo hnm h
    simp only [List.mem_singleton] at hc; subst hc
    exact ⟨_, by omega, o', rfl⟩

lemma goOps_top {u w : Fin k → Bool} {t : ℕ} (ht : t < (goOps hnm k' top u w).length) :
    (scannable O).runOps u ((goOps hnm k' top u w).take t) top = u top := by
  have hlen : (opsTo hnm u w [top] : List (ScanOp O)).length ≤ 1 := by
    simp only [opsTo]
    exact (List.length_filterMap_le _ _).trans (by simp)
  have ht' : t ≤ (opsTo hnm u w (lowComps k')).length := by
    simp only [goOps, List.length_append] at ht; omega
  rw [goOps, List.take_append_of_le_length ht']
  apply runOps_apply_of_noTouch
  intro o ho i o' he
  obtain ⟨c, hc, o'', rfl⟩ := mem_opsTo hnm (List.mem_of_mem_take ho)
  simp only [ScanOp.update.injEq] at he
  obtain ⟨rfl, -⟩ := he
  rw [mem_lowComps] at hc
  intro e; subst e; omega

end GoTo

/-! ### Executions -/

section Exec

variable {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
  {I : Impl (scannable O) B P L} {p₀ : P}

variable (hnm : ∀ c, (O c).NonMonotonic) (hof : I.ObstructionFree)
  (hall : ∀ p o, SingleUpdater p₀ p o → I.allowed p o)

include hnm hof hall in
/-- **The execution `λ`.** From a configuration where `p₀` is idle, `p₀` alone changes the value
of the object from the current value `u` to `w` (which agrees with `u` on the components
`≥ k'`), updating the differing components in ascending order; the top live component
`top = k' - 1` changes last. -/
theorem goTo_exec {k' : ℕ} {top : Fin k} (htop : top.val + 1 = k')
    {ε : List (Label P (scannable O))} {X : Config (scannable O) B P L}
    (hX : I.run ε = some X) (hp₀ : X.pend p₀ = none) (w : Fin k → Bool)
    (hw : ∀ c : Fin k, k' ≤ c.val → curVal p₀ ε c = w c) :
    ∃ lam Y, I.runFrom X lam = some Y ∧ Y.pend p₀ = none ∧ (∀ ℓ ∈ lam, ℓ.proc = p₀) ∧
      Lim p₀ {p₀} k' lam ∧ curVal p₀ (ε ++ lam) = w ∧
      ∀ t, t < (opsOf lam p₀).length →
        valAt p₀ (ε ++ lam) ((opsOf ε p₀).length + t) top = curVal p₀ ε top := by
  set os := goOps hnm k' top (curVal p₀ ε) w with hos
  have hallow : ∀ o ∈ os, I.allowed p₀ o := by
    intro o ho
    obtain ⟨c, -, o', rfl⟩ := goOps_mem hnm htop ho
    exact hall _ _ rfl
  obtain ⟨Y, h1, h2, h3, h4, -⟩ := I.soloOps_spec hof p₀ os hallow hX hp₀
  refine ⟨_, Y, h1, h2, h3, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    refine ⟨by simp [h3 ℓ hℓ], ?_⟩
    cases ℓ with
    | inv p o =>
      have hp : p = p₀ := h3 _ hℓ
      subst hp
      have ho : o ∈ os := by rw [← h4]; exact mem_opsOf_of_inv_mem hℓ
      obtain ⟨c, hc, o', rfl⟩ := goOps_mem hnm htop ho
      exact ⟨rfl, fun i o'' he => by simp only [ScanOp.update.injEq] at he; obtain ⟨rfl, -⟩ := he; exact hc⟩
    | _ => trivial
  · have := valAt_append_add (p₀ := p₀) ε (I.soloOps p₀ X os) (opsOf (I.soloOps p₀ X os) p₀).length
    rw [List.take_length, h4, goOps_final hnm htop hw] at this
    rw [← this]; simp [curVal, h4]
  · intro t ht
    rw [valAt_append_add, h4]
    rw [h4] at ht
    exact goOps_top hnm htop ht

variable (hlin : I.Linearizable)

include hof hall hlin in
/-- **A solo scan** by `s ≠ p₀` from a configuration where `p₀` and `s` are idle returns the
current value. -/
theorem solo_scan {ε : List (Label P (scannable O))} {Y : Config (scannable O) B P L}
    (hY : I.run ε = some Y) (hsu : SUExec p₀ ε) (hp₀ : Y.pend p₀ = none) {s : P} (hs : s ≠ p₀)
    (hsi : Y.pend s = none) :
    ∃ Z, I.runFrom Y (I.soloOp s .scan Y) = some Z ∧ Z.pend s = none ∧
      (∀ ℓ ∈ I.soloOp s .scan Y, ℓ.proc = s) ∧ opsOf (I.soloOp s .scan Y) s = [.scan] ∧
      respsOf (I.soloOp s .scan Y) s = [.view (curVal p₀ ε)] := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := I.soloOp_spec hof s .scan (hall _ _ hs) hY hsi
  refine ⟨Z, h1, h2, h3, h4, ?_⟩
  set γ := I.soloOp s .scan Y
  obtain ⟨r, hr⟩ : ∃ r, respsOf γ s = [r] := List.length_eq_one_iff.1 h5
  rw [hr]
  have hv : I.Valid (ε ++ γ) := ⟨Z, (I.run_append_of_eq hY _).trans h1⟩
  have hsu' : SUExec p₀ (ε ++ γ) := by
    rw [suExec_append]; refine ⟨hsu, fun p o hm => ?_⟩
    have hp : p = s := h3 _ hm
    subst hp
    have : o ∈ opsOf γ p := mem_opsOf_of_inv_mem hm
    rw [h4] at this; simp only [List.mem_singleton] at this; subst this; exact hs
  have hcnt := (Impl.run_idle_counts hY hsi).symm
  have hrespOf : respOf (ε ++ γ) (s, (opsOf ε s).length) = some r := by
    simp [respOf, respsOf_append, hr, ← hcnt]
  obtain ⟨i, hi1, hi2, hri⟩ := scan_resp hlin hv hsu' hs (m := (opsOf ε s).length)
    (by simp [Invoked]) hrespOf
  have hγ0 : opsOf γ p₀ = [] := opsOf_eq_nil_of_proc_ne (fun ℓ hℓ he => hs (he ▸ (h3 ℓ hℓ).symm))
  rw [(Impl.run_idle_counts hY hp₀).symm] at hi1
  rw [opsOf_append, hγ0, List.append_nil] at hi2
  have hi : i = (opsOf ε p₀).length := by omega
  rw [hri, hi, valAt_append_of_le le_rfl]
  rfl

end Exec

/-! ### Values along restricted executions -/

section LimVal

variable {p₀ : P}

/-- Along a restricted execution that updates only components `< k''`, the components `≥ k''`
keep their values. -/
lemma valAt_lim {A : Finset P} {k'' : ℕ} {ε β : List (Label P (scannable O))}
    (hβ : Lim p₀ A k'' β) {c : Fin k} (hc : k'' ≤ c.val) {t : ℕ} :
    valAt p₀ (ε ++ β) ((opsOf ε p₀).length + t) c = curVal p₀ ε c := by
  rw [valAt_append_add]
  apply runOps_apply_of_noTouch
  intro o ho i o' he
  have hm := inv_mem_of_mem_opsOf (List.mem_of_mem_take ho)
  have := ((hβ _ hm).2).2 i o' he
  intro e; subst e; omega

lemma curVal_lim {A : Finset P} {k'' : ℕ} {ε β : List (Label P (scannable O))}
    (hβ : Lim p₀ A k'' β) {c : Fin k} (hc : k'' ≤ c.val) :
    curVal p₀ (ε ++ β) c = curVal p₀ ε c := by
  have := valAt_lim (ε := ε) hβ hc (t := (opsOf β p₀).length)
  simpa [curVal] using this

/-- A restricted execution that never updates component `top`, which is `0`, is `V`-absent for
every set `V` of vectors with `1` at `top`. -/
lemma absent_of_top {A : Finset P} {k'' : ℕ} {ε β : List (Label P (scannable O))}
    (hβ : Lim p₀ A k'' β) {top : Fin k} (htop : k'' ≤ top.val) (h0 : curVal p₀ ε top = false)
    {V : Set (Fin k → Bool)} (hV : ∀ v ∈ V, v top = true) : Absent p₀ V ε β := by
  intro i h1 h2 hm
  obtain ⟨t, rfl⟩ : ∃ t, i = (opsOf ε p₀).length + t := ⟨i - (opsOf ε p₀).length, by omega⟩
  have := hV _ hm
  rw [valAt_lim hβ htop, h0] at this
  exact Bool.false_ne_true this

end LimVal

/-! ### Replaying a solo execution with fix-ups -/

-- CSLib candidate: this section is object-generic (any `A`, `B`).

section Replay

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P : Type} [DecidableEq P]
  {L : Type} {I : Impl A B P L}

/-- **Replay with fix-ups** (the construction of `γ` in the proof of Lemma 5). Let `δ` be an
execution of process `s` from `Y`, and let `X` be a configuration in which `s` has the same
state as in `Y`. We replay the steps of `δ` from `X`; whenever `s` is about to access a base
object `b` whose value differs from its value in the corresponding configuration of `δ`, the
hypothesis `hfix` provides an execution of other processes after which `b` has the right value.
The result is an execution `γ` from `X`, satisfying the invariant `Good`, in which `s` performs
exactly the steps of `δ`. -/
theorem replay (s : P) (Good : List (Label P A) → Prop) {X Y : Config A B P L}
    (hloc : X.loc s = Y.loc s) (hpend : X.pend s = Y.pend s) (hgood : Good [])
    (δ : List (Label P A)) (hδ : ∀ ℓ ∈ δ, ℓ.proc = s)
    (hext : ∀ γ ℓ, ℓ ∈ δ → Good γ → Good (γ ++ [ℓ]))
    (hfix : ∀ γ G δ₀ H b, Good γ → I.runFrom X γ = some G → δ₀ <+: δ → I.runFrom Y δ₀ = some H →
      G.mem b ≠ H.mem b →
      ∃ β' G', (∀ ℓ ∈ β', ℓ.proc ≠ s) ∧ Good (γ ++ β') ∧ I.runFrom G β' = some G' ∧
        G'.mem b = H.mem b)
    {Z : Config A B P L} (hZ : I.runFrom Y δ = some Z) :
    ∃ γ G, Good γ ∧ I.runFrom X γ = some G ∧ γ.filter (fun ℓ => decide (ℓ.proc = s)) = δ ∧
      G.loc s = Z.loc s ∧ G.pend s = Z.pend s := by
  induction δ using List.reverseRecOn generalizing Z with
  | nil =>
    simp only [Impl.runFrom_nil, Option.some.injEq] at hZ; subst hZ
    exact ⟨[], X, hgood, rfl, rfl, hloc, hpend⟩
  | append_singleton δ d ih =>
    obtain ⟨Z', hZ'1, hZ'2⟩ := I.runFrom_eq_some_of_append hZ
    rw [I.runFrom_singleton] at hZ'2
    obtain ⟨γ, G, g1, g2, g3, g4, g5⟩ := ih (fun ℓ hℓ => hδ ℓ (by simp [hℓ]))
      (fun γ ℓ hℓ hg => hext γ ℓ (by simp [hℓ]) hg)
      (fun γ G δ₀ H b h1 h2 h3 h4 h5 => hfix γ G δ₀ H b h1 h2 (h3.trans (List.prefix_append _ _))
        h4 h5) hZ'1
    have hds : d.proc = s := hδ d (by simp)
    have hdδ : d ∈ δ ++ [d] := by simp
    by_cases hc : ∃ b o kk, d = .tau s ∧ I.act s (Z'.loc s) = .access b o kk ∧ G.mem b ≠ Z'.mem b
    · obtain ⟨b, o, kk, hd, hact, hne⟩ := hc
      obtain ⟨β', G', f1, f2, f3, f4⟩ := hfix γ G δ Z' b g1 g2 (List.prefix_append _ _) hZ'1 hne
      have hoth := I.runFrom_other f3 (fun ℓ hℓ => f1 ℓ hℓ)
      obtain ⟨D', hD', e1, e2, -⟩ := Impl.step_local (I := I) (C := Z') (D := G')
        (by rw [hoth.1, g4]) (by rw [hoth.2, g5]) hds
        (fun _ i o' k' hact' _ => by
          rw [hact] at hact'
          simp only [Action.access.injEq] at hact'
          obtain ⟨rfl, -⟩ := hact'
          exact f4.symm) hZ'2
      refine ⟨γ ++ β' ++ [d], D', hext _ d hdδ f2, ?_, ?_, e1.symm, e2.symm⟩
      · rw [I.runFrom_append_of_eq (by rw [I.runFrom_append_of_eq g2, f3]), I.runFrom_singleton,
          hD']
      · simp only [List.filter_append, g3, List.filter_cons, hds, decide_true, ↓reduceIte,
          List.filter_nil]
        rw [List.filter_eq_nil_iff.2 (fun ℓ hℓ => by simpa using f1 ℓ hℓ)]
        simp
    · obtain ⟨D', hD', e1, e2, -⟩ := Impl.step_local (I := I) (C := Z') (D := G)
        g4.symm g5.symm hds
        (fun hd i o' k' hact' _ => by
          by_contra hne
          exact hc ⟨i, o', k', hd, hact', Ne.symm hne⟩) hZ'2
      refine ⟨γ ++ [d], D', hext _ d hdδ g1, ?_, ?_, e1.symm, e2.symm⟩
      · rw [I.runFrom_append_of_eq g2, I.runFrom_singleton, hD']
      · simp [List.filter_append, g3, hds]

end Replay

end Cslib.SharedMemory.Scannable
