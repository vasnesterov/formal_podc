import Cslib.Computability.Distributed.SharedMemory.FullInfo

/-!
# Stranger-free tasks need `n` registers (Theorem 2.1 of Gafni–Losa–Raynal–Taubenfeld, PODC 2025)

**Model.** Asynchronous shared memory (`Cslib.SharedMemory`): processes `P`, deterministic
algorithms, multi-writer multi-reader atomic read/write registers indexed by `ι`
(`RegFamily ι V v₀`), no a-priori allocation of registers to processes. A task is solved by an
`Impl` of `taskObj T.In T.Out`, each process invoking it at most once (`OneShot`).

**Full information.** `Impl.fullInfo I` is the full-information version of `I`: registers store
the writer's *view* (identifier, input, all values read), processes store their view
(`Cslib/Computability/Distributed/SharedMemory/FullInfo.lean`). "`q` appears in `p`'s view" is `View.Mentions`.

**Stranger-freedom (paper, §2).** A task is stranger-free when, for every full-information
algorithm that solves it wait-free using read/write registers only, in every execution, any two
processes that have both output are not complete strangers: one of them appears in the view of
the other. We quantify over the full-information versions of all read/write algorithms solving
the task; every full-information algorithm is (behaviourally) its own full-information version.
The progress condition is a parameter (`Progress.waitFree` is the paper's definition;
`Progress.obstructionFree` gives the stronger hypothesis needed for the obstruction-free variant
of Theorem 2.1 mentioned after its proof).

## Main results

* `covering_of_strangerFree`: the covering construction — in some one-shot execution of `I`,
  the `n` given processes cover `n` distinct registers.
* `theorem_2_1`: for `n ≥ 2` processes, every algorithm solving a stranger-free task (wait-free,
  or obstruction-free for the OF variant) uses at least `n` registers.

The proof follows the paper: induction on the number `j` of covered registers, the invariant
being a one-shot execution in which only `p₁, …, p_j` participate, they cover `j` distinct
registers, and `p₁` appears in no register and no other view (`FIClean p₁`). If `p_{j+1}`, run
solo, returned without writing outside the covered set `R`, then after the block write of
`p₁, …, p_j` (which obliterates `R`, `Impl.blockWrite_agreeOn`) and a solo run of `p₁`, `p₁` and
`p_{j+1}` would be complete strangers. The base case uses `p₂` as the stranger of `p₁`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory Impl

/-- Progress conditions for the stranger-freedom quantifier. -/
inductive Progress where
  | waitFree
  | obstructionFree

variable {P : Type} [DecidableEq P]

/-- `I` satisfies the progress condition. -/
def Progress.Holds {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (prog : Progress) (I : Impl A B P L) : Prop :=
  match prog with
  | .waitFree => I.WaitFree
  | .obstructionFree => I.ObstructionFree

lemma Progress.Holds.oneShotOF {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
    {L : Type} {prog : Progress} {I : Impl A B P L} (h : prog.Holds I) : I.OneShotOF := by
  cases prog
  · exact Impl.WaitFree.oneShotOF I h
  · exact Impl.ObstructionFree.oneShotOF I h

lemma Progress.holds_obstructionFree {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
    {L : Type} {I : Impl A B P L} (h : Progress.waitFree.Holds I) :
    Progress.obstructionFree.Holds I := Impl.WaitFree.obstructionFree I h

/-- **Stranger-freedom** (paper, §2). For every read/write algorithm `I` that solves `T` with
progress `prog` (wait-free in the paper) and accepts every input at every process, in every one-shot execution of the full-information
version of `I`, any two processes `i`, `j` that have both output are not complete strangers:
`j` appears in `i`'s view or `i` appears in `j`'s view. -/
def _root_.Cslib.SharedMemory.Task.StrangerFree (T : Task P) [Inhabited T.Out]
    (prog : Progress := .waitFree) : Prop :=
  ∀ (ι V L : Type) [DecidableEq ι] (v₀ : V) (I : Impl (taskObj T.In T.Out) (RegFamily ι V v₀) P L),
    I.Solves T → (∀ p x, I.allowed p x) → prog.Holds I →
    ∀ (α : List (Label P (taskObj T.In T.Out))) (C : FIConfig (taskObj T.In T.Out) ι V P L v₀),
      I.fullInfo.run α = some C → OneShot α →
      ∀ i j, respsOf α i ≠ [] → respsOf α j ≠ [] →
        (C.loc i).2.Mentions j ∨ (C.loc j).2.Mentions i

/-- The obstruction-free variant of stranger-freedom implies the wait-free one. -/
lemma strangerFree_of_obstructionFree {T : Task P} [Inhabited T.Out]
    (h : T.StrangerFree .obstructionFree) : T.StrangerFree .waitFree :=
  fun ι V L _ v₀ I hI hall hp => h ι V L v₀ I hI hall (Progress.holds_obstructionFree hp)

section Covering

variable {T : Task P} [Inhabited T.Out] {ι V L : Type} [DecidableEq ι] {v₀ : V}
  (I : Impl (taskObj T.In T.Out) (RegFamily ι V v₀) P L)

/-- The end of both branches of the covering argument: if `p` has output and appears nowhere,
`p`'s view does not mention `w`, and `w` is pending or has not started yet, then letting `w`
run solo to completion produces two complete strangers — impossible for a stranger-free task. -/
theorem strangers_absurd {prog : Progress} (hT : T.StrangerFree prog) (hI : I.Solves T)
    (hall : ∀ p x, I.allowed p x) (hprog : prog.Holds I) {α : List (Label P (taskObj T.In T.Out))}
    {C : FIConfig (taskObj T.In T.Out) ι V P L v₀} (hα : I.fullInfo.run α = some C)
    (h1 : OneShot α) {p w : P} (hpw : p ≠ w) (hp : respsOf α p ≠ []) (hcp : FIClean p C)
    (hpv : ¬ (C.loc p).2.Mentions w)
    (hw : C.pend w ≠ none ∨ (opsOf α w = [] ∧ ∃ x, I.allowed w x)) : False := by
  classical
  have hof : I.fullInfo.OneShotOF := I.fullInfo_oneShotOF hprog.oneShotOF
  -- first make `w` pending
  obtain ⟨α', C', hα', h1', hp', hcp', hloc', hw', hops'⟩ :
      ∃ (α' : List (Label P (taskObj T.In T.Out))) (C' : FIConfig (taskObj T.In T.Out) ι V P L v₀),
        I.fullInfo.run α' = some C' ∧
        OneShot α' ∧ respsOf α' p ≠ [] ∧ FIClean p C' ∧ C'.loc p = C.loc p ∧
        C'.pend w ≠ none ∧ opsOf α' w ≠ [] := by
    rcases hw with hw | ⟨hw, x, hx⟩
    · exact ⟨α, C, hα, h1, hp, hcp, rfl, hw, Impl.opsOf_ne_nil_of_pend hα hw⟩
    · have hpend : C.pend w = none := pend_none_of_opsOf_nil hα hw
      obtain ⟨C₁, hs⟩ := Option.isSome_iff_exists.1
        (show (I.fullInfo.step C (.inv w x)).isSome by simp [Impl.step, hpend, Impl.fullInfo, hx])
      have hrun : I.fullInfo.run (α ++ [.inv w x]) = some C₁ := by
        rw [run_append_of_eq _ hα, runFrom_singleton, hs]
      refine ⟨_, C₁, hrun, OneShot.append_inv h1 hw x, by simpa [respsOf_append] using hp,
        I.fiClean_step hs (by simpa [Label.proc] using Ne.symm hpw) hcp,
        (step_other hs (by simpa [Label.proc] using Ne.symm hpw)).1, ?_,
        by simp [opsOf_append]⟩
      rw [(step_inv hs).2.2.1]; simp
  -- run `w` solo to completion
  obtain ⟨K, hK⟩ := hof α' C' w hα' h1' hw'
  set C'' := (I.fullInfo.soloStep w)^[K] C'
  have hrun : I.fullInfo.runFrom C' (I.fullInfo.soloLabels w C' K) = some C'' :=
    I.fullInfo.runFrom_soloLabels w C' K
  have hα'' : I.fullInfo.run (α' ++ I.fullInfo.soloLabels w C' K) = some C'' := by
    rw [run_append_of_eq _ hα', hrun]
  have hproc := I.fullInfo.soloLabels_proc w C' K
  have h1'' : OneShot (α' ++ I.fullInfo.soloLabels w C' K) :=
    OneShot.append_of_opsOf_nil h1' (fun y => I.fullInfo.opsOf_soloLabels w y C' K)
  have hrw : respsOf (α' ++ I.fullInfo.soloLabels w C' K) w ≠ [] :=
    Impl.respsOf_ne_nil_of_idle hα'' hK (by simpa [opsOf_append, opsOf_soloLabels] using hops')
  have hrp : respsOf (α' ++ I.fullInfo.soloLabels w C' K) p ≠ [] := by
    simp only [respsOf_append, ne_eq, List.append_eq_nil_iff, not_and]
    exact fun h => absurd h hp'
  have hclean := I.fiClean_runFrom hrun (fun ℓ hℓ => by rw [hproc ℓ hℓ]; exact Ne.symm hpw) hcp'
  have hlocp : C''.loc p = C.loc p := by
    rw [(I.fullInfo.runFrom_other hrun (fun ℓ hℓ => by rw [hproc ℓ hℓ]; exact Ne.symm hpw)).1,
      hloc']
  rcases hT ι V L v₀ I hI hall hprog _ C'' hα'' h1'' p w hrp hrw with h | h
  · rw [hlocp] at h; exact hpv h
  · exact hclean.2 w (Ne.symm hpw) h

/-- **The induction step of the covering argument.** The processes `qs` cover distinct
registers `f q` (the set `R`); `p` has not started. Run `p` solo until it is about to write
outside `R`; it cannot return before (else, after the block write of `qs`, it and the witness
`w` would be complete strangers). In the base case (`qs = []`) the witness `w` has not started. -/
theorem cover_step {prog : Progress} (hT : T.StrangerFree prog) (hI : I.Solves T)
    (hall : ∀ p x, I.allowed p x) (hprog : prog.Holds I) {α : List (Label P (taskObj T.In T.Out))}
    {C : FIConfig (taskObj T.In T.Out) ι V P L v₀} (hα : I.fullInfo.run α = some C)
    (h1 : OneShot α) (cs : List (P × ι)) (hqs : (cs.map Prod.fst).Nodup)
    (hf : (cs.map Prod.snd).Nodup) (hcov : ∀ c ∈ cs, I.fullInfo.Covers C c.1 c.2) {p : P}
    (hpq : p ∉ cs.map Prod.fst) (hpα : opsOf α p = []) {x : T.In} (hx : I.allowed p x) {w : P}
    (hwp : w ≠ p)
    (hw : (w ∈ cs.map Prod.fst ∧ FIClean w C) ∨ (cs = [] ∧ opsOf α w = [] ∧ ∃ y, I.allowed w y)) :
    ∃ (α' : List (Label P (taskObj T.In T.Out))) (C' : FIConfig (taskObj T.In T.Out) ι V P L v₀)
      (r : ι), I.fullInfo.run α' = some C' ∧ OneShot α' ∧
      (∀ y, y ≠ p → opsOf α' y = opsOf α y) ∧
      r ∉ cs.map Prod.snd ∧ I.fullInfo.Covers C' p r ∧ (∀ c ∈ cs, I.fullInfo.Covers C' c.1 c.2) ∧
      (w ∈ cs.map Prod.fst → FIClean w C') ∧ (cs = [] → FIClean p C') := by
  classical
  set qs := cs.map Prod.fst with hqsdef
  have hof : I.fullInfo.OneShotOF := I.fullInfo_oneShotOF hprog.oneShotOF
  have hpp : C.pend p = none := pend_none_of_opsOf_nil hα hpα
  have hcleanp : FIClean p C := I.fiClean_of_not_invoked hα hpα
  obtain ⟨C₁, hs₁⟩ := Option.isSome_iff_exists.1
    (show (I.fullInfo.step C (.inv p x)).isSome by simp [Impl.step, hpp, Impl.fullInfo, hx])
  have hα₁ : I.fullInfo.run (α ++ [.inv p x]) = some C₁ := by
    rw [run_append_of_eq _ hα, runFrom_singleton, hs₁]
  have h1₁ := OneShot.append_inv h1 hpα x
  have hp₁ : C₁.pend p ≠ none := by rw [(step_inv hs₁).2.2.1]; simp
  obtain ⟨K, hK⟩ := hof _ C₁ p hα₁ h1₁ hp₁
  set R := cs.map Prod.snd
  obtain ⟨m, hm₁, hm₂⟩ := I.fullInfo.exists_solo_until p C₁
    (fun a => ∃ i o k, a = .access i o k ∧ i ∉ R ∧
      (RegFamily ι (V × Option (View P (taskObj T.In T.Out).Op)) (v₀, none) i).Overwrites o)
    ⟨K, hK⟩
  set C₂ := (I.fullInfo.soloStep p)^[m] C₁
  set γ := I.fullInfo.soloLabels p C₁ m
  have hrun₂ : I.fullInfo.runFrom C₁ γ = some C₂ := I.fullInfo.runFrom_soloLabels p C₁ m
  have hα₂ : I.fullInfo.run ((α ++ [.inv p x]) ++ γ) = some C₂ := by
    rw [run_append_of_eq _ hα₁, hrun₂]
  have hprocγ := I.fullInfo.soloLabels_proc p C₁ m
  have h1₂ : OneShot ((α ++ [.inv p x]) ++ γ) :=
    OneShot.append_of_opsOf_nil h1₁ (fun y => I.fullInfo.opsOf_soloLabels p y C₁ m)
  have hrunC : I.fullInfo.runFrom C ([.inv p x] ++ γ) = some C₂ := by
    rw [runFrom_append, runFrom_singleton, hs₁]; exact hrun₂
  have hprocCγ : ∀ ℓ ∈ ([.inv p x] ++ γ), ℓ.proc = p := by
    intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · simp only [List.mem_singleton] at hℓ; subst hℓ; rfl
    · exact hprocγ ℓ hℓ
  have hother : ∀ y, y ≠ p → C₂.loc y = C.loc y ∧ C₂.pend y = C.pend y := fun y hy =>
    I.fullInfo.runFrom_other hrunC (fun ℓ hℓ => by rw [hprocCγ ℓ hℓ]; exact Ne.symm hy)
  have hops : ∀ y, y ≠ p → opsOf ((α ++ [.inv p x]) ++ γ) y = opsOf α y := by
    intro y hy
    have : opsOf ([.inv p x] ++ γ) y = [] :=
      opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hprocCγ ℓ hℓ]; exact Ne.symm hy)
    rw [List.append_assoc, opsOf_append, this, List.append_nil]
  have hcov₂ : ∀ c ∈ cs, I.fullInfo.Covers C₂ c.1 c.2 := by
    intro c hc
    have hqp : c.1 ≠ p := fun h => hpq (h ▸ List.mem_map_of_mem hc)
    obtain ⟨hq1, o, k, hact, hov⟩ := hcov c hc
    exact ⟨by rw [(hother c.1 hqp).2]; exact hq1, o, k, by rw [(hother c.1 hqp).1]; exact hact, hov⟩
  have hmemR : ∀ i, i ∉ R → C₂.mem i = C.mem i := by
    intro i hi
    rw [I.fullInfo.iterate_soloStep_mem_of_readOnly p C₁ {i | i ∈ R} m (fun j hj i o k hact hiR =>
      I.fullInfo_access_readOnly hact (fun hov => (hm₁ j hj).2 ⟨i, o, k, hact, hiR, hov⟩)) i hi]
    rw [(step_inv hs₁).2.2.2.2]
  have hwclean₂ : w ∈ qs → FIClean w C₂ := by
    intro hwq
    rcases hw with ⟨-, hcw⟩ | ⟨hcs, -⟩
    · exact I.fiClean_runFrom hrunC (fun ℓ hℓ => by rw [hprocCγ ℓ hℓ]; exact Ne.symm hwp) hcw
    · simp [hqsdef, hcs] at hwq
  by_cases hret : C₂.pend p = none
  · -- `p` returned without writing outside `R`: contradiction
    exfalso
    have hrp : respsOf ((α ++ [.inv p x]) ++ γ) p ≠ [] :=
      Impl.respsOf_ne_nil_of_idle hα₂ hret (by simp [opsOf_append, Label.invOf])
    have hagC : ∀ q ∈ qs, C₂.loc q = C.loc q := fun q hq =>
      (hother q (fun h => hpq (h ▸ hq))).1
    have hagP : ∀ q ∈ qs, C₂.pend q = C.pend q := fun q hq =>
      (hother q (fun h => hpq (h ▸ hq))).2
    obtain ⟨C₃, C₃', hb, hb', hag⟩ := I.fullInfo.blockWrite_agreeOn (Q := {y | y ∈ qs}) hqs
      (fun c hc => List.mem_map_of_mem hc) hcov₂ hagC hagP hmemR
    have hbproc : ∀ ℓ ∈ (blockWrite qs : List (Label P (taskObj T.In T.Out))), ℓ.proc ∈ qs :=
      fun ℓ hℓ => mem_blockWrite hℓ
    have hclean₃' : FIClean p C₃' :=
      I.fiClean_runFrom hb' (fun ℓ hℓ h => hpq (by rw [← h]; exact hbproc ℓ hℓ)) hcleanp
    have hclean₃ : FIClean p C₃ := by
      refine ⟨fun i => by rw [hag.mem]; exact hclean₃'.1 i, fun y hy => ?_⟩
      by_cases hyq : y ∈ qs
      · rw [hag.loc y hyq]; exact hclean₃'.2 y hy
      · have hne : ∀ ℓ ∈ (blockWrite qs : List (Label P (taskObj T.In T.Out))), ℓ.proc ≠ y :=
          fun ℓ hℓ h => hyq (by rw [← h]; exact hbproc ℓ hℓ)
        have e1 := (I.fullInfo.runFrom_other hb hne).1
        have e2 := (I.fullInfo.runFrom_other hb' hne).1
        rw [e1, (hother y hy).1, ← e2]; exact hclean₃'.2 y hy
    have hα₃ : I.fullInfo.run (((α ++ [.inv p x]) ++ γ) ++ blockWrite qs) = some C₃ := by
      rw [run_append_of_eq _ hα₂, hb]
    have h1₃ := OneShot.append_of_opsOf_nil h1₂ (opsOf_blockWrite qs)
    have hlocp : C₃.loc p = C₂.loc p :=
      (I.fullInfo.runFrom_other hb (fun ℓ hℓ h => hpq (by rw [← h]; exact hbproc ℓ hℓ))).1
    have hwclean₂' : FIClean w C₂ := by
      rcases hw with ⟨hwq, -⟩ | ⟨-, hwα, -⟩
      · exact hwclean₂ hwq
      · exact I.fiClean_of_not_invoked hα₂ (by rw [hops w hwp]; exact hwα)
    refine strangers_absurd I hT hI hall hprog hα₃ h1₃ (Ne.symm hwp)
      (by simpa [respsOf_append, respsOf_blockWrite] using hrp) hclean₃
      (by rw [hlocp]; exact hwclean₂'.2 p (Ne.symm hwp)) ?_
    rcases hw with ⟨hwq, -⟩ | ⟨-, hwα, hwx⟩
    · left
      rw [I.fullInfo.runFrom_pend_of_tau hb blockWrite_tau, (hother w hwp).2]
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hwq
      exact (hcov c hc).1
    · right
      exact ⟨by rw [opsOf_append, hops w hwp, hwα, opsOf_blockWrite]; rfl, hwx⟩
  · -- `p` is poised to write outside `R`
    obtain ⟨r, o, k, hact, hrR, hov⟩ := hm₂.resolve_left hret
    refine ⟨_, C₂, r, hα₂, h1₂, hops, hrR, ⟨hret, o, k, hact, hov⟩, hcov₂, hwclean₂, ?_⟩
    rintro rfl
    refine ⟨fun i => by rw [hmemR i (by simp [R])]; exact hcleanp.1 i, fun y hy => ?_⟩
    rw [(hother y hy).1]; exact hcleanp.2 y hy

/-- **The covering construction** (proof of Theorem 2.1): if `T` is stranger-free, then for any
`n ≥ 2` distinct processes `ps` (each with an allowed input) there is a one-shot execution of `I`
in which the processes of `ps` cover `n` distinct registers. -/
theorem covering_of_strangerFree {prog : Progress} (hT : T.StrangerFree prog) (hI : I.Solves T)
    (hall : ∀ p x, I.allowed p x) (hprog : prog.Holds I) (ps : List P) (hnd : ps.Nodup)
    (h2 : 2 ≤ ps.length)
    (hin : ∀ p ∈ ps, ∃ x, I.allowed p x) :
    ∃ (α : List (Label P (taskObj T.In T.Out)))
      (C : Config (taskObj T.In T.Out) (RegFamily ι V v₀) P L) (cs : List (P × ι)),
      I.run α = some C ∧ OneShot α ∧ cs.map Prod.fst = ps ∧ (cs.map Prod.snd).Nodup ∧
      ∀ c ∈ cs, I.Covers C c.1 c.2 := by
  have h0 : 0 < ps.length := by omega
  have h1' : 1 < ps.length := by omega
  have hne : ∀ a b (ha : a < ps.length) (hb : b < ps.length), a ≠ b → ps[a] ≠ ps[b] :=
    fun a b ha hb hab h => hab ((List.Nodup.getElem_inj_iff hnd).1 h)
  have htake : ∀ j (hj : j < ps.length), ps.take (j + 1) = ps.take j ++ [ps[j]] := by
    intro j hj; rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  have key : ∀ j, 1 ≤ j → j ≤ ps.length → ∃ (α : List (Label P (taskObj T.In T.Out)))
      (C : FIConfig (taskObj T.In T.Out) ι V P L v₀) (cs : List (P × ι)),
      I.fullInfo.run α = some C ∧ OneShot α ∧ (∀ y, y ∉ ps.take j → opsOf α y = []) ∧
      cs.map Prod.fst = ps.take j ∧ (cs.map Prod.snd).Nodup ∧
      (∀ c ∈ cs, I.fullInfo.Covers C c.1 c.2) ∧ FIClean ps[0] C := by
    intro j hj1 hjn
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · obtain ⟨xw, hxw⟩ := hin ps[0] (List.getElem_mem _)
        obtain ⟨xu, hxu⟩ := hin ps[1] (List.getElem_mem _)
        obtain ⟨α', C', r, hrun, h1, hops, -, hcovp, -, -, hclean⟩ :=
          cover_step I hT hI hall hprog (α := []) (C := I.fullInfo.initCfg) rfl (fun _ => by simp) []
            (by simp) (by simp) (by simp) (p := ps[0]) (by simp) rfl hxw (w := ps[1])
            (hne 1 0 h1' h0 (by omega)) (Or.inr ⟨rfl, rfl, xu, hxu⟩)
        have ht1 : ps.take (0 + 1) = [ps[0]] := by rw [htake 0 h0]; simp
        refine ⟨α', C', [(ps[0], r)], hrun, h1, fun y hy => ?_, by rw [ht1]; rfl, by simp,
          by simpa using hcovp, hclean rfl⟩
        have hy0 : y ≠ ps[0] := by rintro rfl; apply hy; rw [ht1]; simp
        rw [hops y hy0]; rfl
      · obtain ⟨α, C, cs, hrun, h1, hops, hcs1, hcs2, hcov, hclean⟩ := ih (by omega) (by omega)
        have hjl : j < ps.length := by omega
        have hnd' : (ps.take j ++ [ps[j]]).Nodup := by
          rw [← htake j hjl]; exact hnd.sublist (List.take_sublist _ _)
        have hpq : ps[j] ∉ ps.take j := by
          intro h
          exact (List.nodup_append.1 hnd').2.2 _ h _ (List.mem_singleton_self _) rfl
        obtain ⟨x, hx⟩ := hin ps[j] (List.getElem_mem _)
        have hwq : ps[0] ∈ cs.map Prod.fst := by
          rw [hcs1]
          have : (ps.take j)[0]'(by simp; omega) = ps[0] := by simp
          rw [← this]; exact List.getElem_mem _
        obtain ⟨α', C', r, hrun', h1', hops', hr, hcovp, hcov', hclean', -⟩ :=
          cover_step I hT hI hall hprog hrun h1 cs (by rw [hcs1]; exact hnd.sublist (List.take_sublist _ _))
            hcs2 hcov (by rw [hcs1]; exact hpq) (hops _ hpq) hx (hne 0 j h0 hjl (by omega))
            (Or.inl ⟨hwq, hclean⟩)
        refine ⟨α', C', cs ++ [(ps[j], r)], hrun', h1', fun y hy => ?_, ?_, ?_, ?_, hclean' hwq⟩
        · rw [htake j hjl] at hy
          have hy1 : y ≠ ps[j] := fun h => hy (by rw [h]; exact List.mem_append_right _ (by simp))
          rw [hops' y hy1]; exact hops y (fun h => hy (List.mem_append_left _ h))
        · rw [htake j hjl]; simp [hcs1]
        · simp only [List.map_append, List.map_cons, List.map_nil]
          exact List.nodup_append.2 ⟨hcs2, List.nodup_singleton _, fun a ha b hb => by
            simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hr ha⟩
        · intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact hcov' c hc
          · simp only [List.mem_singleton] at hc; subst hc; exact hcovp
  obtain ⟨α, C, cs, hrun, h1, -, hcs1, hcs2, hcov, -⟩ := key ps.length (by omega) le_rfl
  rw [List.take_length] at hcs1
  exact ⟨α, fiProj C, cs, I.fullInfo_run_some hrun, h1, hcs1, hcs2,
    fun c hc => I.fullInfo_covers (hcov c hc)⟩

/-- **Theorem 2.1** (Gafni–Losa–Raynal–Taubenfeld, PODC 2025). For every `n > 1` and every
stranger-free task for `n` processes, every wait-free algorithm that solves the task using
read/write registers only uses at least `n` registers. (In fact, `n` distinct registers are
covered simultaneously in some execution: `covering_of_strangerFree`.) -/
theorem theorem_2_1 [Fintype P] [Fintype ι] (hn : 2 ≤ Fintype.card P) (hT : T.StrangerFree)
    (hI : I.Solves T) (hwf : I.WaitFree) (hall : ∀ p x, I.allowed p x) [Nonempty T.In] :
    Fintype.card P ≤ Fintype.card ι := by
  classical
  obtain ⟨-, -, cs, -, -, hcs1, hcs2, -⟩ := covering_of_strangerFree I hT hI hall hwf
    Finset.univ.toList (Finset.nodup_toList _) (by rw [Finset.length_toList]; exact hn)
    (fun p _ => ⟨(Classical.arbitrary T.In : T.In), hall p _⟩)
  have := hcs2.length_le_card
  rw [List.length_map] at this
  have hl := congrArg List.length hcs1
  rw [List.length_map, Finset.length_toList, Finset.card_univ] at hl
  rw [← hl]; exact this

/-- **Theorem 2.1, obstruction-free variant** (remark after the proof in the paper): the same
bound for obstruction-free algorithms, for tasks that are stranger-free with respect to
obstruction-free full-information algorithms. -/
theorem theorem_2_1_obstructionFree [Fintype P] [Fintype ι] (hn : 2 ≤ Fintype.card P)
    (hT : T.StrangerFree .obstructionFree) (hI : I.Solves T) (hof : I.ObstructionFree)
    (hall : ∀ p x, I.allowed p x) [Nonempty T.In] : Fintype.card P ≤ Fintype.card ι := by
  classical
  obtain ⟨-, -, cs, -, -, hcs1, hcs2, -⟩ := covering_of_strangerFree I hT hI hall hof
    Finset.univ.toList (Finset.nodup_toList _) (by rw [Finset.length_toList]; exact hn)
    (fun p _ => ⟨(Classical.arbitrary T.In : T.In), hall p _⟩)
  have := hcs2.length_le_card
  rw [List.length_map] at this
  have hl := congrArg List.length hcs1
  rw [List.length_map, Finset.length_toList, Finset.card_univ] at hl
  rw [← hl]; exact this

end Covering

end Cslib.SharedMemory.StrangerFree
