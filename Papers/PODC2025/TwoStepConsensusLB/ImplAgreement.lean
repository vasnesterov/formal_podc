import Papers.PODC2025.TwoStepConsensusLB.ImplRefine
import Papers.PODC2025.TwoStepConsensusLB.Fig1Safety
import Papers.PODC2025.TwoStepConsensusLB.ImplMain
import Papers.PODC2025.TwoStepConsensusLB.LowerBound

/-!
# Agreement of the implementation, by refinement to the abstract system of Fig. 1

For every run `R` of `fig1 c` (task runs with inputs `cfg.input`, or well-formed object runs),
the abstraction `absState cfg c R τ` of the global state at time `τ` (local states via `absLoc`,
messages = all messages sent before `τ`) is a reachable state of the abstract transition system
`Fig1` (`absState_reachable`). Agreement then follows from `Fig1.agreement_msgs`
(`task_agreement'`, `object_agreement'`).

No assumption on the run's timing (`Valid`) is needed: only that the adversary's order is a
permutation.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

open _root_.Cslib.CrashPartialSync

open Relation

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

section Defs

variable (cfg : Fig1.Config P V) (c : Cfg P) (R : Run P V (Msg P V))

/-- Ghost: the argument of the invocation of `p` before time `τ` (if it was alive then). -/
def absInv : ℕ → P → Option V
  | 0, _ => none
  | τ + 1, p => if R.alive p τ ∧ (R.inv p τ).isSome then R.inv p τ else absInv τ p

/-- The ghost invocation of the abstract system (object version only). -/
def ghost (τ : ℕ) (p : P) : Option V := if cfg.ver = .object then absInv R τ p else none

/-- All (abstract) messages sent before time `τ`. -/
def absMsgs (τ : ℕ) : Set (Fig1.Msg P V) :=
  {m | ∃ q τ', τ' < τ ∧ R.alive q τ' ∧ m ∈ (R.st (fig1 c) (τ' + 1) q).out.map (absMsg q)}

/-- The abstraction of the global state at time `τ`. -/
noncomputable def absState (τ : ℕ) : Fig1.State P V :=
  ⟨fun x => absLoc cfg x (ghost cfg R τ x) (R.st (fig1 c) τ x), absMsgs c R τ⟩

end Defs

section Lemmas

variable {cfg : Fig1.Config P V} {c : Cfg P} {R : Run P V (Msg P V)}

theorem alive_of_succ {x : P} {τ : ℕ} (h : R.alive x (τ + 1)) : R.alive x τ := by
  rw [Run.alive_iff] at h ⊢
  intro c hc; have := h c hc; omega

theorem alive_of_le {x : P} {τ τ' : ℕ} (hle : τ ≤ τ') (h : R.alive x τ') : R.alive x τ := by
  rw [Run.alive_iff] at h ⊢
  intro c hc; have := h c hc; omega

theorem absMsgs_mono {τ τ' : ℕ} (h : τ ≤ τ') : absMsgs c R τ ⊆ absMsgs c R τ' := by
  rintro m ⟨q, τ₁, h1, h2, h3⟩
  exact ⟨q, τ₁, by omega, h2, h3⟩

theorem absMsgs_succ (τ : ℕ) : absMsgs c R (τ + 1) =
    absMsgs c R τ ∪
      {m | ∃ q, R.alive q τ ∧ m ∈ (R.st (fig1 c) (τ + 1) q).out.map (absMsg q)} := by
  ext m
  simp only [absMsgs, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, τ₁, h1, h2, h3⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | rfl
    · exact Or.inl ⟨q, τ₁, h, h2, h3⟩
    · exact Or.inr ⟨q, h2, h3⟩
  · rintro (⟨q, τ₁, h1, h2, h3⟩ | ⟨q, h2, h3⟩)
    · exact ⟨q, τ₁, by omega, h2, h3⟩
    · exact ⟨q, τ, by omega, h2, h3⟩

/-- Extending the set of messages by messages that are not `2A`s of ballots owned by `p`. -/
theorem LocI.extend {p : P} {Mr M M' : Set (Fig1.Msg P V)} {s : St P V}
    (hI : LocI cfg c p Mr M s)
    (h : ∀ m ∈ M', m ∈ M ∨ m ∈ {m | m ∈ s.out.map (absMsg p)} ∨
      ∀ b w, m = .twoA b w → c.owner b ≠ p) : LocI cfg c p Mr M' s := by
  refine ⟨hI.twoBs, hI.oneBs, hI.key, hI.owner, fun b w hb hw => ?_, hI.shape⟩
  rcases hw with hw | hw
  · rcases h _ hw with h' | h' | h'
    · exact hI.twoA b w hb (Or.inl h')
    · exact hI.twoA b w hb (Or.inr h')
    · exact absurd hb (h' b w rfl)
  · exact hI.twoA b w hb (Or.inr hw)

/-- Clearing the outbox. -/
theorem LocI.reset {p : P} {Mr M : Set (Fig1.Msg P V)} {s : St P V}
    (hI : LocI cfg c p Mr M s) : LocI cfg c p Mr M { s with out := [] } :=
  ⟨hI.twoBs, hI.oneBs, hI.key, hI.owner,
    fun b w hb hw => hI.twoA b w hb (Or.inl (by simpa using hw)),
    by simp⟩

/-- `2A`s sent by `q` are of ballots owned by `q`. -/
theorem twoA_owner_of_shape {q : P} {l : List (Dest P × Msg P V)}
    (h : ∀ dm ∈ l, Shape c q dm) {m : Fig1.Msg P V} (hm : m ∈ l.map (absMsg q)) :
    ∀ b w, m = .twoA b w → c.owner b = q := by
  rintro b w rfl
  obtain ⟨⟨d, m'⟩, hdm, he⟩ := List.mem_map.1 hm
  cases m' with
  | twoA b' w' =>
    simp only [absMsg, Fig1.Msg.twoA.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ((h _ hdm).twoA _ _ rfl).1
  | twoB b' w' => cases d <;> simp [absMsg] at he
  | propose v => simp [absMsg] at he
  | decide b' v => simp [absMsg] at he
  | oneA b' => simp [absMsg] at he
  | oneB b' d' => simp [absMsg] at he

theorem LocI.mono_r {p : P} {Mr Mr' M : Set (Fig1.Msg P V)} {s : St P V}
    (hI : LocI cfg c p Mr M s) (h : Mr ⊆ Mr') : LocI cfg c p Mr' M s :=
  ⟨fun x hx => h (hI.twoBs x hx), fun x hx => h (hI.oneBs x hx), hI.key, hI.owner, hI.twoA,
    hI.shape⟩

/-- A message `(q, m)` delivered to `y` at time `τ` satisfies `RcvOK`, given the shapes of all
earlier outboxes. -/
theorem rcvOK_of_inbox (hord : IsOrder R.ord) {τ : ℕ}
    (hC : ∀ τ' < τ, ∀ q, R.alive q τ' → ∀ dm ∈ (R.st (fig1 c) (τ' + 1) q).out, Shape c q dm)
    {y q : P} {m : Msg P V} (hqm : (q, m) ∈ R.inbox (fig1 c) y τ) :
    RcvOK c y (absMsgs c R τ) (q, m) := by
  obtain ⟨τ', hτ', -, hm⟩ := (Run.mem_inbox _ R hord).1 hqm
  have hal : R.alive q τ' := by
    by_contra h
    rw [Run.out_of_not_alive _ _ (by simpa using h)] at hm
    simp at hm
  rw [Run.out_of_alive _ _ hal, mem_send] at hm
  obtain ⟨d, hd, hinc⟩ := hm
  have hsh := hC τ' hτ' q hal (d, m) hd
  obtain ⟨τ'', -, hT⟩ := timing_inbox hord hqm
  refine ⟨⟨q, τ', hτ', hal, List.mem_map.2 ⟨(d, m), hd, ?_⟩⟩, fun v hv => ?_, fun b dd hb => ?_,
    fun b w hb => ?_, fun b hb => ?_⟩
  · cases m with
    | twoB b v =>
      obtain ⟨r, hr⟩ := hsh.twoB b v rfl
      simp only at hr; subst hr
      simp only [Dest.incl, decide_eq_true_eq] at hinc
      subst hinc; rfl
    | propose v => rfl
    | decide b v => rfl
    | oneA b => rfl
    | oneB b dd => rfl
    | twoA b v => rfl
  · simp only at hv; subst hv
    have := hsh.propose v rfl
    simp only at this; subst this
    simp only [Dest.incl, decide_eq_true_eq] at hinc
    exact fun h => hinc h.symm
  · simp only at hb; subst hb
    have := hsh.oneB b dd rfl
    simp only at this; subst this
    simp only [Dest.incl, decide_eq_true_eq] at hinc
    exact hinc.symm
  · simp only at hb; subst hb
    exact (hsh.twoA b w rfl).1
  · simp only at hb; subst hb
    exact hT.2.2

theorem absInv_succ_of_not_alive {y : P} {τ : ℕ} (h : ¬ R.alive y τ) :
    absInv R (τ + 1) y = absInv R τ y := by
  simp [absInv, h]

theorem absInv_eq_none {y : P} {τ : ℕ} (h : ∀ τ₁ < τ, R.alive y τ₁ → R.inv y τ₁ = none) :
    absInv R τ y = none := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    simp only [absInv]
    split_ifs with h'
    · exact absurd (h τ (by omega) h'.1) (Option.isSome_iff_ne_none.1 h'.2)
    · exact ih fun τ₁ hτ₁ => h τ₁ (by omega)

end Lemmas

/-! ### The simulation -/

section Simulation

variable (cfg : Fig1.Config P V) (c : Cfg P) (R : Run P V (Msg P V))

/-- The run is one of the runs considered by the specification: task runs (inputs
`cfg.input`) or well-formed object runs; the delivery order is a permutation. -/
def RunOK : Prop :=
  IsOrder R.ord ∧ ((cfg.ver = .task ∧ R.inv = taskInv cfg.input) ∨
    (cfg.ver = .object ∧ R.WellFormed))

/-- The invariant of the simulation at time `τ`. -/
structure Claim (τ : ℕ) : Prop where
  reach : Fig1.Reachable cfg (absState cfg c R τ)
  loc : ∀ x, R.alive x τ →
    LocI cfg c x (absMsgs c R τ) (absMsgs c R τ) { R.st (fig1 c) τ x with out := [] }
  iv : cfg.ver = .task → ∀ x, R.alive x τ → 1 ≤ τ →
    (R.st (fig1 c) τ x).initVal = some (cfg.input x)
  shape : ∀ τ' < τ, ∀ q, R.alive q τ' → ∀ dm ∈ (R.st (fig1 c) (τ' + 1) q).out, Shape c q dm

/-- The abstract state in the middle of the simulation of time step `τ`: the processes of `D`
have done their step. -/
noncomputable def midSt (τ : ℕ) (D : Finset P) : Fig1.State P V :=
  ⟨fun x => if x ∈ D then absLoc cfg x (ghost cfg R (τ + 1) x) (R.st (fig1 c) (τ + 1) x)
    else absLoc cfg x (ghost cfg R τ x) (R.st (fig1 c) τ x),
   absMsgs c R τ ∪
    {m | ∃ q ∈ D, R.alive q τ ∧ m ∈ (R.st (fig1 c) (τ + 1) q).out.map (absMsg q)}⟩

variable {cfg c R}

theorem midSt_empty (τ : ℕ) : midSt cfg c R τ ∅ = absState cfg c R τ := by
  refine state_ext ?_ ?_
  · funext x; simp [midSt, absState]
  · ext m; simp [midSt, absState]

theorem midSt_univ (τ : ℕ) : midSt cfg c R τ Finset.univ = absState cfg c R (τ + 1) := by
  refine state_ext ?_ ?_
  · funext x; simp [midSt, absState]
  · rw [absState, absMsgs_succ]; ext m; simp [midSt]

/-- The invocation hypothesis of `sim_stepFn` holds for runs satisfying `RunOK`. -/
theorem invoke_hyp (hR : RunOK cfg R) {τ : ℕ} (hC : Claim cfg c R τ) {y : P}
    (hal : R.alive y τ) :
    (R.inv y τ = none ∧ ghost cfg R (τ + 1) y = ghost cfg R τ y ∧
        (cfg.ver = .task → (R.st (fig1 c) τ y).initVal = some (cfg.input y))) ∨
      (cfg.ver = .object ∧ ghost cfg R τ y = none ∧ R.inv y τ = ghost cfg R (τ + 1) y ∧
        (R.inv y τ).isSome) ∨
      (cfg.ver = .task ∧ R.inv y τ = some (cfg.input y) ∧ (R.st (fig1 c) τ y).val = none ∧
        ghost cfg R (τ + 1) y = ghost cfg R τ y) := by
  rcases hR.2 with ⟨hver, hinv⟩ | ⟨hver, hwf⟩
  · have hg : ∀ t, ghost cfg R t y = none := fun t => by simp [ghost, hver]
    rcases τ with _ | τ
    · right; right
      exact ⟨hver, by simp [hinv, taskInv], by simp [fig1], by rw [hg, hg]⟩
    · left
      exact ⟨by simp [hinv, taskInv], by rw [hg, hg], fun h => hC.iv h y hal (by omega)⟩
  · have hg : ∀ t, ghost cfg R t y = absInv R t y := fun t => by simp [ghost, hver]
    rcases h : R.inv y τ with _ | v
    · left
      refine ⟨rfl, ?_, fun h' => by simp [hver] at h'⟩
      rw [hg, hg]; simp [absInv, h]
    · right; left
      refine ⟨hver, ?_, ?_, by simp⟩
      · rw [hg]
        refine absInv_eq_none fun τ₁ hτ₁ _ => ?_
        by_contra hne
        have := hwf y τ₁ τ hne (by simp [h])
        omega
      · rw [hg]; simp [absInv, hal, h]

/-- **One time step of the run is a sequence of abstract steps** (process by process). -/
theorem step_D (hm : Match cfg c) (hR : RunOK cfg R) {τ : ℕ} (hC : Claim cfg c R τ)
    (D : Finset P) :
    ReflTransGen (Fig1.Next cfg) (absState cfg c R τ) (midSt cfg c R τ D) ∧
      ∀ x ∈ D, R.alive x τ →
        LocI cfg c x (absMsgs c R τ) (midSt cfg c R τ D).msgs (R.st (fig1 c) (τ + 1) x) ∧
        (cfg.ver = .task → (R.st (fig1 c) (τ + 1) x).initVal = some (cfg.input x)) := by
  induction D using Finset.induction_on with
  | empty => exact ⟨by rw [midSt_empty], by simp⟩
  | @insert y D hy ih =>
    obtain ⟨ihR, ihL⟩ := ih
    by_cases hal : R.alive y τ
    · set L := (midSt cfg c R τ D).loc
      set M := (midSt cfg c R τ D).msgs
      have hsub : absMsgs c R τ ⊆ M := fun m hm' => Or.inl hm'
      have hI0 : LocI cfg c y (absMsgs c R τ) M { R.st (fig1 c) τ y with out := [] } := by
        refine (hC.loc y hal).extend fun m hm' => ?_
        rcases hm' with hm' | ⟨q, hq, hqal, hqm⟩
        · exact Or.inl hm'
        · right; right
          intro b w hbw
          have := twoA_owner_of_shape (ihL q hq hqal).1.shape hqm b w hbw
          rw [this]; rintro rfl; exact hy hq
      have hl : ∀ qm ∈ R.inbox (fig1 c) y τ, RcvOK c y (absMsgs c R τ) qm := by
        rintro ⟨q, m⟩ hqm
        exact rcvOK_of_inbox hR.1 hC.shape hqm
      obtain ⟨hrt, hloc, hiv⟩ := sim_stepFn hm hsub (L := L) (g := ghost cfg R τ y)
        (g' := ghost cfg R (τ + 1) y) τ hI0 (invoke_hyp hR hC hal) hl
      have hst : R.st (fig1 c) (τ + 1) y =
          stepFn c y τ (R.st (fig1 c) τ y) (R.inv y τ) (R.inbox (fig1 c) y τ) :=
        Run.st_succ_of_alive _ _ hal
      rw [← hst] at hrt hloc hiv
      have hstart : simSt cfg L M y (ghost cfg R τ y) { R.st (fig1 c) τ y with out := [] } =
          midSt cfg c R τ D := by
        refine state_ext ?_ ?_
        · funext x
          simp only [simSt, Function.update_apply]
          split_ifs with h
          · subst h; simp [midSt, hy]; rfl
          · rfl
        · ext m; simp [simSt, M]
      have hend : simSt cfg L M y (ghost cfg R (τ + 1) y) (R.st (fig1 c) (τ + 1) y) =
          midSt cfg c R τ (insert y D) := by
        refine state_ext ?_ ?_
        · funext x
          simp only [simSt, Function.update_apply, L, midSt, Finset.mem_insert]
          split_ifs <;> simp_all
        · ext m
          simp only [simSt, M, midSt, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_insert]
          constructor
          · rintro ((h | ⟨q, hq, h1, h2⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨q, Or.inr hq, h1, h2⟩
            · exact Or.inr ⟨y, Or.inl rfl, hal, h⟩
          · rintro (h | ⟨q, hq | hq, h1, h2⟩)
            · exact Or.inl (Or.inl h)
            · subst hq; exact Or.inr h2
            · exact Or.inl (Or.inr ⟨q, hq, h1, h2⟩)
      have hMnew : (midSt cfg c R τ (insert y D)).msgs = M ∪
          {m | m ∈ (R.st (fig1 c) (τ + 1) y).out.map (absMsg y)} := by
        rw [← hend]; rfl
      refine ⟨ihR.trans (hstart ▸ hend ▸ hrt), fun x hx hxal => ?_⟩
      rw [hMnew]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · refine ⟨hloc.extend fun m hm' => ?_, hiv⟩
        rcases hm' with hm' | hm'
        · exact Or.inl hm'
        · exact Or.inr (Or.inl hm')
      · obtain ⟨h1, h2⟩ := ihL x hx hxal
        refine ⟨h1.extend fun m hm' => ?_, h2⟩
        rcases hm' with hm' | hm'
        · exact Or.inl hm'
        · right; right
          intro b w hbw
          have := twoA_owner_of_shape hloc.shape hm' b w hbw
          rw [this]; rintro rfl; exact hy hx
    · have hst : R.st (fig1 c) (τ + 1) y = R.st (fig1 c) τ y :=
        Run.st_succ_of_not_alive _ _ (by simpa using hal)
      have hg : ghost cfg R (τ + 1) y = ghost cfg R τ y := by
        simp only [ghost]; split_ifs
        · exact absInv_succ_of_not_alive hal
        · rfl
      have heq : midSt cfg c R τ (insert y D) = midSt cfg c R τ D := by
        refine state_ext ?_ ?_
        · funext x
          simp only [midSt, Finset.mem_insert]
          by_cases hxy : x = y
          · subst hxy; simp [hy, hst, hg]
          · simp [hxy]
        · ext m
          simp only [midSt, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_insert]
          constructor
          · rintro (h | ⟨q, hq | hq, h1, h2⟩)
            · exact Or.inl h
            · subst hq; exact absurd h1 hal
            · exact Or.inr ⟨q, hq, h1, h2⟩
          · rintro (h | ⟨q, hq, h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨q, Or.inr hq, h1, h2⟩
      refine ⟨heq ▸ ihR, fun x hx hxal => ?_⟩
      rw [heq]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact absurd hxal hal
      · exact ihL x hx hxal

theorem claim_zero : Claim cfg c R 0 := by
  refine ⟨?_, fun x _ => ?_, fun _ _ _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  · have : absState cfg c R 0 = Fig1.init cfg := by
      refine state_ext ?_ ?_
      · funext x
        simp only [absState, Run.st_zero, Fig1.init, ghost, absInv, absLoc]
        split_ifs <;> simp_all [fig1]
      · ext m; simp [absState, absMsgs, Fig1.init]
    rw [this]; exact ReflTransGen.refl
  · refine ⟨by simp [fig1], by simp [fig1], by simp [fig1], by simp [fig1], fun b w _ hw => ?_,
      by simp⟩
    simp [absMsgs] at hw

theorem claim_succ (hm : Match cfg c) (hR : RunOK cfg R) {τ : ℕ} (hC : Claim cfg c R τ) :
    Claim cfg c R (τ + 1) := by
  obtain ⟨hrt, hL⟩ := step_D hm hR hC Finset.univ
  rw [midSt_univ] at hrt hL
  refine ⟨hC.reach.trans hrt, fun x hx => ?_, fun hver x hx _ => ?_, fun τ' hτ' q hq => ?_⟩
  · have := (hL x (Finset.mem_univ _) (alive_of_succ hx)).1
    exact (this.mono_r (absMsgs_mono (by omega))).reset
  · exact (hL x (Finset.mem_univ _) (alive_of_succ hx)).2 hver
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hτ' with h | rfl
    · exact hC.shape τ' h q hq
    · exact (hL q (Finset.mem_univ _) hq).1.shape

/-- **Refinement.** At every time, the abstraction of the global state of a run of the
implementation is a reachable state of the abstract system of Fig. 1. -/
theorem absState_reachable (hm : Match cfg c) (hR : RunOK cfg R) (τ : ℕ) :
    Fig1.Reachable cfg (absState cfg c R τ) := by
  have : ∀ τ, Claim cfg c R τ := by
    intro τ
    induction τ with
    | zero => exact claim_zero
    | succ τ ih => exact claim_succ hm hR ih
  exact (this τ).reach

/-- Agreement of all decisions in a run of the implementation, given the abstract `Hyp`. -/
theorem agreement_of_hyp (hm : Match cfg c) (hR : RunOK cfg R) (hH : Fig1.Hyp cfg) {p q : P}
    {τ τ' : ℕ} {u v : V} (hp : (R.st (fig1 c) τ p).decided = some u)
    (hq : (R.st (fig1 c) τ' q).decided = some v) : u = v := by
  have hpr := absState_reachable hm hR τ
  have hqr := absState_reachable hm hR τ'
  obtain ⟨x, b, hx⟩ := (Fig1.basic_of_reachable hH.f_lt hpr).decided_msg p u hp
  obtain ⟨y, b', hy⟩ := (Fig1.basic_of_reachable hH.f_lt hqr).decided_msg q v hq
  have hT := absState_reachable hm hR (max τ τ')
  exact Fig1.agreement_msgs hH hT (absMsgs_mono (le_max_left τ τ') hx)
    (absMsgs_mono (le_max_right τ τ') hy)

end Simulation

/-! ### Agreement -/

/-- **Agreement of the task version** (Theorem 1, "if"): for `n ≥ 2f + 1`, `e ≤ f` and
`n ≥ 2e + f`. -/
theorem task_agreement' (c : Cfg P) (hobj : c.obj = false) (hn1 : 2 * c.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * c.e + c.f ≤ Fintype.card P) (hef : c.e ≤ c.f) : TaskAgreement (V := V) c := by
  intro R I hR hinv p q τ τ' v w hp hq
  let cfg : Fig1.Config P V := ⟨.task, c.e, c.f, c.owner, I, false⟩
  have hm : Match cfg c := ⟨rfl, rfl, rfl, Or.inl ⟨rfl, hobj, rfl⟩, by omega⟩
  exact agreement_of_hyp hm ⟨hR.ord_perm, Or.inl ⟨rfl, hinv⟩⟩ ⟨hn1, hef, Or.inl ⟨rfl, hn2⟩⟩ hp hq

/-- **Agreement of the object version** (Theorem 2, "if"; with the fix of lines 37–38): for
`n ≥ 2f + 1`, `e ≤ f` and `n ≥ 2e + f - 1`. -/
theorem object_agreement' (c : Cfg P) (hobj : c.obj = true) (hn1 : 2 * c.f + 1 ≤ Fintype.card P)
    (hn2 : 2 * c.e + c.f ≤ Fintype.card P + 1) (hef : c.e ≤ c.f) :
    ObjectAgreement (V := V) c := by
  intro R hR hwf p q τ τ' v w hp hq
  let cfg : Fig1.Config P V := ⟨.object, c.e, c.f, c.owner, fun _ => v, true⟩
  have hm : Match cfg c := ⟨rfl, rfl, rfl, Or.inr ⟨rfl, hobj, rfl⟩, by omega⟩
  exact agreement_of_hyp hm ⟨hR.ord_perm, Or.inr ⟨rfl, hwf⟩⟩ ⟨hn1, hef, Or.inr ⟨rfl, hn2⟩⟩
    hp.2 hq.2


/-! ### Theorems 1 and 2 -/

/-- **Theorem 1, "if" direction**: for `e ≤ f`, `n ≥ max (2e + f) (2f + 1)` and `n ≥ e + 2`,
the task version of Figure 1 with round-robin ballots is an `f`-resilient `e`-two-step
consensus task. -/
theorem theorem_1_upper [Nonempty P] (e f : ℕ) (hef : e ≤ f) (hn1 : 2 * f + 1 ≤ Fintype.card P)
    (hn2 : 2 * e + f ≤ Fintype.card P) (hn' : e + 2 ≤ Fintype.card P) :
    SolvesTask (fig1 (V := V) (⟨e, f, false, rrOwner⟩ : Cfg P)) f ∧
      TwoStepTask (fig1 (V := V) (⟨e, f, false, rrOwner⟩ : Cfg P)) e :=
  theorem_1_upper_of_agreement e f hn1 hn'
    (task_agreement' _ rfl hn1 hn2 hef)

/-- **Theorem 2, "if" direction**: for `e ≤ f`, `n ≥ max (2e + f - 1) (2f + 1)` and `n ≥ e + 2`,
the object version of Figure 1 (with our fix of lines 37–38) with round-robin ballots is an
`f`-resilient `e`-two-step consensus object. -/
theorem theorem_2_upper [Nonempty P] (e f : ℕ) (hef : e ≤ f) (hn1 : 2 * f + 1 ≤ Fintype.card P)
    (hn2 : 2 * e + f ≤ Fintype.card P + 1) (hn' : e + 2 ≤ Fintype.card P) :
    SolvesObject (fig1 (V := V) (⟨e, f, true, rrOwner⟩ : Cfg P)) f ∧
      TwoStepObject (fig1 (V := V) (⟨e, f, true, rrOwner⟩ : Cfg P)) e :=
  theorem_2_upper_of_agreement e f hn1 hn'
    (object_agreement' _ rfl hn1 hn2 hef)

end TwoStepConsensus.Impl

namespace TwoStepConsensus

open _root_.Cslib.CrashPartialSync

universe u v

/-- **Theorem 1** (Ryabinin–Gotsman–Sutra, PODC 2025): for `n ≥ 2` processes, at least two
values and `e ≤ f`, an `f`-resilient `e`-two-step consensus task is implementable iff
`n ≥ max (2e + f) (2f + 1)`. -/
theorem theorem_1 {P : Type u} {V : Type v} [Fintype P] [DecidableEq P] [LinearOrder V]
    {a b : V} (hab : a ≠ b) (hn : 2 ≤ Fintype.card P) {e f : ℕ} (hef : e ≤ f) :
    (∃ (M S : Type (max u v)) (A : Protocol P V M S), SolvesTask A f ∧ TwoStepTask A e) ↔
      2 * e + f ≤ Fintype.card P ∧ 2 * f + 1 ≤ Fintype.card P := by
  constructor
  · rintro ⟨M, S, A, hA, h2⟩
    exact theorem_1_lower hA h2 hab hn hef
  · rintro ⟨h1, h2⟩
    have : Nonempty P := Fintype.card_pos_iff.1 (by omega)
    have hn' : e + 2 ≤ Fintype.card P := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · omega
      · omega
    exact ⟨_, _, _, Impl.theorem_1_upper e f hef h2 h1 hn'⟩

/-- **Theorem 2** (Ryabinin–Gotsman–Sutra, PODC 2025; upper bound with our fix of the object
protocol): for `n ≥ 2` processes, at least two values and `e ≤ f`, an `f`-resilient
`e`-two-step consensus object is implementable iff `n ≥ max (2e + f - 1) (2f + 1)`. -/
theorem theorem_2 {P : Type u} {V : Type v} [Fintype P] [DecidableEq P] [LinearOrder V]
    {a b : V} (hab : a ≠ b) (hn : 2 ≤ Fintype.card P) {e f : ℕ} (hef : e ≤ f) :
    (∃ (M S : Type (max u v)) (A : Protocol P V M S), SolvesObject A f ∧ TwoStepObject A e) ↔
      2 * e + f ≤ Fintype.card P + 1 ∧ 2 * f + 1 ≤ Fintype.card P := by
  constructor
  · rintro ⟨M, S, A, hA, h2⟩
    exact theorem_2_lower hA h2 hab hn hef
  · rintro ⟨h1, h2⟩
    have : Nonempty P := Fintype.card_pos_iff.1 (by omega)
    have hn' : e + 2 ≤ Fintype.card P := by omega
    exact ⟨_, _, _, Impl.theorem_2_upper e f hef h2 h1 hn'⟩

end TwoStepConsensus
