import Papers.PODC2015.SafetyLivenessExclusion.Theorem49

/-!
# Theorem 4.9 fails when processes may take steps while idle

In the paper's I/O-automaton model a process automaton `A_{I_i}` is arbitrary; nothing forbids
internal actions of a process that is not executing an operation. With such *idle steps* the
commutation claim of the proof of Theorem 4.9 ("because `A_{I'}` is input-enabled, every history
`h'` with a single response and `h'|p_i = inv_i · res_i` is a history of `A_{I'}`") is false, and
so is the theorem.

**The counterexample** (`n = 2`, one invocation `()` and one response `()`):

* Safety property `S` (`S`): a well-formed history is in `S` unless `p₀` receives a response after
  `p₁` crashed *before `p₀`'s first invocation and without ever having invoked*. It is prefix- and
  limit-closed, every invocation can be answered sequentially, and every history of `S` is a
  history of the implementation `Is` below, which ensures `S`.
* `Is` (`Is`): base objects are a counter and a flag. `p₁` increments the counter at every step,
  also while idle (a heartbeat), and sets the flag at the first step of each operation. On its
  first invocation `p₀` reads the counter and waits until the counter changes or the flag is set
  (evidence that `p₁` was alive after `p₀`'s invocation, or invoked); later invocations are
  answered at once.
* `h₀ = crash₁ · inv₀` is fair for *every* valid implementation ensuring `S`: after it no response
  to `p₀` can ever be given (`h0_mem_fairH`).
* With `Lmax = U \ {h₀}` (every finite well-formed history has an extension in it) the strongest
  liveness property not excluding `S` is `U ≠ Lmax` (`theorem_4_9_false`).

`CounterexampleWF.lean` upgrades this to `Lmax =` wait-freedom.
-/

namespace Podc.SafetyLivenessExclusion.Counterexample

open Hist Impl

/-- Events of the counterexample: two processes, one invocation, one response. -/
abbrev E := Ext 2 Unit Unit

/-! ## The safety property -/

/-- State of the monitor of `S`: process statuses, whether `p₀`/`p₁` invoked, and whether `p₁`
crashed before any invocation of `p₀` and `p₁` ("bad"). -/
structure MS where
  /-- Process statuses. -/
  σ : Fin 2 → PStat
  /-- `p₀` has invoked. -/
  s0 : Bool
  /-- `p₁` has invoked. -/
  s1 : Bool
  /-- `p₁` crashed before any invocation of `p₀` or `p₁`. -/
  bad : Bool

/-- One step of the monitor (`none`: the history leaves `S`). -/
def mstep (m : MS) : E → Option MS
  | .inv i _ => (stepStat m.σ (Ext.inv (Res := Unit) i ())).map fun σ' =>
      ⟨σ', m.s0 || decide (i = 0), m.s1 || decide (i = 1), m.bad⟩
  | .res i _ => if i = 0 ∧ m.bad = true then none else
      (stepStat m.σ (Ext.res (Inv := Unit) i ())).map fun σ' => ⟨σ', m.s0, m.s1, m.bad⟩
  | .crash i => (stepStat m.σ (Ext.crash (Inv := Unit) (Res := Unit) i)).map fun σ' =>
      ⟨σ', m.s0, m.s1, m.bad || (decide (i = 1) && !m.s0 && !m.s1)⟩

/-- Initial monitor state. -/
def m0 : MS := ⟨fun _ => .idle, false, false, false⟩

/-- The monitor on a finite history. -/
def runMon (l : List E) : Option MS := l.foldl (fun o e => o.bind (mstep · e)) (some m0)

/-- Finite histories accepted by the monitor. -/
def Good (l : List E) : Prop := (runMon l).isSome

instance : DecidablePred Good := fun l => inferInstanceAs (Decidable ((runMon l).isSome = true))

/-- The safety property `S` of the counterexample. -/
def S : Set (Hist E) := Safe Good

theorem runMon_append (l : List E) (e : E) :
    runMon (l ++ [e]) = (runMon l).bind (mstep · e) := by
  simp [runMon, List.foldl_append]

theorem runMon_append_eq_some {l : List E} {e : E} {m' : MS} :
    runMon (l ++ [e]) = some m' ↔ ∃ m, runMon l = some m ∧ mstep m e = some m' := by
  rw [runMon_append]; cases runMon l <;> simp

theorem mstep_σ {m m' : MS} {e : E} (h : mstep m e = some m') : stepStat m.σ e = some m'.σ := by
  cases e with
  | inv i x =>
    cases x; simp only [mstep, Option.map_eq_some_iff] at h
    obtain ⟨σ', h1, rfl⟩ := h; exact h1
  | res i r =>
    cases r; simp only [mstep] at h
    split_ifs at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨σ', h1, rfl⟩ := h; exact h1
  | crash i =>
    simp only [mstep, Option.map_eq_some_iff] at h
    obtain ⟨σ', h1, rfl⟩ := h; exact h1

theorem runMon_runStat {l : List E} {m : MS} (h : runMon l = some m) : runStat l = some m.σ := by
  induction l using List.reverseRecOn generalizing m with
  | nil => simp [runMon, m0] at h; subst h; rfl
  | append_singleton l e ih =>
    obtain ⟨m₁, h₁, h₂⟩ := runMon_append_eq_some.1 h
    rw [runStat_append, ih h₁]
    exact mstep_σ h₂

theorem Good.wf {l : List E} (h : Good l) : WF l := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 h
  simp [WF, runMon_runStat hm]

theorem Good.of_prefix {l l' : List E} (hl : l' <+: l) (h : Good l) : Good l' := by
  obtain ⟨t, rfl⟩ := hl
  induction t using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t e ih =>
    apply ih
    rw [← List.append_assoc, Good, runMon_append] at h
    cases hm : runMon (l' ++ t) with
    | none => simp [hm] at h
    | some _ => simp [Good, hm]

theorem fin_mem_S {l : List E} : Hist.fin l ∈ S ↔ Good l :=
  ⟨fun h => h l (List.prefix_refl _), fun h _ hm => Good.of_prefix hm h⟩

theorem S_isSafety : IsSafety S := safe_isSafety (by simp [Good, runMon])

theorem S_subset_U : S ⊆ U := fun _ hh l hl => (hh l hl).wf

theorem S_seq (i : Fin 2) (x : Unit) : ∃ r, Hist.fin [Ext.inv i x, Ext.res i r] ∈ S := by
  refine ⟨(), fin_mem_S.2 ?_⟩
  cases x
  fin_cases i <;> decide

/-- The history `crash₁ · inv₀`. -/
def h0 : List E := [.crash 1, .inv 0 ()]

theorem not_good_h0_res : ¬ Good (h0 ++ [.res 0 ()]) := by decide

/-! ## The implementation `Is` -/

/-- Local states of `Is`: `p₀` uses `w0 … done0`, `p₁` uses `h1, pend1, ready1`. -/
inductive HQ where
  /-- `p₀` never invoked. -/
  | w0
  /-- `p₀`'s first operation, before reading the counter. -/
  | wRead
  /-- `p₀`'s first operation, having read the counter value `v`. -/
  | wWait (v : ℕ)
  /-- `p₀` about to respond. -/
  | ready0
  /-- `p₀` idle after a response. -/
  | done0
  /-- `p₁` idle. -/
  | h1
  /-- `p₁` invoked, flag not yet set. -/
  | pend1
  /-- `p₁` about to respond. -/
  | ready1
  deriving DecidableEq

/-- The implementation `Is` (base objects: a counter and a flag). `p₁`'s idle step `h1 → h1` is
the heartbeat: a step of a process that is not executing an operation. The base objects have a
stuttering internal action (used only to pad executions). -/
abbrev Is : Impl 2 Unit Unit where
  Q := HQ
  B := ℕ × Bool
  initQ i q := (i = 0 ∧ q = .w0) ∨ (i = 1 ∧ q = .h1)
  initB b := b = (0, false)
  invT _ q _ q' := (q = .w0 ∧ q' = .wRead) ∨ (q = .done0 ∧ q' = .ready0) ∨ (q = .h1 ∧ q' = .pend1)
  resT _ q _ q' := (q = .ready0 ∧ q' = .done0) ∨ (q = .ready1 ∧ q' = .h1)
  stepT _ q b q' b' :=
    (q = .wRead ∧ b' = b ∧ ((b.2 = true ∧ q' = .ready0) ∨ (b.2 = false ∧ q' = .wWait b.1))) ∨
    (∃ v, q = .wWait v ∧ b' = b ∧ (b.2 = true ∨ b.1 ≠ v) ∧ q' = .ready0) ∨
    (q = .h1 ∧ q' = .h1 ∧ b' = (b.1 + 1, b.2)) ∨
    (q = .pend1 ∧ q' = .ready1 ∧ b' = (b.1 + 1, true))
  baseT b b' := b' = b

/-- Local states of `p₀` and their statuses. -/
def Fits0 : Option HQ → PStat → Prop
  | none, s => s = .dead
  | some .w0, s => s = .idle
  | some .done0, s => s = .idle
  | some .wRead, s => s = .pend
  | some (.wWait _), s => s = .pend
  | some .ready0, s => s = .pend
  | some _, _ => False

/-- Local states of `p₁` and their statuses. -/
def Fits1 : Option HQ → PStat → Prop
  | none, s => s = .dead
  | some .h1, s => s = .idle
  | some .pend1, s => s = .pend
  | some .ready1, s => s = .pend
  | some _, _ => False

/-- The invariant of `Is` relating the local states `l0, l1`, the base objects `b` and the monitor
state `m` of the history. -/
structure InvD (l0 l1 : Option HQ) (b : ℕ × Bool) (m : MS) : Prop where
  f0 : Fits0 l0 (m.σ 0)
  f1 : Fits1 l1 (m.σ 1)
  w0s : l0 = some .w0 → m.s0 = false
  s0w : m.s0 = false → l0 = some .w0 ∨ l0 = none
  flag : b.2 = true → m.s1 = true
  p1s : l1 = some .pend1 ∨ l1 = some .ready1 → m.s1 = true
  r1f : l1 = some .ready1 → b.2 = true
  wait : ∀ v, l0 = some (.wWait v) → v ≤ b.1 ∧ (v < b.1 → m.bad = false)
  rd : l0 = some .ready0 ∨ l0 = some .done0 → m.bad = false
  bad1 : m.bad = true → m.s1 = false ∧ m.σ 1 = .dead
  dead1 : m.σ 1 = .dead → m.bad = true ∨ m.s0 = true ∨ m.s1 = true

/-- The invariant on states. -/
abbrev Inv (c : Is.Cfg) (m : MS) : Prop := InvD (c.loc 0) (c.loc 1) c.mem m

theorem step0 {q q' : HQ} {l1 : Option HQ} {b b' : ℕ × Bool} {m : MS}
    (h : InvD (some q) l1 b m) (hs : Is.stepT 0 q b q' b') : InvD (some q') l1 b' m := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  rcases hs with ⟨rfl, rfl, (⟨hf, rfl⟩ | ⟨hf, rfl⟩)⟩ | ⟨v, rfl, rfl, hcond, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals first
    | (simp [Fits0] at f0; done)
    | (constructor <;> (try simp_all [Fits0, Fits1]))
  rcases hcond with h | h
  · cases hb : m.bad
    · rfl
    · simp_all
  · exact wait.2 (lt_of_le_of_ne wait.1 (Ne.symm h))

theorem step1 {q q' : HQ} {l0 : Option HQ} {b b' : ℕ × Bool} {m : MS}
    (h : InvD l0 (some q) b m) (hs : Is.stepT 1 q b q' b') : InvD l0 (some q') b' m := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  rcases hs with ⟨rfl, rfl, (⟨hf, rfl⟩ | ⟨hf, rfl⟩)⟩ | ⟨v, rfl, rfl, hcond, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals first
    | (simp [Fits1] at f1; done)
    | (constructor <;> (try simp_all [Fits0, Fits1]))
  all_goals exact fun v hv => Nat.le_succ_of_le (wait v hv)

theorem inv0 {q q' : HQ} {l1 : Option HQ} {b : ℕ × Bool} {m : MS}
    (h : InvD (some q) l1 b m) (ht : Is.invT 0 q () q') :
    mstep m (.inv 0 ()) = some ⟨Function.update m.σ 0 .pend, true, m.s1, m.bad⟩ ∧
      InvD (some q') l1 b ⟨Function.update m.σ 0 .pend, true, m.s1, m.bad⟩ := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | (simp [Fits0] at f0; done)
    | (simp only [Fits0] at f0
       refine ⟨by simp [mstep, stepStat, f0], ?_⟩
       constructor <;> (try simp_all [Fits0, Fits1]))


theorem inv1 {q q' : HQ} {l0 : Option HQ} {b : ℕ × Bool} {m : MS}
    (h : InvD l0 (some q) b m) (ht : Is.invT 1 q () q') :
    mstep m (.inv 1 ()) = some ⟨Function.update m.σ 1 .pend, m.s0, true, m.bad⟩ ∧
      InvD l0 (some q') b ⟨Function.update m.σ 1 .pend, m.s0, true, m.bad⟩ := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | (simp [Fits1] at f1; done)
    | (simp only [Fits1] at f1
       refine ⟨by simp [mstep, stepStat, f1], ?_⟩
       constructor <;> (try simp_all [Fits0, Fits1]))


theorem res0 {q q' : HQ} {l1 : Option HQ} {b : ℕ × Bool} {m : MS}
    (h : InvD (some q) l1 b m) (ht : Is.resT 0 q () q') :
    mstep m (.res 0 ()) = some ⟨Function.update m.σ 0 .idle, m.s0, m.s1, m.bad⟩ ∧
      InvD (some q') l1 b ⟨Function.update m.σ 0 .idle, m.s0, m.s1, m.bad⟩ := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | (simp [Fits0] at f0; done)
    | (simp only [Fits0] at f0
       refine ⟨by simp [mstep, stepStat, f0, rd], ?_⟩
       constructor <;> (try simp_all [Fits0, Fits1]))


theorem res1 {q q' : HQ} {l0 : Option HQ} {b : ℕ × Bool} {m : MS}
    (h : InvD l0 (some q) b m) (ht : Is.resT 1 q () q') :
    mstep m (.res 1 ()) = some ⟨Function.update m.σ 1 .idle, m.s0, m.s1, m.bad⟩ ∧
      InvD l0 (some q') b ⟨Function.update m.σ 1 .idle, m.s0, m.s1, m.bad⟩ := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | (simp [Fits1] at f1; done)
    | (simp only [Fits1] at f1
       refine ⟨by simp [mstep, stepStat, f1], ?_⟩
       constructor <;> (try simp_all [Fits0, Fits1]))


theorem crash0 {q : HQ} {l1 : Option HQ} {b : ℕ × Bool} {m : MS}
    (h : InvD (some q) l1 b m) :
    mstep m (.crash 0) = some ⟨Function.update m.σ 0 .dead, m.s0, m.s1, m.bad⟩ ∧
      InvD none l1 b ⟨Function.update m.σ 0 .dead, m.s0, m.s1, m.bad⟩ := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  have hd : m.σ 0 ≠ .dead := by cases q <;> simp_all [Fits0]
  refine ⟨by simp [mstep, stepStat, hd], ?_⟩
  constructor <;> (try simp_all [Fits0, Fits1])


theorem crash1 {q : HQ} {l0 : Option HQ} {b : ℕ × Bool} {m : MS}
    (h : InvD l0 (some q) b m) :
    mstep m (.crash 1) =
        some ⟨Function.update m.σ 1 .dead, m.s0, m.s1, m.bad || (!m.s0 && !m.s1)⟩ ∧
      InvD l0 none b ⟨Function.update m.σ 1 .dead, m.s0, m.s1, m.bad || (!m.s0 && !m.s1)⟩ := by
  obtain ⟨f0, f1, w0s, s0w, flag, p1s, r1f, wait, rd, bad1, dead1⟩ := h
  have hd : m.σ 1 ≠ .dead := by cases q <;> simp_all [Fits1]
  refine ⟨by simp [mstep, stepStat, hd], ?_⟩
  constructor <;> (try simp_all [Fits0, Fits1])
  · intro v hv _ h0; rcases s0w h0 with h | h <;> simp_all
  · intro hv h0; rcases s0w h0 with h | h <;> rcases hv with hv | hv <;> simp_all
  · cases m.s0 <;> cases m.s1 <;> simp

theorem upd01 {α : Type} (f : Fin 2 → α) (v : α) : Function.update f 0 v 1 = f 1 :=
  Function.update_of_ne (by decide) _ _

theorem upd10 {α : Type} (f : Fin 2 → α) (v : α) : Function.update f 1 v 0 = f 0 :=
  Function.update_of_ne (by decide) _ _

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

theorem init_loc {c : Is.Cfg} (hc : Is.IsInit c) :
    c.loc 0 = some .w0 ∧ c.loc 1 = some .h1 ∧ c.mem = (0, false) := by
  obtain ⟨q0, hq0, hq0'⟩ := hc.1 0
  obtain ⟨q1, hq1, hq1'⟩ := hc.1 1
  simp only [Fin.isValue, true_and, zero_ne_one, false_and, or_false] at hq0'
  simp only [Fin.isValue, one_ne_zero, false_and, true_and, false_or] at hq1'
  exact ⟨by rw [hq0, hq0'], by rw [hq1, hq1'], hc.2⟩

/-- Every reachable state of `Is` satisfies the invariant, and the monitor accepts its history. -/
theorem reach_inv {c : Is.Cfg} {l : List E} (hc : Is.Reach c l) :
    ∃ m, runMon l = some m ∧ Inv c m := by
  refine Reach.induct (P := fun c l => ∃ m, runMon l = some m ∧ Inv c m) ?_ ?_ hc
  · intro c hc
    obtain ⟨h0, h1, hb⟩ := init_loc hc
    refine ⟨m0, rfl, ?_⟩
    show InvD (c.loc 0) (c.loc 1) c.mem m0
    rw [h0, h1, hb]
    constructor <;> simp [m0, Fits0, Fits1]
  · rintro c l a c' - ⟨m, hm, hI⟩ ht
    cases ht with
    | @inv i x q q' hq ht =>
      cases x
      rcases fin2_cases i with rfl | rfl
      · have hI' : InvD (some q) (c.loc 1) c.mem m := by rw [← hq]; exact hI
        obtain ⟨h1, h2⟩ := inv0 hI' ht
        refine ⟨_, by rw [hist_single_ext, runMon_append, hm]; exact h1, ?_⟩
        show InvD (Function.update c.loc 0 (some q') 0) (Function.update c.loc 0 (some q') 1) _ _
        rw [Function.update_self, upd01]; exact h2
      · have hI' : InvD (c.loc 0) (some q) c.mem m := by rw [← hq]; exact hI
        obtain ⟨h1, h2⟩ := inv1 hI' ht
        refine ⟨_, by rw [hist_single_ext, runMon_append, hm]; exact h1, ?_⟩
        show InvD (Function.update c.loc 1 (some q') 0) (Function.update c.loc 1 (some q') 1) _ _
        rw [Function.update_self, upd10]; exact h2
    | @res i r q q' hq ht =>
      cases r
      rcases fin2_cases i with rfl | rfl
      · have hI' : InvD (some q) (c.loc 1) c.mem m := by rw [← hq]; exact hI
        obtain ⟨h1, h2⟩ := res0 hI' ht
        refine ⟨_, by rw [hist_single_ext, runMon_append, hm]; exact h1, ?_⟩
        show InvD (Function.update c.loc 0 (some q') 0) (Function.update c.loc 0 (some q') 1) _ _
        rw [Function.update_self, upd01]; exact h2
      · have hI' : InvD (c.loc 0) (some q) c.mem m := by rw [← hq]; exact hI
        obtain ⟨h1, h2⟩ := res1 hI' ht
        refine ⟨_, by rw [hist_single_ext, runMon_append, hm]; exact h1, ?_⟩
        show InvD (Function.update c.loc 1 (some q') 0) (Function.update c.loc 1 (some q') 1) _ _
        rw [Function.update_self, upd10]; exact h2
    | @crash i q hq =>
      rcases fin2_cases i with rfl | rfl
      · have hI' : InvD (some q) (c.loc 1) c.mem m := by rw [← hq]; exact hI
        obtain ⟨h1, h2⟩ := crash0 hI'
        refine ⟨_, by rw [hist_single_ext, runMon_append, hm]; exact h1, ?_⟩
        show InvD (Function.update c.loc 0 none 0) (Function.update c.loc 0 none 1) _ _
        rw [Function.update_self, upd01]; exact h2
      · have hI' : InvD (c.loc 0) (some q) c.mem m := by rw [← hq]; exact hI
        obtain ⟨h1, h2⟩ := crash1 hI'
        refine ⟨_, by rw [hist_single_ext, runMon_append, hm]; exact h1, ?_⟩
        show InvD (Function.update c.loc 1 none 0) (Function.update c.loc 1 none 1) _ _
        rw [Function.update_self, upd10]; exact h2
    | @step i q q' b' hq hs =>
      refine ⟨m, by simpa using hm, ?_⟩
      rcases fin2_cases i with rfl | rfl
      · have hI' : InvD (some q) (c.loc 1) c.mem m := by rw [← hq]; exact hI
        show InvD (Function.update c.loc 0 (some q') 0) (Function.update c.loc 0 (some q') 1) _ _
        rw [Function.update_self, upd01]; exact step0 hI' hs
      · have hI' : InvD (c.loc 0) (some q) c.mem m := by rw [← hq]; exact hI
        show InvD (Function.update c.loc 1 (some q') 0) (Function.update c.loc 1 (some q') 1) _ _
        rw [Function.update_self, upd10]; exact step1 hI' hs
    | @base b' hb =>
      refine ⟨m, by simpa using hm, ?_⟩
      have : b' = c.mem := hb
      subst this; exact hI

/-- `Is` ensures `S`. -/
theorem Is_ensuresS : Is.EnsuresS S := by
  rintro l ⟨c, hc⟩
  obtain ⟨m, hm, -⟩ := reach_inv hc
  exact fin_mem_S.2 (by simp [Good, hm])

/-- `Is` is a valid implementation (it is not reactive: `p₁` steps while idle). -/
theorem Is_valid : Is.Valid := by
  refine ⟨⟨⟨fun i => if i = 0 then some .w0 else some .h1, (0, false)⟩, fun i => ?_, rfl⟩, ?_, ?_⟩
  · rcases fin2_cases i with rfl | rfl
    · exact ⟨_, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · rintro l ⟨c, hc⟩
    obtain ⟨m, hm, -⟩ := reach_inv hc
    simp [WF, runMon_runStat hm]
  · intro c l hc σ hσ i hi x
    cases x
    obtain ⟨m, hm, hI⟩ := reach_inv hc
    rw [runMon_runStat hm] at hσ; cases hσ
    rcases fin2_cases i with rfl | rfl
    · have := hI.f0
      rw [hi] at this
      rcases h : c.loc 0 with _ | q
      · rw [h] at this; cases this
      · rw [h] at this
        cases q <;> simp [Fits0] at this
        · exact ⟨_, .inv h (Or.inl ⟨rfl, rfl⟩)⟩
        · exact ⟨_, .inv h (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · have := hI.f1
      rw [hi] at this
      rcases h : c.loc 1 with _ | q
      · rw [h] at this; cases this
      · rw [h] at this
        cases q <;> simp [Fits1] at this
        exact ⟨_, .inv h (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-! ## Every history of `S` is a history of `Is` -/

/-- A state of `Is` from the local states of `p₀`, `p₁` and the base objects. -/
def mk (l0 l1 : Option HQ) (b : ℕ × Bool) : Is.Cfg := ⟨fun i => if i = 0 then l0 else l1, b⟩

@[simp] theorem mk_loc0 (l0 l1 : Option HQ) (b : ℕ × Bool) : (mk l0 l1 b).loc 0 = l0 := rfl
@[simp] theorem mk_loc1 (l0 l1 : Option HQ) (b : ℕ × Bool) : (mk l0 l1 b).loc 1 = l1 := rfl
@[simp] theorem mk_mem (l0 l1 : Option HQ) (b : ℕ × Bool) : (mk l0 l1 b).mem = b := rfl

theorem mk_eta (c : Is.Cfg) : mk (c.loc 0) (c.loc 1) c.mem = c := by
  obtain ⟨loc, mem⟩ := c
  simp only [mk, Impl.Cfg.mk.injEq, and_true]
  funext i
  rcases fin2_cases i with rfl | rfl <;> rfl

theorem upd0 (l0 l1 v : Option HQ) (b : ℕ × Bool) :
    Function.update (mk l0 l1 b).loc 0 v = (mk v l1 b).loc := by
  funext i; rcases fin2_cases i with rfl | rfl <;> rfl

theorem upd1 (l0 l1 v : Option HQ) (b : ℕ × Bool) :
    Function.update (mk l0 l1 b).loc 1 v = (mk l0 v b).loc := by
  funext i; rcases fin2_cases i with rfl | rfl <;> rfl

section trans
variable {q q' : HQ} {l0 l1 : Option HQ} {b b' : ℕ × Bool}

theorem tinv0 (h : Is.invT 0 q () q') :
    Is.Trans (mk (some q) l1 b) (.ext (.inv 0 ())) (mk (some q') l1 b) := by
  have := Impl.Trans.inv (I := Is) (c := mk (some q) l1 b) (i := 0) (x := ()) rfl h
  rwa [upd0] at this

theorem tinv1 (h : Is.invT 1 q () q') :
    Is.Trans (mk l0 (some q) b) (.ext (.inv 1 ())) (mk l0 (some q') b) := by
  have := Impl.Trans.inv (I := Is) (c := mk l0 (some q) b) (i := 1) (x := ()) rfl h
  rwa [upd1] at this

theorem tres0 (h : Is.resT 0 q () q') :
    Is.Trans (mk (some q) l1 b) (.ext (.res 0 ())) (mk (some q') l1 b) := by
  have := Impl.Trans.res (I := Is) (c := mk (some q) l1 b) (i := 0) (r := ()) rfl h
  rwa [upd0] at this

theorem tres1 (h : Is.resT 1 q () q') :
    Is.Trans (mk l0 (some q) b) (.ext (.res 1 ())) (mk l0 (some q') b) := by
  have := Impl.Trans.res (I := Is) (c := mk l0 (some q) b) (i := 1) (r := ()) rfl h
  rwa [upd1] at this

theorem tcrash0 : Is.Trans (mk (some q) l1 b) (.ext (.crash 0)) (mk none l1 b) := by
  have := Impl.Trans.crash (I := Is) (c := mk (some q) l1 b) (i := 0) rfl
  rwa [upd0] at this

theorem tcrash1 : Is.Trans (mk l0 (some q) b) (.ext (.crash 1)) (mk l0 none b) := by
  have := Impl.Trans.crash (I := Is) (c := mk l0 (some q) b) (i := 1) rfl
  rwa [upd1] at this

theorem tstep0 (h : Is.stepT 0 q b q' b') :
    Is.Trans (mk (some q) l1 b) (.step 0) (mk (some q') l1 b') := by
  have := Impl.Trans.step (I := Is) (c := mk (some q) l1 b) (i := 0) rfl h
  rwa [upd0] at this

theorem tstep1 (h : Is.stepT 1 q b q' b') :
    Is.Trans (mk l0 (some q) b) (.step 1) (mk l0 (some q') b') := by
  have := Impl.Trans.step (I := Is) (c := mk l0 (some q) b) (i := 1) rfl h
  rwa [upd1] at this

theorem tbase : Is.Trans (mk l0 l1 b) .base (mk l0 l1 b) :=
  Impl.Trans.base (I := Is) (c := mk l0 l1 b) (b' := b) rfl

end trans

/-- The invariant of the driver: no process is in the middle of a step sequence, the flag is set
as soon as `p₁` invoked, and if `S` still allows a response to `p₀`, one step of `p₀` suffices. -/
structure DInvD (l0 l1 : Option HQ) (b : ℕ × Bool) (m : MS) : Prop where
  inv : InvD l0 l1 b m
  nr : l0 ≠ some .wRead
  np : l1 ≠ some .pend1
  sf : m.s1 = true → b.2 = true
  ww : ∀ v, l0 = some (.wWait v) → m.bad = false → b.2 = true ∨ v < b.1

theorem dinv_init : DInvD (some .w0) (some .h1) (0, false) m0 := by
  refine ⟨?_, by simp, by simp, by simp [m0], by simp⟩
  constructor <;> simp [m0, Fits0, Fits1]

/-- One block of the driver: three actions producing the next event of a history of `S`. -/
theorem drive {l0 l1 : Option HQ} {b : ℕ × Bool} {m m' : MS} {e : E} (hD : DInvD l0 l1 b m)
    (hm : mstep m e = some m') :
    ∃ a₀ a₁ a₂ c₁ c₂ l0' l1' b', Is.Trans (mk l0 l1 b) a₀ c₁ ∧ Is.Trans c₁ a₁ c₂ ∧
      Is.Trans c₂ a₂ (mk l0' l1' b') ∧ hist [a₀, a₁, a₂] = [e] ∧ DInvD l0' l1' b' m' := by
  obtain ⟨hI, nr, np, sf, ww⟩ := hD
  have hσ := mstep_σ hm
  cases e with
  | inv i x =>
    cases x
    rcases fin2_cases i with rfl | rfl
    · have hi := (stepStat_inv.1 hσ).1
      have f0 := hI.f0
      rw [hi] at f0
      rcases l0 with _ | q
      · simp [Fits0] at f0
      cases q <;> simp [Fits0] at f0
      · -- first invocation of `p₀`
        obtain ⟨h1, h2⟩ := inv0 hI (Or.inl ⟨rfl, rfl⟩)
        rw [h1] at hm; cases hm
        let q2 : HQ := if b.2 then .ready0 else .wWait b.1
        have hs2 : Is.stepT 0 .wRead b q2 b := by
          left; refine ⟨rfl, rfl, ?_⟩
          cases hb : b.2
          · right; simp [q2, hb]
          · left; simp [q2, hb]
        have h3 := step0 h2 hs2
        by_cases hl1 : l1 = some .h1
        · subst hl1
          have hs3 : Is.stepT 1 .h1 b .h1 (b.1 + 1, b.2) := Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
          refine ⟨_, _, _, _, _, some q2, some .h1, (b.1 + 1, b.2), tinv0 (Or.inl ⟨rfl, rfl⟩),
            tstep0 hs2, tstep1 hs3, rfl, step1 h3 hs3, ?_, by simp, by simpa using sf, ?_⟩
          · simp only [q2]; split_ifs <;> simp
          · intro v hv _
            simp only [q2] at hv
            split_ifs at hv with hb
            · simp at hv
            · simp at hv; subst hv; right; simp
        · refine ⟨_, _, _, _, _, some q2, l1, b, tinv0 (Or.inl ⟨rfl, rfl⟩),
            tstep0 hs2, tbase, rfl, h3, ?_, np, by simpa using sf, ?_⟩
          · simp only [q2]; split_ifs <;> simp
          · intro v hv hbad
            simp only [q2] at hv
            split_ifs at hv with hb
            · simp at hv
            · exfalso
              have hs0 := hI.w0s rfl
              have f1 := hI.f1
              rcases l1 with _ | q1
              · simp only [Fits1] at f1
                rcases hI.dead1 f1 with h | h | h
                · simp_all
                · simp_all
                · exact hb (sf h)
              · cases q1 <;> simp_all [Fits1]
                have := hI.r1f rfl; simp_all
      · -- a later invocation of `p₀`
        obtain ⟨h1, h2⟩ := inv0 hI (Or.inr (Or.inl ⟨rfl, rfl⟩))
        rw [h1] at hm; cases hm
        refine ⟨_, _, _, _, _, some .ready0, l1, b, tinv0 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
          tbase, tbase, rfl, h2, by simp, np, by simpa using sf, by simp⟩
    · have hi := (stepStat_inv.1 hσ).1
      have f1 := hI.f1
      rw [hi] at f1
      rcases l1 with _ | q
      · simp [Fits1] at f1
      cases q <;> simp [Fits1] at f1
      obtain ⟨h1, h2⟩ := inv1 hI (Or.inr (Or.inr ⟨rfl, rfl⟩))
      rw [h1] at hm; cases hm
      have hs3 : Is.stepT 1 .pend1 b .ready1 (b.1 + 1, true) :=
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
      refine ⟨_, _, _, _, _, l0, some .ready1, (b.1 + 1, true),
        tinv1 (Or.inr (Or.inr ⟨rfl, rfl⟩)), tstep1 hs3, tbase, rfl, step1 h2 hs3, nr, by simp,
        by simp, by simp⟩
  | res i r =>
    cases r
    rcases fin2_cases i with rfl | rfl
    · have hi := (stepStat_res.1 hσ).1
      have hbad : m.bad = false := by
        cases h : m.bad
        · rfl
        · simp [mstep, h] at hm
      have f0 := hI.f0
      rw [hi] at f0
      rcases l0 with _ | q
      · simp [Fits0] at f0
      cases q <;> simp [Fits0] at f0
      · exact absurd rfl nr
      · -- `p₀` waits: one step makes it ready
        rename_i v
        have hs : Is.stepT 0 (.wWait v) b .ready0 b := by
          right; left
          refine ⟨v, rfl, rfl, ?_, rfl⟩
          rcases ww v rfl hbad with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        have h2 := step0 hI hs
        obtain ⟨h3, h4⟩ := res0 h2 (Or.inl ⟨rfl, rfl⟩)
        rw [h3] at hm; cases hm
        refine ⟨_, _, _, _, _, some .done0, l1, b, tstep0 hs, tbase,
          tres0 (Or.inl ⟨rfl, rfl⟩), rfl, h4, by simp, np, by simpa using sf, by simp⟩
      · obtain ⟨h3, h4⟩ := res0 hI (Or.inl ⟨rfl, rfl⟩)
        rw [h3] at hm; cases hm
        refine ⟨_, _, _, _, _, some .done0, l1, b, tbase, tbase,
          tres0 (Or.inl ⟨rfl, rfl⟩), rfl, h4, by simp, np, by simpa using sf, by simp⟩
    · have hi := (stepStat_res.1 hσ).1
      have f1 := hI.f1
      rw [hi] at f1
      rcases l1 with _ | q
      · simp [Fits1] at f1
      cases q <;> simp [Fits1] at f1
      · exact absurd rfl np
      · obtain ⟨h3, h4⟩ := res1 hI (Or.inr ⟨rfl, rfl⟩)
        rw [h3] at hm; cases hm
        refine ⟨_, _, _, _, _, l0, some .h1, b, tbase, tbase,
          tres1 (Or.inr ⟨rfl, rfl⟩), rfl, h4, nr, by simp, by simpa using sf, ?_⟩
        intro v hv hbad; exact ww v hv hbad
  | crash i =>
    rcases fin2_cases i with rfl | rfl
    · rcases l0 with _ | q
      · have := (stepStat_crash.1 hσ).1
        have f0 := hI.f0; simp only [Fits0] at f0; exact absurd f0 this
      obtain ⟨h3, h4⟩ := crash0 hI
      rw [h3] at hm; cases hm
      exact ⟨_, _, _, _, _, none, l1, b, tbase, tbase, tcrash0, rfl, h4, by simp, np,
        by simpa using sf, by simp⟩
    · rcases l1 with _ | q
      · have := (stepStat_crash.1 hσ).1
        have f1 := hI.f1; simp only [Fits1] at f1; exact absurd f1 this
      obtain ⟨h3, h4⟩ := crash1 hI
      rw [h3] at hm; cases hm
      refine ⟨_, _, _, _, _, l0, none, b, tbase, tbase, tcrash1, rfl, h4, nr, by simp,
        by simpa using sf, ?_⟩
      intro v hv hbad
      simp only [Bool.or_eq_false_iff] at hbad
      exact ww v hv hbad.1

theorem mk_init : Is.IsInit (mk (some .w0) (some .h1) (0, false)) :=
  ⟨fun i => by
    rcases fin2_cases i with rfl | rfl
    · exact ⟨_, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩

theorem run3 {c c₁ c₂ c₃ : Is.Cfg} {a₀ a₁ a₂ : Act 2 Unit Unit} (h₀ : Is.Trans c a₀ c₁)
    (h₁ : Is.Trans c₁ a₁ c₂) (h₂ : Is.Trans c₂ a₂ c₃) : Is.Run c [a₀, a₁, a₂] c₃ :=
  .cons h₀ (.cons h₁ (.cons h₂ (.nil _)))

/-- Every finite history of `S` is a history of `Is`, reached in a driver state. -/
theorem good_reach {l : List E} (h : Good l) :
    ∃ l0 l1 b m, Is.Reach (mk l0 l1 b) l ∧ runMon l = some m ∧ DInvD l0 l1 b m := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨_, _, _, m0, Reach.init mk_init, rfl, dinv_init⟩
  | append_singleton l e ih =>
    obtain ⟨l0, l1, b, m, hr, hm, hD⟩ := ih (Good.of_prefix (List.prefix_append _ _) h)
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨m₁, hm₁, hstep⟩ := runMon_append_eq_some.1 hm'
    rw [hm] at hm₁; cases hm₁
    obtain ⟨a₀, a₁, a₂, c₁, c₂, l0', l1', b', h₀, h₁, h₂, hh, hD'⟩ := drive hD hstep
    exact ⟨l0', l1', b', m', by simpa [hh] using hr.run (run3 h₀ h₁ h₂), hm', hD'⟩

/-- Every history of `S` (finite or infinite) is a history of `Is`. -/
theorem S_isHistOf {h : Hist E} (hh : h ∈ S) : Is.IsHistOf h := by
  cases h with
  | fin l =>
    obtain ⟨l0, l1, b, m, hr, -, -⟩ := good_reach (fin_mem_S.1 hh)
    exact Or.inl ⟨l, rfl, _, hr⟩
  | inf f =>
    right
    have hg : ∀ k, Good (pfx f k) := fun k => hh _ (finPrefix_pfx f k)
    refine exists_infExec_of_blocks (P := fun k c => ∃ l0 l1 b m, c = mk l0 l1 b ∧
      runMon (pfx f k) = some m ∧ DInvD l0 l1 b m) mk_init ⟨_, _, _, m0, rfl, rfl, dinv_init⟩ ?_
    rintro k c ⟨l0, l1, b, m, rfl, hm, hD⟩
    obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 (hg (k + 1))
    rw [pfx_succ] at hm'
    obtain ⟨m₁, hm₁, hstep⟩ := runMon_append_eq_some.1 hm'
    rw [hm] at hm₁; cases hm₁
    obtain ⟨a₀, a₁, a₂, c₁, c₂, l0', l1', b', h₀, h₁, h₂, hh, hD'⟩ := drive hD hstep
    exact ⟨a₀, a₁, a₂, c₁, c₂, _, h₀, h₁, h₂, hh, l0', l1', b', m', rfl,
      by rw [pfx_succ]; exact hm', hD'⟩

/-! ## `crash₁ · inv₀` is fair for every implementation ensuring `S` -/

theorem not_good_h0 (e : E) (he : ¬ (Act.ext e).IsCrash) : ¬ Good (h0 ++ [e]) := by
  cases e with
  | inv i x => cases x; rcases fin2_cases i with rfl | rfl <;> decide
  | res i r => cases r; rcases fin2_cases i with rfl | rfl <;> decide
  | crash i => exact absurd trivial he

/-- From a state reached with history `crash₁ · inv₀`, no external action other than a crash and
no step of `p₁` is ever enabled, in any valid implementation ensuring `S`. -/
theorem quiet_h0 {I : Impl 2 Unit Unit} (hS : I.EnsuresS S) {c : I.Cfg} (hc : I.Reach c h0) :
    ∀ d as, I.Run c as d → hist as = [] →
      (∀ e : E, ¬ (Act.ext e).IsCrash → ¬ I.Enabled d (.ext e)) ∧
        ∀ j, j ≠ 0 → ¬ I.Enabled d (.step j) := by
  intro d as hrun has
  have hreach : I.Reach d h0 := by simpa [has] using hc.run hrun
  refine ⟨fun e he ⟨d', ht⟩ => ?_, fun j hj ⟨d', ht⟩ => ?_⟩
  · have hreach' : I.Reach d' (h0 ++ [e]) := by simpa using hreach.trans ht
    exact not_good_h0 e he (fin_mem_S.1 (hS _ ⟨_, hreach'⟩))
  · have hj1 : j = 1 := (fin2_cases j).resolve_left hj
    subst hj1
    have hσ : runStat h0 = some (Function.update (Function.update (fun _ => PStat.idle) 1 .dead)
        0 .pend) := by decide
    have hnone := (hreach.loc_eq_none_iff hσ 1).2 (by decide)
    have := ht.loc_isSome (j := 1) rfl
    rw [hnone] at this; cases this

/-- After `crash₁ · inv₀`, no implementation ensuring `S` can ever answer `p₀`: the history is
fair for every valid implementation ensuring `S`. -/
theorem h0_mem_fairH {I : Impl 2 Unit Unit} (hV : I.Valid) (hS : I.EnsuresS S) :
    Hist.fin h0 ∈ I.fairH := by
  obtain ⟨c₀, hc₀⟩ := hV.1
  obtain ⟨q₁, hq₁, -⟩ := hc₀.1 1
  have hr₀ := Reach.init hc₀
  have ht₁ : I.Trans c₀ (.ext (.crash 1)) _ := .crash hq₁
  have hr₁ : I.Reach ⟨Function.update c₀.loc 1 none, c₀.mem⟩
      [Ext.crash (Inv := Unit) (Res := Unit) (1 : Fin 2)] := by
    simpa using hr₀.trans ht₁
  obtain ⟨c₂, ht₂⟩ := hV.2.2 _ _ hr₁ (Function.update (fun _ => .idle) 1 .dead) rfl 0 rfl ()
  have hr₂ : I.Reach c₂ h0 := by simpa [h0] using hr₁.trans ht₂
  exact fin_mem_fairH_of_quiet hr₂ 0 (quiet_h0 hS hr₂)

/-! ## The counterexample -/

/-- The strongest liveness requirement of the counterexample: all well-formed histories except
`crash₁ · inv₀`. -/
def Lmax₀ : Set (Hist E) := U \ {Hist.fin h0}

theorem S_assumptions : SafetyAssumptions {I : Impl 2 Unit Unit | I.Valid} S where
  isSafety := S_isSafety
  subset_U := S_subset_U
  seq := S_seq
  impl _ hh := ⟨Is, Is_valid, Is_ensuresS, S_isHistOf hh⟩

theorem Lmax₀_assumptions : LmaxAssumptions Lmax₀ where
  subset_U := Set.sdiff_subset
  ext l hl := by
    by_cases hl0 : l = h0
    · subst hl0
      refine ⟨Hist.fin (h0 ++ [.crash 0]), ⟨fin_mem_U.2 (show (runStat _).isSome = true by decide), ?_⟩,
        List.prefix_append _ _⟩
      simp [h0]
    · exact ⟨Hist.fin l, ⟨fin_mem_U.2 hl, by simpa using hl0⟩, List.prefix_refl _⟩

/-- **Theorem 4.9 is false** in the paper's model (processes may take steps while idle): there
are a safety property `S` and a strongest liveness requirement `Lmax`, both satisfying all the
paper's assumptions, such that a strongest liveness property not excluding `S` exists but is
not `Lmax`. -/
theorem theorem_4_9_false :
    ∃ (S Lmax : Set (Hist (Ext 2 Unit Unit))),
      SafetyAssumptions {I : Impl 2 Unit Unit | I.Valid} S ∧ LmaxAssumptions Lmax ∧
      (∃ L, (setting {I : Impl 2 Unit Unit | I.Valid} S Lmax).IsStrongestNonExcl L) ∧
      ∀ L, (setting {I : Impl 2 Unit Unit | I.Valid} S Lmax).IsStrongestNonExcl L → L ≠ Lmax := by
  refine ⟨S, Lmax₀, S_assumptions, Lmax₀_assumptions, ?_, ?_⟩
  · rw [Setting.exists_isStrongestNonExcl_iff]
    refine ⟨Is, ⟨Is_valid, Is_ensuresS⟩, fun h hh => ?_⟩
    by_cases hh0 : h = Hist.fin h0
    · subst hh0
      exact Or.inr fun I hI => h0_mem_fairH hI.1 hI.2
    · exact Or.inl ⟨fairH_subset_U Is_valid.2.1 hh, hh0⟩
  · intro L hL hLeq
    have hL' := ((Setting.isStrongestNonExcl_iff _ L).1 hL).1
    have : Hist.fin h0 ∈ L := by
      rw [hL']
      exact Or.inr fun I hI => h0_mem_fairH hI.1 hI.2
    rw [hLeq] at this
    exact this.2 rfl
