import Mathlib
import Papers.PODC2015.SafetyLivenessExclusion.Abstract

/-!
# The shared-memory model of Section 2 (I/O automata with crashes)

Model of Bushkov–Guerraoui, PODC 2015, §2–3.

* `n` asynchronous processes `Fin n`; an object type is given by its invocations `Inv` and
  responses `Res` (the sequential specification plays no role in §3–4).
* External actions `Ext`: `inv i x`, `res i r`, `crash i` (the paper's `ext(Tp)`).
* Histories `Hist`: finite or infinite sequences of external actions. `U` is the set of
  *well-formed* histories: per process, invocations and responses alternate starting with an
  invocation, and nothing follows a crash.
* An implementation `Impl` is the composition `A_{I_1} × … × A_{I_n} × A_B` of the paper: a local
  state per process (or `none` once crashed — the special state `s_crashed,i`), a state of the
  base objects, and transitions
  - `inv i x`, `res i r`: input/output actions of `A_{I_i}`, touching only the local state of `i`;
  - `crash i`: always enabled unless `i` crashed, leads to the crashed state;
  - `step i`: an internal action of process `i` (local computation or an access to the base
    objects, i.e. a hidden action shared by `A_{I_i}` and `A_B`);
  - `base`: an internal action of `A_B` alone.
* Fair executions (§3.2): a finite execution is fair if no action other than a crash is enabled
  at its end; an infinite one is fair if every process either takes infinitely many actions or
  is infinitely often in a state where no action of it other than its crash is enabled.
* `fairH I`: histories of fair executions (`fair(A_I)`); `EnsuresS I S`: every finite history of
  `I` is in `S`.
* `Impl.Valid`: the paper's standing requirements — some initial state exists, every history is
  well-formed, and the implementation is input-enabled (an invocation by a process that is not
  pending is always enabled).
* `Impl.Reactive`: processes take steps only while executing an operation (no step of a process
  that is not pending). This is *not* required by the paper's I/O-automaton model; it is the
  hypothesis under which Theorem 4.9 holds (`Theorem49.lean`).
-/

namespace Podc.SafetyLivenessExclusion

/-! ## Finite or infinite sequences -/

/-- Finite or infinite sequences. -/
inductive Hist (α : Type) where
  | fin (l : List α)
  | inf (f : ℕ → α)

namespace Hist

variable {α : Type}

/-- The first `k` elements of an infinite sequence. -/
def pfx (f : ℕ → α) (k : ℕ) : List α := (List.range k).map f

@[simp] theorem length_pfx (f : ℕ → α) (k : ℕ) : (pfx f k).length = k := by simp [pfx]

@[simp] theorem getElem_pfx (f : ℕ → α) (k i : ℕ) (hi : i < (pfx f k).length) :
    (pfx f k)[i] = f i := by simp [pfx]

theorem pfx_succ (f : ℕ → α) (k : ℕ) : pfx f (k + 1) = pfx f k ++ [f k] := by
  simp [pfx, List.range_succ]

/-- `l` is a finite prefix of `h`. -/
def FinPrefix (l : List α) : Hist α → Prop
  | fin m => l <+: m
  | inf f => ∀ i (hi : i < l.length), l[i] = f i

theorem finPrefix_inf_iff {l : List α} {f : ℕ → α} :
    FinPrefix l (inf f) ↔ l = pfx f l.length := by
  constructor
  · intro h
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [h i h1]
  · intro h i hi
    rw [List.getElem_of_eq h hi]
    simp

theorem finPrefix_pfx (f : ℕ → α) (k : ℕ) : FinPrefix (pfx f k) (inf f) := by
  intro i hi; simp

theorem pfx_prefix {f : ℕ → α} {l : List α} (hl : FinPrefix l (inf f)) {m : ℕ}
    (hm : m ≤ l.length) : pfx f m <+: l := by
  rw [finPrefix_inf_iff] at hl
  rw [hl, List.prefix_iff_eq_take]
  simp [pfx, ← List.map_take, List.take_range, Nat.min_eq_left hm]

theorem FinPrefix.trans {l m : List α} {h : Hist α} (hlm : l <+: m) (hm : FinPrefix m h) :
    FinPrefix l h := by
  cases h with
  | fin k => exact hlm.trans hm
  | inf f =>
    intro i hi
    have hi' : i < m.length := lt_of_lt_of_le hi hlm.length_le
    rw [← hm i hi', hlm.getElem hi]

/-- `h` is the limit of the chain of finite sequences `p`. -/
def IsLim (p : ℕ → List α) : Hist α → Prop
  | fin l => ∃ K, ∀ k ≥ K, p k = l
  | inf f => (∀ k, FinPrefix (p k) (inf f)) ∧ ∀ m, ∃ k, m ≤ (p k).length

/-- A set of sequences is prefix-closed (contains the finite prefixes of its members). -/
def PrefixClosed (T : Set (Hist α)) : Prop := ∀ h ∈ T, ∀ l, FinPrefix l h → fin l ∈ T

/-- A set of sequences is limit-closed (contains every infinite sequence all of whose finite
prefixes it contains). -/
def LimitClosed (T : Set (Hist α)) : Prop := ∀ f, (∀ k, fin (pfx f k) ∈ T) → inf f ∈ T

/-- Definition 3.1: a safety property is a non-empty, prefix-closed and limit-closed set. -/
def IsSafety (T : Set (Hist α)) : Prop := T.Nonempty ∧ PrefixClosed T ∧ LimitClosed T

/-- If all members of a chain are in a prefix- and limit-closed set, so is its limit. -/
theorem IsLim.mem {p : ℕ → List α} {h : Hist α} (hlim : IsLim p h) {T : Set (Hist α)}
    (hP : PrefixClosed T) (hL : LimitClosed T) (hp : ∀ k, fin (p k) ∈ T) : h ∈ T := by
  cases h with
  | fin l =>
    obtain ⟨K, hK⟩ := hlim
    rw [← hK K le_rfl]; exact hp K
  | inf f =>
    apply hL
    intro m
    obtain ⟨k, hk⟩ := hlim.2 m
    exact hP _ (hp k) _ (pfx_prefix (hlim.1 k) hk)

/-- The safety closure of a predicate on finite sequences: all finite prefixes satisfy it. -/
def Safe (P : List α → Prop) : Set (Hist α) := {h | ∀ l, FinPrefix l h → P l}

theorem safe_prefixClosed (P : List α → Prop) : PrefixClosed (Safe P) :=
  fun _ hh _ hl m hm => hh m (FinPrefix.trans hm hl)

theorem safe_limitClosed (P : List α → Prop) : LimitClosed (Safe P) := by
  intro f hf l hl
  rw [finPrefix_inf_iff] at hl
  rw [hl]
  exact hf _ _ (List.prefix_refl _)

theorem fin_mem_safe {P : List α → Prop} {l : List α} :
    fin l ∈ Safe P ↔ ∀ m, m <+: l → P m := Iff.rfl

theorem safe_isSafety {P : List α → Prop} (h0 : P []) : IsSafety (Safe P) :=
  ⟨⟨fin [], fun l hl => by
    simp only [FinPrefix, List.prefix_nil] at hl; rw [hl]; exact h0⟩,
    safe_prefixClosed P, safe_limitClosed P⟩

end Hist

open Hist

/-! ## External actions and well-formed histories -/

/-- External actions of an object type with invocations `Inv` and responses `Res`
(the paper's `ext(Tp)`). -/
inductive Ext (n : ℕ) (Inv Res : Type) where
  | inv (i : Fin n) (x : Inv)
  | res (i : Fin n) (r : Res)
  | crash (i : Fin n)

variable {n : ℕ} {Inv Res : Type}

/-- The process of an external action. -/
def Ext.proc : Ext n Inv Res → Fin n
  | .inv i _ => i
  | .res i _ => i
  | .crash i => i

/-- Status of a process in a history. -/
inductive PStat where
  | idle
  | pend
  | dead
  deriving DecidableEq

/-- One step of the well-formedness monitor (`none` = not well-formed). -/
def stepStat (σ : Fin n → PStat) : Ext n Inv Res → Option (Fin n → PStat)
  | .inv i _ => if σ i = .idle then some (Function.update σ i .pend) else none
  | .res i _ => if σ i = .pend then some (Function.update σ i .idle) else none
  | .crash i => if σ i = .dead then none else some (Function.update σ i .dead)

/-- Status of all processes after a finite history (`none` if not well-formed). -/
def runStat (l : List (Ext n Inv Res)) : Option (Fin n → PStat) :=
  l.foldl (fun o e => o.bind (stepStat · e)) (some fun _ => .idle)

@[simp] theorem runStat_nil : runStat ([] : List (Ext n Inv Res)) = some fun _ => .idle := rfl

theorem runStat_append (l : List (Ext n Inv Res)) (e : Ext n Inv Res) :
    runStat (l ++ [e]) = (runStat l).bind (stepStat · e) := by
  simp [runStat, List.foldl_append]

/-- A finite history is well-formed. -/
def WF (l : List (Ext n Inv Res)) : Prop := (runStat l).isSome

/-- `U`: the well-formed (finite or infinite) histories. -/
def U : Set (Hist (Ext n Inv Res)) := Safe WF

theorem runStat_prefix {l m : List (Ext n Inv Res)} (h : l <+: m) (hm : WF m) : WF l := by
  obtain ⟨t, rfl⟩ := h
  induction t using List.reverseRecOn with
  | nil => simpa using hm
  | append_singleton t e ih =>
    apply ih
    rw [← List.append_assoc, WF, runStat_append] at hm
    cases h : runStat (l ++ t) with
    | none => simp [h] at hm
    | some _ => simp [WF, h]

theorem fin_mem_U {l : List (Ext n Inv Res)} : Hist.fin l ∈ U ↔ WF l :=
  ⟨fun h => h l (List.prefix_refl _), fun h _ hm => runStat_prefix hm h⟩

/-! ## Implementations -/

/-- An implementation `I = {I_1, …, I_n}` as the composition `A_{I_1} × … × A_{I_n} × A_B`.
All processes share the local-state type `Q`; `B` is the state of the base objects. -/
structure Impl (n : ℕ) (Inv Res : Type) where
  /-- Local states of the processes. -/
  Q : Type
  /-- States of the base objects (`A_B`). -/
  B : Type
  /-- Initial local states. -/
  initQ : Fin n → Q → Prop
  /-- Initial base-object states. -/
  initB : B → Prop
  /-- Transitions of `A_{I_i}` on `inv_i x`. -/
  invT : Fin n → Q → Inv → Q → Prop
  /-- Transitions of `A_{I_i}` on `res_i r`. -/
  resT : Fin n → Q → Res → Q → Prop
  /-- Internal steps of process `i` (local, or a hidden action shared with `A_B`). -/
  stepT : Fin n → Q → B → Q → B → Prop
  /-- Internal steps of `A_B` alone. -/
  baseT : B → B → Prop

/-- Actions of the composed automaton. -/
inductive Act (n : ℕ) (Inv Res : Type) where
  | ext (e : Ext n Inv Res)
  | step (i : Fin n)
  | base

/-- The external action of an action, if any. -/
def Act.ext? : Act n Inv Res → Option (Ext n Inv Res)
  | .ext e => some e
  | _ => none

/-- `a` is an action of `A_{I_i}`. -/
def Act.IsProc (i : Fin n) : Act n Inv Res → Prop
  | .ext e => e.proc = i
  | .step j => j = i
  | .base => False

/-- `a` is a crash action. -/
def Act.IsCrash : Act n Inv Res → Prop
  | .ext (.crash _) => True
  | _ => False

/-- The history of a finite sequence of actions. -/
def hist (as : List (Act n Inv Res)) : List (Ext n Inv Res) := as.filterMap Act.ext?

@[simp] theorem hist_nil : hist ([] : List (Act n Inv Res)) = [] := rfl
@[simp] theorem hist_cons_ext (e : Ext n Inv Res) (as : List (Act n Inv Res)) :
    hist (.ext e :: as) = e :: hist as := rfl
@[simp] theorem hist_cons_step (i : Fin n) (as : List (Act n Inv Res)) :
    hist (.step i :: as) = hist as := rfl
@[simp] theorem hist_cons_base (as : List (Act n Inv Res)) :
    hist (.base :: as) = hist as := rfl
@[simp] theorem hist_append (as bs : List (Act n Inv Res)) :
    hist (as ++ bs) = hist as ++ hist bs := by simp [hist]

namespace Impl

variable (I : Impl n Inv Res)

/-- States of the composed automaton: local states (`none` = crashed) and base objects. -/
structure Cfg where
  /-- Local state of each process; `none` is the crashed state. -/
  loc : Fin n → Option I.Q
  /-- State of the base objects. -/
  mem : I.B

/-- The transition relation of the composition. -/
inductive Trans : I.Cfg → Act n Inv Res → I.Cfg → Prop
  | inv {c : I.Cfg} {i : Fin n} {x : Inv} {q q' : I.Q} :
      c.loc i = some q → I.invT i q x q' →
      Trans c (.ext (.inv i x)) ⟨Function.update c.loc i (some q'), c.mem⟩
  | res {c : I.Cfg} {i : Fin n} {r : Res} {q q' : I.Q} :
      c.loc i = some q → I.resT i q r q' →
      Trans c (.ext (.res i r)) ⟨Function.update c.loc i (some q'), c.mem⟩
  | crash {c : I.Cfg} {i : Fin n} {q : I.Q} :
      c.loc i = some q → Trans c (.ext (.crash i)) ⟨Function.update c.loc i none, c.mem⟩
  | step {c : I.Cfg} {i : Fin n} {q q' : I.Q} {b' : I.B} :
      c.loc i = some q → I.stepT i q c.mem q' b' →
      Trans c (.step i) ⟨Function.update c.loc i (some q'), b'⟩
  | base {c : I.Cfg} {b' : I.B} : I.baseT c.mem b' → Trans c .base ⟨c.loc, b'⟩

/-- Initial states. -/
def IsInit (c : I.Cfg) : Prop := (∀ i, ∃ q, c.loc i = some q ∧ I.initQ i q) ∧ I.initB c.mem

/-- Finite runs. -/
inductive Run : I.Cfg → List (Act n Inv Res) → I.Cfg → Prop
  | nil (c : I.Cfg) : Run c [] c
  | cons {c c' c'' : I.Cfg} {a : Act n Inv Res} {as : List (Act n Inv Res)} :
      I.Trans c a c' → Run c' as c'' → Run c (a :: as) c''

variable {I}

theorem Run.append {c c' c'' : I.Cfg} {as bs : List (Act n Inv Res)} (h1 : I.Run c as c')
    (h2 : I.Run c' bs c'') : I.Run c (as ++ bs) c'' := by
  induction h1 with
  | nil => exact h2
  | cons ht _ ih => exact .cons ht (ih h2)

theorem Run.snoc {c c' c'' : I.Cfg} {as : List (Act n Inv Res)} {a : Act n Inv Res}
    (h1 : I.Run c as c') (h2 : I.Trans c' a c'') : I.Run c (as ++ [a]) c'' :=
  h1.append (.cons h2 (.nil _))

theorem Run.single {c c' : I.Cfg} {a : Act n Inv Res} (h : I.Trans c a c') :
    I.Run c [a] c' := .cons h (.nil _)

theorem Run.of_append {c c'' : I.Cfg} {as bs : List (Act n Inv Res)}
    (h : I.Run c (as ++ bs) c'') : ∃ c', I.Run c as c' ∧ I.Run c' bs c'' := by
  induction as generalizing c with
  | nil => exact ⟨c, .nil _, h⟩
  | cons a as ih =>
    cases h with
    | cons ht hr =>
      obtain ⟨c', h1, h2⟩ := ih hr
      exact ⟨c', .cons ht h1, h2⟩

variable (I)

/-- `c` is reachable by a finite execution with history `l`. -/
def Reach (c : I.Cfg) (l : List (Ext n Inv Res)) : Prop :=
  ∃ c₀ as, I.IsInit c₀ ∧ I.Run c₀ as c ∧ hist as = l

/-- `l` is a finite history of `A_I`. -/
def FinHist (l : List (Ext n Inv Res)) : Prop := ∃ c, I.Reach c l

/-- `a` is enabled at `c`. -/
def Enabled (c : I.Cfg) (a : Act n Inv Res) : Prop := ∃ c', I.Trans c a c'

/-- Some action of `A_{I_i}` other than `crash_i` is enabled at `c`. -/
def NonCrashEnabled (c : I.Cfg) (i : Fin n) : Prop :=
  ∃ a, a.IsProc i ∧ ¬ a.IsCrash ∧ I.Enabled c a

/-- A finite execution ending in `c` is fair iff no action other than a crash is enabled at `c`. -/
def FinFair (c : I.Cfg) : Prop := ∀ a c', I.Trans c a c' → a.IsCrash

/-- Infinite executions. -/
structure InfExec where
  /-- States. -/
  cfg : ℕ → I.Cfg
  /-- Actions. -/
  act : ℕ → Act n Inv Res
  init : I.IsInit (cfg 0)
  trans : ∀ k, I.Trans (cfg k) (act k) (cfg (k + 1))

variable {I}

/-- The first `k` actions of an infinite execution. -/
def InfExec.pre (e : I.InfExec) (k : ℕ) : List (Act n Inv Res) := (List.range k).map e.act

theorem InfExec.run_pre (e : I.InfExec) (k : ℕ) : I.Run (e.cfg 0) (e.pre k) (e.cfg k) := by
  induction k with
  | zero => exact .nil _
  | succ k ih =>
    have : e.pre (k + 1) = e.pre k ++ [e.act k] := by simp [InfExec.pre, List.range_succ]
    rw [this]
    exact ih.snoc (e.trans k)

/-- An infinite execution is fair: every process takes infinitely many actions, or is infinitely
often in a state where no action of it other than its crash is enabled. -/
def InfExec.Fair (e : I.InfExec) : Prop :=
  ∀ i, (∀ K, ∃ k ≥ K, (e.act k).IsProc i) ∨ (∀ K, ∃ k ≥ K, ¬ I.NonCrashEnabled (e.cfg k) i)

/-- The history of an infinite execution is the limit of the histories of its prefixes. -/
def InfExec.HasHist (e : I.InfExec) (h : Hist (Ext n Inv Res)) : Prop :=
  IsLim (fun k => hist (e.pre k)) h

variable (I)

/-- `fair(A_I)`: the histories of the fair executions of `A_I`. -/
def fairH : Set (Hist (Ext n Inv Res)) :=
  {h | (∃ c l, I.Reach c l ∧ I.FinFair c ∧ h = .fin l) ∨ ∃ e : I.InfExec, e.Fair ∧ e.HasHist h}

/-- `h` is a (finite or infinite) history of `A_I`. -/
def IsHistOf (h : Hist (Ext n Inv Res)) : Prop :=
  (∃ l, h = .fin l ∧ I.FinHist l) ∨ ∃ e : I.InfExec, e.HasHist h

/-- `I` ensures the safety property `S`: every finite history of `A_I` is in `S`. -/
def EnsuresS (S : Set (Hist (Ext n Inv Res))) : Prop := ∀ l, I.FinHist l → Hist.fin l ∈ S

/-- All histories of `A_I` are well-formed. -/
def WellFormed : Prop := ∀ l, I.FinHist l → WF l

/-- Input-enabledness: an invocation by a process that is not pending (and not crashed) is
enabled. We read "`p_i` is not pending at `s`" per execution: in the history of the execution
that reached `s`. -/
def InputEnabled : Prop :=
  ∀ c l, I.Reach c l → ∀ σ, runStat l = some σ → ∀ i, σ i = .idle → ∀ x,
    I.Enabled c (.ext (.inv i x))

/-- The paper's standing requirements on implementations. -/
def Valid : Prop := (∃ c, I.IsInit c) ∧ I.WellFormed ∧ I.InputEnabled

/-- Processes take steps only while they execute an operation (are pending). -/
def Reactive : Prop :=
  ∀ c l, I.Reach c l → ∀ σ, runStat l = some σ → ∀ i, σ i = .idle → ¬ I.Enabled c (.step i)

variable {I}

theorem Reach.run {c c' : I.Cfg} {l : List (Ext n Inv Res)} (hc : I.Reach c l)
    {as : List (Act n Inv Res)} (hr : I.Run c as c') : I.Reach c' (l ++ hist as) := by
  obtain ⟨c₀, bs, hi, hb, rfl⟩ := hc
  exact ⟨c₀, bs ++ as, hi, hb.append hr, by simp⟩

theorem Reach.trans {c c' : I.Cfg} {l : List (Ext n Inv Res)} (hc : I.Reach c l)
    {a : Act n Inv Res} (ht : I.Trans c a c') : I.Reach c' (l ++ hist [a]) :=
  hc.run (.single ht)

theorem InfExec.finHist_pre (e : I.InfExec) (k : ℕ) : I.FinHist (hist (e.pre k)) :=
  ⟨e.cfg k, e.cfg 0, e.pre k, e.init, e.run_pre k, rfl⟩

/-- Every history of `A_I` (finite or infinite) lies in every prefix- and limit-closed set
containing its finite histories. -/
theorem IsHistOf.mem {h : Hist (Ext n Inv Res)} (hh : I.IsHistOf h)
    {T : Set (Hist (Ext n Inv Res))} (hP : PrefixClosed T) (hL : LimitClosed T)
    (hT : ∀ l, I.FinHist l → Hist.fin l ∈ T) : h ∈ T := by
  rcases hh with ⟨l, rfl, hl⟩ | ⟨e, he⟩
  · exact hT l hl
  · exact IsLim.mem he hP hL fun k => hT _ (e.finHist_pre k)

theorem fairH_subset_isHistOf : I.fairH ⊆ {h | I.IsHistOf h} := by
  rintro h (⟨c, l, hc, -, rfl⟩ | ⟨e, -, he⟩)
  · exact Or.inl ⟨l, rfl, c, hc⟩
  · exact Or.inr ⟨e, he⟩

theorem fairH_subset_of {T : Set (Hist (Ext n Inv Res))} (hP : PrefixClosed T)
    (hL : LimitClosed T) (hT : ∀ l, I.FinHist l → Hist.fin l ∈ T) : I.fairH ⊆ T :=
  fun _ hh => IsHistOf.mem (fairH_subset_isHistOf hh) hP hL hT

/-- Fair histories of an implementation ensuring a safety property `S` are in `S`. -/
theorem fairH_subset_S {S : Set (Hist (Ext n Inv Res))} (hS : IsSafety S) (hI : I.EnsuresS S) :
    I.fairH ⊆ S := fairH_subset_of hS.2.1 hS.2.2 hI

/-- Fair histories of a well-formed implementation are well-formed. -/
theorem fairH_subset_U (hI : I.WellFormed) : I.fairH ⊆ U :=
  fairH_subset_of (safe_prefixClosed _) (safe_limitClosed _) fun l hl => fin_mem_U.2 (hI l hl)

end Impl

/-! ## The paper's standing assumptions and the abstract setting -/

/-- The standing assumptions of §3.1 on a safety property `S` w.r.t. a class `𝓒` of admissible
implementations: `S` is a safety property of well-formed histories; every invocation executed
alone from the initial state may receive some response; every history of `S` is a history of
some implementation of `𝓒` that ensures `S`. -/
structure SafetyAssumptions (𝓒 : Set (Impl n Inv Res)) (S : Set (Hist (Ext n Inv Res))) :
    Prop where
  isSafety : IsSafety S
  subset_U : S ⊆ U
  seq : ∀ i x, ∃ r, Hist.fin [Ext.inv i x, Ext.res i r] ∈ S
  impl : ∀ h ∈ S, ∃ I ∈ 𝓒, I.EnsuresS S ∧ I.IsHistOf h

/-- The assumption of §3.2 on `Lmax`: a set of well-formed histories such that every finite
well-formed history is a prefix of one of them. -/
structure LmaxAssumptions (Lmax : Set (Hist (Ext n Inv Res))) : Prop where
  subset_U : Lmax ⊆ U
  ext : ∀ l, WF l → ∃ h ∈ Lmax, FinPrefix l h

/-- The abstract setting of `Abstract.lean` for the model: implementations of the class `𝓒`. -/
def setting (𝓒 : Set (Impl n Inv Res)) (S Lmax : Set (Hist (Ext n Inv Res))) :
    Setting (Hist (Ext n Inv Res)) (Impl n Inv Res) where
  fair I := I.fairH
  ensS I := I ∈ 𝓒 ∧ I.EnsuresS S
  S := S
  Lmax := Lmax

theorem setting_fair_subset {𝓒 : Set (Impl n Inv Res)} {S Lmax : Set (Hist (Ext n Inv Res))}
    (hS : SafetyAssumptions 𝓒 S) :
    ∀ I, (setting 𝓒 S Lmax).ensS I → (setting 𝓒 S Lmax).fair I ⊆ (setting 𝓒 S Lmax).S :=
  fun _ hI => Impl.fairH_subset_S hS.isSafety hI.2

theorem setting_exists {𝓒 : Set (Impl n Inv Res)} {S Lmax : Set (Hist (Ext n Inv Res))}
    (hS : SafetyAssumptions 𝓒 S) : ∃ I, (setting 𝓒 S Lmax).ensS I := by
  obtain ⟨h, hh⟩ := hS.isSafety.1
  obtain ⟨I, hI, hIS, -⟩ := hS.impl h hh
  exact ⟨I, hI, hIS⟩

/-- **Theorem 4.4** in the model: for every class of implementations and every safety property
satisfying the paper's assumptions, a weakest liveness property excluding `S` exists iff `Gmax`
is an adversary set w.r.t. `Lmax` and `S`. -/
theorem theorem_4_4 (𝓒 : Set (Impl n Inv Res)) (S Lmax : Set (Hist (Ext n Inv Res)))
    (hS : SafetyAssumptions 𝓒 S) :
    (∃ L, (setting 𝓒 S Lmax).IsWeakestExcl L) ↔
      (setting 𝓒 S Lmax).Gmax ∈ (setting 𝓒 S Lmax).advSets :=
  Setting.theorem_4_4 _ (setting_fair_subset hS) (setting_exists hS)

end Podc.SafetyLivenessExclusion
