import Mathlib.Data.ENat.Basic
import Mathlib.Logic.Function.Basic
import Podc.Computability.Distributed.SharedMemory.Persistent.StrictLin

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Persistent/Model.lean

/-!
# Persistent memory behind a volatile write-back cache, with wear-out

A model of concurrent objects implemented from `k` words of *persistent memory* accessed through
a *volatile write-back cache*, with system-wide crashes and memory-cell *wear-out* (Liu–Golab,
*Towards a theory of wear leveling in persistent data structures*, PODC 2022, Section 4).

* Threads `P` run an algorithm `A : Alg O k V` implementing the sequential object `O`. A thread
  step is one primitive (`Act`): `read i` (of the cached value of word `i`),
  `cas i exp new` (compare-and-swap on the cached word; a successful CAS marks the cache line
  *dirty*, a failed one does not), `flush i` (write the line back if it is dirty), or `ret r`.
* Persistent memory is changed **only** by write-backs (`writeBack`), triggered by `flush` or by
  a spontaneous eviction (event `evict i`). A write-back of a clean line does nothing; a
  write-back of a dirty line copies the cached value to persistent memory, increments the wear
  counter of the word and cleans the line (the assumptions (1)–(3) of the proof of Theorem 4.3).
* **Wear-out** (`Wear`): a word survives `T` write-backs (`T : ℕ∞`, `⊤` = no wear-out). Every
  later write-back of that word stores an arbitrary value `junk i w old new` instead of `new`
  (`w` = the number of earlier write-backs). `Wear.ideal` never wears out.
* A system-wide crash (`Ev.crash`) loses the cache (it is reloaded from persistent memory, all
  lines clean) and all running operations (threads become idle).
* Histories (`HEv`) record invocations (with fresh identifiers `cnt`), responses and crashes;
  correctness is strict linearizability (`IsStrictLin`).

## Main definitions

* `Act`, `Alg`, `Wear`, `TS`, `Cfg`, `Ev`, `writeBack`, `step1`, `exec`, `hist`
* `SafeUpTo`, `cfgAt`, `LockFreeOn`, `LockFree`, `LiveUpTo`, `GuaranteesUpTo`, `HasEndurance`
  (Definition 2.1 of Liu–Golab), `ObstructionFree`
* `HInv`: the generic well-formedness invariant of histories (`hInv_exec`)
-/

namespace Cslib.SharedMemory.Persistent

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

/-- A primitive step of a thread on `k` cached persistent words with values in `V`; `L` is the
type of local states (continuations), `R` the type of responses. -/
inductive Act (k : ℕ) (V L R : Type) where
  /-- Read the (cached) value of word `i`. -/
  | read (i : Fin k) (κ : V → L)
  /-- Compare-and-swap on word `i`; the continuation gets the success bit. -/
  | cas (i : Fin k) (exp new : V) (κ : Bool → L)
  /-- Flush (write back) the cache line of word `i`. -/
  | flush (i : Fin k) (next : L)
  /-- Return `r`. -/
  | ret (r : R)

/-- An implementation of the object `O` from `k` persistent words with values in `V`. -/
structure Alg (O : ObjSpec) (k : ℕ) (V : Type) where
  /-- Local states. -/
  L : Type
  /-- Initial contents of the words. -/
  init : Fin k → V
  /-- Local state at the invocation of `o`. -/
  start : O.Op → L
  /-- The next step in a local state. -/
  act : L → Act k V L O.Resp

/-- Wear-out model: each word survives `T` write-backs; later write-backs of word `i` store
`junk i w old new` (where `w` is the number of earlier write-backs of `i`). -/
structure Wear (k : ℕ) (V : Type) where
  /-- Endurance of a word (number of write-backs it survives). -/
  T : ℕ∞
  /-- What a worn-out word stores. -/
  junk : Fin k → ℕ → V → V → V

/-- No wear-out. -/
def Wear.ideal (k : ℕ) (V : Type) : Wear k V := ⟨⊤, fun _ _ old _ => old⟩

/-- State of a thread: idle, or running operation instance `a` (operation `o`) in local
state `l`. -/
inductive TS (Op L : Type) where
  | idle
  | run (a : ℕ) (o : Op) (l : L)

variable {O : ObjSpec} {k : ℕ} {V : Type}

/-- Configurations. -/
structure Cfg (A : Alg O k V) (P : Type) where
  /-- Cached (coherent, volatile) values. -/
  cache : Fin k → V
  /-- Dirty bits of the cache lines. -/
  dirty : Fin k → Bool
  /-- Persistent memory. -/
  pm : Fin k → V
  /-- Number of write-backs of each word so far. -/
  wear : Fin k → ℕ
  /-- Thread states. -/
  ts : P → TS O.Op A.L
  /-- Next operation identifier (= number of invocations so far). -/
  cnt : ℕ

/-- Schedule events. -/
inductive Ev (k : ℕ) (P Op : Type) where
  /-- Thread `p` invokes `o` (ignored if `p` is running). -/
  | inv (p : P) (o : Op)
  /-- Thread `p` takes a step (ignored if `p` is idle). -/
  | step (p : P)
  /-- Spontaneous eviction (write-back) of the cache line of word `i`. -/
  | evict (i : Fin k)
  /-- System-wide crash. -/
  | crash

namespace Alg

variable (A : Alg O k V) (P : Type)

/-- The initial configuration. -/
def initCfg : Cfg A P := ⟨A.init, fun _ => false, A.init, fun _ => 0, fun _ => .idle, 0⟩

variable {A P} [DecidableEq P] [DecidableEq V]

/-- Write-back of the cache line of word `i` (does nothing if the line is clean). -/
def writeBack (W : Wear k V) (C : Cfg A P) (i : Fin k) : Cfg A P :=
  if C.dirty i then
    { C with
      pm := Function.update C.pm i
        (if (C.wear i : ℕ∞) < W.T then C.cache i else W.junk i (C.wear i) (C.pm i) (C.cache i))
      wear := Function.update C.wear i (C.wear i + 1)
      dirty := Function.update C.dirty i false }
  else C

/-- One event: the new configuration and the emitted history events. -/
def step1 (W : Wear k V) (C : Cfg A P) : Ev k P O.Op → Cfg A P × List (HEv P O.Op O.Resp)
  | .inv p o =>
    match C.ts p with
    | .idle => ({ C with ts := Function.update C.ts p (.run C.cnt o (A.start o)),
                         cnt := C.cnt + 1 }, [.inv C.cnt p o])
    | .run .. => (C, [])
  | .step p =>
    match C.ts p with
    | .idle => (C, [])
    | .run a o l =>
      match A.act l with
      | .read i κ => ({ C with ts := Function.update C.ts p (.run a o (κ (C.cache i))) }, [])
      | .cas i e n κ =>
        if C.cache i = e then
          ({ C with cache := Function.update C.cache i n,
                    dirty := Function.update C.dirty i true,
                    ts := Function.update C.ts p (.run a o (κ true)) }, [])
        else ({ C with ts := Function.update C.ts p (.run a o (κ false)) }, [])
      | .flush i l' => ({ writeBack W C i with ts := Function.update C.ts p (.run a o l') }, [])
      | .ret r => ({ C with ts := Function.update C.ts p .idle }, [.res a r])
  | .evict i => (writeBack W C i, [])
  | .crash => ({ C with cache := C.pm, dirty := fun _ => false, ts := fun _ => .idle },
      [.crash])

/-- Execution of a schedule from `C`: final configuration and history. -/
def exec (W : Wear k V) (C : Cfg A P) : List (Ev k P O.Op) → Cfg A P × List (HEv P O.Op O.Resp)
  | [] => (C, [])
  | e :: es => ((exec W (step1 W C e).1 es).1, (step1 W C e).2 ++ (exec W (step1 W C e).1 es).2)

@[simp] lemma exec_nil (W : Wear k V) (C : Cfg A P) : exec W C [] = (C, []) := rfl

lemma exec_append (W : Wear k V) (C : Cfg A P) (es fs : List (Ev k P O.Op)) :
    exec W C (es ++ fs) =
      ((exec W (exec W C es).1 fs).1, (exec W C es).2 ++ (exec W (exec W C es).1 fs).2) := by
  induction es generalizing C with
  | nil => simp
  | cons e es ih => simp [exec, ih]

lemma exec_concat (W : Wear k V) (C : Cfg A P) (es : List (Ev k P O.Op)) (e : Ev k P O.Op) :
    exec W C (es ++ [e]) =
      ((step1 W (exec W C es).1 e).1, (exec W C es).2 ++ (step1 W (exec W C es).1 e).2) := by
  rw [exec_append]; simp [exec]

variable (A P)

/-- The history of the execution of the schedule `es` from the initial configuration. -/
def hist (W : Wear k V) (es : List (Ev k P O.Op)) : List (HEv P O.Op O.Resp) :=
  (exec W (initCfg A P) es).2

/-! ### Correctness and progress notions -/

/-- **Safety for executions with at most `N` invocations**: their histories are strictly
linearizable. -/
def SafeUpTo (W : Wear k V) (N : ℕ∞) : Prop :=
  ∀ es : List (Ev k P O.Op), (invCount (hist A P W es) : ℕ∞) ≤ N →
    StrictLinearizable O (hist A P W es)

/-- The prefix of length `t` of an infinite schedule. -/
def pfx (e : ℕ → Ev k P O.Op) (t : ℕ) : List (Ev k P O.Op) := (List.range t).map e

/-- The configuration at time `t` of an infinite schedule. -/
def cfgAt (W : Wear k V) (e : ℕ → Ev k P O.Op) (t : ℕ) : Cfg A P :=
  (exec W (initCfg A P) (pfx P e t)).1

/-- **Lock-freedom on a class `E` of infinite schedules**: if from some time on there is no
crash and threads that are running keep taking steps, then responses keep occurring. -/
def LockFreeOn (W : Wear k V) (E : (ℕ → Ev k P O.Op) → Prop) : Prop :=
  ∀ e, E e → (∃ t₀, ∀ t ≥ t₀, e t ≠ .crash) →
    (∀ t, ∃ t' ≥ t, ∃ p, e t' = .step p ∧ (cfgAt A P W e t').ts p ≠ .idle) →
    ∀ t, ∃ t' ≥ t, ∃ a r, (step1 W (cfgAt A P W e t') (e t')).2 = [.res a r]

/-- Lock-freedom (on all infinite schedules). -/
def LockFree (W : Wear k V) : Prop := LockFreeOn A P W fun _ => True

/-- **Liveness for executions with at most `N` invocations.** -/
def LiveUpTo (W : Wear k V) (N : ℕ∞) : Prop :=
  LockFreeOn A P W fun e => ∀ t, (invCount (hist A P W (pfx P e t)) : ℕ∞) ≤ N

/-- If every word survives `T` write-backs (whatever worn-out words store), the implementation is
safe and live in all executions with at most `N` invocations (updates). -/
def GuaranteesUpTo (T : ℕ∞) (N : ℕ∞) : Prop :=
  ∀ junk, SafeUpTo A P ⟨T, junk⟩ N ∧ LiveUpTo A P ⟨T, junk⟩ N

/-- **Definition 2.1** (endurance) for an implementation whose words have endurance `T`: it
maintains safety and liveness in all executions with at most `N` updates, but not in some
execution with `N + 1` updates. (All operations of the objects considered here are updates.) -/
def HasEndurance (T : ℕ∞) (N : ℕ) : Prop :=
  GuaranteesUpTo A P T N ∧ ¬ GuaranteesUpTo A P T (N + 1 : ℕ)

/-- Obstruction-freedom: from every reachable configuration a thread running solo (without
crashes) completes its operation. -/
def ObstructionFree (W : Wear k V) : Prop :=
  ∀ (es : List (Ev k P O.Op)) (p : P), ∃ n,
    (exec W (initCfg A P) (es ++ List.replicate n (.step p))).1.ts p = .idle

/-! ### Basic facts -/

variable {A P}

lemma cfgAt_succ (W : Wear k V) (e : ℕ → Ev k P O.Op) (t : ℕ) :
    cfgAt A P W e (t + 1) = (step1 W (cfgAt A P W e t) (e t)).1 := by
  simp [cfgAt, pfx, List.range_succ, exec_concat]

lemma hist_pfx_succ (W : Wear k V) (e : ℕ → Ev k P O.Op) (t : ℕ) :
    hist A P W (pfx P e (t + 1)) =
      hist A P W (pfx P e t) ++ (step1 W (cfgAt A P W e t) (e t)).2 := by
  simp [hist, cfgAt, pfx, List.range_succ, exec_concat]

lemma cnt_step1 (W : Wear k V) (C : Cfg A P) (e : Ev k P O.Op) :
    (step1 W C e).1.cnt = C.cnt + invCount (step1 W C e).2 := by
  cases e with
  | inv p o => cases h : C.ts p <;> simp [step1, h]
  | step p =>
    cases h : C.ts p with
    | idle => simp [step1, h]
    | run a o l =>
      cases h' : A.act l with
      | cas i e n κ => by_cases hc : C.cache i = e <;> simp [step1, h, h', hc]
      | flush i l' => simp [step1, h, h', writeBack]; split_ifs <;> rfl
      | _ => simp [step1, h, h']
  | evict i => simp [step1, writeBack]; split_ifs <;> rfl
  | crash => simp [step1]

lemma cnt_exec (W : Wear k V) (C : Cfg A P) (es : List (Ev k P O.Op)) :
    (exec W C es).1.cnt = C.cnt + invCount (exec W C es).2 := by
  induction es generalizing C with
  | nil => simp
  | cons e es ih => simp only [exec, invCount_append, ih, cnt_step1]; omega

lemma invCount_hist (W : Wear k V) (es : List (Ev k P O.Op)) :
    invCount (hist A P W es) = (exec W (initCfg A P) es).1.cnt := by
  rw [cnt_exec]; simp [hist, initCfg]

/-! ### Well-formedness of histories -/

/-- Generic invariant relating a configuration and the history produced so far. -/
structure HInv (C : Cfg A P) (h : List (HEv P O.Op O.Resp)) : Prop where
  inv_lt : ∀ a p o, HEv.inv a p o ∈ h → a < C.cnt
  res_lt : ∀ a r, HEv.res a r ∈ h → a < C.cnt
  run_inv : ∀ p a o l, C.ts p = .run a o l → HEv.inv a p o ∈ h
  run_notEnded : ∀ p a o l, C.ts p = .run a o l → NotEnded h a
  run_inj : ∀ p q a o o' l l', C.ts p = .run a o l → C.ts q = .run a o' l' → p = q

lemma hInv_init : HInv (initCfg A P) [] :=
  ⟨by simp, by simp, by simp [initCfg], by simp [initCfg], by simp [initCfg]⟩

lemma HInv.run_lt {C : Cfg A P} {h : List (HEv P O.Op O.Resp)} (hI : HInv C h) {p a o l}
    (hp : C.ts p = .run a o l) : a < C.cnt :=
  hI.inv_lt a p o (hI.run_inv p a o l hp)

/-- Changing only the local state of a running thread (no history event). -/
lemma HInv.update_local {C : Cfg A P} {h : List (HEv P O.Op O.Resp)} (hI : HInv C h) {p a o l}
    (hp : C.ts p = .run a o l) (l' : A.L) (C' : Cfg A P) (hcnt : C'.cnt = C.cnt)
    (hts : C'.ts = Function.update C.ts p (.run a o l')) : HInv C' h where
  inv_lt := by rw [hcnt]; exact hI.inv_lt
  res_lt := by rw [hcnt]; exact hI.res_lt
  run_inv q b o' l'' hq := by
    rw [hts] at hq
    by_cases hqp : q = p
    · subst hqp; simp at hq; obtain ⟨rfl, rfl, rfl⟩ := hq; exact hI.run_inv _ _ _ _ hp
    · simp only [Function.update_of_ne hqp] at hq; exact hI.run_inv _ _ _ _ hq
  run_notEnded q b o' l'' hq := by
    rw [hts] at hq
    by_cases hqp : q = p
    · subst hqp; simp at hq; obtain ⟨rfl, rfl, rfl⟩ := hq; exact hI.run_notEnded _ _ _ _ hp
    · simp only [Function.update_of_ne hqp] at hq; exact hI.run_notEnded _ _ _ _ hq
  run_inj q q' b o₁ o₂ l₁ l₂ hq hq' := by
    rw [hts] at hq hq'
    have key : ∀ r o₃ l₃, Function.update C.ts p (.run a o l') r = .run b o₃ l₃ →
        ∃ l₄, C.ts r = .run b o₃ l₄ := by
      intro r o₃ l₃ hr
      by_cases hrp : r = p
      · subst hrp; simp at hr; obtain ⟨rfl, rfl, rfl⟩ := hr; exact ⟨l, hp⟩
      · rw [Function.update_of_ne hrp] at hr; exact ⟨l₃, hr⟩
    obtain ⟨_, h1⟩ := key q o₁ l₁ hq
    obtain ⟨_, h2⟩ := key q' o₂ l₂ hq'
    exact hI.run_inj _ _ _ _ _ _ _ h1 h2

lemma writeBack_cnt (W : Wear k V) (C : Cfg A P) (i : Fin k) : (writeBack W C i).cnt = C.cnt := by
  unfold writeBack; split_ifs <;> rfl

lemma writeBack_cache (W : Wear k V) (C : Cfg A P) (i : Fin k) :
    (writeBack W C i).cache = C.cache := by
  unfold writeBack; split_ifs <;> rfl

lemma writeBack_dirty (W : Wear k V) (C : Cfg A P) (i : Fin k) :
    (writeBack W C i).dirty = Function.update C.dirty i false := by
  unfold writeBack
  by_cases h : C.dirty i = true
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    funext j
    by_cases hj : j = i
    · subst hj; simpa using h
    · simp [Function.update_of_ne hj]

lemma writeBack_ts (W : Wear k V) (C : Cfg A P) (i : Fin k) : (writeBack W C i).ts = C.ts := by
  unfold writeBack; split_ifs <;> rfl

lemma HInv.step1 {C : Cfg A P} {h : List (HEv P O.Op O.Resp)} (hI : HInv C h) (W : Wear k V)
    (e : Ev k P O.Op) : HInv (Alg.step1 W C e).1 (h ++ (Alg.step1 W C e).2) := by
  cases e with
  | inv p o =>
    cases hp : C.ts p with
    | run => simpa [Alg.step1, hp] using hI
    | idle =>
      simp only [Alg.step1, hp]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a q o' ha
        rcases List.mem_append.1 ha with ha | ha
        · have := hI.inv_lt _ _ _ ha; simp; omega
        · simp at ha; simp [ha.1]
      · intro a r ha
        rcases List.mem_append.1 ha with ha | ha
        · have := hI.res_lt _ _ ha; simp; omega
        · simp at ha
      · intro q a o' l hq
        by_cases hqp : q = p
        · subst hqp; simp at hq; obtain ⟨rfl, rfl, rfl⟩ := hq; simp
        · simp only [Function.update_of_ne hqp] at hq
          exact List.mem_append_left _ (hI.run_inv _ _ _ _ hq)
      · intro q a o' l hq
        by_cases hqp : q = p
        · subst hqp; simp at hq; obtain ⟨rfl, rfl, rfl⟩ := hq
          intro i hi
          rcases hi with ⟨r, hr⟩ | ⟨hc, j, hji, hj⟩
          · have hlt : i < h.length := by
              by_contra hc
              rcases Nat.lt_or_ge i (h.length + 1) with h1 | h1
              · have : i = h.length := by omega
                subst this; simp at hr
              · rw [List.getElem?_eq_none (by simp; omega)] at hr; cases hr
            rw [List.getElem?_append_left hlt] at hr
            have := hI.res_lt _ _ (List.mem_of_getElem? hr); omega
          · have hlt : i < h.length := by
              by_contra hc'
              rcases Nat.lt_or_ge i (h.length + 1) with h1 | h1
              · have : i = h.length := by omega
                subst this; simp at hc
              · rw [List.getElem?_eq_none (by simp; omega)] at hc; cases hc
            obtain ⟨p', o', hj⟩ := hj
            rw [List.getElem?_append_left (by omega)] at hj
            have := hI.inv_lt _ _ _ (List.mem_of_getElem? hj); omega
        · simp only [Function.update_of_ne hqp] at hq
          have hne := hI.run_notEnded _ _ _ _ hq
          have hlt := hI.run_lt hq
          intro i hi
          have hilt : i < h.length := by
            by_contra hc
            rcases hi with ⟨r, hr⟩ | ⟨hc', _⟩
            · rcases Nat.lt_or_ge i (h.length + 1) with h1 | h1
              · have : i = h.length := by omega
                subst this; simp at hr
              · rw [List.getElem?_eq_none (by simp; omega)] at hr; cases hr
            · rcases Nat.lt_or_ge i (h.length + 1) with h1 | h1
              · have : i = h.length := by omega
                subst this; simp at hc'
              · rw [List.getElem?_eq_none (by simp; omega)] at hc'; cases hc'
          exact hne i (hi.of_append hilt)
      · intro q q' a o₁ o₂ l₁ l₂ hq hq'
        by_cases hqp : q = p <;> by_cases hq'p : q' = p
        · rw [hqp, hq'p]
        · subst hqp; simp at hq; obtain ⟨rfl, -, -⟩ := hq
          simp only [Function.update_of_ne hq'p] at hq'
          have := hI.run_lt hq'; omega
        · subst hq'p; simp at hq'; obtain ⟨rfl, -, -⟩ := hq'
          simp only [Function.update_of_ne hqp] at hq
          have := hI.run_lt hq; omega
        · simp only [Function.update_of_ne hqp] at hq; simp only [Function.update_of_ne hq'p] at hq'
          exact hI.run_inj _ _ _ _ _ _ _ hq hq'
  | step p =>
    cases hp : C.ts p with
    | idle => simpa [Alg.step1, hp] using hI
    | run a o l =>
      cases hact : A.act l with
      | read i κ =>
        simp only [Alg.step1, hp, hact, List.append_nil]
        exact hI.update_local hp _ _ rfl rfl
      | cas i e n κ =>
        by_cases hc : C.cache i = e
        · simp only [Alg.step1, hp, hact, hc, ite_true, List.append_nil]
          exact hI.update_local hp _ _ rfl rfl
        · simp only [Alg.step1, hp, hact, hc, ite_false, List.append_nil]
          exact hI.update_local hp _ _ rfl rfl
      | flush i l' =>
        simp only [Alg.step1, hp, hact, List.append_nil]
        exact hI.update_local hp _ _ (writeBack_cnt W C i) rfl
      | ret r =>
        simp only [Alg.step1, hp, hact]
        have hane := hI.run_notEnded _ _ _ _ hp
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro b q o' hb
          rcases List.mem_append.1 hb with hb | hb
          · exact hI.inv_lt _ _ _ hb
          · simp at hb
        · intro b r' hb
          rcases List.mem_append.1 hb with hb | hb
          · exact hI.res_lt _ _ hb
          · simp at hb; rw [hb.1]; exact hI.run_lt hp
        · intro q b o' l' hq
          by_cases hqp : q = p
          · subst hqp; simp at hq
          · simp only [Function.update_of_ne hqp] at hq
            exact List.mem_append_left _ (hI.run_inv _ _ _ _ hq)
        · intro q b o' l' hq i hi
          by_cases hqp : q = p
          · subst hqp; simp at hq
          · simp only [Function.update_of_ne hqp] at hq
            have hne := hI.run_notEnded _ _ _ _ hq
            by_cases hilt : i < h.length
            · exact hne i (hi.of_append hilt)
            · rcases hi with ⟨r', hr'⟩ | ⟨hc', _⟩
              · rcases Nat.lt_or_ge i (h.length + 1) with h1 | h1
                · have : i = h.length := by omega
                  subst this; simp at hr'
                  exact hqp (hI.run_inj _ _ _ _ _ _ _ hq (hr'.1 ▸ hp))
                · rw [List.getElem?_eq_none (by simp; omega)] at hr'; cases hr'
              · rcases Nat.lt_or_ge i (h.length + 1) with h1 | h1
                · have : i = h.length := by omega
                  subst this; simp at hc'
                · rw [List.getElem?_eq_none (by simp; omega)] at hc'; cases hc'
        · intro q q' b o₁ o₂ l₁ l₂ hq hq'
          by_cases hqp : q = p
          · subst hqp; simp at hq
          by_cases hq'p : q' = p
          · subst hq'p; simp at hq'
          simp only [Function.update_of_ne hqp] at hq; simp only [Function.update_of_ne hq'p] at hq'
          exact hI.run_inj _ _ _ _ _ _ _ hq hq'
  | evict i =>
    simp only [Alg.step1, List.append_nil]
    have := writeBack_cnt W C i; have := writeBack_ts W C i
    exact ⟨by simpa [writeBack_cnt] using hI.inv_lt, by simpa [writeBack_cnt] using hI.res_lt,
      by simpa [writeBack_ts] using hI.run_inv, by simpa [writeBack_ts] using hI.run_notEnded,
      by simpa [writeBack_ts] using hI.run_inj⟩
  | crash =>
    simp only [Alg.step1]
    refine ⟨?_, ?_, by simp, by simp, by simp⟩
    · intro b q o' hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hI.inv_lt _ _ _ hb
      · simp at hb
    · intro b r' hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hI.res_lt _ _ hb
      · simp at hb

lemma hInv_exec (W : Wear k V) (es : List (Ev k P O.Op)) :
    HInv (exec W (initCfg A P) es).1 (exec W (initCfg A P) es).2 := by
  induction es using List.reverseRecOn with
  | nil => exact hInv_init
  | append_singleton es e ih =>
    rw [exec_concat]; exact ih.step1 W e

end Alg

end Cslib.SharedMemory.Persistent
