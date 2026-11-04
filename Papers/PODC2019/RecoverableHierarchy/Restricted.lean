import Papers.PODC2019.RecoverableHierarchy.Defs

/-!
# The restricted failure model of Assumptions 1 and 2

The impossibility proofs of Theorems 3 and 6 restrict attention to executions in which only two
processes `a` (the paper's `p₁`) and `b` (`p₂`) take steps, `b` never crashes, and `a` crashes
**if and only if** its previous step was its first *triggering* operation on some object
(Assumption 1: the first access to a TAS object; Assumption 2: the first access to a consensus
object). Which operations trigger a crash is a parameter `trig`; the triggering objects lie in a
finite set `F`, so a restricted execution has at most `|F|` crashes.

In the restricted model every process has exactly one possible next move, so an execution is
determined by its *schedule* `σ : List Bool` (`false` = a move of `a`, `true` = a move of `b`).
We track the restricted state `RS`: the configuration, the set `trg` of objects on which `a` has
already applied a triggering operation, and a flag `pend` ("`a` must crash next").

* `Restr.mv`, `Restr.ev`, `Restr.rrun`, `Restr.evs`: moves, the underlying events of CSLib's
  model, runs (`rrun_c`: the configuration is CSLib's `run` of the underlying events);
* `Restr.numCrashes_E_le`: a restricted execution has at most `|F|` crashes;
* `Restr.RCorrect`: agreement (distinct processes), validity and recoverable wait-freedom on the
  restricted executions — what the paper's proofs use; `SolvesP.rcorrect` derives it from the
  paper's specification.
-/

namespace Podc.RecoverableHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ}

/-- The data of a restricted failure model: the two participating processes `a` (crashes) and
`b` (never crashes), the triggering operations, and a finite set `F` containing every object with
a triggering operation. -/
structure Restr (A : Alg n T) where
  /-- The process that crashes (the paper's `p₁`). -/
  a : Fin n
  /-- The process that never crashes (the paper's `p₂`). -/
  b : Fin n
  hab : a ≠ b
  /-- Operations whose first application to an object by `a` is followed by a crash of `a`. -/
  trig : (i : ι) → (T i).Op → Bool
  /-- The objects with triggering operations. -/
  F : Finset ι
  hF : ∀ i o, trig i o = true → i ∈ F

variable (A : Alg n T) in
/-- Restricted states: configuration, objects already triggered by `a`, pending crash of `a`. -/
@[ext] structure RS where
  c : Cfg A
  trg : Finset ι
  pend : Bool

variable {A : Alg n T}

variable (A) in
/-- The initial restricted state with inputs `x`. -/
def RS.init (x : Fin n → Bool) : RS A := ⟨initCfg A x, ∅, false⟩

namespace Restr

variable (R : Restr A)

/-- The object on which `a`'s next step is a first triggering operation, if any. -/
def newTrig (s : RS A) : Option ι :=
  match A.act (s.c.loc R.a) with
  | .access i o _ => if R.trig i o = true ∧ i ∉ s.trg then some i else none
  | .out _ => none

/-- The process moving in a move `m`. -/
def who : Bool → Fin n
  | true => R.b
  | false => R.a

/-- The underlying event of the move `m` from `s`. -/
def ev (s : RS A) : Bool → Ev n
  | true => .step R.b
  | false => if s.pend then .crash R.a else .step R.a

/-- The restricted state after the move `m`. -/
def mv (s : RS A) : Bool → RS A
  | true => { s with c := s.c.stepP R.b }
  | false =>
    if s.pend then { s with c := s.c.next (.crash R.a), pend := false }
    else match R.newTrig s with
      | some i => ⟨s.c.stepP R.a, insert i s.trg, true⟩
      | none => { s with c := s.c.stepP R.a }

lemma mv_c (s : RS A) (m : Bool) : (R.mv s m).c = s.c.next (R.ev s m) := by
  cases m
  · by_cases h : s.pend
    · simp [mv, ev, h]
    · simp only [mv, ev, h, Bool.false_eq_true, ite_false]
      cases R.newTrig s <;> rfl
  · rfl

lemma ev_proc (s : RS A) (m : Bool) : (R.ev s m).proc = R.who m := by
  cases m
  · by_cases h : s.pend <;> simp [ev, h, who]
  · rfl

@[simp] lemma mv_true (s : RS A) : R.mv s true = { s with c := s.c.stepP R.b } := rfl

@[simp] lemma ev_true (s : RS A) : R.ev s true = .step R.b := rfl

lemma mv_false_pend (s : RS A) (h : s.pend = true) :
    R.mv s false = { s with c := s.c.next (.crash R.a), pend := false } := by
  simp [mv, h]

lemma ev_false_pend (s : RS A) (h : s.pend = true) : R.ev s false = .crash R.a := by
  simp [ev, h]

lemma ev_false_npend (s : RS A) (h : s.pend = false) : R.ev s false = .step R.a := by
  simp [ev, h]

lemma mv_false_npend (s : RS A) (h : s.pend = false) :
    R.mv s false = match R.newTrig s with
      | some i => ⟨s.c.stepP R.a, insert i s.trg, true⟩
      | none => { s with c := s.c.stepP R.a } := by
  simp [mv, h]

/-- Run a schedule. -/
def rrun (s : RS A) (σ : List Bool) : RS A := σ.foldl R.mv s

/-- The underlying events of a schedule. -/
def evs : RS A → List Bool → List (Ev n)
  | _, [] => []
  | s, m :: σ => R.ev s m :: evs (R.mv s m) σ

@[simp] lemma rrun_nil (s : RS A) : R.rrun s [] = s := rfl
@[simp] lemma rrun_cons (s : RS A) (m : Bool) (σ : List Bool) :
    R.rrun s (m :: σ) = R.rrun (R.mv s m) σ := rfl
@[simp] lemma evs_nil (s : RS A) : R.evs s [] = [] := rfl
@[simp] lemma evs_cons (s : RS A) (m : Bool) (σ : List Bool) :
    R.evs s (m :: σ) = R.ev s m :: R.evs (R.mv s m) σ := rfl

lemma rrun_append (s : RS A) (σ τ : List Bool) :
    R.rrun s (σ ++ τ) = R.rrun (R.rrun s σ) τ := by
  simp [rrun, List.foldl_append]

lemma evs_append (s : RS A) (σ τ : List Bool) :
    R.evs s (σ ++ τ) = R.evs s σ ++ R.evs (R.rrun s σ) τ := by
  induction σ generalizing s with
  | nil => rfl
  | cons m σ ih => simp [ih]

@[simp] lemma evs_length (s : RS A) (σ : List Bool) : (R.evs s σ).length = σ.length := by
  induction σ generalizing s with
  | nil => rfl
  | cons m σ ih => simp [ih]

lemma rrun_c (s : RS A) (σ : List Bool) : (R.rrun s σ).c = run s.c (R.evs s σ) := by
  induction σ generalizing s with
  | nil => rfl
  | cons m σ ih => simp [ih, mv_c]

lemma rrun_concat (s : RS A) (σ : List Bool) (m : Bool) :
    R.rrun s (σ ++ [m]) = R.mv (R.rrun s σ) m := by
  simp [rrun_append]

lemma evs_concat (s : RS A) (σ : List Bool) (m : Bool) :
    R.evs s (σ ++ [m]) = R.evs s σ ++ [R.ev (R.rrun s σ) m] := by
  simp [evs_append]

lemma evs_take (s : RS A) (σ : List Bool) (k : ℕ) :
    (R.evs s σ).take k = R.evs s (σ.take k) := by
  induction σ generalizing s k with
  | nil => simp
  | cons m σ ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih]

/-- The events of `b`'s moves are steps of `b`; all events are by `a` or `b`. -/
lemma mem_evs_proc (s : RS A) (σ : List Bool) (e : Ev n) (he : e ∈ R.evs s σ) :
    ∃ m ∈ σ, e.proc = R.who m := by
  induction σ generalizing s with
  | nil => simp at he
  | cons m σ ih =>
    simp only [evs_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨m, by simp, R.ev_proc s m⟩
    · obtain ⟨m', hm', h⟩ := ih _ he
      exact ⟨m', by simp [hm'], h⟩

/-- `b` never crashes in a restricted execution. -/
lemma crash_b_not_mem (s : RS A) (σ : List Bool) : Ev.crash R.b ∉ R.evs s σ := by
  induction σ generalizing s with
  | nil => simp
  | cons m σ ih =>
    simp only [evs_cons, List.mem_cons, not_or]
    refine ⟨?_, ih _⟩
    cases m
    · by_cases h : s.pend
      · simp only [ev, h, ite_true, Ev.crash.injEq]
        exact fun h' => R.hab h'.symm
      · simp [ev, h]
    · simp [ev]


/-- The restricted state after schedule `σ` from the initial state with inputs `x`. -/
abbrev S (x : Fin n → Bool) (σ : List Bool) : RS A := R.rrun (RS.init A x) σ

/-- The underlying events of the schedule `σ` from the initial state with inputs `x`. -/
abbrev E (x : Fin n → Bool) (σ : List Bool) : List (Ev n) := R.evs (RS.init A x) σ

lemma S_c (x : Fin n → Bool) (σ : List Bool) : (R.S x σ).c = run (initCfg A x) (R.E x σ) :=
  R.rrun_c (RS.init A x) σ

/-! ## Counting crashes -/

lemma newTrig_spec {s : RS A} {i : ι} (h : R.newTrig s = some i) :
    i ∉ s.trg ∧ i ∈ R.F := by
  unfold newTrig at h
  split at h
  · rename_i i' o k _
    split_ifs at h with h'
    cases h
    exact ⟨h'.2, R.hF _ _ h'.1⟩
  · cases h

/-- `1` if `a` must crash next. -/
def pb (s : RS A) : ℕ := if s.pend then 1 else 0

lemma crash_count_one (s : RS A) (m : Bool) :
    numCrashes [R.ev s m] + pb (R.mv s m) + s.trg.card = (R.mv s m).trg.card + pb s := by
  cases m
  · by_cases hp : s.pend
    · rw [R.ev_false_pend s hp, R.mv_false_pend s hp]
      simp [pb, hp, numCrashes]; omega
    · simp only [Bool.not_eq_true] at hp
      rw [R.ev_false_npend s hp, R.mv_false_npend s hp]
      rcases hn : R.newTrig s with _ | i
      · simp [pb, hp, numCrashes]
      · have h1 := (R.newTrig_spec hn).1
        simp [pb, hp, numCrashes, Finset.card_insert_of_notMem h1]
        omega
  · rcases s with ⟨c, trg, pend⟩
    cases pend <;> (simp [pb, numCrashes, ev]; try omega)

/-- Crash accounting: every crash consumes a pending flag, every pending flag consumes a newly
triggered object. -/
lemma crash_count (s : RS A) (σ : List Bool) :
    numCrashes (R.evs s σ) + pb (R.rrun s σ) + s.trg.card = (R.rrun s σ).trg.card + pb s := by
  induction σ generalizing s with
  | nil => simp; omega
  | cons m σ ih =>
    have h1 := ih (R.mv s m)
    have h2 := R.crash_count_one s m
    simp only [evs_cons, rrun_cons]
    rw [show R.ev s m :: R.evs (R.mv s m) σ = [R.ev s m] ++ R.evs (R.mv s m) σ from rfl,
      numCrashes_append]
    omega

lemma trg_subset (s : RS A) (hs : s.trg ⊆ R.F) (σ : List Bool) : (R.rrun s σ).trg ⊆ R.F := by
  induction σ generalizing s with
  | nil => exact hs
  | cons m σ ih =>
    apply ih
    cases m
    · by_cases hp : s.pend
      · simpa [R.mv_false_pend s hp] using hs
      · simp only [Bool.not_eq_true] at hp
        rw [R.mv_false_npend s hp]
        rcases hn : R.newTrig s with _ | i
        · simpa using hs
        · simp only
          exact Finset.insert_subset (R.newTrig_spec hn).2 hs
    · exact hs

/-- A restricted execution has at most `|F|` crashes. -/
lemma numCrashes_E_le (x : Fin n → Bool) (σ : List Bool) : numCrashes (R.E x σ) ≤ R.F.card := by
  have h := R.crash_count (RS.init A x) σ
  have h2 := Finset.card_le_card (R.trg_subset (RS.init A x) (by simp [RS.init]) σ)
  have e1 : (RS.init A x).trg = ∅ := rfl
  have e2 : pb (RS.init A x) = 0 := rfl
  rw [e1, e2, Finset.card_empty] at h
  have : pb (R.rrun (RS.init A x) σ) ≥ 0 := Nat.zero_le _
  change numCrashes (R.evs (RS.init A x) σ) ≤ _
  omega

/-! ## Infinite schedules -/

/-- The first `t` moves of an infinite schedule. -/
def bpre (sch : ℕ → Bool) (t : ℕ) : List Bool := (List.range t).map sch

lemma bpre_succ (sch : ℕ → Bool) (t : ℕ) : bpre sch (t + 1) = bpre sch t ++ [sch t] := by
  simp [bpre, List.range_succ]

@[simp] lemma bpre_length (sch : ℕ → Bool) (t : ℕ) : (bpre sch t).length = t := by simp [bpre]

/-- The underlying infinite event sequence of an infinite schedule. -/
def eInf (x : Fin n → Bool) (sch : ℕ → Bool) (t : ℕ) : Ev n :=
  R.ev (R.S x (bpre sch t)) (sch t)

lemma pre_eInf (x : Fin n → Bool) (sch : ℕ → Bool) (t : ℕ) :
    pre (R.eInf x sch) t = R.E x (bpre sch t) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [pre_succ, ih, bpre_succ, E, E, R.evs_concat]; rfl

/-- The infinite schedule `σ` followed by moves `m` forever. -/
def ext (σ : List Bool) (m : Bool) (t : ℕ) : Bool := if h : t < σ.length then σ[t] else m

lemma bpre_ext (σ : List Bool) (m : Bool) (k : ℕ) :
    bpre (ext σ m) (σ.length + k) = σ ++ List.replicate k m := by
  induction k with
  | zero =>
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [bpre, ext, show i < σ.length by simpa using h1]
  | succ k ih =>
    rw [← add_assoc, bpre_succ, ih, List.replicate_succ', ← List.append_assoc]
    simp [ext]

/-! ## Correctness on restricted executions -/

/-- Correctness of `A` on the restricted executions: agreement between distinct processes,
validity, and recoverable wait-freedom for the two moving processes. These are exactly the
properties the proofs of Theorems 3 and 6 use. -/
structure RCorrect : Prop where
  agree : ∀ x σ p q, p ≠ q → ∀ v w, Outputs (initCfg A x) (R.E x σ) p v →
    Outputs (initCfg A x) (R.E x σ) q w → v = w
  valid : ∀ x σ v, Dec (initCfg A x) (R.E x σ) v → ∃ p, x p = v
  prog : ∀ x (sch : ℕ → Bool) (m : Bool) N, (∀ M, ∃ t ≥ M, sch t = m) →
    (∀ t ≥ N, R.eInf x sch t ≠ .crash (R.who m)) →
    ∃ t ≥ N, ∃ v, (R.S x (bpre sch t)).c.Out (R.who m) v

end Restr

/-- The paper's specification on a set of executions containing all restricted executions
implies correctness on the restricted executions. -/
theorem SolvesP.rcorrect {A : Alg n T} {Adm : List (Ev n) → Prop} (h : SolvesP A Adm)
    (R : Restr A) (hAdm : ∀ x σ, Adm (R.E x σ)) : R.RCorrect where
  agree x σ p q hpq v w hv hw := h.agree x _ (hAdm x σ) p q hpq v w hv hw
  valid x σ v hv := h.valid x _ (hAdm x σ) v hv
  prog x sch m N hinf hN := by
    have hadm : ∀ t, Adm (pre (R.eInf x sch) t) := fun t => by
      rw [R.pre_eInf]; exact hAdm x _
    have hsteps : ∀ M, ∃ t ≥ M, R.eInf x sch t = .step (R.who m) := by
      intro M
      obtain ⟨t, ht, hm⟩ := hinf (max M N)
      refine ⟨t, le_of_max_le_left ht, ?_⟩
      have hN' := hN t (le_of_max_le_right ht)
      unfold Restr.eInf at hN' ⊢
      rw [hm] at hN' ⊢
      cases m
      · by_cases hp : (R.S x (Restr.bpre sch t)).pend
        · exact absurd (R.ev_false_pend _ hp) hN'
        · simp only [Bool.not_eq_true] at hp
          exact R.ev_false_npend _ hp
      · rfl
    obtain ⟨t, ht, v, hv⟩ := h.prog x (R.eInf x sch) (R.who m) N hadm hsteps hN
    refine ⟨t, ht, v, ?_⟩
    rwa [R.S_c, ← R.pre_eInf]

/-- Restricted executions have at most `f` crashes if `|F| ≤ f`. -/
lemma Restr.atMost_E {A : Alg n T} (R : Restr A) {f : ℕ} (hf : R.F.card ≤ f) (x : Fin n → Bool)
    (σ : List Bool) : AtMost f (R.E x σ) :=
  (R.numCrashes_E_le x σ).trans hf

end Podc.RecoverableHierarchy
