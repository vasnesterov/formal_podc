import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/NIS/Model.lean (staged by Papers/PODC2021/ExtensionBasedReductions)
/-!
# The non-uniform iterated snapshot (NIS) model, full-information form

Brusse–Ellen, *Reductions and Extension-Based Proofs*, PODC 2021, Section 3.

* `n` processes form a finite type `P`; there is an infinite sequence `S₁, S₂, …` of single-writer
  snapshot objects. Each process accesses each object at most twice, in order: first an `update`
  with its current state, then a `scan`.
* Protocols are **full-information**: a protocol is its decision function `δ`. The state of a process
  is its whole history (`St`): `init i x` (initial state `(i, xᵢ)`), `upd s` (the state `s·1` after
  updating with `s`), and `scan s v` (the state after the scan whose response is `v`, `s` being the
  state just before the scan). The paper writes the post-scan state as `(i, v)`; since `v i` is the
  state the process just wrote, the two encodings carry the same information.
* After each scan the process consults `δ`; if `δ` returns `some y` it outputs `y` and terminates.
  `δ` is consulted only on post-scan states (`decided`).
* Since every component of every object is written at most once, the contents of the memory are
  determined by the states of the processes (`hist`), so a configuration is just the vector of states.

All results are stated for every input vector `x : P → X` being an initial configuration (the protocol
does not know the task's input set; the task only constrains runs from its input vectors).
-/

namespace Cslib.NIS

/-- Full-information local states of the NIS model. -/
inductive St (P X : Type) : Type where
  /-- initial state `(i, x)` -/
  | init : P → X → St P X
  /-- the state `s·1` after performing `update(s)` -/
  | upd : St P X → St P X
  /-- the state after a scan with response `v` (from the state `s`, which is an `upd` state) -/
  | scan : St P X → (P → Option (St P X)) → St P X

namespace St

variable {P X : Type}

/-- The list of values this process has written, in order (`hist s)[h]` is what it wrote to
`S_{h+1}`). -/
def hist : St P X → List (St P X)
  | init _ _ => []
  | upd s => hist s ++ [s]
  | scan s _ => hist s

/-- Number of scans performed (= number of completed rounds). -/
def rounds : St P X → ℕ
  | init _ _ => 0
  | upd s => rounds s
  | scan s _ => rounds s + 1

/-- Number of steps taken. -/
def depth : St P X → ℕ
  | init _ _ => 0
  | upd s => depth s + 1
  | scan s _ => depth s + 1

/-- The identifier of the process (stored in its initial state). -/
def pid : St P X → P
  | init i _ => i
  | upd s => pid s
  | scan s _ => pid s

/-- The input of the process. -/
def input : St P X → X
  | init _ x => x
  | upd s => input s
  | scan s _ => input s

/-- The state before the last step (`init` states are their own parent). -/
def parent : St P X → St P X
  | init i x => init i x
  | upd s => s
  | scan s _ => s

/-- `s` is an initial state (the process has not taken a step). -/
def IsInit : St P X → Prop
  | init _ _ => True
  | _ => False

/-- `s` is a post-scan state. -/
def IsScan : St P X → Prop
  | scan _ _ => True
  | _ => False

instance (s : St P X) : Decidable s.IsInit := by cases s <;> simp [IsInit] <;> infer_instance
instance (s : St P X) : Decidable s.IsScan := by cases s <;> simp [IsScan] <;> infer_instance

@[simp] lemma isInit_init (i : P) (x : X) : (init i x).IsInit := trivial
@[simp] lemma not_isInit_upd (s : St P X) : ¬ (upd s).IsInit := id
@[simp] lemma not_isInit_scan (s : St P X) v : ¬ (scan s v).IsInit := id

lemma isInit_iff (s : St P X) : s.IsInit ↔ ∃ i x, s = init i x := by
  cases s <;> simp [IsInit]

lemma isInit_iff_depth (s : St P X) : s.IsInit ↔ s.depth = 0 := by
  cases s <;> simp [IsInit, depth]

end St

/-- Configurations: the vector of the states of the processes. -/
abbrev Config (P X : Type) := P → St P X

/-- A protocol (in full-information standard form) is its decision function. -/
abbrev Protocol (P X Y : Type) := St P X → Option Y

variable {P X Y : Type} [DecidableEq P]

open St

/-- The decision function is consulted only after scans. -/
def decided (δ : Protocol P X Y) : St P X → Option Y
  | scan s v => δ (scan s v)
  | _ => none

@[simp] lemma decided_init (δ : Protocol P X Y) i x : decided δ (init i x) = none := rfl
@[simp] lemma decided_upd (δ : Protocol P X Y) s : decided δ (upd s) = none := rfl
@[simp] lemma decided_scan (δ : Protocol P X Y) s v : decided δ (scan s v) = δ (scan s v) := rfl

/-- The initial configuration with input vector `x`. -/
def initC (x : P → X) : Config P X := fun i => init i (x i)

/-- The new state of `q` when it takes a step: an update if it is poised to update, otherwise a scan
of the snapshot object it is accessing (object number `rounds s + 1`). -/
def stepState (C : Config P X) (q : P) : St P X :=
  match C q with
  | upd s => scan (upd s) (fun j => (C j).hist[s.rounds]?)
  | s => upd s

/-- `C q`: the configuration after `q` takes a step from `C`. -/
def step (C : Config P X) (q : P) : Config P X := Function.update C q (stepState C q)

/-- `C α`: the configuration after the schedule `α`. -/
def exec (C : Config P X) : List P → Config P X
  | [] => C
  | q :: α => exec (step C q) α

/-- `q` is active (not terminated) in `C`. -/
def Active (δ : Protocol P X Y) (C : Config P X) (q : P) : Prop := decided δ (C q) = none

/-- `α` is a schedule from `C`: every process in it is active when it takes its step. -/
def IsSched (δ : Protocol P X Y) : Config P X → List P → Prop
  | _, [] => True
  | C, q :: α => Active δ C q ∧ IsSched δ (step C q) α

/-- Outputs of the processes in `C` (`none` = not terminated). -/
def outs (δ : Protocol P X Y) (C : Config P X) (q : P) : Option Y := decided δ (C q)

/-- `C` is final: no process is active. -/
def Final (δ : Protocol P X Y) (C : Config P X) : Prop := ∀ q, ¬ Active δ C q

/-- The input vector of a configuration. -/
def inputs (C : Config P X) : P → X := fun j => (C j).input

/-- `C` is reachable: it is `C₀ α` for an initial configuration `C₀` and a schedule `α`. -/
def Reach (δ : Protocol P X Y) (C : Config P X) : Prop :=
  ∃ x α, IsSched δ (initC x) α ∧ C = exec (initC x) α

/-- A protocol is wait-free if it has no infinite schedule from an initial configuration. -/
def WaitFree (δ : Protocol P X Y) : Prop :=
  ∀ x : P → X, ¬ ∃ f : ℕ → P, ∀ k, IsSched δ (initC x) ((List.range k).map f)

/-- A task: input vectors and, for each, the set of valid output vectors. -/
structure Task (P X Y : Type) where
  inputs : Set (P → X)
  spec : (P → X) → Set (P → Y)

/-- Composition `T' ∘ T` of tasks: first solve `T`, then solve `T'` on its outputs. -/
def Task.comp {X Y Z : Type} (T' : Task P Y Z) (T : Task P X Y) : Task P X Z where
  inputs := T.inputs
  spec x := {z | ∃ y ∈ T.spec x, z ∈ T'.spec y}

/-- `δ` solves `T`: it is wait-free and every final configuration reachable from an initial
configuration with input vector `x ∈ I` has a valid output vector. -/
def Solves (δ : Protocol P X Y) (T : Task P X Y) : Prop :=
  WaitFree δ ∧ ∀ x ∈ T.inputs, ∀ α, IsSched δ (initC x) α → Final δ (exec (initC x) α) →
    ∃ y ∈ T.spec x, ∀ q, outs δ (exec (initC x) α) q = some (y q)

/-- The outputs in `C` violate the specification of `T`: the input vector of `C` is an input
vector of `T`, and no valid output vector agrees with the outputs of the terminated processes. -/
def Violates (T : Task P X Y) (δ : Protocol P X Y) (C : Config P X) : Prop :=
  inputs C ∈ T.inputs ∧ ¬ ∃ y ∈ T.spec (inputs C), ∀ q z, outs δ C q = some z → y q = z

/-- `δ` is an iterated-snapshot (IS) protocol in normal form: every process terminates exactly after
its `t`-th scan (in the IS model every process terminates in the same round `t`). -/
def IsIS (δ : Protocol P X Y) (t : ℕ) : Prop :=
  ∀ s v, (δ (scan s v)).isSome ↔ (scan s v).rounds = t

/-- Replace the initial states of the processes that have not taken a step by the initial states
with inputs `u`. -/
def reinit (C : Config P X) (u : P → X) : Config P X :=
  fun j => if (C j).IsInit then init j (u j) else C j

/-- Total number of steps taken. -/
def totalDepth [Fintype P] (C : Config P X) : ℕ := ∑ j, (C j).depth


/-! ## Basic lemmas -/

namespace St
variable {P X : Type}

/-- Ancestors of a state (itself first). -/
def anc : St P X → List (St P X)
  | init i x => [init i x]
  | upd s => upd s :: anc s
  | scan s v => scan s v :: anc s

lemma mem_anc_self (s : St P X) : s ∈ s.anc := by cases s <;> simp [anc]

lemma depth_le_of_mem_anc : ∀ {s t : St P X}, s ∈ t.anc → s.depth ≤ t.depth
  | _, init i x, h => by simp [anc] at h; subst h; simp
  | _, upd t, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; simp
    · simp only [depth]; exact Nat.le_succ_of_le (depth_le_of_mem_anc h)
  | _, scan t v, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; simp
    · simp only [depth]; exact Nat.le_succ_of_le (depth_le_of_mem_anc h)

lemma anc_subset_of_mem : ∀ {s t : St P X}, s ∈ t.anc → s.anc ⊆ t.anc
  | _, init i x, h => by simp [anc] at h; subst h; exact fun _ h => h
  | _, upd t, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact fun _ h => h
    · exact fun a ha => List.mem_cons_of_mem _ (anc_subset_of_mem h ha)
  | _, scan t v, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact fun _ h => h
    · exact fun a ha => List.mem_cons_of_mem _ (anc_subset_of_mem h ha)

lemma eq_of_mem_anc_of_depth_eq : ∀ {s s' t : St P X}, s ∈ t.anc → s' ∈ t.anc →
    s.depth = s'.depth → s = s'
  | _, _, init i x, h, h', _ => by simp [anc] at h h'; rw [h, h']
  | _, _, upd t, h, h', hd => by
    simp only [anc, List.mem_cons] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · rw [h, h']
    · subst h; have := depth_le_of_mem_anc h'; simp [depth] at hd; omega
    · subst h'; have := depth_le_of_mem_anc h; simp [depth] at hd; omega
    · exact eq_of_mem_anc_of_depth_eq h h' hd
  | _, _, scan t v, h, h', hd => by
    simp only [anc, List.mem_cons] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · rw [h, h']
    · subst h; have := depth_le_of_mem_anc h'; simp [depth] at hd; omega
    · subst h'; have := depth_le_of_mem_anc h; simp [depth] at hd; omega
    · exact eq_of_mem_anc_of_depth_eq h h' hd

end St

section Steps
variable {δ : Protocol P X Y}

@[simp] lemma step_self (C : Config P X) (q : P) : step C q q = stepState C q := by simp [step]

lemma step_ne (C : Config P X) {q j : P} (h : j ≠ q) : step C q j = C j := by
  simp [step, Function.update_of_ne h]

lemma stepState_cases (C : Config P X) (q : P) :
    (∃ s, C q = upd s ∧ stepState C q = scan (upd s) (fun j => (C j).hist[s.rounds]?)) ∨
    ((∀ s, C q ≠ upd s) ∧ stepState C q = upd (C q)) := by
  unfold stepState
  split
  · next s h => exact Or.inl ⟨s, h, rfl⟩
  · next s h => exact Or.inr ⟨fun s' h' => h s' h', rfl⟩

@[simp] lemma depth_stepState (C : Config P X) (q : P) :
    (stepState C q).depth = (C q).depth + 1 := by
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩ <;> simp [h2, St.depth, *]

@[simp] lemma pid_stepState (C : Config P X) (q : P) : (stepState C q).pid = (C q).pid := by
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩ <;> simp [h2, St.pid, *]

@[simp] lemma input_stepState (C : Config P X) (q : P) : (stepState C q).input = (C q).input := by
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩ <;> simp [h2, St.input, *]

@[simp] lemma not_isInit_stepState (C : Config P X) (q : P) : ¬ (stepState C q).IsInit := by
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩ <;> simp [h2]

lemma anc_stepState (C : Config P X) (q : P) :
    (stepState C q).anc = stepState C q :: (C q).anc := by
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩ <;> simp [h2, St.anc, *]

@[simp] lemma exec_nil (C : Config P X) : exec C [] = C := rfl
@[simp] lemma exec_cons (C : Config P X) q α : exec C (q :: α) = exec (step C q) α := rfl

lemma exec_append (C : Config P X) (α β : List P) : exec C (α ++ β) = exec (exec C α) β := by
  induction α generalizing C with
  | nil => rfl
  | cons q α ih => exact ih _

@[simp] lemma isSched_nil (C : Config P X) : IsSched δ C [] := trivial
@[simp] lemma isSched_cons (C : Config P X) q α :
    IsSched δ C (q :: α) ↔ Active δ C q ∧ IsSched δ (step C q) α := Iff.rfl

lemma isSched_append (C : Config P X) (α β : List P) :
    IsSched δ C (α ++ β) ↔ IsSched δ C α ∧ IsSched δ (exec C α) β := by
  induction α generalizing C with
  | nil => simp
  | cons q α ih => simp [ih, and_assoc]

lemma isSched_concat (C : Config P X) (α : List P) (q : P) :
    IsSched δ C (α ++ [q]) ↔ IsSched δ C α ∧ Active δ (exec C α) q := by
  simp [isSched_append]

lemma exec_apply_of_not_mem (C : Config P X) {α : List P} {j : P} (h : j ∉ α) :
    exec C α j = C j := by
  induction α generalizing C with
  | nil => rfl
  | cons q α ih =>
    simp at h
    rw [exec_cons, ih _ h.2, step_ne _ h.1]

lemma not_isInit_exec_of_mem (C : Config P X) {α : List P} {j : P} (h : j ∈ α) :
    ¬ (exec C α j).IsInit := by
  induction α generalizing C with
  | nil => simp at h
  | cons q α ih =>
    rw [exec_cons]
    by_cases hj : j ∈ α
    · exact ih _ hj
    · simp [hj] at h; subst h; rw [exec_apply_of_not_mem _ hj]; simp

lemma depth_exec (C : Config P X) (α : List P) (j : P) :
    (exec C α j).depth = (C j).depth + α.count j := by
  induction α generalizing C with
  | nil => simp
  | cons q α ih =>
    rw [exec_cons, ih]
    by_cases h : j = q
    · subst h; simp; omega
    · rw [step_ne _ h, List.count_cons_of_ne (Ne.symm h)]

lemma mem_anc_exec (C : Config P X) (α : List P) (j : P) : C j ∈ (exec C α j).anc := by
  induction α generalizing C with
  | nil => exact St.mem_anc_self _
  | cons q α ih =>
    rw [exec_cons]
    refine St.anc_subset_of_mem (ih _) ?_
    by_cases h : j = q
    · subst h; simp [anc_stepState, St.mem_anc_self]
    · rw [step_ne _ h]; exact St.mem_anc_self _

lemma pid_exec (C : Config P X) (α : List P) (j : P) : (exec C α j).pid = (C j).pid := by
  induction α generalizing C with
  | nil => rfl
  | cons q α ih =>
    rw [exec_cons, ih]; by_cases h : j = q
    · subst h; simp
    · rw [step_ne _ h]

lemma input_exec (C : Config P X) (α : List P) (j : P) : (exec C α j).input = (C j).input := by
  induction α generalizing C with
  | nil => rfl
  | cons q α ih =>
    rw [exec_cons, ih]; by_cases h : j = q
    · subst h; simp
    · rw [step_ne _ h]

lemma measure_step [Fintype P] (C : Config P X) (q : P) : totalDepth (step C q) = totalDepth C + 1 := by
  unfold totalDepth
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q), ← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
  rw [Finset.sum_congr rfl (fun j hj => by rw [step_ne _ (Finset.ne_of_mem_erase hj)])]
  simp; omega

lemma measure_exec [Fintype P] (C : Config P X) (α : List P) :
    totalDepth (exec C α) = totalDepth C + α.length := by
  induction α generalizing C with
  | nil => rfl
  | cons q α ih => rw [exec_cons, ih, measure_step]; simp; omega

/-- A terminated process takes no step in a schedule. -/
lemma not_mem_of_terminated {C : Config P X} {α : List P} (hα : IsSched δ C α) {j : P}
    (hj : decided δ (C j) ≠ none) : j ∉ α := by
  induction α generalizing C with
  | nil => simp
  | cons q α ih =>
    obtain ⟨hq, hα⟩ := hα
    have hjq : j ≠ q := by rintro rfl; exact hj hq
    simp only [List.mem_cons, not_or]
    exact ⟨hjq, ih hα (by rwa [step_ne _ hjq])⟩

lemma exec_of_terminated {C : Config P X} {α : List P} (hα : IsSched δ C α) {j : P}
    (hj : decided δ (C j) ≠ none) : exec C α j = C j :=
  exec_apply_of_not_mem _ (not_mem_of_terminated hα hj)

/-- Validity of a schedule only depends on its start and end configurations: every state a process
steps from is a strict ancestor of its final state, no older than its initial one. -/
lemma isSched_iff (C : Config P X) (α : List P) :
    IsSched δ C α ↔ ∀ q, ∀ s ∈ (exec C α q).anc, (C q).depth ≤ s.depth →
      s.depth < (exec C α q).depth → decided δ s = none := by
  induction α generalizing C with
  | nil => simp; intro q s _ h1 h2; omega
  | cons q α ih =>
    rw [isSched_cons, ih, exec_cons]
    constructor
    · rintro ⟨hq, h⟩ p s hs h1 h2
      by_cases hp : p = q
      · subst hp
        have hmem := mem_anc_exec (step C p) α p
        simp only [step_self] at hmem
        by_cases hd : s.depth = (C p).depth
        · have hC : C p ∈ (exec (step C p) α p).anc :=
            St.anc_subset_of_mem hmem (by simp [anc_stepState, St.mem_anc_self])
          rw [St.eq_of_mem_anc_of_depth_eq hs hC hd]; exact hq
        · exact h p s hs (by simp; omega) h2
      · exact h p s hs (by rw [step_ne _ hp]; exact h1) h2
    · intro h
      refine ⟨?_, fun p s hs h1 h2 => h p s hs ?_ h2⟩
      · have hmem := mem_anc_exec (step C q) α q
        simp only [step_self] at hmem
        have hC : C q ∈ (exec (step C q) α q).anc :=
          St.anc_subset_of_mem hmem (by simp [anc_stepState, St.mem_anc_self])
        refine h q (C q) hC le_rfl ?_
        have := depth_exec (step C q) α q; simp at this; omega
      · by_cases hp : p = q
        · subst hp; simp at h1; omega
        · rwa [step_ne _ hp] at h1

lemma isSched_of_exec_eq {C : Config P X} {α β : List P} (h : exec C α = exec C β)
    (hα : IsSched δ C α) : IsSched δ C β := by
  rw [isSched_iff] at hα ⊢; rw [← h]; exact hα

end Steps

/-! ## Locality: processes that have not taken a step are invisible -/

section Locality
variable {δ : Protocol P X Y}

/-- `C` and `C'` agree up to the inputs of processes that have not taken a step. -/
def SimC (C C' : Config P X) : Prop := ∀ j, C j = C' j ∨ ((C j).IsInit ∧ (C' j).IsInit)

lemma hist_of_isInit {s : St P X} (h : s.IsInit) : s.hist = [] := by
  cases s <;> simp_all [St.IsInit, St.hist]

lemma stepState_congr {C C' : Config P X} (hs : SimC C C') {q : P} (hq : C q = C' q) :
    stepState C q = stepState C' q := by
  have hh : ∀ j, (C j).hist = (C' j).hist := fun j => by
    rcases hs j with h | ⟨h1, h2⟩
    · rw [h]
    · rw [hist_of_isInit h1, hist_of_isInit h2]
  unfold stepState; rw [hq]; simp only [hh]

lemma simC_step {C C' : Config P X} (hs : SimC C C') {q : P} (hq : C q = C' q) :
    SimC (step C q) (step C' q) := by
  intro j
  by_cases h : j = q
  · subst h; left; simp [stepState_congr hs hq]
  · rw [step_ne _ h, step_ne _ h]; exact hs j

lemma exec_congr {C C' : Config P X} (hs : SimC C C') {α : List P}
    (hα : ∀ j ∈ α, C j = C' j) :
    SimC (exec C α) (exec C' α) ∧ (∀ j ∈ α, exec C α j = exec C' α j) ∧
      (IsSched δ C α ↔ IsSched δ C' α) := by
  induction α generalizing C C' with
  | nil => simpa using hs
  | cons q α ih =>
    have hq := hα q (by simp)
    have hs' := simC_step hs hq
    have hα' : ∀ j ∈ α, step C q j = step C' q j := fun j hj => by
      by_cases h : j = q
      · subst h; simp [stepState_congr hs hq]
      · rw [step_ne _ h, step_ne _ h]; exact hα j (by simp [hj])
    obtain ⟨h1, h2, h3⟩ := ih hs' hα'
    refine ⟨h1, fun j hj => ?_, ?_⟩
    · by_cases hj' : j ∈ α
      · exact h2 j hj'
      · simp [hj'] at hj; subst hj
        simp only [exec_cons]; rw [exec_apply_of_not_mem _ hj', exec_apply_of_not_mem _ hj']
        simp [stepState_congr hs hq]
    · simp only [isSched_cons, Active, h3, hq]

lemma simC_reinit (C : Config P X) (u : P → X) : SimC (reinit C u) C := by
  intro j; unfold reinit; split_ifs with h
  · right; exact ⟨trivial, h⟩
  · left; rfl

lemma reinit_of_not_isInit {C : Config P X} {j : P} (h : ¬ (C j).IsInit) (u : P → X) :
    reinit C u j = C j := by simp [reinit, h]

lemma reinit_of_isInit {C : Config P X} {j : P} (h : (C j).IsInit) (u : P → X) :
    reinit C u j = init j (u j) := by simp [reinit, h]

lemma isInit_reinit_iff (C : Config P X) (u : P → X) (j : P) :
    (reinit C u j).IsInit ↔ (C j).IsInit := by
  unfold reinit; split_ifs with h <;> simp [h]

lemma reinit_reinit (C : Config P X) (u u' : P → X) : reinit (reinit C u) u' = reinit C u' := by
  funext j; unfold reinit; split_ifs <;> simp_all

lemma reinit_initC (x u : P → X) : reinit (initC x) u = initC u := by
  funext j; simp [reinit, initC]

/-- Running a schedule after changing the inputs of processes that do not take part in it. -/
lemma exec_reinit (C : Config P X) (u : P → X) {α : List P}
    (hα : ∀ j ∈ α, (C j).IsInit → C j = init j (u j)) :
    exec (reinit C u) α = reinit (exec C α) u ∧ (IsSched δ (reinit C u) α ↔ IsSched δ C α) := by
  have hag : ∀ j ∈ α, reinit C u j = C j := fun j hj => by
    unfold reinit; split_ifs with h
    · exact (hα j hj h).symm
    · rfl
  obtain ⟨h1, h2, h3⟩ := exec_congr (δ := δ) (simC_reinit C u) hag
  refine ⟨funext fun j => ?_, h3⟩
  by_cases hj : j ∈ α
  · rw [h2 j hj, reinit_of_not_isInit (not_isInit_exec_of_mem _ hj)]
  · rw [exec_apply_of_not_mem _ hj]
    simp only [reinit, exec_apply_of_not_mem _ hj]

lemma measure_reinit [Fintype P] (C : Config P X) (u : P → X) : totalDepth (reinit C u) = totalDepth C := by
  unfold totalDepth; congr 1; funext j; unfold reinit; split_ifs with h
  · rw [(St.isInit_iff_depth _).1 h]; rfl
  · rfl

end Locality

/-! ## Reachability -/

section Reach
variable {δ : Protocol P X Y}

lemma Reach.run {C : Config P X} (h : Reach δ C) {α : List P} (hα : IsSched δ C α) :
    Reach δ (exec C α) := by
  obtain ⟨x, β, hβ, rfl⟩ := h
  exact ⟨x, β ++ α, (isSched_append _ _ _).2 ⟨hβ, hα⟩, (exec_append _ _ _).symm⟩

lemma Reach.step {C : Config P X} (h : Reach δ C) {q : P} (hq : Active δ C q) :
    Reach δ (step C q) := h.run (α := [q]) ⟨hq, trivial⟩

lemma reach_initC (x : P → X) : Reach δ (initC x) := ⟨x, [], trivial, rfl⟩

lemma Reach.isInit_eq {C : Config P X} (h : Reach δ C) {j : P} (hj : (C j).IsInit) :
    C j = init j ((C j).input) := by
  obtain ⟨x, β, -, rfl⟩ := h
  by_cases hm : j ∈ β
  · exact absurd hj (not_isInit_exec_of_mem _ hm)
  · rw [exec_apply_of_not_mem _ hm]; rfl

lemma Reach.pid {C : Config P X} (h : Reach δ C) (j : P) : (C j).pid = j := by
  obtain ⟨x, β, -, rfl⟩ := h
  rw [pid_exec]; rfl

lemma reach_reinit {C : Config P X} (h : Reach δ C) (u : P → X) : Reach δ (reinit C u) := by
  obtain ⟨x, β, hβ, rfl⟩ := h
  set u'' : P → X := fun j => if j ∈ β then x j else u j
  have key := exec_reinit (δ := δ) (initC x) u'' (α := β) (fun j hj _ => by simp [u'', initC, hj])
  rw [reinit_initC] at key
  refine ⟨u'', β, key.2.2 hβ, ?_⟩
  rw [key.1]
  funext j
  by_cases hj : j ∈ β
  · simp [reinit, not_isInit_exec_of_mem _ hj]
  · simp [reinit, exec_apply_of_not_mem _ hj, initC, u'', hj]

/-- In a wait-free protocol every reachable configuration can be extended to a final one. -/
lemma WaitFree.exists_final (hw : WaitFree δ) {C : Config P X} (hC : Reach δ C) :
    ∃ α, IsSched δ C α ∧ Final δ (exec C α) := by
  by_contra hne
  push_neg at hne
  obtain ⟨x, β, hβ, rfl⟩ := hC
  -- extend forever
  have hext : ∀ γ : List P, IsSched δ (exec (initC x) β) γ →
      ∃ q, IsSched δ (exec (initC x) β) (γ ++ [q]) := fun γ hγ => by
    have := hne γ hγ
    simp only [Final, not_forall, not_not] at this
    obtain ⟨q, hq⟩ := this
    exact ⟨q, (isSched_concat _ _ _).2 ⟨hγ, hq⟩⟩
  let g : ℕ → {γ : List P // IsSched δ (exec (initC x) β) γ} := fun k =>
    Nat.rec ⟨[], trivial⟩ (fun _ γ => ⟨γ.1 ++ [(hext γ.1 γ.2).choose], (hext γ.1 γ.2).choose_spec⟩) k
  have hg : ∀ k, (g (k + 1)).1 = (g k).1 ++ [(hext (g k).1 (g k).2).choose] := fun k => rfl
  have hlen : ∀ k, (g k).1.length = k := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [hg]; simp [ih]
  have hpre : ∀ k m, k ≤ m → (g k).1 <+: (g m).1 := fun k m hkm => by
    induction m, hkm using Nat.le_induction with
    | base => exact List.prefix_refl _
    | succ m _ ih => rw [hg]; exact ih.trans (List.prefix_append _ _)
  obtain ⟨q0, -⟩ := hext [] trivial
  let f : ℕ → P := fun i => ((β ++ (g (i + 1)).1)[i]?).getD q0
  apply hw x
  refine ⟨f, fun k => ?_⟩
  -- the first k letters of β ++ g k
  have hk : (List.range k).map f = (β ++ (g k).1).take k := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_take]
      simp only [f]
      have hi : i < (β ++ (g (i + 1)).1).length := by simp [hlen]; omega
      rw [List.getElem?_eq_getElem hi, Option.getD_some]
      have hi2 : i < (β ++ (g k).1).length := by simp [hlen] at h2 ⊢; omega
      by_cases hib : i < β.length
      · simp [List.getElem_append_left hib]
      · push_neg at hib
        rw [List.getElem_append_right hib, List.getElem_append_right hib]
        rcases le_total (i + 1) k with hle | hle
        · exact (hpre _ _ hle).getElem _
        · exact ((hpre _ _ hle).getElem _).symm
  rw [hk]
  have hfull : IsSched δ (initC x) (β ++ (g k).1) := (isSched_append _ _ _).2 ⟨hβ, (g k).2⟩
  have := List.take_append_drop k (β ++ (g k).1)
  rw [← this, isSched_append] at hfull
  exact hfull.1

end Reach

end Cslib.NIS
