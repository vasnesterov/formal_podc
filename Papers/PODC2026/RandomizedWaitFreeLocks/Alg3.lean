import Papers.PODC2026.RandomizedWaitFreeLocks.Trace

/-!
# Algorithm 3 (non-abortable `Lock` for the weak adaptive adversary): safety

Section 3.3 and Section 4.3.1 (Lemmas 4.31, 4.32, Corollary 4.33, Lemma 4.34) of Aeini,
Bencivenga, Giakkoupis, Woelfel, *Simple and Efficient Randomized Wait-Free Locks* (PODC 2026).

## Model

* Asynchronous shared memory; one atomic shared-memory operation per step.  The adversary
  (`Act`) chooses which process takes the next step (`sched p j`) or makes an idle process invoke
  `Lock(d)` (`invoke p d`).  Every step also gets a coin `b : Bool`.
* Processes `P`, non-dummy descriptors `D`; a descriptor value is `Option D` with `none` the
  dummy descriptor (`isDone() = True`; executing it is a `tau` step).
* Shared objects: the FAID object `C : ℕ`, the registers `R : ℕ → Option D` (the array
  `R[0..⌊log n⌋]`, over-approximated by an unbounded array), the CAS object
  `L : Option D × ℕ` (fields `desc`, `level`), and the `isDone` registers `done : D → Bool`
  (set by the last step of `execute()`).
* Ghost state: `started : D → Bool` (some `execute()` of the descriptor was invoked),
  `used : D → Bool` (descriptor already passed to a `Lock` call), `clock` (number of steps,
  incremented by *every* step, including stutter steps), and per process its current call
  `call : Option D` (`none` = idle) and the invocation index `callIdx`.
* `pc` is the line about to be executed.  Each step executes one line of the pseudocode
  (lines 48–54 and 35–47); lines without a shared-memory operation (line 51 when the coin says
  "do not write") are stutter (`tau`) steps.  This only inserts `tau` events, which do not affect
  (S1), (S2).
* `invoke p d` is line 48 (`C.FAI()`, the first shared step of the call); it emits `inv p d`.
  It is allowed iff `p` is idle and `d` was never used (the paper's "each `Lock()` call takes a
  distinct descriptor"; the safety proof below does not actually use this assumption).
* `w.execute()` (line 36) consists of two steps: its invocation (`exS w`, sets `started w`) and
  its response (`exE w`, sets `done w`); the thunk's internal steps are not modelled.
* The response of `Lock(D)` is its last shared step, line 54 `C.FAD()`, which emits
  `resp p D (done D)`; we prove the value is always `true` (Lemma 4.34).

## Over-approximations (sound for safety)

The randomness is replaced by nondeterminism: the write-or-not decision of line 51 is the step's
coin `b`; the level `μ = ⌊log C⌋` of line 50 and the new level `ℓ'` of lines 42–46 are chosen
by the adversary (the `j` of `sched p j`).  Hence every execution of the real algorithm (with any
coin outcomes) is a run of this system, and all safety statements transfer.

Invalid actions (scheduling an idle process, invoking a busy process or a used descriptor) leave
the configuration unchanged except for `clock`, and emit `tau`.
-/

namespace Podc.RandomizedWaitFreeLocks.Alg3

open Function

/-- Program counter: the line about to be executed.  `l36s` / `l36e` are the invocation and the
response of `w.execute()` in line 36. -/
inductive PC
  | l50 | l51 | l35 | l36s | l36e | l37 | l38 | l39 | l42 | l47 | l53 | l54
  deriving DecidableEq

/-- Lines 37–47: after `w.execute()` of line 36 has responded. -/
def PC.post : PC → Prop
  | .l37 | .l38 | .l39 | .l42 | .l47 => True
  | _ => False

/-- Local state of a process.  `call = none` means the process is idle. -/
structure Loc (D : Type*) where
  call : Option D := none
  pc : PC := .l50
  callIdx : ℕ := 0
  μ : ℕ := 0
  w : Option D := none
  ℓ : ℕ := 0
  s : Bool := false
  d : Option D := none
  w' : Option D := none

/-- Configurations: shared objects, ghost state and local states. -/
structure Cfg (P D : Type*) where
  C : ℕ
  R : ℕ → Option D
  L : Option D × ℕ
  done : D → Bool
  started : D → Bool
  used : D → Bool
  clock : ℕ
  loc : P → Loc D

/-- Adversary actions: let an idle process invoke `Lock(d)`, or schedule a process; `j` is the
adversarially chosen level (used by lines 50 and 47). -/
inductive Act (P D : Type*)
  | invoke (p : P) (d : D)
  | sched (p : P) (j : ℕ)

variable {P D : Type*}

/-- `isDone()` of a descriptor value; the dummy descriptor is done. -/
def isDoneO (done : D → Bool) : Option D → Bool
  | none => true
  | some ω => done ω

/-- Initial configuration: `C = 0`, `R[j]` and `L.desc` hold the dummy, `L.level = 0`. -/
def init : Cfg P D where
  C := 0
  R := fun _ => none
  L := (none, 0)
  done := fun _ => false
  started := fun _ => false
  used := fun _ => false
  clock := 0
  loc := fun _ => {}

variable [DecidableEq P] [DecidableEq D]

/-- One step of process `p`, which executes `Lock(D₀)` with local state `l` (lines 35–54). -/
def pstep (c : Cfg P D) (p : P) (D₀ : D) (l : Loc D) (j : ℕ) (b : Bool) : Cfg P D × Ev P D :=
  match l.pc with
  -- line 50: `μ ← ⌊log C.Read()⌋` (level chosen by the adversary)
  | .l50 => ({c with loc := update c.loc p {l with pc := .l51, μ := j}}, .tau)
  -- line 51: with some probability `R[μ].Write(D)` (decided by the coin)
  | .l51 => ({c with R := if b then update c.R l.μ (some D₀) else c.R,
                     loc := update c.loc p {l with pc := .l35}}, .tau)
  -- line 35: `(w, ℓ) ← L.Read()`
  | .l35 => ({c with loc := update c.loc p {l with pc := .l36s, w := c.L.1, ℓ := c.L.2}}, .tau)
  -- line 36: invocation of `w.execute()`
  | .l36s => match l.w with
    | none => ({c with loc := update c.loc p {l with pc := .l36e}}, .tau)
    | some ω => ({c with started := update c.started ω true,
                         loc := update c.loc p {l with pc := .l36e}}, .exS ω)
  -- line 36: response of `w.execute()` (sets `w`'s isDone register)
  | .l36e => match l.w with
    | none => ({c with loc := update c.loc p {l with pc := .l37}}, .tau)
    | some ω => ({c with done := update c.done ω true,
                         loc := update c.loc p {l with pc := .l37}}, .exE ω)
  -- line 37: `s ← D.isDone()`
  | .l37 => ({c with loc := update c.loc p {l with pc := .l38, s := c.done D₀}}, .tau)
  -- line 38: `d ← R[ℓ].Read()`
  | .l38 => ({c with loc := update c.loc p {l with pc := .l39, d := c.R l.ℓ}}, .tau)
  -- lines 39–41
  | .l39 =>
    if isDoneO c.done l.d = false then
      ({c with loc := update c.loc p {l with pc := .l42, w' := l.d}}, .tau)
    else if l.s = false then
      ({c with loc := update c.loc p {l with pc := .l42, w' := some D₀}}, .tau)
    else ({c with loc := update c.loc p {l with pc := .l53}}, .tau)
  -- line 42: `λ ← ⌊log C.Read()⌋` (lines 43–46 are local; the new level is the adversary's `j`)
  | .l42 => ({c with loc := update c.loc p {l with pc := .l47}}, .tau)
  -- line 47: `L.CAS((w, ℓ), (w', ℓ'))`
  | .l47 => ({c with L := if c.L = (l.w, l.ℓ) then (l.w', j) else c.L,
                     loc := update c.loc p {l with pc := .l53}}, .tau)
  -- line 53: `until D.isDone() = True`
  | .l53 => if c.done D₀ then ({c with loc := update c.loc p {l with pc := .l54}}, .tau)
      else ({c with loc := update c.loc p {l with pc := .l50}}, .tau)
  -- line 54: `C.FAD()`, the response of `Lock(D)`
  | .l54 => ({c with C := c.C - 1, loc := update c.loc p {l with call := none}},
      .resp p D₀ (c.done D₀))

/-- A step without the clock update. -/
def stepCore (c : Cfg P D) : Act P D → Bool → Cfg P D × Ev P D
  | .invoke p d, _ =>
    if (c.loc p).call = none ∧ c.used d = false then
      ({c with C := c.C + 1, used := update c.used d true,
               loc := update c.loc p {call := some d, pc := .l50, callIdx := c.clock}}, .inv p d)
    else (c, .tau)
  | .sched p j, b =>
    match (c.loc p).call with
    | none => (c, .tau)
    | some D₀ => pstep c p D₀ (c.loc p) j b

/-- The transition function of Algorithm 3: one step, with its event. -/
def step (c : Cfg P D) (a : Act P D) (b : Bool) : Cfg P D × Ev P D :=
  ({(stepCore c a b).1 with clock := c.clock + 1}, (stepCore c a b).2)

/-! ## Basic facts about single steps -/

section StepFacts

variable (c : Cfg P D) (p : P) (D₀ : D) (l : Loc D) (j : ℕ) (b : Bool)

lemma pstep_started (ω : D) :
    (pstep c p D₀ l j b).1.started ω = true ↔
      c.started ω = true ∨ (pstep c p D₀ l j b).2 = .exS ω := by
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  cases pc <;> simp only [pstep] <;> (try split_ifs) <;> (try cases w) <;>
    (simp [update_apply]; try grind)

lemma pstep_done (ω : D) :
    (pstep c p D₀ l j b).1.done ω = true ↔
      c.done ω = true ∨ (pstep c p D₀ l j b).2 = .exE ω := by
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  cases pc <;> simp only [pstep] <;> (try split_ifs) <;> (try cases w) <;>
    (simp [update_apply]; try grind)

lemma pstep_ne_inv (q : P) (d : D) : (pstep c p D₀ l j b).2 ≠ .inv q d := by
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  cases pc <;> simp only [pstep] <;> (try split_ifs) <;> (try cases w) <;> simp

lemma pstep_resp {q : P} {d : D} {r : Bool} (h : (pstep c p D₀ l j b).2 = .resp q d r) :
    q = p ∧ d = D₀ ∧ r = c.done D₀ ∧ l.pc = .l54 ∧ ((pstep c p D₀ l j b).1.loc p).call = none := by
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  cases pc <;> simp only [pstep] at h ⊢ <;> (try split_ifs at h) <;> (try cases w) <;>
    simp_all [eq_comm]

lemma pstep_loc_ne {q : P} (hq : q ≠ p) : (pstep c p D₀ l j b).1.loc q = c.loc q := by
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  cases pc <;> simp only [pstep] <;> (try split_ifs) <;> (try cases w) <;> simp [update_of_ne hq]

lemma pstep_loc_self (h : ∀ d r, (pstep c p D₀ l j b).2 ≠ .resp p d r) :
    ((pstep c p D₀ l j b).1.loc p).call = l.call ∧
      ((pstep c p D₀ l j b).1.loc p).callIdx = l.callIdx := by
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  cases pc <;> simp only [pstep] at h ⊢ <;> (try split_ifs) <;> (try cases w) <;> simp_all

lemma pstep_L (h : (pstep c p D₀ l j b).1.L ≠ c.L) : l.pc = .l47 ∧ c.L = (l.w, l.ℓ) := by
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  cases pc <;> simp only [pstep] at h ⊢ <;> (try split_ifs at h) <;> (try cases w) <;> simp_all

end StepFacts

/-! ## The invariant -/

/-- A descriptor value is *owned*: if it is a non-dummy descriptor that is not done, then it
belongs to a pending `Lock` call. -/
def OD (c : Cfg P D) (x : Option D) : Prop :=
  ∀ ω, x = some ω → c.done ω = false → ∃ q, (c.loc q).call = some ω

/-- Per-process invariant. -/
structure LInv (c : Cfg P D) (l : Loc D) : Prop where
  d : OD c l.d
  w' : OD c l.w'
  /-- Before invoking `w.execute()` in line 36, `L.desc = w` or `w` is done. -/
  at36 : l.pc = .l36s → c.L.1 = l.w ∨ isDoneO c.done l.w = true
  /-- After line 36, `w` is done. -/
  post : l.pc.post → isDoneO c.done l.w = true
  /-- Line 54 is reached only after `D.isDone()` returned `True` in line 53. -/
  at54 : ∀ D₀, l.call = some D₀ → l.pc = .l54 → c.done D₀ = true

/-- The global invariant of Algorithm 3. -/
structure Inv (c : Cfg P D) : Prop where
  /-- Lemma 4.32: a started, not yet done descriptor is `L.desc`. -/
  mutex : ∀ ω, c.started ω = true → c.done ω = false → c.L.1 = some ω
  L : OD c c.L.1
  R : ∀ j, OD c (c.R j)
  loc : ∀ q, LInv c (c.loc q)

/-- `c'` has at least the done descriptors of `c`, and every owned descriptor stays owned. -/
structure Grows (c c' : Cfg P D) : Prop where
  done : ∀ ω, c.done ω = true → c'.done ω = true
  call : ∀ ω q, (c.loc q).call = some ω → c.done ω = false → ∃ q', (c'.loc q').call = some ω

section InvLemmas

variable {c c' : Cfg P D}

omit [DecidableEq P] [DecidableEq D] in
lemma OD.mono {x : Option D} (h : OD c x) (g : Grows c c') : OD c' x := by
  intro ω hx hd
  have h' : c.done ω = false := by
    cases h' : c.done ω
    · rfl
    · rw [g.done ω h'] at hd; cases hd
  obtain ⟨q, hq⟩ := h ω hx h'
  exact g.call ω q hq h'

omit [DecidableEq P] [DecidableEq D] in
lemma isDoneO_mono (g : Grows c c') {x : Option D} (h : isDoneO c.done x = true) :
    isDoneO c'.done x = true := by
  cases x with
  | none => rfl
  | some ω => exact g.done ω h

omit [DecidableEq P] [DecidableEq D] in
lemma LInv.mono {l : Loc D} (h : LInv c l) (g : Grows c c')
    (hL : c'.L = c.L ∨ isDoneO c.done c.L.1 = true) : LInv c' l where
  d := h.d.mono g
  w' := h.w'.mono g
  at36 hpc := by
    rcases h.at36 hpc with h1 | h1
    · rcases hL with hL | hL
      · exact Or.inl (by rw [hL, h1])
      · rw [h1] at hL; exact Or.inr (isDoneO_mono g hL)
    · exact Or.inr (isDoneO_mono g h1)
  post hpc := isDoneO_mono g (h.post hpc)
  at54 D₀ h1 h2 := g.done D₀ (h.at54 D₀ h1 h2)

omit [DecidableEq D] in
lemma grows_frame {p : P} {l' : Loc D} (hd : ∀ ω, c.done ω = true → c'.done ω = true)
    (hloc : c'.loc = update c.loc p l') (hcall : l'.call = (c.loc p).call) : Grows c c' where
  done := hd
  call ω q hq _ := ⟨q, by
    rw [hloc]
    by_cases hqp : q = p
    · subst hqp; simp [hcall, hq]
    · simp [update_of_ne hqp, hq]⟩

omit [DecidableEq D] in
/-- Generic preservation: only process `p`'s local state is replaced. -/
lemma Inv.of_update (hI : Inv c) {p : P} {l' : Loc D}
    (hloc : c'.loc = update c.loc p l') (g : Grows c c')
    (hM : ∀ ω, c'.started ω = true → c'.done ω = false → c'.L.1 = some ω)
    (hL : c'.L = c.L ∨ isDoneO c.done c.L.1 = true)
    (hLod : OD c' c'.L.1) (hR : ∀ j, OD c' (c'.R j)) (hl : LInv c' l') : Inv c' where
  mutex := hM
  L := hLod
  R := hR
  loc q := by
    rw [hloc]
    by_cases hqp : q = p
    · subst hqp; simpa using hl
    · rw [update_of_ne hqp]; exact (hI.loc q).mono g hL

omit [DecidableEq D] in
/-- Preservation for steps that only change `p`'s local state (keeping its call). -/
lemma Inv.frame (hI : Inv c) {p : P} {l' : Loc D} (hcall : l'.call = (c.loc p).call)
    (hl : LInv c l') : Inv {c with loc := update c.loc p l'} := by
  have g : Grows c {c with loc := update c.loc p l'} := grows_frame (fun _ h => h) rfl hcall
  exact hI.of_update rfl g hI.mutex (Or.inl rfl) (hI.L.mono g) (fun j => (hI.R j).mono g)
    (hl.mono g (Or.inl rfl))

end InvLemmas

/-! ## Preservation of the invariant -/

section Preservation

variable {c : Cfg P D}

/-- The invariant is preserved by the steps of a process executing `Lock(D₀)`. -/
lemma Inv.pstep_pres (hI : Inv c) {p : P} {D₀ : D} (hcall : (c.loc p).call = some D₀) (j : ℕ)
    (b : Bool) : Inv (pstep c p D₀ (c.loc p) j b).1 := by
  have hl := hI.loc p
  generalize hlp : c.loc p = l at hl hcall
  rcases l with ⟨call, pc, callIdx, μ, w, ℓ, s, d, w'⟩
  simp only at hcall; subst hcall
  have hown : OD c (some D₀) := fun ω h _ => by cases h; exact ⟨p, by rw [hlp]⟩
  cases pc
  case l50 =>
    exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h), (fun h => h.elim),
      (by intro _ _ h; cases h)⟩
  case l51 =>
    cases b
    · exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h), (fun h => h.elim),
        (by intro _ _ h; cases h)⟩
    · dsimp only [Alg3.pstep]
      refine hI.of_update rfl ?g hI.mutex (Or.inl rfl) (hI.L.mono ?g) (fun k => ?_)
        ⟨hl.d.mono ?g, hl.w'.mono ?g, (by intro h; cases h), (fun h => h.elim),
          (by intro _ _ h; cases h)⟩
      case g => exact grows_frame (fun _ h => h) rfl (by simp [hlp])
      by_cases hk : k = μ
      · subst hk; simp only [ite_true, update_self]
        exact hown.mono (grows_frame (fun _ h => h) rfl (by simp [hlp]))
      · simp only [ite_true, update_of_ne hk]
        exact (hI.R k).mono (grows_frame (fun _ h => h) rfl (by simp [hlp]))
  case l35 =>
    exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (fun _ => Or.inl rfl), (fun h => h.elim),
      (by intro _ _ h; cases h)⟩
  case l36s =>
    cases w with
    | none =>
      exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h), (fun h => h.elim),
        (by intro _ _ h; cases h)⟩
    | some ω =>
      dsimp only [Alg3.pstep]
      refine hI.of_update rfl ?g (fun ω' hs hd => ?_) (Or.inl rfl) (hI.L.mono ?g)
        (fun k => (hI.R k).mono ?g)
        ⟨hl.d.mono ?g, hl.w'.mono ?g, (by intro h; cases h), (fun h => h.elim),
          (by intro _ _ h; cases h)⟩
      case g => exact grows_frame (fun _ h => h) rfl (by simp [hlp])
      by_cases hω : ω' = ω
      · subst hω
        rcases hl.at36 rfl with h | h
        · exact h
        · simp only at hd; simp only [isDoneO] at h; rw [h] at hd; cases hd
      · simp only [update_of_ne hω] at hs; exact hI.mutex ω' hs hd
  case l36e =>
    cases w with
    | none =>
      exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h), (fun _ => rfl),
        (by intro _ _ h; cases h)⟩
    | some ω =>
      dsimp only [Alg3.pstep]
      refine hI.of_update rfl ?g (fun ω' hs hd => ?_) (Or.inl rfl) (hI.L.mono ?g)
        (fun k => (hI.R k).mono ?g)
        ⟨hl.d.mono ?g, hl.w'.mono ?g, (by intro h; cases h), (fun _ => by simp [isDoneO]),
          (by intro _ _ h; cases h)⟩
      case g =>
        exact grows_frame (fun ω' h => by by_cases hω : ω' = ω <;> simp [hω, h])
          rfl (by simp [hlp])
      have hω : ω' ≠ ω := by rintro rfl; simp at hd
      simp only [update_of_ne hω] at hd
      exact hI.mutex ω' hs hd
  case l37 =>
    exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h),
      (fun _ => hl.post trivial), (by intro _ _ h; cases h)⟩
  case l38 =>
    exact hI.frame (by simp [hlp]) ⟨hI.R ℓ, hl.w', (by intro h; cases h),
      (fun _ => hl.post trivial), (by intro _ _ h; cases h)⟩
  case l39 =>
    dsimp only [Alg3.pstep]
    split_ifs
    · exact hI.frame (by simp [hlp]) ⟨hl.d, hl.d, (by intro h; cases h),
        (fun _ => hl.post trivial), (by intro _ _ h; cases h)⟩
    · exact hI.frame (by simp [hlp]) ⟨hl.d, hown, (by intro h; cases h),
        (fun _ => hl.post trivial), (by intro _ _ h; cases h)⟩
    · exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h),
        (fun h => h.elim), (by intro _ _ h; cases h)⟩
  case l42 =>
    exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h),
      (fun _ => hl.post trivial), (by intro _ _ h; cases h)⟩
  case l47 =>
    dsimp only [Alg3.pstep]
    have hpost : isDoneO c.done w = true := hl.post trivial
    split_ifs with hL
    · refine hI.of_update rfl ?g (fun ω hs hd => ?_) (Or.inr (by rw [hL]; exact hpost))
        (hl.w'.mono ?g) (fun k => (hI.R k).mono ?g)
        ⟨hl.d.mono ?g, hl.w'.mono ?g, (by intro h; cases h), (fun h => h.elim),
          (by intro _ _ h; cases h)⟩
      case g => exact grows_frame (fun _ h => h) rfl (by simp [hlp])
      have h1 := hI.mutex ω hs hd
      rw [hL] at h1; simp only at h1; subst h1
      simp only [isDoneO] at hpost; simp only at hd; rw [hpost] at hd; cases hd
    · exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h),
        (fun h => h.elim), (by intro _ _ h; cases h)⟩
  case l53 =>
    dsimp only [Alg3.pstep]
    split_ifs with h
    · exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h),
        (fun h => h.elim), (by intro _ h1 _; cases h1; exact h)⟩
    · exact hI.frame (by simp [hlp]) ⟨hl.d, hl.w', (by intro h; cases h),
        (fun h => h.elim), (by intro _ _ h; cases h)⟩
  case l54 =>
    dsimp only [Alg3.pstep]
    have hd54 : c.done D₀ = true := hl.at54 D₀ rfl rfl
    refine hI.of_update rfl ?g hI.mutex (Or.inl rfl) (hI.L.mono ?g) (fun k => (hI.R k).mono ?g)
      ⟨hl.d.mono ?g, hl.w'.mono ?g, (by intro h; cases h), (fun h => h.elim),
        (by intro _ h1 _; cases h1)⟩
    case g =>
      refine ⟨fun _ h => h, fun ω q hq hd => ⟨q, ?_⟩⟩
      by_cases hqp : q = p
      · subst hqp; rw [hlp] at hq; cases hq; rw [hd54] at hd; cases hd
      · simp [update_of_ne hqp, hq]

/-- The invariant is preserved by every step. -/
lemma Inv.step_pres (hI : Inv c) (a : Act P D) (b : Bool) : Inv (step c a b).1 := by
  have h : Inv (stepCore c a b).1 := by
    cases a with
    | invoke p d =>
      dsimp only [stepCore]
      split_ifs with h
      · refine hI.of_update rfl ?g hI.mutex (Or.inl rfl) (hI.L.mono ?g)
          (fun k => (hI.R k).mono ?g)
          ⟨(by intro _ h; cases h), (by intro _ h; cases h), (by intro h; cases h),
            (fun h => h.elim), (by intro _ _ h; cases h)⟩
        case g =>
          refine ⟨fun _ h => h, fun ω q hq _ => ⟨q, ?_⟩⟩
          by_cases hqp : q = p
          · subst hqp; rw [h.1] at hq; cases hq
          · simp [update_of_ne hqp, hq]
      · exact hI
    | sched p j =>
      dsimp only [stepCore]
      split
      · exact hI
      · exact hI.pstep_pres (by assumption) j b
  have g : Grows (stepCore c a b).1 (step c a b).1 :=
    ⟨fun _ h => h, fun _ q hq _ => ⟨q, hq⟩⟩
  exact ⟨h.mutex, h.L, h.R, fun q => (h.loc q).mono g (Or.inl rfl)⟩

omit [DecidableEq P] [DecidableEq D] in
lemma inv_init : Inv (init : Cfg P D) where
  mutex _ h := by cases h
  L _ h := by cases h
  R _ _ h := by cases h
  loc _ := ⟨(by intro _ h; cases h), (by intro _ h; cases h), (by intro h; cases h),
    (fun h => h.elim), (by intro _ h; cases h)⟩

/-- The invariant holds in every reachable configuration. -/
lemma Inv.reachable {c : Cfg P D} (h : Reachable init step c) : Inv c :=
  Reachable.induction (init := init) (step := step) (Q := Inv) inv_init (fun _ a b _ hI => Inv.step_pres hI a b) h

end Preservation

/-! ## Coherence with the events, and the main results -/

section Main

/-- The ghost state is coherent with the emitted events. -/
lemma coherent : Coherent (P := P) (D := D) init step (fun c d => c.started d = true)
    (fun c d => c.done d = true) (fun c p => (c.loc p).call) (fun c p => (c.loc p).callIdx)
    Cfg.clock where
  clock_init := rfl
  clock_step _ _ _ _ := rfl
  started_init _ h := by cases h
  started_step c a b d _ := by
    cases a with
    | invoke p d' => dsimp only [step, stepCore]; split_ifs <;> simp
    | sched p j =>
      dsimp only [step, stepCore]
      split
      · simp
      · exact pstep_started ..
  done_init _ h := by cases h
  done_step c a b d _ := by
    cases a with
    | invoke p d' => dsimp only [step, stepCore]; split_ifs <;> simp
    | sched p j =>
      dsimp only [step, stepCore]
      split
      · simp
      · exact pstep_done ..
  call_init _ := rfl
  call_inv c a b p d _ h := by
    cases a with
    | invoke p' d' =>
      dsimp only [step, stepCore] at h ⊢
      split_ifs at h ⊢ with hc
      · cases h; simp [hc.1]
    | sched p' j =>
      dsimp only [step, stepCore] at h ⊢
      split at h
      · cases h
      · exact absurd h (pstep_ne_inv _ _ _ _ _ _ _ _)
  call_resp c a b p d r _ h := by
    cases a with
    | invoke p' d' =>
      dsimp only [step, stepCore] at h
      split_ifs at h
    | sched p' j =>
      dsimp only [step, stepCore] at h ⊢
      cases hc : (c.loc p').call with
      | none => simp only [hc] at h; cases h
      | some D₀ =>
        simp only [hc] at h ⊢
        obtain ⟨rfl, rfl, rfl, -, h5⟩ := pstep_resp _ _ _ _ _ _ h
        exact ⟨hc, h5, Iff.rfl⟩
  call_other c a b p _ hinv hresp := by
    cases a with
    | invoke p' d' =>
      dsimp only [step, stepCore] at hinv ⊢
      split_ifs at hinv ⊢ with hc
      · have hp : p ≠ p' := by rintro rfl; exact hinv d' rfl
        simp [update_of_ne hp]
      · simp
    | sched p' j =>
      dsimp only [step, stepCore] at hresp ⊢
      cases hc : (c.loc p').call with
      | none => simp
      | some D₀ =>
        simp only [hc] at hresp ⊢
        by_cases hp : p = p'
        · subst hp; exact pstep_loc_self _ _ _ _ _ _ hresp
        · simp [pstep_loc_ne _ _ _ _ _ _ hp]

variable {c : Cfg P D}

/-- **Lemma 4.31** (state version).  A step that changes `L` (a successful CAS in line 47) is
taken only when the current `L.desc` is done (the dummy counts as done).  Since `done` is
monotone, the old `L.desc` stays done forever. -/
theorem lemma_4_31 (hc : Reachable init step c) (a : Act P D) (b : Bool)
    (h : (step c a b).1.L ≠ c.L) : isDoneO c.done c.L.1 = true := by
  have hI := Inv.reachable hc
  cases a with
  | invoke p d =>
    dsimp only [step, stepCore] at h
    split_ifs at h <;> exact absurd rfl h
  | sched p j =>
    dsimp only [step, stepCore] at h
    split at h
    · exact absurd rfl h
    · obtain ⟨h1, h2⟩ := pstep_L _ _ _ _ _ _ h
      rw [h2]
      exact (hI.loc p).post (by rw [h1]; trivial)

/-- **Lemma 4.32** (state version).  Throughout the execution interval of `ω`'s thunk (i.e.
while some `ω.execute()` has been invoked but none has responded), `L.desc = ω`. -/
theorem lemma_4_32 (hc : Reachable init step c) (ω : D) (hs : c.started ω = true)
    (hd : c.done ω = false) : c.L.1 = some ω :=
  (Inv.reachable hc).mutex ω hs hd

/-- **Lemma 4.34** (state version).  If `Lock(ω)` responds (line 54), then `ω` is done, so the
response value `done ω` is `true`. -/
theorem lemma_4_34 (hc : Reachable init step c) {a : Act P D} {b : Bool} {p : P} {d : D}
    {r : Bool} (h : (step c a b).2 = .resp p d r) : c.done d = true ∧ r = true := by
  have hI := Inv.reachable hc
  cases a with
  | invoke p' d' =>
    dsimp only [step, stepCore] at h
    split_ifs at h
  | sched p' j =>
    dsimp only [step, stepCore] at h
    split at h
    · cases h
    · rename_i D₀ hcall
      obtain ⟨rfl, rfl, rfl, h4, -⟩ := pstep_resp _ _ _ _ _ _ h
      have := (hI.loc p).at54 d hcall h4
      exact ⟨this, this⟩

/-- **Corollary 4.33 and Lemma 4.34**: every execution of Algorithm 3 satisfies (S1) (mutual
exclusion of thunk execution intervals) and (S2) (each thunk's execution interval lies within a
single `Lock` call on its descriptor; a call returns `true` iff it responds after the thunk has
been executed). -/
theorem alg3_safety (xs : List (Act P D × Bool)) :
    S1 (run init step xs).2 ∧ S2 (run init step xs).2 := by
  refine s1_s2_of_invariants coherent ?_ ?_ ?_ xs
  · intro c hc d₁ d₂ hne hs₁ hd₁ hs₂ hd₂
    have h₁ := lemma_4_32 hc d₁ hs₁ (by simpa using hd₁)
    have h₂ := lemma_4_32 hc d₂ hs₂ (by simpa using hd₂)
    rw [h₁] at h₂; exact hne (Option.some_injective _ h₂)
  · intro c hc d hs hd
    have hd' : c.done d = false := by simpa using hd
    exact (Inv.reachable hc).L d (lemma_4_32 hc d hs hd') hd'
  · intro c a b p d r hc h _
    exact (lemma_4_34 hc h).1

/-- **Lemma 4.34** (trace version): every response of a `Lock(d)` call returns `true` (the call
is successful), and it happens after some `d.execute()` has responded. -/
theorem alg3_resp_true (xs : List (Act P D × Bool)) (j : ℕ) (p : P) (d : D) (r : Bool)
    (h : (run init step xs).2[j]? = some (.resp p d r)) :
    r = true ∧ ∃ e < j, (run init step xs).2[e]? = some (.exE d) := by
  have hj : j < xs.length := by
    rw [← run_length init step xs]
    rcases Nat.lt_or_ge j (run init step xs).2.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have hr : r = true := by
    rw [(run_take_succ init step xs j hj).2] at h
    exact (lemma_4_34 ⟨_, rfl⟩ (Option.some_injective _ h)).2
  exact ⟨hr, ((alg3_safety xs).2.2 j p d r h).1 hr⟩

end Main

/-! ## Non-vacuity: a run in which a thunk is executed and its `Lock` call responds -/

section Example

/-- One process, one descriptor: the process writes its descriptor to `R[0]`, promotes it to `L`,
executes it in its next `HelpAndPromote()`, and returns. -/
def exampleRun : List (Act Unit Unit × Bool) :=
  [(.invoke () (), false), (.sched () 0, false), (.sched () 0, true)] ++
    List.replicate 19 (.sched () 0, false)

example : (run init step exampleRun).2 =
    [.inv () (), .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau, .tau,
      .tau, .exS (), .exE (), .tau, .tau, .tau, .tau, .resp () () true] := by
  decide

end Example

end Podc.RandomizedWaitFreeLocks.Alg3
