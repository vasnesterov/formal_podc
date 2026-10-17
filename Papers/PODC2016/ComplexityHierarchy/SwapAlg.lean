import Papers.PODC2016.ComplexityHierarchy.SwapAlgAbstract
import Cslib.Computability.Distributed.SharedMemory.Objects.Swap

/-!
# Swap and read (Section 8 of [EGSZ16]): Algorithm 1 with double-collect scans — safety

[EGSZ16] F. Ellen, R. Gelashvili, N. Shavit, L. Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016 (arXiv 1607.06139), Section 8, Algorithm 1.

The algorithm `swapAlg k m P` for processes `P`, values `Fin k` and `m` locations supporting
`read` and `swap` (the library's readable swap object `rswapObj`). A location stores a *tagged* lap vector `(tag, laps)`, where the
tag `some (p, c)` identifies the `c`-th swap of process `p` (the paper's "process identifier and
strictly increasing sequence number") and `none` the initial value. The scan of the `m` locations
is the double collect: read `X_1, …, X_m` one by one, repeatedly, until two consecutive collects
return the same values; then the local computation of lines 4–12 (`after`) is performed.

## Main results

* `swapAlg_safe`: in every finite execution (one-shot or not) decisions agree and are inputs of
  participating processes, provided `|P| ≤ m + 1`.
* `swapAlg_solves`: `(swapAlg k m P).Solves (consensus P (Fin k))`.

## Proof: reduction to atomic scans

A process `q` in the middle of a double collect is `Ready` if its previous collect `pv` is
complete, the reads of the current collect so far returned `pv`, and the locations not yet
read still contain `pv`. Because tags are never reused, a ready process's scan, if it succeeds,
returns `pv` = the memory at the end of its previous collect, so it can be linearized there.
`simInv` states that for *every* set `Q` of ready processes, the abstract configuration in which
the processes of `Q` have already performed their (atomic) scan, returning `pv`, and all other
scanning processes are about to scan, satisfies the abstract invariant `AInv` of
`SwapAlgAbstract.lean`. This is proved by induction on executions: a read is either invisible in
the abstract system or (when a collect completes and the memory equals it) an abstract scan; a
swap is an abstract swap; it destroys the readiness of every process that has not yet re-read
the swapped location in its current collect (tags are fresh).

## Modelling choices and differences from the paper

* Processes: any finite type `P` with `|P| ≤ m + 1` (the paper: `n` processes, `m = n − 1`);
  values `Fin k` for any `k ≥ 1` (the paper: `k = n`); `m ≥ 1` locations. The bound
  `|P| ≤ m + 1` is necessary: with `3` processes, `2` values and `1` location there is a
  10-step execution (with atomic scans, hence also with double collects) in which two processes
  decide differently (found by model checking).
* Asynchronous deterministic processes, atomic `read`/`swap` on each location, consensus as a
  one-shot task (CSLib `Cslib.SharedMemory` + `Cslib/Computability/Distributed/SharedMemory/Consensus.lean`). A process
  that has decided and is invoked again returns its decision again; safety is proved for all
  executions, not only one-shot ones.
* Anonymity: as in the paper, swap arguments carry `(process id, sequence number)`; identifiers
  are used for nothing else. Strictly speaking this is not an anonymous protocol (the paper calls
  it anonymous); without unique tags the double collect is not a linearizable scan.
* Lemma 8.2 is false as stated for every scan `S` with `ℓ_v(S) = 1`: it would require an earlier
  scan `T` with `ℓ_v(T) = 0` in which all laps are `0` (since `ℓ_{v'}(T) ≤ ℓ_v(T)`), but every
  scanner has `ℓ_{input} ≥ 1`, so no such `T` exists. It is only applied with `ℓ_v(S) ≥ 2`
  (Lemma 8.4), where the proof works. Here it is replaced by the
  invariant "every lap value in the system is at most the floor plus one" (`Bnd`).
* Lemma 8.6 proves only weak validity ("if all inputs are `x`, only `x` is decided"); we prove
  the standard validity (every decision is the input of a participating process).
* The paper obtains linearizable scans from the double collect with `(id, seq)` tags, citing
  [AAD+93], and then argues with scans as atomic steps (Lemmas 8.3–8.5); only the composition
  step (that the algorithm with double-collect scans behaves like the one with atomic scans) is
  left implicit. Here it is proved by the simulation `SInv.sim`.
* Lemma 8.7's bound of `3n − 2` scans in solo runs is not formalized; we prove termination of
  solo runs from every reachable configuration (`SwapAlgOF.lean`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy.SwapRead

open Cslib.SharedMemory Finset

/-- Contents of a location: a tag (`none` = initial value, `some (p, c)` = written by the
`c`-th swap of `p`) and a lap vector. -/
abbrev SVal (k : ℕ) (P : Type) := Option (P × ℕ) × Laps k

variable {k m : ℕ} {P : Type}

/-- Local state of a process of Algorithm 1 with double-collect scans. -/
structure DLoc (k m : ℕ) (P : Type) where
  /-- Program counter. -/
  ph : Ph k m
  /-- The local laps `ℓ_0, …, ℓ_{k-1}`. -/
  l : Laps k
  /-- Laps returned by the last swap. -/
  s : Laps k
  /-- The input. -/
  inp : Fin k
  /-- Number of swaps performed so far (the sequence number of the next swap). -/
  seq : ℕ
  /-- The previous complete collect (`none` in the first collect of a scan). -/
  prev : Option (Fin m → SVal k P)
  /-- The next location to read in the current collect. -/
  idx : Fin m
  /-- Values read in the current collect (meaningful below `idx`). -/
  cur : Fin m → SVal k P

/-- The lap vectors of a collect. -/
def vecs (c : Fin m → SVal k P) : Fin m → Laps k := fun j => (c j).2

variable [NeZero k] [NeZero m] [DecidableEq P]

/-- The local state after reading `r` from location `d.idx` during a scan. -/
def readStep (d : DLoc k m P) (r : SVal k P) : DLoc k m P :=
  if h : d.idx.val + 1 < m then
    { d with idx := ⟨d.idx.val + 1, h⟩, cur := Function.update d.cur d.idx r }
  else if d.prev = some (Function.update d.cur d.idx r) then
    { d with ph := (after d.l d.s (vecs (Function.update d.cur d.idx r))).1,
             l := (after d.l d.s (vecs (Function.update d.cur d.idx r))).2,
             cur := Function.update d.cur d.idx r }
  else
    { d with prev := some (Function.update d.cur d.idx r), idx := 0,
             cur := Function.update d.cur d.idx r }

/-- The local state after a swap returning `r`. -/
def afterSwap (d : DLoc k m P) (r : SVal k P) : DLoc k m P :=
  { d with ph := .scan, s := r.2, seq := d.seq + 1, prev := none, idx := 0 }

/-- The local state after invocation with input `x` (line 1). -/
def startLoc (d : DLoc k m P) (x : Fin k) : DLoc k m P :=
  { d with ph := .scan, l := Function.update 0 x 1, s := 0, inp := x, prev := none, idx := 0 }

/-- The initial local state. -/
def dInit : DLoc k m P := ⟨.idle, 0, 0, 0, 0, none, 0, fun _ => (none, 0)⟩

variable (k m P)

/-- Algorithm 1 of [EGSZ16]: obstruction-free consensus on `Fin k` for processes `P` from `m`
locations supporting `read` and `swap`, all initially `(none, 0)`. -/
def swapAlg :
    Impl (taskObj (Fin k) (Fin k)) (fun _ : Fin m => rswapObj (SVal k P) (none, 0)) P
      (DLoc k m P) where
  memInit _ := (none, 0)
  locInit _ := dInit
  invoke _ d x := match d.ph with
    | .idle => startLoc d x
    | _ => d
  act p d := match d.ph with
    | .idle => .ret (0 : Fin k) d
    | .scan => .access d.idx .read (fun r => readStep d r)
    | .swap j => .access j (.swap (some (p, d.seq), d.l)) (fun r => afterSwap d r)
    | .done w => .ret w d

/-- Configurations of the algorithm. -/
abbrev DCfg := Config (taskObj (Fin k) (Fin k)) (fun _ : Fin m => rswapObj (SVal k P) (none, 0))
  P (DLoc k m P)

/-- Labels of executions. -/
abbrev DLbl := Label P (taskObj (Fin k) (Fin k))

variable {k m P}

/-! ### Steps -/

section Steps

variable {C C' : DCfg k m P} {q : P}

lemma act_scan {d : DLoc k m P} (h : d.ph = .scan) :
    (swapAlg k m P).act q d = .access d.idx .read (fun r => readStep d r) := by
  simp [swapAlg, h]

lemma act_swap {d : DLoc k m P} {j : Fin m} (h : d.ph = .swap j) :
    (swapAlg k m P).act q d = .access j (.swap (some (q, d.seq), d.l)) (fun r => afterSwap d r) := by
  simp [swapAlg, h]

lemma act_done {d : DLoc k m P} {w : Fin k} (h : d.ph = .done w) :
    (swapAlg k m P).act q d = .ret w d := by
  simp [swapAlg, h]

lemma act_idle {d : DLoc k m P} (h : d.ph = .idle) :
    (swapAlg k m P).act q d = .ret (0 : Fin k) d := by
  simp [swapAlg, h]

lemma invoke_idle {d : DLoc k m P} {x : Fin k} (h : d.ph = .idle) :
    (swapAlg k m P).invoke q d x = startLoc d x := by
  simp [swapAlg, h]

lemma invoke_ne_idle {d : DLoc k m P} {x : Fin k} (h : d.ph ≠ .idle) :
    (swapAlg k m P).invoke q d x = d := by
  cases hd : d.ph <;> simp_all [swapAlg]

lemma step_tau_scan (hp : C.pend q ≠ none) (hph : (C.loc q).ph = .scan) :
    (swapAlg k m P).step C (.tau q) =
      some ⟨Function.update C.loc q (readStep (C.loc q) (C.mem (C.loc q).idx)), C.pend, C.mem⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, act_scan hph]
  congr 2
  exact Function.update_eq_self _ _

lemma step_tau_swap {j : Fin m} (hp : C.pend q ≠ none) (hph : (C.loc q).ph = .swap j) :
    (swapAlg k m P).step C (.tau q) =
      some ⟨Function.update C.loc q (afterSwap (C.loc q) (C.mem j)), C.pend,
        Function.update C.mem j (some (q, (C.loc q).seq), (C.loc q).l)⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, act_swap hph]

end Steps

/-! ### Abstraction to the atomic-scan algorithm -/

/-- The abstract local state of a process (its scan, if in progress, not yet linearized). -/
def toA (d : DLoc k m P) : ALoc k m := ⟨d.ph, d.l, d.s, d.inp⟩

/-- The abstract local state of a ready process whose scan is linearized at the end of its
previous collect `pv`: it has performed the atomic scan returning `pv`. -/
def scannedA (d : DLoc k m P) : ALoc k m :=
  match d.prev with
  | some pv => ⟨(after d.l d.s (vecs pv)).1, (after d.l d.s (vecs pv)).2, d.s, d.inp⟩
  | none => toA d

/-- The abstract configuration in which the processes of `Q` have performed their scans. -/
def absCfg (Q : Finset P) (C : DCfg k m P) : ACfg k m P :=
  ⟨fun j => (C.mem j).2, fun p => if p ∈ Q then scannedA (C.loc p) else toA (C.loc p)⟩

/-- A process with local state `d` is in the middle of a double collect whose previous collect
`pv` is complete, and every location contains (or, if already re-read in the current collect,
contained when re-read) its value in `pv`, for memory `mem`. -/
def ReadyL (d : DLoc k m P) (mem : Fin m → SVal k P) : Prop :=
  d.ph = .scan ∧ ∃ pv, d.prev = some pv ∧ (∀ j, j < d.idx → d.cur j = pv j) ∧
    ∀ j, d.idx ≤ j → mem j = pv j

/-- `q` is ready in `C`. -/
def Ready (C : DCfg k m P) (q : P) : Prop := ReadyL (C.loc q) C.mem

lemma readyL_continue {d : DLoc k m P} {mem : Fin m → SVal k P} (hph : d.ph = .scan)
    (hlt : d.idx.val + 1 < m)
    (hR : ReadyL { d with idx := ⟨d.idx.val + 1, hlt⟩,
                          cur := Function.update d.cur d.idx (mem d.idx) } mem) :
    ReadyL d mem := by
  obtain ⟨-, pv, hpv, hcur, hm⟩ := hR
  simp only at hpv hcur hm
  refine ⟨hph, pv, hpv, fun j hj => ?_, fun j hj => ?_⟩
  · have := hcur j (by rw [Fin.lt_def] at hj ⊢; simp only; omega)
    rwa [Function.update_of_ne (ne_of_lt hj)] at this
  · by_cases hjj : j = d.idx
    · subst hjj
      have := hcur d.idx (by rw [Fin.lt_def]; simp)
      rwa [Function.update_self] at this
    · refine hm j ?_
      rw [Fin.le_def] at hj ⊢
      have : j.val ≠ d.idx.val := fun h' => hjj (Fin.ext h')
      simp only; omega

lemma readyL_complete {d : DLoc k m P} {mem : Fin m → SVal k P} (hph : d.ph = .scan)
    (hge : ¬ d.idx.val + 1 < m)
    (hpv : d.prev = some (Function.update d.cur d.idx (mem d.idx))) : ReadyL d mem := by
  refine ⟨hph, _, hpv, fun j hj => ?_, fun j hj => ?_⟩
  · rw [Function.update_of_ne (ne_of_lt hj)]
  · have : j = d.idx := Fin.ext (by have := j.isLt; rw [Fin.le_def] at hj; omega)
    subst this; rw [Function.update_self]

lemma readyL_restart {d : DLoc k m P} {mem : Fin m → SVal k P} {c : Fin m → SVal k P}
    (hR : ReadyL { d with prev := some c, idx := 0, cur := c } mem) : ∀ j, mem j = c j := by
  obtain ⟨-, pv, hpv, -, hm⟩ := hR
  simp only [Option.some.injEq] at hpv hm
  intro j; rw [hpv]; exact hm j (by rw [Fin.le_def]; simp)

/-- The tag `t` is older than the current sequence number of its writer. -/
def TagOK (C : DCfg k m P) (t : Option (P × ℕ)) : Prop :=
  ∀ p c, t = some (p, c) → c < (C.loc p).seq

lemma TagOK.mono {C C' : DCfg k m P} {t : Option (P × ℕ)} (h : TagOK C t)
    (hs : ∀ p, (C.loc p).seq ≤ (C'.loc p).seq) : TagOK C' t :=
  fun p c ht => (h p c ht).trans_le (hs p)

lemma ready_congr {C C' : DCfg k m P} {r : P} (hl : C'.loc r = C.loc r) (hm : C'.mem = C.mem) :
    Ready C' r ↔ Ready C r := by
  unfold Ready; rw [hl, hm]

lemma absCfg_loc (Q : Finset P) (C : DCfg k m P) (p : P) :
    (absCfg Q C).loc p = if p ∈ Q then scannedA (C.loc p) else toA (C.loc p) := rfl

lemma absCfg_ext {Q Q' : Finset P} {C C' : DCfg k m P}
    (hm : ∀ j, (C'.mem j).2 = (C.mem j).2) (hl : ∀ p, (absCfg Q' C').loc p = (absCfg Q C).loc p) :
    absCfg Q' C' = absCfg Q C := by
  have h1 : (absCfg Q' C').mem = (absCfg Q C).mem := funext hm
  have h2 : (absCfg Q' C').loc = (absCfg Q C).loc := funext hl
  cases h : absCfg Q' C'; cases h' : absCfg Q C
  rw [h, h'] at h1 h2; simp only at h1 h2; rw [h1, h2]

lemma readStep_cases (d : DLoc k m P) (v : SVal k P) :
    (∃ h : d.idx.val + 1 < m,
      readStep d v = { d with idx := ⟨d.idx.val + 1, h⟩, cur := Function.update d.cur d.idx v }) ∨
    (¬ d.idx.val + 1 < m ∧ d.prev = some (Function.update d.cur d.idx v) ∧
      readStep d v = { d with ph := (after d.l d.s (vecs (Function.update d.cur d.idx v))).1,
                              l := (after d.l d.s (vecs (Function.update d.cur d.idx v))).2,
                              cur := Function.update d.cur d.idx v }) ∨
    (¬ d.idx.val + 1 < m ∧ d.prev ≠ some (Function.update d.cur d.idx v) ∧
      readStep d v = { d with prev := some (Function.update d.cur d.idx v), idx := 0,
                              cur := Function.update d.cur d.idx v }) := by
  unfold readStep
  by_cases h1 : d.idx.val + 1 < m
  · left; exact ⟨h1, by simp [h1]⟩
  · by_cases h2 : d.prev = some (Function.update d.cur d.idx v)
    · right; left; exact ⟨h1, h2, by simp [h1, h2]⟩
    · right; right; exact ⟨h1, h2, by simp [h1, h2]⟩

/-! ### The safety invariant -/

variable [Fintype P]

/-- The safety invariant of Algorithm 1. -/
structure SInv (α : List (DLbl k P)) (C : DCfg k m P) : Prop where
  freshMem : ∀ j, TagOK C (C.mem j).1
  freshCur : ∀ q j, TagOK C ((C.loc q).cur j).1
  freshPrev : ∀ q pv, (C.loc q).prev = some pv → ∀ j, TagOK C (pv j).1
  idle : ∀ q, (C.loc q).ph = .idle → opsOf α q = [] ∧ C.pend q = none
  inp : ∀ q, (C.loc q).ph ≠ .idle → inputs α q = some (C.loc q).inp
  resp : ∀ q (w : (taskObj (Fin k) (Fin k)).Resp), w ∈ respsOf α q → (C.loc q).ph = .done w
  sim : ∀ Q : Finset P, (∀ q ∈ Q, Ready C q) → AInv (absCfg Q C)

lemma sInv_init : SInv [] (swapAlg k m P).initCfg where
  freshMem j p c h := by simp [Impl.initCfg, swapAlg] at h
  freshCur q j p c h := by simp [Impl.initCfg, swapAlg, dInit] at h
  freshPrev q pv h := by simp [Impl.initCfg, swapAlg, dInit] at h
  idle q _ := ⟨rfl, rfl⟩
  inp q h := by simp [Impl.initCfg, swapAlg, dInit] at h
  resp q w h := by simp at h
  sim Q hQ := by
    have : absCfg Q (swapAlg k m P).initCfg = aInit := by
      have h1 : ∀ p, p ∉ Q := fun p hp => by
        have := (hQ p hp).1; simp [Impl.initCfg, swapAlg, dInit] at this
      simp only [absCfg, aInit, h1, ↓reduceIte]
      rfl
    rw [this]; exact aInv_init

/-! ### Step lemmas for the invariant -/

lemma acfg_ext {a b : ACfg k m P} (hm : a.mem = b.mem) (hl : ∀ p, a.loc p = b.loc p) : a = b := by
  cases a; cases b; simp only [ACfg.mk.injEq]; exact ⟨hm, funext hl⟩

@[simp] lemma readStep_cur (d : DLoc k m P) (v : SVal k P) :
    (readStep d v).cur = Function.update d.cur d.idx v := by
  rcases readStep_cases d v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]

@[simp] lemma readStep_seq (d : DLoc k m P) (v : SVal k P) : (readStep d v).seq = d.seq := by
  rcases readStep_cases d v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]

@[simp] lemma readStep_s (d : DLoc k m P) (v : SVal k P) : (readStep d v).s = d.s := by
  rcases readStep_cases d v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]

@[simp] lemma readStep_inp (d : DLoc k m P) (v : SVal k P) : (readStep d v).inp = d.inp := by
  rcases readStep_cases d v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]

lemma readStep_prev (d : DLoc k m P) (v : SVal k P) :
    (readStep d v).prev = d.prev ∨ (readStep d v).prev = some (Function.update d.cur d.idx v) := by
  rcases readStep_cases d v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] <;> simp

lemma readStep_ph_ne_idle {d : DLoc k m P} (hd : d.ph = .scan) (v : SVal k P) :
    (readStep d v).ph ≠ .idle := by
  rcases readStep_cases d v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  · simp [hd]
  · exact after_ph_ne_idle _ _ _
  · simp [hd]

lemma readStep_ph_ne_done {d : DLoc k m P} (hd : d.ph = .scan) (v : SVal k P) {w : Fin k}
    (hw : (readStep d v).ph = .done w) : (after d.l d.s (vecs (Function.update d.cur d.idx v))).1 = .done w := by
  rcases readStep_cases d v with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> rw [h] at hw
  · simp [hd] at hw
  · exact hw
  · simp [hd] at hw

lemma inputs_append_of_ne_nil {α β : List (DLbl k P)} {r : P} (h : inputs α r ≠ none) :
    inputs (α ++ β) r = inputs α r := by
  simp only [inputs, opsOf_append] at h ⊢
  rw [List.head?_append]
  cases hh : (opsOf α r).head? with
  | none => exact absurd hh h
  | some x => rfl

variable {α : List (DLbl k P)} {C C' : DCfg k m P} {q : P}

lemma SInv.step_inv {x : Fin k} (hI : SInv α C)
    (h : (swapAlg k m P).step C (.inv q x) = some C') : SInv (α ++ [.inv q x]) C' := by
  obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hresp : ∀ r, respsOf (α ++ [.inv q x]) r = respsOf α r := by simp [respsOf, Label.retOf]
  have hops : ∀ r, r ≠ q → opsOf (α ++ [.inv q x]) r = opsOf α r := by
    intro r hr; simp [opsOf, Label.invOf, Ne.symm hr]
  have hpend' : ∀ r, r ≠ q → C'.pend r = C.pend r := by
    intro r hr; simp [hpend, Function.update_of_ne hr]
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := by
    intro r hr; simp [hloc, Function.update_of_ne hr]
  by_cases hph : (C.loc q).ph = .idle
  · have hlq : C'.loc q = startLoc (C.loc q) x := by rw [hloc, invoke_idle hph]; simp
    have hseq : ∀ r, (C.loc r).seq ≤ (C'.loc r).seq := by
      intro r; by_cases hr : r = q
      · subst hr; rw [hlq]; exact le_rfl
      · rw [hlr r hr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; rw [hmem]; exact (hI.freshMem j).mono hseq
    · intro r j; by_cases hr : r = q
      · subst hr; rw [hlq]; exact (hI.freshCur r j).mono hseq
      · rw [hlr r hr]; exact (hI.freshCur r j).mono hseq
    · intro r pv hr j; by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; simp [startLoc] at hr
      · rw [hlr r hrq] at hr; exact (hI.freshPrev r pv hr j).mono hseq
    · intro r hr; by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; simp [startLoc] at hr
      · rw [hlr r hrq] at hr; rw [hops r hrq, hpend' r hrq]; exact hI.idle r hr
    · intro r hr; by_cases hrq : r = q
      · subst hrq; rw [hlq]
        simp [inputs, opsOf_append, (hI.idle r hph).1, startLoc, Label.invOf]; rfl
      · rw [hlr r hrq] at hr ⊢; rw [inputs, hops r hrq]; exact hI.inp r hr
    · intro r w hr; rw [hresp] at hr; have := hI.resp r w hr
      by_cases hrq : r = q
      · subst hrq; rw [hph] at this; cases this
      · rw [hlr r hrq]; exact this
    · intro Q hQ
      have hqQ : q ∉ Q := fun hq => by
        obtain ⟨-, pv, hpv, -⟩ := hQ q hq; rw [hlq] at hpv; simp [startLoc] at hpv
      have hQ' : ∀ r ∈ Q, Ready C r := fun r hr =>
        (ready_congr (hlr r (by rintro rfl; exact hqQ hr)) hmem).1 (hQ r hr)
      have := (hI.sim Q hQ').invoke (p := q) (x := x) (by rw [absCfg_loc, ifNeg hqQ]; exact hph)
      convert this using 1
      refine acfg_ext (by simp [absCfg, hmem]) fun r => ?_
      rw [ACfg.invoke_loc, absCfg_loc, absCfg_loc]
      by_cases hrq : r = q
      · subst hrq; simp [hqQ, hlq, toA, startLoc]
      · simp [hrq, hlr r hrq]
  · have hl : C'.loc = C.loc := by rw [hloc, invoke_ne_idle hph]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; rw [hmem]; exact (hI.freshMem j).mono (fun p => by rw [hl])
    · intro r j; rw [hl]; exact (hI.freshCur r j).mono (fun p => by rw [hl])
    · intro r pv hr j; rw [hl] at hr; exact (hI.freshPrev r pv hr j).mono (fun p => by rw [hl])
    · intro r hr
      rw [hl] at hr
      have hrq : r ≠ q := by rintro rfl; exact hph hr
      rw [hops r hrq, hpend' r hrq]; exact hI.idle r hr
    · intro r hr; rw [hl] at hr ⊢
      rw [inputs_append_of_ne_nil (by rw [hI.inp r hr]; exact Option.some_ne_none _)]; exact hI.inp r hr
    · intro r w hr; rw [hresp] at hr; rw [hl]; exact hI.resp r w hr
    · intro Q hQ
      have hQ' : ∀ r ∈ Q, Ready C r := fun r hr => (ready_congr (by rw [hl]) hmem).1 (hQ r hr)
      have := hI.sim Q hQ'
      have he : absCfg Q C' = absCfg Q C := by
        refine acfg_ext (by simp [absCfg, hmem]) fun r => ?_
        rw [absCfg_loc, absCfg_loc, hl]
      rwa [he]

lemma SInv.step_ret {w : (taskObj (Fin k) (Fin k)).Resp} (hI : SInv α C)
    (h : (swapAlg k m P).step C (.ret q w) = some C') : SInv (α ++ [.ret q w]) C' := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have hops : ∀ r, opsOf (α ++ [.ret q w]) r = opsOf α r := by simp [opsOf, Label.invOf]
  rcases hph : (C.loc q).ph with _ | _ | j | w'
  · exact absurd (hI.idle q hph).2 h0
  · rw [act_scan hph] at hact; cases hact
  · rw [act_swap hph] at hact; cases hact
  rw [act_done hph] at hact
  injection hact with h1 h2
  subst h2; subst h1
  have hl : C'.loc = C.loc := by rw [hloc]; simp
  have hpend' : ∀ r, r ≠ q → C'.pend r = C.pend r := by
    intro r hr; simp [hpend, Function.update_of_ne hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hmem]; exact (hI.freshMem j).mono (fun p => by rw [hl])
  · intro r j; rw [hl]; exact (hI.freshCur r j).mono (fun p => by rw [hl])
  · intro r pv hr j; rw [hl] at hr; exact (hI.freshPrev r pv hr j).mono (fun p => by rw [hl])
  · intro r hr
    rw [hl] at hr
    have hrq : r ≠ q := by rintro rfl; rw [hph] at hr; cases hr
    rw [hops r, hpend' r hrq]; exact hI.idle r hr
  · intro r hr; rw [hl] at hr ⊢; rw [inputs, hops]; exact hI.inp r hr
  · intro r w hr
    rw [hl]
    rw [respsOf_append] at hr
    rcases List.mem_append.1 hr with hr1 | hr1
    · exact hI.resp r w hr1
    · by_cases hrq : q = r
      · subst hrq; simp [respsOf, Label.retOf] at hr1; rw [hph]; exact congrArg Ph.done (Option.some.inj hr1)
      · simp [respsOf, Label.retOf, hrq] at hr1
  · intro Q hQ
    have hQ' : ∀ r ∈ Q, Ready C r := fun r hr => (ready_congr (by rw [hl]) hmem).1 (hQ r hr)
    have := hI.sim Q hQ'
    have he : absCfg Q C' = absCfg Q C := by
      refine acfg_ext (by simp [absCfg, hmem]) fun r => ?_
      rw [absCfg_loc, absCfg_loc, hl]
    rwa [he]

lemma SInv.step_tau (hP : Fintype.card P ≤ m + 1) (hI : SInv α C)
    (h : (swapAlg k m P).step C (.tau q) = some C') : SInv (α ++ [.tau q]) C' := by
  have hp : C.pend q ≠ none := (Impl.step_tau h).1
  have hops : ∀ r, opsOf (α ++ [.tau q]) r = opsOf α r := by simp [opsOf, Label.invOf]
  have hresps : ∀ r, respsOf (α ++ [.tau q]) r = respsOf α r := by simp [respsOf, Label.retOf]
  have hinputs : ∀ r, inputs (α ++ [.tau q]) r = inputs α r := by intro r; simp only [inputs, hops]
  rcases hph : (C.loc q).ph with _ | _ | j | w
  · exact absurd (hI.idle q hph).2 hp
  · -- a read during a scan
    rw [step_tau_scan hp hph] at h
    have hC' := (Option.some.inj h).symm
    set d := C.loc q with hd
    set v := C.mem d.idx with hv
    have hlq : C'.loc q = readStep d v := by rw [hC']; simp
    have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := by
      intro r hr; rw [hC']; simp [Function.update_of_ne hr]
    have hmem : C'.mem = C.mem := by rw [hC']
    have hpend : C'.pend = C.pend := by rw [hC']
    have hseq : ∀ r, (C.loc r).seq ≤ (C'.loc r).seq := by
      intro r; by_cases hr : r = q
      · subst hr; rw [hlq, readStep_seq]
      · rw [hlr r hr]
    have hcurOK : ∀ j, TagOK C' ((Function.update d.cur d.idx v) j).1 := by
      intro j
      by_cases hj : j = d.idx
      · subst hj; rw [Function.update_self]; exact (hI.freshMem _).mono hseq
      · rw [Function.update_of_ne hj]; exact (hI.freshCur q j).mono hseq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; rw [hmem]; exact (hI.freshMem j).mono hseq
    · intro r j; by_cases hr : r = q
      · subst hr; rw [hlq, readStep_cur]; exact hcurOK j
      · rw [hlr r hr]; exact (hI.freshCur r j).mono hseq
    · intro r pv hr j; by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr
        rcases readStep_prev d v with h1 | h1 <;> rw [h1] at hr
        · exact (hI.freshPrev _ pv hr j).mono hseq
        · cases hr; exact hcurOK j
      · rw [hlr r hrq] at hr; exact (hI.freshPrev r pv hr j).mono hseq
    · intro r hr; by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; exact absurd hr (readStep_ph_ne_idle hph v)
      · rw [hlr r hrq] at hr; rw [hops, hpend]; exact hI.idle r hr
    · intro r hr; rw [hinputs]; by_cases hrq : r = q
      · subst hrq; rw [hlq, readStep_inp]; exact hI.inp _ (by rw [hph]; simp)
      · rw [hlr r hrq] at hr ⊢; exact hI.inp r hr
    · intro r w hr; rw [hresps] at hr; have := hI.resp r w hr
      by_cases hrq : r = q
      · subst hrq; rw [hph] at this; cases this
      · rw [hlr r hrq]; exact this
    · intro Q hQ
      have hQo : ∀ r ∈ Q, r ≠ q → Ready C r := fun r hr hrq =>
        (ready_congr (hlr r hrq) hmem).1 (hQ r hr)
      rcases readStep_cases d v with ⟨hlt, hrs⟩ | ⟨hge, hpv, hrs⟩ | ⟨hge, hpv, hrs⟩
      · -- the collect continues
        have hQC : ∀ r ∈ Q, Ready C r := by
          intro r hr
          by_cases hrq : r = q
          · rw [hrq] at hr ⊢
            have := hQ q hr
            unfold Ready at this ⊢
            rw [hlq, hrs, hmem] at this
            exact readyL_continue hph hlt this
          · exact hQo r hr hrq
        have he : absCfg Q C' = absCfg Q C := acfg_ext (by simp [absCfg, hmem]) fun r => by
          rw [absCfg_loc, absCfg_loc]
          by_cases hrq : r = q
          · rw [hrq, hlq, hrs, ← hd]; simp [scannedA, toA]
          · rw [hlr r hrq]
        rw [he]; exact hI.sim Q hQC
      · -- the scan completes: it was linearized at the end of the previous collect
        have hqQ : q ∉ Q := fun hq => by
          have := (hQ q hq).1; rw [hlq, hrs] at this; exact after_ph_ne_scan _ _ _ this
        have hRq : Ready C q := readyL_complete hph hge hpv
        have hQC : ∀ r ∈ insert q Q, Ready C r := by
          intro r hr; rcases mem_insert.1 hr with rfl | hr'
          · exact hRq
          · exact hQo r hr' (by rintro rfl; exact hqQ hr')
        have he : absCfg Q C' = absCfg (insert q Q) C := acfg_ext (by simp [absCfg, hmem]) fun r => by
          rw [absCfg_loc, absCfg_loc]
          by_cases hrq : r = q
          · rw [hrq, ifNeg hqQ, ifPos (mem_insert_self _ _), hlq, hrs, ← hd]
            simp [scannedA, toA, hpv]
          · rw [hlr r hrq]; simp [hrq]
        rw [he]; exact hI.sim _ hQC
      · -- the collect is complete but differs from the previous one
        by_cases hqQ : q ∈ Q
        · have hm : ∀ j, C.mem j = (Function.update d.cur d.idx v) j := by
            have := hQ q hqQ
            unfold Ready at this
            rw [hlq, hrs, hmem] at this
            exact readyL_restart this
          have hQC : ∀ r ∈ Q.erase q, Ready C r := fun r hr =>
            hQo r (mem_of_mem_erase hr) (ne_of_mem_erase hr)
          have hA := (hI.sim _ hQC).scan hP (q := q)
            (by rw [absCfg_loc, ifNeg (notMem_erase q Q)]; exact hph)
          have hvec : vecs (Function.update d.cur d.idx v) = fun j => (C.mem j).2 := by
            funext j; rw [vecs, hm j]
          have he : absCfg Q C' = (absCfg (Q.erase q) C).scanStep q :=
            acfg_ext (by simp [absCfg, hmem, ACfg.scanStep]) fun r => by
              by_cases hrq : r = q
              · rw [hrq, absCfg_loc, ifPos hqQ, hlq, hrs]
                simp only [ACfg.scanStep, Function.update_self, absCfg_loc, notMem_erase,
                  ↓reduceIte, scannedA, toA]
                rw [hvec]; rfl
              · rw [absCfg_loc]
                simp only [ACfg.scanStep, Function.update_of_ne hrq, absCfg_loc, mem_erase, hrq,
                  ne_eq, not_false_eq_true, true_and]
                rw [hlr r hrq]
          rw [he]; exact hA
        · have hQC : ∀ r ∈ Q, Ready C r := fun r hr =>
            hQo r hr (by rintro rfl; exact hqQ hr)
          have he : absCfg Q C' = absCfg Q C := acfg_ext (by simp [absCfg, hmem]) fun r => by
            rw [absCfg_loc, absCfg_loc]
            by_cases hrq : r = q
            · rw [hrq, ifNeg hqQ, ifNeg hqQ, hlq, hrs, ← hd]; simp [toA]
            · rw [hlr r hrq]
          rw [he]; exact hI.sim Q hQC
  · -- a swap
    rw [step_tau_swap hp hph] at h
    have hC' := (Option.some.inj h).symm
    have hlq : C'.loc q = afterSwap (C.loc q) (C.mem j) := by rw [hC']; simp
    have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := by
      intro r hr; rw [hC']; simp [Function.update_of_ne hr]
    have hmem : C'.mem = Function.update C.mem j (some (q, (C.loc q).seq), (C.loc q).l) := by
      rw [hC']
    have hpend : C'.pend = C.pend := by rw [hC']
    have hseq : ∀ r, (C.loc r).seq ≤ (C'.loc r).seq := by
      intro r; by_cases hr : r = q
      · subst hr; rw [hlq]; simp [afterSwap]
      · rw [hlr r hr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j'; rw [hmem]
      by_cases hj : j' = j
      · subst hj; rw [Function.update_self]
        intro p c hpc
        simp only [Option.some.injEq, Prod.mk.injEq] at hpc
        obtain ⟨rfl, rfl⟩ := hpc
        rw [hlq]; simp [afterSwap]
      · rw [Function.update_of_ne hj]; exact (hI.freshMem j').mono hseq
    · intro r j'; by_cases hr : r = q
      · subst hr; rw [hlq]; exact (hI.freshCur _ j').mono hseq
      · rw [hlr r hr]; exact (hI.freshCur r j').mono hseq
    · intro r pv hr j'; by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; simp [afterSwap] at hr
      · rw [hlr r hrq] at hr; exact (hI.freshPrev r pv hr j').mono hseq
    · intro r hr; by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; simp [afterSwap] at hr
      · rw [hlr r hrq] at hr; rw [hops, hpend]; exact hI.idle r hr
    · intro r hr; rw [hinputs]; by_cases hrq : r = q
      · subst hrq; rw [hlq]; exact hI.inp _ (by rw [hph]; simp)
      · rw [hlr r hrq] at hr ⊢; exact hI.inp r hr
    · intro r w hr; rw [hresps] at hr; have := hI.resp r w hr
      by_cases hrq : r = q
      · subst hrq; rw [hph] at this; cases this
      · rw [hlr r hrq]; exact this
    · intro Q hQ
      have hqQ : q ∉ Q := fun hq => by
        obtain ⟨-, pv, hpv, -⟩ := hQ q hq; rw [hlq] at hpv; simp [afterSwap] at hpv
      have hQC : ∀ r ∈ Q, Ready C r := by
        intro r hr
        have hrq : r ≠ q := by rintro rfl; exact hqQ hr
        obtain ⟨hs, pv, hpv, hcur, hm⟩ := hQ r hr
        rw [hlr r hrq] at hs hpv hcur hm
        refine ⟨hs, pv, hpv, hcur, fun j' hj' => ?_⟩
        have := hm j' hj'
        rw [hmem] at this
        by_cases hj : j' = j
        · subst hj
          rw [Function.update_self] at this
          have hok := hI.freshPrev r pv hpv j' q (C.loc q).seq (by rw [← this])
          omega
        · rwa [Function.update_of_ne hj] at this
      have hA := (hI.sim Q hQC).swap (p := q) (j := j) (by rw [absCfg_loc, ifNeg hqQ]; exact hph)
      have he : absCfg Q C' = (absCfg Q C).swapStep q j := by
        refine acfg_ext ?_ fun r => ?_
        · funext j'
          simp only [absCfg, ACfg.swapStep, hmem, ifNeg hqQ, toA]
          by_cases hj : j' = j
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        · by_cases hrq : r = q
          · subst hrq
            simp only [absCfg, ACfg.swapStep, Function.update_self, ifNeg hqQ, toA, hlq, afterSwap]
          · simp only [absCfg, ACfg.swapStep, Function.update_of_ne hrq, hlr r hrq]
      rw [he]; exact hA
  · obtain ⟨-, -, i, o, k', hact, -⟩ := Impl.step_tau h
    rw [act_done hph] at hact; cases hact

/-- The safety invariant holds in every reachable configuration (if `|P| ≤ m + 1`). -/
theorem sInv_run (hP : Fintype.card P ≤ m + 1) {α : List (DLbl k P)} {C : DCfg k m P}
    (h : (swapAlg k m P).run α = some C) : SInv α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [Impl.run_nil, Option.some.injEq] at h; subst h; exact sInv_init
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (swapAlg k m P).runFrom (swapAlg k m P).initCfg α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      have hI := ih hα
      cases ℓ with
      | inv q o => exact hI.step_inv h
      | ret q o => exact hI.step_ret h
      | tau q => exact hI.step_tau hP h

/-- Agreement and validity hold in every finite execution of Algorithm 1 (one-shot or not),
provided `|P| ≤ m + 1`. -/
theorem swapAlg_safe (hP : Fintype.card P ≤ m + 1) (α : List (DLbl k P))
    (hα : (swapAlg k m P).Valid α) : (consensus P (Fin k)).Δ (inputs α) (outputs α) := by
  obtain ⟨C, hC⟩ := hα
  have hI := sInv_run hP hC
  have hout : ∀ q (w : (taskObj (Fin k) (Fin k)).Resp), outputs α q = some w →
      ((absCfg ∅ C).loc q).ph = .done w := fun q w h => by
    rw [absCfg_loc, ifNeg (notMem_empty q)]; exact hI.resp q w (List.mem_of_head? h)
  have hA := hI.sim ∅ (by simp)
  refine ⟨fun p q x y hx hy => hA.agree (hout p x hx) (hout q y hy), fun p y hy => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := hA.valid (hout p y hy)
  rw [absCfg_loc, ifNeg (notMem_empty q)] at hq1 hq2
  exact ⟨q, by rw [hI.inp q hq1]; exact congrArg some hq2⟩

/-- Algorithm 1 solves consensus (agreement + validity), if `|P| ≤ m + 1`. -/
theorem swapAlg_solves (hP : Fintype.card P ≤ m + 1) :
    (swapAlg k m P).Solves (consensus P (Fin k)) :=
  fun α hα _ => swapAlg_safe hP α hα

end Cslib.SharedMemory.ComplexityHierarchy.SwapRead
