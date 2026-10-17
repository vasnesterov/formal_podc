import Mathlib
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Progress
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Objects.FetchAdd
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Task
import Podc.Computability.Distributed.SharedMemory.Model

/-!
# Mod-`φ` fetch-and-increment from one bounded fetch-and-add object
(Section 6 / Appendix B of [BJW23])

[BJW23]: Bashari, Jamadi, Woelfel, *Efficient Bounded Timestamping from Standard Synchronization
Primitives*, PODC 2023.

## Model

* Asynchronous shared memory, CSLib model (`Cslib.SharedMemory.Impl`): processes `Fin n`
  (`0, …, n-1`), deterministic, each with at most one pending high-level operation; wait-freedom
  as in CSLib (no crash model needed: a crashed process is one that stops taking steps).
* One base object `Counter : bfaaObj B ovf` (index type `Unit`): a *bounded* fetch-and-add object
  with values in `{0, …, B-1}`, initially `0`, operations `read` and `faa d` (`d : ℤ`), both
  returning the previous value. If `0 ≤ v + d < B`, `faa d` sets the value to `v + d`; otherwise
  (overflow, "arbitrary behaviour" in the paper) it sets it to `ovf v d` for an **arbitrary**
  function `ovf`, a parameter of every theorem.
* Implemented object `modFaiObj φ` (CSLib catalog): state `s ∈ {0, …, φ-1}`,
  initially `0`; `read()` returns `s`, `FAI()` returns `s` and sets `s := (s + 1) mod φ`.
* Algorithm (Fig. 3, lines 75–78), program counters explicit (`Loc`):
  ```
  FAI():  tmp ← Counter.read()                                  -- pc `fai`
          if tmp ≥ φn − n then tmp ← Counter.FAA(1 − φ)          -- pc `dec` (line 76)
          else tmp ← Counter.FAA(1)                              -- pc `inc` (line 77)
          return tmp mod φ                                       -- pc `done`
  read(): return Counter.read() mod φ                            -- pc `rd`
  ```
  The paper only gives `FAI`; `read()` is our (obvious) addition.

## Results

* `lemma63` (Lemma 63) and its sharpening `lemma63_sharp`: `(φ-1)·k⁻ ≤ v` and `v + k⁺ ≤ φn − 1`
  (the paper has `v ≤ φn − k⁺`).
* `corollary64` (Corollary 64): no `faa` ever overflows, already for `B ≥ φn` (the paper assumes
  `B > φn`); hence `ovf` is irrelevant.
* `theorem11_linearizable`, `theorem11_waitFree`, `theorem11_steps` (Theorem 11).
* Tightness of `B ≥ φn` for `φ ≥ 2`, `n ≥ 1`: `exists_overflow` (with `B < φn` some `faa`
  overflows), `exists_reach_max` (the counter reaches `φn − 1`).
-/

namespace Cslib.SharedMemory.BoundedTS.FAI

open Cslib.SharedMemory

/-! ## Objects and the algorithm -/

/-- Operations of a fetch-and-add object. -/
inductive FAAOp where
  | read
  | faa (d : ℤ)

/-- A bounded fetch-and-add object with values in `{0, …, B-1}`, initially `0`. On overflow
(`v + d ∉ [0, B)`) the new value is `ovf v d` (arbitrary). Every operation returns the old
value. -/
abbrev bfaaObj (B : ℕ) (ovf : ℕ → ℤ → ℕ) : ObjSpec where
  State := ℕ
  Op := FAAOp
  Resp := ℕ
  init := 0
  δ v o := match o with
    | .read => (v, v)
    | .faa d => (if 0 ≤ (v : ℤ) + d ∧ (v : ℤ) + d < B then ((v : ℤ) + d).toNat else ovf v d, v)

/-- Program counters. `fai`: about to read `Counter` (line 75); `dec` / `inc`: poised to execute
`FAA(1-φ)` (line 76) / `FAA(1)` (line 77); `rd`: `read()` about to read `Counter`;
`done r`: about to return `r`. -/
inductive Loc where
  | idle
  | rd
  | fai
  | dec
  | inc
  | done (r : ℕ)
  deriving DecidableEq

/-- The high-level operation being executed at a program counter (if it has not yet been
linearized). -/
def Loc.op : Loc → Option FAIOp
  | .rd => some .read
  | .fai => some .fai
  | .dec => some .fai
  | .inc => some .fai
  | _ => none

/-- Program counter right after an invocation. -/
def invLoc : FAIOp → Loc
  | .read => .rd
  | .fai => .fai

/-- The algorithm of Fig. 3 (plus `read()`), for `n` processes. -/
def alg (n φ B : ℕ) (ovf : ℕ → ℤ → ℕ) :
    Impl (modFaiObj φ) (fun _ : Unit => bfaaObj B ovf) (Fin n) Loc where
  memInit _ := 0
  locInit _ := .idle
  invoke _ _ o := invLoc o
  act _ l := match l with
    | .idle => .ret 0 .idle
    | .rd => .access () .read (fun v => .done (v % φ))
    | .fai => .access () .read (fun v => if φ * n - n ≤ v then .dec else .inc)
    | .dec => .access () (.faa (1 - (φ : ℤ))) (fun v => .done (v % φ))
    | .inc => .access () (.faa 1) (fun v => .done (v % φ))
    | .done r => .ret r .idle

/-- Configurations of the algorithm. -/
abbrev Cfg (n φ B : ℕ) (ovf : ℕ → ℤ → ℕ) :=
  Config (modFaiObj φ) (fun _ : Unit => bfaaObj B ovf) (Fin n) Loc

variable {n φ B : ℕ} {ovf : ℕ → ℤ → ℕ}

lemma faa_ok {v : ℕ} {d : ℤ} (h0 : 0 ≤ (v : ℤ) + d) (h1 : (v : ℤ) + d < B) :
    ((bfaaObj B ovf).δ v (.faa d)).1 = ((v : ℤ) + d).toNat := by
  show (if _ then _ else _) = _
  simp only [h0, h1, and_self, ite_true]

/-! ## Counting processes at a program counter -/

/-- Number of processes whose program counter is `c` (paper: `k⁻` for `c = dec`, `k⁺` for
`c = inc`). -/
def numAt (f : Fin n → Loc) (c : Loc) : ℕ := (Finset.univ.filter (fun q => f q = c)).card

lemma numAt_update (f : Fin n → Loc) (p : Fin n) (a c : Loc) :
    numAt (Function.update f p a) c + (if f p = c then 1 else 0) =
      numAt f c + (if a = c then 1 else 0) := by
  simp only [numAt, Finset.card_filter]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase _ (fun q => if f q = c then 1 else 0) (Finset.mem_univ p),
    Function.update_self]
  have : ∑ x ∈ Finset.univ.erase p, (if Function.update f p a x = c then 1 else 0) =
      ∑ x ∈ Finset.univ.erase p, (if f x = c then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  rw [this]; ring

lemma numAt_le (f : Fin n → Loc) (c : Loc) : numAt f c ≤ n :=
  (Finset.card_le_univ _).trans (by simp)

lemma numAt_pos (f : Fin n → Loc) (p : Fin n) (c : Loc) (h : f p = c) : 1 ≤ numAt f c :=
  Finset.card_pos.2 ⟨p, by simp [h]⟩

lemma numAt_lt (f : Fin n → Loc) (p : Fin n) (c : Loc) (h : f p ≠ c) : numAt f c + 1 ≤ n := by
  have := numAt_update f p c c
  simp only [h, ite_false, ite_true, add_zero] at this
  have := numAt_le (Function.update f p c) c
  omega

@[simp] lemma numAt_const (a c : Loc) : numAt (fun _ : Fin n => a) c = if a = c then n else 0 := by
  by_cases h : a = c <;> simp [numAt, h]

/-! ## The invariant -/

/-- The value of `Counter` in a configuration. -/
def cval (C : Cfg n φ B ovf) : ℕ := C.mem ()

/-- Per-process part of the invariant. -/
structure PInv (α : List (Label (Fin n) (modFaiObj φ))) (L : List (OpId (Fin n) × FAIOp))
    (l : Loc) (pd : Option FAIOp) (q : Fin n) : Prop where
  idle : l = .idle ↔ pd = none
  pending : ∀ o, l.op = some o → pd = some o ∧
    (q, (respsOf α q).length) ∉ L.map Prod.fst ∧ opOf α (q, (respsOf α q).length) = some o
  done : ∀ r, l = .done r → pd ≠ none ∧ ∃ L₁ L₂ o,
    L = L₁ ++ ((q, (respsOf α q).length), o) :: L₂ ∧
    ((modFaiObj φ).δ ((modFaiObj φ).runOps (modFaiObj φ).init (L₁.map Prod.snd)) o).2 = r

lemma PInv.of_op {α : List (Label (Fin n) (modFaiObj φ))} {L : List (OpId (Fin n) × FAIOp)}
    {l l' : Loc} {pd : Option FAIOp} {q : Fin n} {o : FAIOp} (h : PInv α L l pd q)
    (hl : l.op = some o) (hl' : l'.op = some o) : PInv α L l' pd q := by
  have hp := h.pending o hl
  refine ⟨⟨?_, ?_⟩, fun o' ho' => ?_, fun r hr => ?_⟩
  · rintro rfl; simp [Loc.op] at hl'
  · intro h'; rw [hp.1] at h'; cases h'
  · rw [hl'] at ho'; cases ho'; exact hp
  · subst hr; simp [Loc.op] at hl'

lemma PInv.frame {α α' : List (Label (Fin n) (modFaiObj φ))} {L L' M : List (OpId (Fin n) × FAIOp)}
    {l : Loc} {pd : Option FAIOp} {q : Fin n} (h : PInv α L l pd q)
    (hops : opsOf α' q = opsOf α q) (hresps : respsOf α' q = respsOf α q) (hL : L' = L ++ M)
    (hM : ∀ y ∈ M, y.1.1 ≠ q) : PInv α' L' l pd q := by
  subst hL
  refine ⟨h.idle, fun o ho => ?_, fun r hr => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := h.pending o ho
    refine ⟨h1, ?_, ?_⟩
    · rw [hresps]; simp only [List.map_append, List.mem_append, not_or]
      refine ⟨h2, fun hm => ?_⟩
      obtain ⟨y, hy, hy'⟩ := List.mem_map.1 hm
      exact hM y hy (by rw [hy'])
    · simp only [opOf, hops, hresps] at h3 ⊢; exact h3
  · obtain ⟨h1, L₁, L₂, o, hs, hr'⟩ := h.done r hr
    exact ⟨h1, L₁, L₂ ++ M, o, by rw [hresps, hs]; simp, hr'⟩

lemma procs_step {α : List (Label (Fin n) (modFaiObj φ))} {ℓ : Label (Fin n) (modFaiObj φ)}
    {C₀ C : Cfg n φ B ovf} {L L' M : List (OpId (Fin n) × FAIOp)} {p : Fin n}
    (hI : ∀ q, PInv α L (C₀.loc q) (C₀.pend q) q)
    (hstep : (alg n φ B ovf).step C₀ ℓ = some C) (hp : ℓ.proc = p) (hL : L' = L ++ M)
    (hM : ∀ y ∈ M, y.1.1 = p) (hnew : PInv (α ++ [ℓ]) L' (C.loc p) (C.pend p) p) :
    ∀ q, PInv (α ++ [ℓ]) L' (C.loc q) (C.pend q) q := by
  intro q
  by_cases hq : q = p
  · subst hq; exact hnew
  · have hne : ℓ.proc ≠ q := by rw [hp]; exact Ne.symm hq
    obtain ⟨h1, h2⟩ := Impl.step_other hstep hne
    rw [h1, h2]
    exact (hI q).frame (by simp [Label.invOf_eq_none_of_proc_ne hne])
      (by simp [Label.retOf_eq_none_of_proc_ne hne]) hL
      (fun y hy => by rw [hM y hy]; exact Ne.symm hq)

/-- The invariant of the algorithm: `L` is a linearization, the abstract state is the counter
value mod `φ`, Lemma 63 (in the sharpened form `v + k⁺ ≤ φn − 1`), and the per-process part. -/
structure Inv (α : List (Label (Fin n) (modFaiObj φ))) (C : Cfg n φ B ovf)
    (L : List (OpId (Fin n) × FAIOp)) : Prop where
  lin : IsLinearization α L
  mem : cval C % φ = linState (A := modFaiObj φ) L
  lower : (φ - 1) * numAt C.loc .dec ≤ cval C
  upper : cval C + numAt C.loc .inc ≤ φ * n - 1
  proc : ∀ q, PInv α L (C.loc q) (C.pend q) q

lemma step_tau_access {C C' : Cfg n φ B ovf} {p : Fin n} {o : FAAOp} {k : ℕ → Loc}
    (hact : (alg n φ B ovf).act p (C.loc p) = .access () o k)
    (h : (alg n φ B ovf).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧ C'.mem () = ((bfaaObj B ovf).δ (C.mem ()) o).1 ∧
      C'.loc = Function.update C.loc p (k ((bfaaObj B ovf).δ (C.mem ()) o).2) := by
  obtain ⟨h0, hpend, i, o', k', hact', hmem, hloc⟩ := Impl.step_tau h
  rw [hact] at hact'
  cases i
  simp only [Action.access.injEq, heq_eq_eq, true_and] at hact'
  obtain ⟨rfl, rfl⟩ := hact'
  exact ⟨h0, hpend, by rw [hmem, Function.update_self], hloc⟩

/-- **The invariant holds in every reachable configuration** (for `φ ≥ 1`, `B ≥ φn`). -/
theorem inv_of_run (hφ : 1 ≤ φ) (hB : φ * n ≤ B) {α : List (Label (Fin n) (modFaiObj φ))}
    {C : Cfg n φ B ovf} (h : (alg n φ B ovf).run α = some C) : ∃ L, Inv α C L := by
  refine Impl.run_induction (Q := fun α C => ∃ L, Inv α C L) ?_ ?_ h
  · refine ⟨[], ⟨isLinearization_nil, ?_, ?_, ?_, ?_⟩⟩
    · show (0 : ℕ) % φ = 0; simp
    · simp [Impl.initCfg, alg, cval]
    · simp [Impl.initCfg, alg, cval]
    · intro q
      refine ⟨by simp [Impl.initCfg, alg], fun o ho => by simp [Impl.initCfg, alg, Loc.op] at ho,
        fun r hr => ?_⟩
      simp [Impl.initCfg, alg] at hr
  rintro α C₀ ℓ C hα ⟨L, hI⟩ h
  have hn : ∀ q : Fin n, 1 ≤ φ * n := fun q => Nat.mul_pos hφ (Fin.pos q)
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hlen : (opsOf α p).length = (respsOf α p).length := Impl.run_idle_counts hα h0
    have hidle : C₀.loc p = .idle := (hI.proc p).idle.2 h0
    have hloc' : C.loc = Function.update C₀.loc p (invLoc o) := hloc
    have e1 : numAt C.loc .dec = numAt C₀.loc .dec := by
      have := numAt_update C₀.loc p (invLoc o) .dec
      rw [hidle, ← hloc'] at this; cases o <;> simpa [invLoc] using this
    have e2 : numAt C.loc .inc = numAt C₀.loc .inc := by
      have := numAt_update C₀.loc p (invLoc o) .inc
      rw [hidle, ← hloc'] at this; cases o <;> simpa [invLoc] using this
    have hv : cval C = cval C₀ := congrFun hmem ()
    refine ⟨L, hI.lin.append_inv p o, by rw [hv]; exact hI.mem,
      by rw [hv, e1]; exact hI.lower, by rw [hv, e2]; exact hI.upper, ?_⟩
    refine procs_step (p := p) hI.proc h rfl L.append_nil.symm (by simp) ?_
    rw [hloc', hpend, Function.update_self, Function.update_self]
    have hr : respsOf (α ++ [.inv p o]) p = respsOf α p := by simp
    refine ⟨?_, fun o' ho' => ?_, fun r hr' => ?_⟩
    · cases o <;> simp [invLoc]
    · have : o' = o := by cases o <;> cases o' <;> simp_all [invLoc, Loc.op]
      subst this
      refine ⟨rfl, ?_, ?_⟩
      · rw [hr]; intro hm
        have := hI.lin.mem_invoked hm
        simp [Invoked] at this; omega
      · simp [opOf, hr, ← hlen]
    · cases o <;> simp [invLoc] at hr'
  | tau p =>
    have hr : respsOf (α ++ [.tau p]) p = respsOf α p := by simp
    have hpI := hI.proc p
    have hlow := hI.lower
    have hup := hI.upper
    have hn1 := hn p
    cases hl : C₀.loc p with
    | idle =>
      exfalso; obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h; simp [alg, hl] at hact
    | done r =>
      exfalso; obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h; simp [alg, hl] at hact
    | rd =>
      obtain ⟨h0, hpend, hmem, hloc⟩ :=
        step_tau_access (o := .read) (k := fun v => .done (v % φ)) (by rw [hl]; rfl) h
      have hmem' : cval C = cval C₀ := hmem
      have hloc' : C.loc = Function.update C₀.loc p (.done (cval C₀ % φ)) := hloc
      obtain ⟨hp1, hp2, hp3⟩ := hpI.pending .read (by rw [hl]; rfl)
      have e1 := numAt_update C₀.loc p (.done (cval C₀ % φ)) .dec
      have e2 := numAt_update C₀.loc p (.done (cval C₀ % φ)) .inc
      rw [hl, ← hloc'] at e1 e2; simp at e1 e2
      have hnc : ¬ Completed α (p, (respsOf α p).length) := by simp [Completed]
      refine ⟨L ++ [((p, (respsOf α p).length), .read)],
        (hI.lin.push hp3 hp2 hnc).append_tau p, ?_, ?_, ?_, ?_⟩
      · rw [hmem', linState_concat]; exact hI.mem
      · rw [hmem', e1]; exact hlow
      · rw [hmem', e2]; exact hup
      · refine procs_step (p := p) hI.proc h rfl rfl (fun y hy => by simp at hy; simp [hy]) ?_
        rw [hloc', hpend, Function.update_self]
        refine ⟨by simp [h0], fun o ho => by simp [Loc.op] at ho,
          fun r hr' => ⟨h0, L, [], .read, by rw [hr], ?_⟩⟩
        simp only [Loc.done.injEq] at hr'; rw [← hr']; exact hI.mem.symm
    | fai =>
      obtain ⟨h0, hpend, hmem, hloc⟩ := step_tau_access (o := .read)
        (k := fun v => if φ * n - n ≤ v then .dec else .inc) (by rw [hl]; rfl) h
      have hmem' : cval C = cval C₀ := hmem
      have hloc' : C.loc = Function.update C₀.loc p
          (if φ * n - n ≤ cval C₀ then .dec else .inc) := hloc
      have hnew : ∀ l', l'.op = some .fai → PInv (α ++ [.tau p]) L l' (C₀.pend p) p :=
        fun l' hl' => (hpI.of_op (by rw [hl]; rfl) hl').frame (by simp) (by simp)
          L.append_nil.symm (by simp)
      have hlin := hI.lin.append_tau p
      by_cases hv : φ * n - n ≤ cval C₀
      · simp only [hv, ↓reduceIte] at hloc'
        have e1 := numAt_update C₀.loc p .dec .dec
        have e2 := numAt_update C₀.loc p .dec .inc
        rw [hl, ← hloc'] at e1 e2; simp at e1 e2
        have hK := numAt_lt C₀.loc p .dec (by rw [hl]; simp)
        refine ⟨L, hlin, by rw [hmem']; exact hI.mem, ?_, by rw [hmem', e2]; exact hup, ?_⟩
        · rw [hmem', e1]
          calc (φ - 1) * (numAt C₀.loc .dec + 1) ≤ (φ - 1) * n := Nat.mul_le_mul_left _ hK
            _ = φ * n - n := Nat.sub_one_mul φ n
            _ ≤ cval C₀ := hv
        · exact procs_step (p := p) hI.proc h rfl L.append_nil.symm (by simp)
            (by rw [hloc', hpend, Function.update_self]; exact hnew _ rfl)
      · simp only [hv, ↓reduceIte] at hloc'
        have e1 := numAt_update C₀.loc p .inc .dec
        have e2 := numAt_update C₀.loc p .inc .inc
        rw [hl, ← hloc'] at e1 e2; simp at e1 e2
        have hK := numAt_lt C₀.loc p .inc (by rw [hl]; simp)
        refine ⟨L, hlin, by rw [hmem']; exact hI.mem, by rw [hmem', e1]; exact hlow, ?_, ?_⟩
        · rw [hmem', e2]; omega
        · exact procs_step (p := p) hI.proc h rfl L.append_nil.symm (by simp)
            (by rw [hloc', hpend, Function.update_self]; exact hnew _ rfl)
    | dec =>
      obtain ⟨h0, hpend, hmem, hloc⟩ := step_tau_access (o := .faa (1 - (φ : ℤ)))
        (k := fun v => .done (v % φ)) (by rw [hl]; rfl) h
      have hK := numAt_pos C₀.loc p .dec hl
      have hge : φ - 1 ≤ cval C₀ :=
        calc φ - 1 = (φ - 1) * 1 := (mul_one _).symm
          _ ≤ (φ - 1) * numAt C₀.loc .dec := Nat.mul_le_mul_left _ hK
          _ ≤ cval C₀ := hlow
      have hmem' : cval C = cval C₀ + 1 - φ := by
        refine hmem.trans ((faa_ok (v := cval C₀) (by omega)
          (by omega)).trans ?_)
        rw [show ∀ z : ℤ, ∀ m : ℕ, z = m → z.toNat = m from fun z m h => by rw [h]; simp]
        omega
      have hloc' : C.loc = Function.update C₀.loc p (.done (cval C₀ % φ)) := hloc
      obtain ⟨hp1, hp2, hp3⟩ := hpI.pending .fai (by rw [hl]; rfl)
      have e1 := numAt_update C₀.loc p (.done (cval C₀ % φ)) .dec
      have e2 := numAt_update C₀.loc p (.done (cval C₀ % φ)) .inc
      rw [hl, ← hloc'] at e1 e2; simp at e1 e2
      have hnc : ¬ Completed α (p, (respsOf α p).length) := by simp [Completed]
      refine ⟨L ++ [((p, (respsOf α p).length), .fai)],
        (hI.lin.push hp3 hp2 hnc).append_tau p, ?_, ?_, ?_, ?_⟩
      · rw [hmem', linState_concat, ← hI.mem]
        show (cval C₀ + 1 - φ) % φ = (cval C₀ % φ + 1) % φ
        rw [Nat.mod_add_mod]
        conv_rhs => rw [show cval C₀ + 1 = (cval C₀ + 1 - φ) + φ by omega]
        rw [Nat.add_mod_right]
      · rw [hmem']; rw [← e1, mul_add_one] at hlow; omega
      · rw [hmem', e2]; omega
      · refine procs_step (p := p) hI.proc h rfl rfl (fun y hy => by simp at hy; simp [hy]) ?_
        rw [hloc', hpend, Function.update_self]
        refine ⟨by simp [h0], fun o ho => by simp [Loc.op] at ho,
          fun r hr' => ⟨h0, L, [], .fai, by rw [hr], ?_⟩⟩
        simp only [Loc.done.injEq] at hr'; rw [← hr']; exact hI.mem.symm
    | inc =>
      obtain ⟨h0, hpend, hmem, hloc⟩ := step_tau_access (o := .faa 1)
        (k := fun v => .done (v % φ)) (by rw [hl]; rfl) h
      have hK := numAt_pos C₀.loc p .inc hl
      have hmem' : cval C = cval C₀ + 1 := by
        refine hmem.trans ((faa_ok (v := cval C₀) (by omega)
          (by omega)).trans ?_)
        rw [show ∀ z : ℤ, ∀ m : ℕ, z = m → z.toNat = m from fun z m h => by rw [h]; simp]
        omega
      have hloc' : C.loc = Function.update C₀.loc p (.done (cval C₀ % φ)) := hloc
      obtain ⟨hp1, hp2, hp3⟩ := hpI.pending .fai (by rw [hl]; rfl)
      have e1 := numAt_update C₀.loc p (.done (cval C₀ % φ)) .dec
      have e2 := numAt_update C₀.loc p (.done (cval C₀ % φ)) .inc
      rw [hl, ← hloc'] at e1 e2; simp at e1 e2
      have hnc : ¬ Completed α (p, (respsOf α p).length) := by simp [Completed]
      refine ⟨L ++ [((p, (respsOf α p).length), .fai)],
        (hI.lin.push hp3 hp2 hnc).append_tau p, ?_, ?_, ?_, ?_⟩
      · rw [hmem', linState_concat, ← hI.mem]
        show (cval C₀ + 1) % φ = (cval C₀ % φ + 1) % φ
        rw [Nat.mod_add_mod]
      · rw [hmem', e1]; omega
      · rw [hmem']; omega
      · refine procs_step (p := p) hI.proc h rfl rfl (fun y hy => by simp at hy; simp [hy]) ?_
        rw [hloc', hpend, Function.update_self]
        refine ⟨by simp [h0], fun o ho => by simp [Loc.op] at ho,
          fun r hr' => ⟨h0, L, [], .fai, by rw [hr], ?_⟩⟩
        simp only [Loc.done.injEq] at hr'; rw [← hr']; exact hI.mem.symm
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    cases hl : C₀.loc p with
    | idle => exact absurd ((hI.proc p).idle.1 hl) h0
    | done r' =>
      simp only [alg, hl, Action.ret.injEq] at hact
      obtain ⟨hrr, rfl⟩ := hact
      subst hrr
      obtain ⟨-, L₁, L₂, o, hs, hres⟩ := (hI.proc p).done _ hl
      have e1 := numAt_update C₀.loc p .idle .dec
      have e2 := numAt_update C₀.loc p .idle .inc
      rw [hl, ← hloc] at e1 e2; simp at e1 e2
      have hv : cval C = cval C₀ := congrFun hmem ()
      refine ⟨L, hI.lin.append_ret L₁ L₂ o hs hres, by rw [hv]; exact hI.mem,
        by rw [hv, e1]; exact hI.lower, by rw [hv, e2]; exact hI.upper, ?_⟩
      refine procs_step (p := p) hI.proc h rfl L.append_nil.symm (by simp) ?_
      rw [hloc, hpend, Function.update_self, Function.update_self]
      exact ⟨by simp, fun o ho => by simp [Loc.op] at ho, fun r h => by cases h⟩
    | _ => simp [alg, hl] at hact

/-! ## Lemma 63, Corollary 64, linearizability -/

/-- **Lemma 63 of [BJW23]** (stated with the weaker hypothesis `B ≥ φn`; the paper assumes
`B > φn`): in every reachable configuration, with `k⁻` / `k⁺` the numbers of processes poised to
execute `FAA(1-φ)` (line 76) / `FAA(1)` (line 77), the counter value `v` satisfies
`(φ-1)·k⁻ ≤ v ≤ φn − k⁺`. -/
theorem lemma63 (hφ : 1 ≤ φ) (hB : φ * n ≤ B) {C : Cfg n φ B ovf}
    (hC : (alg n φ B ovf).Reachable C) :
    (φ - 1) * numAt C.loc .dec ≤ cval C ∧ cval C ≤ φ * n - numAt C.loc .inc := by
  obtain ⟨α, hα⟩ := hC
  obtain ⟨L, hI⟩ := inv_of_run hφ hB hα
  exact ⟨hI.lower, by have := hI.upper; omega⟩

/-- Sharpening of Lemma 63 (our observation): `v + k⁺ ≤ φn − 1`; in particular the counter
never exceeds `φn − 1`. -/
theorem lemma63_sharp (hφ : 1 ≤ φ) (hB : φ * n ≤ B) {C : Cfg n φ B ovf}
    (hC : (alg n φ B ovf).Reachable C) :
    (φ - 1) * numAt C.loc .dec ≤ cval C ∧ cval C + numAt C.loc .inc ≤ φ * n - 1 := by
  obtain ⟨α, hα⟩ := hC
  obtain ⟨L, hI⟩ := inv_of_run hφ hB hα
  exact ⟨hI.lower, hI.upper⟩

/-- **Corollary 64 of [BJW23]** (with the weaker hypothesis `B ≥ φn`): whenever a process is
poised to execute `Counter.FAA(x)` at counter value `v`, then `v + x ∈ {0, …, B-1}`. Hence no
overflow ever happens and the overflow behaviour `ovf` is irrelevant. -/
theorem corollary64 (hφ : 1 ≤ φ) (hB : φ * n ≤ B) {C : Cfg n φ B ovf}
    (hC : (alg n φ B ovf).Reachable C) (p : Fin n) {x : ℤ} {k : ℕ → Loc}
    (hact : (alg n φ B ovf).act p (C.loc p) = .access () (.faa x) k) :
    0 ≤ (cval C : ℤ) + x ∧ (cval C : ℤ) + x < B := by
  obtain ⟨hlow, hup⟩ := lemma63_sharp hφ hB hC
  have hn : 1 ≤ φ * n := Nat.mul_pos hφ (Fin.pos p)
  cases hl : C.loc p with
  | dec =>
    rw [hl] at hact
    simp only [alg, Action.access.injEq, true_and] at hact
    obtain ⟨h1, -⟩ := hact
    cases h1
    have hK := numAt_pos C.loc p .dec hl
    have hge : φ - 1 ≤ cval C :=
      calc φ - 1 = (φ - 1) * 1 := (mul_one _).symm
        _ ≤ (φ - 1) * numAt C.loc .dec := Nat.mul_le_mul_left _ hK
        _ ≤ cval C := hlow
    omega
  | inc =>
    rw [hl] at hact
    simp only [alg, Action.access.injEq, true_and] at hact
    obtain ⟨h1, -⟩ := hact
    cases h1
    have hK := numAt_pos C.loc p .inc hl
    omega
  | _ => rw [hl] at hact; simp [alg] at hact

/-- **Theorem 11 of [BJW23]** (linearizability; with the weaker hypothesis `B ≥ φn`): the
algorithm of Fig. 3 is a linearizable implementation of a mod-`φ` fetch-and-increment object,
for every overflow behaviour `ovf` of the bounded fetch-and-add object. -/
theorem theorem11_linearizable (hφ : 1 ≤ φ) (hB : φ * n ≤ B) (ovf : ℕ → ℤ → ℕ) :
    (alg n φ B ovf).Linearizable :=
  Impl.linearizable_of_run fun _ _ hC =>
    let ⟨L, hL⟩ := inv_of_run hφ hB hC
    ⟨L, hL.lin⟩

/-- Theorem 11 under the paper's exact hypothesis `B > φn`. -/
theorem theorem11_linearizable_paper (hφ : 1 ≤ φ) (hB : φ * n < B) (ovf : ℕ → ℤ → ℕ) :
    (alg n φ B ovf).Linearizable :=
  theorem11_linearizable hφ hB.le ovf

/-! ## Step complexity and wait-freedom -/

/-- Upper bound on the remaining base-object accesses of an operation. -/
def pot : Loc → ℕ
  | .rd => 1
  | .fai => 2
  | .dec => 1
  | .inc => 1
  | _ => 0

/-- Number of base-object accesses of an operation: `read()` 1, `FAI()` 2. -/
def cost : FAIOp → ℕ
  | .read => 1
  | .fai => 2

lemma pot_decreases (p : Fin n) (l : Loc) (i : Unit) (o : FAAOp) (k : ℕ → Loc)
    (hact : (alg n φ B ovf).act p l = .access i o k) (x : ℕ) : pot (k x) < pot l := by
  cases i
  cases l with
  | rd | dec | inc =>
    simp only [alg, Action.access.injEq, true_and] at hact
    obtain ⟨-, rfl⟩ := hact; simp [pot]
  | fai =>
    simp only [alg, Action.access.injEq, true_and] at hact
    obtain ⟨-, rfl⟩ := hact; dsimp only; split_ifs <;> simp [pot]
  | idle | done _ => simp [alg] at hact

/-- **Theorem 11 of [BJW23]** (constant step complexity): in every execution, after `p` invokes
an operation `o`, `p` performs at most `cost o ≤ 2` base-object accesses before it returns
(`γ` is any continuation not containing a response of `p`). -/
theorem theorem11_steps {α γ : List (Label (Fin n) (modFaiObj φ))} {p : Fin n} {o : FAIOp}
    (hv : (alg n φ B ovf).Valid (α ++ .inv p o :: γ)) (hret : ∀ r, Label.ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ cost o := by
  obtain ⟨l, h⟩ := (alg n φ B ovf).tauSteps_le_potential_invoke (fun _ l => pot l)
    (fun p l i o k hact x => pot_decreases p l i o k hact x) hv hret
  cases o <;> exact h

/-- **Theorem 11 of [BJW23]** (wait-freedom; no assumption on `B` needed). -/
theorem theorem11_waitFree (ovf : ℕ → ℤ → ℕ) : (alg n φ B ovf).WaitFree :=
  (alg n φ B ovf).waitFree_of_potential (fun _ l => pot l)
    (fun p l i o k hact x => pot_decreases p l i o k hact x)

/-! ## Tightness of `B ≥ φn` (our observation)

For `φ ≥ 2` and `n ≥ 1` the counter can reach `φn − 1`: one process performs `T − 1` complete
`FAI`s (`T = φn − n`), each reading a value `< T` and incrementing; then all `n` processes read
`T − 1` and perform `FAA(1)`. So with `B < φn` some `FAA` overflows. -/

/-- A configuration in which only `FAI`s are pending, the counter is `v` and the program counters
are `f`. -/
structure Shape (C : Cfg n φ B ovf) (v : ℕ) (f : Fin n → Loc) : Prop where
  mem : cval C = v
  loc : C.loc = f
  pend : ∀ q, C.pend q = if f q = .idle then none else some .fai

lemma Shape.congr {C : Cfg n φ B ovf} {v v' : ℕ} {f f' : Fin n → Loc} (h : Shape C v f)
    (hv : v = v') (hf : f = f') : Shape C v' f' := by subst hv hf; exact h

/-- Invoke `FAI` and read the counter. -/
lemma start_fai {C : Cfg n φ B ovf} {v : ℕ} {f : Fin n → Loc} {p : Fin n}
    (hC : (alg n φ B ovf).Reachable C) (hS : Shape C v f) (hp : f p = .idle) :
    ∃ C', (alg n φ B ovf).Reachable C' ∧
      Shape C' v (Function.update f p (if φ * n - n ≤ v then .dec else .inc)) := by
  have h0 : C.pend p = none := by rw [hS.pend]; simp [hp]
  set C1 : Cfg n φ B ovf := { C with
      pend := Function.update C.pend p (some .fai), loc := Function.update C.loc p (invLoc .fai) }
  have hC1 : (alg n φ B ovf).Reachable C1 :=
    hC.step (Impl.step_inv_eq_some (I := alg n φ B ovf) (o := .fai) h0 trivial)
  have h1 : C1.pend p ≠ none := by simp [C1]
  have hact : (alg n φ B ovf).act p (C1.loc p) =
      .access () .read (fun v => if φ * n - n ≤ v then .dec else .inc) := by
    simp only [C1, Function.update_self]; rfl
  refine ⟨_, hC1.step (Impl.step_tau_eq_some h1 hact), ?_, ?_, ?_⟩
  · show Function.update C.mem () _ () = v
    rw [Function.update_self]; exact hS.mem
  · show Function.update (Function.update C.loc p _) p _ = _
    rw [Function.update_idem, hS.loc]
    have hm : C.mem () = v := hS.mem
    show Function.update f p (if φ * n - n ≤ C.mem () then _ else _) = _
    rw [hm]
  · intro q
    show Function.update C.pend p _ q = _
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]; split_ifs <;> simp_all
    · simp only [Function.update_of_ne hq, hS.pend]

/-- A process poised at `FAA(1)` executes it (no overflow) and returns. -/
lemma finish_inc {C : Cfg n φ B ovf} {v : ℕ} {f : Fin n → Loc} {p : Fin n}
    (hC : (alg n φ B ovf).Reachable C) (hS : Shape C v f) (hp : f p = .inc) (hvB : v + 1 < B) :
    ∃ C', (alg n φ B ovf).Reachable C' ∧ Shape C' (v + 1) (Function.update f p .idle) := by
  have h0 : C.pend p ≠ none := by rw [hS.pend, hp]; simp
  have hact : (alg n φ B ovf).act p (C.loc p) =
      .access () (.faa 1) (fun v => .done (v % φ)) := by rw [hS.loc, hp]; rfl
  set C1 : Cfg n φ B ovf := { C with
      mem := Function.update C.mem () ((bfaaObj B ovf).δ (C.mem ()) (.faa 1)).1,
      loc := Function.update C.loc p
        ((fun v => .done (v % φ)) ((bfaaObj B ovf).δ (C.mem ()) (.faa 1)).2) }
  have hC1 : (alg n φ B ovf).Reachable C1 := hC.step (Impl.step_tau_eq_some h0 hact)
  have h1 : C1.pend p ≠ none := h0
  have hact1 : (alg n φ B ovf).act p (C1.loc p) = .ret (C.mem () % φ) .idle := by
    simp only [C1, Function.update_self]; rfl
  refine ⟨_, hC1.step (Impl.step_ret_eq_some h1 hact1), ?_, ?_, ?_⟩
  · have hm : C.mem () = v := hS.mem
    have e : ((bfaaObj B ovf).δ (C.mem ()) (.faa 1)).1 = v + 1 := by
      rw [faa_ok (v := C.mem ()) (by omega) (by rw [hm]; omega), hm]; simp
    simp only [cval, C1, Function.update_self]; exact e
  · show Function.update (Function.update C.loc p _) p _ = _
    rw [Function.update_idem, hS.loc]
  · intro q
    show Function.update C.pend p _ q = _
    by_cases hq : q = p
    · subst hq; simp
    · simp only [Function.update_of_ne hq, hS.pend]

lemma shape_init : Shape (alg n φ B ovf).initCfg 0 (fun _ => .idle) :=
  ⟨rfl, rfl, fun _ => by simp [Impl.initCfg]⟩

section Tight

variable (hφ : 2 ≤ φ) (hn : 1 ≤ n)
include hφ hn

omit hφ in
/-- Phase A: one process runs `m ≤ T − 1` complete `FAI`s. -/
lemma phaseA (m : ℕ) (hm : m ≤ φ * n - n - 1) (hmB : m ≤ B - 1) :
    ∃ C, (alg n φ B ovf).Reachable C ∧ Shape C m (fun _ => .idle) := by
  induction m with
  | zero => exact ⟨_, ⟨[], rfl⟩, shape_init⟩
  | succ m ih =>
    obtain ⟨C, hC, hS⟩ := ih (by omega) (by omega)
    have hT : ¬ φ * n - n ≤ m := by omega
    obtain ⟨C1, hC1, hS1⟩ := start_fai (p := ⟨0, hn⟩) hC hS rfl
    simp only [hT, ↓reduceIte] at hS1
    obtain ⟨C2, hC2, hS2⟩ := finish_inc (p := ⟨0, hn⟩) hC1 hS1 (by simp) (by omega)
    exact ⟨C2, hC2, hS2.congr rfl (by simp)⟩

/-- Phase B: processes `0, …, j-1` read `T − 1` and become poised at `FAA(1)`. -/
lemma phaseB (hTB : φ * n - n - 1 ≤ B - 1) (j : ℕ) (hj : j ≤ n) :
    ∃ C, (alg n φ B ovf).Reachable C ∧
      Shape C (φ * n - n - 1) (fun q => if q.val < j then .inc else .idle) := by
  have h2n : 2 * n ≤ φ * n := Nat.mul_le_mul_right n hφ
  induction j with
  | zero =>
    obtain ⟨C, hC, hS⟩ := phaseA (ovf := ovf) (B := B) (φ := φ) hn (φ * n - n - 1) le_rfl hTB
    exact ⟨C, hC, hS.congr rfl (by simp)⟩
  | succ j ih =>
    obtain ⟨C, hC, hS⟩ := ih (by omega)
    have hT : ¬ φ * n - n ≤ φ * n - n - 1 := by omega
    obtain ⟨C1, hC1, hS1⟩ := start_fai (p := ⟨j, by omega⟩) hC hS (by simp)
    simp only [hT, ↓reduceIte] at hS1
    refine ⟨C1, hC1, hS1.congr rfl ?_⟩
    funext q
    by_cases hq : q = ⟨j, by omega⟩
    · subst hq; simp
    · rw [Function.update_of_ne hq]
      have : q.val ≠ j := fun h => hq (Fin.ext h)
      by_cases h1 : q.val < j
      · simp [h1, show q.val < j + 1 by omega]
      · simp [h1, show ¬ q.val < j + 1 by omega]

/-- Phase C: processes `0, …, i-1` execute their `FAA(1)` and return. -/
lemma phaseC (j : ℕ) (hj : j ≤ n) (i : ℕ) (hi : i ≤ j)
    (hiB : φ * n - n - 1 + i ≤ B - 1) :
    ∃ C, (alg n φ B ovf).Reachable C ∧ Shape C (φ * n - n - 1 + i)
      (fun q => if q.val < i then .idle else if q.val < j then .inc else .idle) := by
  have h2n : 2 * n ≤ φ * n := Nat.mul_le_mul_right n hφ
  induction i with
  | zero =>
    obtain ⟨C, hC, hS⟩ := phaseB (ovf := ovf) (B := B) hφ hn (by omega) j hj
    exact ⟨C, hC, hS.congr rfl (by simp)⟩
  | succ i ih =>
    obtain ⟨C, hC, hS⟩ := ih (by omega) (by omega)
    obtain ⟨C1, hC1, hS1⟩ := finish_inc (p := ⟨i, by omega⟩) hC hS
      (by simp [show i < j by omega]) (by omega)
    refine ⟨C1, hC1, hS1.congr (by omega) ?_⟩
    funext q
    by_cases hq : q = ⟨i, by omega⟩
    · subst hq; simp
    · rw [Function.update_of_ne hq]
      have : q.val ≠ i := fun h => hq (Fin.ext h)
      by_cases h1 : q.val < i
      · simp [h1, show q.val < i + 1 by omega]
      · simp [h1, show ¬ q.val < i + 1 by omega]

/-- For every `w ≤ φn − 2` (reached without overflow, `w ≤ B − 1`) there is a reachable
configuration with counter value `w` and a process poised at `FAA(1)`. -/
lemma exists_reach_inc (w : ℕ) (hw : w + 2 ≤ φ * n) (hwB : w ≤ B - 1) :
    ∃ C f p, (alg n φ B ovf).Reachable C ∧ Shape C w f ∧ f p = .inc := by
  have h2n : 2 * n ≤ φ * n := Nat.mul_le_mul_right n hφ
  by_cases hwT : w < φ * n - n
  · obtain ⟨C, hC, hS⟩ := phaseA (ovf := ovf) (B := B) (φ := φ) hn w (by omega) hwB
    obtain ⟨C1, hC1, hS1⟩ := start_fai (p := ⟨0, hn⟩) hC hS rfl
    simp only [show ¬ φ * n - n ≤ w by omega, ↓reduceIte] at hS1
    exact ⟨C1, _, ⟨0, hn⟩, hC1, hS1, by simp⟩
  · have hj : w - (φ * n - n) + 2 ≤ n := by omega
    have hi1 : φ * n - n - 1 + (w - (φ * n - n) + 1) = w := by omega
    obtain ⟨C, hC, hS⟩ := phaseC (ovf := ovf) (B := B) hφ hn (w - (φ * n - n) + 2) hj
      (w - (φ * n - n) + 1) (by omega) (by rw [hi1]; exact hwB)
    refine ⟨C, _, ⟨w - (φ * n - n) + 1, by omega⟩, hC, hS.congr hi1 rfl, ?_⟩
    simp

/-- **Tightness of `B ≥ φn`** (our observation): for `φ ≥ 2`, `n ≥ 1` and `B < φn`, for every
overflow behaviour some reachable configuration has a process poised to execute `FAA(x)` with
`v + x ∉ {0, …, B-1}`, i.e. the hypothesis of Corollary 64 cannot be weakened. -/
theorem exists_overflow (hB : B < φ * n) :
    ∃ C : Cfg n φ B ovf, (alg n φ B ovf).Reachable C ∧ ∃ p x k,
      (alg n φ B ovf).act p (C.loc p) = .access () (.faa x) k ∧
      ¬ (0 ≤ (cval C : ℤ) + x ∧ (cval C : ℤ) + x < B) := by
  have h2n : 2 * n ≤ φ * n := Nat.mul_le_mul_right n hφ
  obtain ⟨C, f, p, hC, hS, hp⟩ := exists_reach_inc (ovf := ovf) (B := B) hφ hn (B - 1) (by omega) le_rfl
  refine ⟨C, hC, p, 1, fun v => .done (v % φ), by rw [hS.loc, hp]; rfl, ?_⟩
  rw [hS.mem]; omega

/-- The bound `v ≤ φn − 1` of `lemma63_sharp` is attained (for `φ ≥ 2`, `n ≥ 1`, `B ≥ φn`). -/
theorem exists_reach_max (hB : φ * n ≤ B) :
    ∃ C : Cfg n φ B ovf, (alg n φ B ovf).Reachable C ∧ cval C = φ * n - 1 := by
  have h2n : 2 * n ≤ φ * n := Nat.mul_le_mul_right n hφ
  obtain ⟨C, f, p, hC, hS, hp⟩ :=
    exists_reach_inc (ovf := ovf) (B := B) hφ hn (φ * n - 2) (by omega) (by omega)
  obtain ⟨C1, hC1, hS1⟩ := finish_inc hC hS hp (by omega)
  exact ⟨C1, hC1, by rw [hS1.mem]; omega⟩

end Tight

end Cslib.SharedMemory.BoundedTS.FAI
