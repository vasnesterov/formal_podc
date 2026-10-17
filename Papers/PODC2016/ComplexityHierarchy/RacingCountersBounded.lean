import Papers.PODC2016.ComplexityHierarchy.RacingCounters
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Podc.Algebra.BigOperators.Update

/-!
# Racing bounded counters (Lemma 3.2 of [EGSZ16])

An `m`-component *bounded* counter has components in `{0, …, K-1}` (the paper: `K = 3n`), supports
`inc v`, `dec v` and `scan`; incrementing a component with count `K - 1` or decrementing a
component with count `0` *breaks* the object (state `none`; every later operation returns `⊥`).

Lemma 3.2: obstruction-free `m`-valued consensus among `n` processes can be solved with an
`m`-component bounded counter with `K = 3n`. The algorithm modifies the racing counters algorithm of
Lemma 3.1: to promote `v`, a process looks (in its last scan) at a largest component `c_u` among the
*other* components; if `c_u < n` it increments `c_v`, otherwise it decrements `c_u`.

As for Lemma 3.1, the algorithm is generic over a simulation `BCounterSim m K` of the bounded
counter (used for the `add` implementation of Theorem 3.3, `RacingCountersAdd.lean`).

## Main results

* `racing2_inv`: in every reachable configuration the simulation invariant holds; for the bounded
  counter object this means it **never breaks** (`lemma_3_2`).
* `racing2_safe` / `racing2_solves`: agreement and validity (every execution).
* `racing2_obstructionFree`: obstruction-freedom (CSLib's `Impl.ObstructionFree`).
* `lemma_3_2`.

## Modelling choices / deviations

* The first promotion (of the input) is an increment: the process has not scanned yet, and its
  initial view is all zeros (the paper does not say what the first promotion does).
* The paper's text "let `c_u` be one that stores the largest count [among the others]. If
  `c_u < n` increment `c_v`, else decrement `c_u`" is implemented with `argmaxOther` (ties broken
  arbitrarily); with `m = 1` there is no other component and the process always decides.
* Validity needs that every scan sees a nonzero component (otherwise the arbitrary `argmax` of the
  all-zero vector could be a value nobody proposed). The paper does not discuss this; it holds by the
  invariant `pos` (pending decrements are always strictly fewer than the total count when someone is
  about to scan or decrement).
* `inc`/`dec` of the bounded counter return a dummy acknowledgement (`some 0`, or `none` = `⊥` if
  the object is broken).
* We need `|P| ≤ n` and `1 ≤ n`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory

/-! ### Bounded counters -/

/-- Operations of a bounded counter. -/
inductive BCounterOp (m : ℕ) where
  /-- Increment component `v`. -/
  | inc (v : Fin m)
  /-- Decrement component `v`. -/
  | dec (v : Fin m)
  /-- Return all components. -/
  | scan

/-- The `m`-component bounded counter with components in `{0, …, K-1}`. State `none` = broken
(every operation then returns `⊥ = none`). -/
abbrev bcounterObj (m K : ℕ) : ObjSpec where
  State := Option (Fin m → ℕ)
  Op := BCounterOp m
  Resp := Option (Fin m → ℕ)
  init := some 0
  δ s o := match s, o with
    | none, _ => (none, none)
    | some c, .inc v =>
      if c v + 1 < K then (some (Function.update c v (c v + 1)), some 0) else (none, none)
    | some c, .dec v =>
      if 0 < c v then (some (Function.update c v (c v - 1)), some 0) else (none, none)
    | some c, .scan => (some c, some c)

/-- A simulation of an `m`-component bounded counter (bound `K`) by a base object `B`. -/
structure BCounterSim (m K : ℕ) where
  /-- The base object. -/
  B : ObjSpec
  /-- Its initial state. -/
  init : B.State
  /-- Increment. -/
  incOp : Fin m → B.Op
  /-- Decrement. -/
  decOp : Fin m → B.Op
  /-- Scan. -/
  scanOp : B.Op
  /-- Decoding of scan responses. -/
  decode : B.Resp → Fin m → ℕ
  /-- The counts represented by a state. -/
  cnt : B.State → Fin m → ℕ
  /-- Representation invariant ("not broken"). -/
  Inv : B.State → Prop
  inv_init : Inv init
  cnt_init : cnt init = 0
  inc_ok : ∀ s v, Inv s → cnt s v + 1 < K →
    Inv (B.δ s (incOp v)).1 ∧ cnt (B.δ s (incOp v)).1 = Function.update (cnt s) v (cnt s v + 1)
  dec_ok : ∀ s v, Inv s → 0 < cnt s v →
    Inv (B.δ s (decOp v)).1 ∧ cnt (B.δ s (decOp v)).1 = Function.update (cnt s) v (cnt s v - 1)
  scan_state : ∀ s, (B.δ s scanOp).1 = s
  scan_resp : ∀ s, Inv s → decode (B.δ s scanOp).2 = cnt s

/-- The bounded counter object simulates itself; the invariant says that it is not broken. -/
def bcounterSim (m K : ℕ) : BCounterSim m K where
  B := bcounterObj m K
  init := some 0
  incOp := .inc
  decOp := .dec
  scanOp := .scan
  decode r := r.getD 0
  cnt s := s.getD 0
  Inv s := s ≠ none
  inv_init := by simp
  cnt_init := rfl
  inc_ok s v hs hv := by
    obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.1 hs
    simp only [Option.getD_some] at hv
    simp [hv]
  dec_ok s v hs hv := by
    obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.1 hs
    simp only [Option.getD_some] at hv
    simp [hv]
  scan_state s := by cases s <;> rfl
  scan_resp s hs := by
    obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.1 hs
    rfl

/-! ### The algorithm -/

variable {m : ℕ}

/-- Program counter / local state of a process. -/
inductive Phase2 (m : ℕ) where
  /-- Not invoked yet. -/
  | idle
  /-- About to increment `c_v`. -/
  | inc (v : Fin m)
  /-- About to decrement `c_v`. -/
  | dec (v : Fin m)
  /-- About to scan. -/
  | scan
  /-- Decided `v`. -/
  | done (v : Fin m)
  deriving DecidableEq

/-- Some index of a largest component other than `w` (`w` itself if there is no other). -/
noncomputable def argmaxOther (c : Fin m → ℕ) (w : Fin m) : Fin m :=
  if h : (Finset.univ.erase w).Nonempty then
    Classical.choose (Finset.exists_max_image (Finset.univ.erase w) c h)
  else w

lemma argmaxOther_ne {c : Fin m → ℕ} {w u : Fin m} (hu : u ≠ w) : argmaxOther c w ≠ w := by
  have h : (Finset.univ.erase w).Nonempty := ⟨u, by simp [hu]⟩
  unfold argmaxOther
  simp only [h, ↓reduceDIte]
  have := (Classical.choose_spec (Finset.exists_max_image (Finset.univ.erase w) c h)).1
  simpa using this

lemma le_argmaxOther {c : Fin m → ℕ} {w u : Fin m} (hu : u ≠ w) : c u ≤ c (argmaxOther c w) := by
  have h : (Finset.univ.erase w).Nonempty := ⟨u, by simp [hu]⟩
  unfold argmaxOther
  simp only [h, ↓reduceDIte]
  exact (Classical.choose_spec (Finset.exists_max_image (Finset.univ.erase w) c h)).2 u
    (by simp [hu])

variable [NeZero m]

/-- The local state after a scan returning `c`: decide `w = argmax c` if it leads by `n`;
otherwise promote `w`: decrement a largest other component if it is `≥ n`, else increment `c_w`. -/
noncomputable def afterScan2 (n : ℕ) (c : Fin m → ℕ) : Phase2 m :=
  if Lead n c (argmax c) then .done (argmax c)
  else if argmaxOther c (argmax c) ≠ argmax c ∧ n ≤ c (argmaxOther c (argmax c)) then
    .dec (argmaxOther c (argmax c))
  else .inc (argmax c)

variable {P : Type} [DecidableEq P] {K : ℕ}

/-- The racing bounded counters algorithm (proof of Lemma 3.2 of [EGSZ16]) with threshold `n`. -/
noncomputable def racing2 (S : BCounterSim m K) (n : ℕ) :
    Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => S.B) P (Phase2 m) where
  memInit _ := S.init
  locInit _ := .idle
  invoke _ l o := match l with
    | .idle => .inc o
    | l => l
  act _ l := match l with
    | .idle => .ret (default : Fin m) .idle
    | .inc v => .access () (S.incOp v) (fun _ => .scan)
    | .dec v => .access () (S.decOp v) (fun _ => .scan)
    | .scan => .access () S.scanOp (fun r => afterScan2 n (S.decode r))
    | .done v => .ret v (.done v)

/-! ### Steps -/

variable (S : BCounterSim m K) (n : ℕ)

/-- Configurations. -/
abbrev Cfg2 := Config (taskObj (Fin m) (Fin m)) (fun _ : Unit => S.B) P (Phase2 m)

/-- The counts represented by the memory. -/
def ctr2 (C : Cfg2 (P := P) S) : Fin m → ℕ := S.cnt (C.mem ())

variable {S n}

lemma step2_tau_inc {C : Cfg2 (P := P) S} {q : P} {v : Fin m} (hp : C.pend q ≠ none)
    (hph : C.loc q = .inc v) :
    (racing2 S n).step C (.tau q) =
      some ⟨Function.update C.loc q .scan, C.pend, fun _ => (S.B.δ (C.mem ()) (S.incOp v)).1⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, racing2, hph]
  congr 2

lemma step2_tau_dec {C : Cfg2 (P := P) S} {q : P} {v : Fin m} (hp : C.pend q ≠ none)
    (hph : C.loc q = .dec v) :
    (racing2 S n).step C (.tau q) =
      some ⟨Function.update C.loc q .scan, C.pend, fun _ => (S.B.δ (C.mem ()) (S.decOp v)).1⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, racing2, hph]
  congr 2

lemma step2_tau_scan {C : Cfg2 (P := P) S} {q : P} (hp : C.pend q ≠ none)
    (hph : C.loc q = .scan) :
    (racing2 S n).step C (.tau q) =
      some ⟨Function.update C.loc q (afterScan2 n (S.decode (S.B.δ (C.mem ()) S.scanOp).2)),
        C.pend, fun _ => (S.B.δ (C.mem ()) S.scanOp).1⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, racing2, hph]
  congr 2

lemma act2_done {l : Phase2 m} {q : P} {w : Fin m} (hph : l = .done w) :
    (racing2 S n).act q l = .ret w (.done w) := by
  subst hph; rfl

lemma invoke2_idle {q : P} {o : Fin m} : (racing2 S n).invoke q .idle o = .inc o := rfl

lemma invoke2_ne_idle {l : Phase2 m} {q : P} {o : Fin m} (hph : l ≠ .idle) :
    (racing2 S n).invoke q l o = l := by
  cases l <;> simp_all [racing2]

/-! ### Counting processes by phase -/

/-- Number of processes whose local state satisfies `f`. -/
def cntF [Fintype P] (f : Phase2 m → Bool) (loc : P → Phase2 m) : ℕ :=
  (Finset.univ.filter (fun q => f (loc q) = true)).card

lemma cntF_eq_sum [Fintype P] (f : Phase2 m → Bool) (loc : P → Phase2 m) :
    cntF f loc = ∑ q, (f (loc q)).toNat := by
  unfold cntF
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  cases f (loc q) <;> rfl

lemma cntF_update [Fintype P] (f : Phase2 m → Bool) (loc : P → Phase2 m) (q : P) (l : Phase2 m) :
    cntF f (Function.update loc q l) + (f (loc q)).toNat = cntF f loc + (f l).toNat := by
  simp only [cntF_eq_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q), ← Finset.add_sum_erase _ _ (Finset.mem_univ q)]
  have : ∑ x ∈ Finset.univ.erase q, (f (Function.update loc q l x)).toNat =
      ∑ x ∈ Finset.univ.erase q, (f (loc x)).toNat :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]
  omega

lemma cntF_pos [Fintype P] {f : Phase2 m → Bool} {loc : P → Phase2 m} {q : P}
    (hq : f (loc q) = true) : 1 ≤ cntF f loc :=
  Finset.card_pos.2 ⟨q, by simp [hq]⟩

lemma cntF_lt [Fintype P] {f : Phase2 m → Bool} {loc : P → Phase2 m} {q : P}
    (hq : f (loc q) = false) : cntF f loc + 1 ≤ Fintype.card P :=
  Finset.card_lt_univ_of_notMem (x := q) (by simp [hq])

lemma cntF_mono [Fintype P] {f g : Phase2 m → Bool} {loc : P → Phase2 m}
    (h : ∀ x, f x = true → g x = true) : cntF f loc ≤ cntF g loc :=
  Finset.card_le_card fun q => by simpa using h _

/-- Sum of a counter vector after incrementing a component. -/
lemma sum_update_succ (c : Fin m → ℕ) (v : Fin m) :
    ∑ u, Function.update c v (c v + 1) u = ∑ u, c u + 1 := by
  have := Fintype.sum_update_add c v (c v + 1); omega

/-- Sum of a counter vector after decrementing a positive component. -/
lemma sum_update_pred (c : Fin m → ℕ) (v : Fin m) (hv : 0 < c v) :
    ∑ u, Function.update c v (c v - 1) u + 1 = ∑ u, c u := by
  have := Fintype.sum_update_add c v (c v - 1); omega

/-! ### The safety invariant -/

/-- Idle, or about to increment `c_v`. -/
def idleIncB (v : Fin m) : Phase2 m → Bool
  | .idle => true
  | .inc w => decide (w = v)
  | _ => false

/-- About to decrement `c_u`. -/
def decAtB (u : Fin m) : Phase2 m → Bool
  | .dec w => decide (w = u)
  | _ => false

/-- About to scan or to decrement. -/
def sdB : Phase2 m → Bool
  | .scan => true
  | .dec _ => true
  | _ => false

/-- Processes that may still hurt the lead of `v`: idle ones, those about to increment some
`w ≠ v`, and those about to decrement `v`. -/
def bad2B (v : Fin m) : Phase2 m → Bool
  | .idle => true
  | .inc w => decide (w ≠ v)
  | .dec w => decide (w = v)
  | _ => false

/-- Number of pending decrements of a phase (`1` for `dec _`, else `0`). -/
def nDec (x : Phase2 m) : ℕ := ∑ u, (decAtB u x).toNat

lemma nDec_dec (w : Fin m) : nDec (.dec w) = 1 := by
  simp [nDec, decAtB, Bool.toNat, Finset.sum_ite_eq]

lemma nDec_of_ne {x : Phase2 m} (h : ∀ w, x ≠ .dec w) : nDec x = 0 := by
  cases x <;> simp_all [nDec, decAtB]

/-- Total number of pending decrements. -/
def sumDec [Fintype P] (loc : P → Phase2 m) : ℕ := ∑ u, cntF (decAtB u) loc

lemma sumDec_update [Fintype P] (loc : P → Phase2 m) (q : P) (l : Phase2 m) :
    sumDec (Function.update loc q l) + nDec (loc q) = sumDec loc + nDec l := by
  simp only [sumDec, nDec, ← Finset.sum_add_distrib, cntF_update]

variable [Fintype P]

variable (S n) in
/-- The safety invariant of the racing bounded counters algorithm. -/
structure RInv2 (S : BCounterSim m (3 * n)) (α : List (Label P (taskObj (Fin m) (Fin m))))
    (C : Cfg2 S) : Prop where
  inv : S.Inv (C.mem ())
  idle : ∀ q, C.loc q = .idle → opsOf α q = [] ∧ C.pend q = none
  ph_val : ∀ q w, (C.loc q = .inc w ∨ C.loc q = .done w) → HasInput α w
  cnt_val : ∀ u, 0 < ctr2 S C u → HasInput α u
  incB : ∀ v, ctr2 S C v + cntF (idleIncB v) C.loc + 1 ≤ 3 * n
  decB : ∀ u, cntF (decAtB u) C.loc ≤ ctr2 S C u
  pos : (∃ q, sdB (C.loc q) = true) → sumDec C.loc + 1 ≤ ∑ u, ctr2 S C u
  resp : ∀ q (w : (taskObj (Fin m) (Fin m)).Resp), w ∈ respsOf α q → C.loc q = .done w
  agree : (∀ q w, C.loc q ≠ .done w) ∨
    ∃ v, (∀ q w, C.loc q = .done w → w = v) ∧
      ∀ u, u ≠ v → ctr2 S C u + cntF (bad2B v) C.loc < ctr2 S C v

variable {S : BCounterSim m (3 * n)}

lemma rInv2_init (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) :
    RInv2 n S ([] : List (Label P (taskObj (Fin m) (Fin m)))) (racing2 S n).initCfg where
  inv := S.inv_init
  idle _ _ := ⟨rfl, rfl⟩
  ph_val q w h := by simp [Impl.initCfg, racing2] at h
  cnt_val u h := by simp [ctr2, Impl.initCfg, racing2, S.cnt_init] at h
  incB v := by
    have : cntF (idleIncB v) (racing2 S n).initCfg.loc ≤ Fintype.card P := Finset.card_le_univ _
    simp only [ctr2, Impl.initCfg, racing2, S.cnt_init, Pi.zero_apply] at this ⊢
    omega
  decB u := by simp [cntF, Impl.initCfg, racing2, decAtB]
  pos h := by obtain ⟨q, hq⟩ := h; simp [Impl.initCfg, racing2, sdB] at hq
  resp q w h := by simp only [respsOf_nil] at h; cases h
  agree := Or.inl fun q w h => by simp [Impl.initCfg, racing2] at h

lemma RInv2.step_inv {α : List (Label P (taskObj (Fin m) (Fin m)))} {C C' : Cfg2 S} {q : P}
    {o : Fin m} (hI : RInv2 n S α C) (h : (racing2 S n).step C (.inv q o) = some C') :
    RInv2 n S (α ++ [.inv q o]) C' := by
  obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hctr : ctr2 S C' = ctr2 S C := by simp [ctr2, hmem]
  have hresp : ∀ r, respsOf (α ++ [.inv q o]) r = respsOf α r := by simp [respsOf, Label.retOf]
  have hops : ∀ r, r ≠ q → opsOf (α ++ [.inv q o]) r = opsOf α r := by
    intro r hr; simp [opsOf, Label.invOf, Ne.symm hr]
  have hpend' : ∀ r, r ≠ q → C'.pend r = C.pend r := by
    intro r hr; simp [hpend, Function.update_of_ne hr]
  by_cases hph : C.loc q = .idle
  · have hin : HasInput (α ++ [.inv q o]) o :=
      ⟨q, by simp [inputs, opsOf_append, (hI.idle q hph).1, Label.invOf]; rfl⟩
    have hl : C'.loc = Function.update C.loc q (.inc o) := by rw [hloc, hph]; rfl
    have hlq : C'.loc q = .inc o := by simp [hl]
    have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := by
      intro r hr; simp [hl, Function.update_of_ne hr]
    refine ⟨by rw [hmem]; exact hI.inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; cases hr
      · rw [hlr r hrq] at hr
        exact ⟨by rw [hops r hrq]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
    · intro r w hr
      by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr
        rcases hr with hr | hr <;> cases hr; exact hin
      · rw [hlr r hrq] at hr; exact (hI.ph_val r w hr).append _
    · intro u hu; rw [hctr] at hu; exact (hI.cnt_val u hu).append _
    · intro v
      have := cntF_update (idleIncB v) C.loc q (.inc o)
      rw [← hl, hph] at this
      have h2 := hI.incB v
      have : (idleIncB v (.inc o)).toNat ≤ 1 := Bool.toNat_le _
      simp only [idleIncB, Bool.toNat_true] at *
      rw [hctr]; omega
    · intro u
      have := cntF_update (decAtB u) C.loc q (.inc o)
      rw [← hl, hph] at this
      simp only [decAtB, Bool.toNat_false] at this
      rw [hctr]; have := hI.decB u; omega
    · rintro ⟨r, hr⟩
      have hrq : r ≠ q := by rintro rfl; rw [hlq] at hr; simp [sdB] at hr
      rw [hlr r hrq] at hr
      have h1 := hI.pos ⟨r, hr⟩
      have := sumDec_update C.loc q (.inc o)
      rw [← hl, hph, nDec_of_ne (by simp), nDec_of_ne (by simp)] at this
      rw [hctr]; omega
    · intro r w hr
      rw [hresp] at hr
      have := hI.resp r w hr
      by_cases hrq : r = q
      · subst hrq; rw [hph] at this; cases this
      · rw [hlr r hrq]; exact this
    · rcases hI.agree with hA | ⟨v, hv, hlt⟩
      · left; intro r w hr
        by_cases hrq : r = q
        · subst hrq; rw [hlq] at hr; cases hr
        · rw [hlr r hrq] at hr; exact hA r w hr
      · right; refine ⟨v, fun r w hr => ?_, fun u hu => ?_⟩
        · by_cases hrq : r = q
          · subst hrq; rw [hlq] at hr; cases hr
          · rw [hlr r hrq] at hr; exact hv r w hr
        · have := cntF_update (bad2B v) C.loc q (.inc o)
          rw [← hl, hph] at this
          simp only [bad2B, Bool.toNat_true] at this
          have h3 := Bool.toNat_le (decide (o ≠ v))
          have := hlt u hu
          rw [hctr]; omega
  · have hl : C'.loc = C.loc := by rw [hloc, invoke2_ne_idle hph]; simp
    refine ⟨by rw [hmem]; exact hI.inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      rw [hl] at hr
      have hrq : r ≠ q := by rintro rfl; exact hph hr
      exact ⟨by rw [hops r hrq]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
    · intro r w hr; rw [hl] at hr; exact (hI.ph_val r w hr).append _
    · intro u hu; rw [hctr] at hu; exact (hI.cnt_val u hu).append _
    · intro v; rw [hl, hctr]; exact hI.incB v
    · intro u; rw [hl, hctr]; exact hI.decB u
    · rw [hl, hctr]; exact hI.pos
    · intro r w hr; rw [hresp] at hr; rw [hl]; exact hI.resp r w hr
    · rw [hl, hctr]; exact hI.agree

lemma RInv2.step_ret {α : List (Label P (taskObj (Fin m) (Fin m)))} {C C' : Cfg2 S} {q : P}
    {o : (taskObj (Fin m) (Fin m)).Resp} (hI : RInv2 n S α C)
    (h : (racing2 S n).step C (.ret q o) = some C') : RInv2 n S (α ++ [.ret q o]) C' := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have hctr : ctr2 S C' = ctr2 S C := by simp [ctr2, hmem]
  have hops : ∀ r, opsOf (α ++ [.ret q o]) r = opsOf α r := by simp [opsOf, Label.invOf]
  have hin : ∀ w, HasInput (α ++ [.ret q o]) w ↔ HasInput α w := by
    intro w; simp only [HasInput, inputs, hops]
  rcases hph : C.loc q with _ | w | w | _ | w
  · exact absurd (hI.idle q hph).2 h0
  · rw [hph] at hact; cases hact
  · rw [hph] at hact; cases hact
  · rw [hph] at hact; cases hact
  rw [act2_done hph] at hact
  injection hact with h1 h2
  subst h2; subst w
  have hl : C'.loc = C.loc := by rw [hloc, ← hph]; simp
  have hpend' : ∀ r, r ≠ q → C'.pend r = C.pend r := by
    intro r hr; simp [hpend, Function.update_of_ne hr]
  refine ⟨by rw [hmem]; exact hI.inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hl] at hr
    have hrq : r ≠ q := by rintro rfl; rw [hph] at hr; cases hr
    exact ⟨by rw [hops r]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
  · intro r w hr; rw [hl] at hr; exact (hin w).2 (hI.ph_val r w hr)
  · intro u hu; rw [hctr] at hu; exact (hin u).2 (hI.cnt_val u hu)
  · intro v; rw [hl, hctr]; exact hI.incB v
  · intro u; rw [hl, hctr]; exact hI.decB u
  · rw [hl, hctr]; exact hI.pos
  · intro r w' hr
    rw [hl]
    rw [respsOf_append, respsOf_ret_single] at hr
    rcases List.mem_append.1 hr with hr1 | hr1
    · exact hI.resp r w' hr1
    · split_ifs at hr1 with hrq
      · subst hrq; rw [hph, List.mem_singleton.1 hr1]
      · exact absurd hr1 List.not_mem_nil
  · rw [hl, hctr]; exact hI.agree

omit [Fintype P] in
lemma opsOf_tau (α : List (Label P (taskObj (Fin m) (Fin m)))) (q r : P) :
    opsOf (α ++ [.tau q]) r = opsOf α r := by simp [opsOf, Label.invOf]

omit [Fintype P] in
lemma respsOf_tau (α : List (Label P (taskObj (Fin m) (Fin m)))) (q r : P) :
    respsOf (α ++ [.tau q]) r = respsOf α r := by simp [respsOf, Label.retOf]

omit [Fintype P] in
lemma hasInput_tau {α : List (Label P (taskObj (Fin m) (Fin m)))} {q : P} {w : Fin m} :
    HasInput (α ++ [.tau q]) w ↔ HasInput α w := by
  simp only [HasInput, inputs, opsOf_tau]

lemma sumDec_le {C : Cfg2 S} {α : List (Label P (taskObj (Fin m) (Fin m)))}
    (hI : RInv2 n S α C) : sumDec C.loc ≤ ∑ u, ctr2 S C u :=
  Finset.sum_le_sum fun u _ => hI.decB u

lemma RInv2.tau_inc {α : List (Label P (taskObj (Fin m) (Fin m)))} {C : Cfg2 S} {q : P}
    {v : Fin m} (hI : RInv2 n S α C) (hph : C.loc q = .inc v) :
    RInv2 n S (α ++ [.tau q])
      ⟨Function.update C.loc q .scan, C.pend, fun _ => (S.B.δ (C.mem ()) (S.incOp v)).1⟩ := by
  set C' : Cfg2 S :=
    ⟨Function.update C.loc q .scan, C.pend, fun _ => (S.B.δ (C.mem ()) (S.incOp v)).1⟩ with hC'
  have hlt : ctr2 S C v + 1 < 3 * n := by
    have := hI.incB v
    have := cntF_pos (f := idleIncB v) (loc := C.loc) (q := q) (by simp [hph, idleIncB])
    omega
  obtain ⟨hinv, hcnt⟩ := S.inc_ok (C.mem ()) v hI.inv hlt
  have hctr : ctr2 S C' = Function.update (ctr2 S C) v (ctr2 S C v + 1) := hcnt
  have hctr_ne : ∀ u, u ≠ v → ctr2 S C' u = ctr2 S C u := by
    intro u hu; rw [hctr, Function.update_of_ne hu]
  have hctr_v : ctr2 S C' v = ctr2 S C v + 1 := by rw [hctr]; simp
  have hl : C'.loc = Function.update C.loc q .scan := rfl
  have hlq : C'.loc q = .scan := by simp [hl]
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := by
    intro r hr; simp [hl, Function.update_of_ne hr]
  refine ⟨hinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    by_cases hrq : r = q
    · subst hrq; rw [hlq] at hr; cases hr
    · rw [hlr r hrq] at hr; rw [opsOf_tau]; exact hI.idle r hr
  · intro r w hr
    by_cases hrq : r = q
    · subst hrq; rw [hlq] at hr; rcases hr with hr | hr <;> cases hr
    · rw [hlr r hrq] at hr; exact hasInput_tau.2 (hI.ph_val r w hr)
  · intro u hu
    refine hasInput_tau.2 ?_
    by_cases huv : u = v
    · subst huv; exact hI.ph_val q u (Or.inl hph)
    · rw [hctr_ne u huv] at hu; exact hI.cnt_val u hu
  · intro x
    have e := cntF_update (idleIncB x) C.loc q .scan
    rw [← hl, hph] at e
    have := hI.incB x
    by_cases hx : x = v
    · subst hx; simp only [idleIncB, decide_true, Bool.toNat_true, Bool.toNat_false] at e
      rw [hctr_v]; omega
    · simp only [idleIncB, Ne.symm hx, decide_false, Bool.toNat_false] at e
      rw [hctr_ne x hx]; omega
  · intro x
    have e := cntF_update (decAtB x) C.loc q .scan
    rw [← hl, hph] at e
    simp only [decAtB, Bool.toNat_false] at e
    have := hI.decB x
    have : ctr2 S C x ≤ ctr2 S C' x := by
      by_cases hx : x = v
      · subst hx; omega
      · rw [hctr_ne x hx]
    omega
  · intro _
    have e := sumDec_update C.loc q .scan
    rw [← hl, hph, nDec_of_ne (by simp), nDec_of_ne (by simp)] at e
    have := sumDec_le hI
    rw [hctr, sum_update_succ]; omega
  · intro r w hr
    rw [respsOf_tau] at hr
    have := hI.resp r w hr
    by_cases hrq : r = q
    · subst hrq; rw [hph] at this; cases this
    · rw [hlr r hrq]; exact this
  · rcases hI.agree with hA | ⟨v0, hv, hlt0⟩
    · left; intro r w hr
      by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; cases hr
      · rw [hlr r hrq] at hr; exact hA r w hr
    · right; refine ⟨v0, fun r w hr => ?_, fun u hu => ?_⟩
      · by_cases hrq : r = q
        · subst hrq; rw [hlq] at hr; cases hr
        · rw [hlr r hrq] at hr; exact hv r w hr
      · have e := cntF_update (bad2B v0) C.loc q .scan
        rw [← hl, hph] at e
        have := hlt0 u hu
        by_cases hv0 : v = v0
        · subst hv0
          simp only [bad2B, ne_eq, not_true_eq_false, decide_false, Bool.toNat_false] at e
          rw [hctr_ne u hu, hctr_v]; omega
        · simp only [bad2B, ne_eq, hv0, not_false_eq_true, decide_true, Bool.toNat_true,
            Bool.toNat_false] at e
          have h2 : ctr2 S C' v0 = ctr2 S C v0 := hctr_ne v0 (Ne.symm hv0)
          by_cases huv : u = v
          · subst huv; rw [hctr_v, h2]; omega
          · rw [hctr_ne u huv, h2]; omega

lemma RInv2.tau_dec {α : List (Label P (taskObj (Fin m) (Fin m)))} {C : Cfg2 S} {q : P}
    {v : Fin m} (hI : RInv2 n S α C) (hph : C.loc q = .dec v) :
    RInv2 n S (α ++ [.tau q])
      ⟨Function.update C.loc q .scan, C.pend, fun _ => (S.B.δ (C.mem ()) (S.decOp v)).1⟩ := by
  set C' : Cfg2 S :=
    ⟨Function.update C.loc q .scan, C.pend, fun _ => (S.B.δ (C.mem ()) (S.decOp v)).1⟩ with hC'
  have hpos1 : 1 ≤ cntF (decAtB v) C.loc :=
    cntF_pos (f := decAtB v) (loc := C.loc) (q := q) (by simp [hph, decAtB])
  have hlt : 0 < ctr2 S C v := by have := hI.decB v; omega
  obtain ⟨hinv, hcnt⟩ := S.dec_ok (C.mem ()) v hI.inv hlt
  have hctr : ctr2 S C' = Function.update (ctr2 S C) v (ctr2 S C v - 1) := hcnt
  have hctr_ne : ∀ u, u ≠ v → ctr2 S C' u = ctr2 S C u := by
    intro u hu; rw [hctr, Function.update_of_ne hu]
  have hctr_v : ctr2 S C' v = ctr2 S C v - 1 := by rw [hctr]; simp
  have hctr_le : ∀ u, ctr2 S C' u ≤ ctr2 S C u := by
    intro u; by_cases hu : u = v
    · subst hu; omega
    · rw [hctr_ne u hu]
  have hl : C'.loc = Function.update C.loc q .scan := rfl
  have hlq : C'.loc q = .scan := by simp [hl]
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := by
    intro r hr; simp [hl, Function.update_of_ne hr]
  refine ⟨hinv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    by_cases hrq : r = q
    · subst hrq; rw [hlq] at hr; cases hr
    · rw [hlr r hrq] at hr; rw [opsOf_tau]; exact hI.idle r hr
  · intro r w hr
    by_cases hrq : r = q
    · subst hrq; rw [hlq] at hr; rcases hr with hr | hr <;> cases hr
    · rw [hlr r hrq] at hr; exact hasInput_tau.2 (hI.ph_val r w hr)
  · intro u hu
    exact hasInput_tau.2 (hI.cnt_val u (by have := hctr_le u; omega))
  · intro x
    have e := cntF_update (idleIncB x) C.loc q .scan
    rw [← hl, hph] at e
    simp only [idleIncB, Bool.toNat_false] at e
    have := hI.incB x; have := hctr_le x; omega
  · intro x
    have e := cntF_update (decAtB x) C.loc q .scan
    rw [← hl, hph] at e
    have := hI.decB x
    by_cases hx : x = v
    · subst hx; simp only [decAtB, decide_true, Bool.toNat_true, Bool.toNat_false] at e
      rw [hctr_v]; omega
    · simp only [decAtB, Ne.symm hx, decide_false, Bool.toNat_false] at e
      rw [hctr_ne x hx]; omega
  · intro _
    have h1 := hI.pos ⟨q, by simp [hph, sdB]⟩
    have e := sumDec_update C.loc q .scan
    rw [← hl, hph, nDec_dec, nDec_of_ne (by simp)] at e
    have := sum_update_pred (ctr2 S C) v hlt
    rw [hctr]; omega
  · intro r w hr
    rw [respsOf_tau] at hr
    have := hI.resp r w hr
    by_cases hrq : r = q
    · subst hrq; rw [hph] at this; cases this
    · rw [hlr r hrq]; exact this
  · rcases hI.agree with hA | ⟨v0, hv, hlt0⟩
    · left; intro r w hr
      by_cases hrq : r = q
      · subst hrq; rw [hlq] at hr; cases hr
      · rw [hlr r hrq] at hr; exact hA r w hr
    · right; refine ⟨v0, fun r w hr => ?_, fun u hu => ?_⟩
      · by_cases hrq : r = q
        · subst hrq; rw [hlq] at hr; cases hr
        · rw [hlr r hrq] at hr; exact hv r w hr
      · have e := cntF_update (bad2B v0) C.loc q .scan
        rw [← hl, hph] at e
        have := hlt0 u hu
        by_cases hv0 : v = v0
        · subst hv0
          simp only [bad2B, decide_true, Bool.toNat_true, Bool.toNat_false] at e
          rw [hctr_ne u hu, hctr_v]; omega
        · simp only [bad2B, hv0, decide_false, Bool.toNat_false] at e
          have h2 : ctr2 S C' v0 = ctr2 S C v0 := hctr_ne v0 (Ne.symm hv0)
          have := hctr_le u
          rw [h2]; omega

omit [Fintype P] in
lemma afterScan2_cases (n : ℕ) (c : Fin m → ℕ) :
    (Lead n c (argmax c) ∧ afterScan2 n c = .done (argmax c)) ∨
    (¬ Lead n c (argmax c) ∧ argmaxOther c (argmax c) ≠ argmax c ∧
      n ≤ c (argmaxOther c (argmax c)) ∧ afterScan2 n c = .dec (argmaxOther c (argmax c))) ∨
    (¬ Lead n c (argmax c) ∧
      ¬ (argmaxOther c (argmax c) ≠ argmax c ∧ n ≤ c (argmaxOther c (argmax c))) ∧
      afterScan2 n c = .inc (argmax c)) := by
  unfold afterScan2
  split_ifs with h1 h2
  · left; exact ⟨h1, rfl⟩
  · right; left; exact ⟨h1, h2.1, h2.2, rfl⟩
  · right; right; exact ⟨h1, h2, rfl⟩

omit [Fintype P] in
/-- If a scan neither decides nor decrements, the promoted value is below `2n`. -/
lemma lt_two_n {c : Fin m → ℕ} {w : Fin m} (hnl : ¬ Lead n c w)
    (hnd : ¬ (argmaxOther c w ≠ w ∧ n ≤ c (argmaxOther c w))) : c w < 2 * n := by
  unfold Lead at hnl
  push Not at hnl
  obtain ⟨u, hu, hlt⟩ := hnl
  have h1 := argmaxOther_ne (c := c) hu
  have h2 := le_argmaxOther (c := c) hu
  have : c (argmaxOther c w) < n := by
    by_contra h; exact hnd ⟨h1, by omega⟩
  omega

lemma RInv2.tau_scan (hn : Fintype.card P ≤ n) {α : List (Label P (taskObj (Fin m) (Fin m)))}
    {C : Cfg2 S} {q : P} (hI : RInv2 n S α C) (hph : C.loc q = .scan) :
    RInv2 n S (α ++ [.tau q])
      ⟨Function.update C.loc q (afterScan2 n (ctr2 S C)), C.pend, C.mem⟩ := by
  have hcases := afterScan2_cases n (ctr2 S C)
  set c := ctr2 S C with hc
  set w := argmax c with hw
  set o := argmaxOther c w with ho
  set X := afterScan2 n c with hX
  set C' : Cfg2 S := ⟨Function.update C.loc q X, C.pend, C.mem⟩ with hC'
  have hctr : ctr2 S C' = c := rfl
  have hl : C'.loc = Function.update C.loc q X := rfl
  have hlq : C'.loc q = X := by simp [hl]
  have hlr : ∀ r, r ≠ q → C'.loc r = C.loc r := by
    intro r hr; simp [hl, Function.update_of_ne hr]
  have hposC : sumDec C.loc + 1 ≤ ∑ u, c u := hI.pos ⟨q, by simp [hph, sdB]⟩
  have hincB : ∀ x, c x + cntF (idleIncB x) C.loc + 1 ≤ 3 * n := hI.incB
  have hdecB : ∀ x, cntF (decAtB x) C.loc ≤ c x := hI.decB
  have hwpos : 0 < c w := by
    by_contra h0
    have : ∀ u, c u = 0 := fun u => by have := le_argmax c u; rw [← hw] at this; omega
    simp [this] at hposC
  have hfree : ∀ f : Phase2 m → Bool, f .scan = false → cntF f C.loc + 1 ≤ n := by
    intro f hf
    have := cntF_lt (f := f) (loc := C.loc) (q := q) (by rw [hph]; exact hf)
    omega
  have hXne : X ≠ .idle ∧ X ≠ .scan := by
    rcases hcases with ⟨-, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> simp
  have hwin : HasInput α w := hI.cnt_val w hwpos
  refine ⟨hI.inv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    by_cases hrq : r = q
    · subst hrq; rw [hlq] at hr; exact absurd hr hXne.1
    · rw [hlr r hrq] at hr; rw [opsOf_tau]; exact hI.idle r hr
  · intro r w' hr
    refine hasInput_tau.2 ?_
    by_cases hrq : r = q
    · subst hrq; rw [hlq] at hr
      rcases hcases with ⟨-, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] at hr <;>
        rcases hr with hr | hr <;> cases hr <;> exact hwin
    · rw [hlr r hrq] at hr; exact hI.ph_val r w' hr
  · intro u hu; exact hasInput_tau.2 (hI.cnt_val u hu)
  · intro x
    have e := cntF_update (idleIncB x) C.loc q X
    rw [← hl, hph] at e
    simp only [idleIncB, Bool.toNat_false, add_zero] at e
    have := hincB x
    rcases hcases with ⟨-, h⟩ | ⟨-, -, -, h⟩ | ⟨hnl, hnd, h⟩
    · rw [h] at e; simp only [Bool.toNat_false] at e; rw [hctr]; omega
    · rw [h] at e; simp only [Bool.toNat_false] at e; rw [hctr]; omega
    · rw [h] at e
      by_cases hx : w = x
      · subst hx
        simp only [decide_true, Bool.toNat_true] at e
        have h1 := lt_two_n hnl hnd
        have h2 := hfree (idleIncB w) rfl
        rw [hctr]; omega
      · simp only [hx, decide_false, Bool.toNat_false] at e
        rw [hctr]; omega
  · intro x
    have e := cntF_update (decAtB x) C.loc q X
    rw [← hl, hph] at e
    simp only [decAtB, Bool.toNat_false, add_zero] at e
    have := hdecB x
    rcases hcases with ⟨-, h⟩ | ⟨-, hne, hno, h⟩ | ⟨-, -, h⟩
    · rw [h] at e; simp only [Bool.toNat_false] at e; rw [hctr]; omega
    · rw [h] at e
      by_cases hx : o = x
      · subst hx
        simp only [decide_true, Bool.toNat_true] at e
        have h2 := hfree (decAtB o) rfl
        rw [hctr]; omega
      · simp only [hx, decide_false, Bool.toNat_false] at e
        rw [hctr]; omega
    · rw [h] at e; simp only [Bool.toNat_false] at e; rw [hctr]; omega
  · intro _
    have e := sumDec_update C.loc q X
    rw [← hl, hph, nDec_of_ne (by simp)] at e
    rw [hctr]
    rcases hcases with ⟨-, h⟩ | ⟨-, hne, hno, h⟩ | ⟨-, -, h⟩
    · rw [h, nDec_of_ne (by simp)] at e; omega
    · rw [h, nDec_dec] at e
      -- two more pending decrements than before are covered by `c w` and `c o`
      have hwo : c o ≤ c w := le_argmax c o
      have hpt : ∀ x, cntF (decAtB x) C.loc + ((if x = w then 1 else 0) + (if x = o then 1 else 0))
          ≤ c x := by
        intro x
        have hd := hdecB x
        by_cases hxw : x = w
        · rw [hxw] at hd ⊢
          have := hfree (decAtB w) rfl
          simp [Ne.symm hne]; omega
        · by_cases hxo : x = o
          · rw [hxo] at hd hxw ⊢
            have := hfree (decAtB o) rfl
            simp [hxw]; omega
          · simp [hxw, hxo]; omega
      have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
      simp only [sumDec] at e ⊢
      omega
    · rw [h, nDec_of_ne (by simp)] at e; omega
  · intro r w' hr
    rw [respsOf_tau] at hr
    have := hI.resp r w' hr
    by_cases hrq : r = q
    · subst hrq; rw [hph] at this; cases this
    · rw [hlr r hrq]; exact this
  · have hdone : ∀ r v, C'.loc r = .done v → (r = q ∧ X = .done v) ∨ (r ≠ q ∧ C.loc r = .done v) := by
      intro r v hr
      by_cases hrq : r = q
      · subst hrq; left; rw [hlq] at hr; exact ⟨rfl, hr⟩
      · right; rw [hlr r hrq] at hr; exact ⟨hrq, hr⟩
    rcases hI.agree with hA | ⟨v, hv, hlt⟩
    · rcases hcases with ⟨hL, h⟩ | ⟨hnl, -, -, h⟩ | ⟨hnl, -, h⟩
      · right; refine ⟨w, fun r v hr => ?_, fun u hu => ?_⟩
        · rcases hdone r v hr with ⟨-, h1⟩ | ⟨-, h1⟩
          · rw [h] at h1; cases h1; rfl
          · exact absurd h1 (hA r v)
        · have e := cntF_update (bad2B w) C.loc q X
          rw [← hl, hph, h] at e
          simp only [bad2B, Bool.toNat_false, add_zero] at e
          have h2 := hfree (bad2B w) rfl
          have h3 := hL u hu
          rw [hctr]; omega
      · left; intro r v hr
        rcases hdone r v hr with ⟨-, h1⟩ | ⟨-, h1⟩
        · rw [h] at h1; cases h1
        · exact hA r v h1
      · left; intro r v hr
        rcases hdone r v hr with ⟨-, h1⟩ | ⟨-, h1⟩
        · rw [h] at h1; cases h1
        · exact hA r v h1
    · have hlt' : ∀ u, u ≠ v → c u + cntF (bad2B v) C.loc < c v := hlt
      have hwv : w = v := argmax_eq fun u hu => by have := hlt' u hu; omega
      have hbad : bad2B v X = false := by
        rcases hcases with ⟨-, h⟩ | ⟨-, hne, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
        · rfl
        · simp [bad2B, ← hwv, hne]
        · simp [bad2B, hwv]
      right; refine ⟨v, fun r v' hr => ?_, fun u hu => ?_⟩
      · rcases hdone r v' hr with ⟨-, h1⟩ | ⟨-, h1⟩
        · rcases hcases with ⟨-, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] at h1 <;> cases h1
          exact hwv
        · exact hv r v' h1
      · have e := cntF_update (bad2B v) C.loc q X
        rw [← hl, hph, hbad] at e
        simp only [bad2B, Bool.toNat_false, add_zero] at e
        have := hlt' u hu
        rw [hctr]; omega

lemma RInv2.step_tau (hn : Fintype.card P ≤ n) {α : List (Label P (taskObj (Fin m) (Fin m)))}
    {C C' : Cfg2 S} {q : P} (hI : RInv2 n S α C) (h : (racing2 S n).step C (.tau q) = some C') :
    RInv2 n S (α ++ [.tau q]) C' := by
  have hp : C.pend q ≠ none := (Impl.step_tau h).1
  rcases hph : C.loc q with _ | v | v | _ | w
  · exact absurd (hI.idle q hph).2 hp
  · rw [step2_tau_inc hp hph] at h; cases h; exact hI.tau_inc hph
  · rw [step2_tau_dec hp hph] at h; cases h; exact hI.tau_dec hph
  · rw [step2_tau_scan hp hph] at h; cases h
    have hm : (fun _ : Unit => (S.B.δ (C.mem ()) S.scanOp).1) = C.mem :=
      funext fun i => by cases i; exact S.scan_state _
    rw [S.scan_resp _ hI.inv, hm]
    exact hI.tau_scan hn hph
  · obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
    rw [hph] at hact; cases hact

/-- The safety invariant holds in every reachable configuration (if `1 ≤ n` and `|P| ≤ n`). -/
theorem rInv2_run (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n)
    {α : List (Label P (taskObj (Fin m) (Fin m)))} {C : Cfg2 S}
    (h : (racing2 S n).run α = some C) : RInv2 n S α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [Impl.run_nil, Option.some.injEq] at h; subst h; exact rInv2_init hn hn1
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (racing2 S n).runFrom (racing2 S n).initCfg α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      have hI := ih hα
      cases ℓ with
      | inv q o => exact hI.step_inv h
      | ret q o => exact hI.step_ret h
      | tau q => exact hI.step_tau hn h

/-- In every reachable configuration the representation invariant of the bounded counter
simulation holds; for the bounded counter object: it never breaks. -/
theorem racing2_inv (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) {C : Cfg2 (P := P) S}
    (h : (racing2 S n).Reachable C) : S.Inv (C.mem ()) := by
  obtain ⟨α, hα⟩ := h; exact (rInv2_run hn hn1 hα).inv

/-- Agreement and validity hold in every finite execution of the racing bounded counters
algorithm (if `1 ≤ n` and `|P| ≤ n`). -/
theorem racing2_safe (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n)
    (α : List (Label P (taskObj (Fin m) (Fin m)))) (hα : (racing2 S n).Valid α) :
    (consensus P (Fin m)).Δ (inputs α) (outputs α) := by
  obtain ⟨C, hC⟩ := hα
  have hI := rInv2_run hn hn1 hC
  have hout : ∀ q (w : (taskObj (Fin m) (Fin m)).Resp), outputs α q = some w → C.loc q = .done w :=
    fun q w h => hI.resp q w (List.mem_of_head? h)
  refine ⟨fun p q x y hx hy => ?_, fun p y hy => hI.ph_val p y (Or.inr (hout p y hy))⟩
  rcases hI.agree with hA | ⟨v, hv, -⟩
  · exact absurd (hout p x hx) (hA p x)
  · rw [hv p x (hout p x hx), hv q y (hout q y hy)]

/-- The racing bounded counters algorithm solves consensus. -/
theorem racing2_solves (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) :
    (racing2 S n).Solves (consensus P (Fin m)) :=
  fun α hα _ => racing2_safe hn hn1 α hα

/-! ### Obstruction-freedom -/

omit [Fintype P] in
lemma soloStep2_eq {C C' : Cfg2 S} {p : P} (hp : C.pend p ≠ none)
    (h : (racing2 S n).step C ((racing2 S n).nextLabel C p) = some C') :
    (racing2 S n).soloStep p C = C' := by
  simp [Impl.soloStep, hp, h]

omit [Fintype P] in
lemma solo2_inc {C : Cfg2 S} {p : P} {v : Fin m} (hp : C.pend p ≠ none)
    (hph : C.loc p = .inc v) (hinv : S.Inv (C.mem ())) (hlt : ctr2 S C v + 1 < 3 * n) :
    ((racing2 S n).soloStep p C).pend p ≠ none ∧ ((racing2 S n).soloStep p C).loc p = .scan ∧
      ctr2 S ((racing2 S n).soloStep p C) = Function.update (ctr2 S C) v (ctr2 S C v + 1) := by
  have hnl : (racing2 S n).nextLabel C p = .tau p := by simp [Impl.nextLabel, racing2, hph]
  rw [soloStep2_eq hp (by rw [hnl]; exact step2_tau_inc hp hph)]
  exact ⟨hp, by simp, (S.inc_ok (C.mem ()) v hinv hlt).2⟩

omit [Fintype P] in
lemma solo2_dec {C : Cfg2 S} {p : P} {v : Fin m} (hp : C.pend p ≠ none)
    (hph : C.loc p = .dec v) (hinv : S.Inv (C.mem ())) (hlt : 0 < ctr2 S C v) :
    ((racing2 S n).soloStep p C).pend p ≠ none ∧ ((racing2 S n).soloStep p C).loc p = .scan ∧
      ctr2 S ((racing2 S n).soloStep p C) = Function.update (ctr2 S C) v (ctr2 S C v - 1) := by
  have hnl : (racing2 S n).nextLabel C p = .tau p := by simp [Impl.nextLabel, racing2, hph]
  rw [soloStep2_eq hp (by rw [hnl]; exact step2_tau_dec hp hph)]
  exact ⟨hp, by simp, (S.dec_ok (C.mem ()) v hinv hlt).2⟩

omit [Fintype P] in
lemma solo2_scan {C : Cfg2 S} {p : P} (hp : C.pend p ≠ none) (hph : C.loc p = .scan)
    (hinv : S.Inv (C.mem ())) :
    ((racing2 S n).soloStep p C).pend p ≠ none ∧
      ((racing2 S n).soloStep p C).loc p = afterScan2 n (ctr2 S C) ∧
      ctr2 S ((racing2 S n).soloStep p C) = ctr2 S C := by
  have hnl : (racing2 S n).nextLabel C p = .tau p := by simp [Impl.nextLabel, racing2, hph]
  rw [soloStep2_eq hp (by rw [hnl]; exact step2_tau_scan hp hph)]
  refine ⟨hp, ?_, congrArg S.cnt (S.scan_state _)⟩
  simp only [Function.update_self]
  rw [S.scan_resp _ hinv]; rfl

omit [Fintype P] in
lemma solo2_done {C : Cfg2 S} {p : P} {w : Fin m} (hp : C.pend p ≠ none)
    (hph : C.loc p = .done w) : ((racing2 S n).soloStep p C).pend p = none := by
  have hnl : (racing2 S n).nextLabel C p = .ret p w := by simp [Impl.nextLabel, act2_done hph]
  have hs : (racing2 S n).step C (.ret p w) =
      some { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p (.done w) } := by
    simp [Impl.step, hp, act2_done hph]; rfl
  rw [soloStep2_eq hp (by rw [hnl]; exact hs)]
  simp

/-- Solo run from a configuration where `p` is about to increment a value `w` leading by `k`
while all other components are below `n`. -/
lemma solo2_lead (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) (p : P) (j : ℕ) :
    ∀ (C : Cfg2 S) (k : ℕ) (w : Fin m), (racing2 S n).Reachable C → C.pend p ≠ none →
      C.loc p = .inc w → Lead k (ctr2 S C) w → (∀ u, u ≠ w → ctr2 S C u < n) → n ≤ k + j →
      ∃ t, (((racing2 S n).soloStep p)^[t] C).pend p = none := by
  induction j with
  | zero =>
    intro C k w hR hp hph hL hlow hk
    obtain ⟨α, hα⟩ := hR
    have hI := rInv2_run hn hn1 hα
    have hlt : ctr2 S C w + 1 < 3 * n := by
      have := hI.incB w
      have := cntF_pos (f := idleIncB w) (loc := C.loc) (q := p) (by simp [hph, idleIncB])
      omega
    obtain ⟨hp1, hph1, hc1⟩ := solo2_inc hp hph hI.inv hlt
    obtain ⟨α1, hα1⟩ := Impl.Reachable.soloStep (I := racing2 S n) ⟨α, hα⟩ p
    obtain ⟨hp2, hph2, -⟩ := solo2_scan hp1 hph1 (rInv2_run hn hn1 hα1).inv
    have hL1 : Lead (k + 1) (ctr2 S ((racing2 S n).soloStep p C)) w := by rw [hc1]; exact hL.inc
    rcases afterScan2_cases n (ctr2 S ((racing2 S n).soloStep p C)) with
      ⟨-, h⟩ | ⟨hnl, -⟩ | ⟨hnl, -⟩
    · rw [h] at hph2; exact ⟨3, solo2_done hp2 hph2⟩
    · exact absurd (hL1.argmax_eq ▸ hL1.mono (by omega)) hnl
    · exact absurd (hL1.argmax_eq ▸ hL1.mono (by omega)) hnl
  | succ j ih =>
    intro C k w hR hp hph hL hlow hk
    obtain ⟨α, hα⟩ := hR
    have hI := rInv2_run hn hn1 hα
    have hlt : ctr2 S C w + 1 < 3 * n := by
      have := hI.incB w
      have := cntF_pos (f := idleIncB w) (loc := C.loc) (q := p) (by simp [hph, idleIncB])
      omega
    obtain ⟨hp1, hph1, hc1⟩ := solo2_inc hp hph hI.inv hlt
    obtain ⟨α1, hα1⟩ := Impl.Reachable.soloStep (I := racing2 S n) ⟨α, hα⟩ p
    obtain ⟨hp2, hph2, hc2⟩ := solo2_scan hp1 hph1 (rInv2_run hn hn1 hα1).inv
    set C1 := (racing2 S n).soloStep p C with hC1
    have hL1 : Lead (k + 1) (ctr2 S C1) w := by rw [hc1]; exact hL.inc
    have hlow1 : ∀ u, u ≠ w → ctr2 S C1 u < n := by
      intro u hu; rw [hc1, Function.update_of_ne hu]; exact hlow u hu
    have ham := hL1.argmax_eq
    rcases afterScan2_cases n (ctr2 S C1) with ⟨-, h⟩ | ⟨-, hne, hno, -⟩ | ⟨hnl, -, h⟩
    · rw [h] at hph2; exact ⟨3, solo2_done hp2 hph2⟩
    · rw [ham] at hne hno; exact absurd (hlow1 _ hne) (by omega)
    · rw [h, ham] at hph2
      obtain ⟨t, ht⟩ := ih ((racing2 S n).soloStep p C1) (k + 1) w
        (Impl.Reachable.soloStep (I := racing2 S n) ⟨α1, hα1⟩ p) hp2 hph2 (by rw [hc2]; exact hL1)
        (by rw [hc2]; exact hlow1) (by omega)
      exact ⟨t + 2, by rw [Function.iterate_add_apply]; exact ht⟩

/-- Solo run from a configuration where `p` is about to scan. -/
lemma solo2_from_scan (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) (p : P) (s : ℕ) :
    ∀ C : Cfg2 S, (racing2 S n).Reachable C → C.pend p ≠ none → C.loc p = .scan →
      ∑ u, ctr2 S C u ≤ s → ∃ t, (((racing2 S n).soloStep p)^[t] C).pend p = none := by
  induction s with
  | zero => ?_
  | succ s ih => ?_
  all_goals
    intro C hR hp hph hs
    obtain ⟨α, hα⟩ := hR
    have hI := rInv2_run hn hn1 hα
    obtain ⟨hp1, hph1, hc1⟩ := solo2_scan hp hph hI.inv
    obtain ⟨α1, hα1⟩ := Impl.Reachable.soloStep (I := racing2 S n) ⟨α, hα⟩ p
    rcases afterScan2_cases n (ctr2 S C) with ⟨-, h⟩ | ⟨-, hne, hno, h⟩ | ⟨hnl, hnd, h⟩
    · rw [h] at hph1; exact ⟨2, solo2_done hp1 hph1⟩
    · rw [h] at hph1
      have hpos : 0 < ctr2 S ((racing2 S n).soloStep p C) (argmaxOther (ctr2 S C) (argmax (ctr2 S C))) := by
        rw [hc1]; omega
      have hI1 := rInv2_run hn hn1 hα1
      obtain ⟨hp2, hph2, hc2⟩ := solo2_dec hp1 hph1 hI1.inv hpos
      have hsum := sum_update_pred _ _ hpos
      rw [← hc2, hc1] at hsum
      first
        | (exfalso
           have := Finset.single_le_sum (f := ctr2 S C) (fun _ _ => Nat.zero_le _)
             (Finset.mem_univ (argmaxOther (ctr2 S C) (argmax (ctr2 S C))))
           omega)
        | (obtain ⟨t, ht⟩ := ih _ (Impl.Reachable.soloStep (I := racing2 S n) ⟨α1, hα1⟩ p) hp2 hph2 (by omega)
           exact ⟨t + 2, by rw [Function.iterate_add_apply]; exact ht⟩)
    · rw [h] at hph1
      have hlow : ∀ u, u ≠ argmax (ctr2 S C) → ctr2 S C u < n := by
        intro u hu
        have h1 := argmaxOther_ne (c := ctr2 S C) hu
        have h2 := le_argmaxOther (c := ctr2 S C) hu
        have : ctr2 S C (argmaxOther (ctr2 S C) (argmax (ctr2 S C))) < n := by
          by_contra hc; exact hnd ⟨h1, by omega⟩
        omega
      obtain ⟨t, ht⟩ := solo2_lead hn hn1 p n _ 0 _ (Impl.Reachable.soloStep (I := racing2 S n) ⟨α, hα⟩ p) hp1 hph1
        (by rw [hc1]; exact lead_zero_argmax _) (by rw [hc1]; exact hlow) (by omega)
      exact ⟨t + 1, by rw [Function.iterate_add_apply]; exact ht⟩

/-- The racing bounded counters algorithm is obstruction-free (if `1 ≤ n` and `|P| ≤ n`). -/
theorem racing2_obstructionFree (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) :
    (racing2 (P := P) S n).ObstructionFree := by
  intro C p hR hp
  obtain ⟨α, hα⟩ := hR
  have hI := rInv2_run hn hn1 hα
  rcases hph : C.loc p with _ | v | v | _ | w
  · exact absurd (hI.idle p hph).2 hp
  · have hlt : ctr2 S C v + 1 < 3 * n := by
      have := hI.incB v
      have := cntF_pos (f := idleIncB v) (loc := C.loc) (q := p) (by simp [hph, idleIncB])
      omega
    obtain ⟨hp1, hph1, -⟩ := solo2_inc hp hph hI.inv hlt
    obtain ⟨t, ht⟩ := solo2_from_scan hn hn1 p _ _ (Impl.Reachable.soloStep (I := racing2 S n) ⟨α, hα⟩ p) hp1 hph1 le_rfl
    exact ⟨t + 1, by rw [Function.iterate_add_apply]; exact ht⟩
  · have hlt : 0 < ctr2 S C v := by
      have := hI.decB v
      have := cntF_pos (f := decAtB v) (loc := C.loc) (q := p) (by simp [hph, decAtB])
      omega
    obtain ⟨hp1, hph1, -⟩ := solo2_dec hp hph hI.inv hlt
    obtain ⟨t, ht⟩ := solo2_from_scan hn hn1 p _ _ (Impl.Reachable.soloStep (I := racing2 S n) ⟨α, hα⟩ p) hp1 hph1 le_rfl
    exact ⟨t + 1, by rw [Function.iterate_add_apply]; exact ht⟩
  · exact solo2_from_scan hn hn1 p _ C ⟨α, hα⟩ hp hph le_rfl
  · exact ⟨1, solo2_done hp hph⟩

/-! ### Lemma 3.2 -/

/-- Lemma 3.2 of [EGSZ16]: obstruction-free `m`-valued consensus among (at most) `n ≥ 1` processes
can be solved using one `m`-component bounded counter with components in `{0, …, 3n-1}`
(initially all `0`); moreover the counter never breaks. -/
theorem lemma_3_2 (m : ℕ) [NeZero m] (n : ℕ) (P : Type) [DecidableEq P] [Fintype P]
    (hn : Fintype.card P ≤ n) (hn1 : 1 ≤ n) :
    ∃ (L : Type) (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => bcounterObj m (3 * n)) P L),
      I.memInit () = some 0 ∧ (∀ p v, I.allowed p v) ∧
        (∀ C, I.Reachable C → C.mem () ≠ none) ∧
        I.Solves (consensus P (Fin m)) ∧ I.ObstructionFree :=
  ⟨Phase2 m, racing2 (bcounterSim m (3 * n)) n, rfl, fun _ _ => trivial,
    fun _ hC => racing2_inv (S := bcounterSim m (3 * n)) hn hn1 hC,
    racing2_solves hn hn1, racing2_obstructionFree hn hn1⟩

end Cslib.SharedMemory.ComplexityHierarchy
