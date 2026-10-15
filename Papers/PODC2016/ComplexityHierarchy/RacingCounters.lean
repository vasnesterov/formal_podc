import Cslib.Computability.Distributed.SharedMemory.Consensus
import Cslib.Computability.Distributed.SharedMemory.Progress
import Mathlib.Data.Finset.Max

/-!
# Racing counters: obstruction-free consensus from counters (Lemma 3.1 of [EGSZ16])

[EGSZ16] F. Ellen, R. Gelashvili, N. Shavit, L. Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016 (arXiv 1607.06139), Section 3.

An `m`-component unbounded counter has components `c_0, …, c_{m-1} ∈ ℕ`, supports `inc v`
(increment `c_v`) and `scan` (return all components). The *racing counters* algorithm solves
obstruction-free `m`-valued consensus among `n` processes: a process promotes (increments) its
input, then alternates between a `scan` and promoting a value with the largest count; when a scan
shows some `c_v` at least `n` larger than every other component, it decides `v`.

To reuse the algorithm for the single-location implementations of Theorem 3.3, it is generic over
a *counter simulation* `CounterSim m P`: a base object `S.B` with an increment operation
`S.incOp p v k` (which may depend on the process `p` and on the number `k` of previous
increments of `c_v` by `p`, as in the `set-bit` implementation), a read-only scan operation
`S.scanOp`, a decoding of scan responses into counts, and an abstraction function `S.cnt` from
states to counts, correct under a representation invariant `S.Inv` relating the state with the
per-process increment counts. The `m`-component counter object `counterObj m` is the trivial
instance (`counterSim`).

## Main results

* `racing_solves`: the algorithm satisfies agreement and validity in *every* execution (not only
  one-shot ones), provided `Fintype.card P ≤ n`.
* `racing_obstructionFree`: it is obstruction-free (CSLib's `Impl.ObstructionFree`, from every
  reachable configuration, including ones where processes were re-invoked).
* `lemma_3_1`: Lemma 3.1 of [EGSZ16] for the counter object.

## Modelling choices / deviations from the paper

* Tie-breaking: the promoted value after a scan is `argmax c`, *some* index of a maximal count
  (chosen by `Classical.choose`; the paper breaks ties arbitrarily).
* Decision rule: the process decides `argmax c` if it is at least `n` larger than every other
  component. For `n ≥ 1` this is exactly the paper's rule (a component `n` larger than all others
  is the unique maximum); the threshold `n` is a parameter and agreement needs `|P| ≤ n`.
* A process that has decided and is invoked again returns its decision immediately (one-shot tasks
  only constrain one-shot executions; this makes the algorithm a total `Impl` and gives full
  `ObstructionFree`).
* The response of `inc` is an uninformative acknowledgement (`0`).
* Values are `Fin m` with `m ≥ 1` (`[NeZero m]`).
-/

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory

/-! ### The counter object and counter simulations -/

/-- Operations of an `m`-component counter. -/
inductive CounterOp (m : ℕ) where
  /-- Increment component `v`. -/
  | inc (v : Fin m)
  /-- Return all components. -/
  | scan

/-- The `m`-component unbounded counter object: state `Fin m → ℕ`, initially `0`; `inc v`
increments component `v` (acknowledged by the dummy response `0`), `scan` returns the state. -/
abbrev counterObj (m : ℕ) : ObjSpec where
  State := Fin m → ℕ
  Op := CounterOp m
  Resp := Fin m → ℕ
  init := 0
  δ s o := match o with
    | .inc v => (Function.update s v (s v + 1), 0)
    | .scan => (s, s)

/-- A simulation of an `m`-component counter by a base object `B`, for processes `P`.
`incOp p v k` increments `c_v` when performed by `p` after `k` previous increments of `c_v` by
`p`; `Inv s c` is a representation invariant relating the state `s` with the per-process
increment counts `c`. -/
structure CounterSim (m : ℕ) (P : Type) [DecidableEq P] where
  /-- The base object. -/
  B : ObjSpec
  /-- Its initial state. -/
  init : B.State
  /-- The increment operation. -/
  incOp : P → Fin m → ℕ → B.Op
  /-- The scan operation. -/
  scanOp : B.Op
  /-- Decoding a scan response. -/
  decode : B.Resp → Fin m → ℕ
  /-- The counts represented by a state. -/
  cnt : B.State → Fin m → ℕ
  /-- Representation invariant (w.r.t. the per-process increment counts). -/
  Inv : B.State → (P → Fin m → ℕ) → Prop
  inv_init : Inv init 0
  cnt_init : cnt init = 0
  inv_inc : ∀ s c p v, Inv s c →
    Inv (B.δ s (incOp p v (c p v))).1 (Function.update c p (Function.update (c p) v (c p v + 1)))
  cnt_inc : ∀ s c p v, Inv s c →
    cnt (B.δ s (incOp p v (c p v))).1 = Function.update (cnt s) v (cnt s v + 1)
  scan_state : ∀ s, (B.δ s scanOp).1 = s
  scan_resp : ∀ s c, Inv s c → decode (B.δ s scanOp).2 = cnt s

/-- The counter object simulates itself. -/
def counterSim (m : ℕ) (P : Type) [DecidableEq P] : CounterSim m P where
  B := counterObj m
  init := 0
  incOp _ v _ := .inc v
  scanOp := .scan
  decode := id
  cnt := id
  Inv _ _ := True
  inv_init := trivial
  cnt_init := rfl
  inv_inc _ _ _ _ _ := trivial
  cnt_inc _ _ _ _ _ := rfl
  scan_state _ := rfl
  scan_resp _ _ _ := rfl

/-! ### The algorithm -/

variable {m : ℕ}

/-- Program counter of a process. -/
inductive RacingPhase (m : ℕ) where
  /-- Not invoked yet. -/
  | idle
  /-- About to promote (increment) value `w`. -/
  | promote (w : Fin m)
  /-- About to scan. -/
  | scan
  /-- Decided `w`. -/
  | done (w : Fin m)
  deriving DecidableEq

/-- Local state: program counter and the number of own increments of every component. -/
structure RacingLoc (m : ℕ) where
  /-- Program counter. -/
  ph : RacingPhase m
  /-- Number of increments of each component performed by this process. -/
  mine : Fin m → ℕ

/-- Some index of a maximal component (ties broken arbitrarily). -/
noncomputable def argmax [NeZero m] (c : Fin m → ℕ) : Fin m :=
  Classical.choose (Finset.exists_max_image Finset.univ c Finset.univ_nonempty)

lemma le_argmax [NeZero m] (c : Fin m → ℕ) (u : Fin m) : c u ≤ c (argmax c) :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ c Finset.univ_nonempty)).2 u
    (Finset.mem_univ u)

/-- `c_w` is at least `k` larger than every other component. -/
def Lead (k : ℕ) (c : Fin m → ℕ) (w : Fin m) : Prop := ∀ u, u ≠ w → c u + k ≤ c w

instance (k : ℕ) (c : Fin m → ℕ) (w : Fin m) : Decidable (Lead k c w) := by
  unfold Lead; infer_instance

lemma argmax_eq [NeZero m] {c : Fin m → ℕ} {w : Fin m} (h : ∀ u, u ≠ w → c u < c w) :
    argmax c = w := by
  by_contra hne
  have := h _ hne
  have := le_argmax c w
  omega

lemma Lead.argmax_eq [NeZero m] {k : ℕ} {c : Fin m → ℕ} {w : Fin m} (h : Lead (k + 1) c w) :
    argmax c = w :=
  ComplexityHierarchy.argmax_eq fun u hu => by have := h u hu; omega

lemma Lead.mono {k k' : ℕ} {c : Fin m → ℕ} {w : Fin m} (h : Lead k c w) (hk : k' ≤ k) :
    Lead k' c w := fun u hu => by have := h u hu; omega

lemma Lead.inc {k : ℕ} {c : Fin m → ℕ} {w : Fin m} (h : Lead k c w) :
    Lead (k + 1) (Function.update c w (c w + 1)) w := fun u hu => by
  have := h u hu; simp [Function.update_of_ne hu]; omega

lemma lead_zero_argmax [NeZero m] (c : Fin m → ℕ) : Lead 0 c (argmax c) :=
  fun u _ => by simpa using le_argmax c u

/-- The local state after a scan returning counts `c`: decide `argmax c` if it leads by `n`,
otherwise promote it. -/
noncomputable def afterScan [NeZero m] (n : ℕ) (l : RacingLoc m) (c : Fin m → ℕ) : RacingLoc m :=
  if Lead n c (argmax c) then ⟨.done (argmax c), l.mine⟩ else ⟨.promote (argmax c), l.mine⟩

variable {P : Type} [DecidableEq P] [NeZero m]

/-- The racing-counters algorithm (proof of Lemma 3.1 of [EGSZ16]) with decision threshold `n`,
over a counter simulation `S`. -/
noncomputable def racing (S : CounterSim m P) (n : ℕ) :
    Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => S.B) P (RacingLoc m) where
  memInit _ := S.init
  locInit _ := ⟨.idle, 0⟩
  invoke _ l o := match l.ph with
    | .idle => ⟨.promote o, l.mine⟩
    | _ => l
  act p l := match l.ph with
    | .idle => .ret (default : Fin m) l
    | .promote w => .access () (S.incOp p w (l.mine w))
        (fun _ => ⟨.scan, Function.update l.mine w (l.mine w + 1)⟩)
    | .scan => .access () S.scanOp (fun r => afterScan n l (S.decode r))
    | .done w => .ret w l

/-! ### Steps of the algorithm -/

variable (S : CounterSim m P) (n : ℕ)

/-- Configurations of the racing-counters algorithm. -/
abbrev RacingCfg := Config (taskObj (Fin m) (Fin m)) (fun _ : Unit => S.B) P (RacingLoc m)

/-- The counts represented by the memory. -/
def ctr (C : RacingCfg S) : Fin m → ℕ := S.cnt (C.mem ())

variable {S n}

lemma step_tau_promote {C : RacingCfg S} {q : P} {w : Fin m} (hp : C.pend q ≠ none)
    (hph : (C.loc q).ph = .promote w) :
    (racing S n).step C (.tau q) =
      some ⟨Function.update C.loc q ⟨.scan, Function.update (C.loc q).mine w ((C.loc q).mine w + 1)⟩,
        C.pend, fun _ => (S.B.δ (C.mem ()) (S.incOp q w ((C.loc q).mine w))).1⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, racing, hph]
  congr 2

lemma step_tau_scan {C : RacingCfg S} {q : P} (hp : C.pend q ≠ none) (hph : (C.loc q).ph = .scan) :
    (racing S n).step C (.tau q) =
      some ⟨Function.update C.loc q (afterScan n (C.loc q) (S.decode (S.B.δ (C.mem ()) S.scanOp).2)),
        C.pend, fun _ => (S.B.δ (C.mem ()) S.scanOp).1⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, racing, hph]
  congr 2

lemma act_promote {l : RacingLoc m} {q : P} {w : Fin m} (hph : l.ph = .promote w) :
    (racing S n).act q l = .access () (S.incOp q w (l.mine w))
      (fun _ => ⟨.scan, Function.update l.mine w (l.mine w + 1)⟩) := by
  simp [racing, hph]

lemma act_scan {l : RacingLoc m} {q : P} (hph : l.ph = .scan) :
    (racing S n).act q l = .access () S.scanOp (fun r => afterScan n l (S.decode r)) := by
  simp [racing, hph]

lemma act_done {l : RacingLoc m} {q : P} {w : Fin m} (hph : l.ph = .done w) :
    (racing S n).act q l = .ret w l := by
  simp [racing, hph]

lemma act_idle {l : RacingLoc m} {q : P} (hph : l.ph = .idle) :
    (racing S n).act q l = .ret (default : Fin m) l := by
  simp [racing, hph]

lemma invoke_idle {l : RacingLoc m} {q : P} {o : Fin m} (hph : l.ph = .idle) :
    (racing S n).invoke q l o = ⟨.promote o, l.mine⟩ := by
  simp [racing, hph]

lemma invoke_ne_idle {l : RacingLoc m} {q : P} {o : Fin m} (hph : l.ph ≠ .idle) :
    (racing S n).invoke q l o = l := by
  cases h : l.ph <;> simp_all [racing]

/-! ### The safety invariant -/

/-- `w` is the input of some process. -/
def HasInput (α : List (Label P (taskObj (Fin m) (Fin m)))) (w : Fin m) : Prop :=
  ∃ r, inputs α r = some w

lemma HasInput.append {α : List (Label P (taskObj (Fin m) (Fin m)))} {w : Fin m}
    (h : HasInput α w) (β : List (Label P (taskObj (Fin m) (Fin m)))) : HasInput (α ++ β) w := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  simp only [inputs, opsOf_append] at hr ⊢
  rw [List.head?_append, hr]; rfl

/-- Processes that may still increment a component other than `v`: idle processes and
processes about to promote some `w ≠ v`. -/
def badB (v : Fin m) : RacingPhase m → Bool
  | .idle => true
  | .promote w => decide (w ≠ v)
  | _ => false

variable [Fintype P]

variable (S) in
/-- The set of processes that may still increment a component other than `v`. -/
def bad (C : RacingCfg S) (v : Fin m) : Finset P :=
  Finset.univ.filter (fun q => badB v (C.loc q).ph = true)

variable (S) in
/-- The safety invariant of the racing-counters algorithm. -/
structure RInv (α : List (Label P (taskObj (Fin m) (Fin m)))) (C : RacingCfg S) : Prop where
  sim : S.Inv (C.mem ()) (fun q => (C.loc q).mine)
  idle : ∀ q, (C.loc q).ph = .idle → opsOf α q = [] ∧ C.pend q = none
  ph_val : ∀ q w, ((C.loc q).ph = .promote w ∨ (C.loc q).ph = .done w) → HasInput α w
  cnt_val : ∀ u, 0 < ctr S C u → HasInput α u
  scan_pos : ∀ q, (C.loc q).ph = .scan → ∃ u, 0 < ctr S C u
  resp : ∀ q (w : (taskObj (Fin m) (Fin m)).Resp), w ∈ respsOf α q → (C.loc q).ph = .done w
  agree : (∀ q w, (C.loc q).ph ≠ .done w) ∨
    ∃ v, (∀ q w, (C.loc q).ph = .done w → w = v) ∧
      ∀ u, u ≠ v → ctr S C u + (bad S C v).card < ctr S C v

lemma card_bad_le {C C' : RacingCfg S} {v : Fin m}
    (h : ∀ r, badB v (C'.loc r).ph = true → badB v (C.loc r).ph = true) :
    (bad S C' v).card ≤ (bad S C v).card :=
  Finset.card_le_card fun r => by simpa [bad] using h r

lemma ctr_pos_argmax {c : Fin m → ℕ} (h : ∃ u, 0 < c u) : 0 < c (argmax c) := by
  obtain ⟨u, hu⟩ := h; have := le_argmax c u; omega

lemma rInv_init : RInv S [] (racing S n).initCfg where
  sim := S.inv_init
  idle _ _ := ⟨rfl, rfl⟩
  ph_val q w h := by simp [Impl.initCfg, racing] at h
  cnt_val u h := by simp [ctr, Impl.initCfg, racing, S.cnt_init] at h
  scan_pos q h := by simp [Impl.initCfg, racing] at h
  resp q w h := by simp only [respsOf_nil] at h; cases h
  agree := Or.inl fun q w h => by simp [Impl.initCfg, racing] at h

lemma RInv.step_inv {α : List (Label P (taskObj (Fin m) (Fin m)))} {C C' : RacingCfg S} {q : P} {o : Fin m}
    (hI : RInv S α C) (h : (racing S n).step C (.inv q o) = some C') :
    RInv S (α ++ [.inv q o]) C' := by
  obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hctr : ctr S C' = ctr S C := by simp [ctr, hmem]
  have hresp : ∀ r, respsOf (α ++ [.inv q o]) r = respsOf α r := by simp [respsOf, Label.retOf]
  have hops : ∀ r, r ≠ q → opsOf (α ++ [.inv q o]) r = opsOf α r := by
    intro r hr; simp [opsOf, Label.invOf, Ne.symm hr]
  have hpend' : ∀ r, r ≠ q → C'.pend r = C.pend r := by
    intro r hr; simp [hpend, Function.update_of_ne hr]
  by_cases hph : (C.loc q).ph = .idle
  · have hin : HasInput (α ++ [.inv q o]) o :=
      ⟨q, by simp [inputs, opsOf_append, (hI.idle q hph).1, Label.invOf]; rfl⟩
    have hl : ∀ r, C'.loc r = if r = q then ⟨.promote o, (C.loc q).mine⟩ else C.loc r := by
      intro r; rw [hloc, invoke_idle hph]; simp [Function.update_apply]
    have hmine : (fun r => (C'.loc r).mine) = fun r => (C.loc r).mine := by
      funext r; rw [hl]; split_ifs with hr <;> simp [hr]
    refine ⟨by rw [hmine, hmem]; exact hI.sim, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      rw [hl] at hr; split_ifs at hr with hrq
      exact ⟨by rw [hops r hrq]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
    · intro r w hr
      rw [hl] at hr; split_ifs at hr with hrq
      · simp only [RacingPhase.promote.injEq, or_false] at hr; subst hr; exact hin
      · exact (hI.ph_val r w hr).append _
    · intro u hu; rw [hctr] at hu; exact (hI.cnt_val u hu).append _
    · intro r hr
      rw [hl] at hr; split_ifs at hr with hrq
      rw [hctr]; exact hI.scan_pos r hr
    · intro r w hr
      rw [hresp] at hr
      have := hI.resp r w hr
      rw [hl]; split_ifs with hrq
      · subst hrq; rw [hph] at this; simp at this
      · exact this
    · rcases hI.agree with hA | ⟨v, hv, hlt⟩
      · left; intro r w hr
        rw [hl] at hr; split_ifs at hr with hrq
        exact hA r w hr
      · right; refine ⟨v, fun r w hr => ?_, fun u hu => ?_⟩
        · rw [hl] at hr; split_ifs at hr with hrq
          exact hv r w hr
        · have := hlt u hu
          have hb : (bad S C' v).card ≤ (bad S C v).card := card_bad_le fun r hr => by
            rw [hl] at hr; split_ifs at hr with hrq
            · subst hrq; rw [hph]; rfl
            · exact hr
          rw [hctr]; omega
  · have hl : C'.loc = C.loc := by rw [hloc, invoke_ne_idle hph]; simp
    refine ⟨by rw [hl, hmem]; exact hI.sim, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      rw [hl] at hr
      have hrq : r ≠ q := by rintro rfl; exact hph hr
      exact ⟨by rw [hops r hrq]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
    · intro r w hr; rw [hl] at hr; exact (hI.ph_val r w hr).append _
    · intro u hu; rw [hctr] at hu; exact (hI.cnt_val u hu).append _
    · intro r hr; rw [hl] at hr; rw [hctr]; exact hI.scan_pos r hr
    · intro r w hr; rw [hresp] at hr; rw [hl]; exact hI.resp r w hr
    · have hb : ∀ v, bad S C' v = bad S C v := by intro v; simp [bad, hl]
      simp only [hl, hb, hctr]; exact hI.agree

omit [NeZero m] [Fintype P] in
lemma respsOf_ret_single {A : ObjSpec} (q p : P) (r : A.Resp) :
    respsOf [(Label.ret q r : Label P A)] p = if q = p then [r] else [] := by
  by_cases h : q = p <;> simp [respsOf, h]

lemma RInv.step_ret {α : List (Label P (taskObj (Fin m) (Fin m)))} {C C' : RacingCfg S} {q : P} {o : (taskObj (Fin m) (Fin m)).Resp}
    (hI : RInv S α C) (h : (racing S n).step C (.ret q o) = some C') :
    RInv S (α ++ [.ret q o]) C' := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have hctr : ctr S C' = ctr S C := by simp [ctr, hmem]
  have hops : ∀ r, opsOf (α ++ [.ret q o]) r = opsOf α r := by simp [opsOf, Label.invOf]
  have hin : ∀ w, HasInput (α ++ [.ret q o]) w ↔ HasInput α w := by
    intro w; simp only [HasInput, inputs, hops]
  rcases hph : (C.loc q).ph with _ | w | _ | w
  · exact absurd (hI.idle q hph).2 h0
  · rw [act_promote hph] at hact; cases hact
  · rw [act_scan hph] at hact; cases hact
  rw [act_done hph] at hact
  injection hact with h1 h2
  subst h2; subst w
  have hl : C'.loc = C.loc := by rw [hloc]; simp
  have hpend' : ∀ r, r ≠ q → C'.pend r = C.pend r := by
    intro r hr; simp [hpend, Function.update_of_ne hr]
  refine ⟨by rw [hl, hmem]; exact hI.sim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hl] at hr
    have hrq : r ≠ q := by rintro rfl; rw [hph] at hr; simp at hr
    exact ⟨by rw [hops r]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
  · intro r w hr; rw [hl] at hr; exact (hin w).2 (hI.ph_val r w hr)
  · intro u hu; rw [hctr] at hu; exact (hin u).2 (hI.cnt_val u hu)
  · intro r hr; rw [hl] at hr; rw [hctr]; exact hI.scan_pos r hr
  · intro r w' hr
    rw [hl]
    rw [respsOf_append, respsOf_ret_single] at hr
    rcases List.mem_append.1 hr with hr1 | hr1
    · exact hI.resp r w' hr1
    · split_ifs at hr1 with hrq
      · subst hrq; rw [hph, List.mem_singleton.1 hr1]
      · exact absurd hr1 List.not_mem_nil
  · have hb : ∀ v, bad S C' v = bad S C v := by intro v; simp [bad, hl]
    simp only [hl, hb, hctr]; exact hI.agree

omit [Fintype P] in
lemma afterScan_ph (l : RacingLoc m) (c : Fin m → ℕ) :
    (afterScan n l c).ph = if Lead n c (argmax c) then .done (argmax c) else .promote (argmax c) := by
  unfold afterScan; split_ifs <;> rfl

omit [Fintype P] in
@[simp] lemma afterScan_mine (l : RacingLoc m) (c : Fin m → ℕ) : (afterScan n l c).mine = l.mine := by
  unfold afterScan; split_ifs <;> rfl

lemma card_bad_lt {C C' : RacingCfg S} {v : Fin m} {q : P} (hq : badB v (C.loc q).ph = true)
    (hq' : badB v (C'.loc q).ph = false)
    (h : ∀ r, r ≠ q → badB v (C'.loc r).ph = true → badB v (C.loc r).ph = true) :
    (bad S C' v).card + 1 ≤ (bad S C v).card := by
  have hsub : bad S C' v ⊆ (bad S C v).erase q := by
    intro r hr
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hr ⊢
    have hrq : r ≠ q := by rintro rfl; rw [hq'] at hr; simp at hr
    exact ⟨hrq, h r hrq hr⟩
  have hqm : q ∈ bad S C v := by simp [bad, hq]
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hqm] at this
  have : 0 < (bad S C v).card := Finset.card_pos.2 ⟨q, hqm⟩
  omega

lemma RInv.step_tau (hn : Fintype.card P ≤ n) {α : List (Label P (taskObj (Fin m) (Fin m)))}
    {C C' : RacingCfg S} {q : P} (hI : RInv S α C) (h : (racing S n).step C (.tau q) = some C') :
    RInv S (α ++ [.tau q]) C' := by
  have hp : C.pend q ≠ none := (Impl.step_tau h).1
  have hops : ∀ r, opsOf (α ++ [.tau q]) r = opsOf α r := by simp [opsOf, Label.invOf]
  have hresps : ∀ r, respsOf (α ++ [.tau q]) r = respsOf α r := by simp [respsOf, Label.retOf]
  have hin : ∀ w, HasInput (α ++ [.tau q]) w ↔ HasInput α w := by
    intro w; simp only [HasInput, inputs, hops]
  rcases hph : (C.loc q).ph with _ | w | _ | w
  · exact absurd (hI.idle q hph).2 hp
  · -- promote `w`: increment `c_w`
    rw [step_tau_promote hp hph] at h
    cases h
    set C' : RacingCfg S := ⟨Function.update C.loc q
        ⟨.scan, Function.update (C.loc q).mine w ((C.loc q).mine w + 1)⟩, C.pend,
        fun _ => (S.B.δ (C.mem ()) (S.incOp q w ((C.loc q).mine w))).1⟩ with hC'
    have hl : ∀ r, C'.loc r = if r = q then
        ⟨.scan, Function.update (C.loc q).mine w ((C.loc q).mine w + 1)⟩ else C.loc r := by
      intro r; simp [hC', Function.update_apply]
    have hctr : ctr S C' = Function.update (ctr S C) w (ctr S C w + 1) :=
      S.cnt_inc (C.mem ()) (fun r => (C.loc r).mine) q w hI.sim
    have hctr_ne : ∀ u, u ≠ w → ctr S C' u = ctr S C u := by
      intro u hu; rw [hctr, Function.update_of_ne hu]
    have hctr_w : ctr S C' w = ctr S C w + 1 := by rw [hctr]; simp
    have hctr_le : ∀ u, ctr S C u ≤ ctr S C' u := by
      intro u; by_cases hu : u = w
      · subst hu; omega
      · rw [hctr_ne u hu]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert S.inv_inc (C.mem ()) (fun r => (C.loc r).mine) q w hI.sim using 1
      funext r; rw [hl]; split_ifs with hr
      · subst hr; simp
      · simp [Function.update_of_ne hr]
    · intro r hr
      rw [hl] at hr; split_ifs at hr with hrq
      exact ⟨by rw [hops]; exact (hI.idle r hr).1, (hI.idle r hr).2⟩
    · intro r v hr
      rw [hl] at hr; split_ifs at hr with hrq
      · simp at hr
      · exact (hin v).2 (hI.ph_val r v hr)
    · intro u hu
      refine (hin u).2 ?_
      by_cases huw : u = w
      · subst huw; exact hI.ph_val q u (Or.inl hph)
      · rw [hctr_ne u huw] at hu; exact hI.cnt_val u hu
    · intro r hr
      rw [hl] at hr; split_ifs at hr with hrq
      · exact ⟨w, by omega⟩
      · obtain ⟨u, hu⟩ := hI.scan_pos r hr; exact ⟨u, by have := hctr_le u; omega⟩
    · intro r v hr
      rw [hresps] at hr
      have := hI.resp r v hr
      rw [hl]; split_ifs with hrq
      · subst hrq; rw [hph] at this; simp at this
      · exact this
    · rcases hI.agree with hA | ⟨v, hv, hlt⟩
      · left; intro r v hr
        rw [hl] at hr; split_ifs at hr with hrq
        exact hA r v hr
      · right; refine ⟨v, fun r v' hr => ?_, fun u hu => ?_⟩
        · rw [hl] at hr; split_ifs at hr with hrq
          exact hv r v' hr
        · have hrest : ∀ r, r ≠ q → badB v (C'.loc r).ph = true → badB v (C.loc r).ph = true := by
            intro r hrq hr; simp only [hl, hrq, ↓reduceIte] at hr; exact hr
          have hq' : badB v (C'.loc q).ph = false := by simp only [hl, ↓reduceIte]; rfl
          by_cases hwv : w = v
          · subst hwv
            have hb : (bad S C' w).card ≤ (bad S C w).card := card_bad_le fun r hr => by
              by_cases hrq : r = q
              · subst hrq; rw [hq'] at hr; simp at hr
              · exact hrest r hrq hr
            have := hlt u hu
            rw [hctr_ne u hu, hctr_w]; omega
          · have hb := card_bad_lt (S := S) (C := C) (C' := C') (v := v) (q := q)
              (by rw [hph]; simp [badB, hwv]) hq' hrest
            have hv' : ctr S C' v = ctr S C v := hctr_ne v (Ne.symm hwv)
            by_cases huw : u = w
            · subst huw; have := hlt u hu; rw [hctr_w, hv']; omega
            · have := hlt u hu; rw [hctr_ne u huw, hv']; omega
  · -- scan
    rw [step_tau_scan hp hph] at h
    cases h
    have hmem : (fun _ : Unit => (S.B.δ (C.mem ()) S.scanOp).1) = C.mem := by
      funext i; cases i; exact S.scan_state _
    have hdec : S.decode (S.B.δ (C.mem ()) S.scanOp).2 = ctr S C := S.scan_resp _ _ hI.sim
    rw [hdec, hmem]
    set c := ctr S C with hc
    set a := argmax c with ha
    set C' : RacingCfg S := ⟨Function.update C.loc q (afterScan n (C.loc q) c), C.pend, C.mem⟩ with hC'
    have hctr : ctr S C' = c := rfl
    have hl : ∀ r, C'.loc r = if r = q then afterScan n (C.loc q) c else C.loc r := by
      intro r; simp [hC', Function.update_apply]
    have hqa : HasInput α a := hI.cnt_val a (ctr_pos_argmax (hI.scan_pos q hph))
    have hqph : (C'.loc q).ph = if Lead n c a then .done a else .promote a := by
      simp only [hl, ↓reduceIte, afterScan_ph]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert hI.sim using 1
      funext r; rw [hl]; split_ifs with hr
      · subst hr; simp
      · rfl
    · intro r hr
      by_cases hrq : r = q
      · subst hrq; rw [hqph] at hr; split_ifs at hr
      · simp only [hl, hrq, ↓reduceIte] at hr
        exact ⟨by rw [hops]; exact (hI.idle r hr).1, (hI.idle r hr).2⟩
    · intro r v hr
      refine (hin v).2 ?_
      by_cases hrq : r = q
      · subst hrq; rw [hqph] at hr
        split_ifs at hr <;> simp at hr <;> rw [← hr] <;> exact hqa
      · simp only [hl, hrq, ↓reduceIte] at hr; exact hI.ph_val r v hr
    · intro u hu; exact (hin u).2 (hI.cnt_val u hu)
    · intro r hr
      by_cases hrq : r = q
      · subst hrq; rw [hqph] at hr; split_ifs at hr
      · simp only [hl, hrq, ↓reduceIte] at hr; exact hI.scan_pos r hr
    · intro r v hr
      rw [hresps] at hr
      have := hI.resp r v hr
      by_cases hrq : r = q
      · subst hrq; rw [hph] at this; simp at this
      · simp only [hl, hrq, ↓reduceIte]; exact this
    · have hdone : ∀ r v, (C'.loc r).ph = .done v → r = q ∧ v = a ∨ r ≠ q ∧ (C.loc r).ph = .done v := by
        intro r v hr
        by_cases hrq : r = q
        · subst hrq; rw [hqph] at hr; left
          split_ifs at hr
          simp only [RacingPhase.done.injEq] at hr; exact ⟨rfl, hr.symm⟩
        · right; simp only [hl, hrq, ↓reduceIte] at hr; exact ⟨hrq, hr⟩
      rcases hI.agree with hA | ⟨v, hv, hlt⟩
      · by_cases hL : Lead n c a
        · right; refine ⟨a, fun r v hr => ?_, fun u hu => ?_⟩
          · rcases hdone r v hr with ⟨-, h1⟩ | ⟨-, h1⟩
            · exact h1
            · exact absurd h1 (hA r v)
          · have hqn : q ∉ bad S C' a := by
              simp [bad, hqph, hL, badB]
            have h1 := Finset.card_lt_univ_of_notMem hqn
            have h2 := hL u hu
            rw [hctr]; omega
        · left; intro r v hr
          rcases hdone r v hr with ⟨rfl, -⟩ | ⟨-, h1⟩
          · simp only [hqph, hL, ↓reduceIte] at hr; simp at hr
          · exact hA r v h1
      · have hav : a = v := argmax_eq fun u hu => by have := hlt u hu; rw [← hc] at this; omega
        right; refine ⟨v, fun r v' hr => ?_, fun u hu => ?_⟩
        · rcases hdone r v' hr with ⟨-, h1⟩ | ⟨-, h1⟩
          · rw [h1, hav]
          · exact hv r v' h1
        · have hb : (bad S C' v).card ≤ (bad S C v).card := card_bad_le fun r hr => by
            by_cases hrq : r = q
            · subst hrq; rw [hqph, hav] at hr; split_ifs at hr <;> simp [badB] at hr
            · simp only [hl, hrq, ↓reduceIte] at hr; exact hr
          have := hlt u hu
          rw [hctr, hc]; omega
  · obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
    rw [act_done hph] at hact; cases hact

/-- The safety invariant holds in every reachable configuration (if `|P| ≤ n`). -/
theorem rInv_run (hn : Fintype.card P ≤ n) {α : List (Label P (taskObj (Fin m) (Fin m)))}
    {C : RacingCfg S} (h : (racing S n).run α = some C) : RInv S α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [Impl.run_nil, Option.some.injEq] at h; subst h; exact rInv_init
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (racing S n).runFrom (racing S n).initCfg α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      have hI := ih hα
      cases ℓ with
      | inv q o => exact hI.step_inv h
      | ret q o => exact hI.step_ret h
      | tau q => exact hI.step_tau hn h

/-- Agreement and validity hold in *every* finite execution of the racing-counters algorithm
(one-shot or not), provided `|P| ≤ n`. -/
theorem racing_safe (hn : Fintype.card P ≤ n) (α : List (Label P (taskObj (Fin m) (Fin m))))
    (hα : (racing S n).Valid α) : (consensus P (Fin m)).Δ (inputs α) (outputs α) := by
  obtain ⟨C, hC⟩ := hα
  have hI := rInv_run hn hC
  have hout : ∀ q (w : (taskObj (Fin m) (Fin m)).Resp), outputs α q = some w →
      (C.loc q).ph = .done w :=
    fun q w h => hI.resp q w (List.mem_of_head? h)
  refine ⟨fun p q x y hx hy => ?_, fun p y hy => hI.ph_val p y (Or.inr (hout p y hy))⟩
  rcases hI.agree with hA | ⟨v, hv, -⟩
  · exact absurd (hout p x hx) (hA p x)
  · rw [hv p x (hout p x hx), hv q y (hout q y hy)]

/-- The racing-counters algorithm solves consensus (agreement + validity), if `|P| ≤ n`. -/
theorem racing_solves (hn : Fintype.card P ≤ n) :
    (racing S n).Solves (consensus P (Fin m)) :=
  fun α hα _ => racing_safe hn α hα

/-! ### Obstruction-freedom -/

omit [Fintype P] in
lemma reachable_soloStep {C : RacingCfg S} (h : (racing S n).Reachable C) (p : P) :
    (racing S n).Reachable ((racing S n).soloStep p C) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α ++ (racing S n).soloLabels p C 1, by
    rw [Impl.run_append_of_eq _ hα, Impl.runFrom_soloLabels]; rfl⟩

omit [Fintype P] in
lemma soloStep_eq {C C' : RacingCfg S} {p : P} (hp : C.pend p ≠ none)
    (h : (racing S n).step C ((racing S n).nextLabel C p) = some C') :
    (racing S n).soloStep p C = C' := by
  simp [Impl.soloStep, hp, h]

omit [Fintype P] in
/-- A solo step of a process about to promote `w`. -/
lemma solo_promote {C : RacingCfg S} {p : P} {w : Fin m} (hp : C.pend p ≠ none)
    (hph : (C.loc p).ph = .promote w) (hsim : S.Inv (C.mem ()) (fun r => (C.loc r).mine)) :
    ((racing S n).soloStep p C).pend p ≠ none ∧ (((racing S n).soloStep p C).loc p).ph = .scan ∧
      ctr S ((racing S n).soloStep p C) = Function.update (ctr S C) w (ctr S C w + 1) := by
  have hnl : (racing S n).nextLabel C p = .tau p := by simp [Impl.nextLabel, act_promote hph]
  rw [soloStep_eq hp (by rw [hnl]; exact step_tau_promote hp hph)]
  exact ⟨hp, by simp, S.cnt_inc (C.mem ()) (fun r => (C.loc r).mine) p w hsim⟩

omit [Fintype P] in
/-- A solo step of a process about to scan. -/
lemma solo_scan {C : RacingCfg S} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .scan)
    (hsim : S.Inv (C.mem ()) (fun r => (C.loc r).mine)) :
    ((racing S n).soloStep p C).pend p ≠ none ∧
      (((racing S n).soloStep p C).loc p).ph = (if Lead n (ctr S C) (argmax (ctr S C))
        then .done (argmax (ctr S C)) else .promote (argmax (ctr S C))) ∧
      ctr S ((racing S n).soloStep p C) = ctr S C := by
  have hnl : (racing S n).nextLabel C p = .tau p := by simp [Impl.nextLabel, act_scan hph]
  rw [soloStep_eq hp (by rw [hnl]; exact step_tau_scan hp hph)]
  refine ⟨hp, ?_, congrArg S.cnt (S.scan_state _)⟩
  simp only [Function.update_self, afterScan_ph]
  rw [S.scan_resp _ _ hsim]; rfl

omit [Fintype P] in
/-- A solo step of a process that has decided. -/
lemma solo_done {C : RacingCfg S} {p : P} {w : Fin m} (hp : C.pend p ≠ none)
    (hph : (C.loc p).ph = .done w) : ((racing S n).soloStep p C).pend p = none := by
  have hnl : (racing S n).nextLabel C p = .ret p w := by simp [Impl.nextLabel, act_done hph]
  have hs : (racing S n).step C (.ret p w) =
      some { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p (C.loc p) } := by
    simp [Impl.step, hp, act_done hph]; rfl
  rw [soloStep_eq hp (by rw [hnl]; exact hs)]
  simp

/-- Running solo from a configuration where `p` is about to promote a value `w` that leads by
`k`, with `n ≤ k + j`, `p` returns. -/
lemma solo_lead (hn : Fintype.card P ≤ n) (p : P) (j : ℕ) :
    ∀ (C : RacingCfg S) (k : ℕ) (w : Fin m), (racing S n).Reachable C → C.pend p ≠ none →
      (C.loc p).ph = .promote w → Lead k (ctr S C) w → n ≤ k + j →
      ∃ t, (((racing S n).soloStep p)^[t] C).pend p = none := by
  induction j with
  | zero =>
    intro C k w hR hp hph hL hk
    obtain ⟨α, hα⟩ := hR
    obtain ⟨hp1, hph1, hc1⟩ := solo_promote (n := n) hp hph (rInv_run hn hα).sim
    have hR1 := reachable_soloStep (n := n) ⟨α, hα⟩ p
    obtain ⟨α1, hα1⟩ := hR1
    obtain ⟨hp2, hph2, -⟩ := solo_scan (n := n) hp1 hph1 (rInv_run hn hα1).sim
    have hL1 : Lead (k + 1) (ctr S ((racing S n).soloStep p C)) w := by rw [hc1]; exact hL.inc
    rw [hL1.argmax_eq] at hph2
    split_ifs at hph2 with hLn
    · exact ⟨3, solo_done hp2 hph2⟩
    · exact absurd (hL1.mono (by omega)) hLn
  | succ j ih =>
    intro C k w hR hp hph hL hk
    obtain ⟨α, hα⟩ := hR
    obtain ⟨hp1, hph1, hc1⟩ := solo_promote (n := n) hp hph (rInv_run hn hα).sim
    have hR1 := reachable_soloStep (n := n) ⟨α, hα⟩ p
    obtain ⟨α1, hα1⟩ := hR1
    obtain ⟨hp2, hph2, hc2⟩ := solo_scan (n := n) hp1 hph1 (rInv_run hn hα1).sim
    have hL1 : Lead (k + 1) (ctr S ((racing S n).soloStep p C)) w := by rw [hc1]; exact hL.inc
    rw [hL1.argmax_eq] at hph2
    split_ifs at hph2 with hLn
    · exact ⟨3, solo_done hp2 hph2⟩
    · obtain ⟨t, ht⟩ := ih _ (k + 1) w (reachable_soloStep ⟨α1, hα1⟩ p) hp2 hph2
        (by rw [hc2]; exact hL1) (by omega)
      exact ⟨t + 2, by rw [Function.iterate_add_apply]; exact ht⟩

/-- Running solo from a configuration where `p` is about to scan, `p` returns. -/
lemma solo_from_scan (hn : Fintype.card P ≤ n) {C : RacingCfg S} {p : P} (hR : (racing S n).Reachable C)
    (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .scan) :
    ∃ t, (((racing S n).soloStep p)^[t] C).pend p = none := by
  obtain ⟨α, hα⟩ := hR
  obtain ⟨hp1, hph1, hc1⟩ := solo_scan (n := n) hp hph (rInv_run hn hα).sim
  split_ifs at hph1 with hLn
  · exact ⟨2, solo_done hp1 hph1⟩
  · obtain ⟨t, ht⟩ := solo_lead hn p n _ 0 _ (reachable_soloStep ⟨α, hα⟩ p) hp1 hph1
      (by rw [hc1]; exact lead_zero_argmax _) (by omega)
    exact ⟨t + 1, by rw [Function.iterate_add_apply]; exact ht⟩

/-- The racing-counters algorithm is obstruction-free (if `|P| ≤ n`). -/
theorem racing_obstructionFree (hn : Fintype.card P ≤ n) : (racing S n).ObstructionFree := by
  intro C p hR hp
  obtain ⟨α, hα⟩ := hR
  have hI := rInv_run hn hα
  rcases hph : (C.loc p).ph with _ | w | _ | w
  · exact absurd (hI.idle p hph).2 hp
  · obtain ⟨hp1, hph1, -⟩ := solo_promote (n := n) hp hph hI.sim
    obtain ⟨t, ht⟩ := solo_from_scan hn (reachable_soloStep ⟨α, hα⟩ p) hp1 hph1
    exact ⟨t + 1, by rw [Function.iterate_add_apply]; exact ht⟩
  · exact solo_from_scan hn ⟨α, hα⟩ hp hph
  · exact ⟨1, solo_done hp hph⟩

/-! ### Lemma 3.1 -/

/-- Lemma 3.1 of [EGSZ16]: obstruction-free `m`-valued consensus among the processes `P` can be
solved using one `m`-component unbounded counter (initially all `0`), with decision threshold
`n = |P|`. Agreement and validity hold in every execution (`racing_safe`); obstruction-freedom is
CSLib's `Impl.ObstructionFree` (from every reachable configuration). -/
theorem lemma_3_1 (m : ℕ) [NeZero m] (P : Type) [DecidableEq P] [Fintype P] :
    ∃ (L : Type) (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Unit => counterObj m) P L),
      I.memInit () = 0 ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus P (Fin m)) ∧
        I.ObstructionFree :=
  ⟨RacingLoc m, racing (counterSim m P) (Fintype.card P), rfl, fun _ _ => trivial,
    racing_solves le_rfl, racing_obstructionFree le_rfl⟩

end Cslib.SharedMemory.ComplexityHierarchy
