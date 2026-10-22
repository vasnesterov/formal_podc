/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Podc.Computability.Distributed.SWMR.Basic
import Mathlib

/-!
# Lemma 2.2: wait-free binary `1/k`-agreement with unbounded registers

The classical fact (Lemma 2.2 of the paper) that binary `1/k`-agreement is wait-free solvable by
any number of processes in the read/write model with unbounded single-writer registers.

## Algorithm (iterated collect-midpoint)

Every process `p` keeps a current value `v` (initially its input `0` or `1`) and runs `R` rounds.
In round `r` it writes the list of its round values `[v₀, …, v_r]` to its register, then reads
the registers of all processes (in the order of a fixed list `L`), taking the `r`-th entry of
every list long enough; `lo`/`hi` are the minimum/maximum of the values taken (initialised to
`v_r`). Then `v_{r+1} := (lo + hi) / 2`. After `R` rounds it decides `⌊k · v_R⌋₊` and then does
no-op reads forever.

Any two processes finishing round `r` took a common value (whichever wrote first is read by the
other), so the spread of the round values halves every round; with `R = k` the final values are
`1/2^k ≤ 1/k` apart.

The local state also records ghost information (all round values, all ranges, and the results
of all reads), which is harmless since local states are unbounded in this model.
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

/-- Local state of the collect-midpoint algorithm. -/
structure AAState (P : Type) where
  /-- Current round. -/
  r : ℕ
  /-- Whether the write of the current round has been done. -/
  wrote : Bool
  /-- Processes still to be read in the current round. -/
  todo : List P
  /-- `val i` is the value of round `i` (for `i ≤ r`). -/
  val : ℕ → ℚ
  /-- `lo i` is the minimum of the values collected in round `i` (and `val i`). -/
  lo : ℕ → ℚ
  /-- `hi i` is the maximum of the values collected in round `i` (and `val i`). -/
  hi : ℕ → ℚ
  /-- `seen i q`: result of the round-`i` read of `q` (`none` = not read yet). -/
  seen : ℕ → P → Option (Option ℚ)
  /-- Whether the process has decided. -/
  done : Bool

variable {P : Type} [DecidableEq P]

namespace AAState

/-- Number of rounds whose value has been written. -/
def wc (s : AAState P) : ℕ := if s.wrote then s.r + 1 else s.r

/-- Minimum with an optional value. -/
def minO (a : ℚ) : Option ℚ → ℚ
  | none => a
  | some e => min a e

/-- Maximum with an optional value. -/
def maxO (a : ℚ) : Option ℚ → ℚ
  | none => a
  | some e => max a e

/-- The initial state with input `b`. -/
def init (L : List P) (b : Bool) : AAState P where
  r := 0
  wrote := false
  todo := L
  val := fun _ => if b then 1 else 0
  lo := fun _ => if b then 1 else 0
  hi := fun _ => if b then 1 else 0
  seen := fun _ _ => none
  done := false

/-- End of a round: compute the midpoint and start the next round. -/
def advance (L : List P) (s : AAState P) : AAState P :=
  let v := (s.lo s.r + s.hi s.r) / 2
  { s with r := s.r + 1, wrote := false, todo := L, val := Function.update s.val (s.r + 1) v,
           lo := Function.update s.lo (s.r + 1) v, hi := Function.update s.hi (s.r + 1) v }

/-- Record the result `o` of reading the register of `q`. -/
def record (s : AAState P) (q : P) (t : List P) (o : Option ℚ) : AAState P :=
  { s with todo := t,
           seen := Function.update s.seen s.r (Function.update (s.seen s.r) q (some o)),
           lo := Function.update s.lo s.r (minO (s.lo s.r) o),
           hi := Function.update s.hi s.r (maxO (s.hi s.r) o) }

/-- The next step of the collect-midpoint algorithm with `R` rounds, output scale `k`, and
reading order `L`. -/
def next (R k : ℕ) (L : List P) (p : P) (s : AAState P) :
    Act P Unit (fun _ => List ℚ) ℕ (AAState P) :=
  if s.done then .read p () (fun _ => s)
  else if s.r = R then .decide ⌊(k : ℚ) * s.val R⌋₊ { s with done := true }
  else if s.wrote then
    match s.todo with
    | [] => .read p () (fun _ => advance L s)
    | q :: t => .read q () (fun l => record s q t l[s.r]?)
  else .write () ((List.range (s.r + 1)).map s.val) { s with wrote := true }

end AAState

/-- The iterated collect-midpoint algorithm with `R` rounds, output scale `k` and reading
order `L`. -/
def aaAlg (R k : ℕ) (L : List P) : Alg P Unit (fun _ => List ℚ) Bool ℕ where
  S := AAState P
  v₀ := fun _ => []
  init := fun _ b => AAState.init L b
  next := AAState.next R k L

section Steps

variable {R k : ℕ} {L : List P}

/-- The local state of `p` in a configuration of the collect-midpoint algorithm. -/
abbrev st (C : Config (aaAlg R k L)) (p : P) : AAState P := C.loc p

lemma step_done (C : Config (aaAlg R k L)) (p : P) (h : (st C p).done = true) :
    (aaAlg R k L).step p C = C := by
  simp [Alg.step, aaAlg, AAState.next, h]
  rfl

lemma step_decide (C : Config (aaAlg R k L)) (p : P) (h : (st C p).done = false)
    (hr : (st C p).r = R) :
    (aaAlg R k L).step p C = { C with
      loc := Function.update C.loc p ({ st C p with done := true } : AAState P),
      out := Function.update C.out p ((C.out p).or (some ⌊(k : ℚ) * (st C p).val R⌋₊)) } := by
  simp [Alg.step, aaAlg, AAState.next, h, hr]

lemma step_write (C : Config (aaAlg R k L)) (p : P) (h : (st C p).done = false)
    (hr : (st C p).r ≠ R) (hw : (st C p).wrote = false) :
    (aaAlg R k L).step p C = { C with
      loc := Function.update C.loc p ({ st C p with wrote := true } : AAState P),
      mem := Function.update C.mem p
        (Function.update (C.mem p) () ((List.range ((st C p).r + 1)).map (st C p).val)) } := by
  simp [Alg.step, aaAlg, AAState.next, h, hr, hw]

lemma step_advance (C : Config (aaAlg R k L)) (p : P) (h : (st C p).done = false)
    (hr : (st C p).r ≠ R) (hw : (st C p).wrote = true) (ht : (st C p).todo = []) :
    (aaAlg R k L).step p C = { C with
      loc := Function.update C.loc p (AAState.advance L (st C p)) } := by
  simp [Alg.step, aaAlg, AAState.next, h, hr, hw, ht]

lemma step_read (C : Config (aaAlg R k L)) (p : P) (h : (st C p).done = false)
    (hr : (st C p).r ≠ R) (hw : (st C p).wrote = true) {q : P} {t : List P}
    (ht : (st C p).todo = q :: t) :
    (aaAlg R k L).step p C = { C with
      loc := Function.update C.loc p
        (AAState.record (st C p) q t (C.mem q ())[(st C p).r]?) } := by
  simp [Alg.step, aaAlg, AAState.next, h, hr, hw, ht]

end Steps

/-! ### The invariant -/

section Invariant

variable {R k : ℕ} {L : List P} {a b : ℚ}

/-- The inductive invariant of the collect-midpoint algorithm (all inputs in `[a, b]`). -/
structure Inv (R k : ℕ) (L : List P) (a b : ℚ) (C : Config (aaAlg R k L)) : Prop where
  wc_le : ∀ p, (st C p).wc ≤ R
  todo_eq : ∀ p, (st C p).wrote = false → (st C p).todo = L
  todo_suffix : ∀ p, (st C p).todo <:+ L
  seen_lt : ∀ p i q, (st C p).seen i q ≠ none → i < (st C p).wc
  seen_old : ∀ p i q, i < (st C p).r → (st C p).seen i q ≠ none
  seen_cur : ∀ p q, (st C p).wrote = true → q ∉ (st C p).todo →
    (st C p).seen (st C p).r q ≠ none
  mem_eq : ∀ p i, (C.mem p ())[i]? = if i < (st C p).wc then some ((st C p).val i) else none
  lo_le : ∀ p i, i ≤ (st C p).r → (st C p).lo i ≤ (st C p).val i ∧ (st C p).val i ≤ (st C p).hi i
  val_succ : ∀ p i, i < (st C p).r → (st C p).val (i + 1) = ((st C p).lo i + (st C p).hi i) / 2
  lo_wit : ∀ p i, i ≤ (st C p).r → ∃ q, i ≤ (st C q).r ∧ (st C p).lo i = (st C q).val i
  hi_wit : ∀ p i, i ≤ (st C p).r → ∃ q, i ≤ (st C q).r ∧ (st C p).hi i = (st C q).val i
  seen_val : ∀ p i q e, (st C p).seen i q = some (some e) →
    i ≤ (st C q).r ∧ e = (st C q).val i ∧ (st C p).lo i ≤ e ∧ e ≤ (st C p).hi i
  range : ∀ p i, i ≤ (st C p).r → a ≤ (st C p).val i ∧ (st C p).val i ≤ b
  out_some : ∀ p, (C.out p).isSome = (st C p).done
  done_r : ∀ p, (st C p).done = true → (st C p).r = R
  out_val : ∀ p m, C.out p = some m → m = ⌊(k : ℚ) * (st C p).val R⌋₊
  dist : ∀ p q i, i ≤ (st C p).r → i ≤ (st C q).r →
    |(st C p).val i - (st C q).val i| ≤ 1 / 2 ^ i
  cross : ∀ p q i, (st C p).seen i q = some none → i < (st C q).wc →
    (st C q).seen i p ≠ some none

lemma inv_init (x : P → Bool) (hab : ∀ p, a ≤ (if x p then 1 else 0 : ℚ) ∧
    (if x p then 1 else 0 : ℚ) ≤ b) :
    Inv R k L a b ((aaAlg R k L).initCfg x) where
  wc_le p := by simp [st, Alg.initCfg, aaAlg, AAState.init, AAState.wc]
  todo_eq p _ := rfl
  todo_suffix p := List.suffix_refl L
  seen_lt p i q h := by simp [st, Alg.initCfg, aaAlg, AAState.init] at h
  seen_old p i q h := by simp [st, Alg.initCfg, aaAlg, AAState.init] at h
  seen_cur p q h := by simp [st, Alg.initCfg, aaAlg, AAState.init] at h
  mem_eq p i := by simp [st, Alg.initCfg, aaAlg, AAState.init, AAState.wc]
  lo_le p i _ := by simp [st, Alg.initCfg, aaAlg, AAState.init]
  val_succ p i h := by simp [st, Alg.initCfg, aaAlg, AAState.init] at h
  lo_wit p i _ := ⟨p, by simp_all [st, Alg.initCfg, aaAlg, AAState.init]⟩
  hi_wit p i _ := ⟨p, by simp_all [st, Alg.initCfg, aaAlg, AAState.init]⟩
  seen_val p i q e h := by simp [st, Alg.initCfg, aaAlg, AAState.init] at h
  range p i _ := hab p
  out_some p := by simp [st, Alg.initCfg, aaAlg, AAState.init]
  done_r p h := by simp [st, Alg.initCfg, aaAlg, AAState.init] at h
  out_val p m h := by simp [Alg.initCfg] at h
  dist p q i hi _ := by
    have : i = 0 := by simpa [st, Alg.initCfg, aaAlg, AAState.init] using hi
    subst this
    simp only [st, Alg.initCfg, aaAlg, AAState.init]
    cases x p <;> cases x q <;> norm_num
  cross p q i h := by simp [st, Alg.initCfg, aaAlg, AAState.init] at h

omit [DecidableEq P] in
lemma wc_eq (s : AAState P) : s.wc = if s.wrote then s.r + 1 else s.r := rfl

variable {C C' : Config (aaAlg R k L)}

/-- The decision step preserves the invariant. -/
lemma inv_decide (hI : Inv R k L a b C) {p : P} (hrR : (st C p).r = R)
    (hloc : ∀ x, st C' x = if x = p then { st C p with done := true } else st C x)
    (hmem : C'.mem = C.mem)
    (hout : ∀ x, C'.out x = if x = p then some ⌊(k : ℚ) * (st C p).val R⌋₊ else C.out x) :
    Inv R k L a b C' := by
  have hr' : ∀ x, (st C' x).r = (st C x).r := fun x => by rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hw' : ∀ x, (st C' x).wrote = (st C x).wrote := fun x => by rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have ht' : ∀ x, (st C' x).todo = (st C x).todo := fun x => by rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hv' : ∀ x, (st C' x).val = (st C x).val := fun x => by rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hlo' : ∀ x, (st C' x).lo = (st C x).lo := fun x => by rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hhi' : ∀ x, (st C' x).hi = (st C x).hi := fun x => by rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hs' : ∀ x, (st C' x).seen = (st C x).seen := fun x => by rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hwc' : ∀ x, (st C' x).wc = (st C x).wc := fun x => by simp only [wc_eq, hr', hw']
  have hd' : ∀ x, (st C' x).done = if x = p then true else (st C x).done := fun x => by
    rw [hloc]; split_ifs <;> rfl
  constructor
  all_goals try simp only [hr', hw', ht', hv', hlo', hhi', hs', hwc', hmem]
  · exact hI.wc_le
  · exact hI.todo_eq
  · exact hI.todo_suffix
  · exact hI.seen_lt
  · exact hI.seen_old
  · exact hI.seen_cur
  · exact hI.mem_eq
  · exact hI.lo_le
  · exact hI.val_succ
  · exact hI.lo_wit
  · exact hI.hi_wit
  · exact hI.seen_val
  · exact hI.range
  · intro x; rw [hout, hd']; split_ifs <;> simp [hI.out_some]
  · intro x; rw [hd']; split_ifs with hx
    · subst hx; simp [hrR]
    · exact hI.done_r x
  · intro x m; rw [hout]; split_ifs with hx
    · subst hx; intro h; simp at h; omega
    · exact hI.out_val x m
  · exact hI.dist
  · exact hI.cross

/-- The write step preserves the invariant. -/
lemma inv_write (hI : Inv R k L a b C) (hL : ∀ q, q ∈ L) {p : P} (hrR : (st C p).r ≠ R)
    (hw : (st C p).wrote = false)
    (hloc : ∀ x, st C' x = if x = p then { st C p with wrote := true } else st C x)
    (hmem : ∀ x, C'.mem x () =
      if x = p then (List.range ((st C p).r + 1)).map (st C p).val else C.mem x ())
    (hout : C'.out = C.out) :
    Inv R k L a b C' := by
  have hr' : ∀ x, (st C' x).r = (st C x).r := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have ht' : ∀ x, (st C' x).todo = (st C x).todo := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hv' : ∀ x, (st C' x).val = (st C x).val := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hlo' : ∀ x, (st C' x).lo = (st C x).lo := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hhi' : ∀ x, (st C' x).hi = (st C x).hi := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hs' : ∀ x, (st C' x).seen = (st C x).seen := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hd' : ∀ x, (st C' x).done = (st C x).done := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hw' : ∀ x, (st C' x).wrote = if x = p then true else (st C x).wrote := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have hwcp : (st C p).wc = (st C p).r := by simp [wc_eq, hw]
  have hwc' : ∀ x, (st C' x).wc = if x = p then (st C p).r + 1 else (st C x).wc := fun x => by
    by_cases hx : x = p
    · subst hx; simp [wc_eq, hw', hr']
    · simp [hx, wc_eq, hw', hr']
  constructor
  · intro x; rw [hwc']; split_ifs
    · have := hI.wc_le p; omega
    · exact hI.wc_le x
  · intro x; rw [hw', ht']; split_ifs
    · simp
    · exact hI.todo_eq x
  · intro x; rw [ht']; exact hI.todo_suffix x
  · intro x i q h; rw [hs'] at h; rw [hwc']; split_ifs with hx
    · subst hx; have := hI.seen_lt x i q h; omega
    · exact hI.seen_lt x i q h
  · intro x i q; rw [hr', hs']; exact hI.seen_old x i q
  · intro x q; rw [hw', ht', hs', hr']; split_ifs with hx
    · intro _ hq; subst hx; exact absurd (hL q) (by rwa [hI.todo_eq _ hw] at hq)
    · exact hI.seen_cur x q
  · intro x i; rw [hmem, hwc', hv']; by_cases hx : x = p
    · subst hx; simp only [↓reduceIte]; split_ifs with h1 <;> simp [h1]
    · simp only [hx, ↓reduceIte]; exact hI.mem_eq x i
  all_goals try simp only [hr', hv', hlo', hhi', hs', hd', hout]
  · exact hI.lo_le
  · exact hI.val_succ
  · exact hI.lo_wit
  · exact hI.hi_wit
  · exact hI.seen_val
  · exact hI.range
  · exact hI.out_some
  · exact hI.done_r
  · exact hI.out_val
  · exact hI.dist
  · intro x q i h hi hc
    rw [hwc'] at hi
    split_ifs at hi with hq
    · subst hq
      have := hI.seen_lt q i x (by rw [hc]; simp)
      exact hI.cross x q i h (by omega) hc
    · exact hI.cross x q i h hi hc

/-- The key step: two processes finishing round `r` have a common collected value, so their
next values are `1/2^(r+1)` apart. -/
lemma Inv.key (hI : Inv R k L a b C) {p y : P} (hw : (st C p).wrote = true)
    (htd : (st C p).todo = []) (hy : (st C p).r < (st C y).r) :
    |((st C p).lo (st C p).r + (st C p).hi (st C p).r) / 2 - (st C y).val ((st C p).r + 1)|
      ≤ 1 / 2 ^ ((st C p).r + 1) := by
  set r := (st C p).r with hr
  rw [hI.val_succ y r hy]
  obtain ⟨c, h1, h2, h3, h4⟩ : ∃ c, (st C p).lo r ≤ c ∧ c ≤ (st C p).hi r ∧
      (st C y).lo r ≤ c ∧ c ≤ (st C y).hi r := by
    have hs := hI.seen_cur p y hw (by simp [htd])
    rcases hsy : (st C p).seen r y with _ | (_ | e)
    · exact absurd hsy hs
    · have hc := hI.cross p y r hsy (by rw [wc_eq]; split_ifs <;> omega)
      have hn := hI.seen_old y r p hy
      rcases hsy' : (st C y).seen r p with _ | (_ | e)
      · exact absurd hsy' hn
      · exact absurd hsy' hc
      · obtain ⟨-, rfl, h3, h4⟩ := hI.seen_val y r p e hsy'
        obtain ⟨h1, h2⟩ := hI.lo_le p r le_rfl
        exact ⟨_, h1, h2, h3, h4⟩
    · obtain ⟨-, rfl, h1, h2⟩ := hI.seen_val p r y e hsy
      obtain ⟨h3, h4⟩ := hI.lo_le y r hy.le
      exact ⟨_, h1, h2, h3, h4⟩
  obtain ⟨w1, hw1, e1⟩ := hI.hi_wit p r le_rfl
  obtain ⟨w2, hw2, e2⟩ := hI.lo_wit y r hy.le
  obtain ⟨w3, hw3, e3⟩ := hI.hi_wit y r hy.le
  obtain ⟨w4, hw4, e4⟩ := hI.lo_wit p r le_rfl
  have d1 := hI.dist w1 w2 r hw1 hw2
  have d2 := hI.dist w3 w4 r hw3 hw4
  rw [← e1, ← e2] at d1
  rw [← e3, ← e4] at d2
  have hD : (1 : ℚ) / 2 ^ (r + 1) = (1 / 2 ^ r) / 2 := by ring
  rw [hD]
  generalize (1 : ℚ) / 2 ^ r = D at *
  rw [abs_le] at d1 d2 ⊢
  constructor <;> linarith [d1.1, d1.2, d2.1, d2.2]

/-- The end-of-round step preserves the invariant. -/
lemma inv_advance (hI : Inv R k L a b C) {p : P} (hrR : (st C p).r ≠ R)
    (hw : (st C p).wrote = true) (htd : (st C p).todo = [])
    (hloc : ∀ x, st C' x = if x = p then AAState.advance L (st C p) else st C x)
    (hmem : C'.mem = C.mem) (hout : C'.out = C.out) :
    Inv R k L a b C' := by
  have hr' : ∀ x, (st C' x).r = if x = p then (st C p).r + 1 else (st C x).r := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have hw' : ∀ x, (st C' x).wrote = if x = p then false else (st C x).wrote := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have ht' : ∀ x, (st C' x).todo = if x = p then L else (st C x).todo := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have hv' : ∀ x, (st C' x).val = if x = p then Function.update (st C p).val ((st C p).r + 1)
      (((st C p).lo (st C p).r + (st C p).hi (st C p).r) / 2) else (st C x).val := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have hlo' : ∀ x, (st C' x).lo = if x = p then Function.update (st C p).lo ((st C p).r + 1)
      (((st C p).lo (st C p).r + (st C p).hi (st C p).r) / 2) else (st C x).lo := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have hhi' : ∀ x, (st C' x).hi = if x = p then Function.update (st C p).hi ((st C p).r + 1)
      (((st C p).lo (st C p).r + (st C p).hi (st C p).r) / 2) else (st C x).hi := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have hs' : ∀ x, (st C' x).seen = (st C x).seen := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hd' : ∀ x, (st C' x).done = (st C x).done := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hwcp : (st C p).wc = (st C p).r + 1 := by simp [wc_eq, hw]
  have hwc' : ∀ x, (st C' x).wc = (st C x).wc := fun x => by
    by_cases hx : x = p
    · rw [hx, hwcp, wc_eq, hw', hr']; simp
    · simp [hx, wc_eq, hw', hr']
  have tr : ∀ q i, i ≤ (st C q).r → i ≤ (st C' q).r ∧ (st C' q).val i = (st C q).val i := by
    intro q i hi
    rw [hr', hv']
    by_cases hq : q = p
    · subst hq; simp only [↓reduceIte]
      exact ⟨by omega, Function.update_of_ne (by omega) _ _⟩
    · simp [hq, hi]
  constructor
  · intro x; rw [hwc']; exact hI.wc_le x
  · intro x hx'; rw [ht']; rw [hw'] at hx'
    split_ifs at hx' ⊢ with hx
    · rfl
    · exact hI.todo_eq x hx'
  · intro x; rw [ht']; split_ifs
    · exact List.suffix_refl L
    · exact hI.todo_suffix x
  · intro x i q h; rw [hs'] at h; rw [hwc']; exact hI.seen_lt x i q h
  · intro x i q hi; rw [hr'] at hi; rw [hs']
    split_ifs at hi with hx
    · subst hx
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact hI.seen_old _ i q h
      · rw [h]; exact hI.seen_cur _ q hw (by simp [htd])
    · exact hI.seen_old x i q hi
  · intro x q hwx; rw [hw'] at hwx
    by_cases hx : x = p
    · simp [hx] at hwx
    · simp only [hx, ↓reduceIte] at hwx
      rw [ht', hs', hr']; simp only [hx, ↓reduceIte]; exact hI.seen_cur x q hwx
  · intro x i; rw [hmem, hwc', hv', hI.mem_eq x i]
    by_cases hx : x = p
    · subst hx; simp only [↓reduceIte]
      split_ifs with h1
      · rw [Function.update_of_ne (by omega)]
      · rfl
    · simp [hx]
  · intro x i hi; rw [hr'] at hi; rw [hlo', hv', hhi']
    by_cases hx : x = p
    · subst hx; simp only [↓reduceIte] at hi ⊢
      by_cases hi' : i = (st C x).r + 1
      · rw [hi']; simp
      · simp only [Function.update_of_ne hi']; exact hI.lo_le _ i (by omega)
    · simp only [hx, ↓reduceIte] at hi ⊢; exact hI.lo_le x i hi
  · intro x i hi; rw [hr'] at hi; rw [hlo', hv', hhi']
    by_cases hx : x = p
    · subst hx; simp only [↓reduceIte] at hi ⊢
      by_cases hi' : i = (st C x).r
      · rw [hi']; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hI.val_succ _ i (by omega)
    · simp only [hx, ↓reduceIte] at hi ⊢; exact hI.val_succ x i hi
  · intro x i hi; rw [hr'] at hi; rw [hlo']
    by_cases hx : x = p
    · subst hx; simp only [↓reduceIte] at hi ⊢
      by_cases hi' : i = (st C x).r + 1
      · refine ⟨x, ?_, ?_⟩
        · rw [hr']; simp [hi']
        · rw [hv', hi']; simp
      · rw [Function.update_of_ne hi']
        obtain ⟨q, hq, e⟩ := hI.lo_wit x i (by omega)
        exact ⟨q, (tr q i hq).1, by rw [(tr q i hq).2, e]⟩
    · simp only [hx, ↓reduceIte] at hi ⊢
      obtain ⟨q, hq, e⟩ := hI.lo_wit x i hi
      exact ⟨q, (tr q i hq).1, by rw [(tr q i hq).2, e]⟩
  · intro x i hi; rw [hr'] at hi; rw [hhi']
    by_cases hx : x = p
    · subst hx; simp only [↓reduceIte] at hi ⊢
      by_cases hi' : i = (st C x).r + 1
      · refine ⟨x, ?_, ?_⟩
        · rw [hr']; simp [hi']
        · rw [hv', hi']; simp
      · rw [Function.update_of_ne hi']
        obtain ⟨q, hq, e⟩ := hI.hi_wit x i (by omega)
        exact ⟨q, (tr q i hq).1, by rw [(tr q i hq).2, e]⟩
    · simp only [hx, ↓reduceIte] at hi ⊢
      obtain ⟨q, hq, e⟩ := hI.hi_wit x i hi
      exact ⟨q, (tr q i hq).1, by rw [(tr q i hq).2, e]⟩
  · intro x i q e h
    rw [hs'] at h
    obtain ⟨h1, h2, h3, h4⟩ := hI.seen_val x i q e h
    have hlt := hI.seen_lt x i q (by simp [h])
    refine ⟨(tr q i h1).1, by rw [(tr q i h1).2, h2], ?_, ?_⟩
    · rw [hlo']; split_ifs with hx
      · subst hx; rw [Function.update_of_ne (by omega)]; exact h3
      · exact h3
    · rw [hhi']; split_ifs with hx
      · subst hx; rw [Function.update_of_ne (by omega)]; exact h4
      · exact h4
  · intro x i hi; rw [hr'] at hi; rw [hv']
    by_cases hx : x = p
    · subst hx; simp only [↓reduceIte] at hi ⊢
      by_cases hi' : i = (st C x).r + 1
      · rw [hi']; simp only [Function.update_self]
        obtain ⟨q, hq, e⟩ := hI.lo_wit x _ le_rfl
        obtain ⟨q', hq', e'⟩ := hI.hi_wit x _ le_rfl
        have r1 := hI.range q _ hq
        have r2 := hI.range q' _ hq'
        rw [e, e']
        constructor <;> linarith [r1.1, r1.2, r2.1, r2.2]
      · rw [Function.update_of_ne hi']; exact hI.range _ i (by omega)
    · simp only [hx, ↓reduceIte] at hi ⊢; exact hI.range x i hi
  · intro x; rw [hout, hd']; exact hI.out_some x
  · intro x hdx; rw [hd'] at hdx; rw [hr']
    split_ifs with hx
    · subst hx; exact absurd (hI.done_r _ hdx) hrR
    · exact hI.done_r x hdx
  · intro x m hm; rw [hout] at hm
    have hdx : (st C x).done = true := by rw [← hI.out_some x, hm]; rfl
    rw [hv']
    split_ifs with hx
    · subst hx; exact absurd (hI.done_r _ hdx) hrR
    · exact hI.out_val x m hm
  · intro x y i hx hy
    by_cases hxp : x = p <;> by_cases hyp : y = p
    · subst hxp; subst hyp; simp
    · rw [hr'] at hx hy; simp only [hxp, hyp, ↓reduceIte] at hx hy
      subst hxp
      rw [(tr y i hy).2]
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hx) with h | h
      · rw [(tr x i (by omega)).2]; exact hI.dist x y i (by omega) hy
      · rw [hv', h]; simp only [↓reduceIte, Function.update_self]
        exact hI.key hw htd (by omega)
    · rw [hr'] at hx hy; simp only [hxp, hyp, ↓reduceIte] at hx hy
      subst hyp
      rw [(tr x i hx).2, abs_sub_comm]
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hy) with h | h
      · rw [(tr y i (by omega)).2]; exact hI.dist y x i (by omega) hx
      · rw [hv', h]; simp only [↓reduceIte, Function.update_self]
        exact hI.key hw htd (by omega)
    · rw [hr'] at hx hy; simp only [hxp, hyp, ↓reduceIte] at hx hy
      rw [(tr x i hx).2, (tr y i hy).2]; exact hI.dist x y i hx hy
  · intro x q i; rw [hs', hs', hwc']; exact hI.cross x q i

omit [DecidableEq P] in
lemma minO_le (a : ℚ) (o : Option ℚ) : AAState.minO a o ≤ a := by
  cases o <;> simp [AAState.minO]

omit [DecidableEq P] in
lemma le_maxO (a : ℚ) (o : Option ℚ) : a ≤ AAState.maxO a o := by
  cases o <;> simp [AAState.maxO]

omit [DecidableEq P] in
lemma wc_le_succ (s : AAState P) : s.wc ≤ s.r + 1 := by
  rw [wc_eq]; split_ifs <;> omega

/-- The read step preserves the invariant. -/
lemma inv_read (hI : Inv R k L a b C) {p q : P} {t : List P}
    (hw : (st C p).wrote = true) (htd : (st C p).todo = q :: t)
    (hloc : ∀ x, st C' x = if x = p then
      AAState.record (st C p) q t (C.mem q ())[(st C p).r]? else st C x)
    (hmem : C'.mem = C.mem) (hout : C'.out = C.out) :
    Inv R k L a b C' := by
  have ho := hI.mem_eq q (st C p).r
  generalize (C.mem q ())[(st C p).r]? = o at hloc ho
  have hr' : ∀ x, (st C' x).r = (st C x).r := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hw' : ∀ x, (st C' x).wrote = (st C x).wrote := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hv' : ∀ x, (st C' x).val = (st C x).val := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hd' : ∀ x, (st C' x).done = (st C x).done := fun x => by
    rw [hloc]; split_ifs <;> subst_vars <;> rfl
  have hwc' : ∀ x, (st C' x).wc = (st C x).wc := fun x => by simp only [wc_eq, hr', hw']
  have ht' : ∀ x, (st C' x).todo = if x = p then t else (st C x).todo := fun x => by
    rw [hloc]; split_ifs <;> rfl
  have hs' : ∀ x i y, (st C' x).seen i y =
      if x = p ∧ i = (st C p).r ∧ y = q then some o else (st C x).seen i y := by
    intro x i y; rw [hloc]
    by_cases hx : x = p
    · subst hx
      by_cases hi : i = (st C x).r
      · subst hi
        by_cases hy : y = q
        · subst hy; simp [AAState.record]
        · simp [AAState.record, hy]
      · simp [AAState.record, hi]
    · simp [hx]
  have hlo' : ∀ x i, (st C' x).lo i = if x = p ∧ i = (st C p).r then
      AAState.minO ((st C p).lo (st C p).r) o else (st C x).lo i := by
    intro x i; rw [hloc]
    by_cases hx : x = p
    · subst hx
      by_cases hi : i = (st C x).r
      · subst hi; simp [AAState.record]
      · simp [AAState.record, hi]
    · simp [hx]
  have hhi' : ∀ x i, (st C' x).hi i = if x = p ∧ i = (st C p).r then
      AAState.maxO ((st C p).hi (st C p).r) o else (st C x).hi i := by
    intro x i; rw [hloc]
    by_cases hx : x = p
    · subst hx
      by_cases hi : i = (st C x).r
      · subst hi; simp [AAState.record]
      · simp [AAState.record, hi]
    · simp [hx]
  -- what a hit means
  have hit : ∀ e, o = some e → (st C p).r ≤ (st C q).r ∧ e = (st C q).val (st C p).r := by
    intro e he
    rw [he] at ho
    split_ifs at ho with h1
    · have := wc_le_succ (st C q)
      exact ⟨by omega, (Option.some_injective _ ho).symm ▸ rfl⟩
  constructor
  · intro x; rw [hwc']; exact hI.wc_le x
  · intro x hx'; rw [hw'] at hx'; rw [ht']
    split_ifs with hx
    · subst hx; rw [hw] at hx'; exact absurd hx' (by simp)
    · exact hI.todo_eq x hx'
  · intro x; rw [ht']; split_ifs with hx
    · have := hI.todo_suffix p; rw [htd] at this; exact (List.suffix_cons q t).trans this
    · exact hI.todo_suffix x
  · intro x i y h; rw [hwc']; rw [hs'] at h
    split_ifs at h with hc
    · obtain ⟨rfl, rfl, rfl⟩ := hc; rw [wc_eq, hw]; simp
    · exact hI.seen_lt x i y h
  · intro x i y hi; rw [hr'] at hi; rw [hs']
    split_ifs with hc
    · simp
    · exact hI.seen_old x i y hi
  · intro x y hwx hy; rw [hw'] at hwx; rw [ht'] at hy; rw [hs', hr']
    by_cases hx : x = p
    · subst hx; simp only [↓reduceIte] at hy
      by_cases hyq : y = q
      · simp [hyq]
      · rw [ite_eq_right (by simp [hyq])]
        exact hI.seen_cur _ y hw (by rw [htd]; simp [hyq, hy])
    · simp only [hx, false_and, ↓reduceIte] at hy ⊢; exact hI.seen_cur x y hwx hy
  · intro x i; rw [hmem, hwc', hv']; exact hI.mem_eq x i
  · intro x i hi; rw [hr'] at hi; rw [hlo', hhi', hv']
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      have := hI.lo_le x (st C x).r le_rfl
      exact ⟨(minO_le _ _).trans this.1, this.2.trans (le_maxO _ _)⟩
    · exact hI.lo_le x i hi
  · intro x i hi; rw [hr'] at hi; rw [hv', hlo', hhi']
    have hc : ¬(x = p ∧ i = (st C p).r) := by rintro ⟨rfl, rfl⟩; omega
    simp only [hc, ↓reduceIte]; exact hI.val_succ x i hi
  · intro x i hi; rw [hr'] at hi; rw [hlo']; simp only [hr', hv']
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      cases o with
      | none => exact hI.lo_wit _ _ le_rfl
      | some e =>
        obtain ⟨h1, h2⟩ := hit e rfl
        simp only [AAState.minO]
        rcases min_choice ((st C x).lo (st C x).r) e with h | h <;> rw [h]
        · exact hI.lo_wit _ _ le_rfl
        · exact ⟨q, h1, h2⟩
    · exact hI.lo_wit x i hi
  · intro x i hi; rw [hr'] at hi; rw [hhi']; simp only [hr', hv']
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      cases o with
      | none => exact hI.hi_wit _ _ le_rfl
      | some e =>
        obtain ⟨h1, h2⟩ := hit e rfl
        simp only [AAState.maxO]
        rcases max_choice ((st C x).hi (st C x).r) e with h | h <;> rw [h]
        · exact hI.hi_wit _ _ le_rfl
        · exact ⟨q, h1, h2⟩
    · exact hI.hi_wit x i hi
  · intro x i y e h; rw [hs'] at h; simp only [hr', hv']; rw [hlo', hhi']
    by_cases hc1 : x = p ∧ i = (st C p).r
    · rw [ite_eq_left hc1, ite_eq_left hc1]
      obtain ⟨rfl, rfl⟩ := hc1
      by_cases hyq : y = q
      · subst hyq
        rw [ite_eq_left ⟨rfl, rfl, rfl⟩] at h
        obtain rfl := Option.some_injective _ h
        obtain ⟨h1, h2⟩ := hit e rfl
        exact ⟨h1, h2, min_le_right _ _, le_max_right _ _⟩
      · rw [ite_eq_right (by simp [hyq])] at h
        obtain ⟨h1, h2, h3, h4⟩ := hI.seen_val _ _ y e h
        exact ⟨h1, h2, (minO_le _ _).trans h3, h4.trans (le_maxO _ _)⟩
    · rw [ite_eq_right hc1, ite_eq_right hc1]
      rw [ite_eq_right (fun hc => hc1 ⟨hc.1, hc.2.1⟩)] at h
      exact hI.seen_val x i y e h
  · simp only [hr', hv']; exact hI.range
  · intro x; rw [hout, hd']; exact hI.out_some x
  · simp only [hd', hr']; exact hI.done_r
  · simp only [hout, hv']; exact hI.out_val
  · simp only [hr', hv']; exact hI.dist
  · intro x y i h hi hc
    rw [hwc'] at hi; rw [hs'] at h hc
    by_cases c1 : x = p ∧ i = (st C p).r ∧ y = q
    · rw [ite_eq_left c1] at h
      obtain ⟨rfl, rfl, rfl⟩ := c1
      obtain rfl := Option.some_injective _ h
      rw [ite_eq_left hi] at ho
      simp at ho
    · rw [ite_eq_right c1] at h
      by_cases c2 : y = p ∧ i = (st C p).r ∧ x = q
      · rw [ite_eq_left c2] at hc
        obtain ⟨rfl, rfl, rfl⟩ := c2
        obtain rfl := Option.some_injective _ hc
        have := hI.seen_lt _ _ _ (by rw [h]; simp : (st C x).seen (st C y).r y ≠ none)
        rw [ite_eq_left this] at ho
        simp at ho
      · rw [ite_eq_right c2] at hc; exact hI.cross x y i h hi hc

/-- Every step preserves the invariant. -/
lemma Inv.step (hI : Inv R k L a b C) (hL : ∀ q, q ∈ L) (p : P) :
    Inv R k L a b ((aaAlg R k L).step p C) := by
  cases hd : (st C p).done
  · by_cases hr : (st C p).r = R
    · rw [step_decide C p hd hr]
      have hnone : C.out p = none := by
        have := hI.out_some p; rw [hd] at this; simpa using this
      refine inv_decide hI hr (fun x => ?_) rfl (fun x => ?_)
      · simp only [st]; exact Function.update_apply _ _ _ _
      · simp [Function.update_apply, hnone]
    · cases hw : (st C p).wrote
      · rw [step_write C p hd hr hw]
        refine inv_write hI hL hr hw (fun x => ?_) (fun x => ?_) rfl
        · simp only [st]; exact Function.update_apply _ _ _ _
        · simp only [Function.update_apply]; split_ifs <;> rfl
      · cases ht : (st C p).todo with
        | nil =>
          rw [step_advance C p hd hr hw ht]
          exact inv_advance hI hr hw ht (fun x => by simp only [st]; exact Function.update_apply _ _ _ _) rfl rfl
        | cons q t =>
          rw [step_read C p hd hr hw ht]
          exact inv_read hI hw ht (fun x => by simp only [st]; exact Function.update_apply _ _ _ _) rfl rfl
  · rw [step_done C p hd]; exact hI

/-- The invariant holds in every reachable configuration. -/
lemma inv_run (hL : ∀ q, q ∈ L) (x : P → Bool)
    (hab : ∀ p, a ≤ (if x p then 1 else 0 : ℚ) ∧ (if x p then 1 else 0 : ℚ) ≤ b) (σ : List P) :
    Inv R k L a b ((aaAlg R k L).run ((aaAlg R k L).initCfg x) σ) := by
  induction σ using List.reverseRecOn with
  | nil => exact inv_init x hab
  | append_singleton σ z ih => rw [Alg.run_concat]; exact ih.step hL z

end Invariant

/-! ### Termination -/

section Termination

variable {R k : ℕ} {L : List P}

/-- Progress measure: the number of steps taken by a process that has not decided yet. -/
def prog (n : ℕ) (s : AAState P) : ℕ :=
  s.r * (n + 2) + if s.wrote then 1 + (n - s.todo.length) else 0

lemma prog_run (hL : ∀ q, q ∈ L) (x : P → Bool) (σ : List P) (p : P) :
    (st ((aaAlg R k L).run ((aaAlg R k L).initCfg x) σ) p).done = false →
    prog L.length (st ((aaAlg R k L).run ((aaAlg R k L).initCfg x) σ) p) = σ.count p := by
  induction σ using List.reverseRecOn with
  | nil => intro _; simp [prog, st, Alg.initCfg, aaAlg, AAState.init]
  | append_singleton σ z ih =>
    intro hd'
    have hI : Inv R k L 0 1 _ := inv_run (σ := σ) hL x (fun p => by cases x p <;> norm_num)
    rw [Alg.run_concat] at hd' ⊢
    rw [List.count_append, List.count_singleton]
    generalize (aaAlg R k L).run ((aaAlg R k L).initCfg x) σ = C at hI hd' ih ⊢
    by_cases hz : z = p
    · subst hz
      simp only [beq_self_eq_true, ↓reduceIte]
      cases hd : (st C z).done
      · have ih := ih hd
        by_cases hr : (st C z).r = R
        · have e : st ((aaAlg R k L).step z C) z = { st C z with done := true } := by
            rw [step_decide C z hd hr]; exact Function.update_self _ _ _
          rw [e] at hd'; simp at hd'
        · cases hw : (st C z).wrote
          · have e : st ((aaAlg R k L).step z C) z = { st C z with wrote := true } := by
              rw [step_write C z hd hr hw]; exact Function.update_self _ _ _
            rw [e]
            have := hI.todo_eq z hw
            simp only [prog] at ih ⊢
            simp [hw, this] at ih ⊢
            omega
          · cases ht : (st C z).todo with
            | nil =>
              have e : st ((aaAlg R k L).step z C) z = AAState.advance L (st C z) := by
                rw [step_advance C z hd hr hw ht]; exact Function.update_self _ _ _
              rw [e]
              simp only [prog] at ih ⊢
              simp [hw, ht, AAState.advance] at ih ⊢
              rw [Nat.add_mul]
              omega
            | cons q t =>
              have e : st ((aaAlg R k L).step z C) z =
                  AAState.record (st C z) q t (C.mem q ())[(st C z).r]? := by
                rw [step_read C z hd hr hw ht]; exact Function.update_self _ _ _
              rw [e]
              have hle := (hI.todo_suffix z).length_le
              rw [ht] at hle
              simp only [prog] at ih ⊢
              simp [hw, ht, AAState.record] at ih hle ⊢
              omega
      · rw [step_done C z hd] at hd'; rw [hd'] at hd; simp at hd
    · simp only [st, Alg.step_loc_ne C (Ne.symm hz)] at hd' ⊢
      simp [hz, ih hd']

/-- A process that has not decided has taken fewer than `R * (|L| + 2) + 1` steps. -/
lemma prog_lt {a b : ℚ} {C : Config (aaAlg R k L)} (hI : Inv R k L a b C) (p : P) :
    prog L.length (st C p) < R * (L.length + 2) + 1 := by
  have h1 := hI.wc_le p
  have h2 := (hI.todo_suffix p).length_le
  rw [wc_eq] at h1
  unfold prog
  split_ifs at h1 ⊢ with hw
  · have := Nat.mul_le_mul_right (L.length + 2) h1
    rw [Nat.add_mul] at this
    omega
  · have := Nat.mul_le_mul_right (L.length + 2) h1
    omega

/-- Wait-freedom: every process decides within `R * (|L| + 2) + 1` of its own steps. -/
lemma decides_of_count (hL : ∀ q, q ∈ L) (x : P → Bool) (σ : List P) (p : P)
    (hσ : R * (L.length + 2) + 1 ≤ σ.count p) :
    (((aaAlg R k L).run ((aaAlg R k L).initCfg x) σ).out p).isSome := by
  have hI : Inv R k L 0 1 _ := inv_run (σ := σ) hL x (fun p => by cases x p <;> norm_num)
  rw [hI.out_some p]
  by_contra hd
  simp only [Bool.not_eq_true] at hd
  have := prog_run (R := R) (k := k) hL x σ p hd
  have := prog_lt hI p
  omega

end Termination

/-! ### Lemma 2.2 -/

/-- The collect-midpoint algorithm with `k` rounds (reading all processes in the order of
`Finset.univ.toList`) solves binary `1/k`-agreement wait-free. -/
theorem aaAlg_solves {P : Type} [Fintype P] [DecidableEq P] (k : ℕ) :
    (aaAlg k k (Finset.univ : Finset P).toList).Solves (Fintype.card P - 1)
      (epsAgreement k) := by
  set L := (Finset.univ : Finset P).toList
  have hL : ∀ q, q ∈ L := by simp [L]
  refine ⟨fun x σ => ?_, fun x σ _ p hp => ?_⟩
  · have hI : Inv k k L 0 1 ((aaAlg k k L).run ((aaAlg k k L).initCfg x) σ) :=
      inv_run hL x (fun p => by cases x p <;> norm_num) σ
    set C := (aaAlg k k L).run ((aaAlg k k L).initCfg x) σ
    have hdec : ∀ p m, C.out p = some m →
        (st C p).r = k ∧ m = ⌊(k : ℚ) * (st C p).val k⌋₊ := by
      intro p m hm
      refine ⟨hI.done_r p ?_, hI.out_val p m hm⟩
      rw [← hI.out_some p, hm]; rfl
    refine ⟨fun p m hm => ?_, fun bb hb p m hm => ?_, fun p q m m' hm hm' => ?_⟩
    · obtain ⟨hr, rfl⟩ := hdec p m hm
      have := hI.range p k hr.ge
      have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      calc ⌊(k : ℚ) * (st C p).val k⌋₊ ≤ ⌊(k : ℚ)⌋₊ := Nat.floor_le_floor (by nlinarith)
        _ = k := Nat.floor_natCast k
    · have hI' : Inv k k L (if bb then 1 else 0) (if bb then 1 else 0) C :=
        inv_run hL x (fun p => by rw [hb p]; simp) σ
      obtain ⟨hr, rfl⟩ := hdec p m hm
      have h := hI'.range p k hr.ge
      have hv : (st C p).val k = if bb then 1 else 0 := le_antisymm h.2 h.1
      rw [hv]; cases bb <;> simp
    · obtain ⟨hr, rfl⟩ := hdec p m hm
      obtain ⟨hr', rfl⟩ := hdec q m' hm'
      have hd := hI.dist p q k hr.ge hr'.ge
      have r1 := hI.range q k hr'.ge
      have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hk2 : (k : ℚ) ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self.le
      have key : (k : ℚ) * (st C p).val k ≤ (k : ℚ) * (st C q).val k + 1 := by
        have h1 : (st C p).val k - (st C q).val k ≤ 1 / 2 ^ k := (le_abs_self _).trans hd
        have h2 : (k : ℚ) * (1 / 2 ^ k) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; exact hk2
        nlinarith [mul_le_mul_of_nonneg_left h1 hk0]
      calc _ ≤ ⌊(k : ℚ) * (st C q).val k + 1⌋₊ := Nat.floor_le_floor key
        _ = _ := Nat.floor_add_one (mul_nonneg hk0 r1.1)
  · exact Alg.termination_of_bound _ _ (fun x σ p h => decides_of_count hL x σ p h) x σ p hp

/-- **Lemma 2.2** (classical): for every number of processes and every `k ≥ 1`, binary
`1/k`-agreement is wait-free solvable in the read/write model with unbounded registers. -/
theorem approxAgreement_solvable {P : Type} [Fintype P] [DecidableEq P] (k : ℕ) (_hk : 1 ≤ k) :
    ∃ A : Alg P Unit (fun _ => List ℚ) Bool ℕ, A.Solves (Fintype.card P - 1) (epsAgreement k) :=
  ⟨_, aaAlg_solves k⟩

end Podc.BoundedRegisterPower
