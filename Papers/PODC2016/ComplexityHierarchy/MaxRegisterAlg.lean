import Papers.PODC2016.ComplexityHierarchy.MaxRegister
import Cslib.Computability.Distributed.SharedMemory.Consensus
import Cslib.Computability.Distributed.SharedMemory.Progress
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Foundations.Data.Nat.Descent

/-!
# Consensus from two max-registers (Theorem 4.2 of [EGSZ16])

[EGSZ16] F. Ellen, R. Gelashvili, N. Shavit, L. Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016 (arXiv 1607.06139), Section 4.

`theorem_4_2`: obstruction-free `n`-valued consensus can be solved by any set of processes using
two max-registers `m₁`, `m₂` over `S = ℕ × {0, …, n-1}` ordered lexicographically, both
initially `(0, 0)`.

## Main results

* `theorem_4_2`: Theorem 4.2 (`n` values, processes `Fin n`).
* `theorem_4_2_general`: the same for `m ≥ 1` values and an *arbitrary* type of processes
  (the paper: "for any number of processes").
* `TwoMax.alg_safe`: agreement and validity in every finite execution (not only one-shot ones);
  `TwoMax.alg_obstructionFree`: CSLib's `Impl.ObstructionFree` (from every reachable
  configuration).
* `TwoMax.encode_strictMono`: the paper's encoding is an order embedding.

## The algorithm (paper's description)

A process first performs `write-max (0, x)` on `m₁` (`x` its input). Then it alternates between
a *scan* of `(m₁, m₂)` and a `write-max`: if the scan returns `m₁ = (r+1, x)`, `m₂ = (r, x)` it
decides `x`; if `m₁ = m₂ = (r, x)` it performs `write-max (r+1, x)` on `m₁`; otherwise it performs
`write-max` on `m₂` with the value of `m₁` in the scan. The scan is the *double collect*: read
`m₁` then `m₂` repeatedly until two consecutive collects return the same pair.

## Modelling choices / deviations from the paper

* The max-registers are over the lexicographic order `ℕ ×ₗ Fin n` directly (`Val n`), as the
  paper itself says "we may assume". The paper's encoding `(r, x) ↦ (x+1)·yʳ` (`y > n` prime)
  is an order embedding into `ℕ` (`encode_lt_encode_iff`, `encode_strictMono`), so this is no
  restriction.
* The local state of a process is just its program counter `Ph n`; after a `write-max` a new
  scan starts from scratch (no previous collect).
* As in the racing-counters files, a process that has decided and is invoked again returns its
  decision immediately; processes never invoked do nothing. All inputs are allowed.

## Proof (differs from the paper's presentation, same idea)

The double-collect scan returning `(a, b)` is linearized at the read of `m₂` in its *first*
collect: at that moment `m₂ = b` and, by monotonicity of `m₁` (read `a` before and after),
`m₁ = a`. Instead of reasoning about times we keep a *ghost set* `Snap` of all pairs
`(m₁, m₂)` present at *every* read of `m₂` (whether or not the scan later succeeds). The
invariant (`Inv`) says: `Snap` is a chain for the componentwise order and lies below the current
memory; `m₂ ≤ m₁`; whenever `m₁` (or the first component of a snapshot, or a pending `write-max`
to `m₁`) is `(j+1, x)`, the pair `((j, x), (j, x))` is in `Snap` (`Good`); and every process's
program counter is justified by a snapshot (`LocOK`), in particular a decided process has a
snapshot `((r+1, x), (r, x))`. Agreement then follows from the chain property by the paper's
downward induction (`agree_aux`).

## Remarks on the paper's proof

The argument is correct. Minor issues: the sentence "Note that `(r, x) ≺ (r′, x)`, so
`j ≤ r′`" is a typo for `(r, x) ≺ (r′, x′)` (established a few lines earlier); and the
proof's "this scan occurred after the scan by `p`" implicitly uses linearization points of the
(non-atomic) double-collect scans, which exist because both registers are monotone. Validity
needs a small extra observation not spelled out in the paper: a value `(0, 0)` in `m₁` may come
from the initialization rather than from an input, but a scanning process has already written
`(0, x)` with its own input `x`, so if it sees `m₁ = (0, 0)` then `0` is an input.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory

namespace TwoMax

/-- The values `S = ℕ × {0, …, n-1}` of the max-registers, ordered lexicographically. -/
abbrev Val (n : ℕ) := ℕ ×ₗ Fin n

variable {n : ℕ} [NeZero n]

/-- `(0, 0)`: the initial value and least element of `Val n`. -/
def bot : Val n := toLex (0, 0)

lemma bot_le (v : Val n) : bot ≤ v := by
  rw [Prod.Lex.le_iff]
  rcases Nat.eq_zero_or_pos (ofLex v).1 with h | h
  · right; exact ⟨by simp [bot, h], by simp [bot]⟩
  · left; simpa [bot] using h

lemma ne_bot_mono {v w : Val n} (h : v ≤ w) (hv : v ≠ bot) : w ≠ bot := by
  rintro rfl; exact hv (le_antisymm h (bot_le v))

lemma eq_bot_of_le {v : Val n} (h : v ≤ bot) : v = bot := le_antisymm h (bot_le v)

/-- Program counter of a process. -/
inductive Ph (n : ℕ) where
  /-- Not invoked yet. -/
  | idle
  /-- About to perform `write-max v` on `m₁`. -/
  | w1 (v : Val n)
  /-- About to perform `write-max v` on `m₂`. -/
  | w2 (v : Val n)
  /-- About to read `m₁` (start a collect); `prev` is the previous collect of this scan. -/
  | r1 (prev : Option (Val n × Val n))
  /-- Read `m₁ = a`, about to read `m₂`. -/
  | r2 (prev : Option (Val n × Val n)) (a : Val n)
  /-- Decided `x`. -/
  | done (x : Fin n)

/-- What a process does after a scan returning `(a, b)` (`m₁ = a`, `m₂ = b`). -/
def afterScan (a b : Val n) : Ph n :=
  if (ofLex a).1 = (ofLex b).1 + 1 ∧ (ofLex a).2 = (ofLex b).2 then .done (ofLex a).2
  else if a = b then .w1 (toLex ((ofLex a).1 + 1, (ofLex a).2))
  else .w2 a

/-- After a collect `(a, b)`: finish the scan if it equals the previous collect, otherwise
collect again. -/
def next (prev : Option (Val n × Val n)) (a b : Val n) : Ph n :=
  if prev = some (a, b) then afterScan a b else .r1 (some (a, b))

variable (n) in
/-- The algorithm of Theorem 4.2 of [EGSZ16]: base object `0` is `m₁`, base object `1` is
`m₂`. -/
def alg (P : Type) :
    Impl (taskObj (Fin n) (Fin n)) (fun _ : Fin 2 => maxReg (Val n)) P (Ph n) where
  memInit _ := bot
  locInit _ := .idle
  invoke _ l o := match l with
    | .idle => .w1 (toLex (0, o))
    | l => l
  act _ l := match l with
    | .idle => .ret (default : Fin n) .idle
    | .w1 v => .access 0 (.write v) (fun _ => .r1 none)
    | .w2 v => .access 1 (.write v) (fun _ => .r1 none)
    | .r1 prev => .access 0 .read (fun r => .r2 prev (r.getD bot))
    | .r2 prev a => .access 1 .read (fun r => next prev a (r.getD bot))
    | .done x => .ret x (.done x)

variable (n) in
/-- Configurations of the algorithm. -/
abbrev Cfg (P : Type) :=
  Config (taskObj (Fin n) (Fin n)) (fun _ : Fin 2 => maxReg (Val n)) P (Ph n)

variable (n) in
/-- Labels (executions are lists of labels). -/
abbrev Lbl (P : Type) := Label P (taskObj (Fin n) (Fin n))

variable {P : Type} [DecidableEq P]

/-! ### Steps -/

lemma step_w1 {C : Cfg n P} {q : P} {v : Val n} (hp : C.pend q ≠ none) (h : C.loc q = .w1 v) :
    (alg n P).step C (.tau q) =
      some ⟨Function.update C.loc q (.r1 none), C.pend,
        Function.update C.mem 0 (max (C.mem 0) v)⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, alg, h]

lemma step_w2 {C : Cfg n P} {q : P} {v : Val n} (hp : C.pend q ≠ none) (h : C.loc q = .w2 v) :
    (alg n P).step C (.tau q) =
      some ⟨Function.update C.loc q (.r1 none), C.pend,
        Function.update C.mem 1 (max (C.mem 1) v)⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, alg, h]

lemma step_r1 {C : Cfg n P} {q : P} {prev} (hp : C.pend q ≠ none) (h : C.loc q = .r1 prev) :
    (alg n P).step C (.tau q) =
      some ⟨Function.update C.loc q (.r2 prev (C.mem 0)), C.pend, C.mem⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, alg, h]
  congr 2
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · simp [Function.update_of_ne hi]

lemma step_r2 {C : Cfg n P} {q : P} {prev a} (hp : C.pend q ≠ none) (h : C.loc q = .r2 prev a) :
    (alg n P).step C (.tau q) =
      some ⟨Function.update C.loc q (next prev a (C.mem 1)), C.pend, C.mem⟩ := by
  simp only [Impl.step, hp, ↓reduceIte, alg, h]
  congr 2
  funext i
  by_cases hi : i = 1
  · subst hi; simp
  · simp [Function.update_of_ne hi]

/-! ### The safety invariant -/

/-- `x` is the input of some process in `α`. -/
def HasIn (α : List (Lbl n P)) (x : Fin n) : Prop := ∃ r, inputs α r = some x

lemma HasIn.append {α : List (Lbl n P)} {x : Fin n} (h : HasIn α x) (β : List (Lbl n P)) :
    HasIn (α ++ β) x := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  simp only [inputs, opsOf_append] at hr ⊢
  rw [List.head?_append, hr]; rfl

/-- If `v = (j+1, x)` then some snapshot saw `m₁ = m₂ = (j, x)`. -/
def Good (Snap : Set (Val n × Val n)) (v : Val n) : Prop :=
  ∀ j x, v = toLex (j + 1, x) → (toLex (j, x), toLex (j, x)) ∈ Snap

lemma Good.mono {S S' : Set (Val n × Val n)} (hS : S ⊆ S') {v : Val n} (h : Good S v) :
    Good S' v := fun j x hv => hS (h j x hv)

/-- What the program counter of a process says, given the snapshots `Snap`, the current value
`M1` of `m₁` and the set `H` of inputs. -/
def LocOK (Snap : Set (Val n × Val n)) (M1 : Val n) (H : Fin n → Prop) : Ph n → Prop
  | .idle => True
  | .w1 v => Good Snap v ∧ H (ofLex v).2
  | .w2 v => (M1 ≠ bot ∨ H 0) ∧ ∃ s2, (v, s2) ∈ Snap
  | .r1 prev => (M1 ≠ bot ∨ H 0) ∧ ∀ a b, prev = some (a, b) → ∃ s1, (s1, b) ∈ Snap ∧ a ≤ s1
  | .r2 prev a' => (M1 ≠ bot ∨ H 0) ∧ a' ≤ M1 ∧
      ∀ a b, prev = some (a, b) → ∃ s1, (s1, b) ∈ Snap ∧ a ≤ s1 ∧ s1 ≤ a'
  | .done x => ∃ r, (toLex (r + 1, x), toLex (r, x)) ∈ Snap

lemma LocOK.mono {S S' : Set (Val n × Val n)} {M1 M1' : Val n} {H H' : Fin n → Prop}
    (hS : S ⊆ S') (hM : M1 ≤ M1') (hH : ∀ x, H x → H' x) {l : Ph n} (h : LocOK S M1 H l) :
    LocOK S' M1' H' l := by
  have hZ : (M1 ≠ bot ∨ H 0) → (M1' ≠ bot ∨ H' 0) := fun h => h.imp (ne_bot_mono hM) (hH 0)
  cases l with
  | idle => trivial
  | w1 v => exact ⟨h.1.mono hS, hH _ h.2⟩
  | w2 v => obtain ⟨h1, s2, hs⟩ := h; exact ⟨hZ h1, s2, hS hs⟩
  | r1 prev =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨hZ h1, fun a b hab => let ⟨s1, hs, ha⟩ := h2 a b hab; ⟨s1, hS hs, ha⟩⟩
  | r2 prev a' =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨hZ h1, h2.trans hM, fun a b hab =>
      let ⟨s1, hs, ha, hb⟩ := h3 a b hab; ⟨s1, hS hs, ha, hb⟩⟩
  | done x => obtain ⟨r, hr⟩ := h; exact ⟨r, hS hr⟩

/-- The safety invariant, for the ghost set `Snap` of snapshots `(m₁, m₂)` taken at reads of
`m₂`. -/
structure Inv (α : List (Lbl n P)) (C : Cfg n P) (Snap : Set (Val n × Val n)) : Prop where
  chain : ∀ s ∈ Snap, ∀ t ∈ Snap, (s.1 ≤ t.1 ∧ s.2 ≤ t.2) ∨ (t.1 ≤ s.1 ∧ t.2 ≤ s.2)
  le_mem : ∀ s ∈ Snap, s.1 ≤ C.mem 0 ∧ s.2 ≤ C.mem 1
  m21 : C.mem 1 ≤ C.mem 0
  goodM : Good Snap (C.mem 0)
  goodS : ∀ s ∈ Snap, Good Snap s.1
  valM : C.mem 0 = bot ∨ HasIn α (ofLex (C.mem 0)).2
  valS : ∀ s ∈ Snap, HasIn α (ofLex s.1).2
  idle : ∀ q, C.loc q = .idle → opsOf α q = [] ∧ C.pend q = none
  loc : ∀ q, LocOK Snap (C.mem 0) (HasIn α) (C.loc q)
  resp : ∀ q (w : (taskObj (Fin n) (Fin n)).Resp), w ∈ respsOf α q → C.loc q = .done w

lemma inv_init : Inv ([] : List (Lbl n P)) (alg n P).initCfg ∅ where
  chain := by simp
  le_mem := by simp
  m21 := le_rfl
  goodM j x h := by
    simp only [Impl.initCfg, alg, bot] at h
    have := congrArg (fun v => (ofLex v).1) h
    simp at this
  goodS := by simp
  valM := Or.inl rfl
  valS := by simp
  idle _ _ := ⟨rfl, rfl⟩
  loc _ := trivial
  resp q w h := by simp only [respsOf_nil] at h; cases h

lemma Inv.step_inv {α : List (Lbl n P)} {C C' : Cfg n P} {S : Set (Val n × Val n)} {q : P}
    {o : (taskObj (Fin n) (Fin n)).Op} (hI : Inv α C S)
    (h : (alg n P).step C (.inv q o) = some C') : Inv (α ++ [.inv q o]) C' S := by
  obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  rcases C' with ⟨loc', pend', mem'⟩
  dsimp only at hmem hpend hloc; subst hmem
  have hresp : ∀ r, respsOf (α ++ [.inv q o]) r = respsOf α r := by simp [respsOf, Label.retOf]
  have hops : ∀ r, r ≠ q → opsOf (α ++ [.inv q o]) r = opsOf α r := by
    intro r hr; simp [opsOf, Label.invOf, Ne.symm hr]
  have hpend' : ∀ r, r ≠ q → pend' r = C.pend r := by
    intro r hr; simp [hpend, Function.update_of_ne hr]
  have hH : ∀ x, HasIn α x → HasIn (α ++ [.inv q o]) x := fun x hx => hx.append _
  have hl : ∀ r, loc' r =
      if r = q then (match C.loc q with | .idle => .w1 (toLex (0, o)) | l => l) else C.loc r := by
    intro r; rw [hloc]; simp only [Function.update_apply]; rfl
  refine ⟨hI.chain, hI.le_mem, hI.m21, hI.goodM, hI.goodS, hI.valM.imp_right (hH _),
    fun s hs => hH _ (hI.valS s hs), ?_, ?_, ?_⟩
  · intro r hr
    dsimp only at hr ⊢
    rw [hl] at hr
    split_ifs at hr with hrq
    · subst hrq
      cases hq : C.loc r <;> rw [hq] at hr <;> simp at hr
    · exact ⟨by rw [hops r hrq]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
  · intro r
    dsimp only
    rw [hl]
    split_ifs with hrq
    · subst hrq
      cases hq : C.loc r with
      | idle =>
        refine ⟨fun j x hj => ?_, ⟨r, ?_⟩⟩
        · have := congrArg (fun v => (ofLex v).1) hj; simp at this
        · simp [inputs, opsOf_append, (hI.idle r hq).1, Label.invOf]; rfl
      | _ => have := hI.loc r; rw [hq] at this; exact this.mono subset_rfl le_rfl hH
    · exact (hI.loc r).mono subset_rfl le_rfl hH
  · intro r w hr
    dsimp only at hr ⊢
    rw [hresp] at hr
    have := hI.resp r w hr
    rw [hl]; split_ifs with hrq
    · subst hrq; rw [this]
    · exact this

lemma Inv.step_ret {α : List (Lbl n P)} {C C' : Cfg n P} {S : Set (Val n × Val n)} {q : P}
    {o : (taskObj (Fin n) (Fin n)).Resp} (hI : Inv α C S)
    (h : (alg n P).step C (.ret q o) = some C') : Inv (α ++ [.ret q o]) C' S := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  rcases C' with ⟨loc', pend', mem'⟩
  dsimp only at hmem hpend hloc; subst hmem
  have hops : ∀ r, opsOf (α ++ [.ret q o]) r = opsOf α r := by simp [opsOf, Label.invOf]
  have hin : ∀ w, HasIn (α ++ [.ret q o]) w ↔ HasIn α w := by
    intro w; simp only [HasIn, inputs, hops]
  have hH : ∀ x, HasIn α x → HasIn (α ++ [.ret q o]) x := fun x hx => (hin x).2 hx
  cases hph : C.loc q with
  | idle => exact absurd (hI.idle q hph).2 h0
  | w1 v => rw [hph] at hact; cases hact
  | w2 v => rw [hph] at hact; cases hact
  | r1 prev => rw [hph] at hact; cases hact
  | r2 prev a => rw [hph] at hact; cases hact
  | done x =>
    rw [hph] at hact
    simp only [alg] at hact
    obtain ⟨rfl, rfl⟩ := hact
    have hl : loc' = C.loc := by rw [hloc, ← hph]; simp
    have hpend' : ∀ r, r ≠ q → pend' r = C.pend r := by
      intro r hr; simp [hpend, Function.update_of_ne hr]
    refine ⟨hI.chain, hI.le_mem, hI.m21, hI.goodM, hI.goodS, hI.valM.imp_right (hH _),
      fun s hs => hH _ (hI.valS s hs), ?_, ?_, ?_⟩
    · intro r hr
      dsimp only at hr ⊢
      rw [hl] at hr
      have hrq : r ≠ q := by rintro rfl; rw [hph] at hr; cases hr
      exact ⟨by rw [hops r]; exact (hI.idle r hr).1, by rw [hpend' r hrq]; exact (hI.idle r hr).2⟩
    · intro r; dsimp only; rw [hl]; exact (hI.loc r).mono subset_rfl le_rfl hH
    · intro r w hr
      dsimp only at hr ⊢
      rw [hl]
      rw [respsOf_append] at hr
      rcases List.mem_append.1 hr with hr1 | hr1
      · exact hI.resp r w hr1
      · by_cases hrq : q = r
        · subst hrq
          simp [respsOf, Label.retOf] at hr1
          rw [hph, hr1]
        · simp [respsOf, Label.retOf, hrq] at hr1

lemma Inv.mk' {α : List (Lbl n P)} {C : Cfg n P} {S : Set (Val n × Val n)} {M1 M2 : Val n}
    (h0 : C.mem 0 = M1) (h1 : C.mem 1 = M2)
    (chain : ∀ s ∈ S, ∀ t ∈ S, (s.1 ≤ t.1 ∧ s.2 ≤ t.2) ∨ (t.1 ≤ s.1 ∧ t.2 ≤ s.2))
    (le_mem : ∀ s ∈ S, s.1 ≤ M1 ∧ s.2 ≤ M2) (m21 : M2 ≤ M1) (goodM : Good S M1)
    (goodS : ∀ s ∈ S, Good S s.1) (valM : M1 = bot ∨ HasIn α (ofLex M1).2)
    (valS : ∀ s ∈ S, HasIn α (ofLex s.1).2)
    (idle : ∀ q, C.loc q = .idle → opsOf α q = [] ∧ C.pend q = none)
    (loc : ∀ q, LocOK S M1 (HasIn α) (C.loc q))
    (resp : ∀ q (w : (taskObj (Fin n) (Fin n)).Resp), w ∈ respsOf α q → C.loc q = .done w) :
    Inv α C S := by
  subst h0 h1; exact ⟨chain, le_mem, m21, goodM, goodS, valM, valS, idle, loc, resp⟩

lemma afterScan_ne_idle (a b : Val n) : afterScan a b ≠ .idle := by
  unfold afterScan; split_ifs <;> simp

lemma next_ne_idle (prev : Option (Val n × Val n)) (a b : Val n) : next prev a b ≠ .idle := by
  unfold next; split_ifs
  · exact afterScan_ne_idle a b
  · simp

lemma afterScan_ok {S : Set (Val n × Val n)} {M1 : Val n} {H : Fin n → Prop} {a b : Val n}
    (hab : (a, b) ∈ S) (hH : H (ofLex a).2) (hZ : M1 ≠ bot ∨ H 0) :
    LocOK S M1 H (afterScan a b) := by
  unfold afterScan
  split_ifs with h1 h2
  · refine ⟨(ofLex b).1, ?_⟩
    have ha : a = toLex ((ofLex b).1 + 1, (ofLex a).2) := by rw [← h1.1]; rfl
    have hb : b = toLex ((ofLex b).1, (ofLex a).2) := by rw [h1.2]; rfl
    rw [← ha, ← hb]; exact hab
  · subst h2
    refine ⟨fun j x hj => ?_, hH⟩
    have := congrArg ofLex hj
    simp only [ofLex_toLex, Prod.mk.injEq] at this
    obtain ⟨h3, h4⟩ := this
    have : a = toLex (j, x) := by rw [← h4, show j = (ofLex a).1 by omega]; rfl
    rw [← this]; exact hab
  · exact ⟨hZ, b, hab⟩

/-- Preservation of the invariant by a step of `q` that changes its program counter to `l`
and the memory to `mem'`. -/
lemma Inv.tau_aux {α : List (Lbl n P)} {C : Cfg n P} {S : Set (Val n × Val n)} (hI : Inv α C S)
    {q : P} (hq : ∀ w, C.loc q ≠ .done w) {l : Ph n} (hl : l ≠ .idle)
    {S' : Set (Val n × Val n)} {M1' M2' : Val n} {mem' : (i : Fin 2) → (maxReg (Val n)).State}
    (h0 : mem' 0 = M1') (h1 : mem' 1 = M2') (hS : S ⊆ S') (hM : C.mem 0 ≤ M1')
    (chain : ∀ s ∈ S', ∀ t ∈ S', (s.1 ≤ t.1 ∧ s.2 ≤ t.2) ∨ (t.1 ≤ s.1 ∧ t.2 ≤ s.2))
    (le_mem : ∀ s ∈ S', s.1 ≤ M1' ∧ s.2 ≤ M2') (m21 : M2' ≤ M1') (goodM : Good S' M1')
    (goodS : ∀ s ∈ S', Good S' s.1) (valM : M1' = bot ∨ HasIn α (ofLex M1').2)
    (valS : ∀ s ∈ S', HasIn α (ofLex s.1).2) (hloc : LocOK S' M1' (HasIn α) l) :
    Inv (α ++ [.tau q]) ⟨Function.update C.loc q l, C.pend, mem'⟩ S' := by
  have hops : ∀ r, opsOf (α ++ [.tau q]) r = opsOf α r := by simp [opsOf, Label.invOf]
  have hresps : ∀ r, respsOf (α ++ [.tau q]) r = respsOf α r := by simp [respsOf, Label.retOf]
  have hin : ∀ w, HasIn (α ++ [.tau q]) w ↔ HasIn α w := by
    intro w; simp only [HasIn, inputs, hops]
  have hH : ∀ x, HasIn α x → HasIn (α ++ [.tau q]) x := fun x hx => (hin x).2 hx
  refine Inv.mk' h0 h1 chain le_mem m21 goodM goodS (valM.imp_right (hH _))
    (fun s hs => hH _ (valS s hs)) ?_ ?_ ?_
  · intro r hr
    dsimp only at hr ⊢
    by_cases hrq : r = q
    · subst hrq; simp at hr; exact absurd hr hl
    · rw [Function.update_of_ne hrq] at hr
      exact ⟨by rw [hops]; exact (hI.idle r hr).1, (hI.idle r hr).2⟩
  · intro r
    dsimp only
    by_cases hrq : r = q
    · subst hrq; simp only [Function.update_self]; exact hloc.mono subset_rfl le_rfl hH
    · rw [Function.update_of_ne hrq]; exact (hI.loc r).mono hS hM hH
  · intro r w hr
    dsimp only
    rw [hresps] at hr
    have := hI.resp r w hr
    by_cases hrq : r = q
    · subst hrq; exact absurd this (hq w)
    · rw [Function.update_of_ne hrq]; exact this

lemma Inv.step_tau {α : List (Lbl n P)} {C C' : Cfg n P} {S : Set (Val n × Val n)} {q : P}
    (hI : Inv α C S) (h : (alg n P).step C (.tau q) = some C') :
    ∃ S', Inv (α ++ [.tau q]) C' S' := by
  have hp : C.pend q ≠ none := (Impl.step_tau h).1
  have hlq := hI.loc q
  cases hph : C.loc q with
  | idle => exact absurd (hI.idle q hph).2 hp
  | done x =>
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
    rw [hph] at hact; cases hact
  | w1 v =>
    rw [step_w1 hp hph] at h
    cases h
    rw [hph] at hlq
    obtain ⟨hgv, hHv⟩ := hlq
    refine ⟨S, hI.tau_aux (M1' := max (C.mem 0) v) (M2' := C.mem 1) (by simp [hph]) (by simp) (by simp) (by simp) subset_rfl
      (le_max_left _ _) hI.chain (fun s hs => ⟨(hI.le_mem s hs).1.trans (le_max_left _ _),
        (hI.le_mem s hs).2⟩) (hI.m21.trans (le_max_left _ _)) ?_ hI.goodS ?_ hI.valS ?_⟩
    · rcases max_choice (C.mem 0) v with he | he <;> rw [he]
      · exact hI.goodM
      · exact hgv
    · rcases max_choice (C.mem 0) v with he | he <;> rw [he]
      · exact hI.valM
      · exact Or.inr hHv
    · refine ⟨?_, fun a b hab => by cases hab⟩
      by_cases hb : max (C.mem 0) v = bot
      · right
        have hv : v = bot := eq_bot_of_le (hb ▸ le_max_right _ _)
        rw [hv] at hHv; exact hHv
      · exact Or.inl hb
  | w2 v =>
    rw [step_w2 hp hph] at h
    cases h
    rw [hph] at hlq
    obtain ⟨hZ, s2, hs2⟩ := hlq
    have hv : v ≤ C.mem 0 := (hI.le_mem _ hs2).1
    refine ⟨S, hI.tau_aux (M1' := C.mem 0) (M2' := max (C.mem 1) v) (by simp [hph]) (by simp) (by simp) (by simp) subset_rfl
      le_rfl hI.chain (fun s hs => ⟨(hI.le_mem s hs).1,
        (hI.le_mem s hs).2.trans (le_max_left _ _)⟩) (max_le hI.m21 hv) hI.goodM hI.goodS
      hI.valM hI.valS ⟨hZ, fun a b hab => by cases hab⟩⟩
  | r1 prev =>
    rw [step_r1 hp hph] at h
    cases h
    rw [hph] at hlq
    obtain ⟨hZ, hprev⟩ := hlq
    refine ⟨S, hI.tau_aux (by simp [hph]) (by simp) rfl rfl subset_rfl
      le_rfl hI.chain hI.le_mem hI.m21 hI.goodM hI.goodS hI.valM hI.valS
      ⟨hZ, le_rfl, fun a b hab => ?_⟩⟩
    obtain ⟨s1, hs1, ha⟩ := hprev a b hab
    exact ⟨s1, hs1, ha, (hI.le_mem _ hs1).1⟩
  | r2 prev a' =>
    rw [step_r2 hp hph] at h
    cases h
    rw [hph] at hlq
    obtain ⟨hZ, ha', hprev⟩ := hlq
    set S' := insert (C.mem 0, C.mem 1) S with hS'
    have hsub : S ⊆ S' := Set.subset_insert _ _
    have hnew : (C.mem 0, C.mem 1) ∈ S' := Set.mem_insert _ _
    have hval0 : HasIn α (ofLex (C.mem 0)).2 := by
      rcases hI.valM with h0 | h0
      · rcases hZ with hZ | hZ
        · exact absurd h0 hZ
        · rw [h0]; exact hZ
      · exact h0
    have goodS' : ∀ s ∈ S', Good S' s.1 := by
      intro s hs
      rcases Set.mem_insert_iff.1 hs with rfl | hs
      · exact hI.goodM.mono hsub
      · exact (hI.goodS s hs).mono hsub
    have valS' : ∀ s ∈ S', HasIn α (ofLex s.1).2 := by
      intro s hs
      rcases Set.mem_insert_iff.1 hs with rfl | hs
      · exact hval0
      · exact hI.valS s hs
    refine ⟨S', hI.tau_aux (by simp [hph]) (next_ne_idle _ _ _) rfl rfl hsub le_rfl ?_ ?_
      hI.m21 (hI.goodM.mono hsub) goodS' hI.valM valS' ?_⟩
    · intro s hs t ht
      rcases Set.mem_insert_iff.1 hs with rfl | hs <;>
        rcases Set.mem_insert_iff.1 ht with rfl | ht
      · exact Or.inl ⟨le_rfl, le_rfl⟩
      · exact Or.inr (hI.le_mem t ht)
      · exact Or.inl (hI.le_mem s hs)
      · exact hI.chain s hs t ht
    · intro s hs
      rcases Set.mem_insert_iff.1 hs with rfl | hs
      · exact ⟨le_rfl, le_rfl⟩
      · exact hI.le_mem s hs
    · unfold next
      split_ifs with he
      · obtain ⟨s1, hs1, h1, h2⟩ := hprev a' (C.mem 1) he
        have : s1 = a' := le_antisymm h2 h1
        subst this
        exact afterScan_ok (hsub hs1) (valS' _ (hsub hs1)) hZ
      · refine ⟨hZ, fun a b hab => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        exact ⟨C.mem 0, hnew, ha'⟩

/-- The invariant holds in every reachable configuration (for some ghost set of snapshots). -/
theorem inv_run {α : List (Lbl n P)} {C : Cfg n P} (h : (alg n P).run α = some C) :
    ∃ S, Inv α C S := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [Impl.run_nil, Option.some.injEq] at h; subst h; exact ⟨∅, inv_init⟩
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (alg n P).runFrom (alg n P).initCfg α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      obtain ⟨S, hI⟩ := ih hα
      cases ℓ with
      | inv q o => exact ⟨S, hI.step_inv h⟩
      | ret q o => exact ⟨S, hI.step_ret h⟩
      | tau q => exact hI.step_tau h

/-! ### Agreement and validity -/

/-- The paper's downward induction: if `((r+1, x), (r, x))` is a snapshot, then every snapshot
`((j, x'), (j, x'))` with `x' ≠ x` satisfies `(j, x') ≤ (r, x)`. -/
lemma agree_aux {S : Set (Val n × Val n)}
    (chain : ∀ s ∈ S, ∀ t ∈ S, (s.1 ≤ t.1 ∧ s.2 ≤ t.2) ∨ (t.1 ≤ s.1 ∧ t.2 ≤ s.2))
    (goodS : ∀ s ∈ S, Good S s.1) {r : ℕ} {x x' : Fin n} (hx : x' ≠ x)
    (hd : (toLex (r + 1, x), toLex (r, x)) ∈ S) :
    ∀ j, (toLex (j, x'), toLex (j, x')) ∈ S → toLex (j, x') ≤ toLex (r, x) := by
  intro j
  induction j with
  | zero =>
    intro hj
    rcases chain _ hj _ hd with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · rw [Prod.Lex.toLex_le_toLex] at h; simp at h
  | succ j ih =>
    intro hj
    rcases chain _ hj _ hd with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · have h2 := ih (goodS _ hj j x' rfl)
      rw [Prod.Lex.toLex_le_toLex] at h h2 ⊢
      simp only at h h2 ⊢
      rcases h with h | ⟨h, h'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
      · omega
      · omega
      · omega
      · exact absurd (le_antisymm h2' h') hx

/-- Two decision snapshots carry the same value. -/
lemma agree_two {S : Set (Val n × Val n)}
    (chain : ∀ s ∈ S, ∀ t ∈ S, (s.1 ≤ t.1 ∧ s.2 ≤ t.2) ∨ (t.1 ≤ s.1 ∧ t.2 ≤ s.2))
    (goodS : ∀ s ∈ S, Good S s.1) {r r' : ℕ} {x x' : Fin n}
    (hd : (toLex (r + 1, x), toLex (r, x)) ∈ S)
    (hd' : (toLex (r' + 1, x'), toLex (r', x')) ∈ S) : x = x' := by
  by_contra hne
  rcases chain _ hd _ hd' with ⟨-, h⟩ | ⟨-, h⟩
  · have h2 := agree_aux chain goodS (Ne.symm hne) hd r' (goodS _ hd' r' x' rfl)
    have := congrArg (fun v => (ofLex v).2) (le_antisymm h h2)
    simp at this; exact hne this
  · have h2 := agree_aux chain goodS hne hd' r (goodS _ hd r x rfl)
    have := congrArg (fun v => (ofLex v).2) (le_antisymm h h2)
    simp at this; exact hne this.symm

/-- Agreement and validity hold in *every* finite execution (one-shot or not). -/
theorem alg_safe (α : List (Lbl n P)) (hα : (alg n P).Valid α) :
    (consensus P (Fin n)).Δ (inputs α) (outputs α) := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨S, hI⟩ := inv_run hC
  have hout : ∀ q (w : (taskObj (Fin n) (Fin n)).Resp), outputs α q = some w →
      C.loc q = .done w :=
    fun q w h => hI.resp q w (List.mem_of_head? h)
  have hdec : ∀ q (w : Fin n), outputs α q = some w →
      ∃ r, (toLex (r + 1, w), toLex (r, w)) ∈ S := by
    intro q w h; have := hI.loc q; rw [hout q w h] at this; exact this
  refine ⟨fun p q x y hx hy => ?_, fun p y hy => ?_⟩
  · obtain ⟨r, hr⟩ := hdec p x hx
    obtain ⟨r', hr'⟩ := hdec q y hy
    exact agree_two hI.chain hI.goodS hr hr'
  · obtain ⟨r, hr⟩ := hdec p y hy
    exact hI.valS _ hr

/-- The algorithm solves consensus. -/
theorem alg_solves : (alg n P).Solves (consensus P (Fin n)) :=
  fun α hα _ => alg_safe α hα

/-! ### Obstruction-freedom -/

variable (p : P)

/-- `p` running solo from `C` eventually returns. -/
def Term (C : Cfg n P) : Prop := ∃ k, (((alg n P).soloStep p)^[k] C).pend p = none

variable {p}

lemma Term.of_solo {C : Cfg n P} (h : Term p ((alg n P).soloStep p C)) : Term p C := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

lemma soloStep_tau {C C' : Cfg n P} (hp : C.pend p ≠ none)
    (hn : (alg n P).nextLabel C p = .tau p) (h : (alg n P).step C (.tau p) = some C') :
    (alg n P).soloStep p C = C' := by
  simp [Impl.soloStep, hp, hn, h]

lemma solo_w1 {C : Cfg n P} {v : Val n} (hp : C.pend p ≠ none) (hph : C.loc p = .w1 v) :
    ((alg n P).soloStep p C).pend = C.pend ∧ ((alg n P).soloStep p C).loc p = .r1 none ∧
      ((alg n P).soloStep p C).mem 0 = max (C.mem 0) v ∧
      ((alg n P).soloStep p C).mem 1 = C.mem 1 := by
  rw [soloStep_tau hp (by simp [Impl.nextLabel, alg, hph]) (step_w1 hp hph)]
  simp

lemma solo_w2 {C : Cfg n P} {v : Val n} (hp : C.pend p ≠ none) (hph : C.loc p = .w2 v) :
    ((alg n P).soloStep p C).pend = C.pend ∧ ((alg n P).soloStep p C).loc p = .r1 none ∧
      ((alg n P).soloStep p C).mem 0 = C.mem 0 ∧
      ((alg n P).soloStep p C).mem 1 = max (C.mem 1) v := by
  rw [soloStep_tau hp (by simp [Impl.nextLabel, alg, hph]) (step_w2 hp hph)]
  simp

lemma solo_r1 {C : Cfg n P} {prev} (hp : C.pend p ≠ none) (hph : C.loc p = .r1 prev) :
    ((alg n P).soloStep p C).pend = C.pend ∧
      ((alg n P).soloStep p C).loc p = .r2 prev (C.mem 0) ∧
      ((alg n P).soloStep p C).mem = C.mem := by
  rw [soloStep_tau hp (by simp [Impl.nextLabel, alg, hph]) (step_r1 hp hph)]
  simp

lemma solo_r2 {C : Cfg n P} {prev a} (hp : C.pend p ≠ none) (hph : C.loc p = .r2 prev a) :
    ((alg n P).soloStep p C).pend = C.pend ∧
      ((alg n P).soloStep p C).loc p = next prev a (C.mem 1) ∧
      ((alg n P).soloStep p C).mem = C.mem := by
  rw [soloStep_tau hp (by simp [Impl.nextLabel, alg, hph]) (step_r2 hp hph)]
  simp

lemma term_done {C : Cfg n P} {x : Fin n} (hp : C.pend p ≠ none) (hph : C.loc p = .done x) :
    Term p C := by
  refine ⟨1, ?_⟩
  have hn : (alg n P).nextLabel C p = .ret p x := by simp [Impl.nextLabel, alg, hph]
  have hs : (alg n P).step C (.ret p x) =
      some { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p (.done x) } := by
    simp [Impl.step, hp, alg, hph]
    rfl
  simp [Impl.soloStep, hp, hn, hs]

/-- A complete collect (two solo steps) from `r1 prev`. -/
lemma Term.of_collect {C : Cfg n P} {prev} (hp : C.pend p ≠ none) (hph : C.loc p = .r1 prev)
    (h : ∀ C' : Cfg n P, C'.pend = C.pend → C'.loc p = next prev (C.mem 0) (C.mem 1) →
      C'.mem = C.mem → ((alg n P).Reachable C → (alg n P).Reachable C') → Term p C') :
    Term p C := by
  obtain ⟨h1, h2, h3⟩ := solo_r1 hp hph
  obtain ⟨h4, h5, h6⟩ := solo_r2 (by rw [h1]; exact hp) h2
  exact Term.of_solo (Term.of_solo (h _ (h4.trans h1) (by rw [h5, h3]) (h6.trans h3)
    fun hR => (hR.soloStep p).soloStep p))

lemma afterScan_dec (r : ℕ) (x : Fin n) :
    afterScan (toLex (r + 1, x)) (toLex (r, x)) = .done x := by
  simp [afterScan]

lemma afterScan_self (a : Val n) :
    afterScan a a = .w1 (toLex ((ofLex a).1 + 1, (ofLex a).2)) := by
  simp [afterScan]

lemma next_some (a b : Val n) : next (some (a, b)) a b = afterScan a b := by simp [next]

lemma next_none (a b : Val n) : next none a b = .r1 (some (a, b)) := by simp [next]

lemma le_succ_val (a : Val n) : a ≤ toLex ((ofLex a).1 + 1, (ofLex a).2) := by
  rw [Prod.Lex.le_iff]; left; simp

lemma term_dec {C : Cfg n P} {r : ℕ} {x : Fin n} (hp : C.pend p ≠ none)
    (hph : C.loc p = .r1 none) (h0 : C.mem 0 = toLex (r + 1, x)) (h1 : C.mem 1 = toLex (r, x)) :
    Term p C := by
  refine Term.of_collect hp hph fun C1 hp1 hl1 hm1 _ => ?_
  rw [next_none] at hl1
  refine Term.of_collect (by rw [hp1]; exact hp) hl1 fun C2 hp2 hl2 hm2 _ => ?_
  rw [hm1, next_some, h0, h1, afterScan_dec] at hl2
  exact term_done (by rw [hp2, hp1]; exact hp) hl2

lemma term_w1_succ {C : Cfg n P} {a : Val n} (hp : C.pend p ≠ none)
    (hph : C.loc p = .w1 (toLex ((ofLex a).1 + 1, (ofLex a).2))) (h0 : C.mem 0 = a)
    (h1 : C.mem 1 = a) : Term p C := by
  obtain ⟨e1, e2, e3, e4⟩ := solo_w1 hp hph
  refine Term.of_solo (term_dec (r := (ofLex a).1) (x := (ofLex a).2) (by rw [e1]; exact hp) e2
    ?_ ?_)
  · rw [e3, h0]; exact max_eq_right (le_succ_val a)
  · rw [e4, h1]; rfl

lemma term_eq {C : Cfg n P} {a : Val n} (hp : C.pend p ≠ none) (hph : C.loc p = .r1 none)
    (h0 : C.mem 0 = a) (h1 : C.mem 1 = a) : Term p C := by
  refine Term.of_collect hp hph fun C1 hp1 hl1 hm1 _ => ?_
  rw [next_none] at hl1
  refine Term.of_collect (by rw [hp1]; exact hp) hl1 fun C2 hp2 hl2 hm2 _ => ?_
  rw [hm1, next_some, h0, h1, afterScan_self] at hl2
  exact term_w1_succ (by rw [hp2, hp1]; exact hp) hl2 (by rw [hm2, hm1, h0])
    (by rw [hm2, hm1, h1])

/-- A fresh scan (no previous collect) run solo with `m₂ ≤ m₁` leads to a decision. -/
lemma term_fresh {C : Cfg n P} (hp : C.pend p ≠ none) (hph : C.loc p = .r1 none)
    (h21 : C.mem 1 ≤ C.mem 0) : Term p C := by
  refine Term.of_collect hp hph fun C1 hp1 hl1 hm1 _ => ?_
  rw [next_none] at hl1
  refine Term.of_collect (by rw [hp1]; exact hp) hl1 fun C2 hp2 hl2 hm2 _ => ?_
  rw [hm1, next_some] at hl2
  have hp2' : C2.pend p ≠ none := by rw [hp2, hp1]; exact hp
  have hm : C2.mem = C.mem := hm2.trans hm1
  unfold afterScan at hl2
  split_ifs at hl2 with hd he
  · exact term_done hp2' hl2
  · exact term_w1_succ hp2' hl2 (by rw [hm]) (by rw [hm, he])
  · obtain ⟨e1, e2, e3, e4⟩ := solo_w2 hp2' hl2
    exact Term.of_solo (term_eq (a := C.mem 0) (by rw [e1]; exact hp2') e2 (by rw [e3, hm])
      (by rw [e4, hm, max_eq_right h21]))

lemma term_dw {C : Cfg n P} (hR : (alg n P).Reachable C) (hp : C.pend p ≠ none)
    (hph : (∃ x, C.loc p = .done x) ∨ (∃ v, C.loc p = .w1 v) ∨ (∃ v, C.loc p = .w2 v) ∨
      C.loc p = .r1 none) : Term p C := by
  obtain ⟨α, hα⟩ := hR
  obtain ⟨S, hI⟩ := inv_run hα
  rcases hph with ⟨x, hph⟩ | ⟨v, hph⟩ | ⟨v, hph⟩ | hph
  · exact term_done hp hph
  · obtain ⟨e1, e2, e3, e4⟩ := solo_w1 hp hph
    exact Term.of_solo (term_fresh (by rw [e1]; exact hp) e2
      (by rw [e3, e4]; exact hI.m21.trans (le_max_left _ _)))
  · obtain ⟨e1, e2, e3, e4⟩ := solo_w2 hp hph
    have hl := hI.loc p
    rw [hph] at hl
    obtain ⟨-, s2, hs2⟩ := hl
    exact Term.of_solo (term_fresh (by rw [e1]; exact hp) e2
      (by rw [e3, e4]; exact max_le hI.m21 (hI.le_mem _ hs2).1))
  · exact term_fresh hp hph hI.m21

lemma term_after {C : Cfg n P} (hR : (alg n P).Reachable C) (hp : C.pend p ≠ none)
    {a b : Val n} (hph : C.loc p = afterScan a b) : Term p C := by
  unfold afterScan at hph
  split_ifs at hph
  · exact term_dw hR hp (Or.inl ⟨_, hph⟩)
  · exact term_dw hR hp (Or.inr (Or.inl ⟨_, hph⟩))
  · exact term_dw hR hp (Or.inr (Or.inr (Or.inl ⟨_, hph⟩)))

lemma term_r1 {C : Cfg n P} (hR : (alg n P).Reachable C) (hp : C.pend p ≠ none)
    {prev : Option (Val n × Val n)} (hph : C.loc p = .r1 prev) : Term p C := by
  cases prev with
  | none => exact term_dw hR hp (Or.inr (Or.inr (Or.inr hph)))
  | some ab =>
    refine Term.of_collect hp hph fun C1 hp1 hl1 hm1 hR1 => ?_
    have hp1' : C1.pend p ≠ none := by rw [hp1]; exact hp
    unfold next at hl1
    split_ifs at hl1 with he
    · exact term_after (hR1 hR) hp1' hl1
    · refine Term.of_collect hp1' hl1 fun C2 hp2 hl2 hm2 hR2 => ?_
      rw [hm1, next_some] at hl2
      exact term_after (hR2 (hR1 hR)) (by rw [hp2]; exact hp1') hl2

lemma term_r2 {C : Cfg n P} (hR : (alg n P).Reachable C) (hp : C.pend p ≠ none)
    {prev : Option (Val n × Val n)} {a : Val n} (hph : C.loc p = .r2 prev a) : Term p C := by
  obtain ⟨e1, e2, -⟩ := solo_r2 hp hph
  have hp1 : ((alg n P).soloStep p C).pend p ≠ none := by rw [e1]; exact hp
  refine Term.of_solo ?_
  unfold next at e2
  split_ifs at e2
  · exact term_after (hR.soloStep p) hp1 e2
  · exact term_r1 (hR.soloStep p) hp1 e2

/-- The algorithm is obstruction-free (CSLib's `Impl.ObstructionFree`: from every reachable
configuration, a pending process running solo returns). -/
theorem alg_obstructionFree : (alg n P).ObstructionFree := by
  intro C q hR hp
  obtain ⟨α, hα⟩ := hR
  obtain ⟨S, hI⟩ := inv_run hα
  show Term q C
  cases hph : C.loc q with
  | idle => exact absurd (hI.idle q hph).2 hp
  | done x => exact term_done hp hph
  | w1 v => exact term_dw ⟨α, hα⟩ hp (Or.inr (Or.inl ⟨v, hph⟩))
  | w2 v => exact term_dw ⟨α, hα⟩ hp (Or.inr (Or.inr (Or.inl ⟨v, hph⟩)))
  | r1 prev => exact term_r1 ⟨α, hα⟩ hp hph
  | r2 prev a => exact term_r2 ⟨α, hα⟩ hp hph

/-! ### The paper's encoding of `S` into `ℕ` -/

/-- The paper's encoding `(r, x) ↦ (x + 1)·yʳ`. -/
def encode (y : ℕ) (v : Val n) : ℕ := ((ofLex v).2.val + 1) * y ^ (ofLex v).1

/-- The paper's encoding is an order embedding of `ℕ ×ₗ Fin n` into `ℕ` as soon as `y > n`
(primality of `y` is not needed). Hence max-registers over `ℕ` can simulate max-registers over
`ℕ ×ₗ Fin n`. -/
lemma encode_strictMono {y : ℕ} (hy : n < y) : StrictMono (encode (n := n) y) := by
  intro a b hab
  rw [Prod.Lex.lt_iff] at hab
  unfold encode
  have hy0 : 0 < y := by have := NeZero.pos n; omega
  have ha : (ofLex a).2.val + 1 < y := by have := (ofLex a).2.isLt; omega
  rcases hab with h | ⟨h1, h2⟩
  · calc ((ofLex a).2.val + 1) * y ^ (ofLex a).1 < y * y ^ (ofLex a).1 :=
          Nat.mul_lt_mul_of_pos_right ha (pow_pos hy0 _)
      _ = y ^ ((ofLex a).1 + 1) := by ring
      _ ≤ y ^ (ofLex b).1 := Nat.pow_le_pow_right hy0 h
      _ ≤ ((ofLex b).2.val + 1) * y ^ (ofLex b).1 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  · rw [h1]
    exact Nat.mul_lt_mul_of_pos_right (by have := Fin.lt_def.1 h2; omega) (pow_pos hy0 _)

lemma encode_lt_encode_iff {y : ℕ} (hy : n < y) {a b : Val n} :
    encode y a < encode y b ↔ a < b := (encode_strictMono hy).lt_iff_lt

lemma encode_le_encode_iff {y : ℕ} (hy : n < y) {a b : Val n} :
    encode y a ≤ encode y b ↔ a ≤ b := (encode_strictMono hy).le_iff_le

end TwoMax

/-- **Theorem 4.2 of [EGSZ16]** (general form): for every `m ≥ 1` and every set of processes
`P` (of any size), obstruction-free `m`-valued consensus can be solved with two max-registers
over `ℕ ×ₗ Fin m` (lexicographic order), both initially `(0, 0)`. Agreement and validity hold in
every execution (`TwoMax.alg_safe`). -/
theorem theorem_4_2_general (m : ℕ) [NeZero m] (P : Type) [DecidableEq P] :
    ∃ (L : Type) (I : Impl (taskObj (Fin m) (Fin m)) (fun _ : Fin 2 => maxReg (ℕ ×ₗ Fin m)) P L),
      (∀ i, I.memInit i = toLex (0, 0)) ∧ (∀ p v, I.allowed p v) ∧
        I.Solves (consensus P (Fin m)) ∧ I.ObstructionFree :=
  ⟨TwoMax.Ph m, TwoMax.alg m P, fun _ => rfl, fun _ _ => trivial, TwoMax.alg_solves,
    TwoMax.alg_obstructionFree⟩

/-- **Theorem 4.2 of [EGSZ16]**: `n`-consensus (obstruction-free `n`-valued consensus among `n`
processes) can be solved using only two max-registers (over `ℕ ×ₗ Fin n`, lexicographically
ordered, both initially `(0, 0)`). -/
theorem theorem_4_2 (n : ℕ) [NeZero n] :
    ∃ (L : Type) (I : Impl (taskObj (Fin n) (Fin n)) (fun _ : Fin 2 => maxReg (ℕ ×ₗ Fin n))
      (Fin n) L),
      (∀ i, I.memInit i = toLex (0, 0)) ∧ (∀ p v, I.allowed p v) ∧
        I.Solves (consensus (Fin n) (Fin n)) ∧ I.ObstructionFree :=
  theorem_4_2_general n (Fin n)

end Cslib.SharedMemory.ComplexityHierarchy
