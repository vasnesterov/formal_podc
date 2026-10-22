import Podc.Computability.Distributed.SWMR.Basic
import Mathlib.Tactic

/-!
# Algorithm 1: wait-free two-process ε-agreement with 1-bit registers

Delporte-Gallet, Fauconnier, Fraigniaud, Rajsbaum, Travers, *The Computational Power of
Distributed Shared-Memory Models with Bounded-Size Registers*, PODC 2024, Section 5.1.

Processes are `Bool` (the other process of `p` is `!p`). Every process owns two registers,
indexed by `Bool`: `false` is the write-once input register `I` (`Option Bool`, initially `none`
= ⊥) and `true` is the 1-bit register `R` (`Bool`, initially `false` = 0). Outputs are
numerators `m : ℕ` standing for `m / (2k+1)`.

## Encoding

One step = one shared-memory access or the decision. Line 8 (`x_me ← I_me.read()`) is not a
step: the process keeps `x_me = myInput` in its local state. After deciding, a process keeps
reading its own register `R` (the model requires every step to be an action). Hence a process
takes at most `2k+3` steps before deciding: write `I`, `≤ k` iterations of (write `R`, read
`R_other`), read `I_other`, decide.

## Proof

The invariant `Inv` says that memory and outputs are functions of the local states and that the
pairwise invariant `Rel` holds: (F2) the number of completed iterations of a process is at most
the number of writes of the other one; (F4) the two processes never `break` in the same iteration
(Lemma 5.2); (F5) reading `⊥` from `I_other` only happens before completing an iteration. The
case analysis of Lemmas 5.1–5.5 is `outVal_agree`.

## Main statements

* `alg1_solves`: Proposition 5.1 (wait-free `1/(2k+1)`-agreement, `k ≥ 1`);
* `alg1_decides`: step bound `2k+3`;
* `alg1_lemma_5_6`: Lemma 5.6 (decisions `0`/`1` only by processes with that input);
* `alg1_mid`: intermediate decisions imply different inputs and a written `I_other`.
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

/-- Register types: `Alg1Reg false` is the write-once input register `I` (⊥ = `none`),
`Alg1Reg true` is the 1-bit register `R`. -/
abbrev Alg1Reg : Bool → Type
  | false => Option Bool
  | true => Bool

namespace Alg1

/-- Parity bit `r mod 2`. -/
def par (r : ℕ) : Bool := decide (r % 2 = 1)

/-- Program counter of Algorithm 1 (with the values of the relevant local variables).
* `start`: about to execute line 2 (`I_me.write(myInput)`);
* `wr r prec`: about to execute line 4 in iteration `r`;
* `rd r prec`: about to execute line 5 in iteration `r`;
* `rdI r new`: left the loop with the current values of `r` and `new`, about to execute line 9
  (read `I_other`);
* `dec r new xo`: read `x_other = xo`, about to return (lines 10–17);
* `done r new xo`: has returned (the local variables keep their values). -/
inductive PC
  | start
  | wr (r : ℕ) (prec : Bool)
  | rd (r : ℕ) (prec : Bool)
  | rdI (r : ℕ) (new : Bool)
  | dec (r : ℕ) (new : Bool) (xo : Option Bool)
  | done (r : ℕ) (new : Bool) (xo : Option Bool)
  deriving DecidableEq

/-- Local state: the input `x = myInput` (we keep `x_me = myInput` in the local state instead of
reading the own write-once register at line 8) and the program counter. -/
structure St where
  x : Bool
  pc : PC
  deriving DecidableEq

/-- Lines 6–7 and the loop control: after reading `new` in iteration `r` with previous value
`prec`, continue with iteration `r + 1` if `new ≠ prec` and `r < k`; otherwise leave the loop
(by `break` if `new = prec`, normally if `r = k`). -/
def afterRd (k r : ℕ) (prec new : Bool) : PC :=
  if new ≠ prec ∧ r < k then .wr (r + 1) new else .rdI r new

/-- Lines 10–17: the decision (numerator over `2k+1`) of a process with input `x`, final values
`r`, `new` of its loop variables, that read `xo` from the input register of the other process. -/
def outVal (k : ℕ) (x : Bool) (r : ℕ) (new : Bool) (xo : Option Bool) : ℕ :=
  match xo with
  | none => x.toNat * (2 * k + 1)
  | some xo =>
    if xo = x then x.toNat * (2 * k + 1)
    else if r = k ∧ new = par k then
      -- lines 12–14: `who := me` if `r` is even, `other` otherwise; return `(x_who + k)/(2k+1)`
      (if r % 2 = 0 then x else xo).toNat + k
    else
      -- lines 15–17: `who := other` if `r` is even, `me` otherwise;
      -- return `(x_who (2k+1) + (-1)^x_who (r-1))/(2k+1)`
      if (if r % 2 = 0 then xo else x) then 2 * k + 2 - r else r - 1

end Alg1

open Alg1

/-- Algorithm 1 (`A_k`), one shared-memory access (or decision) per step. After deciding, a
process keeps reading its own register `R` forever. -/
def alg1 (k : ℕ) : Alg Bool Bool Alg1Reg Bool ℕ where
  S := St
  v₀ := fun | false => (none : Option Bool) | true => false
  init _ x := ⟨x, .start⟩
  next p s := match s.pc with
    | .start => .write false (some s.x) ⟨s.x, .wr 1 false⟩
    | .wr r prec => .write true (par r) ⟨s.x, .rd r prec⟩
    | .rd r prec => .read (!p) true (fun new => ⟨s.x, afterRd k r prec new⟩)
    | .rdI r new => .read (!p) false (fun xo => ⟨s.x, .dec r new xo⟩)
    | .dec r new xo => .decide (outVal k s.x r new xo) ⟨s.x, .done r new xo⟩
    | .done _ _ _ => .read p true (fun _ => s)

namespace Alg1

/-! ### Abstract per-process quantities -/

namespace PC

/-- Number of writes to `R` performed so far (`R` holds `w mod 2`). -/
def w : PC → ℕ
  | start => 0
  | wr r _ => r - 1
  | rd r _ => r
  | rdI r _ => r
  | dec r _ _ => r
  | done r _ _ => r

/-- Number of completed iterations (iterations whose read returned `r mod 2`). -/
def c : PC → ℕ
  | start => 0
  | wr r _ => r - 1
  | rd r _ => r - 1
  | rdI r new => if new = par r then r else r - 1
  | dec r new _ => if new = par r then r else r - 1
  | done r new _ => if new = par r then r else r - 1

/-- The iteration in which the process left the loop by `break` (line 7), if any. -/
def broke : PC → Option ℕ
  | rdI r new => if new = par r then none else some r
  | dec r new _ => if new = par r then none else some r
  | done r new _ => if new = par r then none else some r
  | _ => none

/-- The value read from the other input register (line 9), if already read. -/
def xo : PC → Option (Option Bool)
  | dec _ _ xo => some xo
  | done _ _ xo => some xo
  | _ => none

/-- Local well-formedness. -/
def WF (k : ℕ) : PC → Prop
  | start => True
  | wr r prec => 1 ≤ r ∧ r ≤ k ∧ prec = par (r - 1)
  | rd r prec => 1 ≤ r ∧ r ≤ k ∧ prec = par (r - 1)
  | rdI r new => 1 ≤ r ∧ r ≤ k ∧ (new = par r → r = k)
  | dec r new _ => 1 ≤ r ∧ r ≤ k ∧ (new = par r → r = k)
  | done r new _ => 1 ≤ r ∧ r ≤ k ∧ (new = par r → r = k)

end PC

/-- Content of the input register `I` of a process in local state `t`. -/
def Ival (t : St) : Option Bool := match t.pc with
  | .start => none
  | _ => some t.x

/-- Content of the bit register `R` of a process in local state `t`. -/
def Rval (t : St) : Bool := par t.pc.w

/-- Output of a process in local state `s`. -/
def outOf (k : ℕ) (s : St) : Option ℕ := match s.pc with
  | .done r new xo => some (outVal k s.x r new xo)
  | _ => none

/-- The next local state of a process in state `s` whose partner is in state `t` (registers
hold `Ival`/`Rval` of the local states). -/
def nextSt (k : ℕ) (s t : St) : St := match s.pc with
  | .start => ⟨s.x, .wr 1 false⟩
  | .wr r prec => ⟨s.x, .rd r prec⟩
  | .rd r prec => ⟨s.x, afterRd k r prec (Rval t)⟩
  | .rdI r new => ⟨s.x, .dec r new (Ival t)⟩
  | .dec r new xo => ⟨s.x, .done r new xo⟩
  | .done _ _ _ => s

lemma par_eq_par {a b : ℕ} : par a = par b ↔ a % 2 = b % 2 := by
  unfold par; constructor <;> intro h
  · have := congrArg (· = true) h; simp at this; omega
  · have : a % 2 = 1 ↔ b % 2 = 1 := by omega
    simp [this]

@[simp] lemma nextSt_x (k : ℕ) (s t : St) : (nextSt k s t).x = s.x := by
  rcases s with ⟨x, _ | _ | _ | _ | _ | _⟩ <;> simp [nextSt, afterRd]

lemma w_le_nextSt (k : ℕ) (s t : St) : s.pc.w ≤ (nextSt k s t).pc.w := by
  rcases s with ⟨x, _ | _ | ⟨r, b⟩ | _ | _ | _⟩ <;> simp [nextSt, PC.w]
  unfold afterRd; split_ifs <;> simp

lemma nextSt_ne_start (k : ℕ) (s t : St) (h : s.pc ≠ .start) : (nextSt k s t).pc ≠ .start := by
  rcases s with ⟨x, _ | _ | _ | _ | _ | _⟩ <;> simp_all [nextSt, afterRd]
  split_ifs <;> simp

lemma PC.w_of_broke {pc : PC} {ρ : ℕ} (h : pc.broke = some ρ) : pc.w = ρ := by
  cases pc <;> simp_all [PC.broke, PC.w]

lemma Ival_cases (t : St) : (Ival t = some t.x ∧ t.pc ≠ .start) ∨ (Ival t = none ∧ t.pc = .start) := by
  rcases t with ⟨x, _ | _ | _ | _ | _ | _⟩ <;> simp [Ival]

/-- The pairwise invariant (process in state `s`, partner in state `t`); facts (F2)–(F5) of the
paper's proof. -/
structure Rel (k : ℕ) (s t : St) : Prop where
  /-- Local well-formedness. -/
  wf : s.pc.WF k
  /-- (F2) completed iterations are bounded by the partner's writes. -/
  cw : s.pc.c ≤ t.pc.w
  /-- (F4) the two processes never `break` in the same iteration (Lemma 5.2). -/
  broke : s.pc.broke = none ∨ s.pc.broke ≠ t.pc.broke
  /-- (F5) the value read from the other input register is its input (and then that register is
  written forever), or `⊥`, which only happens before completing an iteration. -/
  xo : ∀ xo, s.pc.xo = some xo → (xo = some t.x ∧ t.pc ≠ .start) ∨ (xo = none ∧ s.pc.c = 0)

lemma broke_symm {a b : Option ℕ} (h : a = none ∨ a ≠ b) : b = none ∨ b ≠ a := by
  rcases h with h | h
  · subst h; cases b <;> simp
  · exact Or.inr (Ne.symm h)

/-- Preservation of the pairwise invariant for the stepping process. -/
lemma rel_nextSt_left {k : ℕ} (hk : 1 ≤ k) (s t : St) (h1 : Rel k s t) (h2 : Rel k t s) :
    Rel k (nextSt k s t) t := by
  obtain ⟨wf, cw, br, xo⟩ := h1
  rcases s with ⟨x, _ | ⟨r, prec⟩ | ⟨r, prec⟩ | ⟨r, new⟩ | ⟨r, new, o⟩ | ⟨r, new, o⟩⟩
  · exact ⟨⟨le_rfl, hk, rfl⟩, by simp [nextSt, PC.c], by simp [nextSt, PC.broke],
      by simp [nextSt, PC.xo]⟩
  · simp only [PC.WF] at wf
    exact ⟨wf, by simpa [nextSt, PC.c] using cw, by simp [nextSt, PC.broke],
      by simp [nextSt, PC.xo]⟩
  · simp only [PC.WF] at wf
    obtain ⟨hr1, hrk, rfl⟩ := wf
    simp only [PC.c] at cw
    have hpr : par (r - 1) ≠ par r := by rw [Ne, par_eq_par]; omega
    simp only [nextSt, Rval]
    by_cases hc : par t.pc.w ≠ par (r - 1) ∧ r < k
    · have e : afterRd k r (par (r - 1)) (par t.pc.w) = .wr (r + 1) (par t.pc.w) := by
        simp [afterRd, hc]
      rw [e]
      have hpn : par t.pc.w = par r := by
        rcases Bool.eq_false_or_eq_true (par t.pc.w) with h | h <;>
        rcases Bool.eq_false_or_eq_true (par r) with h' | h' <;>
        rcases Bool.eq_false_or_eq_true (par (r-1)) with h'' | h'' <;> simp_all
      have := par_eq_par.1 hpn
      refine ⟨⟨by omega, by omega, by simpa using hpn⟩, ?_, by simp [PC.broke],
        by simp [PC.xo]⟩
      simp only [PC.c]; omega
    · have e : afterRd k r (par (r - 1)) (par t.pc.w) = .rdI r (par t.pc.w) := by
        simp only [afterRd, hc, ↓reduceIte]
      rw [e]
      refine ⟨⟨hr1, hrk, fun h => ?_⟩, ?_, ?_, by simp [PC.xo]⟩
      · by_contra hne
        exact hc ⟨by rw [h]; exact hpr.symm, by omega⟩
      · simp only [PC.c]
        split_ifs with h
        · have := par_eq_par.1 h; omega
        · omega
      · simp only [PC.broke]
        split_ifs with h
        · simp
        · right
          intro ht
          have := PC.w_of_broke ht.symm
          exact h (by rw [this])
  · simp only [PC.WF] at wf
    refine ⟨by simpa [nextSt, PC.WF] using wf, by simpa [nextSt, PC.c] using cw,
      by simpa [nextSt, PC.broke] using br, ?_⟩
    simp only [nextSt, PC.xo, Option.some.injEq, forall_eq']
    rcases Ival_cases t with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩
    · refine Or.inr ⟨h, ?_⟩
      simp only [PC.c] at cw ⊢; rw [h'] at cw; simpa [PC.w] using cw
  · exact ⟨by simpa [nextSt, PC.WF] using wf, by simpa [nextSt, PC.c] using cw,
      by simpa [nextSt, PC.broke] using br, by simpa [nextSt, PC.xo, PC.c] using xo⟩
  · exact ⟨wf, cw, br, xo⟩

/-- Preservation of the pairwise invariant for both processes. -/
lemma rel_nextSt {k : ℕ} (hk : 1 ≤ k) (s t : St) (h1 : Rel k s t) (h2 : Rel k t s) :
    Rel k (nextSt k s t) t ∧ Rel k t (nextSt k s t) := by
  have h := rel_nextSt_left hk s t h1 h2
  refine ⟨h, h2.wf, le_trans h2.cw (w_le_nextSt k s t), broke_symm h.broke, ?_⟩
  intro xo hxo
  rcases h2.xo xo hxo with ⟨h3, h4⟩ | h3
  · exact Or.inl ⟨by simpa using h3, nextSt_ne_start k s t h4⟩
  · exact Or.inr h3

/-! ### The global invariant -/

/-- The invariant of reachable configurations of `alg1 k` with input vector `x`: local inputs,
memory (F1) and outputs are determined by the local states, and the pairwise invariant holds. -/
structure Inv (k : ℕ) (x : Bool → Bool) (C : Config (alg1 k)) : Prop where
  inp : ∀ p, (C.loc p).x = x p
  memI : ∀ p, C.mem p false = Ival (C.loc p)
  memR : ∀ p, C.mem p true = Rval (C.loc p)
  out : ∀ p, C.out p = outOf k (C.loc p)
  rel : ∀ p, Rel k (C.loc p) (C.loc (!p))

lemma inv_init {k : ℕ} (x : Bool → Bool) : Inv k x ((alg1 k).initCfg x) where
  inp _ := rfl
  memI _ := rfl
  memR _ := rfl
  out _ := rfl
  rel _ := ⟨trivial, le_rfl, Or.inl rfl, by simp [alg1, Alg.initCfg, PC.xo]⟩

/-- The effect of one step of `p`, in terms of `nextSt`. -/
lemma step_spec {k : ℕ} {x : Bool → Bool} {C : Config (alg1 k)} (h : Inv k x C) (p : Bool) :
    ((alg1 k).step p C).loc p = nextSt k (C.loc p) (C.loc (!p)) ∧
    ((alg1 k).step p C).mem p false = Ival (nextSt k (C.loc p) (C.loc (!p))) ∧
    ((alg1 k).step p C).mem p true = Rval (nextSt k (C.loc p) (C.loc (!p))) ∧
    ((alg1 k).step p C).out p = outOf k (nextSt k (C.loc p) (C.loc (!p))) := by
  have hI := h.memI p
  have hR := h.memR p
  have hO := h.out p
  generalize hs : C.loc p = s at hI hR hO
  rcases s with ⟨sx, _ | ⟨r, prec⟩ | ⟨r, prec⟩ | ⟨r, new⟩ | ⟨r, new, o⟩ | ⟨r, new, o⟩⟩
  · have hn : (alg1 k).next p (C.loc p) = .write false (some sx) ⟨sx, .wr 1 false⟩ := by
      rw [hs]; rfl
    rw [Alg.step_of_write hn]
    refine ⟨(Function.update_self _ _ _).trans ?_, ?_, ?_, ?_⟩ <;>
      simp [nextSt, Ival, Rval, outOf, PC.w, hR, hO]
    rfl
  · have hn : (alg1 k).next p (C.loc p) = .write true (par r) ⟨sx, .rd r prec⟩ := by
      rw [hs]; rfl
    rw [Alg.step_of_write hn]
    refine ⟨(Function.update_self _ _ _).trans ?_, ?_, ?_, ?_⟩ <;>
      simp [nextSt, Ival, Rval, outOf, PC.w, hI, hO]
    rfl
  · have hn : (alg1 k).next p (C.loc p) =
        .read (!p) true (fun new => ⟨sx, afterRd k r prec new⟩) := by
      rw [hs]; rfl
    rw [Alg.step_of_read hn]
    refine ⟨(Function.update_self _ _ _).trans ?_, ?_, ?_, ?_⟩ <;>
      simp [nextSt, Ival, Rval, outOf, PC.w, hI, hR, hO, h.memR (!p)]
    · rfl
    all_goals unfold afterRd; split_ifs <;> simp
  · have hn : (alg1 k).next p (C.loc p) =
        .read (!p) false (fun xo => ⟨sx, .dec r new xo⟩) := by
      rw [hs]; rfl
    rw [Alg.step_of_read hn]
    refine ⟨(Function.update_self _ _ _).trans ?_, ?_, ?_, ?_⟩ <;>
      simp [nextSt, Ival, Rval, outOf, PC.w, hI, hR, hO, h.memI (!p)]
    rfl
  · have hn : (alg1 k).next p (C.loc p) =
        .decide (outVal k sx r new o) ⟨sx, .done r new o⟩ := by
      rw [hs]; rfl
    rw [Alg.step_of_decide hn]
    refine ⟨(Function.update_self _ _ _).trans ?_, ?_, ?_, ?_⟩ <;>
      simp [nextSt, Ival, Rval, outOf, PC.w, hI, hR, hO]
    rfl
  · have hn : (alg1 k).next p (C.loc p) =
        .read p true (fun _ => ⟨sx, .done r new o⟩) := by
      rw [hs]; rfl
    rw [Alg.step_of_read hn]
    refine ⟨(Function.update_self _ _ _).trans ?_, ?_, ?_, ?_⟩ <;>
      simp [nextSt, Ival, Rval, outOf, PC.w, hI, hR, hO]
    rfl

lemma inv_step {k : ℕ} (hk : 1 ≤ k) {x : Bool → Bool} {C : Config (alg1 k)} (h : Inv k x C)
    (p : Bool) : Inv k x ((alg1 k).step p C) := by
  obtain ⟨hl, hmI, hmR, hout⟩ := step_spec h p
  have hne : (!p) ≠ p := by cases p <;> decide
  have hlo : ((alg1 k).step p C).loc (!p) = C.loc (!p) := Alg.step_loc_ne C hne
  have hmo := Alg.step_mem_ne C hne
  have hoo := Alg.step_out_ne C hne
  have h2 := h.rel (!p)
  rw [Bool.not_not] at h2
  have hrel := rel_nextSt hk (C.loc p) (C.loc (!p)) (h.rel p) h2
  have key : ∀ q, q = p ∨ q = !p := by intro q; cases q <;> cases p <;> simp
  constructor
  · intro q; rcases key q with rfl | rfl
    · rw [hl]; exact (nextSt_x k _ _).trans (h.inp _)
    · rw [hlo, h.inp]
  · intro q; rcases key q with rfl | rfl
    · rw [hl]; exact hmI
    · rw [hmo, hlo]; exact h.memI _
  · intro q; rcases key q with rfl | rfl
    · rw [hl]; exact hmR
    · rw [hmo, hlo]; exact h.memR _
  · intro q; rcases key q with rfl | rfl
    · rw [hl]; exact hout
    · rw [hoo, hlo]; exact h.out _
  · intro q; rcases key q with rfl | rfl
    · rw [hl, hlo]; exact hrel.1
    · rw [Bool.not_not, hlo, hl]; exact hrel.2

lemma inv_run {k : ℕ} (hk : 1 ≤ k) {x : Bool → Bool} (σ : List Bool) :
    ∀ {C : Config (alg1 k)}, Inv k x C → Inv k x ((alg1 k).run C σ) := by
  induction σ with
  | nil => exact fun h => h
  | cons p σ ih => exact fun h => ih (inv_step hk h p)

/-- Every reachable configuration satisfies the invariant. -/
lemma inv_reachable {k : ℕ} (hk : 1 ≤ k) (x : Bool → Bool) (σ : List Bool) :
    Inv k x ((alg1 k).run ((alg1 k).initCfg x) σ) :=
  inv_run hk σ (inv_init x)

/-! ### Step bound -/

/-- Progress measure: a lower bound on the number of steps taken so far (exact before the
loop ends), `2k+3` once decided. -/
def pot (k : ℕ) : PC → ℕ
  | .start => 0
  | .wr r _ => 2 * r - 1
  | .rd r _ => 2 * r
  | .rdI _ _ => 2 * k + 1
  | .dec _ _ _ => 2 * k + 2
  | .done _ _ _ => 2 * k + 3

lemma pot_nextSt {k : ℕ} {s : St} (t : St) (hwf : s.pc.WF k) :
    min (pot k s.pc + 1) (2 * k + 3) ≤ pot k (nextSt k s t).pc := by
  rcases s with ⟨x, _ | ⟨r, b⟩ | ⟨r, b⟩ | _ | _ | _⟩ <;>
    simp only [PC.WF] at hwf <;> simp only [nextSt]
  · simp only [pot]; omega
  · simp only [pot]; omega
  · unfold afterRd; split_ifs <;> simp only [pot] <;> omega
  · simp only [pot]; omega
  · simp only [pot]; omega
  · simp only [pot]; omega

lemma pot_lt {k : ℕ} {pc : PC} (hwf : pc.WF k) (hd : ∀ r new xo, pc ≠ .done r new xo) :
    pot k pc < 2 * k + 3 := by
  cases pc <;> simp_all [PC.WF, pot] <;> omega

lemma run_pot {k : ℕ} (hk : 1 ≤ k) {x : Bool → Bool} (p : Bool) (σ : List Bool) :
    ∀ {C : Config (alg1 k)}, Inv k x C →
      min (pot k (C.loc p).pc + σ.count p) (2 * k + 3) ≤ pot k (((alg1 k).run C σ).loc p).pc := by
  induction σ with
  | nil => intro C _; simp
  | cons q σ ih =>
    intro C h
    have ih' := ih (inv_step hk h q)
    rw [Alg.run_cons]
    rw [List.count_cons]
    by_cases hq : q = p
    · subst hq
      have h1 := pot_nextSt (C.loc (!q)) (h.rel q).wf
      rw [(step_spec h q).1] at ih'
      simp only [beq_self_eq_true, ↓reduceIte] at *
      omega
    · have hne : p ≠ q := Ne.symm hq
      rw [Alg.step_loc_ne C hne] at ih'
      simp only [beq_iff_eq, hq, ↓reduceIte] at *
      omega

/-! ### Safety -/

lemma outVal_le {k r : ℕ} (x new : Bool) (xo : Option Bool) (h1 : 1 ≤ r) (h2 : r ≤ k) :
    outVal k x r new xo ≤ 2 * k + 1 := by
  rcases xo with _ | y <;> cases x <;> (try cases y) <;> simp only [outVal] <;> (try split_ifs) <;>
    simp_all <;> omega

lemma outVal_self {k r : ℕ} (x new : Bool) {xo : Option Bool} (h : xo = none ∨ xo = some x) :
    outVal k x r new xo = x.toNat * (2 * k + 1) := by
  rcases h with rfl | rfl <;> simp [outVal]

/-- Lemma 5.6: a decision of `0` (resp. `1`, i.e. numerator `2k+1`) is only taken by a process
with input `0` (resp. `1`). -/
lemma outVal_extreme {k r : ℕ} (hk : 1 ≤ k) (x new : Bool) (xo : Option Bool) (h1 : 1 ≤ r)
    (h2 : r ≤ k) :
    (outVal k x r new xo = 0 → x = false) ∧ (outVal k x r new xo = 2 * k + 1 → x = true) := by
  rcases xo with _ | y <;> cases x <;> (try cases y) <;> simp only [outVal] <;> (try split_ifs) <;>
    simp_all <;> omega

/-- Intermediate decisions (strictly between `0` and `1`) are only taken by a process that read
the other process' input, and that input differs from its own. -/
lemma outVal_mid {k r : ℕ} (x new : Bool) (xo : Option Bool)
    (h : 0 < outVal k x r new xo ∧ outVal k x r new xo < 2 * k + 1) : xo = some (!x) := by
  revert h
  unfold outVal
  rcases xo with _ | y <;> cases x <;> (try cases y) <;> simp

lemma par_eq_true {r : ℕ} : par r = true ↔ r % 2 = 1 := by simp [par]
lemma par_eq_false {r : ℕ} : par r = false ↔ r % 2 = 0 := by simp [par]
lemma true_eq_par {r : ℕ} : true = par r ↔ r % 2 = 1 := by rw [eq_comm, par_eq_true]
lemma false_eq_par {r : ℕ} : false = par r ↔ r % 2 = 0 := by rw [eq_comm, par_eq_false]

/-- The decision when the other input was read and differs from the own input. -/
lemma outVal_cross {k r : ℕ} {x new : Bool} (hwf : PC.WF k (.done r new none)) :
    outVal k x r new (some (!x)) =
      if new = par r then (if r % 2 = 0 then x else !x).toNat + k
      else if (if r % 2 = 0 then !x else x) then 2 * k + 2 - r else r - 1 := by
  simp only [PC.WF] at hwf
  obtain ⟨-, -, h3⟩ := hwf
  have e : (r = k ∧ new = par k) ↔ new = par r := by
    constructor
    · rintro ⟨rfl, h⟩; exact h
    · intro h; exact ⟨h3 h, by rw [← h3 h]; exact h⟩
  simp only [outVal, Bool.not_eq_eq_eq_not, Bool.eq_not_self, ite_false]
  simp only [e]

/-- Lemmas 5.1–5.5: the decisions of two processes that both decided differ by at most `1/(2k+1)`. -/
lemma outVal_agree {k : ℕ} {s t : St} (hs : Rel k s t) (ht : Rel k t s) {r r' : ℕ}
    {new new' : Bool} {xo xo' : Option Bool} (hsd : s.pc = .done r new xo)
    (htd : t.pc = .done r' new' xo') :
    outVal k s.x r new xo ≤ outVal k t.x r' new' xo' + 1 := by
  obtain ⟨wf1, cw1, b1, xo1⟩ := hs
  obtain ⟨wf2, cw2, b2, xo2⟩ := ht
  rcases s with ⟨x, pc⟩
  rcases t with ⟨y, pc'⟩
  simp only at hsd htd
  subst hsd htd
  simp only [PC.xo, Option.some.injEq, forall_eq'] at xo1 xo2
  by_cases hxy : y = x
  · subst hxy
    rw [outVal_self _ _ (by rcases xo1 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]),
      outVal_self _ _ (by rcases xo2 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])]
    dsimp only
    omega
  have hy : y = !x := by cases x <;> cases y <;> simp_all
  subst hy
  have wf1' : PC.WF k (.done r new none) := wf1
  have wf2' : PC.WF k (.done r' new' none) := wf2
  simp only [PC.WF, PC.c, PC.w, PC.broke] at wf1 wf2 cw1 cw2 b1 b2 xo1 xo2
  have e2 := outVal_cross (x := !x) wf2'
  rw [Bool.not_not] at e2
  have e1 := outVal_cross (x := x) wf1'
  clear wf1' wf2' hxy
  dsimp only
  rcases xo1 with ⟨rfl, -⟩ | ⟨rfl, h1⟩ <;> rcases xo2 with ⟨rfl, -⟩ | ⟨rfl, h2⟩
  · rw [e1, e2]
    clear e1 e2
    cases x <;> cases new <;> cases new' <;>
      simp only [true_eq_par, false_eq_par, Bool.not_true, Bool.not_false] at * <;>
      split_ifs at * <;> (try simp at *) <;> omega
  · rw [e1]; simp only [outVal]
    clear e1 e2
    cases x <;> cases new <;> cases new' <;>
      simp only [true_eq_par, false_eq_par, Bool.not_true, Bool.not_false] at * <;>
      split_ifs at * <;> (try simp at *) <;> omega
  · rw [e2]; simp only [outVal]
    clear e1 e2
    cases x <;> cases new <;> cases new' <;>
      simp only [true_eq_par, false_eq_par, Bool.not_true, Bool.not_false] at * <;>
      split_ifs at * <;> (try simp at *) <;> omega
  · -- both read `⊥`: impossible, both would have broken in iteration 1
    exfalso; clear e1 e2
    cases new <;> cases new' <;> simp only [true_eq_par, false_eq_par] at * <;>
      split_ifs at * <;>
      (try simp only [Option.some_ne_none, ne_eq, Option.some.injEq, not_true, false_or,
        or_false, reduceCtorEq] at *) <;> omega

/-! ### Main results -/

lemma out_eq_some {k : ℕ} {x : Bool → Bool} {C : Config (alg1 k)} (h : Inv k x C) {p : Bool}
    {m : ℕ} (hm : C.out p = some m) :
    ∃ r new xo, (C.loc p).pc = .done r new xo ∧ m = outVal k (x p) r new xo := by
  rw [h.out p] at hm
  have hx := h.inp p
  revert hm hx
  generalize (C.loc p : St) = s
  rcases s with ⟨sx, _ | _ | _ | _ | _ | ⟨r, new, xo⟩⟩ <;> intro hm hx <;> simp [outOf] at hm
  subst hx
  exact ⟨r, new, xo, rfl, hm.symm⟩

lemma Ival_of_ne_start {t : St} (h : t.pc ≠ .start) : Ival t = some t.x := by
  rcases Ival_cases t with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · exact absurd h2 h

lemma bool_eq_or_not (p q : Bool) : q = p ∨ q = !p := by cases p <;> cases q <;> simp

end Alg1

open Alg1

/-- Step bound: a process that has taken `2k+3` steps (write `I`, at most `k` iterations of two
accesses each, read the other `I`, decide) has decided. -/
theorem alg1_decides (k : ℕ) (hk : 1 ≤ k) (x : Bool → Bool) (σ : List Bool) (p : Bool)
    (hσ : 2 * k + 3 ≤ σ.count p) :
    (((alg1 k).run ((alg1 k).initCfg x) σ).out p).isSome := by
  have h := inv_reachable hk x σ
  have hp := run_pot hk p σ (inv_init x)
  have h0 : pot k (((alg1 k).initCfg x).loc p).pc = 0 := rfl
  rw [h0, zero_add] at hp
  rw [h.out p]
  by_contra hd
  have hwf := (h.rel p).wf
  have := pot_lt hwf (by
    intro r new xo he
    apply hd
    simp [outOf, he])
  have : min (σ.count p) (2 * k + 3) = 2 * k + 3 := by omega
  omega

/-- **Proposition 5.1** of [Delporte-Gallet et al., PODC 2024]: for every `k ≥ 1`, Algorithm 1
(`A_k`) solves `1/(2k+1)`-agreement wait-free for two processes (`t = 1`), using one 1-bit
register and one write-once input register per process. -/
theorem alg1_solves (k : ℕ) (hk : 1 ≤ k) : (alg1 k).Solves 1 (epsAgreement (2 * k + 1)) := by
  refine ⟨fun x σ => ?_, fun x σ _ p hp =>
    Alg.termination_of_bound _ (2 * k + 3) (fun x σ p h => alg1_decides k hk x σ p h) x σ p hp⟩
  have h := inv_reachable hk x σ
  refine ⟨?_, ?_, ?_⟩
  · intro p m hm
    obtain ⟨r, new, xo, hpc, rfl⟩ := out_eq_some h hm
    have hwf := (h.rel p).wf
    rw [hpc] at hwf
    exact outVal_le _ _ _ hwf.1 hwf.2.1
  · intro b hb p m hm
    obtain ⟨r, new, xo, hpc, rfl⟩ := out_eq_some h hm
    have hxo := (h.rel p).xo xo (by rw [hpc]; rfl)
    rw [outVal_self]
    · cases b <;> simp [hb]
    · rcases hxo with ⟨e, -⟩ | ⟨e, -⟩
      · right; rw [e, h.inp, hb, hb]
      · left; exact e
  · intro p q m m' hm hm'
    obtain ⟨r, new, xo, hpc, rfl⟩ := out_eq_some h hm
    obtain ⟨r', new', xo', hpc', rfl⟩ := out_eq_some h hm'
    rcases bool_eq_or_not p q with rfl | rfl
    · rw [hpc] at hpc'
      cases hpc'
      omega
    · have h2 := h.rel (!p)
      rw [Bool.not_not] at h2
      have := outVal_agree (h.rel p) h2 hpc hpc'
      rwa [h.inp, h.inp] at this

/-- **Lemma 5.6** of [Delporte-Gallet et al., PODC 2024]: a process deciding `0` has input `0`,
and a process deciding `1` (numerator `2k+1`) has input `1`. -/
theorem alg1_lemma_5_6 (k : ℕ) (hk : 1 ≤ k) (x : Bool → Bool) (σ : List Bool) (p : Bool) :
    (((alg1 k).run ((alg1 k).initCfg x) σ).out p = some 0 → x p = false) ∧
    (((alg1 k).run ((alg1 k).initCfg x) σ).out p = some (2 * k + 1) → x p = true) := by
  have h := inv_reachable hk x σ
  constructor <;> intro hm <;> obtain ⟨r, new, xo, hpc, hm⟩ := out_eq_some h hm <;>
    have hwf := (h.rel p).wf <;> rw [hpc] at hwf
  · exact (outVal_extreme hk (x p) new xo hwf.1 hwf.2.1).1 hm.symm
  · exact (outVal_extreme hk (x p) new xo hwf.1 hwf.2.1).2 hm.symm

/-- An intermediate decision `m/(2k+1)` with `0 < m < 2k+1` is only possible if the inputs
differ, and then the other process has already written its input register. -/
theorem alg1_mid (k : ℕ) (hk : 1 ≤ k) (x : Bool → Bool) (σ : List Bool) (i : Bool) {m : ℕ}
    (hm : ((alg1 k).run ((alg1 k).initCfg x) σ).out i = some m) (h0 : 0 < m)
    (h1 : m < 2 * k + 1) :
    x i ≠ x (!i) ∧ ((alg1 k).run ((alg1 k).initCfg x) σ).mem (!i) false = some (x (!i)) := by
  have h := inv_reachable hk x σ
  obtain ⟨r, new, xo, hpc, rfl⟩ := out_eq_some h hm
  have e := outVal_mid (x i) new xo ⟨h0, h1⟩
  have hxo := (h.rel i).xo xo (by rw [hpc]; rfl)
  rw [h.inp] at hxo
  rcases hxo with ⟨e', hst⟩ | ⟨e', -⟩
  · rw [e] at e'
    have e'' : x (!i) = !x i := (Option.some.inj e').symm
    refine ⟨by rw [e'']; cases x i <;> simp, ?_⟩
    rw [h.memI, Ival_of_ne_start hst, h.inp]
  · rw [e] at e'; cases e'

/-! ### Sanity checks -/

/-- `k = 2`, inputs `1` (process `true`) and `0`, lock-step schedule: both complete the loop and
decide at line 14, `3/5` and `2/5`. -/
example : ((alg1 2).run ((alg1 2).initCfg id) ((List.replicate 7 [true, false]).flatten)).out =
    fun p => if p then some 3 else some 2 := by
  funext p; cases p <;> decide

/-- `k = 3`: process `true` (input `1`) writes `I`, writes `R`, and reads `R_false = 0` before
`false` writes: it breaks in iteration 1. Then `false` (input `0`) runs alone: it breaks in
iteration 2 and decides `6/7` (line 17); finally `true` resumes and decides `1` (line 17, `r = 1`). -/
example : ((alg1 3).run ((alg1 3).initCfg id)
    (List.replicate 3 true ++ List.replicate 9 false ++ List.replicate 9 true)).out =
    fun p => if p then some 7 else some 6 := by
  funext p; cases p <;> decide

end Podc.BoundedRegisterPower
