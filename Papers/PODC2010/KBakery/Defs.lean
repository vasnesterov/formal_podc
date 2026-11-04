import Papers.PODC2010.KBakery.Basic

/-!
# Invariant definitions for the k-Bakery

The central notion is `Safe s q v r`: process `q` does not have priority over the pair
`(v, r)` (ticket `v` of process `r`), *now and until `q` chooses its next ticket*: `q` is in the
NCS, at line 14 or in the exit protocol (its next ticket will be read after `Ticket[r] ≥ v`), at
line 15 with a prospective ticket `> v`, or it holds a ticket with `(v, r) < (Ticket[q], q)`.
`U s v r` is the set of processes that are not safe for `(v, r)`.

This replaces the interval reasoning of the paper (Lemma 3, Claims 3.1–3.2 and the
"CS-qualified" induction of the thesis' Lemma 5.14) by inductive invariants:
* `s1`: a process `p` in the waiting loop only removed safe processes from its predecessor set;
* `s3`: a captured process was captured with a pair `(v, r)`, `v > Ticket[p]`, for which fewer than
  `k` processes are unsafe;
* `s4`: a process past the loop has fewer than `k` unsafe processes;
* `s5`: every capture value `Capture[r][x]` was written by `r` past its loop.
`U s v r` can only shrink as long as `v ≤ Ticket[r]`.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]

/-- `q` does not have priority over `(v, r)` until it chooses its next ticket. -/
def Safe (s : Cfg P) (q : P) (v : ℕ) (r : P) : Prop :=
  match s.pc q with
  | .ncs | .d14 _ | .ex _ => True
  | .d15 acc rem => v ≤ acc ∨ ∃ j ∈ rem, v ≤ s.ticket j
  | _ => lexLt v r (s.ticket q) q

open Classical in
/-- The processes other than `r` that are not safe for `(v, r)`. -/
noncomputable def U (s : Cfg P) (v : ℕ) (r : P) : Finset P :=
  univ.filter fun q => q ≠ r ∧ ¬ Safe s q v r

lemma mem_U {s : Cfg P} {v : ℕ} {r q : P} : q ∈ U s v r ↔ q ≠ r ∧ ¬ Safe s q v r := by
  classical
  simp [U]

/-- Consistency of `Want[q][p]` with the location of `q`. -/
def WantSpec (s : Cfg P) (q p : P) : Prop :=
  match s.pc q with
  | .ncs => s.want q p = ⊤
  | .d14 rem => if p ∈ rem then s.want q p = ⊤ else s.want q p = s.ticket q
  | .d15 _ _ => s.want q p = s.ticket q
  | .d16 rem => if p ∈ rem then s.want q p < s.ticket q else s.want q p = s.ticket q
  | .ex rem => if p ∈ rem then s.want q p = s.ticket q else s.want q p = ⊤
  | _ => s.want q p = s.ticket q

/-- Predecessor set of a process in the waiting loop. -/
def PC.pred : PC P → Finset P
  | .head pred _ | .scan pred _ | .chk pred _ _ => pred
  | _ => ∅

/-- Lines 19–22 (the waiting loop). -/
def PC.InLoop : PC P → Prop
  | .head _ _ | .scan _ _ | .chk _ _ _ => True
  | _ => False

/-- Lines 16–22 (holding the new ticket, before line 23). -/
def PC.PreCap : PC P → Prop
  | .d16 _ | .head _ _ | .scan _ _ | .chk _ _ _ => True
  | _ => False

/-- `captured = true`. -/
def PC.Captured : PC P → Prop
  | .head _ true | .chk _ _ true => True
  | _ => False

/-- Past the waiting loop ("CS-qualified"): line 23 or the CS. -/
def PC.Qual : PC P → Prop
  | .cap23 _ | .cs => True
  | _ => False

instance (c : PC P) : Decidable c.Qual := by unfold PC.Qual; split <;> infer_instance
instance (c : PC P) : Decidable c.InLoop := by unfold PC.InLoop; split <;> infer_instance

/-- The inductive invariant. -/
structure Inv (k : ℕ) (s : Cfg P) : Prop where
  g1 : ∀ q acc rem, s.pc q = .d15 acc rem → q ∉ rem → s.ticket q ≤ acc
  wantC : ∀ q p, q ≠ p → WantSpec s q p
  capLe : ∀ r x, s.capture r x ≤ s.ticket r
  capLt : ∀ p, (s.pc p).PreCap → ∀ x, s.capture p x < s.ticket p
  predNot : ∀ p, p ∉ (s.pc p).pred
  scanNot : ∀ p pred rem, s.pc p = .scan pred rem → p ∉ rem
  s1 : ∀ p, (s.pc p).InLoop → ∀ q, q ≠ p → q ∉ (s.pc p).pred → Safe s q (s.ticket p) p
  s3 : ∀ p, (s.pc p).Captured →
    ∃ v r, r ≠ p ∧ s.ticket p < v ∧ v ≤ s.ticket r ∧ (U s v r).card < k
  s4 : ∀ p, (s.pc p).Qual → (U s (s.ticket p) p).card < k
  s5 : ∀ r x, 0 < s.capture r x → (U s (s.capture r x) r).card < k

end Podc.KBakery
