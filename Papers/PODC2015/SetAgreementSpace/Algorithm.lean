import Papers.PODC2015.SetAgreementSpace.Defs

/-!
# The algorithm of Figure 3 (one-shot `m`-obstruction-free `k`-set agreement)

`n` processes `Fin n` share one snapshot object `A` with `r` components holding `⊥` or a pair
`(value, id)` (the paper takes `r = n + 2m - k`). Code for process `id` (Figure 3):

```
Propose(v):
  pref ← v; i ← 0
  loop
    update A[i] with (pref, id)
    s ← scan of A
    if |{s[j]}| ≤ m and ∀ j, s[j] ≠ ⊥ then                                       (line 9)
      j₁ ← min {j₁ : ∃ j₂ > j₁, s[j₁] = s[j₂]}; output value in s[j₁] and halt     (line 10)
    if ∀ j ≠ i, s[j] ∉ {⊥, (pref, id)} and ∃ j₁ ≠ j₂, s[j₁] = s[j₂] then           (line 11)
      j₁ ← min {j₁ : ∃ j₂ > j₁, s[j₁] = s[j₂]}; pref ← value in s[j₁]             (lines 12–13)
    else i ← (i + 1) mod r                                                        (line 14)
```

`fig3 fix n m r` is this algorithm as a CSLib `Impl`. With `fix = false` it is exactly Figure 3;
with `fix = true` the adoption branch (lines 11–13) is additionally guarded by
"the value in `s[j₁]` differs from `pref`" — otherwise the process advances `i` (line 14). The
original algorithm is not obstruction-free (`Counterexample.lean`); the guarded one is
(`Liveness.lean`), and both are safe (`Safety.lean`).

Local state: program counter (`idle`, `upd` = about to update, `scan` = about to scan,
`ret` = decided, about to return), `pref`, `i`, and the decided value `out`.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

/-- Program counter of a process. -/
inductive PC where
  | idle
  | upd
  | scan
  | ret
  deriving DecidableEq

/-- Local state of a process. -/
structure Loc (V : Type) (r : ℕ) where
  /-- Program counter. -/
  pc : PC
  /-- Preferred value. -/
  pref : V
  /-- Next component to update. -/
  i : Fin r
  /-- Decided value (set when deciding, kept afterwards). -/
  out : Option V

variable {V : Type} [DecidableEq V] [Inhabited V] {n r : ℕ}

/-- A component's content: `⊥` or a pair (value, process id). -/
abbrev Cell (V : Type) (n : ℕ) := Option (V × Fin n)

/-- The base objects: a single snapshot object (`ι = Unit`). -/
abbrev Mem (V : Type) (n r : ℕ) : Unit → ObjSpec := fun _ => snapObjOpt r (V × Fin n)

/-- `j₁` is the first component of a duplicated pair: `s[j₁] = s[j₂]` for some `j₂ > j₁`. -/
def IsDup (s : Fin r → Cell V n) (j₁ : Fin r) : Prop := ∃ j₂, j₁ < j₂ ∧ s j₂ = s j₁

instance (s : Fin r → Cell V n) (j₁ : Fin r) : Decidable (IsDup s j₁) := by
  unfold IsDup; infer_instance

/-- `min {j₁ : ∃ j₂ > j₁, s[j₁] = s[j₂]}` (`none` if there is no duplicated pair). -/
def firstDup (s : Fin r → Cell V n) : Option (Fin r) :=
  (List.finRange r).find? (fun j => decide (IsDup s j))

/-- The value of the first duplicated pair (`none` if there is none or it is `⊥`). -/
def dupVal (s : Fin r → Cell V n) : Option V :=
  (firstDup s).bind fun j => (s j).map Prod.fst

/-- Line 9: at most `m` distinct pairs and no `⊥`. -/
def DecideCond (m : ℕ) (s : Fin r → Cell V n) : Prop :=
  (Finset.univ.image s).card ≤ m ∧ ∀ j, s j ≠ none

instance (m : ℕ) (s : Fin r → Cell V n) : Decidable (DecideCond m s) := by
  unfold DecideCond; infer_instance

/-- Line 11 (with `fix`: and the value of the first duplicated pair is not `pref`). -/
def AdoptCond (fix : Bool) (s : Fin r → Cell V n) (i : Fin r) (pref : V) (id : Fin n) : Prop :=
  (∀ j, j ≠ i → s j ≠ none ∧ s j ≠ some (pref, id)) ∧ (∃ j₁ j₂, j₁ ≠ j₂ ∧ s j₁ = s j₂) ∧
    (fix = true → dupVal s ≠ some pref)

instance (fix : Bool) (s : Fin r → Cell V n) (i : Fin r) (pref : V) (id : Fin n) :
    Decidable (AdoptCond fix s i pref id) := by
  unfold AdoptCond; infer_instance

/-- The local state after the scan returning `s` (lines 9–14). -/
def afterScan [NeZero r] (fix : Bool) (m : ℕ) (id : Fin n) (l : Loc V r)
    (s : Fin r → Cell V n) : Loc V r :=
  if DecideCond m s then { l with pc := .ret, out := some ((dupVal s).getD l.pref) }
  else if AdoptCond fix s l.i l.pref id then { l with pc := .upd, pref := (dupVal s).getD l.pref }
  else { l with pc := .upd, i := l.i + 1 }

/-- **Figure 3** as an implementation of `k`-set agreement from one `r`-component snapshot,
for processes `Fin n`, decision threshold `m`; `fix = true` adds the guard described above. -/
def fig3 (fix : Bool) (n m r : ℕ) [NeZero r] :
    Impl (saObj V) (Mem V n r) (Fin n) (Loc V r) where
  memInit _ := fun _ => none
  locInit _ := ⟨.idle, default, 0, none⟩
  invoke _ _ v := ⟨.upd, v, 0, none⟩
  act id l := match l.pc with
    | .upd => .access () (.update l.i (l.pref, id)) (fun _ => { l with pc := .scan })
    | .scan => .access () .scan (fun s => afterScan fix m id l s)
    | .ret => .ret (l.out.getD default) { l with pc := .idle }
    | .idle => .ret (default : V) l

end Podc.SetAgreementSpace
