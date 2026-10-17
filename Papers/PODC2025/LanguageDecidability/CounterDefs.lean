import Papers.PODC2025.LanguageDecidability.Classes

/-!
# Eventually consistent counters (Example 3, Definitions 2.7, 2.8) and the algorithm of Figure 5

Alphabet (Example 3): `Σᵢ< = {<ᵢ⁺ (inc), <ᵢ (read)}`, `Σᵢ> = {>ᵢ (ack), >ᵢˣ (value x)}`.

Positions in an ω-word: the response at position `r` of process `p` belongs to the operation whose
invocation is the last symbol of `p` before `r` (`x` is well-formed).

* `Typed x` — every operation is `inc : ack` or `read : val v` (the paper's languages are about
  counter histories, so ill-typed operations are not in them).
* `WEC1` — (1) every `read` of `p` returns at least the number of `inc`s of `p` before it.
* `WEC2` — (2) every `read` of `p` returns at least the value of every earlier `read` of `p`.
* `WEC3` — (3), *intended reading*: finitely many `inc`s, and eventually every `read` returns
  their number.
* `WEC3lit` — (3), *literal reading*: "for every finite prefix `α` such that the suffix `β` has
  only `read` operations, eventually all operations in `β` return the number of `inc` operations
  in `α`": vacuous if there are infinitely many `inc`s.
* `SEC4` — (4) every `read` returns at most the number of `inc`s that precede or are concurrent
  to it, i.e. whose invocation is before the `read`'s response.
* `WEC`, `WEClit`, `SEC` — the languages `WEC_COUNT` (both readings) and `SEC_COUNT`.
* `fig5Alg` — the algorithm of Figure 5, literally; `wecAlg` — the corrected algorithm: the
  safety check of the second clause of Line 06 is made only for `read` operations, and ill-typed
  operations also set the flag.
-/

namespace Podc2025.LanguageDecidability.Counter

open Podc2025.LanguageDecidability

/-- Counter invocations. -/
inductive CInv
  | inc
  | read
  deriving DecidableEq

/-- Counter responses. -/
inductive CRes
  | ack
  | val (v : ℕ)
  deriving DecidableEq

variable {n : ℕ}

/-- Counter ω-words. -/
abbrev CWord (n : ℕ) := Word (n := n) (fun _ => CInv) (fun _ => CRes)

/-- Symbols of the counter alphabet. -/
abbrev CSym (n : ℕ) := Sym (n := n) (fun _ => CInv) (fun _ => CRes)

/-- The symbol is an invocation of `inc`. -/
def IsInc (a : CSym n) : Prop := a.2 = .inl .inc

instance (a : CSym n) : Decidable (IsInc a) := inferInstanceAs (Decidable (a.2 = _))

/-- Number of `inc` invocations among the first `k` symbols. -/
def incs (x : CWord n) : ℕ → ℕ
  | 0 => 0
  | k + 1 => incs x k + if IsInc (x k) then 1 else 0

/-- Number of `inc` invocations of `p` among the first `k` symbols. -/
def ownIncs (x : CWord n) (p : Fin n) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ownIncs x p k + if IsInc (x k) ∧ (x k).1 = p then 1 else 0

/-- `invAt x r i`: position `i` holds the invocation of the operation whose response is at `r`
(the last symbol of the same process before `r`). -/
def invAt (x : CWord n) (r i : ℕ) : Prop :=
  i < r ∧ (x i).1 = (x r).1 ∧ ∀ m, i < m → m < r → (x m).1 ≠ (x r).1

/-- Every operation is `inc : ack` or `read : val v`. -/
def Typed (x : CWord n) : Prop :=
  ∀ r i p (w : CRes), x r = ⟨p, .inr w⟩ → invAt x r i →
    (x i = ⟨p, .inl .inc⟩ ∧ w = .ack) ∨ (x i = ⟨p, .inl .read⟩ ∧ ∃ v, w = .val v)

/-- Property (1). -/
def WEC1 (x : CWord n) : Prop := ∀ r p v, x r = ⟨p, .inr (.val v)⟩ → ownIncs x p r ≤ v

/-- Property (2). -/
def WEC2 (x : CWord n) : Prop :=
  ∀ r r' p v v', r' < r → x r' = ⟨p, .inr (.val v')⟩ → x r = ⟨p, .inr (.val v)⟩ → v' ≤ v

/-- Finitely many `inc` invocations: `S` is their number and none occurs at or after `N`. -/
def FinIncs (x : CWord n) (S : ℕ) : Prop := ∃ N, incs x N = S ∧ ∀ m, N ≤ m → ¬ IsInc (x m)

/-- Eventually every `read` returns `S`. -/
def EvReads (x : CWord n) (S : ℕ) : Prop := ∃ N, ∀ r p v, N ≤ r → x r = ⟨p, .inr (.val v)⟩ → v = S

/-- Property (3), intended reading. -/
def WEC3 (x : CWord n) : Prop := ∃ S, FinIncs x S ∧ EvReads x S

/-- Property (3), literal reading. -/
def WEC3lit (x : CWord n) : Prop := ∀ S, FinIncs x S → EvReads x S

/-- Property (4). -/
def SEC4 (x : CWord n) : Prop := ∀ r p v, x r = ⟨p, .inr (.val v)⟩ → v ≤ incs x r

/-- **Definition 2.7** (`WEC_COUNT`), intended reading of property (3). -/
def WEC : Set (CWord n) := {x | WF x ∧ Typed x ∧ WEC1 x ∧ WEC2 x ∧ WEC3 x}

/-- **Definition 2.7** (`WEC_COUNT`), literal reading of property (3). -/
def WEClit : Set (CWord n) := {x | WF x ∧ Typed x ∧ WEC1 x ∧ WEC2 x ∧ WEC3lit x}

/-- **Definition 2.8** (`SEC_COUNT`), with the intended reading of property (3). -/
def SEC : Set (CWord n) := {x | x ∈ WEC ∧ SEC4 x}

lemma WEC3.lit {x : CWord n} (h : WEC3 x) : WEC3lit x := by
  obtain ⟨S, ⟨N, hN, hinc⟩, hev⟩ := h
  intro S' ⟨N', hN', hinc'⟩
  have : incs x N = incs x N' := by
    have key : ∀ a b, a ≤ b → (∀ m, a ≤ m → ¬ IsInc (x m)) → incs x b = incs x a := by
      intro a b hab ha
      induction hab with
      | refl => rfl
      | step hle ih => simp [incs, ih, ha _ hle]
    rcases le_total N N' with h | h
    · exact (key N N' h hinc).symm
    · exact key N' N h hinc'
  rw [← hN', ← this, hN]; exact hev

lemma WEC_subset_WEClit : (WEC : Set (CWord n)) ⊆ WEClit :=
  fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5.lit⟩

lemma isDistLang_WEC : IsDistLang (WEC : Set (CWord n)) := fun _ h => h.1
lemma isDistLang_WEClit : IsDistLang (WEClit : Set (CWord n)) := fun _ h => h.1
lemma isDistLang_SEC : IsDistLang (SEC : Set (CWord n)) := fun _ h => h.1.1

/-! ### The algorithm of Figure 5 -/

/-- Local variables of Figure 5 (plus the invocation of the current iteration). -/
structure Loc where
  prevRead : ℕ := 0
  prevIncs : ℕ := 0
  count : ℕ := 0
  flag : Bool := false
  currRead : ℕ := 0
  inv : CInv := .read

/-- Lines 01–02 of Figure 5: announce increments in `INCS[i]`. -/
def pre5 (_t : ℕ) (p : Fin n) (l : Loc) (v : CInv) (m : Fin n → ℕ) : Loc × (Fin n → ℕ) :=
  match v with
  | .inc => ({ l with count := l.count + 1, inv := .inc }, Function.update m p (l.count + 1))
  | .read => ({ l with inv := .read }, m)

/-- Lines 05–06 of Figure 5, literally. -/
def post5 (_t : ℕ) (p : Fin n) (l : Loc) (w : CRes) (m : Fin n → ℕ) :
    Loc × (Fin n → ℕ) × Verdict :=
  let currIncs := ∑ j, m j
  let currRead := match w with
    | .val r => r
    | .ack => l.currRead
  let l' : Loc := { l with currRead := currRead, prevRead := currRead, prevIncs := currIncs }
  if l.flag then (l', m, .no)
  else if currRead < m p ∨ currRead < l.prevRead then ({ l' with flag := true }, m, .no)
  else if currRead ≠ currIncs ∨ l.prevIncs < currIncs then (l', m, .no)
  else (l', m, .yes)

/-- The algorithm of Figure 5 as written. -/
def fig5Alg : Alg n (fun _ => CInv) (fun _ => CRes) Verdict where
  L := Loc
  M := Fin n → ℕ
  m0 := fun _ => 0
  l0 := fun _ => {}
  pre := pre5
  post := post5

/-- The operation is ill-typed. -/
def illTyped (v : CInv) (w : CRes) : Bool :=
  match v, w with
  | .inc, .val _ => true
  | .read, .ack => true
  | _, _ => false

/-- Lines 05–06 of Figure 5, corrected: the second clause only applies to `read` operations,
and an ill-typed operation also sets the flag. -/
def postFix (_t : ℕ) (p : Fin n) (l : Loc) (w : CRes) (m : Fin n → ℕ) :
    Loc × (Fin n → ℕ) × Verdict :=
  let currIncs := ∑ j, m j
  let currRead := match w with
    | .val r => r
    | .ack => l.currRead
  let isRead := match w with
    | .val _ => true
    | .ack => false
  let l' : Loc := { l with currRead := currRead, prevRead := currRead, prevIncs := currIncs }
  if l.flag then (l', m, .no)
  else if illTyped l.inv w = true ∨ (isRead = true ∧ (currRead < m p ∨ currRead < l.prevRead)) then
    ({ l' with flag := true }, m, .no)
  else if currRead ≠ currIncs ∨ l.prevIncs < currIncs then (l', m, .no)
  else (l', m, .yes)

/-- The corrected algorithm for Lemma 5.3. -/
def wecAlg : Alg n (fun _ => CInv) (fun _ => CRes) Verdict where
  L := Loc
  M := Fin n → ℕ
  m0 := fun _ => 0
  l0 := fun _ => {}
  pre := pre5
  post := postFix

end Podc2025.LanguageDecidability.Counter
