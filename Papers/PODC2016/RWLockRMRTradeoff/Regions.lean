import Papers.PODC2016.RWLockRMRTradeoff.Model

/-!
# Regions of processes along executions, and the reader-writer lock properties

Helper lemmas on CSLib's `regionOf` (the remainder / entry / CS / exit bookkeeping of the
`lock(); CS; unlock()` client pattern) and the definitions of the properties of Section 2.1 of the
paper: Mutual Exclusion, Bounded Exit, Concurrent Entering (Deadlock Freedom is CSLib's
`Impl.DeadlockFree`), and the RMR complexities of the writer's entry and the reader's exit
sections.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

section RegionFold

variable {P : Type} [DecidableEq P]

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Mutex.lean
/-- The region of `p` after the labels `l`, starting from region `r`. -/
def regFold (r : Option Region) (l : List (Label P mutexObj)) (p : P) : Option Region :=
  l.foldl (fun r ℓ => if ℓ.proc = p then r.bind (fun r => r.next ℓ) else r) r

lemma regionOf_eq_regFold (α : List (Label P mutexObj)) (p : P) :
    regionOf α p = regFold (some .rem) α p := rfl

@[simp] lemma regFold_nil (r : Option Region) (p : P) : regFold r [] p = r := rfl

lemma regFold_cons (r : Option Region) (ℓ : Label P mutexObj) (l : List (Label P mutexObj))
    (p : P) : regFold r (ℓ :: l) p =
      regFold (if ℓ.proc = p then r.bind (fun r => r.next ℓ) else r) l p := rfl

lemma regFold_append (r : Option Region) (l₁ l₂ : List (Label P mutexObj)) (p : P) :
    regFold r (l₁ ++ l₂) p = regFold (regFold r l₁ p) l₂ p := by
  simp [regFold, List.foldl_append]

lemma regionOf_append (α β : List (Label P mutexObj)) (p : P) :
    regionOf (α ++ β) p = regFold (regionOf α p) β p := regFold_append _ _ _ _

@[simp] lemma regFold_none (l : List (Label P mutexObj)) (p : P) : regFold none l p = none := by
  induction l with
  | nil => rfl
  | cons ℓ l ih => rw [regFold_cons]; split_ifs <;> simpa using ih

lemma regFold_filter (r : Option Region) (l : List (Label P mutexObj)) (p : P) :
    regFold r (l.filter (fun ℓ => decide (ℓ.proc = p))) p = regFold r l p := by
  induction l generalizing r with
  | nil => rfl
  | cons ℓ l ih =>
    by_cases h : ℓ.proc = p
    · simp [List.filter_cons, h, regFold_cons, ih]
    · simp [List.filter_cons, h, regFold_cons, ih]

lemma regFold_of_forall_ne (r : Option Region) (l : List (Label P mutexObj)) (p : P)
    (h : ∀ ℓ ∈ l, ℓ.proc ≠ p) : regFold r l p = r := by
  induction l generalizing r with
  | nil => rfl
  | cons ℓ l ih =>
    rw [regFold_cons, if_neg (h ℓ List.mem_cons_self)]
    exact ih r (fun ℓ' h' => h ℓ' (List.mem_cons_of_mem _ h'))

lemma regFold_ne_none_of_prefix {r : Option Region} {l₁ l₂ : List (Label P mutexObj)} {p : P}
    (hp : l₁ <+: l₂) (h : regFold r l₂ p ≠ none) : regFold r l₁ p ≠ none := by
  obtain ⟨t, rfl⟩ := hp
  rw [regFold_append] at h
  intro h'; rw [h'] at h; simp at h

/-- Region of `p` after labels of `p` that are all internal steps. -/
lemma regFold_taus (r : Option Region) (l : List (Label P mutexObj)) (p : P)
    (h : ∀ ℓ ∈ l, ℓ.proc = p → ∃ q, ℓ = .tau q) : regFold r l p = r := by
  induction l generalizing r with
  | nil => rfl
  | cons ℓ l ih =>
    rw [regFold_cons]
    have ih' := fun r => ih r (fun ℓ' h' => h ℓ' (List.mem_cons_of_mem _ h'))
    split_ifs with hp
    · obtain ⟨q, rfl⟩ := h ℓ List.mem_cons_self hp
      cases r with
      | none => simp
      | some r => simpa [Region.next] using ih' (some r)
    · exact ih' r

end RegionFold

/-! ### Counting internal steps -/

section Count

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- Whether a label is an internal step of `p`. -/
def isTauOf (p : P) : Label P A → Bool
  | .tau q => decide (q = p)
  | _ => false

/-- Number of internal steps of `p` in `β`. -/
def tauCount (p : P) (β : List (Label P A)) : ℕ := β.countP (isTauOf p)

/-- `p` returns from an operation during `β`. -/
def Returns (p : P) (β : List (Label P A)) : Prop := ∃ r, Label.ret p r ∈ β

@[simp] lemma tauCount_nil (p : P) : tauCount p ([] : List (Label P A)) = 0 := rfl

lemma tauCount_append (p : P) (β γ : List (Label P A)) :
    tauCount p (β ++ γ) = tauCount p β + tauCount p γ := List.countP_append ..

end Count

/-! ### The reader-writer lock properties (Section 2.1) -/

section Properties

variable {n m : ℕ} {ι V L : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable (I : RWAlg n m ι V v₀ L)

/-- **Mutual Exclusion**: in every (client well-formed) execution, if a writer is in the CS then
no other process is in the CS. -/
def RWMutualExclusion : Prop :=
  ∀ α, I.Valid α → ClientWF α → ∀ j q, InCS α (.inr j) → InCS α q → q = .inr j

/-- **Bounded Exit**: an exit section, once started, completes within a bounded number of steps of
the exiting process (the bound may depend on the configuration where the exit section starts;
this is weaker than a uniform bound). -/
def BoundedExit : Prop :=
  ∀ α p, I.Valid α → ClientWF α → regionOf α p = some .exiting →
    ∃ B, ∀ β, I.Valid (α ++ β) → ¬ Returns p β → tauCount p β ≤ B

/-- **Concurrent Entering**: if all writers are in the remainder section and no writer takes
steps, a reader in its entry section enters the CS within a bounded number of its own steps (the
bound may depend on the configuration). -/
def ConcurrentEntering : Prop :=
  ∀ α i, I.Valid α → ClientWF α → (∀ j, regionOf α (.inr j) = some .rem) →
    regionOf α (.inl i) = some .trying →
    ∃ b, ∀ β, I.Valid (α ++ β) → (∀ ℓ ∈ β, ℓ.proc.isLeft) → ¬ Returns (.inl i) β →
      tauCount (.inl i) β ≤ b

variable (cm : CacheModel (Proc n m) ι)

/-- The RMR complexity of the writers' entry section is at most `Wb`: in every execution
`α ++ β` where writer `j` is in the remainder section after `α` and does not start its exit
section during `β`, `j` incurs at most `Wb` RMRs during `β`. -/
def WriterEntryRMR (Wb : ℕ) : Prop :=
  ∀ α β (X Y : Ext I cm) j, xrun (Ext.init I cm) α = some X → xrun X β = some Y →
    ClientWF (α ++ β) → regionOf α (.inr j) = some .rem →
    (∀ ℓ ∈ β, ℓ ≠ .inv (.inr j) .unlock) → xcount (RMRBy (.inr j)) X β ≤ Wb

/-- The RMR complexity of the readers' exit section is at most `Rb`: in every execution
`α ++ β` where reader `i` is in the CS after `α` and does not start a new entry section during
`β`, `i` incurs at most `Rb` RMRs during `β`. -/
def ReaderExitRMR (Rb : ℕ) : Prop :=
  ∀ α β (X Y : Ext I cm) i, xrun (Ext.init I cm) α = some X → xrun X β = some Y →
    ClientWF (α ++ β) → regionOf α (.inl i) = some .cs →
    (∀ ℓ ∈ β, ℓ ≠ .inv (.inl i) .lock) → xcount (RMRBy (.inl i)) X β ≤ Rb

end Properties

end Podc.RWLockRMRTradeoff
