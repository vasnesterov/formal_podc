import Papers.PODC2015.ABADetection.Common

/-!
# Implementations from bounded writable CAS objects: definitions (Section 2.2)

All base objects are writable CAS objects `wcasObj V v₀` over one finite value type `V`
(registers and non-writable CAS objects are writable CAS objects on which the implementation
only uses `Read`/`Write`, respectively `Read`/`CAS`).

* `poisedAcc I C q` — the access (object, primitive) `q`'s next step performs, if any.
* `SOp s o` — `o` applied to an object with value `s` is a `Write` or a *successful* `CAS(x,y)`
  with `x ≠ y` (the paper assumes w.l.o.g. that `CAS(x,x)` is never used; we treat such a CAS
  as a read instead).
* `Succ I C β` — the schedule `β` (one step per process) is *successful* for `C` (paper:
  `P`-successful): every step is a `Write` or a successful `CAS`.
* `WCov I C R S`, `CCov I C R S` — the processes of `S` poised to `Write`, respectively to `CAS`,
  object `R` (paper: `WCov(C,R) ∩ S`, `CCov(C,R) ∩ S`).
* `Budget I C q t` — from `C`, `q` takes at most `t` steps before returning (paper: "in no
  execution starting from `C`, `q` executes more than `t` shared memory steps before finishing").
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}

/-- The access `q` is poised to perform next (ignoring whether `q` is pending). -/
def poisedAcc (I : Impl A (fun _ : ι => wcasObj V v₀) P L) (C : Config A (fun _ : ι => wcasObj V v₀) P L)
    (q : P) : Option (ι × WCasOp V) :=
  match I.act q (C.loc q) with
  | .access i o _ => some (i, o)
  | .ret _ _ => none

/-- A `Write`, or a successful `CAS(x,y)` with `x ≠ y`, on an object with value `s`. -/
def SOp (s : V) : WCasOp V → Prop
  | .write _ => True
  | .cas x y => x ≠ y ∧ s = x
  | .read => False

/-- The schedule `β` (each process takes one step, in order) is **successful** for `C`: every step
is a `Write` or a successful `CAS(x,y)` with `x ≠ y` (paper: `P`-successful schedule). -/
def Succ (I : Impl A (fun _ : ι => wcasObj V v₀) P L) :
    Config A (fun _ : ι => wcasObj V v₀) P L → List P → Prop
  | _, [] => True
  | C, p :: β => C.pend p ≠ none ∧ ∃ i o k C', I.act p (C.loc p) = .access i o k ∧
      SOp (C.mem i) o ∧ I.step C (.tau p) = some C' ∧ Succ I C' β

open Classical in
/-- The processes of `S` poised to `Write` object `R` in `C`. -/
noncomputable def WCov (I : Impl A (fun _ : ι => wcasObj V v₀) P L)
    (C : Config A (fun _ : ι => wcasObj V v₀) P L) (R : ι) (S : Finset P) : Finset P :=
  S.filter fun q => ∃ v, poisedAcc I C q = some (R, .write v)

open Classical in
/-- The processes of `S` poised to `CAS` object `R` in `C`. -/
noncomputable def CCov (I : Impl A (fun _ : ι => wcasObj V v₀) P L)
    (C : Config A (fun _ : ι => wcasObj V v₀) P L) (R : ι) (S : Finset P) : Finset P :=
  S.filter fun q => ∃ x y, poisedAcc I C q = some (R, .cas x y)

/-- From `C`, process `q` takes at most `t` steps in any execution in which it does not return. -/
def Budget (I : Impl A (fun _ : ι => wcasObj V v₀) P L)
    (C : Config A (fun _ : ι => wcasObj V v₀) P L) (q : P) (t : ℕ) : Prop :=
  ∀ δ C', I.runFrom C δ = some C' → (∀ ℓ ∈ δ, ℓ.proc = q → ℓ = .tau q) →
    δ.countP (Label.isTauOf q) ≤ t

/-! ### Basic lemmas -/

-- CSLib candidate: `Succ` and the lemmas below (successful one-step-per-process schedules on
-- CAS objects), together with `wcasObj` (SharedMemory/Objects).

variable {I : Impl A (fun _ : ι => wcasObj V v₀) P L}

lemma step_tau_eq {C : Config A (fun _ : ι => wcasObj V v₀) P L} {p : P} {i : ι} {o : WCasOp V}
    {k : Option V → L} (hp : C.pend p ≠ none) (hact : I.act p (C.loc p) = .access i o k) :
    I.step C (.tau p) = some { C with
      mem := Function.update C.mem i ((wcasObj V v₀).δ (C.mem i) o).1,
      loc := Function.update C.loc p (k ((wcasObj V v₀).δ (C.mem i) o).2) } := by
  simp [Impl.step, hp, hact]

lemma poisedAcc_eq_of_act {C : Config A (fun _ : ι => wcasObj V v₀) P L} {p : P} {i : ι}
    {o : WCasOp V} {k : Option V → L} (hact : I.act p (C.loc p) = .access i o k) :
    poisedAcc I C p = some (i, o) := by
  simp [poisedAcc, hact]

lemma poisedAcc_congr {C D : Config A (fun _ : ι => wcasObj V v₀) P L} {p : P}
    (h : C.loc p = D.loc p) : poisedAcc I C p = poisedAcc I D p := by
  simp [poisedAcc, h]

/-- A successful schedule can be run. -/
lemma Succ.run : ∀ {C : Config A (fun _ : ι => wcasObj V v₀) P L} {β : List P}, Succ I C β →
    ∃ C', I.runFrom C (Impl.blockWrite β) = some C'
  | _, [], _ => ⟨_, rfl⟩
  | _, p :: β, ⟨_, i, o, k, C', _, _, hs, h⟩ => by
    obtain ⟨D, hD⟩ := Succ.run h
    exact ⟨D, by simp [hs, hD]⟩

/-- Successful schedules of processes of `S` transfer along `S`-agreement. -/
lemma Succ.agreeOn {S : Set P} :
    ∀ {C D : Config A (fun _ : ι => wcasObj V v₀) P L} {β : List P}, Impl.AgreeOn S C D →
      (∀ p ∈ β, p ∈ S) → Succ I C β →
      Succ I D β ∧ ∃ C' D', I.runFrom C (Impl.blockWrite β) = some C' ∧
        I.runFrom D (Impl.blockWrite β) = some D' ∧ Impl.AgreeOn S C' D'
  | C, D, [], h, _, _ => ⟨trivial, C, D, rfl, rfl, h⟩
  | C, D, p :: β, h, hS, ⟨hp, i, o, k, C', hact, hso, hs, hβ⟩ => by
    have hpS := hS p List.mem_cons_self
    obtain ⟨D', hD', hag⟩ := Impl.step_agreeOn (ℓ := .tau p) h hpS hs
    obtain ⟨h1, C'', D'', h2, h3, h4⟩ := Succ.agreeOn hag (fun q hq => hS q
      (List.mem_cons_of_mem _ hq)) hβ
    refine ⟨⟨h.pend p hpS ▸ hp, i, o, k, D', by rw [← h.loc p hpS, hact],
      by rw [← h.mem]; exact hso, hD', h1⟩, C'', D'', by simp [hs, h2], by simp [hD', h3], h4⟩

/-- A successful schedule only depends on the memory and on the poised accesses of its
processes (paper, proof of Lemma 3: configurations with the same *signature*); the memories
after the schedule agree. -/
lemma Succ.congr :
    ∀ {C D : Config A (fun _ : ι => wcasObj V v₀) P L} {β : List P}, β.Nodup → C.mem = D.mem →
      (∀ p ∈ β, D.pend p ≠ none ∧ poisedAcc I C p = poisedAcc I D p) → Succ I C β →
      Succ I D β ∧ ∃ C' D', I.runFrom C (Impl.blockWrite β) = some C' ∧
        I.runFrom D (Impl.blockWrite β) = some D' ∧ C'.mem = D'.mem
  | C, D, [], _, hm, _, _ => ⟨trivial, C, D, rfl, rfl, hm⟩
  | C, D, p :: β, hnd, hm, hpa, ⟨hp, i, o, k, C', hact, hso, hs, hβ⟩ => by
    obtain ⟨hpD, hpa'⟩ := hpa p List.mem_cons_self
    rw [poisedAcc_eq_of_act hact] at hpa'
    obtain ⟨k', hact'⟩ : ∃ k', I.act p (D.loc p) = .access i o k' := by
      unfold poisedAcc at hpa'
      split at hpa'
      · rename_i i' o' k' h'
        simp only [Option.some.injEq, Prod.mk.injEq] at hpa'
        obtain ⟨rfl, rfl⟩ := hpa'
        exact ⟨k', h'⟩
      · simp at hpa'
    have hs' := step_tau_eq (I := I) hpD hact'
    rw [step_tau_eq hp hact] at hs
    cases hs
    have hpnot := (List.nodup_cons.1 hnd).1
    obtain ⟨h1, C'', D'', h2, h3, h4⟩ := Succ.congr (List.nodup_cons.1 hnd).2
      (D := { D with
        mem := Function.update D.mem i ((wcasObj V v₀).δ (D.mem i) o).1,
        loc := Function.update D.loc p (k' ((wcasObj V v₀).δ (D.mem i) o).2) })
      (by simp only [hm]) (fun q hq => by
        have hqp : q ≠ p := fun e => hpnot (e ▸ hq)
        obtain ⟨a, b⟩ := hpa q (List.mem_cons_of_mem _ hq)
        refine ⟨by simpa using a, ?_⟩
        simpa [poisedAcc, Function.update_of_ne hqp] using b) hβ
    exact ⟨⟨hpD, i, o, k', _, hact', by rw [← hm]; exact hso, hs', h1⟩, C'', D'',
      by simp [step_tau_eq hp hact, h2], by simp [hs', h3], h4⟩

/-- Appending one step to a successful schedule. -/
lemma succ_append_singleton {p : P} :
    ∀ {C C' : Config A (fun _ : ι => wcasObj V v₀) P L} {β : List P},
      Succ I C β → I.runFrom C (Impl.blockWrite β) = some C' → Succ I C' [p] →
      Succ I C (β ++ [p]) := by
  intro C C' β
  induction β generalizing C with
  | nil =>
    intro _ h hp
    simp only [Impl.blockWrite_nil, Impl.runFrom_nil, Option.some.injEq] at h
    subst h; simpa using hp
  | cons q β ih =>
    intro hs h hp
    obtain ⟨hq, i, o, k, C₁, hact, hso, hs1, hβ⟩ := hs
    simp only [Impl.blockWrite_cons, Impl.runFrom_cons, hs1, Option.bind_some] at h
    exact ⟨hq, i, o, k, C₁, hact, hso, hs1, ih hβ h hp⟩

/-- In a successful schedule, every process is pending and poised to `Write` or `CAS`. -/
lemma Succ.poised :
    ∀ {C : Config A (fun _ : ι => wcasObj V v₀) P L} {β : List P}, β.Nodup → Succ I C β →
      ∀ p ∈ β, C.pend p ≠ none ∧ ∃ R, (∃ v, poisedAcc I C p = some (R, .write v)) ∨
        (∃ x y, poisedAcc I C p = some (R, .cas x y))
  | _, [], _, _ => by simp
  | C, q :: β, hnd, ⟨hq, i, o, k, C₁, hact, hso, hs, hβ⟩ => by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · refine ⟨hq, i, ?_⟩
      rw [poisedAcc_eq_of_act hact]
      cases o with
      | read => exact absurd hso id
      | write v => exact Or.inl ⟨v, rfl⟩
      | cas x y => exact Or.inr ⟨x, y, rfl⟩
    · have hpq : p ≠ q := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hp)
      obtain ⟨h1, h2⟩ := Succ.poised (List.nodup_cons.1 hnd).2 hβ p hp
      have hl := Impl.step_other hs (q := p) (Ne.symm hpq)
      rw [← hl.2]
      refine ⟨h1, ?_⟩
      rwa [← poisedAcc_congr hl.1]

end Cslib.SharedMemory.ABADetection
