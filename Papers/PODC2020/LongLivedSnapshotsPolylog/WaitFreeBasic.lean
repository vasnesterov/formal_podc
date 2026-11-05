import Papers.PODC2020.LongLivedSnapshotsPolylog.BoundedIncrement

/-!
# Wait-freedom of Algorithm 1: basic facts

Monotonicity of the max registers and timestamps, the invariant `H[j].ts = ts_j`, and the
per-step consequence of Definition 2.1 used in Lemma 3.4.
-/

namespace Podc.LongLivedSnapshotsPolylog.WaitFree

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

variable {n m X : ℕ}

/-- Configurations of Algorithm 1. -/
abbrev Cfg (n : ℕ) := Config maxArrObj (objSpec n) (Fin n) (Loc n)

/-- Labels of executions of Algorithm 1. -/
abbrev Lbl (n : ℕ) := Label (Fin n) maxArrObj

/-- The value of `MR_left`. -/
def mrL (C : Cfg n) : ℕ := C.mem .mrL

/-- The value of `MR_right`. -/
def mrR (C : Cfg n) : ℕ := C.mem .mrR

/-- The persistent timestamp of process `k` (equal to `H[k].ts`, `help_fst`). -/
def tsOf (C : Cfg n) (k : Fin n) : ℕ := (C.loc k).ts

lemma invoke_ts (p : Fin n) (l : Loc n) (o : MAOp) : ((alg1 n m X).invoke p l o).ts = l.ts := by
  cases o <;> rfl

/-- Response steps keep the timestamp. -/
lemma act_ret_ts {p : Fin n} {l l' : Loc n} {r : ℕ × ℕ}
    (h : (alg1 n m X).act p l = .ret r l') : l'.ts = l.ts := by
  simp only [act] at h
  split at h <;> first | (split at h <;> cases h) | cases h <;> rfl

/-- One step does not decrease the max registers and the timestamps. -/
lemma step_mono {C C' : Cfg n} {ℓ : Lbl n} (h : (alg1 n m X).step C ℓ = some C') :
    mrL C ≤ mrL C' ∧ mrR C ≤ mrR C' ∧ ∀ k, tsOf C k ≤ tsOf C' k := by
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, hl, hm⟩ := Impl.step_inv h
    refine ⟨by simp [mrL, hm], by simp [mrR, hm], fun k => ?_⟩
    simp only [tsOf, hl]
    by_cases hk : k = p
    · subst hk; cases o <;> simp
    · simp [Function.update_of_ne hk]
  | ret p r =>
    obtain ⟨-, -, hm, l, hact, hl⟩ := Impl.step_ret h
    refine ⟨by simp [mrL, hm], by simp [mrR, hm], fun k => ?_⟩
    simp only [tsOf, hl]
    by_cases hk : k = p
    · subst hk; simp [act_ret_ts hact]
    · simp [Function.update_of_ne hk]
  | tau p =>
    rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ | ⟨cs, first, k, acc⟩ | r
    all_goals simp [Impl.step, act, hpc] at h
    all_goals obtain ⟨-, rfl⟩ := h
    all_goals refine ⟨?_, ?_, fun k' => ?_⟩
    all_goals simp [mrL, mrR, tsOf]
    all_goals by_cases hk : k' = p
    all_goals first | (subst hk; simp) | simp [Function.update_of_ne hk]

/-- Monotonicity along an execution fragment. -/
lemma runFrom_mono {C C' : Cfg n} {γ : List (Lbl n)}
    (h : (alg1 n m X).runFrom C γ = some C') :
    mrL C ≤ mrL C' ∧ mrR C ≤ mrR C' ∧ ∀ k, tsOf C k ≤ tsOf C' k := by
  induction γ generalizing C with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; simp
  | cons ℓ γ ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg1 n m X).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨a1, a2, a3⟩ := step_mono hs
      obtain ⟨b1, b2, b3⟩ := ih h
      exact ⟨a1.trans b1, a2.trans b2, fun k => (a3 k).trans (b3 k)⟩

/-- Monotonicity between a prefix and the whole execution. -/
lemma run_mono_of_prefix {β α : List (Lbl n)} {C₁ C : Cfg n} (hp : β <+: α)
    (h₁ : (alg1 n m X).run β = some C₁) (h : (alg1 n m X).run α = some C) :
    mrL C₁ ≤ mrL C ∧ mrR C₁ ≤ mrR C ∧ ∀ k, tsOf C₁ k ≤ tsOf C k := by
  obtain ⟨γ, rfl⟩ := hp
  rw [Impl.run, Impl.runFrom_append] at h
  rw [Impl.run] at h₁
  rw [h₁, Option.bind_some] at h
  exact runFrom_mono h

/-- The basic configuration invariant: `H[k].ts = ts_k`, and idle processes are at `idle`. -/
def Basic (C : Cfg n) : Prop :=
  (∀ k, (C.mem (.help k)).1 = tsOf C k) ∧ (∀ k, C.pend k = none → (C.loc k).pc = .idle)

lemma basic_step {C C' : Cfg n} {ℓ : Lbl n} (hC : Basic C)
    (h : (alg1 n m X).step C ℓ = some C') : Basic C' := by
  obtain ⟨hH, hI⟩ := hC
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, hpe, hl, hm⟩ := Impl.step_inv h
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · simp only [hm, hH k, tsOf, hl]
      by_cases hk : k = p
      · subst hk; cases o <;> simp
      · simp [Function.update_of_ne hk]
    · have hkp : k ≠ p := by rintro rfl; simp [hpe] at hk
      rw [hpe, Function.update_of_ne hkp] at hk
      simp only [hl, Function.update_of_ne hkp]; exact hI k hk
  | ret p r =>
    obtain ⟨-, hpe, hm, l, hact, hl⟩ := Impl.step_ret h
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · simp only [hm, hH k, tsOf, hl]
      by_cases hk : k = p
      · subst hk; simp [act_ret_ts hact]
      · simp [Function.update_of_ne hk]
    · by_cases hkp : k = p
      · subst hkp
        simp only [hl, Function.update_self]
        simp only [act] at hact
        split at hact <;> first | (split at hact <;> cases hact) |
          (cases hact <;> first | assumption | rfl)
      · rw [hpe, Function.update_of_ne hkp] at hk
        simp only [hl, Function.update_of_ne hkp]; exact hI k hk
  | tau p =>
    have hpe := (Impl.step_tau h).2.1
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
        ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
        ⟨cs, first, j, acc⟩ | r
      all_goals simp [Impl.step, act, hpc] at h
      all_goals obtain ⟨-, rfl⟩ := h
      all_goals have hk' := hH k
      all_goals simp only [tsOf] at hk' ⊢
      all_goals by_cases hk : k = p
      all_goals first | (subst hk; simp [hk']) | simp [hk, hk']
    · have hkp : k ≠ p := by
        rintro rfl; exact (Impl.step_tau h).1 (by rw [← hpe]; exact hk)
      rw [hpe] at hk
      simp only [(Impl.step_other h (q := k) (by simpa [Label.proc] using hkp.symm)).1]
      exact hI k hk

lemma basic_run {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) : Basic C :=
  Impl.invariant_of_run (I := alg1 n m X) (Inv := Basic)
    ⟨fun _ => rfl, fun _ _ => rfl⟩ (fun _ _ _ hC hs => basic_step hC hs) h

/-! ### Write logs -/

section Log

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
variable {κ : Type}

lemma wlogFrom_append (I : Impl A B P L) (w : P → L → Option (κ × ℕ))
    {C C' : Config A B P L} {α : List (Label P A)} (h : I.runFrom C α = some C')
    (β : List (Label P A)) :
    wlogFrom I w C (α ++ β) = wlogFrom I w C α ++ wlogFrom I w C' β := by
  induction α generalizing C with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; simp [wlogFrom]
  | cons x α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C x with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      simp only [List.cons_append, wlogFrom, hs, ih h, List.append_assoc]

/-- The log entry of one step. -/
def wstep (w : P → L → Option (κ × ℕ)) (C : Config A B P L) : Label P A → List (κ × ℕ)
  | .tau p => (w p (C.loc p)).toList
  | _ => []

lemma wlogFrom_singleton (I : Impl A B P L) (w : P → L → Option (κ × ℕ))
    {C C' : Config A B P L} {x : Label P A} (h : I.step C x = some C') :
    wlogFrom I w C [x] = wstep w C x := by
  cases x <;> simp only [wlogFrom, h] <;> simp [wstep]

end Log

/-- The value of the max register of side `s` (`false`: left, `true`: right). -/
def mrS (s : Bool) (C : Cfg n) : ℕ := match s with
  | false => mrL C
  | true => mrR C

/-- The max registers hold the maximum of the values written to them. -/
lemma mrS_eq_lmax {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) (s : Bool) :
    mrS s C = lmax (writesTo (alg1 n m X) wm1 α s) := by
  refine Impl.run_induction (I := alg1 n m X)
    (Q := fun α C => ∀ s, mrS s C = lmax (writesTo (alg1 n m X) wm1 α s))
    (fun s => by cases s <;> rfl) (fun α C x C' hα ih hs s => ?_) h s
  have hw : writesTo (alg1 n m X) wm1 (α ++ [x]) s = writesTo (alg1 n m X) wm1 α s ++
      (wlogFrom (alg1 n m X) wm1 C [x]).filterMap
        (fun e => if e.1 = s then some e.2 else none) := by
    simp [writesTo, wlogFrom_append _ _ hα]
  rw [hw, lmax_append, wlogFrom_singleton _ _ hs, ← ih s]
  cases x with
  | inv p o =>
    obtain ⟨-, -, -, -, hm⟩ := Impl.step_inv hs
    cases s <;> simp [mrS, mrL, mrR, hm, wstep]
  | ret p r =>
    obtain ⟨-, -, hm, -⟩ := Impl.step_ret hs
    cases s <;> simp [mrS, mrL, mrR, hm, wstep]
  | tau p =>
    rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, first, j, acc⟩ | r
    all_goals simp [Impl.step, act, hpc] at hs
    all_goals obtain ⟨-, rfl⟩ := hs
    all_goals cases s <;> simp [mrS, mrL, mrR, wm1, hpc, wstep]

lemma writesTo_append {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C)
    (β : List (Lbl n)) (s : Bool) :
    writesTo (alg1 n m X) wm1 (α ++ β) s = writesTo (alg1 n m X) wm1 α s ++
      (wlogFrom (alg1 n m X) wm1 C β).filterMap (fun e => if e.1 = s then some e.2 else none) := by
  simp [writesTo, wlogFrom_append _ _ h]

/-- **Definition 2.1, one step**: in an `ℓ`-bounded-increment execution, a `WriteMax(v)` on
`MR_s` performed at a configuration `C` writes at most `MR_s + ℓ`. -/
lemma bi_step {ℓ : ℕ} {α β : List (Lbl n)} {Cα : Cfg n} (hα : (alg1 n m X).run α = some Cα)
    (hBI : BIExec n m X ℓ α) {p : Fin n}
    (hpre : β ++ [.tau p] <+: α) {C : Cfg n} (hβ : (alg1 n m X).run β = some C) {s : Bool}
    {v : ℕ} (hpc : (C.loc p).pc = .wm s v) : v ≤ mrS s C + ℓ := by
  obtain ⟨C', hC'⟩ := Impl.valid_of_prefix (I := alg1 n m X) ⟨Cα, hα⟩ hpre
  have hs : (alg1 n m X).step C (.tau p) = some C' := by
    rw [Impl.run_concat, hβ, Option.bind_some] at hC'; exact hC'
  have h1 : writesTo (alg1 n m X) wm1 (β ++ [.tau p]) s = writesTo (alg1 n m X) wm1 β s ++ [v] := by
    rw [writesTo_append hβ, wlogFrom_singleton _ _ hs]
    simp [wstep, wm1, hpc]
  obtain ⟨γ, rfl⟩ := hpre
  have h2 := writesTo_append hC' γ s
  rw [h1] at h2
  have hsb := stepBounded_of_boundedIncr (hBI s)
  set ws := writesTo (alg1 n m X) wm1 β s
  have hi : ws.length < (writesTo (alg1 n m X) wm1 (β ++ [.tau p] ++ γ) s).length := by
    rw [h2]; simp
  have := hsb ws.length hi
  have e1 : (writesTo (alg1 n m X) wm1 (β ++ [.tau p] ++ γ) s)[ws.length] = v := by
    simp only [h2]; simp
  have e2 : (writesTo (alg1 n m X) wm1 (β ++ [.tau p] ++ γ) s).take ws.length = ws := by
    simp only [h2]; simp
  rw [e1, e2] at this
  rw [mrS_eq_lmax hβ]; exact this

end Podc.LongLivedSnapshotsPolylog.WaitFree
