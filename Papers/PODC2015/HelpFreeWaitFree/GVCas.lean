import Papers.PODC2015.HelpFreeWaitFree.GVClaims
import Papers.PODC2015.HelpFreeWaitFree.Theorem43

/-!
# The critical steps of Figure 4.2 (Claims 4.6.8–4.6.12 of [CPT15], repaired)

In the setting of `GVClaims.lean`:

* `Str.append_*` — the structure `Str` is preserved by the steps of the programs.
* `mem_ne_of_db` — a step of `p₁` or `p₂` that decides its operation before a view changes the
  memory (otherwise `p₃` could not tell the difference, `kl`).
* `loc_of_decides` — such a step accesses the location accessed by `p₃`'s next step, if `p₃`'s
  step prevents it from deciding (Claim 4.6.8 (1)).
* `caseA` — **Claim 4.6.8 / Corollary 4.4** (line 16 true): the next steps of `p₁` and `p₂` are
  successful `cas` on the same location.
* `race` — the same conclusion in the situation that the paper's Claim 4.6.12 overlooks (line 16
  false, but the step of `p_k` decides `op_k` before the *next* view); `bbad` provides its
  hypothesis.
* `cas_move` — lines 17–20 and 26–27: `p₂`'s `cas` succeeds, `p₁`'s fails, `p₂` and `p₃` complete
  their operations; the main-loop invariant holds for the next modifier and view, and `p₁` took a
  step (Claims 4.6.9, 4.6.13).
* `good_move` — lines 24–27 when the step of `p_k` decides nothing (Claims 4.6.10–4.6.13).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {P L : Type} [DecidableEq P]

lemma labOf_eq_of_agree {B : ι → ObjSpec} (I : Impl A B P L) {C D : Config A B P L} {p : P}
    (hl : D.loc p = C.loc p) (hp : D.pend p = C.pend p) (o : A.Op) :
    labOf I D p o = labOf I C p o := by
  unfold labOf Impl.nextLabel; rw [hl, hp]

lemma labOf_eq_tau {B : ι → ObjSpec} {I : Impl A B P L} {C : Config A B P L} {p : P} {i : ι}
    {o : (B i).Op} {k : (B i).Resp → L} (hp : C.pend p ≠ none)
    (hact : I.act p (C.loc p) = .access i o k) (o' : A.Op) : labOf I C p o' = .tau p := by
  unfold labOf Impl.nextLabel; simp [hp, hact]

lemma run_snoc {B : ι → ObjSpec} {I : Impl A B P L} {h : List (Label P A)} {C C' : Config A B P L}
    {γ : Label P A} (hC : I.run h = some C) (hs : I.step C γ = some C') :
    I.run (h ++ [γ]) = some C' := by
  rw [I.run_concat, hC]; exact hs

lemma step_of_run_snoc {B : ι → ObjSpec} {I : Impl A B P L} {h : List (Label P A)}
    {C C' : Config A B P L} {γ : Label P A} (hC : I.run h = some C)
    (hs : I.run (h ++ [γ]) = some C') : I.step C γ = some C' := by
  rw [I.run_concat, hC] at hs; exact hs

namespace Ctx

section Generic

variable {B : ι → ObjSpec} {I : Impl A B P L} (X : Ctx I)

/-! ### Preservation of `Str` -/

lemma Str.append_noinv {i j : ℕ} {h u : List (Label P A)} (hs : X.Str i j h)
    (hv : I.Valid (h ++ u)) (hu : ∀ q, opsOf u q = []) : X.Str i j (h ++ u) := by
  refine ⟨hv, ?_, ?_, ?_, ?_, ?_, fun k hk => (hs.prec k hk).mono⟩
  · rw [opsOf_append, hu, List.append_nil]; exact hs.ops1
  · rw [opsOf_append, hu, List.append_nil]; exact hs.ops2
  · rw [opsOf_append, hu, List.append_nil]; exact hs.ops3
  · have := hs.resp3; simp only [respsOf_append, List.length_append]; omega
  · intro q h1 h2 h3; rw [opsOf_append, hu, List.append_nil]; exact hs.other q h1 h2 h3

lemma opsOf_tau_list {l : List (Label P A)} (hl : ∀ γ ∈ l, ∃ p, γ = .tau p) (q : P) :
    opsOf l q = [] := by
  simp only [opsOf, List.filterMap_eq_nil_iff]
  intro γ hγ; obtain ⟨p, rfl⟩ := hl γ hγ; rfl

lemma Str.append_lab1 {i j : ℕ} {h : List (Label P A)} {C C' : Config A B P L}
    (hs : X.Str i j h) (hC : I.run h = some C) (hr : respsOf h X.p₁ = [])
    (hst : I.step C (labOf I C X.p₁ X.op) = some C') : X.Str i j (h ++ [labOf I C X.p₁ X.op]) := by
  have hv : I.Valid (h ++ [labOf I C X.p₁ X.op]) := ⟨C', run_snoc hC hst⟩
  have hne : ∀ q, q ≠ X.p₁ → opsOf (h ++ [labOf I C X.p₁ X.op]) q = opsOf h q := fun q hq => by
    rw [opsOf_concat, invOf_labOf]; simp [Ne.symm hq]
  refine ⟨hv, ?_, by rw [hne _ X.h12.symm]; exact hs.ops2, by rw [hne _ X.h13.symm]; exact hs.ops3,
    ?_, fun q h1 h2 h3 => by rw [hne q h1]; exact hs.other q h1 h2 h3, fun k hk => (hs.prec k hk).mono⟩
  · rw [opsOf_concat, invOf_labOf]
    by_cases hp : C.pend X.p₁ = none
    · have hl := I.run_idle_counts hC hp
      rw [hr] at hl
      simp [List.eq_nil_of_length_eq_zero hl, hp]
    · simp only [hp, false_and, ↓reduceIte, Option.toList_none, List.append_nil]; exact hs.ops1
  · have := hs.resp3; simp only [respsOf_append, List.length_append]; omega

lemma Str.append_lab2 {i j : ℕ} {h : List (Label P A)} {C C' : Config A B P L}
    (hs : X.Str i j h) (hC : I.run h = some C) (hr : (respsOf h X.p₂).length = i)
    (hst : I.step C (labOf I C X.p₂ (X.W i)) = some C') :
    X.Str i j (h ++ [labOf I C X.p₂ (X.W i)]) := by
  have hv : I.Valid (h ++ [labOf I C X.p₂ (X.W i)]) := ⟨C', run_snoc hC hst⟩
  have hne : ∀ q, q ≠ X.p₂ → opsOf (h ++ [labOf I C X.p₂ (X.W i)]) q = opsOf h q := fun q hq => by
    rw [opsOf_concat, invOf_labOf]; simp [Ne.symm hq]
  refine ⟨hv, by rw [hne _ X.h12]; exact hs.ops1, ?_, by rw [hne _ X.h23.symm]; exact hs.ops3,
    ?_, fun q h1 h2 h3 => by rw [hne q h2]; exact hs.other q h1 h2 h3, fun k hk => (hs.prec k hk).mono⟩
  · rw [opsOf_concat, invOf_labOf]
    by_cases hp : C.pend X.p₂ = none
    · have hl := I.run_idle_counts hC hp
      rw [hr] at hl
      have : opsOf h X.p₂ = pre X.W i := by
        rcases hs.ops2 with e | e
        · exact e
        · rw [e] at hl; simp [pre] at hl
      right; simp [this, hp, pre_succ']
    · simp only [hp, false_and, ↓reduceIte, Option.toList_none, List.append_nil]; exact hs.ops2
  · have := hs.resp3; simp only [respsOf_append, List.length_append]; omega

lemma Str.append_lab3 {i j : ℕ} {h : List (Label P A)} {C C' : Config A B P L}
    (hs : X.Str i j h) (hC : I.run h = some C) (hr : (respsOf h X.p₃).length = j)
    (hst : I.step C (labOf I C X.p₃ (X.R j)) = some C') :
    X.Str i j (h ++ [labOf I C X.p₃ (X.R j)]) := by
  have hv : I.Valid (h ++ [labOf I C X.p₃ (X.R j)]) := ⟨C', run_snoc hC hst⟩
  have hne : ∀ q, q ≠ X.p₃ → opsOf (h ++ [labOf I C X.p₃ (X.R j)]) q = opsOf h q := fun q hq => by
    rw [opsOf_concat, invOf_labOf]; simp [Ne.symm hq]
  refine ⟨hv, by rw [hne _ X.h13]; exact hs.ops1, by rw [hne _ X.h23]; exact hs.ops2, ?_,
    ?_, fun q h1 h2 h3 => by rw [hne q h3]; exact hs.other q h1 h2 h3, fun k hk => (hs.prec k hk).mono⟩
  · rw [opsOf_concat, invOf_labOf]
    by_cases hp : C.pend X.p₃ = none
    · have hl := I.run_idle_counts hC hp
      rw [hr] at hl
      have : opsOf h X.p₃ = pre X.R j := by
        rcases hs.ops3 with e | e
        · exact e
        · rw [e] at hl; simp [pre] at hl
      right; simp [this, hp, pre_succ']
    · simp only [hp, false_and, ↓reduceIte, Option.toList_none, List.append_nil]; exact hs.ops3
  · have := hs.resp3; simp only [respsOf_append, List.length_append]; omega

/-! ### Steps that decide change the memory -/

/-- A step of `p₁` or `p₂` after which `op₁` (or `(p₂, i)`) is decided before a view, but not
before, changes the memory: otherwise `p₃` cannot tell the difference (`kl`). -/
lemma mem_ne_of_db (hsep : X.GVSep) {i j : ℕ} {Z : List (Label P A)} {C C' : Config A B P L}
    {γ : Label P A} (hs : X.Str i j Z) (hs' : X.Str i j (Z ++ [γ])) (hC : I.run Z = some C)
    (hst : I.step C γ = some C') (hγ : γ.proc ≠ X.p₃) {a : OpId P}
    (ha : a = (X.p₁, 0) ∨ a = (X.p₂, i)) {l : ℕ} (hl : j ≤ l) (h1 : ¬ X.DB Z a (X.p₃, l))
    (h2 : X.DB (Z ++ [γ]) a (X.p₃, l)) : C'.mem ≠ C.mem := by
  intro hm
  have hag : Impl.AgreeOn {X.p₃} C' C := ⟨hm,
    fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact (Impl.step_other hst hγ).1,
    fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact (Impl.step_other hst hγ).2⟩
  exact h1 (X.kl hsep hs' hs (run_snoc hC hst) hC hag
    (by simp [Label.invOf_eq_none_of_proc_ne hγ])
    (by simp [Label.retOf_eq_none_of_proc_ne hγ]) ha hl h2)

/-- **Claim 4.6.8 (1).** If the step `τ r` of `r ∈ {p₁, p₂}` (an access to location `ℓ`)
decides `a` before `op₃`, but not after `p₃`'s next step, then `p₃`'s next step is an access to
`ℓ` (otherwise the two steps commute). -/
lemma loc_of_decides (hsep : X.GVSep) {i j : ℕ} {h : List (Label P A)} {C C3 : Config A B P L}
    (hs : X.Str i j h) (hC : I.run h = some C) (hr3 : (respsOf h X.p₃).length = j) {r : P}
    (hr : r ≠ X.p₃) (op_r : A.Op) {a : OpId P} (ha : a = (X.p₁, 0) ∨ a = (X.p₂, i))
    {ℓ : ι} {π : (B ℓ).Op} {k : (B ℓ).Resp → L} (hpend : C.pend r ≠ none)
    (hact : I.act r (C.loc r) = .access ℓ π k)
    (e : X.DB (h ++ [.tau r]) a (X.p₃, j))
    (hC3 : I.step C (labOf I C X.p₃ (X.R j)) = some C3)
    (a1 : ¬ X.DB (h ++ [labOf I C X.p₃ (X.R j), labOf I C3 r op_r]) a (X.p₃, j)) :
    labOf I C X.p₃ (X.R j) = .tau X.p₃ ∧ ∃ o k', I.act X.p₃ (C.loc X.p₃) = .access ℓ o k' := by
  set σ₃ := labOf I C X.p₃ (X.R j) with hσ₃
  have h3p : σ₃.proc = X.p₃ := labOf_proc _ _ _ _
  have hoth := Impl.step_other hC3 (by rw [h3p]; exact Ne.symm hr)
  have hlab : labOf I C3 r op_r = .tau r := by
    rw [labOf_eq_of_agree I hoth.1 hoth.2]; exact labOf_eq_tau hpend hact _
  rw [hlab] at a1
  obtain ⟨C31, h31, -, -, -⟩ := tau_step (I := I) (C := C3) (by rw [hoth.2]; exact hpend)
    (by rw [hoth.1]; exact hact)
  obtain ⟨C1, h1, -, -, -⟩ := tau_step (I := I) (C := C) hpend hact
  by_contra hn
  have hnc : ∀ i' o k j' o' k', σ₃ = .tau X.p₃ → I.act X.p₃ (C.loc X.p₃) = .access i' o k →
      (Label.tau r : Label P A) = .tau r → I.act r (C.loc r) = .access j' o' k' →
        i' ≠ j' ∨ (((B i').δ (C.mem i') o).1 = C.mem i' ∧ ((B j').δ (C.mem j') o').1 = C.mem j') := by
    intro i' o k₀ j' o' k' hσ hact3 _ hact1
    left
    rintro rfl
    rw [hact] at hact1
    have hj : ℓ = i' := (Action.access.inj hact1).1
    subst hj
    exact hn ⟨hσ, o, k₀, hact3⟩
  obtain ⟨Cb, hCb, hCb'⟩ := Impl.step_comm (Ne.symm hr) h3p rfl hC3 h31 hnc
  rw [h1] at hCb; cases hCb
  have hs1 : X.Str i j (h ++ [.tau r]) :=
    hs.append_noinv X ⟨_, run_snoc hC h1⟩ (opsOf_tau_list (by simp))
  have hlab3 : labOf I C1 X.p₃ (X.R j) = σ₃ := by
    have := Impl.step_other h1 (show (Label.tau r : Label P A).proc ≠ X.p₃ from hr)
    exact labOf_eq_of_agree I this.1 this.2 _
  have hrun13 : I.run (h ++ [.tau r] ++ [σ₃]) = some C31 := run_snoc (run_snoc hC h1) hCb'
  have hs13 : X.Str i j (h ++ [.tau r] ++ [σ₃]) := by
    have := hs1.append_lab3 X (run_snoc hC h1) (by simpa using hr3) (by rw [hlab3]; exact hCb')
    rwa [hlab3] at this
  have hrun31 : I.run (h ++ [σ₃] ++ [.tau r]) = some C31 := run_snoc (run_snoc hC hC3) h31
  have hs31 : X.Str i j (h ++ [σ₃] ++ [.tau r]) :=
    (hs.append_lab3 X hC hr3 hC3).append_noinv X ⟨_, hrun31⟩ (opsOf_tau_list (by simp))
  apply a1
  have := X.kl hsep hs13 hs31 hrun13 hrun31 (Impl.AgreeOn.refl _ _)
    (by simp) (by simp) ha le_rfl (by simpa using e.append [σ₃])
  simpa using this

/-! ### Decisions forced by later views (the case the paper's Claim 4.6.12 misses) -/

/-- If after `h₂` the step of `p_k` decided `op_k` before the next view `(p₃, j+1)` but not before
`op₃ = (p₃, j)`, and `op_{k̄}` is not decided before `(p₃, j+1)`, then no step of `p_{k̄}` can decide
`op_{k̄}` before `op₃`: `op_k` is decided before `op_{k̄}`. -/
lemma bbad (hsep : X.GVSep) {i j : ℕ} {h₂ : List (Label P A)} (hs : X.Str i j h₂)
    {a b : OpId P} (ha : a = (X.p₁, 0) ∨ a = (X.p₂, i)) (hb : b = (X.p₁, 0) ∨ b = (X.p₂, i))
    (hab : a.1 ≠ b.1)
    (hk : X.DB h₂ a (X.p₃, j + 1)) (hk3 : ¬ X.DB h₂ a (X.p₃, j)) (hkb : ¬ X.DB h₂ b (X.p₃, j + 1))
    (γ : Label P A) (hγ : γ.proc = b.1) (hv : I.Valid (h₂ ++ [γ])) :
    ¬ X.DB (h₂ ++ [γ]) b (X.p₃, j) := by
  have ha3 : a.1 ≠ X.p₃ := by rcases ha with rfl | rfl <;> [exact X.h13; exact X.h23]
  have hb3 : b.1 ≠ X.p₃ := by rcases hb with rfl | rfl <;> [exact X.h13; exact X.h23]
  obtain ⟨t, D, hD, htp, hto, htr⟩ := X.exists_run3_to hs (l := j + 1) (by omega)
  have hc := hs.cstr X (by omega) htp hto htr
  have hvt : I.Valid (h₂ ++ t) := ⟨D, hD⟩
  have hab' : X.DB h₂ a b := by
    rcases X.gvDecided hsep hc hb with h | h
    · exact absurd (X.owner.decidedBefore_of_append hvt
        (fun γ hγ => by rw [htp γ hγ]; exact Ne.symm hb3) h) hkb
    · exact X.owner.decidedBefore_of_append hvt (fun γ hγ => by rw [htp γ hγ]; exact Ne.symm ha3)
        ((hk.append t).trans h)
  intro hd
  exact hk3 (X.owner.decidedBefore_of_append hv (fun γ' hγ' => by
    simp only [List.mem_singleton] at hγ'; rw [hγ', hγ]; exact Ne.symm hab)
    ((hab'.append [γ]).trans hd))

/-! ### The main-loop invariant and the good move -/

/-- The invariant at line 5 of Figure 4.2 (Claim 4.6.1): `p₂` completed exactly `M(i)`, `p₃`
completed exactly `V(j)` and invoked nothing more, and neither `op₁` nor `op₂ = (p₂, i)` is
decided before `op₃ = (p₃, j)`. -/
structure GInv (i j : ℕ) (h : List (Label P A)) : Prop where
  str : X.Str i j h
  ops3 : opsOf h X.p₃ = pre X.R j
  resp2 : (respsOf h X.p₂).length = i
  u1 : ¬ X.DB h (X.p₁, 0) (X.p₃, j)
  u2 : ¬ X.DB h (X.p₂, i) (X.p₃, j)

lemma GInv.resp3 {i j : ℕ} {h : List (Label P A)} (hi : X.GInv i j h) :
    (respsOf h X.p₃).length = j := by
  have h1 := hi.str.resp3
  obtain ⟨C, hC⟩ := hi.str.valid
  have h2 := I.run_resps_le_ops hC X.p₃
  rw [hi.ops3] at h2; simp [pre] at h2; omega

lemma GInv.not_inv3 {i j : ℕ} {h : List (Label P A)} (hi : X.GInv i j h) :
    ¬ Invoked h (X.p₃, j) := by
  simp [Invoked, hi.ops3, pre]

/-- At line 5, `op₁` has not completed. -/
lemma GInv.resp1 {i j : ℕ} {h : List (Label P A)} (hi : X.GInv i j h) : respsOf h X.p₁ = [] := by
  by_contra hne
  exact hi.u1 (decidedBefore_of_completed X.lin (by simp only [Completed]; exact List.length_pos_iff.2 hne)
    hi.not_inv3)

/-- **Lines 24–27 when the step of `p_k` decides nothing** (Claims 4.6.10–4.6.13): if neither
`op₁` nor `op₂` is decided before the next view `(p₃, j+1)`, `p₃` completes `op₃` and the
invariant holds for the next view. -/
theorem good_move {i j : ℕ} {h : List (Label P A)} (hs : X.Str i j h)
    (hr2 : (respsOf h X.p₂).length = i) (hu1 : ¬ X.DB h (X.p₁, 0) (X.p₃, j + 1))
    (hu2 : ¬ X.DB h (X.p₂, i) (X.p₃, j + 1)) : ∃ y, X.GInv i (j + 1) y ∧ h <+: y := by
  obtain ⟨t, D, hD, htp, hto, htr⟩ := X.exists_run3_to hs (l := j) le_rfl
  have hnil : ∀ q, q ≠ X.p₃ → opsOf t q = [] ∧ respsOf t q = [] := fun q hq => opsOf_of_proc htp hq
  have hv : I.Valid (h ++ t) := ⟨D, hD⟩
  have hback : ∀ a : OpId P, a.1 ≠ X.p₃ → ¬ X.DB h a (X.p₃, j + 1) → ¬ X.DB (h ++ t) a (X.p₃, j + 1) :=
    fun a ha hn hd => hn (X.owner.decidedBefore_of_append hv (fun γ hγ => by rw [htp γ hγ]; exact Ne.symm ha) hd)
  refine ⟨h ++ t, ⟨⟨hv, ?_, ?_, Or.inl hto, by omega, ?_, fun k hk => Precedes.mono_idx (Precedes.mono (β := t) (hs.prec k hk)) (by omega)⟩,
    hto, ?_, hback _ X.h13 hu1, hback _ X.h23 hu2⟩, List.prefix_append _ _⟩
  · rw [opsOf_append, (hnil _ X.h13).1, List.append_nil]; exact hs.ops1
  · rw [opsOf_append, (hnil _ X.h23).1, List.append_nil]; exact hs.ops2
  · intro q h1 h2 h3; rw [opsOf_append, (hnil _ h3).1, List.append_nil]; exact hs.other q h1 h2 h3
  · rw [respsOf_append, (hnil _ X.h23).2, List.append_nil]; exact hr2

end Generic

section CAS

variable {V : ι → Type} [∀ i, DecidableEq (V i)] {v₀ : ∀ i, V i}
variable {I : Impl A (fun i => casObject (V i) (v₀ i)) P L} (X : Ctx I)

/-- At `C`, the next steps of `p` and `q` are `cas` operations on the same location, both
expecting its current value and writing a different one. -/
def CasRace (C : Config A (fun i => casObject (V i) (v₀ i)) P L) (p q : P) : Prop :=
  C.pend p ≠ none ∧ C.pend q ≠ none ∧ ∃ (ℓ : ι) (n₁ n₂ : V ℓ) (k₁ : _) (k₂ : _),
    I.act p (C.loc p) = .access ℓ (.cas (C.mem ℓ) n₁) k₁ ∧
    I.act q (C.loc q) = .access ℓ (.cas (C.mem ℓ) n₂) k₂ ∧ n₁ ≠ C.mem ℓ ∧ n₂ ≠ C.mem ℓ

omit [DecidableEq ι] [DecidableEq P] in
lemma CasRace.symm {C : Config A (fun i => casObject (V i) (v₀ i)) P L} {p q : P}
    (h : CasRace (I := I) C p q) : CasRace (I := I) C q p := by
  obtain ⟨h1, h2, ℓ, n₁, n₂, k₁, k₂, a1, a2, b1, b2⟩ := h
  exact ⟨h2, h1, ℓ, n₂, n₁, k₂, k₁, a2, a1, b2, b1⟩

omit [DecidableEq ι] in
/-- A primitive that changes the register and is not a write is a successful `cas`. -/
lemma cas_of_change {W : Type} [DecidableEq W] {w₀ : W} (m : W) (o : CASOp W)
    (hch : ((casObject W w₀).δ m o).1 ≠ m) (hw : ∀ w, o ≠ .write w) :
    ∃ n, o = .cas m n ∧ n ≠ m := by
  cases o with
  | read => exact absurd rfl hch
  | write w => exact absurd rfl (hw w)
  | cas e n =>
    simp only [casObject] at hch
    split_ifs at hch with he
    · exact ⟨n, by rw [he], hch⟩
    · exact absurd rfl hch

/-- **Race lemma.** Let the step of `p` decide `a` before the view `(p₃, la)` and the step of `q`
decide `b` before `(p₃, lb)` (neither was decided before), but after `p`'s step, `q`'s step no
longer decides `b` before `(p₃, lb)`. Then both steps are successful `cas` on the same location.
-/
theorem race (hsep : X.GVSep) {i j : ℕ} {Z : List (Label P A)}
    {C : Config A (fun i => casObject (V i) (v₀ i)) P L} (hs : X.Str i j Z) (hC : I.run Z = some C)
    {p q : P} {op_p op_q : A.Op} {a b : OpId P} (hpq : p ≠ q) (hp3 : p ≠ X.p₃) (hq3 : q ≠ X.p₃)
    (ha : a = (X.p₁, 0) ∨ a = (X.p₂, i)) (hb : b = (X.p₁, 0) ∨ b = (X.p₂, i)) (hbq : b.1 = q)
    {la lb : ℕ} (hla : j ≤ la) (hlb : j ≤ lb)
    (hsp : X.Str i j (Z ++ [labOf I C p op_p])) (hsq : X.Str i j (Z ++ [labOf I C q op_q]))
    (r1 : X.DB (Z ++ [labOf I C p op_p]) a (X.p₃, la)) (r1' : ¬ X.DB Z a (X.p₃, la))
    (r2 : X.DB (Z ++ [labOf I C q op_q]) b (X.p₃, lb)) (r2' : ¬ X.DB Z b (X.p₃, lb))
    (r3 : ∀ γ : Label P A, γ.proc = q → I.Valid (Z ++ [labOf I C p op_p, γ]) →
      ¬ X.DB (Z ++ [labOf I C p op_p, γ]) b (X.p₃, lb)) :
    CasRace (I := I) C p q := by
  obtain ⟨Cp, hCp⟩ := hsp.valid
  obtain ⟨Cq, hCq⟩ := hsq.valid
  have hstp := step_of_run_snoc hC hCp
  have hstq := step_of_run_snoc hC hCq
  have hmp := X.mem_ne_of_db hsep hs hsp hC hstp (by rw [labOf_proc]; exact hp3) ha hla r1' r1
  have hmq := X.mem_ne_of_db hsep hs hsq hC hstq (by rw [labOf_proc]; exact hq3) hb hlb r2' r2
  obtain ⟨hpp, hlp, ℓp, op', kp, hactp, hchp⟩ := lab_access hstp hmp
  obtain ⟨hpq', hlq, ℓq, oq', kq, hactq, hchq⟩ := lab_access hstq hmq
  rw [hlp] at hstp hCp r1 r3 hsp
  rw [hlq] at hstq hCq r2 hsq
  obtain ⟨Cp', hsp', hmp', hpdp, hlcp⟩ := tau_step hpp hactp
  rw [hstp] at hsp'; cases hsp'
  obtain ⟨Cq', hsq', hmq', hpdq, hlcq⟩ := tau_step hpq' hactq
  rw [hstq] at hsq'; cases hsq'
  obtain ⟨Cpq, spq, hmpq, hpdpq, hlcpq⟩ := tau_step (C := Cp) (by rw [hpdp]; exact hpq')
    (by rw [hlcp _ hpq.symm]; exact hactq)
  obtain ⟨Cqp, sqp, hmqp, hpdqp, hlcqp⟩ := tau_step (C := Cq) (by rw [hpdq]; exact hpp)
    (by rw [hlcq _ hpq]; exact hactp)
  have hrunpq : I.run (Z ++ [.tau p, .tau q]) = some Cpq := by
    rw [show Z ++ [Label.tau p, .tau q] = (Z ++ [.tau p]) ++ [.tau q] by simp]; exact run_snoc hCp spq
  have hrunqp : I.run (Z ++ [.tau q, .tau p]) = some Cqp := by
    rw [show Z ++ [Label.tau q, .tau p] = (Z ++ [.tau q]) ++ [.tau p] by simp]; exact run_snoc hCq sqp
  have hspq : X.Str i j (Z ++ [.tau p, .tau q]) :=
    hs.append_noinv X ⟨_, hrunpq⟩ (opsOf_tau_list (by simp))
  have hsqp : X.Str i j (Z ++ [.tau q, .tau p]) :=
    hs.append_noinv X ⟨_, hrunqp⟩ (opsOf_tau_list (by simp))
  -- the state of `p₃` is unchanged
  have l3p : Cp.loc X.p₃ = C.loc X.p₃ := hlcp _ (Ne.symm hp3)
  have l3q : Cq.loc X.p₃ = C.loc X.p₃ := hlcq _ (Ne.symm hq3)
  have l3pq : Cpq.loc X.p₃ = C.loc X.p₃ := by rw [hlcpq _ (Ne.symm hq3), l3p]
  have l3qp : Cqp.loc X.p₃ = C.loc X.p₃ := by rw [hlcqp _ (Ne.symm hp3), l3q]
  have agree : ∀ D D' : Config A (fun i => casObject (V i) (v₀ i)) P L, D.mem = D'.mem →
      D.loc X.p₃ = C.loc X.p₃ → D'.loc X.p₃ = C.loc X.p₃ → D.pend = C.pend → D'.pend = C.pend →
      Impl.AgreeOn {X.p₃} D D' := fun D D' hm h1 h2 h3 h4 =>
    ⟨hm, fun r hr => by rw [Set.mem_singleton_iff.1 hr, h1, h2], fun r hr => by rw [h3, h4]⟩
  have hbq3 : ∀ γ ∈ ([.tau p] : List (Label P A)), γ.proc ≠ b.1 := by
    intro γ hγ; simp only [List.mem_singleton] at hγ; subst hγ; rw [hbq]; exact hpq
  have hr2qp : X.DB (Z ++ [.tau q, .tau p]) b (X.p₃, lb) := by
    simpa using r2.append [.tau p]
  -- same location
  by_cases hℓ : ℓp = ℓq
  swap
  · exfalso
    have hmem : Cqp.mem = Cpq.mem := by
      rw [hmpq, hmqp, hmp', hmq', Function.update_of_ne (Ne.symm hℓ), Function.update_of_ne hℓ,
        Function.update_comm hℓ]
    exact r3 (.tau q) rfl ⟨_, by simpa using hrunpq⟩ (by
      simpa using X.kl hsep hsqp hspq hrunqp hrunpq
        (agree _ _ hmem l3qp l3pq (by rw [hpdqp, hpdq]) (by rw [hpdpq, hpdp])) (by simp) (by simp)
        hb hlb hr2qp)
  subst hℓ
  -- the step of `p` is not a write
  have hwp : ∀ w, op' ≠ .write w := by
    rintro w rfl
    have hmem : Cqp.mem = Cp.mem := by rw [hmqp, hmq', hmp', Function.update_idem]
    have hd := X.kl hsep hsqp hsp hrunqp hCp
      (agree _ _ hmem l3qp l3p (by rw [hpdqp, hpdq]) hpdp) (by simp) (by simp) hb hlb hr2qp
    exact r2' (X.owner.decidedBefore_of_append ⟨_, hCp⟩ hbq3 hd)
  -- the step of `q` is not a write
  have hwq : ∀ w, oq' ≠ .write w := by
    rintro w rfl
    have hmem : Cq.mem = Cpq.mem := by rw [hmpq, hmq', hmp', Function.update_idem]
    exact r3 (.tau q) rfl ⟨_, by simpa using hrunpq⟩ (by
      simpa using X.kl hsep hsq hspq hCq hrunpq
        (agree _ _ hmem l3q l3pq hpdq (by rw [hpdpq, hpdp])) (by simp) (by simp) hb hlb r2)
  obtain ⟨n₁, rfl, hn₁⟩ := cas_of_change _ op' hchp hwp
  obtain ⟨n₂, rfl, hn₂⟩ := cas_of_change _ oq' hchq hwq
  exact ⟨hpp, hpq', ℓp, n₁, n₂, kp, kq, hactp, hactq, hn₁, hn₂⟩

/-- **Claim 4.6.8 and Corollary 4.4** (line 16 true), with the reasoning repaired by `kl`: if the
next steps of `p₁` and `p₂` decide `op₁`, resp. `op₂`, before `op₃`, but neither does so after the
next step of `p₃`, then they are successful `cas` on the same location. -/
theorem caseA (hsep : X.GVSep) {i j : ℕ} {h : List (Label P A)}
    {C C3 : Config A (fun i => casObject (V i) (v₀ i)) P L}
    (hs : X.Str i j h) (hC : I.run h = some C) (hr1 : respsOf h X.p₁ = [])
    (hr2 : (respsOf h X.p₂).length = i) (hr3 : (respsOf h X.p₃).length = j)
    (e1 : X.DB (h ++ [labOf I C X.p₁ X.op]) (X.p₁, 0) (X.p₃, j))
    (e2 : X.DB (h ++ [labOf I C X.p₂ (X.W i)]) (X.p₂, i) (X.p₃, j))
    (u1 : ¬ X.DB h (X.p₁, 0) (X.p₃, j)) (u2 : ¬ X.DB h (X.p₂, i) (X.p₃, j))
    (hC3 : I.step C (labOf I C X.p₃ (X.R j)) = some C3)
    (a1 : ¬ X.DB (h ++ [labOf I C X.p₃ (X.R j), labOf I C3 X.p₁ X.op]) (X.p₁, 0) (X.p₃, j))
    (a2 : ¬ X.DB (h ++ [labOf I C X.p₃ (X.R j), labOf I C3 X.p₂ (X.W i)]) (X.p₂, i) (X.p₃, j)) :
    CasRace (I := I) C X.p₁ X.p₂ := by
  obtain ⟨C1, hst1⟩ := step_labOf (I := I) C X.p₁ X.op (X.allowed _ _)
  obtain ⟨C2, hst2⟩ := step_labOf (I := I) C X.p₂ (X.W i) (X.allowed _ _)
  have hs1 := hs.append_lab1 X hC hr1 hst1
  have hs2 := hs.append_lab2 X hC hr2 hst2
  have hm1 := X.mem_ne_of_db hsep hs hs1 hC hst1 (by rw [labOf_proc]; exact X.h13) (Or.inl rfl)
    le_rfl u1 e1
  have hm2 := X.mem_ne_of_db hsep hs hs2 hC hst2 (by rw [labOf_proc]; exact X.h23) (Or.inr rfl)
    le_rfl u2 e2
  obtain ⟨hp1, hl1, ℓ₁, π₁, k₁, hact1, hch1⟩ := lab_access hst1 hm1
  obtain ⟨hp2, hl2, ℓ₂, π₂, k₂, hact2, hch2⟩ := lab_access hst2 hm2
  rw [hl1] at e1 hst1 hs1
  rw [hl2] at e2 hst2 hs2
  -- both access the location of `p₃`'s next step
  obtain ⟨-, o, k, hact3⟩ := X.loc_of_decides hsep hs hC hr3 X.h13 X.op (Or.inl rfl) hp1 hact1 e1 hC3 a1
  obtain ⟨-, o', k', hact3'⟩ := X.loc_of_decides hsep hs hC hr3 X.h23 (X.W i) (Or.inr rfl) hp2 hact2 e2 hC3 a2
  have hℓ : ℓ₁ = ℓ₂ := (Action.access.inj (hact3.symm.trans hact3')).1
  subst hℓ
  -- configurations
  obtain ⟨C1', hs1', hm1', hpd1, hlc1⟩ := tau_step hp1 hact1
  rw [hst1] at hs1'; cases hs1'
  obtain ⟨C2', hs2', hm2', hpd2, hlc2⟩ := tau_step hp2 hact2
  rw [hst2] at hs2'; cases hs2'
  obtain ⟨C12, s12, hm12, hpd12, hlc12⟩ := tau_step (C := C1) (by rw [hpd1]; exact hp2)
    (by rw [hlc1 _ X.h12.symm]; exact hact2)
  obtain ⟨C21, s21, hm21, hpd21, hlc21⟩ := tau_step (C := C2) (by rw [hpd2]; exact hp1)
    (by rw [hlc2 _ X.h12]; exact hact1)
  have hrun1 := run_snoc hC hst1
  have hrun2 := run_snoc hC hst2
  have hrun12 : I.run (h ++ [.tau X.p₁, .tau X.p₂]) = some C12 := by
    rw [show h ++ [Label.tau X.p₁, .tau X.p₂] = (h ++ [.tau X.p₁]) ++ [.tau X.p₂] by simp]
    exact run_snoc hrun1 s12
  have hrun21 : I.run (h ++ [.tau X.p₂, .tau X.p₁]) = some C21 := by
    rw [show h ++ [Label.tau X.p₂, .tau X.p₁] = (h ++ [.tau X.p₂]) ++ [.tau X.p₁] by simp]
    exact run_snoc hrun2 s21
  have hs12 : X.Str i j (h ++ [.tau X.p₁, .tau X.p₂]) :=
    hs.append_noinv X ⟨_, hrun12⟩ (opsOf_tau_list (by simp))
  have hs21 : X.Str i j (h ++ [.tau X.p₂, .tau X.p₁]) :=
    hs.append_noinv X ⟨_, hrun21⟩ (opsOf_tau_list (by simp))
  have agree : ∀ D D' : Config A (fun i => casObject (V i) (v₀ i)) P L, D.mem = D'.mem →
      D.loc X.p₃ = C.loc X.p₃ → D'.loc X.p₃ = C.loc X.p₃ → D.pend = C.pend → D'.pend = C.pend →
      Impl.AgreeOn {X.p₃} D D' := fun D D' hm h1 h2 h3 h4 =>
    ⟨hm, fun r hr => by rw [Set.mem_singleton_iff.1 hr, h1, h2], fun r hr => by rw [h3, h4]⟩
  have l1 : C1.loc X.p₃ = C.loc X.p₃ := hlc1 _ X.h13.symm
  have l2 : C2.loc X.p₃ = C.loc X.p₃ := hlc2 _ X.h23.symm
  have l12 : C12.loc X.p₃ = C.loc X.p₃ := by rw [hlc12 _ X.h23.symm, l1]
  have l21 : C21.loc X.p₃ = C.loc X.p₃ := by rw [hlc21 _ X.h13.symm, l2]
  -- the step of `p₁` is not a write
  have hw1 : ∀ w, π₁ ≠ .write w := by
    rintro w rfl
    have hmem : C21.mem = C1.mem := by rw [hm21, hm2', hm1', Function.update_idem]
    have hd := X.kl hsep hs21 hs1 hrun21 hrun1 (agree _ _ hmem l21 l1 (by rw [hpd21, hpd2]) hpd1)
      (by simp) (by simp) (Or.inr rfl) le_rfl (by simpa using e2.append [.tau X.p₁])
    exact u2 (X.owner.decidedBefore_of_append ⟨_, hrun1⟩ (fun γ hγ => by
      simp only [List.mem_singleton] at hγ; subst hγ; exact X.h12) hd)
  -- the step of `p₂` is not a write
  have hw2 : ∀ w, π₂ ≠ .write w := by
    rintro w rfl
    have hmem : C12.mem = C2.mem := by rw [hm12, hm1', hm2', Function.update_idem]
    have hd := X.kl hsep hs12 hs2 hrun12 hrun2 (agree _ _ hmem l12 l2 (by rw [hpd12, hpd1]) hpd2)
      (by simp) (by simp) (Or.inl rfl) le_rfl (by simpa using e1.append [.tau X.p₂])
    exact u1 (X.owner.decidedBefore_of_append ⟨_, hrun2⟩ (fun γ hγ => by
      simp only [List.mem_singleton] at hγ; subst hγ; exact X.h12.symm) hd)
  obtain ⟨n₁, rfl, hn₁⟩ := cas_of_change _ π₁ hch1 hw1
  obtain ⟨n₂, rfl, hn₂⟩ := cas_of_change _ π₂ hch2 hw2
  exact ⟨hp1, hp2, ℓ₁, n₁, n₂, k₁, k₂, hact1, hact2, hn₁, hn₂⟩

/-- **Lines 17–20 and 26–27** (Corollary 4.4, Claims 4.6.9 and 4.6.13): when the next steps of
`p₁` and `p₂` are competing successful `cas`, let `p₂` go first; `p₁`'s `cas` then fails, so
`op₁` stays undecided before the next view; then `p₂` completes `op₂` and `p₃` completes `op₃`.
The main-loop invariant holds for the next modifier and the next view. -/
theorem cas_move (hsep : X.GVSep) {i j : ℕ} {h : List (Label P A)}
    {C : Config A (fun i => casObject (V i) (v₀ i)) P L} (hs : X.Str i j h) (hC : I.run h = some C)
    (hr2 : (respsOf h X.p₂).length = i) (hu1 : ¬ X.DB h (X.p₁, 0) (X.p₃, j + 1))
    (hcas : CasRace (I := I) C X.p₁ X.p₂) :
    ∃ y, X.GInv (i + 1) (j + 1) y ∧ h ++ [.tau X.p₂, .tau X.p₁] <+: y := by
  obtain ⟨hp1, hp2, ℓ, n₁, n₂, k₁, k₂, hact1, hact2, hn₁, hn₂⟩ := hcas
  obtain ⟨C2, s2, hm2, hpd2, hlc2⟩ := tau_step hp2 hact2
  obtain ⟨C21, s21, hm21, hpd21, hlc21⟩ := tau_step (C := C2) (by rw [hpd2]; exact hp1)
    (by rw [hlc2 _ X.h12]; exact hact1)
  have hmem : C21.mem = C2.mem := by
    have e2 : C2.mem ℓ = n₂ := by rw [hm2]; simp [casObject]
    rw [hm21]; simp [casObject, e2, hn₂]
  have hrun2 := run_snoc hC s2
  have hrun21 : I.run (h ++ [.tau X.p₂, .tau X.p₁]) = some C21 := by
    rw [show h ++ [Label.tau X.p₂, .tau X.p₁] = (h ++ [.tau X.p₂]) ++ [.tau X.p₁] by simp]
    exact run_snoc hrun2 s21
  have hs2 : X.Str i j (h ++ [.tau X.p₂]) := hs.append_noinv X ⟨_, hrun2⟩ (opsOf_tau_list (by simp))
  have hs21 : X.Str i j (h ++ [.tau X.p₂, .tau X.p₁]) :=
    hs.append_noinv X ⟨_, hrun21⟩ (opsOf_tau_list (by simp))
  -- Claim 4.6.9: the failed `cas` decides nothing
  have hnd1 : ¬ X.DB (h ++ [.tau X.p₂, .tau X.p₁]) (X.p₁, 0) (X.p₃, j + 1) := by
    intro hd
    have hag : Impl.AgreeOn {X.p₃} C21 C2 := ⟨hmem,
      fun r hr => by rw [Set.mem_singleton_iff.1 hr]; exact hlc21 _ X.h13.symm,
      fun r hr => by rw [hpd21]⟩
    have := X.kl hsep hs21 hs2 hrun21 hrun2 hag (by simp) (by simp) (Or.inl rfl) (by omega) hd
    exact hu1 (X.owner.decidedBefore_of_append ⟨_, hrun2⟩ (fun γ hγ => by
      simp only [List.mem_singleton] at hγ; subst hγ; exact X.h12.symm) this)
  -- `p₂` completes `op₂`
  obtain ⟨s, E, g1, g2, -, -, g5, g6⟩ := X.exists_finish hrun21 X.p₂ (X.W i)
  have hpE : C21.pend X.p₂ ≠ none := by rw [hpd21, hpd2]; exact hp2
  have hs0 : opsOf s X.p₂ = [] := g5 hpE
  have hrunE : I.run (h ++ [.tau X.p₂, .tau X.p₁] ++ s) = some E := by
    rw [I.run_append_of_eq hrun21, g1]
  have hsnil : ∀ q, opsOf s q = [] := fun q => by
    by_cases hq : q = X.p₂
    · rw [hq]; exact hs0
    · exact (opsOf_of_proc g2 hq).1
  have hsE : X.Str i j (h ++ [.tau X.p₂, .tau X.p₁] ++ s) := hs21.append_noinv X ⟨_, hrunE⟩ hsnil
  have hndE : ¬ X.DB (h ++ [.tau X.p₂, .tau X.p₁] ++ s) (X.p₁, 0) (X.p₃, j + 1) := fun hd =>
    hnd1 (X.owner.decidedBefore_of_append ⟨_, hrunE⟩ (fun γ hγ => by rw [g2 γ hγ]; exact X.h12.symm) hd)
  -- `p₃` completes `op₃`
  obtain ⟨t, D, hD, htp, hto, htr⟩ := X.exists_run3_to hsE (l := j) le_rfl
  set y := h ++ [.tau X.p₂, .tau X.p₁] ++ s ++ t with hy
  have hvy : I.Valid y := ⟨D, hD⟩
  have hndy : ¬ X.DB y (X.p₁, 0) (X.p₃, j + 1) := fun hd =>
    hndE (X.owner.decidedBefore_of_append hvy (fun γ hγ => by rw [htp γ hγ]; exact X.h13.symm) hd)
  have htnil : ∀ q, q ≠ X.p₃ → opsOf t q = [] ∧ respsOf t q = [] := fun q hq => opsOf_of_proc htp hq
  have hops2h : opsOf h X.p₂ = pre X.W (i + 1) := by
    have hl := I.run_pend_counts hC hp2
    rcases hs.ops2 with e | e
    · rw [e, hr2] at hl; simp [pre] at hl
    · exact e
  have hops2 : opsOf y X.p₂ = pre X.W (i + 1) := by
    simp [hy, hops2h, hs0, (htnil _ X.h23).1]
  have hresp2 : (respsOf y X.p₂).length = i + 1 := by
    simp [hy, hr2, g6, (htnil _ X.h23).2]
  have hops1 : opsOf y X.p₁ = opsOf h X.p₁ := by
    simp [hy, (opsOf_of_proc g2 X.h12).1, (htnil _ X.h13).1]
  refine ⟨y, ⟨⟨hvy, by rw [hops1]; exact hs.ops1, Or.inl hops2, Or.inl hto, by omega, ?_, ?_⟩,
    hto, hresp2, hndy, ?_⟩, by rw [hy, List.append_assoc]; exact List.prefix_append _ _⟩
  · intro q h1 h2 h3
    simp [hy, hs.other q h1 h2 h3, (opsOf_of_proc g2 h2).1, (htnil _ h3).1]
  · intro k hk
    refine ⟨y, [], by simp, ?_, ?_⟩
    · simp only [Completed, hresp2]; omega
    · simp [Invoked, hto, pre]
  · have hcur : curOp y X.p₃ = (X.p₃, j + 1) := by simp [curOp, htr]
    rw [← hcur]
    exact X.not_decidedBefore_cur hvy (by simp [Invoked, hops2, pre]) X.h23

end CAS


end Ctx

end Podc.HelpFreeWaitFree
