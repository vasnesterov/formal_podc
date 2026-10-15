import Papers.PODC2016.ComplexityHierarchy.Zhu

/-!
# Space lower bounds for ℓ-buffers and multiple assignment (Theorems 6.8 and 7.5 of EGSZ'16)

* `lowerBound_core`: for a binary consensus algorithm over `MB R ℓ V` and a packing capacity `k`
  with `ℓ ≤ k` and (`2ℓ ≤ k` or single-location writes), `n - 1 ≤ k · |R|`.
* `theorem_7_5`: memory of `ℓ`-buffers with multiple assignment: `n - 1 ≤ 2ℓ · |R|`, i.e. at
  least `⌈(n-1)/2ℓ⌉` locations.
* `theorem_6_8`: memory of `ℓ`-buffers (Section 6 model: one base object `bufferSpec ℓ V` per
  location `i : ι`): `n - 1 ≤ ℓ · |ι|`, i.e. at least `⌈(n-1)/ℓ⌉` locations. Proved by simulating
  the per-location model in the single-memory model (`toMB`).
* `zhu_registers`: the special case `ℓ = 1` (single-value registers stored as 1-buffers): `n - 1`
  locations (Zhu, STOC'16).

All lower bounds hold for *weak* validity (`weakConsensus`) and one-shot obstruction-freedom
(`OneShotOF`), hence a fortiori for the paper's consensus and obstruction-freedom, and for any
initial memory contents.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

section MultiBuffer

variable {R V P L : Type} [DecidableEq P] [DecidableEq R] {ℓ : ℕ}
  {I : Impl BinCons (MB R ℓ V) P L}

/-- With no memory locations at all, two processes cannot solve consensus. -/
theorem no_locations [Fintype P] [IsEmpty R] (hS : I.Solves (weakConsensus P Bool))
    (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v) {p₀ p₁ : P} (hne : p₀ ≠ p₁) : False := by
  obtain ⟨C, hC, h0, h1⟩ := I.exists_initial_bivalent hS hof hall hne
  obtain ⟨β, C', hβ, hC', hd⟩ := h0
  have hp₁ := I.runFrom_other hC' (hβ.proc_ne (by simpa using hne.symm))
  have hag : AgreeOn ({p₁} : Set P) C C' :=
    ⟨funext fun _ => funext fun r => isEmptyElim r,
      fun q hq => by rw [Set.mem_singleton_iff] at hq; subst hq; exact hp₁.1.symm,
      fun q hq => by rw [Set.mem_singleton_iff] at hq; subst hq; exact hp₁.2.symm⟩
  have := hC.decides_canDecide_eq hS hβ hC' hd (canDecide_of_agreeOn hag h1)
  simp at this

/-- The common lower bound behind Theorems 6.8 and 7.5. -/
theorem lowerBound_core [Fintype P] [Fintype R] (hS : I.Solves (weakConsensus P Bool))
    (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v) {k : ℕ} (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k)
    (h2 : 2 * ℓ ≤ k ∨ I.SingleWrites) (hn : 2 ≤ Fintype.card P) :
    Fintype.card P - 1 ≤ k * Fintype.card R := by
  classical
  obtain ⟨p₀, p₁, hne⟩ := Fintype.exists_pair_of_one_lt_card hn
  rcases isEmpty_or_nonempty R with hR | hR
  · exact (no_locations hS hof hall hne).elim
  obtain ⟨C, hC, h0, h1⟩ := I.exists_initial_bivalent hS hof hall hne
  have hb : I.Bivalent (↑(Finset.univ : Finset P)) C :=
    bivalent_of_canDecide (v := false) (by simp) (by simp) h0 h1
  obtain ⟨C', hCC', Q, -, hQc, hbQ, π, hπ⟩ :=
    zhu_induction hS hof hℓ hk h2 _ hn Finset.univ rfl C hC hb
  have hC' := hC.reachBy hCC'
  have hcardR : 1 ≤ Fintype.card R := Fintype.card_pos
  by_cases hR' : (Finset.univ \ Q).Nonempty
  · obtain ⟨p, hp⟩ := hR'
    obtain ⟨T1, T2, hB, hT⟩ := exists_isBlock hℓ hk h2 hπ
    obtain ⟨-, -, -, -, -, -, -, q, -, r₀, hr₀, -⟩ :=
      key_lemma hS hof hC' Finset.disjoint_sdiff hbQ hB hT hp
    have := card_lt_of_not_fullyPacked (show ¬ FullyPacked _ _ _ r₀ from hr₀)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hQc] at this
    omega
  · have h0 : (Finset.univ \ Q).card = 0 := by
      rw [Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.1 hR'
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hQc] at h0
    have : 1 ≤ k * Fintype.card R := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega

/-- **Theorem 7.5** of Ellen–Gelashvili–Shavit–Zhu. Consider a memory of `ℓ`-buffers in which each
process can atomically perform `ℓ-buffer-write` to any subset of the `ℓ`-buffers. Then any
obstruction-free binary consensus algorithm for `n ≥ 2` processes uses at least `⌈(n-1)/2ℓ⌉`
locations: `n - 1 ≤ 2ℓ · |R|`. -/
theorem theorem_7_5 [Fintype P] [Fintype R] (I : Impl BinCons (MB R ℓ V) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hℓ : 1 ≤ ℓ) (hn : 2 ≤ Fintype.card P) :
    Fintype.card P - 1 ≤ 2 * ℓ * Fintype.card R :=
  lowerBound_core hS hof hall hℓ (by omega) (Or.inl le_rfl) hn

/-- Theorem 7.5 in the paper's form `⌈(n-1)/2ℓ⌉ ≤ |R|`. -/
theorem theorem_7_5_ceil [Fintype P] [Fintype R] (I : Impl BinCons (MB R ℓ V) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hℓ : 1 ≤ ℓ) (hn : 2 ≤ Fintype.card P) :
    (Fintype.card P - 1 + (2 * ℓ - 1)) / (2 * ℓ) ≤ Fintype.card R := by
  have h := theorem_7_5 I hS hof hall hℓ hn
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  exact Nat.add_le_add_right (h.trans (le_of_eq (by ring))) _

end MultiBuffer

/-! ### Section 6: one `ℓ`-buffer base object per location -/

section PerLocation

/-- Operations of a single `ℓ`-buffer. -/
inductive BOp (V : Type) where
  /-- `ℓ-buffer-read()`. -/
  | read
  /-- `ℓ-buffer-write(v)`. -/
  | write (v : V)

/-- An `ℓ`-buffer (Section 6): the content is the list of the inputs of the (at most) `ℓ` most
recent writes, most recent first; `read` returns it, `write` returns nothing. -/
abbrev bufferSpec (ℓ : ℕ) (V : Type) : ObjSpec where
  State := List V
  Op := BOp V
  Resp := List V
  init := []
  δ s o := match o with
    | .read => (s, s)
    | .write v => (bufWrite ℓ v s, [])

variable {ι V P L : Type} [DecidableEq P] [DecidableEq ι] {ℓ : ℕ}

/-- The simulation of the per-location model in the single-memory model. -/
def toMB (I : Impl BinCons (fun _ : ι => bufferSpec ℓ V) P L) : Impl BinCons (MB ι ℓ V) P L where
  memInit := fun _ => I.memInit
  locInit := I.locInit
  invoke := I.invoke
  act p l := match I.act p l with
    | .access i .read k => .access () (.read i) k
    | .access i (.write v) k => .access () (.write (fun r => if r = i then some v else none)) k
    | .ret r l' => .ret r l'
  allowed := I.allowed

/-- Configurations of the per-location model as configurations of the single-memory model. -/
def trC (C : Config BinCons (fun _ : ι => bufferSpec ℓ V) P L) : Config BinCons (MB ι ℓ V) P L :=
  ⟨C.loc, C.pend, fun _ => C.mem⟩

variable (I : Impl BinCons (fun _ : ι => bufferSpec ℓ V) P L)

lemma toMB_step (C : Config BinCons (fun _ : ι => bufferSpec ℓ V) P L) (lab : Label P BinCons) :
    (toMB I).step (trC C) lab = (I.step C lab).map trC := by
  classical
  cases lab with
  | inv p o =>
    simp only [Impl.step]
    split_ifs <;> simp_all [trC, toMB]
  | tau p =>
    simp only [Impl.step]
    by_cases hp : C.pend p = none
    · simp [hp, trC]
    · simp only [trC, hp, if_false]
      rcases h : I.act p (C.loc p) with ⟨i, o, k⟩ | ⟨r, l'⟩
      · cases o with
        | read =>
          simp only [toMB, h, Option.map_some]
          congr 1
          unfold trC
          congr 1
          funext u j; cases u; by_cases hj : j = i <;> simp [hj]
        | write v =>
          simp only [toMB, h, Option.map_some]
          congr 1
          unfold trC
          congr 1
          funext u j; cases u; by_cases hj : j = i <;> simp [hj, applyW]
      · simp [toMB, h]
  | ret p r =>
    simp only [Impl.step]
    by_cases hp : C.pend p = none
    · simp [hp, trC]
    · simp only [trC, hp, if_false]
      rcases h : I.act p (C.loc p) with ⟨i, o, k⟩ | ⟨r', l'⟩
      · cases o <;> simp [toMB, h]
      · simp only [toMB, h]
        split_ifs <;> simp [trC]

lemma toMB_runFrom (C : Config BinCons (fun _ : ι => bufferSpec ℓ V) P L)
    (α : List (Label P BinCons)) : (toMB I).runFrom (trC C) α = (I.runFrom C α).map trC := by
  induction α generalizing C with
  | nil => rfl
  | cons lab α ih =>
    simp only [runFrom_cons, toMB_step]
    cases I.step C lab with
    | none => rfl
    | some C' => simp [ih]

lemma toMB_run (α : List (Label P BinCons)) : (toMB I).run α = (I.run α).map trC :=
  toMB_runFrom I I.initCfg α

lemma toMB_valid {α : List (Label P BinCons)} (h : (toMB I).Valid α) : I.Valid α := by
  obtain ⟨C, hC⟩ := h
  rw [toMB_run] at hC
  cases h' : I.run α with
  | none => simp [h'] at hC
  | some C' => exact ⟨C', h'⟩

lemma toMB_nextLabel (C : Config BinCons (fun _ : ι => bufferSpec ℓ V) P L) (p : P) :
    (toMB I).nextLabel (trC C) p = I.nextLabel C p := by
  unfold nextLabel
  simp only [trC, toMB]
  rcases h : I.act p (C.loc p) with ⟨i, o, k⟩ | ⟨r, l'⟩
  · cases o <;> simp
  · simp

lemma toMB_soloStep (C : Config BinCons (fun _ : ι => bufferSpec ℓ V) P L) (p : P) :
    (toMB I).soloStep p (trC C) = trC (I.soloStep p C) := by
  unfold soloStep
  rw [toMB_nextLabel, toMB_step]
  by_cases hp : C.pend p = none
  · simp [hp, trC]
  · have hp' : (trC C).pend p ≠ none := hp
    rw [if_neg hp', if_neg hp]
    cases I.step C (I.nextLabel C p) <;> rfl

lemma toMB_iterate_soloStep (C : Config BinCons (fun _ : ι => bufferSpec ℓ V) P L) (p : P)
    (n : ℕ) : ((toMB I).soloStep p)^[n] (trC C) = trC ((I.soloStep p)^[n] C) := by
  induction n generalizing C with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, toMB_soloStep, ih]

lemma toMB_oneShotOF (hof : I.OneShotOF) : (toMB I).OneShotOF := by
  intro α C' p hα h1 hp
  rw [toMB_run] at hα
  cases h' : I.run α with
  | none => simp [h'] at hα
  | some C =>
    rw [h'] at hα; simp only [Option.map_some, Option.some.injEq] at hα; subst hα
    obtain ⟨K, hK⟩ := hof α C p h' h1 hp
    exact ⟨K, by rw [toMB_iterate_soloStep]; exact hK⟩

lemma toMB_singleWrites : (toMB I).SingleWrites := by
  intro p l w k h r r' hr hr'
  simp only [toMB] at h
  rcases h' : I.act p l with ⟨i, o, k'⟩ | ⟨r'', l'⟩
  · rw [h'] at h
    cases o with
    | read => simp at h
    | write v =>
      simp only [Action.access.injEq, true_and] at h
      obtain ⟨hw, -⟩ := h
      cases hw
      by_cases e : r = i
      · by_cases e' : r' = i
        · rw [e, e']
        · simp [e'] at hr'
      · simp [e] at hr
  · rw [h'] at h; simp at h

/-- **Theorem 6.8** of Ellen–Gelashvili–Shavit–Zhu. Consider a memory consisting of `ℓ`-buffers
(one base object `bufferSpec ℓ V` per location `i : ι`). Then any obstruction-free binary
consensus algorithm for `n ≥ 2` processes uses at least `⌈(n-1)/ℓ⌉` locations:
`n - 1 ≤ ℓ · |ι|`. -/
theorem theorem_6_8 [Fintype P] [Fintype ι] (I : Impl BinCons (fun _ : ι => bufferSpec ℓ V) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hℓ : 1 ≤ ℓ) (hn : 2 ≤ Fintype.card P) :
    Fintype.card P - 1 ≤ ℓ * Fintype.card ι :=
  lowerBound_core (I := toMB I) (fun α hα h1 => hS α (toMB_valid I hα) h1) (toMB_oneShotOF I hof)
    hall hℓ le_rfl (Or.inr (toMB_singleWrites I)) hn

/-- Theorem 6.8 in the paper's form `⌈(n-1)/ℓ⌉ ≤ |ι|`. -/
theorem theorem_6_8_ceil [Fintype P] [Fintype ι]
    (I : Impl BinCons (fun _ : ι => bufferSpec ℓ V) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hℓ : 1 ≤ ℓ) (hn : 2 ≤ Fintype.card P) :
    (Fintype.card P - 1 + (ℓ - 1)) / ℓ ≤ Fintype.card ι := by
  have h := theorem_6_8 I hS hof hall hℓ hn
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  exact Nat.add_le_add_right (h.trans (le_of_eq (by ring))) _

/-- The case `ℓ = 1` (registers, represented as `1`-buffers) is Zhu's `n - 1` lower bound
(STOC 2016): obstruction-free binary consensus for `n` processes needs `n - 1` registers. -/
theorem zhu_registers [Fintype P] [Fintype ι] (I : Impl BinCons (fun _ : ι => bufferSpec 1 V) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hn : 2 ≤ Fintype.card P) : Fintype.card P - 1 ≤ Fintype.card ι := by
  simpa using theorem_6_8 I hS hof hall le_rfl hn

end PerLocation

end Cslib.SharedMemory.ComplexityHierarchy
