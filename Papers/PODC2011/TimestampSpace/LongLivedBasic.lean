import Papers.PODC2011.TimestampSpace.EFR

/-!
# Long-lived lower bound: signatures, `(3,k)`-configurations and execution helpers

Definitions of Section 3 of the paper and generic lemmas used in the proof of Theorem 1.1
(`LongLived.lean`):

* `sig I C i` — number of processes covering base object `i` in `C` (the signature of `C`);
* `Is3k I C k` — `C` is a `(3,k)`-configuration: every object is covered by at most three
  processes and `k` processes cover objects in total (`∑ i, sig I C i = k`);
* `R3 I C` — the objects covered by exactly three processes;
* `Triple I C R b₀ b₁ b₂` — three disjoint block writes, each covering exactly `R` in `C`.

Since processes are deterministic, a process covers at most one object (`covers_unique`), so
`∑ i, sig I C i` is the number of covering processes.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L}

/-! ### Covering -/

-- CSLib candidate (generic in the implemented object)
/-- A (deterministic) process covers at most one base object. -/
lemma covers_unique {C : Config (tsObj T) B P L} {p : P} {i j : ι} (hi : I.Covers C p i)
    (hj : I.Covers C p j) : i = j := by
  obtain ⟨-, o, k, h1, -⟩ := hi
  obtain ⟨-, o', k', h2, -⟩ := hj
  rw [h1] at h2
  cases h2; rfl

lemma not_covers_of_idle {C : Config (tsObj T) B P L} {p : P} (hp : C.pend p = none) (i : ι) :
    ¬ I.Covers C p i := fun h => h.1 hp

/-! ### Signatures and `(3,k)`-configurations -/

section Sig

variable [Fintype P]

open Classical in
variable (I) in
/-- The signature of `C`: `sig I C i` is the number of processes covering base object `i`. -/
noncomputable def sig (C : Config (tsObj T) B P L) (i : ι) : ℕ :=
  (Finset.univ.filter (fun p => I.Covers C p i)).card

variable (I) in
/-- `R₃(C)`: the base objects covered by exactly three processes. -/
def R3 (C : Config (tsObj T) B P L) : Set ι := {i | sig I C i = 3}

variable (I) in
/-- `C` is a `(3,k)`-configuration: no base object is covered by more than three processes, and
`k` processes are covering (in terms of signatures: `cᵢ ≤ 3` and `∑ cᵢ = k`). -/
def Is3k [Fintype ι] (C : Config (tsObj T) B P L) (k : ℕ) : Prop :=
  (∀ i, sig I C i ≤ 3) ∧ ∑ i, sig I C i = k

lemma sig_eq_card (C : Config (tsObj T) B P L) (i : ι) [DecidablePred (fun p => I.Covers C p i)] :
    sig I C i = (Finset.univ.filter (fun p => I.Covers C p i)).card := by
  unfold sig; congr 1; ext; simp

lemma sig_eq_zero_of_quiescent {C : Config (tsObj T) B P L} (hC : C.Quiescent) (i : ι) :
    sig I C i = 0 := by
  classical
  rw [sig_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun p _ => not_covers_of_idle (hC p) i

lemma is3k_zero_of_quiescent [Fintype ι] {C : Config (tsObj T) B P L} (hC : C.Quiescent) :
    Is3k I C 0 :=
  ⟨fun i => by simp [sig_eq_zero_of_quiescent hC], by simp [sig_eq_zero_of_quiescent hC]⟩

/-- In a `(3,k)`-configuration, `k ≤ 3 m` where `m` is the number of base objects. -/
lemma Is3k.le [Fintype ι] {C : Config (tsObj T) B P L} {k : ℕ} (h : Is3k I C k) :
    k ≤ 3 * Fintype.card ι := by
  rw [← h.2]
  calc ∑ i, sig I C i ≤ ∑ _i : ι, 3 := Finset.sum_le_sum fun i _ => h.1 i
    _ = 3 * Fintype.card ι := by simp [mul_comm]

/-- Adding one covering process `p` (idle in `C`, covering `r` in `X`, all other processes
unchanged) to a `(3,k)`-configuration in which `r` is covered at most twice yields a
`(3,k+1)`-configuration. -/
lemma Is3k.insert [Fintype ι] {C X : Config (tsObj T) B P L} {k : ℕ} (hC : Is3k I C k) {p : P}
    (hp : C.pend p = none) (hag : ∀ q, q ≠ p → X.loc q = C.loc q ∧ X.pend q = C.pend q)
    {r : ι} (hX : I.Covers X p r) (hr : sig I C r ≤ 2) : Is3k I X (k + 1) := by
  classical
  have hiff : ∀ q, q ≠ p → ∀ j, I.Covers X q j ↔ I.Covers C q j := fun q hq j =>
    ⟨covers_congr (hag q hq).1 (hag q hq).2,
      covers_congr (hag q hq).1.symm (hag q hq).2.symm⟩
  have hsig : ∀ j, sig I X j = sig I C j + if j = r then 1 else 0 := by
    intro j
    rw [sig_eq_card, sig_eq_card]
    split_ifs with hj
    · subst hj
      rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter (fun q => I.Covers C q j))
        (a := p) (by simp [not_covers_of_idle hp])]
      congr 1; ext q
      by_cases hq : q = p
      · subst hq; simp [hX]
      · simp [hq, hiff q hq]
    · congr 1; ext q
      by_cases hq : q = p
      · subst hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_covers_of_idle hp,
          iff_false]
        exact fun h => hj (covers_unique h hX)
      · simp [hiff q hq]
  refine ⟨fun j => ?_, ?_⟩
  · rw [hsig]; split_ifs with hj
    · subst hj; omega
    · simpa using hC.1 j
  · simp only [hsig, Finset.sum_add_distrib, hC.2, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]

end Sig

/-! ### Three disjoint block writes covering the same set -/

variable (I) in
/-- `b₀, b₁, b₂` are three block writes by pairwise distinct processes, each covering exactly
the set `R` of base objects in `C`. -/
structure Triple (C : Config (tsObj T) B P L) (R : Set ι) (b₀ b₁ b₂ : List (P × ι)) : Prop where
  nodup : (b₀.map Prod.fst ++ b₁.map Prod.fst ++ b₂.map Prod.fst).Nodup
  covers : ∀ c ∈ b₀ ++ b₁ ++ b₂, I.Covers C c.1 c.2
  mem₀ : ∀ i, i ∈ R ↔ i ∈ b₀.map Prod.snd
  mem₁ : ∀ i, i ∈ R ↔ i ∈ b₁.map Prod.snd
  mem₂ : ∀ i, i ∈ R ↔ i ∈ b₂.map Prod.snd

/-- In a configuration where every object is covered at most three times, the objects covered
three times are covered by three disjoint block writes. -/
lemma exists_triple [Fintype P] [Fintype ι] (C : Config (tsObj T) B P L) :
    ∃ b₀ b₁ b₂, Triple I C (R3 I C) b₀ b₁ b₂ := by
  classical
  rcases isEmpty_or_nonempty P with hP | hP
  · refine ⟨[], [], [], by simp, by simp, ?_, ?_, ?_⟩ <;>
    · intro i; simp [R3, sig_eq_card, Finset.univ_eq_empty]
  -- three distinct coverers of each object of `R₃(C)`
  have hf : ∀ i : ι, ∃ f : Fin 3 → P, sig I C i = 3 →
      Function.Injective f ∧ ∀ j, I.Covers C (f j) i := by
    intro i
    by_cases hi : sig I C i = 3
    · rw [sig_eq_card] at hi
      obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.1 hi
      have hmem : ∀ q ∈ ({a, b, c} : Finset P), I.Covers C q i := by
        intro q hq; rw [← he] at hq; simpa using hq
      refine ⟨![a, b, c], fun _ => ⟨?_, fun j => hmem _ ?_⟩⟩
      · intro x y hxy
        fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
      · fin_cases j <;> simp
    · exact ⟨fun _ => Classical.arbitrary P, fun h => absurd h hi⟩
  choose f hf using hf
  set Rl := (Finset.univ.filter (fun i => sig I C i = 3)).toList with hRl
  have hRl_nd : Rl.Nodup := Finset.nodup_toList _
  have hmemRl : ∀ i, i ∈ Rl ↔ sig I C i = 3 := by intro i; simp [hRl]
  let b : Fin 3 → List (P × ι) := fun j => Rl.map (fun i => (f i j, i))
  have hcov : ∀ j, ∀ c ∈ b j, I.Covers C c.1 c.2 := by
    intro j c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact (hf i ((hmemRl i).1 hi)).2 j
  have hsnd : ∀ j, (b j).map Prod.snd = Rl := by intro j; simp [b, Function.comp_def]
  have hfst : ∀ j, (b j).map Prod.fst = Rl.map (fun i => f i j) := by
    intro j; simp [b, Function.comp_def]
  have hinj : ∀ j j' i i', i ∈ Rl → i' ∈ Rl → f i j = f i' j' → i = i' ∧ j = j' := by
    intro j j' i i' hi hi' he
    have h1 := (hf i ((hmemRl i).1 hi)).2 j
    have h2 := (hf i' ((hmemRl i').1 hi')).2 j'
    rw [he] at h1
    have hii := covers_unique h1 h2
    subst hii
    exact ⟨rfl, (hf i ((hmemRl i).1 hi)).1 he⟩
  have hnd1 : ∀ j, (Rl.map (fun i => f i j)).Nodup := fun j =>
    hRl_nd.map_on (fun i hi i' hi' he => (hinj j j i i' hi hi' he).1)
  have hdisj : ∀ j j', j ≠ j' → ∀ x ∈ Rl.map (fun i => f i j), ∀ y ∈ Rl.map (fun i => f i j'),
      x ≠ y := by
    intro j j' hjj x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hy
    exact hjj (hinj j j' i i' hi hi' hxy).2
  refine ⟨b 0, b 1, b 2, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hfst, hfst, hfst]
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hnd1 0, hnd1 1, ?_⟩, hnd1 2, ?_⟩
    · exact hdisj 0 1 (by decide)
    · intro x hx y hy
      rcases List.mem_append.1 hx with hx | hx
      · exact hdisj 0 2 (by decide) x hx y hy
      · exact hdisj 1 2 (by decide) x hx y hy
  · intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact hcov 0 c hc
    · exact hcov 1 c hc
    · exact hcov 2 c hc
  all_goals intro i; rw [hsnd, hmemRl]; rfl

/-! ### Generic execution helpers -/

-- CSLib candidate (generic in the implemented object)
/-- From a reachable configuration, the processes of `ps` can finish their pending operations one
after the other (obstruction-freedom); the other processes do not move. -/
lemma exists_finish (hst : SoloTerm I false) (ps : List P) :
    ∀ {α : List (Label P (tsObj T))} {F : Config (tsObj T) B P L}, I.run α = some F →
      ∃ γ F', (∀ ℓ ∈ γ, ℓ.proc ∈ ps) ∧ I.runFrom F γ = some F' ∧
        (∀ p ∈ ps, F'.pend p = none) ∧ (∀ q, q ∉ ps → F'.loc q = F.loc q ∧ F'.pend q = F.pend q) := by
  induction ps with
  | nil =>
    intro α F _
    exact ⟨[], F, by simp, rfl, by simp, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons p ps ih =>
    intro α F hα
    have hfin : ∃ K, ((I.soloStep p)^[K] F).pend p = none := by
      by_cases hp : F.pend p = none
      · exact ⟨0, hp⟩
      · exact hst α F p hα (adm_false _) hp
    set γ₁ := I.soloLabels p F (I.soloTime p F)
    set F₁ := (I.soloStep p)^[I.soloTime p F] F
    have hr₁ : I.runFrom F γ₁ = some F₁ := I.runFrom_soloLabels p F _
    have hF₁ : F₁.pend p = none := I.soloTime_spec p F hfin
    obtain ⟨γ, F', hγ, hr, hfin', hoth⟩ := ih (α := α ++ γ₁) (F := F₁)
      (by rw [run_append_of_eq I hα, hr₁])
    refine ⟨γ₁ ++ γ, F', fun ℓ hℓ => ?_, by rw [runFrom_append_of_eq I hr₁, hr], fun q hq => ?_,
      fun q hq => ?_⟩
    · rcases List.mem_append.1 hℓ with h | h
      · rw [I.soloLabels_proc p F _ ℓ h]; simp
      · exact List.mem_cons_of_mem _ (hγ ℓ h)
    · rcases List.mem_cons.1 hq with rfl | hq
      · by_cases hq' : q ∈ ps
        · exact hfin' q hq'
        · rw [(hoth q hq').2, hF₁]
      · exact hfin' q hq
    · have hqp : q ≠ p := fun h => hq (by simp [h])
      have hqs : q ∉ ps := fun h => hq (List.mem_cons_of_mem _ h)
      rw [(hoth q hqs).1, (hoth q hqs).2, (I.iterate_soloStep_other hqp F _).1,
        (I.iterate_soloStep_other hqp F _).2]
      exact ⟨rfl, rfl⟩

/-- **Solo `getTS` dichotomy.** Let `p` be idle in a reachable configuration `A` and run
`getTS` solo by `p`. Then either `p` completes its `getTS` while leaving the memory outside `R`
unchanged, or `p` reaches a point (without having changed the memory outside `R`) where it covers
an object outside `R`. -/
lemma solo_getTS_or_covers (hI : IsTS I false) (hB : RWLike B) {α : List (Label P (tsObj T))}
    {A : Config (tsObj T) B P L} (hα : I.run α = some A) {p : P} (hp : A.pend p = none)
    (R : Set ι) :
    ∃ β D, I.runFrom A β = some D ∧ (∀ ℓ ∈ β, ℓ.proc = p) ∧ (∀ j ∉ R, D.mem j = A.mem j) ∧
      ((opsOf β p = [.getTS] ∧ (respsOf β p).length = 1 ∧ D.pend p = none) ∨
        ∃ r, r ∉ R ∧ I.Covers D p r) := by
  classical
  obtain ⟨A₁, hs⟩ : ∃ A₁, I.step A (.inv p .getTS) = some A₁ := by
    simp [step, hp, hI.allowed p]
  have hA₁p : A₁.pend p ≠ none := by
    have := (step_inv hs).2.2.1; simp [this]
  have hrun₁ : I.run (α ++ [.inv p .getTS]) = some A₁ := by
    rw [run_append_of_eq I hα, runFrom_singleton, hs]
  have hfin := hI.progress _ A₁ p hrun₁ (adm_false _) hA₁p
  obtain ⟨m, hm₁, hm₂⟩ := I.exists_solo_until p A₁
    (fun a => ∃ i o k, a = .access i o k ∧ i ∉ R ∧ ¬ (B i).ReadOnly o) hfin
  set D := (I.soloStep p)^[m] A₁
  set β : List (Label P (tsObj T)) := .inv p .getTS :: I.soloLabels p A₁ m
  have hrun : I.runFrom A β = some D := by
    simp only [β, runFrom_cons, hs, Option.bind_some, runFrom_soloLabels]; rfl
  have hproc : ∀ ℓ ∈ β, ℓ.proc = p := by
    intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · rfl
    · exact I.soloLabels_proc p A₁ m ℓ hℓ
  have hmem : ∀ j ∉ R, D.mem j = A.mem j := by
    intro j hj
    rw [I.iterate_soloStep_mem_of_readOnly p A₁ R m (fun j' hj' i o k hact hiR => by
      by_contra hro; exact (hm₁ j' hj').2 ⟨i, o, k, hact, hiR, hro⟩) j hj]
    rw [(step_inv hs).2.2.2.2]
  refine ⟨β, D, hrun, hproc, hmem, ?_⟩
  by_cases hD : D.pend p = none
  · left
    have hops : opsOf β p = [.getTS] := by
      simp only [β, opsOf_cons, opsOf_soloLabels]; simp [Label.invOf]
    refine ⟨hops, ?_, hD⟩
    have := I.runFrom_counts hrun p 0 0 (Or.inl ⟨hp, rfl⟩)
    rw [hops] at this
    simp only [hD, true_and, ne_eq, not_true_eq_false, false_and, or_false] at this
    simp at this; omega
  · right
    rcases hm₂ with h | ⟨i, o, k, hact, hiR, hro⟩
    · exact absurd h hD
    · rcases hB i o with h | h
      · exact absurd h hro
      · exact ⟨i, hiR, hD, o, k, hact, h⟩

end Cslib.SharedMemory.Timestamp
