import Papers.PODC2011.TimestampSpace.Defs
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Foundations.Data.Nat.Descent

/-!
# Lemma 2.1 (Ellen, Fatourou, Ruppert)

Let `C` be reachable, and let `B₀, B₁, B₂` be disjoint sets of processes each covering the same
set `R` of base objects. Let `U₀, U₁` be disjoint sets of further processes. Then it is impossible
that, for both `i ∈ {0, 1}`, some `Uᵢ`-only execution from `πBᵢ(C)` contains a complete `getTS`
and leaves the memory outside `R` unchanged.

We state the lemma in the form used by the paper: the complete `getTS` is by a process
`qᵢ ∈ Uᵢ` that is idle (no pending operation) in `C`, invokes exactly one operation (a `getTS`)
in the `Uᵢ`-only execution `βᵢ` and has returned at its end. Instead of "does not write outside
`R`" we only assume that the memory outside `R` at the end of `βᵢ` equals that of `C` (a weaker
hypothesis, hence a stronger lemma).

Proof: the executions `C; πB₀ β₀ πB₁ β₁ πB₂` and `C; πB₁ β₁ πB₀ β₀ πB₂` end in the *same*
configuration (block writes obliterate everything inside `R`). After it, `q₀` runs
`compare(t₀, t₁)` solo. In the first execution `getTS(q₀) → getTS(q₁)`, so the answer must be
`true`; in the second `getTS(q₁) → getTS(q₀)`, so it must be `false`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L} {os : Bool}

/-! ### Generic helpers -/

/-- A block write by the processes of a list of (process, object) pairs. -/
abbrev bw (cs : List (P × ι)) : List (Label P (tsObj T)) := blockWrite (cs.map Prod.fst)

@[simp] lemma getTSCount_blockWrite (ps : List P) (p : P) :
    getTSCount (blockWrite (A := tsObj T) ps) p = 0 := by
  simp [getTSCount]

lemma runFrom_mem_cons {C C' : Config (tsObj T) B P L} {β : List (Label P (tsObj T))}
    (h : I.runFrom C β = some C') {S : Set P} (hβ : ∀ ℓ ∈ β, ℓ.proc ∈ S) {q : P} (hq : q ∉ S) :
    C'.loc q = C.loc q ∧ C'.pend q = C.pend q :=
  I.runFrom_other h (fun ℓ hℓ he => hq (he ▸ hβ ℓ hℓ))

lemma mem_bw_proc {cs : List (P × ι)} {ℓ : Label P (tsObj T)} (h : ℓ ∈ bw cs) :
    ℓ.proc ∈ cs.map Prod.fst := mem_blockWrite h

lemma getTSCount_inv_compare (q p : P) (a b : T) :
    getTSCount [(.inv q (.compare a b) : Label P (tsObj T))] p = 0 := by
  simp only [getTSCount, opsOf, List.filterMap_cons, List.filterMap_nil, Label.invOf]
  split_ifs <;> simp [TSOp.isGetTS]

/-! ### Lemma 2.1 -/

/-- **Lemma 2.1** of the paper (due to Ellen, Fatourou and Ruppert), in the form used by the
paper: with `b₀, b₁, b₂` disjoint lists of (process, object) pairs covering the same set `R`
in the reachable configuration `C`, and `U₀`, `U₁` disjoint sets of other processes, it is
impossible that for both `i` a `Uᵢ`-only execution `βᵢ` from `πBᵢ(C)` contains a complete
`getTS` by an idle process `qᵢ ∈ Uᵢ` and leaves the memory outside `R` unchanged. -/
theorem lemma_2_1 (hI : IsTS I os) {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L}
    (hα : I.run α = some C) (b₀ b₁ b₂ : List (P × ι))
    (hnd : (b₀.map Prod.fst ++ b₁.map Prod.fst ++ b₂.map Prod.fst).Nodup)
    (hcov : ∀ c ∈ b₀ ++ b₁ ++ b₂, I.Covers C c.1 c.2) (R : Set ι)
    (hR₀ : ∀ i, i ∈ R ↔ i ∈ b₀.map Prod.snd) (hR₁ : ∀ i, i ∈ R ↔ i ∈ b₁.map Prod.snd)
    (hR₂ : ∀ i, i ∈ R ↔ i ∈ b₂.map Prod.snd)
    (U₀ U₁ : Set P) (hU : Disjoint U₀ U₁) (hUb : ∀ c ∈ b₀ ++ b₁ ++ b₂, c.1 ∉ U₀ ∧ c.1 ∉ U₁)
    (β₀ β₁ : List (Label P (tsObj T))) (hβ₀ : ∀ ℓ ∈ β₀, ℓ.proc ∈ U₀)
    (hβ₁ : ∀ ℓ ∈ β₁, ℓ.proc ∈ U₁)
    {X₀ X₁ D₀ D₁ : Config (tsObj T) B P L}
    (hX₀ : I.runFrom C (bw b₀) = some X₀) (hD₀ : I.runFrom X₀ β₀ = some D₀)
    (hX₁ : I.runFrom C (bw b₁) = some X₁) (hD₁ : I.runFrom X₁ β₁ = some D₁)
    (hmem₀ : ∀ i ∉ R, D₀.mem i = C.mem i) (hmem₁ : ∀ i ∉ R, D₁.mem i = C.mem i)
    (q₀ q₁ : P) (hq₀ : q₀ ∈ U₀) (hq₁ : q₁ ∈ U₁) (hpq₀ : C.pend q₀ = none)
    (hpq₁ : C.pend q₁ = none)
    (hops₀ : opsOf β₀ q₀ = [.getTS]) (hresp₀ : (respsOf β₀ q₀).length = 1)
    (hops₁ : opsOf β₁ q₁ = [.getTS]) (hresp₁ : (respsOf β₁ q₁).length = 1)
    (hfin₀ : D₀.pend q₀ = none)
    (hadm : Adm os (α ++ β₀ ++ β₁)) : False := by
  classical
  -- the two `getTS` instances return timestamps
  have hts : ∀ (b : List (P × ι)) (β : List (Label P (tsObj T))) (X D : Config (tsObj T) B P L)
      (q : P), I.runFrom C (bw b) = some X → I.runFrom X β = some D → C.pend q = none →
      opsOf β q = [.getTS] → (respsOf β q).length = 1 →
      (∀ p, getTSCount β p ≤ getTSCount (β₀ ++ β₁) p) →
      ∃ t, respsOf β q = [.inl t] := by
    intro b β X D q hX hD hpq hops hresp hcβ
    obtain ⟨r, hr⟩ : ∃ r, respsOf β q = [r] := by
      match h : respsOf β q, hresp with
      | [r], _ => exact ⟨r, rfl⟩
    have hv : I.run (α ++ (bw b ++ β)) = some D := by
      rw [run_append_of_eq I hα, runFrom_append_of_eq I hX, hD]
    have had : Adm os (α ++ (bw b ++ β)) := hadm.of_count (fun p => by
      have := hcβ p
      simp only [getTSCount_append, getTSCount_blockWrite] at this ⊢; omega)
    have hcntq := I.run_counts hα q
    simp only [hpq, true_and, ne_eq, not_true_eq_false, false_and, or_false] at hcntq
    obtain ⟨t, ht⟩ := (hI.correct _ ⟨_, hv⟩ had).getTS_ts (q, (opsOf α q).length) r
      (by simp [opOf, hops]) (by simp [respOf, hr, hcntq])
    exact ⟨t, by rw [hr, ht]⟩
  obtain ⟨t₀, hresp₀⟩ := hts b₀ β₀ X₀ D₀ q₀ hX₀ hD₀ hpq₀ hops₀ hresp₀ (fun p => by simp)
  obtain ⟨t₁, hresp₁⟩ := hts b₁ β₁ X₁ D₁ q₁ hX₁ hD₁ hpq₁ hops₁ hresp₁ (fun p => by simp)
  -- disjointness facts
  have hnd' := hnd
  simp only [List.nodup_append, List.mem_append, List.mem_map] at hnd'
  -- membership helpers
  set S₀ : Set P := {q | q ∈ U₀ ∨ q ∈ b₀.map Prod.fst} with hS₀
  set S₁ : Set P := {q | q ∈ U₁ ∨ q ∈ b₁.map Prod.fst} with hS₁
  have hS01 : ∀ q, q ∈ S₀ → q ∉ S₁ := by
    intro q h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact hU.ne_of_mem h0 h1 rfl
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h1
      exact (hUb c (by simp [hc])).1 h0
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h0
      exact (hUb c (by simp [hc])).2 h1
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h0
      obtain ⟨c', hc', he⟩ := List.mem_map.1 h1
      exact hnd'.1.2.2 _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ he.symm
  have hb2S : ∀ c ∈ b₂, c.1 ∉ S₀ ∧ c.1 ∉ S₁ := by
    intro c hc
    have hu := hUb c (by simp [hc])
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact hu.1 h
      · obtain ⟨c', hc', he⟩ := List.mem_map.1 h
        exact hnd'.2.2 _ (Or.inl ⟨c', hc', rfl⟩) _ ⟨c, hc, rfl⟩ he
    · rcases h with h | h
      · exact hu.2 h
      · obtain ⟨c', hc', he⟩ := List.mem_map.1 h
        exact hnd'.2.2 _ (Or.inr ⟨c', hc', rfl⟩) _ ⟨c, hc, rfl⟩ he
  -- labels of the two halves
  have hl₀ : ∀ ℓ ∈ bw b₀ ++ β₀, ℓ.proc ∈ S₀ := by
    intro ℓ hℓ
    rcases List.mem_append.1 hℓ with h | h
    · exact Or.inr (mem_bw_proc h)
    · exact Or.inl (hβ₀ ℓ h)
  have hl₁ : ∀ ℓ ∈ bw b₁ ++ β₁, ℓ.proc ∈ S₁ := by
    intro ℓ hℓ
    rcases List.mem_append.1 hℓ with h | h
    · exact Or.inr (mem_bw_proc h)
    · exact Or.inl (hβ₁ ℓ h)
  have hrD₀ : I.runFrom C (bw b₀ ++ β₀) = some D₀ := by
    rw [runFrom_append_of_eq I hX₀, hD₀]
  have hrD₁ : I.runFrom C (bw b₁ ++ β₁) = some D₁ := by
    rw [runFrom_append_of_eq I hX₁, hD₁]
  have hD₀o : ∀ q ∉ S₀, D₀.loc q = C.loc q ∧ D₀.pend q = C.pend q :=
    fun q hq => runFrom_mem_cons hrD₀ hl₀ hq
  have hD₁o : ∀ q ∉ S₁, D₁.loc q = C.loc q ∧ D₁.pend q = C.pend q :=
    fun q hq => runFrom_mem_cons hrD₁ hl₁ hq
  -- Step 1: from D₀, the block write by b₁ leads to a configuration agreeing with X₁ outside S₀
  have hmem_b : ∀ (b : List (P × ι)), (∀ i, i ∈ R ↔ i ∈ b.map Prod.snd) →
      ∀ (D : Config (tsObj T) B P L), (∀ i ∉ R, D.mem i = C.mem i) →
      ∀ i, i ∉ b.map Prod.snd → D.mem i = C.mem i :=
    fun b hb D hD i hi => hD i (fun h => hi ((hb i).1 h))
  obtain ⟨Y₀, X₁', hY₀, hX₁', hag₀⟩ := blockWrite_agreeOn (I := I) (Q := S₀ᶜ) (cs := b₁)
    (by simpa using hnd.sublist (by simp))
    (fun c hc h => hS01 c.1 h (Or.inr (List.mem_map_of_mem hc)))
    (C := D₀) (D := C)
    (fun c hc => (hcov c (by simp [hc])).congr
      (hD₀o c.1 (fun h => hS01 c.1 h (Or.inr (List.mem_map_of_mem hc)))).1.symm
      (hD₀o c.1 (fun h => hS01 c.1 h (Or.inr (List.mem_map_of_mem hc)))).2.symm)
    (fun q hq => (hD₀o q hq).1) (fun q hq => (hD₀o q hq).2) (hmem_b b₁ hR₁ D₀ hmem₀)
  rw [hX₁] at hX₁'; cases hX₁'
  obtain ⟨Y₁, X₀', hY₁, hX₀', hag₁⟩ := blockWrite_agreeOn (I := I) (Q := S₁ᶜ) (cs := b₀)
    (by simpa using hnd.sublist (by simp))
    (fun c hc h => hS01 c.1 (Or.inr (List.mem_map_of_mem hc)) h)
    (C := D₁) (D := C)
    (fun c hc => (hcov c (by simp [hc])).congr
      (hD₁o c.1 (fun h => hS01 c.1 (Or.inr (List.mem_map_of_mem hc)) h)).1.symm
      (hD₁o c.1 (fun h => hS01 c.1 (Or.inr (List.mem_map_of_mem hc)) h)).2.symm)
    (fun q hq => (hD₁o q hq).1) (fun q hq => (hD₁o q hq).2) (hmem_b b₀ hR₀ D₁ hmem₁)
  rw [hX₀] at hX₀'; cases hX₀'
  -- Step 2: run β₁ after Y₀ and β₀ after Y₁
  obtain ⟨Z₀, hZ₀, hagZ₀⟩ := runFrom_agreeOn (I := I) hag₀.symm (β := β₁)
    (fun ℓ hℓ h => hS01 _ h (Or.inl (hβ₁ ℓ hℓ))) hD₁
  obtain ⟨Z₁, hZ₁, hagZ₁⟩ := runFrom_agreeOn (I := I) hag₁.symm (β := β₀)
    (fun ℓ hℓ h => hS01 _ (Or.inl (hβ₀ ℓ hℓ)) h) hD₀
  -- Z₀ = D₀ on S₁ᶜ, Z₀ = D₁ on S₀ᶜ, similarly Z₁
  have hrZ₀ : I.runFrom D₀ (bw b₁ ++ β₁) = some Z₀ := by rw [runFrom_append_of_eq I hY₀, hZ₀]
  have hrZ₁ : I.runFrom D₁ (bw b₀ ++ β₀) = some Z₁ := by rw [runFrom_append_of_eq I hY₁, hZ₁]
  have hZ₀a : ∀ q ∉ S₁, Z₀.loc q = D₀.loc q ∧ Z₀.pend q = D₀.pend q :=
    fun q hq => runFrom_mem_cons hrZ₀ hl₁ hq
  have hZ₁a : ∀ q ∉ S₀, Z₁.loc q = D₁.loc q ∧ Z₁.pend q = D₁.pend q :=
    fun q hq => runFrom_mem_cons hrZ₁ hl₀ hq
  have hZ₀b : ∀ q ∉ S₀, Z₀.loc q = D₁.loc q ∧ Z₀.pend q = D₁.pend q :=
    fun q hq => ⟨(hagZ₀.loc q hq).symm, (hagZ₀.pend q hq).symm⟩
  have hZ₁b : ∀ q ∉ S₁, Z₁.loc q = D₀.loc q ∧ Z₁.pend q = D₀.pend q :=
    fun q hq => ⟨(hagZ₁.loc q hq).symm, (hagZ₁.pend q hq).symm⟩
  have hZst : ∀ q, Z₀.loc q = Z₁.loc q ∧ Z₀.pend q = Z₁.pend q := by
    intro q
    by_cases h1 : q ∈ S₁
    · have h0 : q ∉ S₀ := fun h => hS01 q h h1
      rw [(hZ₀b q h0).1, (hZ₀b q h0).2, (hZ₁a q h0).1, (hZ₁a q h0).2]; exact ⟨rfl, rfl⟩
    · rw [(hZ₀a q h1).1, (hZ₀a q h1).2, (hZ₁b q h1).1, (hZ₁b q h1).2]; exact ⟨rfl, rfl⟩
  have hZmem : ∀ i ∉ R, Z₀.mem i = Z₁.mem i := by
    intro i hi
    rw [← hagZ₀.mem, ← hagZ₁.mem, hmem₀ i hi, hmem₁ i hi]
  -- Step 3: the final block write by b₂ makes Z₀ and Z₁ identical
  have hb2st : ∀ c ∈ b₂, Z₀.loc c.1 = C.loc c.1 ∧ Z₀.pend c.1 = C.pend c.1 := by
    intro c hc
    obtain ⟨h0, h1⟩ := hb2S c hc
    rw [(hZ₀a c.1 h1).1, (hZ₀a c.1 h1).2, (hD₀o c.1 h0).1, (hD₀o c.1 h0).2]; exact ⟨rfl, rfl⟩
  obtain ⟨F₀, F₁, hF₀, hF₁, hagF⟩ := blockWrite_agreeOn (I := I) (Q := Set.univ) (cs := b₂)
    (by simpa using hnd.sublist (by simp)) (fun _ _ => trivial) (C := Z₀) (D := Z₁)
    (fun c hc => (hcov c (by simp [hc])).congr (hb2st c hc).1.symm (hb2st c hc).2.symm)
    (fun q _ => (hZst q).1) (fun q _ => (hZst q).2)
    (fun i hi => hZmem i (fun h => hi ((hR₂ i).1 h)))
  have hFeq : F₀ = F₁ := hagF.univ_eq
  subst hFeq
  -- the two executions
  set E₀' := α ++ bw b₀ ++ β₀ ++ bw b₁ ++ β₁ ++ bw b₂ with hE₀'
  set E₁' := α ++ bw b₁ ++ β₁ ++ bw b₀ ++ β₀ ++ bw b₂ with hE₁'
  have hrE₀' : I.run E₀' = some F₀ := by
    simp only [hE₀', List.append_assoc]
    rw [run_append_of_eq I hα, runFrom_append_of_eq I hX₀, runFrom_append_of_eq I hD₀,
      runFrom_append_of_eq I hY₀, runFrom_append_of_eq I hZ₀, hF₀]
  have hrE₁' : I.run E₁' = some F₀ := by
    simp only [hE₁', List.append_assoc]
    rw [run_append_of_eq I hα, runFrom_append_of_eq I hX₁, runFrom_append_of_eq I hD₁,
      runFrom_append_of_eq I hY₁, runFrom_append_of_eq I hZ₁, hF₁]
  have hcnt : ∀ p, getTSCount E₀' p = getTSCount (α ++ β₀ ++ β₁) p := by
    intro p; simp [hE₀']
  have hcnt' : ∀ p, getTSCount E₁' p = getTSCount (α ++ β₀ ++ β₁) p := by
    intro p; simp [hE₁']; try omega
  have hadm₀ : Adm os E₀' := hadm.of_count (fun p => (hcnt p).le)
  have hadm₁ : Adm os E₁' := hadm.of_count (fun p => (hcnt' p).le)
  -- q₀ is idle at the end
  have hq₀S₁ : q₀ ∉ S₁ := hS01 q₀ (Or.inl hq₀)
  have hq₁S₀ : q₁ ∉ S₀ := fun h => hS01 q₁ h (Or.inl hq₁)
  have hq₀b₂ : q₀ ∉ b₂.map Prod.fst := by
    intro h; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h; exact (hb2S c hc).1 (Or.inl hq₀)
  have hFq₀ : F₀.pend q₀ = none := by
    rw [(I.runFrom_other hF₀ (fun ℓ hℓ he => hq₀b₂ (by rw [← he]; exact mem_bw_proc hℓ))).2, (hZ₀a q₀ hq₀S₁).2,
      hfin₀]
  -- q₀ runs compare(t₀, t₁) solo
  set o : TSOp T := .compare t₀ t₁ with ho
  have hadmc : Adm os (E₀' ++ [.inv q₀ o]) :=
    hadm₀.append_of_zero (fun p => getTSCount_inv_compare q₀ p t₀ t₁)
  obtain ⟨F', hF', -, hpr, hsops, hsresp⟩ :=
    I.soloOp_spec_of_obstructionFreeOn hI.progress q₀ o (hI.allowed q₀ o) hrE₀' hFq₀ hadmc
  set S := I.soloOp q₀ o F₀
  obtain ⟨r, hr⟩ : ∃ r, respsOf S q₀ = [r] := by
    match h : respsOf S q₀, hsresp with
    | [r], _ => exact ⟨r, rfl⟩
  have hscnt0 : ∀ p, getTSCount S p = 0 := by
    intro p
    by_cases hp : p = q₀
    · rw [hp, getTSCount, hsops]; simp [ho, TSOp.isGetTS]
    · exact getTSCount_of_proc_ne fun ℓ hℓ h => hp (h.symm.trans (hpr ℓ hℓ))
  have hv₀ : I.Valid (E₀' ++ S) := ⟨F', by rw [run_append_of_eq I hrE₀', hF']⟩
  have hv₁ : I.Valid (E₁' ++ S) := ⟨F', by rw [run_append_of_eq I hrE₁', hF']⟩
  have hc₀ := hI.correct _ hv₀ (hadm₀.append_of_zero hscnt0)
  have hc₁ := hI.correct _ hv₁ (hadm₁.append_of_zero hscnt0)
  -- operation identifiers
  have hcnt₀ := I.run_counts hα q₀
  have hcnt₁ := I.run_counts hα q₁
  simp only [hpq₀, hpq₁, true_and, ne_eq, not_true_eq_false, false_and, or_false] at hcnt₀ hcnt₁
  set a₀ := (opsOf α q₀).length
  set a₁ := (opsOf α q₁).length
  have hβ₀q₁ : opsOf β₀ q₁ = [] := opsOf_eq_nil_of_proc_ne
    (fun ℓ hℓ he => hq₁S₀ (Or.inl (he ▸ hβ₀ ℓ hℓ)))
  have hβ₀q₁' : respsOf β₀ q₁ = [] := respsOf_eq_nil_of_proc_ne
    (fun ℓ hℓ he => hq₁S₀ (Or.inl (he ▸ hβ₀ ℓ hℓ)))
  have hβ₁q₀ : opsOf β₁ q₀ = [] := opsOf_eq_nil_of_proc_ne
    (fun ℓ hℓ he => hq₀S₁ (Or.inl (he ▸ hβ₁ ℓ hℓ)))
  have hβ₁q₀' : respsOf β₁ q₀ = [] := respsOf_eq_nil_of_proc_ne
    (fun ℓ hℓ he => hq₀S₁ (Or.inl (he ▸ hβ₁ ℓ hℓ)))
  have hne : q₀ ≠ q₁ := fun h => hU.ne_of_mem hq₀ hq₁ h
  have hSq₁ : opsOf S q₁ = [] := by
    have : getTSCount S q₁ = 0 := hscnt0 q₁
    have hp : ∀ ℓ ∈ S, ℓ.proc ≠ q₁ := by
      intro ℓ hℓ he
      exact hne ((hpr ℓ hℓ).symm.trans he)
    exact opsOf_eq_nil_of_proc_ne hp
  have hSq₁' : respsOf S q₁ = [] := by
    exact respsOf_eq_nil_of_proc_ne (fun ℓ hℓ he => hne ((hpr ℓ hℓ).symm.trans he))
  let g₀ : OpId P := (q₀, a₀)
  let g₁ : OpId P := (q₁, a₁)
  let c : OpId P := (q₀, a₀ + 1)
  -- facts in E₀ = E₀' ++ S
  have e0g0 : opOf (E₀' ++ S) g₀ = some .getTS := by
    simp [opOf, g₀, hE₀', hops₀, hβ₁q₀, hsops, a₀]
  have e0g0r : respOf (E₀' ++ S) g₀ = some (.inl t₀) := by
    simp [respOf, g₀, hE₀', hresp₀, hβ₁q₀', hr, a₀, hcnt₀]
  have e0g1 : opOf (E₀' ++ S) g₁ = some .getTS := by
    simp [opOf, g₁, hE₀', hops₁, hβ₀q₁, hSq₁, a₁]
  have e0g1r : respOf (E₀' ++ S) g₁ = some (.inl t₁) := by
    simp [respOf, g₁, hE₀', hresp₁, hβ₀q₁', hSq₁', a₁, hcnt₁]
  have e0c : opOf (E₀' ++ S) c = some o := by
    simp [opOf, c, hE₀', hops₀, hβ₁q₀, hsops, a₀]
  have e0cr : respOf (E₀' ++ S) c = some r := by
    simp [respOf, c, hE₀', hresp₀, hβ₁q₀', hr, a₀, hcnt₀]
  have e1g0 : opOf (E₁' ++ S) g₀ = some .getTS := by
    simp [opOf, g₀, hE₁', hops₀, hβ₁q₀, hsops, a₀]
  have e1g0r : respOf (E₁' ++ S) g₀ = some (.inl t₀) := by
    simp [respOf, g₀, hE₁', hresp₀, hβ₁q₀', hr, a₀, hcnt₀]
  have e1g1 : opOf (E₁' ++ S) g₁ = some .getTS := by
    simp [opOf, g₁, hE₁', hops₁, hβ₀q₁, hSq₁, a₁]
  have e1g1r : respOf (E₁' ++ S) g₁ = some (.inl t₁) := by
    simp [respOf, g₁, hE₁', hresp₁, hβ₀q₁', hSq₁', a₁, hcnt₁]
  have e1c : opOf (E₁' ++ S) c = some o := by
    simp [opOf, c, hE₁', hops₀, hβ₁q₀, hsops, a₀]
  have e1cr : respOf (E₁' ++ S) c = some r := by
    simp [respOf, c, hE₁', hresp₀, hβ₁q₀', hr, a₀, hcnt₀]
  -- precedences
  have p0a : Precedes (E₀' ++ S) g₀ g₁ :=
    ⟨α ++ bw b₀ ++ β₀, bw b₁ ++ β₁ ++ bw b₂ ++ S, by simp [hE₀'],
      by simp [Completed, g₀, hresp₀, hcnt₀, a₀], by simp [Invoked, g₁, hβ₀q₁, a₁]⟩
  have p0b : Precedes (E₀' ++ S) g₁ c :=
    ⟨α ++ bw b₀ ++ β₀ ++ bw b₁ ++ β₁, bw b₂ ++ S, by simp [hE₀'],
      by simp [Completed, g₁, hresp₁, hβ₀q₁', hcnt₁, a₁], by simp [Invoked, c, hops₀, hβ₁q₀, a₀]⟩
  have p1a : Precedes (E₁' ++ S) g₁ g₀ :=
    ⟨α ++ bw b₁ ++ β₁, bw b₀ ++ β₀ ++ bw b₂ ++ S, by simp [hE₁'],
      by simp [Completed, g₁, hresp₁, hcnt₁, a₁], by simp [Invoked, g₀, hβ₁q₀, a₀]⟩
  have p1b : Precedes (E₁' ++ S) g₀ c :=
    ⟨α ++ bw b₁ ++ β₁ ++ bw b₀ ++ β₀, bw b₂ ++ S, by simp [hE₁'],
      by simp [Completed, g₀, hresp₀, hβ₁q₀', hcnt₀, a₀], by simp [Invoked, c, hops₀, hβ₁q₀, a₀]⟩
  have h0 := (hc₀.order g₀ g₁ c t₀ t₁ o r e0g0 e0g0r e0g1 e0g1r p0a p0b e0c e0cr).1 rfl
  have h1 := (hc₁.order g₁ g₀ c t₁ t₀ o r e1g1 e1g1r e1g0 e1g0r p1a p1b e1c e1cr).2 rfl
  rw [h0] at h1; simp at h1

end Cslib.SharedMemory.Timestamp
