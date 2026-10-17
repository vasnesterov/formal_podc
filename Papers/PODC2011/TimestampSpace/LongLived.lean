import Papers.PODC2011.TimestampSpace.LongLivedBasic

/-!
# Theorem 1.1: space lower bound for long-lived timestamps

Every long-lived (obstruction-free) timestamp implementation for `n` processes from read/write-like
base objects (e.g. registers) uses at least `⌊n/6⌋ > n/6 - 1` base objects.

Proof (Section 3 of the paper): `lemma_3_1` (a Burns–Lynch style pigeonhole on signatures
yields two `(3,k)`-configurations `C₀`, `C₁` with the same signature, the execution from `C₀` to `C₁`
starting with three block writes to `R₃(C₀)`) and `lemma_3_2` (by induction on `k`, using
`lemma_2_1`, from every reachable quiescent configuration a `(3,k)`-configuration is reachable
using `2k` processes).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L}

/-! ### Block writes -/

lemma mem_bw_proc' {cs : List (P × ι)} {ℓ : Label P (tsObj T)} (h : ℓ ∈ bw cs) :
    ∃ c ∈ cs, ℓ.proc = c.1 := by
  obtain ⟨q, hq, he⟩ := List.mem_map.1 (mem_bw_proc h); exact ⟨q, hq, he.symm⟩

/-- **Core of the inductive step of Lemma 3.2.** From `C₀`, the block write `b`, then a solo
execution `β` of `p` that does not change the memory outside `R` and ends with `p` covering `r`,
then the block writes `b'`, `b₂` (both covering exactly `R`) and `η` (without `p`), lead to a
configuration `X` in which `p` covers `r` and which every other process cannot distinguish from
the configuration `C₁` reached from `W₀` by `b₂` and `η`, where `W₀` agrees with `bw b ++ bw b'`
on all processes and on the memory outside `R`. -/
lemma insert_cover {C₀ A D W W₀ C₁ : Config (tsObj T) B P L} {b b' b₂ : List (P × ι)}
    {R : Set ι} {p : P} {r : ι}
    (hnd : (b.map Prod.fst ++ b'.map Prod.fst ++ b₂.map Prod.fst).Nodup)
    (hcov : ∀ c ∈ b ++ b' ++ b₂, I.Covers C₀ c.1 c.2)
    (hR' : ∀ j, j ∈ R ↔ j ∈ b'.map Prod.snd) (hR₂ : ∀ j, j ∈ R ↔ j ∈ b₂.map Prod.snd)
    (hp : ∀ c ∈ b ++ b' ++ b₂, c.1 ≠ p)
    (hA : I.runFrom C₀ (bw b) = some A) {β : List (Label P (tsObj T))}
    (hβ : ∀ ℓ ∈ β, ℓ.proc = p) (hD : I.runFrom A β = some D)
    (hDm : ∀ j ∉ R, D.mem j = A.mem j) (hDc : I.Covers D p r)
    (hW : I.runFrom A (bw b') = some W)
    (hW₀ : ∀ q, W₀.loc q = W.loc q ∧ W₀.pend q = W.pend q) (hW₀m : ∀ j ∉ R, W₀.mem j = W.mem j)
    {η : List (Label P (tsObj T))} (hη : ∀ ℓ ∈ η, ℓ.proc ≠ p)
    (hC₁ : I.runFrom W₀ (bw b₂ ++ η) = some C₁) :
    ∃ X, I.runFrom D (bw b' ++ bw b₂ ++ η) = some X ∧
      (∀ q, q ≠ p → X.loc q = C₁.loc q ∧ X.pend q = C₁.pend q) ∧ I.Covers X p r := by
  obtain ⟨hnd₁₂, hnd₃, hdis₃⟩ := List.nodup_append.1 hnd
  obtain ⟨hnd₁, hnd₂, hdis₁₂⟩ := List.nodup_append.1 hnd₁₂
  -- `b'` still covers after the block write `b`
  have hcb'A : ∀ c ∈ b', I.Covers A c.1 c.2 := by
    intro c hc
    have hn : c.1 ∉ b.map Prod.fst := fun h => hdis₁₂ _ h _ (List.mem_map_of_mem hc) rfl
    have h1 := runFrom_blockWrite_other hA hn
    exact (hcov c (by simp [hc])).congr h1.1.symm h1.2.symm
  have hAD : ∀ q, q ≠ p → D.loc q = A.loc q ∧ D.pend q = A.pend q := fun q hq =>
    I.runFrom_other hD (fun ℓ hℓ he => hq (he ▸ hβ ℓ hℓ))
  obtain ⟨W₁, W', hW₁, hW', hag₁⟩ := blockWrite_agreeOn (I := I) (Q := {q | q ≠ p}) (cs := b')
    hnd₂ (fun c hc => hp c (by simp [hc])) (C := A) (D := D) hcb'A
    (fun q hq => (hAD q hq).1.symm) (fun q hq => (hAD q hq).2.symm)
    (fun j hj => (hDm j (fun h => hj ((hR' j).1 h))).symm)
  rw [hW] at hW₁; cases hW₁
  -- `b₂` covers in `W₀`
  have hcb₂ : ∀ c ∈ b₂, I.Covers W₀ c.1 c.2 := by
    intro c hc
    have hn : c.1 ∉ b.map Prod.fst :=
      fun h => hdis₃ _ (List.mem_append_left _ h) _ (List.mem_map_of_mem hc) rfl
    have hn' : c.1 ∉ b'.map Prod.fst :=
      fun h => hdis₃ _ (List.mem_append_right _ h) _ (List.mem_map_of_mem hc) rfl
    have h1 := runFrom_blockWrite_other hA hn
    have h2 := runFrom_blockWrite_other hW hn'
    exact (hcov c (by simp [hc])).congr (by rw [(hW₀ c.1).1, h2.1, h1.1]) (by rw [(hW₀ c.1).2, h2.2, h1.2])
  obtain ⟨Z₀, Z', hZ₀, hZ', hag₂⟩ := blockWrite_agreeOn (I := I) (Q := {q | q ≠ p}) (cs := b₂)
    hnd₃ (fun c hc => hp c (by simp [hc])) (C := W₀) (D := W') hcb₂
    (fun q hq => by rw [(hW₀ q).1]; exact hag₁.loc q hq)
    (fun q hq => by rw [(hW₀ q).2]; exact hag₁.pend q hq)
    (fun j hj => by
      have hjR : j ∉ R := fun h => hj ((hR₂ j).1 h)
      rw [hW₀m j hjR, hag₁.mem])
  rw [runFrom_append_of_eq I hZ₀] at hC₁
  obtain ⟨X, hX, hag₃⟩ := runFrom_agreeOn (I := I) hag₂ (β := η) (fun ℓ hℓ => hη ℓ hℓ) hC₁
  refine ⟨X, by rw [runFrom_append_of_eq I (by rw [runFrom_append_of_eq I hW', hZ'] :
    I.runFrom D (bw b' ++ bw b₂) = some Z'), hX],
    fun q hq => ⟨(hag₃.loc q hq).symm, (hag₃.pend q hq).symm⟩, ?_⟩
  have h1 := I.runFrom_other hX (fun ℓ hℓ he => hη ℓ hℓ he)
  have h2 := runFrom_blockWrite_other hZ' (fun h => by
    obtain ⟨c, hc, he⟩ := List.mem_map.1 h; exact hp c (by simp [hc]) he)
  have h3 := runFrom_blockWrite_other hW' (fun h => by
    obtain ⟨c, hc, he⟩ := List.mem_map.1 h; exact hp c (by simp [hc]) he)
  exact hDc.congr (by rw [h1.1, h2.1, h3.1]) (by rw [h1.2, h2.2, h3.2])

/-! ### The inductive step of Lemma 3.2 -/

lemma mem_bw_append {b₀ b₁ b₂ : List (P × ι)} {η : List (Label P (tsObj T))}
    {ℓ : Label P (tsObj T)} (h : ℓ ∈ bw b₀ ++ bw b₁ ++ bw b₂ ++ η) :
    (∃ c ∈ b₀ ++ b₁ ++ b₂, ℓ.proc = c.1) ∨ ℓ ∈ η := by
  simp only [List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨c, hc, he⟩ := mem_bw_proc' h; exact Or.inl ⟨c, by simp [hc], he⟩
  · obtain ⟨c, hc, he⟩ := mem_bw_proc' h; exact Or.inl ⟨c, by simp [hc], he⟩
  · obtain ⟨c, hc, he⟩ := mem_bw_proc' h; exact Or.inl ⟨c, by simp [hc], he⟩
  · exact Or.inr h

variable [Fintype P] [Fintype ι]

/-- **Inductive step of Lemma 3.2.** Let `C₀`, `C₁` be `(3,k)`-configurations with the same
signature, `C₁` reached from the reachable `C₀` by three disjoint block writes to `R₃(C₀)`
followed by `η`, and let `p ≠ p'` be idle in `C₀` and not take part in `η`. Then a
`(3,k+1)`-configuration is reachable from `C₀` using only `p`, `p'` and the processes of the
block writes and of `η`. -/
theorem step_3_2 (hI : IsTS I false) (hB : RWLike B)
    {α : List (Label P (tsObj T))} {C₀ C₁ : Config (tsObj T) B P L} (hα : I.run α = some C₀)
    {b₀ b₁ b₂ : List (P × ι)} (htr : Triple I C₀ (R3 I C₀) b₀ b₁ b₂)
    {η : List (Label P (tsObj T))} {k : ℕ}
    (hC₁ : I.runFrom C₀ (bw b₀ ++ bw b₁ ++ bw b₂ ++ η) = some C₁)
    (h₀ : Is3k I C₀ k) (h₁ : Is3k I C₁ k) (hsig : sig I C₀ = sig I C₁)
    {p p' : P} (hpp : p ≠ p') (hp : C₀.pend p = none) (hp' : C₀.pend p' = none)
    (hη : ∀ ℓ ∈ η, ℓ.proc ≠ p ∧ ℓ.proc ≠ p') (S : Set P) (hpS : p ∈ S) (hp'S : p' ∈ S)
    (hbS : ∀ c ∈ b₀ ++ b₁ ++ b₂, c.1 ∈ S) (hηS : ∀ ℓ ∈ η, ℓ.proc ∈ S) :
    ∃ σ X, (∀ ℓ ∈ σ, ℓ.proc ∈ S) ∧ I.runFrom C₀ σ = some X ∧ Is3k I X (k + 1) := by
  classical
  set R := R3 I C₀ with hRdef
  have hbp : ∀ c ∈ b₀ ++ b₁ ++ b₂, c.1 ≠ p ∧ c.1 ≠ p' := fun c hc =>
    ⟨fun h => (htr.covers c hc).1 (h ▸ hp), fun h => (htr.covers c hc).1 (h ▸ hp')⟩
  obtain ⟨hnd₁₂, -, -⟩ := List.nodup_append.1 htr.nodup
  obtain ⟨hnd₁, hnd₂, -⟩ := List.nodup_append.1 hnd₁₂
  obtain ⟨W₀, hW₀, hC₁'⟩ := I.runFrom_eq_some_of_append (α := bw b₀ ++ bw b₁)
    (β := bw b₂ ++ η) (by rwa [← List.append_assoc])
  have hlab : ∀ ℓ ∈ bw b₀ ++ bw b₁ ++ bw b₂ ++ η, ℓ.proc ≠ p ∧ ℓ.proc ≠ p' := by
    intro ℓ hℓ
    rcases mem_bw_append hℓ with ⟨c, hc, he⟩ | h
    · rw [he]; exact hbp c hc
    · exact hη ℓ h
  have hC₁p : C₁.pend p = none :=
    (I.runFrom_other hC₁ (fun ℓ hℓ => (hlab ℓ hℓ).1)).2.trans hp
  have hC₁p' : C₁.pend p' = none :=
    (I.runFrom_other hC₁ (fun ℓ hℓ => (hlab ℓ hℓ).2)).2.trans hp'
  -- the case where some process `q` covers an object outside `R` after a solo run
  have finish : ∀ (b b' : List (P × ι)) (q : P) (A D W : Config (tsObj T) B P L)
      (β : List (Label P (tsObj T))) (r : ι),
      (b.map Prod.fst ++ b'.map Prod.fst ++ b₂.map Prod.fst).Nodup →
      (∀ c ∈ b ++ b' ++ b₂, I.Covers C₀ c.1 c.2) → (∀ j, j ∈ R ↔ j ∈ b'.map Prod.snd) →
      (∀ c ∈ b ++ b' ++ b₂, c.1 ≠ q ∧ c.1 ∈ S) → q ∈ S → C₁.pend q = none →
      (∀ ℓ ∈ η, ℓ.proc ≠ q) →
      I.runFrom C₀ (bw b) = some A → (∀ ℓ ∈ β, ℓ.proc = q) → I.runFrom A β = some D →
      (∀ j ∉ R, D.mem j = A.mem j) → I.Covers D q r → r ∉ R →
      I.runFrom A (bw b') = some W →
      (∀ q, W₀.loc q = W.loc q ∧ W₀.pend q = W.pend q) → (∀ j ∉ R, W₀.mem j = W.mem j) →
      ∃ σ X, (∀ ℓ ∈ σ, ℓ.proc ∈ S) ∧ I.runFrom C₀ σ = some X ∧ Is3k I X (k + 1) := by
    intro b b' q A D W β r hnd hcov hR' hqb hqS hC₁q hηq hA hβ hD hDm hDc hr hW hag hagm
    obtain ⟨X, hX, hXag, hXc⟩ := insert_cover hnd hcov hR' htr.mem₂ (fun c hc => (hqb c hc).1)
      hA hβ hD hDm hDc hW hag hagm hηq hC₁'
    refine ⟨bw b ++ β ++ (bw b' ++ bw b₂ ++ η), X, fun ℓ hℓ => ?_, ?_,
      h₁.insert hC₁q hXag hXc ?_⟩
    · simp only [List.mem_append] at hℓ
      rcases hℓ with (h | h) | ((h | h) | h)
      · obtain ⟨c, hc, he⟩ := mem_bw_proc' h; rw [he]; exact (hqb c (by simp [hc])).2
      · rw [hβ ℓ h]; exact hqS
      · obtain ⟨c, hc, he⟩ := mem_bw_proc' h; rw [he]; exact (hqb c (by simp [hc])).2
      · obtain ⟨c, hc, he⟩ := mem_bw_proc' h; rw [he]; exact (hqb c (by simp [hc])).2
      · exact hηS ℓ h
    · rw [runFrom_append_of_eq I (by rw [runFrom_append_of_eq I hA, hD] :
        I.runFrom C₀ (bw b ++ β) = some D), hX]
    · rw [← hsig]
      have h3 := h₀.1 r
      have : sig I C₀ r ≠ 3 := hr
      omega
  -- the two block writes and the two solo `getTS` runs
  have hpb₀ : p ∉ b₀.map Prod.fst := fun h => by
    obtain ⟨c, hc, he⟩ := List.mem_map.1 h; exact (hbp c (by simp [hc])).1 he
  have hpb₁ : p' ∉ b₁.map Prod.fst := fun h => by
    obtain ⟨c, hc, he⟩ := List.mem_map.1 h; exact (hbp c (by simp [hc])).2 he
  obtain ⟨A₀, hA₀, hA₀o, hA₀m⟩ := blockWrite_run (I := I) hnd₁
    (fun c hc => htr.covers c (by simp [hc]))
  obtain ⟨A₁, hA₁, hA₁o, hA₁m⟩ := blockWrite_run (I := I) hnd₂
    (fun c hc => htr.covers c (by simp [hc]))
  obtain ⟨β₀, D₀, hD₀, hβ₀, hD₀m, hc₀⟩ := solo_getTS_or_covers hI hB
    (by rw [run_append_of_eq I hα]; exact hA₀) (((hA₀o p hpb₀).2).trans hp) R
  obtain ⟨β₁, D₁, hD₁, hβ₁, hD₁m, hc₁⟩ := solo_getTS_or_covers hI hB
    (by rw [run_append_of_eq I hα]; exact hA₁) (((hA₁o p' hpb₁).2).trans hp') R
  have hSall : ∀ c ∈ b₀ ++ b₁ ++ b₂, c.1 ≠ p ∧ c.1 ∈ S := fun c hc => ⟨(hbp c hc).1, hbS c hc⟩
  have hSall' : ∀ c ∈ b₁ ++ b₀ ++ b₂, c.1 ≠ p' ∧ c.1 ∈ S := fun c hc => by
    have hc' : c ∈ b₀ ++ b₁ ++ b₂ := by simp only [List.mem_append] at hc ⊢; tauto
    exact ⟨(hbp c hc').2, hbS c hc'⟩
  rcases hc₀ with ⟨hops₀, hresp₀, hfin₀⟩ | ⟨r, hrR, hcov₀⟩
  · rcases hc₁ with ⟨hops₁, hresp₁, -⟩ | ⟨r, hrR, hcov₁⟩
    · -- both complete their `getTS` without writing outside `R`: impossible by Lemma 2.1
      exfalso
      exact lemma_2_1 hI hα b₀ b₁ b₂ htr.nodup htr.covers R htr.mem₀ htr.mem₁ htr.mem₂
        {p} {p'} (Set.disjoint_singleton.2 hpp)
        (fun c hc => ⟨by simpa using (hbp c hc).1, by simpa using (hbp c hc).2⟩)
        β₀ β₁ (fun ℓ hℓ => by simpa using hβ₀ ℓ hℓ) (fun ℓ hℓ => by simpa using hβ₁ ℓ hℓ)
        hA₀ hD₀ hA₁ hD₁
        (fun i hi => by rw [hD₀m i hi, hA₀m i (fun h => hi ((htr.mem₀ i).2 h))])
        (fun i hi => by rw [hD₁m i hi, hA₁m i (fun h => hi ((htr.mem₁ i).2 h))])
        p p' rfl rfl hp hp' hops₀ hresp₀ hops₁ hresp₁ hfin₀ (adm_false _)
    · -- `p'` covers `r ∉ R` after `πB₁`: compare with `πB₁ πB₀ πB₂ η`
      have hcov' : ∀ c ∈ b₁ ++ b₀, I.Covers C₀ c.1 c.2 := fun c hc =>
        htr.covers c (by simp only [List.mem_append] at hc ⊢; tauto)
      obtain ⟨X, X', hX, hX', hXX, hXXm⟩ := blockWrite_swap (I := I) (b := b₀) (b' := b₁)
        hnd₁₂ (fun c hc => htr.covers c (by simp only [List.mem_append] at hc ⊢; tauto))
        (fun j => (htr.mem₀ j).symm.trans (htr.mem₁ j))
      rw [hW₀] at hX; cases hX
      rw [runFrom_append_of_eq I hA₁] at hX'
      exact finish b₁ b₀ p' A₁ D₁ X' β₁ r
        ((List.perm_append_comm.append_right _).nodup_iff.1 htr.nodup)
        (fun c hc => htr.covers c (by simp only [List.mem_append] at hc ⊢; tauto))
        htr.mem₀ hSall' hp'S hC₁p' (fun ℓ hℓ => (hη ℓ hℓ).2) hA₁ hβ₁ hD₁ hD₁m hcov₁ hrR hX'
        hXX (fun j hj => hXXm j (fun h => hj ((htr.mem₀ j).2 h)))
  · -- `p` covers `r ∉ R` after `πB₀`
    rw [runFrom_append_of_eq I hA₀] at hW₀
    exact finish b₀ b₁ p A₀ D₀ W₀ β₀ r htr.nodup htr.covers htr.mem₁ hSall hpS hC₁p
      (fun ℓ hℓ => (hη ℓ hℓ).1) hA₀ hβ₀ hD₀ hD₀m hcov₀ hrR hW₀ (fun _ => ⟨rfl, rfl⟩)
      (fun _ _ => rfl)

/-! ### Lemma 3.1 -/

/-- The block writes of a `Triple` in a configuration in which all processes outside `S` are idle
are by processes of `S`. -/
lemma Triple.mem_S {C : Config (tsObj T) B P L} {R : Set ι} {b₀ b₁ b₂ : List (P × ι)}
    (htr : Triple I C R b₀ b₁ b₂) {S : Finset P} (hidle : ∀ q ∉ S, C.pend q = none) :
    ∀ c ∈ b₀ ++ b₁ ++ b₂, c.1 ∈ S := fun c hc => by
  by_contra h; exact (htr.covers c hc).1 (hidle _ h)

lemma Triple.bw_mem_S {C : Config (tsObj T) B P L} {R : Set ι} {b₀ b₁ b₂ : List (P × ι)}
    (htr : Triple I C R b₀ b₁ b₂) {S : Finset P} (hidle : ∀ q ∉ S, C.pend q = none)
    {η : List (Label P (tsObj T))} (hη : ∀ ℓ ∈ η, ℓ.proc ∈ S) :
    ∀ ℓ ∈ bw b₀ ++ bw b₁ ++ bw b₂ ++ η, ℓ.proc ∈ S := fun ℓ hℓ => by
  rcases mem_bw_append hℓ with ⟨c, hc, he⟩ | h
  · rw [he]; exact htr.mem_S hidle c hc
  · exact hη ℓ h

/-- One round of the construction in the proof of Lemma 3.1: from a reachable
`(3,k)`-configuration `E` (processes outside `S` idle), three block writes to `R₃(E)`, then
all pending processes of `S` finish their operations, then the hypothesis leads to a reachable
`(3,k)`-configuration `E'`. -/
lemma round_3_1 (hI : IsTS I false) (S : Finset P) (k : ℕ)
    (H : ∀ (α : List (Label P (tsObj T))) (D : Config (tsObj T) B P L), I.run α = some D →
      D.Quiescent → ∃ σ E, (∀ ℓ ∈ σ, ℓ.proc ∈ S) ∧ I.runFrom D σ = some E ∧ Is3k I E k)
    {α : List (Label P (tsObj T))} {E : Config (tsObj T) B P L} (hα : I.run α = some E)
    (hidle : ∀ q ∉ S, E.pend q = none) :
    ∃ E' b₀ b₁ b₂ η, Triple I E (R3 I E) b₀ b₁ b₂ ∧ (∀ ℓ ∈ η, ℓ.proc ∈ S) ∧
      I.runFrom E (bw b₀ ++ bw b₁ ++ bw b₂ ++ η) = some E' ∧ Is3k I E' k ∧
      (∀ q ∉ S, E'.pend q = none) := by
  obtain ⟨b₀, b₁, b₂, htr⟩ := exists_triple (I := I) E
  have hbw : (bw b₀ ++ bw b₁ ++ bw b₂ : List (Label P (tsObj T))) = bw (b₀ ++ b₁ ++ b₂) := by
    simp [blockWrite]
  obtain ⟨F, hF, -, -⟩ := blockWrite_run (I := I) (cs := b₀ ++ b₁ ++ b₂)
    (by simpa using htr.nodup) htr.covers
  have hFp : F.pend = E.pend := runFrom_pend_of_tau hF blockWrite_tau
  obtain ⟨γ, F', hγ, -, hF', hfin, hoth⟩ := I.exists_finish hI.progress
    (fun _ _ _ _ => adm_false _) S.toList (α := α ++ bw (b₀ ++ b₁ ++ b₂))
    (by rw [run_append_of_eq I hα]; exact hF) (adm_false _)
  have hq : F'.Quiescent := fun q => by
    by_cases hqS : q ∈ S
    · exact hfin q (by simpa using hqS)
    · rw [(hoth q (by simpa using hqS)).2, hFp]; exact hidle q hqS
  obtain ⟨σ, E', hσ, hE', h3⟩ := H _ F' (by
    rw [run_append_of_eq I (by rw [run_append_of_eq I hα]; exact hF), hF']) hq
  refine ⟨E', b₀, b₁, b₂, γ ++ σ, htr, fun ℓ hℓ => ?_, ?_, h3, fun q hqS => ?_⟩
  · rcases List.mem_append.1 hℓ with h | h
    · simpa using hγ ℓ h
    · exact hσ ℓ h
  · rw [show (bw b₀ ++ bw b₁ ++ bw b₂ ++ (γ ++ σ) : List (Label P (tsObj T))) =
      bw (b₀ ++ b₁ ++ b₂) ++ (γ ++ σ) by rw [← hbw],
      runFrom_append_of_eq I hF, runFrom_append_of_eq I hF', hE']
  · rw [(I.runFrom_other hE' (fun ℓ hℓ he => hqS (by rw [← he]; exact hσ ℓ hℓ))).2]; exact hq q

/-- **Lemma 3.1.** Let `S` be a set of processes such that from every reachable quiescent
configuration an `S`-only execution leads to a `(3,k)`-configuration. Then from every reachable
quiescent configuration `D` there are `S`-only executions `γ₀` and `γ₁ = πB₀ πB₁ πB₂ η` leading
from `D` to a `(3,k)`-configuration `C₀` and from `C₀` to a `(3,k)`-configuration `C₁` with
`sig(C₀) = sig(C₁)`, where `B₀`, `B₁`, `B₂` are disjoint sets of processes each covering
`R₃(C₀)`. -/
theorem lemma_3_1 (hI : IsTS I false) (S : Finset P) (k : ℕ)
    (H : ∀ (α : List (Label P (tsObj T))) (D : Config (tsObj T) B P L), I.run α = some D →
      D.Quiescent → ∃ σ E, (∀ ℓ ∈ σ, ℓ.proc ∈ S) ∧ I.runFrom D σ = some E ∧ Is3k I E k)
    {α : List (Label P (tsObj T))} {D : Config (tsObj T) B P L} (hα : I.run α = some D)
    (hD : D.Quiescent) :
    ∃ (C₀ C₁ : Config (tsObj T) B P L) (γ₀ η : List (Label P (tsObj T)))
      (b₀ b₁ b₂ : List (P × ι)),
      (∀ ℓ ∈ γ₀, ℓ.proc ∈ S) ∧ (∀ ℓ ∈ bw b₀ ++ bw b₁ ++ bw b₂ ++ η, ℓ.proc ∈ S) ∧
      I.runFrom D γ₀ = some C₀ ∧ I.runFrom C₀ (bw b₀ ++ bw b₁ ++ bw b₂ ++ η) = some C₁ ∧
      Is3k I C₀ k ∧ Is3k I C₁ k ∧ sig I C₀ = sig I C₁ ∧ Triple I C₀ (R3 I C₀) b₀ b₁ b₂ := by
  classical
  -- reachable `(3,k)`-configurations whose processes outside `S` are idle
  let Good : Config (tsObj T) B P L → Prop := fun E =>
    (∃ β, I.run β = some E) ∧ Is3k I E k ∧ ∀ q ∉ S, E.pend q = none
  have hround : ∀ E, Good E → ∃ E' b₀ b₁ b₂ η, Good E' ∧ Triple I E (R3 I E) b₀ b₁ b₂ ∧
      (∀ ℓ ∈ η, ℓ.proc ∈ S) ∧ I.runFrom E (bw b₀ ++ bw b₁ ++ bw b₂ ++ η) = some E' := by
    rintro E ⟨⟨β, hβ⟩, -, hidle⟩
    obtain ⟨E', b₀, b₁, b₂, η, htr, hη, hE', h3, hidle'⟩ := round_3_1 hI S k H hβ hidle
    exact ⟨E', b₀, b₁, b₂, η, ⟨⟨_, by rw [run_append_of_eq I hβ, hE']⟩, h3, hidle'⟩, htr, hη,
      hE'⟩
  choose! nx f₀ f₁ f₂ fη hgood htr hη hrun using hround
  -- the initial `(3,k)`-configuration `E₀ = σ(D)`
  obtain ⟨σ, E₀, hσ, hE₀, h3₀⟩ := H α D hα hD
  have hgood₀ : Good E₀ := ⟨⟨_, by rw [run_append_of_eq I hα, hE₀]⟩, h3₀,
    fun q hq => by rw [(I.runFrom_other hE₀ (fun ℓ hℓ he => hq (by rw [← he]; exact hσ ℓ hℓ))).2]; exact hD q⟩
  let E : ℕ → Config (tsObj T) B P L := fun n => nx^[n] E₀
  have hEs : ∀ n, E (n + 1) = nx (E n) := fun n => Function.iterate_succ_apply' nx n E₀
  have hgE : ∀ n, Good (E n) := by
    intro n; induction n with
    | zero => exact hgood₀
    | succ n ih => rw [hEs]; exact hgood _ ih
  have hstep : ∀ n, ∀ ℓ ∈ bw (f₀ (E n)) ++ bw (f₁ (E n)) ++ bw (f₂ (E n)) ++ fη (E n),
      ℓ.proc ∈ S := fun n =>
    (htr _ (hgE n)).bw_mem_S (hgE n).2.2 (hη _ (hgE n))
  have hreach : ∀ m d, ∃ ρ, (∀ ℓ ∈ ρ, ℓ.proc ∈ S) ∧ I.runFrom (E m) ρ = some (E (m + d)) := by
    intro m d; induction d with
    | zero => exact ⟨[], by simp, rfl⟩
    | succ d ih =>
      obtain ⟨ρ, hρ, hr⟩ := ih
      refine ⟨ρ ++ (bw (f₀ (E (m + d))) ++ bw (f₁ (E (m + d))) ++ bw (f₂ (E (m + d))) ++
        fη (E (m + d))), fun ℓ hℓ => ?_, ?_⟩
      · rcases List.mem_append.1 hℓ with h | h
        · exact hρ ℓ h
        · exact hstep _ ℓ h
      · rw [runFrom_append_of_eq I hr, hrun _ (hgE _), ← Nat.add_assoc, hEs]
  -- pigeonhole on the (finitely many) signatures
  let sg : ℕ → ι → Fin 4 := fun n i => ⟨min (sig I (E n) i) 3, by omega⟩
  obtain ⟨m, n, hmn, hsg⟩ := Finite.exists_ne_map_eq_of_infinite sg
  have hsig : ∀ m n, sg m = sg n → sig I (E m) = sig I (E n) := by
    intro m n h; funext i
    have h1 := congrArg Fin.val (congrFun h i)
    have hm := (hgE m).2.1.1 i
    have hn := (hgE n).2.1.1 i
    simp only [sg] at h1; omega
  wlog hlt : m < n generalizing m n
  · exact this n m hmn.symm hsg.symm (by omega)
  obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - (m + 1), by omega⟩
  obtain ⟨ρ₀, hρ₀, hr₀⟩ := hreach 0 m
  obtain ⟨ρ₁, hρ₁, hr₁⟩ := hreach (m + 1) d
  rw [Nat.zero_add] at hr₀
  refine ⟨E m, E (m + 1 + d), σ ++ ρ₀, fη (E m) ++ ρ₁, f₀ (E m), f₁ (E m), f₂ (E m),
    fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, by rw [runFrom_append_of_eq I hE₀]; exact hr₀, ?_,
    (hgE m).2.1, (hgE _).2.1, hsig _ _ hsg, htr _ (hgE m)⟩
  · rcases List.mem_append.1 hℓ with h | h
    · exact hσ ℓ h
    · exact hρ₀ ℓ h
  · simp only [← List.append_assoc, List.mem_append] at hℓ
    rcases hℓ with h | h
    · exact hstep m ℓ (by simpa only [List.mem_append] using h)
    · exact hρ₁ ℓ h
  · rw [← List.append_assoc, runFrom_append_of_eq I (hrun _ (hgE m)), ← hEs, hr₁]

/-! ### Lemma 3.2 and Theorem 1.1 -/

/-- **Lemma 3.2** (with an arbitrary set `S` of at least `2k` processes in place of the paper's
`P_{2k} = {p₁, …, p_{2k}}`). In a long-lived timestamp implementation from read/write-like base
objects, for every `k` and every set `S` of at least `2k` processes, from every reachable quiescent
configuration `D` some `S`-only execution leads to a `(3,k)`-configuration. -/
theorem lemma_3_2 (hB : RWLike B) (hI : IsTS I false) (k : ℕ) :
    ∀ (S : Finset P), 2 * k ≤ S.card → ∀ (α : List (Label P (tsObj T)))
      (D : Config (tsObj T) B P L), I.run α = some D → D.Quiescent →
      ∃ σ E, (∀ ℓ ∈ σ, ℓ.proc ∈ S) ∧ I.runFrom D σ = some E ∧ Is3k I E k := by
  classical
  induction k with
  | zero =>
    intro S _ α D _ hD
    exact ⟨[], D, by simp, rfl, is3k_zero_of_quiescent hD⟩
  | succ k ih =>
    intro S hS α D hα hD
    obtain ⟨p, hpS, p', hp'S, hpp⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
    set S' := (S.erase p).erase p' with hS'
    have hcard : 2 * k ≤ S'.card := by
      rw [hS', Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hpp, hp'S⟩),
        Finset.card_erase_of_mem hpS]
      omega
    have hpS' : p ∉ S' := by simp [hS']
    have hp'S' : p' ∉ S' := by simp [hS']
    have hS'S : ∀ q ∈ S', q ∈ S := fun q hq => by
      simp only [hS', Finset.mem_erase] at hq; exact hq.2.2
    obtain ⟨C₀, C₁, γ₀, η, b₀, b₁, b₂, hγ₀, hγ₁, hC₀, hC₁, h₀, h₁, hsig, htr⟩ :=
      lemma_3_1 hI S' k (ih S' hcard) hα hD
    have hidle : ∀ q ∉ S', C₀.pend q = none := fun q hq => by
      rw [(I.runFrom_other hC₀ (fun ℓ hℓ he => hq (by rw [← he]; exact hγ₀ ℓ hℓ))).2]; exact hD q
    have hηS' : ∀ ℓ ∈ η, ℓ.proc ∈ S' := fun ℓ hℓ => hγ₁ ℓ (List.mem_append_right _ hℓ)
    obtain ⟨σ, X, hσ, hX, h3⟩ := step_3_2 hI hB (by rw [run_append_of_eq I hα]; exact hC₀) htr
      hC₁ h₀ h₁ hsig hpp (hidle p hpS') (hidle p' hp'S')
      (fun ℓ hℓ => ⟨fun h => hpS' (h ▸ hηS' ℓ hℓ), fun h => hp'S' (h ▸ hηS' ℓ hℓ)⟩)
      {q | q ∈ S} hpS hp'S (fun c hc => hS'S _ (htr.mem_S hidle c hc))
      (fun ℓ hℓ => hS'S _ (hηS' ℓ hℓ))
    refine ⟨γ₀ ++ σ, X, fun ℓ hℓ => ?_, by rw [runFrom_append_of_eq I hC₀, hX], h3⟩
    rcases List.mem_append.1 hℓ with h | h
    · exact hS'S _ (hγ₀ ℓ h)
    · exact hσ ℓ h

/-- **Theorem 1.1** (main counting form). Every long-lived timestamp implementation for `n`
processes from read/write-like base objects (e.g. registers) satisfying non-deterministic
solo-termination (obstruction-freedom) has a reachable `(3,⌊n/2⌋)`-configuration, hence
`⌊n/2⌋ ≤ 3m` where `m` is the number of base objects. -/
theorem theorem_1_1 (hB : RWLike B) (hI : IsTS I false) :
    Fintype.card P / 2 ≤ 3 * Fintype.card ι := by
  obtain ⟨-, E, -, -, h3⟩ := lemma_3_2 hB hI (Fintype.card P / 2) Finset.univ
    (by rw [Finset.card_univ]; omega) [] I.initCfg rfl (fun _ => rfl)
  exact h3.le

/-- **Theorem 1.1.** Every long-lived timestamp implementation for `n` processes from
read/write-like base objects satisfying non-deterministic solo-termination uses at least
`⌊n/6⌋` base objects. -/
theorem theorem_1_1_div (hB : RWLike B) (hI : IsTS I false) :
    Fintype.card P / 6 ≤ Fintype.card ι := by
  have := theorem_1_1 hB hI
  rw [show (6 : ℕ) = 2 * 3 from rfl, ← Nat.div_div_eq_div_mul]
  omega

/-- **Theorem 1.1** in the paper's form: at least `n/6 - 1` (in fact strictly more) base
objects are needed. -/
theorem theorem_1_1_real (hB : RWLike B) (hI : IsTS I false) :
    (Fintype.card P : ℝ) / 6 - 1 < Fintype.card ι := by
  have h := theorem_1_1_div hB hI
  have h6 : Fintype.card P < 6 * (Fintype.card P / 6 + 1) := by omega
  have h6' : (Fintype.card P : ℝ) < 6 * ((Fintype.card P / 6 : ℕ) + 1 : ℝ) := by exact_mod_cast h6
  have hle : ((Fintype.card P / 6 : ℕ) : ℝ) ≤ Fintype.card ι := by exact_mod_cast h
  linarith

end Cslib.SharedMemory.Timestamp
