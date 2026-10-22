import Papers.PODC2015.SetAgreementSpace.LowerBoundLemma1

/-!
# Theorem 2 of [DFKR15]: the space lower bound for repeated set agreement

**Theorem 2.** Any `m`-obstruction-free algorithm for repeated `k`-set agreement among `n`
processes from registers uses at least `n + m - k` registers.

## Proof structure

The paper's construction (execution (1) and Figure 2) is formalized as follows.

* `NoWriteOutside I D Q R` — property 8: no execution fragment of the processes of `Q` from `D`
  reaches a configuration in which a process of `Q` is poised to write a register outside `R`.
  By `Cslib.SharedMemory.Impl.runFrom_mem_eq_of_not_covers`, every such fragment then leaves the
  registers outside `R` unchanged (`NoWriteOutside.mem_eq`).
* `figure2` — the loop of Figure 2: from any configuration `C`, given a set `Q₀` of fresh
  processes and enough processes (`|U| + |Q₀| + r ≤ n`), it builds `α_j`, `D_j`, the covering
  processes `P_j` with their registers `A_j` (`cs : List (P × ι)`), and `Q_j` with properties
  1, 5–8. Termination is by strong induction on `r - |A_j|`.
* `exists_gamma` — the fragments `γ_j`: the processes of `Q_j` first complete their first `s`
  invocations by solo runs, then run the `(s+1)`-th instance as given by Lemma 1 (`Lemma1Prop`).
* `splice` — the inductive splicing argument over the list of groups: the fragment `γ_j` is
  inserted at `D_j` and hidden by the block write `β_j` (`blockWrite_agreeOn`), and the rest of
  the execution is replayed unchanged (`runFrom_agreeOn`). It is stated for an arbitrary list
  of group sizes `gs ++ [glast]`, all at most `m`.
* `theorem2` — the theorem, from `Lemma1Prop`; `theorem2'` — from `BGImpossibility`.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V ι W L : Type} [DecidableEq P] [DecidableEq ι] [Inhabited V] {w₀ : W}

/-- Every primitive of a register is read-only or a blind write. -/
lemma regFamily_readOnly_or_overwrites (i : ι) (o : (RegFamily ι W w₀ i).Op) :
    (RegFamily ι W w₀ i).ReadOnly o ∨ (RegFamily ι W w₀ i).Overwrites o := by
  cases o with
  | read => exact Or.inl fun _ => rfl
  | write v => exact Or.inr (register_write_overwrites w₀ v)

section Construction

variable (I : Impl (saObj V) (RegFamily ι W w₀) P L)

/-- Property 8 of the proof of Theorem 2: there is no execution fragment starting from `D` in
which only processes of `Q` take steps and some process (of `Q`) is poised to write a register
outside `R`. -/
def NoWriteOutside (D : Config (saObj V) (RegFamily ι W w₀) P L) (Q : Finset P) (R : Finset ι) :
    Prop :=
  ∀ δ D' q i, (∀ ℓ ∈ δ, ℓ.proc ∈ Q) → I.runFrom D δ = some D' → q ∈ Q → i ∉ R →
    ¬ I.Covers D' q i

variable {I}

/-- Under property 8, fragments of `Q` from `D` do not change the registers outside `R`. -/
lemma NoWriteOutside.mem_eq {D : Config (saObj V) (RegFamily ι W w₀) P L} {Q : Finset P}
    {R : Finset ι} (h : NoWriteOutside I D Q R) {γ : List (Label P (saObj V))}
    {D' : Config (saObj V) (RegFamily ι W w₀) P L} (hγ : ∀ ℓ ∈ γ, ℓ.proc ∈ Q)
    (hrun : I.runFrom D γ = some D') : ∀ i ∉ R, D'.mem i = D.mem i :=
  fun i hi => Impl.runFrom_mem_eq_of_not_covers (Q := (Q : Set P)) (R := (R : Set ι))
    regFamily_readOnly_or_overwrites (fun δ D' q i h1 h2 h3 h4 => h δ D' q i h1 h2 h3 h4)
    hγ hrun i hi

/-- A process outside a finset that is not too large. -/
lemma exists_not_mem_of_card_lt [Fintype P] {S : Finset P} (h : S.card < Fintype.card P) :
    ∃ q, q ∉ S := by
  by_contra hcon
  push Not at hcon
  have : (Finset.univ : Finset P) ⊆ S := fun q _ => hcon q
  exact absurd (Finset.card_le_card this) (by simpa using h)

/-- **The loop of Figure 2** of [DFKR15]. From a configuration `C` and a set `Q₀` of processes
disjoint from the set `U` of processes used before (`Q_1 ∪ ⋯ ∪ Q_{j-1}`), provided
`|U| + |Q₀| + r ≤ n`, there are an execution fragment `α` from `C` to `D` by processes outside
`U`, a list `cs` of distinct processes `P_j` outside `U` together with registers `A_j` that they
cover in `D`, and a set `Q` of processes of the size of `Q₀`, disjoint from `U` and from `P_j`,
such that property 8 holds: no fragment of `Q` from `D` writes outside `A_j`. -/
theorem figure2 [Fintype P] [Fintype ι] (C : Config (saObj V) (RegFamily ι W w₀) P L)
    (U Q₀ : Finset P) (hdisj : Disjoint Q₀ U)
    (hcnt : U.card + Q₀.card + Fintype.card ι ≤ Fintype.card P) :
    ∃ (α : List (Label P (saObj V))) (D : Config (saObj V) (RegFamily ι W w₀) P L)
      (cs : List (P × ι)) (Q : Finset P), I.runFrom C α = some D ∧
      (∀ ℓ ∈ α, ℓ.proc ∉ U) ∧ Q.card = Q₀.card ∧ Disjoint Q U ∧ (cs.map Prod.fst).Nodup ∧
      (∀ c ∈ cs, c.1 ∉ Q ∧ c.1 ∉ U ∧ I.Covers D c.1 c.2) ∧
      NoWriteOutside I D Q (cs.map Prod.snd).toFinset := by
  -- the loop invariant, by strong induction on `r - |A_j|`
  suffices key : ∀ N, ∀ (α : List (Label P (saObj V))) (D : Config (saObj V) (RegFamily ι W w₀) P L)
      (cs : List (P × ι)) (Q : Finset P),
      Fintype.card ι - cs.length = N → I.runFrom C α = some D →
      (∀ ℓ ∈ α, ℓ.proc ∉ U) → Q.card = Q₀.card → Disjoint Q U → (cs.map Prod.fst).Nodup →
      (cs.map Prod.snd).Nodup → (∀ c ∈ cs, c.1 ∉ Q ∧ c.1 ∉ U ∧ I.Covers D c.1 c.2) →
      ∃ (α : List (Label P (saObj V))) (D : Config (saObj V) (RegFamily ι W w₀) P L)
      (cs : List (P × ι)) (Q : Finset P), I.runFrom C α = some D ∧
        (∀ ℓ ∈ α, ℓ.proc ∉ U) ∧ Q.card = Q₀.card ∧ Disjoint Q U ∧ (cs.map Prod.fst).Nodup ∧
        (∀ c ∈ cs, c.1 ∉ Q ∧ c.1 ∉ U ∧ I.Covers D c.1 c.2) ∧
        NoWriteOutside I D Q (cs.map Prod.snd).toFinset by
    exact key _ [] C [] Q₀ rfl rfl (by simp) rfl hdisj (by simp) (by simp) (by simp)
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro α D cs Q hN hα hαU hQc hQU hnd1 hnd2 hcs
  by_cases hex : ∃ δ D' q i, (∀ ℓ ∈ δ, ℓ.proc ∈ Q) ∧ I.runFrom D δ = some D' ∧ q ∈ Q ∧
      i ∉ (cs.map Prod.snd).toFinset ∧ I.Covers D' q i
  swap
  · refine ⟨α, D, cs, Q, hα, hαU, hQc, hQU, hnd1, hcs, ?_⟩
    intro δ D' q i h1 h2 h3 h4 h5
    exact hex ⟨δ, D', q, i, h1, h2, h3, h4, h5⟩
  obtain ⟨δ, D', q, i, hδ, hD', hq, hi, hcov⟩ := hex
  -- `A_j` is not all registers
  have hlen : cs.length < Fintype.card ι := by
    have hsub : (cs.map Prod.snd).toFinset ⊆ Finset.univ.erase i := fun j hj =>
      Finset.mem_erase.2 ⟨fun h => hi (h ▸ hj), Finset.mem_univ _⟩
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd2, List.length_map, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ] at this
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    omega
  -- the fresh process `q'` of line 11
  obtain ⟨q', hq'⟩ := exists_not_mem_of_card_lt (S := U ∪ Q ∪ (cs.map Prod.fst).toFinset) (by
    calc (U ∪ Q ∪ (cs.map Prod.fst).toFinset).card
        ≤ U.card + Q.card + (cs.map Prod.fst).toFinset.card :=
          (Finset.card_union_le _ _).trans (by
            have := Finset.card_union_le U Q; omega)
      _ ≤ U.card + Q.card + cs.length := by
          have := List.toFinset_card_le (cs.map Prod.fst); simp at this; omega
      _ < Fintype.card P := by omega)
  simp only [Finset.mem_union, List.mem_toFinset, not_or] at hq'
  obtain ⟨⟨hq'U, hq'Q⟩, hq'cs⟩ := hq'
  have hqq' : q ≠ q' := fun h => hq'Q (h ▸ hq)
  have hqU : q ∉ U := Finset.disjoint_left.1 hQU hq
  refine ih (Fintype.card ι - (cs.length + 1)) (by omega) (α ++ δ) D' (cs ++ [(q, i)])
    (insert q' (Q.erase q)) (by simp) (by rw [Impl.runFrom_append_of_eq I hα, hD'])
    (fun ℓ hℓ => ?_) ?_ ?_ ?_ ?_ ?_
  · rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact hαU ℓ hℓ
    · exact Finset.disjoint_left.1 hQU (hδ ℓ hℓ)
  · rw [Finset.card_insert_of_notMem (fun h => hq'Q (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hq, ← hQc]
    have := Finset.card_pos.2 ⟨q, hq⟩; omega
  · rw [Finset.disjoint_insert_left]
    exact ⟨hq'U, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hQU⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨hnd1, by simp, ?_⟩
    simp only [List.mem_singleton]
    rintro a ha b rfl rfl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    exact (hcs c hc).1 hq
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨hnd2, by simp, ?_⟩
    simp only [List.mem_singleton]
    rintro a ha b rfl rfl
    exact hi (List.mem_toFinset.2 ha)
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨h1, h2, h3⟩ := hcs c hc
      have hne : c.1 ≠ q' := fun h => hq'cs (h ▸ List.mem_map_of_mem hc)
      refine ⟨by simp [hne, h1], h2, ?_⟩
      have := I.runFrom_other hD' (q := c.1) (fun ℓ hℓ h => h1 (h ▸ hδ ℓ hℓ))
      exact h3.congr this.1.symm this.2.symm
    · simp only [List.mem_singleton] at hc; subst hc
      exact ⟨by simp [hqq'], hqU, hcov⟩

/-- A process `q` that has invoked at most `s` operations completes its pending operation (if any)
and then its first `s` invocations by running solo (obstruction-freedom). -/
lemma exists_complete_one (hobs : I.ObstructionFree) (hall : ∀ p o, I.allowed p o)
    {π : List (Label P (saObj V))} {D : Config (saObj V) (RegFamily ι W w₀) P L}
    (hπ : I.run π = some D) {s : ℕ} (hs : ∀ p, (opsOf π p).length ≤ s) (q : P) :
    ∃ γ D', I.runFrom D γ = some D' ∧ (∀ ℓ ∈ γ, ℓ.proc = q) ∧
      (∀ p, (opsOf (π ++ γ) p).length ≤ s) ∧ D'.pend q = none ∧
      (opsOf (π ++ γ) q).length = s := by
  -- finish the pending operation
  obtain ⟨γ₁, D₁, h1, h1p, h1o, h1i⟩ : ∃ γ₁ D₁, I.runFrom D γ₁ = some D₁ ∧
      (∀ ℓ ∈ γ₁, ℓ.proc = q) ∧ (∀ p, opsOf γ₁ p = []) ∧ D₁.pend q = none := by
    by_cases hq : D.pend q = none
    · exact ⟨[], D, rfl, by simp, by simp, hq⟩
    · obtain hfin := hobs D q ⟨π, hπ⟩ hq
      exact ⟨I.soloLabels q D (I.soloTime q D), _, I.runFrom_soloLabels q D _,
        I.soloLabels_proc q D _, fun p => I.opsOf_soloLabels q p D _, I.soloTime_spec q D hfin⟩
  have hπ₁ : I.run (π ++ γ₁) = some D₁ := by rw [Impl.run_append_of_eq I hπ, h1]
  -- then invoke until `s` invocations
  set os : List V := List.replicate (s - (opsOf π q).length) default
  obtain ⟨D', h2, h2i, h2p, h2o, -⟩ := I.soloOps_spec hobs q os (fun o _ => hall q o) hπ₁ h1i
  refine ⟨γ₁ ++ I.soloOps q D₁ os, D', by rw [Impl.runFrom_append_of_eq I h1, h2], ?_, ?_, h2i, ?_⟩
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact h1p ℓ hℓ
    · exact h2p ℓ hℓ
  · intro p
    by_cases hpq : p = q
    · subst hpq; simp [h1o, h2o, os]; have := hs p; omega
    · rw [opsOf_append, opsOf_append, h1o, opsOf_eq_nil_of_proc_ne (fun ℓ hℓ h => hpq
        (h.symm.trans (h2p ℓ hℓ)))]
      simpa using hs p
  · simp [h1o, h2o, os]; have := hs q; omega

/-- The processes of a list complete their pending operations and their first `s` invocations,
one after the other, by solo runs. -/
lemma exists_complete (hobs : I.ObstructionFree) (hall : ∀ p o, I.allowed p o) {s : ℕ}
    (l : List P) : ∀ {π : List (Label P (saObj V))} {D : Config (saObj V) (RegFamily ι W w₀) P L},
    I.run π = some D → (∀ p, (opsOf π p).length ≤ s) →
    ∃ γ D', I.runFrom D γ = some D' ∧ (∀ ℓ ∈ γ, ℓ.proc ∈ l) ∧
      (∀ p, (opsOf (π ++ γ) p).length ≤ s) ∧
      ∀ q ∈ l, D'.pend q = none ∧ (opsOf (π ++ γ) q).length = s := by
  induction l with
  | nil => intro π D _ hs; exact ⟨[], D, rfl, by simp, by simpa using hs, by simp⟩
  | cons q l ih =>
    intro π D hπ hs
    obtain ⟨γ₁, D₁, h1, h1p, h1s, h1i, h1q⟩ := exists_complete_one hobs hall hπ hs q
    have hπ₁ : I.run (π ++ γ₁) = some D₁ := by rw [Impl.run_append_of_eq I hπ, h1]
    obtain ⟨γ₂, D₂, h2, h2p, h2s, h2l⟩ := ih hπ₁ h1s
    refine ⟨γ₁ ++ γ₂, D₂, by rw [Impl.runFrom_append_of_eq I h1, h2], ?_, ?_, ?_⟩
    · intro ℓ hℓ
      rcases List.mem_append.1 hℓ with hℓ | hℓ
      · simp [h1p ℓ hℓ]
      · simp [h2p ℓ hℓ]
    · simpa using h2s
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · by_cases hpl : p ∈ l
        · simpa using h2l p hpl
        · have hne : ∀ ℓ ∈ γ₂, ℓ.proc ≠ p := fun ℓ hℓ h => hpl (h ▸ h2p ℓ hℓ)
          refine ⟨by rw [(I.runFrom_other h2 hne).2]; exact h1i, ?_⟩
          rw [← List.append_assoc, opsOf_append, opsOf_eq_nil_of_proc_ne hne, List.append_nil]
          exact h1q
      · simpa using h2l p hp

/-- **The fragments `γ_j`** of the proof of Theorem 2. From a configuration `D` reached by an
execution `π` in which every process invoked at most `s` times, the processes of a set `Q` of at
most `m` processes first complete their first `s` invocations by solo runs and then run the
`(s+1)`-th instance given by Lemma 1, in which all values `inp q`, `q ∈ Q`, are output. -/
lemma exists_gamma {m : ℕ} (hobs : I.ObstructionFree) (hall : ∀ p o, I.allowed p o)
    (hL1 : Lemma1Prop I m) {π : List (Label P (saObj V))}
    {D : Config (saObj V) (RegFamily ι W w₀) P L} (hπ : I.run π = some D) {s : ℕ}
    (hs : ∀ p, (opsOf π p).length ≤ s) (Q : Finset P) (hQm : Q.card ≤ m) (inp : P → V)
    (hinj : Set.InjOn inp Q) :
    ∃ γ D', I.runFrom D γ = some D' ∧ (∀ ℓ ∈ γ, ℓ.proc ∈ Q) ∧
      ∀ q ∈ Q, ∃ q' ∈ Q, (respsOf (π ++ γ) q')[s]? = some (inp q) := by
  obtain ⟨γ₁, D₁, h1, h1p, h1s, h1q⟩ := exists_complete hobs hall Q.toList hπ hs
  have hπ₁ : I.run (π ++ γ₁) = some D₁ := by rw [Impl.run_append_of_eq I hπ, h1]
  obtain ⟨γ₂, D₂, h2, h2p, h2o⟩ := hL1 (π ++ γ₁) D₁ s Q inp hπ₁ h1s hQm
    (fun q hq => h1q q (Finset.mem_toList.2 hq)) hinj
  refine ⟨γ₁ ++ γ₂, D₂, by rw [Impl.runFrom_append_of_eq I h1, h2], ?_, ?_⟩
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact Finset.mem_toList.1 (h1p ℓ hℓ)
    · exact h2p ℓ hℓ
  · intro q hq
    obtain ⟨q', hq', hr⟩ := h2o q hq
    refine ⟨q', hq', ?_⟩
    have hlen : (respsOf (π ++ γ₁) q').length = s := by
      rw [← I.run_idle_counts hπ₁ (h1q q' (Finset.mem_toList.2 hq')).1]
      exact (h1q q' (Finset.mem_toList.2 hq')).2
    rw [← List.append_assoc, respsOf_append, hr, List.getElem?_append_right (by omega), hlen,
      Nat.sub_self]
    rfl

end Construction

section Splice

variable {I : Impl (saObj V) (RegFamily ι W w₀) P L}

/-- **The splicing argument** of the proof of Theorem 2, by induction over the groups
`Q_j` (of sizes `gs ++ [glast]`, all at most `m`).

From a configuration `C` reached by `π`, with the set `U` of processes already used, there is an
execution fragment `ρ` from `C` (the rest of execution (1)) such that for every `s` bounding the
number of invocations of every process in `π ++ ρ`, there is another fragment `ρ'` from `C` (the
execution (1) with the fragments `γ_j` spliced in) by processes outside `U` and a set `G` of
`|gs| + glast` processes outside `U` such that every value `inp q`, `q ∈ G`, is output by a
process of `G` in the `(s+1)`-th instance.

For a group that is not the last one, Figure 2 (`figure2`) needs `|U| + |Q_j| + r ≤ n`; for the
last group (`Q_c` in the paper), `|U| + |Q_c| ≤ n` suffices. -/
theorem splice [Fintype P] [Fintype ι] {m : ℕ} (hobs : I.ObstructionFree)
    (hall : ∀ p o, I.allowed p o) (hL1 : Lemma1Prop I m) (inp : P → V)
    (hinj : Function.Injective inp) (glast : ℕ) (hglast : glast ≤ m) :
    ∀ (gs : List ℕ), (∀ g ∈ gs, g ≤ m) → ∀ (π : List (Label P (saObj V)))
      (C : Config (saObj V) (RegFamily ι W w₀) P L) (U : Finset P), I.run π = some C →
      U.card + gs.sum + Fintype.card ι ≤ Fintype.card P →
      U.card + gs.sum + glast ≤ Fintype.card P →
      ∃ ρ, I.Valid (π ++ ρ) ∧ ∀ s, (∀ p, (opsOf (π ++ ρ) p).length ≤ s) →
        ∃ (ρ' : List (Label P (saObj V))) (G : Finset P), I.Valid (π ++ ρ') ∧ (∀ ℓ ∈ ρ', ℓ.proc ∉ U) ∧ Disjoint G U ∧
          G.card = gs.sum + glast ∧
          ∀ q ∈ G, ∃ q' ∈ G, (respsOf (π ++ ρ') q')[s]? = some (inp q) := by
  intro gs
  induction gs with
  | nil =>
    intro _ π C U hπ _ hcnt
    simp only [List.sum_nil, add_zero] at hcnt
    obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ \ U)
      (n := glast) (by rw [Finset.card_univ_sdiff]; omega)
    have hGU : Disjoint G U := Finset.disjoint_of_subset_left hGsub Finset.sdiff_disjoint
    refine ⟨[], by rw [List.append_nil]; exact ⟨C, hπ⟩, fun s hs => ?_⟩
    simp only [List.append_nil] at hs
    obtain ⟨γ, D', h1, h2, h3⟩ :=
      exists_gamma hobs hall hL1 hπ hs G (hGcard ▸ hglast) inp hinj.injOn
    exact ⟨γ, G, ⟨D', by rw [Impl.run_append_of_eq I hπ, h1]⟩,
      fun ℓ hℓ hU => Finset.disjoint_left.1 hGU (h2 ℓ hℓ) hU, hGU, by simp [hGcard], h3⟩
  | cons g gs ih =>
    intro hgs π C U hπ hcnt1 hcnt2
    simp only [List.sum_cons] at hcnt1 hcnt2
    obtain ⟨Q₀, hQ₀sub, hQ₀card⟩ := Finset.exists_subset_card_eq (s := Finset.univ \ U)
      (n := g) (by rw [Finset.card_univ_sdiff]; omega)
    have hQ₀U : Disjoint Q₀ U := Finset.disjoint_of_subset_left hQ₀sub Finset.sdiff_disjoint
    -- `α_j`, `D_j`, `P_j`, `A_j`, `Q_j` (Figure 2)
    obtain ⟨α, D, cs, Q, hα, hαU, hQc, hQU, hnd, hcs, h8⟩ :=
      figure2 C U Q₀ hQ₀U (by omega)
    have hcov : ∀ c ∈ cs, I.Covers D c.1 c.2 := fun c hc => (hcs c hc).2.2
    -- the block write `β_j`
    obtain ⟨C₁, hβ, -, -⟩ := Impl.blockWrite_run hnd hcov
    set bw : List (Label P (saObj V)) := Impl.blockWrite (A := saObj V) (cs.map Prod.fst) with hbw
    have hπα : I.run (π ++ α) = some D := by rw [Impl.run_append_of_eq I hπ, hα]
    have hπ₁ : I.run (π ++ α ++ bw) = some C₁ := by rw [Impl.run_append_of_eq I hπα, hβ]
    have hUQ : Disjoint U Q := hQU.symm
    obtain ⟨ρ, hρ, hρs⟩ := ih (fun g hg => hgs g (by simp [hg])) _ C₁ (U ∪ Q) hπ₁
      (by rw [Finset.card_union_of_disjoint hUQ]; omega)
      (by rw [Finset.card_union_of_disjoint hUQ]; omega)
    refine ⟨α ++ bw ++ ρ, by simpa [List.append_assoc] using hρ, fun s hs => ?_⟩
    have hs₁ : ∀ p, (opsOf (π ++ α ++ bw ++ ρ) p).length ≤ s := by
      simpa [List.append_assoc] using hs
    obtain ⟨ρ', G, hρ'v, hρ'U, hGU, hGc, hGo⟩ := hρs s hs₁
    -- the fragment `γ_j` from `D_j`
    obtain ⟨γ, Dγ, hγ, hγQ, hγo⟩ := exists_gamma hobs hall hL1 hπα (s := s)
      (fun p => by
        have := hs p
        simp only [opsOf_append, List.length_append] at this ⊢; omega)
      Q (by rw [hQc, hQ₀card]; exact hgs g (by simp)) inp hinj.injOn
    have hγnot : ∀ p, p ∉ Q → ∀ ℓ ∈ γ, ℓ.proc ≠ p :=
      fun p hp ℓ hℓ h => hp (h ▸ hγQ ℓ hℓ)
    -- `γ_j` is hidden by the block write `β_j`
    obtain ⟨C₁a, C₁b, ha, hb, hag⟩ := Impl.blockWrite_agreeOn (Q := ((Q : Set P)ᶜ)) hnd
      (fun c hc => (hcs c hc).1) hcov
      (fun p hp => ((I.runFrom_other hγ (hγnot p hp)).1).symm)
      (fun p hp => ((I.runFrom_other hγ (hγnot p hp)).2).symm)
      (fun i hi => (h8.mem_eq hγQ hγ i (by simpa using hi)).symm)
    rw [← hbw, hβ, Option.some.injEq] at ha
    subst ha
    rw [← hbw] at hb
    -- the rest of the spliced execution is replayed unchanged
    obtain ⟨X, hX⟩ := hρ'v
    rw [Impl.run_append_of_eq I hπ₁] at hX
    have hρ'Q : ∀ ℓ ∈ ρ', ℓ.proc ∈ ((Q : Set P)ᶜ) := fun ℓ hℓ h =>
      hρ'U ℓ hℓ (Finset.mem_union_right _ h)
    obtain ⟨X', hX', -⟩ := Impl.runFrom_agreeOn hag hρ'Q hX
    have hDγ : I.run (π ++ α ++ γ) = some Dγ := by rw [Impl.run_append_of_eq I hπα, hγ]
    have hC₁b : I.run (π ++ α ++ γ ++ bw) = some C₁b := by rw [Impl.run_append_of_eq I hDγ, hb]
    have hrun : I.run (π ++ α ++ γ ++ bw ++ ρ') = some X' := by
      rw [Impl.run_append_of_eq I hC₁b, hX']
    have hbwQ : ∀ ℓ ∈ bw, ℓ.proc ∉ Q ∧ ℓ.proc ∉ U := by
      intro ℓ hℓ
      obtain ⟨c, hc, h⟩ := List.mem_map.1 (Impl.mem_blockWrite hℓ)
      rw [← h]; exact ⟨(hcs c hc).1, (hcs c hc).2.1⟩
    have hGUQ : Disjoint G (U ∪ Q) := hGU
    refine ⟨α ++ γ ++ bw ++ ρ', Q ∪ G, ⟨X', by simpa [List.append_assoc] using hrun⟩, ?_, ?_, ?_,
      ?_⟩
    · intro ℓ hℓ
      simp only [List.mem_append] at hℓ
      rcases hℓ with ((hℓ | hℓ) | hℓ) | hℓ
      · exact hαU ℓ hℓ
      · exact Finset.disjoint_left.1 hQU (hγQ ℓ hℓ)
      · exact (hbwQ ℓ hℓ).2
      · exact fun h => hρ'U ℓ hℓ (Finset.mem_union_left _ h)
    · exact Finset.disjoint_union_left.2 ⟨hQU, Finset.disjoint_of_subset_right
        Finset.subset_union_left hGU⟩
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right
        Finset.subset_union_right hGUQ).symm, hQc, hQ₀card, hGc, List.sum_cons]
      omega
    · intro q hq
      rcases Finset.mem_union.1 hq with hq | hq
      · obtain ⟨q', hq', h⟩ := hγo q hq
        refine ⟨q', Finset.mem_union_left _ hq', ?_⟩
        have h1 : respsOf bw q' = [] :=
          respsOf_eq_nil_of_proc_ne fun ℓ hℓ e => (hbwQ ℓ hℓ).1 (e ▸ hq')
        have h2 : respsOf ρ' q' = [] :=
          respsOf_eq_nil_of_proc_ne fun ℓ hℓ e => hρ'Q ℓ hℓ (e ▸ hq')
        have e : respsOf (π ++ (α ++ γ ++ bw ++ ρ')) q' = respsOf (π ++ α ++ γ) q' := by
          simp only [respsOf_append, h1, h2, List.append_nil, List.append_assoc]
        rw [e]; exact h
      · obtain ⟨q', hq', h⟩ := hGo q hq
        refine ⟨q', Finset.mem_union_right _ hq', ?_⟩
        have hq'Q : q' ∉ Q := fun h' =>
          Finset.disjoint_left.1 hGUQ hq' (Finset.mem_union_right _ h')
        have h1 : respsOf γ q' = [] := respsOf_eq_nil_of_proc_ne (hγnot q' hq'Q)
        have e : respsOf (π ++ (α ++ γ ++ bw ++ ρ')) q' = respsOf (π ++ α ++ bw ++ ρ') q' := by
          simp only [respsOf_append, h1, List.nil_append, List.append_assoc]
        rw [e]; exact h

end Splice

/-! ### Theorem 2 -/

/-- **Theorem 2 of [DFKR15].** Any `m`-obstruction-free algorithm for repeated `k`-set agreement
among `n` processes (`1 ≤ m ≤ k < n`) from registers uses at least `n + m - k` registers.

Hypotheses: the algorithm `I` uses the registers `ι`; every process may propose every value
(`hall`); the input domain contains the process identifiers (`hV`; the proof uses identifiers as
inputs); `I` satisfies validity and `k`-agreement in every instance of every execution
(`hsolve`) and is `m`-obstruction-free (`hof`); Lemma 1 holds in the form `Lemma1Prop` (it
follows from the wait-free set-agreement impossibility, see `theorem2'`). -/
theorem theorem2 [Fintype P] [Fintype ι] (I : Impl (saObj V) (RegFamily ι W w₀) P L) {k m : ℕ}
    (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k < Fintype.card P) (hall : ∀ p o, I.allowed p o)
    (hV : Nonempty (P ↪ V)) (hsolve : I.SolvesRepeated k)
    (hof : I.MObstructionFreeOn m (fun _ => True)) (hL1 : Lemma1Prop I m) :
    Fintype.card P + m - k ≤ Fintype.card ι := by
  by_contra hlt
  push Not at hlt
  obtain ⟨inp⟩ := hV
  have hobs : I.ObstructionFree := Impl.obstructionFreeOn_true_iff.1
    (hof.obstructionFreeOn hm prefixClosed_true (fun _ _ _ => trivial))
  -- groups `Q_1, …, Q_{c-1}` of sizes at most `m` summing to `k + 1 - m`, and `|Q_c| = m`
  set gs : List ℕ := List.replicate ((k + 1 - m) / m) m ++ [(k + 1 - m) % m] with hgsdef
  have hgs : ∀ g ∈ gs, g ≤ m := by
    intro g hg
    simp only [hgsdef, List.mem_append, List.mem_replicate, List.mem_singleton] at hg
    rcases hg with ⟨-, rfl⟩ | rfl
    · exact le_rfl
    · exact (Nat.mod_lt _ (by omega)).le
  have hsum : gs.sum = k + 1 - m := by
    simp only [hgsdef, List.sum_append, List.sum_replicate, nsmul_eq_mul, Nat.cast_id, List.sum_singleton]
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  obtain ⟨ρ, -, hρ⟩ := splice hobs hall hL1 inp inp.injective m le_rfl gs hgs [] I.initCfg ∅
    rfl (by simp only [Finset.card_empty, hsum]; omega)
    (by simp only [Finset.card_empty, hsum]; omega)
  obtain ⟨ρ', G, hv, -, -, hGc, hGo⟩ := hρ ρ.length (fun p => by
    simpa [opsOf] using List.length_filterMap_le (Label.invOf p) ρ)
  -- `k + 1` distinct outputs in instance `s + 1`
  have hsub : inp '' G ⊆ outputsAt ρ' ρ.length := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨q', -, h⟩ := hGo q hq
    exact ⟨q', by simpa using h⟩
  have h1 := (hsolve ρ' (by simpa using hv) ρ.length).2
  have h2 : (inp '' G).encard = ((k + 1 : ℕ) : ℕ∞) := by
    rw [inp.injective.injOn.encard_image, Set.encard_coe_eq_coe_finsetCard, hGc, hsum]
    congr 1; omega
  have := (Set.encard_le_encard hsub).trans h1
  rw [h2] at this
  norm_cast at this
  omega

/-- **Theorem 2 of [DFKR15]**, with Lemma 1 derived (`lemma1`) from the impossibility of
wait-free set agreement (`BGImpossibility`, assumed). -/
theorem theorem2' [Fintype P] [Fintype ι] (I : Impl (saObj V) (RegFamily ι W w₀) P L) {k m : ℕ}
    (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k < Fintype.card P) (hall : ∀ p o, I.allowed p o)
    (hV : Nonempty (P ↪ V)) (hsolve : I.SolvesRepeated k)
    (hof : I.MObstructionFreeOn m (fun _ => True)) (hBG : BGImpossibility P V ι W L w₀) :
    Fintype.card P + m - k ≤ Fintype.card ι :=
  theorem2 I hm hmk hkn hall hV hsolve hof (lemma1 I hBG hall hsolve hof)

end Podc.SetAgreementSpace
