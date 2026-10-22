import Papers.PODC2015.MinimalSynchronyBC.Basic

/-!
# CB-broadcast from reliable broadcast (Figure 1, Theorem 1)

A correct process `i` RB-broadcasts `CB_VAL(x i)` (line 1); `cb_valid_i` is the set of values
RB-delivered from at least `t + 1` processes (line 4, `fig1Valid`); `CB_broadcast()` returns, at
the first time `cb_valid_i ≠ ∅` (line 2), an arbitrary value of `cb_valid_i` (line 3, chosen by
`sel`).
-/

namespace MinimalSynchronyBC

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- Line 4 of Figure 1: `cb_valid_i` at time `τ`, the values RB-delivered from `t + 1` processes. -/
def fig1Valid (t : ℕ) (D : RBTrace P V) (i : P) (τ : ℕ) : Set V :=
  {v | t + 1 ≤ (univ.filter fun j => D i τ j = some v).card}

/-- An execution of Figure 1: the trace of the `CB_VAL` RB instance and the value picked at line 3
(`sel i τ`, if `i` returns at time `τ`). -/
structure Fig1 (P V : Type*) where
  /-- RB deliveries of `CB_VAL` messages. -/
  D : RBTrace P V
  /-- The value of `cb_valid_i` returned at line 3. -/
  sel : P → ℕ → V

open Classical in
/-- What correct processes observe: `cb_valid` and the return of `CB_broadcast()` (at the first
time `cb_valid_i` is non-empty). -/
noncomputable def Fig1.obs (t : ℕ) (C : Fig1 P V) : CBObs P V where
  valid := fig1Valid t C.D
  ret i := if h : ∃ τ, (fig1Valid t C.D i τ).Nonempty then
    some (Nat.find h, C.sel i (Nat.find h)) else none

/-- If a monotone (in time) property eventually holds for each element of a finite set, it holds
for all of them at a common time (take the maximum). -/
theorem exists_time_forall {ι : Type*} (J : Finset ι) (p : ι → ℕ → Prop)
    (hmono : ∀ j τ τ', p j τ → τ ≤ τ' → p j τ') (h : ∀ j ∈ J, ∃ τ, p j τ) :
    ∃ τ, ∀ j ∈ J, p j τ := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨τ1, h1⟩ := ih (fun j hj => h j (mem_insert_of_mem hj))
    obtain ⟨τ2, h2⟩ := h a (mem_insert_self _ _)
    refine ⟨max τ1 τ2, fun j hj => ?_⟩
    rcases mem_insert.1 hj with rfl | hj
    · exact hmono _ _ _ h2 (le_max_right _ _)
    · exact hmono _ _ _ (h1 j hj) (le_max_left _ _)

omit [Fintype P] [DecidableEq P] in
/-- A set of more than `t` processes contains a process outside `B` when `|B| ≤ t`. -/
theorem exists_mem_notMem_of_card {t : ℕ} {B s : Finset P} (hB : B.card ≤ t)
    (hs : t + 1 ≤ s.card) : ∃ j ∈ s, j ∉ B := by
  by_contra h
  push Not at h
  have := card_le_card (show s ⊆ B from h)
  omega

omit [DecidableEq V] in
/-- Two monotone families of sets, contained in a fixed finite set, such that every element of one
eventually belongs to the other, are eventually equal. -/
theorem eventually_eq_of_mono {f g : ℕ → Set V} (W : Finset V)
    (hf : ∀ {τ τ'}, τ ≤ τ' → f τ ⊆ f τ') (hg : ∀ {τ τ'}, τ ≤ τ' → g τ ⊆ g τ')
    (hW : ∀ τ v, v ∈ f τ ∨ v ∈ g τ → v ∈ W)
    (hfg : ∀ τ v, v ∈ f τ → ∃ τ', v ∈ g τ') (hgf : ∀ τ v, v ∈ g τ → ∃ τ', v ∈ f τ') :
    ∃ T, ∀ τ ≥ T, f τ = g τ := by
  obtain ⟨T, hT⟩ := exists_time_forall W
    (fun v τ => (∃ σ, v ∈ f σ ∨ v ∈ g σ) → v ∈ f τ ∧ v ∈ g τ)
    (fun v τ τ' h hle hv => ⟨hf hle (h hv).1, hg hle (h hv).2⟩) (by
      intro v _
      by_cases hv : ∃ σ, v ∈ f σ ∨ v ∈ g σ
      · obtain ⟨σ, hσ | hσ⟩ := hv
        · obtain ⟨σ', hσ'⟩ := hfg σ v hσ
          exact ⟨max σ σ', fun _ => ⟨hf (le_max_left _ _) hσ, hg (le_max_right _ _) hσ'⟩⟩
        · obtain ⟨σ', hσ'⟩ := hgf σ v hσ
          exact ⟨max σ σ', fun _ => ⟨hf (le_max_right _ _) hσ', hg (le_max_left _ _) hσ⟩⟩
      · exact ⟨0, fun h => absurd h hv⟩)
  refine ⟨T, fun τ hτ => Set.ext fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · exact hg hτ (hT v (hW τ v (Or.inl hv)) ⟨τ, Or.inl hv⟩).2
  · exact hf hτ (hT v (hW τ v (Or.inr hv)) ⟨τ, Or.inr hv⟩).1

omit [DecidableEq P] in
/-- `cb_valid_i` of Figure 1 only grows. -/
theorem fig1Valid_mono {t : ℕ} {B : Finset P} {x : P → Option V} {D : RBTrace P V}
    (hD : RBSpec B x D) {i : P} {τ τ' : ℕ} (h : τ ≤ τ') : fig1Valid t D i τ ⊆ fig1Valid t D i τ' := by
  intro v hv
  refine le_trans hv (card_le_card ?_)
  intro j
  simp only [mem_filter, mem_univ, true_and]
  exact fun hj => hD.mono hj h

omit [DecidableEq P] in
/-- A value of `cb_valid_i` (Figure 1) eventually enters `cb_valid_k` (RB-Termination-2). -/
theorem fig1Valid_eventually {t : ℕ} {B : Finset P} {x : P → Option V} {D : RBTrace P V}
    (hD : RBSpec B x D) {i k : P} (hi : i ∉ B) (hk : k ∉ B) {τ : ℕ} {v : V}
    (hv : v ∈ fig1Valid t D i τ) : ∃ τ', v ∈ fig1Valid t D k τ' := by
  obtain ⟨τ', hτ'⟩ := exists_time_forall (univ.filter fun j => D i τ j = some v)
    (fun j τ' => D k τ' j = some v) (fun j _ _ h hle => hD.mono h hle) (by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      exact hD.term2 hi hk hj)
  refine ⟨τ', le_trans hv (card_le_card ?_)⟩
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact hτ' j (by simpa using hj)

/-- **Theorem 1.** Figure 1 implements CB-broadcast: if the `CB_VAL` messages are RB-broadcast
(correct `j` RB-broadcasts `x j`), at most `t` processes are faulty, and line 3 returns a value of
`cb_valid_i`, then all CB-broadcast properties hold (termination under feasibility). -/
theorem theorem1 {t : ℕ} {B : Finset P} {x : P → Option V} {C : Fig1 P V}
    (hB : B.card ≤ t) (hD : RBSpec B x C.D)
    (hsel : ∀ i τ, (fig1Valid t C.D i τ).Nonempty → C.sel i τ ∈ fig1Valid t C.D i τ) :
    CBSpec t B x (C.obs t) := by
  classical
  have hvalid : ∀ {i τ v}, i ∉ B → v ∈ fig1Valid t C.D i τ → ∃ j ∉ B, x j = some v := by
    intro i τ v hi hv
    obtain ⟨j, hj, hjB⟩ := exists_mem_notMem_of_card hB hv
    simp only [mem_filter, mem_univ, true_and] at hj
    exact ⟨j, hjB, hD.validity hi hjB hj⟩
  have hterm : (∀ j ∉ B, (x j).isSome) → Feasible t B x → ∀ i ∉ B,
      ∃ τ, (fig1Valid t C.D i τ).Nonempty := by
    intro _ ⟨v, hv⟩ i hi
    obtain ⟨τ, hτ⟩ := exists_time_forall (univ.filter fun j => j ∉ B ∧ x j = some v)
      (fun j τ => C.D i τ j = some v) (fun j _ _ h hle => hD.mono h hle) (by
        intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj
        exact hD.term1 hi hj.1 hj.2)
    refine ⟨τ, v, le_trans hv (card_le_card ?_)⟩
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact hτ j (by simpa using hj)
  refine
    { mono := fun h => fig1Valid_mono hD h
      op_termination := ?_
      op_validity := ?_
      set_termination := hterm
      set_validity := hvalid
      set_agreement := ?_ }
  · intro hall hfeas i hi
    obtain ⟨τ, hτ⟩ := hterm hall hfeas i hi
    simp only [Fig1.obs, show ∃ τ, (fig1Valid t C.D i τ).Nonempty from ⟨τ, hτ⟩,
      dite_true, Option.isSome_some]
  · intro i τ v _ hret
    simp only [Fig1.obs] at hret ⊢
    split_ifs at hret with h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_injective _ hret)
    exact hsel i _ (Nat.find_spec h)
  · intro i k hi hk
    let W : Finset V := (univ.filter (· ∉ B)).biUnion fun j => (x j).toFinset
    refine eventually_eq_of_mono W (fun h => fig1Valid_mono hD h) (fun h => fig1Valid_mono hD h)
      ?_ (fun τ v hv => fig1Valid_eventually hD hi hk hv)
      (fun τ v hv => fig1Valid_eventually hD hk hi hv)
    intro τ v hv
    obtain ⟨j, hj, hx⟩ := hv.elim (hvalid hi) (hvalid hk)
    simp only [W, mem_biUnion, mem_filter, mem_univ, true_and, Option.mem_toFinset]
    exact ⟨j, hj, hx⟩

/-- The feasibility condition `n − t > m t` of Section 2.3: if every correct process inputs one of
at most `m` values, some value is input by at least `t + 1` correct processes. -/
theorem feasible_of_mValued {t m : ℕ} {B : Finset P} {x : P → Option V} (hB : B.card ≤ t)
    (hall : ∀ j ∉ B, (x j).isSome) (hm : MValued m B x) (hnt : m * t < Fintype.card P - t) :
    Feasible t B x := by
  classical
  obtain ⟨S, hS, hxS⟩ := hm
  by_contra hne
  simp only [Feasible, not_exists, not_le] at hne
  have hC : (univ.filter fun j => j ∉ B) = Bᶜ := by ext j; simp
  have hsub : (univ.filter fun j => j ∉ B) ⊆
      S.biUnion fun v => univ.filter fun j => j ∉ B ∧ x j = some v := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hall j hj)
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨v, hxS j hj v hv, hj, hv⟩
  have h1 := card_le_card hsub
  have h2 := card_biUnion_le_card_mul S (fun v => univ.filter fun j => j ∉ B ∧ x j = some v) t
    (fun v _ => Nat.lt_succ_iff.1 (hne v))
  rw [hC, card_compl] at h1
  have h3 : S.card * t ≤ m * t := Nat.mul_le_mul_right _ hS
  omega

end MinimalSynchronyBC
