import Papers.PODC2021.TimeOptimalSSLE.Model

/-!
# Theorem 2.1: SSLE needs at least `n` states and exact knowledge of `n`

Theorem 2.1 of the paper (cited from Cai, Izumi, Wada, *How to prove impossibility under global
fairness: on space complexity of self-stabilizing leader election on a population protocol model*,
Theory Comput. Syst. 50 (2012)): *any population protocol solving SSLE has `≥ n` states and is
strongly nonuniform.*

* `card_le_card_states`: a protocol solving SSLE on `n` agents has at least `n` states. The proof
  is the *closed-set argument* of Cai–Izumi–Wada: starting from the `n - 1` followers of a stably
  correct configuration (which can never generate a leader state), repeatedly either find a state
  the current sub-configuration cannot generate, or drop one agent and find such a state; after
  `|Q| - #leader-states` rounds a nonempty sub-configuration cannot generate any state.
* `not_solvesSSLE_two_sizes`: no protocol (same states, transitions and leader output) solves SSLE
  for two population sizes `n₁ < n₂` (the argument sketched in the paper after Theorem 2.1:
  a leaderless sub-population of size `n₁` of a stably correct size-`n₂` configuration would
  create a second leader).

Both results hold for randomized transitions (we only use their support) and under the weakest
"positive probability" reading of self-stabilization (`SelfStabilizes`).
-/

open Cslib.PopulationProtocol

namespace TimeOptimalSSLE.NProtocol

variable {Q A : Type*} [DecidableEq A] (P : NProtocol Q)

/-- The sub-configuration of `C` on the agents `S` cannot generate any state of `G`. -/
def CannotGen (S : Finset A) (C : Config A Q) (G : Set Q) : Prop :=
  ∀ D, P.ReachIn (· ∈ S) C D → ∀ a ∈ S, D a ∉ G

-- CSLib candidate
/-- **Lemma 4 of Cai–Izumi–Wada.** If the sub-configuration `(S, C)` cannot generate `G` and the
complement of `G` is not closed, then some sub-configuration with at most one agent less cannot
generate `G` plus one more state. -/
lemma CannotGen.extend {S : Finset A} {C : Config A Q} {G : Set Q} (h : P.CannotGen S C G)
    (hG : ¬ P.ClosedStates Gᶜ) :
    ∃ S' : Finset A, ∃ C' : Config A Q, ∃ q, q ∉ G ∧ S.card ≤ S'.card + 1 ∧
      P.CannotGen S' C' (insert q G) := by
  simp only [Cslib.PopulationProtocol.NProtocol.ClosedStates, not_forall, Set.mem_compl_iff,
    not_and_or, not_not] at hG
  obtain ⟨p, hp, q, hq, o, ho, hoG⟩ := hG
  by_cases hgen : ∃ D, P.ReachIn (· ∈ S) C D ∧ ∃ a ∈ S, D a = p
  · obtain ⟨D, hD, a, haS, hDa⟩ := hgen
    refine ⟨S.erase a, D, q, hq, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem haS]; omega
    intro E hE b hb hEb
    have hEC : P.ReachIn (· ∈ S) C E :=
      hD.trans (hE.mono fun x hx => Finset.mem_of_mem_erase hx)
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbS : b ∈ S := Finset.mem_of_mem_erase hb
    rcases hEb with hEb | hEb
    · -- `b` has the state `q`, while `a` (idle in the sub-run) still has `p`
      have hEa : E a = p := by
        rw [hE.apply_eq (x := a) (by simp)]; exact hDa
      have hstep : P.StepIn (· ∈ S) E (upd E a b o) :=
        ⟨a, b, ⟨haS, hbS, hba.symm⟩, o, by rw [hEa, hEb]; exact ho, rfl⟩
      have hreach := hEC.tail hstep
      rcases hoG with h1 | h2
      · exact h (upd E a b o) hreach a haS (by rw [upd_left _ hba.symm]; exact h1)
      · exact h (upd E a b o) hreach b hbS (by rw [upd_right]; exact h2)
    · exact h E hEC b hbS hEb
  · push Not at hgen
    refine ⟨S, C, p, hp, by omega, ?_⟩
    intro D hD a ha hDa
    rcases hDa with hDa | hDa
    · exact hgen D hD a ha hDa
    · exact h D hD a ha hDa

variable [Fintype A]

/-- **Lemma 5 of Cai–Izumi–Wada.** A protocol solving SSLE has no nonempty closed set of
non-leader states (from a configuration using only such states no leader can ever appear). -/
lemma not_closedSet_of_solvesSSLE [Nonempty A] {leader : Q → Bool}
    (hP : P.SolvesSSLE (A := A) leader) {H : Set Q} (hne : H.Nonempty)
    (hL : ∀ q ∈ H, leader q = false) : ¬ P.ClosedStates H := by
  intro hH
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨D, hD, hDs⟩ := hP (fun _ => q₀)
  -- all reachable configurations only use states of `H`
  have hall : ∀ E, P.Reachable (fun _ : A => q₀) E → ∀ a, E a ∈ H :=
    fun _ hE => hH.reach (fun _ => hq₀) hE
  have h1 : numLeaders leader D = 1 := hDs D Relation.ReflTransGen.refl
  have h0 : numLeaders leader D = 0 := by
    unfold numLeaders
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _
    rw [hL _ (hall D hD a)]; simp
  omega

/-- **Theorem 2.1 (first part), [Cai–Izumi–Wada].** Any population protocol solving
self-stabilizing leader election on `n = |A|` agents has at least `n` states. -/
theorem card_le_card_states [Fintype Q] [Nonempty Q] {leader : Q → Bool}
    (hP : P.SolvesSSLE (A := A) leader) : Fintype.card A ≤ Fintype.card Q := by
  classical
  by_contra hlt
  push Not at hlt
  have hA : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  obtain ⟨C, -, hC⟩ := hP (fun _ => q₀)
  have h1 : numLeaders leader C = 1 := hC C Relation.ReflTransGen.refl
  obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp h1
  have hℓC : leader (C ℓ) = true := by
    have : ℓ ∈ Finset.univ.filter fun a => leader (C a) = true := by rw [hℓ]; simp
    simpa using this
  have honly : ∀ a, leader (C a) = true → a = ℓ := by
    intro a ha
    have : a ∈ Finset.univ.filter fun a => leader (C a) = true := by simpa using ha
    rw [hℓ] at this; simpa using this
  set L : Set Q := {q | leader q = true}
  -- the followers of a stably correct configuration cannot generate a leader state
  have hstart : P.CannotGen (Finset.univ.erase ℓ) C L := by
    intro D hD a ha hDa
    have hDℓ : D ℓ = C ℓ := hD.apply_eq (by simp)
    have hDc : numLeaders leader D = 1 := hC D hD.reachable
    have hsub : ({a, ℓ} : Finset A) ⊆ Finset.univ.filter fun x => leader (D x) = true := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using (show leader (D x) = true from hDa)
      · simpa [hDℓ] using hℓC
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (Finset.ne_of_mem_erase ha)] at this
    unfold numLeaders at hDc; omega
  -- iterate Lemma 4, measured by the number of states not yet in `G`
  have key : ∀ k : ℕ, ∀ (S : Finset A) (D : Config A Q) (G : Finset Q),
      Fintype.card Q - G.card = k → L ⊆ ↑G → Fintype.card A ≤ S.card + G.card →
      P.CannotGen S D ↑G → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro S D G hk hLG hcard hgen
      have hGQ : G.card ≤ Fintype.card Q := Finset.card_le_univ G
      obtain ⟨a, haS⟩ : S.Nonempty := by
        rw [← Finset.card_pos]; omega
      have haG : D a ∉ (G : Set Q) := hgen D Relation.ReflTransGen.refl a haS
      by_cases hcl : P.ClosedStates (↑G : Set Q)ᶜ
      · refine P.not_closedSet_of_solvesSSLE hP ⟨D a, haG⟩ ?_ hcl
        intro q hq
        by_contra hql
        exact hq (hLG (show leader q = true by simpa using hql))
      · obtain ⟨S', D', q, hq, hS', hgen'⟩ := hgen.extend P hcl
        have hqG : q ∉ G := by simpa using hq
        refine ih (Fintype.card Q - (insert q G).card) ?_ S' D' (insert q G) rfl
          (hLG.trans (by simp [Set.subset_insert])) ?_ (by simpa using hgen')
        · rw [Finset.card_insert_of_notMem hqG]
          have : (insert q G).card ≤ Fintype.card Q := Finset.card_le_univ _
          rw [Finset.card_insert_of_notMem hqG] at this; omega
        · rw [Finset.card_insert_of_notMem hqG]; omega
  refine key _ (Finset.univ.erase ℓ) C (Finset.univ.filter fun q => leader q = true) rfl
    (by intro q hq; simpa using (show leader q = true from hq)) ?_
    (by simpa [L] using hstart)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have : 1 ≤ (Finset.univ.filter fun q => leader q = true).card :=
    Finset.card_pos.mpr ⟨C ℓ, by simpa using hℓC⟩
  have : 1 ≤ Fintype.card A := Fintype.card_pos
  omega

/-- **Theorem 2.1 (second part): SSLE protocols are strongly nonuniform.** The same protocol
(states, transitions and leader output) cannot solve self-stabilizing leader election for two
population sizes `n₁ < n₂`. Equivalently, any SSLE protocol must "know" `n` exactly. -/
theorem not_solvesSSLE_two_sizes [Nonempty Q] {leader : Q → Bool} {n₁ n₂ : ℕ} (hn : n₁ < n₂)
    (h₁ : P.SolvesSSLE (A := Fin n₁) leader) (h₂ : P.SolvesSSLE (A := Fin n₂) leader) : False := by
  classical
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  obtain ⟨C, -, hC⟩ := h₂ (fun _ => q₀)
  obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp (hC C Relation.ReflTransGen.refl)
  have hℓC : leader (C ℓ) = true := by
    have : ℓ ∈ Finset.univ.filter fun a => leader (C a) = true := by rw [hℓ]; simp
    simpa using this
  -- an embedding of `Fin n₁` avoiding the leader `ℓ`
  obtain ⟨e₀⟩ : Nonempty (Fin n₁ ↪ {x : Fin n₂ // x ≠ ℓ}) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; simp; omega
  let e : Fin n₁ ↪ Fin n₂ := e₀.trans (Function.Embedding.subtype _)
  -- the size-`n₁` sub-population (without `ℓ`) elects a leader on its own
  obtain ⟨D', hD', hD's⟩ := h₁ (fun x => C (e x))
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (hD's D' Relation.ReflTransGen.refl)
  have hiD : leader (D' i) = true := by
    have : i ∈ Finset.univ.filter fun a => leader (D' a) = true := by rw [hi]; simp
    simpa using this
  obtain ⟨D, hD, hDe⟩ := P.exists_reachIn_of_embedding e C hD'
  have hℓnot : ¬ ∃ y, e y = ℓ := fun ⟨y, hy⟩ => (e₀ y).2 hy
  have hDℓ : D ℓ = C ℓ := hD.apply_eq hℓnot
  have hei : e i ≠ ℓ := (e₀ i).2
  have hsub : ({e i, ℓ} : Finset (Fin n₂)) ⊆ Finset.univ.filter fun x => leader (D x) = true := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · have : D (e i) = D' i := congrFun hDe i
      simpa [this] using hiD
    · simpa [hDℓ] using hℓC
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair hei] at h2
  have : LeaderCorrect leader D := hC D hD.reachable
  unfold LeaderCorrect numLeaders at this; omega

end TimeOptimalSSLE.NProtocol
