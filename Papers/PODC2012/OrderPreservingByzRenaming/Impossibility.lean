import Papers.PODC2012.OrderPreservingByzRenaming.Spec

/-!
# Impossibility of order-preserving renaming for `n ≤ 3t` (Theorem 46)

**Three processes, one fault (Theorem 46).** We run a candidate protocol on an infinite *line* of
nodes `0, 1, 2, …`; node `i` runs the code of process `i mod 3` with original id `i`, listens to
node `i + 1` as process `(i + 1) mod 3` and to node `i - 1` as process `(i + 2) mod 3` (node `0`
hears nothing from its left). For every `i`, the two adjacent nodes `i, i + 1` form a *lift*:
the single Byzantine process `(i + 2) mod 3` simulates the rest of the line (FLM covering,
`CoverSystem.decides_scenario_iff`). Applying the specification to the `M` executions
`i = 0, …, M - 1` gives names `v₀ < v₁ < ⋯ < v_M` in `{1, …, M}`: a contradiction. Only the ids
`0, …, M` are used, so the impossibility holds from the original namespace `{0, …, M}` (of size
`M + 1`) into `{1, …, M}`, as in the paper. The paper uses a ring of `M + 1` processes; with
process-specific code (CSLib's protocols may depend on the process) a ring would need length
divisible by 3, the line avoids this.

**General `n ≤ 3t`.** As in the paper, three processes simulate the `n`-process system
(CSLib's `GroupSim`): process `i ∈ Fin 3` simulates the processes with index `≡ i (mod 3)`,
giving the simulated process with index `k` the id `x · n + k`, where `x` is the simulator's id;
the simulator decides the name of one of its simulated processes. The simulated original
namespace is `{0, …, n (M + 1) - 1}`.
-/

namespace Podc.OrderPreservingByzRenaming

open Cslib.Byzantine.LockStep

section ThreeProcesses

/-- The process whose code node `i` of the line runs. -/
def lineφ (i : ℕ) : Fin 3 := ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The line covering system: node `i` listens to `i + 1` as `lineφ (i + 1)` and to `i - 1` as
`lineφ (i + 2)` (if `i ≥ 1`); node `i` has original id `i`. -/
def lineCover : CoverSystem (Fin 3) ℕ ℕ where
  φ := lineφ
  nbr i p := if p = lineφ (i + 1) then some (i + 1)
    else if p = lineφ (i + 2) ∧ 1 ≤ i then some (i - 1) else none
  xq i := i

/-- The lift of the honest pair `lineφ i, lineφ (i + 1)` to the nodes `i, i + 1`. -/
def lineσ (i : ℕ) (p : Fin 3) : ℕ := if p = lineφ i then i else i + 1

lemma lineφ_ne_succ (i : ℕ) : lineφ i ≠ lineφ (i + 1) := by
  simp only [lineφ, ne_eq, Fin.mk.injEq]; omega

lemma lineφ_cases (i : ℕ) (p : Fin 3) : p = lineφ i ∨ p = lineφ (i + 1) ∨ p = lineφ (i + 2) := by
  simp only [lineφ, Fin.ext_iff]; omega

lemma lineLift (i : ℕ) :
    lineCover.Lift (⊤ : SimpleGraph (Fin 3)) {lineφ (i + 2)} (lineσ i) where
  φ_σ p hp := by
    simp only [Set.mem_singleton_iff] at hp
    rcases lineφ_cases i p with rfl | rfl | rfl
    · simp [lineσ, lineCover]
    · simp [lineσ, lineCover, (lineφ_ne_succ i).symm]
    · exact absurd rfl hp
  nbr_σ p q hp hq hpq := by
    simp only [Set.mem_singleton_iff] at hp hq
    have hpq' : p ≠ q := hpq.ne
    have h1 := lineφ_ne_succ i
    rcases lineφ_cases i p with rfl | rfl | rfl <;> rcases lineφ_cases i q with rfl | rfl | rfl
    all_goals first | exact absurd rfl hp | exact absurd rfl hq | exact absurd rfl hpq' | skip
    · -- p = φ i, q = φ (i+1)
      have e1 : lineφ i ≠ lineφ (i + 1 + 1) := by simp only [lineφ, ne_eq, Fin.ext_iff]; omega
      have e2 : lineφ i = lineφ (i + 1 + 2) := by simp only [lineφ, Fin.ext_iff]; omega
      have s1 : lineσ i (lineφ (i + 1)) = i + 1 := by simp [lineσ, h1.symm]
      rw [s1]
      show (if lineφ i = lineφ (i + 1 + 1) then some (i + 1 + 1)
        else if lineφ i = lineφ (i + 1 + 2) ∧ 1 ≤ i + 1 then some (i + 1 - 1) else none) = _
      rw [if_neg e1, if_pos ⟨e2, by omega⟩, lineσ, if_pos rfl]; rfl
    · -- p = φ (i+1), q = φ i
      simp [lineσ, lineCover, hpq']

/-- In the execution simulating nodes `i, i + 1` (ids `i < i + 1 ≤ M`), the two nodes decide
names `1 ≤ a < b ≤ M`. -/
lemma line_step {Msg : Type} {alg : Protocol (Fin 3) ℕ Msg ℕ} {M : ℕ}
    (halg : Solves ⊤ alg (atMost 1) (OPRenamingOn (Set.Iio (M + 1)) M)) (i : ℕ) (hi : i < M) :
    ∃ a b, lineCover.Decides ⊤ alg i a ∧ lineCover.Decides ⊤ alg (i + 1) b ∧
      1 ≤ a ∧ a < b ∧ b ≤ M := by
  set s := lineCover.scenario ⊤ alg {lineφ (i + 2)} (lineσ i) (fun _ => 0)
  have hL := lineLift i
  have hbyz : s.byz ∈ (atMost 1 : AdvStructure (Fin 3)) := by
    simp [s, Set.ncard_singleton]
  have hspec := halg s hbyz (CoverSystem.scenario_reliable _ _)
  have hp0 : lineφ i ∉ s.byz := by
    simp only [s, CoverSystem.scenario_byz, Set.mem_singleton_iff, lineφ, Fin.ext_iff]; omega
  have hp1 : lineφ (i + 1) ∉ s.byz := by
    simp only [s, CoverSystem.scenario_byz, Set.mem_singleton_iff, lineφ, Fin.ext_iff]; omega
  have hσ0 : lineσ i (lineφ i) = i := by simp [lineσ]
  have hσ1 : lineσ i (lineφ (i + 1)) = i + 1 := by simp [lineσ, (lineφ_ne_succ i).symm]
  have hin : ∀ p, p ∉ s.byz → s.input p = lineσ i p := fun p hp =>
    CoverSystem.scenario_input_of_not_mem _ _ hp
  have hhon : ∀ p, p ∉ s.byz → p = lineφ i ∨ p = lineφ (i + 1) := by
    intro p hp
    rcases lineφ_cases i p with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · simp [s, h] at hp
  obtain ⟨hterm, hval, -, hord⟩ := hspec (by
    refine ⟨fun p hp q hq hpq => ?_, fun p hp => ?_⟩
    · have hp' : p ∉ s.byz := hp
      have hq' : q ∉ s.byz := hq
      rw [hin p hp', hin q hq'] at hpq
      rcases hhon p hp' with rfl | rfl <;> rcases hhon q hq' with rfl | rfl <;>
        simp_all
    · have hp' : p ∉ s.byz := hp
      rw [hin p hp']
      rcases hhon p hp' with rfl | rfl
      · rw [hσ0]; simp; omega
      · rw [hσ1]; simp; omega)
  obtain ⟨a, ha⟩ := hterm _ hp0
  obtain ⟨b, hb⟩ := hterm _ hp1
  have hab := hord _ hp0 _ hp1 a b ha hb (by rw [hin _ hp0, hin _ hp1, hσ0, hσ1]; omega)
  have ha' := (CoverSystem.decides_scenario_iff lineCover hL _ hp0 a).1 ha
  have hb' := (CoverSystem.decides_scenario_iff lineCover hL _ hp1 b).1 hb
  rw [hσ0] at ha'
  rw [hσ1] at hb'
  exact ⟨a, b, ha', hb', (hval _ hp0 a ha).1, hab, (hval _ hp1 b hb).2⟩

/-- **Theorem 46 of the thesis.** There is no deterministic algorithm solving order-preserving
renaming with `n = 3` processes and `t = 1` Byzantine fault, from the original namespace
`{0, …, M}` into the target namespace `{1, …, M}`, for any `M ≥ 1`. -/
theorem theorem_46 (M : ℕ) (hM : 1 ≤ M) :
    ¬ Solvable (⊤ : SimpleGraph (Fin 3)) (atMost 1) (OPRenamingOn (P := Fin 3) (Set.Iio (M + 1)) M) := by
  rintro ⟨Msg, alg, halg⟩
  -- by induction along the line, node `i ≤ M` decides a name `≥ i + 1`
  have key : ∀ i ≤ M, ∃ a, lineCover.Decides ⊤ alg i a ∧ i + 1 ≤ a ∧ a ≤ M := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨a, b, ha, -, h1, hab, hb⟩ := line_step halg 0 (by omega)
      exact ⟨a, ha, h1, by omega⟩
    | succ i ih =>
      intro hi
      obtain ⟨a, ha, hia, -⟩ := ih (by omega)
      obtain ⟨a', b, ha', hb, -, hab, hbM⟩ := line_step halg i (by omega)
      have := FirstSome.unique ha ha'
      exact ⟨b, hb, by omega, hbM⟩
  obtain ⟨a, -, h1, h2⟩ := key M le_rfl
  omega

end ThreeProcesses

section General

variable {P : Type} [Fintype P]

/-- The group of a process: its index modulo 3. -/
noncomputable def grp3 (p : P) : Fin 3 := ⟨(Fintype.equivFin P p).val % 3, Nat.mod_lt _ (by norm_num)⟩

lemma card_fiber_grp3 (B : Set (Fin 3)) (hB : B.ncard ≤ 1) :
    (grp3 (P := P) ⁻¹' B).ncard ≤ (Fintype.card P + 2) / 3 := by
  classical
  rcases (Set.ncard_le_one_iff_eq (Set.toFinite _)).1 hB with rfl | ⟨c, rfl⟩
  · simp
  set e := Fintype.equivFin P
  have hsub : grp3 (P := P) ⁻¹' {c} = ↑(Finset.univ.filter fun p => (e p).val % 3 = c.val) := by
    ext p; simp [grp3, e, Fin.ext_iff]
  rw [hsub, Set.ncard_coe_finset]
  have : (Finset.univ.filter fun p => (e p).val % 3 = c.val).card ≤
      (Finset.range ((Fintype.card P + 2) / 3)).card := by
    apply Finset.card_le_card_of_injOn (fun p => (e p).val / 3)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_range]
      have := (e p).isLt
      omega
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq hpq
      apply e.injective
      apply Fin.ext
      omega
  simpa using this

/-- **Theorem 46, general case** (the paper's simulation by three processes): for `3 ≤ n ≤ 3t`
processes, there is no deterministic algorithm solving order-preserving renaming into
`{1, …, M}` (any `M ≥ 1`), even with original ids restricted to `{0, …, n (M + 1) - 1}`. -/
theorem theorem_46_general (t M : ℕ) (hM : 1 ≤ M) (h3 : 3 ≤ Fintype.card P)
    (ht : Fintype.card P ≤ 3 * t) :
    ¬ Solvable (⊤ : SimpleGraph P) (atMost t)
      (OPRenamingOn (P := P) (Set.Iio (Fintype.card P * (M + 1))) M) := by
  intro h
  apply theorem_46 M hM
  set n := Fintype.card P
  set e := Fintype.equivFin P
  refine GroupSim.Solvable.of_groupSim grp3 (fun q => e.symm ⟨q.val, by omega⟩) ?_
    (fun _ x p => x * n + (e p).val) (fun _ o => o) ?_ ?_ ?_ h
  · intro q; simp [grp3, e, Fin.ext_iff]
  · intro p p' _ hne; simpa using hne
  · intro B hB
    simp only [mem_atMost] at hB ⊢
    exact (card_fiber_grp3 B hB).trans (by omega)
  · intro x B dec dec' hP hdec ⟨hinj, hx⟩
    have hrep : ∀ q : Fin 3, grp3 (e.symm ⟨q.val, by omega⟩) = q := by
      intro q; simp [grp3, e, Fin.ext_iff]
    have hrepB : ∀ q : Fin 3, q ∉ B → e.symm ⟨q.val, by omega⟩ ∈ (grp3 ⁻¹' B)ᶜ := by
      intro q hq; simp [hrep q, hq]
    have hdiv : ∀ (a b : ℕ) (p : P), (a * n + (e p).val) / n = a ∧ (a * n + (e p).val) % n = (e p).val := by
      intro a b p
      have hp := (e p).isLt
      have hn : 0 < n := by omega
      constructor
      · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hp, zero_add]
      · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
    obtain ⟨hterm, hval, huniq, hord⟩ := hP (by
      refine ⟨fun p hp p' hp' hpp' => ?_, fun p hp => ?_⟩
      · simp only at hpp'
        have h1 := hdiv (x (grp3 p)) 0 p
        have h2 := hdiv (x (grp3 p')) 0 p'
        rw [hpp'] at h1
        apply e.injective
        apply Fin.ext
        rw [← h1.2, h2.2]
      · have hgp : grp3 p ∉ B := hp
        have := hx (grp3 p) hgp
        simp only [Set.mem_Iio] at this ⊢
        have hp' := (e p).isLt
        calc x (grp3 p) * n + (e p).val < x (grp3 p) * n + n := by omega
          _ = (x (grp3 p) + 1) * n := by ring
          _ ≤ (M + 1) * n := Nat.mul_le_mul_right _ (by omega)
          _ = n * (M + 1) := by ring)
    refine ⟨fun q hq => ?_, fun q hq o ho => ?_, fun q hq q' hq' o o' ho ho' hne => ?_,
      fun q hq q' hq' o o' ho ho' hlt => ?_⟩
    · obtain ⟨o, ho⟩ := hterm _ (hrepB q hq)
      exact ⟨o, (hdec q hq o).2 ⟨o, ho, rfl⟩⟩
    · obtain ⟨o₁, h₁, rfl⟩ := (hdec q hq o).1 ho
      exact hval _ (hrepB q hq) _ h₁
    · obtain ⟨o₁, h₁, rfl⟩ := (hdec q hq o).1 ho
      obtain ⟨o₂, h₂, rfl⟩ := (hdec q' hq' o').1 ho'
      refine huniq _ (hrepB q hq) _ (hrepB q' hq') _ _ h₁ h₂ ?_
      intro heq
      apply hne
      have := congrArg grp3 heq
      rwa [hrep, hrep] at this
    · obtain ⟨o₁, h₁, rfl⟩ := (hdec q hq o).1 ho
      obtain ⟨o₂, h₂, rfl⟩ := (hdec q' hq' o').1 ho'
      refine hord _ (hrepB q hq) _ (hrepB q' hq') _ _ h₁ h₂ ?_
      simp only [hrep]
      have h1 := (e (e.symm ⟨q.val, by omega⟩)).isLt
      have h2 := (e (e.symm ⟨q'.val, by omega⟩)).isLt
      have : x q + 1 ≤ x q' := hlt
      calc x q * n + (e (e.symm ⟨q.val, by omega⟩)).val < x q * n + n := by omega
        _ = (x q + 1) * n := by ring
        _ ≤ x q' * n := Nat.mul_le_mul_right _ this
        _ ≤ _ := Nat.le_add_right _ _

/-- **Theorem 46** for arbitrary original ids: for `3 ≤ n ≤ 3t` no deterministic algorithm solves
order-preserving renaming, whatever the target namespace `{1, …, M}`. -/
theorem theorem_46_anyNamespace (t M : ℕ) (h3 : 3 ≤ Fintype.card P)
    (ht : Fintype.card P ≤ 3 * t) :
    ¬ Solvable (⊤ : SimpleGraph P) (atMost t) (OPRenaming (P := P) M) := by
  intro h
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · -- names in `{1, …, 0}`: impossible as soon as a correct process exists
    obtain ⟨Msg, alg, halg⟩ := h
    have hs := halg ⟨∅, fun p => (Fintype.equivFin P p).val, fun _ _ _ => none, fun _ _ _ => False⟩
      (by simp) (fun _ _ _ h => h)
    obtain ⟨hterm, hval, -⟩ := hs ⟨fun p _ q _ hpq => (Fintype.equivFin P).injective (Fin.ext hpq),
      fun _ _ => trivial⟩
    obtain ⟨o, ho⟩ := hterm ((Fintype.equivFin P).symm ⟨0, by omega⟩) (by simp [Scenario.honest])
    have hp : (Fintype.equivFin P).symm ⟨0, by omega⟩ ∈ Scenario.honest
      (⟨∅, fun p => (Fintype.equivFin P p).val, fun _ _ _ => none, fun _ _ _ => False⟩ :
        Scenario P ℕ Msg) := by simp [Scenario.honest]
    have := hval _ hp o ho
    omega
  · exact theorem_46_general t M hM h3 ht (solvable_mono (Set.subset_univ _) h)

end General

end Podc.OrderPreservingByzRenaming
