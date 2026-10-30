import Papers.PODC2025.AsymmetricDAGConsensus.Gather3Liveness
import Papers.PODC2025.AsymmetricDAGConsensus.Counterexamples

/-!
# Non-vacuity of the hypotheses of Lemma 3.8

* `lemma_3_8_maxGuild`: Lemma 3.8 for the maximal guild, as in the paper.
* `rbc_of_bad_empty`: in an execution without corruptions the reliable-broadcast hypotheses
  `RBC` hold for every set of processes.
* `alg3_fig1`: on the 30-process system of Figure 1 (where Algorithm 2 fails, `lemma_3_2`)
  Algorithm 3 has fair executions satisfying all hypotheses of Lemma 3.8; hence all its
  conclusions (termination, common core, validity, agreement) hold for them.
-/

namespace Podc.AsymmetricDAGConsensus

open Cslib.Byzantine.AsyncBroadcast Cslib.AsymmetricQuorum

namespace Gather3

variable {P V : Type*} [DecidableEq P]

/-- **Lemma 3.8** for the maximal guild. -/
theorem lemma_3_8_maxGuild [Fintype P] {Fs Qs : P → Set (Finset P)} {x : P → V}
    {fk : FaultKind} {t : ℕ} (E : Exec (protocol Qs) x fk t) (hF : E.Fair)
    (hrbc : RBC E (maxGuild Fs Qs (Faulty E))) (hQ : IsQuorumSystem Fs Qs)
    (hne : (maxGuild Fs Qs (Faulty E)).Nonempty) :
    (∀ k ∈ maxGuild Fs Qs (Faulty E), ∃ n U, (E.σ n).dec k = some U) ∧
    ExecCommonCore (maxGuild Fs Qs (Faulty E)) E ∧
    (∀ k ∈ maxGuild Fs Qs (Faulty E), ∀ s, Wise Fs (Faulty E) s → ∀ n U,
      (E.σ n).dec k = some U → ∀ v, (s, v) ∈ U → v = x s) ∧
    (∀ k ∈ maxGuild Fs Qs (Faulty E), ∀ k' ∈ maxGuild Fs Qs (Faulty E), ∀ s n n' U U' v v',
      (E.σ n).dec k = some U → (E.σ n').dec k' = some U' → (s, v) ∈ U → (s, v') ∈ U' →
      v = v') :=
  lemma_3_8 E (isGuild_maxGuild Fs Qs (Faulty E)) hF hrbc hQ hne

/-- Without corruptions the reliable-broadcast hypotheses hold. -/
theorem rbc_of_bad_empty {Qs : P → Set (Finset P)} {x : P → V} {fk : FaultKind} {t : ℕ}
    (E : Exec (protocol Qs) x fk t) (hF : E.Fair) (hbad : ∀ i, (E.σ i).bad = ∅)
    (G : Set P) : RBC E G where
  agree q _ q' _ s v v' i j hv hv' := by
    have hc := Exec.correct_of_bad_empty E hbad s
    rw [sent_val (E.reachable i) (genuine_of_correct E hc hv),
      sent_val (E.reachable j) (genuine_of_correct E hc hv')]
  total q _ q' _ s v i hv := by
    have hc := Exec.correct_of_bad_empty E hbad s
    exact hF.deliver q' s _ i (Exec.correct_of_bad_empty E hbad q') hc
      (genuine_of_correct E hc hv)

/-- Injection of the messages into a countable sum type. -/
def GMsg.toSum : GMsg P V → V ⊕ Set (P × V) ⊕ (P × Set (P × V)) ⊕ Bool ⊕ Set (P × V)
  | .val v => .inl v
  | .distS S => .inr (.inl S)
  | .ack j S => .inr (.inr (.inl (j, S)))
  | .ready => .inr (.inr (.inr (.inl true)))
  | .confirm => .inr (.inr (.inr (.inl false)))
  | .distT T => .inr (.inr (.inr (.inr T)))

omit [DecidableEq P] in
theorem GMsg.toSum_injective : Function.Injective (GMsg.toSum (P := P) (V := V)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [GMsg.toSum]

instance [Countable P] [Countable V] [Countable (Set (P × V))] : Countable (GMsg P V) :=
  GMsg.toSum_injective.countable

end Gather3

open Gather3 in
/-- Algorithm 3 on the system of Figure 1: there is a fair execution (no corruptions) that
satisfies every hypothesis of Lemma 3.8 with the guild of all 30 processes. -/
theorem alg3_fig1 (x : Fin 30 → Bool) :
    ∃ E : Exec (protocol (V := Bool) (canonicalQuorums fig1)) x .byzantine 0,
      E.Fair ∧ RBC E Set.univ ∧
      IsGuild (canonicalFailProne fig1) (canonicalQuorums fig1) (Faulty E) Set.univ ∧
      IsQuorumSystem (canonicalFailProne fig1) (canonicalQuorums fig1) := by
  obtain ⟨E, hF, hbad⟩ := exists_fair (protocol (V := Bool) (canonicalQuorums fig1)) x
    .byzantine 0
  have hfault : Faulty E = ∅ := by
    ext p; simp [Faulty, Exec.correct_of_bad_empty E hbad p]
  refine ⟨E, hF, rbc_of_bad_empty E hF hbad _, ?_, isQuorumSystem_canonical fig1_inter⟩
  rw [hfault]; exact isGuild_univ_canonical fig1

open Gather3 in
/-- Consequently, Algorithm 3 has a common core (and terminates) on the system of Figure 1,
where Algorithm 2 does not. -/
theorem alg3_fig1_commonCore (x : Fin 30 → Bool) :
    ∃ E : Exec (protocol (V := Bool) (canonicalQuorums fig1)) x .byzantine 0,
      E.Fair ∧ (∀ k, ∃ n U, (E.σ n).dec k = some U) ∧ ExecCommonCore Set.univ E := by
  obtain ⟨E, hF, hrbc, hG, hQ⟩ := alg3_fig1 x
  obtain ⟨h1, h2, -, -⟩ := lemma_3_8 E hG hF hrbc hQ ⟨0, Set.mem_univ _⟩
  exact ⟨E, hF, fun k => h1 k (Set.mem_univ k), h2⟩

end Podc.AsymmetricDAGConsensus
