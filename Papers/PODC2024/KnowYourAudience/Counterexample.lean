import Podc.Computability.Distributed.AnonymousNetworks.Lifting

/-!
# Counterexamples to the impossibility half of Theorem 4.1 and Corollary 4.2

In the paper's model every agent receives its own message on its self-loop, so in round 1 an agent
learns its indegree. In a strongly connected network the indegree is `1` iff the agent is alone.
Hence the function "`1` if the network has a single agent, `0` otherwise" (`isSingleton`) is
computable — in every communication model, even simple broadcast — although it is not
frequency-based: `isSingleton [a] = 1 ≠ 0 = isSingleton [a, a]`.

With symmetric communications an agent also learns, in round 2, the indegrees of its neighbours:
both endpoints of an edge have degree one (one neighbour besides themselves) iff the network is
`K₂`. Hence `isPair` ("the network has exactly two agents") is computable with symmetric
communications, and is not frequency-based on vectors of length `≥ 2`:
`isPair [a, b] = 1 ≠ 0 = isPair [a, b, a, b]`.

Both algorithms are self-stabilizing (the output is correct from round 1, resp. 2, whatever the
initial configuration), so the counterexamples do not depend on how initial states are chosen.
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset Filter Topology

universe u

variable {I : Type u}

/-- "The network has a single agent." -/
def isSingleton (l : List I) : ℕ := if l.length = 1 then 1 else 0

/-- "The network has exactly two agents." -/
def isPair (l : List I) : ℕ := if l.length = 2 then 1 else 0

/-- Count the received messages; the output is `1` iff exactly one message was received. -/
def detectOne (I : Type u) : Algorithm I ℕ where
  Q := I × Bool
  M := PUnit
  init a := (a, false)
  send _ _ _ := PUnit.unit
  trans q R := (q.1, decide (Multiset.card R = 1))
  out q := if q.2 then 1 else 0

lemma detectOne_allowed (m : CommModel) : m.Allowed (detectOne I) := by
  cases m <;> simp [CommModel.Allowed, detectOne]

lemma detectOne_out {n : ℕ} (N : Network (Fin n)) (hsc : N.StronglyConnected)
    (C₀ : Fin n → (detectOne I).Q) (t : ℕ) (i : Fin n) :
    (detectOne I).out (N.runFrom (detectOne I) C₀ (t + 1) i) = if n = 1 then 1 else 0 := by
  rw [Network.runFrom_succ]
  simp only [Network.step, Network.recv]
  have := N.card_inN_eq_one_iff hsc i
  rw [Fintype.card_fin] at this
  by_cases h : n = 1 <;> simp [detectOne, h, this]

/-- `isSingleton` is computable in the class of static strongly connected networks, in every
communication model (from any initial configuration, all outputs are correct from round 1 on). -/
theorem isSingleton_computable (m : CommModel) :
    Computable m staticSC (fun _ => True) (isSingleton (I := I)) := by
  refine ⟨detectOne I, detectOne_allowed m, fun n _ N hN _ x _ i => ?_⟩
  rw [tendsto_atTop_nhds]
  intro U hU _
  refine ⟨1, fun t ht => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Network.run, detectOne_out N hN]
  simpa [isSingleton] using hU

lemma isSingleton_not_frequencyBased [Nonempty I] [DecidableEq I] :
    ¬ FrequencyBased (isSingleton (I := I)) := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty I›
  have := h [a] [a, a] (by simp) (by simp)
    (by rw [freq_eq_freq_iff (by simp) (by simp)]; intro b; by_cases hb : a = b <;> simp [hb])
  simp [isSingleton] at this

/-! ### `K₂` is recognisable with symmetric communications -/

/-- Round 1: learn the indegree. Later rounds: broadcast it; the output is `1` iff the agent and
all its in-neighbours have indegree `2`. -/
def detectTwo (I : Type u) : Algorithm I ℕ where
  Q := I × ℕ × Bool
  M := ULift ℕ
  init a := (a, 0, false)
  send q _ _ := ⟨q.2.1⟩
  trans q R := (q.1, Multiset.card R, decide (Multiset.card R = 2 ∧ ∀ r ∈ R, r.down = 2))
  out q := if q.2.2 then 1 else 0

lemma detectTwo_allowed : CommModel.symmetric.Allowed (detectTwo I) := by
  simp [CommModel.Allowed, detectTwo]

lemma detectTwo_deg {n : ℕ} (N : Network (Fin n)) (C₀ : Fin n → (detectTwo I).Q) (t : ℕ)
    (i : Fin n) : (N.runFrom (detectTwo I) C₀ (t + 1) i).2.1 = (N.inN i).card := by
  rw [Network.runFrom_succ]
  simp [Network.step, Network.recv, detectTwo]

/-- In a bidirectional strongly connected network, an agent of degree `2` whose in-neighbours all
have degree `2` lives in a network with two agents, and conversely. -/
lemma pair_iff {n : ℕ} {N : Network (Fin n)} (hsc : N.StronglyConnected) (hsym : N.Symmetric)
    (i : Fin n) : ((N.inN i).card = 2 ∧ ∀ j ∈ N.inN i, (N.inN j).card = 2) ↔ n = 2 := by
  constructor
  · rintro ⟨hi, hj⟩
    obtain ⟨a, b, hab, hiab⟩ := Finset.card_eq_two.1 hi
    -- `j` is the other vertex
    have hii := N.self_mem_inN i
    obtain ⟨j, hjmem, hji⟩ : ∃ j ∈ N.inN i, j ≠ i := by
      rw [hiab] at hii ⊢
      rcases Finset.mem_insert.1 hii with h | h
      · exact ⟨b, by simp, fun h' => hab (h ▸ h'.symm ▸ rfl)⟩
      · rw [Finset.mem_singleton] at h
        exact ⟨a, by simp, fun h' => hab (h ▸ h' ▸ rfl)⟩
    have hinI : N.inN i = {i, j} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hii
        · exact hjmem
      · rw [hi, Finset.card_pair hji.symm]
    have hij' : i ∈ N.inN j := by
      rw [N.mem_inN]; exact hsym _ _ ((N.mem_inN).1 hjmem)
    have hinJ : N.inN j = {i, j} := by
      symm; apply Finset.eq_of_subset_of_card_le
      · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hij'
        · exact N.self_mem_inN _
      · rw [hj j hjmem, Finset.card_pair hji.symm]
    -- every vertex reaches `i`, hence lies in `{i, j}`
    have hS : ∀ k, k ∈ ({i, j} : Finset (Fin n)) := by
      intro k
      have key : ∀ c, Relation.ReflTransGen N.Adj k c → c ∈ ({i, j} : Finset (Fin n)) →
          k ∈ ({i, j} : Finset (Fin n)) := by
        intro c h
        induction h using Relation.ReflTransGen.head_induction_on with
        | refl => exact id
        | head hkb _ ih =>
          intro hc
          have hb := ih hc
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rename_i a b
          rcases hb with rfl | rfl
          · rw [← hinI]; exact (N.mem_inN).2 hkb
          · rw [← hinJ]; exact (N.mem_inN).2 hkb
      exact key i (hsc k i) (by simp)
    have : (Finset.univ : Finset (Fin n)) = {i, j} := Finset.eq_univ_of_forall hS ▸ rfl
    have h2 := congrArg Finset.card this
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hji.symm] at h2
    exact h2
  · intro hn
    subst hn
    have hall : ∀ k : Fin 2, N.inN k = Finset.univ := by
      intro k
      apply Finset.eq_univ_of_forall
      intro j
      by_cases hjk : j = k
      · subst hjk; exact N.self_mem_inN _
      · obtain ⟨j', hj', hj'k⟩ := N.exists_mem_inN_ne hsc hjk
        have : j' = j := by omega
        exact this ▸ hj'
    refine ⟨by rw [hall]; rfl, fun j _ => by rw [hall]; rfl⟩

lemma detectTwo_out {n : ℕ} (N : Network (Fin n)) (hsc : N.StronglyConnected)
    (hsym : N.Symmetric) (C₀ : Fin n → (detectTwo I).Q) (t : ℕ) (i : Fin n) :
    (detectTwo I).out (N.runFrom (detectTwo I) C₀ (t + 2) i) = if n = 2 then 1 else 0 := by
  simp only [← pair_iff hsc hsym i]
  have hd : ∀ j, (N.runFrom (detectTwo I) C₀ (t + 1) j).2.1 = (N.inN j).card :=
    detectTwo_deg N C₀ t
  rw [Network.runFrom_succ]
  simp only [Network.step, Network.recv]
  simp only [detectTwo, Multiset.card_map, Finset.card_val, Multiset.mem_map, Finset.mem_val,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [detectTwo] at hd
  simp [hd]

/-- `isPair` is computable with symmetric communications in static strongly connected
networks. -/
theorem isPair_computable :
    Computable .symmetric staticSC (fun _ => True) (isPair (I := I)) := by
  refine ⟨detectTwo I, detectTwo_allowed, fun n _ N hN hsym x _ i => ?_⟩
  rw [tendsto_atTop_nhds]
  intro U hU _
  refine ⟨2, fun t ht => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  rw [Network.run, detectTwo_out N hN hsym]
  simpa [isPair] using hU

lemma isPair_not_frequencyBasedFrom_two [Nonempty I] [DecidableEq I] :
    ¬ FrequencyBasedFrom 2 (isPair (I := I)) := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty I›
  have := h [a, a] [a, a, a, a] (by simp) (by simp) (by simp) (by simp)
    (by rw [freq_eq_freq_iff (by simp) (by simp)]; intro b; by_cases hb : a = b <;> simp [hb])
  simp [isPair] at this

end Podc.KnowYourAudience
