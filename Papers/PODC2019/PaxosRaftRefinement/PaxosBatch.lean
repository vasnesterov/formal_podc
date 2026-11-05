import Papers.PODC2019.PaxosRaftRefinement.Paxos

/-!
# Batches of MultiPaxos steps

A single Raft* step corresponds to a *sequence* of MultiPaxos steps (Appendix C: "one
AppendEntries step is mapped to several Phase2a steps"). These lemmas run `phase2a`, `phase2b`
and `learn` for all positions of a list of values.
-/

namespace Podc.PaxosRaftRefinement.Paxos

variable {N V : Type*} [DecidableEq N] {Q : QuorumSystem N}

theorem setOf_append_singleton {α : Type*} (L₀ : List V) (v : V) (F : ℕ → V → α) :
    {x | ∃ i, ∃ h : i < (L₀ ++ [v]).length, x = F i (L₀ ++ [v])[i]} =
      insert (F L₀.length v) {x | ∃ i, ∃ h : i < L₀.length, x = F i L₀[i]} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases Nat.lt_or_ge i L₀.length with h | h
    · exact Or.inr ⟨i, h, by rw [hx, List.getElem_append_left h]⟩
    · have : i = L₀.length := by simp at hi; omega
      subst this; left; rw [hx]; simp
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨L₀.length, by simp, by rw [hx]; simp⟩
    · exact ⟨i, by simp; omega, by rw [hx, List.getElem_append_left hi]⟩

theorem setOf_nil {α : Type*} (F : ℕ → V → α) :
    {x | ∃ i, ∃ h : i < ([] : List V).length, x = F i ([] : List V)[i]} = ∅ := by
  ext x; simp

/-- The leader `s` proposes `L[i]` for every instance `i < L.length`. -/
theorem phase2a_batch (p : State N V) (s : N) (L : List V) (hl : p.leader s = true)
    (hv : ∀ i (h : i < L.length), p.inst s i = none ∨ ∃ c, p.inst s i = some (c, L[i]))
    (hu : ∀ i (h : i < L.length) w, (i, p.ballot s, w) ∈ p.m2a → w = L[i]) :
    Relation.ReflTransGen (Step Q) p
      { p with m2a := p.m2a ∪ {x | ∃ i, ∃ h : i < L.length, x = (i, p.ballot s, L[i])} } := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [setOf_nil (fun i (w : V) => (i, p.ballot s, w)), Set.union_empty]
  | append_singleton L₀ v ih =>
    have hlen : ∀ i, i < L₀.length → i < (L₀ ++ [v]).length := fun i h => by simp; omega
    have hget : ∀ i (h : i < L₀.length), (L₀ ++ [v])[i]'(hlen i h) = L₀[i] := fun i h =>
      List.getElem_append_left h
    have ih' := ih (fun i h => by rw [← hget i h]; exact hv i (hlen i h))
      (fun i h w hw => by rw [← hget i h]; exact hu i (hlen i h) w hw)
    have hn : L₀.length < (L₀ ++ [v]).length := by simp
    have hgetn : (L₀ ++ [v])[L₀.length]'hn = v := by simp
    rw [setOf_append_singleton L₀ v (fun i w => (i, p.ballot s, w)), Set.union_insert]
    refine ih'.tail ?_
    exact Step.phase2a (Q := Q)
      { p with m2a := p.m2a ∪ {x | ∃ i, ∃ h : i < L₀.length, x = (i, p.ballot s, L₀[i])} }
      s L₀.length v hl (by simpa [hgetn] using hv _ hn) (by
        rintro w (hw | ⟨i, hi, hiw⟩)
        · have := hu _ hn w hw; rwa [hgetn] at this
        · simp only [Prod.mk.injEq] at hiw; omega)

/-- Server `s` accepts the proposals `(i, b, L[i])` for every `i < L.length` (`L ≠ []`). -/
theorem phase2b_batch (p : State N V) (s : N) (b : ℕ) (L : List V) (hL : L ≠ [])
    (hb : p.ballot s ≤ b) (hm : ∀ i (h : i < L.length), (i, b, L[i]) ∈ p.m2a) :
    Relation.ReflTransGen (Step Q) p
      { p with
        ballot := Function.update p.ballot s b
        leader := Function.update p.leader s (if p.ballot s < b then false else p.leader s)
        inst := Function.update p.inst s
          (fun i => if h : i < L.length then some (b, L[i]) else p.inst s i)
        m2b := p.m2b ∪ {x | ∃ i, ∃ h : i < L.length, x = (s, i, b, L[i])} } := by
  induction L using List.reverseRecOn with
  | nil => exact absurd rfl hL
  | append_singleton L₀ v ih =>
    have hlen : ∀ i, i < L₀.length → i < (L₀ ++ [v]).length := fun i h => by simp; omega
    have hget : ∀ i (h : i < L₀.length), (L₀ ++ [v])[i]'(hlen i h) = L₀[i] := fun i h =>
      List.getElem_append_left h
    have hn : L₀.length < (L₀ ++ [v]).length := by simp
    have hgetn : (L₀ ++ [v])[L₀.length]'hn = v := by simp
    have hmv : (L₀.length, b, v) ∈ p.m2a := by have := hm _ hn; rwa [hgetn] at this
    rw [setOf_append_singleton L₀ v (fun i w => (s, i, b, w)), Set.union_insert]
    have hinst : ∀ (f : ℕ → Option (ℕ × V)),
        (fun i => if h : i < (L₀ ++ [v]).length then some (b, (L₀ ++ [v])[i]) else f i) =
        Function.update (fun i => if h : i < L₀.length then some (b, L₀[i]) else f i)
          L₀.length (some (b, v)) := by
      intro f; funext i
      by_cases hi : i = L₀.length
      · subst hi; simp [hgetn]
      · rw [Function.update_of_ne hi]
        by_cases hi' : i < L₀.length
        · rw [dif_pos (hlen i hi'), dif_pos hi', hget]
        · have : ¬ i < (L₀ ++ [v]).length := by simp; omega
          rw [dif_neg this, dif_neg hi']
    rcases eq_or_ne L₀ [] with rfl | h0
    · refine Relation.ReflTransGen.single ?_
      have := Step.phase2b (Q := Q) p s 0 b v (by simpa using hmv) hb
      convert this using 2
      · funext a; by_cases ha : a = s
        · subst ha; simp only [Function.update_self]; rw [hinst]; simp
        · simp [Function.update_of_ne ha]
      · simp
    · have ih' := ih h0 (fun i h => by rw [← hget i h]; exact hm i (hlen i h))
      refine ih'.tail ?_
      set p₀ : State N V := { p with
        ballot := Function.update p.ballot s b
        leader := Function.update p.leader s (if p.ballot s < b then false else p.leader s)
        inst := Function.update p.inst s
          (fun i => if h : i < L₀.length then some (b, L₀[i]) else p.inst s i)
        m2b := p.m2b ∪ {x | ∃ i, ∃ h : i < L₀.length, x = (s, i, b, L₀[i])} } with hp₀
      have := Step.phase2b (Q := Q) p₀ s L₀.length b v hmv (by simp [hp₀])
      convert this using 2
      · simp [hp₀]
      · simp [hp₀]
      · funext a; by_cases ha : a = s
        · subst ha; simp only [hp₀, Function.update_self]; rw [hinst]
        · simp [hp₀, Function.update_of_ne ha]

/-- Server `s` learns `L[i]` for every instance `i < L.length`. -/
theorem learn_batch (p : State N V) (s : N) (L : List V)
    (hc : ∀ i (h : i < L.length), ∃ b A, Q.IsQuorum A ∧ ∀ a ∈ A, (a, i, b, L[i]) ∈ p.m2b) :
    Relation.ReflTransGen (Step Q) p
      { p with
        chosen := Function.update p.chosen s
          (p.chosen s ∪ {x | ∃ i, ∃ h : i < L.length, x = (i, L[i])}) } := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [setOf_nil (fun i (w : V) => (i, w)), Set.union_empty, Function.update_eq_self]
  | append_singleton L₀ v ih =>
    have hlen : ∀ i, i < L₀.length → i < (L₀ ++ [v]).length := fun i h => by simp; omega
    have hget : ∀ i (h : i < L₀.length), (L₀ ++ [v])[i]'(hlen i h) = L₀[i] := fun i h =>
      List.getElem_append_left h
    have hn : L₀.length < (L₀ ++ [v]).length := by simp
    have hgetn : (L₀ ++ [v])[L₀.length]'hn = v := by simp
    have ih' := ih (fun i h => by rw [← hget i h]; exact hc i (hlen i h))
    refine ih'.tail ?_
    obtain ⟨b, A, hA, hA'⟩ := hc _ hn
    rw [hgetn] at hA'
    set p₀ : State N V := { p with
      chosen := Function.update p.chosen s
        (p.chosen s ∪ {x | ∃ i, ∃ h : i < L₀.length, x = (i, L₀[i])}) } with hp₀
    have := Step.learn (Q := Q) p₀ s L₀.length b v A hA hA'
    convert this using 2
    funext a
    by_cases ha : a = s
    · subst ha
      simp only [hp₀, Function.update_self]
      rw [setOf_append_singleton L₀ v (fun i w => (i, w)), Set.union_insert]
    · simp [hp₀, Function.update_of_ne ha]

end Podc.PaxosRaftRefinement.Paxos
