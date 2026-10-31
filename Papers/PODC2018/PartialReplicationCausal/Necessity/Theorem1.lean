import Papers.PODC2018.PartialReplicationCausal.Necessity.Case3

/-!
# Theorem 1 (necessity)

**Theorem 1** of Xiang–Vaidya: if a deterministic metadata algorithm implements replica-centric
causal consistency, then in any quiescent reachable state, replica `i` is *not* oblivious to
updates on any edge `e_jk ∈ E_i` of its timestamp graph. Since the metadata of `i` must then
distinguish causal dependency graphs that differ only in updates on `e_jk`, it must, in effect,
track every edge of `E_i`.

The proof distinguishes `j = i` (`T1.case1`), `k = i` (`T1.case2`) and the loop case
(`T1.case3`); here the loop is turned into the lists of writes used by `T1.case3`.
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*} {X : ι → Set Reg} {A : Alg ι Reg M}

namespace T1

@[simp] lemma linked_nil (z : Reg) (t : ι) : Linked X z [] t ↔ z ∈ X t := Iff.rfl
@[simp] lemma linked_cons (z : Reg) (p : ι) (x : Reg) (L : List (ι × Reg)) (t : ι) :
    Linked X z ((p, x) :: L) t ↔ z ∈ X p ∧ Linked X x L t := Iff.rfl

/-- The path `i, l₁, …, l_{s-1}, k` gives the writes of the path phase: `i` writes `y₀`, then
`l₁, l₂, …` each write a register shared with the next replica, up to the first register stored
at `k`. -/
lemma path_lists {k : ι} : ∀ (l : List ι) (i : ι), List.IsChain (Adj X) (i :: l ++ [k]) →
    ∃ y₀ Lr La pf xf, y₀ ∈ X i ∧ (∀ q ∈ Lr, q.1 ∈ l ∧ q.2 ∈ X q.1) ∧
      (i, y₀) :: Lr = La ++ [(pf, xf)] ∧ (∀ q ∈ La, q.2 ∉ X k) ∧ xf ∈ X k ∧ Linked X y₀ Lr k
  | [], i, h => by
    simp only [List.cons_append, List.nil_append, List.isChain_cons_cons,
      List.isChain_singleton, and_true] at h
    obtain ⟨-, y, hyi, hyk⟩ := h
    exact ⟨y, [], [], i, y, hyi, by simp, rfl, by simp, hyk, hyk⟩
  | l₁ :: l', i, h => by
    simp only [List.cons_append, List.isChain_cons_cons] at h
    obtain ⟨⟨-, y, hyi, hyl⟩, h'⟩ := h
    by_cases hyk : y ∈ X k
    · exact ⟨y, [], [], i, y, hyi, by simp, rfl, by simp, hyk, hyk⟩
    · obtain ⟨y₀', Lr', La', pf, xf, hy₀', hLr', hsplit', hLa', hxf, hlink'⟩ :=
        path_lists l' l₁ (by simpa using h')
      refine ⟨y, (l₁, y₀') :: Lr', (i, y) :: La', pf, xf, hyi, ?_, ?_, ?_, hxf, ⟨hyl, hlink'⟩⟩
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨by simp, hy₀'⟩
        · exact ⟨by simp [(hLr' q hq).1], (hLr' q hq).2⟩
      · rw [hsplit']; rfl
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hyk
        · exact hLa' q hq

/-- Condition (iii) of the loop gives the writes of the chain phase along `r₂, …, r_t`. -/
lemma chain_lists {i k : ι} {l : List ι} (L₂ : List (ι × Reg))
    (hL₂ : ∀ z ∈ X i, Linked X z L₂ k) : ∀ r : List ι,
    List.IsChain (fun a b => ∃ x ∈ X a ∩ X b, x ∉ X k ∧ ∀ p ∈ l, x ∉ X p) (r ++ [i]) →
    ∃ Lr : List (ι × Reg), (∀ q ∈ Lr, q.1 ∈ r ∧ q.2 ∈ X q.1 ∧ q.2 ∉ X k ∧ ∀ p ∈ l, q.2 ∉ X p) ∧
      ∀ z ∈ X (r.headD i), Linked X z (Lr ++ L₂) k
  | [], _ => ⟨[], by simp, fun z hz => hL₂ z hz⟩
  | a :: r', h => by
    have h' : (∃ x ∈ X a ∩ X (r'.headD i), x ∉ X k ∧ ∀ p ∈ l, x ∉ X p) ∧
        List.IsChain (fun a b => ∃ x ∈ X a ∩ X b, x ∉ X k ∧ ∀ p ∈ l, x ∉ X p) (r' ++ [i]) := by
      cases r' with
      | nil => simpa using h
      | cons b r'' => simpa using h
    obtain ⟨⟨x, hx, hxk, hxl⟩, hrest⟩ := h'
    obtain ⟨Lr', hLr', hlink'⟩ := chain_lists L₂ hL₂ r' hrest
    refine ⟨(a, x) :: Lr', ?_, fun z hz => ?_⟩
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨by simp, hx.1, hxk, hxl⟩
      · obtain ⟨h1, h2⟩ := hLr' q hq
        exact ⟨by simp [h1], h2⟩
    · simp only [List.cons_append, linked_cons]
      exact ⟨hz, hlink' x hx.2⟩

end T1

/-- **Theorem 1** of [Xiang–Vaidya, PODC 2018] (necessity): if a deterministic metadata algorithm
implements replica-centric causal consistency, then for every edge `e_jk ∈ E_i` of the timestamp
graph of `i` and every quiescent reachable state `s₀`, replica `i` is not oblivious to updates on
`e_jk` after `s₀`. -/
theorem theorem_1 [Fintype ι] (hA : Implements X A) {i j k : ι} (he : TsEdge X i j k)
    {s₀ : St ι Reg M} (hs₀ : Reachable X A s₀) (hq : Quiescent X s₀) :
    ¬ Oblivious X A s₀ i j k := by
  intro hobl
  obtain ⟨hjk, hcase⟩ := he
  rcases hcase with rfl | rfl | ⟨l, r, hloop⟩
  · exact T1.case1 hA hjk hs₀ hq hobl
  · exact T1.case2 hA hjk hs₀ hq hobl
  · obtain ⟨hnd, hadj, ⟨w0, hw0, hw0l⟩, ⟨w1, hw1, hw1l⟩, hiii⟩ := hloop
    -- distinctness of the replicas of the loop
    have hnd1 := List.nodup_cons.1 hnd
    have hil : i ∉ l := fun h => hnd1.1 (by simp [h])
    have hik : i ≠ k := fun h => hnd1.1 (by simp [h])
    have hij : i ≠ j := fun h => hnd1.1 (by simp [h])
    have hir : i ∉ r := fun h => hnd1.1 (by simp [h])
    have hnd2 := List.nodup_append.1 hnd1.2
    have hdisj : ∀ a ∈ l, ∀ b ∈ k :: j :: r, a ≠ b := by
      rintro a ha b hb rfl
      exact List.disjoint_of_nodup_append hnd1.2 ha hb
    have hkl : k ∉ l := fun h => hdisj k h k (by simp) rfl
    have hjl : j ∉ l := fun h => hdisj j h j (by simp) rfl
    have hrl : ∀ a ∈ r, a ∉ l := fun a ha h => hdisj a h a (by simp [ha]) rfl
    have hnd3 := List.nodup_cons.1 hnd2.2.1
    have hkr : k ∉ r := fun h => hnd3.1 (by simp [h])
    -- the path phase
    have hpath : List.IsChain (Adj X) (i :: l ++ [k]) := by
      have e : i :: (l ++ k :: j :: r) ++ [i] = (i :: l ++ [k]) ++ (j :: (r ++ [i])) := by simp
      rw [e] at hadj
      exact hadj.left_of_append
    obtain ⟨y₀, Lr, La, pf, xf, hy₀, hLr, hsplit, hLa, hxf, hlinkr⟩ := T1.path_lists l i hpath
    -- the chain phase
    obtain ⟨Lc, hLc, hlinkc⟩ := T1.chain_lists (X := X) (k := k) (l := l) ((i, y₀) :: Lr)
      (fun z hz => ⟨hz, hlinkr⟩) r hiii
    have hLc' : ∀ q ∈ Lc, q.2 ∈ X q.1 ∧ q.2 ∉ X k ∧ (∀ p ∈ l, q.2 ∉ X p) ∧ q.1 ≠ i ∧ q.1 ≠ k ∧
        q.1 ∉ l := by
      intro q hq
      obtain ⟨h1, h2, h3, h4⟩ := hLc q hq
      exact ⟨h2, h3, h4, fun h => hir (h ▸ h1), fun h => hkr (h ▸ h1), hrl _ h1⟩
    by_cases h31 : ∃ x ∈ X j ∩ X (r.headD i), x ∉ X k ∧ ∀ p ∈ l, x ∉ X p
    · -- 3.1: `u_A, u_B` on `w₀ ∈ X_jk`, then `j` writes `x ∈ X_{j r₂}` (not stored at `k`)
      obtain ⟨x, hx, hxk, hxl⟩ := h31
      refine T1.case3 hA hs₀ hq hobl hjk.1 hik hij hil hkl hjl hw0.1 hw0.2 hw0l ((j, x) :: Lc)
        ?_ hy₀ Lr hLr La pf xf hsplit hLa hxf ?_
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨hx.1, hxk, hxl, Ne.symm hij, hjk.1, hjl⟩
        · exact hLc' q hq
      · simp only [List.cons_append, T1.linked_cons]
        exact ⟨hw0.1, hlinkc x hx.2⟩
    · -- 3.2: `u_A, u_B` on `w₁ ∈ X_{j r₂}`, which is then stored at `k` too
      have hw1k : w1 ∈ X k := by
        by_contra h
        exact h31 ⟨w1, hw1, h, hw1l⟩
      exact T1.case3 hA hs₀ hq hobl hjk.1 hik hij hil hkl hjl hw1.1 hw1k hw1l Lc hLc' hy₀ Lr hLr
        La pf xf hsplit hLa hxf (hlinkc w1 hw1.2)

end Podc.PartialReplicationCausal.Necessity
