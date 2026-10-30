import Papers.PODC2011.RulesOfThumb.FLP

/-!
# Bivalent histories

* `exists_segment`: from a bivalent history, for every node `i`, a finite schedule segment that
  activates `i` (and only nonempty sets) leads to a bivalent history (two applications of the
  extension lemma `exists_bivalent_after`, for `e_i` and then for `W`).
* `exists_biv_hist`: two distinct stable states give a bivalent history (Lemma F.13 and its
  non-stationary / `k`-recall variants in Appendix F.7–F.8): histories at the same time step
  are connected by changing the actions of one node at a time, and two univalent histories that
  differ only in one node's actions have the same colour.
-/

namespace Podc.RulesOfThumb

open Filter Relation

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι]

/-- `τ` activates nonempty sets at the `m` time steps after `h`. -/
def IsSegment (h : Hist A) (τ : ℕ → Finset ι) (m : ℕ) : Prop :=
  ∀ t, h.time < t → t ≤ h.time + m → (τ t).Nonempty

namespace System

variable {F : System A}

/-- An act-and-tell path from a history with nothing pending is a finite schedule segment. -/
lemma segment_of_path {h : Hist A} {s : Hist A × Finset ι}
    (hp : ReflTransGen (fun s s' => ∃ e, F.ATStep e s s') (h, ∅) s) :
    ∃ τ m, IsSegment h τ m ∧ F.run h τ m = s.1 := by
  induction hp with
  | refl => exact ⟨fun _ => ∅, 0, fun t h1 h2 => by omega, rfl⟩
  | @tail s s' _ hst ih =>
    obtain ⟨τ, m, hseg, hrun⟩ := ih
    obtain ⟨e, hst⟩ := hst
    cases hst with
    | add j g P => exact ⟨τ, m, hseg, hrun⟩
    | fire g P hP =>
      refine ⟨fun t => if t = h.time + m + 1 then P else τ t, m + 1, fun t h1 h2 => ?_, ?_⟩
      · by_cases ht : t = h.time + m + 1
        · simp [ht, hP]
        · simp only [ht, if_false]; exact hseg t h1 (by omega)
      · have hg : g.time = h.time + m := by simp [← show F.run h τ m = g from hrun]
        rw [run_succ, F.run_congr (τ := τ) (fun t _ h2 => by simp; omega), hrun]
        simp [hg]

lemma avoid_none_path {s u : Hist A × Finset ι} (hp : ReflTransGen (F.Avoid none) s u) :
    u.1 = s.1 ∧ s.2 ⊆ u.2 := by
  induction hp with
  | refl => exact ⟨rfl, le_rfl⟩
  | @tail u v _ huv ih =>
    obtain ⟨e, he, hst⟩ := huv
    cases hst with
    | add j g P => exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩
    | fire g P hP => exact absurd rfl he

variable [Fintype ι] [Nonempty ι]

/-- From a bivalent history, for every node `i`, a finite segment activating `i` leads to a
bivalent history. -/
theorem exists_segment {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k)
    (hsi : F.SelfIndependent) (hconv : F.Convergent) {h : Hist A} (hb : F.Biv (h, ∅))
    (i : ι) : ∃ τ m, IsSegment h τ m ∧ (∃ t, h.time < t ∧ t ≤ h.time + m ∧ i ∈ τ t) ∧
      F.Biv (F.run h τ m, ∅) := by
  obtain ⟨u₁, s₂, hp₁, hst₁, hb₂⟩ := exists_bivalent_after hk hrec hsi hconv (some i) hb
  obtain ⟨u₂, s₃, hp₂, hst₂, hb₃⟩ := exists_bivalent_after hk hrec hsi hconv none hb₂
  cases hst₁ with
  | add _ g Q =>
  cases hst₂ with
  | fire g₂ Q₂ hQ₂ =>
  obtain ⟨hg, hsub⟩ := avoid_none_path hp₂
  simp only at hg hsub
  subst hg
  obtain ⟨τ, m, hseg, hrun⟩ :=
    segment_of_path (ReflTransGen.mono (p := fun s s' => ∃ e, F.ATStep e s s')
      (fun s s' (hs : F.Avoid _ s s') => ⟨hs.choose, hs.choose_spec.2⟩) _ _ hp₁)
  simp only at hrun
  refine ⟨fun t => if t = h.time + m + 1 then Q₂ else τ t, m + 1, fun t h1 h2 => ?_,
    ⟨h.time + m + 1, by omega, by omega, by simpa using hsub (Finset.mem_insert_self _ _)⟩, ?_⟩
  · by_cases ht : t = h.time + m + 1
    · simp [ht, hQ₂]
    · simp only [ht, if_false]; exact hseg t h1 (by omega)
  · have hg : g₂.time = h.time + m := by simp [← hrun]
    rw [run_succ, F.run_congr (τ := τ) (fun t _ h2 => by simp; omega), hrun]
    simpa [hg] using hb₃

end System

/-! ### Mixing two histories node by node -/

/-- The profile that takes the actions of the nodes in `S` from `b` and the others from `a`. -/
def mixP (S : Finset ι) (a b : Profile A) : Profile A := fun l => if l ∈ S then b l else a l

/-- The history that takes the actions of the nodes in `S` from `h'` and the others from `h`. -/
def mixH (S : Finset ι) (h h' : Hist A) : Hist A :=
  ⟨mixP S h.cur h'.cur, List.zipWith (mixP S) h.past h'.past⟩

lemma forall₂_zipWith {α β γ δ : Type*} (R : γ → δ → Prop) (f : α → β → γ) (g : α → β → δ)
    (hfg : ∀ a b, R (f a b) (g a b)) :
    ∀ (l₁ : List α) (l₂ : List β), List.Forall₂ R (List.zipWith f l₁ l₂) (List.zipWith g l₁ l₂)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, b :: l₂ => by
    simp only [List.zipWith_cons_cons]
    exact List.Forall₂.cons (hfg a b) (forall₂_zipWith R f g hfg l₁ l₂)

lemma zipWith_left {α β : Type*} : ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
    List.zipWith (fun a _ => a) l₁ l₂ = l₁
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by simp at h; simp [zipWith_left l₁ l₂ h]

lemma zipWith_right {α β : Type*} : ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
    List.zipWith (fun _ b => b) l₁ l₂ = l₂
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l₁, b :: l₂, h => by simp at h; simp [zipWith_right l₁ l₂ h]

lemma mixH_empty {h h' : Hist A} (ht : h.time = h'.time) : mixH ∅ h h' = h := by
  have : mixP (∅ : Finset ι) = fun (a b : Profile A) => a := by
    funext a b l; simp [mixP]
  simp only [mixH, this]
  rw [zipWith_left _ _ (by simpa [Hist.time] using ht)]

lemma mixH_univ [Fintype ι] {h h' : Hist A} (ht : h.time = h'.time) : mixH Finset.univ h h' = h' := by
  have : mixP (Finset.univ : Finset ι) = fun (_ b : Profile A) => b := by
    funext a b l; simp [mixP]
  simp only [mixH, this]
  rw [zipWith_right _ _ (by simpa [Hist.time] using ht)]

lemma othersEq_mixH (S : Finset ι) (j : ι) (h h' : Hist A) :
    OthersEq j (mixH S h h') (mixH (insert j S) h h') := by
  have hp : ∀ a b : Profile A, ∀ l, l ≠ j → mixP S a b l = mixP (insert j S) a b l := by
    intro a b l hl; simp [mixP, hl]
  unfold OthersEq Hist.toList mixH
  exact List.Forall₂.cons (hp _ _) (forall₂_zipWith _ _ _ hp _ _)

namespace System

variable {F : System A} [Fintype ι] [Nonempty ι]

/-- Two distinct stable states give a bivalent history. -/
theorem exists_biv_hist {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k)
    (hsi : F.SelfIndependent) (hconv : F.Convergent) {c d : Profile A} (hcd : c ≠ d)
    (hc : F.IsStableState c) (hd : F.IsStableState d) : ∃ h, F.Biv (h, ∅) := by
  obtain ⟨sc, σc, hσc, hfc, hcc⟩ := hc
  obtain ⟨sd, σd, hσd, hfd, hcd'⟩ := hd
  set T := max sc.time sd.time
  set hc' := F.run sc σc (T - sc.time)
  set hd' := F.run sd σd (T - sd.time)
  have htc : hc'.time = T := by simp [hc']; omega
  have htd : hd'.time = T := by simp [hd']; omega
  have memc : c ∈ F.lims hc' ∅ := mem_lims_run hσc hfc hcc _ (Finset.empty_subset _)
  have memd : d ∈ F.lims hd' ∅ := mem_lims_run hσd hfd hcd' _ (Finset.empty_subset _)
  by_contra H
  push Not at H
  simp only [Biv, col, not_not] at H
  have key : ∀ S : Finset ι, F.lims (mixH S hc' hd') ∅ = F.lims hc' ∅ := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [mixH_empty (htc.trans htd.symm)]
    | insert j S _ ih =>
      rw [← ih]
      exact subsingleton_eq_of_inter (H _) (H _)
        (Set.inter_comm _ _ ▸ lims_inter_nonempty hk hrec hsi hconv (othersEq_mixH S j hc' hd'))
  have := key Finset.univ
  rw [mixH_univ (htc.trans htd.symm)] at this
  rw [this] at memd
  exact hcd (H _ memc memd)

end System

end Podc.RulesOfThumb
