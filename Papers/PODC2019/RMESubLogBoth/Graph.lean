import Papers.PODC2019.RMESubLogBoth.Model

/-!
# Maximal paths in graphs with in- and out-degree at most one

Lemmas about `IsMaxPath` (lines 39–48 of the algorithm): a vertex lies on at most one maximal path,
maximal paths are closed under edges, and in a finite acyclic graph every vertex lies on a maximal
path.
-/

namespace Podc.RMESubLogBoth

open Relation

/-- The edge relation of a scanned graph. -/
def EdgeR (E : Finset (ℕ × ℕ)) (a b : ℕ) : Prop := (a, b) ∈ E

variable {V : Finset ℕ} {E : Finset (ℕ × ℕ)}

/-- Out-degree at most one. -/
def OutDeg1 (E : Finset (ℕ × ℕ)) : Prop := ∀ u v v', (u, v) ∈ E → (u, v') ∈ E → v = v'

/-- In-degree at most one. -/
def InDeg1 (E : Finset (ℕ × ℕ)) : Prop := ∀ u u' v, (u, v) ∈ E → (u', v) ∈ E → u = u'

lemma isChain_rtg_head {l : List ℕ} {a : ℕ} (h : (a :: l).IsChain (EdgeR E)) :
    ∀ u ∈ a :: l, ReflTransGen (EdgeR E) a u := by
  induction l generalizing a with
  | nil => intro u hu; simp at hu; subst hu; exact .refl
  | cons b l ih =>
    rw [List.isChain_cons_cons] at h
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact .refl
    · exact .head h.1 (ih h.2 u hu)

lemma isChain_rtg_last {l : List ℕ} (h : l.IsChain (EdgeR E)) (hne : l ≠ []) :
    ∀ u ∈ l, ReflTransGen (EdgeR E) u (l.getLastD 0) := by
  induction l with
  | nil => simp at hne
  | cons a l ih =>
    intro u hu
    cases l with
    | nil => simp at hu; subst hu; exact .refl
    | cons b l =>
      rw [List.isChain_cons_cons] at h
      have ih' := ih h.2 (by simp)
      have hl : (a :: b :: l).getLastD 0 = (b :: l).getLastD 0 := by
        simp [List.getLastD_eq_getLast?, List.getLast?_cons_cons]
      rw [hl]
      rcases List.mem_cons.mp hu with rfl | hu
      · exact .head h.1 (ih' b (by simp))
      · exact ih' u hu

/-- Every vertex of a path is reachable from its start. -/
lemma IsPath.rtg_start {σ : List ℕ} (h : IsPath V E σ) :
    ∀ u ∈ σ, ReflTransGen (EdgeR E) (pstart σ) u := by
  obtain ⟨hne, -, hc⟩ := h
  cases σ with
  | nil => simp at hne
  | cons a l => exact isChain_rtg_head hc

/-- The end of a path is reachable from each of its vertices. -/
lemma IsPath.rtg_end {σ : List ℕ} (h : IsPath V E σ) :
    ∀ u ∈ σ, ReflTransGen (EdgeR E) u (pend σ) :=
  isChain_rtg_last h.2.2 h.1

lemma pstart_mem {σ : List ℕ} (h : σ ≠ []) : pstart σ ∈ σ := by
  cases σ with
  | nil => simp at h
  | cons a l => simp [pstart]

lemma pend_mem {σ : List ℕ} (h : σ ≠ []) : pend σ ∈ σ := by
  rw [pend, List.getLastD_eq_getLast?, List.getLast?_eq_getLast h]
  exact List.getLast_mem h

/-- Paths with the same start that end in sinks coincide (out-degree ≤ 1). -/
lemma path_eq_of_start (hout : OutDeg1 E) :
    ∀ {σ τ : List ℕ}, σ ≠ [] → σ.IsChain (EdgeR E) → (∀ w, (σ.getLastD 0, w) ∉ E) →
      τ ≠ [] → τ.IsChain (EdgeR E) → (∀ w, (τ.getLastD 0, w) ∉ E) →
      σ.headD 0 = τ.headD 0 → σ = τ
  | [], _, h, _, _, _, _, _, _ => absurd rfl h
  | _, [], _, _, _, h, _, _, _ => absurd rfl h
  | [a], [b], _, _, _, _, _, _, hh => by simp at hh; subst hh; rfl
  | [a], b :: b' :: τ, _, _, hσe, _, hτ, _, hh => by
      simp at hh; subst hh
      rw [List.isChain_cons_cons] at hτ
      exact absurd hτ.1 (by simpa using hσe b' : (a, b') ∉ E)
  | a :: a' :: σ, [b], _, hσ, _, _, _, hτe, hh => by
      simp at hh; subst hh
      rw [List.isChain_cons_cons] at hσ
      exact absurd hσ.1 (by simpa using hτe a' : (a, a') ∉ E)
  | a :: a' :: σ, b :: b' :: τ, _, hσ, hσe, _, hτ, hτe, hh => by
      simp at hh; subst hh
      rw [List.isChain_cons_cons] at hσ hτ
      have : a' = b' := hout _ _ _ hσ.1 hτ.1
      subst this
      have := path_eq_of_start hout (σ := a' :: σ) (τ := a' :: τ) (by simp) hσ.2
        (by simpa [List.getLastD_eq_getLast?, List.getLast?_cons_cons] using hσe) (by simp) hτ.2
        (by simpa [List.getLastD_eq_getLast?, List.getLast?_cons_cons] using hτe) rfl
      rw [this]

/-- Two sources reaching the same vertex coincide (in-degree ≤ 1). -/
lemma source_eq (hin : InDeg1 E) {s v : ℕ} (h : ReflTransGen (EdgeR E) s v) :
    ∀ {s'}, ReflTransGen (EdgeR E) s' v → (∀ u, (u, s) ∉ E) → (∀ u, (u, s') ∉ E) → s = s' := by
  induction h with
  | refl =>
    intro s' h' hs _
    rcases ReflTransGen.cases_tail h' with h | ⟨c, -, hc⟩
    · exact h
    · exact absurd hc (hs c)
  | tail h1 e ih =>
    intro s' h' hs hs'
    rcases ReflTransGen.cases_tail h' with h | ⟨c, hc1, hc⟩
    · subst h; exact absurd e (hs' _)
    · have := hin _ _ _ e hc
      subst this
      exact ih hc1 hs hs'

/-- A vertex lies on at most one maximal path. -/
lemma maxPath_unique (hout : OutDeg1 E) (hin : InDeg1 E) {σ τ : List ℕ} (hσ : IsMaxPath V E σ)
    (hτ : IsMaxPath V E τ) {v : ℕ} (hvσ : v ∈ σ) (hvτ : v ∈ τ) : σ = τ := by
  have hs : pstart σ = pstart τ :=
    source_eq hin (hσ.1.rtg_start v hvσ) (hτ.1.rtg_start v hvτ) hσ.2.1 hτ.2.1
  exact path_eq_of_start hout hσ.1.1 hσ.1.2.2 hσ.2.2 hτ.1.1 hτ.1.2.2 hτ.2.2 hs

lemma chain_succ {R : ℕ → ℕ → Prop} : ∀ {σ : List ℕ}, σ.IsChain R → ∀ {v}, v ∈ σ →
    v ≠ σ.getLastD 0 → ∃ w ∈ σ, R v w
  | [], _, _, hv, _ => by simp at hv
  | [a], _, _, hv, hl => by simp at hv; subst hv; simp at hl
  | a :: b :: l, h, v, hv, hl => by
      rw [List.isChain_cons_cons] at h
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨b, by simp, h.1⟩
      · obtain ⟨w, hw, hr⟩ := chain_succ h.2 hv
          (by simpa [List.getLastD_eq_getLast?, List.getLast?_cons_cons] using hl)
        exact ⟨w, List.mem_cons_of_mem _ hw, hr⟩

lemma chain_pred {R : ℕ → ℕ → Prop} : ∀ {σ : List ℕ}, σ.IsChain R → ∀ {v}, v ∈ σ →
    v ≠ σ.headD 0 → ∃ w ∈ σ, R w v
  | [], _, _, hv, _ => by simp at hv
  | [a], _, _, hv, hl => by simp at hv; subst hv; simp at hl
  | a :: b :: l, h, v, hv, hl => by
      rw [List.isChain_cons_cons] at h
      rcases List.mem_cons.mp hv with rfl | hv
      · simp at hl
      · by_cases hvb : v = b
        · subst hvb; exact ⟨a, by simp, h.1⟩
        · obtain ⟨w, hw, hr⟩ := chain_pred h.2 hv (by simpa using hvb)
          exact ⟨w, List.mem_cons_of_mem _ hw, hr⟩

/-- Membership in a maximal path along an edge (forward). -/
lemma IsMaxPath.mem_succ (hout : OutDeg1 E) {σ : List ℕ} (hσ : IsMaxPath V E σ) {u v : ℕ}
    (hu : u ∈ σ) (huv : (u, v) ∈ E) : v ∈ σ := by
  by_cases hl : u = σ.getLastD 0
  · subst hl; exact absurd huv (hσ.2.2 v)
  · obtain ⟨w, hw, hr⟩ := chain_succ hσ.1.2.2 hu hl
    have := hout _ _ _ huv hr; subst this; exact hw

/-- Membership in a maximal path along an edge (backward). -/
lemma IsMaxPath.mem_pred (hin : InDeg1 E) {σ : List ℕ} (hσ : IsMaxPath V E σ) {u v : ℕ}
    (hv : v ∈ σ) (huv : (u, v) ∈ E) : u ∈ σ := by
  by_cases hl : v = σ.headD 0
  · subst hl; exact absurd huv (hσ.2.1 u)
  · obtain ⟨w, hw, hr⟩ := chain_pred hσ.1.2.2 hv hl
    have := hin _ _ _ huv hr; subst this; exact hw

/-- Membership in a maximal path is closed under reachability. -/
lemma IsMaxPath.mem_rtg (hout : OutDeg1 E) {σ : List ℕ} (hσ : IsMaxPath V E σ) {u v : ℕ}
    (hu : u ∈ σ) (h : ReflTransGen (EdgeR E) u v) : v ∈ σ := by
  induction h with
  | refl => exact hu
  | tail _ e ih => exact hσ.mem_succ hout ih e

/-- A sink on a maximal path is its end. -/
lemma IsMaxPath.eq_pend_of_sink {σ : List ℕ} (hσ : IsMaxPath V E σ) {u : ℕ} (hu : u ∈ σ)
    (hs : ∀ w, (u, w) ∉ E) : u = pend σ := by
  by_contra hl
  obtain ⟨w, -, hr⟩ := chain_succ hσ.1.2.2 hu hl
  exact hs w hr

/-- A source on a maximal path is its start. -/
lemma IsMaxPath.eq_pstart_of_source {σ : List ℕ} (hσ : IsMaxPath V E σ) {u : ℕ} (hu : u ∈ σ)
    (hs : ∀ w, (w, u) ∉ E) : u = pstart σ := by
  by_contra hl
  obtain ⟨w, -, hr⟩ := chain_pred hσ.1.2.2 hu hl
  exact hs w hr

lemma wf_of_acyc (hEV : ∀ u v, (u, v) ∈ E → u ∈ V ∧ v ∈ V)
    (hacyc : ∀ u, ¬ TransGen (EdgeR E) u u) (R : ℕ → ℕ → Prop)
    (hR : R = (fun a b => TransGen (EdgeR E) b a) ∨ R = TransGen (EdgeR E)) : WellFounded R := by
  let S := {x // x ∈ V}
  have htr : ∀ a b, R a b → a ∈ V ∧ b ∈ V := by
    intro a b h
    rcases hR with rfl | rfl
    · exact ⟨(TransGen.tail'_iff.mp h).choose_spec.2 |> fun e => (hEV _ _ e).2,
        (TransGen.head'_iff.mp h).choose_spec.1 |> fun e => (hEV _ _ e).1⟩
    · exact ⟨(TransGen.head'_iff.mp h).choose_spec.1 |> fun e => (hEV _ _ e).1,
        (TransGen.tail'_iff.mp h).choose_spec.2 |> fun e => (hEV _ _ e).2⟩
  let r' : S → S → Prop := fun a b => R a.1 b.1
  have : IsTrans S r' := ⟨fun a b c hab hbc => by
    rcases hR with rfl | rfl
    · exact TransGen.trans hbc hab
    · exact TransGen.trans hab hbc⟩
  have : Std.Irrefl r' := ⟨fun a h => by
    rcases hR with rfl | rfl
    · exact hacyc _ h
    · exact hacyc _ h⟩
  have hwf : WellFounded r' := Finite.wellFounded_of_trans_of_irrefl r'
  refine ⟨fun x => ?_⟩
  by_cases hx : x ∈ V
  · have hacc := hwf.apply ⟨x, hx⟩
    suffices ∀ a : S, Acc r' a → Acc R a.1 from this _ hacc
    intro a ha
    induction ha with
    | intro a _ ih =>
      exact Acc.intro _ (fun y hy => ih ⟨y, (htr _ _ hy).1⟩ hy)
  · exact Acc.intro _ (fun y hy => absurd (htr _ _ hy).2 hx)

/-- In a finite acyclic graph every vertex lies on a maximal path. -/
lemma exists_maxPath (hEV : ∀ u v, (u, v) ∈ E → u ∈ V ∧ v ∈ V)
    (hacyc : ∀ u, ¬ TransGen (EdgeR E) u u) {v : ℕ} (hv : v ∈ V) :
    ∃ σ, IsMaxPath V E σ ∧ v ∈ σ := by
  -- forward part
  have hfw : ∀ a, a ∈ V → ∃ l : List ℕ, (a :: l).IsChain (EdgeR E) ∧ (∀ u ∈ a :: l, u ∈ V) ∧
      ∀ w, ((a :: l).getLastD 0, w) ∉ E := by
    intro a
    induction a using (wf_of_acyc hEV hacyc _ (.inl rfl)).induction with
    | _ a ih =>
      intro ha
      by_cases hs : ∃ w, (a, w) ∈ E
      · obtain ⟨w, hw⟩ := hs
        obtain ⟨l, hl1, hl2, hl3⟩ := ih w (TransGen.single hw) (hEV _ _ hw).2
        refine ⟨w :: l, ?_, ?_, ?_⟩
        · exact List.IsChain.cons hl1 (fun y hy => by simp at hy; subst hy; exact hw)
        · intro u hu; rcases List.mem_cons.mp hu with rfl | hu
          · exact ha
          · exact hl2 u hu
        · simpa [List.getLastD_eq_getLast?, List.getLast?_cons_cons] using hl3
      · push_neg at hs
        exact ⟨[], by simp, by simpa using ha, by simpa using hs⟩
  -- backward part
  have hbw : ∀ a, a ∈ V → ∃ l : List ℕ, (l ++ [a]).IsChain (EdgeR E) ∧
      (∀ u ∈ l ++ [a], u ∈ V) ∧ ∀ w, (w, (l ++ [a]).headD 0) ∉ E := by
    intro a
    induction a using (wf_of_acyc hEV hacyc _ (.inr rfl)).induction with
    | _ a ih =>
      intro ha
      by_cases hs : ∃ w, (w, a) ∈ E
      · obtain ⟨w, hw⟩ := hs
        obtain ⟨l, hl1, hl2, hl3⟩ := ih w (TransGen.single hw) (hEV _ _ hw).1
        refine ⟨l ++ [w], ?_, ?_, ?_⟩
        · exact List.IsChain.append hl1 (List.isChain_singleton a) (by
            intro x hx y hy; simp at hx hy; subst hx hy; exact hw)
        · intro u hu
          rcases List.mem_append.mp hu with hu | hu
          · exact hl2 u hu
          · simp at hu; subst hu; exact ha
        · cases l with
          | nil => simpa using hl3
          | cons b l => simpa using hl3
      · push_neg at hs
        exact ⟨[], by simp, by simpa using ha, by simpa using hs⟩
  obtain ⟨l1, h11, h12, h13⟩ := hbw v hv
  obtain ⟨l2, h21, h22, h23⟩ := hfw v hv
  refine ⟨l1 ++ v :: l2, ⟨⟨by simp, ?_, ?_⟩, ?_, ?_⟩, by simp⟩
  · intro u hu; simp at hu; rcases hu with hu | rfl | hu
    · exact h12 u (by simp [hu])
    · exact hv
    · exact h22 u (by simp [hu])
  · have : l1 ++ v :: l2 = (l1 ++ [v]) ++ l2 := by simp
    rw [this]
    exact List.IsChain.append h11 (List.IsChain.tail h21) (by
      intro x hx y hy
      rw [List.getLast?_append] at hx; simp at hx; subst hx
      cases l2 with
      | nil => simp at hy
      | cons b l2 => simp at hy; subst hy; exact (List.isChain_cons_cons.mp h21).1)
  · intro u; cases l1 with
    | nil => simpa using h13 u
    | cons b l1 => simpa using h13 u
  · intro w
    have : (l1 ++ v :: l2).getLastD 0 = (v :: l2).getLastD 0 := by
      simp only [List.getLastD_eq_getLast?]
      rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rw [this]; exact h23 w

end Podc.RMESubLogBoth
