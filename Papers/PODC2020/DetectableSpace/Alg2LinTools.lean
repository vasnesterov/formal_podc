import Papers.PODC2020.DetectableSpace.Lin
import Podc.SharedMemory.LinResp

/-!
# More tools for building durable detectable linearizations incrementally

General lemmas (not specific to Algorithm 2; candidates for `Lin.lean`):

* `hresp_of_respIn`: responding with the response `O.respIn σ L a` that the linearization `L`
  assigns to `a` (responses in sequential histories are the library's `ObjSpec.respIn`);
* `DLin.filter`: removing *pending* entries whose operation does not change the state (at its
  position in `L`) preserves a linearization, the final state and the responses of the other
  entries (`filter_pres`);
* `DLin.append_pending`: appending a list of pending operations;
* `exists_list_of_bounded`: a list enumerating a bounded set of operation instances.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

variable {P : Type} {O : ObjSpec}

/-- Responding with the response given by `ObjSpec.respIn` (for `DLin.append_res`). -/
lemma hresp_of_respIn {σ : O.State} {L : List (ℕ × O.Op)} {a : ℕ} {r : Option O.Resp}
    (hnd : (L.map Prod.fst).Nodup) (hr : ∀ r', r = some r' → O.respIn σ L a = some r') :
    ∀ r', r = some r' → ∀ L₁ o L₂, L = L₁ ++ (a, o) :: L₂ →
      r' = (O.δ (O.runOps σ (L₁.map Prod.snd)) o).2 := by
  intro r' hr' L₁ o L₂ hL
  have := (hr r' hr').symm.trans (ObjSpec.respIn_of_split hnd hL)
  exact Option.some.inj this

/-! ### Removing state-preserving pending entries -/

/-- Removing entries (selected by `f a = false` on their identifiers) whose operation does not
change the state at their position preserves the final state, the responses of the remaining
entries and legality. -/
theorem filter_pres (h : List (HEv P O.Op O.Resp)) (f : ℕ → Bool) :
    ∀ (σ : O.State) (L : List (ℕ × O.Op)), (L.map Prod.fst).Nodup →
      (∀ x ∈ L, f x.1 = false → ∀ r, O.respIn σ L x.1 = some r →
        ∀ τ, (O.δ τ x.2).2 = r → (O.δ τ x.2).1 = τ) →
      O.runOps σ ((L.filter (fun x => f x.1)).map Prod.snd) = O.runOps σ (L.map Prod.snd) ∧
      (∀ a, f a = true → O.respIn σ (L.filter (fun x => f x.1)) a = O.respIn σ L a) ∧
      (Legal O h σ L → Legal O h σ (L.filter (fun x => f x.1))) := by
  intro σ L
  induction L generalizing σ with
  | nil => intro _ _; simp
  | cons x L ih =>
    obtain ⟨b, o⟩ := x
    intro hnd hpres
    have hbL : b ∉ L.map Prod.fst := (List.nodup_cons.1 (by simpa using hnd)).1
    have hnd' : (L.map Prod.fst).Nodup := (List.nodup_cons.1 (by simpa using hnd)).2
    have hne : ∀ y ∈ L, b ≠ y.1 := fun y hy hb => hbL (hb ▸ List.mem_map_of_mem hy)
    have hpres' : ∀ y ∈ L, f y.1 = false → ∀ r, O.respIn (O.δ σ o).1 L y.1 = some r →
        ∀ τ, (O.δ τ y.2).2 = r → (O.δ τ y.2).1 = τ := by
      intro y hy hf r hr
      exact hpres y (by simp [hy]) hf r (by rw [ObjSpec.respIn_cons_of_ne _ _ _ (hne y hy)]; exact hr)
    by_cases hfb : f b = true
    · have e : (List.filter (fun x => f x.1) ((b, o) :: L)) =
          (b, o) :: L.filter (fun x => f x.1) := by simp [hfb]
      obtain ⟨h1, h2, h3⟩ := ih (O.δ σ o).1 hnd' hpres'
      rw [e]
      refine ⟨by simpa using h1, ?_, ?_⟩
      · intro a ha
        simp only [ObjSpec.respIn_cons]
        split_ifs
        · rfl
        · exact h2 a ha
      · intro hl
        exact ⟨hl.1, h3 hl.2⟩
    · have hfb' : f b = false := by simpa using hfb
      have e : (List.filter (fun x => f x.1) ((b, o) :: L)) = L.filter (fun x => f x.1) := by
        simp [hfb']
      have hst : (O.δ σ o).1 = σ :=
        hpres (b, o) (by simp) hfb' _ (by simp) σ rfl
      obtain ⟨h1, h2, h3⟩ := ih (O.δ σ o).1 hnd' hpres'
      rw [hst] at h1 h2 h3
      rw [e]
      refine ⟨by simpa [hst] using h1, ?_, ?_⟩
      · intro a ha
        have hba : b ≠ a := by rintro rfl; rw [hfb'] at ha; exact absurd ha (by simp)
        rw [ObjSpec.respIn_cons_of_ne _ _ _ hba, hst]
        exact h2 a ha
      · intro hl
        have := hl.2
        rw [hst] at this
        exact h3 this

/-- Removing pending, state-preserving entries preserves a durable detectable linearization. -/
theorem DLin.filter {h : List (HEv P O.Op O.Resp)} {σ : O.State} {L : List (ℕ × O.Op)}
    (hd : DLin O h σ L) (f : ℕ → Bool)
    (hpend : ∀ x ∈ L, f x.1 = false → ∀ r c, HEv.res x.1 r c ∉ h)
    (hpres : ∀ x ∈ L, f x.1 = false → ∀ r, O.respIn σ L x.1 = some r →
      ∀ τ, (O.δ τ x.2).2 = r → (O.δ τ x.2).1 = τ) :
    DLin O h σ (L.filter (fun x => f x.1)) where
  nodup := ((List.filter_sublist (l := L)).map Prod.fst).nodup hd.nodup
  inv_of_mem x hx := hd.inv_of_mem x (List.mem_of_mem_filter hx)
  mem_of_res a r c ha := by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hd.mem_of_res a r c ha)
    refine List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, ?_⟩, rfl⟩
    by_contra hf
    exact hpend x hx (by simpa using hf) _ c ha
  not_mem_of_fail a c ha hm :=
    hd.not_mem_of_fail a c ha (((List.filter_sublist (l := L)).map Prod.fst).subset hm)
  rt := hd.rt.sublist (List.filter_sublist (l := L))
  legal := (filter_pres h f σ L hd.nodup hpres).2.2 hd.legal

/-! ### Appending pending operations -/

theorem DLin.append_pending {h : List (HEv P O.Op O.Resp)} {σ : O.State} :
    ∀ (M L : List (ℕ × O.Op)), DLin O h σ L → ((L ++ M).map Prod.fst).Nodup →
      (∀ x ∈ M, ∃ p, HEv.inv x.1 p x.2 ∈ h) → (∀ x ∈ M, ∀ r c, HEv.res x.1 r c ∉ h) →
      DLin O h σ (L ++ M) := by
  intro M
  induction M with
  | nil => intro L hd _ _ _; simpa using hd
  | cons x M ih =>
    intro L hd hnd hinv hnr
    have e : L ++ x :: M = (L ++ [x]) ++ M := by simp
    rw [e] at hnd ⊢
    obtain ⟨p, hp⟩ := hinv x (by simp)
    have hxL : x.1 ∉ L.map Prod.fst := by
      intro hx
      simp only [List.map_append, List.map_cons, List.map_nil] at hnd
      have := (List.nodup_append.1 hnd).1
      exact (List.nodup_append.1 this).2.2 _ hx _ (by simp) rfl
    have := hd.push x.1 p x.2 hp (hnr x (by simp)) hxL
    exact ih (L ++ [x]) this hnd (fun y hy => hinv y (by simp [hy]))
      (fun y hy => hnr y (by simp [hy]))

/-! ### Enumerating a bounded set of operation instances -/

theorem exists_list_of_bounded {α : Type} (Q : ℕ × α → Prop) (n : ℕ)
    (hb : ∀ x, Q x → x.1 < n) (hu : ∀ x y, Q x → Q y → x.1 = y.1 → x = y) :
    ∃ M : List (ℕ × α), (M.map Prod.fst).Nodup ∧ ∀ x, x ∈ M ↔ Q x := by
  classical
  have key : ∀ k, ∃ M : List (ℕ × α), (M.map Prod.fst).Nodup ∧ ∀ x, x ∈ M ↔ Q x ∧ x.1 < k := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp, by simp⟩
    | succ k ih =>
      obtain ⟨M, hnd, hM⟩ := ih
      by_cases hk : ∃ a, Q (k, a)
      · obtain ⟨a, ha⟩ := hk
        refine ⟨M ++ [(k, a)], ?_, ?_⟩
        · simp only [List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.2 ⟨hnd, by simp, ?_⟩
          intro y hy z hz
          simp only [List.mem_singleton] at hz
          subst hz
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          have := ((hM x).1 hx).2
          omega
        · intro x
          simp only [List.mem_append, List.mem_singleton, hM]
          constructor
          · rintro (⟨h1, h2⟩ | rfl)
            · exact ⟨h1, by omega⟩
            · exact ⟨ha, by simp⟩
          · rintro ⟨h1, h2⟩
            by_cases hxk : x.1 = k
            · right; exact hu x (k, a) h1 ha hxk
            · left; exact ⟨h1, by omega⟩
      · refine ⟨M, hnd, ?_⟩
        intro x
        rw [hM]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          by_contra hx
          have hxk : x.1 = k := by omega
          exact hk ⟨x.2, by rw [← hxk]; exact h1⟩
  obtain ⟨M, hnd, hM⟩ := key n
  exact ⟨M, hnd, fun x => (hM x).trans ⟨fun h => h.1, fun h => ⟨h, hb x h⟩⟩⟩

end Papers.PODC2020.DetectableSpace
