import Papers.PODC2020.DetectableSpace.Lin

/-!
# More tools for building durable detectable linearizations incrementally

General lemmas (not specific to Algorithm 2; candidates for `Lin.lean`):

* `linResp O σ L a`: the response of operation instance `a` in the sequential execution of `L`
  from `σ` (`none` if `a ∉ L`), with `linResp_append`, `linResp_of_split`;
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

/-- The response of operation instance `a` in the sequential execution of `L` from `σ`
(first occurrence; `none` if `a` does not occur). -/
def linResp (O : ObjSpec) : O.State → List (ℕ × O.Op) → ℕ → Option O.Resp
  | _, [], _ => none
  | σ, x :: L, a => if x.1 = a then some (O.δ σ x.2).2 else linResp O (O.δ σ x.2).1 L a

@[simp] lemma linResp_nil (σ : O.State) (a : ℕ) : linResp O σ [] a = none := rfl

lemma linResp_cons (σ : O.State) (x : ℕ × O.Op) (L : List (ℕ × O.Op)) (a : ℕ) :
    linResp O σ (x :: L) a =
      if x.1 = a then some (O.δ σ x.2).2 else linResp O (O.δ σ x.2).1 L a := rfl

lemma linResp_cons_of_ne (σ : O.State) (x : ℕ × O.Op) (L : List (ℕ × O.Op)) (a : ℕ)
    (h : x.1 ≠ a) : linResp O σ (x :: L) a = linResp O (O.δ σ x.2).1 L a := by
  simp [linResp_cons, h]

lemma linResp_isSome (σ : O.State) (L : List (ℕ × O.Op)) (a : ℕ) :
    (linResp O σ L a).isSome ↔ a ∈ L.map Prod.fst := by
  induction L generalizing σ with
  | nil => simp
  | cons x L ih =>
    rw [linResp_cons]
    by_cases h : x.1 = a
    · simp [h]
    · simp only [h, ite_false, ih, List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h' | h')
        · exact absurd h'.symm h
        · exact h'

lemma linResp_eq_none (σ : O.State) (L : List (ℕ × O.Op)) (a : ℕ) :
    linResp O σ L a = none ↔ a ∉ L.map Prod.fst := by
  rw [← linResp_isSome (O := O) σ]; simp

lemma linResp_append (σ : O.State) (L M : List (ℕ × O.Op)) (a : ℕ) :
    linResp O σ (L ++ M) a =
      (linResp O σ L a).or (linResp O (O.runOps σ (L.map Prod.snd)) M a) := by
  induction L generalizing σ with
  | nil => simp
  | cons x L ih =>
    simp only [List.cons_append, linResp_cons, List.map_cons, ObjSpec.runOps_cons]
    split_ifs
    · simp
    · exact ih _

lemma linResp_append_of_mem (σ : O.State) (L M : List (ℕ × O.Op)) (a : ℕ)
    (h : a ∈ L.map Prod.fst) : linResp O σ (L ++ M) a = linResp O σ L a := by
  rw [linResp_append]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((linResp_isSome σ L a).2 h)
  simp [hr]

lemma linResp_append_of_not_mem (σ : O.State) (L M : List (ℕ × O.Op)) (a : ℕ)
    (h : a ∉ L.map Prod.fst) :
    linResp O σ (L ++ M) a = linResp O (O.runOps σ (L.map Prod.snd)) M a := by
  rw [linResp_append, (linResp_eq_none σ L a).2 h]; simp

lemma linResp_singleton (σ : O.State) (b : ℕ) (o : O.Op) (a : ℕ) :
    linResp O σ [(b, o)] a = if b = a then some (O.δ σ o).2 else none := by
  simp [linResp_cons]

lemma linResp_of_split {σ : O.State} {L L₁ L₂ : List (ℕ × O.Op)} {a : ℕ} {o : O.Op}
    (hnd : (L.map Prod.fst).Nodup) (hL : L = L₁ ++ (a, o) :: L₂) :
    linResp O σ L a = some (O.δ (O.runOps σ (L₁.map Prod.snd)) o).2 := by
  subst hL
  have ha : a ∉ L₁.map Prod.fst := by
    simp only [List.map_append, List.map_cons] at hnd
    exact fun h => (List.nodup_append.1 hnd).2.2 _ h _ (by simp) rfl
  rw [linResp_append_of_not_mem _ _ _ _ ha, linResp_cons]; simp

/-- Responding with the response given by `linResp` (for `DLin.append_res`). -/
lemma hresp_of_linResp {σ : O.State} {L : List (ℕ × O.Op)} {a : ℕ} {r : Option O.Resp}
    (hnd : (L.map Prod.fst).Nodup) (hr : ∀ r', r = some r' → linResp O σ L a = some r') :
    ∀ r', r = some r' → ∀ L₁ o L₂, L = L₁ ++ (a, o) :: L₂ →
      r' = (O.δ (O.runOps σ (L₁.map Prod.snd)) o).2 := by
  intro r' hr' L₁ o L₂ hL
  have := (hr r' hr').symm.trans (linResp_of_split hnd hL)
  exact Option.some.inj this

/-! ### Removing state-preserving pending entries -/

/-- Removing entries (selected by `f a = false` on their identifiers) whose operation does not
change the state at their position preserves the final state, the responses of the remaining
entries and legality. -/
theorem filter_pres (h : List (HEv P O.Op O.Resp)) (f : ℕ → Bool) :
    ∀ (σ : O.State) (L : List (ℕ × O.Op)), (L.map Prod.fst).Nodup →
      (∀ x ∈ L, f x.1 = false → ∀ r, linResp O σ L x.1 = some r →
        ∀ τ, (O.δ τ x.2).2 = r → (O.δ τ x.2).1 = τ) →
      O.runOps σ ((L.filter (fun x => f x.1)).map Prod.snd) = O.runOps σ (L.map Prod.snd) ∧
      (∀ a, f a = true → linResp O σ (L.filter (fun x => f x.1)) a = linResp O σ L a) ∧
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
    have hpres' : ∀ y ∈ L, f y.1 = false → ∀ r, linResp O (O.δ σ o).1 L y.1 = some r →
        ∀ τ, (O.δ τ y.2).2 = r → (O.δ τ y.2).1 = τ := by
      intro y hy hf r hr
      exact hpres y (by simp [hy]) hf r (by rw [linResp_cons_of_ne _ _ _ _ (hne y hy)]; exact hr)
    by_cases hfb : f b = true
    · have e : (List.filter (fun x => f x.1) ((b, o) :: L)) =
          (b, o) :: L.filter (fun x => f x.1) := by simp [hfb]
      obtain ⟨h1, h2, h3⟩ := ih (O.δ σ o).1 hnd' hpres'
      rw [e]
      refine ⟨by simpa using h1, ?_, ?_⟩
      · intro a ha
        simp only [linResp_cons]
        split_ifs
        · rfl
        · exact h2 a ha
      · intro hl
        exact ⟨hl.1, h3 hl.2⟩
    · have hfb' : f b = false := by simpa using hfb
      have e : (List.filter (fun x => f x.1) ((b, o) :: L)) = L.filter (fun x => f x.1) := by
        simp [hfb']
      have hst : (O.δ σ o).1 = σ :=
        hpres (b, o) (by simp) hfb' _ (by simp [linResp_cons]) σ rfl
      obtain ⟨h1, h2, h3⟩ := ih (O.δ σ o).1 hnd' hpres'
      rw [hst] at h1 h2 h3
      rw [e]
      refine ⟨by simpa [hst] using h1, ?_, ?_⟩
      · intro a ha
        have hba : b ≠ a := by rintro rfl; rw [hfb'] at ha; exact absurd ha (by simp)
        rw [linResp_cons_of_ne _ _ _ _ hba, hst]
        exact h2 a ha
      · intro hl
        have := hl.2
        rw [hst] at this
        exact h3 this

/-- Removing pending, state-preserving entries preserves a durable detectable linearization. -/
theorem DLin.filter {h : List (HEv P O.Op O.Resp)} {σ : O.State} {L : List (ℕ × O.Op)}
    (hd : DLin O h σ L) (f : ℕ → Bool)
    (hpend : ∀ x ∈ L, f x.1 = false → ∀ r c, HEv.res x.1 r c ∉ h)
    (hpres : ∀ x ∈ L, f x.1 = false → ∀ r, linResp O σ L x.1 = some r →
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
