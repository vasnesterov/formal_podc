import Papers.PODC2023.LeaderTradeoffs.Model

-- CSLib candidate

/-!
# Extending and gluing partial port maps

* `augment`: add new links to a partial port map: every node `u` gets linked to all nodes of a
  prescribed set `R u` (a symmetric relation, disjoint from the existing links), and the new links
  use (at least) a prescribed set `N u` of free ports. This is the adversary's freedom to choose
  "the mapping of the unused ports adaptively" (Lemma 3.3 of the paper and its uses).
* `exists_isPortMap_extends`: every well-formed partial port map on `m + 1` nodes extends to a
  (total) port map.
* `glue`: isolated partial executions of disjoint node sets run in parallel
  ("combining the port mappings … in a natural way", proofs of Lemma 3.6 and Claim 1).
-/

open Classical Finset Function

namespace LeaderTradeoffs

variable {m : ℕ}

/-- One node's new links: an injective partial map from free ports onto `R`, covering `N`. -/
theorem exists_newPorts (F N : Finset (Fin m)) (R : Finset ℕ) (hNF : N ⊆ F)
    (hNR : N.card ≤ R.card) (hRF : R.card ≤ F.card) :
    ∃ q : Fin m → Option ℕ, (∀ j v, q j = some v → v ∈ R ∧ j ∈ F) ∧
      (∀ i j v, q i = some v → q j = some v → i = j) ∧ (∀ v ∈ R, ∃ j, q j = some v) ∧
      (∀ j ∈ N, (q j).isSome) := by
  obtain ⟨F', hNF', hF'F, hcard⟩ := Finset.exists_subsuperset_card_eq hNF hNR hRF
  have hc : Fintype.card F' = Fintype.card R := by simp [hcard]
  let e : F' ≃ R := Fintype.equivOfCardEq hc
  refine ⟨fun j => if h : j ∈ F' then some (e ⟨j, h⟩).1 else none, ?_, ?_, ?_, ?_⟩
  · intro j v hj
    by_cases h : j ∈ F'
    · simp only [h, dite_true, Option.some.injEq] at hj
      subst hj
      exact ⟨(e ⟨j, h⟩).2, hF'F h⟩
    · simp [h] at hj
  · intro i j v hi hj
    by_cases h1 : i ∈ F'
    · by_cases h2 : j ∈ F'
      · simp only [h1, h2, dite_true, Option.some.injEq] at hi hj
        rw [← hj] at hi
        have := e.injective (Subtype.ext hi)
        simpa using this
      · simp [h2] at hj
    · simp [h1] at hi
  · intro v hv
    refine ⟨(e.symm ⟨v, hv⟩).1, ?_⟩
    simp
  · intro j hj
    simp [hNF' hj]

/-- Adding new links to a partial port map. -/
theorem augment (p : PortMap m) (S : Finset ℕ) (hp : WF p S) (R : ℕ → Finset ℕ)
    (N : ℕ → Finset (Fin m))
    (hRS : ∀ u ∈ S, R u ⊆ S) (hRu : ∀ u ∈ S, u ∉ R u)
    (hRn : ∀ u ∈ S, ∀ v ∈ R u, ∀ j, p u j ≠ some v)
    (hRsymm : ∀ u ∈ S, ∀ v ∈ R u, u ∈ R v)
    (hN : ∀ u ∈ S, ∀ j ∈ N u, p u j = none)
    (hNR : ∀ u ∈ S, (N u).card ≤ (R u).card)
    (hRF : ∀ u ∈ S, (R u).card ≤ (freePorts p u).card) :
    ∃ p' : PortMap m, WF p' S ∧ (∀ u ∈ S, ∀ j v, p u j = some v → p' u j = some v) ∧
      (∀ u ∈ S, ∀ j v, p' u j = some v → p u j = some v ∨ v ∈ R u) ∧
      (∀ u ∈ S, ∀ v ∈ R u, ∃ j, p' u j = some v) ∧
      (∀ u ∈ S, ∀ j ∈ N u, (p' u j).isSome) := by
  have hex : ∀ u, ∃ q : Fin m → Option ℕ, u ∈ S →
      (∀ j v, q j = some v → v ∈ R u ∧ j ∈ freePorts p u) ∧
      (∀ i j v, q i = some v → q j = some v → i = j) ∧ (∀ v ∈ R u, ∃ j, q j = some v) ∧
      (∀ j ∈ N u, (q j).isSome) := by
    intro u
    by_cases hu : u ∈ S
    · have hNF : N u ⊆ freePorts p u := by
        intro j hj
        simp [freePorts, hN u hu j hj]
      obtain ⟨q, hq⟩ := exists_newPorts (freePorts p u) (N u) (R u) hNF (hNR u hu) (hRF u hu)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨fun _ => none, fun h => absurd h hu⟩
  choose q hq using hex
  have hfree : ∀ u ∈ S, ∀ j v, q u j = some v → p u j = none := by
    intro u hu j v h
    have := ((hq u hu).1 j v h).2
    simpa [freePorts] using this
  let p' : PortMap m := fun u j => (p u j).or (q u j)
  have hp'_of_p : ∀ u j v, p u j = some v → p' u j = some v := by
    intro u j v h; simp [p', h]
  have hp'_of_q : ∀ u ∈ S, ∀ j v, q u j = some v → p' u j = some v := by
    intro u hu j v h; simp [p', h, hfree u hu j v h]
  have hp'_cases : ∀ u j v, p' u j = some v → p u j = some v ∨ (p u j = none ∧ q u j = some v) := by
    intro u j v h
    rcases hpj : p u j with _ | w
    · right; simp only [p', hpj, Option.none_or] at h; exact ⟨rfl, h⟩
    · left; simp only [p', hpj, Option.some_or] at h; rw [h]
  refine ⟨p', ⟨?_, ?_, ?_, ?_⟩, fun u _ j v h => hp'_of_p u j v h, ?_, ?_, ?_⟩
  · intro u hu j v h
    rcases hp'_cases u j v h with h | ⟨_, h⟩
    · exact hp.mem u hu j v h
    · exact hRS u hu ((hq u hu).1 j v h).1
  · intro u hu j h
    rcases hp'_cases u j u h with h | ⟨_, h⟩
    · exact hp.ne u hu j h
    · exact hRu u hu ((hq u hu).1 j u h).1
  · intro u hu i j v hi hj
    rcases hp'_cases u i v hi with hi | ⟨hi0, hi⟩ <;>
      rcases hp'_cases u j v hj with hj | ⟨hj0, hj⟩
    · exact hp.inj u hu i j v hi hj
    · exact absurd hi (hRn u hu v ((hq u hu).1 j v hj).1 i)
    · exact absurd hj (hRn u hu v ((hq u hu).1 i v hi).1 j)
    · exact (hq u hu).2.1 i j v hi hj
  · intro u hu j v h
    rcases hp'_cases u j v h with h | ⟨_, h⟩
    · obtain ⟨i, hi⟩ := hp.symm u hu j v h
      exact ⟨i, hp'_of_p v i u hi⟩
    · have hvR := ((hq u hu).1 j v h).1
      have hv : v ∈ S := hRS u hu hvR
      obtain ⟨i, hi⟩ := (hq v hv).2.2.1 u (hRsymm u hu v hvR)
      exact ⟨i, hp'_of_q v hv i u hi⟩
  · intro u hu j v h
    rcases hp'_cases u j v h with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr ((hq u hu).1 j v h).1
  · intro u hu v hv
    obtain ⟨j, hj⟩ := (hq u hu).2.2.1 v hv
    exact ⟨j, hp'_of_q u hu j v hj⟩
  · intro u hu j hj
    have := (hq u hu).2.2.2 j hj
    rcases hqj : q u j with _ | v
    · rw [hqj] at this; cases this
    · rw [hp'_of_q u hu j v hqj]; rfl

/-- Every well-formed partial port map on `m + 1` nodes extends to a port map. -/
theorem exists_isPortMap_extends (p : PortMap m) (I : Finset ℕ) (hp : WF p I)
    (hI : I.card = m + 1) :
    ∃ P : PortMap m, IsPortMap P I ∧ ∀ u ∈ I, ∀ j v, p u j = some v → P u j = some v := by
  have hcardR : ∀ u ∈ I, ((I.erase u) \ nbrs p u).card = (freePorts p u).card := by
    intro u hu
    rw [Finset.card_sdiff_of_subset (nbrs_subset hp hu), Finset.card_erase_of_mem hu, hI]
    have := card_nbrs hp hu
    omega
  obtain ⟨P, hP, hext, -, -, hN⟩ := augment p I hp (fun u => (I.erase u) \ nbrs p u)
    (fun u => freePorts p u)
    (fun u _ => (Finset.sdiff_subset).trans (Finset.erase_subset _ _))
    (fun u _ h => by simp at h)
    (fun u _ v hv j hj => by
      simp only [Finset.mem_sdiff] at hv
      exact hv.2 (mem_nbrs.2 ⟨j, hj⟩))
    (fun u hu v hv => by
      simp only [Finset.mem_sdiff, Finset.mem_erase] at hv ⊢
      refine ⟨⟨fun h => hv.1.1 h.symm, hu⟩, fun h => hv.2 ?_⟩
      obtain ⟨i, hi⟩ := mem_nbrs.1 h
      obtain ⟨j, hj⟩ := hp.symm v hv.1.2 i u hi
      exact mem_nbrs.2 ⟨j, hj⟩)
    (fun u _ j hj => by simpa [freePorts] using hj)
    (fun u hu => (hcardR u hu).ge)
    (fun u hu => (hcardR u hu).le)
  refine ⟨P, ⟨hP, ?_⟩, hext⟩
  intro u hu j
  rcases hpj : p u j with _ | v
  · exact hN u hu j (by simp [freePorts, hpj])
  · rw [hext u hu j v hpj]; rfl

/-- Gluing isolated partial executions of pairwise disjoint node sets. -/
theorem glue {ι : Type*} [Fintype ι] (A : Algorithm m) (X : ι → Finset ℕ) (q : ι → PortMap m)
    (hdisj : Pairwise (Disjoint on X)) (hwf : ∀ a, WF (q a) (X a)) (r : ℕ)
    (hval : ∀ a, Valid A (q a) r (X a)) :
    ∃ p : PortMap m, WF p (univ.biUnion X) ∧ Valid A p r (univ.biUnion X) ∧
      ∀ a, ∀ u ∈ X a, ∀ r', run A p r' u = run A (q a) r' u := by
  let p : PortMap m := fun u => if h : ∃ a, u ∈ X a then q (Classical.choose h) u else fun _ => none
  have hpa : ∀ a, ∀ u ∈ X a, p u = q a u := by
    intro a u hu
    have h : ∃ a, u ∈ X a := ⟨a, hu⟩
    simp only [p, h, dite_true]
    have hc := Classical.choose_spec h
    by_contra hne
    have hab : Classical.choose h ≠ a := fun h' => hne (by rw [h'])
    exact Finset.disjoint_left.1 (hdisj hab) hc hu
  have hrun : ∀ a, ∀ u ∈ X a, ∀ r', run A p r' u = run A (q a) r' u := by
    intro a u hu r'
    exact run_congr (X := X a) (fun v hv => hpa a v hv)
      (fun v hv j w hj => (hwf a).mem v hv j w (by rw [← hpa a v hv]; exact hj)) r' u hu
  refine ⟨p, ⟨?_, ?_, ?_, ?_⟩, ?_, hrun⟩
  · intro u hu j v h
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
    rw [hpa a u ha] at h
    exact Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, (hwf a).mem u ha j v h⟩
  · intro u hu j h
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
    rw [hpa a u ha] at h
    exact (hwf a).ne u ha j h
  · intro u hu i j v hi hj
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
    rw [hpa a u ha] at hi hj
    exact (hwf a).inj u ha i j v hi hj
  · intro u hu j v h
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
    rw [hpa a u ha] at h
    obtain ⟨i, hi⟩ := (hwf a).symm u ha j v h
    exact ⟨i, by rw [hpa a v ((hwf a).mem u ha j v h)]; exact hi⟩
  · intro r' hr' u hu j hj
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
    rw [hpa a u ha] at hj
    rw [hrun a u ha]
    exact hval a r' hr' u ha j hj

/-- Gluing isolated partial executions into a full execution on `m + 1` nodes. -/
theorem glue_full {ι : Type*} [Fintype ι] (A : Algorithm m) (X : ι → Finset ℕ)
    (q : ι → PortMap m) (hdisj : Pairwise (Disjoint on X)) (hwf : ∀ a, WF (q a) (X a)) (r : ℕ)
    (hval : ∀ a, Valid A (q a) r (X a)) (hcard : (univ.biUnion X).card = m + 1) :
    ∃ P : PortMap m, IsPortMap P (univ.biUnion X) ∧
      ∀ a, ∀ u ∈ X a, ∀ r' ≤ r, run A P r' u = run A (q a) r' u := by
  obtain ⟨p, hp, hv, hrun⟩ := glue A X q hdisj hwf r hval
  obtain ⟨P, hP, hext⟩ := exists_isPortMap_extends p _ hp hcard
  refine ⟨P, hP, fun a u hu r' hr' => ?_⟩
  rw [run_eq_of_extends hp hP.1 hext hv r' hr' u
    (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hu⟩), hrun a u hu r']

theorem card_biUnion_univ {ι : Type*} [Fintype ι] (X : ι → Finset ℕ)
    (hdisj : Pairwise (Disjoint on X)) (s : ℕ) (hs : ∀ a, (X a).card = s) :
    (univ.biUnion X).card = Fintype.card ι * s := by
  rw [Finset.card_biUnion (fun a _ b _ hab => hdisj hab)]
  simp [hs, Finset.card_univ]

end LeaderTradeoffs
