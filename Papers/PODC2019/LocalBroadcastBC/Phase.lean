import Papers.PODC2019.LocalBroadcastBC.Algorithm

/-!
# One phase of Algorithm 1, abstractly: Lemmas 5.2 and 5.3 of [KNV19]

We abstract the outcome of the flooding step (a) of a phase as `FloodOutcome`: every non-faulty
node `v` received along `K` (where `K ++ [v]` is the path) a value that

* (soundness, Observation B.1) equals the value `fv a` *flooded* by the first node `a` of `K`
  whenever all other nodes of `K` are non-faulty, and
* (completeness, used tacitly in the paper) is indeed received, with that value, whenever
  `K ++ [v]` is a simple path whose nodes other than the first are non-faulty.

`fv a` is the state of `a` at the start of the phase if `a` is non-faulty. With this, steps (b),
(c) give Lemma 5.2 (`lemma_5_2`) and, given the disjoint paths of Lemma 5.5 (`PathsExist`),
Lemma 5.3 (`lemma_5_3`).
-/

open Finset

namespace LocalBroadcastBC

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : ℕ}
  {sel : Finset V → V → V → List V}

/-! ### Small list lemmas -/

omit [Fintype V] [DecidableEq V] in
lemma head?_dropLast_of_ne {l : List V} {a v : V} (ha : l.head? = some a)
    (hv : l.getLast? = some v) (hne : a ≠ v) : l.dropLast.head? = some a := by
  have hl := List.dropLast_append_getLast? v hv
  rcases hd : l.dropLast with _ | ⟨b, t⟩
  · rw [hd] at hl
    rw [← hl] at ha
    simp at ha
    exact absurd ha.symm hne
  · rw [hd] at hl
    rw [← hl] at ha
    simpa using ha

omit [Fintype V] [DecidableEq V] in
lemma mem_of_mem_dropLast {l : List V} {x : V} (h : x ∈ l.dropLast) : x ∈ l :=
  List.dropLast_subset l h

omit [Fintype V] [DecidableEq V] in
lemma mem_of_mem_internal {l : List V} {x : V} (h : x ∈ internal l) : x ∈ l :=
  List.mem_of_mem_tail (List.dropLast_subset _ h)

/-! ### The abstract flooding outcome -/

/-- The outcome of step (a) of a phase, for the faulty set `Bz`: `ac v K` is the value that the
non-faulty node `v` received along `K ++ [v]`, and `fv a` the value flooded by `a`. -/
structure FloodOutcome (G : SimpleGraph V) (Bz : Finset V) (fv : V → Bool)
    (ac : V → List V → Option Bool) : Prop where
  sound : ∀ v, v ∉ Bz → ∀ K b, ac v K = some b → (∀ z ∈ K.tail, z ∉ Bz) →
    ∃ a, K.head? = some a ∧ b = fv a
  complete : ∀ v, v ∉ Bz → ∀ K a, K.head? = some a → IsPathList G (K ++ [v]) →
    (∀ z ∈ K.tail, z ∉ Bz) → ac v K = some (fv a)

/-- The conclusion of Lemma 5.5: `f + 1` simple `A w`-paths that exclude `F` and pairwise share
only `w`. -/
def DisjointPaths (G : SimpleGraph V) (f : ℕ) (F A : Finset V) (w : V) : Prop :=
  ∃ S : Finset (List V), S.card = f + 1 ∧
    (∀ P ∈ S, IsPathList G P ∧ (∃ a ∈ A, P.head? = some a) ∧ P.getLast? = some w ∧
      ∀ x ∈ internal P, x ∉ F) ∧
    ∀ P ∈ S, ∀ P' ∈ S, P ≠ P' → ∀ x ∈ P, x ∈ P' → x = w

/-- Lemma 5.5 as a property of the graph: in every phase, if `w ∈ B_w` then there are `f + 1`
node-disjoint `A_w w`-paths that exclude `F` (it only depends on `Z_w` and `F`). -/
def PathsExist (G : SimpleGraph V) (f : ℕ) : Prop :=
  ∀ F : Finset V, F.card ≤ f → ∀ Z : Finset V, ∀ w ∈ (sets f F Z).2,
    DisjointPaths G f F (sets f F Z).1 w

lemma sets_eq (F Z : Finset V) :
    sets f F Z = (univ \ Z, Z) ∨ sets f F Z = (Z, univ \ Z) := by
  unfold sets
  split_ifs <;> simp

lemma not_mem_fst_of_mem_snd {F Z : Finset V} {w : V} (hw : w ∈ (sets f F Z).2) :
    w ∉ (sets f F Z).1 := by
  rcases sets_eq (f := f) F Z with h | h <;> rw [h] at hw ⊢ <;> simp_all

/-- Pigeonhole: among `f + 1` paths pairwise sharing only `w`, with `w` non-faulty and at most `f`
faulty nodes, one path has no faulty node at all. -/
lemma exists_fault_free {Bz : Finset V} (hBz : Bz.card ≤ f) {w : V} (hw : w ∉ Bz)
    {S : Finset (List V)} (hS : S.card = f + 1)
    (hdisj : ∀ P ∈ S, ∀ P' ∈ S, P ≠ P' → ∀ x ∈ P, x ∈ P' → x = w) :
    ∃ P ∈ S, ∀ x ∈ P, x ∉ Bz := by
  classical
  by_contra h
  push Not at h
  choose g hg hgB using h
  have hinj : Set.InjOn (fun P => if hP : P ∈ S then g P hP else w) S := by
    intro P hP P' hP' heq
    simp only [mem_coe.1 hP, mem_coe.1 hP', dite_true] at heq
    by_contra hne
    have h1 := hg P' hP'
    rw [← heq] at h1
    have := hdisj P hP P' hP' hne _ (hg P hP) h1
    exact hw (this ▸ hgB P hP)
  have := card_le_card_of_injOn (t := Bz) _
    (fun P hP => by simp only [mem_coe.1 hP, dite_true]; exact hgB P hP) hinj
  omega

/-- **Lemma 5.2** of [KNV19]: the state of a non-faulty node at the end of a phase is the state of
some non-faulty node at the start of the phase. -/
theorem lemma_5_2 {Bz : Finset V} (hBz : Bz.card ≤ f) {fv : V → Bool} {γ : V → Bool}
    {ac : V → List V → Option Bool} (hO : FloodOutcome G Bz fv ac)
    (hfv : ∀ u, u ∉ Bz → fv u = γ u) (F : Finset V) {v : V} (hv : v ∉ Bz) :
    ∃ u, u ∉ Bz ∧ update G f sel F v (γ v) (ac v) = γ u := by
  classical
  -- received `δ` along `f + 1` disjoint paths: one of them is fault-free
  have key : ∀ A δ, v ∉ A → Accepts G f F A v (ac v) δ → ∃ u, u ∉ Bz ∧ δ = γ u := by
    intro A δ hvA ⟨S, hS, hP, hdisj⟩
    obtain ⟨P, hPS, hPf⟩ := exists_fault_free hBz hv hS hdisj
    obtain ⟨-, ⟨a, haA, ha⟩, hlast, -, hacc⟩ := hP P hPS
    have hne : a ≠ v := fun h => hvA (h ▸ haA)
    obtain ⟨a', ha', hδ⟩ := hO.sound v hv _ δ hacc
      (fun z hz => hPf z (mem_of_mem_dropLast (List.mem_of_mem_tail hz)))
    have ha'P : a' ∈ P := mem_of_mem_dropLast (List.mem_of_mem_head? ha')
    exact ⟨a', hPf a' ha'P, hδ.trans (hfv a' (hPf a' ha'P))⟩
  unfold update
  simp only
  split_ifs with hB h0 h1
  · obtain ⟨u, hu, h⟩ := key _ false (not_mem_fst_of_mem_snd hB) h0
    exact ⟨u, hu, h⟩
  · obtain ⟨u, hu, h⟩ := key _ true (not_mem_fst_of_mem_snd hB) h1
    exact ⟨u, hu, h⟩
  · exact ⟨v, hv, rfl⟩
  · exact ⟨v, hv, rfl⟩

/-- In a phase whose `F` contains all faulty nodes, every non-faulty node computes
`Z_v = {u | u flooded 0}` (first part of the proof of Lemma 5.3). -/
lemma zset_eq {Bz F : Finset V} (hBF : Bz ⊆ F) (hF : F.card ≤ f) (hsel : SelSpec G f sel)
    {fv : V → Bool} {γ : V → Bool} {ac : V → List V → Option Bool}
    (hO : FloodOutcome G Bz fv ac) (hfv : ∀ u, u ∉ Bz → fv u = γ u) {v : V} (hv : v ∉ Bz) :
    Zset sel F v (γ v) (ac v) = univ.filter (fun u => fv u = false) := by
  classical
  ext u
  by_cases huv : u = v
  · subst huv
    simp [mem_Zset, recv, hfv u hv]
  · simp only [mem_Zset, recv, mem_filter, mem_univ, true_and, huv, ite_false]
    obtain ⟨hpath, hhead, hlast, hint⟩ := hsel F hF u v huv
    have hK : (sel F u v).dropLast ++ [v] = sel F u v := List.dropLast_append_getLast? v hlast
    have := hO.complete v hv _ u (head?_dropLast_of_ne hhead hlast huv) (by rw [hK]; exact hpath)
      (fun z hz => by
        rw [List.tail_dropLast] at hz
        exact fun hzB => hint z hz (hBF hzB))
    rw [this]
    simp

/-- **Lemma 5.3** of [KNV19]: in a phase whose set `F` contains all faulty nodes, all non-faulty
nodes end the phase with the same state. -/
theorem lemma_5_3 {Bz F : Finset V} (hBF : Bz ⊆ F) (hF : F.card ≤ f) (hsel : SelSpec G f sel)
    (hpaths : PathsExist G f) {fv : V → Bool} {γ : V → Bool} {ac : V → List V → Option Bool}
    (hO : FloodOutcome G Bz fv ac) (hfv : ∀ u, u ∉ Bz → fv u = γ u) :
    ∃ α, ∀ v, v ∉ Bz → update G f sel F v (γ v) (ac v) = α := by
  classical
  set Z := univ.filter (fun u => fv u = false) with hZ
  have hZv : ∀ v, v ∉ Bz → Zset sel F v (γ v) (ac v) = Z := fun v hv =>
    zset_eq hBF hF hsel hO hfv hv
  -- the common value `α` flooded by all nodes of `A`
  obtain ⟨α, hα⟩ : ∃ α, ∀ a, a ∈ (sets f F Z).1 ↔ fv a = α := by
    rcases sets_eq (f := f) F Z with h | h
    · refine ⟨true, fun a => ?_⟩
      rw [h]; simp [hZ]
    · refine ⟨false, fun a => ?_⟩
      rw [h]; simp [hZ]
  have hβ : ∀ a, a ∈ (sets f F Z).2 ↔ a ∉ (sets f F Z).1 := by
    intro a
    rcases sets_eq (f := f) F Z with h | h <;> rw [h] <;> simp
  refine ⟨α, fun v hv => ?_⟩
  -- only `α` can be accepted
  have honly : ∀ δ, Accepts G f F (sets f F Z).1 v (ac v) δ → v ∉ (sets f F Z).1 → δ = α := by
    rintro δ ⟨S, hS, hP, -⟩ hvA
    obtain ⟨P, hPS⟩ : S.Nonempty := card_pos.1 (by omega)
    obtain ⟨-, ⟨a, haA, ha⟩, hlast, hint, hacc⟩ := hP P hPS
    have hne : a ≠ v := fun h => hvA (h ▸ haA)
    obtain ⟨a', ha', hδ⟩ := hO.sound v hv _ δ hacc (fun z hz => by
      rw [List.tail_dropLast] at hz
      exact fun hzB => hint z hz (hBF hzB))
    rw [head?_dropLast_of_ne ha hlast hne] at ha'
    cases ha'
    exact hδ.trans ((hα a).1 haA)
  unfold update
  simp only [hZv v hv]
  by_cases hB : v ∈ (sets f F Z).2
  · have hvA := (hβ v).1 hB
    -- `α` is accepted, by Lemma 5.5 and completeness of flooding
    have hacc : Accepts G f F (sets f F Z).1 v (ac v) α := by
      obtain ⟨S, hS, hP, hdisj⟩ := hpaths F hF Z v hB
      refine ⟨S, hS, fun P hPS => ?_, hdisj⟩
      obtain ⟨hpath, ⟨a, haA, ha⟩, hlast, hint⟩ := hP P hPS
      have hne : a ≠ v := fun h => hvA (h ▸ haA)
      refine ⟨hpath.1, ⟨a, haA, ha⟩, hlast, hint, ?_⟩
      have hK : P.dropLast ++ [v] = P := List.dropLast_append_getLast? v hlast
      rw [hO.complete v hv _ a (head?_dropLast_of_ne ha hlast hne) (by rw [hK]; exact hpath)
        (fun z hz => by
          rw [List.tail_dropLast] at hz
          exact fun hzB => hint z hz (hBF hzB)), (hα a).1 haA]
    simp only [hB, ite_true]
    split_ifs with h0 h1
    · exact (honly false h0 hvA)
    · exact (honly true h1 hvA)
    · exact absurd (by cases α <;> simp_all) h1
  · simp only [hB, ite_false]
    have hvA : v ∈ (sets f F Z).1 := by by_contra h; exact hB ((hβ v).2 h)
    rw [← hfv v hv]
    exact (hα v).1 hvA

end LocalBroadcastBC
