import Podc.Computability.Distributed.DistributedAutomata.Basic

-- CSLib candidate: Cslib/Computability/Distributed/DistributedAutomata/Simulation.lean

/-!
# Simulation lemmas for distributed automata

* Run algebra: `runFrom_add`, `runFrom_eq_runList`, `runList_append`.
* Views along maps: `view_comp_of_bijOn` (covering-type maps preserve counting views),
  `view_one_comp_of_image_eq` (maps that are surjective on neighbourhoods preserve non-counting
  views).
* `sim`: a run on `G` lifts to a run on `H` along `π : H → G` on a shrinking family of "good"
  nodes where views are preserved (covering arguments, and their local versions used in
  "cut-and-paste" constructions).
* Independent selections: `step_step_of_indep` (non-adjacent disjoint selections can be executed
  one after the other), `Selection.Liftable`, `reach_step_of_liftable`.
* `Reach`: reachability by finite sequences of permitted selections.
-/

namespace Cslib.DistributedAutomata

open Set

variable {Λ Q V W : Type*}

section RunAlgebra

variable (M : Machine Λ Q) (G : SimpleGraph V)

@[simp] lemma runFrom_zero (C : V → Q) (σ : ℕ → Set V) : runFrom M G C σ 0 = C := rfl

lemma runFrom_succ (C : V → Q) (σ : ℕ → Set V) (t : ℕ) :
    runFrom M G C σ (t + 1) = step M G (runFrom M G C σ t) (σ t) := rfl

@[simp] lemma step_empty (C : V → Q) : step M G C ∅ = C := by
  funext v; simp [step]

lemma step_of_mem {C : V → Q} {S : Set V} {v : V} (h : v ∈ S) :
    step M G C S v = M.δ (C v) (view M.β G C v) := by
  simp [step, h]

lemma step_of_notMem {C : V → Q} {S : Set V} {v : V} (h : v ∉ S) : step M G C S v = C v := by
  simp [step, h]

lemma runFrom_add (C : V → Q) (σ : ℕ → Set V) (n m : ℕ) :
    runFrom M G C σ (n + m) = runFrom M G (runFrom M G C σ n) (fun t => σ (n + t)) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← Nat.add_assoc, runFrom_succ, ih, runFrom_succ]

@[simp] lemma runList_nil (C : V → Q) : runList M G C [] = C := rfl

@[simp] lemma runList_cons (C : V → Q) (S : Set V) (l : List (Set V)) :
    runList M G C (S :: l) = runList M G (step M G C S) l := rfl

lemma runList_append (C : V → Q) (l₁ l₂ : List (Set V)) :
    runList M G C (l₁ ++ l₂) = runList M G (runList M G C l₁) l₂ := by
  simp [runList, List.foldl_append]

lemma runList_concat (C : V → Q) (l : List (Set V)) (S : Set V) :
    runList M G C (l ++ [S]) = step M G (runList M G C l) S := by
  simp [runList_append]

lemma runFrom_eq_runList (C : V → Q) (σ : ℕ → Set V) (n : ℕ) :
    runFrom M G C σ n = runList M G C ((List.range n).map σ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runFrom_succ, ih, List.range_succ, List.map_append, runList_append]; rfl

/-- Running a constant-in-a-state: a node not selected keeps its state. -/
lemma runFrom_eq_of_forall_notMem (C : V → Q) (σ : ℕ → Set V) (v : V) (n : ℕ)
    (h : ∀ t < n, v ∉ σ t) : runFrom M G C σ n v = C v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ, step_of_notMem M G (h n (by omega))]
    exact ih fun t ht => h t (by omega)

end RunAlgebra

section Views

lemma view_congr {β : ℕ} {G : SimpleGraph V} {C C' : V → Q} {v : V}
    (h : ∀ u, G.Adj v u → C u = C' u) : view β G C v = view β G C' v := by
  funext q
  simp only [view]
  congr 2
  ext u
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hu, rfl⟩; exact ⟨hu, (h u hu).symm⟩
  · rintro ⟨hu, rfl⟩; exact ⟨hu, h u hu⟩

/-- A map that is a bijection from the neighbourhood of `w` onto the neighbourhood of `π w`
preserves the (counting) view of `w`. -/
lemma view_comp_of_bijOn {β : ℕ} {G : SimpleGraph V} {H : SimpleGraph W} {π : W → V} {w : W}
    (h : BijOn π {u | H.Adj w u} {x | G.Adj (π w) x}) (C : V → Q) :
    view β H (C ∘ π) w = view β G C (π w) := by
  funext q
  simp only [view]
  congr 1
  have hinj : InjOn π {u | H.Adj w u ∧ C (π u) = q} := h.injOn.mono fun u hu => hu.1
  simp only [Function.comp_apply]
  rw [← hinj.ncard_image]
  congr 1
  ext x
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨u, ⟨hu, hq⟩, rfl⟩; exact ⟨h.mapsTo hu, hq⟩
  · rintro ⟨hx, hq⟩
    obtain ⟨u, hu, rfl⟩ := h.surjOn hx
    exact ⟨u, ⟨hu, hq⟩, rfl⟩

lemma min_one_ncard_eq {α γ : Type*} [Finite α] [Finite γ] {s : Set α} {t : Set γ}
    (h : s.Nonempty ↔ t.Nonempty) : min 1 s.ncard = min 1 t.ncard := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · have ht : t = ∅ := by
      rw [← not_nonempty_iff_eq_empty, ← h, hs]; exact not_nonempty_empty
    simp [hs, ht]
  · have ht := h.1 hs
    rw [min_eq_left (Nat.one_le_iff_ne_zero.2 ((ncard_pos (toFinite _)).2 hs).ne'),
      min_eq_left (Nat.one_le_iff_ne_zero.2 ((ncard_pos (toFinite _)).2 ht).ne')]

/-- A map that sends the neighbourhood of `w` onto the neighbourhood of `π w` preserves the
non-counting view (`β = 1`) of `w`. -/
lemma view_one_comp_of_image_eq [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    {π : W → V} {w : W} (h : π '' {u | H.Adj w u} = {x | G.Adj (π w) x}) (C : V → Q) :
    view 1 H (C ∘ π) w = view 1 G C (π w) := by
  funext q
  simp only [view]
  apply min_one_ncard_eq
  constructor
  · rintro ⟨u, hu, hq⟩
    have : π u ∈ π '' {u | H.Adj w u} := mem_image_of_mem _ hu
    rw [h] at this
    exact ⟨π u, this, hq⟩
  · rintro ⟨x, hx, hq⟩
    have hx' : x ∈ π '' {u | H.Adj w u} := h ▸ hx
    obtain ⟨u, hu, rfl⟩ := hx'
    exact ⟨u, hu, hq⟩

end Views

section Sim

variable (M : Machine Λ Q) (G : SimpleGraph V) (H : SimpleGraph W)

/-- **Simulation along a map.** Let `π : W → V`, let `R` be a schedule of `G`, and run `H` with the
pulled-back schedule `π ⁻¹' R t`. On a shrinking family `Good t` of nodes of `H` whose good
neighbours stay good one step earlier and whose views are preserved by `π`, the run on `H` is the
run on `G` composed with `π`. -/
theorem sim (π : W → V) (R : ℕ → Set V) (C : V → Q) (D : W → Q) (Good : ℕ → Set W)
    (h0 : ∀ w ∈ Good 0, D w = C (π w))
    (hmono : ∀ t, Good (t + 1) ⊆ Good t)
    (hnbr : ∀ t, ∀ w ∈ Good (t + 1), ∀ u, H.Adj w u → u ∈ Good t)
    (hview : ∀ t, ∀ w ∈ Good (t + 1),
      view M.β H (runFrom M G C R t ∘ π) w = view M.β G (runFrom M G C R t) (π w)) :
    ∀ t, ∀ w ∈ Good t, runFrom M H D (fun t => π ⁻¹' R t) t w = runFrom M G C R t (π w) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro w hw
    have hw' := hmono t hw
    rw [runFrom_succ, runFrom_succ]
    by_cases hR : π w ∈ R t
    · rw [step_of_mem _ _ (show w ∈ π ⁻¹' R t from hR), step_of_mem _ _ hR, ih w hw', ← hview t w hw]
      congr 1
      exact view_congr fun u hu => ih u (hnbr t w hw u hu)
    · rw [step_of_notMem _ _ (show w ∉ π ⁻¹' R t from hR), step_of_notMem _ _ hR, ih w hw']

/-- Global version of `sim`: if `π` preserves all views, runs lift along `π`. -/
theorem sim_global (π : W → V) (R : ℕ → Set V) (C : V → Q)
    (hview : ∀ (C : V → Q) w, view M.β H (C ∘ π) w = view M.β G C (π w)) (t : ℕ) :
    runFrom M H (C ∘ π) (fun t => π ⁻¹' R t) t = runFrom M G C R t ∘ π := by
  funext w
  exact sim M G H π R C (C ∘ π) (fun _ => univ) (fun _ _ => rfl) (fun _ => subset_rfl)
    (fun _ _ _ _ _ => trivial) (fun t w _ => hview _ w) t w trivial

end Sim

section Indep

variable (M : Machine Λ Q) (G : SimpleGraph V)

lemma step_mem_or (C : V → Q) (A S : Set V) (hAS : A ⊆ S) (v : V) :
    step M G C A v = C v ∨ step M G C A v = step M G C S v := by
  by_cases hv : v ∈ A
  · right; rw [step_of_mem _ _ hv, step_of_mem _ _ (hAS hv)]
  · left; rw [step_of_notMem _ _ hv]

/-- Two disjoint selections without edges between them can be executed one after the other. -/
lemma step_step_of_indep (C : V → Q) (A B : Set V) (hd : Disjoint A B)
    (hadj : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj b a) :
    step M G (step M G C A) B = step M G C (A ∪ B) := by
  funext v
  by_cases hB : v ∈ B
  · have hA : v ∉ A := fun h => hd.ne_of_mem h hB rfl
    rw [step_of_mem _ _ hB, step_of_mem _ _ (show v ∈ A ∪ B from Or.inr hB), step_of_notMem _ _ hA]
    congr 1
    exact view_congr fun u hu => step_of_notMem _ _ fun huA => hadj u huA v hB hu
  · rw [step_of_notMem _ _ hB]
    by_cases hA : v ∈ A
    · rw [step_of_mem _ _ hA, step_of_mem _ _ (show v ∈ A ∪ B from Or.inl hA)]
    · rw [step_of_notMem _ _ hA, step_of_notMem _ _ (by simp [hA, hB])]

/-- Executing the nodes of an independent list one at a time. -/
lemma runList_singletons (C : V → Q) (l : List V) (hl : l.Nodup)
    (hind : ∀ a ∈ l, ∀ b ∈ l, ¬ G.Adj a b) :
    runList M G C (l.map fun v => {v}) = step M G C {v | v ∈ l} := by
  induction l generalizing C with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, runList_cons, ih _ (List.nodup_cons.1 hl).2
      (fun x hx y hy => hind x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)),
      step_step_of_indep]
    · congr 1; ext v; simp
    · rw [disjoint_singleton_left]; exact (List.nodup_cons.1 hl).1
    · rintro x rfl b hb; exact hind b (List.mem_cons_of_mem _ hb) x (List.mem_cons_self)

/-- Reachability by finite sequences of permitted selections. -/
def Reach (κ : Selection) (C D : V → Q) : Prop :=
  ∃ l : List (Set V), (∀ S ∈ l, κ.Permitted S) ∧ runList M G C l = D

variable {M G}

lemma Reach.refl (κ : Selection) (C : V → Q) : Reach M G κ C C := ⟨[], by simp, rfl⟩

lemma Reach.trans {κ : Selection} {C D E : V → Q} (h₁ : Reach M G κ C D) (h₂ : Reach M G κ D E) :
    Reach M G κ C E := by
  obtain ⟨l₁, hl₁, rfl⟩ := h₁
  obtain ⟨l₂, hl₂, rfl⟩ := h₂
  refine ⟨l₁ ++ l₂, ?_, runList_append _ _ _ _ _⟩
  intro S hS
  rcases List.mem_append.1 hS with h | h
  exacts [hl₁ S h, hl₂ S h]

lemma reach_step {κ : Selection} {S : Set V} (hS : κ.Permitted S) (C : V → Q) :
    Reach M G κ C (step M G C S) := ⟨[S], by simpa using hS, rfl⟩

end Indep

/-- Selections that can be simulated under the selection constraint `κ`: any selection for liberal
selection, independent nonempty sets for exclusive selection (executed one node at a time), the
full set for synchronous selection. -/
def Selection.Liftable (G : SimpleGraph V) : Selection → Set V → Prop
  | .liberal, _ => True
  | .exclusive, S => G.IsIndepSet S ∧ S.Nonempty
  | .synchronous, S => S = univ

lemma Selection.liftable_of_permitted {G : SimpleGraph V} {κ : Selection} {S : Set V}
    (h : κ.Permitted S) : κ.Liftable G S := by
  cases κ with
  | liberal => trivial
  | exclusive =>
    obtain ⟨v, rfl⟩ := h
    exact ⟨fun a ha b hb hab => absurd (ha.trans hb.symm) hab, singleton_nonempty v⟩
  | synchronous => exact h

section Lift

variable {M : Machine Λ Q} {G : SimpleGraph V}

lemma reach_step_of_liftable [Finite V] {κ : Selection} {S : Set V} (hS : κ.Liftable G S)
    (C : V → Q) : Reach M G κ C (step M G C S) := by
  cases κ with
  | liberal => exact reach_step (κ := .liberal) (S := S) trivial C
  | synchronous => exact reach_step (κ := .synchronous) (S := S) hS C
  | exclusive =>
    obtain ⟨hind, -⟩ := hS
    have hfin : S.Finite := toFinite S
    refine ⟨hfin.toFinset.toList.map fun v => {v}, ?_, ?_⟩
    · simp only [List.mem_map]
      rintro _ ⟨v, -, rfl⟩
      exact ⟨v, rfl⟩
    · rw [runList_singletons M G C _ (Finset.nodup_toList _)]
      · congr 1; ext v; simp
      · intro a ha b hb hab
        simp only [Finset.mem_toList, Finite.mem_toFinset] at ha hb
        exact hind ha hb (G.ne_of_adj hab) hab

lemma reach_runFrom_of_liftable [Finite V] {κ : Selection} {R : ℕ → Set V}
    (hR : ∀ t, κ.Liftable G (R t)) (C : V → Q) (n : ℕ) :
    Reach M G κ C (runFrom M G C R n) := by
  induction n with
  | zero => exact Reach.refl κ C
  | succ n ih => exact ih.trans (reach_step_of_liftable (hR n) _)

end Lift

end Cslib.DistributedAutomata
