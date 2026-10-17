import Papers.PODC2019.HardnessOptimization.HamPathTheorem

/-!
# Claim 2.6 and Theorem 2.3: directed Hamiltonian cycle

`D'_{x,y}` is `D_{x,y}` plus a vertex `middle` (`none : Option (HV _)`) with the arcs
`end → middle → start` (`cycArc`). Claim 2.6: `D'_{x,y}` has a directed Hamiltonian cycle iff
`D_{x,y}` has a directed Hamiltonian path. With `middle ∈ V_A` the cut grows by one pair
(`middle – end`), giving Theorem 2.3.
-/

namespace HardnessOptimization.HamPath

open HV Finset Podc.CongestLB

/-- A directed Hamiltonian cycle: a list of all vertices without repetitions, consecutive vertices
joined by arcs, and an arc from the last vertex back to the first. -/
def HasHamCycle {V : Type*} (R : V → V → Prop) : Prop :=
  ∃ l : List V, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain R ∧ ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b

/-- Add a vertex `middle = none` with arcs `t → middle → s`. -/
def cycArc {V : Type*} (R : V → V → Prop) (s t : V) : Option V → Option V → Prop
  | some u, some v => R u v
  | some u, none => u = t
  | none, some v => v = s
  | none, none => False

instance {V : Type*} [DecidableEq V] (R : V → V → Prop) [DecidableRel R] (s t : V) :
    DecidableRel (cycArc R s t) := fun u v => by
  cases u <;> cases v <;> unfold cycArc <;> infer_instance

section Generic

variable {α : Type*} {R : α → α → Prop}

/-- A Hamiltonian cycle can be rotated to start at any vertex. -/
lemma cycle_rotate {l : List α} (hc : l.IsChain R) (hw : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b)
    {v : α} (hv : v ∈ l) :
    ∃ t, (v :: t).Perm l ∧ (v :: t).IsChain R ∧ ∀ a ∈ (v :: t).getLast?, R a v := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hv
  obtain ⟨c1, c2, link⟩ := List.isChain_append.1 hc
  refine ⟨l₂ ++ l₁, ?_, ?_, ?_⟩
  · exact (List.perm_append_comm (l₁ := v :: l₂) (l₂ := l₁))
  · rw [← List.cons_append]
    refine List.isChain_append.2 ⟨c2, c1, fun a ha b hb => hw a ?_ b ?_⟩
    · have ha' : (v :: l₂).getLast? = some a := ha
      rw [List.getLast?_append, ha']; rfl
    · cases l₁ with
      | nil => simp at hb
      | cons c l₁ => simpa using hb
  · intro a ha
    cases l₁ using List.reverseRecOn with
    | nil =>
      apply hw a (by simpa using ha) v (by simp)
    | append_singleton l₁ c _ =>
      have ha' : a = c := by
        rw [show v :: (l₂ ++ (l₁ ++ [c])) = (v :: l₂ ++ l₁) ++ [c] by simp,
          List.getLast?_concat] at ha
        simpa using ha.symm
      subst ha'
      exact link a (by simp) v (by simp)

lemma exists_map_some : ∀ {t : List (Option α)}, none ∉ t → ∃ p : List α, t = p.map some
  | [], _ => ⟨[], rfl⟩
  | none :: t, h => absurd (List.mem_cons_self) h
  | some a :: t, h => by
    obtain ⟨p, rfl⟩ := exists_map_some (t := t) (fun h' => h (List.mem_cons_of_mem _ h'))
    exact ⟨a :: p, rfl⟩

/-- **Claim 2.6** (generic form): `R + middle` has a Hamiltonian cycle iff `R` has a Hamiltonian
path from `s` to `t`. -/
lemma hamCycle_iff (s t : α) :
    HasHamCycle (cycArc R s t) ↔ ∃ l : List α, l.Nodup ∧ (∀ v, v ∈ l) ∧ l.IsChain R ∧
      l.head? = some s ∧ l.getLast? = some t := by
  constructor
  · rintro ⟨l, hnd, hall, hc, hw⟩
    obtain ⟨u, hp, hc', hw'⟩ := cycle_rotate hc hw (hall none)
    have hnd' := hp.nodup_iff.2 hnd
    have hnone : none ∉ u := (List.nodup_cons.1 hnd').1
    obtain ⟨p, rfl⟩ := exists_map_some hnone
    refine ⟨p, ?_, fun v => ?_, ?_, ?_, ?_⟩
    · exact (List.nodup_map_iff (Option.some_injective _)).1 (List.nodup_cons.1 hnd').2
    · have := hp.mem_iff.2 (hall (some v))
      simpa using this
    · have := (List.isChain_cons.1 hc').2
      rwa [List.isChain_map] at this
    · cases p with
      | nil => simp [cycArc] at hw'
      | cons a p =>
        have := (List.isChain_cons.1 hc').1 (some a) (by simp)
        simp only [cycArc] at this
        simp [this]
    · cases p using List.reverseRecOn with
      | nil => simp [cycArc] at hw'
      | append_singleton p a _ =>
        have hl : (none :: (p ++ [a]).map some).getLast? = some (some a) := by
          rw [List.map_append, ← List.cons_append, List.map_singleton, List.getLast?_concat]
        have := hw' (some a) hl
        simp only [cycArc] at this
        rw [List.getLast?_concat, this]
  · rintro ⟨l, hnd, hall, hc, hs, ht⟩
    refine ⟨none :: l.map some, ?_, ?_, ?_, ?_⟩
    · simp [List.nodup_map_iff (Option.some_injective _), hnd]
    · intro v; cases v with
      | none => simp
      | some v => simp [hall v]
    · refine List.isChain_cons.2 ⟨?_, (List.isChain_map _).2 hc⟩
      intro b hb
      cases l with
      | nil => simp at hs
      | cons a l =>
        simp at hs hb; subst hs hb; rfl
    · intro a ha b hb
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      cases l using List.reverseRecOn with
      | nil => simp at ht
      | append_singleton l c _ =>
        simp at ht
        subst ht
        have : a = some c := by
          simp only [List.map_append, List.map_cons, List.map_nil] at ha
          rw [← List.cons_append, List.getLast?_concat] at ha
          simpa using ha.symm
        subst this; rfl

end Generic

/-- `D'_{x,y}` = `D_{x,y}` plus `middle` with arcs `end → middle → start`. -/
def dCycArc (L : ℕ) (x y : Idx (L + 1) → Idx (L + 1) → Bool) :
    Option (HV (L + 1)) → Option (HV (L + 1)) → Prop :=
  cycArc (dArc L x y) .start .stop

instance (L : ℕ) (x y : Idx (L + 1) → Idx (L + 1) → Bool) : DecidableRel (dCycArc L x y) :=
  inferInstanceAs (DecidableRel (cycArc _ _ _))

/-- **Claim 2.6.** `D'_{x,y}` has a directed Hamiltonian cycle iff `D_{x,y}` has a directed
Hamiltonian path. -/
theorem claim_2_6 {L : ℕ} (x y : Idx (L + 1) → Idx (L + 1) → Bool) :
    HasHamCycle (dCycArc L x y) ↔ HasHamPath (dArc L x y) := by
  rw [dCycArc, hamCycle_iff]
  constructor
  · rintro ⟨l, hnd, hall, hc, -, -⟩; exact ⟨l, hnd, hall, hc⟩
  · rintro ⟨l, hnd, hall, hc⟩
    refine ⟨l, hnd, hall, hc, ?_, ?_⟩
    · have h0 := idxOf_of_no_in hall hc (a := .start) (fun w => not_arc_into_start w)
      have hlt := List.idxOf_lt_length_iff.2 (hall .start)
      cases l with
      | nil => simp at hlt
      | cons a l => rw [← List.getElem_idxOf hlt]; simp [h0]
    · have h0 := idxOf_of_no_out hall hc (a := .stop) (fun w => not_arc_from_stop w)
      have hlt := List.idxOf_lt_length_iff.2 (hall .stop)
      rw [List.getLast?_eq_getElem?, ← h0, Nat.add_sub_cancel, List.getElem?_eq_getElem hlt,
        List.getElem_idxOf hlt]

/-- Claims 2.1, 2.2, 2.6: `D'_{x,y}` has a directed Hamiltonian cycle iff `DISJ(x, y) = FALSE`. -/
theorem hamCycle_iff_not_disj {L : ℕ} (x y : Idx (L + 1) → Idx (L + 1) → Bool) :
    HasHamCycle (dCycArc L x y) ↔ ∃ i j, x i j = true ∧ y i j = true := by
  rw [claim_2_6, hamPath_iff]

/-! ### The family of lower bound graphs for the cycle -/

/-- The network: underlying undirected graph of `D'_{x,y}`. -/
def cycNet (L : ℕ) (x y : Idx (L + 1) × Idx (L + 1) → Bool) : SimpleGraph (Option (HV (L + 1))) :=
  SimpleGraph.fromRel (dCycArc L (fun i j => x (i, j)) (fun i j => y (i, j)))

instance {L : ℕ} (x y : Idx (L + 1) × Idx (L + 1) → Bool) : DecidableRel (cycNet L x y).Adj :=
  fun a b => decidable_of_iff _ (SimpleGraph.fromRel_adj _ a b).symm

/-- Node inputs: incident out- and in-arcs. -/
def cycInp (L : ℕ) (x y : Idx (L + 1) × Idx (L + 1) → Bool) (v : Option (HV (L + 1))) :
    Option (HV (L + 1)) → Bool × Bool := fun w =>
  (decide (dCycArc L (fun i j => x (i, j)) (fun i j => y (i, j)) v w),
    decide (dCycArc L (fun i j => x (i, j)) (fun i j => y (i, j)) w v))

/-- `V_A` plus `middle`. -/
def aliceC {L : ℕ} : Option (HV (L + 1)) → Bool
  | none => true
  | some v => alice v

/-- `E_cut` plus the pair `(middle, end)`. -/
def cycCut (L : ℕ) : Finset (Option (HV (L + 1)) × Option (HV (L + 1))) :=
  insert (none, some .stop) ((hamCut L).image fun p => (some p.1, some p.2))

lemma card_cycCut {L : ℕ} : (cycCut L).card ≤ 24 * (L + 1) + 2 := by
  refine (card_insert_le _ _).trans ?_
  have := (card_image_le (s := hamCut L) (f := fun p => (some p.1, some p.2))).trans card_hamCut
  omega

lemma cycCut_sub {L : ℕ} (p) (hp : p ∈ cycCut L) : aliceC p.1 = true ∧ aliceC p.2 = false := by
  rcases mem_insert.1 hp with rfl | hp
  · simp [aliceC, alice]
  · obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
    exact hamCut_sub q hq

section Indep

variable {L : ℕ} {x x' y y' : Idx (L + 1) → Idx (L + 1) → Bool}

lemma cyc_indep_y {u v : Option (HV (L + 1))} (h : aliceC u = true ∨ aliceC v = true) :
    dCycArc L x y u v ↔ dCycArc L x y' u v := by
  cases u <;> cases v <;> simp only [dCycArc, cycArc]
  exact arc_indep_y (by simpa [aliceC] using h)

lemma cyc_indep_x {u v : Option (HV (L + 1))} (h : aliceC u = false ∨ aliceC v = false) :
    dCycArc L x y u v ↔ dCycArc L x' y u v := by
  cases u <;> cases v <;> simp only [dCycArc, cycArc]
  exact arc_indep_x (by simpa [aliceC] using h)

lemma cyc_cross {u v : Option (HV (L + 1))} (h : dCycArc L x y u v) (hs : aliceC u ≠ aliceC v) :
    (u, v) ∈ cycCut L ∨ (v, u) ∈ cycCut L := by
  cases u with
  | none =>
    cases v with
    | none => exact h.elim
    | some v =>
      simp only [dCycArc, cycArc] at h
      subst h; simp [aliceC, alice] at hs
  | some u =>
    cases v with
    | none =>
      simp only [dCycArc, cycArc] at h
      subst h; exact Or.inr (mem_insert_self _ _)
    | some v =>
      simp only [dCycArc, cycArc, aliceC] at h hs
      rcases cross ((arc_cross hs).1 h) hs with h' | h'
      · exact Or.inl (mem_insert_of_mem (mem_image_of_mem _ h'))
      · exact Or.inr (mem_insert_of_mem (mem_image_of_mem _ h'))

lemma cyc_fixed {u v : Option (HV (L + 1))} (hs : aliceC u ≠ aliceC v) :
    dCycArc L x y u v ↔ dCycArc L x' y' u v := by
  cases u <;> cases v <;> simp only [dCycArc, cycArc, dArc]
  simp only [aliceC] at hs
  rw [arc_cross hs, arc_cross hs]

end Indep

/-- The directed Hamiltonian cycle graphs as a family of lower bound graphs. -/
def cycFamily (L : ℕ) :
    LBFamily (Idx (L + 1) × Idx (L + 1) → Bool) (Idx (L + 1) × Idx (L + 1) → Bool)
      (Option (HV (L + 1))) (Option (HV (L + 1)) → Bool × Bool) where
  G := cycNet L
  inp := cycInp L
  alice := aliceC
  Ecut := cycCut L
  Ecut_sub := cycCut_sub
  adj_cut x y a b ha hb hab := by
    rw [cycNet, SimpleGraph.fromRel_adj] at hab
    have hs : aliceC a ≠ aliceC b := by simp [ha, hb]
    rcases hab.2 with h | h
    · rcases cyc_cross h hs with h' | h'
      · exact h'
      · simpa [ha] using (cycCut_sub _ h').2
    · rcases cyc_cross h hs.symm with h' | h'
      · simpa [ha] using (cycCut_sub _ h').2
      · exact h'
  adj_alice x y y' a b ha hb := by
    simp only [cycNet, SimpleGraph.fromRel_adj]
    rw [cyc_indep_y (y' := fun i j => y' (i, j)) (Or.inl ha),
      cyc_indep_y (y' := fun i j => y' (i, j)) (Or.inl hb)]
  adj_bob x x' y a b ha hb := by
    simp only [cycNet, SimpleGraph.fromRel_adj]
    rw [cyc_indep_x (x' := fun i j => x' (i, j)) (Or.inl ha),
      cyc_indep_x (x' := fun i j => x' (i, j)) (Or.inl hb)]
  adj_fixed x x' y y' a b ha hb := by
    have hs : aliceC a ≠ aliceC b := by simp [ha, hb]
    simp only [cycNet, SimpleGraph.fromRel_adj]
    rw [cyc_fixed (x' := fun i j => x' (i, j)) (y' := fun i j => y' (i, j)) hs,
      cyc_fixed (x' := fun i j => x' (i, j)) (y' := fun i j => y' (i, j)) hs.symm]
  inp_alice x y y' v hv := by
    funext w
    simp only [cycInp, Prod.mk.injEq]
    exact ⟨decide_eq_decide.2 (cyc_indep_y (Or.inl hv)),
      decide_eq_decide.2 (cyc_indep_y (Or.inr hv))⟩
  inp_bob x x' y v hv := by
    funext w
    simp only [cycInp, Prod.mk.injEq]
    exact ⟨decide_eq_decide.2 (cyc_indep_x (Or.inl hv)),
      decide_eq_decide.2 (cyc_indep_x (Or.inr hv))⟩

instance {L : ℕ} (x y : Idx (L + 1) × Idx (L + 1) → Bool) :
    DecidableRel ((cycFamily L).G x y).Adj :=
  inferInstanceAs (DecidableRel (cycNet L x y).Adj)

/-- **Theorem 2.3** (deterministic, decision version). If a deterministic CONGEST algorithm with
`B`-bit messages decides in `T` rounds, on every network `D'_{x,y}`, whether the digraph has a
directed Hamiltonian cycle, then `k² ≤ 2 T (24 log k + 2) B + 2` (`k = 2 ^ (L + 1)`). -/
theorem theorem_2_3 {L : ℕ} {σ : Type*} {B : ℕ}
    (A : Algorithm (Option (HV (L + 1))) (Option (HV (L + 1)) → Bool × Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx (L + 1) × Idx (L + 1) → Bool,
      A.Accepts (cycNet L x y) (cycInp L x y) T ↔
        HasHamCycle (dCycArc L (fun i j => x (i, j)) (fun i j => y (i, j)))) :
    4 ^ (L + 1) ≤ T * (2 * ((24 * (L + 1) + 2) * B)) + 2 := by
  have h := (cycFamily L).not_disj_lowerBound A T fun x y => by
    change A.Accepts (cycNet L x y) (cycInp L x y) T ↔ _
    rw [hA x y, hamCycle_iff_not_disj]
    simp [Protocol.disj]
  have hc : Fintype.card (Idx (L + 1) × Idx (L + 1)) = 4 ^ (L + 1) := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  refine h.trans ?_
  have : (cycFamily L).Ecut.card ≤ 24 * (L + 1) + 2 := card_cycCut
  gcongr

end HardnessOptimization.HamPath
