import Podc.Computability.Distributed.SharedMemory.Awareness

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/AwarenessRound.lean

/-!
# One round of steps at most triples awareness

Lemma 1 of Hendler–Khait (PODC'14), following Attiya–Hendler: given an execution in which all
awareness and familiarity sets have at most `B` elements, and a set `T` of processes each poised to
access a read/write/CAS base object, the steps of `T` can be scheduled (each process exactly once)
so that afterwards all awareness and familiarity sets have at most `3 B` elements.

The schedule: first all reads and all CAS that do not change the value (w.r.t. the current
memory), then all writes, then all CAS that would change the value.
-/

namespace Cslib.SharedMemory.Awareness

open Cslib.SharedMemory

variable {A : ObjSpec} {ι P L V : Type} [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}
  {I : Impl A (RWC ι V v₀) P L}

/-- All awareness and familiarity sets have at most `B` elements. -/
def Bounded (G : Ghost P ι V) (B : ℕ) : Prop :=
  (∀ q, (G.aw q).card ≤ B) ∧ ∀ i, (G.F i).card ≤ B

/-- Running a list of distinct processes, one step each, under a step invariant. -/
lemma arunFrom_map_tau
    (Q : Config A (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop) (l : List P) :
    ∀ (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V) (D : Finset P), l.Nodup →
      (∀ p ∈ l, p ∉ D) → Q C G D →
      (∀ C G D p, Q C G D → p ∉ D → p ∈ l →
        ∃ C', I.step C (.tau p) = some C' ∧ Q C' (gstep I C G (.tau p)) (insert p D)) →
      ∃ C' G', arunFrom I (C, G) (l.map .tau) = some (C', G') ∧ Q C' G' (D ∪ l.toFinset) := by
  induction l with
  | nil => intro C G D _ _ hQ _; exact ⟨C, G, rfl, by simpa using hQ⟩
  | cons p l ih =>
    intro C G D hnd hD hQ hst
    obtain ⟨C₁, hs, hQ₁⟩ := hst C G D p hQ (hD p List.mem_cons_self) List.mem_cons_self
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨C', G', h1, h2⟩ := ih C₁ (gstep I C G (.tau p)) (insert p D) hnd'.2
      (fun q hq hqD => by
        rcases Finset.mem_insert.1 hqD with rfl | hqD
        · exact hnd'.1 hq
        · exact hD q (List.mem_cons_of_mem _ hq) hqD)
      hQ₁ (fun C G D q h1 h2 h3 => hst C G D q h1 h2 (List.mem_cons_of_mem _ h3))
    refine ⟨C', G', ?_, ?_⟩
    · simp only [List.map_cons, arunFrom_cons]
      rw [show astep I (C, G) (.tau p) = some (C₁, gstep I C G (.tau p)) from
        (astep_eq_some I).2 ⟨hs, rfl⟩]
      exact h1
    · have : insert p D ∪ l.toFinset = D ∪ (p :: l).toFinset := by
        ext x; simp [or_left_comm]
      rwa [this] at h2

section Round

variable (C₀ : Config A (RWC ι V v₀) P L) (G₀ : Ghost P ι V) (T : Finset P)

/-- Processes of `T` that have not stepped yet are unchanged. -/
def Fresh (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V) (D : Finset P) : Prop :=
  ∀ q ∈ T, q ∉ D → C.loc q = C₀.loc q ∧ C.pend q = C₀.pend q ∧ G.aw q = G₀.aw q

/-- `p` is poised to write. -/
def IsW (p : P) : Prop := ∃ i v k, I.act p (C₀.loc p) = .access i (.write v) k

/-- `p` is poised to apply a CAS that changes the value of its object. -/
def IsC (p : P) : Prop :=
  ∃ i a b k, I.act p (C₀.loc p) = .access i (.cas a b) k ∧ C₀.mem i = a ∧ b ≠ a

variable {C₀ G₀ T}

lemma fresh_step {C C' : Config A (RWC ι V v₀) P L} {G : Ghost P ι V} {D : Finset P} {p : P}
    (hF : Fresh C₀ G₀ T C G D) (hs : I.step C (.tau p) = some C') :
    Fresh C₀ G₀ T C' (gstep I C G (.tau p)) (insert p D) := by
  intro q hq hqD
  have hpq : p ≠ q := fun h => hqD (h ▸ Finset.mem_insert_self _ _)
  have h1 := Impl.step_other hs (q := q) (by simpa [Label.proc] using hpq)
  have h2 := (gstep_aw (I := I) C G (.tau p) q).2 (by simpa [Label.proc] using hpq)
  obtain ⟨a, b, c⟩ := hF q hq (fun h => hqD (Finset.mem_insert_of_mem h))
  exact ⟨h1.1.trans a, h1.2.trans b, h2.trans c⟩

lemma card_union_le_add {s t : Finset P} {a b : ℕ} (hs : s.card ≤ a) (ht : t.card ≤ b) :
    (s ∪ t).card ≤ a + b := (Finset.card_union_le s t).trans (Nat.add_le_add hs ht)

/-- **Lemma 1 of Hendler–Khait (PODC'14).** One step of each process of `T` can be scheduled so
that the maximal size of awareness and familiarity sets at most triples. -/
theorem exists_round {α : List (Label P A)} (h : arun I α = some (C₀, G₀))
    (hT : ∀ p ∈ T, C₀.pend p ≠ none ∧ ∃ i o k, I.act p (C₀.loc p) = .access i o k)
    {B : ℕ} (hB : Bounded G₀ B) :
    ∃ l : List P, l.Perm T.toList ∧ ∃ C' G', arunFrom I (C₀, G₀) (l.map .tau) = some (C', G') ∧
      Bounded G' (3 * B) := by
  classical
  have hI := arun_inv h
  let l1 := T.toList.filter (fun p => decide (¬ IsW (I := I) C₀ p ∧ ¬ IsC (I := I) C₀ p))
  let l2 := T.toList.filter (fun p => decide (IsW (I := I) C₀ p))
  let l3 := T.toList.filter (fun p => decide (IsC (I := I) C₀ p))
  have hWC : ∀ p, IsW (I := I) C₀ p → ¬ IsC (I := I) C₀ p := by
    rintro p ⟨i, v, k, h1⟩ ⟨i', a, b, k', h2, -⟩
    rw [h1] at h2; cases h2
  have hnd : (l1 ++ l2 ++ l3).Nodup := by
    have hT' := T.nodup_toList
    refine List.Nodup.append (List.Nodup.append (hT'.filter _) (hT'.filter _) ?_)
      (hT'.filter _) ?_
    · intro x hx1 hx2
      simp only [l1, l2, List.mem_filter, decide_eq_true_eq] at hx1 hx2
      exact hx1.2.1 hx2.2
    · intro x hx1 hx2
      simp only [l1, l2, l3, List.mem_append, List.mem_filter, decide_eq_true_eq] at hx1 hx2
      rcases hx1 with hx1 | hx1
      · exact hx1.2.2 hx2.2
      · exact hWC x hx1.2 hx2.2
  have hperm : (l1 ++ l2 ++ l3).Perm T.toList := by
    rw [List.perm_ext_iff_of_nodup hnd T.nodup_toList]
    intro x
    simp only [l1, l2, l3, List.mem_append, List.mem_filter, decide_eq_true_eq]
    tauto
  refine ⟨l1 ++ l2 ++ l3, hperm, ?_⟩
  -- common facts
  have hTl : ∀ p ∈ l1 ++ l2 ++ l3, p ∈ T := fun p hp =>
    Finset.mem_toList.1 (hperm.subset hp)
  have hF0 : Fresh C₀ G₀ T C₀ G₀ ∅ := fun q _ _ => ⟨rfl, rfl, rfl⟩
  -- phase 1: reads and value-preserving CAS
  let Q1 : Config A (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop := fun C G D =>
    Fresh C₀ G₀ T C G D ∧ C.mem = C₀.mem ∧ G.hist = G₀.hist ∧ ∀ q, (G.aw q).card ≤ 2 * B
  obtain ⟨C₁, G₁, hr1, hQ1⟩ := arunFrom_map_tau (I := I) Q1 l1 C₀ G₀ ∅
    (hnd.sublist (List.sublist_append_left _ _ |>.trans (List.sublist_append_left _ _)))
    (by simp) ⟨hF0, rfl, rfl, fun q => (hB.1 q).trans (by omega)⟩ (by
      intro C G D p ⟨hF, hm, hh, haw⟩ hpD hpl
      have hpT : p ∈ T := hTl p (List.mem_append_left _ (List.mem_append_left _ hpl))
      obtain ⟨hloc, hpend, hawp⟩ := hF p hpT hpD
      obtain ⟨hpend0, i, o, k, hact0⟩ := hT p hpT
      have hcls : ¬ IsW (I := I) C₀ p ∧ ¬ IsC (I := I) C₀ p := by
        have := hpl; simp only [l1, List.mem_filter, decide_eq_true_eq] at this; exact this.2
      have hact : I.act p (C.loc p) = .access i o k := by rw [hloc]; exact hact0
      have hpend' : C.pend p ≠ none := by rw [hpend]; exact hpend0
      refine ⟨_, Impl.step_tau_eq_some hpend' hact, fresh_step hF (Impl.step_tau_eq_some hpend' hact),
        ?_, ?_, ?_⟩
      · rw [hm]
        cases o with
        | read => simp
        | write v => exact absurd ⟨i, v, k, hact0⟩ hcls.1
        | cas a b =>
          funext j
          by_cases hj : j = i
          · subst hj
            simp only [Function.update_self]
            by_cases hc : C₀.mem j = a
            · have hb : b = a := by
                by_contra hb
                exact hcls.2 ⟨j, a, b, k, hact0, hc, hb⟩
              simp [hc, hb]
            · simp [hc]
          · simp [Function.update_of_ne hj]
      · cases o with
        | read => rw [gstep_tau_read hact]; exact hh
        | write v => exact absurd ⟨i, v, k, hact0⟩ hcls.1
        | cas a b =>
          rw [gstep_tau_cas hact]
          have : ¬ (C.mem i = a ∧ b ≠ a) := fun ⟨h1, h2⟩ =>
            hcls.2 ⟨i, a, b, k, hact0, hm ▸ h1, h2⟩
          simp [this, hh]
      · intro q
        have hFi : (G.F i).card ≤ B := by
          simp only [Ghost.F, hh]; exact hB.2 i
        have hawp' : (G.aw p).card ≤ B := by rw [hawp]; exact hB.1 p
        cases o with
        | read =>
          rw [gstep_tau_read hact]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self]
            exact (card_union_le_add hawp' hFi).trans (by omega)
          · simp only [Function.update_of_ne hq]; exact haw q
        | write v => exact absurd ⟨i, v, k, hact0⟩ hcls.1
        | cas a b =>
          rw [gstep_tau_cas hact]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self]
            exact (card_union_le_add hawp' hFi).trans (by omega)
          · simp only [Function.update_of_ne hq]; exact haw q)
  obtain ⟨hF1, hm1, hh1, haw1⟩ := hQ1
  -- phase 2: writes
  let Q2 : Config A (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop := fun C G D =>
    Fresh C₀ G₀ T C G D ∧ (∀ q, (G.aw q).card ≤ 2 * B) ∧ ∀ i, (G.F i).card ≤ B
  obtain ⟨C₂, G₂, hr2, hQ2⟩ := arunFrom_map_tau (I := I) Q2 l2 C₁ G₁ (∅ ∪ l1.toFinset)
    (hnd.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)))
    (by
      intro p hp2 hp1
      simp only [Finset.empty_union, List.mem_toFinset] at hp1
      exact List.disjoint_of_nodup_append
        (hnd.sublist (List.sublist_append_left _ _)) hp1 hp2)
    ⟨hF1, haw1, fun i => by simp only [Ghost.F, hh1]; exact hB.2 i⟩ (by
      intro C G D p ⟨hF, haw, hFb⟩ hpD hpl
      have hpT : p ∈ T := hTl p (List.mem_append_left _ (List.mem_append_right _ hpl))
      obtain ⟨hloc, hpend, hawp⟩ := hF p hpT hpD
      obtain ⟨hpend0, -⟩ := hT p hpT
      obtain ⟨i, v, k, hact0⟩ : IsW (I := I) C₀ p := by
        have := hpl; simp only [l2, List.mem_filter, decide_eq_true_eq] at this; exact this.2
      have hact : I.act p (C.loc p) = .access i (.write v) k := by rw [hloc]; exact hact0
      have hpend' : C.pend p ≠ none := by rw [hpend]; exact hpend0
      refine ⟨_, Impl.step_tau_eq_some hpend' hact, fresh_step hF (Impl.step_tau_eq_some hpend' hact),
        ?_, ?_⟩
      · rw [gstep_tau_write hact]; exact haw
      · intro j
        rw [gstep_tau_write hact]
        by_cases hj : j = i
        · subst hj; simp only [Ghost.F, Function.update_self, topAw_cons]
          rw [hawp]; exact hB.1 p
        · simp only [Ghost.F, Function.update_of_ne hj]; exact hFb j)
  obtain ⟨hF2, haw2, hFb2⟩ := hQ2
  -- phase 3: value-changing CAS
  let Q3 : Config A (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop := fun C G D =>
    Fresh C₀ G₀ T C G D ∧ (∀ q, (G.aw q).card ≤ 3 * B) ∧
      ∀ i, (G.F i).card ≤ 2 * B ∧ (C.mem i = C₀.mem i → (G.F i).card ≤ B)
  obtain ⟨C₃, G₃, hr3, hQ3⟩ := arunFrom_map_tau (I := I) Q3 l3 C₂ G₂
    (∅ ∪ l1.toFinset ∪ l2.toFinset) (hnd.sublist (List.sublist_append_right _ _))
    (by
      intro p hp3 hp12
      simp only [Finset.empty_union, Finset.mem_union, List.mem_toFinset] at hp12
      exact List.disjoint_of_nodup_append hnd (List.mem_append.2 hp12) hp3)
    ⟨hF2, fun q => (haw2 q).trans (by omega),
      fun i => ⟨(hFb2 i).trans (by omega), fun _ => hFb2 i⟩⟩ (by
      intro C G D p ⟨hF, haw, hFb⟩ hpD hpl
      have hpT : p ∈ T := hTl p (List.mem_append_right _ hpl)
      obtain ⟨hloc, hpend, hawp⟩ := hF p hpT hpD
      obtain ⟨hpend0, -⟩ := hT p hpT
      obtain ⟨i, a, b, k, hact0, ha, hb⟩ : IsC (I := I) C₀ p := by
        have := hpl; simp only [l3, List.mem_filter, decide_eq_true_eq] at this; exact this.2
      have hact : I.act p (C.loc p) = .access i (.cas a b) k := by rw [hloc]; exact hact0
      have hpend' : C.pend p ≠ none := by rw [hpend]; exact hpend0
      have hawp' : (G.aw p).card ≤ B := by rw [hawp]; exact hB.1 p
      refine ⟨_, Impl.step_tau_eq_some hpend' hact, fresh_step hF (Impl.step_tau_eq_some hpend' hact),
        ?_, ?_⟩
      · intro q
        rw [gstep_tau_cas hact]
        by_cases hq : q = p
        · subst hq; simp only [Function.update_self]
          exact (card_union_le_add hawp' (hFb i).1).trans (by omega)
        · simp only [Function.update_of_ne hq]; exact haw q
      · intro j
        rw [gstep_tau_cas hact]
        by_cases hc : C.mem i = a
        · -- the CAS succeeds and changes the value
          have hbF : (G.aw p ∪ G.F i).card ≤ 2 * B :=
            (card_union_le_add hawp' ((hFb i).2 (hc.trans ha.symm))).trans (by omega)
          simp only [hc, ne_eq, hb, not_false_eq_true, and_self, if_true]
          by_cases hj : j = i
          · subst hj
            simp only [Ghost.F, Function.update_self, topAw_cons, hc, if_true]
            refine ⟨hbF, fun h' => absurd (h'.trans ha) hb⟩
          · simp only [Ghost.F, Function.update_of_ne hj] at hFb ⊢
            exact hFb j
        · have : ¬ (C.mem i = a ∧ b ≠ a) := fun h => hc h.1
          simp only [this, if_false]
          by_cases hj : j = i
          · subst hj
            refine ⟨(hFb j).1, fun h' => ?_⟩
            simp only [Function.update_self] at h'
            rw [if_neg hc] at h'
            exact (hFb j).2 h'
          · simp only [Function.update_of_ne hj]; exact hFb j)
  obtain ⟨-, haw3, hFb3⟩ := hQ3
  refine ⟨C₃, G₃, ?_, haw3, fun i => (hFb3 i).1.trans (by omega)⟩
  simp only [List.map_append, arunFrom_append, hr1, Option.bind_some, hr2, hr3]

end Round

end Cslib.SharedMemory.Awareness
