import Papers.PODC2022.ConsensusFromSwap.Valency

/-!
# Readable swap objects: basic facts

Algorithms whose objects are all readable swap objects with values in `D`
(`T = fun _ => rswapObj D d₀`).
-/

namespace ConsensusFromSwap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {D : Type} {d₀ : D} {P : Type} [DecidableEq P]
  {A : Alg (fun _ : ι => rswapObj D d₀) P Bool}

/-- A process poised to `Swap` covers the object. -/
lemma covers_of_swap {C : Cfg A} {p : P} {i : ι} {w : D} {k : D → A.L}
    (h : A.act (C.loc p) = .access i (RSOp.swap w) k) : C.Covers p i :=
  ⟨RSOp.swap w, k, h, fun _ _ => rfl⟩

lemma step_swap_mem {C : Cfg A} {p : P} {i : ι} {w : D} {k : D → A.L}
    (h : A.act (C.loc p) = .access i (RSOp.swap w) k) (j : ι) :
    (C.step p).mem j = if j = i then w else C.mem j := by
  rw [C.step_of_access h]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

lemma step_swap_mem_self {C : Cfg A} {p : P} {i : ι} {w : D} {k : D → A.L}
    (h : A.act (C.loc p) = .access i (RSOp.swap w) k) : (C.step p).mem i = w := by
  rw [step_swap_mem h]; simp

lemma step_read_mem {C : Cfg A} {p : P} {i : ι} {k : D → A.L}
    (h : A.act (C.loc p) = .access i RSOp.read k) : (C.step p).mem = C.mem := by
  rw [C.step_of_access h]
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- If the value of `B` after `j` solo steps of `p` differs from its value at the start, then `p`
swapped exactly this value into `B` at some step `t < j`. -/
lemma exists_swap_solo (E : Cfg A) (p : P) (B : ι) :
    ∀ j, (run E (solo p j)).mem B ≠ E.mem B →
      ∃ t < j, ∃ k, A.act ((run E (solo p t)).loc p) =
        .access B (RSOp.swap ((run E (solo p j)).mem B)) k := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hne
    set G := run E (solo p j)
    have hG : run E (solo p (j + 1)) = G.step p := by rw [solo_succ, run_concat]
    rw [hG] at hne ⊢
    by_cases hch : (G.step p).mem B = G.mem B
    · rw [hch] at hne ⊢
      obtain ⟨t, ht, k, hk⟩ := ih hne
      exact ⟨t, by omega, k, hk⟩
    · rcases G.dec_or_poised p with hd | ⟨i, o, k, hpa⟩
      · exact absurd (by rw [G.step_of_dec hd]) hch
      · by_cases hiB : i = B
        · subst hiB
          cases o with
          | read => exact absurd (by rw [step_read_mem hpa]) hch
          | swap w =>
            refine ⟨j, by omega, k, ?_⟩
            rw [step_swap_mem hpa]
            simpa using hpa
        · exact absurd (G.step_mem_other ⟨o, k, hpa⟩ (Ne.symm hiB)) hch

/-- In a block update by processes covering distinct objects, the value of a covered object
afterwards is the value swapped in by its covering process. -/
lemma block_mem_swap {C : Cfg A} {cs : List (P × ι)} (hC : Covering C cs)
    (hnd : (cs.map Prod.snd).Nodup) {c : P × ι} (hc : c ∈ cs) {w : D} {k : D → A.L}
    (hw : A.act (C.loc c.1) = .access c.2 (RSOp.swap w) k) :
    (run C (block cs)).mem c.2 = w := by
  induction cs generalizing C with
  | nil => simp at hc
  | cons c' cs ih =>
    obtain ⟨p, i⟩ := c'
    have hnd1 := hC.1
    simp only [List.map_cons, List.nodup_cons] at hnd1 hnd
    have hnot : ∀ c ∈ cs, c.1 ≠ p := fun c hc h => hnd1.1 (h ▸ List.mem_map_of_mem hc)
    have hnoti : ∀ c ∈ cs, c.2 ≠ i := fun c hc h => hnd.1 (h ▸ List.mem_map_of_mem hc)
    have hCs : Covering (C.step p) cs := ⟨hnd1.2, fun c hc => (hC.2 c (by simp [hc])).of_loc
      (C.step_loc_other (hnot c hc))⟩
    simp only [block, List.map_cons, run_cons]
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · have e1 := run_block_mem_other hCs hnoti
      simp only [block] at e1
      rw [e1]
      exact step_swap_mem_self hw
    · have := ih hCs hnd.2 hc (by rw [C.step_loc_other (hnot c hc)]; exact hw)
      simpa [block] using this

/-- Removing the pairs with object `B` removes at most one pair if the objects are distinct. -/
lemma length_filter_ne {cs : List (P × ι)} (hnd : (cs.map Prod.snd).Nodup) (B : ι) :
    cs.length ≤ (cs.filter (fun c => c.2 ≠ B)).length + 1 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hc : c.2 = B
    · have : cs.filter (fun c => c.2 ≠ B) = cs := by
        rw [List.filter_eq_self]
        intro c' hc'
        simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        intro h
        exact hnd.1 (hc ▸ h ▸ List.mem_map_of_mem hc')
      rw [List.filter_cons_of_neg (by simpa using hc), this]
      simp
    · rw [List.filter_cons_of_pos (by simpa using hc)]
      simp only [List.length_cons]
      have := ih hnd.2
      omega

/-! ## The process sets of Section 5 -/

section Sets

variable (q₀ q₁ : P) (ps : List P)

/-- `Q ∪ P_i`, where `Q = {q₀, q₁}` and `P_i` are the processes of `ps` from position `i` on. -/
def RS (i : ℕ) : Set P := {r | r = q₀ ∨ r = q₁ ∨ r ∈ ps.drop i}

variable {q₀ q₁ ps}

lemma Q_sub_RS (i : ℕ) : ({q₀, q₁} : Set P) ⊆ RS q₀ q₁ ps i := by
  intro r hr
  rcases hr with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

lemma RS_mono {i i' : ℕ} (h : i ≤ i') : RS q₀ q₁ ps i' ⊆ RS q₀ q₁ ps i := by
  rintro r (hr | hr | hr)
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)
  · refine Or.inr (Or.inr ?_)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← List.drop_drop] at hr
    exact List.mem_of_mem_drop hr

lemma RS_succ {i : ℕ} (hi : i < ps.length) :
    RS q₀ q₁ ps i = insert ps[i] (RS q₀ q₁ ps (i + 1)) := by
  ext r
  simp only [RS, Set.mem_insert_iff, Set.mem_ofPred_eq, List.drop_eq_getElem_cons hi,
    List.mem_cons]
  tauto

lemma not_mem_RS_succ (hnd : (q₀ :: q₁ :: ps).Nodup) {i : ℕ} (hi : i < ps.length) :
    ps[i] ∉ RS q₀ q₁ ps (i + 1) := by
  simp only [List.nodup_cons] at hnd
  rintro (h | h | h)
  · exact hnd.1 (List.mem_cons_of_mem _ (by rw [← h]; exact List.getElem_mem hi))
  · exact hnd.2.1 (by rw [← h]; exact List.getElem_mem hi)
  · have h2 := hnd.2.2
    rw [← List.take_append_drop (i + 1) ps] at h2
    exact List.disjoint_of_nodup_append h2
      (List.mem_take_iff_getElem.2 ⟨i, by simp; omega, rfl⟩) h

lemma not_mem_RS_of_take (hnd : (q₀ :: q₁ :: ps).Nodup) {i : ℕ} {r : P} (hr : r ∈ ps.take i) :
    r ∉ RS q₀ q₁ ps i := by
  simp only [List.nodup_cons] at hnd
  have hrps : r ∈ ps := List.mem_of_mem_take hr
  rintro (h | h | h)
  · exact hnd.1 (List.mem_cons_of_mem _ (h ▸ hrps))
  · exact hnd.2.1 (h ▸ hrps)
  · have h2 := hnd.2.2
    rw [← List.take_append_drop i ps] at h2
    exact List.disjoint_of_nodup_append h2 hr h

lemma getElem_mem_take_succ {i : ℕ} (hi : i < ps.length) : ps[i] ∈ ps.take (i + 1) :=
  List.mem_take_iff_getElem.2 ⟨i, by simp; omega, rfl⟩

lemma take_sub_take_succ {i : ℕ} {r : P} (h : r ∈ ps.take i) : r ∈ ps.take (i + 1) := by
  rw [List.take_add_one]; exact List.mem_append_left _ h

end Sets

end ConsensusFromSwap
