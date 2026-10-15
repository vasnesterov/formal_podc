import Papers.PODC2025.StrangerFreeTasks.Alg1

/-!
# Algorithm 1 is obstruction-free

A process running solo from *any* configuration (reachable or not) returns. The solo run of `p`
is described by the function `soloF` on (local state of `p`, memory).
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] (k : ℕ)

/-- Memory of Algorithm 1. -/
abbrev Mem (P : Type) (k : ℕ) := Fin (k + 1) → Triple P

/-- One solo step of `p` on (local state, memory), for phases `wr`, `col1`, `col2`. -/
def soloF (p : P) (s : Loc P k × Mem P k) : Loc P k × Mem P k :=
  match s.1.phase with
  | .wr => ({ s.1 with phase := .col1, j := 0, i := s.1.i + 1, seq := s.1.seq + 1 },
      Function.update s.2 s.1.i ⟨some p, s.1.seq, s.1.seen⟩)
  | .col1 => (afterCol1 k s.1 (s.2 s.1.j), s.2)
  | .col2 => (afterCol2 k s.1 (s.2 s.1.j), s.2)
  | _ => s

lemma soloStep_eq_soloF (p : P) (C : Config (laObj P) (Regs P k) P (Loc P k))
    (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .wr ∨ (C.loc p).phase = .col1 ∨
      (C.loc p).phase = .col2) :
    (alg1 k).soloStep p C = { C with loc := Function.update C.loc p (soloF k p (C.loc p, C.mem)).1,
                                     mem := (soloF k p (C.loc p, C.mem)).2 } := by
  rcases hph with h | h | h <;>
    simp [Impl.soloStep, Impl.nextLabel, Impl.step, alg1, soloF, h, hp]

lemma soloStep_pend_of_done (p : P) (C : Config (laObj P) (Regs P k) P (Loc P k))
    (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .done ∨ (C.loc p).phase = .idle) :
    ((alg1 k).soloStep p C).pend p = none := by
  rcases hph with h | h <;>
    simp [Impl.soloStep, Impl.nextLabel, Impl.step, alg1, h, hp] <;>
    split_ifs with hh <;> first | exact absurd rfl hh | simp

/-! ### Solo dynamics on (local state, memory) -/

variable {k}

/-- The solo run of `p` from `s` reaches phase `done`. -/
def Term (p : P) (s : Loc P k × Mem P k) : Prop := ∃ n, ((soloF k p)^[n] s).1.phase = .done

lemma Term.of_iterate {p : P} {s : Loc P k × Mem P k} (t : ℕ) (h : Term p ((soloF k p)^[t] s)) :
    Term p s := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + t, by rwa [Function.iterate_add_apply]⟩

lemma soloF_wr (p : P) (l : Loc P k) (m : Mem P k) (h : l.phase = .wr) :
    soloF k p (l, m) = ({ l with phase := .col1, j := 0, i := l.i + 1, seq := l.seq + 1 },
      Function.update m l.i ⟨some p, l.seq, l.seen⟩) := by
  simp [soloF, h]

lemma soloF_col1 (p : P) (l : Loc P k) (m : Mem P k) (h : l.phase = .col1) :
    soloF k p (l, m) = (afterCol1 k l (m l.j), m) := by
  simp [soloF, h]

lemma soloF_col2 (p : P) (l : Loc P k) (m : Mem P k) (h : l.phase = .col2) :
    soloF k p (l, m) = (afterCol2 k l (m l.j), m) := by
  simp [soloF, h]

lemma fin_eq_of_val_eq_last {r j : Fin (k + 1)} (hj : j.val = k) (h : j ≤ r) : r = j := by
  have := r.isLt; rw [Fin.le_def] at h; ext; omega

lemma fin_le_iff_succ {r j : Fin (k + 1)} (hj : j.val < k) :
    j ≤ r ↔ r = j ∨ j + 1 ≤ r := by
  have hv : (j + 1).val = j.val + 1 := Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)
  simp only [Fin.le_def, hv, Fin.ext_iff]; omega

/-- The rest of the first collect. -/
lemma col1_run (p : P) (m : Mem P k) : ∀ t (l : Loc P k), l.phase = .col1 → l.j.val + t = k →
    ∃ l', (soloF k p)^[t + 1] (l, m) = (l', m) ∧ l'.phase = .col2 ∧ l'.j = 0 ∧ l'.snap = true ∧
      l'.i = l.i ∧ l'.seq = l.seq ∧ (∀ r, l.j ≤ r → l'.collect r = m r) ∧
      (∀ r, r < l.j → l'.collect r = l.collect r) ∧
      (∀ x, x ∈ l'.seen ↔ x ∈ l.seen ∨ ∃ r, l.j ≤ r ∧ x ∈ (m r).seen) := by
  intro t
  induction t with
  | zero =>
    intro l hl hj
    simp only [Nat.add_zero] at hj
    refine ⟨_, by rw [Function.iterate_one, soloF_col1 p l m hl], ?_⟩
    simp only [afterCol1, hj, ↓reduceIte, true_and]
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun x => ?_⟩
    · rw [fin_eq_of_val_eq_last hj hr]; simp
    · simp [ne_of_lt hr]
    · simp only [Finset.mem_union]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨l.j, le_rfl, h⟩
      · rintro (h | ⟨r, hr, h⟩)
        · exact Or.inl h
        · rw [fin_eq_of_val_eq_last hj hr] at h; exact Or.inr h
  | succ t ih =>
    intro l hl hj
    have hjk : l.j.val ≠ k := by omega
    have hv : (l.j + 1).val = l.j.val + 1 :=
      Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)
    obtain ⟨l', h1, h2, h3, h4, h5, h6, h7, h9, h8⟩ := ih
      { l with collect := Function.update l.collect l.j (m l.j), seen := l.seen ∪ (m l.j).seen,
               j := l.j + 1 } hl (by simp only [hv]; omega)
    refine ⟨l', ?_, h2, h3, h4, h5, h6, fun r hr => ?_, fun r hr => ?_, fun x => ?_⟩
    · rw [Function.iterate_succ_apply, soloF_col1 p l m hl]
      simpa [afterCol1, hjk] using h1
    · rcases (fin_le_iff_succ (by omega)).1 hr with rfl | hr'
      · rw [h9 l.j (by rw [Fin.lt_def, hv]; omega)]; simp
      · exact h7 r hr'
    · rw [h9 r (lt_trans hr (by rw [Fin.lt_def, hv]; omega))]
      simp [ne_of_lt hr]
    · rw [h8]
      simp only [Finset.mem_union]
      constructor
      · rintro ((h | h) | ⟨r, hr, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨l.j, le_rfl, h⟩
        · exact Or.inr ⟨r, le_trans (by rw [Fin.le_def, hv]; omega) hr, h⟩
      · rintro (h | ⟨r, hr, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases (fin_le_iff_succ (by omega)).1 hr with rfl | hr'
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨r, hr', h⟩

/-- The rest of the second collect, ending with the decision. -/
lemma col2_run (p : P) (m : Mem P k) : ∀ t (l : Loc P k), l.phase = .col2 → l.j.val + t = k →
    ∃ l', (soloF k p)^[t + 1] (l, m) = (decision k l', m) ∧ l'.i = l.i ∧
      l'.collect = l.collect ∧
      (l'.snap = true ↔ l.snap = true ∧ ∀ r, l.j ≤ r → m r = l.collect r) ∧
      (∀ x, x ∈ l'.seen ↔ x ∈ l.seen ∨ ∃ r, l.j ≤ r ∧ x ∈ (l.collect r).seen) := by
  intro t
  induction t with
  | zero =>
    intro l hl hj
    simp only [Nat.add_zero] at hj
    refine ⟨{ l with snap := l.snap && decide (m l.j = l.collect l.j),
                     seen := l.seen ∪ (l.collect l.j).seen },
      by rw [Function.iterate_one, soloF_col2 p l m hl]; simp [afterCol2, hj], rfl, rfl,
      ?_, fun x => ?_⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun r hr => ?_⟩
        rw [fin_eq_of_val_eq_last hj hr]; exact h2
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2 _ le_rfl⟩
    · simp only [Finset.mem_union]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨l.j, le_rfl, h⟩
      · rintro (h | ⟨r, hr, h⟩)
        · exact Or.inl h
        · rw [fin_eq_of_val_eq_last hj hr] at h; exact Or.inr h
  | succ t ih =>
    intro l hl hj
    have hjk : l.j.val ≠ k := by omega
    have hv : (l.j + 1).val = l.j.val + 1 :=
      Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)
    obtain ⟨l', h1, h2, h3, h4, h5⟩ := ih
      { l with snap := l.snap && decide (m l.j = l.collect l.j),
               seen := l.seen ∪ (l.collect l.j).seen, j := l.j + 1 } hl (by simp only [hv]; omega)
    refine ⟨l', ?_, h2, h3, ?_, fun x => ?_⟩
    · rw [Function.iterate_succ_apply, soloF_col2 p l m hl]
      simpa [afterCol2, hjk] using h1
    · rw [h4]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun r hr => ?_⟩
        rcases (fin_le_iff_succ (by omega)).1 hr with rfl | hr'
        · exact h2
        · exact h3 r hr'
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2 _ le_rfl⟩, fun r hr => h2 r (le_trans (by rw [Fin.le_def, hv]; omega) hr)⟩
    · rw [h5]
      simp only [Finset.mem_union]
      constructor
      · rintro ((h | h) | ⟨r, hr, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨l.j, le_rfl, h⟩
        · exact Or.inr ⟨r, le_trans (by rw [Fin.le_def, hv]; omega) hr, h⟩
      · rintro (h | ⟨r, hr, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases (fin_le_iff_succ (by omega)).1 hr with rfl | hr'
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨r, hr', h⟩

lemma decision_cases (l : Loc P k) :
    (decision k l).phase = .done ∨ (decision k l = { l with phase := .wr } ∧
      ¬ (l.snap = true ∧ ∀ r, l.seen = (l.collect r).seen)) := by
  unfold decision
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, h2⟩

/-- One full solo iteration (write, two collects, decision) from phase `wr`. -/
lemma iter_wr (p : P) (l : Loc P k) (m : Mem P k) (h : l.phase = .wr) :
    ((soloF k p)^[2 * k + 3] (l, m)).1.phase = .done ∨
    ∃ l', (soloF k p)^[2 * k + 3] (l, m) = (l', Function.update m l.i ⟨some p, l.seq, l.seen⟩) ∧
      l'.phase = .wr ∧ l'.i = l.i + 1 ∧
      (∀ x, x ∈ l'.seen ↔ x ∈ l.seen ∨
        ∃ r, x ∈ ((Function.update m l.i ⟨some p, l.seq, l.seen⟩) r).seen) ∧
      ¬ ∀ r, l'.seen = ((Function.update m l.i ⟨some p, l.seq, l.seen⟩) r).seen := by
  generalize hm1 : Function.update m l.i ⟨some p, l.seq, l.seen⟩ = m1
  rw [show 2 * k + 3 = (k + 1) + ((k + 1) + 1) by omega,
    Function.iterate_add_apply (soloF k p) (k + 1) (k + 1 + 1),
    Function.iterate_succ_apply (soloF k p) (k + 1), soloF_wr p l m h, hm1]
  obtain ⟨l2, e2, p2, j2, s2, i2, -, c2, -, sn2⟩ := col1_run p m1 k
    { l with phase := .col1, j := 0, i := l.i + 1, seq := l.seq + 1 } rfl (by simp)
  rw [e2]
  obtain ⟨l3, e3, i3, c3, s3, sn3⟩ := col2_run p m1 k l2 p2 (by simp [j2])
  rw [e3]
  have hc : l2.collect = m1 := funext fun r => c2 r (Fin.zero_le r)
  have hseen : l3.seen = l2.seen := by
    ext x; rw [sn3 x, hc]
    constructor
    · rintro (hx | ⟨r, -, hx⟩)
      · exact hx
      · exact (sn2 x).2 (Or.inr ⟨r, Fin.zero_le _, hx⟩)
    · exact Or.inl
  have hsnap : l3.snap = true := s3.2 ⟨s2, fun r _ => by rw [hc]⟩
  rcases decision_cases l3 with hd | ⟨hd, hn⟩
  · left; exact hd
  · right
    refine ⟨_, by rw [hd], rfl, by simp [i3, i2], fun x => ?_,
      fun hall => hn ⟨hsnap, by rw [c3, hc]; exact hall⟩⟩
    show x ∈ l3.seen ↔ _
    rw [hseen, sn2 x]
    simp

/-- Cyclic distance from the writing position `i` forward to register `r`. -/
def cdist (i r : Fin (k + 1)) : ℕ :=
  if i.val ≤ r.val then r.val - i.val else r.val + (k + 1) - i.val

lemma cdist_lt (i r : Fin (k + 1)) : cdist i r < k + 1 := by
  have := r.isLt; have := i.isLt; unfold cdist; split_ifs <;> omega

lemma cdist_pos {r i : Fin (k + 1)} (h : r ≠ i) : 0 < cdist i r := by
  have h' : r.val ≠ i.val := fun e => h (Fin.ext e)
  have := r.isLt; have := i.isLt; unfold cdist; split_ifs <;> omega

lemma cdist_add_one {r i : Fin (k + 1)} (h : r ≠ i) : cdist (i + 1) r = cdist i r - 1 := by
  have hv : (i + 1).val = if i = Fin.last k then 0 else i.val + 1 := Fin.val_add_one i
  have h' : r.val ≠ i.val := fun e => h (Fin.ext e)
  have := r.isLt; have := i.isLt
  have hl : i = Fin.last k ↔ i.val = k := by simp [Fin.ext_iff]
  unfold cdist
  rw [hv]
  split_ifs at * <;> simp_all <;> omega

/-- Once every register holds a subset of `seen`, `seen` is stable, and every iteration writes
`seen` into the next register; registers with a different `seen` are within distance `n` of the
writing position. -/
lemma term_stable (p : P) : ∀ n (l : Loc P k) (m : Mem P k), l.phase = .wr →
    (∀ r, (m r).seen ⊆ l.seen) → (∀ r, (m r).seen ≠ l.seen → cdist l.i r < n) →
    Term p (l, m) := by
  intro n
  induction n with
  | zero =>
    intro l m hl hsub hbad
    rcases iter_wr p l m hl with hd | ⟨l', -, -, -, hs', hn'⟩
    · exact ⟨_, hd⟩
    · exfalso
      apply hn'
      intro r
      have hseq : l'.seen = l.seen := by
        ext x; rw [hs' x]
        constructor
        · rintro (h | ⟨r', h⟩)
          · exact h
          · by_cases hr : r' = l.i
            · rw [hr] at h; simpa using h
            · rw [Function.update_of_ne hr] at h; exact hsub r' h
        · exact Or.inl
      rw [hseq]
      by_cases hr : r = l.i
      · rw [hr]; simp
      · rw [Function.update_of_ne hr]
        by_contra hne
        have := hbad r (Ne.symm hne)
        omega
  | succ n ih =>
    intro l m hl hsub hbad
    rcases iter_wr p l m hl with hd | ⟨l', e, hp', hi', hs', -⟩
    · exact ⟨_, hd⟩
    · have hm1 : ∀ r, ((Function.update m l.i ⟨some p, l.seq, l.seen⟩) r).seen ⊆ l.seen := by
        intro r
        by_cases hr : r = l.i
        · rw [hr]; simp
        · rw [Function.update_of_ne hr]; exact hsub r
      have hseq : l'.seen = l.seen := by
        ext x; rw [hs' x]
        constructor
        · rintro (h | ⟨r', h⟩)
          · exact h
          · exact hm1 r' h
        · exact Or.inl
      apply Term.of_iterate (2 * k + 3)
      rw [e]
      refine ih l' _ hp' (fun r => hseq ▸ hm1 r) (fun r hr => ?_)
      rw [hseq] at hr
      have hri : r ≠ l.i := by
        intro h; apply hr; rw [h]; simp
      rw [Function.update_of_ne hri] at hr
      have := hbad r hr
      have := cdist_pos hri
      rw [hi', cdist_add_one hri]
      omega

lemma term_wr (p : P) (l : Loc P k) (m : Mem P k) (hl : l.phase = .wr) : Term p (l, m) := by
  rcases iter_wr p l m hl with hd | ⟨l', e, hp', -, hs', -⟩
  · exact ⟨_, hd⟩
  · apply Term.of_iterate (2 * k + 3)
    rw [e]
    exact term_stable p (k + 1) l' _ hp' (fun r x hx => (hs' x).2 (Or.inr ⟨r, hx⟩))
      (fun r _ => cdist_lt l'.i r)

lemma term_col2 (p : P) (l : Loc P k) (m : Mem P k) (hl : l.phase = .col2) : Term p (l, m) := by
  obtain ⟨l', e, -⟩ := col2_run p m (k - l.j.val) l hl (by have := l.j.isLt; omega)
  rcases decision_cases l' with hd | ⟨hd, -⟩
  · exact ⟨_, by rw [e]; exact hd⟩
  · apply Term.of_iterate (k - l.j.val + 1)
    rw [e, hd]
    exact term_wr p _ m rfl

lemma term_col1 (p : P) (l : Loc P k) (m : Mem P k) (hl : l.phase = .col1) : Term p (l, m) := by
  obtain ⟨l', e, hp', -⟩ := col1_run p m (k - l.j.val) l hl (by have := l.j.isLt; omega)
  apply Term.of_iterate (k - l.j.val + 1)
  rw [e]
  exact term_col2 p l' m hp'

lemma term_of_ne_idle (p : P) (l : Loc P k) (m : Mem P k) (hl : l.phase ≠ .idle) :
    Term p (l, m) := by
  rcases h : l.phase with _ | _ | _ | _ | _
  · exact absurd h hl
  · exact term_wr p l m h
  · exact term_col1 p l m h
  · exact term_col2 p l m h
  · exact ⟨0, h⟩

/-! ### Back to configurations -/

lemma solo_returns_of_term (p : P) : ∀ n (C : Config (laObj P) (Regs P k) P (Loc P k)),
    C.pend p ≠ none → ((soloF k p)^[n] (C.loc p, C.mem)).1.phase = .done →
    ∃ N, (((alg1 k).soloStep p)^[N] C).pend p = none := by
  intro n
  induction n with
  | zero =>
    intro C hp hd
    exact ⟨1, soloStep_pend_of_done k p C hp (Or.inl hd)⟩
  | succ n ih =>
    intro C hp hd
    rcases h : (C.loc p).phase with _ | _ | _ | _ | _
    · exact ⟨1, soloStep_pend_of_done k p C hp (Or.inr h)⟩
    all_goals first
      | exact ⟨1, soloStep_pend_of_done k p C hp (Or.inl h)⟩
      | have e := soloStep_eq_soloF k p C hp (by simp [h])
        obtain ⟨N, hN⟩ := ih ((alg1 k).soloStep p C) (by rw [e]; exact hp)
          (by rw [e]; simpa [Function.iterate_succ_apply] using hd)
        exact ⟨N + 1, by rwa [Function.iterate_succ_apply]⟩

/-- **Algorithm 1 is obstruction-free**: from every configuration (reachable or not), a process
with a pending invocation that runs solo returns. (The paper claims wait-freedom, which fails
for `k ≥ 2`.) -/
theorem alg1_obstructionFree (k : ℕ) {P : Type} [DecidableEq P] :
    (alg1 (P := P) k).ObstructionFree := by
  intro C p _ hp
  by_cases h : (C.loc p).phase = .idle
  · exact ⟨1, soloStep_pend_of_done k p C hp (Or.inr h)⟩
  · obtain ⟨n, hn⟩ := term_of_ne_idle p (C.loc p) C.mem h
    exact solo_returns_of_term p n C hp hn

end Cslib.SharedMemory.StrangerFree
