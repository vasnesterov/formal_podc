import Papers.PODC2024.AnonymousCoverings.Stable

/-!
# The write–scan loop (Figure 1) and the eventual pattern (Theorem 4.8)

Figure 1 of the paper: each processor writes its view (the set of inputs it knows) to a register
it has not written in the current round-robin cycle, then reads all registers one by one, adding
the values read to its view, forever.

**Theorem 4.8** (`theorem_4_8`): in every infinite execution with at least as many registers as
processors, the stable views (views of live processors after stabilization, Definition 4.2) have
a least element: the stable-view graph (Definition 4.3: vertices = stable views, edges = strict
inclusion) is a DAG with a unique source (`theorem_4_8_unique_source`).

The hypothesis `card P ≤ card R` is needed: with fewer registers than processors two
non-communicating groups can coexist forever (`Counterexamples.lean`). The paper does not state
the number of registers in Section 4, but its proofs use `N` registers.
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R V : Type*} [Fintype P] [DecidableEq P] [DecidableEq R] [Fintype R] [DecidableEq V]

/-- **Figure 1** (the write–scan loop): the local data is the view, the written value is the
view, a read adds the value read to the view; the loop never stops. -/
def writeScan : Algo R (Finset V) (Finset V) where
  wr d := d
  rd d _ x := d ∪ x
  fin d := d
  stop _ := False

/-- Initial configuration: empty registers; each processor at the write label with view
`{input p}` and nothing written. -/
def initCfg {D : Type*} (d₀ : P → D) {X : Type*} (x₀ : X) : Cfg P R D X :=
  ⟨fun _ => ⟨x₀, none⟩, fun p => ⟨d₀ p, ∅, none⟩⟩

namespace Exec

variable (e : Exec (P := P) (writeScan (R := R) (V := V)))

omit [Fintype P] in
/-- In Figure 1 the view changes only by a read, which adds the value read. -/
theorem ws_view_succ (t : ℕ) (p : P) :
    (e.loc (t + 1) p).d = (e.loc t p).d ∨
      ∃ r, e.act t = .read p r ∧ (e.loc (t + 1) p).d = (e.loc t p).d ∪ (e.reg t r).val := by
  by_cases hm : e.Moves t p
  · obtain ⟨r, hr | hr⟩ := hm
    · left; rw [(e.write_spec hr).2.2.2.2]
    · right
      obtain ⟨S, -, -, hpost⟩ := e.read_spec hr
      refine ⟨r, hr, ?_⟩
      rw [hpost]; split_ifs <;> rfl
  · left; rw [e.loc_succ_of_not_moves hm]

omit [Fintype P] in
/-- In Figure 1 every action is a write or a read (nobody stops). -/
theorem ws_moves (t : ℕ) : e.Moves t (e.act t).proc := by
  have hs := e.step t
  generalize ha : e.act t = a at hs
  cases a with
  | write p r => exact ⟨r, Or.inl ha⟩
  | read p r => exact ⟨r, Or.inr ha⟩
  | idle p => exact absurd hs.2.1 (by simp [writeScan])

/-- Some processor is live. -/
theorem ws_exists_live : ∃ p, e.Live p := by
  by_contra h
  push Not at h
  obtain ⟨T, -, hT⟩ := Nat.eventually_forall_of_finite
    (fun p => e.eventually_not_moves_of_not_live (h p)) 0
  exact hT T le_rfl _ (e.ws_moves T)

variable {e} {input : P → V}

/-- The view hypotheses hold for Figure 1, with the bound `input '' P`. -/
theorem ws_viewSpec (he : e.cfg 0 = initCfg (fun p => ({input p} : Finset V)) ∅) :
    e.ViewSpec id id (univ.image input) := by
  have hinv : ∀ t, (∀ p, (e.loc t p).d ⊆ univ.image input) ∧
      (∀ r, (e.reg t r).val ⊆ univ.image input) := by
    intro t
    induction t with
    | zero =>
      simp only [loc, reg, he, initCfg]
      exact ⟨fun p => by simp, fun r => by simp⟩
    | succ t ih =>
      refine ⟨fun p => ?_, fun r => ?_⟩
      · rcases e.ws_view_succ t p with h | ⟨r, -, h⟩
        · rw [h]; exact ih.1 p
        · rw [h]; exact union_subset (ih.1 p) (ih.2 r)
      · by_cases hw : ∃ q, e.act t = .write q r
        · obtain ⟨q, hq⟩ := hw
          rw [(e.write_spec hq).2.2.2.1]; exact ih.1 q
        · push Not at hw
          rw [e.reg_succ_of_not_write hw]; exact ih.2 r
  refine ⟨fun t p => ?_, fun t p => (hinv t).1 p, fun d => rfl, fun t a r _ hr => ?_, fun r => ?_⟩
  · rcases e.ws_view_succ t p with h | ⟨r, -, h⟩
    · rw [h]
    · rw [h]; exact subset_union_left
  · refine ⟨t + 1, by omega, ?_⟩
    rcases e.ws_view_succ t a with h | ⟨r', hr', h⟩
    · obtain ⟨S, -, -, hpost⟩ := e.read_spec hr
      have : (e.loc (t + 1) a).d = (e.loc t a).d ∪ (e.reg t r).val := by
        rw [hpost]; split_ifs <;> rfl
      rw [this]; exact subset_union_right
    · rw [hr] at hr'; cases hr'; rw [h]; exact subset_union_right
  · simp [reg, he, initCfg]

end Exec

/-- **Definition 4.2.** `W` is a *stable view* of the execution if it is, from some time on, the
view of a live processor. -/
def IsStableView {D X : Type*} {A : Algo R D X} (e : Exec (P := P) A) (view : D → Finset V)
    (W : Finset V) : Prop :=
  ∃ p, e.Live p ∧ ∃ T, ∀ t ≥ T, view (e.loc t p).d = W

/-- **Theorem 4.8** (the eventual pattern). In every infinite execution of the write–scan loop
(Figure 1) with at least as many registers as processors, some stable view is contained in every
stable view. -/
theorem theorem_4_8 (hPR : Fintype.card P ≤ Fintype.card R) {input : P → V}
    (e : Exec (P := P) (writeScan (R := R) (V := V)))
    (he : e.cfg 0 = initCfg (fun p => ({input p} : Finset V)) ∅) :
    ∃ W₀, IsStableView e id W₀ ∧ ∀ W, IsStableView e id W → W₀ ⊆ W := by
  classical
  have hv := Exec.ws_viewSpec he
  obtain ⟨T₀, hst, -, hreg⟩ := Exec.exists_gst hv e.ws_exists_live
  set stab : P → Finset V := fun p => (e.loc T₀ p).d with hstab
  have hstable : ∀ W, IsStableView e id W → ∃ q, e.Live q ∧ stab q = W := by
    rintro W ⟨q, hq, T, hT⟩
    refine ⟨q, hq, ?_⟩
    have h1 := hT (max T T₀) (le_max_left _ _)
    have h2 := hst q (max T T₀) (le_max_right _ _)
    simp only [id] at h1 h2
    rw [← h1, h2]
  set L := univ.filter fun p => e.Live p
  obtain ⟨p₀, hp₀⟩ := e.ws_exists_live
  have hL : L.Nonempty := ⟨p₀, by simp [L, hp₀]⟩
  obtain ⟨p₁, hp₁L, hp₁min⟩ := exists_min_image L (fun p => (stab p).card) hL
  have hp₁ : e.Live p₁ := by simpa [L] using hp₁L
  have min₁ : ∀ x, e.Live x → stab x ⊆ stab p₁ → stab x = stab p₁ := fun x hx hsub =>
    eq_of_subset_of_card_le hsub (hp₁min x (by simp [L, hx]))
  refine ⟨stab p₁, ⟨p₁, hp₁, T₀, fun t ht => hst p₁ t ht⟩, fun W hW => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hstable W hW
  by_contra hnot
  set L' := L.filter fun p => stab p ⊆ stab q
  have hL' : L'.Nonempty := ⟨q, by simp [L', L, hq]⟩
  obtain ⟨p₂, hp₂L, hp₂min⟩ := exists_min_image L' (fun p => (stab p).card) hL'
  simp only [L', L, mem_filter, mem_univ, true_and] at hp₂L
  have min₂ : ∀ x, e.Live x → stab x ⊆ stab p₂ → stab x = stab p₂ := fun x hx hsub =>
    eq_of_subset_of_card_le hsub (hp₂min x (by simp [L', L, hx, hsub.trans hp₂L.2]))
  have hne : stab p₁ ≠ stab p₂ := fun h => hnot (h ▸ hp₂L.2)
  have c₁ := Exec.readsOnlyFrom_minimal hv hst hreg (stab p₁) min₁
  have c₂ := Exec.readsOnlyFrom_minimal hv hst hreg (stab p₂) min₂
  refine e.false_of_two_closed _ _ ?_ ?_ hv.h0 T₀ c₁ c₂
    ⟨p₁, by simp [hp₁, stab], hp₁⟩ ⟨p₂, by simp [hp₂L.1, stab], hp₂L.1⟩
  · rw [disjoint_filter]
    rintro x - ⟨-, h1⟩ ⟨-, h2⟩
    exact hne (h1.symm.trans h2)
  · rw [← card_union_of_disjoint (by
      rw [disjoint_filter]
      rintro x - ⟨-, h1⟩ ⟨-, h2⟩
      exact hne (h1.symm.trans h2))]
    exact (card_le_univ _).trans hPR

/-- **Theorem 4.8, as stated** (unique source): every stable view that contains no other stable
view is the least stable view `W₀`. -/
theorem theorem_4_8_unique_source (hPR : Fintype.card P ≤ Fintype.card R) {input : P → V}
    (e : Exec (P := P) (writeScan (R := R) (V := V)))
    (he : e.cfg 0 = initCfg (fun p => ({input p} : Finset V)) ∅) :
    ∃ W₀, IsStableView e id W₀ ∧ ∀ W, IsStableView e id W →
      (∀ U, IsStableView e id U → ¬ U ⊂ W) → W = W₀ := by
  obtain ⟨W₀, h₀, hmin⟩ := theorem_4_8 hPR e he
  refine ⟨W₀, h₀, fun W hW hsrc => ?_⟩
  by_contra hne
  exact hsrc W₀ h₀ (ssubset_of_subset_of_ne (hmin W hW) (Ne.symm hne))

end Podc.AnonymousCoverings
