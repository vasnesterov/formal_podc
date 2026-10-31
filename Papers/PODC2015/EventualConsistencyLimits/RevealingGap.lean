import Papers.PODC2015.EventualConsistencyLimits.Theorem6

/-!
# The "w.l.o.g. revealing" step of the proof of Theorem 6 fails

Section 5.2.1 of [AEM15] claims that every OCC abstract execution `A` may be assumed revealing
"by adding the appropriate `r_w` operations and vis edges": before every write `w` insert a read
`r_w` of the same object at the same replica, with the same visibility as `w`. The resulting
abstract execution need not be OCC, so the proof of Theorem 6 (which applies Lemma 11 to the
added reads `r_w` in its induction) cannot be run on it.

Counterexample (one object, replicas `0, 1, 2`, values `a = 0`, `b = 1`, `c = 2`):
* `Gap.A`: replica 0 writes `a`, replica 1 writes `b`, replica 2 writes `c`; the writes of
  `a` and `b` are visible to the write of `c`. It has no reads, so it is trivially OCC.
* `Gap.Arev`, its revealing extension: the added read `r_c` before the write of `c` sees the
  two concurrent writes of `a` and `b` and returns `{a, b}`. Definition 18 then requires writes
  `w₀'`, `w₁'` to *other* objects, which do not exist: `Gap.Arev` is not OCC.

`A` itself is trivially realizable; this only shows that the justification of the w.l.o.g.
step is wrong.
-/

namespace Podc.EventualConsistencyLimits

namespace Gap

/-- The visibility relation of `Arev`, as a list of pairs. -/
def visL : List (ℕ × ℕ) :=
  [(0, 1), (2, 3), (4, 5), (1, 4), (3, 4), (1, 5), (3, 5), (0, 4), (0, 5), (2, 4), (2, 5)]

/-- The OCC abstract execution: three writes `a, b, c` of a single object at
replicas `0, 1, 2`; `a` and `b` are visible to `c`. -/
def A : AE (Fin 3) Unit (Fin 3) where
  dom i := i < 3
  rep i := ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩
  ev i := ⟨(), .write ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, .ok⟩
  ord a b := a < b ∧ b < 3
  vis a b := (a, b) ∈ [(0, 2), (1, 2)]

/-- The revealing extension of `A`: event `2i` is the read `r_w` added before the write
`w = 2i + 1` (the `i`-th write of `A`), at replica `i`. The read `4 = r_c` returns `{a, b}`. -/
def Arev : AE (Fin 3) Unit (Fin 3) where
  dom i := i < 6
  rep i := ⟨i / 2 % 3, Nat.mod_lt _ (by norm_num)⟩
  ev i := if i % 2 = 1 then ⟨(), .write ⟨i / 2 % 3, Nat.mod_lt _ (by norm_num)⟩, .ok⟩
    else ⟨(), .read, if i = 4 then .vals {0, 1} else .vals ∅⟩
  ord a b := a < b ∧ b < 6
  vis a b := (a, b) ∈ visL

/-- `rev w = w - 1`: the read `r_w` added before the write `w ∈ {1, 3, 5}`. -/
def rev (w : ℕ) : ℕ := w - 1

instance : DecidableRel A.vis := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ [(0, 2), (1, 2)]))

instance : DecidableRel Arev.vis := fun a b => inferInstanceAs (Decidable ((a, b) ∈ visL))

lemma A_vis_lt {a b : ℕ} (h : A.vis a b) : a < 3 ∧ b < 3 := by
  simp only [A, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

lemma Arev_vis_lt {a b : ℕ} (h : Arev.vis a b) : a < 6 ∧ b < 6 := by
  simp only [Arev, visL, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

lemma A_wf : A.WF where
  ord_dom h := ⟨by simp only [A] at *; omega, h.2⟩
  ord_irrefl a h := by simp [A] at h
  ord_trans h h' := ⟨by have := h.1; have := h'.1; omega, h'.2⟩
  ord_total ha hb hab := by simp only [A] at *; omega
  ord_fin b := (Set.finite_Iio b).subset fun a h => h.1
  vis_ord {a b} h := by
    have key : ∀ a < 3, ∀ b < 3, A.vis a b → a < b := by decide
    obtain ⟨ha, hb⟩ := A_vis_lt h
    exact ⟨key a ha b hb h, hb⟩
  vis_sess {a b} h hr := by
    have key : ∀ b < 3, ∀ a < b, A.rep a = A.rep b → A.vis a b := by decide
    exact key b h.2 a h.1 hr
  vis_mono {a b c} h h' hr := by
    have key : ∀ c < 3, ∀ b < c, A.rep b = A.rep c → ∀ a < 3, A.vis a b → A.vis a c := by
      decide
    exact key c h'.2 b h'.1 hr a (A_vis_lt h).1 h

lemma A_occ : A.OCC := by
  refine ⟨⟨fun e _ => rfl, fun a b c h h' => ?_⟩, fun r _ _ _ hr => ?_⟩
  · have key : ∀ a < 3, ∀ b < 3, ∀ c < 3, A.vis a b → A.vis b c → A.vis a c := by decide
    exact key a (A_vis_lt h).1 b (A_vis_lt h).2 c (A_vis_lt h').2 h h'
  · simp [A] at hr

lemma Arev_wf : Arev.WF where
  ord_dom h := ⟨by simp only [Arev] at *; omega, h.2⟩
  ord_irrefl a h := by simp [Arev] at h
  ord_trans h h' := ⟨by have := h.1; have := h'.1; omega, h'.2⟩
  ord_total ha hb hab := by simp only [Arev] at *; omega
  ord_fin b := (Set.finite_Iio b).subset fun a h => h.1
  vis_ord {a b} h := by
    have key : ∀ a < 6, ∀ b < 6, Arev.vis a b → a < b := by decide
    obtain ⟨ha, hb⟩ := Arev_vis_lt h
    exact ⟨key a ha b hb h, hb⟩
  vis_sess {a b} h hr := by
    have key : ∀ b < 6, ∀ a < b, Arev.rep a = Arev.rep b → Arev.vis a b := by decide
    exact key b h.2 a h.1 hr
  vis_mono {a b c} h h' hr := by
    have key : ∀ c < 6, ∀ b < c, Arev.rep b = Arev.rep c → ∀ a < 6,
        Arev.vis a b → Arev.vis a c := by
      decide
    exact key c h'.2 b h'.1 hr a (Arev_vis_lt h).1 h

lemma Arev_isWrite {e : ℕ} : Arev.IsWrite e ↔ e % 2 = 1 := by
  constructor
  · rintro ⟨v, hv⟩
    by_contra h
    simp [Arev, h] at hv
  · intro h
    exact ⟨⟨e / 2 % 3, Nat.mod_lt _ (by norm_num)⟩, by simp [Arev, h]⟩

lemma Arev_vis_trans : ∀ a b c, Arev.vis a b → Arev.vis b c → Arev.vis a c := by
  intro a b c h h'
  have key : ∀ a < 6, ∀ b < 6, ∀ c < 6, Arev.vis a b → Arev.vis b c → Arev.vis a c := by
    decide
  exact key a (Arev_vis_lt h).1 b (Arev_vis_lt h).2 c (Arev_vis_lt h').2 h h'

/-- The writes visible to the read `r_c = 4`: the writes `1` (of `a`) and `3` (of `b`). -/
lemma Arev_ctxW_four : Arev.ctxW 4 = {1, 3} := by
  ext a
  simp only [AE.ctxW, Arev_isWrite, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, -, h'⟩
    have := (Arev_vis_lt h).1
    interval_cases a <;> simp_all [Arev, visL]
  · rintro (rfl | rfl) <;> exact ⟨by decide, trivial, rfl⟩

lemma Arev_ctxW_empty {e : ℕ} (he : e = 0 ∨ e = 2) : Arev.ctxW e = ∅ := by
  ext a
  simp only [AE.ctxW, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h, -⟩
  have := (Arev_vis_lt h).1
  rcases he with rfl | rfl <;> interval_cases a <;> simp [Arev, visL] at h

lemma Arev_cc : Arev.CC := by
  refine ⟨fun e he => ?_, Arev_vis_trans⟩
  simp only [Arev] at he
  interval_cases e
  · rw [AE.mvr_of_read (by simp [Arev]), Arev_ctxW_empty (by simp)]; simp [Arev]
  · rfl
  · rw [AE.mvr_of_read (by simp [Arev]), Arev_ctxW_empty (by simp)]; simp [Arev]
  · rfl
  · rw [AE.mvr_of_read (by simp [Arev]), Arev_ctxW_four]
    show Resp.vals ({0, 1} : Set (Fin 3)) = Resp.vals _
    congr 1
    ext v
    fin_cases v <;> simp [Arev, visL]
  · rfl

/-- `Arev` is revealing, with `r_w = w - 1`. -/
lemma Arev_revealing : Arev.Revealing rev := by
  intro w hw hW
  rw [Arev_isWrite] at hW
  simp only [Arev] at hw
  have hrep : ∀ w < 6, w % 2 = 1 → Arev.rep (w - 1) = Arev.rep w := by decide
  have k1 : ∀ w < 6, w % 2 = 1 → ∀ e < 6, e ≠ w → Arev.vis (w - 1) e → Arev.vis w e := by
    decide
  have k2 : ∀ w < 6, w % 2 = 1 → ∀ e < 6, e ≠ w - 1 → Arev.vis e w → Arev.vis e (w - 1) := by
    decide
  have hodd : ¬ (w - 1) % 2 = 1 := by omega
  refine ⟨show w - 1 < 6 by omega, hrep w hw hW, rfl, by simp [Arev, rev, hodd],
    ⟨by simp only [rev]; omega, hw⟩, fun e _ _ h => by simp only [Arev, rev] at h; omega,
    fun e he h => k1 w hw hW e (Arev_vis_lt h).2 he h,
    fun e he h => k2 w hw hW e (Arev_vis_lt h).1 he h⟩

/-- `Arev` is not OCC: the read `r_c = 4` returns the two concurrent writes `1` and `3`, and
there is no write to another object to serve as a witness `w₀'` of Definition 18. -/
lemma Arev_not_occ : ¬ Arev.OCC := by
  rintro ⟨-, h⟩
  have hmax : ∀ w ∈ ({1, 3} : Set ℕ), ∀ b ∈ Arev.ctxW 4, ¬ Arev.vis w b := by
    intro w hw b hb
    rw [Arev_ctxW_four] at hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw hb
    rcases hw with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  obtain ⟨w₀', -, -, -, -, -, hobj, -⟩ := h 4 1 3 (show 4 < 6 by norm_num) (by simp [Arev])
    (by rw [Arev_ctxW_four]; simp) (hmax 1 (by simp)) (by rw [Arev_ctxW_four]; simp)
    (hmax 3 (by simp)) (by decide)
  exact hobj rfl

/-- Restricting `Arev` to its writes `1, 3, 5` gives `A` (renaming `2i + 1 ↦ i`). -/
lemma Arev_restrict_writes {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    Arev.rep (2 * i + 1) = A.rep i ∧ Arev.ev (2 * i + 1) = A.ev i ∧
      (Arev.vis (2 * i + 1) (2 * j + 1) ↔ A.vis i j) := by
  interval_cases i <;> interval_cases j <;> exact ⟨rfl, rfl, by decide⟩

/-- **The "w.l.o.g. revealing" step of Section 5.2.1 of [AEM15] fails.** The abstract execution
`A` is OCC, but its revealing extension `Arev` (a read `r_w` with the visibility of `w` inserted
before every write `w`, see `Arev_restrict_writes`) is causally consistent and revealing, yet
not OCC: the added read `r_c` returns the two concurrent writes `{a, b}`, which have no OCC
witnesses (writes to other objects). Hence the induction in the proof of Theorem 6, which applies
Lemma 11 to the added reads `r_w`, cannot be run on `Arev`. -/
theorem revealing_extension_not_OCC :
    A.WF ∧ A.OCC ∧ Arev.WF ∧ Arev.Revealing rev ∧ Arev.CC ∧ ¬ Arev.OCC :=
  ⟨A_wf, A_occ, Arev_wf, Arev_revealing, Arev_cc, Arev_not_occ⟩

end Gap

end Podc.EventualConsistencyLimits
