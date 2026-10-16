import Papers.PODC2025.UniqueIDsBoundedRegisters.Defs

/-!
# Poised processes and restoring register values (Claim 1)

A *poised entry* `(p, i, o)` records that process `p` is pending and its next step applies the
update primitive `o` (a `write` or a `fai`) to register `i`. For a list `S` of poised entries
(distinct processes, pairwise distinct write values per register):

* `Restorable S i y`: either at least `m` entries of `S` are poised on `i`, or one of them is
  poised to `write y` on `i`;
* `claim1` (**Claim 1** of the paper, completed for the case where all poised primitives are
  `fai`): if `Restorable S i y`, some of the processes poised on `i`, each taking one step,
  set `i` to `y`, whatever its current value;
* `restore_many`: the same simultaneously for a list of registers;
* `runFrom_taus`: letting poised processes take one step each has exactly the expected effect
  on the memory and does not touch other processes.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory Impl
open Fin.CommRing

variable {k m : ℕ} [NeZero m] {P L : Type} [DecidableEq P]

/-! ### Register arithmetic -/

/-- New value of a register after a primitive. -/
def app (s : Fin m) (o : BOp m) : Fin m := ((bReg m).δ s o).1

/-- Value after a sequence of primitives. -/
def appList (s : Fin m) (os : List (BOp m)) : Fin m := os.foldl app s

@[simp] lemma app_fai (s : Fin m) : app s .fai = s + 1 := rfl
@[simp] lemma app_write (s v : Fin m) : app s (.write v) = v := rfl
@[simp] lemma app_read (s : Fin m) : app s .read = s := rfl

lemma appList_replicate_fai (r : ℕ) : ∀ s : Fin m,
    appList s (List.replicate r .fai) = s + (r : Fin m) := by
  induction r with
  | zero => intro s; simp [appList]
  | succ r ih =>
    intro s
    rw [List.replicate_succ]
    simp only [appList, List.foldl_cons, app_fai] at ih ⊢
    rw [ih]; push_cast; ring

/-! ### Poised entries -/

/-- Number of entries poised on register `i`. -/
def cnt (S : List (P × Fin k × BOp m)) (i : Fin k) : ℕ := (S.filter (fun e => e.2.1 = i)).length

/-- Register `i` can be set to `y` by entries of `S`. -/
def Restorable (S : List (P × Fin k × BOp m)) (i : Fin k) (y : Fin m) : Prop :=
  m ≤ cnt S i ∨ ∃ p, (p, i, BOp.write y) ∈ S

/-- Pairwise distinct write values on each register. -/
def WD (S : List (P × Fin k × BOp m)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → (∃ v, a.2.2 = .write v) → a = b

lemma cnt_mono {S S' : List (P × Fin k × BOp m)} (h : S.Sublist S') (i : Fin k) :
    cnt S i ≤ cnt S' i :=
  (h.filter _).length_le

lemma Restorable.mono {S S' : List (P × Fin k × BOp m)} (h : S.Sublist S') {i : Fin k} {y : Fin m}
    (hr : Restorable S i y) : Restorable S' i y := by
  rcases hr with hr | ⟨p, hp⟩
  · exact Or.inl (hr.trans (cnt_mono h i))
  · exact Or.inr ⟨p, h.subset hp⟩

/-- `wval (write v) = v`. -/
def wval : BOp m → Fin m
  | .write v => v
  | _ => 0

/-- Is a `fai`. -/
def isFai : BOp m → Bool
  | .fai => true
  | _ => false

/-- **Claim 1.** If register `i` is restorable to `y`, a duplicate-free list of entries poised
on `i` brings it from any value `c` to `y`. -/
theorem claim1 (S : List (P × Fin k × BOp m)) (hnd : S.Nodup) (hWD : WD S)
    (hNR : ∀ e ∈ S, e.2.2 ≠ .read) (i : Fin k) (y c : Fin m) (h : Restorable S i y) :
    ∃ es : List (P × Fin k × BOp m), es.Nodup ∧ (∀ e ∈ es, e ∈ S ∧ e.2.1 = i) ∧
      appList c (es.map (fun e => e.2.2)) = y := by
  classical
  rcases h with h | ⟨p, hp⟩
  swap
  · exact ⟨[(p, i, .write y)], by simp, by simp [hp], by simp [appList]⟩
  set E := S.filter (fun e => e.2.1 = i) with hE
  set F := E.filter (fun e => isFai e.2.2) with hF
  set G := E.filter (fun e => !isFai e.2.2) with hG
  have hElen : E.length = F.length + G.length := by
    rw [hF, hG]; exact List.length_eq_length_filter_add _
  have hEnd : E.Nodup := hnd.filter _
  have hFsub : ∀ e ∈ F, e ∈ S ∧ e.2.1 = i ∧ e.2.2 = .fai := by
    intro e he
    simp only [hF, hE, List.mem_filter, decide_eq_true_eq] at he
    refine ⟨he.1.1, he.1.2, ?_⟩
    have := he.2; revert this; cases e.2.2 <;> simp [isFai]
  have hFnd : F.Nodup := hEnd.filter _
  -- every fai-take
  have take_ok : ∀ r ≤ F.length, ∀ s : Fin m,
      appList s ((F.take r).map (fun e => e.2.2)) = s + (r : Fin m) := by
    intro r hr s
    have : (F.take r).map (fun e => e.2.2) = List.replicate r .fai := by
      rw [List.eq_replicate_iff]
      refine ⟨by simp; omega, fun o ho => ?_⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ho
      exact (hFsub e (List.mem_of_mem_take he)).2.2
    rw [this, appList_replicate_fai]
  by_cases hf : m ≤ F.length
  · refine ⟨F.take (y - c).val, hFnd.sublist (List.take_sublist _ _), fun e he => ?_, ?_⟩
    · have := hFsub e (List.mem_of_mem_take he); exact ⟨this.1, this.2.1⟩
    · rw [take_ok _ (by have := (y - c).isLt; omega)]
      simp
  · push Not at hf
    set f := F.length with hfdef
    -- write values
    set W := (G.map (fun e => wval e.2.2)).toFinset with hW
    have hGw : ∀ e ∈ G, e ∈ S ∧ e.2.1 = i ∧ e.2.2 = .write (wval e.2.2) := by
      intro e he
      simp only [hG, hE, List.mem_filter, decide_eq_true_eq] at he
      refine ⟨he.1.1, he.1.2, ?_⟩
      have h2 := he.2
      have h3 := hNR e he.1.1
      revert h2 h3; cases e.2.2 <;> simp [isFai, wval]
    have hGnd : (G.map (fun e => wval e.2.2)).Nodup := by
      refine List.Nodup.map_on ?_ (hEnd.filter _)
      intro a ha b hb hab
      have ha' := hGw a ha; have hb' := hGw b hb
      refine hWD a ha'.1 b hb'.1 ?_ ⟨_, ha'.2.2⟩
      rw [Prod.ext_iff]; refine ⟨ha'.2.1.trans hb'.2.1.symm, ?_⟩
      rw [ha'.2.2, hb'.2.2, hab]
    have hWcard : W.card = G.length := by
      rw [hW, List.toFinset_card_of_nodup hGnd, List.length_map]
    set T := (Finset.range (f + 1)).image (fun j : ℕ => y - (j : Fin m)) with hT
    have hTcard : T.card = f + 1 := by
      rw [hT, Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      have : (a : Fin m) = (b : Fin m) := by simpa using hab
      have ha' : a < m := by omega
      have hb' : b < m := by omega
      have := congrArg Fin.val this
      simpa [Fin.val_natCast, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using this
    have hcnt : m ≤ E.length := h
    have hinter : (T ∩ W).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.card_union_add_card_inter T W
      have h2 : (T ∪ W).card ≤ m := by
        simpa using Finset.card_le_univ (T ∪ W)
      omega
    obtain ⟨z, hz⟩ := hinter
    rw [Finset.mem_inter] at hz
    obtain ⟨j, hj, hzj⟩ := Finset.mem_image.1 hz.1
    obtain ⟨e, he, hez⟩ := List.mem_map.1 (List.mem_toFinset.1 hz.2)
    rw [Finset.mem_range] at hj
    have he' := hGw e he
    refine ⟨e :: F.take j, ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hmem => ?_, hFnd.sublist (List.take_sublist _ _)⟩
      have := (hFsub e (List.mem_of_mem_take hmem)).2.2
      rw [he'.2.2] at this; cases this
    · intro e' he''
      rcases List.mem_cons.1 he'' with rfl | he''
      · exact ⟨he'.1, he'.2.1⟩
      · have := hFsub e' (List.mem_of_mem_take he''); exact ⟨this.1, this.2.1⟩
    · simp only [List.map_cons, appList, List.foldl_cons]
      rw [he'.2.2, app_write]
      have := take_ok j (by omega) (wval e.2.2)
      simp only [appList] at this
      rw [this, hez, ← hzj]; ring

/-! ### Memory effect of poised steps -/

/-- Memory after the entries `es` each perform their primitive, in order. -/
def memAfter (M : Fin k → Fin m) (es : List (P × Fin k × BOp m)) : Fin k → Fin m :=
  es.foldl (fun M e => Function.update M e.2.1 (app (M e.2.1) e.2.2)) M

@[simp] lemma memAfter_nil (M : Fin k → Fin m) : memAfter M ([] : List (P × Fin k × BOp m)) = M :=
  rfl

lemma memAfter_cons (M : Fin k → Fin m) (e : P × Fin k × BOp m) (es) :
    memAfter M (e :: es) = memAfter (Function.update M e.2.1 (app (M e.2.1) e.2.2)) es := rfl

lemma memAfter_append (M : Fin k → Fin m) (es es' : List (P × Fin k × BOp m)) :
    memAfter M (es ++ es') = memAfter (memAfter M es) es' := by
  simp [memAfter, List.foldl_append]

lemma memAfter_of_ne (j : Fin k) : ∀ (es : List (P × Fin k × BOp m)) (M : Fin k → Fin m),
    (∀ e ∈ es, e.2.1 ≠ j) → memAfter M es j = M j := by
  intro es
  induction es with
  | nil => intro M _; rfl
  | cons e es ih =>
    intro M h
    rw [memAfter_cons, ih _ (fun e' he' => h e' (by simp [he']))]
    rw [Function.update_of_ne (h e (by simp)).symm]

lemma memAfter_single (i : Fin k) : ∀ (es : List (P × Fin k × BOp m)) (M : Fin k → Fin m),
    (∀ e ∈ es, e.2.1 = i) → memAfter M es i = appList (M i) (es.map (fun e => e.2.2)) := by
  intro es
  induction es with
  | nil => intro M _; rfl
  | cons e es ih =>
    intro M h
    rw [memAfter_cons, ih _ (fun e' he' => h e' (by simp [he']))]
    have he := h e (by simp)
    simp only [List.map_cons, appList, List.foldl_cons]
    rw [he, Function.update_self]

/-- Restoring a list of registers simultaneously. -/
theorem restore_many (S : List (P × Fin k × BOp m)) (hnd : S.Nodup) (hWD : WD S)
    (hNR : ∀ e ∈ S, e.2.2 ≠ .read) (x : Fin k → Fin m) :
    ∀ rs : List (Fin k), rs.Nodup → (∀ i ∈ rs, Restorable S i (x i)) → ∀ M : Fin k → Fin m,
      ∃ es : List (P × Fin k × BOp m), es.Nodup ∧ (∀ e ∈ es, e ∈ S ∧ e.2.1 ∈ rs) ∧
        (∀ i ∈ rs, memAfter M es i = x i) ∧ (∀ j ∉ rs, memAfter M es j = M j) := by
  intro rs
  induction rs with
  | nil => intro _ _ M; exact ⟨[], by simp, by simp, by simp, fun _ _ => rfl⟩
  | cons i rs ih =>
    intro hrs hR M
    obtain ⟨hi, hrs'⟩ := List.nodup_cons.1 hrs
    obtain ⟨es₁, h1nd, h1S, h1v⟩ := claim1 S hnd hWD hNR i (x i) (M i) (hR i (by simp))
    set M₁ := memAfter M es₁ with hM₁
    obtain ⟨es₂, h2nd, h2S, h2v, h2o⟩ := ih hrs' (fun j hj => hR j (by simp [hj])) M₁
    refine ⟨es₁ ++ es₂, ?_, ?_, ?_, ?_⟩
    · refine List.nodup_append.2 ⟨h1nd, h2nd, ?_⟩
      intro a ha b hb hab; subst hab
      have := (h1S a ha).2; have := (h2S a hb).2
      exact hi (by simp_all)
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact ⟨(h1S e he).1, by simp [(h1S e he).2]⟩
      · exact ⟨(h2S e he).1, by simp [(h2S e he).2]⟩
    · intro j hj
      rw [memAfter_append]
      rcases List.mem_cons.1 hj with rfl | hj
      · rw [h2o _ hi, hM₁, memAfter_single _ es₁ M (fun e he => (h1S e he).2), h1v]
      · exact h2v j hj
    · intro j hj
      rw [memAfter_append, h2o j (fun h => hj (by simp [h])), hM₁]
      exact memAfter_of_ne j es₁ M (fun e he h => hj (by rw [← h, (h1S e he).2]; simp))

/-! ### Running poised processes -/

variable (I : Impl uidObj (fun _ : Fin k => bReg m) P L)

/-- In `D`, the process of entry `e` is pending and about to apply `e.2.2` to `e.2.1`. -/
def PoisedAt (D : Config uidObj (fun _ : Fin k => bReg m) P L) (e : P × Fin k × BOp m) : Prop :=
  D.pend e.1 ≠ none ∧ ∃ kk, I.act e.1 (D.loc e.1) = .access e.2.1 e.2.2 kk

/-- Letting the entries `es` (distinct processes) take one step each. -/
theorem runFrom_taus : ∀ (es : List (P × Fin k × BOp m)), (es.map Prod.fst).Nodup →
    ∀ D : Config uidObj (fun _ : Fin k => bReg m) P L, (∀ e ∈ es, PoisedAt I D e) →
    ∃ D', I.runFrom D (es.map (fun e => Label.tau e.1)) = some D' ∧
      D'.mem = memAfter D.mem es ∧
      ∀ q ∉ es.map Prod.fst, D'.loc q = D.loc q ∧ D'.pend q = D.pend q := by
  intro es
  induction es with
  | nil => intro _ D _; exact ⟨D, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons e es ih =>
    intro hnd D hP
    obtain ⟨he, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hpend, kk, hact⟩ := hP e (by simp)
    set D₁ : Config uidObj (fun _ : Fin k => bReg m) P L :=
      { D with mem := Function.update D.mem e.2.1 (app (D.mem e.2.1) e.2.2),
               loc := Function.update D.loc e.1 (kk ((bReg m).δ (D.mem e.2.1) e.2.2).2) }
      with hD₁
    have hs : I.step D (.tau e.1) = some D₁ := by
      simp only [step, hpend, ↓reduceIte, hact, hD₁]; rfl
    have hP₁ : ∀ e' ∈ es, PoisedAt I D₁ e' := by
      intro e' he'
      have hne : e'.1 ≠ e.1 := fun h => he (h ▸ List.mem_map_of_mem he')
      obtain ⟨h1, kk', h2⟩ := hP e' (by simp [he'])
      refine ⟨by simpa [hD₁] using h1, kk', ?_⟩
      simpa [hD₁, Function.update_of_ne hne] using h2
    obtain ⟨D', hrun, hmem, hother⟩ := ih hnd' D₁ hP₁
    refine ⟨D', ?_, ?_, ?_⟩
    · simp only [List.map_cons, runFrom_cons, hs, Option.bind_some]; exact hrun
    · rw [hmem, memAfter_cons]
    · intro q hq
      have hq1 : q ≠ e.1 := fun h => hq (by simp [h])
      have hq2 : q ∉ es.map Prod.fst := fun h => hq (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ h)
      obtain ⟨a, b⟩ := hother q hq2
      refine ⟨a.trans ?_, b⟩
      simp [hD₁, Function.update_of_ne hq1]

end Cslib.SharedMemory.UniqueIDs
