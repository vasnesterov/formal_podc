import Papers.PODC2019.BayouRevisited.Constructions
import Papers.PODC2019.BayouRevisited.Fseq

/-!
# Setup for Theorem 5: the first phase of all executions, and generic history lemmas

All executions of the proof start with the *partition phase* `PA p q x y`: replica `p` invokes the
weak `append([x])` and runs until passive; then replica `q` invokes the weak `append([y])` and runs
until passive.
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {Op Val : Type} {I : Impl n Op Val} {S : ACTSpec Op Val}

/-! ### Generic lemmas about runs and histories -/

lemma ValidRun.valid_pre {r : ℕ → I.Act} (h : I.ValidRun S r) (t : ℕ) : I.Valid S (I.pre r t) := by
  intro s hs
  have hs' : s < t := by simpa [pre] using hs
  have h1 : (I.pre r t).take s = I.pre r s := by
    simp only [pre]; rw [← List.map_take, List.take_range, min_eq_left hs'.le]
  have h2 : (I.pre r t)[s]'hs = r s := by simp [pre]
  rw [h1, h2]
  exact h s

lemma pre_succ (r : ℕ → I.Act) (t : ℕ) : I.pre r (t + 1) = I.pre r t ++ [r t] := by
  simp [pre, List.range_succ]

lemma LIn.opOf_eq {x : I.Input} (hx : x.IsInv) {op : Op} {l : Level} (h : x = .inv op l) :
    x.opOf hx = op := by subst h; rfl

lemma LIn.lvlOf_eq {x : I.Input} (hx : x.IsInv) {op : Op} {l : Level} (h : x = .inv op l) :
    x.lvlOf hx = l := by subst h; rfl

lemma history_op {r : ℕ → I.Act} (e : I.Ev r) {i : Fin n} {op : Op} {l : Level}
    (h : r e.1 = (i, .inv op l)) : (I.history r).op e = op :=
  LIn.opOf_eq _ (by rw [h])

lemma history_lvl {r : ℕ → I.Act} (e : I.Ev r) {i : Fin n} {op : Op} {l : Level}
    (h : r e.1 = (i, .inv op l)) : (I.history r).lvl e = l :=
  LIn.lvlOf_eq _ (by rw [h])

lemma lidx_eq {r : ℕ → I.Act} {t : ℕ} {i : Fin n} {x : I.Input} (h : r t = (i, x)) :
    I.lidx r t = (I.loc i (I.pre r t)).length := by
  simp [lidx, h]

/-- The value of a weak read-only invocation is its immediate response. -/
lemma rvalOf_weak (hI : I.IsACT S) {r : ℕ → I.Act} (hV : I.ValidRun S r) (e : I.Ev r)
    {i : Fin n} {op : Op} (he : r e.1 = (i, .inv op .weak)) (hro : RDT.IsReadOnly S.F op)
    (hw : Level.weak ∈ S.lvlmap op) :
    ∃ v, I.immVal i (I.loc i (I.pre r e.1)) op = some v ∧ I.rvalOf r e = some v := by
  have hP := hV.valid_pre e.1
  obtain ⟨-, hs⟩ := hI.invisible_reads _ hP i op hro hw
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨v, hv, rvalOf_eq_of_lresp e (T := e.1 + 1) ?_⟩
  rw [he, lidx_eq he, pre_succ, he, loc_append, loc_singleton, if_pos rfl, lresp_concat_self]
  exact hv

/-- Infinitely many indices avoid a finite set. -/
lemma exists_ge_not_mem {β : Type} {f : ℕ → β} (hf : Function.Injective f) {s : Set β}
    (hs : s.Finite) (N : ℕ) : ∃ K ≥ N, f K ∉ s := by
  obtain ⟨B, hB⟩ := (hs.preimage hf.injOn).bddAbove
  refine ⟨max N (B + 1), le_max_left _ _, fun h => ?_⟩
  have := hB (show max N (B + 1) ∈ f ⁻¹' s from h)
  omega

/-- In a list `L0 ++ R` whose tail `R` invokes only `rd`, an invocation of another operation
lies in `L0`. -/
lemma getElem_of_opsIn {rd : Op} {L0 R : List I.Act} (hR : OpsIn (· = rd) R) {t : ℕ}
    (ht : t < (L0 ++ R).length) {i : Fin n} {op : Op} {l : Level}
    (h : (L0 ++ R)[t] = (i, .inv op l)) (hop : op ≠ rd) :
    ∃ h' : t < L0.length, L0[t] = (i, .inv op l) := by
  by_cases h' : t < L0.length
  · rw [List.getElem_append_left h'] at h; exact ⟨h', h⟩
  · rw [List.getElem_append_right (by omega)] at h
    exact absurd (hR _ (List.getElem_mem _) op l (by rw [h])) hop

/-! ### The partition phase -/

variable {α : Type} {J : Impl n (SeqOp α) (SeqVal α)}

/-- The weak `append([z])` input. -/
abbrev appIn (J : Impl n (SeqOp α) (SeqVal α)) (z : α) : J.Input := .inv (.append [z]) .weak

/-- The local inputs of a replica that invokes `append([z])` and runs until passive. -/
noncomputable def Ablk (J : Impl n (SeqOp α) (SeqVal α)) (i : Fin n) (z : α) : List J.Input :=
  [J.appIn z] ++ J.intBlk i [J.appIn z]

/-- The partition phase: `p` appends `x`, then `q` appends `y`. -/
noncomputable def PA (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) : List J.Act :=
  J.invBlk q (.append [y]) .weak (J.invBlk p (.append [x]) .weak [])

lemma valid_PA (hI : J.IsACT (seqSpec α)) (p q : Fin n) (x y : α) :
    J.Valid (seqSpec α) (J.PA p q x y) ∧
      J.Passive p (J.lstate p (J.loc p (J.invBlk p (.append [x]) .weak []))) ∧
      J.Passive q (J.lstate q (J.loc q (J.PA p q x y))) := by
  obtain ⟨h1, h2⟩ := valid_invBlk hI valid_nil p (op := .append [x]) (l := .weak) (Set.mem_univ _)
  obtain ⟨h3, h4⟩ := valid_invBlk hI h1 q (op := .append [y]) (l := .weak) (Set.mem_univ _)
  exact ⟨h3, h2, h4⟩

lemma loc_PA_p {p q : Fin n} (hpq : p ≠ q) (x y : α) : J.loc p (J.PA p q x y) = J.Ablk p x := by
  rw [PA, loc_invBlk_ne (Ne.symm hpq), loc_invBlk_self]; simp [Ablk]

lemma loc_PA_q {p q : Fin n} (hpq : p ≠ q) (x y : α) : J.loc q (J.PA p q x y) = J.Ablk q y := by
  rw [PA, loc_invBlk_self, loc_invBlk_ne hpq]; simp [Ablk]

lemma loc_PA_other {p q j : Fin n} (hp : j ≠ p) (hq : j ≠ q) (x y : α) :
    J.loc j (J.PA p q x y) = [] := by
  rw [PA, loc_invBlk_ne (Ne.symm hq), loc_invBlk_ne (Ne.symm hp)]; rfl

lemma tobSeq_PA (p q j : Fin n) (x y : α) : J.tobSeq j (J.PA p q x y) = [] := by
  rw [PA, tobSeq_invBlk, tobSeq_invBlk]; rfl

lemma passive_Ablk_p (hI : J.IsACT (seqSpec α)) {p q : Fin n} (hpq : p ≠ q) (x y : α) :
    J.Passive p (J.lstate p (J.Ablk p x)) := by
  have := (valid_PA hI p q x y).2.1
  rwa [loc_invBlk_self, show ([] : List J.Act) = [] from rfl, loc_nil, List.nil_append] at this

lemma passive_Ablk_q (hI : J.IsACT (seqSpec α)) {p q : Fin n} (hpq : p ≠ q) (x y : α) :
    J.Passive q (J.lstate q (J.Ablk q y)) := by
  have := (valid_PA hI p q x y).2.2
  rwa [loc_PA_q hpq] at this

/-- The time of `q`'s append in `PA`. -/
noncomputable def tb (J : Impl n (SeqOp α) (SeqVal α)) (p : Fin n) (x : α) : ℕ :=
  (J.invBlk p (.append [x]) .weak []).length

lemma PA_eq (p q : Fin n) (x y : α) :
    J.PA p q x y = [(p, J.appIn x)] ++ J.atR p (J.intBlk p [J.appIn x]) ++
      [(q, J.appIn y)] ++ J.atR q (J.intBlk q (J.loc q (J.invBlk p (.append [x]) .weak []) ++
        [J.appIn y])) := by
  simp [PA, invBlk]

lemma tb_eq (p : Fin n) (x : α) : J.tb p x = 1 + (J.intBlk p [J.appIn x]).length := by
  simp [tb, invBlk, Nat.add_comm]

lemma PA_getElem_zero (p q : Fin n) (x y : α) (h : 0 < (J.PA p q x y).length) :
    (J.PA p q x y)[0] = (p, J.appIn x) := by
  simp only [PA_eq]; simp

lemma PA_getElem_tb (p q : Fin n) (x y : α) (h : J.tb p x < (J.PA p q x y).length) :
    (J.PA p q x y)[J.tb p x] = (q, J.appIn y) := by
  simp only [PA_eq, tb_eq]
  rw [List.getElem_append_left (by simp <;> omega), List.getElem_append_right (by simp <;> omega)]
  simp [Nat.add_comm]

lemma tb_lt (p q : Fin n) (x y : α) : J.tb p x < (J.PA p q x y).length := by
  rw [tb_eq, PA_eq]; simp; omega

/-- The only invocations of `append` in `PA` are at times `0` and `tb`. -/
lemma PA_app {p q : Fin n} {x y : α} {t : ℕ} (ht : t < (J.PA p q x y).length) {i : Fin n}
    {s : List α} {l : Level} (h : (J.PA p q x y)[t] = (i, .inv (.append s) l)) :
    t = 0 ∨ t = J.tb p x := by
  simp only [PA_eq] at h ht
  rw [tb_eq]
  simp only [List.length_append, List.length_singleton, atR_length] at ht
  set a := (J.intBlk p [J.appIn x]).length
  by_cases h1 : t < 1 + a + 1
  · rw [List.getElem_append_left (by simp <;> omega)] at h
    by_cases h2 : t < 1 + a
    · rw [List.getElem_append_left (by simp <;> omega)] at h
      by_cases h3 : t < 1
      · left; omega
      · rw [List.getElem_append_right (by simp <;> omega)] at h
        simp [atR, intBlk] at h
    · right; omega
  · rw [List.getElem_append_right (by simp <;> omega)] at h
    simp [atR, intBlk] at h

end Podc.BayouRevisited.Impl
