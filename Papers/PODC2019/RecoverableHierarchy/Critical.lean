import Papers.PODC2019.RecoverableHierarchy.Valency

/-!
# The critical state: initial bivalence and the case analysis toolkit

* `Restr.biv_init`: with inputs `a ↦ 0`, `b ↦ 1` (others arbitrary, here `0`) the initial state
  is bivalent: `a` alone decides `0`, `b` alone decides `1` (validity + indistinguishability from
  the unanimous initial states). The paper's proof of Theorem 3 does not state this step.
* `Restr.crit`: the bundled outcome of the construction: a bivalent `σ` with `σ a` `v`-univalent
  and `σ b` `w`-univalent, `v ≠ w`, and no process has output at `σ`.
* The cases of the proof of Theorem 3, each yielding `v = w` (a contradiction):
  - `Crit.false_of_b_absorbs` (Case D: `b` cannot distinguish `σ a b` from `σ b`), with the
    instances `absorb_b_of_pend` (`a`'s move is a crash, Subcase D-1) and `absorb_b_of_absorb`
    (`b`'s operation absorbs `a`'s: `a` reads, or `b` blindly overwrites, Subcases D-1/D-2);
  - `Crit.false_of_a_absorbs` (Case D with roles exchanged: `a` cannot distinguish `σ b a` from
    `σ a`), instance `absorb_a_of_absorb`;
  - `Crit.false_of_commute` (Cases A and C: `σ a b = σ b a`), instances `commute_of_ne` (distinct
    objects) and `commute_of_commuteAt` (operations on one object commuting at its value with the
    same responses);
  - `Crit.false_of_hide` (Case B: `a`'s first triggering operation is followed by its crash, which
    erases `a`'s response), instances `hide_agA` (the states `σ a crash` and `σ b a crash` agree
    for `a` except on the object, and everywhere if the object's value is the same).
-/

namespace Podc.RecoverableHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

namespace Restr

variable {R : Restr A}

/-! ## Initial bivalence -/

variable (R) in
/-- The inputs `a ↦ 0`, everybody else `↦ 1`... more precisely `p ↦ (p = b)`. -/
def x₀ : Fin n → Bool := fun p => decide (p = R.b)

lemma x₀_a : R.x₀ R.a = false := by simp [x₀, R.hab]
lemma x₀_b : R.x₀ R.b = true := by simp [x₀]

/-- **Initial bivalence.** -/
theorem biv_init (hR : R.RCorrect) : R.Biv R.x₀ [] := by
  constructor
  · -- `b` alone decides `1`
    obtain ⟨k, u, hu⟩ := solo_b hR R.x₀ []
    have hag : AgreeOn {R.b} (RS.init A R.x₀).c (RS.init A (fun _ => true)).c := by
      refine ⟨rfl, fun p hp => ?_⟩
      rw [Set.mem_singleton_iff] at hp; subst hp
      simp [RS.init, initCfg, x₀_b]
    have hu' := hu
    simp only [List.nil_append] at hu'
    rw [S, R.rrun_b_solo_c] at hu'
    have h2 := ((run_agreeOn hag (List.replicate k (.step R.b)) (by simp)).out_iff
      (Set.mem_singleton _) u).1 hu'
    rw [← R.rrun_b_solo_c] at h2
    obtain ⟨p, hp⟩ := hR.valid _ _ u (R.dec_of_out (σ := List.replicate k true) h2)
    have : u = true := by rw [← hp]
    subst this
    exact ⟨List.replicate k true, by simpa using R.dec_of_out hu⟩
  · -- `a` alone decides `0`
    obtain ⟨k, u, hu⟩ := solo_a hR R.x₀ []
    have hag : R.AgA ∅ (RS.init A R.x₀) (RS.init A (fun _ => false)) :=
      ⟨fun _ _ => rfl, by simp [RS.init, initCfg, x₀_a], by simp [RS.init, initCfg, x₀_a],
        rfl, rfl⟩
    have h2 := hag.solo k (fun _ _ _ i hi => by simp at hi)
    simp only [List.nil_append] at hu
    have hu' : (R.S (fun _ => false) (List.replicate k false)).c.Out R.a u := by
      unfold Cfg.Out at hu ⊢; rw [← h2.loc]; exact hu
    obtain ⟨p, hp⟩ := hR.valid _ _ u (R.dec_of_out hu')
    have : u = false := by rw [← hp]
    subst this
    exact ⟨List.replicate k false, by simpa using R.dec_of_out hu⟩

/-! ## The critical schedule -/

/-- A critical schedule with the valencies of its two extensions. -/
structure Crit (R : Restr A) (x : Fin n → Bool) (σ : List Bool) (v w : Bool) : Prop where
  biv : R.Biv x σ
  univ_a : R.Univ x (σ ++ [false]) v
  univ_b : R.Univ x (σ ++ [true]) w
  ne : v ≠ w

/-- **Existence of a critical schedule** for an algorithm correct on restricted executions. -/
theorem exists_crit' (hR : R.RCorrect) : ∃ σ v w, R.Crit R.x₀ σ v w := by
  obtain ⟨σ, hb, ha, hb'⟩ := exists_crit hR (biv_init hR)
  obtain ⟨v, hv⟩ := univ_of_not_biv hR ha
  obtain ⟨w, hw⟩ := univ_of_not_biv hR hb'
  exact ⟨σ, v, w, hb, hv, hw, crit_values hb hv hw⟩

variable {x : Fin n → Bool} {σ : List Bool} {v w : Bool}

lemma S_concat (x : Fin n → Bool) (σ : List Bool) (m : Bool) :
    R.S x (σ ++ [m]) = R.mv (R.S x σ) m := R.rrun_concat _ _ _

lemma S_two (x : Fin n → Bool) (σ : List Bool) (m m' : Bool) :
    R.S x (σ ++ [m, m']) = R.mv (R.mv (R.S x σ) m) m' := by
  rw [show σ ++ [m, m'] = σ ++ [m] ++ [m'] by simp, S_concat, S_concat]

lemma S_three (x : Fin n → Bool) (σ : List Bool) (m m' m'' : Bool) :
    R.S x (σ ++ [m, m', m'']) = R.mv (R.mv (R.mv (R.S x σ) m) m') m'' := by
  rw [show σ ++ [m, m', m''] = σ ++ [m] ++ [m'] ++ [m''] by simp, S_concat, S_concat,
    S_concat]

/-- At a critical schedule no process has output. -/
lemma Crit.not_out (hR : R.RCorrect) (hc : R.Crit x σ v w) (p : Fin n) (u : Bool) :
    ¬ (R.S x σ).c.Out p u := fun h => not_out_of_biv hR hc.biv h

/-- Case D: `b` cannot distinguish `σ a b` from `σ b`. -/
theorem Crit.false_of_b_absorbs (hR : R.RCorrect) (hc : R.Crit x σ v w)
    (h : AgreeOn {R.b} (R.mv (R.mv (R.S x σ) false) true).c (R.mv (R.S x σ) true).c) : False := by
  refine hc.ne (contra_b hR (σ₁ := σ ++ [false, true]) (σ₂ := σ ++ [true])
    (by simpa using hc.univ_a.append [true]) hc.univ_b ?_)
  rw [S_two, S_concat]; exact h

/-- Case D with the roles exchanged: `a` cannot distinguish `σ b a` from `σ a`. -/
theorem Crit.false_of_a_absorbs (hR : R.RCorrect) (hc : R.Crit x σ v w)
    (h : R.AgA ∅ (R.mv (R.mv (R.S x σ) true) false) (R.mv (R.S x σ) false)) : False := by
  refine hc.ne (contra_a hR (S := ∅) (σ₁ := σ ++ [true, false]) (σ₂ := σ ++ [false])
    (by simpa using hc.univ_b.append [false]) hc.univ_a ?_ (fun _ _ i hi => by simp at hi)).symm
  rw [S_two, S_concat]; exact h

/-- Cases A and C: the two moves commute. -/
theorem Crit.false_of_commute (hR : R.RCorrect) (hc : R.Crit x σ v w)
    (h : R.mv (R.mv (R.S x σ) false) true = R.mv (R.mv (R.S x σ) true) false) : False := by
  refine hc.ne (contra_b hR (σ₁ := σ ++ [false, true]) (σ₂ := σ ++ [true, false])
    (by simpa using hc.univ_a.append [true]) (by simpa using hc.univ_b.append [false]) ?_)
  rw [S_two, S_two, h]; exact AgreeOn.refl _ _

/-- Case B: after `a`'s first triggering operation and its crash, `a` cannot distinguish
`σ a crash` from `σ b a crash` (except on objects `S` that `a` never accesses again). -/
theorem Crit.false_of_hide (hR : R.RCorrect) (hc : R.Crit x σ v w) {S : Set ι}
    (h : R.AgA S (R.S x (σ ++ [false, false])) (R.S x (σ ++ [true, false, false])))
    (hS : ∀ j, (R.S x (σ ++ [false, false] ++ List.replicate j false)).pend = false →
      ∀ i ∈ S, ¬ (R.S x (σ ++ [false, false] ++ List.replicate j false)).c.Poised R.a i) :
    False :=
  hc.ne (contra_a hR (σ₁ := σ ++ [false, false]) (σ₂ := σ ++ [true, false, false])
    (by simpa using hc.univ_a.append [false]) (by simpa using hc.univ_b.append [false, false])
    h hS)

/-! ## Computing the two-move states -/

lemma mv_false_c_npend (s : RS A) (h : s.pend = false) : (R.mv s false).c = s.c.stepP R.a := by
  rw [R.mv_false_npend s h]; cases R.newTrig s <;> rfl

lemma newTrig_mv_true (s : RS A) : R.newTrig (R.mv s true) = R.newTrig s :=
  R.newTrig_congr (by simp [stepP_loc_other s.c R.hab]) rfl

/-- If `a` must crash, `b` cannot distinguish `σ a b` from `σ b` (Subcase D-1, crash). -/
lemma absorb_b_of_pend (s : RS A) (h : s.pend = true) :
    AgreeOn {R.b} (R.mv (R.mv s false) true).c (R.mv s true).c := by
  rw [R.mv_false_pend s h]
  simp only [mv_true]
  have h0 : AgreeOn ({R.b} : Set (Fin n)) (s.c.next (.crash R.a)) s.c := by
    refine ⟨rfl, fun p hp => ?_⟩
    rw [Set.mem_singleton_iff] at hp; subst hp
    exact ⟨next_loc_other _ _ (by simpa using fun h' => R.hab h'.symm), rfl⟩
  exact next_agreeOn h0 (.step R.b) (by simp)

variable {s : RS A} {i : ι} {o o' : (T i).Op} {k k' : (T i).Resp → A.L}

/-- If `b`'s operation behaves the same after `a`'s as alone, `b` cannot distinguish. -/
lemma absorb_b_of_absorb (hp : s.pend = false) (ha : A.act (s.c.loc R.a) = .access i o k)
    (hb : A.act (s.c.loc R.b) = .access i o' k')
    (h : (T i).δ ((T i).δ (s.c.mem i) o).1 o' = (T i).δ (s.c.mem i) o') :
    AgreeOn {R.b} (R.mv (R.mv s false) true).c (R.mv s true).c := by
  simp only [mv_true, R.mv_false_c_npend s hp]
  exact agreeOn_stepP_stepP_of_absorb _ R.hab ha hb h

/-- If `a`'s operation behaves the same after `b`'s as alone, `a` cannot distinguish. -/
lemma absorb_a_of_absorb (hp : s.pend = false) (ha : A.act (s.c.loc R.a) = .access i o k)
    (hb : A.act (s.c.loc R.b) = .access i o' k')
    (h : (T i).δ ((T i).δ (s.c.mem i) o').1 o = (T i).δ (s.c.mem i) o) :
    R.AgA ∅ (R.mv (R.mv s true) false) (R.mv s false) := by
  have hag := agreeOn_stepP_stepP_of_absorb s.c (Ne.symm R.hab) hb ha h
  have hp' : (R.mv s true).pend = false := hp
  rw [R.mv_false_npend _ hp', R.mv_false_npend _ hp, R.newTrig_mv_true]
  have hl := (hag.2 R.a rfl).1
  have hm := hag.1
  rcases R.newTrig s with _ | j
  · exact ⟨fun j _ => by simp [hm], by simpa using hl, by simp, rfl, by simp [hp]⟩
  · exact ⟨fun j _ => by simp [hm], by simpa using hl, by simp, rfl, rfl⟩

/-- Steps on different objects commute (Case A). -/
lemma commute_of_ne {j : ι} (hp : s.pend = false) (ha : s.c.Poised R.a i)
    (hb : s.c.Poised R.b j) (hij : i ≠ j) :
    R.mv (R.mv s false) true = R.mv (R.mv s true) false := by
  have hp' : (R.mv s true).pend = false := hp
  rw [R.mv_false_npend _ hp', R.mv_false_npend _ hp, R.newTrig_mv_true]
  have hc := stepP_comm s.c R.hab hij ha hb
  rcases R.newTrig s with _ | l
  · simp only [mv_true]; rw [hc]
  · simp only [mv_true]; rw [hc]

/-- Two steps on the same object that commute at its value, with the same responses in both
orders, commute (Case C). -/
lemma stepP_stepP_eq (C : Cfg A) (ha : A.act (C.loc R.a) = .access i o k)
    (hb : A.act (C.loc R.b) = .access i o' k')
    (hst : ((T i).δ ((T i).δ (C.mem i) o).1 o').1 = ((T i).δ ((T i).δ (C.mem i) o').1 o).1)
    (hra : ((T i).δ (C.mem i) o).2 = ((T i).δ ((T i).δ (C.mem i) o').1 o).2)
    (hrb : ((T i).δ (C.mem i) o').2 = ((T i).δ ((T i).δ (C.mem i) o).1 o').2) :
    (C.stepP R.a).stepP R.b = (C.stepP R.b).stepP R.a := by
  have hab := R.hab
  have hb' : A.act ((C.stepP R.a).loc R.b) = .access i o' k' := by
    rw [stepP_loc_other C (Ne.symm hab)]; exact hb
  have ha' : A.act ((C.stepP R.b).loc R.a) = .access i o k := by
    rw [stepP_loc_other C hab]; exact ha
  rw [stepP_of_access _ hb', stepP_of_access _ ha', stepP_of_access C ha, stepP_of_access C hb]
  simp only [Function.update_self, Function.update_idem]
  congr 1
  · rw [Function.update_comm (Ne.symm hab), ← hra, ← hrb]
  · rw [hst]

lemma commute_of_commuteAt (hp : s.pend = false) (ha : A.act (s.c.loc R.a) = .access i o k)
    (hb : A.act (s.c.loc R.b) = .access i o' k')
    (hst : ((T i).δ ((T i).δ (s.c.mem i) o).1 o').1 =
      ((T i).δ ((T i).δ (s.c.mem i) o').1 o).1)
    (hra : ((T i).δ (s.c.mem i) o).2 = ((T i).δ ((T i).δ (s.c.mem i) o').1 o).2)
    (hrb : ((T i).δ (s.c.mem i) o').2 = ((T i).δ ((T i).δ (s.c.mem i) o).1 o').2) :
    R.mv (R.mv s false) true = R.mv (R.mv s true) false := by
  have hp' : (R.mv s true).pend = false := hp
  rw [R.mv_false_npend _ hp', R.mv_false_npend _ hp, R.newTrig_mv_true]
  have hc := R.stepP_stepP_eq s.c ha hb hst hra hrb
  rcases R.newTrig s with _ | l
  · simp only [mv_true]; rw [hc]
  · simp only [mv_true]; rw [hc]

/-- Case B: `a`'s next operation is its first triggering operation on `i` (so `a` crashes right
after it) and `b` is poised on `i`. Then `σ a crash` and `σ b a crash` agree for `a` on every
object except `i`, and on `i` too if `a`'s operation leaves `i` with the same value after `b`'s
operation as alone. -/
lemma hide_agA (hp : s.pend = false) (ha : A.act (s.c.loc R.a) = .access i o k)
    (hb : A.act (s.c.loc R.b) = .access i o' k') (ht : R.newTrig s = some i) (S : Set ι)
    (hS : i ∈ S ∨ ((T i).δ ((T i).δ (s.c.mem i) o').1 o).1 = ((T i).δ (s.c.mem i) o).1) :
    R.AgA S (R.mv (R.mv s false) false) (R.mv (R.mv (R.mv s true) false) false) := by
  have hab := R.hab
  have hp' : (R.mv s true).pend = false := hp
  rw [R.mv_false_npend _ hp', R.mv_false_npend _ hp, R.newTrig_mv_true, ht]
  simp only [mv_true]
  rw [R.mv_false_pend _ rfl, R.mv_false_pend _ rfl]
  have ha' : A.act ((s.c.stepP R.b).loc R.a) = .access i o k := by
    rw [stepP_loc_other s.c hab]; exact ha
  refine ⟨fun j hj => ?_, ?_, by simp, rfl, rfl⟩
  · simp only [crash_mem]
    by_cases hji : j = i
    · subst hji
      rcases hS with h | h
      · exact absurd h hj
      · rw [stepP_mem_self _ ha, stepP_mem_self _ ha', stepP_mem_self _ hb, h]
    · rw [stepP_mem_other _ ha hji, stepP_mem_other _ ha' hji, stepP_mem_other _ hb hji]
  · simp

end Restr

end Podc.RecoverableHierarchy
