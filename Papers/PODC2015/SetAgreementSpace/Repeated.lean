import Papers.PODC2015.SetAgreementSpace.Counterexample

/-!
# The repeated algorithm (Figure 4) is not obstruction-free either

Figure 4 extends Figure 3 to repeated set agreement: processes store tuples
`(pref, id, t, history)` (instance number `t`, decided values so far), adopt the history of a
process found in a higher instance (line 15), decide when all tuples are `t`-tuples and at most `m`
tuples are different (line 17), and otherwise adopt the value of the first duplicated `t`-tuple
(lines 22–24) or advance `i` (line 25). `fig4 fix n m r` is this algorithm as a CSLib `Impl`
(`fix = true` adds the same guard as for Figure 3: adopt only a value different from `pref`).

While every process is in its first instance and nobody has decided, Figure 4 behaves exactly like
Figure 3 (tuples `(v, p, 1, [])` instead of pairs `(v, p)`). The livelock of
`Counterexample.lean` never decides, so it transfers (`fig4_not_mObstructionFree`): the termination
claim of Theorem 8 for the algorithm of Figure 4 is false as well.

The transfer is a step-by-step simulation (`Sim`) between configurations of `fig4` and `fig3`.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

/-- Local state of a process in Figure 4. -/
structure Loc4 (V : Type) (r : ℕ) where
  /-- Program counter. -/
  pc : PC
  /-- Current instance (persistent). -/
  t : ℕ
  /-- Decided values of the instances so far (persistent). -/
  hist : List V
  /-- Preferred value. -/
  pref : V
  /-- Next component to update (persistent). -/
  i : Fin r
  /-- Value to return. -/
  out : Option V

variable {V : Type} [DecidableEq V] [Inhabited V] {n r : ℕ}

/-- Tuples `(value, id, instance, history)`. -/
abbrev Tup (V : Type) (n : ℕ) := V × Fin n × ℕ × List V

/-- The base objects of Figure 4: one snapshot object of tuples. -/
abbrev Mem4 (V : Type) (n r : ℕ) : Unit → ObjSpec := fun _ => snapObjOpt r (Tup V n)

/-- The history of the first tuple of an instance higher than `t` (line 15), if any. -/
def higherHist (s : Fin r → Option (Tup V n)) (t : ℕ) : Option (List V) :=
  ((List.finRange r).filterMap fun j => (s j).bind fun x =>
    if t < x.2.2.1 then some x.2.2.2 else none).head?

/-- `j₁` is the first component of a duplicated `t`-tuple. -/
def IsDupT (s : Fin r → Option (Tup V n)) (t : ℕ) (j₁ : Fin r) : Prop :=
  (s j₁).any (fun x => decide (x.2.2.1 = t)) = true ∧ ∃ j₂, j₁ < j₂ ∧ s j₂ = s j₁

instance (s : Fin r → Option (Tup V n)) (t : ℕ) (j₁ : Fin r) : Decidable (IsDupT s t j₁) := by
  unfold IsDupT; infer_instance

/-- `min {j₁ : ∃ j₂ > j₁, s[j₁], s[j₂] identical t-tuples}`, and the value there. -/
def dupValT (s : Fin r → Option (Tup V n)) (t : ℕ) : Option V :=
  ((List.finRange r).find? (fun j => decide (IsDupT s t j))).bind fun j => (s j).map Prod.fst

/-- Line 17: at most `m` different tuples, and every entry is a tuple of instance `≥ t`
(no `⊥`, no tuple of a lower instance; higher instances were handled at line 15). -/
def DecideCond4 (m : ℕ) (s : Fin r → Option (Tup V n)) (t : ℕ) : Prop :=
  (Finset.univ.image s).card ≤ m ∧ ∀ j, (s j).any (fun x => decide (t ≤ x.2.2.1)) = true

instance (m : ℕ) (s : Fin r → Option (Tup V n)) (t : ℕ) : Decidable (DecideCond4 m s t) := by
  unfold DecideCond4; infer_instance

/-- Line 22 (with `fix`: and the value of the first duplicated `t`-tuple is not `pref`). -/
def AdoptCond4 (fix : Bool) (s : Fin r → Option (Tup V n)) (l : Loc4 V r) (id : Fin n) : Prop :=
  (∀ j, j ≠ l.i → s j ≠ none ∧ s j ≠ some (l.pref, id, l.t, l.hist)) ∧
    (∃ j₁ j₂, j₁ ≠ j₂ ∧ s j₁ = s j₂ ∧ (s j₁).any (fun x => decide (x.2.2.1 = l.t)) = true) ∧
    (fix = true → dupValT s l.t ≠ some l.pref)

noncomputable instance (fix : Bool) (s : Fin r → Option (Tup V n)) (l : Loc4 V r) (id : Fin n) :
    Decidable (AdoptCond4 fix s l id) := by
  unfold AdoptCond4; classical infer_instance

/-- The value of the first duplicated tuple (line 18). -/
def dupVal4 (s : Fin r → Option (Tup V n)) : Option V :=
  ((List.finRange r).find? (fun j => decide (∃ j₂, j < j₂ ∧ s j₂ = s j))).bind
    fun j => (s j).map Prod.fst

/-- The local state after a scan returning `s` (lines 15–25). -/
noncomputable def afterScan4 [NeZero r] (fix : Bool) (m : ℕ) (id : Fin n) (l : Loc4 V r)
    (s : Fin r → Option (Tup V n)) : Loc4 V r :=
  match higherHist s l.t with
  | some his => { l with pc := .ret, hist := his, out := some (his[l.t - 1]?.getD l.pref) }
  | none =>
    if DecideCond4 m s l.t then
      { l with pc := .ret, hist := l.hist ++ [(dupVal4 s).getD l.pref],
               out := some ((dupVal4 s).getD l.pref) }
    else if AdoptCond4 fix s l id then { l with pc := .upd, pref := (dupValT s l.t).getD l.pref }
    else { l with pc := .upd, i := l.i + 1 }

/-- **Figure 4** as a CSLib implementation of repeated set agreement from one `r`-component
snapshot object. -/
noncomputable def fig4 (fix : Bool) (n m r : ℕ) [NeZero r] :
    Impl (saObj V) (Mem4 V n r) (Fin n) (Loc4 V r) where
  memInit _ := fun _ => none
  locInit _ := ⟨.idle, 0, [], default, 0, none⟩
  invoke _ l v :=
    if l.t + 1 ≤ l.hist.length then
      { l with pc := .ret, t := l.t + 1, out := some (l.hist[l.t]?.getD v) }
    else { l with pc := .upd, t := l.t + 1, pref := v, out := none }
  act id l := match l.pc with
    | .upd => .access () (.update l.i (l.pref, id, l.t, l.hist)) (fun _ => { l with pc := .scan })
    | .scan => .access () .scan (fun s => afterScan4 fix m id l s)
    | .ret => .ret (l.out.getD default) { l with pc := .idle }
    | .idle => .ret (default : V) l

/-! ### Simulation of Figure 3 by Figure 4 on one-shot executions -/

section Sim

variable [NeZero r]

/-- A pair of Figure 3 as a first-instance tuple of Figure 4. -/
def embed (x : V × Fin n) : Tup V n := (x.1, x.2, 1, [])

lemma embed_injective : Function.Injective (embed (V := V) (n := n)) := by
  intro x y h; simp only [embed, Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.1

/-- The Figure 4 local state corresponding to a Figure 3 local state (first instance). -/
def lift (l : Loc V r) : Loc4 V r :=
  ⟨l.pc, if l.pc = .idle ∧ l.out = none then 0 else 1, l.out.toList, l.pref, l.i, l.out⟩

/-- The simulation relation between configurations of `fig4` and `fig3`, plus invariants of
`fig3`. -/
def Sim (C₄ : Config (saObj V) (Mem4 V n r) (Fin n) (Loc4 V r))
    (C₃ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)) : Prop :=
  C₄.pend = C₃.pend ∧ C₄.mem () = (fun j => (C₃.mem () j).map embed) ∧
    (∀ p, C₄.loc p = lift (C₃.loc p)) ∧
    (∀ p, C₃.pend p = none ↔ (C₃.loc p).pc = .idle) ∧
    (∀ p, ((C₃.loc p).pc = .upd ∨ (C₃.loc p).pc = .scan) → (C₃.loc p).out = none) ∧
    (∀ p, (C₃.loc p).pc = .ret → (C₃.loc p).out ≠ none) ∧
    (∀ p, (C₃.loc p).pc = .idle → (C₃.loc p).out = none → (C₃.loc p).i = 0)

variable {s : Fin r → Cell V n}

lemma map_embed_eq_iff {j₁ j₂ : Fin r} :
    (s j₁).map embed = (s j₂).map embed ↔ s j₁ = s j₂ :=
  (Option.map_injective embed_injective).eq_iff

lemma dupVal4_eq : dupVal4 (fun j => (s j).map embed) = dupVal s := by
  unfold dupVal4 dupVal firstDup
  have : (fun j => decide (∃ j₂, j < j₂ ∧ (s j₂).map embed = (s j).map embed)) =
      (fun j => decide (IsDup s j)) := by
    funext j; simp only [map_embed_eq_iff, IsDup]
  rw [this]
  cases (List.finRange r).find? (fun j => decide (IsDup s j)) with
  | none => rfl
  | some j => cases h : s j <;> simp [h, embed]

lemma dupValT_eq {i : Fin r} (hs : ∀ j, j ≠ i → s j ≠ none) :
    dupValT (fun j => (s j).map embed) 1 = dupVal s := by
  unfold dupValT dupVal firstDup
  have : (fun j => decide (IsDupT (fun j => (s j).map embed) 1 j)) =
      (fun j => decide (IsDup s j)) := by
    funext j
    simp only [IsDupT, IsDup, map_embed_eq_iff, decide_eq_decide]
    constructor
    · exact fun h => h.2
    · rintro ⟨j₂, hlt, heq⟩
      refine ⟨?_, j₂, hlt, heq⟩
      cases h : s j with
      | some x => simp [embed]
      | none =>
        exfalso
        by_cases hj : j = i
        · exact hs j₂ (by rintro rfl; exact absurd hlt (by rw [hj]; exact lt_irrefl _))
            (heq.trans h)
        · exact hs j hj h
  rw [this]
  cases (List.finRange r).find? (fun j => decide (IsDup s j)) with
  | none => rfl
  | some j => cases h : s j <;> simp [h, embed]

lemma higherHist_embed : higherHist (fun j => (s j).map embed) 1 = none := by
  unfold higherHist
  rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]
  intro j _
  cases h : s j <;> simp [h, embed]

lemma decideCond4_iff {m : ℕ} : DecideCond4 m (fun j => (s j).map embed) 1 ↔ DecideCond m s := by
  unfold DecideCond4 DecideCond
  have hcard : (Finset.univ.image fun j => (s j).map embed).card = (Finset.univ.image s).card := by
    rw [show (fun j => (s j).map embed) = Option.map embed ∘ s from rfl, ← Finset.image_image,
      Finset.card_image_of_injective _ (Option.map_injective embed_injective)]
  rw [hcard]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  cases h : s j <;> simp [h, embed]

lemma adoptCond4_iff {fix : Bool} {l : Loc V r} {id : Fin n} (hout : l.out = none)
    (hpc : l.pc = .scan) :
    AdoptCond4 fix (fun j => (s j).map embed) (lift l) id ↔ AdoptCond fix s l.i l.pref id := by
  have hl : lift l = ⟨.scan, 1, [], l.pref, l.i, none⟩ := by simp [lift, hout, hpc]
  rw [hl]
  unfold AdoptCond4 AdoptCond
  have h1 : (∀ j, j ≠ l.i → (s j).map embed ≠ none ∧ (s j).map embed ≠ some (l.pref, id, 1, [])) ↔
      (∀ j, j ≠ l.i → s j ≠ none ∧ s j ≠ some (l.pref, id)) := by
    apply forall_congr'; intro j; apply imp_congr_right; intro _
    cases s j with
    | none => simp
    | some x => simp [embed, Prod.ext_iff]
  constructor
  · rintro ⟨ha, ⟨j₁, j₂, hne, heq, -⟩, hc⟩
    have ha' := h1.1 ha
    refine ⟨ha', ⟨j₁, j₂, hne, map_embed_eq_iff.1 heq⟩, fun hf => ?_⟩
    rw [← dupValT_eq (fun j hj => (ha' j hj).1)]; exact hc hf
  · rintro ⟨ha, ⟨j₁, j₂, hne, heq⟩, hc⟩
    refine ⟨h1.2 ha, ⟨j₁, j₂, hne, by simp only [heq], ?_⟩, fun hf => ?_⟩
    · cases h : s j₁ with
      | some x => simp [h, embed]
      | none =>
        exfalso
        by_cases hj : j₁ = l.i
        · exact (ha j₂ (by rintro rfl; exact hne hj)).1 (heq ▸ h)
        · exact (ha j₁ hj).1 h
    · simp only
      rw [dupValT_eq (fun j hj => (ha j hj).1)]; exact hc hf

variable {fix : Bool} {m : ℕ}

lemma afterScan4_lift {l : Loc V r} {id : Fin n} (hout : l.out = none) (hpc : l.pc = .scan) :
    afterScan4 fix m id (lift l) (fun j => (s j).map embed) = lift (afterScan fix m id l s) := by
  have hl : lift l = ⟨.scan, 1, [], l.pref, l.i, none⟩ := by simp [lift, hout, hpc]
  have hadopt := adoptCond4_iff (s := s) (fix := fix) (id := id) hout hpc
  rw [hl] at hadopt ⊢
  unfold afterScan4 afterScan
  simp only [higherHist_embed]
  by_cases hd : DecideCond m s
  · rw [if_pos (decideCond4_iff.2 hd), if_pos hd, dupVal4_eq]
    simp [lift, hpc]
  · rw [if_neg (fun h => hd (decideCond4_iff.1 h)), if_neg hd]
    by_cases ha : AdoptCond fix s l.i l.pref id
    · rw [if_pos (hadopt.2 ha), if_pos ha, dupValT_eq (fun j hj => (ha.1 j hj).1)]
      simp [lift, hout]
    · rw [if_neg (fun h => ha (hadopt.1 h)), if_neg ha]
      simp [lift, hout]

lemma afterScan_pc (l : Loc V r) (id : Fin n) :
    (afterScan fix m id l s).pc = .ret ∧ (afterScan fix m id l s).out ≠ none ∨
      (afterScan fix m id l s).pc = .upd ∧ (afterScan fix m id l s).out = l.out := by
  unfold afterScan
  split_ifs <;> simp

lemma lift_pc (l : Loc V r) : (lift l).pc = l.pc := rfl

/-- **Simulation step.** Every step of Figure 3 from a configuration related to a Figure 4
configuration is matched by the same step of Figure 4, provided an invocation is the first one
of its process (`out = none`). -/
lemma sim_step {C₄ : Config (saObj V) (Mem4 V n r) (Fin n) (Loc4 V r)}
    {C₃ C₃' : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} (hS : Sim C₄ C₃)
    {ℓ : Label (Fin n) (saObj V)} (h₃ : (fig3 fix n m r).step C₃ ℓ = some C₃')
    (hinv : ∀ p v, ℓ = .inv p v → (C₃.loc p).out = none) :
    ∃ C₄', (fig4 fix n m r).step C₄ ℓ = some C₄' ∧ Sim C₄' C₃' := by
  obtain ⟨hpend, hmem, hloc, hidle, hout, hret, hi0⟩ := hS
  cases ℓ with
  | inv p v =>
    obtain ⟨hp, -, hpend', hloc', hmem'⟩ := Impl.step_inv h₃
    have hp4 : C₄.pend p = none := by rw [hpend]; exact hp
    have hpc : (C₃.loc p).pc = .idle := (hidle p).1 hp
    have ho : (C₃.loc p).out = none := hinv p v rfl
    have hi : (C₃.loc p).i = 0 := hi0 p hpc ho
    refine ⟨_, Impl.step_inv_eq_some hp4 trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hpend', hpend]
    · rw [hmem', hmem]
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq
        simp only [Function.update_self, hloc]
        simp [fig4, fig3, lift, hpc, ho, hi]
      · simp only [Function.update_of_ne hq, hloc]
    · intro q
      rw [hpend', hloc']
      by_cases hq : q = p
      · subst hq; simp [fig3]
      · simp only [Function.update_of_ne hq]; exact hidle q
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq; simp [fig3]
      · simp only [Function.update_of_ne hq]; exact hout q
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq; simp [fig3]
      · simp only [Function.update_of_ne hq]; exact hret q
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq; simp [fig3]
      · simp only [Function.update_of_ne hq]; exact hi0 q
  | tau p =>
    have hp := (Impl.step_tau h₃).1
    have hp4 : C₄.pend p ≠ none := by rw [hpend]; exact hp
    cases hpc : (C₃.loc p).pc with
    | idle => exact absurd ((hidle p).2 hpc) hp
    | ret => simp [Impl.step, hp, fig3, hpc] at h₃
    | upd =>
      rw [fig3_step_upd hp hpc, Option.some.injEq] at h₃
      subst h₃
      have ho : (C₃.loc p).out = none := hout p (.inl hpc)
      have hact4 : (fig4 fix n m r).act p (C₄.loc p) =
          .access () (.update (C₃.loc p).i ((C₃.loc p).pref, p, 1, []))
            (fun _ => lift { C₃.loc p with pc := .scan }) := by
        rw [hloc]; simp [fig4, lift, hpc, ho]
      refine ⟨_, Impl.step_tau_eq_some hp4 hact4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hpend]
      · funext j
        simp only [Function.update_self, snapObjOpt_update, hmem]
        by_cases hj : j = (C₃.loc p).i
        · subst hj; simp [embed]
        · simp [Function.update_of_ne hj]
      · intro q
        by_cases hq : q = p
        · subst hq; simp
        · simp only [Function.update_of_ne hq, hloc]
      · intro q
        by_cases hq : q = p
        · subst hq; simp [hp]
        · simp only [Function.update_of_ne hq]; exact hidle q
      · intro q
        by_cases hq : q = p
        · subst hq; simp [ho]
        · simp only [Function.update_of_ne hq]; exact hout q
      · intro q
        by_cases hq : q = p
        · subst hq; simp
        · simp only [Function.update_of_ne hq]; exact hret q
      · intro q
        by_cases hq : q = p
        · subst hq; simp
        · simp only [Function.update_of_ne hq]; exact hi0 q
    | scan =>
      rw [fig3_step_scan hp hpc, Option.some.injEq] at h₃
      subst h₃
      have ho : (C₃.loc p).out = none := hout p (.inr hpc)
      have hact4 : (fig4 fix n m r).act p (C₄.loc p) =
          .access () .scan (fun s => afterScan4 fix m p (lift (C₃.loc p)) s) := by
        rw [hloc]; simp [fig4, lift_pc, hpc]
      have hcases := afterScan_pc (fix := fix) (m := m) (s := C₃.mem ()) (C₃.loc p) p
      refine ⟨_, Impl.step_tau_eq_some hp4 hact4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [hpend]
      · funext j; simp [hmem]
      · intro q
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self, snapObjOpt_scan]
          rw [hmem, afterScan4_lift ho hpc]
        · simp only [Function.update_of_ne hq, hloc]
      · intro q
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self]
          rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, hp]
        · simp only [Function.update_of_ne hq]; exact hidle q
      · intro q
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self]
          rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, ho]
        · simp only [Function.update_of_ne hq]; exact hout q
      · intro q
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self]
          rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
        · simp only [Function.update_of_ne hq]; exact hret q
      · intro q
        by_cases hq : q = p
        · subst hq
          simp only [Function.update_self]
          rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
        · simp only [Function.update_of_ne hq]; exact hi0 q
  | ret p w =>
    obtain ⟨hp, hpend', hmem', l', hact, hloc'⟩ := Impl.step_ret h₃
    have hpc : (C₃.loc p).pc = .ret := by
      cases hc : (C₃.loc p).pc with
      | ret => rfl
      | idle => exact absurd ((hidle p).2 hc) hp
      | upd => simp [fig3, hc] at hact
      | scan => simp [fig3, hc] at hact
    simp only [fig3, hpc, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact
    have hon : (C₃.loc p).out ≠ none := hret p hpc
    have hp4 : C₄.pend p ≠ none := by rw [hpend]; exact hp
    have hact4 : (fig4 fix n m r).act p (C₄.loc p) =
        .ret ((C₃.loc p).out.getD default) { lift (C₃.loc p) with pc := .idle } := by
      rw [hloc]; simp [fig4, lift_pc, hpc, lift]
    refine ⟨_, Impl.step_ret_eq_some hp4 hact4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hpend', hpend]
    · rw [hmem', hmem]
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq
        simp only [Function.update_self]
        simp [lift, hpc, hon]
      · simp only [Function.update_of_ne hq, hloc]
    · intro q
      rw [hpend', hloc']
      by_cases hq : q = p
      · subst hq; simp
      · simp only [Function.update_of_ne hq]; exact hidle q
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq; simp
      · simp only [Function.update_of_ne hq]; exact hout q
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq; simp
      · simp only [Function.update_of_ne hq]; exact hret q
    · intro q
      rw [hloc']
      by_cases hq : q = p
      · subst hq; simp [hon]
      · simp only [Function.update_of_ne hq]; exact hi0 q

lemma sim_init : Sim (fig4 (V := V) fix n m r).initCfg (fig3 (V := V) fix n m r).initCfg := by
  refine ⟨rfl, ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_⟩
  · funext j; rfl
  · simp [Impl.initCfg, fig4, fig3, lift]
  · simp [Impl.initCfg, fig3]
  · simp [Impl.initCfg, fig3]
  · simp [Impl.initCfg, fig3]
  · simp [Impl.initCfg, fig3]

/-- Every one-shot execution of Figure 3 is an execution of Figure 4, with related final
configurations. -/
lemma sim_run {α : List (Label (Fin n) (saObj V))}
    {C₃ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)}
    (h : (fig3 fix n m r).run α = some C₃) (hos : OneShot α) :
    ∃ C₄, (fig4 fix n m r).run α = some C₄ ∧ Sim C₄ C₃ := by
  suffices H : OneShot α → (∃ C₄, (fig4 fix n m r).run α = some C₄ ∧ Sim C₄ C₃) ∧
      ∀ p, opsOf α p = [] → (C₃.loc p).out = none ∧ C₃.pend p = none from (H hos).1
  refine Impl.run_induction (Q := fun α C₃ => OneShot α →
    (∃ C₄, (fig4 fix n m r).run α = some C₄ ∧ Sim C₄ C₃) ∧
      ∀ p, opsOf α p = [] → (C₃.loc p).out = none ∧ C₃.pend p = none) ?_ ?_ h
  · intro _
    exact ⟨⟨_, rfl, sim_init⟩, fun p _ => by simp [Impl.initCfg, fig3]⟩
  · intro β C ℓ C' _ ih hstep hos'
    obtain ⟨⟨C₄, hrun₄, hS⟩, hfresh⟩ := ih hos'.of_append
    have hinv : ∀ p v, ℓ = .inv p v → (C.loc p).out = none := by
      rintro p v rfl
      have h1 := hos' p
      simp only [opsOf_append, List.length_append] at h1
      have : opsOf β p = [] := by
        rw [← List.length_eq_zero_iff]
        have : (opsOf [Label.inv p v] p).length = 1 := by simp [opsOf, Label.invOf]
        omega
      exact (hfresh p this).1
    obtain ⟨C₄', h₄, hS'⟩ := sim_step hS hstep hinv
    refine ⟨⟨C₄', by rw [Impl.run_concat, hrun₄]; exact h₄, hS'⟩, fun q hq => ?_⟩
    rw [opsOf_append, List.append_eq_nil_iff] at hq
    obtain ⟨ho, hpn⟩ := hfresh q hq.1
    by_cases hpq : ℓ.proc = q
    · exfalso
      cases ℓ with
      | inv p v => simp [Label.proc] at hpq; subst hpq; simp [opsOf, Label.invOf] at hq
      | tau p => simp [Label.proc] at hpq; subst hpq; exact (Impl.step_tau hstep).1 hpn
      | ret p w => simp [Label.proc] at hpq; subst hpq; exact (Impl.step_ret hstep).1 hpn
    · obtain ⟨h1, h2⟩ := Impl.step_other hstep hpq
      exact ⟨h1 ▸ ho, h2 ▸ hpn⟩

lemma nextLabel_sim {C₄ : Config (saObj V) (Mem4 V n r) (Fin n) (Loc4 V r)}
    {C₃ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} (hS : Sim C₄ C₃) (p : Fin n) :
    (fig4 fix n m r).nextLabel C₄ p = (fig3 fix n m r).nextLabel C₃ p := by
  unfold Impl.nextLabel
  rw [hS.2.2.1 p]
  cases hpc : (C₃.loc p).pc <;> simp [fig4, fig3, lift_pc, hpc, lift]

lemma sim_soloStep {C₄ : Config (saObj V) (Mem4 V n r) (Fin n) (Loc4 V r)}
    {C₃ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} (hS : Sim C₄ C₃) (p : Fin n) :
    Sim ((fig4 fix n m r).soloStep p C₄) ((fig3 fix n m r).soloStep p C₃) := by
  by_cases hp : C₃.pend p = none
  · have hp4 : C₄.pend p = none := by rw [hS.1]; exact hp
    simp only [Impl.soloStep, hp, hp4, if_true]; exact hS
  · have hp4 : C₄.pend p ≠ none := by rw [hS.1]; exact hp
    obtain ⟨C₃', h₃⟩ := Option.isSome_iff_exists.1
      ((fig3 fix n m r).step_nextLabel_isSome C₃ p hp)
    have hni : ∀ q v, (fig3 fix n m r).nextLabel C₃ p = .inv q v → (C₃.loc q).out = none := by
      intro q v h
      have := (fig3 fix n m r).nextLabel_invOf C₃ p q
      rw [h] at this; simp [Label.invOf] at this
    obtain ⟨C₄', h₄, hS'⟩ := sim_step hS h₃ hni
    rw [← nextLabel_sim hS] at h₄
    simp only [Impl.soloStep, hp, hp4, if_false, h₃, h₄, Option.getD_some]
    exact hS'

/-- **Figure 4 livelocks** (from a reachable configuration, process `0` running solo never
returns), for `1 ≤ m < n` and `r ≥ 2m + 1`. -/
theorem fig4_livelock (v : V) (hm : 1 ≤ m) (hmn : m < n) (hr : 2 * m + 1 ≤ r) :
    ∃ α C, (fig4 (V := V) false n m r).run α = some C ∧ OneShot α ∧
      C.pend ⟨0, by omega⟩ ≠ none ∧
      ∀ k, (((fig4 (V := V) false n m r).soloStep ⟨0, by omega⟩)^[k] C).pend ⟨0, by omega⟩ ≠
        none := by
  obtain ⟨α, C₃, h₃, hos, hp, hloop⟩ := fig3_livelock (V := V) (n := n) (m := m) (r := r) v hm hmn hr
  obtain ⟨C₄, h₄, hS⟩ := sim_run h₃ hos
  have hiter : ∀ k, Sim (((fig4 (V := V) false n m r).soloStep ⟨0, by omega⟩)^[k] C₄)
      (((fig3 (V := V) false n m r).soloStep ⟨0, by omega⟩)^[k] C₃) := by
    intro k
    induction k with
    | zero => exact hS
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact sim_soloStep ih _
  exact ⟨α, C₄, h₄, hos, by rw [hS.1]; exact hp, fun k => by rw [(hiter k).1]; exact hloop k⟩

end Sim

/-- **Figure 4 is not `m`-obstruction-free** (refutes the termination part of Theorem 8 for the
algorithm of Figure 4): for all `1 ≤ m ≤ k < n`, with `r = n + 2m - k` components, the algorithm
is not `m'`-obstruction-free for any `m' ≥ 1` — already in executions where every process invokes
`Propose` at most once. -/
theorem fig4_not_mObstructionFree {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k < n)
    [NeZero (n + 2 * m - k)] {m' : ℕ} (hm' : 1 ≤ m') :
    ¬ (fig4 (V := V) false n m (n + 2 * m - k)).MObstructionFreeOn m' (fun _ => True) := by
  obtain ⟨α, C, hrun, -, -, hloop⟩ :=
    fig4_livelock (V := V) (n := n) (m := m) (r := n + 2 * m - k) default hm (by omega)
      (by omega)
  exact Impl.not_mObstructionFreeOn_of_solo (fun _ _ _ => trivial) (fun _ _ _ => trivial) hrun
    trivial hloop hm'

end Podc.SetAgreementSpace
