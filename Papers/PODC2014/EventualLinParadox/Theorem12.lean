import Papers.PODC2014.EventualLinParadox.ImplModel
import Papers.PODC2014.EventualLinParadox.Safety
import Papers.PODC2014.EventualLinParadox.Locality

/-!
# Theorem 12 and Proposition 14: eventually linearizable objects are useless for linearizability

* `projLab`, `agreeP_proj` — in the model with eventually linearizable base objects the
  configuration has no shared component, so a process's behaviour depends only on its own
  steps (projection to one process).
* `localImpl` — the paper's construction for 4 ⇒ 1: every base object is replaced by a local
  copy at each process (base operations are applied to the copy, with responses chosen by the
  base object's specification).
* `theorem12` — **Theorem 12** (the four conditions are equivalent).
* `prop14` — **Proposition 14** (deterministic types: a linearizable obstruction-free
  implementation from eventually linearizable objects exists iff the type is trivial).
-/

namespace Podc.EventualLinParadox

/-! ### Projection to one process -/

section Proj

variable {P HOp HRes X BOp BRes L : Type} [DecidableEq P] (I : Impl P HOp HRes X BOp BRes L)

/-- Two configurations agree on process `p`. -/
structure AgreeP (p : P) (c c' : ECfg P L) : Prop where
  loc : c.loc p = c'.loc p
  pend : c.pend p = c'.pend p
  bpend : c.bpend p = c'.bpend p

lemma elStep_agree {c c' : ECfg P L} (n : ℕ) (l : ELab P HOp BRes) (h : AgreeP l.proc c c') :
    Option.Rel (fun o o' => AgreeP l.proc o.1 o'.1 ∧ o.2 = o'.2)
      (elStep I n c l) (elStep I n c' l) := by
  obtain ⟨hl, hp, hb⟩ := h
  cases l with
  | inv p op =>
    simp only [ELab.proc] at hl hp hb
    simp only [elStep, hp, hl]
    split_ifs
    · exact Option.Rel.some ⟨⟨by simp [ELab.proc], by simp [ELab.proc], hb⟩, rfl⟩
    · exact Option.Rel.none
  | step p =>
    simp only [ELab.proc] at hl hp hb
    simp only [elStep, hp, hb, hl]
    rcases c'.pend p with _ | a
    · exact Option.Rel.none
    rcases c'.bpend p with _ | b
    · cases I.act p (c'.loc p) with
      | call x o k => exact Option.Rel.some ⟨⟨hl, hp, by simp [ELab.proc]⟩, rfl⟩
      | loc l => exact Option.Rel.some ⟨⟨by simp [ELab.proc], hp, hb⟩, rfl⟩
      | ret r l => exact Option.Rel.some ⟨⟨by simp [ELab.proc], by simp [ELab.proc], hb⟩, rfl⟩
    · exact Option.Rel.none
  | bres p r =>
    simp only [ELab.proc] at hl hp hb
    simp only [elStep, hb, hl]
    rcases c'.bpend p with _ | b
    · exact Option.Rel.none
    · cases I.act p (c'.loc p) with
      | call x o k => exact Option.Rel.some ⟨⟨by simp [ELab.proc], hp, by simp [ELab.proc]⟩, rfl⟩
      | loc l => exact Option.Rel.none
      | ret r l => exact Option.Rel.none

lemma elStep_other {c : ECfg P L} {n : ℕ} {l : ELab P HOp BRes} {o} (h : elStep I n c l = some o)
    {p : P} (hp : l.proc ≠ p) : AgreeP p c o.1 := by
  cases l with
  | inv q op =>
    simp only [ELab.proc] at hp
    simp only [elStep] at h
    split_ifs at h
    cases h
    exact ⟨by simp [Function.update_of_ne (Ne.symm hp)], by simp [Function.update_of_ne (Ne.symm hp)], rfl⟩
  | step q =>
    simp only [ELab.proc] at hp
    simp only [elStep] at h
    rcases hq : c.pend q with _ | a <;> rw [hq] at h
    · cases h
    rcases hb : c.bpend q with _ | b <;> rw [hb] at h
    · cases hact : I.act q (c.loc q) <;> rw [hact] at h <;> cases h <;>
        exact ⟨by simp [Function.update_of_ne (Ne.symm hp)], by simp [Function.update_of_ne (Ne.symm hp)],
          by simp [Function.update_of_ne (Ne.symm hp)]⟩
    · cases h
  | bres q r =>
    simp only [ELab.proc] at hp
    simp only [elStep] at h
    rcases hb : c.bpend q with _ | b <;> rw [hb] at h
    · cases h
    · cases hact : I.act q (c.loc q) <;> rw [hact] at h <;> cases h
      exact ⟨by simp [Function.update_of_ne (Ne.symm hp)], rfl, by simp [Function.update_of_ne (Ne.symm hp)]⟩

/-- Keep only the steps of process `p`. -/
def projLab (lab : ℕ → Option (ELab P HOp BRes)) (p : P) : ℕ → Option (ELab P HOp BRes) :=
  fun n => match lab n with
    | some l => if l.proc = p then some l else none
    | none => none

lemma agreeP_proj (lab : ℕ → Option (ELab P HOp BRes)) (p : P) :
    ∀ n, AgreeP p ((elSys I).cfg (projLab lab p) n) ((elSys I).cfg lab n) := by
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    rw [elSys_cfg_succ, elSys_cfg_succ]
    rcases hl : lab n with _ | l
    · simp [projLab, hl]; exact ih
    · by_cases hlp : l.proc = p
      · subst hlp
        simp only [projLab, hl, if_true, Option.bind_some]
        have := elStep_agree I n l ih
        revert this
        generalize elStep I n ((elSys I).cfg (projLab lab l.proc) n) l = o1
        generalize elStep I n ((elSys I).cfg lab n) l = o2
        intro this
        cases this with
        | some h => exact h.1
        | none => exact ih
      · simp only [projLab, hl, hlp, if_false, Option.bind_none, Option.elim_none,
          Option.bind_some]
        rcases ho : elStep I n ((elSys I).cfg lab n) l with _ | o
        · exact ih
        · have := elStep_other I ho hlp
          exact ⟨ih.loc.trans this.loc, ih.pend.trans this.pend, ih.bpend.trans this.bpend⟩

lemma out_proj {lab : ℕ → Option (ELab P HOp BRes)} {p : P} {n : ℕ} {l : ELab P HOp BRes}
    (hl : lab n = some l) (hlp : l.proc = p) :
    Option.Rel (fun o o' => AgreeP p o.1 o'.1 ∧ o.2 = o'.2)
      ((elSys I).out (projLab lab p) n) ((elSys I).out lab n) := by
  rw [LSys.out_eq, LSys.out_eq]
  subst hlp
  have hpl : projLab lab l.proc n = some l := by simp [projLab, hl]
  rw [hpl, hl]
  simp only [Option.bind_some]
  exact elStep_agree I n l (agreeP_proj I lab l.proc n)

lemma hist_proj {lab : ℕ → Option (ELab P HOp BRes)} {p : P} {n : ℕ} {l : ELab P HOp BRes}
    (hl : lab n = some l) (hlp : l.proc = p) :
    (elSys I).hist (projLab lab p) n = (elSys I).hist lab n ∧
      (elSys I).bhist (projLab lab p) n = (elSys I).bhist lab n := by
  have := out_proj I hl hlp
  simp only [LSys.hist, LSys.bhist]
  revert this
  generalize (elSys I).out (projLab lab p) n = o1
  generalize (elSys I).out lab n = o2
  intro this
  cases this with
  | some h => simp [h.2]
  | none => simp

lemma proper_proj {lab : ℕ → Option (ELab P HOp BRes)} (h : (elSys I).Proper lab) (p : P) :
    (elSys I).Proper (projLab lab p) := by
  intro n l hl
  have hl' : lab n = some l ∧ l.proc = p := by
    simp only [projLab] at hl
    rcases hln : lab n with _ | l' <;> rw [hln] at hl
    · cases hl
    · simp only at hl; split_ifs at hl with h1; cases hl; exact ⟨rfl, h1⟩
  obtain ⟨hl1, rfl⟩ := hl'
  have := elStep_agree I n l (agreeP_proj I lab l.proc n)
  have h2 := h n l hl1
  change elStep I n _ l ≠ none at h2
  change elStep I n _ l ≠ none
  revert this h2
  generalize elStep I n ((elSys I).cfg (projLab lab l.proc) n) l = o1
  generalize elStep I n ((elSys I).cfg lab n) l = o2
  intro this h2
  cases this with
  | some _ => simp
  | none => exact absurd rfl h2

/-- A pending base operation of `p` is the one `p`'s program is about to perform, and it was
invoked by `p` (with that operation, on that object). -/
lemma el_bpend_inv (lab : ℕ → Option (ELab P HOp BRes)) :
    ∀ n p b, ((elSys I).cfg lab n).bpend p = some b →
      ((elSys I).cfg lab n).pend p ≠ none ∧ ∃ x o k,
        I.act p (((elSys I).cfg lab n).loc p) = .call x o k ∧
        (elSys I).bhist lab b = some (.inv p x o) := by
  intro n
  induction n with
  | zero => intro p b h; simp [LSys.cfg_zero, elSys] at h
  | succ n ih =>
    intro p b h
    have hbh : (elSys I).bhist lab n =
        ((lab n).bind (elStep I n ((elSys I).cfg lab n))).bind (·.2.2) := elSys_bhist I lab n
    rw [elSys_cfg_succ] at h ⊢
    revert h hbh
    generalize hc : (elSys I).cfg lab n = c at ih
    intro h hbh
    rcases hl : lab n with _ | l
    · rw [hl] at h; simpa [hl] using ih p b h
    rw [hl] at h hbh
    simp only [Option.bind_some] at h hbh ⊢
    cases l with
    | inv q op =>
      simp only [elStep] at h hbh ⊢
      split_ifs at h hbh ⊢ with hq
      · simp only [Option.elim_some] at h ⊢
        by_cases hpq : p = q
        · subst hpq; exact absurd hq (ih p b h).1
        · simpa [Function.update_of_ne hpq] using ih p b h
      · exact ih p b h
    | step q =>
      simp only [elStep] at h hbh ⊢
      rcases hpq : c.pend q with _ | a <;> rcases hbq : c.bpend q with _ | b' <;>
        simp only [hpq, hbq] at h hbh ⊢
      all_goals try exact ih p b h
      cases hact : I.act q (c.loc q) with
      | call x o k =>
        simp only [hact, Option.elim_some] at h hbh ⊢
        by_cases hpq' : p = q
        · subst hpq'
          simp at h; subst h
          refine ⟨by simp [hpq], x, o, k, hact, ?_⟩
          simpa using hbh
        · simp only [Function.update_of_ne hpq'] at h ⊢
          exact ih p b h
      | loc l' =>
        simp only [hact, Option.elim_some] at h ⊢
        by_cases hpq' : p = q
        · subst hpq'; rw [hbq] at h; cases h
        · simpa [Function.update_of_ne hpq'] using ih p b h
      | ret r l' =>
        simp only [hact, Option.elim_some] at h ⊢
        by_cases hpq' : p = q
        · subst hpq'; rw [hbq] at h; cases h
        · simpa [Function.update_of_ne hpq'] using ih p b h
    | bres q r =>
      simp only [elStep] at h hbh ⊢
      rcases hbq : c.bpend q with _ | b' <;> simp only [hbq] at h hbh ⊢
      · exact ih p b h
      cases hact : I.act q (c.loc q) with
      | call x o k =>
        simp only [hact, Option.elim_some] at h ⊢
        by_cases hpq' : p = q
        · subst hpq'; simp at h
        · rw [Function.update_of_ne hpq'] at h
          simpa [Function.update_of_ne hpq'] using ih p b h
      | loc l' => simp only [hact, Option.elim_none] at h ⊢; exact ih p b h
      | ret r' l' => simp only [hact, Option.elim_none] at h ⊢; exact ih p b h

/-- A base invocation at step `n` is performed by the process taking step `n`. -/
lemma el_bhist_inv_proc {lab : ℕ → Option (ELab P HOp BRes)} {n : ℕ} {p : P} {x : X} {o : BOp}
    (h : (elSys I).bhist lab n = some (.inv p x o)) : ∃ l, lab n = some l ∧ l.proc = p := by
  rw [elSys_bhist] at h
  generalize (elSys I).cfg lab n = c at h
  rcases hl : lab n with _ | l
  · rw [hl] at h; simp at h
  rw [hl] at h
  refine ⟨l, rfl, ?_⟩
  simp only [Option.bind_some] at h
  cases l with
  | inv q op =>
    simp only [elStep] at h; split_ifs at h <;> simp at h
  | step q =>
    show q = p
    simp only [elStep] at h
    rcases hp : c.pend q with _ | a <;> rcases hb : c.bpend q with _ | b <;> simp only [hp, hb] at h
    all_goals try simp at h
    cases hact : I.act q (c.loc q) <;> simp [hact] at h
    exact h.1
  | bres q r =>
    simp only [elStep] at h
    rcases hb : c.bpend q with _ | b <;> simp only [hb] at h
    · simp at h
    · cases hact : I.act q (c.loc q) <;> simp [hact] at h

end Proj

/-! ### Local copies of the base objects -/

section Local

variable {P HOp HRes X BOp BRes L Q' : Type} [DecidableEq P] [DecidableEq X]
  (I : Impl P HOp HRes X BOp BRes L) (B : X → ObjType Q' BOp BRes)
  (hB : ∀ x, (B x).init.Nonempty ∧ (B x).Total)

/-- The response and new state of a local copy of `x` in state `q` for operation `o`, chosen
by the (total) specification. -/
noncomputable def lch (x : X) (q : Q') (o : BOp) : BRes × Q' :=
  ⟨Classical.choose ((hB x).2 q o), Classical.choose (Classical.choose_spec ((hB x).2 q o))⟩

lemma lch_spec (x : X) (q : Q') (o : BOp) :
    (B x).δ q o (lch B hB x q o).1 (lch B hB x q o).2 :=
  Classical.choose_spec (Classical.choose_spec ((hB x).2 q o))

/-- The implementation `I'` of the proof of Theorem 12: each process keeps a local copy of every
base object and applies its base operations to its copies (the flag records that a base
operation has been "invoked", so that it takes two local steps like a base access in `I`). It
uses no shared objects. -/
noncomputable def localImpl : Impl P HOp HRes Empty Empty Empty (L × (X → Q') × Bool) where
  locInit p := (I.locInit p, fun x => (hB x).1.some, false)
  invoke p s op := (I.invoke p s.1 op, s.2.1, s.2.2)
  act p s :=
    match s.2.2, I.act p s.1 with
    | false, .call _ _ _ => .loc (s.1, s.2.1, true)
    | false, .loc l => .loc (l, s.2.1, false)
    | false, .ret r l => .ret r (l, s.2.1, false)
    | true, .call x o k =>
      .loc (k (lch B hB x (s.2.1 x) o).1, Function.update s.2.1 x (lch B hB x (s.2.1 x) o).2, false)
    | true, .loc _ => .loc s
    | true, .ret _ _ => .loc s

/-- The label of `I` simulating a label of `I'`. -/
noncomputable def mapLab (c' : ECfg P (L × (X → Q') × Bool)) :
    ELab P HOp Empty → ELab P HOp BRes
  | .inv p op => .inv p op
  | .step p =>
    match (c'.loc p).2.2, I.act p (c'.loc p).1 with
    | true, .call x o _ => .bres p (lch B hB x ((c'.loc p).2.1 x) o).1
    | _, _ => .step p
  | .bres _ r => r.elim

/-- The relation between configurations of `I` and `I'`. -/
structure SimR (c : ECfg P L) (c' : ECfg P (L × (X → Q') × Bool)) : Prop where
  loc : ∀ p, c.loc p = (c'.loc p).1
  pend : c.pend = c'.pend
  bpend : ∀ p, c.bpend p ≠ none ↔ (c'.loc p).2.2 = true
  call : ∀ p, (c'.loc p).2.2 = true → ∃ x o k, I.act p (c.loc p) = .call x o k
  flag_pend : ∀ p, (c'.loc p).2.2 = true → c'.pend p ≠ none
  bpend' : ∀ p, c'.bpend p = none

lemma step_simR {c : ECfg P L} {c' : ECfg P (L × (X → Q') × Bool)} (h : SimR I c c') (n : ℕ)
    (l : ELab P HOp Empty) :
    Option.Rel (fun o o' => SimR I o.1 o'.1 ∧ o.2.1 = o'.2.1)
      (elStep I n c (mapLab I B hB c' l)) (elStep (localImpl I B hB) n c' l) := by
  obtain ⟨hl, hp, hb, hc, hfp, hb'⟩ := h
  cases l with
  | bres p r => exact r.elim
  | inv p op =>
    simp only [mapLab, elStep, hp]
    split_ifs with h1
    · refine Option.Rel.some ⟨⟨fun q => ?_, rfl, fun q => ?_, fun q hq => ?_, fun q hq => ?_, hb'⟩, rfl⟩
      · by_cases hq : q = p
        · subst hq; simp [localImpl, hl]
        · simp [Function.update_of_ne hq, hl]
      · by_cases hq : q = p
        · subst hq; simp [localImpl, hb]
        · simp [Function.update_of_ne hq, hb]
      · by_cases hq' : q = p
        · subst hq'; simp [localImpl] at hq; exact absurd h1 (hfp q hq)
        · simp [Function.update_of_ne hq'] at hq ⊢; exact hc q hq
      · by_cases hq' : q = p
        · subst hq'; simp
        · simp [Function.update_of_ne hq'] at hq ⊢; exact hfp q hq
    · exact Option.Rel.none
  | step p =>
    rcases hpp : c'.pend p with _ | a
    · -- `p` is idle: both steps are disabled
      have hf : (c'.loc p).2.2 = false := by
        by_contra hne; exact hfp p (by simpa using hne) hpp
      simp only [mapLab, hf, elStep, hpp, hp]
      cases I.act p (c'.loc p).1 <;> exact Option.Rel.none
    · rcases hf : (c'.loc p).2.2 with _ | _
      · -- no pending base operation in `I`
        have hbp : c.bpend p = none := by by_contra hne; exact absurd ((hb p).1 hne) (by simp [hf])
        simp only [mapLab, hf, elStep, hpp, hp, hbp, hb' p, localImpl, ← hl p]
        cases hact : I.act p (c.loc p) with
        | call x o k =>
          refine Option.Rel.some ⟨⟨fun q => ?_, rfl, fun q => ?_, fun q hq => ?_, fun q hq => ?_, hb'⟩, rfl⟩
          · by_cases hq : q = p
            · subst hq; simp [hl]
            · simp [Function.update_of_ne hq, hl]
          · by_cases hq : q = p
            · subst hq; simp
            · simp [Function.update_of_ne hq, hb]
          · by_cases hq' : q = p
            · subst hq'; exact ⟨x, o, k, hact⟩
            · simp [Function.update_of_ne hq'] at hq ⊢; exact hc q hq
          · by_cases hq' : q = p
            · subst hq'; simp [hpp]
            · simp [Function.update_of_ne hq'] at hq ⊢; exact hfp q hq
        | loc l' =>
          refine Option.Rel.some ⟨⟨fun q => ?_, rfl, fun q => ?_, fun q hq => ?_, fun q hq => ?_, hb'⟩, rfl⟩
          · by_cases hq : q = p
            · subst hq; simp
            · simp [Function.update_of_ne hq, hl]
          · by_cases hq : q = p
            · subst hq; simp [hbp]
            · simp [Function.update_of_ne hq, hb]
          · by_cases hq' : q = p
            · subst hq'; simp at hq
            · simp [Function.update_of_ne hq'] at hq ⊢; exact hc q hq
          · by_cases hq' : q = p
            · subst hq'; simp at hq
            · simp [Function.update_of_ne hq'] at hq ⊢; exact hfp q hq
        | ret r l' =>
          refine Option.Rel.some ⟨⟨fun q => ?_, rfl, fun q => ?_, fun q hq => ?_, fun q hq => ?_, hb'⟩, rfl⟩
          · by_cases hq : q = p
            · subst hq; simp
            · simp [Function.update_of_ne hq, hl]
          · by_cases hq : q = p
            · subst hq; simp [hbp]
            · simp [Function.update_of_ne hq, hb]
          · by_cases hq' : q = p
            · subst hq'; simp at hq
            · simp [Function.update_of_ne hq'] at hq ⊢; exact hc q hq
          · by_cases hq' : q = p
            · subst hq'; simp at hq
            · simp [Function.update_of_ne hq'] at hq ⊢; exact hfp q hq
      · -- a pending base operation: `I` takes its response step
        obtain ⟨x, o, k, hact⟩ := hc p hf
        obtain ⟨b, hbp⟩ := Option.ne_none_iff_exists'.1 ((hb p).2 hf)
        have hact' : I.act p (c'.loc p).1 = .call x o k := by rw [← hl p]; exact hact
        simp only [mapLab, hf, hact, hact', elStep, hpp, hbp, hb' p, localImpl]
        refine Option.Rel.some ⟨⟨fun q => ?_, hp, fun q => ?_, fun q hq => ?_, fun q hq => ?_, hb'⟩, rfl⟩
        · by_cases hq : q = p
          · subst hq; simp
          · simp [Function.update_of_ne hq, hl]
        · by_cases hq : q = p
          · subst hq; simp
          · simp [Function.update_of_ne hq, hb]
        · by_cases hq' : q = p
          · subst hq'; simp at hq
          · simp [Function.update_of_ne hq'] at hq ⊢; exact hc q hq
        · by_cases hq' : q = p
          · subst hq'; simp at hq
          · simp [Function.update_of_ne hq'] at hq ⊢; exact hfp q hq

/-- How a simulated step changes the local copies, and the base event it produces. -/
def MemRel (c : ECfg P L) (c' c1' : ECfg P (L × (X → Q') × Bool))
    (bev : Option (Ev P X BOp BRes)) : Prop :=
  ((∀ b r, bev ≠ some (.res b r)) ∧ ∀ q, (c1'.loc q).2.1 = (c'.loc q).2.1) ∨
  ∃ p b x o k, c.bpend p = some b ∧ I.act p (c.loc p) = .call x o k ∧
    bev = some (.res b (lch B hB x ((c'.loc p).2.1 x) o).1) ∧
    (c1'.loc p).2.1 = Function.update ((c'.loc p).2.1) x (lch B hB x ((c'.loc p).2.1 x) o).2 ∧
    ∀ q ≠ p, (c1'.loc q).2.1 = (c'.loc q).2.1

lemma step_mem {c : ECfg P L} {c' : ECfg P (L × (X → Q') × Bool)} (h : SimR I c c') (n : ℕ)
    (l : ELab P HOp Empty) {o o'} (ho : elStep I n c (mapLab I B hB c' l) = some o)
    (ho' : elStep (localImpl I B hB) n c' l = some o') : MemRel I B hB c c' o'.1 o.2.2 := by
  obtain ⟨hl, hp, hb, hc, hfp, hb'⟩ := h
  cases l with
  | bres p r => exact r.elim
  | inv p op =>
    simp only [mapLab, elStep, hp] at ho ho'
    split_ifs at ho ho'
    cases ho; cases ho'
    refine Or.inl ⟨by simp, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq; simp [localImpl]
    · simp [Function.update_of_ne hq]
  | step p =>
    rcases hpp : c'.pend p with _ | a
    · simp [elStep, hpp] at ho'
    rcases hf : (c'.loc p).2.2 with _ | _
    · have hbp : c.bpend p = none := by
        by_contra hne; exact absurd ((hb p).1 hne) (by simp [hf])
      simp only [mapLab, hf, elStep, hpp, hp, hbp, hb' p, localImpl, ← hl p] at ho ho'
      cases hact : I.act p (c.loc p) <;> rw [hact] at ho ho' <;> simp only at ho ho' <;>
        cases ho <;> cases ho' <;>
        refine Or.inl ⟨by simp, fun q => ?_⟩ <;>
        by_cases hq : q = p <;> simp_all [Function.update_of_ne]
    · obtain ⟨x, o, k, hact⟩ := hc p hf
      obtain ⟨b, hbp⟩ := Option.ne_none_iff_exists'.1 ((hb p).2 hf)
      have hact' : I.act p (c'.loc p).1 = .call x o k := by rw [← hl p]; exact hact
      simp only [mapLab, hf, hact, hact', elStep, hpp, hbp, hb' p, localImpl] at ho ho'
      cases ho; cases ho'
      refine Or.inr ⟨p, b, x, o, k, hbp, hact, rfl, by simp, fun q hq => by
        simp [Function.update_of_ne hq]⟩

/-- The execution of `I` simulating an execution `lab'` of `I'`. -/
noncomputable def simLab (lab' : ℕ → Option (ELab P HOp Empty)) : ℕ → Option (ELab P HOp BRes) :=
  fun n => (lab' n).map (mapLab I B hB ((elSys (localImpl I B hB)).cfg lab' n))

variable (lab' : ℕ → Option (ELab P HOp Empty))

lemma simR_run : ∀ n, SimR I ((elSys I).cfg (simLab I B hB lab') n)
    ((elSys (localImpl I B hB)).cfg lab' n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => rfl, rfl, fun _ => ?_, fun _ h => ?_, fun _ h => ?_, fun _ => rfl⟩
    · simp [LSys.cfg_zero, elSys, localImpl]
    · simp [LSys.cfg_zero, elSys, localImpl] at h
    · simp [LSys.cfg_zero, elSys, localImpl] at h
  | succ n ih =>
    rw [elSys_cfg_succ, elSys_cfg_succ]
    simp only [simLab]
    rcases lab' n with _ | l
    · exact ih
    · simp only [Option.map_some, Option.bind_some]
      have := step_simR I B hB ih n l
      revert this
      generalize elStep I n _ _ = o1
      generalize elStep (localImpl I B hB) n _ l = o2
      intro this
      cases this with
      | some h => exact h.1
      | none => exact ih

lemma out_simRel (n : ℕ) :
    Option.Rel (fun o o' => SimR I o.1 o'.1 ∧ o.2.1 = o'.2.1)
      ((elSys I).out (simLab I B hB lab') n) ((elSys (localImpl I B hB)).out lab' n) := by
  rw [LSys.out_eq, LSys.out_eq]
  simp only [simLab]
  rcases lab' n with _ | l
  · exact Option.Rel.none
  · exact step_simR I B hB (simR_run I B hB lab' n) n l

lemma hist_sim (n : ℕ) :
    (elSys I).hist (simLab I B hB lab') n = (elSys (localImpl I B hB)).hist lab' n := by
  have := out_simRel I B hB lab' n
  simp only [LSys.hist]
  revert this
  generalize (elSys I).out _ n = o1
  generalize (elSys (localImpl I B hB)).out lab' n = o2
  intro this
  cases this with
  | some h => simp [h.2]
  | none => rfl

lemma hist_sim_eq : (elSys I).hist (simLab I B hB lab') = (elSys (localImpl I B hB)).hist lab' :=
  funext (hist_sim I B hB lab')

lemma proper_sim (h : (elSys (localImpl I B hB)).Proper lab') :
    (elSys I).Proper (simLab I B hB lab') := by
  intro n l hl
  simp only [simLab] at hl
  rcases hn : lab' n with _ | l'
  · rw [hn] at hl; cases hl
  rw [hn] at hl
  simp only [Option.map_some, Option.some.injEq] at hl
  subst hl
  have h2 := h n l' hn
  have := step_simR I B hB (simR_run I B hB lab' n) n l'
  change elStep I n _ _ ≠ none
  change elStep (localImpl I B hB) n _ l' ≠ none at h2
  revert this h2
  generalize elStep I n _ _ = o1
  generalize elStep (localImpl I B hB) n _ l' = o2
  intro this h2
  cases this with
  | some _ => simp
  | none => exact absurd rfl h2

lemma mem_run (n : ℕ) :
    MemRel I B hB ((elSys I).cfg (simLab I B hB lab') n) ((elSys (localImpl I B hB)).cfg lab' n)
      ((elSys (localImpl I B hB)).cfg lab' (n + 1)) ((elSys I).bhist (simLab I B hB lab') n) := by
  rw [elSys_cfg_succ (localImpl I B hB), elSys_bhist]
  simp only [simLab]
  rcases lab' n with _ | l
  · exact Or.inl ⟨by simp, fun _ => rfl⟩
  · simp only [Option.map_some, Option.bind_some]
    have hrel := step_simR I B hB (simR_run I B hB lab' n) n l
    have hmem : ∀ o o', elStep I n ((elSys I).cfg (simLab I B hB lab') n)
        (mapLab I B hB ((elSys (localImpl I B hB)).cfg lab' n) l) = some o →
        elStep (localImpl I B hB) n ((elSys (localImpl I B hB)).cfg lab' n) l = some o' →
        MemRel I B hB ((elSys I).cfg (simLab I B hB lab') n) ((elSys (localImpl I B hB)).cfg lab' n)
          o'.1 o.2.2 :=
      fun o o' ho ho' => step_mem I B hB (simR_run I B hB lab' n) n l ho ho'
    revert hrel hmem
    generalize elStep I n _ _ = o1
    generalize elStep (localImpl I B hB) n _ l = o2
    intro hrel hmem
    cases hrel with
    | some h => exact hmem _ _ rfl rfl
    | none => exact Or.inl ⟨by simp, fun _ => rfl⟩

lemma simLab_trunc (m : ℕ) : ∀ n < m, simLab I B hB (LSys.trunc lab' m) n = simLab I B hB lab' n := by
  intro n hn
  simp only [simLab]
  rw [LSys.trunc_agree lab' m n hn,
    (elSys (localImpl I B hB)).cfg_congr (LSys.trunc_agree lab' m) n hn.le]

lemma simLab_trunc_ge (m : ℕ) : ∀ n, m ≤ n → simLab I B hB (LSys.trunc lab' m) n = none := by
  intro n hn
  simp [simLab, LSys.trunc, show ¬ n < m by omega]

open Classical in
/-- The operations of `p` on `x` in the simulated base history, placed at their response
positions with their responses: the run of `p`'s local copy of `x`. -/
noncomputable def copySeq (p : P) (x : X) : SeqHist BRes := fun i =>
  match (elSys I).bhist (simLab I B hB lab') i with
  | some (.res b r) =>
    if ∃ o, (elSys I).bhist (simLab I B hB lab') b = some (.inv p x o) then some (b, r) else none
  | _ => none

lemma copySeq_eq_some {p : P} {x : X} {i b : ℕ} {r : BRes} :
    copySeq I B hB lab' p x i = some (b, r) ↔
      (elSys I).bhist (simLab I B hB lab') i = some (.res b r) ∧
      ∃ o, (elSys I).bhist (simLab I B hB lab') b = some (.inv p x o) := by
  classical
  unfold copySeq
  rcases h : (elSys I).bhist (simLab I B hB lab') i with _ | (⟨p', x', o'⟩ | ⟨b', r'⟩)
  · simp
  · simp
  · simp only [Option.some.injEq, Ev.res.injEq]
    split_ifs with h1
    · simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, h1⟩
      · rintro ⟨⟨rfl, rfl⟩, -⟩; exact ⟨rfl, rfl⟩
    · simp only [reduceCtorEq, false_iff, not_and]
      rintro ⟨rfl, rfl⟩ h2; exact h1 h2

/-- The local copy of `x` at `p` along the execution of `I'`. -/
noncomputable abbrev copyState (p : P) (x : X) (i : ℕ) : Q' :=
  ((((elSys (localImpl I B hB)).cfg lab' i).loc p).2.1 x)

lemma copy_step (p : P) (x : X) (i : ℕ) :
    (∀ b r, copySeq I B hB lab' p x i = some (b, r) → ∃ o,
      (elSys I).bhist (simLab I B hB lab') b = some (.inv p x o) ∧
      (B x).δ (copyState I B hB lab' p x i) o r (copyState I B hB lab' p x (i + 1))) ∧
    (copySeq I B hB lab' p x i = none →
      copyState I B hB lab' p x (i + 1) = copyState I B hB lab' p x i) := by
  have hm := mem_run I B hB lab' i
  constructor
  · intro b r h
    obtain ⟨hres, o, hinv⟩ := (copySeq_eq_some I B hB lab').1 h
    rcases hm with ⟨hne, -⟩ | ⟨p', b', x', o', k', hbp, hact, hev, hupd, -⟩
    · exact absurd hres (hne b r)
    rw [hres] at hev
    simp only [Option.some.injEq, Ev.res.injEq] at hev
    obtain ⟨rfl, rfl⟩ := hev
    obtain ⟨-, x'', o'', k'', hact', hinv'⟩ := el_bpend_inv I _ i p' b hbp
    rw [hact] at hact'
    simp only [Action.call.injEq] at hact'
    obtain ⟨rfl, rfl, -⟩ := hact'
    rw [hinv] at hinv'
    simp only [Option.some.injEq, Ev.inv.injEq] at hinv'
    obtain ⟨rfl, rfl, rfl⟩ := hinv'
    refine ⟨o, hinv, ?_⟩
    simp only [copyState, hupd, Function.update_self]
    exact lch_spec B hB _ _ _
  · intro h
    rcases hm with ⟨-, hsame⟩ | ⟨p', b', x', o', k', hbp, hact, hev, hupd, hother⟩
    · simp only [copyState, hsame]
    by_cases hpp : p = p'
    · subst hpp
      by_cases hxx : x = x'
      · subst hxx
        exfalso
        obtain ⟨-, x'', o'', k'', hact', hinv'⟩ := el_bpend_inv I _ i p b' hbp
        rw [hact] at hact'
        simp only [Action.call.injEq] at hact'
        obtain ⟨rfl, rfl, -⟩ := hact'
        have := (copySeq_eq_some I B hB lab' (i := i) (b := b')).2 ⟨hev, o', hinv'⟩
        rw [h] at this; cases this
      · simp only [copyState, hupd, Function.update_of_ne hxx]
    · simp only [copyState, hother p hpp]

lemma copySeq_legal (p : P) (x : X) :
    Legal (fun _ => B x) (restrict ((elSys I).bhist (simLab I B hB lab')) x) (copySeq I B hB lab' p x) := by
  refine ⟨fun k b r hk => ?_, fun y => ?_⟩
  · obtain ⟨-, o, hinv⟩ := (copySeq_eq_some I B hB lab').1 hk
    exact invoked_restrict.2 ⟨p, o, hinv⟩
  · by_cases hy : y = x
    · subst hy
      refine ⟨copyState I B hB lab' p y, (hB y).1.some_mem, fun k => ?_⟩
      have hst := copy_step I B hB lab' p y k
      rcases hk : copySeq I B hB lab' p y k with _ | ⟨b, r⟩
      · exact hst.2 hk
      · obtain ⟨o, hinv, hδ⟩ := hst.1 b r hk
        exact Or.inl ⟨p, o, restrict_inv_iff.2 ⟨hinv, rfl⟩, hδ⟩
    · refine ⟨fun _ => (hB x).1.some, (hB x).1.some_mem, fun k => ?_⟩
      rcases hk : copySeq I B hB lab' p x k with _ | ⟨b, r⟩
      · rfl
      · refine Or.inr ⟨fun h => hy ?_, rfl⟩
        exact (onObj_restrict.1 h).2

lemma copySeq_nodup (p : P) (x : X) : (copySeq I B hB lab' p x).Nodup := by
  intro i j b r1 r2 h1 h2
  obtain ⟨h1, -⟩ := (copySeq_eq_some I B hB lab').1 h1
  obtain ⟨h2, -⟩ := (copySeq_eq_some I B hB lab').1 h2
  exact (el_wellFormed_bhist I _).res_unique b i j r1 r2 h1 h2

/-- The simulated base objects are weakly consistent (each process sees its local copy). -/
lemma sim_weaklyConsistent (x : X) :
    WeaklyConsistent (fun _ => B x) (restrict ((elSys I).bhist (simLab I B hB lab')) x) := by
  classical
  have hWF := el_wellFormed_bhist I (simLab I B hB lab')
  intro b j r hjR
  obtain ⟨hjB, p, o, hb⟩ := restrict_res_iff.1 hjR
  have hbj := (hWF.res_inv b j r hjB).1
  have hcj : copySeq I B hB lab' p x j = some (b, r) :=
    (copySeq_eq_some I B hB lab').2 ⟨hjB, o, hb⟩
  refine ⟨(copySeq I B hB lab' p x).trunc (j + 1), (copySeq_nodup I B hB lab' p x).trunc _,
    (copySeq_legal I B hB lab' p x).trunc _, fun c ⟨i, r', hi⟩ => ?_, fun c hc hpre => ?_,
    ⟨j, by rw [trunc_of_lt (by omega)]; exact hcj, fun k hk => trunc_of_ge (by omega)⟩⟩
  · have hij : i < j + 1 := by by_contra h'; rw [trunc_of_ge (by omega)] at hi; cases hi
    rw [trunc_of_lt hij] at hi
    obtain ⟨hres, -⟩ := (copySeq_eq_some I B hB lab').1 hi
    have := (hWF.res_inv c i r' hres).1
    omega
  · obtain ⟨p', y, y', op, op', hc1, hc2⟩ := sameProc_of_restrict hc
    rw [hb] at hc2
    simp only [Option.some.injEq, Ev.inv.injEq] at hc2
    obtain ⟨hpp, -, -⟩ := hc2
    subst hpp
    obtain ⟨i, r', hiR, hib, -⟩ := hpre
    obtain ⟨hiB, ⟨p'', op'', hc3⟩⟩ := restrict_res_iff.1 hiR
    rw [hc1] at hc3
    simp only [Option.some.injEq, Ev.inv.injEq] at hc3
    obtain ⟨-, hyx, -⟩ := hc3
    subst hyx
    refine ⟨i, r', ?_⟩
    rw [trunc_of_lt (by omega)]
    exact (copySeq_eq_some I B hB lab').2 ⟨hiB, op, hc1⟩

/-- If only `p` takes steps, each simulated base object is linearizable. -/
lemma sim_solo_isLin {p : P} (hsolo : ∀ n l, lab' n = some l → l.proc = p) (x : X) :
    IsTLin (fun _ => B x) (restrict ((elSys I).bhist (simLab I B hB lab')) x) 0
      (copySeq I B hB lab' p x) := by
  have hWF := el_wellFormed_bhist I (simLab I B hB lab')
  have hby : ∀ c p' y o, (elSys I).bhist (simLab I B hB lab') c = some (.inv p' y o) → p' = p := by
    intro c p' y o h
    obtain ⟨l, hl, hlp⟩ := el_bhist_inv_proc I h
    simp only [simLab] at hl
    rcases hl' : lab' c with _ | l'
    · rw [hl'] at hl; cases hl
    rw [hl'] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    rw [← hlp, ← hsolo c l' hl']
    cases l' with
    | inv q op => rfl
    | step q => simp only [mapLab]; split <;> rfl
    | bres q r => exact r.elim
  have hentry : ∀ a j r, restrict ((elSys I).bhist (simLab I B hB lab')) x j = some (.res a r) →
      copySeq I B hB lab' p x j = some (a, r) := by
    intro a j r hj
    obtain ⟨hj, p', o, ha⟩ := restrict_res_iff.1 hj
    obtain rfl := hby a p' x o ha
    exact (copySeq_eq_some I B hB lab').2 ⟨hj, o, ha⟩
  refine ⟨copySeq_nodup I B hB lab' p x, copySeq_legal I B hB lab' p x,
    fun a j r hj => ⟨j, r, hentry a j r hj⟩, fun a b j r hj _ hjb _ hbm => ?_,
    fun a j r hj _ => ⟨j, hentry a j r hj⟩⟩
  obtain ⟨i, rb, hi⟩ := hbm
  obtain ⟨hres, -⟩ := (copySeq_eq_some I B hB lab').1 hi
  have := (hWF.res_inv b i rb hres).1
  exact ⟨j, i, r, rb, by omega, hentry a j r hj, hi⟩

end Local

/-! ### `4 ⇒ 1`: the local-copy implementation is linearizable and wait-free -/

section Main

lemma LSys.hist_trunc_eq {C Lab E B : Type} (S : LSys C Lab (Ev P Unit HOp HRes) B)
    (lab : ℕ → Option Lab) (m : ℕ) : S.hist (LSys.trunc lab m) = take (S.hist lab) m := by
  funext n
  by_cases hn : n < m
  · rw [take_of_lt _ hn]; exact S.hist_congr (LSys.trunc_agree lab m) hn
  · rw [take_of_le _ (by omega)]; exact S.hist_trunc_of_ge lab (by omega)

variable {P HOp HRes X BOp BRes L Q Q' : Type} [DecidableEq P] [DecidableEq X]

lemma el_hist_inv_proc (I : Impl P HOp HRes X BOp BRes L) {lab : ℕ → Option (ELab P HOp BRes)}
    {n : ℕ} {p : P} {x : Unit} {op : HOp} (h : (elSys I).hist lab n = some (.inv p x op)) :
    ∃ l, lab n = some l ∧ l.proc = p := by
  rw [elSys_hist] at h
  generalize (elSys I).cfg lab n = c at h
  rcases hl : lab n with _ | l
  · rw [hl] at h; simp at h
  rw [hl] at h
  refine ⟨l, rfl, ?_⟩
  simp only [Option.bind_some] at h
  cases l with
  | inv q op' =>
    simp only [elStep] at h; split_ifs at h
    · simp at h; exact h.1
    · simp at h
  | step q =>
    simp only [elStep] at h
    rcases hp : c.pend q with _ | a <;> rcases hb : c.bpend q with _ | b <;> simp only [hp, hb] at h
    all_goals try simp at h
    cases hact : I.act q (c.loc q) <;> simp [hact] at h
  | bres q r =>
    simp only [elStep] at h
    rcases hb : c.bpend q with _ | b <;> simp only [hb] at h
    · simp at h
    · cases hact : I.act q (c.loc q) <;> simp [hact] at h

lemma lab_ne_none_of_hist {C Lab E B' : Type} (S : LSys C Lab E B') {lab : ℕ → Option Lab} {n : ℕ}
    (h : S.hist lab n ≠ none) : lab n ≠ none := by
  intro hn; apply h; simp [LSys.hist, S.out_none_of_lab hn]

lemma mapLab_proc (I : Impl P HOp HRes X BOp BRes L) (B : X → ObjType Q' BOp BRes)
    (hB : ∀ x, (B x).init.Nonempty ∧ (B x).Total) (c : ECfg P (L × (X → Q') × Bool))
    (l : ELab P HOp Empty) : (mapLab I B hB c l).proc = l.proc := by
  cases l with
  | inv p op => rfl
  | step p => simp only [mapLab]; split <;> rfl
  | bres p r => exact r.elim

/-- The base objects of an implementation that uses no shared objects. -/
def noBase : Empty → ObjType PUnit Empty Empty := fun e => e.elim

lemma elAdm_noBase {HOp' HRes' L' : Type} (I : Impl P HOp' HRes' Empty Empty Empty L')
    {lab : ℕ → Option (ELab P HOp' Empty)} : ELAdm I noBase lab ↔ (elSys I).Proper lab :=
  ⟨fun h => h.1, fun h => ⟨h, fun e => e.elim⟩⟩

/-- **Theorem 12, `4 ⇒ 1`** (the paper's construction). If `I` is a linearizable
obstruction-free implementation of `T` (initialized to `q₀`, finite nondeterminism) from
eventually linearizable base objects (wait-free: total types with initial states), then
replacing every base object by local copies gives a linearizable wait-free implementation
using no shared objects. -/
theorem localImpl_correct [Finite P] (T : ObjType Q HOp HRes) (q₀ : Q) (hT : T.FiniteNondet)
    (I : Impl P HOp HRes X BOp BRes L) (B : X → ObjType Q' BOp BRes)
    (hB : ∀ x, (B x).init.Nonempty ∧ (B x).Total)
    (hlin : (elSys I).IsLinearizable (ELAdm I B) (T.initAt q₀))
    (hof : (elSys I).ObstructionFree ELab.proc (ELAdm I B)) :
    (elSys (localImpl I B hB)).IsLinearizable (ELAdm (localImpl I B hB) noBase) (T.initAt q₀) ∧
    (elSys (localImpl I B hB)).WaitFree ELab.proc (ELAdm (localImpl I B hB) noBase) := by
  constructor
  · intro lab' hadm
    have hp' := (elAdm_noBase _).1 hadm
    refine linearizable_of_forall_take (spec := fun _ => T.initAt q₀) (fun _ => hT)
      (fun _ => Set.finite_singleton q₀)
      (el_wellFormed_hist _ lab') (fun m => ?_)
    set labI := simLab I B hB (LSys.trunc lab' m)
    have hadmI : ELAdm I B labI := by
      refine ⟨proper_sim I B hB _ ((elSys _).proper_trunc hp' m), fun x => ⟨?_, m, ?_⟩⟩
      · exact sim_weaklyConsistent I B hB _ x
      · have hWF := (el_wellFormed_bhist I labI).restrict x
        have hfin : restrict ((elSys I).bhist labI) x = take (restrict ((elSys I).bhist labI) x) m := by
          funext n
          by_cases hn : n < m
          · rw [take_of_lt _ hn]
          · rw [take_of_le _ (by omega)]
            have : (elSys I).bhist labI n = none := by
              have h0 : (elSys I).out labI n = none :=
                (elSys I).out_none_of_lab (simLab_trunc_ge I B hB lab' m n (by omega))
              simp [LSys.bhist, h0]
            unfold restrict; rw [this]
        rw [hfin]
        exact tLinearizable_take_self (fun _ => (hB x).1) (fun _ => (hB x).2) hWF m
    have := hlin labI hadmI
    rwa [hist_sim_eq, LSys.hist_trunc_eq] at this
  · intro lab' hadm a p op ha hinf
    have hp' := (elAdm_noBase _).1 hadm
    set lab'p := projLab lab' p
    set labI := simLab I B hB lab'p
    have hsolo' : ∀ n l, lab'p n = some l → l.proc = p := by
      intro n l hl
      simp only [lab'p, projLab] at hl
      rcases h : lab' n with _ | l' <;> rw [h] at hl
      · cases hl
      · simp only at hl; split_ifs at hl with h1; cases hl; exact h1
    have hsoloI : ∀ n l, labI n = some l → l.proc = p := by
      intro n l hl
      simp only [labI, simLab] at hl
      rcases h : lab'p n with _ | l' <;> rw [h] at hl
      · cases hl
      · simp only [Option.map_some, Option.some.injEq] at hl
        subst hl; rw [mapLab_proc]; exact hsolo' n l' h
    have hadmI : ELAdm I B labI := by
      refine ⟨proper_sim I B hB _ (proper_proj _ hp' p), fun x => ⟨?_, 0, ?_⟩⟩
      · exact sim_weaklyConsistent I B hB _ x
      · exact ⟨_, sim_solo_isLin I B hB lab'p hsolo' x⟩
    obtain ⟨la, hla, hlap⟩ := el_hist_inv_proc _ ha
    have ha' : (elSys I).hist labI a = some (.inv p () op) := by
      rw [hist_sim_eq, (hist_proj _ hla hlap).1]; exact ha
    have hinfI : LSys.InfSteps ELab.proc labI p := by
      intro N
      obtain ⟨n, hn, l, hl, hlp⟩ := hinf N
      refine ⟨n, hn, mapLab I B hB ((elSys (localImpl I B hB)).cfg lab'p n) l, ?_, ?_⟩
      · simp only [labI, simLab, lab'p, projLab, hl, hlp, if_true, Option.map_some]
      · rw [mapLab_proc]; exact hlp
    obtain ⟨j, r, hj⟩ := hof labI hadmI a p op 0 ha' (fun n _ l hl => hsoloI n l hl) hinfI
    rw [hist_sim_eq] at hj
    have hne := lab_ne_none_of_hist _ (show (elSys (localImpl I B hB)).hist lab'p j ≠ none by
      rw [hj]; simp)
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 hne
    have hl' : lab' j = some l ∧ l.proc = p := by
      simp only [lab'p, projLab] at hl
      rcases h : lab' j with _ | l' <;> rw [h] at hl
      · cases hl
      · simp only at hl; split_ifs at hl with h1; cases hl; exact ⟨rfl, h1⟩
    exact ⟨j, r, (hist_proj _ hl'.1 hl'.2).1 ▸ hj⟩

end Main

/-! ### Theorem 12 -/

section Thm12

variable {P HOp HRes Q : Type} [DecidableEq P]

/-- **Theorem 12** of [Guerraoui–Ruppert, PODC 2014]. For a type `T` with finite
nondeterminism (initialized to `q₀`), the following are equivalent:
1. there is a linearizable wait-free implementation of `T` using no shared objects;
2. there is a linearizable obstruction-free implementation of `T` using no shared objects;
3. there is a linearizable wait-free implementation of `T` from some collection of eventually
   linearizable objects;
4. there is a linearizable obstruction-free implementation of `T` from some collection of
   eventually linearizable objects.
The base objects are wait-free (their types are total and have initial states). The paper
states it for `n ≥ 2` processes; the proof works for any finite number of processes. -/
theorem theorem12 [Finite P] (T : ObjType Q HOp HRes) (q₀ : Q) (hT : T.FiniteNondet) :
    List.TFAE [
      ∃ (L : Type) (I : Impl P HOp HRes Empty Empty Empty L),
        (elSys I).IsLinearizable (ELAdm I noBase) (T.initAt q₀) ∧
        (elSys I).WaitFree ELab.proc (ELAdm I noBase),
      ∃ (L : Type) (I : Impl P HOp HRes Empty Empty Empty L),
        (elSys I).IsLinearizable (ELAdm I noBase) (T.initAt q₀) ∧
        (elSys I).ObstructionFree ELab.proc (ELAdm I noBase),
      ∃ (X BOp BRes Q' L : Type) (B : X → ObjType Q' BOp BRes),
        (∀ x, (B x).init.Nonempty ∧ (B x).Total) ∧ ∃ I : Impl P HOp HRes X BOp BRes L,
        (elSys I).IsLinearizable (ELAdm I B) (T.initAt q₀) ∧
        (elSys I).WaitFree ELab.proc (ELAdm I B),
      ∃ (X BOp BRes Q' L : Type) (B : X → ObjType Q' BOp BRes),
        (∀ x, (B x).init.Nonempty ∧ (B x).Total) ∧ ∃ I : Impl P HOp HRes X BOp BRes L,
        (elSys I).IsLinearizable (ELAdm I B) (T.initAt q₀) ∧
        (elSys I).ObstructionFree ELab.proc (ELAdm I B)] := by
  tfae_have 1 → 2 := fun ⟨L, I, h1, h2⟩ => ⟨L, I, h1, h2.obstructionFree⟩
  tfae_have 1 → 3 := fun ⟨L, I, h1, h2⟩ =>
    ⟨Empty, Empty, Empty, PUnit, L, noBase, fun e => e.elim, I, h1, h2⟩
  tfae_have 2 → 4 := fun ⟨L, I, h1, h2⟩ =>
    ⟨Empty, Empty, Empty, PUnit, L, noBase, fun e => e.elim, I, h1, h2⟩
  tfae_have 3 → 4 := fun ⟨X, BOp, BRes, Q', L, B, hB, I, h1, h2⟩ =>
    ⟨X, BOp, BRes, Q', L, B, hB, I, h1, h2.obstructionFree⟩
  tfae_have 4 → 1 := by
    rintro ⟨X, BOp, BRes, Q', L, B, hB, I, h1, h2⟩
    classical
    exact ⟨_, localImpl I B hB, localImpl_correct T q₀ hT I B hB h1 h2⟩
  tfae_finish

end Thm12

end Podc.EventualLinParadox
