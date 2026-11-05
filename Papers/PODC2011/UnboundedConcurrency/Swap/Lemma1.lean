import Papers.PODC2011.UnboundedConcurrency.Swap.WaitFree

/-!
# Lemma 1 of [AMW11], as stated in the paper

`lemma1_paper`: in every execution, when a process tries to capture a node `w` of the right
subtree of `v` (it holds `cap = w`, Lines 3–6), then `v` itself has already been recorded in
`accessed` (some earlier step was `update_{depth v}(v)`, Line 5).

This is an execution-level statement (`Rec x σ v` refers to the history). It follows from the
state form `lemma1` (a node `≥ v` of `v`'s depth has been recorded) and the observation that a
node `v` skipped by its capturing process (never recorded) is skipped because of an accessed node
lying beyond the whole subtree of `v` (`Beyond`), after which nobody tries the right subtree of `v`.
-/

namespace Podc.UnboundedConcurrency.Swap

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Cfg' Node

variable {V : Type}

/-- `v` has been recorded in `accessed` during the execution `σ`: some step of `σ` is the
`update_{depth}(accessed, v)` of Line 5. -/
def Rec (x : ℕ → V) (σ : List ℕ) (v : Node) : Prop :=
  ∃ (t : ℕ) (ht : t < σ.length) (x' : V) (d : ℕ) (w : Bool),
    ((alg V).exec x (σ.take t)).loc σ[t] = .upd x' d v w

/-- `b` lies beyond the whole subtree of `v` (to its right). -/
def Beyond (v b : Node) : Prop := v.key + 1 / 2 ^ (v.d + 1) ≤ b.key

lemma lt_dichotomy {v a : Node} (h : v < a) : rightSub v a ∨ Beyond v a := by
  by_cases hb : Beyond v a
  · exact Or.inr hb
  · left
    unfold Beyond at hb
    push Not at hb
    refine ⟨?_, h, hb⟩
    by_contra hd
    push Not at hd
    have := gap (R := v.d) le_rfl hd h
    linarith

lemma Beyond.lt_of_rightSub {v w b : Node} (hb : Beyond v b) (hw : rightSub v w) : w < b := by
  rw [lt_iff_key]; unfold Beyond at hb; linarith [hw.2.2]

lemma Beyond.mono {v b b' : Node} (hb : Beyond v b) (h : b ≤ b') : Beyond v b' := by
  unfold Beyond at *; rw [le_iff_key] at h; linarith

/-- The node a process is currently trying to capture (Lines 3–5). -/
def Loc.pend : Loc V → Option Node
  | .write _ _ c | .tas _ _ c | .upd _ _ c _ => some c
  | _ => none

section

variable {x : ℕ → V}

lemma rec_snoc {σ : List ℕ} {s : ℕ} {v : Node} :
    Rec x (σ ++ [s]) v ↔ Rec x σ v ∨ ∃ x' d w, ((alg V).exec x σ).loc s = .upd x' d v w := by
  constructor
  · rintro ⟨t, ht, x', d, w, h⟩
    simp only [List.length_append, List.length_singleton] at ht
    rcases Nat.lt_or_ge t σ.length with hlt | hge
    · left
      refine ⟨t, hlt, x', d, w, ?_⟩
      rwa [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt] at h
    · right
      have : t = σ.length := by omega
      subst this
      simp only [List.take_left', List.getElem_append_right (le_refl _), Nat.sub_self,
        List.getElem_singleton] at h
      exact ⟨x', d, w, h⟩
  · rintro (⟨t, ht, x', d, w, h⟩ | ⟨x', d, w, h⟩)
    · refine ⟨t, by simp; omega, x', d, w, ?_⟩
      rwa [List.take_append_of_le_length ht.le, List.getElem_append_left ht]
    · refine ⟨σ.length, by simp, x', d, w, ?_⟩
      simp only [List.take_left', List.getElem_append_right (le_refl _), Nat.sub_self,
        List.getElem_singleton]
      exact h

lemma rec_mono {σ : List ℕ} {s : ℕ} {v : Node} (h : Rec x σ v) : Rec x (σ ++ [s]) v :=
  rec_snoc.2 (Or.inl h)

/-- The invariant for the paper's form of Lemma 1 (`C` is the configuration reached by `σ`). -/
structure SInvC (x : ℕ → V) (σ : List ℕ) (C : Config V) : Prop where
  cellRec : ∀ e a, S C e = some a → Rec x σ a
  skip : ∀ v a, S C v.d = some a → v < a → Rec x σ v ∨ ∃ e b, S C e = some b ∧ Beyond v b
  pend : ∀ p c, (C.loc p).pend = some c → ∀ v : Node, v.d = c.d → Below (S C c.d) v → v < c →
    ∃ e b, S C e = some b ∧ Beyond v b
  strong : ∀ w, ((∃ p, (C.loc p).sel = some w) ∨ ∃ e, S C e = some w) →
    ∀ v, rightSub v w → Rec x σ v

/-- The invariant for the paper's form of Lemma 1. -/
def SInv (x : ℕ → V) (σ : List ℕ) : Prop := SInvC x σ ((alg V).exec x σ)

lemma S_mono {C : Config V} (hI : Inv x C) (s e : ℕ) {a : Node} (h : S C e = some a) :
    ∃ a', S (C.step s) e = some a' ∧ a ≤ a' := by
  cases hs : C.loc s with
  | upd x' d c w =>
    obtain ⟨-, -, -, hS, -, -⟩ := step_upd hs
    have hok := hI.ok s
    rw [hs] at hok
    by_cases hed : e = d
    · subst hed; exact ⟨c, by rw [hS]; simp, le_of_lt (hok.2.2.1 a h)⟩
    · exact ⟨a, by rw [hS, Function.update_of_ne hed]; exact h, le_rfl⟩
  | start => exact ⟨a, by rw [(step_start hs).2.2.2.1]; exact h, le_rfl⟩
  | scan => exact ⟨a, by rw [(step_scan hs).2.2.2.1]; exact h, le_rfl⟩
  | write => exact ⟨a, by rw [(step_write hs).2.2.2.1]; exact h, le_rfl⟩
  | tas => exact ⟨a, by rw [(step_tas hs).2.2.2.1]; exact h, le_rfl⟩
  | readMax => exact ⟨a, by rw [(step_readMax hs).2.2.2.1]; exact h, le_rfl⟩
  | retTas => exact ⟨a, by rw [(step_retTas hs).2.2.2.1]; exact h, le_rfl⟩
  | readReg => exact ⟨a, by rw [(step_readReg hs).2.2.2.1]; exact h, le_rfl⟩
  | done => exact ⟨a, by rw [step_done hs]; exact h, le_rfl⟩

lemma beyond_mono {C : Config V} (hI : Inv x C) (s : ℕ) {v : Node}
    (h : ∃ e b, S C e = some b ∧ Beyond v b) : ∃ e b, S (C.step s) e = some b ∧ Beyond v b := by
  obtain ⟨e, b, hb, hvb⟩ := h
  obtain ⟨b', hb', hbb'⟩ := S_mono hI s e hb
  exact ⟨e, b', hb', hvb.mono hbb'⟩

lemma sinv_nil (x : ℕ → V) : SInv x [] := by
  have hS : S ((alg V).initCfg x) = fun _ => none := rfl
  have hl : ∀ p, ((alg V).initCfg x).loc p = .start (x p) := fun _ => rfl
  show SInvC x [] ((alg V).initCfg x)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hS, hl, Loc.pend, Loc.sel]

/-- Frame: steps that do not change `accessed` and create no new selection. -/
lemma SInv.frame {σ : List ℕ} {s : ℕ} (hS : SInv x σ)
    (hSe : S ((alg V).exec x (σ ++ [s])) = S ((alg V).exec x σ))
    (hsel : ∀ q w, (((alg V).exec x (σ ++ [s])).loc q).sel = some w →
      (((alg V).exec x σ).loc q).sel = some w)
    (hpend : ∀ q c, (((alg V).exec x (σ ++ [s])).loc q).pend = some c →
      (((alg V).exec x σ).loc q).pend = some c) : SInv x (σ ++ [s]) := by
  unfold SInv at hS ⊢
  refine ⟨fun e a h => ?_, fun v a h hlt => ?_, fun p c hp v hv hb hlt => ?_, fun w hw v hv => ?_⟩
  · rw [hSe] at h; exact rec_mono (hS.cellRec e a h)
  · rw [hSe] at h ⊢
    exact (hS.skip v a h hlt).imp_left rec_mono
  · rw [hSe] at hb ⊢; exact hS.pend p c (hpend p c hp) v hv hb hlt
  · rw [hSe] at hw
    refine rec_mono (hS.strong w ?_ v hv)
    rcases hw with ⟨q, hq⟩ | hw
    · exact Or.inl ⟨q, hsel q w hq⟩
    · exact Or.inr hw

lemma SInv.snoc {σ : List ℕ} (hS : SInv x σ) (s : ℕ) : SInv x (σ ++ [s]) := by
  unfold SInv at hS
  set C := (alg V).exec x σ with hCdef
  have hI : Inv x C := inv_exec x σ
  have hC' : (alg V).exec x (σ ++ [s]) = C.step s := Alg.exec_concat _ _ _
  -- generic facts for the frame cases
  have hframe : S (C.step s) = S C → (∀ q w, ((C.step s).loc q).sel = some w →
      (C.loc q).sel = some w) → (∀ q c, ((C.step s).loc q).pend = some c →
      (C.loc q).pend = some c) → SInv x (σ ++ [s]) := by
    intro h1 h2 h3
    exact SInv.frame hS (by rw [hC']; exact h1) (by rw [hC']; exact h2) (by rw [hC']; exact h3)
  have hoth : ∀ q, q ≠ s → (C.step s).loc q = C.loc q := fun q hq => Cfg.step_loc_other C hq
  have lift : ∀ {β : Type} (f : Loc V → Option β), (∀ w, f ((C.step s).loc s) = some w →
      f (C.loc s) = some w) → ∀ q w, f ((C.step s).loc q) = some w → f (C.loc q) = some w := by
    intro β f h q w hq
    by_cases hqs : q = s
    · subst hqs; exact h w hq
    · rwa [hoth q hqs] at hq
  cases hs : C.loc s with
  | start x' =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_start hs
    exact hframe hSe (lift _ (fun w h => by rw [hself] at h; simp [Loc.sel] at h))
      (lift _ (fun w h => by rw [hself] at h; simp [Loc.pend] at h))
  | write x' d c =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_write hs
    exact hframe hSe (lift _ (fun w h => by rw [hself] at h; rw [hs]; exact h))
      (lift _ (fun w h => by rw [hself] at h; rw [hs]; exact h))
  | tas x' d c =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_tas hs
    exact hframe hSe (lift _ (fun w h => by rw [hself] at h; rw [hs]; exact h))
      (lift _ (fun w h => by rw [hself] at h; rw [hs]; exact h))
  | readMax d c =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_readMax hs
    exact hframe hSe
      (lift _ (fun w h => by
        rw [hself] at h; rw [hs]; cases hp : prev c (D C) <;> rw [hp] at h <;>
          simpa [afterPrev, Loc.sel] using h))
      (lift _ (fun w h => by
        rw [hself] at h; cases hp : prev c (D C) <;> rw [hp] at h <;>
          simp [afterPrev, Loc.pend] at h))
  | retTas d c m r =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_retTas hs
    refine hframe hSe (lift _ (fun w h => ?_)) (lift _ (fun w h => ?_))
    · rw [hself] at h; rw [hs]
      by_cases hb : B C r = true
      · rw [ite_eq_left hb] at h; exact h
      · rw [ite_eq_right hb] at h
        cases hp : prev r m <;> rw [hp] at h <;> simpa [afterPrev, Loc.sel] using h
    · rw [hself] at h
      by_cases hb : B C r = true
      · rw [ite_eq_left hb] at h; simp [Loc.pend] at h
      · rw [ite_eq_right hb] at h
        cases hp : prev r m <;> rw [hp] at h <;> simp [afterPrev, Loc.pend] at h
  | readReg d c m r =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_readReg hs
    exact hframe hSe (lift _ (fun w h => by rw [hself] at h; rw [hs]; exact h))
      (lift _ (fun w h => by rw [hself] at h; simp [Loc.pend] at h))
  | done d c m r o =>
    have he := step_done hs
    exact hframe (by rw [he]) (fun q w h => by rwa [he] at h) (fun q c h => by rwa [he] at h)
  | scan x' d pr =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_scan hs
    cases hn : next d (S C) with
    | none =>
      rw [hn] at hself
      exact hframe hSe (lift _ (fun w h => by rw [hself] at h; rw [hs]; exact h))
        (lift _ (fun w h => by rw [hself] at h; rw [hs]; exact h))
    | some c =>
      rw [hn] at hself
      obtain ⟨hcd, habove, hmin⟩ := next_some hn
      have hok := hI.ok s
      rw [hs] at hok
      obtain ⟨-, hSd, -⟩ := hok
      show SInvC x (σ ++ [s]) _
      rw [hC']
      refine ⟨fun e a h => ?_, fun v a h hlt => ?_, fun p c' hp v hv hb hlt => ?_,
        fun w hw v hv => ?_⟩
      · rw [hSe] at h; exact rec_mono (hS.cellRec e a h)
      · rw [hSe] at h ⊢; exact (hS.skip v a h hlt).imp_left rec_mono
      · rw [hSe] at hb ⊢
        by_cases hps : p = s
        · subst hps
          rw [hself] at hp
          obtain rfl : c = c' := by simpa [Loc.pend] using hp
          -- `v` is not above all accessed nodes, by minimality of `c`
          have hna : ¬ Above (S C) v := fun habv =>
            absurd (hmin v (hv.trans hcd) habv) (not_le.2 hlt)
          simp only [Above, not_forall, not_lt] at hna
          obtain ⟨e, a, hea, hva⟩ := hna
          have hae := (hI.cell e a hea).1
          rcases eq_or_lt_of_le hva with heq | hva
          · subst heq
            have : S C c.d = some v := by rw [← hv, hae]; exact hea
            exact absurd (hb v this) (lt_irrefl _)
          · rcases lt_dichotomy hva with hr | hbey
            · obtain ⟨a', ha', hva'⟩ := hI.lemma1 a (Or.inr ⟨e, hea⟩) v hr
              rw [hv] at ha'
              exact absurd (hb a' ha') (not_lt.2 hva')
            · exact ⟨e, a, hea, hbey⟩
        · rw [hoth p hps] at hp; exact hS.pend p c' hp v hv hb hlt
      · rw [hSe] at hw
        rcases hw with ⟨q, hq⟩ | hw
        · by_cases hqs : q = s
          · subst hqs
            rw [hself] at hq; simp only [Loc.sel, Option.some.injEq] at hq; subst hq
            obtain ⟨a, ha, hva⟩ := hI.sel_new hs hn hv
            rcases eq_or_lt_of_le hva with heq | hlt
            · subst heq; exact rec_mono (hS.cellRec _ _ ha)
            · rcases hS.skip v a ha hlt with hr | ⟨e, b, hb, hbey⟩
              · exact rec_mono hr
              · exact absurd (habove e b hb) (not_lt.2 (hbey.lt_of_rightSub hv).le)
          · rw [hoth q hqs] at hq; exact rec_mono (hS.strong w (Or.inl ⟨q, hq⟩) v hv)
        · exact rec_mono (hS.strong w (Or.inr hw) v hv)
  | upd x' d c w =>
    obtain ⟨hself, -, -, hSe, -, -⟩ := step_upd hs
    have hok := hI.ok s
    rw [hs] at hok
    obtain ⟨-, hcd, hbel, -, -, -⟩ := hok
    have hrec : Rec x (σ ++ [s]) c := rec_snoc.2 (Or.inr ⟨x', d, w, hs⟩)
    have hsdep : (C.loc s).dep = some d := by rw [hs]; rfl
    show SInvC x (σ ++ [s]) _
    rw [hC']
    refine ⟨fun e a h => ?_, fun v a h hlt => ?_, fun p c' hp v hv hb hlt => ?_,
      fun w' hw v hv => ?_⟩
    · by_cases hed : e = d
      · subst hed; rw [hSe] at h; simp only [Function.update_self, Option.some.injEq] at h
        subst h; exact hrec
      · rw [hSe, Function.update_of_ne hed] at h; exact rec_mono (hS.cellRec e a h)
    · by_cases hvd : v.d = d
      · rw [hSe, hvd] at h; simp only [Function.update_self, Option.some.injEq] at h; subst h
        rw [← hvd] at hbel
        cases hold : S C v.d with
        | none =>
          right
          have hcv : c.d = v.d := hcd.trans hvd.symm
          exact beyond_mono hI s (hS.pend s c (by rw [hs]; rfl) v (hvd.trans hcd.symm)
            (fun a' ha' => by rw [hcv, hold] at ha'; cases ha') hlt)
        | some a0 =>
          rcases lt_trichotomy v a0 with h1 | h1 | h1
          · exact (hS.skip v a0 hold h1).imp rec_mono (beyond_mono hI s)
          · subst h1; exact Or.inl (rec_mono (hS.cellRec _ _ hold))
          · right
            refine beyond_mono hI s (hS.pend s c (by rw [hs]; rfl) v (hvd.trans hcd.symm)
              ?_ hlt)
            intro a' ha'
            rw [hcd, ← hvd, hold] at ha'
            cases ha'; exact h1
      · rw [hSe, Function.update_of_ne hvd] at h
        exact (hS.skip v a h hlt).imp rec_mono (beyond_mono hI s)
    · have hps : p ≠ s := by
        rintro rfl; rw [hself] at hp; cases w <;> simp [Loc.pend] at hp
      rw [hoth p hps] at hp
      have hdp : c'.d ≠ d := by
        intro hcd'
        have h1 : (C.loc p).dep = some c'.d := by
          have := (hI.ok p).sel (c := c') (by
            cases hl : C.loc p <;> rw [hl] at hp <;> simp [Loc.pend] at hp <;> subst hp <;> rfl)
          exact this
        rw [hcd'] at h1
        exact hps (hI.dep_inj p s d h1 hsdep)
      rw [hSe, Function.update_of_ne hdp] at hb
      exact beyond_mono hI s (hS.pend p c' hp v hv hb hlt)
    · have hw' : (∃ q, (C.loc q).sel = some w') ∨ ∃ e, S C e = some w' := by
        rcases hw with ⟨q, hq⟩ | ⟨e, he⟩
        · left; refine ⟨q, ?_⟩
          by_cases hqs : q = s
          · subst hqs; rw [hself] at hq; rw [hs]; cases w <;> simpa [Loc.sel] using hq
          · rwa [hoth q hqs] at hq
        · by_cases hed : e = d
          · subst hed; rw [hSe] at he; simp only [Function.update_self, Option.some.injEq] at he
            subst he; exact Or.inl ⟨s, by rw [hs]; rfl⟩
          · rw [hSe, Function.update_of_ne hed] at he; exact Or.inr ⟨e, he⟩
      exact rec_mono (hS.strong w' hw' v hv)

lemma sinv (x : ℕ → V) (σ : List ℕ) : SInv x σ := by
  induction σ using List.reverseRecOn with
  | nil => exact sinv_nil x
  | append_singleton σ s ih => exact ih.snoc s

/-- **Lemma 1** of [AMW11], as stated in the paper: a process in the capturing phase cannot try
to capture a node `w` of the right subtree of a node `v` before `v` itself has been recorded in
`accessed`: whenever a process holds `cap = w` (Lines 3–6, and afterwards), `update(v)` has
already been executed. -/
theorem lemma1_paper (x : ℕ → V) (σ : List ℕ) {p : ℕ} {w v : Node}
    (hw : (((alg V).exec x σ).loc p).sel = some w) (hv : rightSub v w) : Rec x σ v :=
  (sinv x σ).strong w (Or.inl ⟨p, hw⟩) v hv

end

end Podc.UnboundedConcurrency.Swap
