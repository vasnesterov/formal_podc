import Papers.PODC2015.HelpFreeWaitFree.Shape

/-!
# Setting of the proof of Theorem 4.3 and the core claim

We fix (`Ctx`) an implementation `I` of a type `A` from arbitrary base objects, a linearization
function `f` that is help-free in the weak sense `OwnerOnlyWith` (a step deciding `a` before `b`
is taken by `a`'s owner), wait-freedom, three distinct processes `p₁ p₂ p₃`, and the data
`op, W, R` of an exact order type. As in the paper, `p₁` runs `op₁ = (p₁, 0)` (operation `op`),
`p₂` runs `W`, `p₃` runs `R`.

`X.Std n h` is the situation of Claims 4.5.2 and 4.5.3: `p₂` has completed its first `n`
operations (which are `W(n)`) and they are decided before `op₁`, `p₂` has invoked at most
`W(n+1)`, `p₁` at most `op`, and `p₃` and all other processes nothing.

`core` is the heart of Claims 4.5.2/4.5.3: if `op₁` or `op₂ = (p₂, n)` is decided before
`op₃ = (p₃, 0)`, and then `p₃` runs and completes `R(m)`, then in every extension the results of
`R(m)` are those of a sequence of `W(n+1) ∘ (R(m) + op?)` if `op₂ ≺ op₁` in the linearization,
and of `W(n) ∘ op ∘ (R(m) + W_{n+1}?)` otherwise.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]

/-! ### Generic helpers -/

section Helpers

/-- Responses of a sequence with tags, read off a linearization. -/
lemma taggedResps_of_seqOK {α : List (Label P A)} (tg : OpId P × A.Op → Bool) :
    ∀ {q : A.State} {S : List (OpId P × A.Op)}, SeqOK α q S →
      (∀ e ∈ S, tg e = true → Completed α e.1) →
      taggedResps A q (S.map (fun e => (tg e, e.2))) = (S.filter tg).filterMap (fun e => respOf α e.1)
  | _, [], _, _ => rfl
  | q, (x, o) :: S, hS, hc => by
    obtain ⟨h1, h2⟩ := hS
    have ih := taggedResps_of_seqOK tg h2 (fun e he => hc e (List.mem_cons_of_mem _ he))
    by_cases ht : tg (x, o) = true
    · obtain ⟨r, hr⟩ : ∃ r, respOf α x = some r := by
        have := hc (x, o) (by simp) ht
        rw [completed_iff_respOf] at this; exact Option.isSome_iff_exists.1 this
      simp only [List.map_cons, taggedResps, ht, ↓reduceIte, List.filter_cons, List.filterMap_cons,
        hr, h1 r hr, List.singleton_append, ih]
    · simp only [Bool.not_eq_true] at ht
      simp only [List.map_cons, taggedResps, ht, List.filter_cons, Bool.false_eq_true,
        ↓reduceIte, List.nil_append, ih]

lemma taggedResps_append (q : A.State) (l₁ l₂ : List (Bool × A.Op)) :
    taggedResps A q (l₁ ++ l₂) =
      taggedResps A q l₁ ++ taggedResps A (A.runOps q (l₁.map Prod.snd)) l₂ := by
  induction l₁ generalizing q with
  | nil => rfl
  | cons x l₁ ih => obtain ⟨t, o⟩ := x; simp [taggedResps, ih, List.append_assoc]

lemma taggedResps_eq_nil (q : A.State) {l : List (Bool × A.Op)} (h : ∀ e ∈ l, e.1 = false) :
    taggedResps A q l = [] := by
  induction l generalizing q with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨t, o⟩ := x
    have ht : t = false := h (t, o) List.mem_cons_self
    simp [taggedResps, ht, ih _ (fun e he => h e (List.mem_cons_of_mem _ he))]

lemma range_filterMap_getElem? {α : Type} (l : List α) :
    (List.range l.length).filterMap (fun j => l[j]?) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    simp only [List.getElem?_cons_zero]
    congr 1

lemma pos_lt_of_le_of_ne {S : List (OpId P × A.Op)} {a b : OpId P} (hb : b ∈ S.map Prod.fst)
    (hle : pos S a ≤ pos S b) (hne : a ≠ b) : pos S a < pos S b := by
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have ha : a ∈ S.map Prod.fst := pos_lt_length_iff.1 (h ▸ pos_lt_length_iff.2 hb)
    exact hne (List.idxOf_inj ha |>.1 h)

end Helpers

/-! ### The context of the proof -/

/-- Data and assumptions of the proof of Theorem 4.3. -/
structure Ctx (I : Impl A B P L) where
  /-- The (weakly) help-free linearization function. -/
  f : List (Label P A) → List (OpId P × A.Op)
  lin : I.IsLinFun f
  owner : OwnerOnlyWith I f
  wf : I.WaitFree
  allowed : ∀ p o, I.allowed p o
  p₁ : P
  p₂ : P
  p₃ : P
  h12 : p₁ ≠ p₂
  h13 : p₁ ≠ p₃
  h23 : p₂ ≠ p₃
  /-- The operation of `p₁`. -/
  op : A.Op
  /-- The program of `p₂`. -/
  W : ℕ → A.Op
  /-- The program of `p₃`. -/
  R : ℕ → A.Op

namespace Ctx

variable {I : Impl A B P L} (X : Ctx I)

/-- The decided-before order of the context. -/
abbrev DB (h : List (Label P A)) (a b : OpId P) : Prop := DecidedBefore I X.f h a b

/-- The situation of Claims 4.5.2/4.5.3 at the start of iteration `n + 1` of the main loop:
`p₂` completed `W(n)`, which is decided before `op₁`; nobody else did anything outside the
programs. -/
structure Std (n : ℕ) (h : List (Label P A)) : Prop where
  valid : I.Valid h
  ops1 : opsOf h X.p₁ = [] ∨ opsOf h X.p₁ = [X.op]
  ops2 : opsOf h X.p₂ = pre X.W n ∨ opsOf h X.p₂ = pre X.W (n + 1)
  resp2 : n ≤ (respsOf h X.p₂).length
  ops3 : opsOf h X.p₃ = []
  other : ∀ q, q ≠ X.p₁ → q ≠ X.p₂ → q ≠ X.p₃ → opsOf h q = []
  dec : ∀ i < n, X.DB h (X.p₂, i) (X.p₁, 0)

/-- The results of `R(m)` are those of a sequence of `W(n+1) ∘ (R(m) + op?)`. -/
def ResW (n m : ℕ) (rs : List A.Resp) : Prop :=
  ∃ x ∈ seqWFirst X.op X.W X.R n m, taggedResps A A.init x = rs

/-- The results of `R(m)` are those of a sequence of `W(n) ∘ op ∘ (R(m) + W_{n+1}?)`. -/
def ResOp (n m : ℕ) (rs : List A.Resp) : Prop :=
  ∃ x ∈ seqOpFirst X.op X.W X.R n m, taggedResps A A.init x = rs

/-- **Core of Claims 4.5.2 and 4.5.3.** In the situation `Std n h`, suppose `op₁` or `op₂` is
decided before `op₃` in `h`, and the fragment `t` of `p₃` completes `R(m)`. Then in every
extension `h ++ t ++ s`, the results of `R(m)` are those of a sequence of `W(n+1) ∘ (R(m) + op?)`
if `op₂ ≺ op₁` in `f (h ++ t ++ s)`, and of `W(n) ∘ op ∘ (R(m) + W_{n+1}?)` otherwise. -/
theorem core {n m : ℕ} {h t s : List (Label P A)} (hstd : X.Std n h) (hm : 0 < m)
    (htp : ∀ γ ∈ t, γ.proc = X.p₃) (hto : opsOf t X.p₃ = pre X.R m)
    (htr : (respsOf t X.p₃).length = m) (hv : I.Valid (h ++ t ++ s))
    (hdec : X.DB h (X.p₁, 0) (X.p₃, 0) ∨ X.DB h (X.p₂, n) (X.p₃, 0)) :
    (Prec (X.f (h ++ t ++ s)) (X.p₂, n) (X.p₁, 0) → X.ResW n m (respsOf t X.p₃)) ∧
    (¬ Prec (X.f (h ++ t ++ s)) (X.p₂, n) (X.p₁, 0) → X.ResOp n m (respsOf t X.p₃)) := by
  set α := h ++ t ++ s with hα
  set S := X.f α with hS
  have hlin : IsLinearization α S := X.lin α hv
  have hwf : WellFormed α := hv.wellFormed
  have hα' : α = h ++ (t ++ s) := by simp [hα]
  -- operations of `t`
  have hto' : ∀ q, q ≠ X.p₃ → opsOf t q = [] := fun q hq =>
    opsOf_eq_nil_of_proc_ne (fun γ hγ => by rw [htp γ hγ]; exact Ne.symm hq)
  have hresp3h : respsOf h X.p₃ = [] := by
    have := hstd.valid.wellFormed.resps_le_ops X.p₃
    rw [hstd.ops3] at this; simpa using this
  set g := h ++ t with hg
  have hgops : ∀ q, q ≠ X.p₃ → opsOf g q = opsOf h q := fun q hq => by
    simp [hg, hto' q hq]
  have hg3 : opsOf g X.p₃ = pre X.R m := by simp [hg, hstd.ops3, hto]
  have hg3r : respsOf g X.p₃ = respsOf t X.p₃ := by simp [hg, hresp3h]
  have hαg : α = g ++ s := by simp [hα, hg]
  -- instances not invoked in `g` come after `R_m`
  have hcompR : ∀ j < m, Completed g (X.p₃, j) := fun j hj => by
    simp only [Completed, hg3r]; omega
  have hlateG : ∀ x ∈ S.map Prod.fst, ¬ Invoked g x → pos S (X.p₃, m - 1) < pos S x := by
    intro x hx hni
    exact pos_lt_of_precedes hlin ⟨g, s, hαg, hcompR (m - 1) (by omega), hni⟩ hx
  have hinvG : ∀ x, Invoked g x → Known X.p₁ X.p₂ X.p₃ n m x := by
    rintro ⟨q, j⟩ hx
    simp only [Invoked] at hx
    by_cases h1 : q = X.p₁
    · subst h1
      rw [hgops _ X.h13] at hx
      left
      rcases hstd.ops1 with h' | h' <;> rw [h'] at hx <;> simp at hx
      simp [hx]
    by_cases h2 : q = X.p₂
    · subst h2
      rw [hgops _ X.h23] at hx
      right; left
      refine ⟨rfl, ?_⟩
      rcases hstd.ops2 with h' | h' <;> rw [h'] at hx <;> simp [pre] at hx <;> simp <;> omega
    by_cases h3 : q = X.p₃
    · subst h3
      rw [hg3] at hx
      right; right; simpa [pre] using hx
    · rw [hgops q h3, hstd.other q h1 h2 h3] at hx; simp at hx
  have hmemG : ∀ x ∈ S.map Prod.fst, pos S x ≤ pos S (X.p₃, m - 1) → Invoked g x := by
    intro x hx hle; by_contra hni; have := hlateG x hx hni; omega
  -- operations of the entries
  have hopG : ∀ e ∈ S, Invoked g e.1 → opOf g e.1 = some e.2 := by
    intro e he hinv
    rw [← opOf_append_of_invoked (β := s) hinv, ← hαg]; exact hlin.op_eq e he
  have hmemS : ∀ e ∈ S, e.1 ∈ S.map Prod.fst := fun e he => List.mem_map.2 ⟨e, he, rfl⟩
  -- completed instances are linearized
  have hcompW : ∀ i < n, Completed h (X.p₂, i) := fun i hi => by
    simp only [Completed]; have := hstd.resp2; omega
  have hmemW : ∀ i < n, ((X.p₂, i) : OpId P) ∈ S.map Prod.fst := fun i hi =>
    hlin.complete _ (by rw [hα']; exact (hcompW i hi).mono)
  have hmemR : ∀ j < m, ((X.p₃, j) : OpId P) ∈ S.map Prod.fst := fun j hj =>
    hlin.complete _ (by rw [hαg]; exact (hcompR j hj).mono)
  have hno3 : ∀ j, ¬ Invoked h (X.p₃, j) := fun j => by simp [Invoked, hstd.ops3]
  have hprog : ∀ q i j, i < j → ((q, j) : OpId P) ∈ S.map Prod.fst → pos S (q, i) < pos S (q, j) :=
    fun q i j hij hj => pos_lt_of_precedes hlin
      (hwf.precedes_of_lt hij (invoked_of_mem_lin hlin hj)) hj
  have hshape := shape X.p₁ X.p₂ X.p₃ X.op X.W X.R n m S X.h12 X.h13 X.h23 hm hlin.nodup
    (by
      intro e he hle he1
      have hinv := hmemG _ (hmemS e he) hle
      have := hopG e he hinv
      rw [he1] at hinv this
      simp only [Invoked, hgops _ X.h13] at hinv
      simp only [opOf, hgops _ X.h13] at this
      rcases hstd.ops1 with h' | h' <;> rw [h'] at hinv this <;> simp at hinv this
      exact this.symm)
    (by
      intro e he hle he1
      have hinv := hmemG _ (hmemS e he) hle
      have := hopG e he hinv
      have he' : e.1 = (X.p₂, e.1.2) := by rw [← he1]
      rw [he'] at hinv this
      simp only [Invoked, hgops _ X.h23] at hinv
      simp only [opOf, hgops _ X.h23] at this
      rw [List.getElem?_eq_getElem hinv] at this
      rcases hstd.ops2 with h' | h' <;> simp only [h', pre, List.getElem_map, List.getElem_range,
        Option.some.injEq] at this <;> exact this.symm)
    (by
      intro e he hle he1
      have hinv := hmemG _ (hmemS e he) hle
      have := hopG e he hinv
      have he' : e.1 = (X.p₃, e.1.2) := by rw [← he1]
      rw [he'] at hinv this
      simp only [Invoked] at hinv
      simp only [opOf] at this
      rw [List.getElem?_eq_getElem hinv] at this
      simp only [hg3, pre, List.getElem_map, List.getElem_range, Option.some.injEq] at this
      exact this.symm)
    hmemW hmemR
    (fun x hx hk => hlateG x hx (fun hi => hk (hinvG x hi)))
    (by
      intro i hi h1
      have := (hstd.dec i hi).mem (s := t ++ s) (by rw [← hα']; exact hv) (by rw [← hα']; exact h1)
      rw [← hα'] at this
      exact pos_lt_of_le_of_ne h1 this.2 (fun e => X.h12 (Prod.ext_iff.1 e).1.symm))
    (fun i hi h2 => hprog _ _ _ hi h2)
    (fun i hi => pos_lt_of_precedes hlin
      ⟨h, t ++ s, hα', hcompW i hi, hno3 0⟩ (hmemR 0 hm))
    (fun i i' hii hi' => hprog _ _ _ hii (hmemW i' hi'))
    (fun j j' hjj hj' => hprog _ _ _ hjj (hmemR j' hj'))
    (by
      have h0 := hmemR 0 hm
      rcases hdec with hd | hd
      · left
        have := hd.mem (s := t ++ s) (by rw [← hα']; exact hv) (by rw [← hα']; exact h0)
        rw [← hα'] at this
        exact pos_lt_of_le_of_ne h0 this.2 (fun e => X.h13 (Prod.ext_iff.1 e).1)
      · right
        have := hd.mem (s := t ++ s) (by rw [← hα']; exact hv) (by rw [← hα']; exact h0)
        rw [← hα'] at this
        exact pos_lt_of_le_of_ne h0 this.2 (fun e => X.h23 (Prod.ext_iff.1 e).1))
  obtain ⟨hfilt, T₁, T₂, hT, hT2, hW, hO⟩ := hshape
  -- the results of the tagged operations are those of `R(m)` in `t`
  have hres : taggedResps A A.init T₁ = respsOf t X.p₃ := by
    have h1 := taggedResps_of_seqOK (tagR X.p₃ m) hlin.seq (fun e he ht => by
      simp only [tagR, decide_eq_true_eq] at ht
      have he' : e.1 = (X.p₃, e.1.2) := by rw [← ht.1]
      rw [he', hαg]; exact (hcompR _ ht.2).mono)
    have h2 : taggedResps A A.init (S.map (fun e => (tagR X.p₃ m e, e.2))) =
        taggedResps A A.init T₁ := by
      rw [← toTagged, hT, taggedResps_append, taggedResps_eq_nil _ hT2, List.append_nil]
    rw [← h2, h1]
    have h3 : (S.filter (tagR X.p₃ m)).filterMap (fun e => respOf α e.1) =
        ((S.filter (tagR X.p₃ m)).map Prod.fst).filterMap (respOf α) := by
      rw [List.filterMap_map]; rfl
    rw [h3, hfilt, List.filterMap_map]
    have : ∀ j ∈ List.range m, respOf α (X.p₃, j) = (respsOf t X.p₃)[j]? := by
      intro j hj
      rw [hαg, respOf_append_of_completed (hcompR j (List.mem_range.1 hj))]
      simp [respOf, hg3r]
    rw [List.filterMap_congr (fun j hj => by simpa using this j hj), ← htr]
    exact range_filterMap_getElem? _
  exact ⟨fun hp => ⟨T₁, hW hp, hres⟩, fun hp => ⟨T₁, hO hp, hres⟩⟩

end Ctx

end Podc.HelpFreeWaitFree
