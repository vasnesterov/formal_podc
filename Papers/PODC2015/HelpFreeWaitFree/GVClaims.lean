import Papers.PODC2015.HelpFreeWaitFree.GVShape
import Papers.PODC2015.HelpFreeWaitFree.Loop

/-!
# Claims of Section 4.6 of [CPT15]: views decide orders

We reuse the context `Ctx` of the proof of Theorem 4.3 (a wait-free implementation with a weakly
help-free linearization function `f`, three processes), with `X.op` the operation of `p₁`,
`X.W` the modifiers (program of `p₂`) and `X.R` the views (program of `p₃`).

* `X.GVSep` — the strong global view property of `X.op, X.W, X.R` (`StrongGlobalView`).
* `X.CStr i l g` — the view `(p₃, l)` has completed in `g` and the relevant operations are those of
  the programs: `p₁` invoked at most `op`, `p₂` at most `M(i+1)`, and the first `i` modifiers
  precede `(p₃, l)` in real time.
* `classify` — in every extension, the result of `(p₃, l)` belongs to the result set
  `gvRes i (l+1) o m` of Definition 4.6.17, where `o`, `m` say whether `op₁ = (p₁,0)`, `(p₂, i)`
  are linearized before `(p₃, l)`.
* `core` — hence (strong global view types) the result of `(p₃, l)` determines whether `op₁`,
  resp. `(p₂, i)`, is linearized before it.
* `decided` — once `(p₃, l)` has completed, its order with `op₁` and with `(p₂, i)` is decided.
* `X.Str i j h` — the structure of the histories built in an iteration of Figure 4.2.
* `kl` — **key lemma**: whether `op₁` (or `(p₂, i)`) is decided before a view `(p₃, l)`, `l ≥ j`,
  only depends on the memory and on the state of `p₃` (two histories that `p₃` cannot tell
  apart agree on it).
* `claim_4_4_5'` — Claim 4.4.5 for an arbitrary not completed operation `(q, m)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]

lemma pre_getElem? {α : Type} (F : ℕ → α) {n k : ℕ} (hk : k < n) : (pre F n)[k]? = some (F k) := by
  simp [pre, hk]

lemma Precedes.mono_idx {α : List (Label P A)} {a : OpId P} {q : P} {j l : ℕ}
    (h : Precedes α a (q, j)) (hjl : j ≤ l) : Precedes α a (q, l) := by
  obtain ⟨β, γ, e, h1, h2⟩ := h
  refine ⟨β, γ, e, h1, fun h3 => h2 ?_⟩
  simp only [Invoked] at h2 h3 ⊢; omega

namespace Ctx

variable {I : Impl A B P L} (X : Ctx I)

/-- The strong global view property for the operations of the context (`StrongGlobalView`). -/
def GVSep : Prop :=
  ∀ i j, 1 ≤ j → ∀ o m o' m' : Bool, (o, m) ≠ (o', m') →
    Disjoint (gvRes X.op X.W X.R i j o m) (gvRes X.op X.W X.R i j o' m')

/-- The view `(p₃, l)` has completed in `g` (and `p₃` invoked nothing more); `p₁` invoked at most
`op`, `p₂` at most `M(i+1)`, nobody else anything, and the first `i` modifiers precede
`(p₃, l)`. -/
structure CStr (i l : ℕ) (g : List (Label P A)) : Prop where
  ops1 : opsOf g X.p₁ = [] ∨ opsOf g X.p₁ = [X.op]
  ops2 : opsOf g X.p₂ = pre X.W i ∨ opsOf g X.p₂ = pre X.W (i + 1)
  ops3 : opsOf g X.p₃ = pre X.R (l + 1)
  resp3 : (respsOf g X.p₃).length = l + 1
  other : ∀ q, q ≠ X.p₁ → q ≠ X.p₂ → q ≠ X.p₃ → opsOf g q = []
  prec : ∀ k < i, Precedes g (X.p₂, k) (X.p₃, l)

/-- **The results of a view** (the reasoning behind Claims 4.6.4, 4.6.8, 4.6.9, 4.6.12): in every
extension, the result of the completed view `(p₃, l)` lies in the result set of
Definition 4.6.17 selected by whether `op₁` and `(p₂, i)` are linearized before it. -/
theorem gvClassify {i l : ℕ} {g s : List (Label P A)} (hc : X.CStr i l g) (hv : I.Valid (g ++ s))
    {r : A.Resp} (hr : respOf g (X.p₃, l) = some r) :
    r ∈ gvRes X.op X.W X.R i (l + 1)
      (decide (pos (X.f (g ++ s)) (X.p₁, 0) < pos (X.f (g ++ s)) (X.p₃, l)))
      (decide (pos (X.f (g ++ s)) (X.p₂, i) < pos (X.f (g ++ s)) (X.p₃, l))) := by
  set α := g ++ s with hα
  set S := X.f α with hS
  have hlin : IsLinearization α S := X.lin α hv
  have hwf : WellFormed α := hv.wellFormed
  set x : OpId P := (X.p₃, l) with hxdef
  have hxc : Completed g x := by simp only [Completed, hc.resp3, hxdef]; omega
  have hxS : x ∈ S.map Prod.fst := hlin.complete x hxc.mono
  have hxinv : Invoked α x := invoked_of_mem_lin hlin hxS
  have hinvg : ∀ y ∈ S.map Prod.fst, pos S y ≤ pos S x → Invoked g y := by
    intro y hy hle
    by_contra hni
    have := pos_lt_of_precedes hlin ⟨g, s, rfl, hxc, hni⟩ hy
    omega
  have hmemS : ∀ e ∈ S, e.1 ∈ S.map Prod.fst := fun e he => List.mem_map.2 ⟨e, he, rfl⟩
  -- the operations of instances invoked in `g`
  have hopg : ∀ y : OpId P, Invoked g y →
      (y = (X.p₁, 0) ∨ (y.1 = X.p₂ ∧ y.2 ≤ i) ∨ (y.1 = X.p₃ ∧ y.2 ≤ l)) ∧
        opOf g y = some ((gvTagOf X.p₁ X.p₂ y).toOp X.op X.W X.R) := by
    rintro ⟨q, k⟩ hy
    simp only [Invoked] at hy
    by_cases h1 : q = X.p₁
    · subst h1
      rcases hc.ops1 with e | e <;> rw [e] at hy <;> simp at hy
      subst hy
      simp [opOf, e, gvTagOf, GVTag.toOp]
    by_cases h2 : q = X.p₂
    · subst h2
      have hk : k ≤ i := by
        rcases hc.ops2 with e | e <;> rw [e] at hy <;> simp [pre] at hy <;> omega
      refine ⟨Or.inr (Or.inl ⟨rfl, hk⟩), ?_⟩
      have : (opsOf g X.p₂)[k]? = some (X.W k) := by
        rcases hc.ops2 with e | e <;> rw [e] <;> rw [e] at hy <;> simp [pre] at hy <;>
          exact pre_getElem? _ (by omega)
      simp [opOf, this, gvTagOf, Ne.symm X.h12, GVTag.toOp]
    by_cases h3 : q = X.p₃
    · subst h3
      rw [hc.ops3] at hy; simp [pre] at hy
      refine ⟨Or.inr (Or.inr ⟨rfl, by omega⟩), ?_⟩
      simp [opOf, hc.ops3, pre_getElem? _ (show k < l + 1 by omega), gvTagOf, Ne.symm X.h13, Ne.symm X.h23, GVTag.toOp]
    · rw [hc.other q h1 h2 h3] at hy; simp at hy
  have hop : ∀ e ∈ S, pos S e.1 ≤ pos S x →
      e.2 = (gvTagOf X.p₁ X.p₂ e.1).toOp X.op X.W X.R := by
    intro e he hle
    have hinv := hinvg _ (hmemS e he) hle
    have h1 := hlin.op_eq e he
    rw [hα, opOf_append_of_invoked hinv, (hopg _ hinv).2] at h1
    exact (Option.some.inj h1).symm
  have hshape := gv_shape S X.p₁ X.p₂ X.p₃ X.op X.W X.R i l X.h12 X.h13 X.h23 hlin.nodup hxS
    (fun e he hle => (hopg _ (hinvg _ (hmemS e he) hle)).1) hop
    (fun k hk => pos_lt_of_precedes hlin ((hc.prec k hk).mono) hxS)
    (fun k hk => pos_lt_of_precedes hlin (hwf.precedes_of_lt hk hxinv) hxS)
    (fun k k' hkk _ hk' => pos_lt_of_precedes hlin
      (hwf.precedes_of_lt hkk (invoked_of_mem_lin hlin hk')) hk')
    (fun k k' hkk hk' => by
      have hk'S : ((X.p₃, k') : OpId P) ∈ S.map Prod.fst :=
        hlin.complete _ (Completed.mono (by simp only [Completed, hc.resp3]; omega))
      exact pos_lt_of_precedes hlin (hwf.precedes_of_lt hkk (invoked_of_mem_lin hlin hk'S)) hk'S)
  have hlen : pos S x < S.length := pos_lt_length_iff.2 hxS
  refine ⟨_, hshape, gv_lastResult X.p₁ X.p₂ X.op X.W X.R hlin.seq hlen ?_ ?_⟩
  · intro e he
    obtain ⟨he, hp⟩ := (mem_take_iff hlin.nodup).1 he
    exact hop e he (by omega)
  · rw [getElem_pos_fst hlen, hα, respOf_append_of_completed hxc, hr]

/-- **Strong global view types: the result of a view determines which of `op₁` and `(p₂, i)`
are linearized before it.** -/
theorem gvCore (hsep : X.GVSep) {i l : ℕ} {g g' s s' : List (Label P A)} (hc : X.CStr i l g)
    (hc' : X.CStr i l g') (hv : I.Valid (g ++ s)) (hv' : I.Valid (g' ++ s'))
    (hr : respOf g (X.p₃, l) = respOf g' (X.p₃, l)) {a : OpId P}
    (ha : a = (X.p₁, 0) ∨ a = (X.p₂, i)) :
    Prec (X.f (g ++ s)) a (X.p₃, l) ↔ Prec (X.f (g' ++ s')) a (X.p₃, l) := by
  obtain ⟨r, hr0⟩ : ∃ r, respOf g (X.p₃, l) = some r := by
    have : Completed g (X.p₃, l) := by simp only [Completed, hc.resp3]; omega
    rw [completed_iff_respOf] at this; exact Option.isSome_iff_exists.1 this
  have h1 := X.gvClassify hc hv hr0
  have h2 := X.gvClassify hc' hv' (hr ▸ hr0)
  have heq := by_contra (fun hne => Set.disjoint_left.1 (hsep i (l + 1) (by omega) _ _ _ _ hne) h1 h2)
  simp only [Prod.mk.injEq, decide_eq_decide] at heq
  rw [prec_iff_pos_lt, prec_iff_pos_lt]
  rcases ha with rfl | rfl
  · exact heq.1
  · exact heq.2

/-- Once the view `(p₃, l)` has completed, its order with `op₁` and with `(p₂, i)` is decided. -/
theorem gvDecided (hsep : X.GVSep) {i l : ℕ} {g : List (Label P A)} (hc : X.CStr i l g)
    {a : OpId P} (ha : a = (X.p₁, 0) ∨ a = (X.p₂, i)) :
    X.DB g a (X.p₃, l) ∨ X.DB g (X.p₃, l) a := by
  by_cases h : ∀ s, I.Valid (g ++ s) → Prec (X.f (g ++ s)) a (X.p₃, l)
  · left; intro s hs; exact prec_asymm (h s hs)
  · right
    push Not at h
    obtain ⟨s₀, hs₀, hn⟩ := h
    intro s hs hp
    exact hn ((X.gvCore hsep hc hc hs hs₀ rfl ha).1 hp)

/-- Two decisions in opposite directions on a completed operation force equality. -/
lemma eq_of_db_both {α : List (Label P A)} (hv : I.Valid α) {a x : OpId P} (hx : Completed α x)
    (h1 : X.DB α a x) (h2 : X.DB α x a) : a = x := by
  have hxS : x ∈ (X.f α).map Prod.fst := (X.lin α hv).complete x hx
  have e1 := (decidedBefore_iff.1 h1) [] (by simpa using hv)
  have e2 := (decidedBefore_iff.1 h2) [] (by simpa using hv)
  simp only [List.append_nil] at e1 e2
  have he : pos (X.f α) a = pos (X.f α) x := le_antisymm e1 e2
  have haS : a ∈ (X.f α).map Prod.fst := pos_lt_length_iff.1 (he ▸ pos_lt_length_iff.2 hxS)
  exact (List.idxOf_inj haS).1 he

/-- Program order: an operation is decided before the later operations of its process. -/
lemma db_program_order (h : List (Label P A)) {q : P} {k k' : ℕ} (hkk : k ≤ k') :
    X.DB h (q, k) (q, k') := by
  show DecidedBefore I X.f h _ _
  rw [decidedBefore_iff]
  intro s hs
  rcases hkk.lt_or_eq with hkk | rfl
  · by_cases hm : ((q, k') : OpId P) ∈ (X.f (h ++ s)).map Prod.fst
    · exact (pos_lt_of_precedes (X.lin _ hs)
        (hs.wellFormed.precedes_of_lt hkk (invoked_of_mem_lin (X.lin _ hs) hm)) hm).le
    · rw [pos_eq_length_iff.2 hm]; exact pos_le_length _ _
  · exact le_rfl

/-! ### The structure of the histories of an iteration -/

/-- The histories built in the iteration of Figure 4.2 in which `op₂ = (p₂, i)` and
`op₃ = (p₃, j)`: `p₁` invoked at most `op`, `p₂` at most `M(i+1)`, `p₃` at most `V(j+1)` and
completed at least `V(j)`, nobody else anything, and the first `i` modifiers precede `op₃`. -/
structure Str (i j : ℕ) (h : List (Label P A)) : Prop where
  valid : I.Valid h
  ops1 : opsOf h X.p₁ = [] ∨ opsOf h X.p₁ = [X.op]
  ops2 : opsOf h X.p₂ = pre X.W i ∨ opsOf h X.p₂ = pre X.W (i + 1)
  ops3 : opsOf h X.p₃ = pre X.R j ∨ opsOf h X.p₃ = pre X.R (j + 1)
  resp3 : j ≤ (respsOf h X.p₃).length
  other : ∀ q, q ≠ X.p₁ → q ≠ X.p₂ → q ≠ X.p₃ → opsOf h q = []
  prec : ∀ k < i, Precedes h (X.p₂, k) (X.p₃, j)

/-- `p₃` runs solo until it has completed the view `(p₃, l)`. -/
lemma exists_run3_to {i j : ℕ} {h : List (Label P A)} (hs : X.Str i j h) {l : ℕ} (hl : j ≤ l) :
    ∃ t D, I.run (h ++ t) = some D ∧ (∀ γ ∈ t, γ.proc = X.p₃) ∧
      opsOf (h ++ t) X.p₃ = pre X.R (l + 1) ∧ (respsOf (h ++ t) X.p₃).length = l + 1 := by
  obtain ⟨C, hC⟩ := hs.valid
  have hle : (respsOf h X.p₃).length ≤ (opsOf h X.p₃).length := I.run_resps_le_ops hC _
  -- first reach an idle state with `pre R c` invoked and completed, `j ≤ c ≤ j + 1`
  obtain ⟨t₀, D₀, h0, h0p, c, hjc, hcl, h0o, h0r⟩ : ∃ t₀ D₀, I.run (h ++ t₀) = some D₀ ∧
      (∀ γ ∈ t₀, γ.proc = X.p₃) ∧ ∃ c, j ≤ c ∧ c ≤ l + 1 ∧ opsOf (h ++ t₀) X.p₃ = pre X.R c ∧
        (respsOf (h ++ t₀) X.p₃).length = c := by
    by_cases hp : C.pend X.p₃ = none
    · have hl := I.run_idle_counts hC hp
      refine ⟨[], C, by simpa using hC, by simp, (respsOf h X.p₃).length, hs.resp3, ?_, ?_, by simp⟩
      · rcases hs.ops3 with e | e <;> rw [e] at hl <;> simp [pre] at hl <;> omega
      · rw [List.append_nil]
        rcases hs.ops3 with e | e <;> rw [e] at hl ⊢ <;> simp [pre] at hl <;> rw [← hl]
    · obtain ⟨s, D, h1, h2, h3, -, h5, h6⟩ := X.exists_finish hC X.p₃ (X.R j)
      have hl := I.run_pend_counts hC hp
      have hops : opsOf h X.p₃ = pre X.R (j + 1) := by
        rcases hs.ops3 with e | e
        · rw [e] at hl; simp [pre] at hl; have := hs.resp3; omega
        · exact e
      refine ⟨s, D, by rw [I.run_append_of_eq hC, h1], h2, j + 1, by omega, by omega, ?_, ?_⟩
      · rw [opsOf_append, h5 hp, hops, List.append_nil]
      · rw [hops] at hl; simp [pre] at hl
        simp only [respsOf_append, List.length_append, h6]; omega
  -- then run views `c, …, l`
  have key : ∀ d c (t₀ : List (Label P A)) D₀, I.run (h ++ t₀) = some D₀ →
      (∀ γ ∈ t₀, γ.proc = X.p₃) → opsOf (h ++ t₀) X.p₃ = pre X.R c →
      (respsOf (h ++ t₀) X.p₃).length = c → c + d = l + 1 →
      ∃ t D, I.run (h ++ t) = some D ∧ (∀ γ ∈ t, γ.proc = X.p₃) ∧
        opsOf (h ++ t) X.p₃ = pre X.R (l + 1) ∧ (respsOf (h ++ t) X.p₃).length = l + 1 := by
    intro d
    induction d with
    | zero => intro c t₀ D₀ h1 h2 h3 h4 h5; exact ⟨t₀, D₀, h1, h2, by rw [h3, show c = l + 1 by omega], by omega⟩
    | succ d ih =>
      intro c t₀ D₀ h1 h2 h3 h4 h5
      have hp : D₀.pend X.p₃ = none := by
        rcases I.run_counts h1 X.p₃ with ⟨e, -⟩ | ⟨-, e⟩
        · exact e
        · rw [h3, h4] at e; simp [pre] at e
      obtain ⟨s, D, g1, g2, -, g4, -, g6⟩ := X.exists_finish h1 X.p₃ (X.R c)
      refine ih (c + 1) (t₀ ++ s) D (by rw [← List.append_assoc, I.run_append_of_eq h1, g1])
        (fun γ hγ => by rcases List.mem_append.1 hγ with hγ | hγ <;> [exact h2 γ hγ; exact g2 γ hγ])
        (by rw [← List.append_assoc, opsOf_append, h3, g4 hp, pre_succ'])
        (by rw [← List.append_assoc, respsOf_append, List.length_append, h4, g6]) (by omega)
  exact key (l + 1 - c) c t₀ D₀ h0 h0p h0o h0r (by omega)

/-- After `p₃` completed the view `(p₃, l)`, `l ≥ j`, the structure `CStr` holds. -/
lemma Str.cstr {i j l : ℕ} {h t : List (Label P A)} (hs : X.Str i j h) (hl : j ≤ l)
    (htp : ∀ γ ∈ t, γ.proc = X.p₃) (ho : opsOf (h ++ t) X.p₃ = pre X.R (l + 1))
    (hr : (respsOf (h ++ t) X.p₃).length = l + 1) : X.CStr i l (h ++ t) := by
  have hnil : ∀ q, q ≠ X.p₃ → opsOf t q = [] := fun q hq => (opsOf_of_proc htp hq).1
  refine ⟨?_, ?_, ho, hr, ?_, fun k hk => Precedes.mono_idx (Precedes.mono (β := t) (hs.prec k hk)) hl⟩
  · rw [opsOf_append, hnil _ X.h13, List.append_nil]; exact hs.ops1
  · rw [opsOf_append, hnil _ X.h23, List.append_nil]; exact hs.ops2
  · intro q h1 h2 h3; rw [opsOf_append, hnil _ h3, List.append_nil]; exact hs.other q h1 h2 h3

/-- **Key lemma.** Two histories of the same iteration that `p₃` cannot tell apart (same memory,
same state of `p₃`, same operations and responses of `p₃`) agree on whether `op₁`, resp.
`(p₂, i)`, is decided before a view `(p₃, l)`, `l ≥ j`. -/
theorem kl (hsep : X.GVSep) {i j : ℕ} {Z Z' : List (Label P A)} {C C' : Config A B P L}
    (hs : X.Str i j Z) (hs' : X.Str i j Z') (hC : I.run Z = some C) (hC' : I.run Z' = some C')
    (hag : Impl.AgreeOn {X.p₃} C C') (ho : opsOf Z X.p₃ = opsOf Z' X.p₃)
    (hr : respsOf Z X.p₃ = respsOf Z' X.p₃) {a : OpId P} (ha : a = (X.p₁, 0) ∨ a = (X.p₂, i))
    {l : ℕ} (hl : j ≤ l) (hd : X.DB Z a (X.p₃, l)) : X.DB Z' a (X.p₃, l) := by
  obtain ⟨t, D, hD, htp, hto, htr⟩ := X.exists_run3_to hs hl
  obtain ⟨D', hD', -⟩ := transport hC hC' hag (fun γ hγ => by simp [htp γ hγ]) hD
  have hc := hs.cstr X hl htp hto htr
  have hc' : X.CStr i l (Z' ++ t) := hs'.cstr X hl htp
    (by rw [opsOf_append, ← ho, ← opsOf_append]; exact hto)
    (by rw [respsOf_append, ← hr, ← respsOf_append]; exact htr)
  have hrr : respOf (Z ++ t) (X.p₃, l) = respOf (Z' ++ t) (X.p₃, l) := by
    simp only [respOf, respsOf_append, hr]
  have hv : I.Valid (Z ++ t ++ []) := ⟨D, by simpa using hD⟩
  have hv' : I.Valid (Z' ++ t) := ⟨D', hD'⟩
  have hane : a ≠ (X.p₃, l) := by
    rcases ha with rfl | rfl
    · exact fun e => X.h13 (Prod.ext_iff.1 e).1
    · exact fun e => X.h23 (Prod.ext_iff.1 e).1
  have hprec : Prec (X.f (Z ++ t ++ [])) a (X.p₃, l) := by
    have hxS : ((X.p₃, l) : OpId P) ∈ (X.f (Z ++ (t ++ []))).map Prod.fst :=
      (X.lin _ (by simpa using hv)).complete _ (by simp only [Completed, List.append_nil, htr]; omega)
    have := (hd.mem (s := t ++ []) (by simpa using hv) hxS)
    rw [prec_iff_pos_lt]
    simpa using pos_lt_of_le_of_ne hxS this.2 hane
  have hdt : X.DB (Z' ++ t) a (X.p₃, l) := by
    intro s hs₀ hp
    have := (X.gvCore hsep hc hc' hv hs₀ hrr ha).1 hprec
    exact prec_asymm this hp
  exact X.owner.decidedBefore_of_append hv' (fun γ hγ => by
    rw [htp γ hγ]; rcases ha with rfl | rfl
    · exact X.h13.symm
    · exact X.h23.symm) hdt

/-! ### Claim 4.4.5 for not yet completed operations -/

/-- **Claim 4.4.5** (general form): if `a` is decided before an operation `(q, m)` of another
process that has not completed, then `a` is decided before every operation `c` of a process other
than `q` that has not been invoked. The proof runs `q` solo until `(q, m)` completes. -/
theorem claim_4_4_5' {h : List (Label P A)} (hv : I.Valid h) {a : OpId P} {q : P} (hq : a.1 ≠ q) :
    ∀ d m, m = (respsOf h q).length + d → X.DB h a (q, m) →
      ∀ c : OpId P, ¬ Invoked h c → c.1 ≠ q → X.DB h a c := by
  intro d
  induction d generalizing h with
  | zero =>
    intro m hm hd c hc hcq
    have hcur : (q, m) = curOp h q := by simp [curOp, hm]
    rw [hcur] at hd
    exact X.claim_4_4_5 hv hq hd hc (fun e => hcq (by rw [e]))
  | succ d ih =>
    intro m hm hd c hc hcq
    obtain ⟨C, hC⟩ := hv
    obtain ⟨s, C', h1, h2, -, -, -, h6⟩ := X.exists_finish hC q (X.W 0)
    have hv' : I.Valid (h ++ s) := ⟨C', by rw [I.run_append_of_eq hC, h1]⟩
    have hc' : ¬ Invoked (h ++ s) c := by
      simp only [Invoked, opsOf_append, (opsOf_of_proc h2 hcq).1, List.append_nil]; exact hc
    have := ih hv' m (by simp only [respsOf_append, List.length_append, h6]; omega)
      (hd.append s) c hc' hcq
    exact X.owner.decidedBefore_of_append hv' (fun γ hγ => by rw [h2 γ hγ]; exact Ne.symm hq) this

end Ctx

end Podc.HelpFreeWaitFree
