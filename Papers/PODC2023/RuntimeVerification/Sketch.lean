import Mathlib
import Papers.PODC2023.RuntimeVerification.Exec

/-!
# The sketch `X(τ)` of a set of 4-tuples (Section 7.3.3)

Given a set `τ` of 4-tuples `(p, op, y, λ)` (we also record the index `k` of the operation), the
paper builds the history `X(τ)`: the distinct views `σ₁ ⊂ σ₂ ⊂ … ⊂ σₘ` are processed in
increasing order; for each `σᵢ`, first the invocations of the operations in `σᵢ \ σᵢ₋₁` are
appended, then the responses of the tuples with view `σᵢ`.

We define `X(τ)` as a timed history `XTH τ`: an invocation gets the time
`(|σ|, 0, rank)` where `σ` is the smallest view containing it, a response gets `(|λ|, 1, rank)`;
since views form a chain, `|σ|` determines `σ`. The within-block order (`rank`, from the
process index and the operation index) is one of the arbitrary orders the paper allows.

Under the structural properties `Valid τ` (self-inclusion, containment comparability and
process sequentiality of Remark 7.2, plus consistency), `XTH τ` is a well-formed timed history
whose real-time order is: the response of `a` precedes the invocation of `b` iff `b ∉ λ_a`
(`tr_lt_ti_iff`).
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing

set_option linter.unusedSectionVars false

/-- A 4-tuple written to `M` by the verifier: the operation `(p, k, o)`, its response `y` from
`A` and its view. -/
structure Tup (n : ℕ) (Op Y : Type) where
  p : Fin n
  k : ℕ
  o : Op
  y : Y
  view : Finset (IRec n Op)
  deriving DecidableEq

/-- Times of sketches. -/
abbrev TX := Lex (ℕ × Lex (ℕ × ℕ))

/-- Lexicographic triples. -/
def lex3 (a b c : ℕ) : TX := toLex (a, toLex (b, c))

@[simp] theorem lex3_lt {a b c a' b' c' : ℕ} :
    lex3 a b c < lex3 a' b' c' ↔ a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c'))) := by
  simp [lex3, Prod.Lex.toLex_lt_toLex]

@[simp] theorem lex3_inj {a b c a' b' c' : ℕ} :
    lex3 a b c = lex3 a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  simp [lex3]

namespace Sketch

variable {n : ℕ} {Op Y : Type} [DecidableEq Op] [DecidableEq Y] [Inhabited Op] [Inhabited Y]
variable (τ : Finset (Tup n Op Y))

/-- All invocation records appearing in the views of `τ`. -/
def allInv : Finset (IRec n Op) := τ.biUnion Tup.view

/-- Indices of the operations of `p` appearing in `τ`'s views. -/
def ids (p : Fin n) : Finset ℕ := ((allInv τ).filter (·.1 = p)).image (·.2.1)

/-- Indices of the operations of `p` that have a tuple in `τ`. -/
def cids (p : Fin n) : Finset ℕ := (τ.filter (·.p = p)).image (·.k)

open Classical in
/-- The argument of the operation `(p, k)`. -/
noncomputable def opOf' (p : Fin n) (k : ℕ) : Op :=
  if h : ∃ x ∈ allInv τ, x.1 = p ∧ x.2.1 = k then h.choose.2.2 else default

open Classical in
/-- The response (with view) of the operation `(p, k)`. -/
noncomputable def resOf' (p : Fin n) (k : ℕ) : Y × Finset (IRec n Op) :=
  if h : ∃ t ∈ τ, t.p = p ∧ t.k = k then (h.choose.y, h.choose.view) else (default, ∅)

/-- The size of the smallest view containing the operation `(p, k)`. -/
noncomputable def sInv (p : Fin n) (k : ℕ) : ℕ :=
  sInf {c | ∃ t ∈ τ, (∃ x ∈ t.view, x.1 = p ∧ x.2.1 = k) ∧ t.view.card = c}

/-- Tie-breaking rank inside a block. -/
def rank (p : Fin n) (k : ℕ) : ℕ := k * n + p.val

/-- The sketch `X(τ)` as a timed history (responses with views). -/
noncomputable def XTH : TH (Fin n) Op (Y × Finset (IRec n Op)) TX where
  m p := (ids τ p).card
  c p := (cids τ p).card
  op := opOf' τ
  res := resOf' τ
  ti p k := lex3 (sInv τ p k) 0 (rank p k)
  tr p k := lex3 (resOf' τ p k).2.card 1 (rank p k)

/-- The sketch with the views disregarded (what is tested against the object `O`). -/
noncomputable def XTHy : TH (Fin n) Op Y TX := (XTH τ).mapRes Prod.fst

/-- Structural properties of the sets of tuples read by the verifier (Remark 7.2 and
consistency). -/
structure Valid : Prop where
  uniq : ∀ t ∈ τ, ∀ t' ∈ τ, t.p = t'.p → t.k = t'.k → t = t'
  self : ∀ t ∈ τ, (t.p, t.k, t.o) ∈ t.view
  cons : ∀ x ∈ allInv τ, ∀ x' ∈ allInv τ, x.1 = x'.1 → x.2.1 = x'.2.1 → x = x'
  chain : ∀ t ∈ τ, ∀ t' ∈ τ, t.view ⊆ t'.view ∨ t'.view ⊆ t.view
  down : ∀ x ∈ allInv τ, ∀ j < x.2.1, ∃ t ∈ τ, t.p = x.1 ∧ t.k = j ∧ x ∉ t.view

variable {τ}

theorem mem_allInv {x : IRec n Op} : x ∈ allInv τ ↔ ∃ t ∈ τ, x ∈ t.view := by
  simp [allInv]

/-- A downward closed finite set of naturals is an initial segment. -/
theorem lt_card_iff_mem {S : Finset ℕ} (hS : ∀ k ∈ S, ∀ j < k, j ∈ S) (k : ℕ) :
    k < S.card ↔ k ∈ S := by
  constructor
  · intro hk
    by_contra hn
    have : S ⊆ Finset.range k := by
      intro j hj
      rw [Finset.mem_range]
      by_contra hjk
      push Not at hjk
      rcases hjk.lt_or_eq with h | h
      · exact hn (hS j hj k h)
      · exact hn (h ▸ hj)
    have := Finset.card_le_card this
    simp at this; omega
  · intro hk
    have : Finset.range (k + 1) ⊆ S := by
      intro j hj
      rw [Finset.mem_range] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
      · exact hS k hk j h
      · exact h ▸ hk
    have := Finset.card_le_card this
    simp at this; omega

theorem mem_ids {p : Fin n} {k : ℕ} : k ∈ ids τ p ↔ ∃ x ∈ allInv τ, x.1 = p ∧ x.2.1 = k := by
  simp only [ids, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl, rfl⟩
  · rintro ⟨x, hx, rfl, rfl⟩; exact ⟨x, ⟨hx, rfl⟩, rfl⟩

theorem mem_cids {p : Fin n} {k : ℕ} : k ∈ cids τ p ↔ ∃ t ∈ τ, t.p = p ∧ t.k = k := by
  simp only [cids, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, rfl⟩, rfl⟩; exact ⟨t, ht, rfl, rfl⟩
  · rintro ⟨t, ht, rfl, rfl⟩; exact ⟨t, ⟨ht, rfl⟩, rfl⟩

theorem self_mem_allInv (hv : Valid τ) {t : Tup n Op Y} (ht : t ∈ τ) :
    (t.p, t.k, t.o) ∈ allInv τ :=
  mem_allInv.2 ⟨t, ht, hv.self t ht⟩

theorem ids_down (hv : Valid τ) (p : Fin n) : ∀ k ∈ ids τ p, ∀ j < k, j ∈ ids τ p := by
  intro k hk j hj
  obtain ⟨x, hx, rfl, rfl⟩ := mem_ids.1 hk
  obtain ⟨t, ht, htp, rfl, -⟩ := hv.down x hx j hj
  exact mem_ids.2 ⟨_, self_mem_allInv hv ht, htp, rfl⟩

theorem cids_down (hv : Valid τ) (p : Fin n) : ∀ k ∈ cids τ p, ∀ j < k, j ∈ cids τ p := by
  intro k hk j hj
  obtain ⟨t, ht, rfl, rfl⟩ := mem_cids.1 hk
  obtain ⟨t', ht', htp, rfl, -⟩ := hv.down _ (self_mem_allInv hv ht) j hj
  exact mem_cids.2 ⟨t', ht', htp, rfl⟩

theorem lt_m_iff (hv : Valid τ) {p : Fin n} {k : ℕ} :
    k < (XTH τ).m p ↔ ∃ x ∈ allInv τ, x.1 = p ∧ x.2.1 = k := by
  rw [show (XTH τ).m p = (ids τ p).card from rfl, lt_card_iff_mem (ids_down hv p), mem_ids]

theorem lt_c_iff (hv : Valid τ) {p : Fin n} {k : ℕ} :
    k < (XTH τ).c p ↔ ∃ t ∈ τ, t.p = p ∧ t.k = k := by
  rw [show (XTH τ).c p = (cids τ p).card from rfl, lt_card_iff_mem (cids_down hv p), mem_cids]

theorem op_eq (hv : Valid τ) {x : IRec n Op} (hx : x ∈ allInv τ) :
    (XTH τ).op x.1 x.2.1 = x.2.2 := by
  have h : ∃ x' ∈ allInv τ, x'.1 = x.1 ∧ x'.2.1 = x.2.1 := ⟨x, hx, rfl, rfl⟩
  simp only [XTH, opOf', dif_pos h]
  have := h.choose_spec
  rw [hv.cons _ this.1 x hx this.2.1 this.2.2]

theorem res_eq (hv : Valid τ) {t : Tup n Op Y} (ht : t ∈ τ) :
    (XTH τ).res t.p t.k = (t.y, t.view) := by
  have h : ∃ t' ∈ τ, t'.p = t.p ∧ t'.k = t.k := ⟨t, ht, rfl, rfl⟩
  simp only [XTH, resOf', dif_pos h]
  have := h.choose_spec
  rw [hv.uniq _ this.1 t ht this.2.1 this.2.2]

theorem sInv_le {t : Tup n Op Y} (ht : t ∈ τ) {x : IRec n Op} (hx : x ∈ t.view) :
    sInv τ x.1 x.2.1 ≤ t.view.card :=
  Nat.sInf_le ⟨t, ht, ⟨x, hx, rfl, rfl⟩, rfl⟩

theorem sInv_spec (hv : Valid τ) {x : IRec n Op} (hx : x ∈ allInv τ) :
    ∃ t ∈ τ, x ∈ t.view ∧ t.view.card = sInv τ x.1 x.2.1 := by
  obtain ⟨t, ht, hxt⟩ := mem_allInv.1 hx
  obtain ⟨t', ht', ⟨x', hx', h1, h2⟩, hc⟩ :=
    Nat.sInf_mem (s := {c | ∃ t ∈ τ, (∃ y ∈ t.view, y.1 = x.1 ∧ y.2.1 = x.2.1) ∧ t.view.card = c})
      ⟨_, t, ht, ⟨x, hxt, rfl, rfl⟩, rfl⟩
  have : x' = x := hv.cons x' (mem_allInv.2 ⟨t', ht', hx'⟩) x hx h1 h2
  subst this
  exact ⟨t', ht', hx', hc⟩

/-- The key property: `|λ_t| < sInv x` iff `x ∉ λ_t`. -/
theorem card_lt_sInv_iff (hv : Valid τ) {t : Tup n Op Y} (ht : t ∈ τ) {x : IRec n Op}
    (hx : x ∈ allInv τ) : t.view.card < sInv τ x.1 x.2.1 ↔ x ∉ t.view := by
  constructor
  · intro h hxt
    exact absurd (sInv_le ht hxt) (by omega)
  · intro hxt
    obtain ⟨t', ht', hxt', hc⟩ := sInv_spec hv hx
    rw [← hc]
    rcases hv.chain t ht t' ht' with h | h
    · exact Finset.card_lt_card ⟨h, fun h' => hxt (h' hxt')⟩
    · exact absurd (h hxt') hxt

theorem rank_inj {p q : Fin n} {k j : ℕ} (h : rank p k = rank q j) : p = q ∧ k = j := by
  simp only [rank] at h
  have hp := p.isLt
  have hq := q.isLt
  have h1 : (k * n + p.val) / n = (j * n + q.val) / n := by rw [h]
  have hn : 0 < n := by omega
  rw [Nat.add_comm (k * n), Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hp,
    Nat.add_comm (j * n), Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hq] at h1
  have hkj : k = j := by omega
  subst hkj
  exact ⟨Fin.ext (by omega), rfl⟩

theorem tr_lt_ti_iff (hv : Valid τ) {t : Tup n Op Y} (ht : t ∈ τ) {x : IRec n Op}
    (hx : x ∈ allInv τ) : (XTH τ).tr t.p t.k < (XTH τ).ti x.1 x.2.1 ↔ x ∉ t.view := by
  simp only [XTH]
  rw [show resOf' τ t.p t.k = (t.y, t.view) from res_eq hv ht, lex3_lt,
    ← card_lt_sInv_iff hv ht hx]
  constructor
  · rintro (h | ⟨-, h | ⟨h, -⟩⟩)
    · exact h
    · omega
    · omega
  · exact Or.inl

theorem XTH_WF (hv : Valid τ) : (XTH τ).WF where
  c_le_m p := by
    apply Finset.card_le_card
    intro k hk
    obtain ⟨t, ht, rfl, rfl⟩ := mem_cids.1 hk
    exact mem_ids.2 ⟨_, self_mem_allInv hv ht, rfl, rfl⟩
  m_le_c p := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hx, hxp, hxk⟩ := (lt_m_iff hv).1 (show (XTH τ).c p + 1 < (XTH τ).m p by omega)
    obtain ⟨t, ht, htp, htk, -⟩ := hv.down x hx ((XTH τ).c p) (by omega)
    have := (lt_c_iff hv).2 ⟨t, ht, htp.trans hxp, htk⟩
    omega
  inv_lt_res p k hk := by
    obtain ⟨t, ht, rfl, rfl⟩ := (lt_c_iff hv).1 hk
    have h1 := sInv_le ht (hv.self t ht)
    simp only [XTH]
    rw [show resOf' τ t.p t.k = (t.y, t.view) from res_eq hv ht, lex3_lt]
    rcases h1.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl (by norm_num)⟩
  res_lt_inv p k hk := by
    obtain ⟨x, hx, rfl, hxk⟩ := (lt_m_iff hv).1 hk
    obtain ⟨t, ht, htp, htk, hxt⟩ := hv.down x hx k (by omega)
    have := (tr_lt_ti_iff hv ht hx).2 hxt
    rw [htp, htk, hxk] at this
    exact this
  inj := by
    rintro ⟨p, k, b⟩ ⟨q, j, b'⟩ - - he
    simp only [TH.time, XTH] at he
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte, lex3_inj] at he
    · obtain ⟨rfl, rfl⟩ := rank_inj he.2.2; rfl
    · exact absurd he.2.1 (by norm_num)
    · exact absurd he.2.1 (by norm_num)
    · obtain ⟨rfl, rfl⟩ := rank_inj he.2.2; rfl

end Sketch

end Podc2023.RuntimeVerification
