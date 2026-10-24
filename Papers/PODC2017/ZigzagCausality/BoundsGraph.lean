import Papers.PODC2017.ZigzagCausality.Zigzag

/-!
# The basic bounds graph `G_B(r)` — Section 5, Appendix B

* `IsSucc` — `σ'` is the (immediate) successor of `σ` on the timeline of their process.
* `BEdge γ r σ w σ'` — the weighted edges of the basic bounds graph `G_B(r)` (Definition 8):
  successor edges of weight `1`, and for every message sent at `σᵢ` and received at `σⱼ` an edge
  `σᵢ → σⱼ` of weight `L i j` and an edge `σⱼ → σᵢ` of weight `−U i j`.
* `BPath γ r σ w σ'` — a path of total weight `w` from `σ` to `σ'` in `G_B(r)`.
* `bpath_prec` — **Lemma 1**: a path of weight `x` gives `σ --x--> σ'`.
* `zigzag_of_bpath` — **Lemma 5** (= Lemma 2): a path of weight `x` from `basic(θ₁)` to
  `basic(θ₂)` gives a zigzag pattern from `θ₁` to `θ₂` of weight `x`.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

namespace Sys

variable (γ : Sys P S M E) (r : Sched P S E) [Finite P]

/-- `σ'` is the successor of `σ`: both appear in `r`, they belong to the same process, and the
local state of `σ'` has exactly one more batch (it is the next local state of the process). -/
def IsSucc (σ σ' : BNode P S M E) : Prop :=
  γ.appears r σ ∧ γ.appears r σ' ∧ σ.1 = σ'.1 ∧ σ'.2.hist.length = σ.2.hist.length + 1

/-- The weighted edges of the basic bounds graph `G_B(r)` (Definition 8). The vertices of
`G_B(r)` are the basic nodes that appear in `r`. -/
inductive BEdge : BNode P S M E → ℤ → BNode P S M E → Prop
  /-- (a) successive nodes of the same process, weight `1`. -/
  | succ {σ σ' : BNode P S M E} : γ.IsSucc r σ σ' → BEdge σ 1 σ'
  /-- (b) a message sent at `σ` and received at `σ'`: an edge `σ → σ'` of weight `L`. -/
  | fwd {σ σ' : BNode P S M E} {j : P} : γ.recv r σ j = some σ' → BEdge σ (γ.net.L σ.1 j) σ'
  /-- (b) a message sent at `σ` and received at `σ'`: an edge `σ' → σ` of weight `−U`. -/
  | bwd {σ σ' : BNode P S M E} {j : P} :
      γ.recv r σ j = some σ' → BEdge σ' (-(γ.net.U σ.1 j : ℤ)) σ

/-- A path of total weight `w` from `σ` to `σ'` in `G_B(r)`. -/
inductive BPath : BNode P S M E → ℤ → BNode P S M E → Prop
  | nil {σ : BNode P S M E} : γ.appears r σ → BPath σ 0 σ
  | cons {σ σ' σ'' : BNode P S M E} {w w' : ℤ} : γ.BEdge r σ w σ' → BPath σ' w' σ'' →
      BPath σ (w + w') σ''

variable {γ r}

theorem IsSucc.timer_lt {σ σ' : BNode P S M E} (h : γ.IsSucc r σ σ') :
    γ.timer r σ < γ.timer r σ' := by
  obtain ⟨h1, h2, hp, hl⟩ := h
  by_contra hle
  push Not at hle
  have := ((γ.timer_le_iff_prefix r hp.symm h2 h1).1 hle).length_le
  omega

theorem IsSucc.ne {σ σ' : BNode P S M E} (h : γ.IsSucc r σ σ') : σ ≠ σ' := by
  rintro rfl
  have := h.2.2.2
  omega

theorem BEdge.appears {σ σ' : BNode P S M E} {w : ℤ} (h : γ.BEdge r σ w σ') :
    γ.appears r σ ∧ γ.appears r σ' := by
  cases h with
  | succ h => exact ⟨h.1, h.2.1⟩
  | fwd h =>
    exact ⟨(recv_appears_left h).1, ((γ.recv_eq_some r).1 h).2 ▸ γ.appears_st r _ _⟩
  | bwd h =>
    exact ⟨((γ.recv_eq_some r).1 h).2 ▸ γ.appears_st r _ _, (recv_appears_left h).1⟩

theorem BPath.appears {σ σ' : BNode P S M E} {w : ℤ} (h : γ.BPath r σ w σ') :
    γ.appears r σ ∧ γ.appears r σ' := by
  induction h with
  | nil h => exact ⟨h, h⟩
  | cons e _ ih => exact ⟨e.appears.1, ih.2⟩

/-- Every edge of `G_B(r)` is a timing constraint satisfied by `r`. -/
theorem BEdge.timer_le (hr : γ.Valid r) {σ σ' : BNode P S M E} {w : ℤ}
    (h : γ.BEdge r σ w σ') : (γ.timer r σ : ℤ) + w ≤ γ.timer r σ' := by
  cases h with
  | succ h => have := h.timer_lt; omega
  | fwd h => have := recv_spec hr h; omega
  | bwd h => have := recv_spec hr h; omega

/-- **Lemma 1** (timer form). A path of weight `w` from `σ` to `σ'` in `G_B(r)` implies
`timer_r(σ) + w ≤ timer_r(σ')`. -/
theorem BPath.timer_le (hr : γ.Valid r) {σ σ' : BNode P S M E} {w : ℤ}
    (h : γ.BPath r σ w σ') : (γ.timer r σ : ℤ) + w ≤ γ.timer r σ' := by
  induction h with
  | nil => simp
  | cons e _ ih => have := e.timer_le hr; omega

/-- **Lemma 1.** If `p` is a path from `σ` to `σ'` in `G_B(r)` with `w(p) = x`, then
`(R, r) ⊨ σ --x--> σ'`. -/
theorem bpath_prec (hr : γ.Valid r) {σ σ' : BNode P S M E} {x : ℤ} (h : γ.BPath r σ x σ') :
    γ.Prec r (GNode.ofB σ) x (GNode.ofB σ') :=
  ⟨σ, σ', γ.basic_ofB r h.appears.1, γ.basic_ofB r h.appears.2, h.timer_le hr⟩

/-! ### Lemma 5: paths in `G_B(r)` give zigzag patterns -/

theorem IsZigzag.tail_eq {F : Fork P S M E} {Z : List (Fork P S M E)} {θ θ' : GNode P S M E}
    (h : γ.IsZigzag r (F :: Z) θ θ') : F.tail = θ := by
  cases Z with
  | nil => exact h.2.1
  | cons G Z => exact h.2.1

theorem IsZigzag.forkIn {F : Fork P S M E} {Z : List (Fork P S M E)} {θ θ' : GNode P S M E}
    (h : γ.IsZigzag r (F :: Z) θ θ') : γ.ForkIn r F := by
  cases Z with
  | nil => exact h.1
  | cons G Z => exact h.1

theorem IsZigzag.ne_nil {Z : List (Fork P S M E)} {θ θ' : GNode P S M E}
    (h : γ.IsZigzag r Z θ θ') : Z ≠ [] := by
  rintro rfl; exact h

/-- Prepending a fork to a zigzag pattern. -/
theorem IsZigzag.cons {F : Fork P S M E} {Z : List (Fork P S M E)} {θ θ' θ'' : GNode P S M E}
    (hF : γ.ForkIn r F) (ht : F.tail = θ) (hadj : γ.Adj r F.head θ')
    (hZ : γ.IsZigzag r Z θ' θ'') : γ.IsZigzag r (F :: Z) θ θ'' := by
  match Z, hZ with
  | G :: Z, hZ =>
    have := hZ.tail_eq
    subst this
    exact ⟨hF, ht, hadj, hZ⟩

theorem wtZ_cons {F : Fork P S M E} {Z : List (Fork P S M E)} {θ' θ'' : GNode P S M E}
    (hZ : γ.IsZigzag r Z θ' θ'') :
    γ.wtZ r (F :: Z) = F.wt γ.net + γ.gap r F.head θ' + γ.wtZ r Z := by
  match Z, hZ with
  | G :: Z, hZ =>
    have := hZ.tail_eq
    subst this
    rfl

/-- Replacing the first fork by one with the same head. -/
theorem IsZigzag.replace {F F' : Fork P S M E} {Z : List (Fork P S M E)} {θ θ' : GNode P S M E}
    (h : γ.IsZigzag r (F :: Z) θ θ') (hF' : γ.ForkIn r F') (hh : F'.head = F.head) :
    γ.IsZigzag r (F' :: Z) F'.tail θ' := by
  cases Z with
  | nil => exact ⟨hF', rfl, hh.trans h.2.2⟩
  | cons G Z => exact ⟨hF', rfl, hh ▸ h.2.2.1, h.2.2.2⟩

theorem wtZ_replace {F F' : Fork P S M E} {Z : List (Fork P S M E)} (hh : F'.head = F.head) :
    γ.wtZ r (F' :: Z) = γ.wtZ r (F :: Z) - F.wt γ.net + F'.wt γ.net := by
  cases Z with
  | nil => simp [wtZ]
  | cons G Z => simp only [wtZ, hh]; ring

theorem gap_of_eq {θ θ' : GNode P S M E} (h : γ.basic r θ = γ.basic r θ') : γ.gap r θ θ' = 0 := by
  simp [gap, h]

theorem adj_of_eq {θ θ' : GNode P S M E} {σ : BNode P S M E} (h : γ.basic r θ = some σ)
    (h' : γ.basic r θ' = some σ) : γ.Adj r θ θ' :=
  ⟨σ, σ, h, h', rfl, le_rfl⟩

theorem forkIn_triv {θ : GNode P S M E} (h : γ.appearsG r θ) : γ.ForkIn r (Fork.triv θ) := by
  simp [ForkIn, h]

theorem appearsG_of {θ : GNode P S M E} {σ : BNode P S M E} (h : γ.basic r θ = some σ) :
    γ.appearsG r θ := by
  simp [appearsG, h]

theorem basic_ext_single {θ : GNode P S M E} {σ σ' : BNode P S M E} {j : P}
    (h : γ.basic r θ = some σ) (hj : γ.recv r σ j = some σ') :
    γ.basic r (θ.ext [j]) = some σ' := by
  have ha : γ.appears r σ' := ((γ.recv_eq_some r).1 hj).2 ▸ γ.appears_st r _ _
  simp [basic_ext, h, hj, ha]

/-- **Lemma 5** (and Lemma 2). Let `basic(θ₁, r) = σ₁` and `basic(θ₂, r) = σ₂`. For every path
from `σ₁` to `σ₂` in `G_B(r)` with weight `x` there is a zigzag pattern `Z` from `θ₁` to `θ₂` in
`r` with `wt(Z) = x`. -/
theorem zigzag_of_bpath {σ₁ σ₂ : BNode P S M E} {x : ℤ} (hp : γ.BPath r σ₁ x σ₂) :
    ∀ {θ₁ θ₂ : GNode P S M E}, γ.basic r θ₁ = some σ₁ → γ.basic r θ₂ = some σ₂ →
      ∃ Z, γ.IsZigzag r Z θ₁ θ₂ ∧ γ.wtZ r Z = x := by
  induction hp with
  | nil _ =>
    intro θ₁ θ₂ h1 h2
    refine ⟨[Fork.triv θ₁, Fork.triv θ₂], ?_, ?_⟩
    · exact ⟨forkIn_triv (appearsG_of h1), by simp, by simpa using adj_of_eq h1 h2,
        forkIn_triv (appearsG_of h2), by simp, by simp⟩
    · simp [wtZ, gap_of_eq (h1.trans h2.symm)]
  | @cons σ σ' σ'' w w' e p ih =>
    intro θ₁ θ₂ h1 h2
    have hσ' : γ.appears r σ' := p.appears.1
    obtain ⟨Z', hZ', hw'⟩ := ih (γ.basic_ofB r hσ') h2
    cases e with
    | succ hs =>
      refine ⟨Fork.triv θ₁ :: Z', IsZigzag.cons (forkIn_triv (appearsG_of h1)) (by simp)
        (by rw [Fork.triv_head]; exact ⟨σ, σ', h1, γ.basic_ofB r hσ', hs.2.2.1, hs.timer_lt.le⟩)
        hZ', ?_⟩
      rw [wtZ_cons hZ', hw']
      have : γ.gap r θ₁ (GNode.ofB σ') = 1 := by
        simp only [gap, h1, γ.basic_ofB r hσ', Option.some.injEq, hs.ne, ite_false]
      simp [this]
    | @fwd _ _ k hk =>
      let F : Fork P S M E := ⟨θ₁, [k], []⟩
      have hh : γ.basic r F.head = some σ' := basic_ext_single h1 hk
      have hFt : F.tail = θ₁ := by simp [F, Fork.tail]
      have hF : γ.ForkIn r F := ⟨appearsG_of hh, hFt ▸ appearsG_of h1⟩
      refine ⟨F :: Z', IsZigzag.cons hF hFt (adj_of_eq hh (γ.basic_ofB r hσ')) hZ', ?_⟩
      rw [wtZ_cons hZ', hw', gap_of_eq (hh.trans (γ.basic_ofB r hσ').symm)]
      simp [F, Fork.wt, ← γ.basic_proc r h1]
    | @bwd _ _ k hk =>
      obtain ⟨F₁, Zr, rfl⟩ : ∃ F₁ Zr, Z' = F₁ :: Zr := by
        cases Z' with
        | nil => exact absurd rfl hZ'.ne_nil
        | cons F₁ Zr => exact ⟨F₁, Zr, rfl⟩
      have ht1 : F₁.tail = GNode.ofB σ' := hZ'.tail_eq
      let F' : Fork P S M E := ⟨F₁.base, F₁.p1, F₁.p2 ++ [σ.1]⟩
      have hF'h : F'.head = F₁.head := rfl
      have hF't : F'.tail = (GNode.ofB σ').ext [σ.1] := by
        rw [← ht1]; simp [F', Fork.tail, GNode.ext_ext]
      have hk1 : k = σ.1 := (((γ.recv_eq_some r).1 hk).2 ▸ rfl : σ.1 = k).symm
      subst hk1
      have hb : γ.basic r F'.tail = some σ := by
        rw [hF't]; exact basic_ext_single (γ.basic_ofB r hσ') hk
      have hF' : γ.ForkIn r F' := ⟨hF'h ▸ hZ'.forkIn.1, appearsG_of hb⟩
      refine ⟨Fork.triv θ₁ :: F' :: Zr, IsZigzag.cons (forkIn_triv (appearsG_of h1)) (by simp)
        (by simpa using adj_of_eq h1 hb) (hZ'.replace hF' hF'h), ?_⟩
      rw [wtZ_cons (hZ'.replace hF' hF'h), wtZ_replace hF'h, hw', Fork.triv_head,
        gap_of_eq (h1.trans hb.symm)]
      have hproc : lastP F₁.base.proc F₁.p2 = σ'.1 := by
        have := congrArg GNode.proc ht1
        rw [Fork.tail, GNode.proc_ext] at this
        simpa [GNode.ofB, GNode.proc] using this
      rw [Fork.triv_wt]
      simp only [F', Fork.wt, Net.Up_append, hproc, Net.Up_cons,
        Net.Up_nil]
      push_cast
      ring

end Sys

end Podc.ZigzagCausality
