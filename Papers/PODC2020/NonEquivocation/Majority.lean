import Papers.PODC2020.NonEquivocation.Exec

/-!
# Consistent majorities (Definition 4.3) and Lemmas 4.4–4.8

Madsen–Debois, PODC 2020, Section 4.2.

`τ` is the local view of a process `p` (`τ w = σ (p :: w)`, see `loc`). `Maj t τ p q Q v`
(Definition 4.3, written `maj^{q,v}_{p,Q}(t, σ_p, P)` in the paper): `|Q| ≥ t + 1` and every route
`p|w|q` with `w ∈ Q*`, `|w| ≤ t` (and no consecutive duplicates) carries the value `v` to `p`.

In the paper `v` ranges over the values *and* `⊥` (Lemma 4.7 claims that no consistent majority for
`⊥` exists). With `v : V` (a genuine value) `Maj` excludes `⊥` by typing; `MajOpt` is the paper's
version with `v : Option V`, and `lemma_4_7_false` shows that Lemma 4.7 fails for it: the decider
`p` itself may be the only non-faulty member of `Q` (its own "report" `σ(p|p|q) = σ(p|q)` is the
`⊥` it received). Under that reading Lemma 4.8 fails too, and so does a line 8 of Algorithm 2
that allows `v = ⊥` (see `Counterexamples.lean`).
-/

namespace NonEquivocation

variable {P V : Type*}

/-- The local view of `p` (all rounds): `σ_p(w) = σ(p|w)`. -/
def loc (σ : MsgMap P V) (p : P) : List P → Option V := fun w => σ (p :: w)

/-- **Definition 4.3** (consistent majority), for a genuine value `v`. -/
def Maj (t : ℕ) (τ : List P → Option V) (p q : P) (Q : Finset P) (v : V) : Prop :=
  t + 1 ≤ Q.card ∧ ∀ w : List P, (∀ x ∈ w, x ∈ Q) → w.length ≤ t → Seq (p :: (w ++ [q])) →
    τ (w ++ [q]) = some v

/-- Definition 4.3 as printed, with `v` ranging over values and `⊥` (`Option V`). -/
def MajOpt (t : ℕ) (τ : List P → Option V) (p q : P) (Q : Finset P) (v : Option V) : Prop :=
  t + 1 ≤ Q.card ∧ ∀ w : List P, (∀ x ∈ w, x ∈ Q) → w.length ≤ t → Seq (p :: (w ++ [q])) →
    τ (w ++ [q]) = v

lemma Maj.direct {t : ℕ} {τ : List P → Option V} {p q : P} {Q : Finset P} {v : V}
    (h : Maj t τ p q Q v) (hpq : p ≠ q) : τ [q] = some v :=
  h.2 [] (by simp) (by simp) (seq_pair.2 hpq)

/-- **Lemma 4.6**: a process has consistent `q`-majorities for at most one value. -/
theorem lemma_4_6 {t t' : ℕ} {τ : List P → Option V} {p q : P} {Q R : Finset P} {v u : V}
    (hpq : p ≠ q) (hv : Maj t τ p q Q v) (hu : Maj t' τ p q R u) : v = u := by
  have := (hv.direct hpq).symm.trans (hu.direct hpq)
  simpa using this

/-- Routes through non-faulty processes carry the truth (used for Lemma 4.4). -/
lemma route_honest [OmitVal V] {k : ℕ} {S F : Finset P} {σ : MsgMap P V} (hσ : NonFaulty k S F σ)
    {q : P} (hqS : q ∈ S) (hqF : q ∉ F) :
    ∀ w : List P, (∀ y ∈ w, y ∈ S ∧ y ∉ F) → w.length < k → ∀ x ∈ S, Seq (x :: (w ++ [q])) →
      σ (x :: (w ++ [q])) = some (rep (σ [q])) := by
  intro w
  induction w with
  | nil =>
    intro _ hk x hx hs
    exact hσ q hqS hqF x hx [] (by simp) hs hk
  | cons y w ih =>
    intro hw hk x hx hs
    have hyS := (hw y (by simp)).1
    have hyF := (hw y (by simp)).2
    have hs' : Seq (x :: y :: (w ++ [q])) := hs
    rw [show x :: (y :: w ++ [q]) = x :: y :: (w ++ [q]) from rfl,
      hσ y hyS hyF x hx (w ++ [q]) (by
        intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact (hw z (by simp [hz])).1
        · simp at hz; exact hz ▸ hqS) hs' (by simp at hk ⊢; omega),
      ih (fun z hz => hw z (by simp [hz])) (by simp at hk ⊢; omega) y hyS hs'.tail]
    rfl

/-- **Lemma 4.4**: if `q` is non-faulty, every process `p` has a consistent `q`-majority (formed by the
non-faulty processes) for `q`'s private value (`⟨⊥⟩` if it has none, which happens only in the
recursive instances of Algorithm 2). -/
theorem lemma_4_4 [OmitVal V] [DecidableEq P] {t : ℕ} {S F : Finset P} {σ : MsgMap P V}
    (hσ : NonFaulty (t + 1) S F σ) {p q : P} (hpS : p ∈ S) (hqS : q ∈ S) (hqF : q ∉ F)
    (hcard : t + 1 ≤ (S \ F).card) :
    Maj t (loc σ p) p q (S \ F) (rep (σ [q])) := by
  refine ⟨hcard, fun w hw hl hs => ?_⟩
  exact route_honest hσ hqS hqF w (fun y hy => by simpa using hw y hy) (by omega) p hpS hs

/-- **Lemma 4.5**: if `p` has no consistent `q`-majority at all, then `q` is faulty
(contraposition of Lemma 4.4). -/
theorem lemma_4_5 [OmitVal V] [DecidableEq P] {t : ℕ} {S F : Finset P} {σ : MsgMap P V}
    (hσ : NonFaulty (t + 1) S F σ) {p q : P} (hpS : p ∈ S) (hqS : q ∈ S)
    (hcard : t + 1 ≤ (S \ F).card) (h : ∀ v (Q : Finset P), Q ⊆ S → ¬ Maj t (loc σ p) p q Q v) :
    q ∈ F := by
  by_contra hqF
  exact h _ _ Finset.sdiff_subset (lemma_4_4 hσ hpS hqS hqF hcard)

/-- **Lemma 4.8**: two processes that have consistent `r`-majorities have them for the same value
(by weak non-equivocation of `r`'s first-round message). -/
theorem lemma_4_8 {k t t' : ℕ} {S : Finset P} {σ : MsgMap P V} (hk : 0 < k) (hσ : WeakNE k S σ)
    {p q r : P} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hpr : p ≠ r) (hqr : q ≠ r)
    {Q R : Finset P} {v u : V} (hv : Maj t (loc σ p) p r Q v) (hu : Maj t' (loc σ q) q r R u) :
    v = u := by
  have h1 : σ [p, r] = some v := hv.direct hpr
  have h2 : σ [q, r] = some u := hu.direct hqr
  have := hσ r hr p hp q hq [] (by simp) (seq_pair.2 hpr) (seq_pair.2 hqr) hk
    (by rw [h1]; simp) (by rw [h2]; simp)
  rw [h1, h2] at this
  simpa using this

/-- Lemma 4.7, repaired: a consistent majority (in the printed sense, `MajOpt`) cannot be for `⊥` if
it contains a non-faulty process other than the decider `p` and the source `q`. (With `Maj`, values
are never `⊥` by typing.) -/
theorem lemma_4_7_repaired [OmitVal V] {k t : ℕ} {S F : Finset P} {σ : MsgMap P V}
    (hσ : NonFaulty k S F σ) (hk : 1 < k) (ht : 1 ≤ t) {p q x : P} (hp : p ∈ S) (hq : q ∈ S)
    {Q : Finset P} (hQ : Q ⊆ S) (hx : x ∈ Q) (hxF : x ∉ F) (hxp : x ≠ p) (hxq : x ≠ q) :
    ¬ MajOpt t (loc σ p) p q Q none := by
  intro h
  have := h.2 [x] (by simpa using hx) (by simpa using ht) (by
    simp [Seq, hxp.symm, hxq])
  have e := hσ x (hQ hx) hxF p hp [q] (by simpa using hq) (by simp [Seq, hxp.symm, hxq]) (by simpa)
  simp only [loc] at this
  rw [show p :: ([x] ++ [q]) = [p, x, q] from rfl] at this
  rw [this] at e
  simp at e

end NonEquivocation
