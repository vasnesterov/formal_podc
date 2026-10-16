import Papers.PODC2020.NonEquivocation.FaultModels

/-!
# From weak non-equivocation to crusader agreement (Section 7.1)

Madsen–Debois, *On the Subject of Non-Equivocation* (PODC 2020), Section 7.1.

Crusader agreement (Dolev) for each source `q`: every correct `p` outputs a value for `q`, or `none`
("I know that `q` is faulty"). We formalise it in the message-map framework, for all sources at once
(like interactive consistency):

* `CAAlg`: `A p τ q : Option V` is `p`'s decision for the source `q` from its local view `τ`;
* `SolvesCA M k t A`: in every `σ` of `M` (with `k` rounds, at most `t` faulty processes, correct
  private values present):
  - **validity**: a correct `p` outputs `σ [q]` for every correct source `q`;
  - **crusader agreement**: two correct processes that both output a value output the same value;
  - **soundness** (footnote 2: "know that `q` is faulty"): a correct process outputs `none` only if
    `q` is faulty.

Termination is built in (decision after `k` rounds).

Results:

* `crusader1_solvesCA_wne`: the 1-round algorithm "output what the source sent me" solves crusader
  agreement under weak non-equivocation for every `t` and every `n` ("Weak non-equivocation implies a
  trivial solution to crusader agreement").
* `crusader1_not_solvesCA_byzantine`: the same algorithm fails in the Byzantine model as soon as there
  are a faulty source and two correct receivers (e.g. `n = 3`, `t = 1`).
-/

namespace NonEquivocation

variable {P V : Type*}

/-- A deterministic crusader-agreement algorithm: `A p τ q` is the decision of `p` for the source
`q` from its local view `τ`; `none` means "the source is faulty". -/
def CAAlg (P V : Type*) := P → (List P → Option V) → P → Option V

/-- `A` solves crusader agreement (Section 7.1) in fault model `M` with `k` rounds and at most `t`
faulty processes. -/
def SolvesCA [OmitVal V] (M : FaultModel P V) (k t : ℕ) (A : CAAlg P V) : Prop :=
  ∀ (F : Finset P) (σ : MsgMap P V), F.card ≤ t → M k F σ → (∀ q, q ∉ F → σ [q] ≠ none) →
    (∀ p q, p ∉ F → q ∉ F → A p (view k σ p) q = σ [q]) ∧
    (∀ p p' q a b, p ∉ F → p' ∉ F →
      A p (view k σ p) q = some a → A p' (view k σ p') q = some b → a = b) ∧
    (∀ p q, p ∉ F → A p (view k σ p) q = none → q ∈ F)

/-- The trivial one-round crusader algorithm of Section 7.1: decide the value received from the
source in round 1 (`⊥`, i.e. `none`, means the source is faulty). -/
def crusader1 [DecidableEq P] : CAAlg P V := fun p τ q => if p = q then τ [] else τ [q]

variable [Fintype P] [DecidableEq P] [OmitVal V]

/-- **Section 7.1** ("From weak non-equivocation to crusader agreement"): under weak
non-equivocation the one-round algorithm `crusader1` solves crusader agreement, for any number `t`
of faulty processes and any `n`. -/
theorem crusader1_solvesCA_wne {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    SolvesCA (wne : FaultModel P V) k t crusader1 := by
  intro F σ _ hM hval
  obtain ⟨hN, hW⟩ := hM
  -- the round-1 message of a correct `q` to `p ≠ q` is its private value
  have hcor : ∀ p q, q ∉ F → p ≠ q → σ [p, q] = σ [q] := by
    intro p q hq hpq
    have := hN q (Finset.mem_univ _) hq p (Finset.mem_univ _) [] (by simp) (by simp [Seq, hpq])
      (by simp; omega)
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hval q hq)
    simp only [hv, rep_some] at this ⊢
    exact this
  have hdec : ∀ p q, crusader1 p (view k σ p) q = if p = q then σ [p] else σ [p, q] := by
    intro p q
    simp only [crusader1, view_of_le (by simp : ([] : List P).length ≤ k),
      view_of_le (by simpa using hk : [q].length ≤ k)]
  have hvalid : ∀ p q, p ∉ F → q ∉ F → crusader1 p (view k σ p) q = σ [q] := by
    intro p q _ hq
    rw [hdec]
    split_ifs with h
    · rw [h]
    · exact hcor p q hq h
  refine ⟨hvalid, ?_, ?_⟩
  · intro p p' q a b hp hp' ha hb
    rw [hdec] at ha hb
    by_cases h : p = q
    · subst h
      simp only [ite_true] at ha
      by_cases h' : p' = p
      · subst h'; simp_all
      · simp only [h', ite_false] at hb
        rw [hcor p' p hp h', ha] at hb
        exact Option.some_injective _ hb
    · simp only [h, ite_false] at ha
      by_cases h' : p' = q
      · subst h'
        simp only [ite_true] at hb
        rw [hcor p p' hp' h, hb] at ha
        exact (Option.some_injective _ ha).symm
      · simp only [h', ite_false] at hb
        have := hW q (Finset.mem_univ _) p (Finset.mem_univ _) p' (Finset.mem_univ _) [] (by simp)
          (by simp [Seq, h]) (by simp [Seq, h']) (by simp; omega) (by simp [ha]) (by simp [hb])
        rw [ha, hb] at this
        exact Option.some_injective _ this
  · intro p q hp hnone
    by_contra hq
    exact hval q hq (by rw [← hvalid p q hp hq, hnone])

/-- **Section 7.1**, necessity of the assumption: in the (unauthenticated) Byzantine fault model the
same algorithm fails crusader agreement as soon as there is a faulty source `s` with two correct
receivers `p, p'` (e.g. `n = 3`, `t = 1`): `s` sends `a` to `p` and `b ≠ a` to `p'`. -/
theorem crusader1_not_solvesCA_byzantine {s p p' : P} (hsp : s ≠ p) (hsp' : s ≠ p')
    (hpp' : p ≠ p') {a b : V} (hab : a ≠ b) {k t : ℕ} (hk : 1 ≤ k) (ht : 1 ≤ t) :
    ¬ SolvesCA (byzantine : FaultModel P V) k t crusader1 := by
  intro h
  let σ : MsgMap P V := mkσ (fun _ => some a) fun x y l o =>
    if y = s ∧ l = [] then (if x = p then some a else some b) else some (rep o)
  have hN : NonFaulty k Finset.univ {s} σ :=
    nonFaulty_mkσ fun x y l o hy => by simp at hy; simp [hy]
  obtain ⟨-, hag, -⟩ := h {s} σ (by simpa using ht) hN (fun _ _ => by simp [σ])
  have hview : ∀ x, x ≠ s → crusader1 x (view k σ x) s = σ [x, s] := by
    intro x hx
    simp [crusader1, hx, view_of_le (by simpa using hk : [s].length ≤ k)]
  refine hab (hag p p' s a b (by simpa using hsp.symm) (by simpa using hsp'.symm) ?_ ?_)
  · rw [hview p hsp.symm]; simp [σ]
  · rw [hview p' hsp'.symm]; simp [σ, hpp'.symm]

end NonEquivocation
