import Papers.PODC2015.MinimalSynchronyBC.CB

/-!
# Adopt-commit for Byzantine processes (Figure 2, Theorem 2)

A correct process `i` with input `x i`:
1. `est_i ← CB_broadcast AC_PROP(x i)` (any CB-broadcast implementation, `CBSpec`);
2. RB-broadcasts `AC_EST(est_i)`;
3. waits until `AC_EST` messages were RB-delivered from a set `Q` of `n − t` processes with values
   in `cb_valid_i` (`Fig2.Follows.wait`; it does not wait forever if this happens: `live`);
4. `MFA_i` is a most frequent value among these `n − t` messages (`mfa`);
5. returns `(commit, MFA_i)` if all of them carry `MFA_i`, else `(adopt, MFA_i)` (`Fig2.out`).
-/

namespace MinimalSynchronyBC

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- An execution of Figure 2. -/
structure Fig2 (P V : Type*) where
  /-- The CB instance of line 1. -/
  cb : CBObs P V
  /-- RB deliveries of the `AC_EST` messages. -/
  E : RBTrace P V
  /-- Completion of line 3: time, the `n − t` senders, and the value `MFA` of line 4. -/
  dec : P → Option (ℕ × Finset P × V)

/-- Number of the messages of `Q` (as delivered to `i` by time `τ`) that carry `u`. -/
def Fig2.count (A : Fig2 P V) (i : P) (τ : ℕ) (Q : Finset P) (u : V) : ℕ :=
  (Q.filter fun j => A.E i τ j = some u).card

/-- The predicate of line 3 for the set `Q` at time `τ`. -/
def Fig2.Wait (A : Fig2 P V) (t : ℕ) (i : P) (τ : ℕ) (Q : Finset P) : Prop :=
  Q.card = Fintype.card P - t ∧ ∀ j ∈ Q, ∃ e, A.E i τ j = some e ∧ e ∈ A.cb.valid i τ

/-- The rules of Figure 2 for correct processes. -/
structure Fig2.Follows (t : ℕ) (B : Finset P) (x : P → Option V) (A : Fig2 P V) : Prop where
  /-- Line 1 uses a CB-broadcast instance with inputs `x`. -/
  cb : CBSpec t B x A.cb
  /-- Line 2: a correct process RB-broadcasts the value returned at line 1. -/
  est : RBSpec B (fun j => (A.cb.ret j).map Prod.snd) A.E
  /-- Line 3. -/
  wait : ∀ {i τ Q w}, i ∉ B → A.dec i = some (τ, Q, w) → A.Wait t i τ Q
  /-- Line 4: `MFA` is a most frequent value of the `n − t` messages. -/
  mfa : ∀ {i τ Q w}, i ∉ B → A.dec i = some (τ, Q, w) →
    (∃ j ∈ Q, A.E i τ j = some w) ∧ ∀ u, A.count i τ Q u ≤ A.count i τ Q w
  /-- Line 3 terminates as soon as its predicate holds (after line 1 returned). -/
  live : ∀ {i}, i ∉ B → (A.cb.ret i).isSome → (∃ τ Q, A.Wait t i τ Q) → (A.dec i).isSome

/-- Lines 5–8: the output of a process. -/
def Fig2.out (A : Fig2 P V) (i : P) : Option (Tag × V) :=
  (A.dec i).map fun d =>
    (if ∀ j ∈ d.2.1, A.E i d.1 j = some d.2.2 then .commit else .adopt, d.2.2)

/-- Unfolding `Fig2.out`. -/
theorem Fig2.out_eq_some {A : Fig2 P V} {i : P} {d : Tag} {v : V} (h : A.out i = some (d, v)) :
    ∃ τ Q, A.dec i = some (τ, Q, v) ∧
      d = if ∀ j ∈ Q, A.E i τ j = some v then .commit else .adopt := by
  unfold Fig2.out at h
  rcases hd : A.dec i with _ | ⟨τ, Q, w⟩
  · simp [hd] at h
  · simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨τ, Q, rfl, h1.symm⟩

omit [DecidableEq V] in
/-- The correct processes form a set of at least `n − t` processes. -/
theorem card_correct_ge {t : ℕ} {B : Finset P} (hB : B.card ≤ t) :
    Fintype.card P - t ≤ (univ.filter fun j => j ∉ B).card := by
  have hC : (univ.filter fun j => j ∉ B) = Bᶜ := by ext j; simp
  rw [hC, card_compl]
  omega

/-- **Theorem 2.** Figure 2 implements an `m`-valued adopt-commit object in
`BZ_AS[t < n/3]`. -/
theorem theorem2 {t : ℕ} {B : Finset P} {x : P → Option V} {A : Fig2 P V}
    (hn : 3 * t < Fintype.card P) (hB : B.card ≤ t) (hA : A.Follows t B x) :
    ACSpec t B x A.out := by
  classical
  -- every value seen in a completed line 3 of a correct process is in its `cb_valid`
  have hwaitv : ∀ {i τ Q w j e}, i ∉ B → A.dec i = some (τ, Q, w) → j ∈ Q →
      A.E i τ j = some e → e ∈ A.cb.valid i τ := by
    intro i τ Q w j e hi hd hj he
    obtain ⟨e', he', hv⟩ := (hA.wait hi hd).2 j hj
    rw [he] at he'
    cases he'
    exact hv
  refine
    { termination := ?_
      domain := ?_
      obligation := ?_
      quasi := ?_ }
  · -- AC-Termination
    intro hall hfeas i hi
    have hdec : (A.dec i).isSome := by
      refine hA.live hi (hA.cb.op_termination hall hfeas i hi) ?_
      obtain ⟨Q, hQC, hQ⟩ := exists_subset_card_eq (card_correct_ge (B := B) hB)
      obtain ⟨τ, hτ⟩ := exists_time_forall Q
        (fun j τ => ∃ e, A.E i τ j = some e ∧ e ∈ A.cb.valid i τ)
        (fun j τ τ' ⟨e, he, hv⟩ hle => ⟨e, hA.est.mono he hle, hA.cb.mono hle hv⟩) (by
          intro j hjQ
          have hj : j ∉ B := by simpa using hQC hjQ
          obtain ⟨⟨τj, ej⟩, hr⟩ := Option.isSome_iff_exists.1
            (hA.cb.op_termination hall hfeas j hj)
          have hej := hA.cb.op_validity hj hr
          obtain ⟨σ, hσ⟩ := hA.est.term1 hi hj (v := ej) (by simp [hr])
          obtain ⟨T, hT⟩ := hA.cb.set_agreement hi hj
          refine ⟨max σ (max T τj), ej, hA.est.mono hσ (le_max_left _ _), ?_⟩
          rw [hT _ (le_trans (le_max_left _ _) (le_max_right _ _))]
          exact hA.cb.mono (le_trans (le_max_right _ _) (le_max_right _ _)) hej)
      exact ⟨τ, Q, hQ, hτ⟩
    simpa [Fig2.out] using hdec
  · -- AC-Output domain
    intro i d v hi hout
    obtain ⟨τ, Q, hd, -⟩ := Fig2.out_eq_some hout
    obtain ⟨⟨j, hj, hjv⟩, -⟩ := hA.mfa hi hd
    exact hA.cb.set_validity hi (hwaitv hi hd hj hjv)
  · -- AC-Obligation
    intro v i d w hx hi hout
    obtain ⟨τ, Q, hd, hdtag⟩ := Fig2.out_eq_some hout
    have hall : ∀ j ∈ Q, A.E i τ j = some v := by
      intro j hj
      obtain ⟨e, he, hv⟩ := (hA.wait hi hd).2 j hj
      obtain ⟨j', hj', hxj'⟩ := hA.cb.set_validity hi hv
      rcases hx j' hj' with h | h
      · rw [h] at hxj'; cases hxj'
      · rw [h] at hxj'; cases hxj'; exact he
    obtain ⟨⟨j, hj, hjw⟩, -⟩ := hA.mfa hi hd
    have hwv : w = v := by
      rw [hall j hj] at hjw
      exact (Option.some_injective _ hjw).symm
    subst hwv
    exact ⟨hdtag.trans (ite_eq_left_of_eq_true _ _ (eq_true hall)), rfl⟩
  · -- AC-Quasi-agreement
    intro i k v d w hi hk houti houtk
    obtain ⟨τ, Q, hd, hdtag⟩ := Fig2.out_eq_some houti
    have hallQ : ∀ j ∈ Q, A.E i τ j = some v := by
      by_contra hne
      simp only [hne, ite_false] at hdtag
      cases hdtag
    obtain ⟨τ', Q', hd', -⟩ := Fig2.out_eq_some houtk
    have hQ := (hA.wait hi hd).1
    have hQ' := (hA.wait hk hd').1
    -- the messages of `Q ∩ Q'` carry `v` at `k`
    have hinter : (Q ∩ Q') ⊆ Q'.filter fun j => A.E k τ' j = some v := by
      intro j hj
      rw [mem_inter] at hj
      obtain ⟨e, he, -⟩ := (hA.wait hk hd').2 j hj.2
      have := RBSpec.agree hA.est hi hk (hallQ j hj.1) he
      subst this
      exact mem_filter.2 ⟨hj.2, he⟩
    have hcard := card_union_add_card_inter Q Q'
    have hU := card_le_univ (Q ∪ Q')
    have hcv := card_le_card hinter
    have hmax := (hA.mfa hk hd').2 v
    by_contra hwv
    have hdisj : Disjoint (Q'.filter fun j => A.E k τ' j = some v)
        (Q'.filter fun j => A.E k τ' j = some w) := by
      rw [disjoint_filter]
      intro j _ h1 h2
      rw [h1] at h2
      exact hwv (Option.some_injective _ h2).symm
    have hsum := card_union_of_disjoint hdisj
    have hsub : (Q'.filter fun j => A.E k τ' j = some v) ∪
        (Q'.filter fun j => A.E k τ' j = some w) ⊆ Q' := union_subset (filter_subset _ _)
      (filter_subset _ _)
    have hle := card_le_card hsub
    unfold Fig2.count at hmax
    omega

end MinimalSynchronyBC
