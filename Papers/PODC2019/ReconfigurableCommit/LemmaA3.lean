/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Spec
import Podc.Foundations.Order.TopologicalSort

/-!
# Lemma A.3 of Bravo–Gotsman (PODC 2019): TCS-LL implies TCS

*M. Bravo, A. Gotsman. Reconfigurable Atomic Transaction Commit. PODC 2019*, App. A.2,
Lemma A.3: every history satisfying the low-level specification TCS-LL (Figure 6) is correct
w.r.t. the global certification function `f`, provided the shard-local functions `fₛ, gₛ`
match `f` (conditions (1), (3)–(5)).

## Main statements

* `lemma_A_3`: the lemma, under the additional hypothesis `EpsNeutral` (`fₛ({ε}, l) = commit`).
* `lemma_A_3_false`: without `EpsNeutral` the lemma is false: a two-shard counterexample.

## Proof

The committed transactions are ordered by a topological sort of `≺rt ∪ ≺dec`, which is acyclic
by constraint (13). For a committed `t` and an earlier committed `t'`, on each shard `s` of both,
the positions `posₛ[t] ≠ posₛ[t']` (7); constraint (10) puts the earlier of the two into the
`Tₛ` or `Pₛ` set of the later one, and (9) together with (4), (5) and monotonicity gives
`fₛ({l' | s}, l | s) = commit`; the case `t ∈ Tₛ[t']` with `t'` before `t` contradicts the
order because then `t ≺dec t'`. On shards of `t` that `t'` does not touch, `l' | s = ε`, and here
the paper silently needs `fₛ({ε}, l | s) = commit` (`EpsNeutral`).
-/

namespace Podc.ReconfigurableCommit

section LemmaA3

variable {T Pl S : Type*} [DecidableEq T] [DecidableEq Pl]

/-- The committed transactions of `h`, as a finset. -/
def committedSet (h : History T Pl) : Finset T :=
  (h.filterMap fun
    | Event.decide t .commit => some t
    | _ => none).toFinset

omit [DecidableEq Pl] in
theorem mem_committedSet {h : History T Pl} {t : T} : t ∈ committedSet h ↔ Committed h t := by
  unfold committedSet Committed
  simp only [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hs⟩
    rcases e with ⟨t', l⟩ | ⟨t', d⟩
    · simp at hs
    · cases d
      · simp only [Option.some.injEq] at hs
        subst hs
        exact he
      · simp at hs
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_payloadsOf {h : History T Pl} {ts : List T} {l : Pl} :
    l ∈ payloadsOf h ts ↔ ∃ t ∈ ts, Event.certify t l ∈ h := by
  unfold payloadsOf
  simp only [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hs⟩
    rcases e with ⟨t', l'⟩ | ⟨t', d⟩
    · simp only at hs
      split_ifs at hs with ht
      cases hs
      exact ⟨t', ht, he⟩
    · simp at hs
  · rintro ⟨t, ht, he⟩
    exact ⟨_, he, by simp [ht]⟩

/-- The shard-level core of Lemma A.3: if `t` commits with payload `l`, then on every shard `s`,
`fₛ(∅, l | s) = commit` and `fₛ({l' | s}, l | s) = commit` for every committed `t'` (payload `l'`)
placed before `t` by an order `ord` extending `≺dec` on committed transactions. -/
theorem shard_commit {σ : Sharding T Pl S} {f : Finset Pl → Pl → Dec}
    {fs gs : S → Finset Pl → Pl → Dec} (hm : Matching σ f fs gs) (heps : EpsNeutral σ fs)
    {h : History T Pl} (hval : ∀ t l, Event.certify t l ∈ h → σ.ValidPayload t l)
    {w : LLWitness T Pl S} (hw : w.Valid σ h fs gs) (ord : List T)
    (hord : ∀ a b, Committed h a → Committed h b → LLWitness.DecRel h w a b →
      ord.idxOf a < ord.idxOf b)
    {t : T} {l : Pl} (ht : Committed h t) (hl : Event.certify t l ∈ h) (s : S) :
    fs s ∅ (σ.proj l s) = .commit ∧
    ∀ t' l', Committed h t' → Event.certify t' l' ∈ h → ord.idxOf t' < ord.idxOf t →
      fs s {σ.proj l' s} (σ.proj l s) = .commit := by
  by_cases hs : s ∈ σ.shards t
  swap
  · rw [hval t l hl s hs]
    exact ⟨hm.fs_eps s ∅, fun _ _ _ _ _ => hm.fs_eps s _⟩
  have hdt : w.ds s t = some .commit := (hw.c6 t .commit ht).1 rfl s hs
  have hsome : (w.ds s t).isSome := by simp [hdt]
  have h9 := Dec.meet_eq_commit.1 ((Dec.le_commit_iff).1 (hw.c9 s t .commit hdt))
  have hpl : w.pload s t = σ.proj l s := (hw.c8 t l s hl).1 hdt
  refine ⟨hpl ▸ (hm.distrib_fs s).mono (Finset.empty_subset _) h9.1, ?_⟩
  intro t' l' ht' hl' hlt
  by_cases hs' : s ∈ σ.shards t'
  swap
  · rw [hval t' l' hl' s hs']
    exact heps s _
  have hdt' : w.ds s t' = some .commit := (hw.c6 t' .commit ht').1 rfl s hs'
  have hsome' : (w.ds s t').isSome := by simp [hdt']
  have h9' :=
    Dec.meet_eq_commit.1 ((Dec.le_commit_iff).1 (hw.c9 s t' .commit hdt'))
  have hpl' : w.pload s t' = σ.proj l' s := (hw.c8 t' l' s hl').1 hdt'
  have hne : t ≠ t' := by
    rintro rfl
    exact lt_irrefl _ hlt
  rw [← hpl, ← hpl']
  rcases lt_or_gt_of_ne (hw.c7 s t' t hne.symm hsome' hsome) with hp | hp
  · -- `t'` is earlier on shard `s`: it is in `Tₛ[t]` or in `Pₛ[t]`
    by_cases hP : t' ∈ w.Ps s t
    · apply hm.g_imp_f
      refine (hm.distrib_gs s).mono ?_ h9.2
      rw [Finset.singleton_subset_iff]
      exact Finset.mem_image_of_mem _ hP
    · have hT : t' ∈ w.Ts s t := (hw.c10 s t hsome t').2 ⟨⟨hsome', hp, ht'⟩, hP⟩
      refine (hm.distrib_fs s).mono ?_ h9.1
      rw [Finset.singleton_subset_iff]
      exact Finset.mem_image_of_mem _ hT
  · -- `t` is earlier on shard `s`: `t ∈ Pₛ[t']` (use (5)), or `t ∈ Tₛ[t']`, contradicting `ord`
    by_cases hP : t ∈ w.Ps s t'
    · apply hm.comm
      refine (hm.distrib_gs s).mono ?_ h9'.2
      rw [Finset.singleton_subset_iff]
      exact Finset.mem_image_of_mem _ hP
    · have hT : t ∈ w.Ts s t' := (hw.c10 s t' hsome' t).2 ⟨⟨hsome, hp, ht⟩, hP⟩
      exact absurd (hord t t' ht ht' ⟨s, hsome', Or.inl hT⟩) (lt_asymm hlt)

/-- Lemma A.3 of [Bravo–Gotsman 2019]: if the shard-local certification functions `fₛ, gₛ`
match `f` (conditions (1), (3)–(5)), then every history with valid payloads that satisfies
TCS-LL (Figure 6) is correct w.r.t. `f`.

The hypothesis `heps : EpsNeutral σ fs` (`fₛ({ε}, l) = commit`) is missing from the paper and
cannot be dropped, see `lemma_A_3_false`. Neither constraint (12) of Figure 6 nor
well-formedness of `h` is needed. -/
theorem lemma_A_3 {σ : Sharding T Pl S} {f : Finset Pl → Pl → Dec}
    {fs gs : S → Finset Pl → Pl → Dec} (hm : Matching σ f fs gs) (heps : EpsNeutral σ fs)
    {h : History T Pl} (hval : ∀ t l, Event.certify t l ∈ h → σ.ValidPayload t l) (hll : TCSLL σ fs gs h) :
    Correct f h := by
  obtain ⟨w, hw⟩ := hll
  obtain ⟨ord, hnd, hmem, hord⟩ := Finset.exists_topologicalSort (committedSet h)
    (fun a b => RT h a b ∨ LLWitness.DecRel h w a b)
    (fun a hc => hw.c13 a (Relation.TransGen.mono (fun _ _ hab => hab.2.2) _ _ hc))
  have hmem' : ∀ t, t ∈ ord ↔ Committed h t := fun t => (hmem t).trans mem_committedSet
  refine ⟨ord, hnd, hmem', fun t t' ht ht' hrt =>
    hord t t' ((hmem t).1 ht) ((hmem t').1 ht') (Or.inl hrt), ?_⟩
  intro i l hl
  have ht : Committed h ord[i] := (hmem' _).1 (List.getElem_mem _)
  have hidx : ord.idxOf ord[i] = i := hnd.idxOf_getElem _ _
  rw [hm.match_f]
  intro s
  obtain ⟨h0, h1⟩ := shard_commit hm heps hval hw ord
    (fun a b ha hb hab => hord a b (mem_committedSet.2 ha) (mem_committedSet.2 hb) (Or.inr hab))
    ht hl s
  rw [(hm.distrib_fs s).eq_commit_iff]
  refine ⟨h0, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨t', ht', hc'⟩ := mem_payloadsOf.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht'
  rw [List.getElem_take] at hc'
  have hj' : j < i := by simp at hj; omega
  refine h1 _ x ((hmem' _).1 (List.getElem_mem _)) hc' ?_
  rw [hidx, hnd.idxOf_getElem]
  exact hj'

end LemmaA3

/-! ### Without `EpsNeutral`, Lemma A.3 fails

Two shards `s₁ = false`, `s₂ = true` and two transactions `t₁ = false`, `t₂ = true` with
`shards(tᵢ) = {sᵢ}`. Payloads are `Option Bool`: `ε = none`, and `some s` is a payload living on
shard `s` only. On every shard, `fₛ(L, l) = commit` iff no `x ∈ L` is `ε` unless `l = ε`, and
`gₛ(L, l) = commit` iff `ε ∉ L` and `l ≠ ε`; `f` is defined from `fₛ` by (3). Conditions (1),
(3)–(5) and `fₛ(L, ε) = commit` hold, but `fₛ({ε}, l) = abort` for `l ≠ ε`.

The history `certify(t₁, some s₁) decide(t₁, commit) certify(t₂, some s₂) decide(t₂, commit)`
satisfies TCS-LL: each transaction is alone on its shard (position `0`, `Tₛ = Pₛ = ∅`). It is
not correct: real time forces `t₁` before `t₂`, and `f({some s₁}, some s₂) = abort` because on
shard `s₂` the projection of `some s₁` is `ε`. -/

namespace LemmaA3Counterexample

/-- A certification function given by a pairwise "no conflict" predicate:
`ofPred P L l = commit ↔ ∀ x ∈ L, P x l`. -/
def ofPred {Pl : Type*} (P : Pl → Pl → Prop) [DecidableRel P] (L : Finset Pl) (l : Pl) : Dec :=
  if ∀ x ∈ L, P x l then .commit else .abort

theorem ofPred_eq_commit {Pl : Type*} {P : Pl → Pl → Prop} [DecidableRel P] {L : Finset Pl}
    {l : Pl} : ofPred P L l = .commit ↔ ∀ x ∈ L, P x l := by
  unfold ofPred
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by simp) h

theorem ofPred_distributive {Pl : Type*} [DecidableEq Pl] (P : Pl → Pl → Prop)
    [DecidableRel P] : Distributive (ofPred P) := by
  intro L₁ L₂ l
  have ext : ∀ a b : Dec, (a = .commit ↔ b = .commit) → a = b := by
    intro a b; cases a <;> cases b <;> simp
  apply ext
  rw [Dec.meet_eq_commit, ofPred_eq_commit, ofPred_eq_commit, ofPred_eq_commit,
    Finset.forall_mem_union]

/-- The sharding: `shards(t) = {t}`, `(some s') | s = some s'` if `s = s'` and `ε` otherwise. -/
def σ : Sharding Bool (Option Bool) Bool where
  shards t := {t}
  proj l s := if l = some s then l else none
  eps := none

/-- `fₛ(L, l) = commit` iff every `x ∈ L` is non-`ε` unless `l = ε`. -/
def fs (_ : Bool) : Finset (Option Bool) → Option Bool → Dec :=
  ofPred fun x l => x ≠ none ∨ l = none

/-- `gₛ(L, l) = commit` iff every `x ∈ L` is non-`ε` and `l ≠ ε`. -/
def gs (_ : Bool) : Finset (Option Bool) → Option Bool → Dec :=
  ofPred fun x l => x ≠ none ∧ l ≠ none

/-- `f` defined from `fₛ` by (3). -/
def f : Finset (Option Bool) → Option Bool → Dec :=
  ofPred fun x l => ∀ s, σ.proj x s ≠ none ∨ σ.proj l s = none

theorem matching : Matching σ f fs gs where
  distrib_f := ofPred_distributive _
  distrib_fs _ := ofPred_distributive _
  distrib_gs _ := ofPred_distributive _
  fs_eps s L := ofPred_eq_commit.2 fun _ _ => Or.inr rfl
  match_f l L := by
    simp only [f, fs, ofPred_eq_commit, Finset.forall_mem_image]
    exact ⟨fun h s x hx => h x hx s, fun h x hx s => h s hx⟩
  g_imp_f s L l h := ofPred_eq_commit.2 fun x hx => Or.inl (ofPred_eq_commit.1 h x hx).1
  comm s l l' h := ofPred_eq_commit.2 fun x hx => by
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Or.inl (ofPred_eq_commit.1 h l (Finset.mem_singleton_self l)).2

theorem not_epsNeutral : ¬ EpsNeutral σ fs := by
  intro h
  have := ofPred_eq_commit.1 (h false (some false)) none (Finset.mem_singleton_self _)
  simp at this

/-- The history `certify(t₁, some s₁) decide(t₁, commit) certify(t₂, some s₂)
decide(t₂, commit)`. -/
def hist : History Bool (Option Bool) :=
  [.certify false (some false), .decide false .commit, .certify true (some true),
    .decide true .commit]

theorem wellFormed : WellFormed hist where
  certify_unique t l l' h₁ h₂ := by
    simp only [hist, List.mem_cons, Event.certify.injEq, reduceCtorEq, List.mem_nil_iff,
      or_false, false_or] at h₁ h₂
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  decide_unique t d d' h₁ h₂ := by
    simp only [hist, List.mem_cons, Event.decide.injEq, reduceCtorEq, List.mem_nil_iff,
      or_false, false_or] at h₁ h₂
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  decide_after_certify j t d hj := by
    match j, hj with
    | ⟨0, _⟩, hj => simp [hist] at hj
    | ⟨1, _⟩, hj =>
      simp [hist] at hj
      obtain ⟨rfl, rfl⟩ := hj
      exact ⟨⟨0, by simp [hist]⟩, by simp, _, rfl⟩
    | ⟨2, _⟩, hj => simp [hist] at hj
    | ⟨3, _⟩, hj =>
      simp [hist] at hj
      obtain ⟨rfl, rfl⟩ := hj
      exact ⟨⟨2, by simp [hist]⟩, by simp, _, rfl⟩

theorem validPayload : ∀ t l, Event.certify t l ∈ hist → σ.ValidPayload t l := by
  intro t l hl s hs
  simp only [hist, List.mem_cons, Event.certify.injEq, reduceCtorEq, List.mem_nil_iff,
    or_false, false_or] at hl
  simp only [σ, Finset.mem_singleton] at hs
  rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [σ, Ne.symm hs]

/-- The TCS-LL witness: each transaction votes `commit` on its only shard, at position `0`. -/
def w : LLWitness Bool (Option Bool) Bool where
  ds s t := if s = t then some .commit else none
  pos _ _ := 0
  pload _ t := some t
  Ts _ _ := ∅
  Ps _ _ := ∅

theorem rt_iff {a b : Bool} (h : RT hist a b) : a = false ∧ b = true := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, ⟨d, hd⟩, ⟨l, hl⟩⟩ := h
  simp only [hist, List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;> simp_all [hist]

theorem decRel_false {a b : Bool} : ¬ LLWitness.DecRel hist w a b := by
  rintro ⟨s, -, h | ⟨h, -⟩⟩ <;> simp [w] at h

theorem tcsll : TCSLL σ fs gs hist := by
  refine ⟨w, ?_⟩
  constructor
  · intro s t h
    simp only [w, Option.isSome_ite] at h
    subst h
    refine ⟨Finset.mem_singleton_self _, some s, ?_⟩
    cases s <;> simp [hist]
  · intro t d _ s hs
    simp only [σ, Finset.mem_singleton] at hs
    simp [w, hs]
  · intro t d hd
    simp only [hist, List.mem_cons, Event.decide.injEq, reduceCtorEq, List.mem_nil_iff,
      or_false, false_or] at hd
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [σ, w]
  · intro s t₁ t₂ hne h₁ h₂
    simp only [w, Option.isSome_ite] at h₁ h₂
    exact absurd (h₁.symm.trans h₂) hne
  · intro t l s hl
    simp only [hist, List.mem_cons, Event.certify.injEq, reduceCtorEq, List.mem_nil_iff,
      or_false, false_or] at hl
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [w, Option.ite_none_right_eq_some] at h
      obtain ⟨rfl, -⟩ := h
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [w, σ]
    · simp [w] at h
  · intro s t d h
    simp only [w, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [Dec.le_commit_iff, Dec.meet_eq_commit]
    exact ⟨ofPred_eq_commit.2 (by simp [w]), ofPred_eq_commit.2 (by simp [w])⟩
  · intro s t _ t'
    simp [w]
  · intro s t _ t' h
    simp [w] at h
  · intro t h
    have key : ∀ a b, Relation.TransGen (fun a b => RT hist a b ∨ LLWitness.DecRel hist w a b)
        a b → a = false ∧ b = true := by
      intro a b hab
      induction hab with
      | single h => exact h.elim rt_iff (fun h => absurd h decRel_false)
      | tail _ h ih =>
        have := h.elim rt_iff (fun h => absurd h decRel_false)
        exact absurd (ih.2.symm.trans this.1) (by decide)
    have := key t t h
    exact absurd (this.1.symm.trans this.2) (by decide)

/-- The witness `w` also satisfies constraint (12), vacuously (the transactions share no shard). -/
theorem constraint12 : LLWitness.Constraint12 σ hist w := by
  intro t' t s hrt h₁ h₂ _ _
  simp only [σ, Finset.mem_singleton] at h₁ h₂
  subst h₁ h₂
  have := rt_iff hrt
  exact absurd (this.1.symm.trans this.2) (by decide)

theorem not_correct : ¬ Correct f hist := by
  rintro ⟨ord, hnd, hmem, hrt, hlegal⟩
  have h1 : false ∈ ord := (hmem false).2 (by simp [Committed, hist])
  have h2 : true ∈ ord := (hmem true).2 (by simp [Committed, hist])
  have hlt := hrt false true h1 h2 ⟨⟨1, by simp [hist]⟩, ⟨2, by simp [hist]⟩, by decide,
    ⟨.commit, rfl⟩, ⟨some true, rfl⟩⟩
  have hi := List.idxOf_lt_length_of_mem h2
  have hget : ord[ord.idxOf true] = true := List.getElem_idxOf hi
  have := hlegal ⟨ord.idxOf true, hi⟩ (some true) (by simp [hget, hist])
  have hpay : some false ∈ payloadsOf hist (ord.take (ord.idxOf true)) := by
    refine mem_payloadsOf.2 ⟨false, ?_, by simp [hist]⟩
    rw [List.mem_take_iff_getElem]
    exact ⟨ord.idxOf false, by simp [hlt, List.idxOf_lt_length_of_mem h1],
      List.getElem_idxOf (List.idxOf_lt_length_of_mem h1)⟩
  have := ofPred_eq_commit.1 this _ hpay true
  simp [σ] at this

end LemmaA3Counterexample

open LemmaA3Counterexample in
/-- Lemma A.3 of [Bravo–Gotsman 2019] is false as stated (without `EpsNeutral`): conditions (1),
(3)–(5) and `fₛ(L, ε) = commit` do not imply `fₛ({ε}, l) = commit`, and there is a well-formed
history with valid payloads satisfying TCS-LL that is not correct w.r.t. `f`. (The TCS-LL
witness also satisfies constraint (12), see `LemmaA3Counterexample.constraint12`.) -/
theorem lemma_A_3_false :
    ∃ (σ : Sharding Bool (Option Bool) Bool) (f : Finset (Option Bool) → Option Bool → Dec)
      (fs gs : Bool → Finset (Option Bool) → Option Bool → Dec) (h : History Bool (Option Bool)),
      Matching σ f fs gs ∧ ¬ EpsNeutral σ fs ∧ WellFormed h ∧
      (∀ t l, Event.certify t l ∈ h → σ.ValidPayload t l) ∧ TCSLL σ fs gs h ∧ ¬ Correct f h :=
  ⟨σ, f, fs, gs, hist, matching, not_epsNeutral, wellFormed, validPayload, tcsll, not_correct⟩

end Podc.ReconfigurableCommit
