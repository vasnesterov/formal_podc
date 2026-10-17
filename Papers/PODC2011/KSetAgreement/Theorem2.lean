import Papers.PODC2011.KSetAgreement.Restrict

/-!
# Theorem 1 in the asynchronous model, Theorem 2 and Corollary 5

`theorem1_async` is the paper's Theorem 1 (reduction of `k`-set agreement to consensus in a
subsystem) instantiated for the asynchronous crash model, with the hypotheses in the concrete
form in which the paper verifies them in Section V:

* `k - 1` pairwise disjoint nonempty groups `Dg i` (the paper's `D_i`) whose solo runs (everybody
  else never takes a step, the group is correct) are admissible — this gives `(dec-D)` and `(B)`;
* a set `Dbar` (the paper's `D̄`) with `|Dbar| ≥ 2`, disjoint from all `Dg i`, whose runs with
  everybody outside `Dbar` initially dead and at most one crash inside `Dbar` are admissible —
  this is `(D)` (and `(A)`);
* `(C)` is CSLib's FLP theorem (`Cslib.FLP.Consensus.one_not_exists`): no consensus algorithm for
  `≥ 2` processes tolerating one crash.

The proof builds, from a `k`-set agreement algorithm `A`, the CSLib binary consensus algorithm
`(A.restrict Dbar).alg (fun _ b => c b) δ` (inputs `c false`, `c true` for the bits, decisions
decoded by `δ`), and proves that it solves consensus with one crash: agreement by merging an
execution of `Dbar` with the solo runs of the `Dg i` (which decide `k - 1` further distinct values;
this is the paper's Fact 1), validity and termination by lifting executions of the restricted
algorithm to executions of `A` in which the processes outside `Dbar` are initially dead. In
validity we use that the initially dead processes may be given the inputs of `Dbar`, the step
missing from the paper's generic proof (see `Abstract.lean`).
-/

namespace KSetAgreement

open Cslib Cslib.FLP

variable {P M S V : Type*} [DecidableEq P] [DecidableEq M]

variable (A : KAlgorithm P M S V) (D : Finset P)

/-- Lifting a finite execution of the restricted algorithm. -/
theorem lift_mTr (ιB : {p // p ∈ D} → Bool → V) (δB : V → Bool) (x : P → V)
    (inpB : {p // p ∈ D} → Bool) (hx : ∀ p : {p // p ∈ D}, ιB p (inpB p) = x p.1)
    {t t' : State {p // p ∈ D} M (Loc M S V)} {s : State P M (Loc M S V)}
    {xl : List (Action {p // p ∈ D} M)}
    (hg : GoodState inpB δB t) (hrel : Rel D t s)
    (h : ((A.restrict D).alg ιB δB).lts.MTr t xl t') :
    ∃ s', (A.algX x).lts.MTr s (xl.map (Option.map liftMsg)) s' ∧ Rel D t' s' := by
  induction h generalizing s with
  | refl => exact ⟨s, LTS.MTr.refl, hrel⟩
  | @stepL t₁ a t₂ xl t₃ htr _ ih =>
    have hg₂ := goodState_tr _ _ _ _ hg htr
    cases a with
    | none =>
      have : t₂ = t₁ := htr
      subst this
      obtain ⟨s', hs', hrel'⟩ := ih hg₂ hrel
      exact ⟨s', LTS.MTr.stepL (show (A.algX x).lts.Tr s none s from rfl) hs', hrel'⟩
    | some m =>
      obtain ⟨htrA, hrelA⟩ := rel_step A D ιB δB x inpB hx hg hrel htr
      obtain ⟨s', hs', hrel'⟩ := ih hg₂ hrelA
      exact ⟨s', LTS.MTr.stepL htrA hs', hrel'⟩

/-- The lifted states of an infinite execution of the restricted algorithm. -/
def liftStates (x : P → V) (s₀ : State P M (Loc M S V))
    (xs : ωSequence (Action {p // p ∈ D} M)) : ℕ → State P M (Loc M S V)
  | 0 => s₀
  | i + 1 =>
    match xs i with
    | none => liftStates x s₀ xs i
    | some m => (A.algX x).recvMsg (liftMsg m) (liftStates x s₀ xs i)

/-- Lifting an infinite execution of the restricted algorithm. -/
theorem lift_omega (ιB : {p // p ∈ D} → Bool → V) (δB : V → Bool) (x : P → V)
    (inpB : {p // p ∈ D} → Bool) (hx : ∀ p : {p // p ∈ D}, ιB p (inpB p) = x p.1)
    {ss : ωSequence (State {p // p ∈ D} M (Loc M S V))} {xs : ωSequence (Action {p // p ∈ D} M)}
    (hex : ((A.restrict D).alg ιB δB).lts.OmegaExecution ss xs) (hg : GoodState inpB δB (ss 0))
    {s₀ : State P M (Loc M S V)} (hrel : Rel D (ss 0) s₀) :
    (∀ i, Rel D (ss i) (liftStates A D x s₀ xs i)) ∧
      (A.algX x).lts.OmegaExecution (ωSequence.mk (liftStates A D x s₀ xs))
        (xs.map (Option.map liftMsg)) := by
  have key : ∀ i, GoodState inpB δB (ss i) ∧ Rel D (ss i) (liftStates A D x s₀ xs i) ∧
      (A.algX x).lts.Tr (liftStates A D x s₀ xs i) ((xs i).map liftMsg)
        (liftStates A D x s₀ xs (i + 1)) := by
    intro i
    induction i with
    | zero =>
      refine ⟨hg, hrel, ?_⟩
      have htr := hex 0
      rcases hxs : xs 0 with _ | m
      · simp only [liftStates, hxs, Option.map_none]; rfl
      · rw [hxs] at htr
        simp only [liftStates, hxs, Option.map_some]
        exact (rel_step A D ιB δB x inpB hx hg hrel htr).1
    | succ i ih =>
      obtain ⟨hgi, hreli, -⟩ := ih
      have htr := hex i
      have hg' : GoodState inpB δB (ss (i + 1)) := goodState_tr _ _ _ _ hgi htr
      have hrel' : Rel D (ss (i + 1)) (liftStates A D x s₀ xs (i + 1)) := by
        rcases hxs : xs i with _ | m
        · rw [hxs] at htr
          have : ss (i + 1) = ss i := htr
          simp only [liftStates, hxs, this]
          exact hreli
        · rw [hxs] at htr
          simp only [liftStates, hxs]
          exact (rel_step A D ιB δB x inpB hx hgi hreli htr).2
      refine ⟨hg', hrel', ?_⟩
      have htr' := hex (i + 1)
      rcases hxs : xs (i + 1) with _ | m
      · simp only [liftStates, hxs, Option.map_none]
        show liftStates A D x s₀ xs (i + 1) = liftStates A D x s₀ xs (i + 1)
        rfl
      · rw [hxs] at htr'
        simp only [liftStates, hxs, Option.map_some]
        exact (rel_step A D ιB δB x inpB hx hg' hrel' htr').1
  exact ⟨fun i => (key i).2.1, fun i => (key i).2.2⟩

/-! ### Transfer of fairness and crashes -/

section Transfer

variable {ss : ωSequence (State {p // p ∈ D} M (Loc M S V))}
  {xs : ωSequence (Action {p // p ∈ D} M)} {sA : ωSequence (State P M (Loc M S V))}

omit [DecidableEq M] in
theorem procFair_lift (hrel : ∀ i, Rel D (ss i) (sA i)) {p : {p // p ∈ D}}
    (h : ProcFair p ss xs) : ProcFair p.1 sA (xs.map (Option.map liftMsg)) := by
  intro m' hm' i hi
  have : m' ∈ (sA i).msgs.filter (fun m => m.dest ∈ D) :=
    Multiset.mem_filter.2 ⟨hi, hm' ▸ p.2⟩
  rw [(hrel i).2, Multiset.mem_map] at this
  obtain ⟨m, hm, rfl⟩ := this
  have hd : m.dest = p := Subtype.ext hm'
  obtain ⟨j, hij, hj⟩ := h m hd i hm
  exact ⟨j, hij, by simp [ωSequence.get_map, hj]⟩

omit [DecidableEq M] in
theorem procFaulty_lift (hrel : ∀ i, Rel D (ss i) (sA i)) {p : {p // p ∈ D}}
    (h : ProcFaulty p ss xs) : ProcFaulty p.1 sA (xs.map (Option.map liftMsg)) := by
  obtain ⟨i, ⟨m, hm, hmd⟩, hnot⟩ := h
  refine ⟨i, ⟨liftMsg m, ?_, by simp [liftMsg, hmd]⟩, ?_⟩
  · have : liftMsg m ∈ (sA i).msgs.filter (fun m => m.dest ∈ D) := by
      rw [(hrel i).2]; exact Multiset.mem_map_of_mem _ hm
    exact Multiset.mem_of_mem_filter this
  · intro j hij m' hj
    rw [ωSequence.get_map] at hj
    rcases hxs : xs j with _ | m₀
    · simp [hxs] at hj
    · simp only [hxs, Option.map_some, Option.some.injEq] at hj
      subst hj
      intro hd
      exact hnot j hij m₀ hxs (Subtype.ext hd)

omit [DecidableEq M] in
theorem procFaulty_of_lift (hrel : ∀ i, Rel D (ss i) (sA i)) {p : {p // p ∈ D}}
    (h : ProcFaulty p.1 sA (xs.map (Option.map liftMsg))) : ProcFaulty p ss xs := by
  obtain ⟨i, ⟨m', hm', hmd⟩, hnot⟩ := h
  have : m' ∈ (sA i).msgs.filter (fun m => m.dest ∈ D) :=
    Multiset.mem_filter.2 ⟨hm', hmd ▸ p.2⟩
  rw [(hrel i).2, Multiset.mem_map] at this
  obtain ⟨m, hm, rfl⟩ := this
  refine ⟨i, ⟨m, hm, Subtype.ext hmd⟩, ?_⟩
  intro j hij m₀ hj hd
  apply hnot j hij (liftMsg m₀) (by simp [ωSequence.get_map, hj])
  simp [liftMsg, hd]

end Transfer

/-! ### Theorem 1 for the asynchronous crash model -/

/-- **Theorem 1** of [BRS11] for asynchronous message passing (the form used in Section V).
Let `A` be an algorithm, `R` the admissible runs, and suppose
* (`(dec-D)`, `(B)`) there are `k - 1 = j` pairwise disjoint nonempty groups `Dg i` (the paper's
  `D₁, …, D_{k-1}`) whose solo runs (everybody outside `Dg i` never takes a step, `Dg i` is
  correct) are admissible;
* (`(A)`, `(D)`) for a set `Dbar` (the paper's `D̄`) disjoint from them with `|Dbar| ≥ 2`, every
  run in which only `Dbar` takes steps and all of `Dbar` except at most one process `c` is correct
  is admissible;
* there are `k + 1` distinct values.
Then `A` does not solve `k`-set agreement. Condition `(C)` (consensus is impossible in `⟨D̄⟩` with
one crash) is CSLib's formalization of FLP, `Cslib.FLP.Consensus.one_not_exists`. (The paper takes
`D̄ = Π \ D`; here processes outside all groups are allowed and are simply never scheduled.) -/
theorem theorem1_async [Fintype P] (A : KAlgorithm P M S V) (R : RunPred P M (Loc M S V))
    (j : ℕ) (Dg : Fin j → Finset P) (hne : ∀ i, (Dg i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (Dg i) (Dg i'))
    (Dbar : Finset P) (hDdisj : ∀ i, Disjoint (Dg i) Dbar) (hD : 2 ≤ Dbar.card)
    (W : Fin (j + 2) → V) (hW : Function.Injective W)
    (hsolo : ∀ i x inp ss xs, IsRun (A.algX x) inp ss xs →
      (∀ t, DestIn (↑(Dg i) : Set P) (xs t)) → (∀ p ∈ Dg i, ProcFair p ss xs) →
      R (A.algX x) inp ss xs)
    (hsub : ∀ x inp ss xs, IsRun (A.algX x) inp ss xs → (∀ t, DestIn (↑Dbar : Set P) (xs t)) →
      (∃ c, (ProcFaulty c ss xs ∨ ProcFair c ss xs) ∧ ∀ p ∈ Dbar, p ≠ c → ProcFair p ss xs) →
      R (A.algX x) inp ss xs) :
    ¬ SolvesKSA A (j + 1) R := by
  rintro ⟨hS, hT⟩
  classical
  -- the values: `c false`, `c true` for the binary inputs of `Dbar`, `w i` for the group `Dg i`
  let c : Bool → V := fun b => W (if b then 1 else 0)
  let w : Fin j → V := fun i => W i.succ.succ
  let δB : V → Bool := fun v => decide (v = c true)
  have hc10 : c true ≠ c false := by
    simp only [c, ↓reduceIte, Bool.false_eq_true, ne_eq]
    exact fun h => absurd (hW h) (by simp)
  have hδc : ∀ b, δB (c b) = b := by
    intro b; cases b
    · simp only [δB, decide_eq_false_iff_not]; exact hc10.symm
    · simp [δB]
  have hcw : ∀ b i, c b ≠ w i := by
    intro b i h
    have := hW h
    cases b <;> simp at this <;>
      exact absurd this (by simp [Fin.ext_iff])
  have hcinj : Function.Injective c := by
    intro b b' h; rw [← hδc b, ← hδc b', h]
  -- the restricted binary consensus algorithm on `Dbar`
  let B := (A.restrict Dbar).alg (fun _ b => c b) δB
  have hcardD : 2 ≤ Fintype.card {p // p ∈ Dbar} := by simpa using hD
  obtain ⟨p₀, hp₀⟩ : Dbar.Nonempty := Finset.card_pos.1 (by omega)
  let inpA : ({p // p ∈ Dbar} → Bool) → P → Bool := fun inpB p =>
    if h : p ∈ Dbar then inpB ⟨p, h⟩ else false
  let x₁ : ({p // p ∈ Dbar} → Bool) → P → V := fun inpB p =>
    if h : p ∈ Dbar then c (inpB ⟨p, h⟩) else c (inpB ⟨p₀, hp₀⟩)
  have hx : ∀ inpB (p : {p // p ∈ Dbar}), (fun _ b => c b) p (inpB p) = x₁ inpB p.1 := by
    intro inpB p; simp [x₁, p.2]
  have hinp : ∀ inpB (p : {p // p ∈ Dbar}), inpA inpB p.1 = inpB p := by
    intro inpB p; simp [inpA, p.2]
  have hrel₀ : ∀ inpB, Rel Dbar (B.start inpB) ((A.algX (x₁ inpB)).start (inpA inpB)) :=
    fun inpB => rel_start A Dbar _ δB (x₁ inpB) inpB (inpA inpB) (hinp inpB)
  refine Consensus.one_not_exists (M := M) (S := Loc M S V) hcardD ⟨B, ?_, ?_⟩
  · -- safety: agreement and validity
    intro inpB t ⟨xl, hxl⟩
    have hgt : GoodState inpB δB t := goodState_of_reachable _ _ _ _ ⟨xl, hxl⟩
    obtain ⟨s₁, hs₁, hrel₁⟩ := lift_mTr A Dbar _ δB (x₁ inpB) inpB (hx inpB)
      (goodState_start _ _ _ _) (hrel₀ inpB) hxl
    have hval₁ := (hS (x₁ inpB) (inpA inpB) s₁ ⟨_, hs₁⟩).2
    have hdecB : ∀ p v, dec t p = some v → ∃ b, v = c b ∧ ∃ q, inpB q = b := by
      intro p v hv
      have : dec s₁ p.1 = some v := by rw [dec, hrel₁.1 p]; exact hv
      obtain ⟨q, hq⟩ := hval₁ p.1 v this
      by_cases h : q ∈ Dbar
      · exact ⟨inpB ⟨q, h⟩, by simp [x₁, h] at hq; exact hq.symm, ⟨q, h⟩, rfl⟩
      · exact ⟨inpB ⟨p₀, hp₀⟩, by simp [x₁, h] at hq; exact hq.symm, ⟨p₀, hp₀⟩, rfl⟩
    have hdecided : ∀ b, t.Decided b → ∃ p v, dec t p = some v ∧ δB v = b := by
      rintro b ⟨p, hp⟩
      have h1 := hgt.1 p
      rw [hp] at h1
      obtain ⟨v, hv, hvb⟩ := Option.map_eq_some_iff.1 h1.symm
      exact ⟨p, v, hv, hvb⟩
    refine ⟨?_, ?_⟩
    · rintro b b' ⟨hb, hb'⟩
      obtain ⟨p, v, hv, rfl⟩ := hdecided b hb
      obtain ⟨p', v', hv', rfl⟩ := hdecided b' hb'
      by_contra hne'
      have hvv : v ≠ v' := fun h => hne' (by rw [h])
      -- solo prefixes of the groups `Dg i`
      have hsoloP := fun i => solo_prefix A R hT (fun _ => w i) (inpA inpB) (Dg i)
        (hsolo i _ _)
      choose xlI sI hxlI hdestI hdecI using hsoloP
      -- merge everything
      let G : Option (Fin j) → Set P := fun o => Option.elim o (↑Dbar) (fun i => ↑(Dg i))
      let y : Option (Fin j) → P → V := fun o => Option.elim o (x₁ inpB) (fun i _ => w i)
      let x : P → V := fun p =>
        if p ∈ Dbar then x₁ inpB p else if h : ∃ i, p ∈ Dg i then w h.choose else c false
      have hy : ∀ o, ∀ p ∈ G o, y o p = x p := by
        intro o p hp
        cases o with
        | none => simp only [G, Option.elim, Finset.mem_coe] at hp; simp [y, x, hp]
        | some i =>
          simp only [G, Option.elim, Finset.mem_coe] at hp
          have hpD : p ∉ Dbar := Finset.disjoint_left.1 (hDdisj i) hp
          have h : ∃ i, p ∈ Dg i := ⟨i, hp⟩
          have hi : h.choose = i := by
            by_contra hne''
            exact Finset.disjoint_left.1 (hdisj _ _ hne'') h.choose_spec hp
          simp [y, x, hpD, h, hi]
      obtain ⟨zl, tm, htm, -, hagree⟩ := merge A x (inpA inpB) G y hy
        (fun o => Option.elim o (xl.map (Option.map liftMsg)) xlI)
        (fun o => Option.elim o s₁ sI)
        (fun o => by cases o with
          | none => exact hs₁
          | some i => exact hxlI i)
        (fun o a ha => by
          cases o with
          | none =>
            simp only [Option.elim, List.mem_map] at ha
            obtain ⟨a, -, rfl⟩ := ha
            cases a with
            | none => trivial
            | some m => exact m.dest.2
          | some i => exact hdestI i a ha)
        (Finset.univ : Finset (Option (Fin j))).toList
        (by
          refine List.Pairwise.imp_of_mem ?_ (Finset.nodup_toList _)
          intro o o' _ _ hoo
          cases o with
          | none =>
            cases o' with
            | none => exact absurd rfl hoo
            | some i => exact Finset.disjoint_coe.2 (hDdisj i).symm
          | some i =>
            cases o' with
            | none => exact Finset.disjoint_coe.2 (hDdisj i)
            | some i' => exact Finset.disjoint_coe.2 (hdisj i i' (fun h => hoo (by rw [h]))))
      have hmemD : ∀ q : {p // p ∈ Dbar}, dec tm q.1 = dec t q := by
        intro q
        rw [dec, hagree none (Finset.mem_toList.2 (Finset.mem_univ _)) q.1 q.2]
        show KAlgorithm.decOf (s₁.proc q.1).state = KAlgorithm.decOf (t.proc q).state
        rw [hrel₁.1 q]
      obtain ⟨b₁, rfl, -⟩ := hdecB p v hv
      obtain ⟨b₂, rfl, -⟩ := hdecB p' v' hv'
      let W' : Fin (j + 2) → V := Fin.cons (c b₁) (Fin.cons (c b₂) w)
      have hW' : Function.Injective W' := by
        refine Fin.cons_injective_iff.2 ⟨?_, Fin.cons_injective_iff.2 ⟨?_, ?_⟩⟩
        · rintro ⟨i, hi⟩
          refine Fin.cases (fun h => hvv (by simpa using h.symm)) (fun i h => ?_) i hi
          exact hcw b₁ i (by simpa using h.symm)
        · rintro ⟨i, hi⟩; exact hcw b₂ i hi.symm
        · intro i i' h; simpa [w, Fin.succ_inj] using hW h
      have hmem : ∀ i, W' i ∈ decVals tm := by
        intro i
        refine Fin.cases ⟨p.1, by rw [hmemD]; exact hv⟩ (fun i => ?_) i
        refine Fin.cases ⟨p'.1, by rw [hmemD]; exact hv'⟩ (fun i => ?_) i
        obtain ⟨q, hq⟩ := hne i
        obtain ⟨u, hu⟩ := hdecI i q hq
        have hu' : u = w i := dec_eq_of_const hS (hxlI i) hu
        have htq : dec tm q = dec (sI i) q := by
          rw [dec, hagree (some i) (Finset.mem_toList.2 (Finset.mem_univ _)) q hq]; rfl
        refine ⟨q, ?_⟩
        rw [htq, hu, hu']
        rfl
      have h1 := le_ncard_decVals tm W' hW' hmem
      have h2 := (hS x (inpA inpB) tm ⟨zl, htm⟩).1
      omega
    · intro b hb
      obtain ⟨p, v, hv, rfl⟩ := hdecided b hb
      obtain ⟨b', rfl, q, hq⟩ := hdecB p v hv
      exact ⟨q, by rw [hq, hδc]⟩
  · -- termination with at most one crash
    intro inpB ss xs ⟨h0, hex, hfair, hcount⟩ p
    have hg0 : GoodState inpB δB (ss 0) := by rw [h0]; exact goodState_start _ _ _ _
    obtain ⟨hrelAll, hexA⟩ := lift_omega A Dbar _ δB (x₁ inpB) inpB (hx inpB) hex hg0
      (by rw [h0]; exact hrel₀ inpB)
    set sA : ωSequence (State P M (Loc M S V)) :=
      ωSequence.mk (liftStates A Dbar (x₁ inpB) ((A.algX (x₁ inpB)).start (inpA inpB)) xs)
    set xsA := xs.map (Option.map liftMsg)
    have hrel : ∀ i, Rel Dbar (ss i) (sA i) := hrelAll
    have hrun : IsRun (A.algX (x₁ inpB)) (inpA inpB) sA xsA := ⟨rfl, hexA⟩
    have hdest : ∀ t, DestIn (↑Dbar : Set P) (xsA t) := by
      intro t
      rw [ωSequence.get_map]
      rcases xs t with _ | m
      · trivial
      · exact m.dest.2
    have hsing : ∀ q q', ProcFaulty q ss xs → ProcFaulty q' ss xs → q = q' := by
      intro q q' hq hq'
      have h1 : ∀ {a b : {p // p ∈ Dbar}}, a ∈ {p | ProcFaulty p ss xs} →
          b ∈ {p | ProcFaulty p ss xs} → a = b :=
        (Set.ncard_le_one_iff (Set.toFinite _)).1 hcount
      exact h1 hq hq'
    have hfairOther : ∀ q q' : {p // p ∈ Dbar}, ProcFaulty q ss xs → q' ≠ q → ProcFair q' ss xs := by
      intro q q' hq hne'
      rcases hfair q' with h | h
      · exact absurd (hsing _ _ h hq) hne'
      · exact h
    have hR : R (A.algX (x₁ inpB)) (inpA inpB) sA xsA := by
      refine hsub _ _ _ _ hrun hdest ?_
      by_cases hf : ∃ q, ProcFaulty q ss xs
      · obtain ⟨q, hq⟩ := hf
        refine ⟨q.1, Or.inl (procFaulty_lift Dbar hrel hq), fun p' hp' hne' => ?_⟩
        exact procFair_lift Dbar hrel
          (hfairOther q ⟨p', hp'⟩ hq (fun h => hne' (by rw [← h])))
      · push Not at hf
        have hall : ∀ q, ProcFair q ss xs := fun q => (hfair q).resolve_left (hf q)
        exact ⟨p₀, Or.inr (procFair_lift Dbar hrel (hall ⟨p₀, hp₀⟩)),
          fun p' hp' _ => procFair_lift Dbar hrel (hall ⟨p', hp'⟩)⟩
    rcases hT (x₁ inpB) (inpA inpB) sA xsA hR p.1 with h | ⟨i, v, hv⟩
    · exact Or.inl (procFaulty_of_lift Dbar hrel h)
    · refine Or.inr ⟨i, δB v, ?_⟩
      have hd : dec (ss i) p = some v := by rw [dec, ← (hrel i).1 p]; exact hv
      have hgi : GoodState inpB δB (ss i) := by
        have := LTS.OmegaExecution.extract_mTr hex (Nat.zero_le i)
        exact goodState_mTr _ _ _ _ hg0 this
      show ((ss i).proc p).out = some (δB v)
      rw [hgi.1 p, hd]
      rfl

/-! ### Theorem 2 and Corollary 5 -/

/-- Runs with Theorem 2's failure pattern are runs with at most `f` crashes. -/
theorem oneCrash_crash [Fintype P] {L : Type*} {f : ℕ} {a : Algorithm P M L} {inp : P → Bool}
    {ss : ωSequence (State P M L)} {xs : ωSequence (Action P M)}
    (h : OneCrash f a inp ss xs) : Crash f a inp ss xs := by
  classical
  obtain ⟨hrun, dead, hcard, hdead, c, hc, hfair⟩ := h
  have hfr : ∀ p, ProcFaulty p ss xs ∨ ProcFair p ss xs := by
    intro p
    by_cases hp : p ∈ dead
    · exact Or.inl (neverSteps_procFaulty hrun (hdead p hp))
    · by_cases hpc : p = c
      · subst hpc; exact hc
      · exact Or.inr (hfair p hp hpc)
  refine ⟨hrun.1, hrun.2, hfr, ?_⟩
  have hsub : {p | ProcFaulty p ss xs} ⊆ ↑(insert c dead) := by
    intro p hp
    by_contra hp'
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at hp'
    exact not_procFaulty_and_procFair p ss xs ⟨hp, hfair p hp'.2 hp'.1⟩
  calc numProcFaulty ss xs ≤ (↑(insert c dead) : Set P).ncard := Set.ncard_le_ncard hsub
    _ = (insert c dead).card := Set.ncard_coe_finset _
    _ ≤ dead.card + 1 := Finset.card_insert_le _ _
    _ ≤ f := hcard

/-- **Theorem 2** of [BRS11], for asynchronous processes (the setting of Corollary 5) but with
Theorem 2's restricted failure pattern: there is no algorithm solving `k`-set agreement among
`n = |P|` processes if `k ≤ (n - 1) / (n - f)`, i.e. `k * (n - f) ≤ n - 1`, even if only `f - 1`
processes can be initially dead and only one further process can crash during the execution.
(We assume `f < n`, as the paper implicitly does, and `k + 1` distinct input values.) -/
theorem theorem2 [Fintype P] (A : KAlgorithm P M S V) {n f k : ℕ} (hn : Fintype.card P = n)
    (hf : f < n) (hk1 : 1 ≤ k) (hk : k * (n - f) ≤ n - 1)
    (W : Fin (k + 1) → V) (hW : Function.Injective W) :
    ¬ SolvesKSA A k (OneCrash f) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set ℓ := n - f with hℓ
  have hℓ1 : 1 ≤ ℓ := by omega
  have hjℓ : j * ℓ + ℓ ≤ n - 1 := by
    have : (j + 1) * ℓ = j * ℓ + ℓ := by ring
    omega
  obtain ⟨Dg, hcard, hdisj⟩ := exists_disjoint_groups j ℓ (by rw [hn]; omega)
  set U := Finset.univ.biUnion Dg
  have hU : U.card ≤ j * ℓ := by
    refine le_trans Finset.card_biUnion_le ?_
    simp [hcard]
  set Dbar := Uᶜ
  have hD : 2 ≤ Dbar.card := by
    rw [Finset.card_compl, hn]; omega
  have hDdisj : ∀ i, Disjoint (Dg i) Dbar := by
    intro i
    refine Finset.disjoint_left.2 fun p hp hpD => ?_
    exact (Finset.mem_compl.1 hpD) (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hp⟩)
  refine theorem1_async A (OneCrash f) j Dg (fun i => ?_) hdisj Dbar hDdisj hD W hW ?_ ?_
  · rw [← Finset.card_pos, hcard]; omega
  · -- solo runs of `Dg i`: `f - 1` processes initially dead, one more crashed at the start
    intro i x inp ss xs hrun hdest hfair
    have hc : ((Dg i)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, hcard, hn]; omega
    obtain ⟨c, hc⟩ := hc
    have hnever : ∀ p ∈ (Dg i)ᶜ, NeverSteps p xs := by
      intro p hp j' m hj hmp
      have := hdest j'
      rw [hj] at this
      exact (Finset.mem_compl.1 hp) (hmp ▸ this)
    refine ⟨hrun, ((Dg i)ᶜ).erase c, ?_, fun p hp => hnever p (Finset.mem_of_mem_erase hp),
      c, Or.inl (neverSteps_procFaulty hrun (hnever c hc)), fun p hp hpc => hfair p ?_⟩
    · rw [Finset.card_erase_of_mem hc, Finset.card_compl, hcard, hn]; omega
    · by_contra hpi
      exact hp (Finset.mem_erase.2 ⟨hpc, Finset.mem_compl.2 hpi⟩)
  · -- runs of `Dbar`: everybody outside `Dbar` (at most `f - 1` processes) is initially dead
    intro x inp ss xs hrun hdest ⟨c, hc, hfair⟩
    refine ⟨hrun, Dbarᶜ, ?_, ?_, c, hc, fun p hp hpc => hfair p (by simpa using hp) hpc⟩
    · rw [compl_compl]; omega
    · intro p hp j' m hj hmp
      have := hdest j'
      rw [hj] at this
      exact (Finset.mem_compl.1 hp) (hmp ▸ this)

/-- **Corollary 5** of [BRS11]: `k`-set agreement is impossible in the asynchronous model with up
to `f < n` crash failures if `k * (n - f) ≤ n - 1`. -/
theorem corollary5 [Fintype P] (A : KAlgorithm P M S V) {n f k : ℕ} (hn : Fintype.card P = n)
    (hf : f < n) (hk1 : 1 ≤ k) (hk : k * (n - f) ≤ n - 1)
    (W : Fin (k + 1) → V) (hW : Function.Injective W) :
    ¬ SolvesKSA A k (Crash f) := by
  rintro ⟨hS, hT⟩
  exact theorem2 A hn hf hk1 hk W hW
    ⟨hS, fun x inp ss xs h => hT x inp ss xs (oneCrash_crash h)⟩

end KSetAgreement
