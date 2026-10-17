import Papers.PODC2020.BezoutElection.LockStep
import Papers.PODC2020.BezoutElection.Exec
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The lock-step execution of all groups

From the symmetric set-up (`Setup`), the *lock-step execution* lets every group invoke `elect()`
and then repeats rounds in which every pending group takes one group round (each member takes
one step). Either at some round all processes have returned — then all members of a group
returned the same response (`exists_symmetric_outcome`) — or the lock-step execution is a fair,
one-shot infinite execution in which every process invoked and some process never returns, which
contradicts termination.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

variable {R : Type} [Inhabited R] {Id V S : Type} {m : ℕ} [MulAction (Equiv.Perm Id) V]
  [MulAction (Equiv.Perm Id) S] {A : SymAlg (elecObj R) Id m V S} {P : Type} [DecidableEq P]
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}
  {k g : ℕ} {e : ℕ → ℕ → P} {σ : Equiv.Perm Id} {sh : Equiv.Perm (Fin m)} {a : ℕ → Id}

/-- Invariant of the lock-step execution after the invocations: execution `α` reaches the
symmetric configuration `C`; `o q` is the response of group `q` (`none` while pending). -/
structure Good (k g : ℕ) (e : ℕ → ℕ → P) (σ : Equiv.Perm Id) (sh : Equiv.Perm (Fin m))
    (ids : P → Id) (π : P → Equiv.Perm (Fin m)) (A : SymAlg (elecObj R) Id m V S)
    (α : List (Label P (elecObj R))) (C : A.Cfg)
    (s : ℕ → S) (b : ℕ → Option Unit) (o : ℕ → Option R) : Prop where
  run : (A.impl ids π).run α = some C
  sym : SymCfg k g e σ sh C s b
  oneShot : OneShot α
  out : ∀ q < k, ∀ i < g, outputs α (e q i) = o q
  pend : ∀ q < k, b q = none ↔ o q ≠ none

section

variable (hS : Setup k g e σ sh a ids π) (hA : A.Symmetric)
include hS hA

lemma opsOf_map_tau (q j : ℕ) (p : P) :
    opsOf ((List.range j).map (fun i => (Label.tau (e q i) : Label P (elecObj R)))) p = [] := by
  simp [opsOf, List.filterMap_map]

lemma respsOf_map_tau (q j : ℕ) (p : P) :
    respsOf ((List.range j).map (fun i => (Label.tau (e q i) : Label P (elecObj R)))) p = [] := by
  simp [respsOf, List.filterMap_map]

lemma opsOf_map_ret (q j : ℕ) (r : R) (p : P) :
    opsOf ((List.range j).map (fun i => (Label.ret (e q i) r : Label P (elecObj R)))) p = [] := by
  simp [opsOf, List.filterMap_map]

/-- One group round of group `q` (if pending) preserves `Good`. -/
lemma good_group_round (hg : 0 < g) {α : List (Label P (elecObj R))} {C : A.Cfg} {s : ℕ → S}
    {b : ℕ → Option Unit} {o : ℕ → Option R} (h : Good k g e σ sh ids π A α C s b o)
    {q : ℕ} (hq : q < k) (hb : b q = some ()) :
    ∃ β C' s' b' o', Good k g e σ sh ids π A (α ++ β) C' s' b' o' ∧
      (∀ i < g, ∃ ℓ ∈ β, ℓ.proc = e q i ∧ ℓ.IsStep) ∧ β ≠ [] ∧
      (∀ q' < k, q' ≠ q → s' q' = s q' ∧ b' q' = b q') ∧
      (∀ q' < k, b' q' = some () → b q' = some ()) := by
  have ho : o q = none := by
    by_contra hne; have := (h.pend q hq).2 hne; simp [hb] at this
  have hne : (List.range g).map (fun j => (Label.tau (e q j) : Label P (elecObj R))) ≠ [] := by
    simp; omega
  have hsteps : ∀ i < g, ∃ ℓ ∈ (List.range g).map (fun j => (Label.tau (e q j) :
      Label P (elecObj R))), ℓ.proc = e q i ∧ ℓ.IsStep :=
    fun i hi => ⟨.tau (e q i), List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl, trivial⟩
  cases hact : A.act (s q) with
  | rmw x f κ =>
    obtain ⟨D, hD, hsym, hpend⟩ := round_rmw hS hA h.sym hq hb hg hact
    refine ⟨_, D, _, b, o, ⟨by rw [Impl.run_append_of_eq _ h.run]; exact hD, hsym,
      fun p => by have := h.oneShot p; simpa [opsOf_map_tau hS hA] using this,
      fun q' hq' i hi => by rw [outputs_append, h.out q' hq' i hi]; simp [outputs,
        respsOf_map_tau hS hA], h.pend⟩, hsteps, hne,
      fun q' _ hqq => ⟨Function.update_of_ne hqq _ _, rfl⟩, fun _ _ h => h⟩
  | snap κ =>
    obtain ⟨D, hD, hsym, hpend⟩ := round_snap hS hA h.sym hq hb hact
    refine ⟨_, D, _, b, o, ⟨by rw [Impl.run_append_of_eq _ h.run]; exact hD, hsym,
      fun p => by have := h.oneShot p; simpa [opsOf_map_tau hS hA] using this,
      fun q' hq' i hi => by rw [outputs_append, h.out q' hq' i hi]; simp [outputs,
        respsOf_map_tau hS hA], h.pend⟩, hsteps, hne,
      fun q' _ hqq => ⟨Function.update_of_ne hqq _ _, rfl⟩, fun _ _ h => h⟩
  | ret r s'' =>
    obtain ⟨D, hD, hsym, hpend⟩ := round_ret hS hA h.sym hq hb hact
    refine ⟨_, D, _, _, Function.update o q (some r),
      ⟨by rw [Impl.run_append_of_eq _ h.run]; exact hD, hsym,
      fun p => by have := h.oneShot p; simpa [opsOf_map_ret hS hA] using this,
      fun q' hq' i hi => ?_, fun q' hq' => ?_⟩,
      fun i hi => ⟨.ret (e q i) r, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, rfl, trivial⟩,
      by simp; omega,
      fun q' _ hqq => ⟨Function.update_of_ne hqq _ _, Function.update_of_ne hqq _ _⟩,
      fun q' _ h' => ?_⟩
    · rw [outputs_append, h.out q' hq' i hi]
      by_cases hqq : q' = q
      · subst hqq
        rw [ho, Function.update_self, Option.none_or]
        set β := (List.range g).map (fun j => (Label.ret (e q' j) r : Label P (elecObj R)))
        have hin : Label.ret (e q' i) r ∈ β := List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
        have hall : ∀ x ∈ respsOf β (e q' i), x = r := by
          intro x hx
          simp only [respsOf, List.mem_filterMap, β, List.mem_map] at hx
          obtain ⟨_, ⟨j, -, rfl⟩, hx⟩ := hx
          simp only [Label.retOf_ret] at hx
          split_ifs at hx; simpa using hx.symm
        have hne' := outputs_ne_none_of_mem hin
        unfold outputs at hne' ⊢
        cases hrs : respsOf β (e q' i) with
        | nil => simp [hrs] at hne'
        | cons x xs => simp [hall x (by simp [hrs])]
      · rw [Function.update_of_ne hqq]
        have : outputs ((List.range g).map (fun j => (Label.ret (e q j) r :
            Label P (elecObj R)))) (e q' i) = none := by
          apply outputs_eq_none_of_proc_ne
          intro ℓ hℓ
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hℓ
          exact hS.ne_of_group_ne hA hq hq' (List.mem_range.1 hj) hi (Ne.symm hqq)
        rw [this]; cases o q' <;> rfl
    · by_cases hqq : q' = q
      · subst hqq; simp
      · rw [Function.update_of_ne hqq, Function.update_of_ne hqq]; exact h.pend q' hq'
    · by_cases hqq : q' = q
      · subst hqq; simp at h'
      · rwa [Function.update_of_ne hqq] at h'

/-- A full round: every pending group takes a group round. -/
lemma good_full_round (hg : 0 < g) {α : List (Label P (elecObj R))} {C : A.Cfg} {s : ℕ → S}
    {b : ℕ → Option Unit} {o : ℕ → Option R} (h : Good k g e σ sh ids π A α C s b o) :
    ∃ β C' s' b' o', Good k g e σ sh ids π A (α ++ β) C' s' b' o' ∧
      (∀ q < k, b q = some () → ∀ i < g, ∃ ℓ ∈ β, ℓ.proc = e q i ∧ ℓ.IsStep) ∧
      ((∃ q < k, b q = some ()) → β ≠ []) ∧
      (∀ q < k, b' q = some () → b q = some ()) := by
  suffices H : ∀ j ≤ k, ∃ β C' s' b' o', Good k g e σ sh ids π A (α ++ β) C' s' b' o' ∧
      (∀ q < k, j ≤ q → s' q = s q ∧ b' q = b q) ∧
      (∀ q < j, b q = some () → ∀ i < g, ∃ ℓ ∈ β, ℓ.proc = e q i ∧ ℓ.IsStep) ∧
      ((∃ q < j, b q = some ()) → β ≠ []) ∧
      (∀ q < k, b' q = some () → b q = some ()) by
    obtain ⟨β, C', s', b', o', h1, -, h3, h4, h5⟩ := H k le_rfl
    exact ⟨β, C', s', b', o', h1, h3, h4, h5⟩
  intro j hj
  induction j with
  | zero =>
    exact ⟨[], C, s, b, o, by simpa using h, fun _ _ _ => ⟨rfl, rfl⟩, fun _ h => absurd h (by omega),
      fun ⟨_, h, _⟩ => absurd h (by omega), fun _ _ h => h⟩
  | succ j ih =>
    obtain ⟨β, C', s', b', o', h1, h2, h3, h4, h5⟩ := ih (by omega)
    obtain ⟨hsj, hbj⟩ := h2 j (by omega) le_rfl
    cases hb : b j with
    | none =>
      refine ⟨β, C', s', b', o', h1, fun q hq hjq => h2 q hq (by omega), fun q hq hbq => ?_,
        fun ⟨q, hq, hbq⟩ => ?_, h5⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
        · exact h3 q hq hbq
        · rw [hb] at hbq; exact absurd hbq (by simp)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
        · exact h4 ⟨q, hq, hbq⟩
        · rw [hb] at hbq; exact absurd hbq (by simp)
    | some u =>
      cases u
      obtain ⟨β2, C'', s'', b'', o'', g1, g2, g3, g4, g5⟩ :=
        good_group_round hS hA hg h1 (q := j) (by omega) (by rw [hbj, hb])
      refine ⟨β ++ β2, C'', s'', b'', o'', by simpa [List.append_assoc] using g1,
        fun q hq hjq => ?_, fun q hq hbq i hi => ?_, fun _ => by simp [g3],
        fun q hq hbq => h5 q hq (g5 q hq hbq)⟩
      · rw [(g4 q hq (by omega)).1, (g4 q hq (by omega)).2]; exact h2 q hq (by omega)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
        · obtain ⟨ℓ, hℓ, h'⟩ := h3 q hq hbq i hi
          exact ⟨ℓ, List.mem_append_left _ hℓ, h'⟩
        · obtain ⟨ℓ, hℓ, h'⟩ := g2 i hi
          exact ⟨ℓ, List.mem_append_right _ hℓ, h'⟩

omit hS hA in
lemma opsOf_map_inv (l : List P) (hl : l.Nodup) (p : P) :
    opsOf (l.map (fun p => (Label.inv p () : Label P (elecObj R)))) p =
      if p ∈ l then [()] else [] := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, opsOf_cons, ih hl.2, Label.invOf_inv, List.mem_cons]
    by_cases hx : x = p
    · subst hx; simp [hl.1]
    · simp [hx, Ne.symm hx]

omit hS hA in
lemma respsOf_map_inv (l : List P) (p : P) :
    respsOf (l.map (fun p => (Label.inv p () : Label P (elecObj R)))) p = [] := by
  simp [respsOf, List.filterMap_map]

omit hA in
lemma runFrom_invs (l : List P) (hl : l.Nodup) (C : A.Cfg) (hC : ∀ p ∈ l, C.pend p = none) :
    ∃ D, (A.impl ids π).runFrom C (l.map (fun p => (Label.inv p () : Label P (elecObj R)))) =
      some D ∧ D.mem = C.mem ∧
      (∀ p, D.pend p = if p ∈ l then some () else C.pend p) ∧
      (∀ p, D.loc p = if p ∈ l then A.invoke (C.loc p) () else C.loc p) := by
  induction l generalizing C with
  | nil => exact ⟨C, rfl, rfl, fun _ => by simp, fun _ => by simp⟩
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    have hx := SymAlg.impl_step_inv (o := ()) ids π (hC x List.mem_cons_self)
    set C1 : A.Cfg := ⟨Function.update C.loc x (A.invoke (C.loc x) ()),
      Function.update C.pend x (some ()), C.mem⟩ with hC1
    obtain ⟨D, hD, h1, h2, h3⟩ := ih hl.2 C1 (fun p hp => by
      have hne : p ≠ x := fun h => hl.1 (h ▸ hp)
      simp [C1, Function.update_of_ne hne, hC p (List.mem_cons_of_mem _ hp)])
    refine ⟨D, by simp only [List.map_cons, Impl.runFrom_cons, hx, Option.bind_some]; exact hD,
      h1, fun p => ?_, fun p => ?_⟩
    · rw [h2]; by_cases hp : p = x
      · subst hp; simp [hl.1, C1]
      · simp [hp, C1]
    · rw [h3]; by_cases hp : p = x
      · subst hp; simp [hl.1, C1]
      · simp [hp, C1]

/-- The invocation phase: every process invokes `elect()`. -/
lemma good_init [Fintype P] :
    ∃ α C s, Good k g e σ sh ids π A α C s (fun _ => some ()) (fun _ => none) ∧
      ∀ p, Label.inv p () ∈ α := by
  set l := (Finset.univ : Finset P).toList
  have hl : l.Nodup := Finset.nodup_toList _
  obtain ⟨D, hD, h1, h2, h3⟩ := runFrom_invs hS (A := A) l hl (A.impl ids π).initCfg
    (fun _ _ => rfl)
  have hC0 := symCfg_init hS hA (A := A)
  refine ⟨_, D, fun q => A.invoke (A.init (a q)) (), ⟨hD, ⟨fun q hq i hi => ?_,
    fun q hq i hi => by simp [h2, l], fun y => by rw [h1]; exact hC0.mem y⟩,
    fun p => by simp [opsOf_map_inv l hl, l], fun q hq i hi => ?_,
    fun q hq => by simp⟩, fun p => List.mem_map.2 ⟨p, by simp [l], rfl⟩⟩
  · have hpl : e q i ∈ l := by simp [l]
    rw [h3]; simp only [hpl, ↓reduceIte]; rw [hC0.loc q hq i hi, hA.invoke]
  · simp [outputs, respsOf_map_inv]

end

section Outcome

variable [Fintype P] (hS : Setup k g e σ sh a ids π) (hA : A.Symmetric)
include hS hA

/-- **The lock-step execution.** If the algorithm terminates, there is a finite one-shot
execution in which all processes returned and all members of each group returned the same
response. -/
theorem exists_symmetric_outcome (hg : 0 < g) (hT : Terminates (A.impl ids π)) :
    ∃ α, (A.impl ids π).Valid α ∧ OneShot α ∧ AllReturned α ∧
      ∀ q < k, ∀ i < g, outputs α (e q i) = outputs α (e q 0) := by
  classical
  let T := {x : List (Label P (elecObj R)) × A.Cfg × (ℕ → S) × (ℕ → Option Unit) ×
    (ℕ → Option R) // Good k g e σ sh ids π A x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2}
  have hstep : ∀ x : T, ∃ y : T, ∃ β, y.1.1 = x.1.1 ++ β ∧
      (∀ q < k, x.1.2.2.2.1 q = some () → ∀ i < g, ∃ ℓ ∈ β, ℓ.proc = e q i ∧ ℓ.IsStep) ∧
      ((∃ q < k, x.1.2.2.2.1 q = some ()) → β ≠ []) ∧
      (∀ q < k, y.1.2.2.2.1 q = some () → x.1.2.2.2.1 q = some ()) := by
    intro x
    obtain ⟨β, C', s', b', o', h1, h2, h3, h4⟩ := good_full_round hS hA hg x.2
    exact ⟨⟨(x.1.1 ++ β, C', s', b', o'), h1⟩, β, rfl, h2, h3, h4⟩
  choose F hF using hstep
  obtain ⟨α₀, C₀, s₀, h₀, hinv⟩ := good_init hS hA (k := k) (g := g)
  let X : ℕ → T := fun j => F^[j] ⟨(α₀, C₀, s₀, fun _ => some (), fun _ => none), h₀⟩
  have hX : ∀ j, X (j + 1) = F (X j) := fun j => Function.iterate_succ_apply' _ _ _
  by_cases hfin : ∃ j, ∀ q < k, (X j).1.2.2.2.1 q = none
  · -- all processes returned
    obtain ⟨j, hj⟩ := hfin
    have hG := (X j).2
    refine ⟨(X j).1.1, ⟨_, hG.run⟩, hG.oneShot, fun p => ?_, fun q hq i hi => ?_⟩
    · obtain ⟨q, hq, i, hi, rfl⟩ := hS.esurj p
      rw [hG.out q hq i hi]; exact (hG.pend q hq).1 (hj q hq)
    · rw [hG.out q hq i hi, hG.out q hq 0 hg]
  · exfalso
    push Not at hfin
    have hpend : ∀ j, ∃ q < k, (X j).1.2.2.2.1 q = some () := by
      intro j; obtain ⟨q, hq, h⟩ := hfin j
      exact ⟨q, hq, by cases h' : (X j).1.2.2.2.1 q with
        | none => exact absurd h' h
        | some u => cases u; rfl⟩
    set E : ℕ → List (Label P (elecObj R)) := fun j => (X j).1.1 with hE
    have hEs : ∀ j, ∃ β, E (j + 1) = E j ++ β ∧
        (∀ q < k, (X j).1.2.2.2.1 q = some () → ∀ i < g, ∃ ℓ ∈ β, ℓ.proc = e q i ∧ ℓ.IsStep) ∧
        β ≠ [] := by
      intro j
      obtain ⟨β, h1, h2, h3, -⟩ := hF (X j)
      exact ⟨β, by simp only [hE, hX]; exact h1, h2, h3 (hpend j)⟩
    have hlen : ∀ j, j ≤ (E j).length := by
      intro j
      induction j with
      | zero => omega
      | succ j ih =>
        obtain ⟨β, h1, -, h3⟩ := hEs j
        rw [h1, List.length_append]
        have := List.length_pos_iff.2 h3
        omega
    obtain ⟨ex, hlbl, hcfg⟩ := (A.impl ids π).exists_infExec_of_chain E
      (fun j => by obtain ⟨β, h1, -⟩ := hEs j; rw [h1]; exact List.prefix_append _ _)
      hlen (fun j => ⟨_, (X j).2.run⟩)
    have hpre : ∀ j t, t ≤ (E j).length → ePre ex t = (E j).take t := by
      intro j t ht
      apply List.ext_getElem
      · simp [ePre]; omega
      · intro n h1 h2
        simp only [ePre, List.getElem_map, List.getElem_range, List.getElem_take]
        exact hlbl j n (by simp [ePre] at h1; omega)
    have hcfgE : ∀ j, ex.cfg (E j).length = (X j).1.2.1 := by
      intro j
      have h := hcfg j _ le_rfl
      rw [List.take_length, (X j).2.run] at h
      exact (Option.some.inj h).symm
    -- the lock-step execution is one-shot, all processes invoke, and it is fair
    have h1s : IsOneShot ex := by
      intro t p
      rw [hpre t t (hlen t)]
      have := (X t).2.oneShot p
      change (opsOf (E t) p).length ≤ 1 at this
      rw [← List.take_append_drop t (E t), opsOf_append, List.length_append] at this
      omega
    have hall : AllInvoke ex := by
      intro p
      obtain ⟨n, hn, hn'⟩ := List.getElem_of_mem (hinv p)
      exact ⟨n, (), by rw [hlbl 0 n hn]; exact hn'⟩
    have hfair : IsFair ex := by
      intro p t hp
      set N := (E (t + 1)).length
      have htN : t < N := by have := hlen (t + 1); omega
      by_cases hpN : (ex.cfg N).pend p = none
      · obtain ⟨t', h1, -, r, hr⟩ := InfExec.exists_ret_between ex hp hpN htN.le
        exact ⟨t', h1, by rw [hr]; rfl, by rw [hr]; trivial⟩
      · obtain ⟨q, hq, i, hi, rfl⟩ := hS.esurj p
        rw [hcfgE, ((X (t + 1)).2.sym.pend q hq i hi)] at hpN
        have hbq : (X (t + 1)).1.2.2.2.1 q = some () := by
          cases h' : (X (t + 1)).1.2.2.2.1 q with
          | none => exact absurd h' hpN
          | some u => cases u; rfl
        obtain ⟨β, h1, h2, -⟩ := hEs (t + 1)
        obtain ⟨ℓ, hℓ, hp1, hp2⟩ := h2 q hq hbq i hi
        obtain ⟨n, hn, hn'⟩ := List.getElem_of_mem hℓ
        have hidx : N + n < (E (t + 1 + 1)).length := by
          rw [h1, List.length_append]; omega
        refine ⟨N + n, by omega, ?_⟩
        have : ex.lbl (N + n) = ℓ := by
          rw [hlbl _ _ hidx]
          simp only [h1]
          rw [List.getElem_append_right (by omega)]
          simp only [N, Nat.add_sub_cancel_left]
          exact hn'
        rw [this]; exact ⟨hp1, hp2⟩
    have hret := hT ex h1s hall hfair
    -- some group is pending forever
    have hmono : ∀ q < k, ∀ j j', j ≤ j' → (X j').1.2.2.2.1 q = some () →
        (X j).1.2.2.2.1 q = some () := by
      intro q hq j j' hjj' h
      induction j', hjj' using Nat.le_induction with
      | base => exact h
      | succ j' _ ih =>
        apply ih
        obtain ⟨-, -, -, -, h4⟩ := hF (X j')
        exact h4 q hq (by rw [← hX]; exact h)
    obtain ⟨q, hq, hqf⟩ : ∃ q < k, ∀ j, (X j).1.2.2.2.1 q = some () := by
      by_contra hcon
      push Not at hcon
      choose J hJ using hcon
      set M := (Finset.range k).sup (fun q => if h : q < k then J q h else 0)
      obtain ⟨q, hq, hqM⟩ := hpend M
      apply hJ q hq
      apply hmono q hq _ M _ hqM
      have : (if h : q < k then J q h else 0) ≤ M :=
        Finset.le_sup (f := fun q => if h : q < k then J q h else 0) (Finset.mem_range.2 hq)
      simpa [hq] using this
    obtain ⟨t, r, ht⟩ := hret (e q 0)
    have htl : t < (E (t + 1)).length := by have := hlen (t + 1); omega
    have hmem : Label.ret (e q 0) r ∈ E (t + 1) := by
      rw [← ht, hlbl (t + 1) t htl]; exact List.getElem_mem _
    have hG := (X (t + 1)).2
    have hout := outputs_ne_none_of_mem hmem
    simp only [hE] at hout
    rw [hG.out q hq 0 hg] at hout
    have := (hG.pend q hq).2 hout
    rw [hqf (t + 1)] at this
    exact absurd this (by simp)

end Outcome

end BezoutElection
