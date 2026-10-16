import Papers.PODC2025.UniqueIDsBoundedRegisters.Restore
import Papers.PODC2025.UniqueIDsBoundedRegisters.Mirror

/-!
# Theorem 4.1: no unique-id object beyond `k·m + k + 1` calls

Any anonymous, obstruction-free implementation of `get()` from `k` registers with `m` values
(`m = 2^w`) and read/write/FAI, run by at least `k·m + k + 2` processes, has an execution with at
most `k·m + k + 2` invocations in which two `get()` operations return the same identifier.

**Construction (as in the paper).** Fresh processes `q₀, q₁, …` are launched one after another,
each running solo. A process is *suspended* (poised) just before an update primitive on `Rᵢ` if
fewer than `m` processes are poised on `Rᵢ` and, for a `write(x)`, no poised process is about
to `write(x)` on `Rᵢ` (`Poisable`). We keep a list `S` of poised processes and a set `U` of
registers that the poised processes can restore to their current value (`Restorable`, Claim 1).
A process that runs to completion either changes some register outside `U` (then `U` grows by
that register — the paper's "special" processes), or changes only registers of `U`; in the
latter case the poised processes restore the memory to its state before it started
(`restore_many`), and a fresh process replays its solo run (anonymity, `runFrom_mirror`) and
returns the same identifier. The potential `|S| + |U| ≤ k·m + k` grows with every launched
process, which bounds the number of invocations.

The paper's definition of "poised" for writes omits the bound "fewer than `m` processes are
poised on `Rᵢ`"; it is needed for the count `k·m` and is used here (see `differencies.md`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory Impl

variable {k m : ℕ} [NeZero m] {P L : Type} [DecidableEq P]
variable (I : Impl uidObj (fun _ : Fin k => bReg m) P L)

/-- The next action of a running process makes it *poised* (it is suspended): an update of
register `i` on which fewer than `m` processes are poised, and, for `write(v)`, no poised
process is about to `write(v)` on `i`. -/
def Poisable (S : List (P × Fin k × BOp m)) : Action uidObj (fun _ : Fin k => bReg m) L → Prop
  | .access i o _ => o ≠ .read ∧ cnt S i < m ∧ ∀ v, o = .write v → ∀ p, (p, i, BOp.write v) ∉ S
  | .ret _ _ => False

/-- Two distinct completed operations returned the same value. -/
def Dup (α : List (Label P uidObj)) : Prop :=
  ∃ x y : OpId P, Completed α x ∧ Completed α y ∧ x ≠ y ∧ respOf α x = respOf α y

lemma not_uniqueResp_of_dup {α : List (Label P uidObj)} (h : Dup α) : ¬ UniqueResp α := by
  obtain ⟨x, y, hx, hy, hxy, he⟩ := h
  exact fun hu => hu x y hx hy hxy he

/-- One solo step of `q` changes the memory at most at the register it accesses. -/
lemma soloStep_mem_cases (q : P) (X : Config uidObj (fun _ : Fin k => bReg m) P L)
    (hp : X.pend q ≠ none) :
    (∃ i o kk, I.act q (X.loc q) = .access i o kk ∧
      (I.soloStep q X).mem = Function.update X.mem i (app (X.mem i) o)) ∨
    (I.soloStep q X).mem = X.mem := by
  unfold soloStep
  simp only [hp, ↓reduceIte]
  obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome X q hp)
  rw [hC', Option.getD_some]
  unfold nextLabel at hC'
  split at hC'
  · rename_i i o kk hact
    obtain ⟨-, -, i', o', kk', hact', hm, -⟩ := step_tau hC'
    rw [hact] at hact'
    simp only [Action.access.injEq] at hact'
    obtain ⟨rfl, hoo, -⟩ := hact'
    have := eq_of_heq hoo; subst this
    exact Or.inl ⟨i, o, kk, hact, hm⟩
  · exact Or.inr (step_ret hC').2.2.1

/-- A process that took no step is in its initial state. -/
lemma fresh_state {α : List (Label P uidObj)} {C : Config uidObj (fun _ : Fin k => bReg m) P L}
    (hrun : I.run α = some C) {p : P} (hp : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    C.loc p = I.locInit p ∧ C.pend p = none :=
  I.runFrom_other hrun hp

lemma invCount_soloLabels (q : P) (C : Config uidObj (fun _ : Fin k => bReg m) P L) (j : ℕ) :
    invCount (I.soloLabels q C j) = 0 := by
  induction j generalizing C with
  | zero => rfl
  | succ j ih =>
    rw [soloLabels_succ]
    split_ifs
    · rfl
    · rw [invCount_cons, ih]
      unfold nextLabel; split <;> rfl

lemma invCount_taus (ps : List P) :
    invCount (ps.map (fun p => (Label.tau p : Label P uidObj))) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih, isInv]

section Construction

variable {N : ℕ} (e : Fin N ↪ P)

/-- Invariant of the construction after launching `n` processes `e 0, …, e (n-1)`:
`S` are the poised processes, `U` the registers they can restore to their current value. -/
structure Good (α : List (Label P uidObj)) (C : Config uidObj (fun _ : Fin k => bReg m) P L)
    (S : List (P × Fin k × BOp m)) (U : Finset (Fin k)) (n : ℕ) : Prop where
  run : I.run α = some C
  nd : (S.map Prod.fst).Nodup
  wd : WD S
  nr : ∀ x ∈ S, x.2.2 ≠ .read
  poised : ∀ x ∈ S, PoisedAt I C x
  cnt_le : ∀ i, cnt S i ≤ m
  restorable : ∀ i ∈ U, Restorable S i (C.mem i)
  fresh : ∀ j : Fin N, n ≤ j.val → ∀ ℓ ∈ α, ℓ.proc ≠ e j
  inv : invCount α = n
  le : n ≤ S.length + U.card

lemma good_init : Good I e [] I.initCfg [] ∅ 0 where
  run := rfl
  nd := List.nodup_nil
  wd := by intro a ha; simp at ha
  nr := by simp
  poised := by simp
  cnt_le := by simp [cnt]
  restorable := by simp
  fresh := by simp
  inv := rfl
  le := by simp

/-- At most `k·m` poised processes. -/
lemma length_le_of_cnt (S : List (P × Fin k × BOp m)) (hS : S.Nodup) (h : ∀ i, cnt S i ≤ m) :
    S.length ≤ k * m := by
  classical
  have h1 : S.length = ∑ i : Fin k, cnt S i := by
    rw [← List.toFinset_card_of_nodup hS,
      Finset.card_eq_sum_card_fiberwise (f := fun x => x.2.1) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [cnt, ← List.toFinset_card_of_nodup (hS.filter _), List.toFinset_filter]
    simp
  rw [h1]
  calc ∑ i : Fin k, cnt S i ≤ ∑ _i : Fin k, m := Finset.sum_le_sum (fun i _ => h i)
    _ = k * m := by simp

/-- **One launch.** Either we find an execution with a duplicate identifier, or the invariant
holds with one more launched process and a larger potential `|S| + |U|`. -/
theorem good_step (hA : Anonymous I) (hall : ∀ p, I.allowed p ()) (hof : I.ObstructionFree)
    {α : List (Label P uidObj)} {C : Config uidObj (fun _ : Fin k => bReg m) P L}
    {S : List (P × Fin k × BOp m)} {U : Finset (Fin k)} {n : ℕ}
    (hG : Good I e α C S U n) (hn : n + 1 < N) :
    (∃ β, I.Valid β ∧ invCount β = n + 2 ∧ Dup β) ∨
    ∃ α' C' S' U', Good I e α' C' S' U' (n + 1) ∧ S.length + U.card < S'.length + U'.card := by
  classical
  set q := e ⟨n, by omega⟩ with hq
  set q' := e ⟨n + 1, hn⟩ with hq'
  have hqq' : q ≠ q' := by
    intro h; have := e.injective h; simp [Fin.ext_iff] at this
  have hqα : ∀ ℓ ∈ α, ℓ.proc ≠ q := hG.fresh ⟨n, by omega⟩ le_rfl
  have hq'α : ∀ ℓ ∈ α, ℓ.proc ≠ q' := hG.fresh ⟨n + 1, hn⟩ (by simp)
  obtain ⟨hCq_loc, hCq_pend⟩ := fresh_state I hG.run hqα
  obtain ⟨hCq'_loc, hCq'_pend⟩ := fresh_state I hG.run hq'α
  have hnotS : ∀ p, C.pend p = none → p ∉ S.map Prod.fst := by
    intro p hp h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    exact (hG.poised x hx).1 hp
  have hqS := hnotS q hCq_pend
  have hq'S := hnotS q' hCq'_pend
  have hSnd : S.Nodup := List.Nodup.of_map _ hG.nd
  have hSinj := List.inj_on_of_nodup_map hG.nd
  -- invocation of `get()` by `q`
  set C₁ : Config uidObj (fun _ : Fin k => bReg m) P L :=
    { C with pend := Function.update C.pend q (some ()),
             loc := Function.update C.loc q (I.invoke q (C.loc q) ()) } with hC₁
  have hs₁ : I.step C (.inv q ()) = some C₁ := by
    simp [step, hCq_pend, hall q, hC₁]
  have hrun₁ : I.run (α ++ [.inv q ()]) = some C₁ := by
    rw [run_append_of_eq I hG.run, runFrom_singleton, hs₁]
  have hC₁q : C₁.pend q ≠ none := by simp [hC₁]
  have hC₁other : ∀ p ≠ q, C₁.loc p = C.loc p ∧ C₁.pend p = C.pend p := by
    intro p hp; simp [hC₁, Function.update_of_ne hp]
  -- solo run of `q` until it returns or becomes poised
  obtain ⟨M, hbefore, hat⟩ :=
    exists_solo_until I q C₁ (Poisable S) (hof C₁ q ⟨_, hrun₁⟩ hC₁q)
  set X : ℕ → Config uidObj (fun _ : Fin k => bReg m) P L := fun j => (I.soloStep q)^[j] C₁
    with hX
  have hXother : ∀ j, ∀ p ≠ q, (X j).loc p = C.loc p ∧ (X j).pend p = C.pend p := by
    intro j p hp
    have := I.iterate_soloStep_other hp C₁ j
    exact ⟨this.1.trans (hC₁other p hp).1, this.2.trans (hC₁other p hp).2⟩
  have hXpoised : ∀ j, ∀ x ∈ S, PoisedAt I (X j) x := by
    intro j x hx
    have hxq : x.1 ≠ q := fun h => hqS (h ▸ List.mem_map_of_mem hx)
    obtain ⟨h1, h2⟩ := hXother j x.1 hxq
    obtain ⟨h3, kk, h4⟩ := hG.poised x hx
    exact ⟨h2 ▸ h3, kk, h1 ▸ h4⟩
  have hXmem : ∀ j ≤ M, ∀ i, (X j).mem i = C.mem i ∨ Restorable S i ((X j).mem i) := by
    intro j
    induction j with
    | zero => intro _ i; left; rfl
    | succ j ih =>
      intro hj i
      have hb := hbefore j (by omega)
      have hXs : X (j + 1) = I.soloStep q (X j) := Function.iterate_succ_apply' _ _ _
      rcases soloStep_mem_cases I q (X j) hb.1 with ⟨i', o, kk, hact, hmem⟩ | hmem
      · rw [hXs, hmem]
        by_cases hii : i = i'
        · subst hii
          simp only [Function.update_self]
          have hnp := hb.2
          rw [hact] at hnp
          simp only [Poisable] at hnp
          cases o with
          | read => simpa using ih (by omega) i
          | fai =>
            right; left
            by_contra hc
            exact hnp ⟨by simp, by omega, fun v hv => by cases hv⟩
          | write v =>
            right
            simp only [app_write]
            by_cases hc : cnt S i < m
            · by_contra hcon
              apply hnp
              refine ⟨by simp, hc, fun v' hv' p hp => hcon (Or.inr ⟨p, ?_⟩)⟩
              cases hv'; exact hp
            · exact Or.inl (by omega)
        · rw [Function.update_of_ne hii]; exact ih (by omega) i
      · rw [hXs, hmem]; exact ih (by omega) i
  -- the solo run as an execution
  set γ : List (Label P uidObj) := .inv q () :: I.soloLabels q C₁ M with hγ
  have hγrun : I.runFrom C γ = some (X M) := by
    rw [hγ, runFrom_cons, hs₁, Option.bind_some, runFrom_soloLabels]
  have hγproc : ∀ ℓ ∈ γ, ℓ.proc = q := by
    intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · rfl
    · exact I.soloLabels_proc q C₁ M ℓ hℓ
  have hγinv : invCount γ = 1 := by
    rw [hγ, invCount_cons, invCount_soloLabels]; rfl
  have hrunγ : I.run (α ++ γ) = some (X M) := by rw [run_append_of_eq I hG.run, hγrun]
  have hfreshγ : ∀ j : Fin N, n + 1 ≤ j.val → ∀ ℓ ∈ α ++ γ, ℓ.proc ≠ e j := by
    intro j hj ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact hG.fresh j (by omega) ℓ hℓ
    · rw [hγproc ℓ hℓ, hq]
      intro h; have := e.injective h; rw [Fin.ext_iff] at this; simp at this; omega
  have hinvγ : invCount (α ++ γ) = n + 1 := by rw [invCount_append, hG.inv, hγinv]
  by_cases hret : (X M).pend q = none
  · -- `q` returned
    by_cases hU : ∀ i ∉ U, (X M).mem i = C.mem i
    · -- only registers of `U` changed: restore the memory and replay `q`'s run by `q'`
      left
      obtain ⟨es, hesnd, hesS, hesU, hesO⟩ :=
        restore_many S hSnd hG.wd hG.nr C.mem U.toList (Finset.nodup_toList U)
          (fun i hi => hG.restorable i (by simpa using hi)) (X M).mem
      have hmemeq : memAfter (X M).mem es = C.mem := by
        funext j
        by_cases hj : j ∈ U
        · exact hesU j (by simpa using hj)
        · rw [hesO j (by simpa using hj)]; exact hU j hj
      have hesfst : (es.map Prod.fst).Nodup :=
        List.Nodup.map_on (fun a ha b hb hab => hSinj (hesS a ha).1 (hesS b hb).1 hab) hesnd
      obtain ⟨D, hDrun, hDmem, hDother⟩ :=
        runFrom_taus I es hesfst (X M) (fun x hx => hXpoised M x (hesS x hx).1)
      have hq'es : q' ∉ es.map Prod.fst := by
        intro h; obtain ⟨x, hx, hx'⟩ := List.mem_map.1 h
        exact hq'S (hx' ▸ List.mem_map_of_mem (hesS x hx).1)
      obtain ⟨hDq'l, hDq'p⟩ := hDother q' hq'es
      have hmirror : Mirror q q' C D := by
        refine ⟨by rw [hDmem, hmemeq], ?_, ?_⟩
        · rw [hDq'l, (hXother M q' hqq'.symm).1, hCq'_loc, hCq_loc, hA.locInit]
        · rw [hDq'p, (hXother M q' hqq'.symm).2, hCq'_pend, hCq_pend]
      obtain ⟨D', hD'run, -⟩ := runFrom_mirror hA (fun o _ => hall q') γ hmirror hγproc hγrun
      set τ : List (Label P uidObj) := es.map (fun x => Label.tau x.1) with hτ
      set β := α ++ γ ++ τ ++ γ.map (relabel q') with hβ
      have hβrun : I.run β = some D' := by
        rw [hβ, run_append_of_eq I (run_append_of_eq I hrunγ τ ▸ hDrun), hD'run]
      -- the response of `q`
      have hcnt := I.runFrom_counts hγrun q 0 0 (Or.inl ⟨hCq_pend, rfl⟩)
      have hops : opsOf γ q = [()] := by
        rw [hγ, opsOf_cons, opsOf_soloLabels]; simp
      simp only [hret, true_and, ne_eq, not_true_eq_false, false_and, or_false, hops,
        List.length_singleton, zero_add] at hcnt
      obtain ⟨r, hr⟩ := List.length_eq_one_iff.1 hcnt.symm
      have hτq : ∀ p, p ∉ es.map Prod.fst → respsOf τ p = [] := by
        intro p hp
        refine respsOf_eq_nil_of_proc_ne (fun ℓ hℓ => ?_)
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hℓ
        exact fun h => hp (h ▸ List.mem_map_of_mem hx)
      have hqes : q ∉ es.map Prod.fst := by
        intro h; obtain ⟨x, hx, hx'⟩ := List.mem_map.1 h
        exact hqS (hx' ▸ List.mem_map_of_mem (hesS x hx).1)
      have hrq : respsOf β q = [r] := by
        rw [hβ, respsOf_append, respsOf_append, respsOf_append, hr,
          respsOf_eq_nil_of_proc_ne hqα, hτq q hqes,
          respsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by
            obtain ⟨ℓ', -, rfl⟩ := List.mem_map.1 hℓ; rw [relabel_proc]; exact hqq'.symm)]
        rfl
      have hrq' : respsOf β q' = [r] := by
        rw [hβ, respsOf_append, respsOf_append, respsOf_append, respsOf_relabel γ hγproc, hr,
          respsOf_eq_nil_of_proc_ne hq'α, hτq q' hq'es,
          respsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hγproc ℓ hℓ]; exact hqq')]
        rfl
      refine ⟨β, ⟨D', hβrun⟩, ?_, (q, 0), (q', 0), ?_, ?_, ?_, ?_⟩
      · have hτinv : invCount τ = 0 := by
          rw [hτ, invCount, List.countP_eq_zero]
          intro ℓ hℓ; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hℓ; simp [isInv]
        rw [hβ, invCount_append, invCount_append, hinvγ, hτinv, invCount_relabel, hγinv]
      · simp [Completed, hrq]
      · simp [Completed, hrq']
      · simp [hqq']
      · simp [respOf, hrq, hrq']
    · -- some register outside `U` changed: `U` grows
      right
      push Not at hU
      obtain ⟨i₀, hi₀U, hi₀⟩ := hU
      refine ⟨α ++ γ, X M, S, insert i₀ U, ⟨hrunγ, hG.nd, hG.wd, hG.nr, hXpoised M, hG.cnt_le,
        ?_, hfreshγ, hinvγ, ?_⟩, ?_⟩
      · intro i hi
        rcases hXmem M le_rfl i with h | h
        · rcases Finset.mem_insert.1 hi with rfl | hi
          · exact absurd h hi₀
          · rw [h]; exact hG.restorable i hi
        · exact h
      · rw [Finset.card_insert_of_notMem hi₀U]; have := hG.le; omega
      · rw [Finset.card_insert_of_notMem hi₀U]; omega
  · -- `q` is poised
    right
    have hpo := hat.resolve_left hret
    obtain ⟨i, o, kk, hact⟩ : ∃ i o kk, I.act q ((X M).loc q) = .access i o kk := by
      revert hpo; cases I.act q ((X M).loc q) with
      | access i o kk => intro _; exact ⟨i, o, kk, rfl⟩
      | ret r l => intro h; exact absurd h (by simp [Poisable])
    rw [hact] at hpo
    obtain ⟨hor, hcnt, hwv⟩ := hpo
    set S' := S ++ [(q, i, o)] with hS'
    have hsub : S.Sublist S' := List.sublist_append_left _ _
    refine ⟨α ++ γ, X M, S', U, ⟨hrunγ, ?_, ?_, ?_, ?_, ?_, ?_, hfreshγ, hinvγ, ?_⟩, ?_⟩
    · rw [hS', List.map_append, List.nodup_append]
      refine ⟨hG.nd, by simp, fun a ha b hb hab => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb; subst hab; exact hqS ha
    · intro a ha b hb hab hw
      rw [hS', List.mem_append, List.mem_singleton] at ha hb
      rcases ha with ha | rfl <;> rcases hb with hb | rfl
      · exact hG.wd a ha b hb hab hw
      · obtain ⟨v, hv⟩ := hw
        obtain ⟨a1, a2⟩ := a
        simp only at hab; subst hab
        simp only at hv; subst hv
        exact absurd ha (hwv v rfl a1)
      · obtain ⟨v, hv⟩ := hw
        obtain ⟨b1, b2⟩ := b
        simp only at hab; subst hab
        simp only at hv; subst hv
        exact absurd hb (hwv v rfl b1)
      · rfl
    · intro x hx
      rw [hS', List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hG.nr x hx
      · exact hor
    · intro x hx
      rw [hS', List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hXpoised M x hx
      · exact ⟨hret, kk, hact⟩
    · intro i'
      have := hG.cnt_le i'
      simp only [cnt, hS', List.filter_append, List.length_append] at this ⊢
      by_cases h : i = i'
      · subst h; simp only [cnt] at hcnt; simp; omega
      · simp [h]; exact this
    · intro i' hi'
      rcases hXmem M le_rfl i' with h | h
      · rw [h]; exact (hG.restorable i' hi').mono hsub
      · exact h.mono hsub
    · rw [hS', List.length_append]; have := hG.le; simp; omega
    · rw [hS', List.length_append]; simp

/-- Iterating `good_step`: a duplicate is found within `k·m + k + 2` invocations. -/
theorem exists_dup (hA : Anonymous I) (hall : ∀ p, I.allowed p ()) (hof : I.ObstructionFree)
    (hN : k * m + k + 2 ≤ N) :
    ∀ s : ℕ, ∀ α C S U n, Good I e α C S U n → k * m + k ≤ S.length + U.card + s →
      ∃ β, I.Valid β ∧ invCount β ≤ k * m + k + 2 ∧ Dup β := by
  intro s
  induction s with
  | zero =>
    intro α C S U n hG hs
    have h1 := length_le_of_cnt S (List.Nodup.of_map _ hG.nd) hG.cnt_le
    have h2 : U.card ≤ k := by simpa using Finset.card_le_univ U
    have hle := hG.le
    rcases good_step I e hA hall hof hG (by nlinarith) with ⟨β, hβ, hc, hd⟩ |
      ⟨α', C', S', U', hG', hlt⟩
    · exact ⟨β, hβ, by omega, hd⟩
    · exfalso
      have h1' := length_le_of_cnt S' (List.Nodup.of_map _ hG'.nd) hG'.cnt_le
      have h2' : U'.card ≤ k := by simpa using Finset.card_le_univ U'
      omega
  | succ s ih =>
    intro α C S U n hG hs
    have h1 := length_le_of_cnt S (List.Nodup.of_map _ hG.nd) hG.cnt_le
    have h2 : U.card ≤ k := by simpa using Finset.card_le_univ U
    have hle := hG.le
    rcases good_step I e hA hall hof hG (by nlinarith) with ⟨β, hβ, hc, hd⟩ |
      ⟨α', C', S', U', hG', hlt⟩
    · exact ⟨β, hβ, by omega, hd⟩
    · exact ih α' C' S' U' (n + 1) hG' (by omega)

end Construction

/-- **Theorem 4.1** (main form, `m`-valued registers). Every anonymous obstruction-free
implementation of `get()` from `k` registers with values in `Fin m` and read/write/FAI, with at
least `k·m + k + 2` processes, has an execution with at most `k·m + k + 2` invocations in which
two distinct completed `get()` operations return the same identifier. -/
theorem lower_bound (hA : Anonymous I) (hall : ∀ p, I.allowed p ()) (hof : I.ObstructionFree)
    (e : Fin (k * m + k + 2) ↪ P) :
    ∃ α, I.Valid α ∧ invCount α ≤ k * m + k + 2 ∧
      ∃ x y : OpId P, Completed α x ∧ Completed α y ∧ x ≠ y ∧ respOf α x = respOf α y :=
  exists_dup I e hA hall hof le_rfl (k * m + k) [] I.initCfg [] ∅ 0 (good_init I e) (by simp)

/-- **Theorem 4.1** (as stated): an anonymous obstruction-free unique-id implementation from `k`
registers with `m` values, with at least `k·m + k + 2` processes, is correct for at most
`k·m + k + 1` calls of `get()`. -/
theorem theorem_4_1 (hA : Anonymous I) (hall : ∀ p, I.allowed p ()) (hof : I.ObstructionFree)
    (e : Fin (k * m + k + 2) ↪ P) {B : ℕ} (hB : CorrectUpTo I B) : B ≤ k * m + k + 1 := by
  by_contra hlt
  obtain ⟨α, hα, hc, x, y, hx, hy, hxy, he⟩ := lower_bound I hA hall hof e
  exact hB α hα (by omega) x y hx hy hxy he

end Cslib.SharedMemory.UniqueIDs
