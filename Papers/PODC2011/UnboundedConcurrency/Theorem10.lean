import Papers.PODC2011.UnboundedConcurrency.Common

/-!
# Theorem 10: `n`-consensus objects for all `n` do not give unbounded-concurrency consensus

Afek, Morrison, Wertheim, *From Bounded to Unbounded Concurrency Objects and Back*, PODC 2011,
Theorem 10: there is no unbounded concurrency wait-free implementation of consensus from
read/write registers and `n`-consensus objects for all `n`.

Model (`Cslib.SharedMemory.Arrival`): processes `ℕ`, deterministic, each starting with its binary
input; asynchronous, every infinite schedule is allowed (unbounded concurrency: infinitely many
processes may arrive and stay active); the algorithm may use any (possibly infinite) family of
atomic base objects, initialized arbitrarily. A `c`-consensus object "can be accessed by at most
`c` processes": we require of the algorithm that in every execution at most `c` distinct processes
apply an operation to it (`AccessBounded`).

We prove the more general `no_consensus_of_rwLike_or_accessBounded`: every base object is either
read/write-like (every operation is read-only or a blind overwrite, e.g. a register) or is
accessed by a bounded number of processes — whatever its sequential specification. Theorem 10
(`theorem_10`) is the special case of registers and consensus objects.

The proof is the paper's: from an `n`-critical execution (critical w.r.t. the processes
`p₀, …, p_{n-1}`), all of `p₀, …, p_{n-1}` are poised on one object `O` that is not a register,
hence `O` admits `c ≥ n` processes; the execution is `(c+1)`-bivalent and has a `(c+1)`-critical
extension, in which `p₀, …, p_c` are poised on an object `O'` admitting `c' ≥ c + 1` processes, so
`O' ≠ O` and `p₀` took a step. Repeating forever, `p₀` takes infinitely many steps without
deciding.
-/

namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec}

section Access

variable {P X Y : Type} [DecidableEq P]

-- CSLib candidate: `Accesses`, `AccessBounded`, `AccessBounded.card_le` (Arrival/Basic.lean)
/-- Process `p` applies an operation to object `i` during the execution `σ` (with inputs `x`):
it takes a step while poised on `i`. -/
def Accesses (A : Alg T P X Y) (x : P → X) (σ : List P) (i : ι) (p : P) : Prop :=
  ∃ τ τ', σ = τ ++ p :: τ' ∧ (A.exec x τ).Poised p i

/-- Object `i` is accessed by at most `c` distinct processes in every execution of `A`. -/
def AccessBounded (A : Alg T P X Y) (i : ι) (c : ℕ) : Prop :=
  ∀ (x : P → X) (σ : List P) (S : Finset P), (∀ p ∈ S, Accesses A x σ i p) → S.card ≤ c

/-- If the processes of `S` are all poised on an object accessed by at most `c` processes, then
`|S| ≤ c` (schedule them one after the other). -/
lemma AccessBounded.card_le {A : Alg T P X Y} {i : ι} {c : ℕ} (h : AccessBounded A i c)
    (x : P → X) (σ : List P) (S : Finset P) (hS : ∀ p ∈ S, (A.exec x σ).Poised p i) :
    S.card ≤ c := by
  classical
  refine h x (σ ++ S.toList) S (fun p hp => ?_)
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem (Finset.mem_toList.2 hp)
  have hnd : (l₁ ++ p :: l₂).Nodup := hl ▸ S.nodup_toList
  have hp₁ : p ∉ l₁ := fun h => (List.nodup_append.1 hnd).2.2 p h p (by simp) rfl
  refine ⟨σ ++ l₁, l₂, by rw [hl]; simp, ?_⟩
  unfold Cfg.Poised
  rw [Alg.exec_append, Alg.run_loc_other _ _ hp₁]
  exact hS p hp

end Access

/-- The processes `p₀, …, p_{n-1}`. -/
def below (n : ℕ) : Set ℕ := {p | p < n}

lemma below_mono {n n' : ℕ} (h : n ≤ n') : below n ⊆ below n' :=
  fun _ hp => lt_of_lt_of_le hp h

variable {A : Alg T ℕ Bool Bool}

section Crit

variable (hag : Agreement A (fun _ => True)) (hwf : WaitFree A (fun s => (Set.range s).Finite))
include hag hwf

/-- In an `n`-critical execution, all of `p₀, …, p_{n-1}` are poised on one object, which is not
read/write-like (the "standard FLP valency arguments" of the paper). -/
theorem crit_same_object {n : ℕ} {x : ℕ → Bool} {α : List ℕ} (hc : Crit A (below n) x α) :
    ∃ i, ¬ (T i).RWLike ∧ ∀ p < n, (A.exec x α).Poised p i := by
  obtain ⟨p₀, hp₀, q₀, hq₀, -, hp₀t, -, hq₀f⟩ := Crit.exists_teams hwf hag hc
  obtain ⟨-, i, hpi, hqi, hrw⟩ := rw_pair hag hwf hc.1 hp₀ hq₀ hp₀t hq₀f
  refine ⟨i, hrw, fun p hp => ?_⟩
  obtain ⟨v, hv⟩ := exists_canDec hwf (show p ∈ below n from hp) x (α ++ [p])
  cases v
  · have hpt : ¬ CanDec A (below n) x (α ++ [p]) true := fun ht => hc.2 p hp ⟨hv, ht⟩
    obtain ⟨-, j, hpj, hqj, -⟩ := rw_pair hag hwf hc.1 hp hq₀ hpt hq₀f
    rwa [hqi.unique hqj]
  · have hpf : ¬ CanDec A (below n) x (α ++ [p]) false := fun hf => hc.2 p hp ⟨hf, hv⟩
    obtain ⟨-, j, hp₀j, hpj, -⟩ := rw_pair hag hwf hc.1 hp₀ hp hp₀t hpf
    rwa [hpi.unique hp₀j]

end Crit

/-- A stage of the construction: an `n`-critical execution, `n ≥ 1`. -/
structure Stage (A : Alg T ℕ Bool Bool) (x : ℕ → Bool) where
  /-- The execution. -/
  α : List ℕ
  /-- The number of processes. -/
  n : ℕ
  pos : 0 < n
  crit : Crit A (below n) x α

/-- **Generalized Theorem 10.** No algorithm solves binary consensus (agreement, weak validity,
wait-freedom) in the unbounded concurrency model if each of its base objects is either
read/write-like (e.g. a register) or accessed by a bounded number of processes. -/
theorem no_consensus_of_rwLike_or_accessBounded
    (hobj : ∀ i, (T i).RWLike ∨ ∃ c, AccessBounded A i c)
    (hag : Agreement A anySched) (hval : WeakValidity A anySched)
    (hwf : WaitFree A infArrival) : False := by
  classical
  have hag' : Agreement A (fun _ => True) := hag
  have hwf' : WaitFree A (fun s => (Set.range s).Finite) := fun x s _ => hwf x s trivial
  -- inputs: `p₀` proposes `false`, every other process `true`
  let x : ℕ → Bool := fun p => decide (p ≠ 0)
  -- a solo run of `p` decides its input
  have hsolo : ∀ p < 2, CanDec A (below 2) x [] (x p) := by
    intro p hp
    obtain ⟨m, v, hout⟩ := exists_solo_out hwf' x [] p
    let x' : ℕ → Bool := fun _ => x p
    have hag0 : AgreeOn {p} (A.initCfg x) (A.initCfg x') :=
      Alg.initCfg_agreeOn (fun q hq => by simp at hq; subst hq; rfl)
    have hrep : ∀ s ∈ List.replicate (m + 1) p, s ∈ ({p} : Set ℕ) := fun s hs => by
      rw [List.eq_of_mem_replicate hs]; rfl
    have h2 := Alg.run_agreeOn hag0 hrep
    have hout' : (A.exec x' ([] ++ List.replicate (m + 1) p)).Out p v :=
      (h2.out_iff (by rfl) v).1 hout
    have hv : v = x p := hval (x p) x' _ trivial (fun _ => rfl) p (by simp) v hout'
    subst hv
    exact ⟨List.replicate (m + 1) p, fun s hs => by rw [List.eq_of_mem_replicate hs]; exact hp,
      p, by simp, hout⟩
  have hbiv0 : Biv A (below 2) x [] :=
    ⟨by simpa [x] using hsolo 0 (by omega), by simpa [x] using hsolo 1 (by omega)⟩
  obtain ⟨β₀, -, hc₀⟩ := exists_crit hwf' hag' (Set.finite_lt_nat 2) hbiv0
  -- the object of an `n`-critical execution admits at least `n` processes
  have hbound : ∀ S : Stage A x, ∃ i c, AccessBounded A i c ∧ S.n ≤ c ∧
      ∀ p < S.n, (A.exec x S.α).Poised p i := by
    intro S
    obtain ⟨i, hrw, hall⟩ := crit_same_object hag' hwf' S.crit
    obtain ⟨c, hc⟩ := (hobj i).resolve_left hrw
    refine ⟨i, c, hc, ?_, hall⟩
    have := hc.card_le x S.α (Finset.range S.n) (fun p hp => hall p (Finset.mem_range.1 hp))
    simpa using this
  -- one stage of the construction: `p₀` takes a step in the extension
  have hnext : ∀ S : Stage A x, ∃ S' : Stage A x, ∃ β, S'.α = S.α ++ β ∧ 0 ∈ β := by
    intro S
    obtain ⟨i, c, hci, hnc, hall⟩ := hbound S
    have hbiv : Biv A (below (c + 1)) x S.α := S.crit.1.mono (below_mono (by omega))
    obtain ⟨β, -, hc⟩ := exists_crit hwf' hag' (Set.finite_lt_nat _) hbiv
    let S' : Stage A x := ⟨S.α ++ β, c + 1, by omega, hc⟩
    obtain ⟨i', c', hci', hnc', hall'⟩ := hbound S'
    refine ⟨S', β, rfl, ?_⟩
    by_contra h0
    have h1 := hall 0 S.pos
    have h2 := hall' 0 (by simp [S'])
    have h2' : (A.exec x S.α).Poised 0 i' := by
      unfold Cfg.Poised at h2 ⊢
      rwa [Alg.exec_append, Alg.run_loc_other _ _ h0] at h2
    have hii : i' = i := h2'.unique h1
    subst hii
    -- `p₀, …, p_c` are all poised on `i`, which admits only `c` processes
    have := hci.card_le x (S.α ++ β) (Finset.range (c + 1))
      (fun p hp => hall' p (by simpa [S'] using hp))
    simp at this
    omega
  choose nxt β hβ h0 using hnext
  let S0 : Stage A x := ⟨[] ++ β₀, 2, by omega, hc₀⟩
  let st : ℕ → Stage A x := fun k => nxt^[k] S0
  have hsucc : ∀ k, (st (k + 1)).α = (st k).α ++ β (st k) := fun k => by
    simp only [st, Function.iterate_succ_apply']; exact hβ _
  have hlen : ∀ k, k ≤ (st k).α.length := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      rw [hsucc, List.length_append]
      have : β (st k) ≠ [] := List.ne_nil_of_mem (h0 (st k))
      have := List.length_pos_of_ne_nil this
      omega
  obtain ⟨s, hs⟩ := exists_seq_of_chain (fun k => (st k).α)
    (fun k => by simp only [hsucc]; exact List.prefix_append _ _) hlen
  have hinf : InfOften s 0 := by
    intro N
    have h1 := hs (N + 1)
    simp only [hsucc, List.length_append, pre_add] at h1
    rw [hs N] at h1
    have h2 := List.append_cancel_left h1
    have h3 : 0 ∈ pre (fun t => s ((st N).α.length + t)) (β (st N)).length := by
      rw [h2]; exact h0 (st N)
    obtain ⟨u, -, hsu⟩ := mem_pre.1 h3
    exact ⟨_ + u, by have := hlen N; omega, hsu⟩
  obtain ⟨t, v, hout⟩ := hwf x s trivial 0 hinf
  apply (st t).crit.1.not_out hag' (Or.inr (st t).pos) v
  obtain ⟨τ, hτ⟩ := pre_prefix s (hlen t)
  rw [hs t] at hτ
  rw [← hτ, Alg.exec_append]
  exact Alg.Cfg.Out.run hout τ

/-! ### Registers and `c`-consensus objects -/

/-- An atomic (multi-valued) consensus object: the state is the decided value (`none` before
the first proposal); `propose v` decides `v` if nothing is decided yet and returns the decided
value. A `c`-consensus object is such an object accessed by at most `c` processes
(`AccessBounded`). -/
abbrev consObj (V : Type) : ObjSpec where
  State := Option V
  Op := V
  Resp := V
  init := none
  δ s v := (some (s.getD v), s.getD v)

lemma register_rwLike (V : Type) (v₀ : V) : (register V v₀).RWLike := by
  intro o
  cases o with
  | read => exact Or.inl (fun _ => rfl)
  | write v => exact Or.inr (fun _ _ => rfl)

/-- **Theorem 10** of [AMW11]. There is no unbounded concurrency wait-free implementation of
(binary) consensus from read/write registers and `n`-consensus objects for all `n`: every base
object `i` of the algorithm is a register (over any value type) or a consensus object (over any
value type) that is accessed by at most `c` processes, for some `c` depending on `i`. -/
theorem theorem_10
    (hobj : ∀ i, (∃ (V : Type) (v₀ : V), T i = register V v₀) ∨
      ∃ (V : Type) (c : ℕ), T i = consObj V ∧ AccessBounded A i c)
    (hag : Agreement A anySched) (hval : WeakValidity A anySched)
    (hwf : WaitFree A infArrival) : False := by
  refine no_consensus_of_rwLike_or_accessBounded (fun i => ?_) hag hval hwf
  rcases hobj i with ⟨V, v₀, h⟩ | ⟨V, c, -, h⟩
  · left; rw [h]; exact register_rwLike V v₀
  · exact Or.inr ⟨c, h⟩

end Podc.UnboundedConcurrency
