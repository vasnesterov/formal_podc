import Papers.PODC2024.KnowYourAudience.Rings

/-!
# The impossibility half of Theorem 4.1, corrected

The paper's argument (Section 4.1): two vectors `v`, `w` with the same frequencies are lifted along
the coverings `R_n → R_p ← R_m` of rings, `p = lcm` of the denominators of the frequencies. This
needs the ring `R_p` to be a network of the class, i.e. `p ≥ 3` (for `p ∈ {1, 2}` the quotient is a
multigraph). We use instead the coverings `R_{n'n} → R_n` and `R_{nn'} → R_{n'}`
(`n = |v|`, `n' = |w|`), together with Lemma 3.3 on vectors of length `nn'`. This needs
`n, n' ≥ 3` for bidirectional rings (symmetric communications) and `n, n' ≥ 2` for directed cycles
(the other models). These bounds are optimal (see `Counterexample.lean`).

* `eq_of_freq_eq_of_covers`: the abstract argument for any family of networks with coverings
  `i ↦ i mod n`.
* `frequencyBasedFrom_two_of_computable` (outdegree awareness, output port awareness, and also
  simple broadcast): computable ⇒ frequency-based on vectors of length `≥ 2`.
* `frequencyBasedFrom_three_of_computable_symmetric`: with symmetric communications, computable ⇒
  frequency-based on vectors of length `≥ 3`.
* The same for the classes `C_{≤B}` for every `B` (Corollary 4.2).
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset

universe u v

variable {I : Type u} [DecidableEq I] {X : Type v} [TopologicalSpace X] [T2Space X]

/-- The lifting argument: `f (x ∘ proj) = f x` along a covering in the class. -/
theorem eq_of_freq_eq_of_covers {m : CommModel} {C : NetClass} {f : List I → X}
    {A : Algorithm I X} (hA : m.Allowed A) (hCiso : IsoClosed C)
    (hcomp : Computes m C (fun _ => True) f A)
    (net : ∀ (k : ℕ) [NeZero k], Network (Fin k)) (lo B : ℕ) (hlo : 1 ≤ lo)
    (fib : ∀ (k n : ℕ) [NeZero k] [NeZero n], lo ≤ n → Fibration (net (k * n)) (net n))
    (hfib : ∀ (k n : ℕ) [NeZero k] [NeZero n] (h : lo ≤ n), (fib k n h).toFun = proj k n)
    (hcompat : ∀ (k n : ℕ) [NeZero k] [NeZero n] (h : lo ≤ n), (fib k n h).Compatible m)
    (hok : ∀ (k : ℕ) [NeZero k], m.NetOK (net k))
    (hC : ∀ (k : ℕ) [NeZero k], k ≤ B → C k (net k))
    {l l' : List I} (hl : lo ≤ l.length) (hl' : lo ≤ l'.length)
    (hB : l.length * l'.length ≤ B) (hfreq : freq l = freq l') : f l = f l' := by
  set n := l.length with hn
  set n' := l'.length with hn'
  have : NeZero n := ⟨by omega⟩
  have : NeZero n' := ⟨by omega⟩
  have hn0 : 0 < n := by omega
  have hn0' : 0 < n' := by omega
  have hnn : n ≤ n' * n := Nat.le_mul_of_pos_left n hn0'
  have hnn' : n' ≤ n * n' := Nat.le_mul_of_pos_left n' hn0
  -- lift `l` to `C_{n'n}`
  have e1 : f (List.ofFn (l.get ∘ proj n' n)) = f l := by
    have := (fib n' n hl).eq_of_computesOn (hcompat n' n hl) hA
      (hcomp _ (by positivity) _ (hC _ (by rw [Nat.mul_comm]; omega)) (hok _))
      (hcomp _ hn0 _ (hC _ (by
        have : n ≤ n * n' := Nat.le_mul_of_pos_right n hn0'
        omega)) (hok _)) (by positivity) l.get trivial trivial
    rw [hfib] at this
    rwa [List.ofFn_get] at this
  have e2 : f (List.ofFn (l'.get ∘ proj n n')) = f l' := by
    have := (fib n n' hl').eq_of_computesOn (hcompat n n' hl') hA
      (hcomp _ (by positivity) _ (hC _ hB) (hok _))
      (hcomp _ hn0' _ (hC _ (by omega)) (hok _)) (by positivity) l'.get trivial trivial
    rw [hfib] at this
    rwa [List.ofFn_get] at this
  -- the two lifts are permutations of each other
  have hperm : (List.ofFn (l.get ∘ proj n' n)).Perm (List.ofFn (l'.get ∘ proj n n')) := by
    rw [List.perm_iff_count]
    intro a
    rw [count_ofFn_comp_proj, count_ofFn_comp_proj, List.ofFn_get, List.ofFn_get]
    have := (freq_eq_freq_iff (List.ne_nil_of_length_pos hn0)
      (List.ne_nil_of_length_pos hn0')).1 hfreq a
    rw [← hn, ← hn'] at this
    linarith [Nat.mul_comm n' (l.count a), Nat.mul_comm n (l'.count a)]
  have e3 := hcomp.perm_eq hA hCiso (n := n' * n) (by positivity)
    (hC _ (by rw [Nat.mul_comm]; omega)) (hok _) (by simp) hperm trivial trivial
  rw [← e1, ← e2, e3]

/-- **Theorem 4.1, (ii) ⇒ (i), corrected (outdegree / output port awareness).** A function
computable in static strongly connected networks is frequency-based on vectors of length `≥ 2`.
(Also true for simple broadcast.) -/
theorem frequencyBasedFrom_two_of_computable {m : CommModel} (hm : m ≠ .symmetric)
    {f : List I → X} (h : Computable m staticSC (fun _ => True) f) : FrequencyBasedFrom 2 f := by
  obtain ⟨A, hA, hcomp⟩ := h
  intro l l' _ _ hl hl' hfreq
  have hok : ∀ (k : ℕ) [NeZero k], m.NetOK (cycleNet k) := by
    intro k _; cases m <;> trivial
  exact eq_of_freq_eq_of_covers hA staticSC_isoClosed hcomp (fun k _ => cycleNet k) 2
    (l.length * l'.length) (by norm_num) (fun k n _ _ h => cycleFib h) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ h => cycleFib_compatible h m) hok (fun k _ _ => cycleNet_sc k) hl hl' le_rfl
    hfreq

/-- **Theorem 4.1, (ii) ⇒ (i), corrected (symmetric communications).** A function computable with
symmetric communications in static strongly connected networks is frequency-based on vectors of
length `≥ 3`. -/
theorem frequencyBasedFrom_three_of_computable_symmetric {f : List I → X}
    (h : Computable .symmetric staticSC (fun _ => True) f) : FrequencyBasedFrom 3 f := by
  obtain ⟨A, hA, hcomp⟩ := h
  intro l l' _ _ hl hl' hfreq
  exact eq_of_freq_eq_of_covers hA staticSC_isoClosed hcomp (fun k _ => ringNet k) 3
    (l.length * l'.length) (by norm_num) (fun k n _ _ h => ringFib h) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ h => ringFib_compatible h _) (fun k _ => ringNet_symmetric k)
    (fun k _ _ => ringNet_sc k) hl hl' le_rfl hfreq

/-- **Corollary 4.2, (ii) ⇒ (i), corrected (outdegree / output port awareness).** -/
theorem frequencyBasedFrom_two_of_computable_sizeLE {m : CommModel} (hm : m ≠ .symmetric)
    {f : List I → X} (h : ∀ B, Computable m (sizeLE B) (fun _ => True) f) :
    FrequencyBasedFrom 2 f := by
  intro l l' _ _ hl hl' hfreq
  obtain ⟨A, hA, hcomp⟩ := h (l.length * l'.length)
  have hok : ∀ (k : ℕ) [NeZero k], m.NetOK (cycleNet k) := by
    intro k _; cases m <;> trivial
  exact eq_of_freq_eq_of_covers hA (sizeLE_isoClosed _) hcomp (fun k _ => cycleNet k) 2
    (l.length * l'.length) (by norm_num) (fun k n _ _ h => cycleFib h) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ h => cycleFib_compatible h m) hok (fun k _ hk => ⟨cycleNet_sc k, hk⟩) hl hl'
    le_rfl hfreq

/-- **Corollary 4.2, (ii) ⇒ (i), corrected (symmetric communications).** -/
theorem frequencyBasedFrom_three_of_computable_sizeLE_symmetric {f : List I → X}
    (h : ∀ B, Computable .symmetric (sizeLE B) (fun _ => True) f) : FrequencyBasedFrom 3 f := by
  intro l l' _ _ hl hl' hfreq
  obtain ⟨A, hA, hcomp⟩ := h (l.length * l'.length)
  exact eq_of_freq_eq_of_covers hA (sizeLE_isoClosed _) hcomp (fun k _ => ringNet k) 3
    (l.length * l'.length) (by norm_num) (fun k n _ _ h => ringFib h) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ h => ringFib_compatible h _) (fun k _ => ringNet_symmetric k)
    (fun k _ hk => ⟨ringNet_sc k, hk⟩) hl hl' le_rfl hfreq

end Podc.KnowYourAudience

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset

universe u' v'

variable {I : Type u'} [DecidableEq I] {X : Type v'} [TopologicalSpace X] [T2Space X]

omit [DecidableEq I] in
/-- Lemma 3.3 for a class containing the rings: computable ⇒ multiset-based. -/
theorem multisetBased_of_computes_rings {m : CommModel} {C : NetClass} {f : List I → X}
    {A : Algorithm I X} (hA : m.Allowed A) (hCiso : IsoClosed C)
    (hcomp : Computes m C (fun _ => True) f A) (hC : ∀ (k : ℕ) [NeZero k], C k (ringNet k)) :
    MultisetBased f := by
  intro l l' hperm
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · rw [List.length_eq_zero_iff] at h0
    subst h0
    rw [List.nil_perm.1 hperm]
  have : NeZero l.length := ⟨by omega⟩
  have hok : m.NetOK (ringNet l.length) := by
    cases m
    all_goals first | trivial | exact ringNet_symmetric _
  exact (hcomp.perm_eq hA hCiso hpos (hC _) hok rfl hperm trivial trivial).symm

omit [DecidableEq I] in
/-- A function computable in static strongly connected networks is multiset-based (Lemma 3.3). -/
theorem multisetBased_of_computable {m : CommModel} {f : List I → X}
    (h : Computable m staticSC (fun _ => True) f) : MultisetBased f := by
  obtain ⟨A, hA, hcomp⟩ := h
  exact multisetBased_of_computes_rings hA staticSC_isoClosed hcomp (fun k _ => ringNet_sc k)

omit [DecidableEq I] in
/-- **Corollary 4.3, (ii) ⇒ (i).** -/
theorem multisetBased_of_computable_sizeEq {m : CommModel} {f : List I → X}
    (h : ∀ k, Computable m (sizeEq k) (fun _ => True) f) : MultisetBased f := by
  intro l l' hperm
  obtain ⟨A, hA, hcomp⟩ := h l.length
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · rw [List.length_eq_zero_iff] at h0
    subst h0
    rw [List.nil_perm.1 hperm]
  have : NeZero l.length := ⟨by omega⟩
  have hok : m.NetOK (ringNet l.length) := by
    cases m
    all_goals first | trivial | exact ringNet_symmetric _
  exact (hcomp.perm_eq hA (sizeEq_isoClosed _) hpos ⟨ringNet_sc _, rfl⟩ hok rfl hperm trivial
    trivial).symm

omit [DecidableEq I] in
/-- Inputs with exactly one leader. -/
def OneLeader (l : List (I × Bool)) : Prop := l.countP (fun p => p.2) = 1

/-- **Corollary 4.4, (ii) ⇒ (i).** If `f` (of the non-leader components) is computable with one
leader, it is multiset-based. -/
theorem multisetBased_of_computable_leader {m : CommModel} {f : List I → X}
    (h : Computable m staticSC OneLeader (fun l => f (l.map Prod.fst))) : MultisetBased f := by
  obtain ⟨A, hA, hcomp⟩ := h
  intro l l' hperm
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · rw [List.length_eq_zero_iff] at h0
    subst h0
    rw [List.nil_perm.1 hperm]
  have : NeZero l.length := ⟨by omega⟩
  obtain ⟨σ, hσ⟩ := exists_equiv_ofFn_comp_eq l.get (l' := l') (by rw [List.ofFn_get]; exact hperm)
  let c : Fin l.length := σ ⟨0, hpos⟩
  let L : Fin l.length → I × Bool := fun i => (l.get i, decide (i = c))
  have hL : OneLeader (List.ofFn L) := by
    unfold OneLeader
    have h1 : (List.ofFn L).countP (fun p => p.2) =
        (List.ofFn (fun i => decide (i = c))).count true := by
      have : (List.ofFn (fun i => decide (i = c))) = (List.ofFn L).map Prod.snd := by
        rw [List.map_ofFn]; rfl
      rw [this, List.count, List.countP_map]
      congr 1
    rw [h1, count_ofFn]
    simp [Finset.filter_eq']
  have hperm' : (List.ofFn (L ∘ σ)).Perm (List.ofFn L) := Equiv.Perm.ofFn_comp_perm σ L
  have hL' : OneLeader (List.ofFn (L ∘ σ)) := by
    unfold OneLeader; rw [hperm'.countP_eq]; exact hL
  have hok : m.NetOK (ringNet l.length) := by
    cases m
    all_goals first | trivial | exact ringNet_symmetric _
  have := hcomp.perm_eq hA staticSC_isoClosed hpos (ringNet_sc _) hok List.length_ofFn hperm'.symm
    hL hL'
  simp only [List.map_ofFn] at this
  have e1 : (Prod.fst ∘ L) = l.get := rfl
  have e2 : Prod.fst ∘ (L ∘ σ) = l.get ∘ σ := rfl
  rw [e1, e2, hσ, List.ofFn_get] at this
  exact this.symm

end Podc.KnowYourAudience
