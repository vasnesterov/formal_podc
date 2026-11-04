import Papers.PODC2013.EarlyDecidingExpensive.Model
import Papers.PODC2013.EarlyDecidingExpensive.Combinatorics

/-!
# Critical pairs of executions (Dolev–Lenzen, PODC 2013, Definition 3.3, Lemmas 3.4, 3.5,
Theorem 3.6)

* `IsCritical A Adm r E₀ E₁ v b`: Definition 3.3, with the output of `E₀` a parameter `b` (the
  paper has `b = 0`; `IsCritical.swap` exchanges the roles, so this is only a relabelling).
* `exists_critical_one`: Lemma 3.4 (for every fault class containing the fault-free executions).
* `pivot E₀ E₁ v r W` (the paper's `E(W)`): the critical node `v` turns Byzantine in round `r`
  and shows `E₀` to the nodes of `W` and `E₁` to the others in rounds `r` and `r + 1`.
* `lemma_3_5`, `theorem_3_6`.
-/

namespace Podc.EarlyDecidingExpensive

open Finset

variable {V M : Type*} [DecidableEq V] {A : Algorithm V M}

/-- All never-faulty nodes of `E` decide `b`. -/
def Out (A : Algorithm V M) (E : Execution V M) (b : Bool) : Prop := ∀ q ∉ E.F, Decides A E q b

lemma Correct.out_not {Adm : Execution V M → Prop} (hA : Correct A Adm) {E : Execution V M}
    (hE : Adm E) {b : Bool} (h : ¬ Out A E b) : Out A E (!b) := by
  simp only [Out, not_forall] at h
  obtain ⟨q, hq, hd⟩ := h
  intro q' hq'
  exact hA.decides_of_decides hE hq hq' (hA.decides_not hE hq hd)

lemma Out.not_not {E : Execution V M} {b : Bool} (h : Out A E b) (h' : Out A E (!b)) {q : V}
    (hq : q ∉ E.F) : False := by
  have := (h q hq).unique (h' q hq)
  cases b <;> simp at this

/-- Definition 3.3 (critical pairs), with the output `b` of `E₀` as a parameter (the paper:
`b = 0`). `E₀` and `E₁` are admissible executions with the same `r - 1` faulty nodes, all
faulty before round `r` and silent after round `r`; before round `r` only the messages received
by the critical node `v` differ, and in round `r` only messages involving `v`; the never-faulty
nodes decide `b` in `E₀` and `!b` in `E₁`. -/
structure IsCritical (A : Algorithm V M) (Adm : Execution V M → Prop) (r : ℕ)
    (E₀ E₁ : Execution V M) (v : V) (b : Bool) : Prop where
  adm₀ : Adm E₀
  adm₁ : Adm E₁
  F_eq : E₁.F = E₀.F
  fr_eq : ∀ p ∈ E₀.F, E₁.fr p = E₀.fr p
  card : E₀.F.card = r - 1
  fr_lt : ∀ p ∈ E₀.F, E₀.fr p < r
  not_mem : v ∉ E₀.F
  input_eq : ∀ q, q ≠ v → E₁.input q = E₀.input q
  msg_eq : ∀ k, 1 ≤ k → k ≤ r → ∀ p q, q ≠ v → (p ≠ v ∨ k < r) →
    msg A E₁ k p q = msg A E₀ k p q
  silent₀ : ∀ p ∈ E₀.F, ∀ k, r < k → ∀ q, msg A E₀ k p q = none
  silent₁ : ∀ p ∈ E₀.F, ∀ k, r < k → ∀ q, msg A E₁ k p q = none
  out₀ : Out A E₀ b
  out₁ : Out A E₁ (!b)

namespace IsCritical

variable {Adm : Execution V M → Prop} {r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

/-- Exchanging the two executions of a critical pair. -/
lemma swap (h : IsCritical A Adm r E₀ E₁ v b) : IsCritical A Adm r E₁ E₀ v (!b) where
  adm₀ := h.adm₁
  adm₁ := h.adm₀
  F_eq := h.F_eq.symm
  fr_eq p hp := (h.fr_eq p (h.F_eq ▸ hp)).symm
  card := h.F_eq ▸ h.card
  fr_lt p hp := by rw [h.fr_eq p (h.F_eq ▸ hp)]; exact h.fr_lt p (h.F_eq ▸ hp)
  not_mem := h.F_eq ▸ h.not_mem
  input_eq q hq := (h.input_eq q hq).symm
  msg_eq k hk1 hk2 p q hq hp := (h.msg_eq k hk1 hk2 p q hq hp).symm
  silent₀ p hp := h.silent₁ p (h.F_eq ▸ hp)
  silent₁ p hp := h.silent₀ p (h.F_eq ▸ hp)
  out₀ := h.out₁
  out₁ := by simpa using h.out₀

/-- Before round `r`, the nodes other than `v` cannot distinguish `E₀` and `E₁`. -/
lemma hist_eq (h : IsCritical A Adm r E₀ E₁ v b) {q : V} (hq : q ≠ v) :
    hist A E₁ (r - 1) q = hist A E₀ (r - 1) q :=
  hist_eq_iff.2 fun k hk1 hk2 p => h.msg_eq k hk1 (by omega) p q hq (Or.inr (by omega))

lemma faultyAt_iff (h : IsCritical A Adm r E₀ E₁ v b) (k : ℕ) (p : V) :
    E₁.FaultyAt k p ↔ E₀.FaultyAt k p := by
  simp only [Execution.FaultyAt, h.F_eq]
  constructor
  · rintro ⟨hp, hk⟩; exact ⟨hp, h.fr_eq p hp ▸ hk⟩
  · rintro ⟨hp, hk⟩; exact ⟨hp, (h.fr_eq p hp).symm ▸ hk⟩

end IsCritical

/-! ### Lemma 3.4 -/

/-- The fault-free execution with inputs `x`. -/
def faultFree (x : V → Bool) : Execution V M := ⟨x, ∅, fun _ => 0, fun _ _ _ => none⟩

/-- **Lemma 3.4.** Every binary consensus algorithm has a `1`-critical pair (of fault-free
executions whose inputs differ at one node), for every fault class containing the fault-free
executions. -/
theorem exists_critical_one [Fintype V] [Nonempty V] {Adm : Execution V M → Prop}
    (hA : Correct A Adm) (hAdm : ∀ x, Adm (faultFree x)) :
    ∃ E₀ E₁ v, IsCritical A Adm 1 E₀ E₁ v false := by
  let E : Finset V → Execution V M := fun S => faultFree fun p => decide (p ∈ S)
  have hval : ∀ S b, Out A (E S) b → ∃ p, decide (p ∈ S) = b := by
    intro S b h
    obtain ⟨q⟩ := ‹Nonempty V›
    exact hA.validity _ (hAdm _) q (by simp [E, faultFree]) b (h q (by simp [E, faultFree]))
  have h0 : ¬ Out A (E ∅) true := fun h => by simpa using hval ∅ true h
  have h1 : Out A (E univ) true := by
    by_contra h
    simpa using hval univ false (hA.out_not (hAdm _) h)
  obtain ⟨W, v, -, -, -, hvW, hW, hW'⟩ :=
    exists_flip (fun S => ¬ Out A (E S) true) (empty_subset univ) h0 (by simpa using h1)
  have hW0 : Out A (E W) false := hA.out_not (hAdm _) hW
  refine ⟨E W, E (insert v W), v, ?_⟩
  exact {
    adm₀ := hAdm _
    adm₁ := hAdm _
    F_eq := rfl
    fr_eq := fun _ _ => rfl
    card := rfl
    fr_lt := by simp [E, faultFree]
    not_mem := by simp [E, faultFree]
    input_eq := fun q hq => by simp [E, faultFree, hq]
    msg_eq := by
      intro k hk1 hk2 p q hq hp
      obtain rfl : k = 1 := by omega
      have hp : p ≠ v := hp.resolve_right (by omega)
      exact msg_congr (E := E (insert v W)) (E' := E W) (k := 1) (p := p)
        (by simp [Execution.FaultyAt, E, faultFree])
        (by simp [Execution.FaultyAt, E, faultFree]) (by simp [E, faultFree, hp]) rfl q
    silent₀ := by simp [E, faultFree]
    silent₁ := by simp [E, faultFree]
    out₀ := hW0
    out₁ := by simpa using hW' }

/-! ### The executions `E(W)` of Lemma 3.5 -/

/-- The paper's `E(W)`: built on `E₀`, the critical node `v` is Byzantine from round `r` on; in
rounds `r` and `r + 1` it sends to the nodes of `W` what it sends in `E₀` and to the others what
it sends in `E₁`; later it is silent. -/
def pivot (A : Algorithm V M) (E₀ E₁ : Execution V M) (v : V) (r : ℕ) (W : Finset V) :
    Execution V M :=
  addFaults E₀ {v} r fun k _ q =>
    if k = r ∨ k = r + 1 then (if q ∈ W then msg A E₀ k v q else msg A E₁ k v q) else none

section Pivot

variable {Adm : Execution V M → Prop} {r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}
  (h : IsCritical A Adm r E₀ E₁ v b) (W : Finset V)
include h

lemma pivot_disjoint : Disjoint E₀.F {v} := by simpa using h.not_mem

lemma card_pivot : (pivot A E₀ E₁ v r W).F.card = r - 1 + 1 := by
  rw [pivot, card_addFaults (pivot_disjoint h), h.card, card_singleton]

lemma pivot_msg_lt {k : ℕ} (hk1 : 1 ≤ k) (hk : k < r) (p q : V) :
    msg A (pivot A E₀ E₁ v r W) k p q = msg A E₀ k p q :=
  msg_addFaults_of_lt (pivot_disjoint h) hk1 hk p q

lemma pivot_hist_lt (q : V) : hist A (pivot A E₀ E₁ v r W) (r - 1) q = hist A E₀ (r - 1) q :=
  hist_addFaults_of_le (pivot_disjoint h) le_rfl q

lemma pivot_msg_r {p : V} (hp : p ≠ v) (q : V) :
    msg A (pivot A E₀ E₁ v r W) r p q = msg A E₀ r p q :=
  msg_addFaults_of_not_mem (pivot_disjoint h) le_rfl (by simpa using hp) q

lemma pivot_msg_v {k : ℕ} (hk : r ≤ k) {q : V} (hq : q ≠ v) :
    msg A (pivot A E₀ E₁ v r W) k v q =
      if k = r ∨ k = r + 1 then (if q ∈ W then msg A E₀ k v q else msg A E₁ k v q) else none :=
  msg_addFaults_of_mem hk (mem_singleton_self v) (Ne.symm hq)

/-- Faulty nodes other than `v` are silent after round `r` in `E(W)`. -/
lemma pivot_msg_F {k : ℕ} (hk : r < k) {p : V} (hp : p ∈ E₀.F) (q : V) :
    msg A (pivot A E₀ E₁ v r W) k p q = none := by
  by_cases hpq : p = q
  · subst hpq; exact msg_self _ _ _
  have hpv : p ≠ v := fun e => h.not_mem (e ▸ hp)
  have hf : E₀.FaultyAt k p := ⟨hp, (h.fr_lt p hp).le.trans hk.le⟩
  have hf' : (pivot A E₀ E₁ v r W).FaultyAt k p :=
    (faultyAt_addFaults_of_not_mem (by simpa using hpv)).2 hf
  rw [msg_of_faultyAt hf' hpq]
  have := h.silent₀ p hp k hk q
  rw [msg_of_faultyAt hf hpq] at this
  simp [pivot, addFaults, hpv, this]

/-- After round `r`, a node `q ≠ v` of `W` has the history it has in `E₀`. -/
lemma pivot_hist_r_mem {q : V} (hq : q ≠ v) (hqW : q ∈ W) (hr : 1 ≤ r) :
    hist A (pivot A E₀ E₁ v r W) r q = hist A E₀ r q := by
  refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
  rcases Nat.lt_or_ge k r with hk | hk
  · exact pivot_msg_lt h W hk1 hk p q
  obtain rfl : k = r := by omega
  by_cases hp : p = v
  · subst hp; rw [pivot_msg_v h W le_rfl hq]; simp [hqW]
  · exact pivot_msg_r h W hp q

/-- After round `r`, a node `q ≠ v` outside `W` has the history it has in `E₁`. -/
lemma pivot_hist_r_not_mem {q : V} (hq : q ≠ v) (hqW : q ∉ W) (hr : 1 ≤ r) :
    hist A (pivot A E₀ E₁ v r W) r q = hist A E₁ r q := by
  refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
  rcases Nat.lt_or_ge k r with hk | hk
  · rw [pivot_msg_lt h W hk1 hk p q, h.msg_eq k hk1 hk2 p q hq (Or.inr hk)]
  obtain rfl : k = r := by omega
  by_cases hp : p = v
  · subst hp; rw [pivot_msg_v h W le_rfl hq]; simp [hqW]
  · rw [pivot_msg_r h W hp q, h.msg_eq k hk1 hk2 p q hq (Or.inl hp)]

/-- In round `r + 1`, an honest node `p ≠ v` of `W` sends what it sends in `E₀`. -/
lemma pivot_msg_succ_mem {p : V} (hp : p ∉ E₀.F) (hpv : p ≠ v) (hpW : p ∈ W) (hr : 1 ≤ r)
    (q : V) : msg A (pivot A E₀ E₁ v r W) (r + 1) p q = msg A E₀ (r + 1) p q :=
  msg_congr (E := pivot A E₀ E₁ v r W) (E' := E₀) (k := r + 1)
    (by simp [pivot, Execution.FaultyAt, hp, hpv])
    (Execution.not_faultyAt_of_not_mem hp) rfl (pivot_hist_r_mem h W hpv hpW hr) q

/-- In round `r + 1`, an honest node `p ≠ v` outside `W` sends what it sends in `E₁`. -/
lemma pivot_msg_succ_not_mem {p : V} (hp : p ∉ E₀.F) (hpv : p ≠ v) (hpW : p ∉ W) (hr : 1 ≤ r)
    (q : V) : msg A (pivot A E₀ E₁ v r W) (r + 1) p q = msg A E₁ (r + 1) p q :=
  msg_congr (E := pivot A E₀ E₁ v r W) (E' := E₁) (k := r + 1)
    (by simp [pivot, Execution.FaultyAt, hp, hpv])
    (by rw [h.faultyAt_iff]; exact Execution.not_faultyAt_of_not_mem hp)
    (h.input_eq p hpv).symm (pivot_hist_r_not_mem h W hpv hpW hr) q

/-- If `W` contains all honest nodes, the honest nodes of `W` cannot distinguish `E(W)` from
`E₀` before round `r + 2`. -/
lemma pivot_hist_succ_E₀ (hW : ∀ p ∉ E₀.F, p ≠ v → p ∈ W) {q : V} (hq : q ∉ E₀.F)
    (hqv : q ≠ v) (hr : 1 ≤ r) :
    hist A (pivot A E₀ E₁ v r W) (r + 1) q = hist A E₀ (r + 1) q := by
  rw [hist_succ, hist_succ, pivot_hist_r_mem h W hqv (hW q hq hqv) hr]
  congr 2; funext p
  by_cases hpv : p = v
  · subst hpv; rw [pivot_msg_v h W (by omega) hqv]; simp [hW q hq hqv]
  by_cases hp : p ∈ E₀.F
  · rw [pivot_msg_F h W (by omega) hp, h.silent₀ p hp _ (by omega)]
  · exact pivot_msg_succ_mem h W hp hpv (hW p hp hpv) hr q

/-- `E(∅)` cannot be distinguished from `E₁` by honest nodes before round `r + 2`. -/
lemma pivot_empty_hist_succ {q : V} (hq : q ∉ E₀.F) (hqv : q ≠ v) (hr : 1 ≤ r) :
    hist A (pivot A E₀ E₁ v r ∅) (r + 1) q = hist A E₁ (r + 1) q := by
  rw [hist_succ, hist_succ, pivot_hist_r_not_mem h ∅ hqv ((by simp)) hr]
  congr 2; funext p
  by_cases hpv : p = v
  · subst hpv; rw [pivot_msg_v h ∅ (by omega) hqv]; simp
  by_cases hp : p ∈ E₀.F
  · rw [pivot_msg_F h ∅ (by omega) hp, h.silent₁ p hp _ (by omega)]
  · exact pivot_msg_succ_not_mem h ∅ hp hpv ((by simp)) hr q

end Pivot

/-! ### Lemma 3.5 -/

/-- Transfer of a decision from an execution with a decision deadline. -/
lemma decidedBy_of_hist {Adm : Execution V M → Prop} {f D : ℕ} (hd : DecidingAt A Adm f D)
    {E E' : Execution V M} (hE : Adm E) (hc : E.F.card = f) {b : Bool} (hout : Out A E b)
    {q : V} (hq : q ∉ E.F) (hx : E.input q = E'.input q) (hh : hist A E D q = hist A E' D q) :
    DecidedBy A E' q D b := by
  obtain ⟨c, hcd⟩ := hd E hE hc q hq
  obtain rfl : c = b := hcd.decides.unique (hout q hq)
  exact hcd.transfer hx hh

section Lemma35

variable {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

lemma pivot_fr (W : Finset V) (p : V) :
    (pivot A E₀ E₁ v r W).fr p = if p = v then r else E₀.fr p := by
  simp [pivot, addFaults]

/-- In rounds `≤ r`, `E(W)` and `E(W ∪ {v'})` differ only in what `v'` receives. -/
lemma pivot_msg_insert_le {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b)
    (W : Finset V) {v' : V} {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ r) (p : V) {q : V} (hq : q ≠ v') :
    msg A (pivot A E₀ E₁ v r W) k p q = msg A (pivot A E₀ E₁ v r (insert v' W)) k p q := by
  rcases Nat.lt_or_ge k r with hk' | hk'
  · rw [pivot_msg_lt h W hk1 hk' p q, pivot_msg_lt h _ hk1 hk' p q]
  obtain rfl : k = r := by omega
  by_cases hpv : p = v
  · subst hpv
    by_cases hqv : q = p
    · subst hqv; simp [msg_self]
    rw [pivot_msg_v h W le_rfl hqv, pivot_msg_v h _ le_rfl hqv]
    simp [hq]
  · rw [pivot_msg_r h W hpv q, pivot_msg_r h _ hpv q]

lemma pivot_hist_insert {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b)
    (W : Finset V) {v' q : V} (hq : q ≠ v') :
    hist A (pivot A E₀ E₁ v r W) r q = hist A (pivot A E₀ E₁ v r (insert v' W)) r q :=
  hist_eq_iff.2 fun k hk1 hk p => pivot_msg_insert_le h W hk1 hk p hq

/-- `E(W ∪ {v'})` and `E(W)` form an `(r+1)`-critical pair as soon as their outputs differ. -/
lemma pivot_isCritical (h : IsCritical A (byzAdm t) r E₀ E₁ v b) (hr : 1 ≤ r) (hrt : r ≤ t)
    {W : Finset V} {v' : V} (hv'F : v' ∉ E₀.F) (hv'v : v' ≠ v)
    (h₀ : Out A (pivot A E₀ E₁ v r (insert v' W)) b) (h₁ : Out A (pivot A E₀ E₁ v r W) (!b)) :
    IsCritical A (byzAdm t) (r + 1) (pivot A E₀ E₁ v r (insert v' W)) (pivot A E₀ E₁ v r W)
      v' b where
  adm₀ := by simp only [byzAdm, card_pivot h]; omega
  adm₁ := by simp only [byzAdm, card_pivot h]; omega
  F_eq := rfl
  fr_eq _ _ := rfl
  card := by rw [card_pivot h]; omega
  fr_lt p hp := by
    rw [pivot_fr]
    split_ifs with hpv
    · omega
    · simp only [pivot, addFaults_F, mem_union, mem_singleton, hpv, or_false] at hp
      have := h.fr_lt p hp; omega
  not_mem := by simp [pivot, hv'F, hv'v]
  input_eq _ _ := rfl
  msg_eq k hk1 hk2 p q hq hp := by
    rcases Nat.lt_or_ge k (r + 1) with hk | hk
    · exact pivot_msg_insert_le h W hk1 (by omega) p hq
    obtain rfl : k = r + 1 := by omega
    have hp : p ≠ v' := hp.resolve_right (by omega)
    by_cases hpv : p = v
    · subst hpv
      by_cases hqv : q = p
      · subst hqv; simp [msg_self]
      rw [pivot_msg_v h W (by omega) hqv, pivot_msg_v h _ (by omega) hqv]
      simp [hq]
    by_cases hpF : p ∈ E₀.F
    · rw [pivot_msg_F h W (by omega) hpF, pivot_msg_F h _ (by omega) hpF]
    · exact msg_congr (E := pivot A E₀ E₁ v r W) (E' := pivot A E₀ E₁ v r (insert v' W))
        (k := r + 1) (p := p) (by simp [pivot, Execution.FaultyAt, hpF, hpv])
        (by simp [pivot, Execution.FaultyAt, hpF, hpv]) rfl (pivot_hist_insert h W hp) q
  silent₀ p hp k hk q := by
    simp only [pivot, addFaults_F, mem_union, mem_singleton] at hp
    rcases hp with hp | rfl
    · exact pivot_msg_F h _ (by omega) hp q
    · by_cases hqv : q = p
      · subst hqv; simp [msg_self]
      rw [pivot_msg_v h _ (by omega) hqv, if_neg (by omega)]
  silent₁ p hp k hk q := by
    simp only [pivot, addFaults_F, mem_union, mem_singleton] at hp
    rcases hp with hp | rfl
    · exact pivot_msg_F h _ (by omega) hp q
    · by_cases hqv : q = p
      · subst hqv; simp [msg_self]
      rw [pivot_msg_v h _ (by omega) hqv, if_neg (by omega)]
  out₀ := h₀
  out₁ := h₁

variable [Fintype V]

/-- The non-faulty nodes of `E(W)`. -/
def honest (E₀ : Execution V M) (v : V) : Finset V := univ.filter fun p => p ∉ E₀.F ∧ p ≠ v

lemma mem_honest {E₀ : Execution V M} {v p : V} : p ∈ honest E₀ v ↔ p ∉ E₀.F ∧ p ≠ v := by
  simp [honest]

lemma not_mem_pivot_F {E₀ : Execution V M} {v p : V} {W : Finset V} :
    p ∉ (pivot A E₀ E₁ v r W).F ↔ p ∈ honest E₀ v := by
  simp [pivot, honest, and_comm]

lemma card_honest {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b) (hr : 1 ≤ r) :
    (honest E₀ v).card = Fintype.card V - r := by
  have : honest E₀ v = univ \ (E₀.F ∪ {v}) := by ext p; simp [honest, and_comm]
  rw [this, card_sdiff_of_subset (subset_univ _), card_univ,
    card_union_of_disjoint (pivot_disjoint h), h.card, card_singleton]
  omega

/-- `E(V \ F_r)` outputs the output of `E₀` (honest nodes cannot distinguish them before round
`r + 2`, and `E₀` has decided by then). -/
lemma out_pivot_honest (h : IsCritical A (byzAdm t) r E₀ E₁ v b) (hr : 1 ≤ r)
    (hd : DecidingAt A (byzAdm t) (r - 1) (r + 1)) :
    Out A (pivot A E₀ E₁ v r (honest E₀ v)) b := by
  intro q hq
  rw [not_mem_pivot_F, mem_honest] at hq
  exact (decidedBy_of_hist (E' := pivot A E₀ E₁ v r (honest E₀ v)) hd h.adm₀ h.card h.out₀ hq.1 rfl
    (pivot_hist_succ_E₀ h _ (fun p hp hpv => mem_honest.2 ⟨hp, hpv⟩) hq.1 hq.2 hr).symm).decides

/-- `E(∅)` outputs the output of `E₁`. -/
lemma out_pivot_empty (h : IsCritical A (byzAdm t) r E₀ E₁ v b) (hr : 1 ≤ r)
    (hd : DecidingAt A (byzAdm t) (r - 1) (r + 1)) :
    Out A (pivot A E₀ E₁ v r ∅) (!b) := by
  intro q hq
  rw [not_mem_pivot_F, mem_honest] at hq
  exact (decidedBy_of_hist (E' := pivot A E₀ E₁ v r ∅) hd h.adm₁ (h.F_eq ▸ h.card) h.out₁
    (h.F_eq ▸ hq.1)
    (h.input_eq q hq.2) (pivot_empty_hist_succ h hq.1 hq.2 hr).symm).decides

/-- The chain step of Lemmas 3.5 and 3.8: if `E(W₀)` outputs `!b`, then adding honest nodes to
`W₀` one by one yields an `(r+1)`-critical pair `E(W ∪ {v'}), E(W)` with `W₀ ⊆ W`. -/
lemma exists_pivot_isCritical (hA : Correct A (byzAdm t))
    (h : IsCritical A (byzAdm t) r E₀ E₁ v b) (hr : 1 ≤ r) (hrt : r ≤ t)
    (hn : r < Fintype.card V) (hd : DecidingAt A (byzAdm t) (r - 1) (r + 1))
    {W₀ : Finset V} (hW₀ : W₀ ⊆ honest E₀ v) (hout : Out A (pivot A E₀ E₁ v r W₀) (!b)) :
    ∃ W v', W₀ ⊆ W ∧ W ⊆ honest E₀ v ∧ v' ∈ honest E₀ v ∧ v' ∉ W ∧
      IsCritical A (byzAdm t) (r + 1) (pivot A E₀ E₁ v r (insert v' W))
        (pivot A E₀ E₁ v r W) v' b := by
  have hadm : ∀ W, byzAdm t (pivot A E₀ E₁ v r W) := fun W => by
    simp only [byzAdm, card_pivot h]; omega
  obtain ⟨q, hq⟩ : (honest E₀ v).Nonempty := by
    rw [← card_pos, card_honest h hr]; omega
  have hnot : ¬ Out A (pivot A E₀ E₁ v r (honest E₀ v)) (!b) := fun h' =>
    (out_pivot_honest h hr hd).not_not (by simpa using h') (not_mem_pivot_F.2 hq)
  obtain ⟨W, v', hW₀W, hW, hv', hv'W, hg, hg'⟩ := exists_flip (fun W => Out A (pivot A E₀ E₁ v r W) (!b)) hW₀ hout hnot
  refine ⟨W, v', hW₀W, hW, hv', hv'W, ?_⟩
  have hv'' := mem_honest.1 hv'
  exact pivot_isCritical h hr hrt hv''.1 hv''.2 (by simpa using hA.out_not (hadm _) hg') hg

/-- **Lemma 3.5.** For a correct algorithm whose executions with `r - 1` Byzantine faults decide
within `r + 1` rounds (the paper's `(f+2)`-deciding assumption, written "`(f+1)`-deciding" in the
proof), an `r`-critical pair (`1 ≤ r ≤ t`) yields an `(r+1)`-critical pair. -/
theorem lemma_3_5 (hA : Correct A (byzAdm t)) (hr : 1 ≤ r) (hrt : r ≤ t)
    (hn : r < Fintype.card V) (hd : DecidingAt A (byzAdm t) (r - 1) (r + 1))
    (h : IsCritical A (byzAdm t) r E₀ E₁ v false) :
    ∃ E₀' E₁' v', IsCritical A (byzAdm t) (r + 1) E₀' E₁' v' false := by
  obtain ⟨W, v', -, -, -, -, hc⟩ :=
    exists_pivot_isCritical hA h hr hrt hn hd (empty_subset _) (out_pivot_empty h hr hd)
  exact ⟨_, _, _, hc⟩

end Lemma35

/-! ### Theorem 3.6 -/

/-- Iterating Lemma 3.5 from Lemma 3.4: an `(f+1)`-critical pair exists if the algorithm decides
within `f' + 2` rounds whenever there are `f' < f` faults. -/
theorem exists_critical [Fintype V] {t : ℕ} (hA : Correct A (byzAdm t)) {f : ℕ}
    (hft : f ≤ t) (hn : f < Fintype.card V)
    (hd : ∀ f' < f, DecidingAt A (byzAdm t) f' (f' + 2)) :
    ∃ E₀ E₁ v, IsCritical A (byzAdm t) (f + 1) E₀ E₁ v false := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  induction f with
  | zero => exact exists_critical_one hA fun x => by simp [byzAdm, faultFree]
  | succ f ih =>
    obtain ⟨E₀, E₁, v, h⟩ := ih (by omega) (by omega) fun f' hf' => hd f' (by omega)
    exact lemma_3_5 hA (by omega) hft hn (by simpa using hd f (by omega)) h

/-- **Theorem 3.6.** Let `A` be a binary consensus algorithm tolerating `t` Byzantine faults,
`n > 3t`, and `0 ≤ f ≤ t - 1`. If `A` decides within `f' + 2` rounds in executions with `f' < f`
faults (this is how the paper's proof uses Lemma 3.5; vacuous for `f = 0`), then some execution
with exactly `f` faults has a never-faulty node that has not decided within `f + 1` rounds, i.e.
decides in round `f + 2` or later. -/
theorem theorem_3_6 [Fintype V] {t : ℕ} (hnt : 3 * t < Fintype.card V)
    (hA : Correct A (byzAdm t)) {f : ℕ} (hft : f + 1 ≤ t)
    (hd : ∀ f' < f, DecidingAt A (byzAdm t) f' (f' + 2)) :
    ∃ E, byzAdm t E ∧ E.F.card = f ∧ ∃ q ∉ E.F, ∀ b, ¬ DecidedBy A E q (f + 1) b := by
  by_contra hcon
  push Not at hcon
  have hfast : DecidingAt A (byzAdm t) f (f + 1) := fun E hE hc q hq => hcon E hE hc q hq
  obtain ⟨E₀, E₁, v, h⟩ := exists_critical hA (by omega) (by omega) hd
  have hr : 1 ≤ f + 1 := by omega
  obtain ⟨w, hw, u, hu, hwu⟩ := Finset.one_lt_card.1 (show 1 < (honest E₀ v).card by
    rw [card_honest h hr]; omega)
  have hw' := mem_honest.1 hw
  have hu' := mem_honest.1 hu
  let E := pivot A E₀ E₁ v (f + 1) {w}
  have hE : byzAdm t E := by simp only [E, byzAdm, card_pivot h]; omega
  have hc : E₀.F.card = f := by rw [h.card]; rfl
  have h0 : DecidedBy A E w (f + 1) false :=
    decidedBy_of_hist hfast h.adm₀ hc h.out₀ hw'.1 rfl
      (pivot_hist_r_mem h {w} hw'.2 (mem_singleton_self w) hr).symm
  have h1 : DecidedBy A E u (f + 1) true :=
    decidedBy_of_hist hfast h.adm₁ (h.F_eq ▸ hc) h.out₁ (h.F_eq ▸ hu'.1) (h.input_eq u hu'.2)
      (pivot_hist_r_not_mem h {w} hu'.2 (by simpa using hwu.symm) hr).symm
  have := hA.agreement E hE w (not_mem_pivot_F.2 hw) u (not_mem_pivot_F.2 hu) _ _ h0.decides
    h1.decides
  simp at this

end Podc.EarlyDecidingExpensive
