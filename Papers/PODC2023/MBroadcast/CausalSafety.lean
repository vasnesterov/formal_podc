import Papers.PODC2023.MBroadcast.CausalInv

/-!
# Algorithm 2: safety (Theorem 1, safety part)

For every reachable configuration of Algorithm 2 (any number of crashes), the MBroadcast trace
satisfies Validity, No-duplication and the paper's assumption that all messages are different
(`UniqueBc`); if moreover `2t < n`, it satisfies Mutual ordering (in the strong reading
`Spec.MutualOrdering`).

Proof of mutual ordering. Suppose `p ≠ p'`, `p` mdelivers its own `m` (position `i`) before
having mdelivered `m'`, and `p'` mdelivers its own `m'` (position `i'`) before having mdelivered
`m`. The quorums `{p} ∪ A` and `{p'} ∪ A'` of the acknowledgements received by `p` and `p'`
have `≥ n - t` elements each, so they intersect (`2(n - t) > n`) in some `k`.
* `k = p ∈ A'` (or symmetrically `k = p' ∈ A`): `p` sent `ack(m')` (id `y'`) to `p'` and
  `init(m)` (id `x`). If `x < y'`, then `x ∈ dep(y')`, so by causal delivery `p'` received
  `init(m)` (and mdelivered `m`) before receiving `y'`, hence before `i'`. If `y' < x`, `p`
  mdelivered `m'` right after sending `y'`, before `x < i`.
* `k ∈ A ∩ A'`: `k` sent `ack(m)` (id `y`) and `ack(m')` (id `y'`), each right after receiving
  the corresponding `init`. If `y < y'`, the `init(m)` received by `k` is in `dep(y')`, so `p'`
  received it, and mdelivered `m`, before receiving `y'`; symmetrically if `y' < y`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Causal

open Finset

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]

section LogLevel

variable {t : ℕ} {C : Cfg P M}

/-- If `q` receives (at position `w`) a message whose causal past contains an `init(m)` of
which `q` is a destination, then `q` has mdelivered `m` before `w`. -/
lemma Inv.dl_before_of_dep (I : Inv t C) {q : P} {w y x : ℕ} {r r0 : Rec P M} {m : M}
    (hw : C.log[w]? = some (.rcv q y)) (hy : C.log[y]? = some (.snd r)) (hx : x ∈ r.dep)
    (hx0 : C.log[x]? = some (.snd r0)) (hb : r0.body = .init m) (hq : q ∈ r0.dst) :
    ∃ j < w, C.log[j]? = some (.mb (.dl q r0.src m)) := by
  obtain ⟨r', hr', -, -, hc⟩ := I.rcv w q y hw
  rw [hy] at hr'; cases hr'
  obtain ⟨w', hw', h'⟩ := hc x hx r0 hx0 hq
  obtain ⟨r1, h1, -, -, -, h2⟩ := I.hdl w' q x r0 m h' hx0 hb
  refine ⟨w' + 2, ?_, h2⟩
  have : w ≠ w' + 1 := by rintro rfl; rw [hw] at h1; cases h1
  have : w ≠ w' + 2 := by rintro rfl; rw [hw] at h2; cases h2
  omega

/-- Case `k = p` of the quorum intersection: `p` acknowledged `m'` to `p'`. -/
lemma Inv.mutual_self (I : Inv t C) {p p' : P} {m m' : M} {i i' : ℕ}
    (hinit : InitSent C.log p m i) (hack : AckRcvd C.log p' m' p i')
    (hi : ∀ j < i, C.log[j]? ≠ some (.mb (.dl p p' m')))
    (hi' : ∀ j < i', C.log[j]? ≠ some (.mb (.dl p' p m))) (hne : p ≠ p') : False := by
  obtain ⟨x, hxi, r0, hx, hsrc0, hb0⟩ := hinit
  obtain ⟨w', hw'i, y', r', hw', hy', hsrc', hb'⟩ := hack
  obtain ⟨z', x', r0', rfl, -, -, -, hdst', -, hdl'⟩ := I.ack y' r' m' hy' hb'
  obtain ⟨r'', hr'', -, hp', -⟩ := I.rcv w' p' (z' + 1) hw'
  rw [hy'] at hr''; cases hr''
  rw [hdst', mem_singleton] at hp'
  rw [← hp', hsrc'] at hdl'
  rcases lt_trichotomy x (z' + 1) with hlt | heq | hgt
  · have hdep := (I.dep (z' + 1) r' hy').1 x hlt r0 hx (hsrc0.trans hsrc'.symm)
    have hdst0 := (I.init x r0 m hx hb0).1
    obtain ⟨j, hj, hj'⟩ := I.dl_before_of_dep hw' hy' hdep hx hb0
      (by rw [hdst0, mem_erase, hsrc0]; exact ⟨fun h => hne h.symm, mem_univ _⟩)
    rw [hsrc0] at hj'
    exact hi' j (by omega) hj'
  · subst heq; rw [hy'] at hx; cases hx; rw [hb0] at hb'; cases hb'
  · have : z' + 2 ≠ x := by intro h; rw [h, hx] at hdl'; cases hdl'
    exact hi (z' + 2) (by omega) hdl'

/-- Case `k ∈ A ∩ A'`, `k` acknowledged `m` before `m'`. -/
lemma Inv.mutual_other (I : Inv t C) {p p' k : P} {m : M} {i' w w' y y' : ℕ}
    {r r' : Rec P M} (hw : C.log[w]? = some (.rcv p y)) (hy : C.log[y]? = some (.snd r))
    (hsrc : r.src = k) (hb : r.body = .ack m)
    (hw' : C.log[w']? = some (.rcv p' y')) (hy' : C.log[y']? = some (.snd r'))
    (hsrc' : r'.src = k) (hw'i : w' < i') (hlt : y < y')
    (hi' : ∀ j < i', C.log[j]? ≠ some (.mb (.dl p' p m))) (hne : p ≠ p') : False := by
  obtain ⟨z, x, r0, rfl, hz, hx, hb0, hdst, -, -⟩ := I.ack y r m hy hb
  obtain ⟨r'', hr'', -, hp, -⟩ := I.rcv w p (z + 1) hw
  rw [hy] at hr''; cases hr''
  rw [hdst, mem_singleton] at hp
  have hdep := (I.dep y' r' hy').2 z (by omega) x (by rw [hsrc', ← hsrc]; exact hz)
  have hdst0 := (I.init x r0 m hx hb0).1
  obtain ⟨j, hj, hj'⟩ := I.dl_before_of_dep hw' hy' hdep hx hb0
    (by rw [hdst0, mem_erase, ← hp]; exact ⟨fun h => hne h.symm, mem_univ _⟩)
  rw [← hp] at hj'
  exact hi' j (by omega) hj'

/-- **Mutual ordering, at the level of the global log.** -/
theorem Inv.mutual (I : Inv t C) (h2t : 2 * t < Fintype.card P) {p p' : P} {m m' : M}
    {i i' : ℕ} (hne : p ≠ p') (hi : C.log[i]? = some (.mb (.dl p p m)))
    (hni : ∀ j < i, C.log[j]? ≠ some (.mb (.dl p p' m')))
    (hi' : C.log[i']? = some (.mb (.dl p' p' m')))
    (hni' : ∀ j < i', C.log[j]? ≠ some (.mb (.dl p' p m))) : False := by
  rcases I.dl i p p m hi with ⟨-, hinit, A, hpA, hA, hAck⟩ | ⟨h, -⟩
  swap; · exact h rfl
  rcases I.dl i' p' p' m' hi' with ⟨-, hinit', A', hpA', hA', hAck'⟩ | ⟨h, -⟩
  swap; · exact h rfl
  -- quorum intersection
  have hc1 : (insert p A).card = A.card + 1 := card_insert_of_notMem hpA
  have hc2 : (insert p' A').card = A'.card + 1 := card_insert_of_notMem hpA'
  have hu := card_union_add_card_inter (insert p A) (insert p' A')
  have hun : (insert p A ∪ insert p' A').card ≤ Fintype.card P := card_le_univ _
  obtain ⟨k, hk⟩ : (insert p A ∩ insert p' A').Nonempty := by
    rw [← card_pos]; omega
  rw [mem_inter, mem_insert, mem_insert] at hk
  obtain ⟨hk1 | hk1, hk2 | hk2⟩ := hk
  · subst hk1; exact hne hk2
  · subst hk1; exact I.mutual_self hinit (hAck' k hk2) hni hni' hne
  · subst hk2; exact I.mutual_self hinit' (hAck k hk1) hni' hni (Ne.symm hne)
  · obtain ⟨w, hwi, y, r, hw, hy, hsrc, hb⟩ := hAck k hk1
    obtain ⟨w', hw'i, y', r', hw', hy', hsrc', hb'⟩ := hAck' k hk2
    rcases lt_trichotomy y y' with hlt | heq | hgt
    · exact I.mutual_other hw hy hsrc hb hw' hy' hsrc' hw'i hlt hni' hne
    · subst heq
      rw [hy] at hy'; cases hy'
      obtain ⟨r1, h1, -, hp1, -⟩ := I.rcv w p y hw
      obtain ⟨r2, h2, -, hp2, -⟩ := I.rcv w' p' y hw'
      rw [hy] at h1 h2; cases h1; cases h2
      obtain ⟨z, x, r0, -, -, -, -, hdst, -, -⟩ := I.ack y r m hy hb
      rw [hdst, mem_singleton] at hp1 hp2
      exact hne (hp1.trans hp2.symm)
    · exact I.mutual_other hw' hy' hsrc' hb' hw hy hsrc hwi hgt hni (Ne.symm hne)

end LogLevel

/-! ## From the log to the MBroadcast trace -/

section Trace

variable {t : ℕ} {C : Cfg P M}

lemma trace_getElem {i : ℕ} {e : Ev P M} (h : C.trace[i]? = some e) :
    ∃ j : ℕ, C.log[j]? = some (.mb e) ∧
      ∀ e' : Ev P M, e' ∈ C.trace.take i ↔ ∃ j' : ℕ, j' < j ∧ C.log[j']? = some (.mb e') := by
  obtain ⟨j, a, h1, h2, h3⟩ := exists_of_getElem?_filterMap mbOf C.log i e h
  rw [mbOf_eq_some] at h2; subst h2
  refine ⟨j, h1, fun e' => ?_⟩
  unfold Cfg.trace
  rw [← h3, mem_filterMap_mbOf, mem_iff_getElem?']
  constructor
  · rintro ⟨j', hj'⟩
    have := lt_of_getElem?_eq_some hj'
    rw [List.getElem?_take] at hj'
    simp only [List.length_take] at this
    exact ⟨j', by omega, by simpa [show j' < j by omega] using hj'⟩
  · rintro ⟨j', hj', h⟩
    exact ⟨j', by rw [List.getElem?_take]; simp [hj', h]⟩

lemma delivBefore_log {p q : P} {m m' : M} (h : DelivBefore C.trace p m q m') :
    ∃ i : ℕ, C.log[i]? = some (.mb (.dl p p m)) ∧
      ∀ j : ℕ, j < i → C.log[j]? ≠ some (.mb (.dl p q m')) := by
  obtain ⟨i, hi, hni⟩ := h
  obtain ⟨j, hj, hiff⟩ := trace_getElem hi
  exact ⟨j, hj, fun j' hj' h => hni ((hiff _).2 ⟨j', hj', h⟩)⟩

/-- **Validity** (Theorem 1). -/
theorem validity (hC : Reachable t C) : Validity C.trace := by
  intro i p q m hi
  obtain ⟨j, hj, hiff⟩ := trace_getElem hi
  obtain ⟨j', hj', h⟩ := hC.inv.bc_of_dl hj
  exact (hiff _).2 ⟨j', hj', h⟩

/-- **No-duplication** (Theorem 1). -/
theorem noDuplication (hC : Reachable t C) : NoDuplication C.trace := by
  intro p q m
  unfold Cfg.trace
  rw [count_filterMap_mbOf]; exact hC.inv.dlU p q m

/-- All mbroadcast messages are different (per sender), as assumed by the paper. -/
theorem uniqueBc (hC : Reachable t C) : UniqueBc C.trace := by
  intro p m
  unfold Cfg.trace
  rw [count_filterMap_mbOf]; exact hC.inv.bcU p m

/-- **Mutual ordering** (Theorem 1), for `t < n/2`. -/
theorem mutualOrdering (h2t : 2 * t < Fintype.card P) (hC : Reachable t C) :
    MutualOrdering C.trace := by
  intro p m p' m' hne ⟨h1, h2⟩
  by_cases hp : p = p'
  · subst hp
    exact not_delivBefore_same (fun h => hne (by rw [h])) ⟨h1, h2⟩
  · obtain ⟨i, hi, hni⟩ := delivBefore_log h1
    obtain ⟨i', hi', hni'⟩ := delivBefore_log h2
    exact hC.inv.mutual h2t hp hi hni hi' hni'

/-- **Theorem 1 (safety).** In `CAMP_{n,t}[t < n/2]` with causal message delivery, every
reachable configuration of Algorithm 2 (with any number of crashes) has an MBroadcast trace
satisfying Validity, No-duplication and Mutual ordering (and all mbroadcast messages are
different). -/
theorem theorem1_safety (h2t : 2 * t < Fintype.card P) (hC : Reachable t C) :
    Safe C.trace ∧ UniqueBc C.trace :=
  ⟨⟨validity hC, noDuplication hC, mutualOrdering h2t hC⟩, uniqueBc hC⟩

end Trace

/-! ## Non-vacuity: a reachable configuration in which a process returns -/

section Example

lemma Reachable.foldlM {t : ℕ} :
    ∀ (as : List (Action P M)) {C C' : Cfg P M}, Reachable t C →
      as.foldlM (Causal.step t) C = some C' → Reachable t C'
  | [], C, C', hC, h => by
    simp only [List.foldlM_nil] at h; cases h; exact hC
  | a :: as, C, C', hC, h => by
    simp only [List.foldlM_cons] at h
    cases hs : Causal.step t C a with
    | none => rw [hs] at h; cases h
    | some C1 =>
      rw [hs] at h
      exact Reachable.foldlM as (hC.step a hs) h

/-- `n = 3`, `t = 1`: process `0` invokes `mbroadcast(())`, process `1` receives `init` (and
acknowledges it, and mdelivers the message), process `0` receives the `ack` and returns. -/
def exampleSchedule : List (Action (Fin 3) Unit) := [.invoke 0 (), .recv 1 1, .recv 0 3, .own 0]

/-- The safety theorem is not vacuous: with `n = 3`, `t = 1` (so `2t < n`), there is a reachable
configuration in which a process has mdelivered its own message. -/
theorem example_reachable :
    ∃ C : Cfg (Fin 3) Unit, Reachable 1 C ∧ Ev.dl 0 0 () ∈ C.trace ∧ Ev.dl 1 0 () ∈ C.trace := by
  have h : (exampleSchedule.foldlM (step 1) initCfg).map
      (fun C => decide (Ev.dl (0 : Fin 3) 0 () ∈ C.trace ∧ Ev.dl (1 : Fin 3) 0 () ∈ C.trace)) =
      some true := by decide
  cases hC : exampleSchedule.foldlM (step 1) initCfg with
  | none => rw [hC] at h; cases h
  | some C =>
    rw [hC] at h
    simp only [Option.map_some, Option.some.injEq, decide_eq_true_eq] at h
    exact ⟨C, Reachable.foldlM _ .init hC, h⟩

end Example

end Podc.MBroadcast.Causal
