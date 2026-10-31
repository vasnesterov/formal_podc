import Papers.PODC2017.MemoryAnonymousCoordination.RenamingSafety

/-!
# Figure 3: obstruction-freedom (Theorem 5.1)

A process `p` running solo finishes its current collect and write. Starting a collect in round
`r`, its first complete (now accurate) iteration catches up to the maximal round in memory (if it
is lagging behind) and fixes its preference; after writing it the local variables `s` are
*stable* (no catch-up, the preference is adopted again, `adopt_stable`), and every further
iteration turns one more register into `(p, s)` (by the hypothesis on line 15) until all
registers hold `(p, s)` and `p` exits the inner loop (`to_last`). Then `p` returns (line 18 or
22) or starts round `s.rd + 1 < n` (`after_last`; the bound `s.rd + 1 ≤ n` comes from the safety
invariant: the history of `s` names `s.rd − 1` processes different from `p` and from the winner
`s.val ≠ p`). Since rounds only increase and stay below `n`, `p` returns (`term_start`).

The paper's proof of Theorem 5.1 is a sketch of the same argument (its item (3) says "increments
mypref" for "increments myround").
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Renaming

open Cslib.SharedMemory

variable {P : Type} {m : ℕ} [DecidableEq P]
  {n : ℕ} {S : Sel P m} {π : P → Equiv.Perm (Fin m)}

variable (n S π) in
/-- `p` running solo from `C` eventually returns. -/
def Term (p : P) (C : Cfg P m) : Prop :=
  ∃ k, (((I n S π).soloStep p)^[k] C).pend p = none

lemma Term.of_iter {p : P} {C : Cfg P m} (t : ℕ)
    (h : Term n S π p (((I n S π).soloStep p)^[t] C)) : Term n S π p C := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + t, by rw [Function.iterate_add_apply]; exact hk⟩

lemma term_done {p : P} {C : Cfg P m} (hp : C.pend p ≠ none) {a : ℕ}
    (hl : C.loc p = .done a) : Term n S π p C :=
  ⟨1, solo_done hp hl⟩

/-- Finishing a collect solo: after the remaining reads, `p` has computed the continuation of
its virtual view. -/
lemma collect_run {p : P} (d : ℕ) : ∀ (C : Cfg P m) (s : St P) (k : Fin m)
    (view : Fin m → Option (P × St P)), k.val + d + 1 = m → C.pend p ≠ none →
    C.loc p = .collect s k view →
    ∃ D, ((I n S π).soloStep p)^[d + 1] C = D ∧ D.pend = C.pend ∧ D.mem = C.mem ∧
      D.loc p = finish n S p s (mixed (π p) k view C.mem) := by
  induction d with
  | zero =>
    intro C s k view hk hp hl
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp [solo_collect hp hl]
    · simp [solo_collect hp hl]
    · have hk' : ¬ k.val + 1 < m := by omega
      simp [solo_collect hp hl, afterRead, hk', mixed_last _ _ _ _ hk']
  | succ d ih =>
    intro C s k view hk hp hl
    have hk' : k.val + 1 < m := by omega
    set C₁ := (I n S π).soloStep p C with hC₁
    have h1 : C₁.loc p = .collect s ⟨k.val + 1, hk'⟩
        (Function.update view k (C.mem (π p k))) := by
      simp [hC₁, solo_collect hp hl, afterRead, hk']
    have hp1 : C₁.pend = C.pend := by simp [hC₁, solo_collect hp hl]
    have hm1 : C₁.mem = C.mem := by simp [hC₁, solo_collect hp hl]
    obtain ⟨D, hD, hDp, hDm, hDl⟩ :=
      ih C₁ s ⟨k.val + 1, hk'⟩ _ (by simp only; omega) (by rw [hp1]; exact hp) h1
    refine ⟨D, ?_, by rw [hDp, hp1], by rw [hDm, hm1], ?_⟩
    · rw [Function.iterate_succ_apply]; exact hD
    · rw [hDl, hm1, mixed_read _ _ _ _ hk']

/-- The registers as seen by `p` (in its own numbering). -/
def localMem (σ : Equiv.Perm (Fin m)) (C : Cfg P m) : Fin m → Option (P × St P) :=
  fun j => C.mem (σ j)

/-- Number of registers not holding `(p, s)`. -/
def miss (p : P) (s : St P) (v : Fin m → Option (P × St P)) : ℕ :=
  (Finset.univ.filter fun j => v j ≠ some (p, s)).card

lemma miss_update_lt {p : P} {s : St P} {v : Fin m → Option (P × St P)} {j : Fin m}
    (hj : v j ≠ some (p, s)) : miss p s (Function.update v j (some (p, s))) < miss p s v := by
  unfold miss
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_apply]
    split_ifs <;> simp_all
  · intro hsub
    have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)
    simp at this

/-- `p` is about to exit the inner loop (line 17) with local variables `s`, after `t` solo
steps. -/
def AtLast (p : P) (s : St P) (C : Cfg P m) : Prop :=
  ∃ t j, (((I n S π).soloStep p)^[t] C).pend p ≠ none ∧
    (((I n S π).soloStep p)^[t] C).loc p = .write s j true

lemma AtLast.of_iter {p : P} {s : St P} {C : Cfg P m} (t : ℕ)
    (h : AtLast (n := n) (S := S) (π := π) p s (((I n S π).soloStep p)^[t] C)) :
    AtLast (n := n) (S := S) (π := π) p s C := by
  obtain ⟨k, j, h1, h2⟩ := h
  refine ⟨k + t, j, ?_, ?_⟩ <;> rw [Function.iterate_add_apply] <;> assumption

/-- One full solo iteration from the start of a collect. -/
lemma iteration (hm : m + 1 = 2 * n) {p : P} {C : Cfg P m} (hp : C.pend p ≠ none) {s : St P}
    {k : Fin m} {view : Fin m → Option (P × St P)} (hl : C.loc p = .collect s k view)
    (hk : k.val = 0) :
    let M := localMem (π p) C
    let s₂ := adopt n M (catchUp S p s M)
    Term n S π p C ∨ AtLast (n := n) (S := S) (π := π) p s₂ C ∨
      ∃ t E, ((I n S π).soloStep p)^[t] C = E ∧ E.pend = C.pend ∧
        E.loc p = .collect s₂ k (fun _ => none) ∧
        localMem (π p) E = Function.update M (S.tgt p s₂ M) (some (p, s₂)) ∧
        (∃ i, M i ≠ some (p, s₂)) := by
  intro M s₂
  have hm0 := pos_of_hm hm
  obtain ⟨D, hD, hDp, hDm, hDl⟩ := collect_run (n := n) (S := S) (π := π) (m - 1) C s k view
    (by omega) hp hl
  rw [mixed_zero _ _ _ _ hk] at hDl
  change D.loc p = finish n S p s M at hDl
  have hpD : D.pend p ≠ none := by rw [hDp]; exact hp
  rcases finish_cases n S p s M with ⟨a, ha, -⟩ | ⟨-, hw⟩
  · left
    refine Term.of_iter (m - 1 + 1) ?_
    rw [hD]
    exact term_done hpD (by rw [hDl, ha])
  · rw [hw] at hDl
    by_cases hb : ∀ i, M i = some (p, s₂)
    · right; left
      refine ⟨m - 1 + 1, S.tgt p s₂ M, by rw [hD]; exact hpD, ?_⟩
      rw [hD, hDl]; congr 1; simpa using hb
    · right; right
      push Not at hb
      have hDl' : D.loc p = .write s₂ (S.tgt p s₂ M) false := by
        rw [hDl]; congr 1; simp only [decide_eq_false_iff_not, not_forall]; exact hb
      refine ⟨m - 1 + 1 + 1, (I n S π).soloStep p D, ?_, ?_, ?_, ?_, hb⟩
      · rw [Function.iterate_succ_apply', hD]
      · rw [solo_write hpD hDl']; exact hDp
      · rw [solo_write hpD hDl']
        simp only [Function.update_self, afterWrite, Bool.false_eq_true, ↓reduceIte,
          startCollect, hm0, ↓reduceDIte]
        congr 1; ext; simp [hk]
      · rw [solo_write hpD hDl']
        funext i
        simp only [localMem, hDm, Function.update_apply, (π p).injective.eq_iff, M]

/-- Stable local variables: no catch-up, the preference is adopted again. -/
def Stable (s : St P) (M : Fin m → Option (P × St P)) : Prop :=
  maxRd M ≤ s.rd ∧ adopt n M s = s

lemma stable_after_write (hm : m + 1 = 2 * n) (hS : S.OK) (p : P) (s : St P)
    (M : Fin m → Option (P × St P)) (j : Fin m) :
    Stable (n := n) (adopt n M (catchUp S p s M))
      (Function.update M j (some (p, adopt n M (catchUp S p s M)))) := by
  refine ⟨maxRd_le fun i => ?_, adopt_stable hm _ _ _ _⟩
  rw [Function.update_apply]; split_ifs
  · simp
  · rw [adopt_rd, catchUp_rd hS]; exact (le_maxRd M i).trans (le_max_right _ _)

/-- From stable local variables, the solo run exits the inner loop or returns. -/
lemma stable_run (hm : m + 1 = 2 * n) (hS : S.OK) {p : P} :
    ∀ N (C : Cfg P m) s k view, miss p s (localMem (π p) C) ≤ N → C.pend p ≠ none →
      C.loc p = .collect s k view → k.val = 0 → Stable (n := n) s (localMem (π p) C) →
      Term n S π p C ∨ AtLast (n := n) (S := S) (π := π) p s C := by
  intro N
  induction N with
  | zero =>
    intro C s k view hN hp hl hk hst
    have hcu : catchUp S p s (localMem (π p) C) = s := catchUp_of_le hst.1
    rcases iteration (S := S) hm hp hl hk with h | h | ⟨t, E, -, -, -, -, i, hi⟩
    · exact Or.inl h
    · right; simpa only [hcu, hst.2] using h
    · exfalso
      simp only [hcu, hst.2] at hi
      have : 0 < miss p s (localMem (π p) C) :=
        Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
      omega
  | succ N ih =>
    intro C s k view hN hp hl hk hst
    have hcu : catchUp S p s (localMem (π p) C) = s := catchUp_of_le hst.1
    rcases iteration (S := S) hm hp hl hk with h | h | ⟨t, E, hE, hEp, hEl, hEm, hex⟩
    · exact Or.inl h
    · right; simpa only [hcu, hst.2] using h
    · simp only [hcu, hst.2] at hEl hEm hex
      have h2 := ih E s k _ ?_ (by rw [hEp]; exact hp) hEl hk ?_
      · rcases h2 with h2 | h2
        · left; exact Term.of_iter t (hE ▸ h2)
        · right; exact AtLast.of_iter t (hE ▸ h2)
      · rw [hEm]; have := miss_update_lt (hS.tgt p s _ hex); omega
      · rw [hEm]
        have := stable_after_write (n := n) hm hS p s (localMem (π p) C)
          (S.tgt p s (localMem (π p) C))
        rwa [hcu, hst.2] at this

/-- From the start of a collect in round `r`, the solo run returns or exits the inner loop in a
round `≥ r`. -/
lemma to_last (hm : m + 1 = 2 * n) (hS : S.OK) {p : P} {C : Cfg P m} (hp : C.pend p ≠ none)
    {s : St P} {k : Fin m} {view : Fin m → Option (P × St P)} (hl : C.loc p = .collect s k view)
    (hk : k.val = 0) :
    Term n S π p C ∨ ∃ s', s.rd ≤ s'.rd ∧ AtLast (n := n) (S := S) (π := π) p s' C := by
  have hrd : s.rd ≤ (adopt n (localMem (π p) C) (catchUp S p s (localMem (π p) C))).rd := by
    rw [adopt_rd, catchUp_rd hS]; exact le_max_left _ _
  rcases iteration (S := S) hm hp hl hk with h | h | ⟨t, E, hE, hEp, hEl, hEm, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, hrd, h⟩
  · have h2 := stable_run (S := S) hm hS _ E _ k _ le_rfl (by rw [hEp]; exact hp) hEl hk
      (by rw [hEm]; exact stable_after_write hm hS p s _ _)
    rcases h2 with h2 | h2
    · left; exact Term.of_iter t (hE ▸ h2)
    · right; exact ⟨_, hrd, AtLast.of_iter t (hE ▸ h2)⟩

/-- After exiting the inner loop, `p` returns or starts the next round, which is `< n`. -/
lemma after_last [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n) (hS : S.OK)
    {p : P} {E : Cfg P m} (hR : (I n S π).Reachable E) (hp : E.pend p ≠ none) {s : St P}
    {j : Fin m} (hl : E.loc p = .write s j true) :
    Term n S π p E ∨ (((I n S π).soloStep p E).pend p ≠ none ∧
      ((I n S π).soloStep p E).loc p = .collect (nextRound p s) ⟨0, pos_of_hm hm⟩
        (fun _ => none) ∧ (nextRound p s).rd < n) := by
  have hm0 := pos_of_hm hm
  obtain ⟨α, hα⟩ := hR
  have hI : Inv n π α E := inv_of_run hm hcard hS hα
  have hlv := hI.loc p
  rw [hl] at hlv
  obtain ⟨hsOK, hown, -, -⟩ := hlv
  have hpE : ((I n S π).soloStep p E).pend p ≠ none := by rw [solo_write hp hl]; exact hp
  have hlE : ((I n S π).soloStep p E).loc p = afterWrite n p s true := by
    rw [solo_write hp hl]; simp
  unfold afterWrite at hlE
  by_cases hv : s.val = p
  · left; simp only [↓reduceIte, hv] at hlE; exact Term.of_iter 1 (term_done hpE hlE)
  · -- the history names `s.rd − 1` processes, all different from `p` and `s.val`
    have hbound : s.rd + 1 ≤ n := by
      have h1 : p ∉ insert s.val (s.hist.image Prod.fst) := by
        simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
        refine ⟨fun h => hv h.symm, ?_⟩
        rintro ⟨u, t⟩ hu rfl; exact hown t hu
      have h2 : s.val ∉ s.hist.image Prod.fst := by
        simp only [Finset.mem_image, not_exists, not_and]
        rintro ⟨u, t⟩ hu rfl; exact hsOK.val t hu
      have := Finset.card_le_univ (insert p (insert s.val (s.hist.image Prod.fst)))
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        hsOK.hist.card_ids] at this
      have := hsOK.rd
      omega
    by_cases hn : s.rd + 1 = n
    · left; simp only [↓reduceIte, hv, hn] at hlE; exact Term.of_iter 1 (term_done hpE hlE)
    · right
      simp only [↓reduceIte, hv, hn, startCollect_eq hm0] at hlE
      exact ⟨hpE, hlE, by simp only [nextRound]; omega⟩

/-- From the start of a collect, the solo run returns (induction on `n − round`). -/
lemma term_start [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n) (hS : S.OK)
    {p : P} : ∀ N (C : Cfg P m) s k view, n - s.rd ≤ N → (I n S π).Reachable C →
      C.pend p ≠ none → C.loc p = .collect s k view → k.val = 0 → Term n S π p C := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro C s k view hN hR hp hl hk
    rcases to_last (S := S) hm hS hp hl hk with h | ⟨s', hss', t, j, hpt, hlt⟩
    · exact h
    · refine Term.of_iter t ?_
      have hRt := hR.iterate_soloStep p t
      rcases after_last hm hcard hS hRt hpt hlt with h | ⟨hp', hl', hlt'⟩
      · exact h
      · refine Term.of_iter 1 ?_
        rw [Function.iterate_one]
        simp only [nextRound] at hlt'
        exact ih (n - (nextRound p s').rd) (by simp only [nextRound]; omega) _ _ _ _ le_rfl
          (hRt.soloStep p) hp' hl' rfl

lemma term_write [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n) (hS : S.OK)
    {p : P} {C : Cfg P m} (hR : (I n S π).Reachable C) (hp : C.pend p ≠ none) {s : St P}
    {j : Fin m} {b : Bool} (hl : C.loc p = .write s j b) : Term n S π p C := by
  have hm0 := pos_of_hm hm
  cases b with
  | true =>
    rcases after_last hm hcard hS hR hp hl with h | ⟨hp', hl', -⟩
    · exact h
    · exact Term.of_iter 1 (term_start hm hcard hS _ _ _ _ _ le_rfl (hR.soloStep p) hp' hl' rfl)
  | false =>
    refine Term.of_iter 1 (term_start (s := s) (k := ⟨0, hm0⟩) (view := fun _ => none) hm hcard
      hS _ _ le_rfl (hR.soloStep p) ?_ ?_ rfl)
    · simp only [Function.iterate_one, solo_write hp hl]; exact hp
    · simp [solo_write hp hl, afterWrite, startCollect, hm0]

/-- Obstruction-freedom for `m + 1 = 2n` registers. -/
theorem obstructionFree_of_hm [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    (hS : S.OK) : ((alg n S).unnamed π).ObstructionFree := by
  intro C p hR hp
  obtain ⟨α, hα⟩ := hR
  have hI : Inv n π α C := inv_of_run hm hcard hS hα
  change Term n S π p C
  cases hl : C.loc p with
  | idle => exact absurd (hI.idle p hl) hp
  | done a => exact term_done hp hl
  | write s j b => exact term_write hm hcard hS ⟨α, hα⟩ hp hl
  | collect s k view =>
    obtain ⟨D, hD, hDp, -, hDl⟩ := collect_run (n := n) (S := S) (π := π) (m - 1 - k.val) C s k
      view (by omega) hp hl
    refine Term.of_iter (m - 1 - k.val + 1) ?_
    rw [hD]
    have hpD : D.pend p ≠ none := by rw [hDp]; exact hp
    have hRD : (I n S π).Reachable D := hD ▸ Impl.Reachable.iterate_soloStep ⟨α, hα⟩ p _
    rcases finish_cases n S p s (mixed (π p) k view C.mem) with ⟨a, ha, -⟩ | ⟨-, hw⟩
    · exact term_done hpD (by rw [hDl, ha])
    · exact term_write hm hcard hS hRD hpD (by rw [hDl, hw])

end Podc.MemoryAnonymousCoordination.Renaming
