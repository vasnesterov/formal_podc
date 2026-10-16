import Papers.PODC2022.ConsensusFromSwap.Alg1Defs

/-!
# Algorithm 1: obstruction-freedom (Lemma 8)

Lemma 8 of Ovens, *The Space Complexity of Consensus from Swap* (PODC 2022): Algorithm 1 is
obstruction-free; more precisely, a process running solo from **any** configuration (reachable or
not) decides within `8 * N` of its own steps (`N = n − k` is the number of swap objects), which is
the paper's bound `8(n − k)` (`lemma8_bound`).

In a solo run of `p` only the local state of `p` and the objects change, so we abstract a solo
step as a function `OF.sstep` on pairs (local state of `p`, memory) (`OF.run_solo_eq`).

Proof structure (as in the paper):
* `OF.sweep`: from any state poised on object `i`, after `N − i` steps `p` has finished the
  current iteration; after a full iteration started at object `0`, every object holds `p`'s
  identifier and a lap counter dominated by `p`'s counter (`OF.Good`);
* `OF.iter_exact`: from a `Good` state the next iteration does not change `U`; the result is the
  `⟨U, p⟩`-total configuration `OF.tot`, or a lap if the state was already total;
* from `tot me U` at most three laps (each lap followed by a conflicting iteration) lead to a
  decision: `5N` steps; hence `N + N + N + 5N = 8N` in total.
-/

namespace ConsensusFromSwap.Alg1

open ConsensusFromSwap

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P] {m N : ℕ} [NeZero m] [NeZero N]

namespace OF

/-! ### Facts about `lead`, `lap`, `after` -/

lemma le_lead (U : Lap m) (j : Fin m) : U j ≤ U (lead U) := by
  unfold lead
  generalize_proofs hne
  exact (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2 j

/-- Line 20: increment the leading component. -/
def bump (U : Lap m) : Lap m := Function.update U (lead U) (U (lead U) + 1)

lemma bump_lead (U : Lap m) : bump U (lead U) = U (lead U) + 1 := by simp [bump]

lemma bump_ne (U : Lap m) {j : Fin m} (hj : j ≠ lead U) : bump U j = U j := by
  simp [bump, Function.update_of_ne hj]

lemma lead_bump (U : Lap m) : lead (bump U) = lead U := by
  by_contra h
  have h1 := le_lead (bump U) (lead U)
  rw [bump_lead, bump_ne U h] at h1
  have h2 := le_lead U (lead (bump U))
  omega

lemma le_bump (U : Lap m) : U ≤ bump U := by
  intro j
  by_cases hj : j = lead U
  · rw [hj, bump_lead]; exact Nat.le_succ _
  · rw [bump_ne U hj]

lemma bump_ne_self (U : Lap m) : bump U ≠ U := by
  intro h
  have := congrFun h (lead U)
  rw [bump_lead] at this
  omega

/-- The leading component of `U` is at least `k` ahead of all other components. -/
def GapOK (k : ℕ) (U : Lap m) : Prop := ∀ j, j ≠ lead U → U j + k ≤ U (lead U)

lemma gapOK_zero (U : Lap m) : GapOK 0 U := fun j _ => by simpa using le_lead U j

lemma GapOK.bump {k : ℕ} {U : Lap m} (h : GapOK k U) : GapOK (k + 1) (bump U) := by
  intro j hj
  rw [lead_bump] at hj ⊢
  rw [bump_lead, bump_ne U hj]
  have := h j hj
  omega

lemma lap_of_gap (me : P) (U : Lap m) (h : GapOK 2 U) :
    lap (N := N) me U = ⟨me, U, 0, false, some (lead U)⟩ := by
  unfold lap
  exact ite_eq_left h

lemma lap_of_not_gap (me : P) (U : Lap m) (h : ¬ GapOK 2 U) :
    lap (N := N) me U = ⟨me, bump U, 0, false, none⟩ := by
  unfold lap
  rw [ite_eq_right (show ¬ ∀ j, j ≠ lead U → U j + 2 ≤ U (lead U) from h)]
  rfl

lemma lap_idx (me : P) (U : Lap m) : (lap (N := N) me U).idx = 0 := by
  unfold lap; split_ifs <;> rfl

lemma lap_conf (me : P) (U : Lap m) : (lap (N := N) me U).conf = false := by
  unfold lap; split_ifs <;> rfl

lemma lap_me (me : P) (U : Lap m) : (lap (N := N) me U).me = me := by
  unfold lap; split_ifs <;> rfl

lemma le_lap_U (me : P) (U : Lap m) : U ≤ (lap (N := N) me U).U := by
  unfold lap
  split_ifs
  · exact le_rfl
  · exact le_bump U

/-- The lap counter after merging the response `r` (lines 10–12). -/
def merge (U : Lap m) (r : Val P m) : Lap m := fun j => max (U j) (r.1 j)

lemma le_merge (U : Lap m) (r : Val P m) : U ≤ merge U r := fun _ => le_max_left _ _

lemma merge_of_le (U : Lap m) (r : Val P m) (h : r.1 ≤ U) : merge U r = U := by
  funext j
  exact max_eq_left (h j)

lemma after_inner (s : LState P m N) (r : Val P m) (h : s.idx.val + 1 < N) :
    after s r = ⟨s.me, merge s.U r, ⟨s.idx.val + 1, h⟩, s.conf || decide (r ≠ (s.U, some s.me)),
      none⟩ := by
  unfold after
  rw [dite_eq_left h]
  rfl

lemma after_end (s : LState P m N) (r : Val P m) (h : ¬ s.idx.val + 1 < N) :
    after s r = if s.conf = true ∨ r ≠ (s.U, some s.me) then
      ⟨s.me, merge s.U r, 0, false, none⟩ else lap s.me (merge s.U r) := by
  unfold after
  rw [dite_eq_right h]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rfl

lemma after_end_props (s : LState P m N) (r : Val P m) (h : ¬ s.idx.val + 1 < N) :
    (after s r).idx = 0 ∧ (after s r).conf = false ∧ (after s r).me = s.me ∧
      s.U ≤ (after s r).U := by
  rw [after_end s r h]
  split_ifs
  · exact ⟨rfl, rfl, rfl, le_merge _ _⟩
  · exact ⟨lap_idx _ _, lap_conf _ _, lap_me _ _, (le_merge _ _).trans (le_lap_U _ _)⟩

/-! ### Solo steps -/

/-- The part of a configuration that changes in a solo run: the local state of the running
process and the memory. -/
abbrev SState (P : Type) (m N : ℕ) := LState P m N × (Fin N → Val P m)

/-- A solo step of a process with local state `σ.1` on memory `σ.2`. -/
def sstep (σ : SState P m N) : SState P m N :=
  match σ.1.dec with
  | some _ => σ
  | none => (after σ.1 (σ.2 σ.1.idx), Function.update σ.2 σ.1.idx (σ.1.U, some σ.1.me))

lemma sstep_of_none {σ : SState P m N} (h : σ.1.dec = none) :
    sstep σ = (after σ.1 (σ.2 σ.1.idx), Function.update σ.2 σ.1.idx (σ.1.U, some σ.1.me)) := by
  unfold sstep; rw [h]

lemma sstep_of_dec {σ : SState P m N} (h : σ.1.dec ≠ none) : sstep σ = σ := by
  unfold sstep
  cases hd : σ.1.dec with
  | none => exact absurd hd h
  | some _ => rfl

lemma iterate_of_dec {σ : SState P m N} (h : σ.1.dec ≠ none) (t : ℕ) : sstep^[t] σ = σ :=
  Function.iterate_fixed (sstep_of_dec h) t

lemma dec_mono {σ : SState P m N} {a b : ℕ} (h : (sstep^[a] σ).1.dec ≠ none) (hab : a ≤ b) :
    (sstep^[b] σ).1.dec ≠ none := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_comm, Function.iterate_add_apply, iterate_of_dec h]
  exact h

/-! ### Bridge to the model -/

lemma act_some (C : Cfg (alg P m N)) (q : P) (v : Fin m)
    (h : (C.loc q : LState P m N).dec = some v) : C.Out q v := by
  show (match (C.loc q : LState P m N).dec with
    | some v => Act.out v
    | none => _) = _
  rw [h]
  rfl

lemma act_none (C : Cfg (alg P m N)) (q : P) (h : (C.loc q : LState P m N).dec = none) :
    (alg P m N).act (C.loc q) = .access (C.loc q : LState P m N).idx
      ((C.loc q : LState P m N).U, some (C.loc q : LState P m N).me)
      (fun r => after (C.loc q) r) := by
  show (match (C.loc q : LState P m N).dec with
    | some v => Act.out v
    | none => _) = _
  rw [h]
  rfl

lemma step_eq (C : Cfg (alg P m N)) (p : P) :
    (((C.step p).loc p : LState P m N), ((C.step p).mem : Fin N → Val P m)) =
      sstep ((C.loc p : LState P m N), (C.mem : Fin N → Val P m)) := by
  cases hd : (C.loc p : LState P m N).dec with
  | some v =>
    rw [C.step_of_out (act_some C p v hd), sstep_of_dec (by simp [hd])]
    rfl
  | none =>
    rw [sstep_of_none hd, C.step_of_access (act_none C p hd)]
    refine Prod.ext ?_ rfl
    exact Function.update_self p _ C.loc

lemma run_solo_eq (C : Cfg (alg P m N)) (p : P) (t : ℕ) :
    (((run C (solo p t)).loc p : LState P m N), ((run C (solo p t)).mem : Fin N → Val P m)) =
      sstep^[t] ((C.loc p : LState P m N), (C.mem : Fin N → Val P m)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [solo_succ, run_concat, step_eq, Function.iterate_succ_apply']
    exact congrArg sstep ih

lemma dec_iff (C : Cfg (alg P m N)) (p : P) : C.Dec p ↔ (C.loc p : LState P m N).dec ≠ none := by
  constructor
  · rintro ⟨v, hv⟩ hd
    have := hv
    rw [Cfg.Out, act_none C p hd] at this
    cases this
  · intro h
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
    exact ⟨v, act_some C p v hv⟩

/-! ### Finishing an iteration -/

/-- After finishing the current iteration (started anywhere), `p` is at the beginning of a new
iteration (or has decided), and all objects it swapped in this iteration contain its identifier
and a lap counter dominated by its own. -/
lemma sweep (j : ℕ) : ∀ σ : SState P m N, σ.1.dec = none → σ.1.idx.val + j + 1 = N →
    (sstep^[j + 1] σ).1.dec ≠ none ∨
      ((sstep^[j + 1] σ).1.dec = none ∧ (sstep^[j + 1] σ).1.idx = 0 ∧
        (sstep^[j + 1] σ).1.conf = false ∧ (sstep^[j + 1] σ).1.me = σ.1.me ∧
        σ.1.U ≤ (sstep^[j + 1] σ).1.U ∧
        (∀ k : Fin N, k.val < σ.1.idx.val → (sstep^[j + 1] σ).2 k = σ.2 k) ∧
        ∀ k : Fin N, σ.1.idx.val ≤ k.val →
          ((sstep^[j + 1] σ).2 k).2 = some σ.1.me ∧ ((sstep^[j + 1] σ).2 k).1 ≤ (sstep^[j + 1] σ).1.U) := by
  induction j with
  | zero =>
    rintro ⟨s, M⟩ hd hN
    simp only at hd hN ⊢
    rw [Function.iterate_one, sstep_of_none hd]
    simp only
    have hlt : ¬ s.idx.val + 1 < N := by omega
    obtain ⟨h1, h2, h3, h4⟩ := after_end_props s (M s.idx) hlt
    by_cases hdec : (after s (M s.idx)).dec = none
    · refine Or.inr ⟨hdec, h1, h2, h3, h4, ?_, ?_⟩
      · intro k hk
        exact Function.update_of_ne (Fin.ne_of_lt hk) _ _
      · intro k hk
        have : k = s.idx := Fin.ext (by omega)
        subst this
        simp only [Function.update_self]
        exact ⟨trivial, h4⟩
    · exact Or.inl hdec
  | succ j ih =>
    rintro ⟨s, M⟩ hd hN
    simp only at hd hN ⊢
    have hlt : s.idx.val + 1 < N := by omega
    rw [Function.iterate_succ_apply, sstep_of_none hd]
    simp only
    have ha := after_inner s (M s.idx) hlt
    rcases ih (after s (M s.idx), Function.update M s.idx (s.U, some s.me)) (by rw [ha])
      (by rw [ha]; simp only; omega) with h | ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · exact Or.inl h
    · have hme : (after s (M s.idx)).me = s.me := by rw [ha]
      have hU : (after s (M s.idx)).U = merge s.U (M s.idx) := by rw [ha]
      have hix : (after s (M s.idx)).idx.val = s.idx.val + 1 := by rw [ha]
      simp only [hme, hU, hix] at h4 h5 h6 h7
      refine Or.inr ⟨h1, h2, h3, h4, (le_merge _ _).trans h5, ?_, ?_⟩
      · intro k hk
        rw [h6 k (by omega)]
        exact Function.update_of_ne (Fin.ne_of_lt hk) _ _
      · intro k hk
        by_cases hk' : k = s.idx
        · subst hk'
          rw [h6 _ (by omega)]
          simp only [Function.update_self]
          exact ⟨trivial, (le_merge _ _).trans h5⟩
        · have hk'' : s.idx.val + 1 ≤ k.val := by
            have : k.val ≠ s.idx.val := fun h => hk' (Fin.ext h)
            omega
          exact h7 k hk''

/-! ### Iterations from a dominated configuration -/

/-- An iteration in which every response is dominated by `U` does not change `U`; its outcome is
determined by whether all responses equal `⟨U, p⟩`. -/
lemma iter_exact (j : ℕ) : ∀ σ : SState P m N, σ.1.dec = none → σ.1.idx.val + j + 1 = N →
    (∀ k : Fin N, σ.1.idx ≤ k → (σ.2 k).1 ≤ σ.1.U) →
    sstep^[j + 1] σ =
      (if σ.1.conf = true ∨ ∃ k : Fin N, σ.1.idx ≤ k ∧ σ.2 k ≠ (σ.1.U, some σ.1.me) then
        ⟨σ.1.me, σ.1.U, 0, false, none⟩ else lap σ.1.me σ.1.U,
       fun k => if σ.1.idx ≤ k then (σ.1.U, some σ.1.me) else σ.2 k) := by
  induction j with
  | zero =>
    rintro ⟨s, M⟩ hd hN hle
    simp only at hd hN hle ⊢
    rw [Function.iterate_one, sstep_of_none hd]
    have hlt : ¬ s.idx.val + 1 < N := by omega
    have hk : ∀ k : Fin N, s.idx ≤ k ↔ k = s.idx := fun k => by
      constructor
      · intro h; exact Fin.ext (by have := k.isLt; rw [Fin.le_iff_val_le_val] at h; omega)
      · rintro rfl; exact le_rfl
    simp only
    rw [after_end s _ hlt, merge_of_le _ _ (hle _ le_rfl)]
    congr 1
    · refine if_congr ?_ rfl rfl
      simp only [hk, exists_eq_left]
    · funext k
      by_cases h : k = s.idx
      · subst h; simp
      · rw [Function.update_of_ne h, ite_eq_right (fun h' => h ((hk k).1 h'))]
  | succ j ih =>
    rintro ⟨s, M⟩ hd hN hle
    simp only at hd hN hle ⊢
    have hlt : s.idx.val + 1 < N := by omega
    rw [Function.iterate_succ_apply, sstep_of_none hd]
    simp only
    rw [after_inner s _ hlt, merge_of_le _ _ (hle _ le_rfl)]
    have hk : ∀ k : Fin N, (⟨s.idx.val + 1, hlt⟩ : Fin N) ≤ k ↔ s.idx ≤ k ∧ k ≠ s.idx := by
      intro k
      simp only [Fin.le_iff_val_le_val, ne_eq, Fin.ext_iff]
      omega
    rw [ih _ rfl (by simp only; omega) (by
      intro k hk'
      simp only at hk' ⊢
      rw [hk] at hk'
      rw [Function.update_of_ne hk'.2]
      exact hle k hk'.1)]
    simp only
    congr 1
    · refine if_congr ?_ rfl rfl
      simp only [Bool.or_eq_true, decide_eq_true_eq, hk]
      constructor
      · rintro ((h | h) | ⟨k, ⟨hk1, hk2⟩, hk3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s.idx, le_rfl, h⟩
        · rw [Function.update_of_ne hk2] at hk3
          exact Or.inr ⟨k, hk1, hk3⟩
      · rintro (h | ⟨k, hk1, hk3⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hk2 : k = s.idx
          · subst hk2; exact Or.inl (Or.inr hk3)
          · refine Or.inr ⟨k, ⟨hk1, hk2⟩, ?_⟩
            rw [Function.update_of_ne hk2]
            exact hk3
    · funext k
      by_cases h : k = s.idx
      · subst h
        simp [hk]
      · by_cases h' : s.idx ≤ k
        · rw [ite_eq_left ((hk k).2 ⟨h', h⟩), ite_eq_left h']
        · rw [ite_eq_right (fun h'' => h' ((hk k).1 h'').1), ite_eq_right h', Function.update_of_ne h]

/-- The `⟨U, me⟩`-total configuration with `p` at the beginning of an iteration. -/
def tot (me : P) (U : Lap m) : SState P m N := (⟨me, U, 0, false, none⟩, fun _ => (U, some me))

/-- `p` is at the beginning of an iteration, every object holds `p`'s identifier and a lap
counter dominated by `p`'s. -/
structure Good (σ : SState P m N) : Prop where
  dec : σ.1.dec = none
  idx : σ.1.idx = 0
  conf : σ.1.conf = false
  le : ∀ k, (σ.2 k).1 ≤ σ.1.U

lemma N_eq : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne N))

lemma iter_good (σ : SState P m N) (h : Good σ) :
    sstep^[N] σ =
      (if ∃ k : Fin N, σ.2 k ≠ (σ.1.U, some σ.1.me) then
        ⟨σ.1.me, σ.1.U, 0, false, none⟩ else lap σ.1.me σ.1.U,
       fun _ => (σ.1.U, some σ.1.me)) := by
  have := iter_exact (N - 1) σ h.dec (by rw [h.idx]; simp [N_eq]) (fun k _ => h.le k)
  rw [N_eq] at this
  rw [this, h.idx, h.conf]
  congr 1
  · refine if_congr ?_ rfl rfl
    simp

lemma tot_good (me : P) (U : Lap m) : Good (tot (N := N) me U) :=
  ⟨rfl, rfl, rfl, fun _ => le_rfl⟩

lemma iter_tot (me : P) (U : Lap m) :
    sstep^[N] (tot (N := N) me U) = (lap me U, fun _ => (U, some me)) := by
  rw [iter_good _ (tot_good me U)]
  simp [tot]

lemma eq_tot_of_good (σ : SState P m N) (h : Good σ) (h' : ¬ ∃ k : Fin N, σ.2 k ≠ (σ.1.U, some σ.1.me)) :
    σ = tot σ.1.me σ.1.U := by
  obtain ⟨⟨me, U, idx, conf, dec⟩, M⟩ := σ
  obtain ⟨hd, hi, hc, -⟩ := h
  simp only at hd hi hc h' ⊢
  simp only [not_exists, not_not] at h'
  subst hd hi hc
  simp only [tot, Prod.mk.injEq, true_and]
  funext k
  exact h' k

/-- From a total configuration, the next iteration completes a lap; if it does not decide, one more
(conflicting) iteration leads to the total configuration for the incremented counter. -/
lemma tot_two (me : P) (U : Lap m) (h : ¬ GapOK 2 U) :
    sstep^[N + N] (tot (N := N) me U) = tot me (bump U) := by
  rw [Function.iterate_add_apply, iter_tot, lap_of_not_gap me U h]
  rw [iter_good _ ⟨rfl, rfl, rfl, fun _ => le_bump U⟩]
  simp only
  rw [ite_eq_left ⟨0, fun h' => bump_ne_self U (by simpa using h'.symm)⟩]
  rfl

lemma tot_decides (k : ℕ) : ∀ (U : Lap m), GapOK (2 - k) U → k ≤ 2 → ∀ me : P,
    (sstep^[(2 * k + 1) * N] (tot (N := N) me U)).1.dec ≠ none := by
  induction k with
  | zero =>
    intro U hU _ me
    simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul]
    rw [iter_tot, lap_of_gap me U hU]
    simp
  | succ k ih =>
    intro U hU hk me
    by_cases h2 : GapOK 2 U
    · refine dec_mono (a := N) ?_ (by nlinarith)
      rw [iter_tot, lap_of_gap me U h2]
      simp
    · have hU' : GapOK (2 - k) (bump U) := by
        have := hU.bump
        rwa [show 2 - (k + 1) + 1 = 2 - k by omega] at this
      have := ih (bump U) hU' (by omega) me
      rw [show (2 * (k + 1) + 1) * N = (2 * k + 1) * N + (N + N) by ring,
        Function.iterate_add_apply, tot_two me U h2]
      exact this

lemma tot_decides_5N (me : P) (U : Lap m) : (sstep^[5 * N] (tot (N := N) me U)).1.dec ≠ none :=
  tot_decides 2 U (gapOK_zero U) le_rfl me

lemma good_decides (σ : SState P m N) (h : Good σ) : (sstep^[6 * N] σ).1.dec ≠ none := by
  by_cases ht : ∃ k : Fin N, σ.2 k ≠ (σ.1.U, some σ.1.me)
  · rw [show 6 * N = 5 * N + N by ring, Function.iterate_add_apply, iter_good σ h, ite_eq_left ht]
    exact tot_decides_5N _ _
  · rw [eq_tot_of_good σ h ht]
    exact dec_mono (tot_decides_5N _ _) (by omega)

/-- Lemma 8 of [Ovens 2022], on the abstract solo state: from any state, a solo run decides
within `8N` steps. -/
lemma decides_8N (σ : SState P m N) : (sstep^[8 * N] σ).1.dec ≠ none := by
  by_cases hd : σ.1.dec = none
  swap
  · rw [iterate_of_dec hd]; exact hd
  -- Phase 1: finish the current iteration.
  have hi := σ.1.idx.isLt
  rcases sweep (N - σ.1.idx.val - 1) σ hd (by omega) with h1 | ⟨h1d, h1i, h1c, -, -, -, -⟩
  · exact dec_mono h1 (by omega)
  set σ1 := sstep^[N - σ.1.idx.val - 1 + 1] σ with hσ1
  -- Phase 2: one full iteration.
  rcases sweep (N - 1) σ1 h1d (by rw [h1i]; simp [N_eq]) with h2 | ⟨h2d, h2i, h2c, -, -, -, h2⟩
  · rw [hσ1, ← Function.iterate_add_apply] at h2
    exact dec_mono h2 (by omega)
  have hG : Good (sstep^[N - 1 + 1] σ1) :=
    ⟨h2d, h2i, h2c, fun k => (h2 k (by rw [h1i]; simp)).2⟩
  have := good_decides _ hG
  rw [hσ1, ← Function.iterate_add_apply, ← Function.iterate_add_apply] at this
  exact dec_mono this (by omega)

end OF

open OF

/-- Lemma 8 of [Ovens 2022], quantitative form: from **any** configuration, a process running solo
decides within `8 * N` steps (`N = n − k` swap objects). -/
theorem lemma8_bound (C : Cfg (alg P m N)) (p : P) :
    ∃ t ≤ 8 * N, (run C (solo p t)).Dec p := by
  refine ⟨8 * N, le_rfl, ?_⟩
  rw [dec_iff]
  have := congrArg Prod.fst (run_solo_eq C p (8 * N))
  simp only at this
  rw [this]
  exact decides_8N _

/-- Lemma 8 of [Ovens 2022]: Algorithm 1 is obstruction-free. -/
theorem lemma8_obstructionFree : ObstructionFree (alg P m N) Set.univ := by
  intro x _ α p
  obtain ⟨t, -, ht⟩ := lemma8_bound (run (initCfg (alg P m N) x) α) p
  exact ⟨t, ht⟩

end ConsensusFromSwap.Alg1
