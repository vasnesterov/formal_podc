import Papers.PODC2024.RecoverableConsensus.Sec4Common
import Podc.Foundations.Data.Finset.Card

/-!
# Lemma 15 of Ovens (PODC'24): `T_{n,n'}` has consensus number `n`

* Lower bound (`alg15_wfConsensus`): one object `O` of type `T_{n,n'}`, initially `s`; a process
  with input `x` applies `op_x` and decides the returned bit. Invariant `Inv15`: `idx` of `O` is
  the number of decided processes, all decided values are equal to the letter of `O` and are
  inputs (so `O = s⊥` only after all `n` processes have decided).
* Upper bound (`not_wfSolvable`): standard valency argument with `E*_0` (crash-free
  executions). Registers and `opR` are excluded by `Crit.not_forall_poised_of_rwLike`/`all_ops`;
  then `σ_p`, `σ_q` (`schedExcept`) are schedules of `m - 1 ≥ n` distinct processes avoiding a
  third process `k`, starting with `p` (team 0) resp. `q` (team 1); after them `O = s⊥` in both,
  so `k` cannot distinguish them. Needs `m ≥ 3`, i.e. `n ≥ 2` (hypothesis `1 ≤ n'`, as in the
  paper); informally, for `n = 1` the type `T_{1,0}` behaves like test-and-set (2-consensus with
  registers), so the hypothesis is necessary (not formalized).
-/

namespace Cslib.SharedMemory.Recoverable.Ovens.Sec4

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

set_option linter.unusedSectionVars false

/-- The schedule `p :: (all processes except p and k)`. -/
def schedExcept {m : ℕ} (p k : Fin m) : List (Fin m) := p :: ((List.finRange m).erase p).erase k

lemma schedExcept_nodup {m : ℕ} (p k : Fin m) : (schedExcept p k).Nodup := by
  have h1 : ((List.finRange m).erase p).Nodup := (List.nodup_finRange m).erase p
  refine List.nodup_cons.2 ⟨fun hp => ?_, h1.erase k⟩
  exact (List.Nodup.not_mem_erase (List.nodup_finRange m)) (List.mem_of_mem_erase hp)

lemma not_mem_schedExcept {m : ℕ} {p k : Fin m} (hkp : k ≠ p) : k ∉ schedExcept p k := by
  have h1 : ((List.finRange m).erase p).Nodup := (List.nodup_finRange m).erase p
  simp only [schedExcept, List.mem_cons, not_or]
  exact ⟨hkp, h1.not_mem_erase⟩

lemma length_schedExcept {m : ℕ} {p k : Fin m} (hkp : k ≠ p) :
    (schedExcept p k).length = m - 1 := by
  have hk : k ∈ (List.finRange m).erase p := (List.mem_erase_of_ne hkp).2 (List.mem_finRange k)
  simp only [schedExcept, List.length_cons, List.length_erase_of_mem hk,
    List.length_erase_of_mem (List.mem_finRange p), List.length_finRange]
  have : 1 ≤ m := by have := p.isLt; omega
  omega

/-- **Lemma 15, upper bound**: wait-free consensus among `m > n` processes cannot be solved with
objects of type `T_{n,n'}` and read/write objects. -/
theorem not_wfSolvable {n n' m : ℕ} (h1 : 1 ≤ n') (h2 : n' < n) (hm : n < m) : ¬ WFSolvable (Tnn n n') m := by
  rintro ⟨ιR, ιS, _, _, R, hR, A, hA⟩
  have hm0 : 0 < m := by omega
  let x : Fin m → Bool := fun p => decide (p.val = 1)
  have hAdm := admOK_crashFree (n := m)
  have hC : Reach A CrashFree (initCfg A x) := Reach.initial hAdm x
  have hb := biv_initial hA hAdm x ⟨⟨0, hm0⟩, by simp [x]⟩ ⟨⟨1, by omega⟩, by simp [x]⟩
  obtain ⟨α, hc⟩ := exists_crit hA hAdm hC hb
  obtain ⟨i, hpo⟩ := hc.poised hA hAdm hC hm0
  rcases i with jR | j
  · exact hc.not_forall_poised_of_rwLike hA hAdm hC hm0 (i := Sum.inl jR) (hR jR) hpo
  have hops := all_ops hA hAdm hC hm0 hc hpo
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA hAdm hC hm0
  obtain ⟨k, hkp, hkq⟩ := Fintype.exists_ne_ne_of_two_lt_card (by simp; omega) p q
  set D := run (initCfg A x) α with hD
  -- the configurations after `σ_p` and `σ_q`
  have key : ∀ r, k ≠ r → (∀ i, (run D ((schedExcept r k).map Ev.step)).mem i = D.mem i ∨
      i = Sum.inr j) ∧ (run D ((schedExcept r k).map Ev.step)).loc k = D.loc k ∧
      (run D ((schedExcept r k).map Ev.step)).mem (Sum.inr j) = (TVal.bot : TVal n) := by
    intro r hkr
    obtain ⟨h1, h2, h3⟩ := run_ops (n' := n') j (schedExcept r k) D (schedExcept_nodup r k)
      (fun r' _ => hops r')
    refine ⟨fun i => ?_, h2 k (not_mem_schedExcept hkr), ?_⟩
    · by_cases hi : i = Sum.inr j
      · exact Or.inr hi
      · exact Or.inl (h1 i hi)
    · apply eq_bot_of_idx (by omega)
      rw [h3, length_schedExcept hkr]
      have := idx_le (n := n) (D.mem (Sum.inr j))
      omega
  obtain ⟨hp1, hp2, hp3⟩ := key p hkp
  obtain ⟨hq1, hq2, hq3⟩ := key q hkq
  have ep : α ++ [.step p] ++ (((List.finRange m).erase p).erase k).map Ev.step =
      α ++ (schedExcept p k).map Ev.step := by simp [schedExcept]
  have eq : α ++ [.step q] ++ (((List.finRange m).erase q).erase k).map Ev.step =
      α ++ (schedExcept q k).map Ev.step := by simp [schedExcept]
  refine team_contra hA hAdm hC hp hq (r := k)
    (β := (((List.finRange m).erase p).erase k).map Ev.step)
    (β' := (((List.finRange m).erase q).erase k).map Ev.step) ?_ ?_ ?_
  · rw [ep]; exact hc.1.append_crashFree (crashFree_steps _)
  · rw [eq]; exact hc.1.append_crashFree (crashFree_steps _)
  · rw [ep, eq, run_append, run_append, ← hD]
    refine ⟨funext fun i => ?_, fun r hr => ?_⟩
    · rcases hp1 i with h | h
      · rcases hq1 i with h' | h'
        · rw [h, h']
        · subst h'; exact hp3.trans hq3.symm
      · subst h; exact hp3.trans hq3.symm
    · simp only [Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨hp2.trans hq2.symm, by simp⟩

/-! ## Lemma 15, lower bound: the algorithm -/

/-- Local states of the wait-free algorithm: about to apply `op_x`, or decided `b`. -/
inductive L15 where
  | start (x : Bool)
  | done (b : Bool)

/-- The wait-free consensus algorithm for `n` processes of Section 4: a process with input `x`
applies `op_x` to `O` (initially `s`) and decides the returned bit. -/
def alg15 (n n' : ℕ) : Alg n (T1 n n') where
  L := L15
  init _ x := .start x
  act
    | .start x => .access (Sum.inr ()) (TOp.op x) (fun r => L15.done (bitOf (n := n) r))
    | .done b => .out b
  mem₀ := mem0

section Alg15

variable {n n' : ℕ}

/-- The value of `O`. -/
abbrev O15 (D : Cfg (alg15 n n')) : TVal n := D.mem (Sum.inr ())

def L15.isDone : L15 → Bool
  | .start _ => false
  | .done _ => true

/-- The processes that have decided. -/
def doneSet (D : Cfg (alg15 n n')) : Finset (Fin n) :=
  Finset.univ.filter (fun p => L15.isDone (D.loc p) = true)

/-- The invariant of crash-free executions. -/
structure Inv15 (x : Fin n → Bool) (D : Cfg (alg15 n n')) : Prop where
  loc : ∀ p, D.loc p = L15.start (x p) ∨ ∃ b, D.loc p = L15.done b
  card : idx (O15 D) = (doneSet D).card
  done : ∀ p b, D.loc p = L15.done b → (∃ q, x q = b) ∧
    (∀ q b', D.loc q = L15.done b' → b' = b) ∧ (∀ v i, O15 D = .sv v i → v = b)

lemma inv15_init (x : Fin n → Bool) : Inv15 x (initCfg (alg15 n n') x) := by
  refine ⟨fun p => Or.inl rfl, ?_, fun p b h => by cases h⟩
  have : doneSet (initCfg (alg15 n n') x) = ∅ := by
    ext p; simp [doneSet, initCfg, alg15, L15.isDone]
  rw [this]; rfl

lemma out15 {D : Cfg (alg15 n n')} {p : Fin n} {v : Bool} (h : D.Out p v) :
    D.loc p = L15.done v := by
  unfold Cfg.Out at h
  revert h
  rcases D.loc p with x | b
  · intro h; cases h
  · intro h; cases h; rfl

lemma mem_doneSet {D : Cfg (alg15 n n')} {p : Fin n} :
    p ∈ doneSet D ↔ L15.isDone (D.loc p) = true := by
  simp [doneSet]

lemma inv15_step {x : Fin n → Bool} {D : Cfg (alg15 n n')} (hI : Inv15 x D) (r : Fin n) :
    Inv15 x (D.stepP r) := by
  rcases hI.loc r with hr | ⟨b, hr⟩
  swap
  · rw [stepP_of_out D (show D.Out r b by rw [Cfg.Out, hr]; rfl)]; exact hI
  have hact : (alg15 n n').act (D.loc r) =
      .access (Sum.inr ()) (TOp.op (x r)) (fun r => L15.done (bitOf (n := n) r)) := by
    rw [hr]; rfl
  obtain ⟨u, hu⟩ : ∃ u, O15 D = u := ⟨_, rfl⟩
  have hEr : (D.stepP r).loc r = L15.done (bitOf (tδ n n' u (TOp.op (x r))).2) := by
    rw [stepP_loc_self D hact]; subst hu; rfl
  have hEq : ∀ q, q ≠ r → (D.stepP r).loc q = D.loc q := fun q hq => stepP_loc_other D hq
  have hEm : O15 (D.stepP r) = (tδ n n' u (TOp.op (x r))).1 := by
    show (D.stepP r).mem (Sum.inr ()) = _
    rw [stepP_mem_self D hact]; subst hu; rfl
  have hrd : r ∉ doneSet D := by rw [mem_doneSet, hr]; simp [L15.isDone]
  have hcard : (doneSet D).card + 1 ≤ n := by
    have : doneSet D ⊆ Finset.univ.erase r := fun p hp =>
      Finset.mem_erase.2 ⟨fun h => hrd (h ▸ hp), Finset.mem_univ _⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < n := by have := r.isLt; omega
    omega
  have hub : u ≠ .bot := by
    intro h
    have := hI.card
    rw [hu, h] at this
    simp only [idx] at this
    omega
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := tδ_op_spec (n' := n') u (x r) hub
  -- all decided processes decided `w`, and `w` is an input
  have hall : ∀ q b, D.loc q = L15.done b → b = w := by
    intro q b hq
    have hq' : q ∈ doneSet D := by rw [mem_doneSet, hq]; rfl
    have hpos : 0 < (doneSet D).card := Finset.card_pos.2 ⟨q, hq'⟩
    rcases hus : u with _ | _ | ⟨v, i⟩
    · have := hI.card; rw [hu, hus] at this; simp only [idx] at this; omega
    · exact absurd hus hub
    · rw [hw3 v i hus]; exact ((hI.done q b hq).2.2 v i (by rw [hu, hus])).symm
  have hval : ∃ q, x q = w := by
    rcases hus : u with _ | _ | ⟨v, i⟩
    · exact ⟨r, (hw2 hus).symm⟩
    · exact absurd hus hub
    · have hpos : 0 < (doneSet D).card := by
        have := hI.card; rw [hu, hus] at this; simp only [idx] at this; omega
      obtain ⟨q, hq⟩ := Finset.card_pos.1 hpos
      rw [mem_doneSet] at hq
      rcases hI.loc q with h | ⟨b, h⟩
      · rw [h] at hq; simp [L15.isDone] at hq
      · rw [← hall q b h]; exact (hI.done q b h).1
  have hnew : ∀ p b, (D.stepP r).loc p = L15.done b → b = w := by
    intro p b hp
    by_cases hpr : p = r
    · subst hpr
      rw [hEr] at hp
      cases hp
      rw [hw1]; rfl
    · rw [hEq p hpr] at hp
      exact hall p b hp
  have hdone' : doneSet (D.stepP r) = insert r (doneSet D) := by
    ext p
    rw [Finset.mem_insert, mem_doneSet, mem_doneSet]
    by_cases hpr : p = r
    · subst hpr; rw [hEr]; simp [L15.isDone]
    · rw [hEq p hpr]; simp [hpr]
  refine ⟨fun p => ?_, ?_, fun p b hp => ?_⟩
  · by_cases hpr : p = r
    · subst hpr; right; exact ⟨_, hEr⟩
    · rw [hEq p hpr]; exact hI.loc p
  · have hc := hI.card
    rw [hu] at hc
    rw [hEm, idx_op, hdone', Finset.card_insert_of_notMem hrd, ← hc]
    omega
  · have hb := hnew p b hp
    subst hb
    refine ⟨hval, fun q b' hq => hnew q b' hq, fun v i hvi => ?_⟩
    rw [hEm] at hvi
    exact hw4 v i hvi

lemma inv15_run {x : Fin n → Bool} : ∀ (β : List (Ev n)) (D : Cfg (alg15 n n')), Inv15 x D →
    CrashFree β → Inv15 x (run D β)
  | [], _, h, _ => h
  | e :: β, D, h, hβ => by
    cases e with
    | step r => exact inv15_run β _ (inv15_step h r) (fun p hp => hβ p (by simp [hp]))
    | crash r => exact absurd (by simp) (hβ r)

lemma done15_run : ∀ (β : List (Ev n)) (D : Cfg (alg15 n n')) (p : Fin n) (b : Bool),
    D.loc p = L15.done b → CrashFree β → (run D β).loc p = L15.done b
  | [], _, _, _, h, _ => h
  | e :: β, D, p, b, h, hβ => by
    cases e with
    | step r =>
      refine done15_run β _ p b ?_ (fun q hq => hβ q (by simp [hq]))
      show (D.stepP r).loc p = _
      by_cases hrp : r = p
      · subst hrp; rw [stepP_of_out D (show D.Out r b by rw [Cfg.Out, h]; rfl)]; exact h
      · rw [stepP_loc_other D (Ne.symm hrp)]; exact h
    | crash r => exact absurd (by simp) (hβ r)

lemma agree15_aux {x : Fin n → Bool} {γ : List (Ev n)} (hγ : CrashFree γ) {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) {p q : Fin n} {v w : Bool}
    (hv : (run (initCfg (alg15 n n') x) (γ.take k₁)).Out p v)
    (hw : (run (initCfg (alg15 n n') x) (γ.take k₂)).Out q w) : v = w := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [List.take_add, run_append] at hw
  have hdrop : CrashFree ((γ.drop k₁).take d) :=
    CrashFree.take (fun r hr => hγ r (List.mem_of_mem_drop hr)) d
  have hd := done15_run _ _ p v (out15 hv) hdrop
  have hI := inv15_run (x := x) _ _ (inv15_init (n' := n') x) (hγ.take k₁)
  have hI' := inv15_run (x := x) _ _ hI hdrop
  exact (hI'.done q w (out15 hw)).2.1 p v hd

/-- Ranking for progress: one operation before deciding. -/
def rank15 : L15 → ℕ
  | .start _ => 1
  | .done _ => 0

/-- The algorithm of Section 4 solves wait-free consensus among `n` processes. -/
theorem alg15_wfConsensus : WFConsensus (alg15 n n') := by
  refine ⟨fun x γ hγ v w hv hw => ?_, fun x γ hγ v hv => ?_, fun x e p N _ hinf hN => ?_⟩
  · obtain ⟨k₁, -, p, hp⟩ := hv
    obtain ⟨k₂, -, q, hq⟩ := hw
    rcases le_total k₁ k₂ with h | h
    · exact agree15_aux hγ h hp hq
    · exact (agree15_aux hγ h hq hp).symm
  · obtain ⟨k, -, p, hp⟩ := hv
    have hI := inv15_run (x := x) _ _ (inv15_init (n' := n') x) (hγ.take k)
    exact (hI.done p v (out15 hp)).1
  · refine prog_of_rank (A := alg15 n n') rank15 (fun l i o k r hl => ?_) _ e p N hinf hN
    cases l with
    | start x => cases hl; simp [rank15]
    | done b => cases hl

end Alg15

end Cslib.SharedMemory.Recoverable.Ovens.Sec4

namespace Cslib.SharedMemory.Recoverable.Ovens

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Sec4

/-- **Lemma 15** of Ovens (PODC'24): `T_{n,n'}` has consensus number `n`. -/
theorem lemma15 {n n' : ℕ} (h1 : 1 ≤ n') (h2 : n' < n) : ConsensusNumber (Tnn n n') n :=
  ⟨⟨Empty, Unit, inferInstance, inferInstance, noRW, fun e => e.elim, alg15 n n', alg15_wfConsensus⟩,
    fun _ hm => not_wfSolvable h1 h2 hm⟩

end Cslib.SharedMemory.Recoverable.Ovens
