import Papers.PODC2022.WearLeveling.Safety
import Papers.PODC2022.WearLeveling.LockFree
import Papers.PODC2022.WearLeveling.Endurance
import Papers.PODC2022.WearLeveling.Tas
import Podc.Computability.Distributed.SharedMemory.Persistent.Solo

/-!
# Theorem 4.4, repaired: optimality of `k·T` for fetch-and-increment

For **every** implementation of a fetch-and-increment counter from `k` persistent words (in the
model with a volatile write-back cache and system-wide crashes) that is strictly linearizable and
obstruction-free (in the ideal model), there is a sequential, crash-free execution of one thread
with `k·T + 1` FAIs in which some word is written back at least `T + 1` times
(`theorem_4_4_fai`). So no FAI implementation keeps every word within `T` write-backs for
`k·T + 1` FAIs. This is the content of the paper's proof sketch.

Proof: after each completed FAI, persistent memory must change. Otherwise, crashing right after
the `j`-th and right after the `(j+1)`-st FAI leads to configurations that are equal up to wear
counters and operation identifiers (`Rel`), so one more FAI returns the same value in both runs,
while strict linearizability forces the values `j` and `j + 1` (`resp_after_crash`). Each change
of persistent memory costs a write-back, and `k·T + 1` write-backs on `k` words put `T + 1` on
some word.
-/

namespace Podc.WearLeveling

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Persistent Alg

variable {k : ℕ} {V : Type} [DecidableEq V] {P : Type} [DecidableEq P]

/-! ### Sequential FAI histories -/

/-- `H` is the history of `c` complete sequential FAIs of `p` (identifiers `0, …, c-1`). -/
inductive IsSeqH (p : P) : List (HEv P Unit ℕ) → ℕ → Prop
  | nil : IsSeqH p [] 0
  | snoc {H c} (r : ℕ) : IsSeqH p H c → IsSeqH p (H ++ [.inv c p (), .res c r]) (c + 1)

lemma IsSeqH.inv_lt {p : P} {H c} (hH : IsSeqH p H c) :
    ∀ a q o, HEv.inv a q o ∈ H → a < c := by
  induction hH with
  | nil => simp
  | snoc r hH ih =>
    intro a q o h
    rcases List.mem_append.1 h with h | h
    · have := ih a q o h; omega
    · simp at h; omega

lemma IsSeqH.res_mem {p : P} {H c} (hH : IsSeqH p H c) :
    ∀ i < c, ∃ r, HEv.res i r ∈ H := by
  induction hH with
  | nil => simp
  | snoc r hH ih =>
    intro i hi
    rcases Nat.lt_or_ge i _ with h | h
    · obtain ⟨r', hr'⟩ := ih i h; exact ⟨r', List.mem_append_left _ hr'⟩
    · exact ⟨r, by simp; omega⟩

/-- After `c` sequential FAIs and a crash, one more FAI must return `c`. -/
lemma resp_after_crash {p : P} {H c r} (hH : IsSeqH p H c) {L : List (ℕ × Unit)}
    (hL : IsStrictLin faiObj (H ++ [.crash, .inv c p (), .res c r]) L) : r = c := by
  set G := H ++ [.crash, .inv c p (), .res c r] with hG
  -- the identifiers of `L` are exactly `0, …, c`
  have hids : ∀ x ∈ L.map Prod.fst, x ≤ c := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, hq⟩ := hL.inv_of_mem y hy
    rcases List.mem_append.1 hq with hq | hq
    · have := hH.inv_lt _ _ _ hq; omega
    · simp at hq; omega
  have hmem : ∀ i ≤ c, i ∈ L.map Prod.fst := by
    intro i hi
    rcases Nat.lt_or_ge i c with h | h
    · obtain ⟨r', hr'⟩ := hH.res_mem i h
      exact hL.mem_of_res i r' (List.mem_append_left _ hr')
    · have : i = c := by omega
      subst this
      exact hL.mem_of_res i r (by simp [hG])
  have hlen : L.length ≤ c + 1 := by
    have hsub : (L.map Prod.fst).toFinset ⊆ Finset.range (c + 1) := by
      intro x hx; simp only [Finset.mem_range]; have := hids x (by simpa using hx); omega
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hL.nodup] at this
    simpa using this
  -- position `n` of `c`
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 (hmem c le_rfl)
  have hnlt : n < L.length := by
    have := (List.getElem?_eq_some_iff.1 hn).1; simpa using this
  -- every `i < c` is before `c` in `L`
  have hbefore : ∀ i < c, i ∈ (L.take n).map Prod.fst := by
    intro i hi
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 (hmem i (by omega))
    have hmlt : m < L.length := by
      have := (List.getElem?_eq_some_iff.1 hm).1; simpa using this
    have hmn : m < n := by
      by_contra hc
      have hne : m ≠ n := by rintro rfl; rw [hm] at hn; simp at hn; omega
      have hlt : n < m := by omega
      have hpw := List.pairwise_iff_getElem.1 hL.rt n m hnlt hmlt hlt
      have h1 : L[n].1 = c := by
        have := hn; simp [List.getElem?_map, List.getElem?_eq_getElem hnlt] at this; exact this
      have h2 : L[m].1 = i := by
        have := hm; simp [List.getElem?_map, List.getElem?_eq_getElem hmlt] at this; exact this
      rw [h1, h2] at hpw
      obtain ⟨r', hr'⟩ := hH.res_mem i hi
      exact hpw (SPrec.of_split (h₁ := H) (h₂ := [.crash, .inv c p (), .res c r]) (p := p)
        (o := ()) hr' (by simp))
    rw [List.map_take]
    exact List.mem_iff_getElem?.2 ⟨m, by rw [List.getElem?_take_of_lt hmn]; exact hm⟩
  have hcn : c ≤ n := by
    have hsub : Finset.range c ⊆ ((L.take n).map Prod.fst).toFinset := by
      intro x hx; simp only [Finset.mem_range] at hx; simpa using hbefore x hx
    have := Finset.card_le_card hsub
    have hnd : ((L.take n).map Prod.fst).Nodup := by
      rw [List.map_take]; exact hL.nodup.sublist (List.take_sublist _ _)
    rw [List.toFinset_card_of_nodup hnd] at this
    simp at this; omega
  have hnc : n = c := by omega
  -- legality at position `n`
  obtain ⟨x, hx, hx1⟩ : ∃ x, L[n]? = some x ∧ x.1 = c := by
    rw [List.getElem?_map] at hn
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.1 hn
    exact ⟨x, hx, hx1⟩
  have hres : HEv.res x.1 r ∈ G := by rw [hx1]; simp [hG]
  have hleg := (legal_iff_getElem (O := faiObj) (h := G) L).1 hL.legal n x hx r hres
  rw [hleg]
  simp [faiObj_runOps, List.length_take]
  omega

/-! ### The sequential schedule -/

section Sched

variable (A : Alg faiObj k V) (p : P)
  (hOF : ObstructionFree A P (Wear.ideal k V))

/-- Number of solo steps that completes the FAI invoked after `es`. -/
noncomputable def nOF (es : List (Ev k P Unit)) : ℕ := Classical.choose (hOF (es ++ [.inv p ()]) p)

lemma nOF_spec (es : List (Ev k P Unit)) :
    (exec (Wear.ideal k V) (initCfg A P)
      ((es ++ [.inv p ()]) ++ List.replicate (nOF A p hOF es) (.step p))).1.ts p = .idle :=
  Classical.choose_spec (hOF (es ++ [.inv p ()]) p)

/-- A complete solo FAI of `p` after `es`. -/
noncomputable def seg (es : List (Ev k P Unit)) : List (Ev k P Unit) :=
  .inv p () :: List.replicate (nOF A p hOF es) (.step p)

/-- `j` sequential FAIs of `p`, each run solo to completion. -/
noncomputable def sched : ℕ → List (Ev k P Unit)
  | 0 => []
  | j + 1 => sched j ++ seg A p hOF (sched j)

variable {A p hOF}

lemma sched_events : ∀ j, ∀ e ∈ sched A p hOF j, e = .step p ∨ ∃ o, e = .inv p o
  | 0 => by simp [sched]
  | j + 1 => by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact sched_events j e he
    · simp only [seg, List.mem_cons, List.mem_replicate] at he
      rcases he with rfl | ⟨-, rfl⟩
      · exact Or.inr ⟨(), rfl⟩
      · exact Or.inl rfl

/-- A FAI of `p` from a configuration where `p` is idle, run solo until `p` is idle again,
emits exactly an invocation and a response. -/
lemma exec_fai_solo (C : Cfg A P) (hp : C.ts p = .idle) (n : ℕ)
    (hend : (exec (Wear.ideal k V) C (.inv p () :: List.replicate n (.step p))).1.ts p = .idle) :
    ∃ r, (exec (Wear.ideal k V) C (.inv p () :: List.replicate n (.step p))).2 =
      [.inv C.cnt p (), .res C.cnt r] := by
  rw [exec_cons] at hend ⊢
  have h1 : step1 (Wear.ideal k V) C (.inv p ()) =
      ({ C with ts := Function.update C.ts p (.run C.cnt () (A.start ())), cnt := C.cnt + 1 },
        [.inv C.cnt p ()]) := by simp [step1, hp]
  rw [h1] at hend ⊢
  dsimp only at hend ⊢
  rcases exec_solo (Wear.ideal k V) p n
    ({ C with ts := Function.update C.ts p (.run C.cnt () (A.start ())), cnt := C.cnt + 1 } :
      Cfg A P) C.cnt () (A.start ()) (by simp) with
    ⟨⟨l', hl'⟩, -⟩ | ⟨-, r, hr⟩
  · rw [hl'] at hend; cases hend
  · exact ⟨r, by rw [hr]; rfl⟩

lemma sched_spec : ∀ j, (∀ q, (exec (Wear.ideal k V) (initCfg A P) (sched A p hOF j)).1.ts q = .idle)
    ∧ (exec (Wear.ideal k V) (initCfg A P) (sched A p hOF j)).1.cnt = j ∧
    IsSeqH p (exec (Wear.ideal k V) (initCfg A P) (sched A p hOF j)).2 j
  | 0 => ⟨fun _ => rfl, rfl, IsSeqH.nil⟩
  | j + 1 => by
    obtain ⟨hidle, hcnt, hH⟩ := sched_spec j
    set C := (exec (Wear.ideal k V) (initCfg A P) (sched A p hOF j)).1 with hC
    have hend := nOF_spec A p hOF (sched A p hOF j)
    rw [List.append_assoc, exec_append, ← hC] at hend
    simp only [sched, seg]
    rw [exec_append, ← hC]
    obtain ⟨r, hr⟩ := exec_fai_solo C (hidle p) _ hend
    refine ⟨fun q => ?_, ?_, ?_⟩
    · by_cases hqp : q = p
      · subst hqp; exact hend
      · rw [exec_other_ts _ hqp _ _ (fun e he => by
          simp only [List.mem_cons, List.mem_replicate] at he
          rcases he with rfl | ⟨-, rfl⟩
          · exact Or.inr ⟨(), rfl⟩
          · exact Or.inl rfl)]
        exact hidle q
    · rw [cnt_exec, hr, hcnt]; simp
    · rw [hr, hcnt]
      exact IsSeqH.snoc r hH

end Sched

/-! ### The main argument -/

variable {A : Alg faiObj k V} {p : P} {hOF : ObstructionFree A P (Wear.ideal k V)}

/-- Configuration after `j` sequential FAIs. -/
noncomputable abbrev cfgJ (A : Alg faiObj k V) (p : P) (hOF : ObstructionFree A P (Wear.ideal k V))
    (j : ℕ) : Cfg A P :=
  (exec (Wear.ideal k V) (initCfg A P) (sched A p hOF j)).1

/-- After `j` sequential FAIs, a crash and one more solo FAI (completed after `n` steps), the
last FAI returns `j`. -/
lemma crash_fai (hSL : ∀ es, StrictLinearizable faiObj (hist A P (Wear.ideal k V) es)) (j n : ℕ)
    (hend : (exec (Wear.ideal k V) (step1 (Wear.ideal k V) (cfgJ A p hOF j) .crash).1
      (.inv p () :: List.replicate n (.step p))).1.ts p = .idle) :
    (exec (Wear.ideal k V) (step1 (Wear.ideal k V) (cfgJ A p hOF j) .crash).1
      (.inv p () :: List.replicate n (.step p))).2 = [.inv j p (), .res j j] := by
  obtain ⟨-, hcnt, hH⟩ := sched_spec (A := A) (p := p) (hOF := hOF) j
  set D := (step1 (Wear.ideal k V) (cfgJ A p hOF j) .crash).1 with hD
  have hDp : D.ts p = .idle := rfl
  have hDcnt : D.cnt = j := by simp [hD, step1, hcnt]
  obtain ⟨r, hr⟩ := exec_fai_solo D hDp n hend
  rw [hDcnt] at hr
  rw [hr]
  obtain ⟨L, hL⟩ := hSL (sched A p hOF j ++ [.crash] ++ (.inv p () :: List.replicate n (.step p)))
  have hh : hist A P (Wear.ideal k V)
      (sched A p hOF j ++ [.crash] ++ (.inv p () :: List.replicate n (.step p))) =
      (exec (Wear.ideal k V) (initCfg A P) (sched A p hOF j)).2 ++
        [.crash, .inv j p (), .res j r] := by
    unfold hist
    rw [exec_append, exec_append]
    have hcr : exec (Wear.ideal k V) (cfgJ A p hOF j) [.crash] = (D, [.crash]) := rfl
    rw [hcr]
    dsimp only
    rw [hr]; simp
  rw [hh] at hL
  rw [resp_after_crash hH hL]

/-- Persistent memory changes during every FAI of the sequential schedule. -/
lemma pm_ne (hSL : ∀ es, StrictLinearizable faiObj (hist A P (Wear.ideal k V) es)) (j : ℕ) :
    (cfgJ A p hOF j).pm ≠ (cfgJ A p hOF (j + 1)).pm := by
  intro hpm
  set D := (step1 (Wear.ideal k V) (cfgJ A p hOF j) .crash).1 with hD
  set D' := (step1 (Wear.ideal k V) (cfgJ A p hOF (j + 1)) .crash).1 with hD'
  obtain ⟨-, hcnt, -⟩ := sched_spec (A := A) (p := p) (hOF := hOF) j
  obtain ⟨-, hcnt', -⟩ := sched_spec (A := A) (p := p) (hOF := hOF) (j + 1)
  have hR : Rel 1 D D' := ⟨by simp [hD, hD', step1, hpm], rfl, by simp [hD, hD', step1, hpm],
    fun q => rfl, by simp [hD, hD', step1, hcnt, hcnt']⟩
  -- complete a solo FAI after the second crash
  obtain ⟨n, hn⟩ := hOF (sched A p hOF (j + 1) ++ [.crash] ++ [.inv p ()]) p
  have hend' : (exec (Wear.ideal k V) D' (.inv p () :: List.replicate n (.step p))).1.ts p =
      .idle := by
    rw [List.append_assoc, List.append_assoc, exec_append, List.singleton_append,
      List.singleton_append, exec_cons] at hn
    exact hn
  have h' := crash_fai (hOF := hOF) hSL (j + 1) n hend'
  obtain ⟨hR2, hmap⟩ := hR.exec (.inv p () :: List.replicate n (.step p))
  have hend : (exec (Wear.ideal k V) D (.inv p () :: List.replicate n (.step p))).1.ts p =
      .idle := by
    have := hR2.ts p
    rw [hend'] at this
    cases hs : (exec (Wear.ideal k V) D (.inv p () :: List.replicate n (.step p))).1.ts p with
    | idle => rfl
    | run a o l => rw [hs, shiftTS_run] at this; cases this
  have h := crash_fai (hOF := hOF) hSL j n hend
  rw [h'] at hmap
  rw [h] at hmap
  simp [shiftEv] at hmap

/-- **Theorem 4.4** of [Liu–Golab, PODC'22], repaired (for fetch-and-increment): every
strictly linearizable, obstruction-free FAI implementation from `k` persistent words has a
sequential, crash-free execution of one thread with `k·T + 1` FAIs in which some word is written
back at least `T + 1` times. -/
theorem theorem_4_4_fai (A : Alg faiObj k V) (p : P)
    (hSL : ∀ es, StrictLinearizable faiObj (hist A P (Wear.ideal k V) es))
    (hOF : ObstructionFree A P (Wear.ideal k V)) (T : ℕ) :
    ∃ es : List (Ev k P Unit), (∀ e ∈ es, e = .step p ∨ e = .inv p ()) ∧
      invCount (hist A P (Wear.ideal k V) es) = k * T + 1 ∧
      ∃ i, T + 1 ≤ (exec (Wear.ideal k V) (initCfg A P) es).1.wear i := by
  have hws : ∀ j, j ≤ wearSum (cfgJ A p hOF j) := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hstep : cfgJ A p hOF (j + 1) =
          (exec (Wear.ideal k V) (cfgJ A p hOF j) (seg A p hOF (sched A p hOF j))).1 := by
        simp only [cfgJ, sched]; rw [exec_append]
      obtain ⟨h1, h2⟩ := exec_wearSum (Wear.ideal k V) (seg A p hOF (sched A p hOF j))
        (cfgJ A p hOF j)
      rw [← hstep] at h1 h2
      have hne := pm_ne (p := p) (hOF := hOF) hSL j
      by_contra hc
      have : wearSum (cfgJ A p hOF (j + 1)) = wearSum (cfgJ A p hOF j) := by omega
      exact hne (h2 this).symm
  refine ⟨sched A p hOF (k * T + 1), fun e he => ?_, ?_, ?_⟩
  · rcases sched_events _ e he with h | ⟨o, h⟩
    · exact Or.inl h
    · exact Or.inr (by rw [h])
  · rw [invCount_hist]; exact (sched_spec _).2.1
  · by_contra hc
    push Not at hc
    have h1 := hws (k * T + 1)
    have h2 : wearSum (cfgJ A p hOF (k * T + 1)) ≤ k * T := by
      unfold wearSum
      calc ∑ i, (cfgJ A p hOF (k * T + 1)).wear i ≤ ∑ _i : Fin k, T :=
            Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.1 (hc i)
        _ = k * T := by simp
    omega

/-- Non-vacuity: the counter of Figure 1 satisfies the hypotheses of `theorem_4_4_fai`
(Theorems 4.1 and 4.2), so it too has, for every `T`, an execution with `k·T + 1` FAIs that
writes some word back `T + 1` times. -/
theorem counter_exceeds [NeZero k] [Finite P] (p : P) (T : ℕ) :
    ∃ es : List (Ev k P Unit), (∀ e ∈ es, e = .step p ∨ e = .inv p ()) ∧
      invCount (hist (counter k) P (W₀ k) es) = k * T + 1 ∧
      ∃ i, T + 1 ≤ (exec (W₀ k) (initCfg (counter k) P) es).1.wear i :=
  theorem_4_4_fai (counter k) p theorem_4_1 (theorem_4_2 (W₀ k)).obstructionFree T

/-- The paper's own counter also violates the bound of Theorem 4.4 (by one): with `k` words of
endurance `T` it maintains safety and liveness in all executions with `k·T + 1` FAIs
(`guarantees_kT_succ`); here with `k = T = 1`. -/
theorem theorem_4_4_false_counter [Finite P] : ¬ Theorem44Statement P :=
  fun h => h faiObj 1 ℕ (counter 1) 1 (guarantees_kT_succ 1)

end Podc.WearLeveling
