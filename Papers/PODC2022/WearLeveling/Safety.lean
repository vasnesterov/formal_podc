import Papers.PODC2022.WearLeveling.Counter

/-!
# Theorem 4.1: the counter of Figure 1 is strictly linearizable

Invariant-based proof in the ideal model (no wear-out). The ghost state is the linearization
`L` (operations in the order of their successful CAS at line 5) and the number `m` of its
operations whose CAS is already persistent. The global invariant (`GInv`):

* the cache holds `stair |L|`, persistent memory and the wear counters hold `stair m`;
* `m ≤ |L| ≤ m + 1`: at most one successful CAS is not yet persistent, its cache line is the
  only dirty one;
* operations of `L` at positions `≥ m` have not responded.

The local invariants (`LocInv`) are the facts the helping flushes provide: a thread at line 5
with `iter, index` knows that persistent memory already holds at least
`iter * k + index` increments (lines 2/13 and 9 flushed the words it passed).
The key consequence: when a CAS succeeds, the persistent memory is up to date (`m = |L|`) and
the CAS is the `|L|`-th increment with `|L| = iter * k + index` (the crucial claim of the proof
of Theorem 4.1, with `⌊ℓ / k⌋` and `ℓ mod k` in place of the paper's `⌊ℓ / 2^k⌋`, `ℓ mod 2^k`).
At a crash the non-persistent last operation (if any) is dropped from `L`.
-/

namespace Podc.WearLeveling

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Persistent Alg

variable {k : ℕ} [NeZero k] {P : Type} [DecidableEq P]

lemma pos_inj {it it' : ℕ} {i j : Fin k} (h : it * k + i.val = it' * k + j.val) : i = j := by
  have h1 : (it * k + i.val) % k = i.val := by simp [Nat.mul_add_mod_of_lt i.isLt]
  have h2 : (it' * k + j.val) % k = j.val := by simp [Nat.mul_add_mod_of_lt j.isLt]
  exact Fin.ext (by rw [← h1, ← h2, h])

/-- The ideal wear model. -/
abbrev W₀ (k : ℕ) : Wear k ℕ := Wear.ideal k ℕ

variable (k) in
/-- Local invariant of a thread running operation `a` (with `n = |L|`). -/
def LocInv (L : List (ℕ × Unit)) (m a : ℕ) : CL k → Prop
  | .rd => a ∉ L.map Prod.fst
  | .fl it => a ∉ L.map Prod.fst ∧ it ≤ stair k L.length (last k)
  | .cas it idx => a ∉ L.map Prod.fst ∧ it * k + idx.val ≤ m
  | .flF it idx => a ∉ L.map Prod.fst ∧ it * k + idx.val ≤ m ∧ it * k + idx.val < L.length
  | .flS it idx => L[it * k + idx.val]? = some (a, ())
  | .ret it idx => L[it * k + idx.val]? = some (a, ()) ∧ it * k + idx.val < m

lemma LocInv.mono {L : List (ℕ × Unit)} {m m' a : ℕ} (hm : m ≤ m') :
    ∀ {l : CL k}, LocInv k L m a l → LocInv k L m' a l
  | .rd, h => h
  | .fl _, h => h
  | .cas _ _, h => ⟨h.1, le_trans h.2 hm⟩
  | .flF _ _, h => ⟨h.1, le_trans h.2.1 hm, h.2.2⟩
  | .flS _ _, h => h
  | .ret _ _, h => ⟨h.1, lt_of_lt_of_le h.2 hm⟩

/-- Global invariant. -/
structure GInv (C : Cfg (counter k) P) (h : List (HEv P Unit ℕ)) (L : List (ℕ × Unit)) (m : ℕ) :
    Prop where
  hinv : HInv C h
  lin : IsStrictLin faiObj h L
  m_le : m ≤ L.length
  le_m : L.length ≤ m + 1
  cache_eq : C.cache = stair k L.length
  pm_eq : C.pm = stair k m
  wear_eq : C.wear = stair k m
  dirty_iff : ∀ i, C.dirty i = true ↔ (L.length = m + 1 ∧ ∃ it, m = it * k + i.val)
  unpers : ∀ n x, m ≤ n → L[n]? = some x → ∀ r, HEv.res x.1 r ∉ h

/-- The full invariant. -/
def CInv (C : Cfg (counter k) P) (h : List (HEv P Unit ℕ)) (L : List (ℕ × Unit)) (m : ℕ) :
    Prop :=
  GInv C h L m ∧ ∀ p a o l, C.ts p = .run a o l → LocInv k L m a l

lemma GInv.ids_lt {C : Cfg (counter k) P} {h L m} (hG : GInv C h L m) :
    ∀ b ∈ L.map Prod.fst, b < C.cnt := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  obtain ⟨q, hq⟩ := hG.lin.inv_of_mem x hx
  exact hG.hinv.inv_lt _ _ _ hq

/-- A clean word holds the same value in the cache and in persistent memory. -/
lemma GInv.stair_eq_of_clean {C : Cfg (counter k) P} {h L m} (hG : GInv C h L m) {i : Fin k}
    (hi : C.dirty i = false) : stair k m i = stair k L.length i := by
  rcases Nat.lt_or_ge m L.length with hlt | hge
  · have hL : L.length = m + 1 := by have := hG.le_m; omega
    obtain ⟨it, j, hm⟩ := exists_pos (k := k) m
    have hij : i ≠ j := by
      rintro rfl
      have := (hG.dirty_iff i).2 ⟨hL, it, hm⟩
      simp [hi] at this
    rw [hL, hm, stair_succ_ne it hij]
  · have : m = L.length := le_antisymm hG.m_le hge
    rw [this]

/-- Write-back of a word (by a flush or an eviction) preserves the global invariant, with a
possibly larger persisted count `m'`, and afterwards the word is up to date. -/
lemma GInv.writeBack {C : Cfg (counter k) P} {h L m} (hG : GInv C h L m) (i : Fin k) :
    ∃ m', m ≤ m' ∧ stair k m' i = stair k L.length i ∧
      GInv (Alg.writeBack (W₀ k) C i) h L m' := by
  by_cases hd : C.dirty i = true
  · obtain ⟨hL, it, hm⟩ := (hG.dirty_iff i).1 hd
    refine ⟨m + 1, by omega, by rw [hL], ?_⟩
    have hwb : Alg.writeBack (W₀ k) C i =
        { C with pm := Function.update C.pm i (C.cache i),
                 wear := Function.update C.wear i (C.wear i + 1),
                 dirty := Function.update C.dirty i false } := by
      simp [Alg.writeBack, hd, Wear.ideal]
    rw [hwb]
    refine ⟨?_, hG.lin, by omega, by omega, hG.cache_eq, ?_, ?_, ?_, ?_⟩
    · have := hG.hinv
      exact ⟨this.inv_lt, this.res_lt, this.run_inv, this.run_notEnded, this.run_inj⟩
    · simp only [hG.pm_eq, hG.cache_eq, hL, hm, stair_succ]
      simp
    · simp only [hG.wear_eq, hm, stair_succ, stair_pos_self]
    · intro j
      simp only
      by_cases hji : j = i
      · subst hji; simp; intro h1; omega
      · rw [Function.update_of_ne hji, hG.dirty_iff j]
        constructor
        · rintro ⟨-, it', hm'⟩
          exact absurd (pos_inj (hm.symm.trans hm')).symm hji
        · rintro ⟨h1, -⟩; omega
    · intro n x hn hx r
      exact hG.unpers n x (by omega) hx r
  · have hd' : C.dirty i = false := by simpa using hd
    refine ⟨m, le_rfl, hG.stair_eq_of_clean hd', ?_⟩
    simpa [Alg.writeBack, hd'] using hG

lemma cinv_of_update {C C' : Cfg (counter k) P} {h h' L L' m m'} (hC : CInv C h L m)
    (hG' : GInv C' h' L' m') {p : P} {a : ℕ} {o : Unit} {l' : CL k}
    (hts : C'.ts = Function.update C.ts p (.run a o l')) (hl' : LocInv k L' m' a l')
    (hoth : ∀ q b o' l, q ≠ p → C.ts q = .run b o' l → LocInv k L m b l → LocInv k L' m' b l) :
    CInv C' h' L' m' := by
  refine ⟨hG', fun q b o' l hq => ?_⟩
  rw [hts] at hq
  by_cases hqp : q = p
  · subst hqp; simp at hq; obtain ⟨rfl, -, rfl⟩ := hq; exact hl'
  · simp only [Function.update_of_ne hqp] at hq
    exact hoth q b o' l hqp hq (hC.2 q b o' l hq)

lemma GInv.congr {C C' : Cfg (counter k) P} {h h' L m} (hG : GInv C h L m) (hH : HInv C' h')
    (hh : h' = h) (hc : C'.cache = C.cache) (hpm : C'.pm = C.pm) (hw : C'.wear = C.wear)
    (hd : C'.dirty = C.dirty) : GInv C' h' L m := by
  subst hh
  exact ⟨hH, hG.lin, hG.m_le, hG.le_m, hc ▸ hG.cache_eq, hpm ▸ hG.pm_eq, hw ▸ hG.wear_eq,
    hd ▸ hG.dirty_iff, hG.unpers⟩

section Steps

variable {C : Cfg (counter k) P} {h : List (HEv P Unit ℕ)} {L : List (ℕ × Unit)} {m : ℕ}
  {p : P} {a : ℕ} {o : Unit}

/-- Line 1 / 12. -/
lemma CInv.step_rd (hC : CInv C h L m) (hp : C.ts p = .run a o CL.rd) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.step p)).1 (h ++ (Alg.step1 (W₀ k) C (.step p)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.step p)
  have heq : Alg.step1 (W₀ k) C (.step p) =
      ({ C with ts := (Function.update C.ts p (.run a o (CL.fl (C.cache (last k))))) }, []) := by
    simp [Alg.step1, hp, counter]
  rw [heq] at hH ⊢
  refine ⟨L, m, cinv_of_update hC (hC.1.congr hH (by simp) rfl rfl rfl rfl) rfl ?_
    (fun _ _ _ _ _ _ hl => hl)⟩
  exact ⟨hC.2 p a o _ hp, by rw [hC.1.cache_eq]⟩

/-- Line 2 / 13. -/
lemma CInv.step_fl (hC : CInv C h L m) {it : ℕ} (hp : C.ts p = .run a o (CL.fl it)) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.step p)).1 (h ++ (Alg.step1 (W₀ k) C (.step p)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.step p)
  have heq : Alg.step1 (W₀ k) C (.step p) =
      ({ Alg.writeBack (W₀ k) C (last k) with
          ts := (Function.update C.ts p (.run a o (CL.cas it 0))) }, []) := by
    simp [Alg.step1, hp, counter]
  rw [heq] at hH ⊢
  obtain ⟨m', hmm', hst, hG'⟩ := hC.1.writeBack (last k)
  have hl : LocInv k L m a (CL.fl it) := hC.2 p a o _ hp
  refine ⟨L, m', cinv_of_update hC (hG'.congr hH (by simp) rfl rfl rfl rfl) rfl ?_
    (fun _ _ _ _ _ _ hl => hl.mono hmm')⟩
  refine ⟨hl.1, ?_⟩
  have h1 := hl.2
  rw [← hst, le_stair_iff] at h1
  simp only [last_val] at h1
  have := k_pos k
  show it * k + 0 ≤ m'
  omega

/-- Line 5, failed CAS. -/
lemma CInv.step_cas_fail (hC : CInv C h L m) {it : ℕ} {idx : Fin k}
    (hp : C.ts p = .run a o (CL.cas it idx)) (hc : C.cache idx ≠ it) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.step p)).1 (h ++ (Alg.step1 (W₀ k) C (.step p)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.step p)
  have heq : Alg.step1 (W₀ k) C (.step p) =
      ({ C with ts := (Function.update C.ts p (.run a o (CL.flF it idx))) }, []) := by
    simp [Alg.step1, hp, counter, hc]
  rw [heq] at hH ⊢
  have hl : LocInv k L m a (CL.cas it idx) := hC.2 p a o _ hp
  refine ⟨L, m, cinv_of_update hC (hC.1.congr hH (by simp) rfl rfl rfl rfl) rfl ?_
    (fun _ _ _ _ _ _ hl => hl)⟩
  refine ⟨hl.1, hl.2, ?_⟩
  rw [hC.1.cache_eq] at hc
  have h1 := hl.2
  have h2 := hC.1.m_le
  -- `it ≤ stair |L| idx` and `≠`, hence `it + 1 ≤ stair |L| idx`
  have h3 : it ≤ stair k L.length idx := by rw [le_stair_iff]; have := k_pos k; omega
  have h4 : it + 1 ≤ stair k L.length idx := by omega
  rw [le_stair_iff, Nat.succ_mul] at h4
  omega

/-- Line 5, successful CAS: the linearization point. -/
lemma CInv.step_cas_succ (hC : CInv C h L m) {it : ℕ} {idx : Fin k}
    (hp : C.ts p = .run a o (CL.cas it idx)) (hc : C.cache idx = it) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.step p)).1 (h ++ (Alg.step1 (W₀ k) C (.step p)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.step p)
  have heq : Alg.step1 (W₀ k) C (.step p) =
      ({ C with cache := Function.update C.cache idx (it + 1),
                dirty := Function.update C.dirty idx true,
                ts := (Function.update C.ts p (.run a o (CL.flS it idx))) }, []) := by
    simp [Alg.step1, hp, counter, hc]
  rw [heq] at hH ⊢
  simp only [List.append_nil] at hH ⊢
  have hG := hC.1
  have hl : LocInv k L m a (CL.cas it idx) := hC.2 p a o _ hp
  -- the key claim: everything is persistent and `|L| = it * k + idx`
  have hn : L.length ≤ it * k + idx.val := by
    have := hG.cache_eq ▸ hc
    have h1 : stair k L.length idx ≤ it := le_of_eq this
    rwa [stair_le_iff] at h1
  have hm : m = L.length := by have := hG.m_le; have := hl.2; omega
  have hnpos : L.length = it * k + idx.val := by have := hl.2; omega
  have ho : o = () := rfl
  subst ho
  have hane := hG.hinv.run_notEnded _ _ _ _ hp
  have hainv := hG.hinv.run_inv _ _ _ _ hp
  refine ⟨L ++ [(a, ())], m, ?_⟩
  refine cinv_of_update hC ⟨hH, hG.lin.push hainv hl.1 hane, by simp; omega, by simp; omega,
    ?_, hG.pm_eq, hG.wear_eq, ?_, ?_⟩ rfl ?_ ?_
  · simp only [List.length_append, List.length_singleton, hG.cache_eq, hnpos, stair_succ]
  · intro j
    simp only [List.length_append, List.length_singleton]
    by_cases hj : j = idx
    · subst hj; simp only [Function.update_self, true_iff]; exact ⟨by omega, it, by omega⟩
    · rw [Function.update_of_ne hj, hG.dirty_iff j]
      constructor
      · rintro ⟨h1, -⟩; omega
      · rintro ⟨-, it', hm'⟩
        exact absurd (pos_inj (hnpos ▸ hm ▸ hm' : it * k + idx.val = it' * k + j.val)).symm hj
  · intro n x hn' hx r hr
    rcases Nat.lt_or_ge n L.length with hlt | hge
    · omega
    · have : n = L.length := by
        have := (List.getElem?_eq_some_iff.1 hx).1; simp at this; omega
      subst this
      rw [List.getElem?_append_right le_rfl] at hx
      simp at hx; subst hx
      exact not_mem_res_of_notEnded hane r hr
  · show (L ++ [(a, ())])[it * k + idx.val]? = some (a, ())
    rw [← hnpos, List.getElem?_append_right le_rfl]; simp
  · intro q b o' l hqp hq hl'
    have hb : b ≠ a := by
      rintro rfl; exact hqp (hG.hinv.run_inj _ _ _ _ _ _ _ hq hp)
    have hb' : b ∉ (L ++ [(a, ())]).map Prod.fst ↔ b ∉ L.map Prod.fst := by simp [hb]
    cases l with
    | rd => exact hb'.2 hl'
    | fl it' =>
      refine ⟨hb'.2 hl'.1, le_trans hl'.2 (stair_mono (by simp) _)⟩
    | cas it' idx' => exact ⟨hb'.2 hl'.1, hl'.2⟩
    | flF it' idx' => exact ⟨hb'.2 hl'.1, hl'.2.1, by have := hl'.2.2; simp; omega⟩
    | flS it' idx' =>
      show (L ++ [(a, ())])[it' * k + idx'.val]? = some (b, ())
      have hlt := (List.getElem?_eq_some_iff.1 hl').1
      rw [List.getElem?_append_left hlt]; exact hl'
    | ret it' idx' =>
      refine ⟨?_, hl'.2⟩
      have hlt := (List.getElem?_eq_some_iff.1 hl'.1).1
      rw [List.getElem?_append_left hlt]; exact hl'.1

/-- Line 6. -/
lemma CInv.step_flS (hC : CInv C h L m) {it : ℕ} {idx : Fin k}
    (hp : C.ts p = .run a o (CL.flS it idx)) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.step p)).1 (h ++ (Alg.step1 (W₀ k) C (.step p)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.step p)
  have heq : Alg.step1 (W₀ k) C (.step p) =
      ({ Alg.writeBack (W₀ k) C idx with
          ts := (Function.update C.ts p (.run a o (CL.ret it idx))) }, []) := by
    simp [Alg.step1, hp, counter]
  rw [heq] at hH ⊢
  obtain ⟨m', hmm', hst, hG'⟩ := hC.1.writeBack idx
  have hl : LocInv k L m a (CL.flS it idx) := hC.2 p a o _ hp
  refine ⟨L, m', cinv_of_update hC (hG'.congr hH (by simp) rfl rfl rfl rfl) rfl ⟨hl, ?_⟩
    (fun _ _ _ _ _ _ hl => hl.mono hmm')⟩
  have hlt := (List.getElem?_eq_some_iff.1 (show L[it * k + idx.val]? = some (a, ()) from hl)).1
  have h1 : it + 1 ≤ stair k L.length idx := by rw [le_stair_iff, Nat.succ_mul]; omega
  rw [← hst, le_stair_iff, Nat.succ_mul] at h1
  omega

/-- Lines 9–11. -/
lemma CInv.step_flF (hC : CInv C h L m) {it : ℕ} {idx : Fin k}
    (hp : C.ts p = .run a o (CL.flF it idx)) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.step p)).1 (h ++ (Alg.step1 (W₀ k) C (.step p)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.step p)
  have heq : Alg.step1 (W₀ k) C (.step p) =
      ({ Alg.writeBack (W₀ k) C idx with
          ts := (Function.update C.ts p (.run a o (nextPC it idx))) }, []) := by
    simp [Alg.step1, hp, counter]
  rw [heq] at hH ⊢
  obtain ⟨m', hmm', hst, hG'⟩ := hC.1.writeBack idx
  have hl : LocInv k L m a (CL.flF it idx) := hC.2 p a o _ hp
  refine ⟨L, m', cinv_of_update hC (hG'.congr hH (by simp) rfl rfl rfl rfl) rfl ?_
    (fun _ _ _ _ _ _ hl => hl.mono hmm')⟩
  have h1 : it + 1 ≤ stair k L.length idx := by
    have := hl.2.2; rw [le_stair_iff, Nat.succ_mul]; omega
  rw [← hst, le_stair_iff, Nat.succ_mul] at h1
  by_cases hk : idx.val + 1 < k
  · rw [nextPC_of_lt k hk]; exact ⟨hl.1, by show it * k + (idx.val + 1) ≤ m'; omega⟩
  · rw [nextPC_of_not_lt k hk]; exact hl.1

/-- Line 7: the response. -/
lemma CInv.step_ret (hC : CInv C h L m) {it : ℕ} {idx : Fin k}
    (hp : C.ts p = .run a o (CL.ret it idx)) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.step p)).1 (h ++ (Alg.step1 (W₀ k) C (.step p)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.step p)
  have heq : Alg.step1 (W₀ k) C (.step p) =
      ({ C with ts := (Function.update C.ts p .idle) }, [.res a (idx.val + it * k)]) := by
    simp [Alg.step1, hp, counter]
  rw [heq] at hH ⊢
  have hG := hC.1
  have hl : LocInv k L m a (CL.ret it idx) := hC.2 p a o _ hp
  obtain ⟨hget, hpos⟩ := hl
  set pos := it * k + idx.val with hposdef
  have hlt := (List.getElem?_eq_some_iff.1 hget).1
  have hsplit : L = L.take pos ++ (a, ()) :: L.drop (pos + 1) := by
    conv_lhs => rw [← List.take_append_drop pos L]
    congr 1
    rw [List.drop_eq_getElem_cons hlt]
    congr 1
    exact (List.getElem?_eq_some_iff.1 hget).2
  refine ⟨L, m, ⟨⟨hH, hG.lin.append_res hsplit ?_, hG.m_le, hG.le_m, hG.cache_eq, hG.pm_eq,
    hG.wear_eq, hG.dirty_iff, ?_⟩, ?_⟩⟩
  · simp [faiObj_runOps, List.length_take, hposdef]; omega
  · intro n x hn hx r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hG.unpers n x hn hx r hr
    · simp at hr
      -- `x.1 = a`, but `a` is at position `pos < m ≤ n`
      have hnd := hG.lin.nodup
      have h1 : (L.map Prod.fst)[n]? = some a := by simp [hx, hr.1]
      have h2 : (L.map Prod.fst)[pos]? = some a := by simp [hget]
      have := (List.Nodup.getElem?_inj (by simpa using hlt) hnd).1 (h2.trans h1.symm)
      omega
  · intro q b o' l hq
    by_cases hqp : q = p
    · subst hqp; simp at hq
    · simp only [Function.update_of_ne hqp] at hq
      exact hC.2 q b o' l hq

/-- Invocation. -/
lemma CInv.step_inv (hC : CInv C h L m) (q : P) (o' : Unit) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.inv q o')).1 (h ++ (Alg.step1 (W₀ k) C (.inv q o')).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.inv q o')
  have hG := hC.1
  cases hq : C.ts q with
  | run b o'' l =>
    have heq : Alg.step1 (W₀ k) C (.inv q o') = (C, []) := by simp [Alg.step1, hq]
    rw [heq]; simpa using ⟨L, m, hC⟩
  | idle =>
    have heq : Alg.step1 (W₀ k) C (.inv q o') =
        ({ C with ts := Function.update C.ts q (.run C.cnt o' CL.rd), cnt := C.cnt + 1 },
          [.inv C.cnt q o']) := by simp [Alg.step1, hq, counter]
    rw [heq] at hH ⊢
    have hfresh : C.cnt ∉ L.map Prod.fst := fun hc => by have := hG.ids_lt _ hc; omega
    refine ⟨L, m, cinv_of_update hC ⟨hH, hG.lin.append_inv hfresh, hG.m_le, hG.le_m,
      hG.cache_eq, hG.pm_eq, hG.wear_eq, hG.dirty_iff, ?_⟩ rfl hfresh
      (fun _ _ _ _ _ _ hl => hl)⟩
    intro n x hn hx r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hG.unpers n x hn hx r hr
    · simp at hr

/-- Spontaneous eviction. -/
lemma CInv.step_evict (hC : CInv C h L m) (i : Fin k) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C (.evict i)).1 (h ++ (Alg.step1 (W₀ k) C (.evict i)).2)
      L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) (.evict i)
  have heq : Alg.step1 (W₀ k) C (.evict i) = (Alg.writeBack (W₀ k) C i, []) := rfl
  rw [heq] at hH ⊢
  obtain ⟨m', hmm', -, hG'⟩ := hC.1.writeBack i
  refine ⟨L, m', hG'.congr hH (by simp) rfl rfl rfl rfl, fun q b o' l hq => ?_⟩
  rw [writeBack_ts] at hq
  exact (hC.2 q b o' l hq).mono hmm'

/-- System-wide crash: the non-persistent last operation (if any) is dropped. -/
lemma CInv.step_crash (hC : CInv C h L m) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C .crash).1 (h ++ (Alg.step1 (W₀ k) C .crash).2) L' m' := by
  have hH := hC.1.hinv.step1 (W₀ k) .crash
  have hG := hC.1
  have heq : Alg.step1 (W₀ k) C .crash =
      ({ C with cache := C.pm, dirty := fun _ => false, ts := fun _ => .idle }, [.crash]) := rfl
  rw [heq] at hH ⊢
  have hlen : (L.take m).length = m := by simp [hG.m_le]
  refine ⟨L.take m, m, ⟨hH, hG.lin.append_crash (List.take_prefix _ _) ?_, by omega, by omega,
    ?_, hG.pm_eq, hG.wear_eq, ?_, ?_⟩, by simp⟩
  · intro x hx hnot r hr
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hx
    rcases Nat.lt_or_ge n m with hlt | hge
    · apply hnot
      apply List.mem_map_of_mem
      exact List.mem_iff_getElem?.2 ⟨n, by rw [List.getElem?_take_of_lt hlt]; exact hn⟩
    · exact hG.unpers n x hge hn r hr
  · simp only [hlen]; exact hG.pm_eq
  · intro i; simp [hlen]
  · intro n x hn hx
    have := (List.getElem?_eq_some_iff.1 hx).1; omega

/-- One event preserves the invariant. -/
lemma CInv.step1 (hC : CInv C h L m) (e : Ev k P Unit) :
    ∃ L' m', CInv (Alg.step1 (W₀ k) C e).1 (h ++ (Alg.step1 (W₀ k) C e).2) L' m' := by
  cases e with
  | inv q o' => exact hC.step_inv q o'
  | evict i => exact hC.step_evict i
  | crash => exact hC.step_crash
  | step q =>
    cases hq : C.ts q with
    | idle =>
      have heq : Alg.step1 (W₀ k) C (.step q) = (C, []) := by simp [Alg.step1, hq]
      rw [heq]; simpa using ⟨L, m, hC⟩
    | run b o' l =>
      cases l with
      | rd => exact hC.step_rd hq
      | fl it => exact hC.step_fl hq
      | cas it idx =>
        by_cases hc : C.cache idx = it
        · exact hC.step_cas_succ hq hc
        · exact hC.step_cas_fail hq hc
      | flS it idx => exact hC.step_flS hq
      | ret it idx => exact hC.step_ret hq
      | flF it idx => exact hC.step_flF hq

end Steps

lemma cInv_init : CInv (initCfg (counter k) P) [] [] 0 := by
  refine ⟨⟨hInv_init, IsStrictLin.nil, le_rfl, by simp, ?_, ?_, ?_, ?_, by simp⟩, by
    simp [initCfg]⟩
  · funext i; simp [initCfg, counter, stair_zero]
  · funext i; simp [initCfg, counter, stair_zero]
  · funext i; simp [initCfg, stair_zero]
  · intro i; simp [initCfg]

/-- The invariant holds along every execution of the ideal model. -/
theorem cInv_exec (es : List (Ev k P Unit)) :
    ∃ L m, CInv (exec (W₀ k) (initCfg (counter k) P) es).1
      (exec (W₀ k) (initCfg (counter k) P) es).2 L m := by
  induction es using List.reverseRecOn with
  | nil => exact ⟨[], 0, cInv_init⟩
  | append_singleton es e ih =>
    obtain ⟨L, m, hC⟩ := ih
    rw [exec_concat]
    exact hC.step1 e

/-- **Theorem 4.1** of [Liu–Golab, PODC'22] (with unbounded words): the counter of Figure 1 is
strictly linearizable — every history of the persistent-memory model with a volatile write-back
cache and system-wide crashes is strictly linearizable w.r.t. a fetch-and-increment counter. -/
theorem theorem_4_1 (es : List (Ev k P Unit)) :
    StrictLinearizable faiObj (hist (counter k) P (W₀ k) es) := by
  obtain ⟨L, m, hC⟩ := cInv_exec (k := k) (P := P) es
  exact ⟨L, hC.1.lin⟩

end Podc.WearLeveling