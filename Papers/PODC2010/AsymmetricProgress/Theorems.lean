import Papers.PODC2010.AsymmetricProgress.LiveCons

/-!
# Theorems 1–4 and Corollary 1

* `theorem1` — no `(n,1)`-live consensus from read/write-like objects (atomic registers) and
  objects with at most `n − 1` ports (in particular `(n−1, n−1)`-live consensus objects);
* `theorem4` — the same for consensus that is obstruction-free for all processes and fault-free
  for one process;
* `theorem2` — no `(n, x+1)`-live consensus from atomic registers and `(n, x)`-live consensus
  objects (`x < n − 1`), the base objects behaving as the legal adversarial objects `advCons`;
* `theorem3_lower`, `theorem3_upper` — the consensus number of `(n, x)`-live consensus objects is
  `x + 1`;
* `corollary1_top` — `(n, n−1)`-liveness is wait-freedom; the strictness part of Corollary 1 is
  `theorem2` (which also covers `x = 0`), monotonicity is `Live.mono`.
-/

namespace Podc.AsymmetricProgress

set_option linter.unusedSectionVars false

variable {n : ℕ}

section General

variable {ι : Type} [DecidableEq ι] {T : ι → BObj n} {A : Alg n T}

/-- Lemmas 4 and 6 combined: a consensus algorithm that is obstruction-free for everybody and
wait-free for some process reaches a configuration where all processes are poised on one object
that is not read/write-like. -/
theorem exists_all_poised_of_wFree (hS : Safe A) (hOF : ∀ r, OFree A r) (hn : 2 ≤ n) {p : Fin n}
    (hWF : WFree A p) :
    ∃ (D : Cfg A) (i : ι), Reachable D ∧ ¬ (T i).RWLike ∧ ∀ r, D.objOf r = some i := by
  obtain ⟨C, hC, hb, hd⟩ := lemma4 hS hOF hn hWF
  obtain ⟨D, -, -, i, hD, -, -, -, -, -, hrw, hall⟩ := lemma6 hS hOF hC hb hd
  exact ⟨D, i, hD, hrw, hall⟩

/-- Lemmas 7 and 9 combined. -/
theorem exists_all_poised_of_fFree (hS : Safe A) (hOF : ∀ r, OFree A r) (hn : 2 ≤ n)
    {p₀ : Fin n} (hFF : FFree A p₀) :
    ∃ (D : Cfg A) (i : ι), Reachable D ∧ ¬ (T i).RWLike ∧ ∀ r, D.objOf r = some i := by
  obtain ⟨C, p, hC, hb, hd⟩ := lemma7 hS hOF hn hFF
  obtain ⟨D, -, -, i, hD, -, -, -, -, -, hrw, hall⟩ := lemma6 hS hOF hC hb hd
  exact ⟨D, i, hD, hrw, hall⟩

lemma exists_not_mem_of_ncard (hn : 1 ≤ n) {Y : Set (Fin n)} (hY : Y.ncard ≤ n - 1) :
    ∃ r, r ∉ Y := by
  by_contra h
  push Not at h
  have : Y = Set.univ := Set.eq_univ_of_forall h
  rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hY
  omega

/-- **Theorem 1** of the paper. There is no `(n, 1)`-live consensus algorithm (wait-free for one
process, obstruction-free for all) — more generally, no consensus algorithm that is
obstruction-free for all and wait-free for the processes of a nonempty set `X` — using
read/write-like objects (e.g. atomic registers) and any objects that can be accessed by at most
`n − 1` processes (e.g. `(n−1, n−1)`-live consensus objects). Objects are arbitrary
(deterministic, possibly blocking) `BObj`s; `Y i` is the set of ports of object `i`. -/
theorem theorem1 (hn : 2 ≤ n) (Y : ι → Set (Fin n)) (hY : ∀ i, (T i).RWLike ∨ (Y i).ncard ≤ n - 1)
    (hports : RespectsPorts A Y) {X : Set (Fin n)} (hX : X.Nonempty) : ¬ Live A X := by
  rintro ⟨hS, hOF, hWF⟩
  obtain ⟨p, hp⟩ := hX
  obtain ⟨D, i, hD, hrw, hall⟩ := exists_all_poised_of_wFree hS hOF hn (hWF p hp)
  obtain ⟨r, hr⟩ := exists_not_mem_of_ncard (by omega) ((hY i).resolve_left hrw)
  exact hr (hports D hD r i (hall r))

/-- Theorem 1 with the paper's `(n, 1)`-liveness (`X = {p}`). -/
theorem theorem1_single (hn : 2 ≤ n) (Y : ι → Set (Fin n))
    (hY : ∀ i, (T i).RWLike ∨ (Y i).ncard ≤ n - 1) (hports : RespectsPorts A Y) (p : Fin n) :
    ¬ Live A {p} :=
  theorem1 hn Y hY hports (Set.singleton_nonempty p)

/-- **Theorem 4** of the paper. There is no consensus algorithm that is obstruction-free for all
processes and fault-free for one process `p₀`, using read/write-like objects (e.g. atomic
registers) and any objects with at most `n − 1` ports (e.g. `(n−1, n−1)`-live consensus
objects). -/
theorem theorem4 (hn : 2 ≤ n) (Y : ι → Set (Fin n)) (hY : ∀ i, (T i).RWLike ∨ (Y i).ncard ≤ n - 1)
    (hports : RespectsPorts A Y) (hS : Safe A) (hOF : ∀ r, OFree A r) (p₀ : Fin n)
    (hFF : FFree A p₀) : False := by
  obtain ⟨D, i, hD, hrw, hall⟩ := exists_all_poised_of_fFree hS hOF hn hFF
  obtain ⟨r, hr⟩ := exists_not_mem_of_ncard (by omega) ((hY i).resolve_left hrw)
  exact hr (hports D hD r i (hall r))

/-- Wait-freedom implies fault-freedom (so Theorem 4 implies Theorem 1). -/
lemma WFree.fFree {p : Fin n} (h : WFree A p) : FFree A p := fun x e he => h x e (he p)

/-- Wait-freedom implies obstruction-freedom. -/
lemma WFree.oFree {p : Fin n} (h : WFree A p) : OFree A p := by
  rintro C ⟨x, σ, rfl⟩
  let e : ℕ → Fin n := fun t => if h : t < σ.length then σ[t] else p
  have hpre : ∀ k, pre e (σ.length + k) = σ ++ List.replicate k p := by
    intro k
    rw [pre_add]
    congr 1
    · apply List.ext_getElem (by simp [length_pre])
      intro l h1 _
      simp only [pre, List.getElem_map, List.getElem_range, e]
      rw [length_pre] at h1
      simp [h1]
    · apply List.ext_getElem (by simp [length_pre])
      intro l h1 _
      simp [pre, e]
  obtain ⟨t, v, ht⟩ := h x e (fun M => ⟨σ.length + M, by omega, by simp [e]⟩)
  refine ⟨t, v, ?_⟩
  have := out_pre_mono (show t ≤ σ.length + t by omega) ht
  rwa [hpre, run_append] at this

/-- An infinite schedule from a reachable configuration in which `w` takes infinitely many steps
but never outputs refutes wait-freedom of `w`. -/
lemma not_wFree_of_stuck {x : Fin n → Bool} {σ : List (Fin n)} (alt : ℕ → Fin n) {w : Fin n}
    (hw : ∀ M, ∃ t ≥ M, alt t = w)
    (hstuck : ∀ t v, ¬ (run (run (initCfg A x) σ) (pre alt t)).Out w v) : ¬ WFree A w := by
  intro hWF
  let e : ℕ → Fin n := fun t => if h : t < σ.length then σ[t] else alt (t - σ.length)
  have hpre : ∀ k, pre e (σ.length + k) = σ ++ pre alt k := by
    intro k
    rw [pre_add]
    congr 1
    · apply List.ext_getElem (by simp [length_pre])
      intro l h1 _
      simp only [pre, List.getElem_map, List.getElem_range, e]
      rw [length_pre] at h1
      simp [h1]
    · apply List.ext_getElem (by simp [length_pre])
      intro l h1 _
      simp [pre, e]
  obtain ⟨t, v, ht⟩ := hWF x e (fun M => by
    obtain ⟨t, ht, hte⟩ := hw M
    exact ⟨σ.length + t, by omega, by simp [e, hte]⟩)
  have := out_pre_mono (show t ≤ σ.length + t by omega) ht
  rw [hpre, run_append] at this
  exact hstuck t v this

/-- If every process other than `r` is wait-free and `r` is obstruction-free, then `r` is
wait-free: eventually every other process has decided or stopped, and then `r` runs alone. -/
theorem wFree_of_wFree_others {r : Fin n} (hOF : OFree A r) (hWF : ∀ q, q ≠ r → WFree A q) :
    WFree A r := by
  intro x e he
  classical
  -- a time after which no other process changes the configuration
  have hq : ∀ q, ∃ T, q ≠ r → (∀ t ≥ T, e t ≠ q) ∨ ∃ v, (run (initCfg A x) (pre e T)).Out q v := by
    intro q
    by_cases hqr : q = r
    · exact ⟨0, fun h => absurd hqr h⟩
    by_cases hinf : ∀ M, ∃ t ≥ M, e t = q
    · obtain ⟨T, v, hT⟩ := hWF q hqr x e hinf
      exact ⟨T, fun _ => Or.inr ⟨v, hT⟩⟩
    · push Not at hinf
      obtain ⟨M, hM⟩ := hinf
      exact ⟨M, fun _ => Or.inl hM⟩
  choose Tq hTq using hq
  set T := Finset.univ.sup Tq
  have hTle : ∀ q, Tq q ≤ T := fun q => Finset.le_sup (Finset.mem_univ q)
  set CT := run (initCfg A x) (pre e T)
  let cnt : ℕ → ℕ := fun m => (pre (fun t => e (T + t)) m).count r
  have hcnt_succ : ∀ m, cnt (m + 1) = cnt m + if e (T + m) = r then 1 else 0 := by
    intro m
    simp only [cnt, pre_succ, List.count_append, List.count_singleton]
    split_ifs <;> simp_all
  have hrun : ∀ m, run (initCfg A x) (pre e (T + m)) = run CT (List.replicate (cnt m) r) := by
    intro m
    induction m with
    | zero => simp [cnt, pre_zero, CT]
    | succ m ih =>
      rw [← Nat.add_assoc, pre_succ, run_concat, ih, hcnt_succ]
      by_cases her : e (T + m) = r
      · simp only [her, ↓reduceIte, run_replicate_succ]
      · rw [ite_eq_right her, Nat.add_zero]
        rcases hTq (e (T + m)) her with h | ⟨v, hv⟩
        · exact absurd rfl (h (T + m) (by have := hTle (e (T + m)); omega))
        · have hv' := out_pre_mono (show Tq (e (T + m)) ≤ T + m by
            have := hTle (e (T + m)); omega) hv
          rw [ih] at hv'
          exact step_of_out hv'
  have hmono : ∀ m m', m ≤ m' → cnt m ≤ cnt m' := by
    intro m m' h
    induction h with
    | refl => exact le_rfl
    | step _ ih => rw [hcnt_succ]; omega
  have hgrow : ∀ k, ∃ m, k ≤ cnt m := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨t, ht, hte⟩ := he (T + m)
      refine ⟨t - T + 1, ?_⟩
      rw [hcnt_succ, show T + (t - T) = t by omega, ite_eq_left hte]
      have := hmono m (t - T) (by omega)
      omega
  obtain ⟨k, v, hk⟩ := hOF CT ⟨x, _, rfl⟩
  obtain ⟨m, hm⟩ := hgrow k
  refine ⟨T + m, v, ?_⟩
  rw [hrun, show cnt m = k + (cnt m - k) by omega, List.replicate_add, run_append]
  exact hk.run _

/-- Monotonicity: an `(n, X)`-live implementation is `(n, X')`-live for every `X' ⊆ X`. -/
lemma Live.mono {X X' : Set (Fin n)} (h : Live A X) (hX : X' ⊆ X) : Live A X' :=
  ⟨h.1, h.2.1, fun p hp => h.2.2 p (hX hp)⟩

/-- **Corollary 1**, top level: `(n, n−1)`-liveness is the same as `(n, n)`-liveness
(wait-freedom): if all processes but `r` are wait-free and `r` is obstruction-free, `r` is
wait-free too. -/
theorem corollary1_top {X : Set (Fin n)} {r : Fin n} (h : Live A X) (hX : ∀ q, q ≠ r → q ∈ X) :
    Live A Set.univ :=
  ⟨h.1, h.2.1, fun p _ => by
    by_cases hp : p = r
    · subst hp
      exact wFree_of_wFree_others (h.2.1 p) (fun q hq => h.2.2 q (hX q hq))
    · exact h.2.2 p (hX p hp)⟩

end General

/-! ## Theorem 2 -/

/-- The base objects of Theorem 2: read/write-like objects `R j` (e.g. atomic registers) and
`(n, X c)`-live consensus objects, which behave as the (legal, `advCons_isLive`) adversarial
objects `liveCons (X c)`. -/
abbrev regsAndLive {ιR ιC : Type} (R : ιR → BObj n) (X : ιC → Finset (Fin n)) :
    ιR ⊕ ιC → BObj n
  | .inl j => R j
  | .inr c => liveCons (X c)

/-- **Theorem 2** of the paper. Let `x < n − 1`. There is no `(n, x+1)`-live consensus algorithm
using read/write-like objects (e.g. atomic registers) and any number of `(n, x)`-live consensus
objects (with arbitrary sets `X c` of at most `x` wait-free processes each): with the legal
adversarial behaviour `advCons` of the base consensus objects, some wait-free process of the
implementation is blocked forever. (The paper assumes `1 ≤ x`; `x = 0` is included.) -/
theorem theorem2 {ιR ιC : Type} [DecidableEq ιR] [DecidableEq ιC] (R : ιR → BObj n)
    (hR : ∀ j, (R j).RWLike) (X : ιC → Finset (Fin n)) {x : ℕ} (hX : ∀ c, (X c).card ≤ x)
    (hxn : x < n - 1) (A : Alg n (regsAndLive R X)) (XP : Finset (Fin n))
    (hXP : XP.card = x + 1) : ¬ Live A (XP : Set (Fin n)) := by
  rintro ⟨hS, hOF, hWF⟩
  have hn : 2 ≤ n := by omega
  obtain ⟨p, hp⟩ : XP.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨D, i, hD, hrw, hall⟩ := exists_all_poised_of_wFree hS hOF hn (hWF p hp)
  rcases i with j | c
  · exact hrw (hR j)
  -- a wait-free process `w` of the implementation that is not wait-free for `c`
  obtain ⟨w, hwXP, hwX⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (X c).card < XP.card by have := hX c; omega)
  -- another process `r` that is not wait-free for `c`
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (insert w (X c)).card < (Finset.univ : Finset (Fin n)).card by
      have := Finset.card_insert_le w (X c)
      have := hX c
      rw [Finset.card_univ, Fintype.card_fin]; omega)
  rw [Finset.mem_insert, not_or] at hr
  obtain ⟨hrw', hrX⟩ := hr
  -- they alternate on `c`, starting with the one that did not take the last step on `c`
  obtain ⟨x₀, σ, rfl⟩ := hD
  set D := run (initCfg A x₀) σ with hDdef
  classical
  set s₀ : LCState n := D.mem (.inr c)
  let a₀ : Fin n := if s₀.last = some w then r else w
  let a₁ : Fin n := if s₀.last = some w then w else r
  let alt : ℕ → Fin n := fun t => if t % 2 = 0 then a₀ else a₁
  have ha01 : a₀ ≠ a₁ := by
    simp only [a₀, a₁]; split_ifs
    · exact hrw'
    · exact fun h => hrw' h.symm
  have hnX : ∀ t, alt t ∉ X c := by
    intro t; simp only [alt, a₀, a₁]; split_ifs <;> assumption
  have halt_succ : ∀ t, alt (t + 1) ≠ alt t := by
    intro t
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      simp only [alt, h, h']; simpa using ha01.symm
    · have h' : (t + 1) % 2 = 0 := by omega
      simp only [alt, h, h']; simpa using ha01
  have hinv : ∀ t, (run D (pre alt t)).loc = D.loc ∧
      ((run D (pre alt t)).mem (.inr c)).last ≠ some (alt t) := by
    intro t
    induction t with
    | zero =>
      refine ⟨rfl, ?_⟩
      show s₀.last ≠ some (if (0 : ℕ) % 2 = 0 then a₀ else a₁)
      by_cases h : s₀.last = some w
      · have : a₀ = r := by simp [a₀, h]
        simp only [Nat.zero_mod, ↓reduceIte, this, h]
        simpa using fun h' => hrw' h'.symm
      · have : a₀ = w := by simp [a₀, h]
        simpa [this] using h
    | succ t ih =>
      obtain ⟨hloc, hlast⟩ := ih
      set E := run D (pre alt t)
      obtain ⟨o, k, hok⟩ := objOf_eq_some_iff.1 (hall (alt t))
      have ha : A.act (E.loc (alt t)) = .access (.inr c) o k := by rw [hloc]; exact hok
      have hδ : ((regsAndLive R X (.inr c)).δ (E.mem (.inr c)) (alt t) o).2 = none := by
        simp only [regsAndLive, liveCons, ConsObj.toBObj, advCons]
        rw [ite_eq_right (by rintro (h | h); exact hnX t h; exact hlast h)]
      rw [pre_succ, run_concat, step_of_access ha, hδ]
      refine ⟨by simpa using hloc, ?_⟩
      simp only [Function.update_self]
      rw [ite_eq_right (by rintro (h | h); exact hnX t h; exact hlast h)]
      simpa using (halt_succ t).symm
  have hw : ∀ M, ∃ t ≥ M, alt t = w := by
    intro M
    by_cases h : s₀.last = some w
    · refine ⟨2 * M + 1, by omega, ?_⟩
      simp [alt, a₁, h, Nat.add_mod]
    · refine ⟨2 * M, by omega, ?_⟩
      simp [alt, a₀, h]
  refine not_wFree_of_stuck (x := x₀) (σ := σ) alt hw (fun t v hout => ?_) (hWF w hwXP)
  have hwD : D.objOf w = some (.inr c) := hall w
  unfold Cfg.Out at hout
  rw [(hinv t).1] at hout
  rw [objOf_eq_some_iff] at hwD
  obtain ⟨o, k, hok⟩ := hwD
  rw [hok] at hout
  cases hout

/-! ## Theorem 3 -/

/-- **Theorem 3** of the paper, lower bound: an `(x+1, x)`-live consensus object is a wait-free
consensus object for `x + 1` processes, so the consensus number of `(n, x)`-live consensus
objects is at least `x + 1` (restrict the object to `x + 1` of its ports, including the `x`
wait-free ones). -/
theorem theorem3_lower {x : ℕ} (B : ConsObj (x + 1)) (X : Set (Fin (x + 1))) (hX : X.ncard = x)
    (hB : B.IsLive X) : B.IsLive Set.univ := by
  have hc : Xᶜ.ncard = 1 := by
    have := Set.ncard_add_ncard_compl X
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  obtain ⟨r, hr⟩ := Set.ncard_eq_one.1 hc
  exact corollary1_top hB (r := r) (fun q hq => by
    by_contra h
    have : q ∈ Xᶜ := h
    rw [hr] at this
    exact hq this)

/-- **Theorem 3** of the paper, upper bound: for every `k ≥ x + 2`, there is no wait-free
consensus algorithm for `k` processes using read/write-like objects (e.g. atomic registers) and
`(k, x)`-live consensus objects (behaving as the legal adversarial objects `advCons`). Hence the
consensus number of `(n, x)`-live consensus objects is at most `x + 1`. -/
theorem theorem3_upper {x k : ℕ} (hk : x + 2 ≤ k) {ιR ιC : Type} [DecidableEq ιR]
    [DecidableEq ιC] (R : ιR → BObj k) (hR : ∀ j, (R j).RWLike) (X : ιC → Finset (Fin k))
    (hX : ∀ c, (X c).card ≤ x) (A : Alg k (regsAndLive R X)) : ¬ Live A Set.univ := by
  intro h
  obtain ⟨XP, -, hXP⟩ := Finset.exists_subset_card_eq
    (show x + 1 ≤ (Finset.univ : Finset (Fin k)).card by
      rw [Finset.card_univ, Fintype.card_fin]; omega)
  exact theorem2 R hR X hX (by omega) A XP hXP (h.mono (Set.subset_univ _))

end Podc.AsymmetricProgress
