import Papers.PODC2011.UnboundedConcurrency.Swap.Lin

/-!
# Lemmas 4–6 and Theorem 9 (linearizability) of [AMW11]

Linearizability of one-shot `swap` operations (`SwapLin x σ L`): `L` is a list of distinct
processes that took a step in `σ` and contains every process that has returned; the sequential
execution of the `swap(x p)` operations of `L` (in this order) on a swap object initially `⊥`
gives every returned process its actual response (`swapResp`: the first one returns `⊥`, the
`(j+1)`-st returns the input of the `j`-th); and `L` respects real time (if `p` returned before `q`
took its first step, `p` precedes `q`). Pending operations may (but need not) appear in `L`.

The linearization is the order of the captured nodes (`κ`).
-/

namespace Podc.UnboundedConcurrency.Swap

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Cfg' Node

variable {V : Type}

/-- Responses of the sequential execution of `swap(x L[0]), swap(x L[1]), …` on a swap object
initialized to `⊥`: the `j`-th operation (from `0`) returns `⊥` if `j = 0` and the argument of
the previous one otherwise (`swapResp_eq` relates it to CSLib's `swapObj`). -/
def swapResp (x : ℕ → V) (L : List ℕ) : ℕ → Option V
  | 0 => none
  | j + 1 => L[j]?.map x

/-- `swapResp` is the response of the sequential swap object `swapObj (Option V) none`: the value
of the object after the first `j` operations. -/
lemma swapResp_eq (x : ℕ → V) (L : List ℕ) (j : ℕ) (hj : j ≤ L.length) :
    swapResp x L j =
      ((L.take j).map (fun p => some (x p))).foldl (fun s v => ((swapObj (Option V) none).δ s v).1)
        none := by
  have key : ∀ (l : List (Option V)) (s : Option V),
      l.foldl (fun s v => ((swapObj (Option V) none).δ s v).1) s = (l.getLast?).getD s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons a l ih =>
      intro s
      simp only [List.foldl_cons, swapObj_δ, ih]
      cases l with
      | nil => rfl
      | cons b l =>
        cases h : (b :: l).getLast? with
        | none => simp at h
        | some z => rw [List.getLast?_cons_cons, h]; rfl
  rw [key]
  cases j with
  | zero => simp [swapResp]
  | succ j =>
    simp only [swapResp, List.getLast?_map]
    have h1 : j < L.length := by omega
    rw [List.getLast?_take]
    simp [List.getElem?_eq_getElem h1]

/-- `L` linearizes the finite execution `σ` of Algorithm 1 with inputs `x` (each process performs
one `swap(x p)`; see the module docstring). -/
def SwapLin (x : ℕ → V) (σ : List ℕ) (L : List ℕ) : Prop :=
  L.Nodup ∧ (∀ p ∈ L, p ∈ σ) ∧ (∀ p v, ((alg V).exec x σ).Out p v → p ∈ L) ∧
  (∀ (j : ℕ) (hj : j < L.length) v, ((alg V).exec x σ).Out L[j] v → v = swapResp x L j) ∧
  (∀ p q τ₁ τ₂ v, σ = τ₁ ++ τ₂ → ((alg V).exec x τ₁).Out p v → p ∈ L → q ∈ L → q ∉ τ₁ →
    L.idxOf p < L.idxOf q)

section Complete

variable {x : ℕ → V} {σ : List ℕ}

lemma Complete.done (hc : Complete x σ) {p : ℕ} (hp : p ∈ σ) :
    ∃ d c m r o, ((alg V).exec x σ).loc p = .done d c m r o := by
  obtain ⟨v, hv⟩ := hc p hp
  obtain ⟨d, c, m, r, h⟩ := out_iff.1 hv
  exact ⟨d, c, m, r, v, h⟩

lemma Complete.sel (hc : Complete x σ) {p : ℕ} (hp : p ∈ σ) :
    (((alg V).exec x σ).loc p).cap = some (κ ((alg V).exec x σ) p) := by
  obtain ⟨d, c, m, r, o, h⟩ := hc.done hp
  rw [κ_of_sel (by rw [h]; rfl), h]; rfl

lemma Complete.κ_inj (hc : Complete x σ) {p q : ℕ} (hp : p ∈ σ) (hq : q ∈ σ)
    (h : κ ((alg V).exec x σ) p = κ ((alg V).exec x σ) q) : p = q := by
  have hp' := hc.sel hp
  rw [h] at hp'
  exact (inv_exec x σ).cap_inj hp' (hc.sel hq)

lemma Complete.ret_cases (hc : Complete x σ) {p : ℕ} (hp : p ∈ σ) :
    (((alg V).exec x σ).loc p).ret = none ∨ ∃ q ∈ σ, RetFrom ((alg V).exec x σ) p q := by
  obtain ⟨d, c, m, r, o, h⟩ := hc.done hp
  cases r with
  | none => left; rw [h]; rfl
  | some r =>
    right
    have hok := (inv_exec x σ).ok p
    rw [h] at hok
    obtain ⟨-, -, q, hq, -⟩ := hok.2.2.2.2.2 r rfl
    exact ⟨q, mem_of_cap hq, r, by rw [h]; rfl, hq⟩

lemma Complete.out_none_iff (hc : Complete x σ) {p : ℕ} (hp : p ∈ σ) :
    ((alg V).exec x σ).Out p none ↔ (((alg V).exec x σ).loc p).ret = none := by
  obtain ⟨d, c, m, r, o, h⟩ := hc.done hp
  have hok := (inv_exec x σ).ok p
  rw [h] at hok
  have ho : r = none → o = none := hok.2.2.2.2.1
  have hs : ∀ r', r = some r' → o ≠ none := by
    intro r' hr'
    obtain ⟨-, -, q, -, ho'⟩ := hok.2.2.2.2.2 r' hr'
    rw [ho']; simp
  rw [out_iff, h]
  simp only [Loc.ret]
  constructor
  · rintro ⟨d', c', m', r', he⟩
    have ho' : o = none := (Loc.done.inj he).2.2.2.2
    cases r with
    | none => rfl
    | some r => exact absurd ho' (hs r rfl)
  · intro hr; exact ⟨d, c, m, r, by rw [ho hr]⟩

/-- Two processes cannot both return `⊥` (the uniqueness part of Lemma 4). -/
lemma Complete.ret_none_unique (hc : Complete x σ) {p p' : ℕ} (hp : p ∈ σ) (hp' : p' ∈ σ)
    (h : (((alg V).exec x σ).loc p).ret = none) (h' : (((alg V).exec x σ).loc p').ret = none) :
    p = p' := by
  have hI := inv_exec x σ
  set C := (alg V).exec x σ
  have key : ∀ p p', p ∈ σ → p' ∈ σ → (C.loc p).ret = none → κ C p' < κ C p → False := by
    intro p p' hp hp' h hlt
    obtain ⟨d, c, m, r, o, hd⟩ := hc.done hp
    rw [hd] at h; simp only [Loc.ret] at h; subst h
    have hcp : c = κ C p := by rw [κ_of_sel (by rw [hd]; rfl)]
    have hcap' := hc.sel hp'
    have hdep' := hI.cap_dep hcap'
    have hri : (C.loc p).rinfo = some (κ C p, m) := by rw [hd, ← hcp]; rfl
    have := hI.lemma2 hri hcap' hdep' hlt
    exact hI.excl p' p _ hcap' (by rw [hd]; exact ⟨this.le, hcp ▸ hlt⟩)
  rcases lt_trichotomy (κ C p) (κ C p') with hlt | heq | hlt
  · exact (key p' p hp' hp h' hlt).elim
  · exact hc.κ_inj hp hp' heq
  · exact (key p p' hp hp' h hlt).elim

/-- The linearization order: the processes of `σ` sorted by their captured nodes. -/
noncomputable def linOrder (x : ℕ → V) (σ : List ℕ) : List ℕ :=
  σ.dedup.mergeSort (fun p q => decide (κ ((alg V).exec x σ) p ≤ κ ((alg V).exec x σ) q))

lemma mem_linOrder {p : ℕ} : p ∈ linOrder x σ ↔ p ∈ σ := by
  rw [linOrder, (List.mergeSort_perm _ _).mem_iff, List.mem_dedup]

lemma nodup_linOrder : (linOrder (V := V) x σ).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (List.nodup_dedup σ)

lemma Complete.sorted (hc : Complete x σ) {i j : ℕ} (hi : i < (linOrder x σ).length)
    (hj : j < (linOrder x σ).length) (hij : i < j) :
    κ ((alg V).exec x σ) (linOrder x σ)[i] < κ ((alg V).exec x σ) (linOrder x σ)[j] := by
  have hpw := List.pairwise_mergeSort
    (le := fun p q => decide (κ ((alg V).exec x σ) p ≤ κ ((alg V).exec x σ) q))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) σ.dedup
  have hle := List.pairwise_iff_getElem.1 hpw i j hi hj hij
  simp only [decide_eq_true_eq] at hle
  refine lt_of_le_of_ne hle fun heq => ?_
  have := hc.κ_inj (mem_linOrder.1 (List.getElem_mem hi)) (mem_linOrder.1 (List.getElem_mem hj))
    heq
  rw [nodup_linOrder.getElem_inj_iff] at this
  omega

lemma Complete.lt_of_κ (hc : Complete x σ) {i j : ℕ} (hi : i < (linOrder x σ).length)
    (hj : j < (linOrder x σ).length)
    (h : κ ((alg V).exec x σ) (linOrder x σ)[i] < κ ((alg V).exec x σ) (linOrder x σ)[j]) :
    i < j := by
  by_contra hji
  push Not at hji
  rcases eq_or_lt_of_le hji with heq | hlt
  · subst heq; exact lt_irrefl _ h
  · exact lt_asymm h (hc.sorted hj hi hlt)

/-- The chain structure (from Lemmas 4–8): in the order of the captured nodes, the first process
returns `⊥` and every other one returns from the node captured by its predecessor. -/
lemma Complete.chain (hc : Complete x σ) (j : ℕ) (hj : j < (linOrder x σ).length) :
    (((alg V).exec x σ).loc (linOrder x σ)[j]).ret =
      if j = 0 then none else some (κ ((alg V).exec x σ) (linOrder x σ)[j - 1]) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  set C := (alg V).exec x σ
  set L := linOrder x σ
  have hjσ : L[j] ∈ σ := mem_linOrder.1 (List.getElem_mem hj)
  rcases hc.ret_cases hjσ with h | ⟨q, hq, hrf⟩
  · split_ifs with hj0
    · exact h
    · exfalso
      have h0 : 0 < L.length := by omega
      have := ih 0 (by omega) h0
      simp only [ite_true] at this
      have := hc.ret_none_unique hjσ (mem_linOrder.1 (List.getElem_mem h0)) h this
      rw [nodup_linOrder.getElem_inj_iff] at this
      exact hj0 this
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ((mem_linOrder (x := x)).2 hq)
    have hlt := hc.lt_of_κ hi hj ((inv_exec x σ).retFrom_lt hrf)
    have hij : i = j - 1 := by
      by_contra hne
      have h1 : i + 1 < j := by omega
      have := ih (i + 1) h1 (by omega)
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at this
      have hrf' : RetFrom C L[i + 1] L[i] := ⟨_, this, hc.sel (mem_linOrder.1 (List.getElem_mem hi))⟩
      have := lemma7 x σ hrf' hrf
      rw [nodup_linOrder.getElem_inj_iff] at this
      omega
    subst hij
    rw [ite_eq_right (by omega)]
    obtain ⟨r, hr, hcap⟩ := hrf
    rw [hr, ← hcap, hc.sel (mem_linOrder.1 (List.getElem_mem hi))]

lemma Inv.step_sel {x : ℕ → V} {C : Config V} (_hI : Inv x C) {q : ℕ} {c : Node}
    (h : ((C.step q).loc q).sel = some c) : (C.loc q).sel = some c ∨ Above (S C) c := by
  cases hq : C.loc q with
  | start x' => rw [(step_start hq).1] at h; simp [Loc.sel] at h
  | scan x' d pr =>
    rw [(step_scan hq).1] at h
    cases hn : next d (S C) with
    | none => rw [hn] at h; simp [Loc.sel] at h
    | some c' =>
      rw [hn] at h; simp only [Loc.sel, Option.some.injEq] at h; subst h
      exact Or.inr (next_some hn).2.1
  | write x' d c' => rw [(step_write hq).1] at h; exact Or.inl h
  | tas x' d c' => rw [(step_tas hq).1] at h; exact Or.inl h
  | upd x' d c' w =>
    rw [(step_upd hq).1] at h
    cases w
    · simp [Loc.sel] at h
    · exact Or.inl h
  | readMax d c' =>
    rw [(step_readMax hq).1] at h
    left; cases hp : prev c' (D C) <;> rw [hp] at h <;> simpa [afterPrev, Loc.sel] using h
  | retTas d c' m r =>
    rw [(step_retTas hq).1] at h
    left
    by_cases hb : B C r = true
    · rw [ite_eq_left hb] at h; exact h
    · rw [ite_eq_right hb] at h
      cases hp : prev r m <;> rw [hp] at h <;> simpa [afterPrev, Loc.sel] using h
  | readReg d c' m r => rw [(step_readReg hq).1] at h; exact Or.inl h
  | done d c' m r o => rw [step_done hq, hq] at h; exact Or.inl h

/-- Real time: if `p` returned before `q` took its first step, `q` captures a larger node. -/
lemma rt_aux {x : ℕ → V} {C₁ : Config V} (hI : Inv x C₁) {p q d m : ℕ} {c : Node}
    {r : Option Node} {o : Option V} (hp : C₁.loc p = .done d c m r o) (hq : C₁.loc q = .start (x q))
    (τ : List ℕ) :
    ((alg V).run C₁ τ).loc p = C₁.loc p ∧
      ∀ c', (((alg V).run C₁ τ).loc q).sel = some c' → c < c' := by
  have hpq : p ≠ q := by rintro rfl; rw [hp] at hq; cases hq
  suffices H : ∀ C : Config V, Inv x C → (C.loc p = C₁.loc p ∧
      ∀ c', (C.loc q).sel = some c' → c < c') → ∀ τ : List ℕ, ((alg V).run C τ).loc p = C₁.loc p ∧
      ∀ c', (((alg V).run C τ).loc q).sel = some c' → c < c' from
    H C₁ hI ⟨rfl, fun c' h => by rw [hq] at h; simp [Loc.sel] at h⟩ τ
  intro C hIC hC τ
  induction τ generalizing C with
  | nil => exact hC
  | cons s τ ih =>
    refine ih (C.step s) (hIC.step s) ⟨?_, fun c' hc' => ?_⟩
    · by_cases hs : s = p
      · subst hs; rw [step_done (hC.1.trans hp)]; exact hC.1
      · rw [Cfg.step_loc_other C (Ne.symm hs)]; exact hC.1
    · by_cases hs : s = q
      · subst hs
        rcases hIC.step_sel hc' with h | h
        · exact hC.2 c' h
        · have hok := hIC.ok p
          rw [hC.1, hp] at hok
          exact h d c hok.2.1
      · rw [Cfg.step_loc_other C (Ne.symm hs)] at hc'; exact hC.2 c' hc'

/-- **Theorem 9** of [AMW11] for complete executions (as proved in the paper): if every process
that took a step in `σ` has returned, the order of the captured nodes linearizes `σ`. -/
theorem theorem9_complete (hc : Complete x σ) : SwapLin x σ (linOrder x σ) := by
  set C := (alg V).exec x σ
  set L := linOrder x σ
  refine ⟨nodup_linOrder, fun p hp => mem_linOrder.1 hp, fun p v hv => ?_, fun j hj v hv => ?_,
    fun p q τ₁ τ₂ v hσ hpv hpL hqL hqτ => ?_⟩
  · obtain ⟨d, c, m, r, h⟩ := out_iff.1 hv
    exact (mem_linOrder (x := x)).2 (mem_of_dep (d := d) (by rw [h]; rfl))
  · have hch := hc.chain j hj
    cases j with
    | zero =>
      simp only [ite_true] at hch
      exact Cfg.Out.unique hv ((hc.out_none_iff (mem_linOrder.1 (List.getElem_mem hj))).2 hch)
    | succ j =>
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at hch
      have hj' : j < L.length := by omega
      have hrf : RetFrom C L[j + 1] L[j] :=
        ⟨_, hch, hc.sel (mem_linOrder.1 (List.getElem_mem hj'))⟩
      rw [Cfg.Out.unique hv ((inv_exec x σ).retFrom_out hrf), swapResp,
        List.getElem?_eq_getElem hj']
      rfl
  · obtain ⟨d, c, m, r, o, hd⟩ : ∃ d c m r o, ((alg V).exec x τ₁).loc p = .done d c m r o := by
      obtain ⟨d, c, m, r, h⟩ := out_iff.1 hpv; exact ⟨d, c, m, r, v, h⟩
    have hrt := rt_aux (inv_exec x τ₁) hd (loc_not_mem hqτ) τ₂
    have hCe : C = (alg V).run ((alg V).exec x τ₁) τ₂ := by simp only [C, hσ, Alg.exec_append]
    have hpσ := mem_linOrder.1 hpL
    have hqσ := mem_linOrder.1 hqL
    have hκp : κ C p = c := by
      rw [κ_of_sel (c := c)]; rw [hCe, hrt.1, hd]; rfl
    have hκq : c < κ C q := hrt.2 _ (by rw [← hCe]; exact Loc.cap_sel (hc.sel hqσ))
    have hip := List.idxOf_lt_length_iff.2 hpL
    have hiq := List.idxOf_lt_length_iff.2 hqL
    have e1 := List.getElem_idxOf hip
    have e2 := List.getElem_idxOf hiq
    apply hc.lt_of_κ hip hiq
    rw [e1, e2, hκp]; exact hκq

/-- **Lemma 4** of [AMW11]: in a complete execution (with at least one process) exactly one
process returns `⊥`. -/
theorem lemma4 (hc : Complete x σ) (hne : σ ≠ []) :
    ∃! p, p ∈ σ ∧ ((alg V).exec x σ).Out p none := by
  have h0 : 0 < (linOrder x σ).length := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil σ hne
    exact List.length_pos_of_mem ((mem_linOrder (x := x)).2 ha)
  have hm := mem_linOrder.1 (List.getElem_mem h0)
  refine ⟨(linOrder x σ)[0], ⟨hm, (hc.out_none_iff hm).2 (by simpa using hc.chain 0 h0)⟩, ?_⟩
  rintro p ⟨hp, hpo⟩
  exact hc.ret_none_unique hp hm ((hc.out_none_iff hp).1 hpo) (by simpa using hc.chain 0 h0)

/-- **Lemma 5** of [AMW11]: in a complete execution (with at least one process) exactly one
process's input is not returned by any process. (The paper only shows that the process with the
largest captured node is not returned; uniqueness follows from the chain structure.) -/
theorem lemma5 (hc : Complete x σ) (hne : σ ≠ []) :
    ∃! q, q ∈ σ ∧ ∀ p ∈ σ, ¬ RetFrom ((alg V).exec x σ) p q := by
  have hn : 0 < (linOrder x σ).length := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil σ hne
    exact List.length_pos_of_mem ((mem_linOrder (x := x)).2 ha)
  have hlast : (linOrder x σ).length - 1 < (linOrder x σ).length := by omega
  refine ⟨(linOrder x σ)[(linOrder x σ).length - 1], ⟨mem_linOrder.1 (List.getElem_mem hlast), fun p hp hrf => ?_⟩, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ((mem_linOrder (x := x)).2 hp)
    have := hc.lt_of_κ hlast hj ((inv_exec x σ).retFrom_lt hrf)
    omega
  · rintro q ⟨hq, hnot⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ((mem_linOrder (x := x)).2 hq)
    by_contra hne'
    have hi' : i + 1 < (linOrder x σ).length := by
      have : i ≠ (linOrder x σ).length - 1 := fun h => hne' (by simp only [h])
      omega
    have hch := hc.chain (i + 1) hi'
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at hch
    exact hnot _ (mem_linOrder.1 (List.getElem_mem hi'))
      ⟨_, hch, hc.sel (mem_linOrder.1 (List.getElem_mem hi))⟩

/-- **Lemma 6** of [AMW11]: in a complete execution each process returns precisely one value. -/
theorem lemma6 (hc : Complete x σ) {p : ℕ} (hp : p ∈ σ) :
    ∃! v, ((alg V).exec x σ).Out p v := by
  obtain ⟨v, hv⟩ := hc p hp
  exact ⟨v, hv, fun w hw => Cfg.Out.unique hw hv⟩

end Complete

/-! ### All finite executions -/

lemma exists_completion (x : ℕ → V) (σ : List ℕ) : ∀ P : List ℕ, ∃ τ : List ℕ,
    (∀ q ∈ τ, q ∈ P) ∧ ∀ p ∈ P, ∃ v, ((alg V).exec x (σ ++ τ)).Out p v := by
  have hwf : WaitFree (alg V) (fun s => (Set.range s).Finite) :=
    waitFree.mono (fun _ _ => trivial)
  intro P
  induction P with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p P ih =>
    obtain ⟨τ, hτ, hout⟩ := ih
    obtain ⟨m, v, hv⟩ := hwf.exists_solo_out x (σ ++ τ) p
    refine ⟨τ ++ List.replicate (m + 1) p, fun q hq => ?_, fun q hq => ?_⟩
    · rcases List.mem_append.1 hq with hq | hq
      · exact List.mem_cons_of_mem _ (hτ q hq)
      · rw [List.eq_of_mem_replicate hq]; exact List.mem_cons_self
    · rw [← List.append_assoc]
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨v, hv⟩
      · obtain ⟨w, hw⟩ := hout q hq
        exact ⟨w, by rw [Alg.exec_append]; exact Alg.Cfg.Out.run hw _⟩

/-- Non-vacuity of `Complete`: every finite execution can be extended, by solo runs of its pending
processes, to a complete one with the same set of processes. -/
theorem exists_complete (x : ℕ → V) (σ : List ℕ) :
    ∃ τ, (∀ q ∈ τ, q ∈ σ) ∧ Complete x (σ ++ τ) := by
  obtain ⟨τ, hτ, hout⟩ := exists_completion x σ σ
  refine ⟨τ, hτ, fun p hp => ?_⟩
  rcases List.mem_append.1 hp with hp | hp
  · exact hout p hp
  · exact hout p (hτ p hp)

/-- **Theorem 9** of [AMW11] (Algorithm 1 is linearizable), for every finite execution: pending
operations are completed by solo runs (wait-freedom) and the linearization of the completed
execution is reused. -/
theorem linearizable (x : ℕ → V) (σ : List ℕ) : ∃ L, SwapLin x σ L := by
  obtain ⟨τ, hτ, hout⟩ := exists_completion x σ σ
  have hc : Complete x (σ ++ τ) := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hout p hp
    · exact hout p (hτ p hp)
  obtain ⟨hnd, hmem, hall, hval, hrt⟩ := theorem9_complete hc
  have hext : ∀ p v, ((alg V).exec x σ).Out p v → ((alg V).exec x (σ ++ τ)).Out p v :=
    fun p v h => by rw [Alg.exec_append]; exact Alg.Cfg.Out.run h _
  refine ⟨linOrder x (σ ++ τ), hnd, fun p hp => ?_, fun p v hv => hall p v (hext p v hv),
    fun j hj v hv => hval j hj v (hext _ _ hv), fun p q τ₁ τ₂ v hσ hpv hpL hqL hqτ => ?_⟩
  · rcases List.mem_append.1 (hmem p hp) with h | h
    · exact h
    · exact hτ p h
  · exact hrt p q τ₁ (τ₂ ++ τ) v (by rw [hσ, List.append_assoc]) hpv hpL hqL hqτ

end Podc.UnboundedConcurrency.Swap
