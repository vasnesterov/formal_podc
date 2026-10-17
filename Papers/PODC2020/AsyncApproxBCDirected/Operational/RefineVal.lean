import Papers.PODC2020.AsyncApproxBCDirected.Operational.BWFacts

/-!
# Refinement, value layer: RedundantFlood satisfies the hypotheses `M_*` of `RoundExec`

For a run of the operational algorithm and a round `r < N`:
* `hst t v` — history of `v` at time `t`; `Xr r v` — the state value of round `r` of `v`;
* `Mr r v t` — the abstract `M_v` at time `t` (`recvM` of the history);
* `accR r p` — the ghost "accepted value" on path `p`;
* `kv` — values carried along paths with a correct last hop are the accepted ones.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

namespace BWOp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (f N : ℕ)
  (B : Finset V) (inp : V → ℝ) (ev : ℕ → Event V (BMsg V))

/-- History of `v` at time `t`. -/
noncomputable abbrev hst (t : ℕ) (v : V) : Hist V := (spec G f N).hist G B inp ev t v

theorem hst_prefix {t t' : ℕ} (h : t ≤ t') (v : V) :
    hst G f N B inp ev t v <+: hst G f N B inp ev t' v :=
  (spec G f N).hist_prefix G B inp ev h v

theorem hst_comparable (t t' : ℕ) (v : V) :
    hst G f N B inp ev t v <+: hst G f N B inp ev t' v ∨
      hst G f N B inp ev t' v <+: hst G f N B inp ev t v := by
  rcases le_total t t' with h | h
  · exact Or.inl (hst_prefix G f N B inp ev h v)
  · exact Or.inr (hst_prefix G f N B inp ev h v)

/-- The state value of round `r` (once the round has started). -/
noncomputable def Xr (r : ℕ) (v : V) : ℝ := by
  classical
  exact if h : ∃ t, (xv G f N v (inp v) r (hst G f N B inp ev t v)).isSome then
    (xv G f N v (inp v) r (hst G f N B inp ev (Nat.find h) v)).getD 0 else 0

theorem xv_hst_eq {r : ℕ} {v : V} {t : ℕ} {y : ℝ}
    (hy : xv G f N v (inp v) r (hst G f N B inp ev t v) = some y) : y = Xr G f N B inp ev r v := by
  classical
  have hex : ∃ t, (xv G f N v (inp v) r (hst G f N B inp ev t v)).isSome := ⟨t, by simp [hy]⟩
  simp only [Xr, hex, dite_true]
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
  rw [hy']
  rcases hst_comparable G f N B inp ev t (Nat.find hex) v with h | h
  · rw [xv_prefix G f N v (inp v) r h hy] at hy'; exact Option.some.inj hy'
  · rw [xv_prefix G f N v (inp v) r h hy'] at hy; exact (Option.some.inj hy).symm

/-- The abstract `M_v` at time `t` in round `r`. -/
noncomputable def Mr (r : ℕ) (v : V) (t : ℕ) : Finset (Msg V) :=
  recvM v r (xv G f N v (inp v) r (hst G f N B inp ev t v)) (hst G f N B inp ev t v)

theorem Mr_mono (r : ℕ) (v : V) : Monotone (Mr G f N B inp ev r v) := fun _ _ h =>
  recvM_mono G f N v (inp v) r (hst_prefix G f N B inp ev h v)

theorem mem_recvM {v : V} {r : ℕ} {own : Option ℝ} {h : Hist V} {m : Msg V} :
    m ∈ recvM v r own h ↔ (∃ e ∈ h, valOf v r e = some m) ∨ (m.2 = [v] ∧ own = some m.1) := by
  classical
  simp only [recvM, mem_union, List.mem_toFinset, List.mem_filterMap]
  apply or_congr Iff.rfl
  cases own with
  | none => simp [ownSet]
  | some y =>
    simp only [ownSet, mem_singleton, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩; exact Prod.ext h2.symm h1

theorem valOf_eq_some {v : V} {r : ℕ} {e : V × BMsg V} {m : Msg V} (h : valOf v r e = some m) :
    ∃ y p, e = (e.1, .val r y p) ∧ p.getLast? = some e.1 ∧ m = (y, p ++ [v]) := by
  rcases e with ⟨u, _ | _⟩
  · simp only [valOf] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, _, by rw [hc.1], hc.2, rfl⟩
  · simp [valOf] at h

/-- Received value messages have paths of length at least 2. -/
theorem valOf_path {v : V} {r : ℕ} {e : V × BMsg V} {m : Msg V} (h : valOf v r e = some m) :
    ∃ p₀ q, m.2 = p₀ ++ [v] ∧ p₀.getLast? = some q ∧ q = e.1 := by
  obtain ⟨y, p, -, hp, rfl⟩ := valOf_eq_some h
  exact ⟨p, e.1, rfl, hp, rfl⟩

/-! ## The ghost accepted values -/

/-- The entry of a history carrying a valid round-`r` value message on path `p`. -/
def IsValEntry (w : V) (r : ℕ) (p : List V) (e : V × BMsg V) : Prop :=
  ∃ m ∈ valOf w r e, m.2 = p

/-- The first value received by `w` on path `p` by time `t`. -/
noncomputable def firstVal (r : ℕ) (w : V) (p : List V) (t : ℕ) : Option ℝ := by
  classical
  exact ((hst G f N B inp ev t w).find? fun e => decide (IsValEntry w r p e)).bind fun e =>
    (valOf w r e).map Prod.fst

/-- The value accepted by `w` on path `p` (ghost). -/
noncomputable def accept (r : ℕ) (w : V) (p : List V) : ℝ := by
  classical
  exact if h : ∃ t, (firstVal G f N B inp ev r w p t).isSome then
    (firstVal G f N B inp ev r w p (Nat.find h)).getD 0 else 0

/-- Accepted values, on reversed paths. -/
noncomputable def accRev (r : ℕ) : List V → ℝ
  | [] => 0
  | [s] => Xr G f N B inp ev r s
  | w :: q :: rest => by
    classical
    exact if q ∈ B then accept G f N B inp ev r w (rest.reverse ++ [q, w])
      else accRev r (q :: rest)

/-- The accepted value on a path (the `acc` of `RoundExec`). -/
noncomputable def accR (r : ℕ) (p : List V) : ℝ := accRev G f N B inp ev r p.reverse

theorem accR_single (r : ℕ) (s : V) : accR G f N B inp ev r [s] = Xr G f N B inp ev r s := by
  simp [accR, accRev]

theorem accR_snoc (r : ℕ) {p : List V} {q : V} (hq : p.getLast? = some q) (w : V) :
    accR G f N B inp ev r (p ++ [w]) =
      if q ∈ B then accept G f N B inp ev r w (p ++ [w]) else accR G f N B inp ev r p := by
  classical
  obtain ⟨p₀, rfl⟩ := List.getLast?_eq_some_iff.mp hq
  simp only [accR, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, accRev]
  split_ifs <;> simp

theorem firstVal_prefix {r : ℕ} {w : V} {p : List V} {t t' : ℕ} (htt : t ≤ t') {y : ℝ}
    (h : firstVal G f N B inp ev r w p t = some y) : firstVal G f N B inp ev r w p t' = some y := by
  classical
  obtain ⟨l, hl⟩ := hst_prefix G f N B inp ev htt w
  simp only [firstVal] at h ⊢
  rw [← hl, List.find?_append]
  rcases hf : (hst G f N B inp ev t w).find? (fun e => decide (IsValEntry w r p e)) with _ | e
  · simp [hf] at h
  · simp only [hf] at h; simpa using h

theorem firstVal_eq_accept {r : ℕ} {w : V} {p : List V} {t : ℕ} {y : ℝ}
    (h : firstVal G f N B inp ev r w p t = some y) : y = accept G f N B inp ev r w p := by
  classical
  have hex : ∃ t, (firstVal G f N B inp ev r w p t).isSome := ⟨t, by simp [h]⟩
  simp only [accept, hex, dite_true]
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
  rw [hy']
  rcases le_total t (Nat.find hex) with h1 | h1
  · rw [firstVal_prefix G f N B inp ev h1 h] at hy'; exact Option.some.inj hy'
  · rw [firstVal_prefix G f N B inp ev h1 hy'] at h; exact (Option.some.inj h).symm

/-- The first entry with path `p`. -/
theorem firstVal_spec {r : ℕ} {w : V} {p : List V} {t : ℕ} {y : ℝ}
    (h : firstVal G f N B inp ev r w p t = some y) :
    ∃ A e C, hst G f N B inp ev t w = A ++ e :: C ∧ valOf w r e = some (y, p) ∧
      ∀ e' ∈ A, ¬ IsValEntry w r p e' := by
  classical
  simp only [firstVal] at h
  rcases hf : (hst G f N B inp ev t w).find? (fun e => decide (IsValEntry w r p e)) with _ | e
  · simp [hf] at h
  simp only [hf, Option.bind_some, Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  obtain ⟨A, C, hAC, hA⟩ := (List.find?_eq_some_iff_append.mp hf).2
  have he := (List.find?_eq_some_iff_append.mp hf).1
  obtain ⟨m', hm', hm'p⟩ := of_decide_eq_true he
  rw [hm] at hm'
  simp only [Option.mem_def, Option.some.injEq] at hm'
  subst hm'
  refine ⟨A, e, C, hAC, by rw [hm, ← hm'p], fun e' he' hv => ?_⟩
  have := hA e' he'
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact this hv

theorem firstVal_isSome {r : ℕ} {w : V} {p : List V} {t : ℕ} {e : V × BMsg V}
    (he : e ∈ hst G f N B inp ev t w) {y : ℝ} (hv : valOf w r e = some (y, p)) :
    ∃ y', firstVal G f N B inp ev r w p t = some y' := by
  classical
  have hfind : ((hst G f N B inp ev t w).find? fun e => decide (IsValEntry w r p e)).isSome := by
    rw [List.find?_isSome]; exact ⟨e, he, by simp [IsValEntry, hv]⟩
  obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp hfind
  have h1 := of_decide_eq_true (List.find?_eq_some_iff_append.mp he').1
  obtain ⟨m, hm, hmp⟩ := h1
  refine ⟨m.1, ?_⟩
  simp only [firstVal, he', Option.bind_some]
  rw [show valOf w r e' = some m from hm]; rfl

theorem firstVal_of_split {r : ℕ} {w : V} {p : List V} {t : ℕ} {A C : Hist V}
    {e : V × BMsg V} (hs : hst G f N B inp ev t w = A ++ e :: C) {y : ℝ}
    (hv : valOf w r e = some (y, p)) (hA : ∀ e' ∈ A, ¬ IsValEntry w r p e') :
    firstVal G f N B inp ev r w p t = some y := by
  classical
  have hf : (hst G f N B inp ev t w).find? (fun e => decide (IsValEntry w r p e)) = some e := by
    rw [hs, List.find?_append]
    have : A.find? (fun e => decide (IsValEntry w r p e)) = none := by
      rw [List.find?_eq_none]; intro e' he'; simpa using hA e' he'
    rw [this, Option.none_or, List.find?_cons]
    have : decide (IsValEntry w r p e) = true := by simp [IsValEntry, hv]
    rw [this]
  simp only [firstVal, hf, Option.bind_some, hv]; rfl

theorem mem_hst_of_take {t : ℕ} {u : V} {k : ℕ} {e : V × BMsg V}
    (he : e ∈ (hst G f N B inp ev t u).take k) : e ∈ hst G f N B inp ev t u :=
  List.mem_of_mem_take he

/-- **Key value lemma**: on a path whose last hop is correct (or on the own path `[w]`), the value
received is the accepted value `accR`; and the first value received on any path is `accR`. -/
theorem kv (r : ℕ) : ∀ n, ∀ p : List V, p.length = n → ∀ w ∉ B, ∀ t y,
    ((y, p) ∈ Mr G f N B inp ev r w t →
      (p = [w] ∨ ∃ p₀ q, p = p₀ ++ [w] ∧ p₀.getLast? = some q ∧ q ∉ B) →
      y = accR G f N B inp ev r p) ∧
    (firstVal G f N B inp ev r w p t = some y → y = accR G f N B inp ev r p) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hpn w hw t y
  have part1 : (y, p) ∈ Mr G f N B inp ev r w t →
      (p = [w] ∨ ∃ p₀ q, p = p₀ ++ [w] ∧ p₀.getLast? = some q ∧ q ∉ B) →
      y = accR G f N B inp ev r p := by
    intro hm hp
    rcases mem_recvM.mp hm with ⟨e, he, hv⟩ | ⟨h1, h2⟩
    · obtain ⟨y', p₀, he', hp₀, hm'⟩ := valOf_eq_some hv
      simp only [Prod.mk.injEq] at hm'
      obtain ⟨rfl, rfl⟩ := hm'
      have hu : e.1 ∉ B := by
        rcases hp with h | ⟨p₀', q, h1, h2, h3⟩
        · have h' : p₀ = [] := by simpa using congrArg List.length h
          subst h'; simp at hp₀
        · obtain ⟨rfl, -⟩ := List.append_inj' h1 rfl
          rw [hp₀] at h2; simp only [Option.some.injEq] at h2; rw [h2]; exact h3
      have hsent := (spec G f N).mem_sent_of_mem_hist G B inp ev hu (t := t) (v := w)
        (m := .val r y p₀) (by rw [he'] at he; exact he)
      obtain ⟨k, hk, hk'⟩ := mem_allSends.mp hsent
      obtain ⟨-, -, hcase⟩ := val_sent G f N hk'
      have hlt : p₀.length < n := by rw [← hpn]; simp
      have hsnoc := accR_snoc G f N B inp ev r hp₀ w
      rw [ite_eq_right hu] at hsnoc
      rw [hsnoc]
      rcases hcase with ⟨h₀, u', p₁, hsplit, hp₁, rfl, -, hfirst⟩ | ⟨rfl, hx⟩
      · -- relay of the first message on `p₁ ‖ u`
        have hpre : (hst G f N B inp ev t e.1).take k <+: hst G f N B inp ev t e.1 :=
          List.take_prefix _ _
        obtain ⟨Crest, hC⟩ := hpre
        have hsplit' : (hst G f N B inp ev t e.1).take k = h₀ ++ [(u', BMsg.val r y p₁)] := hsplit
        have hs' : hst G f N B inp ev t e.1 = h₀ ++ (u', BMsg.val r y p₁) :: Crest := by
          rw [← hC, hsplit']; simp
        have hfv := firstVal_of_split G f N B inp ev hs' (r := r) (p := p₁ ++ [e.1]) (y := y)
          (by simp [valOf, hp₁]) (fun e' he' ⟨m, hm, hm2⟩ => hfirst e' he' m hm hm2)
        exact (ih _ hlt (p₁ ++ [e.1]) rfl e.1 hu t y).2 hfv
      · -- own value of the sender
        have := xv_prefix G f N e.1 (inp e.1) r (List.take_prefix _ _) hx
        rw [xv_hst_eq G f N B inp ev this, accR_single]
    · simp only at h1 h2
      subst h1
      rw [xv_hst_eq G f N B inp ev h2, accR_single]
  refine ⟨part1, fun hf => ?_⟩
  obtain ⟨A, e, C, hs, hv, -⟩ := firstVal_spec G f N B inp ev hf
  have hm : (y, p) ∈ Mr G f N B inp ev r w t :=
    mem_recvM.mpr (Or.inl ⟨e, by rw [hs]; simp, hv⟩)
  obtain ⟨p₀, q, hp, hq, hqe⟩ := valOf_path hv
  simp only at hp
  subst hqe
  by_cases hqB : e.1 ∈ B
  · rw [hp, accR_snoc G f N B inp ev r hq w, ite_eq_left hqB, ← hp]
    exact firstVal_eq_accept G f N B inp ev hf
  · exact part1 hm (Or.inr ⟨p₀, e.1, hp, hq, hqB⟩)

theorem kv_mem (r : ℕ) {w : V} (hw : w ∉ B) {t : ℕ} {y : ℝ} {p : List V}
    (hm : (y, p) ∈ Mr G f N B inp ev r w t)
    (hp : p = [w] ∨ ∃ p₀ q, p = p₀ ++ [w] ∧ p₀.getLast? = some q ∧ q ∉ B) :
    y = accR G f N B inp ev r p :=
  (kv G f N B inp ev r _ p rfl w hw t y).1 hm hp

theorem kv_first (r : ℕ) {w : V} (hw : w ∉ B) {t : ℕ} {y : ℝ} {p : List V}
    (hf : firstVal G f N B inp ev r w p t = some y) : y = accR G f N B inp ev r p :=
  (kv G f N B inp ev r _ p rfl w hw t y).2 hf

/-! ## The `M_*` hypotheses of `RoundExec` -/

theorem M_last' (r : ℕ) {v : V} (t : ℕ) : ∀ m ∈ Mr G f N B inp ev r v t, m.2.getLast? = some v := by
  intro m hm
  rcases mem_recvM.mp hm with ⟨e, -, hv⟩ | ⟨h1, -⟩
  · obtain ⟨p₀, q, hp, -, -⟩ := valOf_path hv; rw [hp]; simp
  · rw [h1]; simp

theorem M_first' (r : ℕ) {v : V} (hv : v ∉ B) (t : ℕ) (y : ℝ) (p : List V)
    (hm : (y, p) ∈ Mr G f N B inp ev r v t) : (accR G f N B inp ev r p, p) ∈ Mr G f N B inp ev r v t := by
  rcases mem_recvM.mp hm with ⟨e, he, hve⟩ | ⟨h1, h2⟩
  · obtain ⟨y', hy'⟩ := firstVal_isSome G f N B inp ev he hve
    obtain ⟨A, e', C, hs, hv', -⟩ := firstVal_spec G f N B inp ev hy'
    rw [← kv_first G f N B inp ev r hv hy']
    exact mem_recvM.mpr (Or.inl ⟨e', by rw [hs]; simp, hv'⟩)
  · simp only at h1 h2
    subst h1
    rw [accR_single, ← xv_hst_eq G f N B inp ev h2]; exact hm

theorem M_honest' (r : ℕ) {v : V} (hv : v ∉ B) (t : ℕ) (y : ℝ) (p : List V)
    (hm : (y, p ++ [v]) ∈ Mr G f N B inp ev r v t) (hp : ∀ q ∈ p.getLast?, q ∉ B) :
    y = accR G f N B inp ev r (p ++ [v]) := by
  refine kv_mem G f N B inp ev r hv hm ?_
  rcases hq : p.getLast? with _ | q
  · left; rw [List.getLast?_eq_none_iff.mp hq]; rfl
  · right; exact ⟨p, q, rfl, hq, hp q hq⟩

theorem acc_snoc' (r : ℕ) (p : List V) (q w : V) (hq : p.getLast? = some q) (hqB : q ∉ B) :
    accR G f N B inp ev r (p ++ [w]) = accR G f N B inp ev r p := by
  rw [accR_snoc G f N B inp ev r hq w, ite_eq_right hqB]

theorem M_src' (r : ℕ) {v : V} (_hv : v ∉ B) (t : ℕ) (y : ℝ) (p : List V) (q : V)
    (hm : (y, p ++ [v]) ∈ Mr G f N B inp ev r v t) (hq : p.getLast? = some q) (hqB : q ∉ B) :
    ∃ t', (accR G f N B inp ev r p, p) ∈ Mr G f N B inp ev r q t' := by
  refine ⟨t, ?_⟩
  rcases mem_recvM.mp hm with ⟨e, he, hve⟩ | ⟨h1, -⟩
  · obtain ⟨y', p₀, he', hp₀, hm'⟩ := valOf_eq_some hve
    simp only [Prod.mk.injEq] at hm'
    obtain ⟨rfl, hpp⟩ := hm'
    obtain ⟨rfl, -⟩ := List.append_inj' hpp rfl
    have hqe : e.1 = q := by rw [hp₀] at hq; exact Option.some.inj hq
    subst hqe
    have hsent := (spec G f N).mem_sent_of_mem_hist G B inp ev hqB (t := t) (v := v)
      (m := .val r y p) (by rw [he'] at he; exact he)
    obtain ⟨k, hk, hk'⟩ := mem_allSends.mp hsent
    obtain ⟨-, -, hcase⟩ := val_sent G f N hk'
    rcases hcase with ⟨h₀, u', p₁, hsplit, hp₁, rfl, -, -⟩ | ⟨rfl, hx⟩
    · have hsplit' : (hst G f N B inp ev t e.1).take k = h₀ ++ [(u', BMsg.val r y p₁)] := hsplit
      have hin : (u', BMsg.val r y p₁) ∈ hst G f N B inp ev t e.1 :=
        List.mem_of_mem_take (i := k) (by rw [hsplit']; simp)
      exact M_first' G f N B inp ev r hqB t y _ (mem_recvM.mpr (Or.inl ⟨_, hin, by
        simp [valOf, hp₁]⟩))
    · have := xv_prefix G f N e.1 (inp e.1) r (List.take_prefix _ _) hx
      rw [accR_single, ← xv_hst_eq G f N B inp ev this]
      exact mem_recvM.mpr (Or.inr ⟨rfl, this⟩)
  · have := congrArg List.length h1
    simp only [List.length_append, List.length_singleton] at this
    have : p = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; simp at hq

/-- The first prefix at which round `r` has started. -/
theorem exists_first_start {v : V} {r : ℕ} {h : Hist V} {y : ℝ}
    (hy : xv G f N v (inp v) r h = some y) :
    ∃ k ≤ h.length, xv G f N v (inp v) r (h.take k) = some y ∧
      (h.take k = [] ∨ xv G f N v (inp v) r (h.take k).dropLast = none) := by
  classical
  have hex : ∃ k, (xv G f N v (inp v) r (h.take k)).isSome := ⟨h.length, by simp [hy]⟩
  set k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkle : k ≤ h.length := Nat.find_min' hex (by simp [hy])
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp hk
  have hyy : y' = y := by
    have := xv_prefix G f N v (inp v) r (List.take_prefix k h) hy'
    rw [hy] at this; exact (Option.some.inj this).symm
  subst hyy
  refine ⟨k, hkle, hy', ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · left; rw [hk0]; simp
  · right
    have hmin := Nat.find_min hex (show k - 1 < k by omega)
    rw [List.dropLast_take, show k - 1 = k - 1 from rfl]
    · simpa using hmin
    · omega

variable {G f N B inp ev} in
/-- `M_live`: correct relays forward accepted values, and messages are delivered. -/
theorem M_live' (r : ℕ) (hr : r < N) (hfair : Fair (alg G f N) G B inp ev) {v : V}
    (hv : v ∉ B) (p : List V) (q : V) (hq : p.getLast? = some q) (hqB : q ∉ B)
    (hadj : G.Adj q v) (hqv : q ≠ v) (hred : IsRedundant G (p ++ [v]))
    (hacc : ∃ t, (accR G f N B inp ev r p, p) ∈ Mr G f N B inp ev r q t) :
    ∃ t, (accR G f N B inp ev r p, p ++ [v]) ∈ Mr G f N B inp ev r v t := by
  obtain ⟨t₀, ht₀⟩ := hacc
  have hw : v ∈ outL G q := (mem_outL G).mpr ⟨hadj, hqv⟩
  rcases mem_recvM.mp ht₀ with ⟨e, he, hve⟩ | ⟨h1, h2⟩
  · -- `q` received `p` from another node: it relayed the first one
    obtain ⟨y', hy'⟩ := firstVal_isSome G f N B inp ev he hve
    obtain ⟨A, e', C, hs, hv', hA⟩ := firstVal_spec G f N B inp ev hy'
    have hyacc := kv_first G f N B inp ev r hqB hy'
    obtain ⟨y'', p₀, he', hp₀, hm'⟩ := valOf_eq_some hv'
    simp only [Prod.mk.injEq] at hm'
    obtain ⟨rfl, hpp⟩ := hm'
    have hred' : IsRedundant G (p₀ ++ [q, v]) := by
      have : p₀ ++ [q, v] = p ++ [v] := by rw [hpp]; simp
      rw [this]; exact hred
    have hrel := react_relay_val G f N (x := inp q) (A := A) (y := y') hr hp₀
      (fun e'' he'' m hm hm2 => hA e'' he'' ⟨m, hm, by rw [hm2, hpp]⟩) hw hred'
    rw [← he'] at hrel
    have hsent : (v, BMsg.val r y' (p₀ ++ [q])) ∈
        (spec G f N).allSends q (inp q) (hst G f N B inp ev t₀ q) := by
      refine mem_allSends.mpr ⟨A.length + 1, ?_, ?_⟩
      · have := congrArg List.length hs
        simp only [List.length_append, List.length_cons] at this
        show A.length + 1 ≤ (hst G f N B inp ev t₀ q).length
        omega
      · have : (hst G f N B inp ev t₀ q).take (A.length + 1) = A ++ [e'] := by
          rw [hs, List.take_append]; simp
        show (v, BMsg.val r y' (p₀ ++ [q])) ∈
          (spec G f N).react q (inp q) ((hst G f N B inp ev t₀ q).take (A.length + 1))
        rw [this]; exact hrel
    obtain ⟨t, ht⟩ := (spec G f N).mem_hist_of_mem_sent G B inp ev hfair hqB hv hqv hadj hsent
    refine ⟨t, mem_recvM.mpr (Or.inl ⟨_, ht, ?_⟩)⟩
    simp [valOf, hp₀, hyacc, hpp]
  · -- own value
    simp only at h1 h2
    subst h1
    obtain ⟨k, hk, hk1, hk2⟩ := exists_first_start G f N inp h2
    have hsent : (v, BMsg.val r (accR G f N B inp ev r [q]) [q]) ∈
        (spec G f N).allSends q (inp q) (hst G f N B inp ev t₀ q) :=
      mem_allSends.mpr ⟨k, hk, react_newVal G f N hr hk1 hk2 hw⟩
    obtain ⟨t, ht⟩ := (spec G f N).mem_hist_of_mem_sent G B inp ev hfair hqB hv hqv hadj hsent
    exact ⟨t, mem_recvM.mpr (Or.inl ⟨_, ht, by simp [valOf]⟩)⟩

theorem M_live_self' (r : ℕ) {s : V}
    (hstart : ∃ t, (xv G f N s (inp s) r (hst G f N B inp ev t s)).isSome) :
    ∃ t, (Xr G f N B inp ev r s, [s]) ∈ Mr G f N B inp ev r s t := by
  obtain ⟨t, ht⟩ := hstart
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ht
  refine ⟨t, mem_recvM.mpr (Or.inr ⟨rfl, ?_⟩)⟩
  rw [hy, ← xv_hst_eq G f N B inp ev hy]

end BWOp

end AsyncApproxBCDirected
