import Papers.PODC2020.DetectableSpace.Lin
import Papers.PODC2020.DetectableSpace.Perturbing

/-!
# Theorem 2: detectable implementations of doubly-perturbing objects need auxiliary state

In our model an implementation `A : RImpl O P` receives exactly the arguments of the abstract
operations (`O.Op`), so auxiliary state can only be provided via non-volatile memory, by the
system / caller at invocation time (`A.aux`). "No auxiliary state" is `∀ p o v, A.aux p o v = v`.

`theorem2`: in a weakly obstruction-free, durably linearizable and detectable implementation,
an operation witnessing that the object is doubly-perturbing must receive auxiliary state
(`theorem2_exists`: some operation of a doubly-perturbing object does).

The proof follows the paper (Figure 2): executions `D` (crash just before `p` returns from its
first `Op_p`) and `E` (`p` returns, invokes `Op_p` again and the system crashes immediately) are
indistinguishable after the crash; `p`'s recovery returns the same value `x` and `q`'s
operation `Op_q` returns the same value `y` in both. In `D`, `Op_p` must be linearized before
`Op_r` (it perturbed `Op_r`), so `x ≠ fail` and `y` is the response of `Op_q` after `H₂`; in `E`,
`x ≠ fail` means the second `Op_p` was linearized before `Op_q`, so `y` is the response after
`H₂ ∘ Op_p` — these differ since `Op_p` is perturbing after `H₂`.

(The paper derives "`Op_q` returns `u` after `E₁`" from linearizability of `E`; that step is not
justified as stated — the second `Op_p` is pending there — but it is not needed: we use the
linearization of `D` instead, see `differencies.md`.)
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

variable {O : ObjSpec} {P : Type}

lemma seqHist_append (H H' : List (P × O.Op)) (rs rs' : List O.Resp)
    (hlen : rs.length = H.length) (n : ℕ) :
    seqHist n (H ++ H') (rs ++ rs') = seqHist n H rs ++ seqHist (n + H.length) H' rs' := by
  induction H generalizing n rs with
  | nil =>
    have : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst this; simp [seqHist]
  | cons x H ih =>
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, seqHist, ih rs hlen (n + 1), List.length_cons]
      simp [Nat.add_assoc, Nat.add_comm 1]

lemma specResps_append (σ : O.State) (H H' : List (P × O.Op)) :
    specResps σ (H ++ H') = specResps σ H ++ specResps (O.runOps σ (H.map Prod.snd)) H' := by
  induction H generalizing σ with
  | nil => simp [specResps]
  | cons x H ih => simp [specResps, ih]

lemma length_specResps (σ : O.State) (H : List (P × O.Op)) :
    (specResps σ H).length = H.length := by
  induction H generalizing σ with
  | nil => rfl
  | cons x H ih => simp [specResps, ih]

namespace RImpl

variable [DecidableEq P] (A : RImpl O P)

lemma exec_append_eq {C D D' : A.Cfg} {es fs : List (Ev P O.Op)}
    {h h' : List (HEv P O.Op O.Resp)} (h1 : A.exec C es = (D, h)) (h2 : A.exec D fs = (D', h')) :
    A.exec C (es ++ fs) = (D', h ++ h') := by
  rw [exec_append, h1]; simp [h2]

end RImpl

/-- If every element of `L` has identifier `≥ m`, and the only invocations with such
identifiers in `h` are those of `t`, then every element of `L` is invoked in `t`. -/
lemma inv_in_tail {h s t : List (HEv P O.Op O.Resp)} (hh : h = s ++ t) {m : ℕ}
    (hs : ∀ a p o, HEv.inv a p o ∈ s → a < m) {y : ℕ × O.Op} (hy : m ≤ y.1)
    (hinv : ∃ p, HEv.inv y.1 p y.2 ∈ h) : ∃ p, HEv.inv y.1 p y.2 ∈ t := by
  obtain ⟨p, hp⟩ := hinv
  rw [hh] at hp
  rcases List.mem_append.1 hp with hp | hp
  · have := hs _ _ _ hp; omega
  · exact ⟨p, hp⟩

lemma mem_seqL {n : ℕ} {H : List (P × O.Op)} {y : ℕ × O.Op} (hy : y ∈ seqL n H) :
    n ≤ y.1 ∧ y.1 < n + H.length := by
  induction H generalizing n with
  | nil => simp [seqL] at hy
  | cons x H ih =>
    simp only [seqL, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp
    · have := ih hy; simp only [List.length_cons]; omega

/-- An identifier `a ≥ n + |H|` in a linearization `seqL n H ++ L'` is in `L'`. -/
lemma mem_tail_of_ge {n : ℕ} {H : List (P × O.Op)} {L' : List (ℕ × O.Op)} {a : ℕ}
    (ha : a ∈ (seqL n H ++ L').map Prod.fst) (hge : n + H.length ≤ a) :
    ∃ y ∈ L', y.1 = a := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
  rcases List.mem_append.1 hy with hy' | hy'
  · have := mem_seqL hy'; omega
  · exact ⟨y, hy', rfl⟩

/-- The linearization argument in execution `E`. -/
lemma lin_E {H2 : List (P × O.Op)} {rs : List O.Resp} (hlen : rs.length = H2.length) {m : ℕ}
    (hm : m = H2.length) {p q : P} {op o_q : O.Op} {x : Option O.Resp} {y0 : O.Resp}
    {h : List (HEv P O.Op O.Resp)}
    (hh : h = seqHist 0 H2 rs ++ [.inv m p op, .crash, .res m x true,
      .inv (m + 1) q o_q, .res (m + 1) (some y0) false])
    (hU : ∀ a p o p' o', HEv.inv a p o ∈ h → HEv.inv a p' o' ∈ h → o = o')
    {L : List (ℕ × O.Op)} (hL : DLin O h O.init L) :
    rs = specResps O.init H2 ∧ (x ≠ none → y0 = respAfter O (H2 ++ [(p, op)]) o_q) := by
  set t : List (HEv P O.Op O.Resp) := [.inv m p op, .crash, .res m x true,
      .inv (m + 1) q o_q, .res (m + 1) (some y0) false] with ht
  have hseq : ∀ a p o, HEv.inv a p o ∈ seqHist 0 H2 rs → a < m := by
    intro a p o ha; have := mem_seqHist_inv ha; omega
  obtain ⟨L', hLeq, hge, hleg, hrs⟩ := peel_seq hU H2 rs 0 [] t O.init L hlen (by simp [hh, ht])
    (by simp) (by intro a p o ha; simp [ht] at ha; omega) hL.nodup hL.rt hL.legal
    hL.inv_of_mem (by simp) (fun a r c ha _ => hL.mem_of_res a r c ha)
  refine ⟨hrs, fun hx => ?_⟩
  obtain ⟨x0, rfl⟩ := Option.ne_none_iff_exists'.1 hx
  have hinvt : ∀ y ∈ L', y = (m, op) ∨ y = (m + 1, o_q) := by
    intro y hy
    obtain ⟨p', hp'⟩ := inv_in_tail hh hseq (by have := hge y hy; omega)
      (hL.inv_of_mem y (by rw [hLeq]; exact List.mem_append_right _ hy))
    simp only [ht, List.mem_cons, HEv.inv.injEq, reduceCtorEq, List.mem_nil_iff, or_false,
      false_or] at hp'
    rcases hp' with ⟨h1, -, h2⟩ | ⟨h1, -, h2⟩
    · exact .inl (Prod.ext h1 h2)
    · exact .inr (Prod.ext h1 h2)
  have hmemL' : ∀ a o, HEv.inv a q o ∈ h ∨ HEv.inv a p o ∈ h → (∃ r c, HEv.res a (some r) c ∈ h) →
      m ≤ a → (a, o) ∈ L' := by
    intro a o hinv ⟨r, c, hr⟩ hma
    obtain ⟨y, hy, hya⟩ := mem_tail_of_ge (hLeq ▸ hL.mem_of_res a r c hr) (by omega)
    obtain ⟨p', hp'⟩ := hL.inv_of_mem y (by rw [hLeq]; exact List.mem_append_right _ hy)
    rw [hya] at hp'
    have : y.2 = o := by
      rcases hinv with hinv | hinv
      · exact hU _ _ _ _ _ hp' hinv
      · exact hU _ _ _ _ _ hp' hinv
    rw [show (a, o) = y from Prod.ext hya.symm this.symm]; exact hy
  have hm1 : (m, op) ∈ L' := hmemL' m op (.inr (by simp [hh, ht])) ⟨x0, true, by simp [hh, ht]⟩ le_rfl
  have hm2 : (m + 1, o_q) ∈ L' := hmemL' (m + 1) o_q (.inl (by simp [hh, ht]))
    ⟨y0, false, by simp [hh, ht]⟩ (by omega)
  have hrt' : L'.Pairwise (fun x y => ¬ Prec h y.1 x.1) := by
    have := hL.rt; rw [hLeq] at this; exact (List.pairwise_append.1 this).2.1
  have hnd' : (L'.map Prod.fst).Nodup := by
    have := hL.nodup; rw [hLeq, List.map_append] at this; exact (List.nodup_append.1 this).2.1
  obtain ⟨L'', rfl⟩ := peel_head hrt' hm1
    (h₁ := seqHist 0 H2 rs ++ [.inv m p op, .crash, .res m (some x0) true])
    (h₂ := [.inv (m + 1) q o_q, .res (m + 1) (some y0) false]) (by simp [hh, ht])
    ⟨some x0, true, by simp⟩
    (by
      intro y hy hne
      rcases hinvt y hy with rfl | rfl
      · exact absurd rfl hne
      · exact ⟨q, by simp⟩)
  have hm2' : (m + 1, o_q) ∈ L'' := by
    rcases List.mem_cons.1 hm2 with h | h
    · simp at h
    · exact h
  obtain ⟨L''', rfl⟩ := peel_head (List.pairwise_cons.1 hrt').2 hm2' (h₁ := h) (h₂ := [])
    (by simp) ⟨some y0, false, by simp [hh, ht]⟩
    (by
      intro y hy hne
      exfalso
      rcases hinvt y (List.mem_cons_of_mem _ hy) with rfl | rfl
      · rw [List.map_cons, List.nodup_cons] at hnd'
        exact (hnd'.1 (List.mem_map.2 ⟨_, hy, rfl⟩)).elim
      · exact hne rfl)
  have hleg2 := (Legal.cons (Legal.cons hleg).2).1 y0 false (by simp [hh, ht])
  rw [hleg2]
  simp [respAfter, stateAfter, ObjSpec.runOps_append]

/-- The linearization argument in execution `D`. -/
lemma lin_D {H₁ E : List (P × O.Op)} {rs1 rs2 : List O.Resp} (hlen1 : rs1.length = H₁.length)
    (hlen2 : rs2.length = E.length) {n1 m : ℕ} (hn1 : n1 = H₁.length)
    (hm : m = n1 + 1 + (E.length + 1)) {p q r : P} {op o_r o_q : O.Op} {ρ : O.Resp}
    (hpert : ρ ≠ respAfter O H₁ o_r) {x : Option O.Resp} {y0 : O.Resp}
    {h : List (HEv P O.Op O.Resp)}
    (hh : h = seqHist 0 H₁ rs1 ++ [.inv n1 p op] ++ seqHist (n1 + 1) ((r, o_r) :: E) (ρ :: rs2) ++
      [.crash, .res n1 x true, .inv m q o_q, .res m (some y0) false])
    (hU : ∀ a p o p' o', HEv.inv a p o ∈ h → HEv.inv a p' o' ∈ h → o = o')
    {L : List (ℕ × O.Op)} (hL : DLin O h O.init L) :
    x ≠ none ∧ y0 = respAfter O (H₁ ++ [(p, op), (r, o_r)] ++ E) o_q := by
  set tD : List (HEv P O.Op O.Resp) :=
    [.crash, .res n1 x true, .inv m q o_q, .res m (some y0) false] with htD
  have hseqE : ∀ a p o, HEv.inv a p o ∈ seqHist (n1 + 1) ((r, o_r) :: E) (ρ :: rs2) →
      n1 + 1 ≤ a ∧ a < m := by
    intro a p o ha; have := mem_seqHist_inv ha; simp at this; omega
  have hseq1 : ∀ a p o, HEv.inv a p o ∈ seqHist 0 H₁ rs1 → a < n1 := by
    intro a p o ha; have := mem_seqHist_inv ha; omega
  -- membership of completed operations with a known invocation
  have hmemL : ∀ (L₀ L₁ : List (ℕ × O.Op)) (k : ℕ), L = L₀ ++ L₁ →
      (∀ y ∈ L₀, y.1 < k) → ∀ a p' o, HEv.inv a p' o ∈ h → (∃ r c, HEv.res a (some r) c ∈ h) →
      k ≤ a → (a, o) ∈ L₁ := by
    intro L₀ L₁ k hL01 hL0 a p' o hinv ⟨r', c, hr⟩ hka
    obtain ⟨y, hy, hya⟩ := List.mem_map.1 (hL.mem_of_res a r' c hr)
    rw [hL01] at hy
    rcases List.mem_append.1 hy with hy | hy
    · have := hL0 y hy; omega
    · obtain ⟨p'', hp''⟩ := hL.inv_of_mem y (by rw [hL01]; exact List.mem_append_right _ hy)
      rw [hya] at hp''
      rw [show (a, o) = y from Prod.ext hya.symm (hU _ _ _ _ _ hp'' hinv).symm]; exact hy
  obtain ⟨L1, hLeq, hge1, hleg1, -⟩ := peel_seq hU H₁ rs1 0 []
    ([.inv n1 p op] ++ seqHist (n1 + 1) ((r, o_r) :: E) (ρ :: rs2) ++ tD) O.init L hlen1
    (by simp [hh, htD]) (by simp)
    (by
      intro a p' o ha
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, htD, reduceCtorEq,
        List.mem_nil_iff, or_false, false_or] at ha
      rcases ha with (ha | ha) | ha
      · simp only [HEv.inv.injEq] at ha; omega
      · have := hseqE _ _ _ ha; omega
      · simp only [HEv.inv.injEq] at ha; omega)
    hL.nodup hL.rt hL.legal hL.inv_of_mem (by simp) (fun a r c ha _ => hL.mem_of_res a r c ha)
  have hseqL1 : ∀ y ∈ seqL 0 H₁, y.1 < n1 := fun y hy => by have := mem_seqL hy; omega
  have hrt1 : L1.Pairwise (fun x y => ¬ Prec h y.1 x.1) := by
    have := hL.rt; rw [hLeq] at this; exact (List.pairwise_append.1 this).2.1
  have hnd1 : (L1.map Prod.fst).Nodup := by
    have := hL.nodup; rw [hLeq, List.map_append] at this; exact (List.nodup_append.1 this).2.1
  have hinvh : ∀ y ∈ L1, ∃ p', HEv.inv y.1 p' y.2 ∈ h :=
    fun y hy => hL.inv_of_mem y (by rw [hLeq]; exact List.mem_append_right _ hy)
  have hr_in : HEv.inv (n1 + 1) r o_r ∈ h := by simp [hh, seqHist]
  have hres_r : HEv.res (n1 + 1) (some ρ) false ∈ h := by simp [hh, seqHist]
  have hmr : (n1 + 1, o_r) ∈ L1 :=
    hmemL _ _ n1 hLeq hseqL1 _ _ _ hr_in ⟨ρ, false, hres_r⟩ (by omega)
  -- the head of `L1` is `p`'s operation
  obtain ⟨y0', L2, hL1⟩ : ∃ y L2, L1 = y :: L2 := by
    cases L1 with
    | nil => simp at hmr
    | cons y L2 => exact ⟨y, L2, rfl⟩
  have hy0 : y0' = (n1, op) := by
    by_contra hne
    have hyge := hge1 y0' (by simp [hL1])
    obtain ⟨p', hp'⟩ := hinvh y0' (by simp [hL1])
    have hne1 : y0'.1 ≠ n1 := by
      intro he
      apply hne
      refine Prod.ext he ?_
      rw [he] at hp'
      exact hU n1 p' y0'.2 p op hp' (by simp [hh])
    by_cases h2 : y0'.1 = n1 + 1
    · have hop : y0'.2 = o_r := by rw [h2] at hp'; exact hU _ _ _ _ _ hp' hr_in
      have hy0eq : y0' = (n1 + 1, o_r) := Prod.ext h2 hop
      rw [hL1, hy0eq] at hleg1
      have := (Legal.cons hleg1).1 ρ false hres_r
      exact hpert (by rw [this]; rfl)
    · -- `y0'` was invoked after `r`'s operation returned
      have hmr2 : (n1 + 1, o_r) ∈ L2 := by
        rw [hL1] at hmr
        rcases List.mem_cons.1 hmr with he | he
        · exact absurd (by rw [← he]) h2
        · exact he
      rw [hL1] at hrt1
      apply (List.pairwise_cons.1 hrt1).1 _ hmr2
      refine ⟨seqHist 0 H₁ rs1 ++ [.inv n1 p op, .inv (n1 + 1) r o_r, .res (n1 + 1) (some ρ) false],
        seqHist (n1 + 1 + 1) E rs2 ++ tD, by simp [hh, htD, seqHist], ⟨some ρ, false, by simp⟩, ?_⟩
      obtain ⟨p'', hp''⟩ := inv_in_tail (s := seqHist 0 H₁ rs1 ++
          [.inv n1 p op, .inv (n1 + 1) r o_r, .res (n1 + 1) (some ρ) false])
        (t := seqHist (n1 + 1 + 1) E rs2 ++ tD) (m := n1 + 2) (by simp [hh, htD, seqHist])
        (by
          intro a p₀ o ha
          simp only [List.mem_append, List.mem_cons, HEv.inv.injEq, reduceCtorEq,
            List.mem_nil_iff, or_false] at ha
          rcases ha with ha | ha | ha
          · have := hseq1 _ _ _ ha; omega
          · omega
          · omega)
        (by omega) ⟨p', hp'⟩
      exact ⟨p'', _, hp''⟩
  subst hy0
  -- `x` is not `fail`
  have hx : x ≠ none := by
    rintro rfl
    apply hL.not_mem_of_fail n1 true (by simp [hh, htD])
    rw [hLeq, hL1]; simp
  refine ⟨hx, ?_⟩
  rw [hL1] at hleg1 hrt1 hnd1
  have hleg2 := (Legal.cons hleg1).2
  have hnd2 : (L2.map Prod.fst).Nodup := (List.nodup_cons.1 (by simpa using hnd1)).2
  have hnL2 : n1 ∉ L2.map Prod.fst := (List.nodup_cons.1 (by simpa using hnd1)).1
  have hge2 : ∀ y ∈ L2, n1 + 1 ≤ y.1 := by
    intro y hy
    have h1 := hge1 y (by simp [hL1, hy])
    have h2 : y.1 ≠ n1 := fun he => hnL2 (List.mem_map.2 ⟨y, hy, he⟩)
    omega
  obtain ⟨L3, hL2, hge3, hleg3, -⟩ := peel_seq hU ((r, o_r) :: E) (ρ :: rs2) (n1 + 1)
    (seqHist 0 H₁ rs1 ++ [.inv n1 p op]) tD _ L2 (by simp [hlen2])
    (by simp [hh, htD])
    (by
      intro a p' o ha
      rcases List.mem_append.1 ha with ha | ha
      · have := hseq1 _ _ _ ha; omega
      · simp at ha; omega)
    (by intro a p' o ha; simp [htD] at ha; simp; omega)
    hnd2 (List.pairwise_cons.1 hrt1).2 hleg2
    (fun y hy => hinvh y (by simp [hL1, hy])) hge2
    (by
      intro a r' c ha hna
      have := hL.mem_of_res a r' c ha
      rw [hLeq, hL1] at this
      obtain ⟨y, hy, hya⟩ := List.mem_map.1 this
      rcases List.mem_append.1 hy with hy | hy
      · have := hseqL1 y hy; omega
      · rcases List.mem_cons.1 hy with hy | hy
        · subst hy; simp at hya; omega
        · exact List.mem_map.2 ⟨y, hy, hya⟩)
  have hq_in : HEv.inv m q o_q ∈ h := by simp [hh, htD]
  have hmq : (m, o_q) ∈ L3 := by
    refine hmemL (seqL 0 H₁ ++ (n1, op) :: seqL (n1 + 1) ((r, o_r) :: E)) L3 m
      (by rw [hLeq, hL1, hL2]; simp) ?_ _ _ _ hq_in ⟨y0, false, by simp [hh, htD]⟩ le_rfl
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · have := hseqL1 y hy; omega
    · rcases List.mem_cons.1 hy with hy | hy
      · subst hy; simp; omega
      · have := mem_seqL hy; simp at this; omega
  have hrt3 : L3.Pairwise (fun x y => ¬ Prec h y.1 x.1) := by
    have := (List.pairwise_cons.1 hrt1).2; rw [hL2] at this
    exact (List.pairwise_append.1 this).2.1
  obtain ⟨L4, rfl⟩ := peel_head hrt3 hmq (h₁ := h) (h₂ := []) (by simp)
    ⟨some y0, false, by simp [hh, htD]⟩
    (by
      intro y hy hne
      exfalso
      obtain ⟨p', hp'⟩ := inv_in_tail (s := seqHist 0 H₁ rs1 ++ [.inv n1 p op] ++
          seqHist (n1 + 1) ((r, o_r) :: E) (ρ :: rs2)) (t := tD) (m := m) (by simp [hh, htD])
        (by
          intro a p₀ o ha
          simp only [List.mem_append, List.mem_singleton] at ha
          rcases ha with (ha | ha) | ha
          · have := hseq1 _ _ _ ha; omega
          · simp only [HEv.inv.injEq] at ha; omega
          · exact (hseqE _ _ _ ha).2)
        (by have := hge3 y hy; simp at this; omega) (hinvh y (by simp [hL1, hL2, hy]))
      simp only [htD, List.mem_cons, reduceCtorEq, HEv.inv.injEq, List.mem_nil_iff,
        or_false, false_or] at hp'
      exact hne (Prod.ext hp'.1 hp'.2.2))
  have := (Legal.cons hleg3).1 y0 false (by simp [hh, htD])
  rw [this]
  simp [respAfter, stateAfter, ObjSpec.runOps_append]

/-- **Theorem 2.** Let `A` be a weakly obstruction-free recoverable implementation of `O`
satisfying durable linearizability and detectability, and let the operation `op` of process `p`
witness that `O` is doubly-perturbing. Then `op` must receive auxiliary state: in our model
(operations receive exactly the arguments of the abstract operations) the system / caller must
write to `p`'s private non-volatile memory when `p` invokes `op`.

The paper says "let `Op` be a recoverable operation"; read universally this is false (e.g. a
`read` of a register needs no auxiliary state), the intended `Op` is the witness. -/
theorem theorem2 [DecidableEq P] (A : RImpl O P) {p : P} {op : O.Op} (hw : DPWitness O p op)
    (hwof : A.WeakOF) (hcor : A.DurLinDet) : ∃ v, A.aux p op v ≠ v := by
  by_contra hcon
  push Not at hcon
  have haux : ∀ v, A.aux p op v = v := hcon
  obtain ⟨H₁, r, o_r, ⟨hrp, hpert1⟩, E, hE, q, o_q, -, hpert2⟩ := hw
  have hU : ∀ es a p o p' o', HEv.inv a p o ∈ (A.exec A.init es).2 →
      HEv.inv a p' o' ∈ (A.exec A.init es).2 → o = o' :=
    fun es a p o p' o' h1 h2 => (A.exec_inv_unique _ es a p p' o o' h1 h2).2
  /- α: the sequential history `H₁`. -/
  obtain ⟨esα, rsα, hlenα, -, hhα, hqα, hcntα⟩ := A.seq_exec hwof hcor H₁ [] (fun x => rfl)
  simp only [RImpl.exec_nil] at hhα hqα hcntα
  have hinit : A.init.cnt = 0 := rfl
  rw [hinit, Nat.zero_add] at hcntα
  rw [hinit] at hhα
  set Cα := (A.exec A.init esα).1 with hCα
  have exα : A.exec A.init esα = (Cα, seqHist 0 H₁ rsα) := Prod.ext rfl hhα
  /- β: `p` runs `op` solo until it is about to return. -/
  set n1 := Cα.cnt with hn1
  set Cα1 := (A.step1 Cα (.inv p op)).1 with hCα1
  have hs1 : A.step1 Cα (.inv p op) = (Cα1, [.inv n1 p op]) :=
    Prod.ext rfl (by rw [A.step1_inv_idle Cα p op (hqα p)])
  have hps1 : Cα1.ps p = .run n1 op false (A.start p op) := by
    rw [hCα1, A.step1_inv_idle Cα p op (hqα p)]; simp [hn1]
  have hoth1 : ∀ y, y ≠ p → Cα1.ps y = .idle := by
    intro y hy; rw [hCα1, A.step1_inv_idle Cα p op (hqα p)]; simp [Function.update_of_ne hy, hqα y]
  have hcnt1 : Cα1.cnt = n1 + 1 := by rw [hCα1, A.step1_inv_idle Cα p op (hqα p)]
  have ex1 : A.exec A.init (esα ++ [.inv p op]) = (Cα1, seqHist 0 H₁ rsα ++ [.inv n1 p op]) :=
    A.exec_append_eq exα (by rw [RImpl.exec_singleton, hs1])
  obtain ⟨k, hk⟩ := hwof Cα1 ⟨esα ++ [.inv p op], by rw [ex1]⟩ p hoth1
  obtain ⟨j, -, l', r0, hj1, hj2, hj3⟩ := A.solo_ret p k Cα1 _ _ _ _ hps1 hk
  set Cβ := (A.exec Cα1 (RImpl.solo p j)).1 with hCβ
  have ex2 : A.exec A.init (esα ++ [.inv p op] ++ RImpl.solo p j) =
      (Cβ, seqHist 0 H₁ rsα ++ [.inv n1 p op] ++ []) := A.exec_append_eq ex1 (Prod.ext rfl hj3)
  have hcntβ : Cβ.cnt = n1 + 1 := by rw [hCβ, RImpl.exec_solo_cnt, hcnt1]
  set Cβ' : A.Cfg := ⟨Cβ.sh, Cβ.pv, Function.update Cβ.ps p .idle, Cβ.cnt⟩ with hCβ'
  have hs2 : A.step1 Cβ (.step p) = (Cβ', [.res n1 r0 false]) := by
    simp [RImpl.step1, hj1, hj2, hCβ']
  have ex3 : A.exec A.init (esα ++ [.inv p op] ++ RImpl.solo p j ++ [.step p]) =
      (Cβ', seqHist 0 H₁ rsα ++ [.inv n1 p op] ++ [] ++ [.res n1 r0 false]) :=
    A.exec_append_eq ex2 (by rw [RImpl.exec_singleton, hs2])
  obtain ⟨r0', rfl⟩ : ∃ r0', r0 = some r0' := by
    cases r0 with
    | some r0' => exact ⟨r0', rfl⟩
    | none => exact absurd (by rw [ex3]; simp) ((hcor _).2 n1)
  have hothβ : ∀ y, y ≠ p → Cβ.ps y = .idle := by
    intro y hy; rw [hCβ, (A.exec_solo_other Cα1 hy j).1]; exact hoth1 y hy
  have hqβ' : A.Quiescent Cβ' := by
    intro y
    by_cases hy : y = p
    · subst hy; simp [hCβ']
    · simp [hCβ', Function.update_of_ne hy, hothβ y hy]
  /- γ: the `p`-free sequential history `(r, o_r) :: E`. -/
  obtain ⟨esγ, rsγ, hlenγ, hfreeγ, hhγ, hqγ, hcntγ⟩ := A.seq_exec hwof hcor ((r, o_r) :: E)
    (esα ++ [.inv p op] ++ RImpl.solo p j ++ [.step p]) (by rw [ex3]; exact hqβ')
  rw [ex3] at hhγ hqγ hcntγ
  simp only at hhγ hqγ hcntγ
  set Cγ' := (A.exec Cβ' esγ).1 with hCγ'
  have hfree : ∀ e ∈ esγ, e.Free p := by
    intro e he
    refine hfreeγ e he p ?_
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hrp
    · exact hE y hy
  have heqβ : A.EqEx p Cβ Cβ' := by
    refine ⟨rfl, rfl, fun _ _ => rfl, fun x hx => ?_⟩
    simp [hCβ', Function.update_of_ne hx]
  obtain ⟨heqγ, hhistγ⟩ := heqβ.exec esγ hfree
  set Cγ := (A.exec Cβ esγ).1 with hCγ
  have exγ' : A.exec Cβ' esγ = (Cγ', seqHist (n1 + 1) ((r, o_r) :: E) rsγ) := by
    refine Prod.ext rfl ?_; rw [hhγ, hcntβ]
  have exγ : A.exec Cβ esγ = (Cγ, seqHist (n1 + 1) ((r, o_r) :: E) rsγ) := by
    refine Prod.ext rfl ?_; rw [hhistγ, hhγ, hcntβ]
  have hpsγ : Cγ.ps p = .run n1 op false l' := by
    rw [hCγ, (A.exec_free Cβ p esγ hfree).1]; exact hj1
  have hpvγ : Cγ.pv p = Cγ'.pv p := by
    rw [hCγ, hCγ', (A.exec_free Cβ p esγ hfree).2, (A.exec_free Cβ' p esγ hfree).2]
  set m := Cγ'.cnt with hm
  have hm' : m = n1 + 1 + (E.length + 1) := by
    rw [hcntγ]; simp [hCβ', hcntβ]
  have hcntγ0 : Cγ.cnt = m := heqγ.cnt
  /- The crash: world `D` (crash just before `p` returns) and world `E` (`p` returns, invokes
  `op` again, crash). -/
  have hqγp : Cγ'.ps p = .idle := hqγ p
  set Ei := (A.step1 Cγ' (.inv p op)).1 with hEi
  have hsEi : A.step1 Cγ' (.inv p op) = (Ei, [.inv m p op]) :=
    Prod.ext rfl (by rw [A.step1_inv_idle Cγ' p op hqγp])
  set E1 := (A.step1 Ei .crash).1 with hE1
  have hsE1 : A.step1 Ei .crash = (E1, [.crash]) := rfl
  set D1 := (A.step1 Cγ .crash).1 with hD1
  have hsD1 : A.step1 Cγ .crash = (D1, [.crash]) := rfl
  have hE1p : E1.ps p = .run m op true (A.recov p op) := by
    show A.crashPS p (Ei.ps p) = _
    rw [hEi, A.step1_inv_idle Cγ' p op hqγp]; simp [RImpl.crashPS, hm]
  have hE1oth : ∀ y, y ≠ p → E1.ps y = .idle := by
    intro y hy
    show A.crashPS y (Ei.ps y) = _
    rw [hEi, A.step1_inv_idle Cγ' p op hqγp]; simp [RImpl.crashPS, Function.update_of_ne hy, hqγ y]
  have hE1cnt : E1.cnt = m + 1 := by
    show Ei.cnt = _
    rw [hEi, A.step1_inv_idle Cγ' p op hqγp]
  have hD1p : D1.ps p = .run n1 op true (A.recov p op) := by
    show A.crashPS p (Cγ.ps p) = _
    rw [hpsγ]; rfl
  have hD1cnt : D1.cnt = m := hcntγ0
  have hag1 : A.Agree Set.univ D1 E1 := by
    refine ⟨?_, ?_, ?_⟩
    · show Cγ.sh = Ei.sh
      rw [hEi, A.step1_inv_idle Cγ' p op hqγp]; exact heqγ.sh
    · intro y _
      show Cγ.pv y = Ei.pv y
      rw [hEi, A.step1_inv_idle Cγ' p op hqγp]
      by_cases hy : y = p
      · subst hy; simp [haux, hpvγ]
      · simp [Function.update_of_ne hy, heqγ.pv y hy]; rfl
    · intro y _
      by_cases hy : y = p
      · subst hy; rw [hD1p, hE1p]; rfl
      · rw [hE1oth y hy]
        show (A.crashPS y (Cγ.ps y)).erase = _
        rw [heqγ.ps y hy, hqγ y]; rfl
  have exE0 : A.exec A.init (esα ++ [.inv p op] ++ RImpl.solo p j ++ [.step p] ++ esγ ++
      [.inv p op] ++ [.crash]) =
      (E1, seqHist 0 H₁ rsα ++ [.inv n1 p op] ++ [] ++ [.res n1 (some r0') false] ++
        seqHist (n1 + 1) ((r, o_r) :: E) rsγ ++ [.inv m p op] ++ [.crash]) :=
    A.exec_append_eq (A.exec_append_eq (A.exec_append_eq ex3 exγ')
      (by rw [RImpl.exec_singleton, hsEi])) (by rw [RImpl.exec_singleton, hsE1])
  have exD0 : A.exec A.init (esα ++ [.inv p op] ++ RImpl.solo p j ++ esγ ++ [.crash]) =
      (D1, seqHist 0 H₁ rsα ++ [.inv n1 p op] ++ [] ++
        seqHist (n1 + 1) ((r, o_r) :: E) rsγ ++ [.crash]) :=
    A.exec_append_eq (A.exec_append_eq ex2 exγ) (by rw [RImpl.exec_singleton, hsD1])
  /- `p` recovers solo. -/
  have reach_of : ∀ {es : List (Ev P O.Op)} {C : A.Cfg} {h : List (HEv P O.Op O.Resp)},
      A.exec A.init es = (C, h) → A.Reachable C := fun h => ⟨_, by rw [h]⟩
  obtain ⟨K, hK⟩ := hwof E1 (reach_of exE0) p hE1oth
  obtain ⟨xr, hxr⟩ := A.solo_hist p K E1 m op true _ hE1p hK
  obtain ⟨hag2, her2⟩ := hag1.exec (RImpl.solo p K) (RImpl.solo_in Set.univ (Set.mem_univ p) K)
  set E2 := (A.exec E1 (RImpl.solo p K)).1 with hE2
  set D2 := (A.exec D1 (RImpl.solo p K)).1 with hD2
  have hidle : ∀ y, (E2.ps y = .idle) → D2.ps y = .idle := by
    intro y hy
    rcases RImpl.PSt.erase_eq_iff.1 (hag2.ps y (Set.mem_univ y)) with ⟨h1, -⟩ | ⟨_, _, _, _, _, -, h2⟩
    · exact h1
    · rw [hy] at h2; cases h2
  have hE2q : A.Quiescent E2 := by
    intro y
    by_cases hy : y = p
    · subst hy; exact hK
    · rw [hE2, (A.exec_solo_other E1 hy K).1]; exact hE1oth y hy
  have hD2q : A.Quiescent D2 := fun y => hidle y (hE2q y)
  obtain ⟨xr', hxr'⟩ := A.solo_hist p K D1 n1 op true _ hD1p (hD2q p)
  have hxx : xr' = xr := by
    have := her2; rw [hxr, hxr'] at this; simpa [HEv.erase] using this
  subst hxx
  have hE2cnt : E2.cnt = m + 1 := by rw [hE2, RImpl.exec_solo_cnt, hE1cnt]
  have hD2cnt : D2.cnt = m := by rw [hD2, RImpl.exec_solo_cnt, hD1cnt]
  /- `q` runs `o_q` solo. -/
  set E3 := (A.step1 E2 (.inv q o_q)).1 with hE3
  have hsE3 : A.step1 E2 (.inv q o_q) = (E3, [.inv (m + 1) q o_q]) :=
    Prod.ext rfl (by rw [A.step1_inv_idle E2 q o_q (hE2q q), hE2cnt])
  set D3 := (A.step1 D2 (.inv q o_q)).1 with hD3
  have hsD3 : A.step1 D2 (.inv q o_q) = (D3, [.inv m q o_q]) :=
    Prod.ext rfl (by rw [A.step1_inv_idle D2 q o_q (hD2q q), hD2cnt])
  have hag3 := (hag2.step1 (.inv q o_q) (Set.mem_univ q)).1
  have hE3q : E3.ps q = .run (m + 1) o_q false (A.start q o_q) := by
    rw [hE3, A.step1_inv_idle E2 q o_q (hE2q q)]; simp [hE2cnt]
  have hD3q : D3.ps q = .run m o_q false (A.start q o_q) := by
    rw [hD3, A.step1_inv_idle D2 q o_q (hD2q q)]; simp [hD2cnt]
  have hE3oth : ∀ y, y ≠ q → E3.ps y = .idle := by
    intro y hy; rw [hE3, A.step1_inv_idle E2 q o_q (hE2q q)]; simp [Function.update_of_ne hy, hE2q y]
  have exE1 := A.exec_append_eq (A.exec_append_eq exE0
    (show A.exec E1 (RImpl.solo p K) = (E2, [.res m xr' true]) from Prod.ext rfl hxr))
    (by rw [RImpl.exec_singleton, hsE3])
  have exD1 := A.exec_append_eq (A.exec_append_eq exD0
    (show A.exec D1 (RImpl.solo p K) = (D2, [.res n1 xr' true]) from Prod.ext rfl hxr'))
    (by rw [RImpl.exec_singleton, hsD3])
  obtain ⟨K', hK'⟩ := hwof E3 (reach_of exE1) q hE3oth
  obtain ⟨yr, hyr⟩ := A.solo_hist q K' E3 (m + 1) o_q false _ hE3q hK'
  obtain ⟨hag4, her4⟩ := hag3.exec (RImpl.solo q K') (RImpl.solo_in Set.univ (Set.mem_univ q) K')
  have hD4q : (A.exec D3 (RImpl.solo q K')).1.ps q = .idle := by
    rcases RImpl.PSt.erase_eq_iff.1 (hag4.ps q (Set.mem_univ q)) with ⟨h1, -⟩ | ⟨_, _, _, _, _, -, h2⟩
    · exact h1
    · rw [hK'] at h2; cases h2
  obtain ⟨yr', hyr'⟩ := A.solo_hist q K' D3 m o_q false _ hD3q hD4q
  have hyy : yr' = yr := by
    have := her4; rw [hyr, hyr'] at this; simpa [HEv.erase] using this
  subst hyy
  have exE := A.exec_append_eq exE1
    (show A.exec E3 (RImpl.solo q K') = (_, [.res (m + 1) yr' false]) from Prod.ext rfl hyr)
  have exD := A.exec_append_eq exD1
    (show A.exec D3 (RImpl.solo q K') = (_, [.res m yr' false]) from Prod.ext rfl hyr')
  obtain ⟨y0, rfl⟩ : ∃ y0, yr' = some y0 := by
    cases yr' with
    | some y0 => exact ⟨y0, rfl⟩
    | none => exact absurd (by rw [exE]; simp) ((hcor _).2 (m + 1))
  /- The linearizations of the two executions. -/
  have dlin_of : ∀ {es : List (Ev P O.Op)} {C : A.Cfg} {h : List (HEv P O.Op O.Resp)},
      A.exec A.init es = (C, h) → ∃ L, DLin O h O.init L := by
    intro es C h hex; obtain ⟨L, hL⟩ := (hcor es).1; rw [hex] at hL; exact ⟨L, hL⟩
  have uniq_of : ∀ {es : List (Ev P O.Op)} {C : A.Cfg} {h : List (HEv P O.Op O.Resp)},
      A.exec A.init es = (C, h) →
      ∀ a p o p' o', HEv.inv a p o ∈ h → HEv.inv a p' o' ∈ h → o = o' := by
    intro es C h hex a p o p' o' h1 h2
    have := hU es a p o p' o'; rw [hex] at this; exact this h1 h2
  obtain ⟨ρ, rsγ', rfl⟩ : ∃ ρ rsγ', rsγ = ρ :: rsγ' := by
    cases rsγ with
    | nil => simp at hlenγ
    | cons ρ rsγ' => exact ⟨ρ, rsγ', rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenγ
  -- world `E`
  obtain ⟨LE, hLE⟩ := dlin_of exE
  have hEres := lin_E (H2 := H₁ ++ ([(p, op)] ++ ((r, o_r) :: E)))
    (rs := rsα ++ ([r0'] ++ ρ :: rsγ')) (by simp [hlenα, hlenγ]) (m := m)
    (by rw [hm', hcntα]; simp; omega) (p := p) (q := q) (op := op) (o_q := o_q) (x := xr')
    (y0 := y0) (by
      rw [seqHist_append _ _ _ _ hlenα, seqHist_append _ _ _ _ rfl]
      simp [seqHist, ← hcntα]) (uniq_of exE) hLE
  obtain ⟨hrsE, hyE⟩ := hEres
  have hρ : ρ = respAfter O (H₁ ++ [(p, op)]) o_r := by
    rw [specResps_append] at hrsE
    obtain ⟨-, h2⟩ := List.append_inj hrsE (by rw [hlenα, length_specResps])
    simp [specResps] at h2
    rw [h2.2.1]
    simp [respAfter, stateAfter, ObjSpec.runOps_append]
  -- world `D`
  obtain ⟨LD, hLD⟩ := dlin_of exD
  have hDres := lin_D (H₁ := H₁) (E := E) hlenα hlenγ (n1 := n1) (m := m) hcntα hm'
    (p := p) (q := q) (r := r) (op := op) (o_r := o_r) (o_q := o_q) (ρ := ρ)
    (by rw [hρ]; exact hpert1) (x := xr') (y0 := y0) (by simp) (uniq_of exD) hLD
  apply hpert2
  rw [← hDres.2, hyE hDres.1]
  simp

/-- **Theorem 2** for a doubly-perturbing object: some operation needs auxiliary state. -/
theorem theorem2_exists [DecidableEq P] (A : RImpl O P) (hDP : DoublyPerturbing O P)
    (hwof : A.WeakOF) (hcor : A.DurLinDet) : ∃ p o v, A.aux p o v ≠ v := by
  obtain ⟨p, op, hw⟩ := hDP
  obtain ⟨v, hv⟩ := theorem2 A hw hwof hcor
  exact ⟨p, op, v, hv⟩

/-! ### Instances (Lemmas 3, 5–8 + Theorem 2) -/

section Instances

variable [DecidableEq P] {p q : P}

/-- Read/write registers need auxiliary state. -/
theorem register_needs_aux {V : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) (hpq : q ≠ p)
    (A : RImpl (register V v₀) P) (hwof : A.WeakOF) (hcor : A.DurLinDet) :
    ∃ p o v, A.aux p o v ≠ v :=
  theorem2_exists A (register_doublyPerturbing v₀ v₁ hv p q hpq) hwof hcor

/-- CAS objects need auxiliary state. -/
theorem cas_needs_aux {V : Type} [DecidableEq V] {v₀ v₁ : V} (hv : v₀ ≠ v₁) (hpq : q ≠ p)
    (A : RImpl (casRC V v₀) P) (hwof : A.WeakOF) (hcor : A.DurLinDet) :
    ∃ p o v, A.aux p o v ≠ v :=
  theorem2_exists A (casRC_doublyPerturbing v₀ v₁ hv p q hpq) hwof hcor

/-- Counters need auxiliary state. -/
theorem counter_needs_aux (hpq : q ≠ p) (A : RImpl counter P) (hwof : A.WeakOF)
    (hcor : A.DurLinDet) : ∃ p o v, A.aux p o v ≠ v :=
  theorem2_exists A (counter_doublyPerturbing p q hpq) hwof hcor

/-- Fetch-and-add objects need auxiliary state. -/
theorem faa_needs_aux (hpq : q ≠ p) (A : RImpl faaObj P) (hwof : A.WeakOF)
    (hcor : A.DurLinDet) : ∃ p o v, A.aux p o v ≠ v :=
  theorem2_exists A (faa_doublyPerturbing p q hpq) hwof hcor

/-- FIFO queues need auxiliary state. -/
theorem queue_needs_aux {V : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) (hpq : q ≠ p)
    (A : RImpl (queueObj V) P) (hwof : A.WeakOF) (hcor : A.DurLinDet) :
    ∃ p o v, A.aux p o v ≠ v :=
  theorem2_exists A (queue_doublyPerturbing v₀ v₁ hv p q hpq) hwof hcor

end Instances

end Papers.PODC2020.DetectableSpace
