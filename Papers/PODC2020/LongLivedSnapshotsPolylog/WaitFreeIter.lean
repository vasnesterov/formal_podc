import Papers.PODC2020.LongLivedSnapshotsPolylog.WaitFreeSeg

/-!
# Wait-freedom of Algorithm 1: the iteration invariant

`MainInv`: an invariant of every execution that records, for a process `i` in iteration `c > X`
of a `CompScan` (i.e. after its first collect `h₀`, line 24), a configuration `C₀` reached after
the first collect such that

* the high-order bits `Q = ⌊MR_left / m⌋ + ⌊MR_right / m⌋` grew by at least `c - X - 1` from
  `C₀` (each unsuccessful iteration increases `Q`: proof of Lemma 3.4), and
* at a second collect (line 26), a configuration `C₁` reached before the collect started, with
  `Q(C₁) ≥ Q(C₀) + (c - X)`, and the entries read so far are at least as recent as `C₁`.
-/

namespace Podc.LongLivedSnapshotsPolylog.WaitFree

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp)

variable {n m X : ℕ}

/-- The sum of the high-order bits of `MR_left` and `MR_right`. -/
def Q (m : ℕ) (C : Cfg n) : ℕ := mrL C / m + mrR C / m

/-- Progress of the current iteration: the values read so far are at most the current register
values and their high-order bits sum to at least `q`. -/
def Prog (m : ℕ) (C : Cfg n) (q : ℕ) : PC n → Prop
  | .rdR1 _ => q ≤ Q m C
  | .rdL _ r1 => r1 ≤ mrR C ∧ q ≤ r1 / m + mrL C / m
  | .rdR2 _ r1 l => r1 ≤ mrR C ∧ l ≤ mrL C ∧ q ≤ r1 / m + l / m
  | .upL _ l r2 => l ≤ mrL C ∧ r2 ≤ mrR C ∧ q ≤ l / m + r2 / m
  | .upR _ l r2 => l ≤ mrL C ∧ r2 ≤ mrR C ∧ q ≤ l / m + r2 / m
  | .scanMA _ l r2 => l ≤ mrL C ∧ r2 ≤ mrR C ∧ q ≤ l / m + r2 / m
  | .chkL _ l r2 _ => l ≤ mrL C ∧ r2 ≤ mrR C ∧ q ≤ l / m + r2 / m
  | .chkR _ l r2 _ => l ≤ mrL C ∧ r2 ≤ mrR C ∧ q ≤ l / m + r2 / m
  | _ => True

/-- The invariant of an iteration `cs.c > X` (outside the collects). -/
def Main (m X : ℕ) (α : List (Lbl n)) (C : Cfg n) (cs : CS n) (pc : PC n) : Prop :=
  X < cs.c → ∃ h0, cs.h0 = some h0 ∧ ∃ β₀ C₀, β₀ <+: α ∧ (alg1 n m X).run β₀ = some C₀ ∧
    (∀ k, (h0 k).1 ≤ tsOf C₀ k) ∧ Prog m C (Q m C₀ + (cs.c - X - 1)) pc

/-- The invariant of one process. -/
def PInv (m X : ℕ) (α : List (Lbl n)) (C : Cfg n) : PC n → Prop
  | .idle => True
  | .wm _ _ => True
  | .retV _ => True
  | .rdR1 cs => Main m X α C cs (.rdR1 cs)
  | .rdL cs r1 => Main m X α C cs (.rdL cs r1)
  | .rdR2 cs r1 l => Main m X α C cs (.rdR2 cs r1 l)
  | .upL cs l r2 => Main m X α C cs (.upL cs l r2)
  | .upR cs l r2 => Main m X α C cs (.upR cs l r2)
  | .scanMA cs l r2 => Main m X α C cs (.scanMA cs l r2)
  | .chkL cs l r2 v => Main m X α C cs (.chkL cs l r2 v)
  | .chkR cs l r2 v => Main m X α C cs (.chkR cs l r2 v)
  | .wH cs v => Main m X α C cs (.wH cs v)
  | .col cs true k acc => cs.c = X ∧ ∀ k' : Fin n, k' < k → (acc k').1 ≤ tsOf C k'
  | .col cs false k acc => X < cs.c ∧ ∃ h0, cs.h0 = some h0 ∧ ∃ β₀ C₀ β₁ C₁, β₀ <+: β₁ ∧ β₁ <+: α ∧
      (alg1 n m X).run β₀ = some C₀ ∧ (alg1 n m X).run β₁ = some C₁ ∧
      (∀ k, (h0 k).1 ≤ tsOf C₀ k) ∧ Q m C₀ + (cs.c - X) ≤ Q m C₁ ∧
      ∀ k' : Fin n, k' < k → tsOf C₁ k' ≤ (acc k').1

/-- The iteration invariant of Algorithm 1. -/
def MainInv (m X : ℕ) (α : List (Lbl n)) (C : Cfg n) : Prop := ∀ i, PInv m X α C (C.loc i).pc

lemma Q_def (C : Cfg n) : Q m C = mrL C / m + mrR C / m := rfl

lemma Q_loc (C : Cfg n) (L : Fin n → Loc n) (P : Fin n → Option MAOp) :
    Q m (⟨L, P, C.mem⟩ : Cfg n) = Q m C := rfl

lemma Q_mono {C C' : Cfg n} (h1 : mrL C ≤ mrL C') (h2 : mrR C ≤ mrR C') : Q m C ≤ Q m C' :=
  Nat.add_le_add (Nat.div_le_div_right h1) (Nat.div_le_div_right h2)

lemma prog_mono {C C' : Cfg n} {q : ℕ} {pc : PC n} (h1 : mrL C ≤ mrL C') (h2 : mrR C ≤ mrR C')
    (h : Prog m C q pc) : Prog m C' q pc := by
  have hQ := Q_mono (m := m) h1 h2
  have hL := Nat.div_le_div_right (c := m) h1
  cases pc <;> simp only [Prog] at h ⊢ <;> omega

lemma main_mono {α α' : List (Lbl n)} {C C' : Cfg n} {cs : CS n} {pc : PC n} (hα : α <+: α')
    (h1 : mrL C ≤ mrL C') (h2 : mrR C ≤ mrR C') (h : Main m X α C cs pc) :
    Main m X α' C' cs pc := by
  intro hc
  obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
  exact ⟨h0, hh0, β₀, C₀, hβ.trans hα, hr, hts, prog_mono h1 h2 hp⟩

lemma pinv_mono {α α' : List (Lbl n)} {C C' : Cfg n} {pc : PC n} (hα : α <+: α')
    (h1 : mrL C ≤ mrL C') (h2 : mrR C ≤ mrR C') (h3 : ∀ k, tsOf C k ≤ tsOf C' k)
    (h : PInv m X α C pc) : PInv m X α' C' pc := by
  cases pc with
  | col cs first k acc =>
    cases first with
    | true =>
      simp only [PInv] at h ⊢
      exact ⟨h.1, fun k' hk' => (h.2 k' hk').trans (h3 k')⟩
    | false =>
      simp only [PInv] at h ⊢
      obtain ⟨hc, h0, hh0, β₀, C₀, β₁, C₁, hp, hp', r0, r1, hts, hQ, hacc⟩ := h
      exact ⟨hc, h0, hh0, β₀, C₀, β₁, C₁, hp, hp'.trans hα, r0, r1, hts, hQ, hacc⟩
  | idle => trivial
  | wm => trivial
  | retV => trivial
  | _ => simp only [PInv] at h ⊢; exact main_mono hα h1 h2 h

/-- After an unsuccessful iteration `c` (in which `Q` grew), the invariant holds at the next
state (lines 23–29). -/
lemma pinv_afterFail {α' : List (Lbl n)} {C' : Cfg n} {cs : CS n} {i : Fin n}
    (hα' : (alg1 n m X).run α' = some C')
    (hF : X < cs.c → ∃ h0, cs.h0 = some h0 ∧ ∃ β₀ C₀, β₀ <+: α' ∧
      (alg1 n m X).run β₀ = some C₀ ∧ (∀ k, (h0 k).1 ≤ tsOf C₀ k) ∧
      Q m C₀ + (cs.c - X) ≤ Q m C') :
    PInv m X α' C' (afterFail X i cs) := by
  unfold afterFail
  split_ifs with h1 h2
  · exact ⟨h1, fun k' hk' => absurd (Fin.lt_def.1 hk') (Nat.not_lt_zero _)⟩
  · obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hQ⟩ := hF h2.1
    exact ⟨h2.1, h0, hh0, β₀, C₀, α', C', hβ, List.prefix_refl _, hr, hα', hts, hQ,
      fun k' hk' => absurd (Fin.lt_def.1 hk') (Nat.not_lt_zero _)⟩
  · simp only [PInv, Main, Prog]
    intro hc
    have hc' : X < cs.c := by omega
    obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hQ⟩ := hF hc'
    exact ⟨h0, hh0, β₀, C₀, hβ, hr, hts, by omega⟩

/-- The iteration invariant is preserved by the steps of the process itself. -/
lemma pinv_tau {α : List (Lbl n)} {C C' : Cfg n} {i : Fin n} (hB : Basic C)
    (hα : (alg1 n m X).run α = some C) (hs : (alg1 n m X).step C (.tau i) = some C')
    (h : PInv m X α C (C.loc i).pc) : PInv m X (α ++ [.tau i]) C' (C'.loc i).pc := by
  have hα' : (alg1 n m X).run (α ++ [.tau i]) = some C' := by
    rw [Impl.run_concat, hα, Option.bind_some, hs]
  have hpre : α <+: α ++ [.tau i] := List.prefix_append _ _
  have hmono := run_mono_of_prefix hpre hα hα'
  rcases hpc : (C.loc i).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
    ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
    ⟨cs, first, k, acc⟩ | r
  all_goals rw [hpc] at h
  all_goals simp [Impl.step, act, hpc] at hs
  all_goals obtain ⟨-, rfl⟩ := hs
  all_goals simp only [Function.update_self]
  all_goals have e1 : C.mem .mrR = mrR C := rfl
  all_goals have e2 : C.mem .mrL = mrL C := rfl
  all_goals try simp only [e1, e2] at hα' hmono ⊢
  all_goals obtain ⟨hmL, hmR, -⟩ := hmono
  all_goals have dL := Nat.div_le_div_right (c := m) hmL
  all_goals have dR := Nat.div_le_div_right (c := m) hmR
  all_goals have eQ : Q m C = mrL C / m + mrR C / m := rfl
  -- `wm`
  · simp [PInv, Main, csInit]
  · simp [PInv, Main, csInit]
  -- line 10
  · simp only [PInv] at h ⊢
    intro hc
    obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
    refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
    simp only [Prog] at hp ⊢
    omega
  -- line 11
  · simp only [PInv] at h ⊢
    intro hc
    obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
    refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
    simp only [Prog] at hp ⊢
    omega
  -- line 12, test of line 13
  · simp only [PInv] at h
    split_ifs at * with ht
    · simp only [PInv]
      intro hc
      obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
      refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
      simp only [Prog] at hp ⊢
      omega
    · refine pinv_afterFail hα' fun hc => ?_
      obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
      refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
      simp only [Prog] at hp
      have := Nat.div_le_div_right (c := m) hp.1
      have : r1 / m < mrR C / m := lt_of_le_of_ne this ht
      have := Nat.div_le_div_right (c := m) hp.2.1
      simp only [Q_def] at hp ⊢
      omega
  · simp only [PInv] at h ⊢
    intro hc
    obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
    refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
    simp only [Prog] at hp ⊢
    omega
  · simp only [PInv] at h ⊢
    intro hc
    obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
    refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
    simp only [Prog] at hp ⊢
    omega
  · simp only [PInv] at h ⊢
    intro hc
    obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
    refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
    simp only [Prog] at hp ⊢
    omega
  · simp only [PInv] at h
    split_ifs at * with ht
    · simp only [PInv]
      intro hc
      obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
      refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
      simp only [Prog] at hp ⊢
      try omega
    · refine pinv_afterFail hα' fun hc => ?_
      obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
      refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
      simp only [Prog] at hp
      have := Nat.div_le_div_right (c := m) hp.1
      have := Nat.div_le_div_right (c := m) hp.2.1
      have : l / m < mrL C / m := lt_of_le_of_ne (Nat.div_le_div_right (c := m) hp.1) (Ne.symm ht)
      simp only [Q_def] at hp ⊢
      omega
  · simp only [PInv] at h
    split_ifs at * with ht
    · simp only [PInv]
      intro hc
      obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
      refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
      simp only [Prog] at hp ⊢
      try omega
    · refine pinv_afterFail hα' fun hc => ?_
      obtain ⟨h0, hh0, β₀, C₀, hβ, hr, hts, hp⟩ := h hc
      refine ⟨h0, hh0, β₀, C₀, hβ.trans hpre, hr, hts, ?_⟩
      simp only [Prog] at hp
      have := Nat.div_le_div_right (c := m) hp.1
      have := Nat.div_le_div_right (c := m) hp.2.1
      have : r2 / m < mrR C / m := lt_of_le_of_ne (Nat.div_le_div_right (c := m) hp.2.1) (Ne.symm ht)
      simp only [Q_def] at hp ⊢
      omega
  -- line 21
  · unfold retOf; split_ifs <;> trivial
  -- the collects
  · have hread : (C.mem (.help k)).1 = tsOf C k := hB.1 k
    have hle : ¬ k.1 + 1 < n → ∀ k' : Fin n, k' ≠ k → k' < k := fun hk k' hne => by
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact h'
      · exfalso; simp only [Fin.lt_def] at h'; omega
    cases first
    · simp only [PInv] at h
      obtain ⟨hc, h0, hh0, β₀, C₀, β₁, C₁, hp, hp', r0, r1, hts, hQ, hacc⟩ := h
      have hm1 := run_mono_of_prefix hp' r1 hα
      by_cases hk : k.1 + 1 < n
      · simp only [hk, ↓reduceDIte, PInv]
        refine ⟨hc, h0, hh0, β₀, C₀, β₁, C₁, hp, hp'.trans hpre, r0, r1, hts, hQ, fun k' hk' => ?_⟩
        rcases fin_lt_succ hk' with hk' | rfl
        · rw [Function.update_of_ne (ne_of_lt hk')]; exact hacc k' hk'
        · rw [Function.update_self, hread]; exact hm1.2.2 k'
      · simp only [hk, ↓reduceDIte, afterCollect, Bool.false_eq_true, ↓reduceIte]
        split
        · unfold retOf; split_ifs <;> trivial
        · simp only [PInv, Main, Prog]
          intro _
          have hQ1 := Q_mono (m := m) hm1.1 hm1.2.1
          refine ⟨h0, hh0, β₀, C₀, hp.trans (hp'.trans hpre), r0, hts, ?_⟩
          rw [Q_loc C]; omega
    · simp only [PInv] at h
      obtain ⟨hc, hacc⟩ := h
      have hacc' : ∀ k' : Fin n, k' < k ∨ k' = k →
          (Function.update acc k (C.mem (Obj.help k)) k').1 ≤ tsOf C k' := by
        rintro k' (hk' | rfl)
        · rw [Function.update_of_ne (ne_of_lt hk')]; exact hacc k' hk'
        · rw [Function.update_self, hread]
      by_cases hk : k.1 + 1 < n
      · simp only [hk, ↓reduceDIte, PInv]
        exact ⟨hc, fun k' hk' => (hacc' k' (fin_lt_succ hk')).trans (tsOf_le_upd _ _ _ _ _ _)⟩
      · simp only [hk, ↓reduceDIte, afterCollect, ↓reduceIte, PInv, Main, Prog]
        intro _
        refine ⟨_, rfl, _, _, List.prefix_refl _, hα', fun k' => ?_, by simp only [Q_def, mrL, mrR]; omega⟩
        refine (hacc' k' ?_).trans (tsOf_le_upd _ _ _ _ _ _)
        by_cases h' : k' = k
        · exact Or.inr h'
        · exact Or.inl (hle hk k' h')

/-- Response steps lead to `idle`. -/
lemma act_ret_idle {p : Fin n} {l l' : Loc n} {r : ℕ × ℕ}
    (h : (alg1 n m X).act p l = .ret r l') : l'.pc = .idle := by
  simp only [act] at h
  split at h <;> first | (split at h <;> cases h) | (cases h <;> first | assumption | rfl)

/-- `MainInv` is an invariant of all executions. -/
theorem mainInv_run {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) :
    MainInv m X α C := by
  refine Impl.run_induction (I := alg1 n m X) (Q := fun α C => MainInv m X α C)
    (fun i => trivial) (fun α C x C' hα ih hs i => ?_) h
  by_cases hx : x.proc = i
  · cases x with
    | tau p =>
      simp only [Label.proc] at hx; subst hx
      exact pinv_tau (basic_run hα) hα hs (ih p)
    | inv p o =>
      simp only [Label.proc] at hx; subst hx
      obtain ⟨-, -, -, hl, -⟩ := Impl.step_inv hs
      rw [hl, Function.update_self]
      cases o <;> simp [PInv, Main, csInit]
    | ret p r =>
      simp only [Label.proc] at hx; subst hx
      obtain ⟨-, -, -, l, hact, hl⟩ := Impl.step_ret hs
      rw [hl, Function.update_self, act_ret_idle hact]
      trivial
  · obtain ⟨h1, h2, h3⟩ := step_mono hs
    rw [(Impl.step_other hs hx).1]
    exact pinv_mono (List.prefix_append _ _) h1 h2 h3 (ih i)

end Podc.LongLivedSnapshotsPolylog.WaitFree
