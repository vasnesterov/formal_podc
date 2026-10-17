import Papers.PODC2015.CrashConsensusDigraph.WA

/-!
# Algorithm WA: global invariant, ε-agreement and validity

* `avg_bounds` — averaging a set `S ⊆ [a, b]` of at most `n` reals containing `c` gives a value in
  `[a + (c − a)/n, b − (b − c)/n]` (the averaging step of the analysis "similar to [13, 5, 1]"
  that the paper omits).
* `contraction` — if every node satisfies the local invariant `LI` (each completed phase value
  is the average of the previous-phase values of a heard set satisfying Condition WAIT) and the
  graph satisfies 2-reach, then the phase-`p` values lie in an interval of width
  `(1 − 1/n)^p · (hi − lo)` inside the input range `[lo, hi]`. Two heard sets intersect by
  **Lemma 1** (`lemma1`, from 2-reach), which gives the common value `c` above.
* `WInv` — the global invariant of executions (local invariants, genuine messages in channels,
  decisions are final phase values, and the flooding invariant used for liveness); `winv_runC`.
* `wa_agreement`, `wa_validity`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## Averaging -/

theorem avg_bounds {S : Finset ℝ} {a b c : ℝ} {n : ℕ} (hS : ∀ y ∈ S, a ≤ y ∧ y ≤ b) (hc : c ∈ S)
    (hn : S.card ≤ n) : a + (c - a) / n ≤ avg S ∧ avg S ≤ b - (b - c) / n := by
  have hk1 : 1 ≤ S.card := card_pos.mpr ⟨c, hc⟩
  have hk : (0 : ℝ) < S.card := by exact_mod_cast hk1
  have hkn : (S.card : ℝ) ≤ n := by exact_mod_cast hn
  have hsum : ∑ y ∈ S, y = c + ∑ y ∈ S.erase c, y := (Finset.add_sum_erase S (fun y => y) hc).symm
  have hcard : ((S.erase c).card : ℝ) = S.card - 1 := by
    rw [card_erase_of_mem hc, Nat.cast_sub hk1]; simp
  have hlow : ((S.card : ℝ) - 1) * a ≤ ∑ y ∈ S.erase c, y := by
    have := Finset.card_nsmul_le_sum (S.erase c) (fun y => y) a
      (fun y hy => (hS y (mem_of_mem_erase hy)).1)
    rw [nsmul_eq_mul, hcard] at this; exact this
  have hup : ∑ y ∈ S.erase c, y ≤ ((S.card : ℝ) - 1) * b := by
    have := Finset.sum_le_card_nsmul (S.erase c) (fun y => y) b
      (fun y hy => (hS y (mem_of_mem_erase hy)).2)
    rw [nsmul_eq_mul, hcard] at this; exact this
  have hca : 0 ≤ c - a := by linarith [(hS c hc).1]
  have hbc : 0 ≤ b - c := by linarith [(hS c hc).2]
  have h1 : (c - a) / n ≤ (c - a) / S.card := div_le_div_of_nonneg_left hca hk hkn
  have h2 : (b - c) / n ≤ (b - c) / S.card := div_le_div_of_nonneg_left hbc hk hkn
  unfold avg
  rw [hsum]
  constructor
  · have : a + (c - a) / S.card ≤ (c + ∑ y ∈ S.erase c, y) / S.card := by
      rw [le_div_iff₀ hk, add_mul, div_mul_cancel₀ _ hk.ne']
      nlinarith
    linarith
  · have : (c + ∑ y ∈ S.erase c, y) / S.card ≤ b - (b - c) / S.card := by
      rw [div_le_iff₀ hk, sub_mul, div_mul_cancel₀ _ hk.ne']
      nlinarith
    linarith

/-! ## Contraction -/

variable {G : Digraph V} {f pend : ℕ}

/-- **Convergence of the phase values.** -/
theorem contraction (hG : TwoReach G f) {g : V → WS V} {inp : V → ℝ}
    (hLI : ∀ i, LI G f pend g inp i) {lo hi : ℝ} (hlohi : lo ≤ hi) (hlo : ∀ w, lo ≤ inp w)
    (hhi : ∀ w, inp w ≤ hi) :
    ∀ p, ∃ a b, lo ≤ a ∧ a ≤ b ∧ b ≤ hi ∧
      b - a ≤ (1 - 1 / (Fintype.card V : ℝ)) ^ p * (hi - lo) ∧
      ∀ i, p < (g i).ph → a ≤ (g i).val p ∧ (g i).val p ≤ b := by
  classical
  set n := Fintype.card V with hn
  have hq : 0 ≤ 1 - 1 / (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
  intro p
  induction p with
  | zero =>
    refine ⟨lo, hi, le_rfl, hlohi, le_rfl, by simp, fun i _ => ?_⟩
    rw [(hLI i).val0]; exact ⟨hlo i, hhi i⟩
  | succ p ih =>
    obtain ⟨a, b, hla, hab, hbh, hw, hval⟩ := ih
    -- the heard sets of completed phase `p + 1`
    have hH : ∀ i, p + 1 < (g i).ph → ∃ H : Finset V, Wait G f i H ∧ (∀ j ∈ H, p < (g j).ph) ∧
        (g i).val (p + 1) = avg (H.image fun j => (g j).val p) := by
      intro i hi
      obtain ⟨H, hW, hHp, hv⟩ := (hLI i).done (p + 1) (by omega) hi
      exact ⟨H, hW, fun j hj => by simpa using hHp j hj, by simpa using hv⟩
    have hS : ∀ H : Finset V, (∀ j ∈ H, p < (g j).ph) →
        ∀ y ∈ H.image (fun j => (g j).val p), a ≤ y ∧ y ≤ b := by
      intro H hHp y hy
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
      exact hval j (hHp j hj)
    have hcardS : ∀ H : Finset V, (H.image fun j => (g j).val p).card ≤ n :=
      fun H => card_image_le.trans (card_le_univ H)
    have hin : ∀ i, p + 1 < (g i).ph → a ≤ (g i).val (p + 1) ∧ (g i).val (p + 1) ≤ b := by
      intro i hi
      obtain ⟨H, hW, hHp, hv⟩ := hH i hi
      have hc : (g i).val p ∈ H.image (fun j => (g j).val p) := mem_image_of_mem _ hW.self_mem
      have hci := hval i (hHp i hW.self_mem)
      obtain ⟨h1, h2⟩ := avg_bounds (hS H hHp) hc (hcardS H)
      have : 0 ≤ ((g i).val p - a) / n := div_nonneg (by linarith) (Nat.cast_nonneg _)
      have : 0 ≤ (b - (g i).val p) / n := div_nonneg (by linarith) (Nat.cast_nonneg _)
      rw [hv]; constructor <;> linarith
    have hpair : ∀ i j, p + 1 < (g i).ph → p + 1 < (g j).ph →
        (g j).val (p + 1) - (g i).val (p + 1) ≤ (1 - 1 / (n : ℝ)) * (b - a) := by
      intro i j hi hj
      obtain ⟨Hi, hWi, hHi, hvi⟩ := hH i hi
      obtain ⟨Hj, hWj, hHj, hvj⟩ := hH j hj
      obtain ⟨Fi, hiF, hFi, hRi⟩ := hWi
      obtain ⟨Fj, hjF, hFj, hRj⟩ := hWj
      obtain ⟨w, hwi, hwj⟩ := hG Fj Fi j i hFj hFi hjF hiF
      have hwHi := hRi w hwi
      have hwHj := hRj w hwj
      obtain ⟨li, -⟩ := avg_bounds (hS Hi hHi) (mem_image_of_mem (fun j => (g j).val p) hwHi)
        (hcardS Hi)
      obtain ⟨-, uj⟩ := avg_bounds (hS Hj hHj) (mem_image_of_mem (fun j => (g j).val p) hwHj)
        (hcardS Hj)
      rw [hvi, hvj]
      have : (1 - 1 / (n : ℝ)) * (b - a) = (b - a) - ((b - (g w).val p) / n + ((g w).val p - a) / n) := by
        ring
      rw [this]
      linarith
    set D := univ.filter fun i => p + 1 < (g i).ph
    by_cases hD : D.Nonempty
    · obtain ⟨imin, himin, hmin⟩ := exists_min_image D (fun i => (g i).val (p + 1)) hD
      obtain ⟨imax, himax, hmax⟩ := exists_max_image D (fun i => (g i).val (p + 1)) hD
      have hmn : p + 1 < (g imin).ph := (mem_filter.mp himin).2
      have hmx : p + 1 < (g imax).ph := (mem_filter.mp himax).2
      refine ⟨(g imin).val (p + 1), (g imax).val (p + 1), by linarith [(hin imin hmn).1],
        hmin imax himax, by linarith [(hin imax hmx).2], ?_, fun i hi => ?_⟩
      · have := hpair imin imax hmn hmx
        rw [pow_succ]
        have : (1 - 1 / (n : ℝ)) * (b - a) ≤ (1 - 1 / (n : ℝ)) * ((1 - 1 / (n : ℝ)) ^ p * (hi - lo)) :=
          mul_le_mul_of_nonneg_left hw hq
        nlinarith
      · have hiD : i ∈ D := mem_filter.mpr ⟨mem_univ _, hi⟩
        exact ⟨hmin i hiD, hmax i hiD⟩
    · refine ⟨a, a, hla, le_rfl, by linarith, ?_, fun i hi => ?_⟩
      · simp only [sub_self]
        exact mul_nonneg (pow_nonneg hq _) (by linarith)
      · exact absurd ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩ hD

/-! ## The global invariant -/

variable [DecidableRel G.Adj]

/-- The global invariant of the executions of Algorithm WA (with crashed set `B`). -/
structure WInv (G : Digraph V) [DecidableRel G.Adj] (f pend : ℕ) (inp : V → ℝ) (B : Finset V)
    (C : Config V (ℝ × V × ℕ) (WS V)) : Prop where
  li : ∀ i, LI G f pend C.st inp i
  closed : ∀ i, Closed G f pend i (C.st i)
  chan_gen : ∀ x y m, m ∈ C.chan x y → Genuine C.st m
  dec_some : ∀ i z, C.dec i = some z → pend < (C.st i).ph ∧ (C.st i).val pend = z
  dec_none : ∀ i, pend < (C.st i).ph → C.dec i ≠ none
  flood : ∀ x y m, G.Adj x y → x ≠ y → x ∉ B → y ∉ B → m ∈ (C.st x).seen →
    m ∈ (C.st y).seen ∨ m ∈ C.chan x y

theorem WInv.anti {inp : V → ℝ} {B B' : Finset V} {C : Config V (ℝ × V × ℕ) (WS V)}
    (h : WInv G f pend inp B C) (hB : B ⊆ B') : WInv G f pend inp B' C :=
  { h with flood := fun x y m e hxy hx hy hm =>
      h.flood x y m e hxy (fun h' => hx (hB h')) (fun h' => hy (hB h')) hm }

theorem mem_sendTo {B : Finset V} {y b : V} {outs : List (V × (ℝ × V × ℕ))} {m : ℝ × V × ℕ} :
    m ∈ sendTo G B y outs b ↔ (b ∉ B ∧ G.Adj y b ∧ y ≠ b) ∧ (b, m) ∈ outs := by
  unfold sendTo
  split_ifs with h
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨b', m'⟩, ⟨hm, rfl⟩, rfl⟩; exact ⟨h, hm⟩
    · rintro ⟨-, hm⟩; exact ⟨(b, m), ⟨hm, rfl⟩, rfl⟩
  · simp [h]

theorem dec_of_out {x : V} {s : WS V} {z : ℝ} (h : (wa G f pend).out x s = some z) :
    pend < s.ph ∧ s.val pend = z := by
  rw [wa_out] at h
  split_ifs at h with h'
  exact ⟨h', Option.some_injective _ h⟩

theorem winv_init (inp : V → ℝ) (B : Finset V) : WInv G f pend inp B (init (wa G f pend) G B inp) := by
  have hst : ∀ x, (init (wa G f pend) G B inp).st x = ((wa G f pend).start x (inp x)).1 :=
    fun _ => rfl
  have hs := fun x => start_spec (G := G) (f := f) (pend := pend) (g := (init (wa G f pend) G B inp).st)
    (inp := inp) (x := x) (hst x)
  refine ⟨fun i => (hs i).1, fun i => (hs i).2.1, ?_, ?_, ?_, ?_⟩
  · intro x y m hm
    simp only [init] at hm
    split_ifs at hm with hx
    · simp at hm
    · exact (hs x).2.2.1 (y, m) (mem_sendTo.mp hm).2
  · intro i z hz
    exact dec_of_out (G := G) (f := f) (x := i) hz
  · intro i hi
    have hi' : pend < ((wa G f pend).start i (inp i)).1.ph := hi
    show (wa G f pend).out i _ ≠ none
    rw [wa_out]; simp [hi']
  · intro x y m e hxy hx hy hm
    right
    simp only [init, hx, ↓reduceIte]
    exact mem_sendTo.mpr ⟨⟨hy, e, hxy⟩, (hs x).2.2.2 m hm y⟩

theorem winv_process {inp : V → ℝ} {B : Finset V} {C : Config V (ℝ × V × ℕ) (WS V)}
    (hI : WInv G f pend inp B C) {x y : V} {m : ℝ × V × ℕ} {rest : List (ℝ × V × ℕ)}
    (hc : C.chan x y = m :: rest) :
    WInv G f pend inp B (process (wa G f pend) G B (C.pop x y rest) y x m) ∧
      (∀ j, Ext (C.st j) ((process (wa G f pend) G B (C.pop x y rest) y x m).st j)) ∧
      m ∈ ((process (wa G f pend) G B (C.pop x y rest) y x m).st y).seen := by
  have hm : Genuine C.st m := hI.chan_gen x y m (by rw [hc]; exact List.mem_cons_self)
  obtain ⟨e, l, gen, new, cl, hmem⟩ := recv_spec (x := x) (hI.li y) (hI.closed y) hm
  set r := (wa G f pend).recv y (C.st y) x m with hr
  have hst : (process (wa G f pend) G B (C.pop x y rest) y x m).st = Function.update C.st y r.1 := rfl
  have hchan : ∀ a b, (process (wa G f pend) G B (C.pop x y rest) y x m).chan a b =
      if a = y then (if a = x ∧ b = y then rest else C.chan a b) ++ sendTo G B y r.2 b
      else (if a = x ∧ b = y then rest else C.chan a b) := fun _ _ => rfl
  have hdec : (process (wa G f pend) G B (C.pop x y rest) y x m).dec =
      Function.update C.dec y ((C.dec y).or ((wa G f pend).out y r.1)) := rfl
  have hext : ∀ j, Ext (C.st j) (Function.update C.st y r.1 j) := ext_update e
  have hchan_sub : ∀ a b m', m' ∈ (if a = x ∧ b = y then rest else C.chan a b) → m' ∈ C.chan a b := by
    intro a b m' h
    split_ifs at h with hab
    · obtain ⟨rfl, rfl⟩ := hab; rw [hc]; exact List.mem_cons_of_mem _ h
    · exact h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hst]; exact hext, by rw [hst]; simpa using hmem⟩
  · intro i
    rw [hst]
    by_cases hi : i = y
    · subst hi; exact l
    · exact (hI.li i).mono hext (Function.update_of_ne hi _ _)
  · intro i
    rw [hst]
    by_cases hi : i = y
    · subst hi; simpa using cl
    · rw [Function.update_of_ne hi]; exact hI.closed i
  · intro a b m' hm'
    rw [hchan] at hm'
    rw [hst]
    by_cases ha : a = y
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ha)] at hm'
      rcases List.mem_append.mp hm' with h | h
      · exact (hI.chan_gen a b m' (hchan_sub a b m' h)).mono hext
      · exact gen (b, m') (mem_sendTo.mp h).2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ha)] at hm'
      exact (hI.chan_gen a b m' (hchan_sub a b m' hm')).mono hext
  · intro i z hz
    rw [hdec] at hz
    rw [hst]
    by_cases hi : i = y
    · subst hi
      simp only [Function.update_self] at hz ⊢
      cases hd : C.dec i with
      | none => rw [hd] at hz; exact dec_of_out (by simpa using hz)
      | some z' =>
        rw [hd] at hz
        simp only [Option.some_or, Option.some.injEq] at hz
        subst hz
        obtain ⟨h1, h2⟩ := hI.dec_some i z' hd
        exact ⟨lt_of_lt_of_le h1 e.1, by rw [e.2.1 pend h1, h2]⟩
    · rw [Function.update_of_ne hi] at hz ⊢
      exact hI.dec_some i z hz
  · intro i hi
    rw [hdec]
    rw [hst] at hi
    by_cases hiy : i = y
    · subst hiy
      simp only [Function.update_self] at hi ⊢
      cases hd : C.dec i with
      | none => simp [wa_out, hi]
      | some z => simp
    · rw [Function.update_of_ne hiy] at hi ⊢
      exact hI.dec_none i hi
  · intro a b m' eab hab ha hb hm'
    rw [hst] at hm' ⊢
    by_cases hay : a = y
    · subst hay
      rw [hchan, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      simp only [Function.update_self] at hm'
      have hbne : b ≠ a := fun h => hab h.symm
      rw [Function.update_of_ne hbne]
      by_cases hold : m' ∈ (C.st a).seen
      · rcases hI.flood a b m' eab hab ha hb hold with h | h
        · left; exact h
        · right
          have : ¬ (a = x ∧ b = a) := fun h' => hbne h'.2
          rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
          exact List.mem_append_left _ h
      · right
        exact List.mem_append_right _ (mem_sendTo.mpr ⟨⟨hb, eab, hab⟩, new m' hm' hold b⟩)
    · rw [Function.update_of_ne hay] at hm'
      rcases hI.flood a b m' eab hab ha hb hm' with h | h
      · left; exact (hext b).2.2 h
      · rw [hchan, ite_eq_right_of_eq_false _ _ (eq_false hay)]
        by_cases hxy : a = x ∧ b = y
        · obtain ⟨rfl, rfl⟩ := hxy
          rw [hc] at h
          rcases List.mem_cons.mp h with h' | h'
          · left; subst h'; simpa using hmem
          · right; simp [h']
        · right; rw [ite_eq_right_of_eq_false _ _ (eq_false hxy)]; exact h

/-- One step preserves the invariant (for event sequences without Byzantine events). -/
theorem winv_step {inp : V → ℝ} {B : Finset V} {C : Config V (ℝ × V × ℕ) (WS V)}
    (hI : WInv G f pend inp B C) (e : Event V (ℝ × V × ℕ)) (he : ∀ x y m, e ≠ .byz x y m) :
    WInv G f pend inp B (step (wa G f pend) G B C e) ∧
      ∀ j, Ext (C.st j) ((step (wa G f pend) G B C e).st j) := by
  cases e with
  | skip => exact ⟨hI, fun j => Ext.refl _⟩
  | byz x y m => exact absurd rfl (he x y m)
  | deliver x y =>
    cases hc : C.chan x y with
    | nil =>
      have : step (wa G f pend) G B C (.deliver x y) = C := by simp only [step, hc]
      rw [this]; exact ⟨hI, fun j => Ext.refl _⟩
    | cons m rest =>
      by_cases hy : y ∈ B
      · have : step (wa G f pend) G B C (.deliver x y) = C := by simp only [step, hc, hy, ↓reduceIte]
        rw [this]; exact ⟨hI, fun j => Ext.refl _⟩
      · have : step (wa G f pend) G B C (.deliver x y) =
            process (wa G f pend) G B (C.pop x y rest) y x m := by
          simp only [step, hc, hy, ↓reduceIte]
        rw [this]
        obtain ⟨h1, h2, -⟩ := winv_process hI hc
        exact ⟨h1, h2⟩

/-- The invariant holds along every execution without Byzantine events. -/
theorem winv_runC (ct : V → Option ℕ) (inp : V → ℝ) (ev : ℕ → Event V (ℝ × V × ℕ))
    (hev : ∀ t x y m, ev t ≠ .byz x y m) (t : ℕ) :
    WInv G f pend inp (crashedAt ct t) (runC (wa G f pend) G ct inp ev t) := by
  induction t with
  | zero => exact winv_init inp _
  | succ t ih =>
    rw [runC_succ]
    exact (winv_step ih (ev t) (hev t)).1.anti fun x hx => crashedAt_mono (Nat.le_succ t) hx

theorem ext_runC (ct : V → Option ℕ) (inp : V → ℝ) (ev : ℕ → Event V (ℝ × V × ℕ))
    (hev : ∀ t x y m, ev t ≠ .byz x y m) {t t' : ℕ} (h : t ≤ t') (j : V) :
    Ext ((runC (wa G f pend) G ct inp ev t).st j) ((runC (wa G f pend) G ct inp ev t').st j) := by
  induction t', h using Nat.le_induction with
  | base => exact Ext.refl _
  | succ t' _ ih =>
    refine ih.trans ?_
    rw [runC_succ]
    exact (winv_step (winv_runC ct inp ev hev t') (ev t') (hev t')).2 j

/-! ## Safety -/

/-- **ε-agreement** at every time. -/
theorem wa_agreement (hG : TwoReach G f) {lo hi : ℝ} (hlohi : lo ≤ hi) {inp : V → ℝ}
    (hinp : ∀ w, inp w ∈ Set.Icc lo hi) {B : Finset V} {C : Config V (ℝ × V × ℕ) (WS V)}
    (hI : WInv G f pend inp B C) {v u : V} {y z : ℝ} (hy : C.dec v = some y)
    (hz : C.dec u = some z) :
    |y - z| ≤ (1 - 1 / (Fintype.card V : ℝ)) ^ pend * (hi - lo) := by
  obtain ⟨a, b, -, -, -, hw, hval⟩ := contraction hG hI.li hlohi (fun w => (hinp w).1)
    (fun w => (hinp w).2) pend
  obtain ⟨hv1, hv2⟩ := hI.dec_some v y hy
  obtain ⟨hu1, hu2⟩ := hI.dec_some u z hz
  have h1 := hval v hv1
  have h2 := hval u hu1
  rw [hv2] at h1; rw [hu2] at h2
  rw [abs_le]; constructor <;> linarith

/-- **Validity**: every decision lies between two inputs. -/
theorem wa_validity (hG : TwoReach G f) {inp : V → ℝ} {B : Finset V}
    {C : Config V (ℝ × V × ℕ) (WS V)} (hI : WInv G f pend inp B C) {v : V} {y : ℝ}
    (hy : C.dec v = some y) : (∃ w, inp w ≤ y) ∧ ∃ w, y ≤ inp w := by
  obtain ⟨wmin, -, hmin⟩ := exists_min_image univ inp ⟨v, mem_univ _⟩
  obtain ⟨wmax, -, hmax⟩ := exists_max_image univ inp ⟨v, mem_univ _⟩
  obtain ⟨a, b, hla, -, hbh, -, hval⟩ := contraction hG hI.li (hmin wmax (mem_univ _))
    (fun w => hmin w (mem_univ _)) (fun w => hmax w (mem_univ _)) pend
  obtain ⟨hv1, hv2⟩ := hI.dec_some v y hy
  have h1 := hval v hv1
  rw [hv2] at h1
  exact ⟨⟨wmin, by linarith⟩, ⟨wmax, by linarith⟩⟩

end CrashConsensusDigraph
