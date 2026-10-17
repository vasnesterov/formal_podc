import Papers.PODC2019.TopologicalConsensus.DynamicNetworks

/-!
# The lossy link (Section 8.1 and Section 8.4 of the paper)

Two processes `0, 1` and binary consensus. The graphs are `toR` (`0 → 1`), `toL` (`1 → 0`) and
`both` (`0 ↔ 1`).

* `MA3` (the oblivious message adversary choosing any graph of `{←, ↔, →}` in every round):
  consensus is impossible (Santoro–Widmayer). We prove it as the paper explains it in Section 8.1:
  for every valid, locally constant labelling (equivalently, every `d_u`-clopen partition with
  validity, `DN.dn_solvable_iff`) we construct a forever-bivalent execution, the common limit of
  `0`-labelled and `1`-labelled executions, and local constancy at that limit gives a contradiction
  (`not_solvable_MA3`).
* `MA2` (choosing from `{←, →}`, Coulouma–Godard–Peters): consensus is solvable; the decision sets
  "the input of the round-1 sender is `v`" are clopen, so the universal algorithm of Theorem 5.2
  solves consensus (`solvable_MA2`).
-/

namespace TopoConsensus

namespace LossyLink

open DN Cslib.HeardOf Set

/-- `0 → 1`. -/
def toR : Graph (Fin 2) := fun q p => q = 0 ∧ p = 1
/-- `1 → 0`. -/
def toL : Graph (Fin 2) := fun q p => q = 1 ∧ p = 0
/-- `0 ↔ 1`. -/
def both : Graph (Fin 2) := fun q p => q ≠ p

/-- The oblivious message adversary `{←, ↔, →}`. -/
def MA3 : Set (ℕ → Graph (Fin 2)) := {σ | ∀ t, σ t = toL ∨ σ t = both ∨ σ t = toR}

/-- The oblivious message adversary `{←, →}`. -/
def MA2 : Set (ℕ → Graph (Fin 2)) := {σ | ∀ t, σ t = toL ∨ σ t = toR}

/-- Labellings of executions (inputs, pattern) by decision values. -/
abbrev Labelling := (Fin 2 → Bool) → (ℕ → Graph (Fin 2)) → Bool

/-- Validity of a labelling. -/
def Valid (MA : Set (ℕ → Graph (Fin 2))) (L : Labelling) : Prop :=
  ∀ v x, ∀ σ ∈ MA, (∀ p, x p = v) → L x σ = v

/-- Local constancy of a labelling (`d_u`-openness of the decision sets). -/
def LocConst (MA : Set (ℕ → Graph (Fin 2))) (L : Labelling) : Prop :=
  ∀ x, ∀ σ ∈ MA, ∃ T, ∀ y, ∀ τ ∈ MA, (∃ p, FIIndist x y σ τ T p) → L y τ = L x σ

/-- `σ` up to round `t`, then `G` in round `t + 1`, then `H` forever. -/
def ext (σ : ℕ → Graph (Fin 2)) (t : ℕ) (G H : Graph (Fin 2)) : ℕ → Graph (Fin 2) :=
  fun k => if k < t then σ k else if k = t then G else H

theorem ext_mem {σ : ℕ → Graph (Fin 2)} (hσ : σ ∈ MA3) (t : ℕ) {G H : Graph (Fin 2)}
    (hG : G = toL ∨ G = both ∨ G = toR) (hH : H = toL ∨ H = both ∨ H = toR) : ext σ t G H ∈ MA3 := by
  intro k
  unfold ext
  split_ifs
  · exact hσ k
  · exact hG
  · exact hH

theorem ext_lt {σ : ℕ → Graph (Fin 2)} {t k : ℕ} {G H : Graph (Fin 2)} (hk : k < t) :
    ext σ t G H k = σ k := by simp [ext, hk]

theorem ext_eq {σ : ℕ → Graph (Fin 2)} {t : ℕ} {G H : Graph (Fin 2)} : ext σ t G H t = G := by
  simp [ext]

theorem ext_gt {σ : ℕ → Graph (Fin 2)} {t k : ℕ} {G H : Graph (Fin 2)} (hk : t < k) :
    ext σ t G H k = H := by
  simp [ext, show ¬ k < t by omega, show k ≠ t by omega]

/-- If `p` hears nobody from round `t + 1` on in both executions, its view stays the same. -/
theorem FIIndist_forever {x y : Fin 2 → Bool} {σ τ : ℕ → Graph (Fin 2)} {p : Fin 2} {t : ℕ}
    (h : FIIndist x y σ τ t p) (hσ : ∀ k ≥ t, ∀ q, ¬ σ k q p) (hτ : ∀ k ≥ t, ∀ q, ¬ τ k q p) :
    ∀ T, FIIndist x y σ τ T p := by
  intro T
  rcases le_total T t with hT | hT
  · exact h.mono T hT
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hT
    induction d with
    | zero => exact h
    | succ d ih =>
      exact (ih (by omega)).succ_of_deaf (hσ _ (by omega)) (hτ _ (by omega))

theorem toR_deaf (q : Fin 2) : ¬ toR q 0 := by simp [toR]
theorem toL_deaf (q : Fin 2) : ¬ toL q 1 := by simp [toL]

/-- Same view forever, same label. -/
theorem eq_of_forever {MA : Set (ℕ → Graph (Fin 2))} {L : Labelling} (hL : LocConst MA L)
    {x y : Fin 2 → Bool} {σ τ : ℕ → Graph (Fin 2)} (hσ : σ ∈ MA) (hτ : τ ∈ MA) (p : Fin 2)
    (h : ∀ T, FIIndist x y σ τ T p) : L y τ = L x σ := by
  obtain ⟨T, hT⟩ := hL x σ hσ
  exact hT y τ hτ ⟨p, h T⟩

/-- Process `0` cannot distinguish `toL` from `both` in round `t + 1` if it hears nobody later. -/
theorem view0_toL_both (x : Fin 2 → Bool) (σ : ℕ → Graph (Fin 2)) (t : ℕ) :
    ∀ T, FIIndist x x (ext σ t toL toR) (ext σ t both toR) T 0 := by
  have hpre : ∀ p, FIIndist x x (ext σ t toL toR) (ext σ t both toR) t p :=
    FIIndist_of_prefix fun k hk => by rw [ext_lt hk, ext_lt hk]
  have h1 : FIIndist x x (ext σ t toL toR) (ext σ t both toR) (t + 1) 0 := by
    refine ⟨hpre 0, fun q => ?_, fun q _ => hpre q⟩
    rw [ext_eq, ext_eq]
    fin_cases q <;> simp [toL, both]
  refine FIIndist_forever h1 (fun k hk q => ?_) (fun k hk q => ?_)
  · rw [ext_gt (by omega)]; exact toR_deaf q
  · rw [ext_gt (by omega)]; exact toR_deaf q

/-- Process `1` cannot distinguish `toR` from `both` in round `t + 1` if it hears nobody later. -/
theorem view1_toR_both (x : Fin 2 → Bool) (σ : ℕ → Graph (Fin 2)) (t : ℕ) :
    ∀ T, FIIndist x x (ext σ t toR toL) (ext σ t both toL) T 1 := by
  have hpre : ∀ p, FIIndist x x (ext σ t toR toL) (ext σ t both toL) t p :=
    FIIndist_of_prefix fun k hk => by rw [ext_lt hk, ext_lt hk]
  have h1 : FIIndist x x (ext σ t toR toL) (ext σ t both toL) (t + 1) 1 := by
    refine ⟨hpre 1, fun q => ?_, fun q _ => hpre q⟩
    rw [ext_eq, ext_eq]
    fin_cases q <;> simp [toR, both]
  refine FIIndist_forever h1 (fun k hk q => ?_) (fun k hk q => ?_)
  · rw [ext_gt (by omega)]; exact toL_deaf q
  · rw [ext_gt (by omega)]; exact toL_deaf q

section Bivalence

variable {L : Labelling}

/-- Some extension in `MA3` of the first `t` rounds of `σ` gets label `v`. -/
def Possible (L : Labelling) (x : Fin 2 → Bool) (σ : ℕ → Graph (Fin 2)) (t : ℕ) (v : Bool) :
    Prop :=
  ∃ τ ∈ MA3, (∀ k < t, τ k = σ k) ∧ L x τ = v

/-- Both labels are possible after the first `t` rounds of `σ`. -/
def Biv (L : Labelling) (x : Fin 2 → Bool) (σ : ℕ → Graph (Fin 2)) (t : ℕ) : Prop :=
  Possible L x σ t true ∧ Possible L x σ t false

theorem eq_of_not_biv {x : Fin 2 → Bool} {σ : ℕ → Graph (Fin 2)} {t : ℕ} (h : ¬ Biv L x σ t)
    {τ₁ τ₂ : ℕ → Graph (Fin 2)} (h₁ : τ₁ ∈ MA3) (h₂ : τ₂ ∈ MA3) (e₁ : ∀ k < t, τ₁ k = σ k)
    (e₂ : ∀ k < t, τ₂ k = σ k) : L x τ₁ = L x τ₂ := by
  by_contra hne
  apply h
  cases hv : L x τ₁ <;> cases hw : L x τ₂
  · rw [hv, hw] at hne; exact absurd rfl hne
  · exact ⟨⟨τ₂, h₂, e₂, hw⟩, ⟨τ₁, h₁, e₁, hv⟩⟩
  · exact ⟨⟨τ₁, h₁, e₁, hv⟩, ⟨τ₂, h₂, e₂, hw⟩⟩
  · rw [hv, hw] at hne; exact absurd rfl hne

theorem ext_prefix {σ : ℕ → Graph (Fin 2)} {t : ℕ} {G H H' : Graph (Fin 2)} :
    ∀ k < t + 1, ext σ t G H k = ext σ t G H' k := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · rw [ext_lt hk, ext_lt hk]
  · rw [ext_eq, ext_eq]

/-- The bivalence step: a bivalent prefix has a bivalent one-round extension. -/
theorem biv_step (hL : LocConst MA3 L) {x : Fin 2 → Bool} {σ : ℕ → Graph (Fin 2)} (hσ : σ ∈ MA3)
    {t : ℕ} (hb : Biv L x σ t) :
    ∃ G, (G = toL ∨ G = both ∨ G = toR) ∧ Biv L x (ext σ t G toR) (t + 1) := by
  by_contra hcon
  push Not at hcon
  have hLm : toL = toL ∨ toL = both ∨ toL = toR := Or.inl rfl
  have hBm : both = toL ∨ both = both ∨ both = toR := Or.inr (Or.inl rfl)
  have hRm : toR = toL ∨ toR = both ∨ toR = toR := Or.inr (Or.inr rfl)
  set eL := ext σ t toL toR
  set eB := ext σ t both toR
  set eB' := ext σ t both toL
  set eR := ext σ t toR toL
  have meL : eL ∈ MA3 := ext_mem hσ t hLm hRm
  have meB : eB ∈ MA3 := ext_mem hσ t hBm hRm
  have meB' : eB' ∈ MA3 := ext_mem hσ t hBm hLm
  have meR : eR ∈ MA3 := ext_mem hσ t hRm hLm
  have hLB : L x eL = L x eB := (eq_of_forever hL meL meB 0 (view0_toL_both x σ t)).symm
  have hRB : L x eR = L x eB' := (eq_of_forever hL meR meB' 1 (view1_toR_both x σ t)).symm
  have hBB : L x eB = L x eB' :=
    eq_of_not_biv (hcon both hBm) meB meB' (fun k _ => rfl) (fun k hk => ext_prefix k hk)
  -- every extension of the first `t` rounds has label `L x eB`
  have hall : ∀ τ ∈ MA3, (∀ k < t, τ k = σ k) → L x τ = L x eB := by
    intro τ hτ hpre
    have hτpre : ∀ G, τ t = G → ∀ k < t + 1, τ k = ext σ t G toR k := by
      intro G hG k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [ext_lt hk, hpre k hk]
      · rw [ext_eq, hG]
    rcases hτ t with h | h | h
    · rw [eq_of_not_biv (hcon toL hLm) hτ meL (hτpre _ h) (fun k _ => rfl), hLB]
    · exact eq_of_not_biv (hcon both hBm) hτ meB (hτpre _ h) (fun k _ => rfl)
    · rw [eq_of_not_biv (hcon toR hRm) hτ (ext_mem hσ t hRm hRm) (hτpre _ h) (fun k _ => rfl),
        eq_of_not_biv (hcon toR hRm) (ext_mem hσ t hRm hRm) meR (fun k _ => rfl)
          (fun k hk => ext_prefix k hk), hRB, ← hBB]
  obtain ⟨⟨τ₁, h₁, e₁, v₁⟩, ⟨τ₂, h₂, e₂, v₂⟩⟩ := hb
  have := (hall τ₁ h₁ e₁).trans (hall τ₂ h₂ e₂).symm
  rw [v₁, v₂] at this
  exact Bool.noConfusion this

/-- The mixed input `x 0 = 0`, `x 1 = 1`. -/
def x01 : Fin 2 → Bool := fun p => if p = 0 then false else true

theorem biv_init (hV : Valid MA3 L) (hL : LocConst MA3 L) (σ : ℕ → Graph (Fin 2)) :
    Biv L x01 σ 0 := by
  have hRc : (fun _ : ℕ => toR) ∈ MA3 := fun _ => Or.inr (Or.inr rfl)
  have hLc : (fun _ : ℕ => toL) ∈ MA3 := fun _ => Or.inl rfl
  refine ⟨⟨fun _ => toL, hLc, fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩,
    ⟨fun _ => toR, hRc, fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩⟩
  · -- process 1 cannot distinguish `x01` from all-`1` when it never hears process 0
    have h := eq_of_forever (x := fun _ => true) (y := x01) hL hLc hLc 1
      (FIIndist_forever (t := 0) (by simp [FIIndist, x01]) (fun k _ q => toL_deaf q)
        (fun k _ q => toL_deaf q))
    rw [h]
    exact hV true _ _ hLc (fun _ => rfl)
  · have h := eq_of_forever (x := fun _ => false) (y := x01) hL hRc hRc 0
      (FIIndist_forever (t := 0) (by simp [FIIndist, x01]) (fun k _ q => toR_deaf q)
        (fun k _ q => toR_deaf q))
    rw [h]
    exact hV false _ _ hRc (fun _ => rfl)

open Classical in
/-- The forever-bivalent run, built round by round. -/
noncomputable def bivSeq (L : Labelling) : ℕ → (ℕ → Graph (Fin 2))
  | 0 => fun _ => toR
  | t + 1 =>
    if h : ∃ G, (G = toL ∨ G = both ∨ G = toR) ∧ Biv L x01 (ext (bivSeq L t) t G toR) (t + 1)
    then ext (bivSeq L t) t (Classical.choose h) toR else bivSeq L t

theorem bivSeq_spec (hV : Valid MA3 L) (hL : LocConst MA3 L) :
    ∀ t, bivSeq L t ∈ MA3 ∧ Biv L x01 (bivSeq L t) t
  | 0 => ⟨fun _ => Or.inr (Or.inr rfl), biv_init hV hL _⟩
  | t + 1 => by
    obtain ⟨hm, hb⟩ := bivSeq_spec hV hL t
    have h := biv_step hL hm hb
    simp only [bivSeq, dite_eq_left h]
    exact ⟨ext_mem hm t (Classical.choose_spec h).1 (Or.inr (Or.inr rfl)),
      (Classical.choose_spec h).2⟩

theorem bivSeq_succ_lt (t k : ℕ) (hk : k < t) : bivSeq L (t + 1) k = bivSeq L t k := by
  classical
  simp only [bivSeq]
  split_ifs
  · exact ext_lt hk
  · rfl

theorem bivSeq_stable : ∀ d t k, k < t → bivSeq L (t + d) k = bivSeq L t k
  | 0, _, _, _ => rfl
  | d + 1, t, k, hk => by
    rw [← add_assoc, bivSeq_succ_lt _ _ (by omega), bivSeq_stable d t k hk]

/-- The limit of the forever-bivalent prefixes. -/
noncomputable def bivLimit (L : Labelling) : ℕ → Graph (Fin 2) := fun k => bivSeq L (k + 1) k

theorem bivLimit_prefix (t k : ℕ) (hk : k < t) : bivLimit L k = bivSeq L t k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hk)
  unfold bivLimit
  rw [bivSeq_stable d (k + 1) k (Nat.lt_succ_self k)]

end Bivalence

/-- No valid, locally constant labelling exists for `{←, ↔, →}`. -/
theorem no_labelling_MA3 : ¬ ∃ L, Valid MA3 L ∧ LocConst MA3 L := by
  rintro ⟨L, hV, hL⟩
  have hρ : bivLimit L ∈ MA3 := fun k => (bivSeq_spec hV hL (k + 1)).1 k
  obtain ⟨T, hT⟩ := hL x01 (bivLimit L) hρ
  obtain ⟨-, ⟨τ₁, h₁, e₁, v₁⟩, ⟨τ₂, h₂, e₂, v₂⟩⟩ := bivSeq_spec hV hL (T + 1)
  have hpre : ∀ τ, (∀ k < T + 1, τ k = bivSeq L (T + 1) k) → ∃ p, FIIndist x01 x01 (bivLimit L) τ T p :=
    fun τ e => ⟨0, FIIndist_of_prefix (fun k hk => by
      rw [bivLimit_prefix (T + 1) k (by omega), e k (by omega)]) 0⟩
  have a₁ := hT x01 τ₁ h₁ (hpre τ₁ e₁)
  have a₂ := hT x01 τ₂ h₂ (hpre τ₂ e₂)
  rw [v₁] at a₁
  rw [v₂] at a₂
  exact Bool.noConfusion (a₁.trans a₂.symm)

/-- **Lossy link `{←, ↔, →}`** (Santoro–Widmayer, Section 8.1): consensus is impossible; there is
no partition of `Σ` into `d_u`-clopen decision sets with validity. -/
theorem not_solvable_MA3 :
    ¬ UniformSolvable (dnModel (V := Bool) MA3) ∧ ¬ NonUniformSolvable (dnModel (V := Bool) MA3) := by
  have h : ¬ UniformSolvable (dnModel (V := Bool) MA3) := by
    rw [dn_solvable_iff]
    rintro ⟨L, hV, hL⟩
    exact no_labelling_MA3 ⟨L, fun v x σ hσ hx => hV v x σ hσ hx, hL⟩
  refine ⟨h, fun h' => h ?_⟩
  rwa [Model.uniformSolvable_iff_nonUniform _ faultFree]

open Classical in
/-- The label of the `{←, →}` adversary: the input of the round-1 sender. -/
noncomputable def L2 : Labelling := fun x σ => if σ 0 1 0 then x 1 else x 0

theorem L2_valid : Valid MA2 L2 := by
  intro v x σ _ hx
  unfold L2
  split_ifs <;> exact hx _

theorem L2_locConst : LocConst MA2 L2 := by
  intro x σ hσ
  refine ⟨1, fun y τ hτ ⟨p, hp, hin, hq⟩ => ?_⟩
  change x p = y p at hp
  have hq' : ∀ q, σ 0 q p → x q = y q := hq
  have hσ0 := hσ 0
  have hτ0 := hτ 0
  unfold L2
  fin_cases p
  · have e := hin 1
    have hx1 := hq' 1
    rcases hσ0 with h₁ | h₁ <;> rcases hτ0 with h₂ | h₂ <;> simp_all [toL, toR]
  · have e := hin 0
    have hx0 := hq' 0
    rcases hσ0 with h₁ | h₁ <;> rcases hτ0 with h₂ | h₂ <;> simp_all [toL, toR]

/-- **Lossy link `{←, →}`** (Coulouma–Godard–Peters, Section 8.1/8.4): consensus is solvable (by
the universal algorithm of Theorem 5.2 applied to the decision sets "the round-1 sender has input
`v`"). -/
theorem solvable_MA2 : UniformSolvable (dnModel (V := Bool) MA2) :=
  dn_solvable_iff.2 ⟨L2, L2_valid, L2_locConst⟩

end LossyLink

end TopoConsensus
