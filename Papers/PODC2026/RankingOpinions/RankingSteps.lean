import Papers.PODC2026.RankingOpinions.RankingProtocol

/-!
# The Ranking protocol: computing single transitions

Lemmas computing `rδ` on pairs of states in the situations used by the reachability proof
(Proposition 6.6) and the stability proof (Lemma 6.5).
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Ranking

variable {k : ℕ} [NeZero k]

/-- A rule leaves the pair unchanged in both orientations. -/
def Still (r : Rule k) (a b : RState k) : Prop := r a b = (a, b) ∧ r b a = (b, a)

lemma Still.symm {r : Rule k} {a b : RState k} (h : Still r a b) : Still r b a := ⟨h.2, h.1⟩

lemma firstChange_still {r : Rule k} {rs : List (Rule k)} {a b : RState k} (h : Still r a b) :
    firstChange (r :: rs) a b = firstChange rs a b := by
  simp [firstChange, applyCase, h.1, h.2]

lemma firstChange_fire {r : Rule k} {rs : List (Rule k)} {a b : RState k} (h : r a b ≠ (a, b)) :
    firstChange (r :: rs) a b = r a b := by
  simp [firstChange, applyCase, h]

lemma firstChange_fire_swap {r : Rule k} {rs : List (Rule k)} {a b : RState k}
    (h1 : r a b = (a, b)) (h : r b a ≠ (b, a)) :
    firstChange (r :: rs) a b = (r b a).swap := by
  have : (r b a).swap ≠ (a, b) := by
    intro e; apply h; rw [← Prod.swap_swap (r b a), e]; rfl
  simp [firstChange, applyCase, h1, this]

lemma firstChange_nil (a b : RState k) : firstChange [] a b = (a, b) := rfl

/-! ### When a rule does not change a pair -/

lemma r2_eq {X Y : RState k} (h : ¬ (X.tok ∧ Y.tok ∧ X.kc = Y.kc)) : r2 X Y = (X, Y) := by
  unfold r2; rw [ite_eq_right]; tauto

lemma r3_eq {X Y : RState k} (h : ¬ (X.tok ∧ Y.tok ∧ X.kr = Y.kr)) : r3 X Y = (X, Y) := by
  unfold r3; rw [ite_eq_right]; tauto

lemma r4a_eq {X Y : RState k} (h : X.tok → Y.tok = false → X.kc = Y.kc → Y.kr = X.kr) :
    r4a X Y = (X, Y) := by
  unfold r4a; split_ifs with hg
  · rw [← h hg.1 hg.2.1 hg.2.2]
  · rfl

lemma r4b_eq {X Y : RState k} (h : X.tok → Y.bc = X.kc → Y.br = X.kr) : r4b X Y = (X, Y) := by
  unfold r4b; split_ifs with hg
  · rw [← h hg.1 hg.2]
  · rfl

lemma r5_eq {X Y : RState k} (h : ¬ Profitable (X.br, X.kr) (Y.br, Y.kr)) : r5 X Y = (X, Y) := by
  unfold r5; rw [ite_eq_right h]

lemma r6a_eq {X Y : RState k}
    (h : ¬ (X.tok = false ∧ X.bc = X.kc ∧ X.br = X.kr ∧ Y.tok ∧ Y.kc = X.kc ∧ Y.kr = X.kr)) :
    r6a X Y = (X, Y) := by
  unfold r6a; rw [ite_eq_right h]

lemma r6b_eq {X Y : RState k}
    (h : ¬ (X.tok = false ∧ Y.tok ∧ X.kc = Y.kc ∧ X.kr = Y.kr ∧ X.bc ≠ X.kc ∧ Y.bc ≠ Y.kc ∧
      X.br < Y.br)) : r6b X Y = (X, Y) := by
  unfold r6b; rw [ite_eq_right h]

lemma r7a_eq {X Y : RState k}
    (h : ¬ (X.tok ∧ Y.tok ∧ X.bc = X.kc ∧ X.br = X.kr ∧ Y.kr = 0 ∧ Y.kc ≠ X.bc ∧ X.br ≠ 0)) :
    r7a X Y = (X, Y) := by
  unfold r7a; rw [ite_eq_right h]

lemma r7b_eq {X Y : RState k} (h : X.tok → Y.tok → X.bc = Y.bc → X.br = Y.br → X.kc ≠ X.bc →
    Y.kc ≠ Y.bc → Y.kr = X.kr) : r7b X Y = (X, Y) := by
  unfold r7b; split_ifs with hg
  · have := h hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2
    ext <;> simp [this]
  · rfl

/-! ### Tokens -/

/-- Number of tokens of a pair. -/
def ntok (a b : RState k) : ℕ := a.tok.toNat + b.tok.toNat

/-- Rule (2): two tokens of the same color meet: one of them is deleted. -/
lemma rδ_del {a b : RState k} (ha : a.tok) (hb : b.tok) (hc : a.kc = b.kc) :
    ntok (rδ a b).1 (rδ a b).2 < ntok a b := by
  simp only [ntok, rδ, norm_tok, rules]
  by_cases hab : a.br ≤ b.br
  · have hfire : r2 a b ≠ (a, b) := by
      unfold r2; rw [ite_eq_left ⟨ha, hb, hc, hab⟩]
      intro e; have := congrArg (fun p => p.2.tok) e; simp [hb] at this
    rw [firstChange_fire hfire]
    unfold r2; rw [ite_eq_left ⟨ha, hb, hc, hab⟩]; simp [ha, hb]
  · have hba : b.br ≤ a.br := le_of_lt (not_le.1 hab)
    have h1 : r2 a b = (a, b) := by unfold r2; rw [ite_eq_right]; tauto
    have hfire : r2 b a ≠ (b, a) := by
      unfold r2; rw [ite_eq_left ⟨hb, ha, hc.symm, hba⟩]
      intro e; have := congrArg (fun p => p.2.tok) e; simp [ha] at this
    rw [firstChange_fire_swap h1 hfire]
    unfold r2; rw [ite_eq_left ⟨hb, ha, hc.symm, hba⟩]; simp [ha, hb]

/-! ### Consistency with a ranking -/

/-- A state is consistent with the ranking `σ` (colors ↦ rankings). -/
def SCons (σ : Fin k → Fin k) (s : RState k) : Prop := s.br = σ s.bc ∧ s.kr = σ s.kc

lemma SCons.normal {σ : Fin k → Fin k} {s : RState k} (h : SCons σ s) : Normal s := by
  intro _ hc; rw [h.1, h.2, hc]

lemma SCons.norm_eq {σ : Fin k → Fin k} {s : RState k} (h : SCons σ s) : norm s = s :=
  norm_of_normal h.normal

lemma norm_of_ne {s : RState k} (h : s.bc ≠ s.kc) : norm s = s := by
  unfold norm; rw [ite_eq_right (fun h' => h h'.2)]

lemma norm_of_not_tok {s : RState k} (h : s.tok = false) : norm s = s := by
  unfold norm; rw [ite_eq_right (fun h' => by simp [h] at h')]

/-! ### Single transitions -/

/-- Nothing changes. -/
lemma rδ_still {a b : RState k} (h2 : Still r2 a b) (h3 : Still r3 a b) (h4a : Still r4a a b)
    (h4b : Still r4b a b) (h5 : Still r5 a b) (h6a : Still r6a a b) (h6b : Still r6b a b)
    (h7a : Still r7a a b) (h7b : Still r7b a b) (ha : Normal a) (hb : Normal b) :
    rδ a b = (a, b) := by
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_still h4a,
    firstChange_still h4b, firstChange_still h5, firstChange_still h6a, firstChange_still h6b,
    firstChange_still h7a, firstChange_still h7b, firstChange_nil, norm_of_normal ha,
    norm_of_normal hb]

lemma fin_add_one_ne {x : Fin k} (hk : 1 < k) : x + 1 ≠ x := by
  intro e
  have h1 : (1 : Fin k) = 0 := by simpa using e
  have := congrArg Fin.val h1
  simp [Nat.mod_eq_of_lt hk] at this

/-- Rule (3): ranking uniqueness. -/
lemma rδ_r3 {a b : RState k} (ha : a.tok) (hb : b.tok) (hr : a.kr = b.kr) (hc : a.kc < b.kc)
    (hna : Normal a) : rδ a b = (a, norm {b with kr := b.kr + 1}) := by
  have hk : 1 < k := by have := b.kc.isLt; have : a.kc.val < b.kc.val := hc; omega
  have h2 : Still r2 a b := ⟨r2_eq (fun h => hc.ne h.2.2), r2_eq (fun h => hc.ne h.2.2.symm)⟩
  have hfire : r3 a b ≠ (a, b) := by
    unfold r3; rw [ite_eq_left ⟨ha, hb, hr, hc⟩]
    intro e
    exact fin_add_one_ne hk (congrArg (fun p => p.2.kr) e)
  simp only [rδ, rules, firstChange_still h2, firstChange_fire hfire]
  unfold r3; rw [ite_eq_left ⟨ha, hb, hr, hc⟩]; simp [norm_of_normal hna]

/-- Rule (4), first bullet: broadcast of a ket ranking. -/
lemma rδ_r4a {h a : RState k} (hh : h.tok) (ha : a.tok = false) (hc : h.kc = a.kc)
    (hr : a.kr ≠ h.kr) (hnh : Normal h) : rδ h a = (h, {a with kr := h.kr}) := by
  have h2 : Still r2 h a := ⟨r2_eq (by simp [ha]), r2_eq (by simp [ha])⟩
  have h3 : Still r3 h a := ⟨r3_eq (by simp [ha]), r3_eq (by simp [ha])⟩
  have hfire : r4a h a ≠ (h, a) := by
    unfold r4a; rw [ite_eq_left ⟨hh, ha, hc⟩]
    intro e; exact hr (congrArg (fun p => p.2.kr) e).symm
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_fire hfire]
  unfold r4a; rw [ite_eq_left ⟨hh, ha, hc⟩]
  simp [norm_of_normal hnh, norm_of_not_tok (s := {a with kr := h.kr}) ha]

/-- Rule (4), second bullet: broadcast of a bra ranking. -/
lemma rδ_r4b {h a : RState k} (hh : h.tok) (hbc : a.bc = h.kc) (hr : a.br ≠ h.kr)
    (h2' : ¬ (a.tok ∧ a.kc = h.kc)) (h3' : a.tok → a.kr ≠ h.kr)
    (h4' : a.tok = false → a.kc = h.kc → a.kr = h.kr) (hnh : Normal h) :
    rδ h a = (h, {a with br := h.kr}) := by
  have h2 : Still r2 h a := ⟨r2_eq (fun h => h2' ⟨h.2.1, h.2.2.symm⟩),
    r2_eq (fun h => h2' ⟨h.1, h.2.2⟩)⟩
  have h3 : Still r3 h a := ⟨r3_eq (fun h => h3' h.2.1 h.2.2.symm),
    r3_eq (fun h => h3' h.1 h.2.2)⟩
  have h4a : Still r4a h a := ⟨r4a_eq (fun _ h1 h2 => h4' h1 h2.symm),
    r4a_eq (fun _ h1 _ => by simp [hh] at h1)⟩
  have hfire : r4b h a ≠ (h, a) := by
    unfold r4b; rw [ite_eq_left ⟨hh, hbc⟩]
    intro e; exact hr (congrArg (fun p => p.2.br) e).symm
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_still h4a,
    firstChange_fire hfire]
  unfold r4b; rw [ite_eq_left ⟨hh, hbc⟩]
  have : norm {a with br := h.kr} = {a with br := h.kr} := by
    unfold norm; rw [ite_eq_right]
    rintro ⟨ht, hc⟩; exact h2' ⟨ht, hc ▸ hbc⟩
  simp [norm_of_normal hnh, this]

/-- Rule (5): Circles on rankings, for states consistent with a ranking. -/
lemma rδ_r5 {σ : Fin k → Fin k} {a b : RState k} (ha : SCons σ a)
    (hb : SCons σ b) (hp : Profitable (a.br, a.kr) (b.br, b.kr)) :
    rδ a b = ({a with kr := b.kr, kc := b.kc, tok := b.tok},
      {b with kr := a.kr, kc := a.kc, tok := a.tok}) := by
  have hkr : a.kr ≠ b.kr := hp.ket_ne
  have hkc : a.kc ≠ b.kc := fun e => hkr (by rw [ha.2, hb.2, e])
  have h2 : Still r2 a b := ⟨r2_eq (fun h => hkc h.2.2), r2_eq (fun h => hkc h.2.2.symm)⟩
  have h3 : Still r3 a b := ⟨r3_eq (fun h => hkr h.2.2), r3_eq (fun h => hkr h.2.2.symm)⟩
  have h4a : Still r4a a b := ⟨r4a_eq (fun _ _ h => absurd h hkc),
    r4a_eq (fun _ _ h => absurd h.symm hkc)⟩
  have h4b : Still r4b a b := ⟨r4b_eq (fun _ h => by rw [hb.1, h, ha.2]),
    r4b_eq (fun _ h => by rw [ha.1, h, hb.2])⟩
  have hfire : r5 a b ≠ (a, b) := by
    unfold r5; rw [ite_eq_left hp]
    intro e; exact hkr (congrArg (fun p => p.1.kr) e).symm
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_still h4a,
    firstChange_still h4b, firstChange_fire hfire]
  unfold r5; rw [ite_eq_left hp]
  have n1 : norm {a with kr := b.kr, kc := b.kc, tok := b.tok} =
      {a with kr := b.kr, kc := b.kc, tok := b.tok} :=
    norm_of_normal (fun _ hc => by simp only at hc ⊢; rw [ha.1, hb.2, hc])
  have n2 : norm {b with kr := a.kr, kc := a.kc, tok := a.tok} =
      {b with kr := a.kr, kc := a.kc, tok := a.tok} :=
    norm_of_normal (fun _ hc => by simp only at hc ⊢; rw [hb.1, ha.2, hc])
  rw [n1, n2]

/-- Rule (6), first bullet: the token moves to a diagonal braket `⟨i,𝔦|𝔦,i⟩`. -/
lemma rδ_r6a {t h : RState k} (ht : t.tok = false) (hd : t.bc = t.kc) (hdr : t.br = t.kr)
    (hh : h.tok) (hc : h.kc = t.kc) (hr : h.kr = t.kr) :
    rδ t h = ({t with tok := true}, {h with tok := false}) := by
  have h2 : Still r2 t h := ⟨r2_eq (by simp [ht]), r2_eq (by simp [ht])⟩
  have h3 : Still r3 t h := ⟨r3_eq (by simp [ht]), r3_eq (by simp [ht])⟩
  have h4a : Still r4a t h := ⟨r4a_eq (by simp [ht]), r4a_eq (fun _ _ _ => hr.symm)⟩
  have h4b : Still r4b t h := ⟨r4b_eq (by simp [ht]), r4b_eq (fun _ _ => by rw [hdr, hr])⟩
  have h5 : Still r5 t h := ⟨r5_eq (fun p => p.ket_ne hr.symm), r5_eq (fun p => p.ket_ne hr)⟩
  have hfire : r6a t h ≠ (t, h) := by
    unfold r6a; rw [ite_eq_left ⟨ht, hd, hdr, hh, hc, hr⟩]
    intro e; have := congrArg (fun p => p.1.tok) e; simp [ht] at this
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_still h4a,
    firstChange_still h4b, firstChange_still h5, firstChange_fire hfire]
  unfold r6a; rw [ite_eq_left ⟨ht, hd, hdr, hh, hc, hr⟩]
  rw [norm_of_normal (s := {t with tok := true}) (fun _ _ => hdr),
    norm_of_not_tok (s := {h with tok := false}) rfl]

/-- Rule (6), first bullet, with the token holder as initiator. -/
lemma rδ_r6a' {t h : RState k} (ht : t.tok = false) (hd : t.bc = t.kc) (hdr : t.br = t.kr)
    (hh : h.tok) (hc : h.kc = t.kc) (hr : h.kr = t.kr) :
    rδ h t = ({h with tok := false}, {t with tok := true}) := by
  have h2 : Still r2 t h := ⟨r2_eq (by simp [ht]), r2_eq (by simp [ht])⟩
  have h3 : Still r3 t h := ⟨r3_eq (by simp [ht]), r3_eq (by simp [ht])⟩
  have h4a : Still r4a t h := ⟨r4a_eq (by simp [ht]), r4a_eq (fun _ _ _ => hr.symm)⟩
  have h4b : Still r4b t h := ⟨r4b_eq (by simp [ht]), r4b_eq (fun _ _ => by rw [hdr, hr])⟩
  have h5 : Still r5 t h := ⟨r5_eq (fun p => p.ket_ne hr.symm), r5_eq (fun p => p.ket_ne hr)⟩
  have h1 : r6a h t = (h, t) := r6a_eq (by simp [hh])
  have hfire : r6a t h ≠ (t, h) := by
    unfold r6a; rw [ite_eq_left ⟨ht, hd, hdr, hh, hc, hr⟩]
    intro e; have := congrArg (fun p => p.1.tok) e; simp [ht] at this
  simp only [rδ, rules, firstChange_still h2.symm, firstChange_still h3.symm,
    firstChange_still h4a.symm, firstChange_still h4b.symm, firstChange_still h5.symm,
    firstChange_fire_swap h1 hfire]
  unfold r6a; rw [ite_eq_left ⟨ht, hd, hdr, hh, hc, hr⟩]
  simp only [Prod.swap]
  rw [norm_of_normal (s := {t with tok := true}) (fun _ _ => hdr),
    norm_of_not_tok (s := {h with tok := false}) rfl]

/-- Rule (6), second bullet: the token moves to a braket with a smaller bra ranking. -/
lemma rδ_r6b {t h : RState k} (ht : t.tok = false) (hh : h.tok) (hc : t.kc = h.kc)
    (hr : t.kr = h.kr) (htd : t.bc ≠ t.kc) (hhd : h.bc ≠ h.kc) (hlt : t.br < h.br) :
    rδ t h = ({t with tok := true}, {h with tok := false}) := by
  have h2 : Still r2 t h := ⟨r2_eq (by simp [ht]), r2_eq (by simp [ht])⟩
  have h3 : Still r3 t h := ⟨r3_eq (by simp [ht]), r3_eq (by simp [ht])⟩
  have h4a : Still r4a t h := ⟨r4a_eq (by simp [ht]), r4a_eq (fun _ _ _ => hr)⟩
  have h4b : Still r4b t h := ⟨r4b_eq (by simp [ht]), r4b_eq (fun _ e => absurd (e.trans hc.symm) htd)⟩
  have h5 : Still r5 t h := ⟨r5_eq (fun p => p.ket_ne hr), r5_eq (fun p => p.ket_ne hr.symm)⟩
  have h6a : Still r6a t h := ⟨r6a_eq (fun g => htd g.2.1), r6a_eq (by simp [hh])⟩
  have hfire : r6b t h ≠ (t, h) := by
    unfold r6b; rw [ite_eq_left ⟨ht, hh, hc, hr, htd, hhd, hlt⟩]
    intro e; have := congrArg (fun p => p.1.tok) e; simp [ht] at this
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_still h4a,
    firstChange_still h4b, firstChange_still h5, firstChange_still h6a, firstChange_fire hfire]
  unfold r6b; rw [ite_eq_left ⟨ht, hh, hc, hr, htd, hhd, hlt⟩]
  rw [norm_of_ne (s := {t with tok := true}) htd, norm_of_not_tok (s := {h with tok := false}) rfl]

/-- Rule (7), first bullet: ranking swap with the color of ranking `0`. -/
lemma rδ_r7a {a b : RState k} (ha : a.tok) (hb : b.tok) (hd : a.bc = a.kc) (hdr : a.br = a.kr)
    (h0 : b.kr = 0) (hc : b.kc ≠ a.bc) (hne : a.br ≠ 0)
    (hbr : b.bc = a.kc → b.br = a.kr) (hp1 : ¬ Profitable (a.br, a.kr) (b.br, b.kr))
    (hp2 : ¬ Profitable (b.br, b.kr) (a.br, a.kr)) :
    rδ a b = ({a with br := 0, kr := 0}, norm {b with kr := a.br}) := by
  have hkc : a.kc ≠ b.kc := fun e => hc (e ▸ hd).symm
  have hkr : a.kr ≠ b.kr := by rw [h0, ← hdr]; exact hne
  have h2 : Still r2 a b := ⟨r2_eq (fun h => hkc h.2.2), r2_eq (fun h => hkc h.2.2.symm)⟩
  have h3 : Still r3 a b := ⟨r3_eq (fun h => hkr h.2.2), r3_eq (fun h => hkr h.2.2.symm)⟩
  have h4a : Still r4a a b := ⟨r4a_eq (by simp [hb]), r4a_eq (by simp [ha])⟩
  have h4b : Still r4b a b := ⟨r4b_eq (fun _ h => hbr h),
    r4b_eq (fun _ h => absurd (hd ▸ h) hkc)⟩
  have h5 : Still r5 a b := ⟨r5_eq hp1, r5_eq hp2⟩
  have h6a : Still r6a a b := ⟨r6a_eq (by simp [ha]), r6a_eq (by simp [hb])⟩
  have h6b : Still r6b a b := ⟨r6b_eq (by simp [ha]), r6b_eq (by simp [hb])⟩
  have hfire : r7a a b ≠ (a, b) := by
    unfold r7a; rw [ite_eq_left ⟨ha, hb, hd, hdr, h0, hc, hne⟩]
    intro e; exact hne (congrArg (fun p => p.1.br) e).symm
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_still h4a,
    firstChange_still h4b, firstChange_still h5, firstChange_still h6a, firstChange_still h6b,
    firstChange_fire hfire]
  unfold r7a; rw [ite_eq_left ⟨ha, hb, hd, hdr, h0, hc, hne⟩]
  rw [norm_of_normal (s := {a with br := 0, kr := 0}) (fun _ _ => rfl)]

/-- Rule (7), second bullet: two tokens on the same bra exchange their rankings. -/
lemma rδ_r7b {a b : RState k} (ha : a.tok) (hb : b.tok) (hbc : a.bc = b.bc) (hbr : a.br = b.br)
    (hda : a.kc ≠ a.bc) (hdb : b.kc ≠ b.bc) (hkc : a.kc ≠ b.kc) (hkr : a.kr ≠ b.kr)
    (hp1 : ¬ Profitable (a.br, a.kr) (b.br, b.kr))
    (hp2 : ¬ Profitable (b.br, b.kr) (a.br, a.kr)) :
    rδ a b = ({a with kr := b.kr}, {b with kr := a.kr}) := by
  have h2 : Still r2 a b := ⟨r2_eq (fun h => hkc h.2.2), r2_eq (fun h => hkc h.2.2.symm)⟩
  have h3 : Still r3 a b := ⟨r3_eq (fun h => hkr h.2.2), r3_eq (fun h => hkr h.2.2.symm)⟩
  have h4a : Still r4a a b := ⟨r4a_eq (by simp [hb]), r4a_eq (by simp [ha])⟩
  have h4b : Still r4b a b := ⟨r4b_eq (fun _ h => absurd (hbc.trans h).symm hda),
    r4b_eq (fun _ h => absurd (hbc.symm.trans h).symm hdb)⟩
  have h5 : Still r5 a b := ⟨r5_eq hp1, r5_eq hp2⟩
  have h6a : Still r6a a b := ⟨r6a_eq (by simp [ha]), r6a_eq (by simp [hb])⟩
  have h6b : Still r6b a b := ⟨r6b_eq (by simp [ha]), r6b_eq (by simp [hb])⟩
  have h7a : Still r7a a b := ⟨r7a_eq (fun h => hda h.2.2.1.symm),
    r7a_eq (fun h => hdb h.2.2.1.symm)⟩
  have hfire : r7b a b ≠ (a, b) := by
    unfold r7b; rw [ite_eq_left ⟨ha, hb, hbc, hbr, hda, hdb⟩]
    intro e; exact hkr (congrArg (fun p => p.1.kr) e).symm
  simp only [rδ, rules, firstChange_still h2, firstChange_still h3, firstChange_still h4a,
    firstChange_still h4b, firstChange_still h5, firstChange_still h6a, firstChange_still h6b,
    firstChange_still h7a, firstChange_fire hfire]
  unfold r7b; rw [ite_eq_left ⟨ha, hb, hbc, hbr, hda, hdb⟩]
  rw [norm_of_ne (s := {a with kr := b.kr}) (Ne.symm hda),
    norm_of_ne (s := {b with kr := a.kr}) (Ne.symm hdb)]

end RankingOpinions.Ranking
