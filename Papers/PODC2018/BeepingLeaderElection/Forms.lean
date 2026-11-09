import Papers.PODC2018.BeepingLeaderElection.Algorithm

/-!
# The five forms of neighbouring prefixes (Lemma 6 of [Casteigts et al.], the source of Lemma 1)

[Casteigts, Métivier, Robson, Zemmari, *Deterministic Leader Election Takes Θ(D + log n) Bit Rounds*,
arXiv:1605.01903v4], Lemma 6: the prefixes `x = Z_u`, `y = Z_v` of two neighbours always have one of the
forms (up to swapping `u` and `v`)

1. `x = p`, `y = p`;
2. `x = p`, `y = p w` with `1 ≤ |w| ≤ 2`;
3. `x = p 0`, `y = p 1 a`;
4. `x = p 1`, `y = p 0 w` with `|w| ≤ 3`;
5. `x = p`, `y = p w` with `3 ≤ |w| ≤ 6`, and `u` deleted letters in the last phase.

This file proves the *one-edge step*: if `x, y` are in one of the forms and the actions of both nodes
respect the constraints that the rules impose because of the other endpoint (`Allowed`), then the new
prefixes are again in one of the forms. Everything here is about two words; the network-level
invariant is assembled in `Lemma1.lean`.
-/

namespace Podc.BeepingLeaderElection

/-- One-sided forms of Lemma 6 of [Casteigts et al.]; `sx` is the `suspicious` flag of `x`'s owner. -/
def F (x y : Word) (sx : Bool) : Prop :=
  x = y ∨
  (∃ w, y = x ++ w ∧ 1 ≤ w.length ∧ w.length ≤ 2) ∨
  (∃ p c, x = p ++ [false] ∧ y = p ++ [true, c]) ∨
  (∃ p w, x = p ++ [true] ∧ y = p ++ false :: w ∧ w.length ≤ 3) ∨
  (∃ w, y = x ++ w ∧ 3 ≤ w.length ∧ w.length ≤ 6 ∧ sx = true)

/-- The forms of Lemma 6 of [Casteigts et al.], up to swapping the two neighbours. -/
def Form (x y : Word) (sx sy : Bool) : Prop := F x y sx ∨ F y x sy

theorem Form.symm {x y : Word} {sx sy : Bool} (h : Form x y sx sy) : Form y x sy sx := Or.symm h

/-- Abstract action of a node in a phase. -/
inductive Act
  /-- delete `k` letters (rules 1, 2) -/
  | del (k : ℕ)
  /-- change the last letter `0` into `1` (rule 3) -/
  | chg
  /-- append a letter (rules 4, 5 or the candidate's own bit) -/
  | app (b : Bool)
  /-- no modification -/
  | null

namespace Act

/-- The effect of an action on the prefix. -/
def apply : Act → Word → Word
  | del k, x => x.take (x.length - k)
  | chg, x => x.dropLast ++ [true]
  | app b, x => x ++ [b]
  | null, x => x

/-- Is the action a deletion (then the node is suspicious in the next phase)? -/
def isDel : Act → Bool
  | del _ => true
  | _ => false

end Act

/-- The constraints that the neighbour with prefix `y` (suspicious flag `sy`) imposes on the action
`a` of a node with prefix `x` (suspicious flag `sx`), under the rules with the largest-deletion
choice, together with the facts that a suspicious node deletes or changes next (Lemma 2 of
[Casteigts et al.]) and that deletions remove at most 3 letters (Corollary 7). -/
structure Allowed (a : Act) (x : Word) (sx : Bool) (y : Word) (sy : Bool) : Prop where
  susp : sx = true → a.isDel = true ∨ a = .chg
  del_bound : ∀ k, a = .del k → 1 ≤ k ∧ k ≤ 3 ∧ k ≤ x.length
  chg_last : a = .chg → ∃ z, x = z ++ [false]
  r1 : sy = true → y <+: x → y.length < x.length → ∃ k, a = .del k ∧ min (x.length - y.length) 3 ≤ k
  r2 : ∀ z w y', x = z ++ false :: w → y = z ++ true :: y' → w ≠ [] →
    ∃ k, a = .del k ∧ w.length ≤ k
  r3 : ∀ z y', x = z ++ [false] → y = z ++ true :: y' → a.isDel = true ∨ a = .chg
  r4 : ∀ w, y = x ++ true :: w → a.isDel = true ∨ a = .chg ∨ a = .app true
  r5 : ∀ w, y = x ++ false :: w → a ≠ .null

section helpers

theorem form_of_prefix {x y : Word} {sx sy : Bool} (h : x <+: y)
    (hl : y.length ≤ x.length + 2 ∨ (y.length ≤ x.length + 6 ∧ sx = true)) :
    Form x y sx sy := by
  obtain ⟨w, rfl⟩ := h
  simp only [List.length_append] at hl
  left
  rcases Nat.lt_or_ge w.length 1 with h0 | h0
  · left; simp [List.length_eq_zero_iff.1 (by omega : w.length = 0)]
  rcases Nat.lt_or_ge w.length 3 with h1 | h1
  · right; left; exact ⟨w, rfl, h0, by omega⟩
  · right; right; right; right
    exact ⟨w, rfl, h1, by omega, by rcases hl with hl | hl <;> [omega; exact hl.2]⟩

/-- Two prefixes of a common word are in one of the prefix forms (1, 2, 5), given length bounds. -/
theorem form_of_common {x y z : Word} {sx sy : Bool} (hx : x <+: z) (hy : y <+: z)
    (h1 : x.length ≤ y.length → y.length ≤ x.length + 2 ∨ (y.length ≤ x.length + 6 ∧ sx = true))
    (h2 : y.length ≤ x.length → x.length ≤ y.length + 2 ∨ (x.length ≤ y.length + 6 ∧ sy = true)) :
    Form x y sx sy := by
  rcases le_total x.length y.length with h | h
  · exact form_of_prefix (List.prefix_of_prefix_length_le hx hy h) (h1 h)
  · exact (form_of_prefix (List.prefix_of_prefix_length_le hy hx h) (h2 h)).symm

@[simp] theorem Act.isDel_del (k : ℕ) : (Act.del k).isDel = true := rfl
@[simp] theorem Act.isDel_chg : Act.chg.isDel = false := rfl
@[simp] theorem Act.isDel_app (b : Bool) : (Act.app b).isDel = false := rfl
@[simp] theorem Act.isDel_null : Act.null.isDel = false := rfl

theorem Act.del_prefix (k : ℕ) (x : Word) : (Act.del k).apply x <+: x := List.take_prefix _ x

@[simp] theorem Act.del_length (k : ℕ) (x : Word) : ((Act.del k).apply x).length = x.length - k := by
  simp [Act.apply]

theorem Act.del_prefix_of_le {k : ℕ} {p q : Word} (hk : q.length ≤ k) :
    (Act.del k).apply (p ++ q) <+: p := by
  simp only [Act.apply, List.length_append]
  rw [List.take_append_of_le_length (by omega)]
  exact List.take_prefix _ _

theorem Act.chg_apply (z : Word) : Act.chg.apply (z ++ [false]) = z ++ [true] := by
  simp [Act.apply]

@[simp] theorem Act.app_apply (b : Bool) (x : Word) : (Act.app b).apply x = x ++ [b] := rfl
@[simp] theorem Act.null_apply (x : Word) : Act.null.apply x = x := rfl

theorem prefix_append_self (x w : Word) : x <+: x ++ w := List.prefix_append x w

theorem form4_of (p w : Word) (hw : w.length ≤ 3) (s s' : Bool) :
    Form (p ++ [true]) (p ++ false :: w) s s' :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, w, rfl, rfl, hw⟩))))

theorem form3_of (p : Word) (c : Bool) (s s' : Bool) :
    Form (p ++ [false]) (p ++ [true, c]) s s' :=
  Or.inl (Or.inr (Or.inr (Or.inl ⟨p, c, rfl, rfl⟩)))

theorem form_refl (x : Word) (s s' : Bool) : Form x x s s' := Or.inl (Or.inl rfl)

theorem Act.del_apply_append {k : ℕ} {p q : Word} (hk : k ≤ q.length) :
    (Act.del k).apply (p ++ q) = p ++ (Act.del k).apply q := by
  simp only [Act.apply, List.length_append]
  rw [List.take_append, List.take_of_length_le (by omega)]
  congr 2; omega

theorem Act.chg_apply_append {p q : Word} (hq : q ≠ []) :
    Act.chg.apply (p ++ q) = p ++ Act.chg.apply q := by
  simp [Act.apply, List.dropLast_append_of_ne_nil hq]

@[simp] theorem Act.del_length_le {k : ℕ} {q : Word} : ((Act.del k).apply q).length ≤ q.length := by
  simp

theorem Act.chg_length {q : Word} (hq : q ≠ []) : (Act.chg.apply q).length = q.length := by
  simp [Act.apply]; have := List.length_pos_of_ne_nil hq; omega

/-- If `x ++ w = z ++ [a]` with `w` nonempty, then `x` is a prefix of `z`. -/
theorem prefix_of_append_eq {x w z : Word} {a : Bool} (h : x ++ w = z ++ [a]) (hw : w ≠ []) :
    x <+: z := by
  have hl := congrArg List.length h
  simp only [List.length_append, List.length_singleton] at hl
  have := List.length_pos_of_ne_nil hw
  exact List.prefix_of_prefix_length_le (h ▸ prefix_append_self x w) (prefix_append_self z _)
    (by omega)

end helpers

/-! ### Form 1: equal prefixes -/

theorem step_eq {x : Word} {sx sy : Bool} {au av : Act}
    (hu : Allowed au x sx x sy) (hv : Allowed av x sy x sx) :
    Form (au.apply x) (av.apply x) au.isDel av.isDel := by
  cases au with
  | del i =>
    obtain ⟨hi1, hi3, hix⟩ := hu.del_bound i rfl
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      exact form_of_common (Act.del_prefix i x) (Act.del_prefix j x) (by simp; omega)
        (by simp; omega)
    | chg =>
      obtain ⟨z, rfl⟩ := hv.chg_last rfl
      rw [Act.chg_apply]
      refine form_of_prefix ((Act.del_prefix_of_le (by simp; omega)).trans
        (prefix_append_self z _)) ?_
      simp; omega
    | app b =>
      refine form_of_prefix ((Act.del_prefix i x).trans (prefix_append_self x _)) ?_
      simp; omega
    | null =>
      refine form_of_prefix (Act.del_prefix i x) ?_
      simp; omega
  | chg =>
    obtain ⟨z, rfl⟩ := hu.chg_last rfl
    rw [Act.chg_apply]
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      refine (form_of_prefix ((Act.del_prefix_of_le (by simp; omega)).trans
        (prefix_append_self z _)) ?_).symm
      simp; omega
    | chg => rw [Act.chg_apply]; exact form_refl _ _ _
    | app b =>
      simpa using form4_of z [b] (by simp) false false
    | null => simpa using form4_of z [] (by simp) false false
  | app b =>
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      refine (form_of_prefix ((Act.del_prefix j x).trans (prefix_append_self x _)) ?_).symm
      simp; omega
    | chg =>
      obtain ⟨z, rfl⟩ := hv.chg_last rfl
      rw [Act.chg_apply]
      simpa using (form4_of z [b] (by simp) false false).symm
    | app c =>
      cases b <;> cases c
      · exact form_refl _ _ _
      · simpa using (form4_of x [] (by simp) false false).symm
      · simpa using form4_of x [] (by simp) false false
      · exact form_refl _ _ _
    | null =>
      refine (form_of_prefix (prefix_append_self x _) ?_).symm
      simp
  | null =>
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      refine (form_of_prefix (Act.del_prefix j x) ?_).symm
      simp; omega
    | chg =>
      obtain ⟨z, rfl⟩ := hv.chg_last rfl
      rw [Act.chg_apply]
      simpa using (form4_of z [] (by simp) false false).symm
    | app c =>
      refine form_of_prefix (prefix_append_self x _) ?_
      simp
    | null => exact form_refl _ _ _


/-! ### Form 2: `y = x w` with `1 ≤ |w| ≤ 2` -/

theorem step_two {x w : Word} {sx sy : Bool} {au av : Act} (hw1 : 1 ≤ w.length)
    (hw2 : w.length ≤ 2) (hu : Allowed au x sx (x ++ w) sy) (hv : Allowed av (x ++ w) sy x sx) :
    Form (au.apply x) (av.apply (x ++ w)) au.isDel av.isDel := by
  have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
  cases au with
  | del i =>
    obtain ⟨hi1, hi3, hix⟩ := hu.del_bound i rfl
    have hx' : (Act.del i).apply x <+: x ++ w := (Act.del_prefix i x).trans (prefix_append_self x w)
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      exact form_of_common hx' (Act.del_prefix j _) (by simp; omega) (by simp; omega)
    | chg =>
      obtain ⟨z, hz⟩ := hv.chg_last rfl
      have hl := congrArg List.length hz
      simp only [List.length_append, List.length_singleton] at hl
      rw [hz, Act.chg_apply]
      refine form_of_prefix (((Act.del_prefix i x).trans (prefix_of_append_eq hz hwne)).trans
        (prefix_append_self z _)) ?_
      simp; omega
    | app b =>
      refine form_of_prefix (hx'.trans (prefix_append_self _ _)) ?_
      simp; omega
    | null =>
      refine form_of_prefix hx' ?_
      simp; omega
  | chg =>
    obtain ⟨z, rfl⟩ := hu.chg_last rfl
    rw [Act.chg_apply]
    have hy : z ++ [false] ++ w = z ++ false :: w := by simp
    rw [hy]
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      rcases Nat.lt_or_ge w.length j with hj | hj
      · refine (form_of_prefix ((Act.del_prefix_of_le (by simp; omega)).trans
          (prefix_append_self z _)) ?_).symm
        simp; omega
      · rw [Act.del_apply_append (by simp; omega),
          show false :: w = [false] ++ w from rfl, Act.del_apply_append hj]
        simpa using form4_of z ((Act.del j).apply w) (by simp; omega) false true
    | chg =>
      rw [show false :: w = [false] ++ w from rfl, ← List.append_assoc,
        Act.chg_apply_append hwne, List.append_assoc]
      simpa using form4_of z (Act.chg.apply w) (by rw [Act.chg_length hwne]; omega) false false
    | app d =>
      simpa using form4_of z (w ++ [d]) (by simp; omega) false false
    | null =>
      simpa using form4_of z w (by omega) false false
  | app b =>
    obtain ⟨c, w', rfl⟩ := List.exists_cons_of_ne_nil hwne
    simp only [List.length_cons] at hw1 hw2
    have hcb : c = true → b = true := by
      rintro rfl
      rcases hu.r4 w' rfl with h | h | h
      · simp at h
      · simp at h
      · simpa using h
    by_cases hbc : b = c
    · subst hbc
      have hx' : x ++ [b] <+: x ++ b :: w' := by simp
      cases av with
      | del j =>
        obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
        exact form_of_common hx' (Act.del_prefix j _) (by simp; omega) (by simp; omega)
      | chg =>
        obtain ⟨z, hz⟩ := hv.chg_last rfl
        rw [hz, Act.chg_apply]
        match w', hw2, hz with
        | [], _, hz =>
          have : x = z ∧ b = false := by simpa using hz
          obtain ⟨rfl, rfl⟩ := this
          simpa using (form4_of x [] (by simp) false false).symm
        | [e], _, hz =>
          have : z = x ++ [b] ∧ e = false := by
            constructor
            · have h2 := congrArg List.dropLast hz
              simpa using h2.symm
            · have h2 := congrArg List.getLast? hz; simpa using h2
          obtain ⟨rfl, rfl⟩ := this
          refine form_of_prefix (prefix_append_self _ _) ?_
          simp
      | app d =>
        refine form_of_prefix (hx'.trans (prefix_append_self _ _)) ?_
        simp; omega
      | null =>
        refine form_of_prefix hx' ?_
        simp; omega
    · have hc : c = false := by
        cases c
        · rfl
        · exact absurd (hcb rfl) (by rintro rfl; exact hbc rfl)
      have hb : b = true := by subst hc; cases b <;> simp_all
      subst hc hb
      simp only [Act.app_apply]
      cases av with
      | del j =>
        obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
        rcases Nat.lt_or_ge w'.length j with hj | hj
        · refine (form_of_prefix ((Act.del_prefix_of_le (by simp; omega)).trans
            (prefix_append_self x _)) ?_).symm
          simp; omega
        · rw [Act.del_apply_append (by simp; omega),
            show false :: w' = [false] ++ w' from rfl, Act.del_apply_append hj]
          simpa using form4_of x ((Act.del j).apply w') (by simp; omega) false true
      | chg =>
        rcases eq_or_ne w' [] with rfl | hw'
        · simpa [Act.chg_apply] using form_refl (x ++ [true]) false false
        · rw [show false :: w' = [false] ++ w' from rfl, ← List.append_assoc,
            Act.chg_apply_append hw', List.append_assoc]
          simpa using form4_of x (Act.chg.apply w') (by rw [Act.chg_length hw']; omega) false false
      | app d =>
        simpa using form4_of x (w' ++ [d]) (by simp; omega) false false
      | null =>
        simpa using form4_of x w' (by omega) false false
  | null =>
    exfalso
    obtain ⟨c, w', rfl⟩ := List.exists_cons_of_ne_nil hwne
    cases c
    · exact hu.r5 w' rfl rfl
    · rcases hu.r4 w' rfl with h | h | h <;> simp at h


/-! ### Form 3: `x = p 0`, `y = p 1 c` -/

theorem step_three {p : Word} {c sx sy : Bool} {au av : Act}
    (hu : Allowed au (p ++ [false]) sx (p ++ [true, c]) sy)
    (hv : Allowed av (p ++ [true, c]) sy (p ++ [false]) sx) :
    Form (au.apply (p ++ [false])) (av.apply (p ++ [true, c])) au.isDel av.isDel := by
  have hpy : p <+: p ++ [true, c] := prefix_append_self _ _
  cases au with
  | del i =>
    obtain ⟨hi1, hi3, hix⟩ := hu.del_bound i rfl
    have hx' : (Act.del i).apply (p ++ [false]) <+: p := Act.del_prefix_of_le (by simp; omega)
    simp only [List.length_append, List.length_singleton] at hix
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      exact form_of_common (hx'.trans hpy) (Act.del_prefix j _) (by simp; omega) (by simp; omega)
    | chg =>
      obtain ⟨z, hz⟩ := hv.chg_last rfl
      rw [hz, Act.chg_apply]
      have hl := congrArg List.length hz
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      have hpz : p <+: z := List.prefix_of_prefix_length_le (hz ▸ hpy) (prefix_append_self z _)
        (by omega)
      refine form_of_prefix ((hx'.trans hpz).trans (prefix_append_self z _)) ?_
      simp; omega
    | app d =>
      refine form_of_prefix ((hx'.trans hpy).trans (prefix_append_self _ _)) ?_
      simp; omega
    | null =>
      refine form_of_prefix (hx'.trans hpy) ?_
      simp; omega
  | chg =>
    rw [Act.chg_apply]
    have hx' : p ++ [true] <+: p ++ [true, c] := by simp
    cases av with
    | del j =>
      obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
      exact form_of_common hx' (Act.del_prefix j _) (by simp; omega) (by simp; omega)
    | chg =>
      obtain ⟨z, hz⟩ := hv.chg_last rfl
      rw [hz, Act.chg_apply]
      have hl := congrArg List.length hz
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      have hpz : p ++ [true] <+: z := List.prefix_of_prefix_length_le (hz ▸ hx')
        (prefix_append_self z _) (by simp; omega)
      refine form_of_prefix (hpz.trans (prefix_append_self z _)) ?_
      simp at hl ⊢; omega
    | app d =>
      refine form_of_prefix (hx'.trans (prefix_append_self _ _)) ?_
      simp
    | null =>
      refine form_of_prefix hx' ?_
      simp
  | app b => rcases hu.r3 p [c] rfl rfl with h | h <;> simp at h
  | null => rcases hu.r3 p [c] rfl rfl with h | h <;> simp at h

theorem Act.del_apply_append_eq {k : ℕ} {p q : Word} (hk : k = q.length) :
    (Act.del k).apply (p ++ q) = p := by
  simp [Act.apply, hk]

/-! ### Form 4: `x = p 1`, `y = p 0 w` with `|w| ≤ 3` -/

theorem step_four {p w : Word} {sx sy : Bool} {au av : Act} (hw : w.length ≤ 3)
    (hu : Allowed au (p ++ [true]) sx (p ++ false :: w) sy)
    (hv : Allowed av (p ++ false :: w) sy (p ++ [true]) sx) :
    Form (au.apply (p ++ [true])) (av.apply (p ++ false :: w)) au.isDel av.isDel := by
  have hy : p ++ false :: w = (p ++ [false]) ++ w := by simp
  have hauchg : au ≠ .chg := by
    rintro rfl
    obtain ⟨z, hz⟩ := hu.chg_last rfl
    have := congrArg List.getLast? hz; simp at this
  cases av with
  | del j =>
    obtain ⟨hj1, hj3, hjx⟩ := hv.del_bound j rfl
    have hjw : w.length ≤ j := by
      rcases eq_or_ne w [] with rfl | hw0
      · simp
      · obtain ⟨k, hk, hk'⟩ := hv.r2 p w [] rfl rfl hw0
        cases hk; exact hk'
    have hy' : (Act.del j).apply (p ++ false :: w) <+: p ++ [false] := by
      rw [hy]; exact Act.del_prefix_of_le hjw
    cases au with
    | del i =>
      obtain ⟨hi1, hi3, hix⟩ := hu.del_bound i rfl
      have hx' : (Act.del i).apply (p ++ [true]) <+: p := Act.del_prefix_of_le (by simp; omega)
      exact form_of_common (hx'.trans (prefix_append_self _ _)) hy' (by simp; omega)
        (by simp; omega)
    | chg => exact absurd rfl hauchg
    | app b =>
      rcases hjw.lt_or_eq with hjw | rfl
      · have : (Act.del j).apply (p ++ false :: w) <+: p := Act.del_prefix_of_le (by simp; omega)
        have h2 : (Act.app b).apply (p ++ [true]) = p ++ [true, b] := by simp
        rw [h2]
        refine (form_of_prefix (this.trans (prefix_append_self p [true, b])) ?_).symm
        simp; omega
      · rw [hy, Act.del_apply_append_eq rfl]
        simpa using (form3_of p b true false).symm
    | null =>
      rcases hjw.lt_or_eq with hjw | rfl
      · have : (Act.del j).apply (p ++ false :: w) <+: p := Act.del_prefix_of_le (by simp; omega)
        refine (form_of_prefix (this.trans (prefix_append_self p _)) ?_).symm
        simp; omega
      · rw [hy, Act.del_apply_append_eq rfl]
        simpa using form4_of p [] (by simp) false true
  | chg =>
    have hw0 : w = [] := by
      by_contra hw0
      obtain ⟨k, hk, -⟩ := hv.r2 p w [] rfl rfl hw0
      cases hk
    subst hw0
    rw [show p ++ [false] = p ++ [false] from rfl, Act.chg_apply]
    cases au with
    | del i =>
      obtain ⟨hi1, hi3, hix⟩ := hu.del_bound i rfl
      refine form_of_prefix (Act.del_prefix i _) ?_
      simp at hix ⊢; omega
    | chg => exact absurd rfl hauchg
    | app b =>
      refine (form_of_prefix (prefix_append_self _ _) ?_).symm
      simp
    | null => exact form_refl _ _ _
  | app d =>
    exfalso
    rcases eq_or_ne w [] with rfl | hw0
    · rcases hv.r3 p [] rfl rfl with h | h <;> simp at h
    · obtain ⟨k, hk, -⟩ := hv.r2 p w [] rfl rfl hw0
      cases hk
  | null =>
    exfalso
    rcases eq_or_ne w [] with rfl | hw0
    · rcases hv.r3 p [] rfl rfl with h | h <;> simp at h
    · obtain ⟨k, hk, -⟩ := hv.r2 p w [] rfl rfl hw0
      cases hk

/-! ### Form 5: `y = x w`, `3 ≤ |w| ≤ 6`, `x` suspicious -/

theorem step_five {x w : Word} {sy : Bool} {au av : Act} (hw3 : 3 ≤ w.length)
    (hw6 : w.length ≤ 6) (hu : Allowed au x true (x ++ w) sy)
    (hv : Allowed av (x ++ w) sy x true) :
    Form (au.apply x) (av.apply (x ++ w)) au.isDel av.isDel := by
  obtain ⟨k, rfl, hk⟩ := hv.r1 rfl (prefix_append_self x w) (by simp; omega)
  obtain ⟨hk1, hk3, -⟩ := hv.del_bound k rfl
  simp only [List.length_append, Nat.add_sub_cancel_left] at hk
  have hk3' : k = 3 := by omega
  subst hk3'
  rw [Act.del_apply_append hw3]
  rcases hu.susp rfl with h | h
  · cases au with
    | del i =>
      obtain ⟨hi1, hi3, hix⟩ := hu.del_bound i rfl
      refine form_of_prefix ((Act.del_prefix i x).trans (prefix_append_self x _)) ?_
      simp; omega
    | _ => simp at h
  · subst h
    obtain ⟨z, rfl⟩ := hu.chg_last rfl
    rw [Act.chg_apply]
    simpa using form4_of z ((Act.del 3).apply w) (by simp; omega) false true


/-! ### The one-edge step -/

theorem step_F {x y : Word} {sx sy : Bool} {au av : Act} (hF : F x y sx)
    (hu : Allowed au x sx y sy) (hv : Allowed av y sy x sx) :
    Form (au.apply x) (av.apply y) au.isDel av.isDel := by
  rcases hF with rfl | ⟨w, rfl, h1, h2⟩ | ⟨p, c, rfl, rfl⟩ | ⟨p, w, rfl, rfl, hw⟩ |
    ⟨w, rfl, h3, h6, rfl⟩
  · exact step_eq hu hv
  · exact step_two h1 h2 hu hv
  · exact step_three hu hv
  · exact step_four hw hu hv
  · exact step_five h3 h6 hu hv

/-- **One-edge step of Lemma 6 of [Casteigts et al.]**: if the prefixes of two neighbours are in one
of the five forms and both actions respect the constraints imposed by the other endpoint, the new
prefixes are again in one of the five forms. -/
theorem form_step {x y : Word} {sx sy : Bool} {au av : Act} (hF : Form x y sx sy)
    (hu : Allowed au x sx y sy) (hv : Allowed av y sy x sx) :
    Form (au.apply x) (av.apply y) au.isDel av.isDel := by
  rcases hF with hF | hF
  · exact step_F hF hu hv
  · exact (step_F hF hv hu).symm

end Podc.BeepingLeaderElection
