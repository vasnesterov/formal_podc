import Papers.PODC2020.NonEquivocation.Exec

/-!
# `t + 1` rounds are necessary (Section 6, end)

Madsen–Debois, *On the Subject of Non-Equivocation* (PODC 2020), end of Section 6: the round
complexity `t + 1` of the algorithms is optimal. We prove that with `k ≤ t` rounds interactive
consistency cannot be solved even against (send-)omission faults, as soon as `n ≥ t + 2`; since omission
runs are weakly non-equivocating (`wne_of_omission`), the same holds under weak non-equivocation.

The proof is the classical chain argument (Dolev–Strong / Aguilera–Toueg style) over *omission runs*:
a run is given by the input `x` of a fixed source `s` (everybody else has a fixed filler input) and an
omission pattern `O r a b` ("the round-`r` messages of `a` to `b` are omitted").

* `RoundLB.claim j`: two runs whose patterns (with senders in `F`) agree on all rounds `≤ k - j` lead
  to the same decisions of the correct processes, provided `|F| + j ≤ t + 1` and `|F| + j + 1 ≤ n`.
  The induction step changes the round-`r` messages into one receiver `b` at a time, silencing `b`
  in all later rounds (by the induction hypothesis with the faulty set `F ∪ {b}`), so that only `b`'s
  view changes (`RoundLB.σ_eq_swap`).
* With `F = {s}` and `j = k`, the run "`s` behaves correctly" is connected to the run "`s` is silent",
  in which the input of `s` is invisible to everybody else; validity then gives a contradiction.
-/

namespace NonEquivocation

namespace RoundLB

variable {P V : Type*} [OmitVal V] [DecidableEq P]

/-- An omission pattern: `O r a b` means that the round-`r` messages of `a` to `b` are omitted. -/
abbrev Pat (P : Type*) := ℕ → P → P → Prop

/-- Omission runs: world `(x, O)` has input `x` at the source `s`, input `c` elsewhere, and omission
pattern `O`; nobody imitates another world. -/
def sys (s : P) (c : V) : ExecSys (V × Pat P) P V where
  input w y := if y = s then some w.1 else some c
  nb w _ := w
  om w := w.2

variable (s : P) (c : V)

omit [OmitVal V] in
@[simp] lemma sys_input (w : V × Pat P) (y : P) :
    (sys s c).input w y = if y = s then some w.1 else some c := rfl

omit [OmitVal V] in
@[simp] lemma sys_nb (w : V × Pat P) (y : P) : (sys s c).nb w y = w := rfl

omit [OmitVal V] in
@[simp] lemma sys_om (w : V × Pat P) : (sys s c).om w = w.2 := rfl

open Classical in
lemma σ_cons_cons' (x : V) (O : Pat P) (y z : P) (l : List P) :
    (sys s c).σ (x, O) (y :: z :: l) =
      if O (l.length + 1) z y then none else some (rep ((sys s c).σ (x, O) (z :: l))) := by
  rw [ExecSys.σ_cons_cons]; rfl

/-- Every omission run in which only processes of `F` omit lies in the omission fault model with
faulty set `F`. -/
lemma omission_of [Fintype P] (k : ℕ) (x : V) {O : Pat P} {F : Finset P}
    (hO : ∀ r a b, O r a b → a ∈ F) : omission k F ((sys s c).σ (x, O)) := by
  refine ⟨(sys s c).nonFaulty_of ?_ k _, ?_⟩
  · intro y hy
    exact ⟨rfl, fun r b h => hy (hO r y b h)⟩
  · intro y z l _ _
    rw [σ_cons_cons']
    split_ifs <;> simp

lemma input_ne_none (x : V) (O : Pat P) (q : P) : (sys s c).σ (x, O) [q] ≠ none := by
  simp only [ExecSys.σ_single, sys_input]
  split_ifs <;> simp

/-- The swap lemma: if two patterns agree on rounds `≤ k` except for round `r` into receiver `b`, and
both silence `b` in rounds `r + 1, …, k`, then they produce the same message map on chains of
length `≤ k + 1` starting at a process `y ≠ b` (and on chains of length `≤ r` starting at `b`). -/
lemma σ_eq_swap (x : V) {O₁ O₂ : Pat P} {k r : ℕ} {b : P}
    (hag : ∀ r' a d, r' ≤ k → ¬ (r' = r ∧ d = b) → (O₁ r' a d ↔ O₂ r' a d))
    (hsil : ∀ r' d, r < r' → r' ≤ k → O₁ r' b d ∧ O₂ r' b d) :
    ∀ (l : List P) (y : P), l.length ≤ k → (y ≠ b ∨ l.length < r) →
      (sys s c).σ (x, O₁) (y :: l) = (sys s c).σ (x, O₂) (y :: l) := by
  intro l
  induction l with
  | nil => intro y _ _; simp
  | cons z l ih =>
    intro y hlen hyb
    simp only [List.length_cons] at hlen hyb
    rw [σ_cons_cons', σ_cons_cons']
    have hiff : O₁ (l.length + 1) z y ↔ O₂ (l.length + 1) z y :=
      hag _ _ _ hlen (by rintro ⟨h1, h2⟩; rcases hyb with h | h; exacts [h h2, by omega])
    by_cases h : O₁ (l.length + 1) z y
    · simp [h, hiff.1 h]
    · have h' : ¬ O₂ (l.length + 1) z y := fun h2 => h (hiff.2 h2)
      simp only [h, h', ite_false]
      rw [ih z (by omega)]
      by_cases hzb : z = b
      · subst hzb
        refine Or.inr (Nat.lt_of_not_le fun hr => ?_)
        exact h (hsil _ _ (by omega) hlen).1
      · exact Or.inl hzb

lemma view_eq_swap (x : V) {O₁ O₂ : Pat P} {k r : ℕ} {b p : P}
    (hag : ∀ r' a d, r' ≤ k → ¬ (r' = r ∧ d = b) → (O₁ r' a d ↔ O₂ r' a d))
    (hsil : ∀ r' d, r < r' → r' ≤ k → O₁ r' b d ∧ O₂ r' b d) (hp : p ≠ b) :
    view k ((sys s c).σ (x, O₁)) p = view k ((sys s c).σ (x, O₂)) p := by
  funext l
  unfold view
  split_ifs with hl
  · exact σ_eq_swap s c x hag hsil l p hl (Or.inl hp)
  · rfl

/-- Patterns agreeing on rounds `≤ k` give the same views after `k` rounds. -/
lemma view_eq_of_agree (x : V) {O₁ O₂ : Pat P} {k : ℕ}
    (hag : ∀ r' a d, r' ≤ k → (O₁ r' a d ↔ O₂ r' a d)) (p : P) :
    view k ((sys s c).σ (x, O₁)) p = view k ((sys s c).σ (x, O₂)) p := by
  funext l
  unfold view
  split_ifs with hl
  · exact σ_eq_swap s c x (r := k + 1) (b := p) (fun r' a d h _ => hag r' a d h)
      (fun r' d h1 h2 => by omega) l p hl (Or.inr (by omega))
  · rfl

/-- The pattern in which the source `s` is silent in every round. -/
def silent : Pat P := fun r a _ => a = s ∧ 0 < r

/-- When `s` is silent, its input is invisible to everybody else. -/
lemma σ_silent (x x' : V) :
    ∀ (l : List P) (y : P), y ≠ s →
      (sys s c).σ (x, silent s) (y :: l) = (sys s c).σ (x', silent s) (y :: l) := by
  intro l
  induction l with
  | nil => intro y hy; simp [hy]
  | cons z l ih =>
    intro y _
    rw [σ_cons_cons', σ_cons_cons']
    by_cases hz : z = s
    · simp [silent, hz]
    · rw [ih z hz]

section Claim

variable [Fintype P] {k t : ℕ} (A : Alg P V)

/-- The decision of `p` about the source `s` in the run `(x, O)`. -/
noncomputable def dec (k : ℕ) (x : V) (O : Pat P) (p : P) : V :=
  A p (view k ((sys s c).σ (x, O)) p) s

variable {s c A}

lemma dec_agree (hA : SolvesIC omission k t A) (x : V) {O : Pat P} {F : Finset P}
    (hF : F.card ≤ t) (hO : ∀ r a b, O r a b → a ∈ F) {p q : P} (hp : p ∉ F) (hq : q ∉ F) :
    dec s c A k x O p = dec s c A k x O q :=
  (hA F _ hF (omission_of s c k x hO) (fun q _ => input_ne_none s c x O q)).2 p q s hp hq

/-- The chain claim: patterns with senders in `F` agreeing on rounds `≤ k - j` yield the same
decisions of all processes outside `F`, provided `|F| + j ≤ t + 1` and `|F| + j + 1 ≤ n`. -/
theorem claim (hA : SolvesIC omission k t A) (j : ℕ) :
    ∀ (F : Finset P) (O O' : Pat P) (x : V), F.card + j ≤ t + 1 →
      F.card + j + 1 ≤ Fintype.card P → (∀ r a b, O r a b → a ∈ F) →
      (∀ r a b, O' r a b → a ∈ F) → (∀ r a b, r ≤ k - j → (O r a b ↔ O' r a b)) →
      ∀ p ∉ F, dec s c A k x O p = dec s c A k x O' p := by
  induction j with
  | zero =>
    intro F O O' x _ _ _ _ hag p _
    unfold dec
    rw [view_eq_of_agree s c x (k := k) (fun r a d h => hag r a d (by omega)) p]
  | succ j ih =>
    intro F O O' x h1 h2 hO hO' hag p hp
    by_cases hjk : k ≤ j
    · exact ih F O O' x (by omega) (by omega) hO hO' (fun r a b hr => hag r a b (by omega)) p hp
    set r := k - j with hr
    have hFt : F.card ≤ t := by omega
    let mid : Finset P → Pat P := fun B r' a d => if r' = r ∧ d ∈ B then O' r' a d else O r' a d
    have hmid : ∀ B r' a d, mid B r' a d → a ∈ F := by
      intro B r' a d h
      simp only [mid] at h
      split_ifs at h
      · exact hO' _ _ _ h
      · exact hO _ _ _ h
    have key : ∀ (B : Finset P) (b : P), b ∉ B → ∀ p ∉ F,
        dec s c A k x (mid B) p = dec s c A k x (mid (insert b B)) p := by
      intro B b hb p hp
      set G := insert b F with hG
      have hGc : G.card ≤ F.card + 1 := Finset.card_insert_le _ _
      obtain ⟨c', -, hc'⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := G) (t := Finset.univ) (by rw [Finset.card_univ]; omega)
      have hc'b : c' ≠ b := fun h => hc' (by rw [h, hG]; exact Finset.mem_insert_self _ _)
      have hc'F : c' ∉ F := fun h => hc' (Finset.mem_insert_of_mem h)
      let S : Finset P → Pat P := fun B' r' a d => mid B' r' a d ∨ (a = b ∧ r < r')
      have hS : ∀ B', ∀ r' a d, S B' r' a d → a ∈ G := by
        intro B' r' a d h
        rcases h with h | ⟨rfl, -⟩
        · exact Finset.mem_insert_of_mem (hmid _ _ _ _ h)
        · exact Finset.mem_insert_self _ _
      have step : ∀ B', dec s c A k x (mid B') c' = dec s c A k x (S B') c' := by
        intro B'
        refine ih G (mid B') (S B') x (by omega) (by omega)
          (fun r' a d h => Finset.mem_insert_of_mem (hmid _ _ _ _ h)) (hS B') ?_ c' hc'
        intro r' a d hr'
        simp only [S]
        constructor
        · exact Or.inl
        · rintro (h | ⟨-, h⟩)
          · exact h
          · omega
      have swap : dec s c A k x (S B) c' = dec s c A k x (S (insert b B)) c' := by
        unfold dec
        rw [view_eq_swap s c x (k := k) (r := r) (b := b) ?_ ?_ hc'b]
        · intro r' a d _ hne
          simp only [S, mid]
          by_cases hrr : r' = r
          · have hd : d ≠ b := fun h => hne ⟨hrr, h⟩
            simp [hrr, Finset.mem_insert, hd]
          · simp [hrr]
        · intro r' d h _
          exact ⟨Or.inr ⟨rfl, h⟩, Or.inr ⟨rfl, h⟩⟩
      rw [dec_agree hA x hFt (hmid B) hp hc'F, step, swap, ← step,
        dec_agree hA x hFt (hmid _) hp hc'F]
    have chain : ∀ B : Finset P, ∀ p ∉ F, dec s c A k x O p = dec s c A k x (mid B) p := by
      intro B
      induction B using Finset.induction_on with
      | empty =>
        intro p _
        have : mid ∅ = O := by funext r' a d; simp [mid]
        rw [this]
      | insert b B hb ihB => intro p hp; rw [ihB p hp, key B b hb p hp]
    rw [chain Finset.univ p hp]
    refine ih F (mid Finset.univ) O' x (by omega) (by omega) (hmid _) hO' ?_ p hp
    intro r' a d hr'
    simp only [mid, Finset.mem_univ, and_true]
    split_ifs with h
    · exact Iff.rfl
    · exact hag r' a d (by omega)

end Claim

end RoundLB

open RoundLB in
/-- Section 6 (round tightness): with `k ≤ t` rounds, interactive consistency cannot be solved even
against send-omission faults (hence not under weak non-equivocation), as soon as `n ≥ t + 2`. -/
theorem not_solvesIC_omission_of_le {P V : Type*} [Fintype P] [DecidableEq P] [OmitVal V]
    [Nontrivial V] {k t : ℕ} (hk : k ≤ t) (hn : t + 2 ≤ Fintype.card P) (A : Alg P V) :
    ¬ SolvesIC omission k t A := by
  intro hA
  obtain ⟨v, u, hvu⟩ := exists_pair_ne V
  have hP : 0 < Fintype.card P := by omega
  obtain ⟨s⟩ := Fintype.card_pos_iff.mp hP
  obtain ⟨c', hc'⟩ := Fintype.exists_ne_of_one_lt_card (by omega) s
  have hc's : c' ∉ ({s} : Finset P) := by simpa using hc'
  have hsil : ∀ r a b, silent s r a b → a ∈ ({s} : Finset P) := by
    intro r a b h; simp [h.1]
  have hnone : ∀ r a b, (fun _ _ _ => False : Pat P) r a b → a ∈ ({s} : Finset P) := by
    intro r a b h; exact h.elim
  have hag : ∀ r a b, r ≤ k - k →
      ((fun _ _ _ => False : Pat P) r a b ↔ silent s r a b) := by
    intro r a b hr; simp [silent]; omega
  have hcard : ({s} : Finset P).card + k ≤ t + 1 := by simp; omega
  have hcard' : ({s} : Finset P).card + k + 1 ≤ Fintype.card P := by simp; omega
  have e1 := claim (s := s) (c := v) hA k {s} _ _ v hcard hcard' hnone hsil hag c' hc's
  have e2 := claim (s := s) (c := v) hA k {s} _ _ u hcard hcard' hnone hsil hag c' hc's
  have e3 : dec s v A k v (silent s) c' = dec s v A k u (silent s) c' := by
    unfold dec
    congr 1
    funext l
    unfold view
    split_ifs
    · exact σ_silent s v v u l c' hc'
    · rfl
  have hval : ∀ x : V, x = dec s v A k x (fun _ _ _ => False) c' := by
    intro x
    have h := (hA ∅ _ (by simp) (omission_of s v k x (O := fun _ _ _ => False) (F := ∅)
      (fun _ _ _ h => h.elim)) (fun q _ => input_ne_none s v x _ q)).1 c' s
      (Finset.notMem_empty _) (Finset.notMem_empty _)
    simpa [dec] using h
  apply hvu
  rw [hval v, hval u, e1, e3, ← e2]

/-- Section 6 (round tightness) under weak non-equivocation: with `k ≤ t` rounds, interactive
consistency cannot be solved under weak non-equivocation as soon as `n ≥ t + 2`. -/
theorem not_solvesIC_wne_of_le {P V : Type*} [Fintype P] [DecidableEq P] [OmitVal V]
    [Nontrivial V] {k t : ℕ} (hk : k ≤ t) (hn : t + 2 ≤ Fintype.card P) (A : Alg P V) :
    ¬ SolvesIC wne k t A := by
  intro hA
  refine not_solvesIC_omission_of_le hk hn A ?_
  intro F σ hF hM hin
  exact hA F σ hF (wne_of_omission hM) hin

end NonEquivocation
