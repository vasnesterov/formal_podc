import Papers.PODC2022.RecoverableHarder.TypeT

/-!
# The type `S_n` of Proposition 21

`S_n` (`n ≥ 2`) has values `(winner, row)` with `winner ∈ {A, B}`, `0 ≤ row < n`; operations
`op_A`, `op_B` (Figure 6, both return `ack`) and `Read`. We define `SS k` (rows `Fin (k + 1)`,
winner `false` = A, `true` = B) and `Sn n := SS (n - 1)`.

* `SS.isRecording`: `SS k` is `(k+1)`-recording (Proposition 21);
* `SS.not_isDiscerning`: `SS k` is not `m`-discerning for `m ≥ k + 2` (Proposition 21).
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

/-- Responses of `S`: `ack`, or a value (of `Read`). -/
inductive SRes (k : ℕ) where
  | ack
  | val (s : Bool × Fin (k + 1))
  deriving DecidableEq

/-- Figure 6 (`false` = A, `true` = B). -/
def sδ (k : ℕ) : Bool × Fin (k + 1) → TOp → (Bool × Fin (k + 1)) × SRes k
  | s, .read => (s, .val s)
  | s, .opA => if s = (true, 0) then ((false, 0), .ack) else ((true, 0), .ack)
  | (w, r), .opB => if r + 1 = 0 then ((true, 0), .ack) else ((w, r + 1), .ack)

/-- The type `SS k` (`S_{k+1}`). -/
abbrev SS (k : ℕ) : ObjSpec where
  State := Bool × Fin (k + 1)
  Op := TOp
  Resp := SRes k
  init := (true, 0)
  δ := sδ k

/-- The type `S_n` of Proposition 21 (`n ≥ 2`). -/
abbrev Sn (n : ℕ) : ObjSpec := SS (n - 1)

theorem SS.readable (k : ℕ) : (SS k).Readable :=
  ⟨.read, fun _ => rfl, fun s t h => by simpa [sδ] using h⟩

section

variable {k : ℕ}

lemma SS.iterB {N : ℕ} (o : Fin N → TOp) :
    ∀ (l : List (Fin N)), (∀ p ∈ l, o p = .opB) → ∀ (w : Bool) (r : Fin (k + 1)),
      (∀ h : r.val + l.length ≤ k, apply (SS k) (w, r) o l = (w, ⟨r.val + l.length, by omega⟩)) ∧
      (r.val + l.length = k + 1 → apply (SS k) (w, r) o l = (true, 0)) := by
  intro l
  induction l with
  | nil => intro _ w r; refine ⟨fun _ => by simp, fun h => ?_⟩; have := r.isLt; simp at h; omega
  | cons p l ih =>
    intro hl w r
    rw [apply_cons, hl p (by simp)]
    have ih' := ih (fun q hq => hl q (by simp [hq]))
    by_cases hrk : r.val = k
    · have : r + 1 = 0 := by rw [fin_add_one_eq_zero]; exact hrk
      simp only [SS, sδ, this, ite_true]
      refine ⟨fun h => by simp at h; omega, fun h => ?_⟩
      have : l = [] := by simp at h; exact List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl
    · have hr' : ¬ r + 1 = 0 := by rw [fin_add_one_eq_zero]; exact hrk
      simp only [SS, sδ, hr', ite_false]
      have hv := fin_val_add_one_of_lt r (by omega)
      refine ⟨fun h => ?_, fun h => (ih' w (r + 1)).2 (by rw [hv]; simp at h; omega)⟩
      rw [(ih' w (r + 1)).1 (by rw [hv]; simp at h; omega)]
      simp [hv]; omega

/-! ## `SS k` is `(k+1)`-recording -/

/-- Teams: process `0` alone on team `A` (`false`). -/
def sTeam (k : ℕ) (p : Fin (k + 1)) : Bool := decide (1 ≤ p.val)

/-- Operations: `op_A` for `p₀`, `op_B` for the others. -/
def sOp (k : ℕ) (p : Fin (k + 1)) : TOp := if sTeam k p then .opB else .opA

lemma sOp_eq_opB {p : Fin (k + 1)} (hp : p ≠ 0) : sOp k p = .opB := by
  have : 1 ≤ p.val := by
    rcases Nat.eq_zero_or_pos p.val with h | h
    · exact absurd (Fin.ext h) hp
    · exact h
  simp [sOp, sTeam, this]

/-- After a schedule starting on team `B`, the winner is `B`. -/
lemma SS.winner_B : ∀ (l : List (Fin (k + 1))) (r : Fin (k + 1)), l.Nodup →
    ((0 : Fin (k + 1)) ∈ l → 1 ≤ r.val) → r.val + (l.filter (· ≠ 0)).length ≤ k →
    (apply (SS k) (true, r) (sOp k) l).1 = true := by
  intro l
  induction l with
  | nil => intro r _ _ _; rfl
  | cons p l ih =>
    intro r hl h0 hlen
    rw [apply_cons]
    have hl' := List.nodup_cons.1 hl
    by_cases hp : p = 0
    · subst hp
      have hr : 1 ≤ r.val := h0 (by simp)
      have hne : ((true, r) : Bool × Fin (k + 1)) ≠ (true, 0) := by
        intro e; simp at e; subst e; simp at hr
      simp only [sOp, sTeam, Fin.val_zero, show ¬ 1 ≤ 0 by omega, decide_false]
      simp only [SS, sδ, hne, ite_false, Bool.false_eq_true]
      exact ih 0 hl'.2 (fun h => absurd h hl'.1) (by
        rw [show List.filter (· ≠ (0 : Fin (k + 1))) ((0 : Fin (k + 1)) :: l) =
          List.filter (· ≠ 0) l by simp] at hlen
        simp only [Fin.val_zero]; omega)
    · rw [sOp_eq_opB hp]
      have hrk : r.val < k := by simp [hp] at hlen; omega
      have hr' : ¬ r + 1 = 0 := by rw [fin_add_one_eq_zero]; omega
      simp only [SS, sδ, hr', ite_false]
      exact ih (r + 1) hl'.2 (fun _ => by rw [fin_val_add_one_of_lt r hrk]; omega)
        (by
          rw [fin_val_add_one_of_lt r hrk]
          rw [List.filter_cons_of_pos (by simpa using hp), List.length_cons] at hlen; omega)

/-- **Proposition 21 (recording part).** `S_{k+1}` is `(k+1)`-recording, with `q₀ = (B, 0)`,
`A = {p₀}` (operation `op_A`) and `B` the other processes (operation `op_B`). -/
theorem SS.isRecording (hk : 1 ≤ k) : IsRecording (k + 1) (SS k) := by
  classical
  have count : ∀ l : List (Fin (k + 1)), l.Nodup → (l.filter (· ≠ 0)).length ≤ k := by
    intro l hl
    have := countP_le_card_of_nodup (fun p : Fin (k + 1) => decide (p ≠ 0)) hl
    rw [List.countP_eq_length_filter] at this
    refine this.trans ?_
    have : (Finset.univ.filter fun p : Fin (k + 1) => decide (p ≠ 0) = true) =
        Finset.univ.erase 0 := by ext p; simp
    rw [this, Finset.card_erase_of_mem (by simp)]; simp
  -- winner after an `A`-first schedule
  have hA : ∀ σ : List (Fin (k + 1)), ((0 : Fin (k + 1)) :: σ).Nodup →
      (apply (SS k) (true, 0) (sOp k) (0 :: σ)).1 = false := by
    intro σ hσ
    rw [apply_cons]
    simp only [sOp, sTeam, Fin.val_zero, show ¬ 1 ≤ 0 by omega, decide_false, Bool.false_eq_true,
      ite_false, SS, sδ, ite_true]
    have h0 : (0 : Fin (k + 1)) ∉ σ := (List.nodup_cons.1 hσ).1
    have hB : ∀ p ∈ σ, sOp k p = .opB := fun p hp => sOp_eq_opB (fun e => h0 (e ▸ hp))
    have hlen : σ.length ≤ k := by
      have := count σ (List.nodup_cons.1 hσ).2
      rwa [List.filter_eq_self.2 (fun p hp => by
        simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact h0 hp)] at this
    rw [(SS.iterB (sOp k) σ hB false 0).1 (by simpa using hlen)]
  have hB : ∀ q τ, (q :: τ).Nodup → sTeam k q = true →
      (apply (SS k) (true, 0) (sOp k) (q :: τ)).1 = true := by
    intro q τ hτ hq
    have hq0 : q ≠ 0 := by rintro rfl; simp [sTeam] at hq
    rw [apply_cons, sOp_eq_opB hq0]
    have h0' : ¬ (0 : Fin (k + 1)) + 1 = 0 := by rw [fin_add_one_eq_zero]; simp; omega
    simp only [SS, sδ, h0', ite_false]
    have hv : ((0 : Fin (k + 1)) + 1).val = 1 := by
      rw [fin_val_add_one_of_lt 0 (by simp; omega)]; simp
    refine SS.winner_B τ _ (List.nodup_cons.1 hτ).2 (fun _ => by rw [hv]) ?_
    have := count (q :: τ) hτ
    rw [hv]; simp [hq0] at this ⊢; omega
  refine ⟨(true, 0), sTeam k, sOp k, ⟨0, by simp [sTeam]⟩, ⟨⟨1, by omega⟩, by simp [sTeam]⟩,
    ?_, ?_⟩
  · intro p σ q τ hσ hτ tp tq heq
    have hp0 : p = 0 := by
      by_contra h
      have : 1 ≤ p.val := by
        rcases Nat.eq_zero_or_pos p.val with h' | h'
        · exact absurd (Fin.ext h') h
        · exact h'
      simp [sTeam, this] at tp
    subst hp0
    have := congrArg Prod.fst heq
    rw [hA σ hσ, hB q τ hτ tq] at this
    simp at this
  · intro p σ hσ heq
    have : sTeam k p = true := by
      by_contra h
      have hp0 : p = 0 := by
        by_contra h'
        have : 1 ≤ p.val := by
          rcases Nat.eq_zero_or_pos p.val with h'' | h''
          · exact absurd (Fin.ext h'') h'
          · exact h''
        simp [sTeam, this] at h
      subst hp0
      have := congrArg Prod.fst heq
      rw [hA σ hσ] at this
      simp at this
    refine ⟨0, by rw [this]; simp [sTeam], fun q hq => ?_⟩
    rw [this] at hq
    by_contra h
    have : 1 ≤ q.val := by
      rcases Nat.eq_zero_or_pos q.val with h'' | h''
      · exact absurd (Fin.ext h'') h
      · exact h''
    simp [sTeam, this] at hq

/-! ## `SS k` is not `m`-discerning for `m ≥ k + 2` -/

/-- From a value other than `(B, 0)`, two operations of `S` lead to the same value, absorb one
another, or commute with the same response. -/
lemma SS.pair_disc {u : Bool × Fin (k + 1)} (hu : u ≠ (true, 0)) (x y : TOp) :
    (sδ k u x).1 = (sδ k u y).1 ∨ sδ k (sδ k u y).1 x = sδ k u x ∨
      sδ k (sδ k u x).1 y = sδ k u y ∨
      ((sδ k (sδ k u x).1 y).1 = (sδ k (sδ k u y).1 x).1 ∧
        (sδ k u x).2 = (sδ k (sδ k u y).1 x).2) := by
  obtain ⟨w, r⟩ := u
  cases x <;> cases y <;> simp only [sδ] <;> (try split_ifs) <;> simp_all

/-- **Proposition 21 (discerning part).** `S_{k+1}` is not `m`-discerning for any `m ≥ k + 2`;
with Ruppert's characterization, `cons(S_n) ≤ n`. -/
theorem SS.not_isDiscerning (hk : 1 ≤ k) {m : ℕ} (hm : k + 2 ≤ m) : ¬ IsDiscerning m (SS k) := by
  classical
  intro h
  obtain ⟨u, team, o, ⟨i, hi⟩, ⟨j, hj⟩, hd⟩ := isDiscerning_iff.1 h
  have third : ∀ p q : Fin m, ∃ r, r ≠ p ∧ r ≠ q := by
    intro p q
    by_contra hno
    push Not at hno
    have : (Finset.univ : Finset (Fin m)) ⊆ {p, q} := fun r _ => by
      by_cases h : r = p
      · simp [h]
      · simp [hno r h]
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_insert_le p {q}
    simp at h1 h2; omega
  have hpair := fun p q (hpq : team p ≠ team q) => DiscCond.pair hd (i := p) (j := q) hpq
  have hij : team i ≠ team j := by simp [hi, hj]
  have hops := TT.ops_of_pairs team o i j hi hj (fun p q hpq => by
    obtain ⟨r, hrp, hrq⟩ := third p q
    refine ⟨fun e => (hpair p q hpq).2.2 r hrp hrq (by rw [e]), fun e => (hpair p q hpq).1 ?_,
      fun e => (hpair q p (Ne.symm hpq)).1 ?_⟩
    · rw [e]; rfl
    · rw [e]; rfl)
  have hu : u = (true, 0) := by
    by_contra hu
    obtain ⟨r, hri, hrj⟩ := third i j
    rcases SS.pair_disc hu (o i) (o j) with e | e | e | e
    · exact (hpair i j hij).2.2 r hri hrj e
    · exact (hpair j i (Ne.symm hij)).1 e
    · exact (hpair i j hij).1 e
    · exact (hpair i j hij).2.1 e
  subst hu
  have cyc : ∀ (X : Bool) (s : Fin m), team s = !X → ∀ l : List (Fin m), l.Nodup →
      (hne : l ≠ []) → (∀ p ∈ l, team p = X) → apply (SS k) (true, 0) o l = (true, 0) →
      False := by
    intro X s hs l hl hne hlX heq
    have hsl : s ∉ l := fun hm => by have := hlX s hm; rw [hs] at this; cases X <;> simp at this
    obtain ⟨p, l', rfl⟩ := List.exists_cons_of_ne_nil hne
    refine DiscCond.false_of_last_ne hd (p :: l') [] s ?_ (by simp) ?_ (by simpa using heq)
    · rw [List.nodup_append]
      exact ⟨hl, by simp, fun x hx y hy => by simp at hy; subst hy; rintro rfl; exact hsl hx⟩
    · simp [hlX p (by simp), hs]
  -- the `op_A` side and the `op_B` side
  obtain ⟨XA, sA, sB, hsA, hsB, htA, hoA, hoB⟩ : ∃ (XA : Bool) (sA sB : Fin m), team sA = XA ∧
      team sB = !XA ∧ (∀ p, team p = XA ∨ team p = !XA) ∧ (∀ p, team p = XA → o p = .opA) ∧
      (∀ p, team p = !XA → o p = .opB) := by
    rcases hops with ⟨⟨hoi, hoj⟩ | ⟨hoi, hoj⟩, hA, hB⟩
    · exact ⟨false, i, j, hi, hj, fun p => by cases team p <;> simp,
        fun p hp => (hA p hp).trans hoi, fun p hp => (hB p (by simpa using hp)).trans hoj⟩
    · exact ⟨true, j, i, hj, hi, fun p => by cases team p <;> simp,
        fun p hp => (hB p hp).trans hoj, fun p hp => (hA p (by simpa using hp)).trans hoi⟩
  set SA := Finset.univ.filter fun p : Fin m => team p = XA
  set SB := Finset.univ.filter fun p : Fin m => team p = !XA
  have hcard : SA.card + SB.card = m := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun p => team p = XA)
    have e : (Finset.univ.filter fun p : Fin m => ¬ team p = XA) = SB := by
      ext p; cases XA <;> simp [SB]
    rw [e] at this; simpa using this
  by_cases h2 : 2 ≤ SA.card
  · -- two `op_A`'s return the object to `(B, 0)`
    obtain ⟨l, hl, hlen, hlX⟩ := Finset.exists_nodup_list h2
    obtain ⟨p₁, p₂, rfl⟩ : ∃ p₁ p₂, l = [p₁, p₂] := by
      match l, hlen with
      | [p₁, p₂], _ => exact ⟨p₁, p₂, rfl⟩
    have t1 : team p₁ = XA := by simpa [SA] using hlX p₁ (by simp)
    have t2 : team p₂ = XA := by simpa [SA] using hlX p₂ (by simp)
    refine cyc XA sB hsB [p₁, p₂] hl (by simp) (fun q hq => by simp at hq; rcases hq with rfl | rfl
      <;> assumption) ?_
    simp [apply, hoA p₁ t1, hoA p₂ t2, sδ]
  · -- `k + 1` operations `op_B` return the object to `(B, 0)`
    have hB : k + 1 ≤ SB.card := by omega
    obtain ⟨l, hl, hlen, hlX⟩ := Finset.exists_nodup_list hB
    refine cyc (!XA) sA (by simp [hsA]) l hl (by rintro rfl; simp at hlen)
      (fun q hq => by simpa [SB] using hlX q hq) ?_
    exact (SS.iterB o l (fun q hq => hoB q (by simpa [SB] using hlX q hq)) true 0).2
      (by simp [hlen])

end

end Podc.RecoverableHarder
