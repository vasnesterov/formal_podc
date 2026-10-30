import Papers.PODC2021.SoreLoserHedging.Hedged

/-!
# Examples: non-vacuity and the counterexample to Lemma 2 (and to the split form of Lemma 3)

* `fig3_admissible`: the conforming execution of the hedged protocol on the swap digraph of
  Figure 3a (Alice the only leader) satisfies every axiom of `Admissible`; every asset is
  escrowed and redeemed, and nobody gains or loses premiums.
* `lemma_2_false`: on the two-party digraph `A ⇄ B` with leader `A`, Bob deposits all his
  premiums and then does not escrow his asset. Alice escrowed hers, so she withholds her secret;
  her hashkey never appears on her leaving arc, yet her net redemption-premium profit is `-p`,
  not `≥ p` as Lemma 2 claims. Her escrow-premium income `E(B, A) = R(A) = 2p` covers this
  (total `+p`, as `lemma_6` guarantees), which is how the proof of Lemma 3 argues; but the
  split statement of Lemma 3 (redemption profit `≥ p` per escrowed asset) is false too.

Admissibility of concrete executions is checked by `decide` on an equivalent decidable
formulation `AdmD` of `Admissible`.
-/

namespace Podc.SoreLoserHedging

open Finset

namespace Swap

variable {V : Type*} [Fintype V] [DecidableEq V] (S : Swap V) (X : Exec V) (C : Finset V)

/-- `P a` for the value `a` of `o`, if any. -/
def OAll {α : Type*} (o : Option α) (P : α → Prop) : Prop :=
  match o with
  | some a => P a
  | none => True

/-- `o` has a value `a` with `P a`. -/
def OEx {α : Type*} (o : Option α) (P : α → Prop) : Prop :=
  match o with
  | some a => P a
  | none => False

instance {α : Type*} (o : Option α) (P : α → Prop) [DecidablePred P] : Decidable (OAll o P) := by
  cases o <;> unfold OAll <;> infer_instance

instance {α : Type*} (o : Option α) (P : α → Prop) [DecidablePred P] : Decidable (OEx o P) := by
  cases o <;> unfold OEx <;> infer_instance

/-- Decidable form of `Signed`. -/
def SignedD (i x : V) (q₂ : List V) (t : ℕ) : Prop :=
  if x = i then q₂ = [] ∧ OEx (S.rel X x) (· ≤ t)
  else OEx (X.fk i x) fun b => b.2 = q₂ ∧ b.1 + 1 ≤ t

instance (i x : V) (q₂ : List V) (t : ℕ) : Decidable (S.SignedD X i x q₂ t) := by
  unfold SignedD; split_ifs <;> infer_instance

/-- A decidable formulation of `Admissible` (for checking concrete executions). -/
def AdmD : Prop :=
  (∀ u v, OAll (X.ep u v) fun t => S.G.Adj u v ∧ t ≤ S.dl1 u) ∧
  (∀ i u v, OAll (X.rp i u v) fun a => S.G.Adj u v ∧ i ∈ S.L ∧ PPath S.G i v a.2 ∧
    a.1 ≤ S.t1 + a.2.length) ∧
  (∀ u v, OAll (X.es u v) fun t => S.G.Adj u v ∧ t ≤ S.dl3 u) ∧
  (∀ i u v, OAll (X.ky i u v) fun a => S.G.Adj u v ∧ i ∈ S.L ∧ KPath S.G i v a.2 ∧
    a.1 ≤ S.B + a.2.length) ∧
  (∀ i u v, OAll (X.rp i u v) fun a => ∀ k : Fin a.2.length, 0 < k.val → a.2.get k ∉ C →
    ∃ u', OEx (X.rp i u' (a.2.get k)) fun b => b.2 = a.2.drop k.val ∧ b.1 ≤ a.1) ∧
  (∀ i u v, OAll (X.ky i u v) fun a => ∀ k : Fin a.2.length, 0 < k.val → a.2.get k ∉ C →
    S.SignedD X i (a.2.get k) (a.2.drop (k.val + 1)) a.1) ∧
  (∀ i v, OAll (X.fp i v) fun a => (∃ w ∈ outN S.G v, X.rp i v w = some a) ∧
    ∀ w ∈ outN S.G v, OAll (X.rp i v w) fun b => a.1 ≤ b.1) ∧
  (∀ i v, X.fp i v = none → ∀ w ∈ outN S.G v, X.rp i v w = none) ∧
  (∀ i v, OAll (X.fk i v) fun a => (∃ w ∈ outN S.G v, X.ky i v w = some a) ∧
    ∀ w ∈ outN S.G v, OAll (X.ky i v w) fun b => a.1 ≤ b.1) ∧
  (∀ i v, X.fk i v = none → ∀ w ∈ outN S.G v, X.ky i v w = none) ∧
  (∀ v ∉ C, ∀ w ∈ outN S.G v, X.ep v w =
    if v ∈ S.L then acc 1 (S.dl1 v) else (S.allIn X.ep v).bind fun m => acc (m + 1) (S.dl1 v)) ∧
  (∀ v ∉ C, v ∈ S.L → ∀ u ∈ inN S.G v, X.rp v u v =
    if ∀ u' ∈ inN S.G v, OptLe ((X.ep u' v).map fun t => (t, ())) S.t1 then
      some (S.t1 + 1, [v]) else none) ∧
  (∀ v ∉ C, ∀ i, i ≠ v → ∀ u ∈ inN S.G v, X.rp i u v =
    match X.fp i v with
    | some (t, q) => if v ∉ q then some (t + 1, v :: q) else none
    | none => none) ∧
  (∀ v ∉ C, ∀ w ∈ outN S.G v, X.es v w =
    if S.Act X v w then
      (if v ∈ S.L then acc (S.t2 + 1) (S.dl3 v)
       else (S.allIn X.es v).bind fun m => acc (max m S.t2 + 1) (S.dl3 v))
    else none) ∧
  (∀ v ∉ C, v ∈ S.L → ∀ u ∈ inN S.G v, X.ky v u v =
    (S.rel X v).bind fun r => if r ≤ S.B + 1 then some (r, [v]) else none) ∧
  (∀ v ∉ C, ∀ i, i ≠ v → ∀ u ∈ inN S.G v, X.ky i u v =
    match X.fk i v with
    | some (t, q) => if KPath S.G i v (v :: q) ∧ t + 1 ≤ S.B + (v :: q).length then
        some (t + 1, v :: q) else none
    | none => none)


set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance : Decidable (S.AdmD X C) := by unfold AdmD; infer_instance

theorem admissible_of_admD (h : S.AdmD X C) : S.Admissible X C := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, ?_, h10, h11, h12, h13, h14, h15, h16⟩
  · intro u v t ht; have := h1 u v; rw [ht] at this; exact this
  · intro i u v t q ht; have := h2 i u v; rw [ht] at this; exact this
  · intro u v t ht; have := h3 u v; rw [ht] at this; exact this
  · intro i u v t q ht; have := h4 i u v; rw [ht] at this; exact this
  · intro i u v t q ht k hk hk0 hkC
    have := h5 i u v; rw [ht] at this
    obtain ⟨u', hb⟩ := this ⟨k, hk⟩ hk0 hkC
    refine ⟨u', ?_⟩
    revert hb
    cases X.rp i u' q[k] with
    | none => intro hb; exact hb.elim
    | some b => intro hb; obtain ⟨h2', h1'⟩ := hb; exact ⟨b.1, by rw [← h2'], h1'⟩
  · intro i u v t q ht k hk hk0 hkC
    have := h6 i u v; rw [ht] at this
    have hs : S.SignedD X i q[k] (q.drop (k + 1)) t := this ⟨k, hk⟩ hk0 hkC
    unfold SignedD at hs
    unfold Signed
    split_ifs at hs ⊢ with hx
    · refine ⟨hs.1, ?_⟩
      have h' := hs.2
      revert h'
      cases S.rel X q[k] with
      | none => intro h'; exact h'.elim
      | some r => intro h'; exact ⟨r, rfl, h'⟩
    · revert hs
      cases X.fk i q[k] with
      | none => intro hs; exact hs.elim
      | some b => intro hs; obtain ⟨h2', h1'⟩ := hs; exact ⟨b.1, by rw [← h2'], h1'⟩
  · intro i v t q ht
    have := h7 i v; rw [ht] at this
    refine ⟨this.1, fun w hw t' q' h' => ?_⟩
    have := this.2 w hw; rw [h'] at this; exact this
  · intro i v t q ht
    have := h9 i v; rw [ht] at this
    refine ⟨this.1, fun w hw t' q' h' => ?_⟩
    have := this.2 w hw; rw [h'] at this; exact this

end Swap

/-! ### Figure 3a: all parties conform -/

namespace Fig3

/-- Alice `0`, Bob `1`, Carol `2`; arcs `A → B`, `B → A`, `B → C`, `C → A`. -/
def arcs : List (Fin 3 × Fin 3) := [(0, 1), (1, 0), (1, 2), (2, 0)]

def G : Digraph (Fin 3) := ⟨fun u v => (u, v) ∈ arcs⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable ((u, v) ∈ arcs))

/-- The swap of Figure 3a with leader Alice and consistent timeouts. -/
def S : Swap (Fin 3) where
  G := G
  loopless := by decide
  L := {0}
  fvs := isFVS_of_rank (fun v => v.val) (by decide)
  p := 1
  dl1 := ![1, 2, 3]
  t1 := 3
  t2 := 6
  dl3 := ![7, 8, 9]
  B := 9
  dl1_le := by decide
  t2_ge := by decide
  dl3_ge := by decide
  dl3_fol := by decide
  dl3_le := by decide

/-- The conforming execution. -/
def X : Exec (Fin 3) where
  ep u v := if (u, v) = (0, 1) then some 1 else if (u, v) = (1, 0) ∨ (u, v) = (1, 2) then some 2
    else if (u, v) = (2, 0) then some 3 else none
  rp i u v := if i ≠ 0 then none
    else if (u, v) = (1, 0) ∨ (u, v) = (2, 0) then some (4, [0])
    else if (u, v) = (0, 1) then some (5, [1, 0])
    else if (u, v) = (1, 2) then some (5, [2, 0]) else none
  es u v := if (u, v) = (0, 1) then some 7 else if (u, v) = (1, 0) ∨ (u, v) = (1, 2) then some 8
    else if (u, v) = (2, 0) then some 9 else none
  ky i u v := if i ≠ 0 then none
    else if (u, v) = (1, 0) ∨ (u, v) = (2, 0) then some (10, [0])
    else if (u, v) = (0, 1) then some (11, [1, 0])
    else if (u, v) = (1, 2) then some (11, [2, 0]) else none
  fp i v := if i ≠ 0 then none
    else if v = 0 then some (5, [1, 0]) else some (4, [0])
  fk i v := if i ≠ 0 then none
    else if v = 0 then some (11, [1, 0]) else some (10, [0])

theorem admissible : S.Admissible X ∅ := Swap.admissible_of_admD _ _ _ (by decide)

/-- Non-vacuity: in the conforming execution of Figure 3a every asset is escrowed and
redeemed, and (Lemma 1) no premium changes hands. -/
theorem fig3_admissible :
    S.Admissible X ∅ ∧ (∀ u v, S.G.Adj u v → S.Redeemed X u v) ∧ ∀ v, S.net X v = 0 :=
  ⟨admissible, by decide, fun v => Swap.lemma_1_net admissible rfl (by decide) v⟩

end Fig3

/-! ### Lemma 2 (and the split form of Lemma 3) fails for a leader -/

namespace TwoCycle

/-- Alice `0` (leader), Bob `1`; arcs `A → B`, `B → A`. -/
def G : Digraph (Fin 2) := ⟨fun u v => u ≠ v⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

def S : Swap (Fin 2) where
  G := G
  loopless := by decide
  L := {0}
  fvs := isFVS_of_rank (fun v => v.val) (by decide)
  p := 1
  dl1 := ![1, 2]
  t1 := 2
  t2 := 4
  dl3 := ![5, 6]
  B := 6
  dl1_le := by decide
  t2_ge := by decide
  dl3_ge := by decide
  dl3_fol := by decide
  dl3_le := by decide

/-- Bob deposits his escrow premium and his redemption premium, then does not escrow his asset;
Alice conforms. -/
def X : Exec (Fin 2) where
  ep u v := if (u, v) = (0, 1) then some 1 else if (u, v) = (1, 0) then some 2 else none
  rp i u v := if i ≠ 0 then none
    else if (u, v) = (1, 0) then some (3, [0]) else if (u, v) = (0, 1) then some (4, [1, 0])
    else none
  es u v := if (u, v) = (0, 1) then some 5 else none
  ky _ _ _ := none
  fp i v := if i ≠ 0 then none else if v = 0 then some (4, [1, 0]) else some (3, [0])
  fk _ _ := none

theorem admissible : S.Admissible X {1} := Swap.admissible_of_admD _ _ _ (by decide)

/-- **Lemma 2 is false for a leader.** Alice conforms, her hashkey never appears on her leaving
arc, she escrowed one asset, but her net redemption-premium profit is `-p < p`. -/
theorem lemma_2_false :
    S.Admissible X {1} ∧ (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) ∧ (0 : Fin 2) ∈ S.L ∧
    (∀ w ∈ outN S.G 0, X.ky 0 0 w = none) ∧ #(S.esc X 0) = 1 ∧ S.netR X 0 0 = -1 ∧
    S.netR X 0 0 < S.p * #(S.esc X 0) := by
  refine ⟨admissible, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **The split form of Lemma 3 is false.** Bob fails to escrow on `(B, A)`; Alice escrowed one
asset, but her net redemption-premium profit (over all hashkeys) is `-p < p`. Her total premium
profit is `+p` (`lemma_6`): the escrow premium `E(B, A) = 2p` makes up for it. -/
theorem lemma_3_split_false :
    S.Admissible X {1} ∧ X.es 1 0 = none ∧ ∑ i ∈ S.L, S.netR X i 0 < S.p * #(S.esc X 0) ∧ S.netE X 0 = 2 ∧
    S.net X 0 = 1 := by
  have hE : S.netE X 0 = 2 := by
    have h1 : S.flowE X 1 0 = 2 := by
      rw [Swap.flowE_eq (by decide) rfl, Ein_eq, if_pos (by decide)]
      decide
    have h0 : S.flowE X 0 1 = 0 := by
      unfold Swap.flowE; rw [if_neg (by decide)]
    have hi : inN S.G 0 = {1} := by decide
    have ho : outN S.G 0 = {1} := by decide
    simp [Swap.netE, hi, ho, h0, h1]
  refine ⟨admissible, rfl, by decide, hE, ?_⟩
  have hR : ∑ i ∈ S.L, S.netR X i 0 = -1 := by decide
  rw [Swap.net, hE, hR]; norm_num

end TwoCycle

end Podc.SoreLoserHedging
