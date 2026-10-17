import Papers.PODC2026.EarlyStabilizingCounting.Basic

/-!
# Graded agreement and King Consensus (Lemmas 2.5 and 2.7, Algorithms 9 and 10)

One instance of the 3-round King Consensus algorithm of [LL26, Appendix A] (Algorithm 10, built on
the 2-round graded agreement Algorithm 9), in the state-broadcast form used throughout: in every
round every node sends its current stage state to everybody.

* Round 1 (Algorithm 9, line 1): every node sends its input `x`. Stage-2 state `KC2`:
  input, leader and the echo flag `e` ("received `x_v` at least `n - t` times").
* Round 2 (Algorithm 9, lines 2–5): nodes with `e` re-send `x`; stage-3 state `KC3` holds the
  graded-agreement output `(z, g)` (`kc3`). Ties in line 4 are broken by the smallest sender.
* Round 3 (Algorithm 10, lines 2–4): the output is `⊥` without a leader, the own `z` with grade 1,
  and the leader's `z` otherwise (`kcOut`).

An instance is described by the receptions of the correct nodes: `r1 v w` is what `v` received
from `w` in the first round; it agrees with the true value on correct senders (`Agree`).

Main results: `ga_spec` (Lemma 2.5: validity and graded agreement), `kc_spec` (Lemma 2.7).
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

open Finset

/-- Stage-2 state of a King Consensus instance (after the first round). -/
structure KC2 (n : ℕ) where
  /-- the input value -/
  x : ℕ
  /-- the leader input (`none` = `⊥`) -/
  l : Option (Fin n)
  /-- echo flag of graded agreement: received the own input at least `n - t` times -/
  e : Bool

/-- Stage-3 state of a King Consensus instance (after the second round). -/
structure KC3 (n : ℕ) where
  /-- graded agreement output value -/
  z : ℕ
  /-- graded agreement output grade -/
  g : Bool
  /-- the leader input -/
  l : Option (Fin n)

/-- Round 1 (Algorithm 9, lines 1–2): `xs w` is the input received from `w`. -/
def kc2 (n : ℕ) (xv : ℕ) (lv : Option (Fin n)) (xs : Fin n → ℕ) : KC2 n :=
  ⟨xv, lv, decide (n - res n ≤ cnt xs xv)⟩

/-- Number of second-round messages carrying `y` (sent only by nodes with the echo flag). -/
def gaCnt {n : ℕ} (rcv : Fin n → KC2 n) (y : ℕ) : ℕ :=
  (univ.filter fun w => (rcv w).e = true ∧ (rcv w).x = y).card

/-- Round 2 (Algorithm 9, lines 3–5): graded agreement output. -/
def kc3 {n : ℕ} (own : KC2 n) (rcv : Fin n → KC2 n) : KC3 n :=
  if n - res n ≤ gaCnt rcv own.x then ⟨own.x, true, own.l⟩
  else
    match (List.finRange n).find?
        (fun w => (rcv w).e && decide (res n + 1 ≤ gaCnt rcv (rcv w).x)) with
    | some w => ⟨(rcv w).x, false, own.l⟩
    | none => ⟨own.x, false, own.l⟩

/-- Round 3 (Algorithm 10, lines 2–4): `rcv w` is the stage-3 state received from `w`. -/
def kcOut {n : ℕ} (own : KC3 n) (rcv : Fin n → KC3 n) : Option ℕ :=
  match own.l with
  | none => none
  | some ℓ => if own.g then some own.z else some (rcv ℓ).z

/-! ### Auxiliary lemmas -/

/-- The second-round message of a stage-2 state: its value if the echo flag is set. -/
def gaMsg {n : ℕ} (r : KC2 n) : Option ℕ := if r.e then some r.x else none

theorem gaMsg_eq_some {n : ℕ} (r : KC2 n) (y : ℕ) : gaMsg r = some y ↔ r.e = true ∧ r.x = y := by
  unfold gaMsg; cases r.e <;> simp

theorem gaCnt_eq_cnt {n : ℕ} (rcv : Fin n → KC2 n) (y : ℕ) :
    gaCnt rcv y = cnt (fun w => gaMsg (rcv w)) (some y) := by
  unfold gaCnt cnt
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, gaMsg_eq_some]

theorem kc3_l {n : ℕ} (own : KC2 n) (rcv : Fin n → KC2 n) : (kc3 own rcv).l = own.l := by
  unfold kc3
  split_ifs
  · rfl
  · split <;> rfl

theorem kc3_g {n : ℕ} (own : KC2 n) (rcv : Fin n → KC2 n) (h : (kc3 own rcv).g = true) :
    n - res n ≤ gaCnt rcv own.x ∧ (kc3 own rcv).z = own.x := by
  unfold kc3 at h ⊢
  split_ifs at h ⊢ with hc
  · exact ⟨hc, rfl⟩
  · exfalso
    split at h <;> simp at h

/-- If `y` is the only value with more than `t` second-round messages and some echoing sender of
`y` is received, graded agreement outputs `y`. -/
theorem kc3_z {n : ℕ} (own : KC2 n) (rcv : Fin n → KC2 n) (y : ℕ)
    (hlow : ∀ y', y' ≠ y → gaCnt rcv y' ≤ res n) (w : Fin n) (hw : (rcv w).e = true)
    (hwx : (rcv w).x = y) (hy : res n + 1 ≤ gaCnt rcv y) : (kc3 own rcv).z = y := by
  have hn : res n < n - res n := by have := w.2; unfold res; omega
  unfold kc3
  split_ifs with hc
  · show own.x = y
    by_contra hne
    have := hlow _ hne
    omega
  · split
    next w' hw' =>
      have h' := List.find?_some hw'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
      show (rcv w').x = y
      by_contra hne
      have := hlow _ hne
      omega
    next hnone =>
      rw [List.find?_eq_none] at hnone
      have := hnone w (List.mem_finRange w)
      simp [hw, hwx, hy] at this

/-- Two values each held by at least `n - t - |F|` correct nodes coincide. -/
theorem eq_of_two_majorities {n : ℕ} (F : Finset (Fin n)) (hF : 3 * F.card < n)
    (x : Fin n → ℕ) (a b : ℕ)
    (ha : n - res n ≤ (univ.filter fun w => w ∉ F ∧ x w = a).card + F.card)
    (hb : n - res n ≤ (univ.filter fun w => w ∉ F ∧ x w = b).card + F.card) : a = b := by
  by_contra hne
  have hdisj : Disjoint (univ.filter fun w => w ∉ F ∧ x w = a)
      (univ.filter fun w => w ∉ F ∧ x w = b) := by
    rw [disjoint_filter]
    rintro w - ⟨-, h1⟩ ⟨-, h2⟩
    exact hne (h1.symm.trans h2)
  have hsub : (univ.filter fun w => w ∉ F ∧ x w = a) ∪ (univ.filter fun w => w ∉ F ∧ x w = b) ⊆
      univ.filter fun w : Fin n => w ∉ F := by
    intro w hw
    simp only [mem_union, mem_filter, mem_univ, true_and] at hw ⊢
    rcases hw with h | h <;> exact h.1
  have h1 := card_le_card hsub
  rw [card_union_of_disjoint hdisj, card_correct] at h1
  have := card_le_res hF
  unfold res at *
  omega

/-- The second-round message count is at least the number of correct echoers of `y`. -/
theorem gaCnt_ge {n : ℕ} (F : Finset (Fin n)) {m s : Fin n → KC2 n} (h : Agree F m s) (y : ℕ) :
    (univ.filter fun w => w ∉ F ∧ gaMsg (s w) = some y).card ≤ gaCnt m y := by
  rw [gaCnt_eq_cnt]
  exact cnt_ge_correct F (m := fun w => gaMsg (m w)) (x := fun w => gaMsg (s w))
    (fun w hw => by simp only [h w hw]) (some y)

/-- The second-round message count is at most the number of correct echoers of `y` plus `|F|`. -/
theorem gaCnt_le {n : ℕ} (F : Finset (Fin n)) {m s : Fin n → KC2 n} (h : Agree F m s) (y : ℕ) :
    gaCnt m y ≤ (univ.filter fun w => w ∉ F ∧ gaMsg (s w) = some y).card + F.card := by
  rw [gaCnt_eq_cnt]
  exact cnt_le_correct_add F (m := fun w => gaMsg (m w)) (x := fun w => gaMsg (s w))
    (fun w hw => by simp only [h w hw]) (some y)

/-- Lemma 2.5 (graded agreement, Algorithm 9): validity and graded agreement for the stage-3
states of the correct nodes. -/
theorem ga_spec {n : ℕ} (F : Finset (Fin n)) (hF : 3 * F.card < n)
    (x : Fin n → ℕ) (l : Fin n → Option (Fin n))
    (r1 : Fin n → Fin n → ℕ) (h1 : ∀ v, v ∉ F → Agree F (r1 v) x)
    (s2 : Fin n → KC2 n) (hs2 : ∀ v, v ∉ F → s2 v = kc2 n (x v) (l v) (r1 v))
    (r2 : Fin n → Fin n → KC2 n) (h2 : ∀ v, v ∉ F → Agree F (r2 v) s2)
    (s3 : Fin n → KC3 n) (hs3 : ∀ v, v ∉ F → s3 v = kc3 (s2 v) (r2 v)) :
    (∀ c, (∀ v, v ∉ F → x v = c) → ∀ v, v ∉ F → (s3 v).z = c ∧ (s3 v).g = true) ∧
    (∀ w, w ∉ F → (s3 w).g = true → ∀ v, v ∉ F → (s3 v).z = (s3 w).z) := by
  have ht := card_le_res hF
  have hn : 3 * res n < n := by unfold res; omega
  -- facts about stage-2 states of correct nodes
  have hx2 : ∀ v, v ∉ F → (s2 v).x = x v := fun v hv => by rw [hs2 v hv]; rfl
  have he2 : ∀ v, v ∉ F → (s2 v).e = true → n - res n ≤ cnt (r1 v) (x v) := fun v hv he => by
    rw [hs2 v hv] at he; simpa [kc2] using he
  -- all correct echoers hold the same value
  have hecho : ∀ u u', u ∉ F → u' ∉ F → (s2 u).e = true → (s2 u').e = true → x u = x u' :=
    fun u u' hu hu' he he' =>
      eq_of_two_majorities F hF x _ _
        ((he2 u hu he).trans (cnt_le_correct_add F (h1 u hu) _))
        ((he2 u' hu' he').trans (cnt_le_correct_add F (h1 u' hu') _))
  refine ⟨fun c hc v hv => ?_, fun w hw hg v hv => ?_⟩
  · -- validity
    have hall : ∀ u, u ∉ F → gaMsg (s2 u) = some c := fun u hu => by
      rw [gaMsg_eq_some, hx2 u hu, hc u hu]
      refine ⟨?_, rfl⟩
      rw [hs2 u hu]
      simpa [kc2, hc u hu] using cnt_all hF (h1 u hu) hc
    have hge := gaCnt_ge F (h2 v hv) c
    have hset : (univ.filter fun w => w ∉ F ∧ gaMsg (s2 w) = some c) =
        univ.filter fun w : Fin n => w ∉ F := by
      ext w; simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.1, fun hw => ⟨hw, hall w hw⟩⟩
    rw [hset, card_correct] at hge
    have hcond : n - res n ≤ gaCnt (r2 v) (s2 v).x := by
      rw [hx2 v hv, hc v hv]; omega
    rw [hs3 v hv]
    unfold kc3
    simp only [hcond, ↓reduceIte]
    exact ⟨(hx2 v hv).trans (hc v hv), trivial⟩
  · -- graded agreement
    rw [hs3 w hw] at hg ⊢
    obtain ⟨hcw, hzw⟩ := kc3_g _ _ hg
    rw [hzw, hx2 w hw]
    rw [hx2 w hw] at hcw
    have hle := gaCnt_le F (h2 w hw) (x w)
    have hpos : 0 < (univ.filter fun u => u ∉ F ∧ gaMsg (s2 u) = some (x w)).card := by omega
    obtain ⟨u0, hu0⟩ := card_pos.mp hpos
    simp only [mem_filter, mem_univ, true_and, gaMsg_eq_some] at hu0
    obtain ⟨hu0F, hu0e, hu0x⟩ := hu0
    rw [hx2 u0 hu0F] at hu0x
    rw [hs3 v hv]
    refine kc3_z _ _ (x w) (fun y' hy' => ?_) u0 ?_ ?_ ?_
    · have := gaCnt_le F (h2 v hv) y'
      have hempty : (univ.filter fun u => u ∉ F ∧ gaMsg (s2 u) = some y') = ∅ := by
        ext u
        simp only [mem_filter, mem_univ, true_and, gaMsg_eq_some, Finset.notMem_empty,
          iff_false, not_and]
        intro hu he hx
        rw [hx2 u hu] at hx
        exact hy' (hx ▸ (hecho u u0 hu hu0F he hu0e).trans hu0x)
      rw [hempty, card_empty] at this
      omega
    · rw [h2 v hv u0 hu0F]; exact hu0e
    · rw [h2 v hv u0 hu0F, hx2 u0 hu0F]; exact hu0x
    · have := gaCnt_ge F (h2 v hv) (x w)
      omega

/-- Lemma 2.7 (King Consensus, Algorithm 10): one instance satisfies Definition 2.6. -/
theorem kc_spec {n : ℕ} (F : Finset (Fin n)) (hF : 3 * F.card < n)
    (x : Fin n → ℕ) (l : Fin n → Option (Fin n))
    (r1 : Fin n → Fin n → ℕ) (h1 : ∀ v, v ∉ F → Agree F (r1 v) x)
    (s2 : Fin n → KC2 n) (hs2 : ∀ v, v ∉ F → s2 v = kc2 n (x v) (l v) (r1 v))
    (r2 : Fin n → Fin n → KC2 n) (h2 : ∀ v, v ∉ F → Agree F (r2 v) s2)
    (s3 : Fin n → KC3 n) (hs3 : ∀ v, v ∉ F → s3 v = kc3 (s2 v) (r2 v))
    (r3 : Fin n → Fin n → KC3 n) (h3 : ∀ v, v ∉ F → Agree F (r3 v) s3)
    (y : Fin n → Option ℕ) (hy : ∀ v, v ∉ F → y v = kcOut (s3 v) (r3 v)) :
    KCSpec F x l y := by
  have hga := ga_spec F hF x l r1 h1 s2 hs2 r2 h2 s3 hs3
  have hl3 : ∀ v, v ∉ F → (s3 v).l = l v := fun v hv => by
    rw [hs3 v hv, kc3_l, hs2 v hv]; rfl
  have hyv : ∀ v, v ∉ F → y v = match l v with
      | none => none
      | some ℓ => if (s3 v).g then some (s3 v).z else some (r3 v ℓ).z := fun v hv => by
    rw [hy v hv, kcOut, hl3 v hv]
  refine ⟨fun c hc v hv => ?_, fun hnone v hv => ?_, fun ℓ hℓ hlead => ?_⟩
  · rw [hyv v hv]
    obtain ⟨hz, hg⟩ := hga.1 c hc v hv
    rcases l v with _ | ℓ
    · exact Or.inl rfl
    · simp [hg, hz]
  · rw [hyv v hv, hnone v hv]
  · have hyℓ : y ℓ = some (s3 ℓ).z := by
      rw [hyv ℓ hℓ, hlead ℓ hℓ]
      simp only [h3 ℓ hℓ ℓ hℓ, ite_self]
    refine ⟨by simp [hyℓ], fun v hv => ?_⟩
    rw [hyℓ, hyv v hv, hlead v hv]
    simp only
    split_ifs with hg
    · rw [hga.2 v hv hg ℓ hℓ]
    · rw [h3 v hv ℓ hℓ]

end EarlyStabilizingCounting
