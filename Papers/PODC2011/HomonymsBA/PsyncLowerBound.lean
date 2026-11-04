import Papers.PODC2011.HomonymsBA.SyncLowerBound

/-!
# Proposition 4 and the lower bound of Theorem 20: `ℓ ≤ (n + 3t) / 2` makes partially
# synchronous BA unsolvable

The partitioning argument of Figure 4 of the paper, for `3t < ℓ` and `2ℓ ≤ n + 3t` (the case
`ℓ ≤ 3t` is Proposition 1 / Theorem 19). Identifiers `0, …, ℓ-1` (0-based) are split into
`X = [0, t)`, `Y = [t, 2t)`, `Z = [2t, 3t)`, `W = [3t, ℓ)`; processes are `Fin n`.

* `α`: process `k < ℓ` has identifier `k`, processes `k ≥ ℓ` have identifier `0` (a stack of
  `n - ℓ + 1` processes with identifier `0 ∈ X`); `Z` is Byzantine and silent; correct inputs `v₀`.
* `β`: the same assignment; `Y` is Byzantine and silent; correct inputs `v₁`.
* `γ`: `X` (one process per identifier) is Byzantine; *left* `= Y ∪ W` with input `v₀`; *right*
  `= Z ∪ W'` with input `v₁`, where `W'` are the processes `ℓ ≤ k < 2ℓ - 3t`, with identifier
  `k - ℓ + 3t ∈ W`; the remaining `n - 2ℓ + 3t` processes form an isolated stack with
  identifier `0`. Before round `T` all messages between different sides are lost and the
  Byzantine processes replay to the left what `X` sends in `α` and to the right what `X` sends in
  `β` (several copies from the stack: unrestricted); from round `T = gst` on everything is
  delivered and the Byzantine processes are silent.

Left processes cannot distinguish `γ` from `α` up to round `T` (`st_left`), right processes
cannot distinguish `γ` from `β` (`st_right`); with `T` larger than the decision rounds of a left
process in `α` and of a right process in `β`, agreement fails in `γ`.

For innumerate processes one copy per identifier suffices (the stack processes of `α` and `β` are
clones, `st_clone`), so the Byzantine processes are restricted (Theorem 20).

Main results: `prop4`, `thm20_lower`.
-/

namespace Podc.HomonymsBA

open Finset

namespace Partition

variable {n ℓ t : ℕ}

/-- Identifiers in `α` and `β`. -/
def idA (hℓ : 3 * t < ℓ) (k : Fin n) : Fin ℓ := if h : k.val < ℓ then ⟨k, h⟩ else ⟨0, by omega⟩

/-- Identifiers in `γ`. -/
def idG (hℓ : 3 * t < ℓ) (k : Fin n) : Fin ℓ :=
  if h : k.val < ℓ then ⟨k, h⟩
  else if h' : k.val < 2 * ℓ - 3 * t then ⟨k.val - ℓ + 3 * t, by omega⟩ else ⟨0, by omega⟩

/-- Left side of `γ`. -/
def L (k : Fin n) : Prop := (t ≤ k.val ∧ k.val < 2 * t) ∨ (3 * t ≤ k.val ∧ k.val < ℓ)

/-- Right side of `γ`. -/
def Rt (k : Fin n) : Prop :=
  (2 * t ≤ k.val ∧ k.val < 3 * t) ∨ (ℓ ≤ k.val ∧ k.val < 2 * ℓ - 3 * t)

/-- Processes of `β` corresponding to the right side (`Z ∪ W`). -/
def RB (k : Fin n) : Prop := 2 * t ≤ k.val ∧ k.val < ℓ

/-- Processes of the class `X` in `α`/`β` (identifiers in `[0, t)`, including the stack). -/
def XA (k : Fin n) : Prop := k.val < t ∨ ℓ ≤ k.val

instance : DecidablePred (L (n := n) (ℓ := ℓ) (t := t)) := fun k => by unfold L; infer_instance
instance : DecidablePred (Rt (n := n) (ℓ := ℓ) (t := t)) := fun k => by unfold Rt; infer_instance
instance : DecidablePred (RB (n := n) (ℓ := ℓ) (t := t)) := fun k => by unfold RB; infer_instance
instance : DecidablePred (XA (n := n) (ℓ := ℓ) (t := t)) := fun k => by unfold XA; infer_instance

/-- The process of `β` simulated by a right process of `γ`. -/
def eR (hℓ : 3 * t < ℓ) (k : Fin n) : Fin n :=
  if h : k.val < ℓ then k else ⟨k.val - ℓ + 3 * t, by have := k.isLt; omega⟩

/-- Inverse of `eR` on the right side. -/
def eR' (hn : 2 * ℓ ≤ n + 3 * t) (k : Fin n) : Fin n :=
  if h : k.val < 3 * t then k else if h' : k.val < ℓ then ⟨k.val + ℓ - 3 * t, by omega⟩ else k

variable (n t) in
def byzα : Finset (Fin n) := univ.filter fun k => 2 * t ≤ k.val ∧ k.val < 3 * t
variable (n t) in
def byzβ : Finset (Fin n) := univ.filter fun k => t ≤ k.val ∧ k.val < 2 * t
variable (n t) in
def byzγ : Finset (Fin n) := univ.filter fun k => k.val < t

lemma card_le_of_interval (a : ℕ) (s : Finset (Fin n)) (h : ∀ k ∈ s, a ≤ k.val ∧ k.val < a + t) :
    s.card ≤ t := by
  have := Finset.card_le_card_of_injOn (s := s) (t := range t) (fun k => k.val - a)
    (fun k hk => by have := h k hk; simp; omega) (fun k hk k' hk' e => by
      have := h k hk; have := h k' hk'; simp only at e; exact Fin.ext (by omega))
  simpa using this

variable (hℓ : 3 * t < ℓ) (hn : 2 * ℓ ≤ n + 3 * t)

lemma idG_of_lt {k : Fin n} (h : k.val < ℓ) : idG hℓ k = ⟨k, h⟩ := by simp [idG, h]
lemma idA_of_lt {k : Fin n} (h : k.val < ℓ) : idA hℓ k = ⟨k, h⟩ := by simp [idA, h]

lemma idA_surj (hln : ℓ ≤ n) : Function.Surjective (idA (n := n) hℓ) := fun i =>
  ⟨⟨i, by omega⟩, by simp [idA]⟩

lemma idG_surj (hln : ℓ ≤ n) : Function.Surjective (idG (n := n) hℓ) := fun i =>
  ⟨⟨i, by omega⟩, by simp [idG]⟩

lemma idA_lt_of_XA (ht : 0 < t) {k : Fin n} (h : XA (ℓ := ℓ) (t := t) k) : (idA hℓ k).val < t := by
  unfold XA at h
  unfold idA; split_ifs with h' <;> simp <;> omega

lemma idG_eq_idA_eR {k : Fin n} (h : Rt (ℓ := ℓ) (t := t) k) : idG hℓ k = idA hℓ (eR hℓ k) := by
  unfold Rt at h
  unfold idG idA eR
  by_cases h1 : k.val < ℓ
  · simp [h1]
  · have h2 : k.val < 2 * ℓ - 3 * t := by omega
    have h3 : k.val - ℓ + 3 * t < ℓ := by omega
    simp [h1, h2, h3]

lemma RB_eR {k : Fin n} (h : Rt (ℓ := ℓ) (t := t) k) : RB (ℓ := ℓ) (t := t) (eR hℓ k) := by
  unfold Rt at h; unfold RB eR
  split_ifs with h1 <;> (try simp only [Fin.val_mk]) <;> omega

lemma Rt_eR' {k : Fin n} (h : RB (ℓ := ℓ) (t := t) k) : Rt (ℓ := ℓ) (t := t) (eR' hn k) := by
  unfold RB at h; unfold Rt eR'
  split_ifs with h1 h2 <;> (try simp only [Fin.val_mk]) <;> omega

lemma eR_eR' {k : Fin n} (h : RB (ℓ := ℓ) (t := t) k) : eR hℓ (eR' hn k) = k := by
  unfold RB at h; unfold eR eR'
  apply Fin.ext
  split_ifs with h1 h2 h3 h4 <;> simp at * <;> omega

lemma eR'_eR {k : Fin n} (h : Rt (ℓ := ℓ) (t := t) k) : eR' hn (eR hℓ k) = k := by
  unfold Rt at h; unfold eR eR'
  apply Fin.ext
  split_ifs with h1 h2 h3 h4 h5 <;> simp at * <;> omega

/-! ### The three runs -/

variable {V M S : Type*} (A : Algorithm ℓ V M S)

/-- `α` (`byz = byzα`, input `v₀`) and `β` (`byz = byzβ`, input `v₁`): synchronous, Byzantine
processes silent. -/
def runA (byz : Finset (Fin n)) (v : V) : Run (Fin n) ℓ V M where
  id := idA hℓ
  byz := byz
  inp _ := v
  gst := 0
  drop _ _ _ := False
  adv _ _ := 0

/-- What the `X` processes of a run of `runA` send to `p`. -/
noncomputable def advX (R : Run (Fin n) ℓ V M) (r : ℕ) (p : Fin n) : Multiset (Fin ℓ × M) :=
  ∑ q ∈ univ.filter (XA (ℓ := ℓ) (t := t)), R.msgFrom A (R.st A r q) q p

variable (v₀ v₁ : V) (g : Multiset (Fin ℓ × M) → Multiset (Fin ℓ × M))

variable (n) in
/-- `γ`. -/
noncomputable def runG (T : ℕ) : Run (Fin n) ℓ V M where
  id := idG hℓ
  byz := byzγ n t
  inp k := if Rt (ℓ := ℓ) (t := t) k then v₁ else v₀
  gst := T
  drop r q p := r < T ∧ ¬ ((L (ℓ := ℓ) (t := t) q ∧ L (ℓ := ℓ) (t := t) p) ∨
    (Rt (ℓ := ℓ) (t := t) q ∧ Rt (ℓ := ℓ) (t := t) p))
  adv r p := if r < T then
      (if L (ℓ := ℓ) (t := t) p then g (advX (t := t) A (runA hℓ (byzα n t) v₀) r p)
       else if Rt (ℓ := ℓ) (t := t) p then g (advX (t := t) A (runA hℓ (byzβ n t) v₁) r (eR hℓ p)) else 0)
    else 0

/-! ### Indistinguishability -/

variable {A v₀ v₁ g}

lemma inbox_runA (byz : Finset (Fin n)) (v : V) (r : ℕ) (p : Fin n) :
    (runA hℓ byz v : Run (Fin n) ℓ V M).inbox A r p =
      ∑ q ∈ univ.filter (· ∉ byz), (runA hℓ byz v : Run (Fin n) ℓ V M).msgFrom A
        ((runA hℓ byz v : Run (Fin n) ℓ V M).st A r q) q p := by
  rw [Run.inbox_eq]
  simp only [runA, add_zero]
  exact Finset.sum_congr (by ext q; simp) fun _ _ => rfl

/-- Processes of `runA` with the same identifier are clones. -/
lemma st_clone (byz : Finset (Fin n)) (v : V) :
    ∀ r (q q' : Fin n), idA hℓ q = idA hℓ q' →
      (runA hℓ byz v : Run (Fin n) ℓ V M).st A r q = (runA hℓ byz v : Run (Fin n) ℓ V M).st A r q' := by
  intro r
  induction r with
  | zero => intro q q' h; simp [runA, h]
  | succ r ih =>
    intro q q' h
    rw [Run.st_succ, Run.st_succ, ih q q' h, inbox_runA, inbox_runA]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Run.msgFrom, runA, h]

lemma st_left (hg : ∀ s m m', A.step s (m + g m') = A.step s (m + m')) (T : ℕ) :
    ∀ r ≤ T, ∀ p ∈ {p : Fin n | L (ℓ := ℓ) (t := t) p},
      (runG n hℓ A v₀ v₁ g T).st A r p = (runA hℓ (byzα n t) v₀ : Run (Fin n) ℓ V M).st A r p := by
  refine Run.st_transfer A _ _ id _ T ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq, L] at hp
    refine ⟨?_, ?_⟩
    · simp [runG, runA, idG_of_lt hℓ (show p.val < ℓ by omega), idA_of_lt hℓ (show p.val < ℓ by omega)]
    · have : ¬ Rt (ℓ := ℓ) (t := t) p := by unfold Rt; omega
      simp [runG, runA, this]
  · intro r hr ih p hp
    simp only [Set.mem_setOf_eq] at hp ih
    have hpL := hp
    unfold L at hp
    have hpR : ¬ Rt (ℓ := ℓ) (t := t) p := by unfold Rt; omega
    rw [ih p hpL, id, Run.inbox_eq, inbox_runA]
    have hadv : (runG n hℓ A v₀ v₁ g T).adv r p = g (advX (t := t) A (runA hℓ (byzα n t) v₀) r p) := by
      simp [runG, hr, hpL]
    rw [hadv, hg]
    congr 1
    -- split the senders of `α` into the left side and `X`
    have hsplit : univ.filter (· ∉ byzα n t) =
        univ.filter (L (ℓ := ℓ) (t := t)) ∪ univ.filter (XA (ℓ := ℓ) (t := t)) := by
      ext q; simp [byzα, L, XA]; omega
    rw [hsplit, Finset.sum_union (by
      rw [Finset.disjoint_filter]; intro q _ h1 h2; unfold L at h1; unfold XA at h2; omega)]
    unfold advX
    congr 1
    refine Finset.sum_congr (by ext q; simp [runG, byzγ, L, Rt, hr]; omega) fun q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [ih q hq]
    have hq' := hq; unfold L at hq'
    simp [Run.msgFrom, runG, runA, idG_of_lt hℓ (show p.val < ℓ by omega),
      idA_of_lt hℓ (show p.val < ℓ by omega), idG_of_lt hℓ (show q.val < ℓ by omega),
      idA_of_lt hℓ (show q.val < ℓ by omega)]

include hn in
lemma st_right (hg : ∀ s m m', A.step s (m + g m') = A.step s (m + m')) (T : ℕ) :
    ∀ r ≤ T, ∀ p ∈ {p : Fin n | Rt (ℓ := ℓ) (t := t) p},
      (runG n hℓ A v₀ v₁ g T).st A r p =
        (runA hℓ (byzβ n t) v₁ : Run (Fin n) ℓ V M).st A r (eR hℓ p) := by
  refine Run.st_transfer A _ _ (eR hℓ) _ T ?_ ?_
  · intro p hp
    simp only [Set.mem_setOf_eq] at hp
    exact ⟨idG_eq_idA_eR hℓ hp, by simp [runG, runA, hp]⟩
  · intro r hr ih p hp
    simp only [Set.mem_setOf_eq] at hp ih
    have hpL : ¬ L (ℓ := ℓ) (t := t) p := by unfold L; unfold Rt at hp; omega
    rw [ih p hp, Run.inbox_eq, inbox_runA]
    have hadv : (runG n hℓ A v₀ v₁ g T).adv r p =
        g (advX (t := t) A (runA hℓ (byzβ n t) v₁) r (eR hℓ p)) := by
      simp [runG, hr, hpL, hp]
    rw [hadv, hg]
    congr 1
    have hsplit : univ.filter (· ∉ byzβ n t) =
        univ.filter (RB (ℓ := ℓ) (t := t)) ∪ univ.filter (XA (ℓ := ℓ) (t := t)) := by
      ext q; simp [byzβ, RB, XA]; omega
    rw [hsplit, Finset.sum_union (by
      rw [Finset.disjoint_filter]; intro q _ h1 h2; unfold RB at h1; unfold XA at h2; omega)]
    unfold advX
    congr 1
    rw [Finset.sum_congr (s₂ := univ.filter (Rt (ℓ := ℓ) (t := t)))
      (by ext q; simp [runG, byzγ, L, Rt, hr]; unfold Rt at hp; omega) (fun _ _ => rfl)]
    refine Finset.sum_nbij' (eR hℓ) (eR' hn) ?_ ?_ ?_ ?_ ?_
    · intro q hq; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact RB_eR hℓ hq
    · intro q hq; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact Rt_eR' hn hq
    · intro q hq; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact eR'_eR hℓ hn hq
    · intro q hq; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact eR_eR' hℓ hn hq
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [ih q hq]
      simp [Run.msgFrom, runG, runA, idG_eq_idA_eR hℓ hq, idG_eq_idA_eR hℓ hp]

/-! ### Admissibility -/

lemma valid_runA (hln : ℓ ≤ n) (byz : Finset (Fin n)) (hb : byz.card ≤ t) (v : V) :
    (runA hℓ byz v : Run (Fin n) ℓ V M).Valid t :=
  ⟨idA_surj hℓ hln, hb, by simp [runA], fun _ _ _ _ _ _ h => h⟩

lemma restricted_runA (byz : Finset (Fin n)) (v : V) :
    (runA hℓ byz v : Run (Fin n) ℓ V M).Restricted := by
  intro r p j; simp [runA]

lemma mem_advX {R : Run (Fin n) ℓ V M} (hR : R.id = idA hℓ) {r : ℕ} {p : Fin n}
    {x : Fin ℓ × M} (hx : x ∈ advX (t := t) A R r p) :
    ∃ q, XA (ℓ := ℓ) (t := t) q ∧ x.1 = idA hℓ q ∧ A.send (R.st A r q) (R.id p) = some x.2 := by
  unfold advX at hx
  rw [Multiset.mem_sum] at hx
  obtain ⟨q, hq, hx⟩ := hx
  rw [Run.mem_msgFrom, hR] at hx
  exact ⟨q, by simpa using hq, hx.1, by rw [hR]; exact hx.2⟩

lemma valid_runG (hln : ℓ ≤ n) (ht : 0 < t) (hgm : ∀ m x, x ∈ g m → x ∈ m) (T : ℕ) :
    (runG n hℓ A v₀ v₁ g T).Valid t := by
  refine ⟨idG_surj hℓ hln, card_le_of_interval 0 _ (fun k hk => by simp [runG, byzγ] at hk ⊢; omega),
    ?_, ?_⟩
  · intro r p x hx
    simp only [runG] at hx
    split_ifs at hx with h1 h2 h3 <;> try simp at hx
    all_goals
      obtain ⟨q, hq, hx1, -⟩ := mem_advX hℓ rfl (hgm _ _ hx)
      have := idA_lt_of_XA hℓ ht hq
      refine ⟨⟨(idA hℓ q).val, by omega⟩, by simp [runG, byzγ, this], ?_⟩
      rw [hx1]; simp [runG, idG] <;> omega
  · intro r q p hr _ _ h
    exact absurd h.1 (by simp [runG] at hr ⊢; omega)

lemma restricted_runG [DecidableEq M] (hln : ℓ ≤ n) (ht : 0 < t) (T : ℕ) :
    (runG n hℓ A v₀ v₁ Multiset.dedup T).Restricted := by
  intro r p j
  have key : ∀ (R : Run (Fin n) ℓ V M) (hR : R.id = idA hℓ)
      (hcl : ∀ q q', idA hℓ q = idA hℓ q' → R.st A r q = R.st A r q') (p' : Fin n),
      ((advX (t := t) A R r p').dedup.filter (·.1 = j)).card ≤
        ((byzγ n t).filter (idG hℓ · = j)).card := by
    intro R hR hcl p'
    by_cases hj : ∃ x ∈ advX (t := t) A R r p', x.1 = j
    · obtain ⟨x, hx, rfl⟩ := hj
      obtain ⟨q, hq, hx1, -⟩ := mem_advX hℓ hR hx
      have hlt := idA_lt_of_XA hℓ ht hq
      have h1 : 1 ≤ ((byzγ n t).filter (idG hℓ · = x.1)).card := by
        refine Finset.card_pos.2 ⟨⟨(idA hℓ q).val, by omega⟩, ?_⟩
        simp only [Finset.mem_filter, byzγ, Finset.mem_univ, true_and]
        refine ⟨hlt, ?_⟩
        rw [hx1]; simp [idG] <;> omega
      refine le_trans ?_ h1
      apply card_dedup_filter_le_one
      intro y hy z hz hy1 hz1
      obtain ⟨q1, -, h1c, h1d⟩ := mem_advX hℓ hR hy
      obtain ⟨q2, -, h2c, h2d⟩ := mem_advX hℓ hR hz
      have hid : idA hℓ q1 = idA hℓ q2 := by rw [← h1c, ← h2c, hy1, hz1]
      rw [hcl q1 q2 hid, h2d] at h1d
      exact Prod.ext (by rw [hy1, hz1]) (Option.some_injective _ h1d).symm
    · push Not at hj
      have : ((advX (t := t) A R r p').dedup.filter (·.1 = j)) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro x hx; exact hj x (Multiset.mem_dedup.1 hx)
      simp [this]
  simp only [runG]
  split_ifs with h1 h2 h3
  · exact key _ rfl (st_clone hℓ _ _ r) p
  · exact key _ rfl (st_clone hℓ _ _ r) _
  · simp
  · simp

/-! ### The contradiction -/

include hn in
theorem partition_contradiction (hln : ℓ ≤ n) (ht : 0 < t)
    (hg : ∀ s m m', A.step s (m + g m') = A.step s (m + m')) (hv : v₀ ≠ v₁)
    (hα : (runA hℓ (byzα n t) v₀ : Run (Fin n) ℓ V M).BA A)
    (hβ : (runA hℓ (byzβ n t) v₁ : Run (Fin n) ℓ V M).BA A)
    (hγ : ∀ T, (runG n hℓ A v₀ v₁ g T).BA A) : False := by
  set pL : Fin n := ⟨t, by omega⟩
  set pR : Fin n := ⟨2 * t, by omega⟩
  have hpLα : pL ∉ byzα n t := by simp [byzα, pL]; omega
  have hpRβ : pR ∉ byzβ n t := by simp [byzβ, pR]
  obtain ⟨w, rα, hrα⟩ := hα.termination pL hpLα
  have := hα.validity v₀ (fun _ _ => rfl) pL hpLα w ⟨rα, hrα⟩
  rw [this] at hrα
  obtain ⟨w, rβ, hrβ⟩ := hβ.termination pR hpRβ
  have := hβ.validity v₁ (fun _ _ => rfl) pR hpRβ w ⟨rβ, hrβ⟩
  rw [this] at hrβ
  set T := max rα rβ
  have hL : L (ℓ := ℓ) (t := t) pL := by unfold L; simp [pL]; omega
  have hR : Rt (ℓ := ℓ) (t := t) pR := by unfold Rt; simp [pR]; omega
  have heR : eR hℓ pR = pR := by simp [eR, pR]; omega
  have d₁ : (runG n hℓ A v₀ v₁ g T).Decides A pL v₀ := by
    refine ⟨rα, ?_⟩
    rw [st_left hℓ hg T rα (le_max_left _ _) pL hL]; exact hrα
  have d₂ : (runG n hℓ A v₀ v₁ g T).Decides A pR v₁ := by
    refine ⟨rβ, ?_⟩
    rw [st_right hℓ hn hg T rβ (le_max_right _ _) pR hR, heR]; exact hrβ
  exact hv ((hγ T).agreement pL (by simp [runG, byzγ, pL]) pR (by simp [runG, byzγ, pR]; omega)
    _ _ d₁ d₂)

end Partition

open Partition

/-- No algorithm solves partially synchronous BA with `3t < ℓ` and `2ℓ ≤ n + 3t` (numerate
processes, unrestricted Byzantine processes). -/
theorem not_solves_partition {n ℓ t : ℕ} (hℓ : 3 * t < ℓ) (hn : 2 * ℓ ≤ n + 3 * t) (ht : 0 < t)
    {V M S : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) (A : Algorithm ℓ V M S) :
    ¬ Solves .psync .unrestricted n t A := by
  intro h
  have hln : ℓ ≤ n := by omega
  have hS : ∀ R : Run (Fin n) ℓ V M, R.Valid t → R.BA A :=
    fun R hR => h (Fin n) (Fintype.card_fin n) R ⟨hR, (fun h' => by cases h'), (fun h' => by cases h')⟩
  have hb : ∀ a, (univ.filter fun k : Fin n => a ≤ k.val ∧ k.val < a + t).card ≤ t :=
    fun a => card_le_of_interval a _ (fun k hk => by simpa using hk)
  exact partition_contradiction hℓ hn (g := fun m => m) hln ht (fun _ _ _ => rfl) hv
    (hS _ (valid_runA hℓ hln _ (card_le_of_interval (2 * t) _
      (fun k hk => by simp [byzα] at hk; omega)) v₀))
    (hS _ (valid_runA hℓ hln _ (card_le_of_interval t _
      (fun k hk => by simp [byzβ] at hk; omega)) v₁))
    (fun T => hS _ (valid_runG hℓ hln ht (fun _ _ h => h) T))

/-- No innumerate algorithm solves partially synchronous BA with `3t < ℓ` and `2ℓ ≤ n + 3t`,
even against restricted Byzantine processes. -/
theorem not_solves_partition_innumerate {n ℓ t : ℕ} (hℓ : 3 * t < ℓ) (hn : 2 * ℓ ≤ n + 3 * t)
    (ht : 0 < t) {V M S : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) (A : Algorithm ℓ V M S)
    (hA : A.Innumerate) : ¬ Solves .psync .restricted n t A := by
  classical
  intro h
  have hln : ℓ ≤ n := by omega
  have hS : ∀ R : Run (Fin n) ℓ V M, R.Valid t → R.Restricted → R.BA A :=
    fun R hR hr => h (Fin n) (Fintype.card_fin n) R ⟨hR, (fun h' => by cases h'), (fun _ => hr)⟩
  have hg : ∀ s (m m' : Multiset (Fin ℓ × M)), A.step s (m + m'.dedup) = A.step s (m + m') :=
    fun s m m' => hA s _ _ fun x => by simp
  exact partition_contradiction hℓ hn hln ht hg hv
    (hS _ (valid_runA hℓ hln _ (card_le_of_interval (2 * t) _
      (fun k hk => by simp [byzα] at hk; omega)) v₀) (restricted_runA hℓ _ _))
    (hS _ (valid_runA hℓ hln _ (card_le_of_interval t _
      (fun k hk => by simp [byzβ] at hk; omega)) v₁) (restricted_runA hℓ _ _))
    (fun T => hS _ (valid_runG hℓ hln ht (fun _ _ h => Multiset.mem_dedup.1 h) T)
      (restricted_runG hℓ hln ht T))

/-- **Proposition 4.** Partially synchronous Byzantine agreement is unsolvable, even with
numerate processes, if `ℓ ≤ (n + 3t) / 2` (stated as `2ℓ ≤ n + 3t`; `n > 3t`, `1 ≤ ℓ`). -/
theorem prop4 {n ℓ t : ℕ} (hn3 : 3 * t < n) (ht : 0 < t) (hℓ0 : 0 < ℓ) (hn : 2 * ℓ ≤ n + 3 * t) {V : Type}
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) : ¬ Solvable .psync .unrestricted .numerate n ℓ t V := by
  intro h
  by_cases hℓ : 3 * t < ℓ
  · obtain ⟨M, S, A, -, hA⟩ := h
    exact not_solves_partition hℓ hn ht hv A hA
  · exact prop1 hn3 hℓ0 (by omega) hv h.sync_of_psync

/-- **Theorem 20, necessity.** Partially synchronous Byzantine agreement with innumerate processes
is unsolvable against restricted Byzantine processes if `ℓ ≤ (n + 3t) / 2`. -/
theorem thm20_lower {n ℓ t : ℕ} (hn3 : 3 * t < n) (ht : 0 < t) (hℓ0 : 0 < ℓ) (hn : 2 * ℓ ≤ n + 3 * t)
    {V : Type} {v₀ v₁ : V} (hv : v₀ ≠ v₁) : ¬ Solvable .psync .restricted .innumerate n ℓ t V := by
  intro h
  by_cases hℓ : 3 * t < ℓ
  · obtain ⟨M, S, A, hk, hA⟩ := h
    exact not_solves_partition_innumerate hℓ hn ht hv A hk hA
  · exact thm19_lower hn3 hℓ0 (by omega) hv h.sync_of_psync

end Podc.HomonymsBA
