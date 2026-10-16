import Papers.PODC2017.StatelessComputation.Model

/-!
# Section 6: a fooling-set method for label-stabilizing lower bounds

Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017, Section 6 and
Appendix D.

* `card_le_of_isFoolingSet` (**Theorem 6.2**, repaired and slightly generalised): if `f` has a
  fooling set `S` with respect to a node set `A`, then every protocol that is label-stabilizing
  and computes `f` (under the synchronous schedule) satisfies `|S| ≤ |L| ^ #cut(A)`, where
  `cut(A)` are the arcs with exactly one endpoint in `A`. The paper's two extra hypotheses
  (inputs of fooling-set elements agree at the tails of cut arcs) are never used in the proof
  and are dropped. `logb_le_of_isFoolingSet` is the paper's logarithmic form.
* `ring_cut_le`: in the bidirectional `n`-ring, the "first `m` nodes" cut has at most `4` arcs.
* `cor_6_3` (**Corollary 6.3**) for even `n`, in the stronger form `2 ^ (n/2) ≤ |L| ^ 4`, and the
  paper's form `(n - 2)/8 ≤ log₂ |L|` (`cor_6_3_logb`). For odd `n` the statement is false:
  `EQₙ` is constant and is computed with a one-letter label space (`cor_6_3_false_odd`).
* `cor_6_4` (**Corollary 6.4**): `⌊n/2⌋ ≤ |L| ^ 4` for majority, and the paper's form
  `log₂ ⌊n/2⌋ / 4 ≤ log₂ |L|` (`cor_6_4_logb`).

Label stabilization and computation are required only under the synchronous schedule
(`Protocol.SyncLabelStabilizing`, `Protocol.SyncComputes`), which is implied by the paper's
`r`-fair notions for every `r ≥ 1`; so the lower bounds hold a fortiori.
-/

namespace StatelessComputation
namespace FoolingSet

open Finset

variable {V : Type*} {L X Y : Type*} {G : Digraph V}

/-- The input that agrees with `z` on `A` and with `z'` outside `A` (the paper's `(x, y')`). -/
def mix [DecidableEq V] (A : Finset V) (z z' : V → X) : V → X :=
  fun v => if v ∈ A then z v else z' v

/-- Arcs with exactly one endpoint in `A` (the paper's `C ∪ D`). -/
def CutArc [DecidableEq V] (G : Digraph V) (A : Finset V) : Type _ :=
  {e : Arc G // ¬ (e.1.1 ∈ A ↔ e.1.2 ∈ A)}

instance [DecidableEq V] [Finite V] (A : Finset V) : Finite (CutArc G A) := by
  unfold CutArc; infer_instance

/-- **Definition 6.1** (fooling set, w.r.t. the split `A` / complement of `A`): `f = b` on `S`,
and for distinct `z, z' ∈ S` one of the two mixed inputs has value `≠ b`. -/
structure IsFoolingSet [DecidableEq V] (A : Finset V) (f : (V → X) → Y) (S : Finset (V → X))
    (b : Y) : Prop where
  val_eq : ∀ z ∈ S, f z = b
  fool : ∀ z ∈ S, ∀ z' ∈ S, z ≠ z' → f (mix A z z') ≠ b ∨ f (mix A z' z) ≠ b

/-- A label-stabilizing protocol computing `f` reaches, from any initial labeling, a fixed
point of the synchronous step at which every node outputs `f z`. -/
lemma exists_fixed (P : Protocol G L X Y) {f : (V → X) → Y} (hstab : P.SyncLabelStabilizing)
    (hcomp : P.SyncComputes f) (z : V → X) (ℓ0 : Labeling G L) :
    ∃ m : Labeling G L, P.syncStep z m = m ∧ ∀ i, P.out z m i = f z := by
  obtain ⟨m, T, hT⟩ := hstab z ℓ0
  refine ⟨m, ?_, fun i => ?_⟩
  · have h1 := hT (T + 1) (by omega)
    rwa [P.syncRun_succ, hT T le_rfl] at h1
  · obtain ⟨T', hT'⟩ := hcomp z ℓ0 i
    have := hT' (max T T') (le_max_right _ _)
    rwa [hT _ (le_max_left _ _)] at this

lemma syncRun_of_fixed (P : Protocol G L X Y) {z : V → X} {m : Labeling G L}
    (hm : P.syncStep z m = m) (t : ℕ) : P.syncRun z m t = m := by
  induction t with
  | zero => rfl
  | succ t ih => rw [P.syncRun_succ, ih, hm]

/-- Gluing two fixed points that agree on the cut arcs gives a fixed point for the mixed
input (core of the proof of Theorem 6.2). -/
lemma mixed_fixed [DecidableEq V] (P : Protocol G L X Y) (A : Finset V) {z z' : V → X}
    {m m' : Labeling G L} (hm : P.syncStep z m = m) (hm' : P.syncStep z' m' = m')
    (hcut : ∀ e : Arc G, ¬ (e.1.1 ∈ A ↔ e.1.2 ∈ A) → m e = m' e) :
    P.syncStep (mix A z z') (fun e => if e.1.1 ∈ A then m e else m' e) =
        (fun e => if e.1.1 ∈ A then m e else m' e) ∧
      ∀ i, P.out (mix A z z') (fun e => if e.1.1 ∈ A then m e else m' e) i =
        if i ∈ A then P.out z m i else P.out z' m' i := by
  set μ : Labeling G L := fun e => if e.1.1 ∈ A then m e else m' e with hμ
  have hin : ∀ i, inLab μ i = if i ∈ A then inLab m i else inLab m' i := by
    intro i
    funext u
    by_cases hu : u.1 ∈ A <;> by_cases hi : i ∈ A <;>
      simp only [inLab, hμ, hu, hi, ite_true, ite_false]
    · exact hcut ⟨(u.1, i), u.2⟩ (by simp [hu, hi])
    · exact (hcut ⟨(u.1, i), u.2⟩ (by simp [hu, hi])).symm
  refine ⟨?_, fun i => ?_⟩
  · funext e
    have h1 := congrFun hm e
    have h2 := congrFun hm' e
    simp only [Protocol.syncStep] at h1 h2 ⊢
    rw [hin]
    by_cases he : e.1.1 ∈ A
    · simp only [he, ite_true, mix, hμ]; exact h1
    · simp only [he, ite_false, mix, hμ]; exact h2
  · simp only [Protocol.out]
    rw [hin]
    by_cases hi : i ∈ A
    · simp [hi, mix]
    · simp [hi, mix]

/-- **Theorem 6.2** of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17] (counting form, without the
paper's unused side conditions). If `f` has a fooling set `S` w.r.t. the node set `A`, then
every protocol over a nonempty finite label space `L` that is label-stabilizing and computes `f`
satisfies `|S| ≤ |L| ^ #cut(A)`. -/
theorem card_le_of_isFoolingSet [Fintype V] [DecidableEq V] [Fintype L] [Nonempty L]
    (P : Protocol G L X Y) {f : (V → X) → Y} (hstab : P.SyncLabelStabilizing)
    (hcomp : P.SyncComputes f) (A : Finset V) {S : Finset (V → X)} {b : Y}
    (hS : IsFoolingSet A f S b) : S.card ≤ Fintype.card L ^ Nat.card (CutArc G A) := by
  classical
  let ℓ0 : Labeling G L := fun _ => Classical.arbitrary L
  choose lim hfix hout using fun z => exists_fixed P hstab hcomp z ℓ0
  -- if the limits agree on the cut, the mixed input is computed wrongly
  have key : ∀ z z', z ≠ z' → f z = b → f z' = b →
      (∀ e : Arc G, ¬ (e.1.1 ∈ A ↔ e.1.2 ∈ A) → lim z e = lim z' e) → f (mix A z z') = b := by
    intro z z' hne hz hz' hcut
    obtain ⟨v, -⟩ : ∃ v, z v ≠ z' v := by
      by_contra h; push Not at h; exact hne (funext h)
    obtain ⟨h1, h2⟩ := mixed_fixed P A (hfix z) (hfix z') hcut
    obtain ⟨T, hT⟩ := hcomp (mix A z z') (fun e => if e.1.1 ∈ A then lim z e else lim z' e) v
    have := hT T le_rfl
    rw [syncRun_of_fixed P h1, h2 v, hout, hout] at this
    rw [← this]
    split_ifs <;> assumption
  let g : (V → X) → (CutArc G A → L) := fun z c => lim z c.1
  have hinj : Set.InjOn g S := by
    intro z hz z' hz' hg
    by_contra hne
    have hcut : ∀ e : Arc G, ¬ (e.1.1 ∈ A ↔ e.1.2 ∈ A) → lim z e = lim z' e :=
      fun e he => congrFun hg ⟨e, he⟩
    rcases hS.fool z hz z' hz' hne with h | h
    · exact h (key z z' hne (hS.val_eq z hz) (hS.val_eq z' hz') hcut)
    · exact h (key z' z (Ne.symm hne) (hS.val_eq z' hz') (hS.val_eq z hz)
        (fun e he => (hcut e he).symm))
  let _ : Fintype (CutArc G A) := Fintype.ofFinite _
  have := Finset.card_le_card_of_injOn g (t := (univ : Finset (CutArc G A → L)))
    (fun _ _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_fun, Fintype.card_eq_nat_card (α := CutArc G A)] at this
  exact this

/-- `s ≤ c ^ k` with `c ≥ 1`, `k > 0` gives `log₂ s / k ≤ log₂ c`. -/
lemma logb_div_le {s c k : ℕ} (hc : 1 ≤ c) (hk : 0 < k) (h : s ≤ c ^ k) :
    Real.logb 2 s / k ≤ Real.logb 2 c := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hk']
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    simp only [Nat.cast_zero, Real.logb_zero]
    exact mul_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast hc)) hk'.le
  · have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hs)
      (show (s : ℝ) ≤ (c : ℝ) ^ k by exact_mod_cast h)
    rw [Real.logb_pow] at this
    linarith

/-- **Theorem 6.2**, the paper's logarithmic form: label complexity
`log₂ |L| ≥ log₂ |S| / (|C| + |D|)` (for a nonempty cut). -/
theorem logb_le_of_isFoolingSet [Fintype V] [DecidableEq V] [Fintype L] [Nonempty L]
    (P : Protocol G L X Y) {f : (V → X) → Y} (hstab : P.SyncLabelStabilizing)
    (hcomp : P.SyncComputes f) (A : Finset V) {S : Finset (V → X)} {b : Y}
    (hS : IsFoolingSet A f S b) (hcut : 0 < Nat.card (CutArc G A)) :
    Real.logb 2 S.card / Nat.card (CutArc G A) ≤ Real.logb 2 (Fintype.card L) :=
  logb_div_le Fintype.card_pos hcut (card_le_of_isFoolingSet P hstab hcomp A hS)

/-! ### The bidirectional ring -/

/-- The bidirectional `n`-ring on `Fin n`: arcs `i → i+1` and `i+1 → i` (indices mod `n`). -/
def ring (n : ℕ) : Digraph (Fin n) where
  Adj u v := v.val = (u.val + 1) % n ∨ u.val = (v.val + 1) % n

/-- The first `m` nodes of the ring (the paper's `[m]`). -/
def half (n m : ℕ) : Finset (Fin n) := univ.filter fun v => v.val < m

lemma succ_mod_cases {u n : ℕ} (h : u < n) :
    ((u + 1) % n = u + 1 ∧ u + 1 < n) ∨ (u + 1 = n ∧ (u + 1) % n = 0) := by
  rcases Nat.lt_or_ge (u + 1) n with h1 | h1
  · exact Or.inl ⟨Nat.mod_eq_of_lt h1, h1⟩
  · have : u + 1 = n := by omega
    exact Or.inr ⟨this, by rw [this, Nat.mod_self]⟩

/-- The cut between the first `m` nodes and the rest of the ring has at most 4 arcs
(`(m-1, m)`, `(m, m-1)`, `(n-1, 0)`, `(0, n-1)`). -/
lemma ring_cut_le (n m : ℕ) : Nat.card (CutArc (ring n) (half n m)) ≤ 4 := by
  classical
  let T : Finset (ℕ × ℕ) := {(m - 1, m), (m, m - 1), (n - 1, 0), (0, n - 1)}
  have hmem : ∀ c : CutArc (ring n) (half n m), (c.1.1.1.val, c.1.1.2.val) ∈ T := by
    rintro ⟨⟨⟨u, v⟩, hadj⟩, hc⟩
    simp only [half, mem_filter, mem_univ, true_and] at hc
    have hc' : (u.val < m ∧ ¬ v.val < m) ∨ (¬ u.val < m ∧ v.val < m) := by tauto
    clear hc
    have hu := u.2
    have hv := v.2
    simp only [T, mem_insert, mem_singleton, Prod.ext_iff]
    rcases hadj with h | h <;> dsimp only at h
    · rcases succ_mod_cases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at h; omega
      · rw [h2] at h; omega
    · rcases succ_mod_cases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at h; omega
      · rw [h2] at h; omega
  let φ : CutArc (ring n) (half n m) → T := fun c => ⟨_, hmem c⟩
  have hφ : Function.Injective φ := by
    rintro ⟨⟨⟨u, v⟩, _⟩, _⟩ ⟨⟨⟨u', v'⟩, _⟩, _⟩ h
    simp only [φ, Subtype.mk.injEq, Prod.mk.injEq] at h
    have hu : u = u' := Fin.ext h.1
    have hv : v = v' := Fin.ext h.2
    subst hu hv
    rfl
  calc Nat.card (CutArc (ring n) (half n m)) ≤ Nat.card T := Nat.card_le_card_of_injective φ hφ
    _ = T.card := Nat.card_eq_finsetCard T
    _ ≤ 4 := Finset.card_le_four

/-! ### Corollary 6.3: equality -/

/-- `EQₙ(z) = 1` iff `n` is even and the two halves of `z` are equal. -/
def eqFun (n : ℕ) (z : Fin n → Bool) : Bool :=
  decide (Even n ∧ ∀ i j : Fin n, j.val = i.val + n / 2 → z i = z j)

/-- The fooling set `{(y, y)}` for `EQ_{2m}`. -/
lemma eq_fooling (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset (Fin (2 * m) → Bool), S.card = 2 ^ m ∧
      IsFoolingSet (half (2 * m) m) (eqFun (2 * m)) S true := by
  classical
  let g : (Fin m → Bool) → (Fin (2 * m) → Bool) := fun y i => y ⟨i.val % m, Nat.mod_lt _ hm⟩
  have hg : Function.Injective g := by
    intro y y' h
    funext k
    have := congrFun h ⟨k.val, by omega⟩
    simpa [g, Nat.mod_eq_of_lt k.2] using this
  refine ⟨univ.image g, by rw [card_image_of_injective _ hg]; simp, ⟨?_, ?_⟩⟩
  · intro z hz
    obtain ⟨y, -, rfl⟩ := mem_image.1 hz
    simp only [eqFun, decide_eq_true_eq]
    refine ⟨⟨m, by ring⟩, fun i j hij => ?_⟩
    simp only [g]
    congr 2
    rw [hij, Nat.mul_div_cancel_left m (by norm_num), Nat.add_mod_right]
  · intro z hz z' hz' hne
    obtain ⟨y, -, rfl⟩ := mem_image.1 hz
    obtain ⟨y', -, rfl⟩ := mem_image.1 hz'
    left
    intro h
    apply hne
    congr 1
    funext k
    simp only [eqFun, decide_eq_true_eq] at h
    have := h.2 ⟨k.val, by omega⟩ ⟨k.val + m, by omega⟩
      (by simp [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)])
    simp only [mix, half, g, mem_filter, mem_univ, true_and, k.2, ite_true,
      show ¬ (k.val + m < m) by omega, ite_false, Nat.mod_eq_of_lt k.2, Nat.add_mod_right] at this
    exact this

/-- **Corollary 6.3** (even `n`, strengthened): a label-stabilizing protocol computing `EQₙ` on
the bidirectional `n`-ring satisfies `2 ^ (n/2) ≤ |L| ^ 4`, i.e. label complexity `≥ n/8`. -/
theorem cor_6_3 {n : ℕ} (he : Even n) {L : Type*} [Fintype L] [Nonempty L]
    (P : Protocol (ring n) L Bool Bool) (hstab : P.SyncLabelStabilizing)
    (hcomp : P.SyncComputes (eqFun n)) : 2 ^ (n / 2) ≤ Fintype.card L ^ 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by obtain ⟨k, hk⟩ := he; omega⟩
  have hc : 1 ≤ Fintype.card L := Fintype.card_pos
  rw [Nat.mul_div_cancel_left m (by norm_num)]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simpa using Nat.one_le_pow _ _ hc
  obtain ⟨S, hS, hfool⟩ := eq_fooling m hm
  have := card_le_of_isFoolingSet P hstab hcomp _ hfool
  rw [hS] at this
  exact this.trans (Nat.pow_le_pow_right hc (ring_cut_le _ _))

/-- **Corollary 6.3** in the paper's form (even `n`): label complexity `log₂ |L| ≥ (n-2)/8`. -/
theorem cor_6_3_logb {n : ℕ} (he : Even n) {L : Type*} [Fintype L] [Nonempty L]
    (P : Protocol (ring n) L Bool Bool) (hstab : P.SyncLabelStabilizing)
    (hcomp : P.SyncComputes (eqFun n)) : ((n : ℝ) - 2) / 8 ≤ Real.logb 2 (Fintype.card L) := by
  have h := logb_div_le Fintype.card_pos (by norm_num) (cor_6_3 he P hstab hcomp)
  push_cast at h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  have hn : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
    obtain ⟨k, hk⟩ := he
    have : n / 2 = k := by omega
    rw [this, hk]; push_cast; ring
  rw [hn]
  linarith

/-- **Corollary 6.3 is false for odd `n`**: `EQₙ ≡ 0` is computed by a label-stabilizing
protocol with a one-element label space (label complexity `0 < (n-2)/8`). -/
theorem cor_6_3_false_odd {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) :
    ∃ P : Protocol (ring n) Unit Bool Bool, P.SyncLabelStabilizing ∧
      P.SyncComputes (eqFun n) ∧ Real.logb 2 (Fintype.card Unit) < ((n : ℝ) - 2) / 8 := by
  refine ⟨⟨fun _ _ _ => (fun _ => (), false)⟩, fun x ℓ0 => ⟨ℓ0, 0, fun _ _ =>
    Subsingleton.elim _ _⟩, fun z ℓ0 i => ⟨0, fun _ _ => ?_⟩, ?_⟩
  · have : ¬ Even n := Nat.not_even_iff_odd.2 ho
    simp [Protocol.out, eqFun, this]
  · have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [Fintype.card_unit, Nat.cast_one, Real.logb_one]
    linarith

/-! ### Corollary 6.4: majority -/

/-- `Majₙ(z) = 1` iff `Σ zᵢ ≥ n/2`. -/
def majFun (n : ℕ) (z : Fin n → Bool) : Bool :=
  decide (n ≤ 2 * (univ.filter fun i => z i = true).card)

/-- The input `1^{a+1} 0^{m-1-a} | 0^{b+1} 1^{m-1-b} | 1^{n-2m}`. -/
def w (m a b i : ℕ) : Bool :=
  if i < m then decide (i ≤ a) else if i < 2 * m then decide (m + b < i) else true

lemma card_filter_fin (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (univ.filter fun i : Fin n => p i.val).card = ((range n).filter p).card := by
  refine Finset.card_bij (fun i _ => i.val) (fun i hi => ?_) (fun i _ j _ h => Fin.ext h)
    (fun k hk => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hi
    simp [hi, i.2]
  · simp only [mem_filter, mem_range] at hk
    exact ⟨⟨k, hk.1⟩, by simp [hk.2], rfl⟩

lemma card_w {n m a b : ℕ} (hn : 2 * m ≤ n) (ha : a < m) (hb : b < m) :
    (univ.filter fun i : Fin n => w m a b i.val = true).card = (a + 1) + (n - (m + b + 1)) := by
  rw [card_filter_fin n (fun i => w m a b i = true)]
  have : (range n).filter (fun i => w m a b i = true) = range (a + 1) ∪ Ico (m + b + 1) n := by
    ext i
    rw [mem_filter]
    simp only [mem_range, mem_union, mem_Ico, w]
    split_ifs <;> simp <;> omega
  rw [this, card_union_of_disjoint, card_range, Nat.card_Ico]
  rw [disjoint_left]
  intro i h1 h2
  simp only [mem_range, mem_Ico] at h1 h2
  omega

/-- The paper's fooling set for majority, of size `⌊n/2⌋`. -/
lemma maj_fooling (n : ℕ) :
    ∃ S : Finset (Fin n → Bool), S.card = n / 2 ∧
      IsFoolingSet (half n (n / 2)) (majFun n) S true := by
  classical
  set m := n / 2 with hm
  have h2m : 2 * m ≤ n := by omega
  let z : ℕ → Fin n → Bool := fun k i => w m k k i.val
  have hz : Set.InjOn z (range m) := by
    intro k hk k' hk' h
    simp only [coe_range, Set.mem_Iio] at hk hk'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := congrFun h ⟨k', by omega⟩
      simp [z, w, hk'] at this; omega
    · have := congrFun h ⟨k, by omega⟩
      simp [z, w, hk] at this; omega
  have hmix : ∀ a b, mix (half n m) (z a) (z b) = fun i => w m a b i.val := by
    intro a b
    funext i
    simp only [mix, half, mem_filter, mem_univ, true_and, z, w]
    split_ifs <;> rfl
  refine ⟨(range m).image z, by rw [card_image_of_injOn hz, card_range], ⟨?_, ?_⟩⟩
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
    rw [mem_range] at hk
    simp only [majFun, decide_eq_true_eq, z]
    rw [card_w h2m hk hk]
    omega
  · intro y hy y' hy' hne
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
    obtain ⟨k', hk', rfl⟩ := mem_image.1 hy'
    rw [mem_range] at hk hk'
    have hkk : k ≠ k' := fun h => hne (h ▸ rfl)
    rcases Nat.lt_or_gt_of_ne hkk with hlt | hlt
    · left
      rw [hmix]
      simp only [majFun, ne_eq, decide_eq_true_eq]
      rw [card_w h2m hk hk']
      omega
    · right
      rw [hmix]
      simp only [majFun, ne_eq, decide_eq_true_eq]
      rw [card_w h2m hk' hk]
      omega

/-- **Corollary 6.4** (counting form): a label-stabilizing protocol computing `Majₙ` on the
bidirectional `n`-ring satisfies `⌊n/2⌋ ≤ |L| ^ 4`. -/
theorem cor_6_4 {n : ℕ} {L : Type*} [Fintype L] [Nonempty L]
    (P : Protocol (ring n) L Bool Bool) (hstab : P.SyncLabelStabilizing)
    (hcomp : P.SyncComputes (majFun n)) : n / 2 ≤ Fintype.card L ^ 4 := by
  obtain ⟨S, hS, hfool⟩ := maj_fooling n
  have := card_le_of_isFoolingSet P hstab hcomp _ hfool
  rw [hS] at this
  exact this.trans (Nat.pow_le_pow_right Fintype.card_pos (ring_cut_le _ _))

/-- **Corollary 6.4** in the paper's form: label complexity `log₂ |L| ≥ log₂ ⌊n/2⌋ / 4`. -/
theorem cor_6_4_logb {n : ℕ} {L : Type*} [Fintype L] [Nonempty L]
    (P : Protocol (ring n) L Bool Bool) (hstab : P.SyncLabelStabilizing)
    (hcomp : P.SyncComputes (majFun n)) :
    Real.logb 2 ((n / 2 : ℕ) : ℝ) / 4 ≤ Real.logb 2 (Fintype.card L) := by
  have := logb_div_le Fintype.card_pos (by norm_num) (cor_6_4 P hstab hcomp)
  exact_mod_cast this

end FoolingSet
end StatelessComputation
