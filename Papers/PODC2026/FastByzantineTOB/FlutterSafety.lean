import Papers.PODC2026.FastByzantineTOB.FlutterNet

set_option linter.unusedSectionVars false

/-!
# Flutter: No Duplication, Integrity, and the safety part of Agreement and Total Order

Main results (for every run of Flutter in which the black-box instances `con[x]` satisfy
Representative Validity and Agreement):

* `theorem6` (No Duplication): a correct server never delivers the same `(θ, m)` twice.
* `theorem7` (Integrity): a correct server delivers `m` from a correct client `θ` only if `θ`
  broadcast `m`.
* `lemma16` (Lemma 16, safety form): if `f + 1` correct servers propose `True` for `y` and a correct
  server's lock time reaches `y.bet`, then `y` is already one of its candidates. Needs
  `n < (f + 1) + q` (paper: `q = 4f + 1`, `n = 5f + 1`) and FIFO links.
* `orders_gapFree` (Lemmas 18–20): the order calls of a correct server are decided `True`, strictly
  increasing, and contain every tag decided `True` below any of them.
* `theorem8_totalOrder` (Theorem 8, safety part): at any two times, the delivery sequences of any
  two correct servers are prefixes of one another.

The liveness half of Theorem 8 ("eventually deliver the same messages") and Validity are not
formalized.
-/

namespace Podc.FastByzantineTOB.Flutter

open Finset

variable {P C M T : Type*} [LinearOrder C] [LinearOrder M] [LinearOrder T] [AddCommMonoid T]
  [Fintype P] [DecidableEq P] [DecidableEq C]

variable {S : Setup P C T} (R : Run (M := M) S)

/-! ### Specification of the black-box Representative Binary Consensus instances -/

/-- Representative Validity of every instance `con[x]`: a value decided at a correct server was
proposed by at least `f + 1` correct servers (at some time of the run). -/
def ConRepValidity : Prop :=
  ∀ k p x v, p ∉ S.F → (x, v) ∈ ((R.st k).srv p).decs →
    ∃ k', S.f + 1 ≤ #{ρ | ρ ∉ S.F ∧ (x, v) ∈ ((R.st k').srv ρ).props}

/-- Agreement of every instance `con[x]`. -/
def ConAgreement : Prop :=
  ∀ k k' p q x v w, p ∉ S.F → q ∉ S.F → (x, v) ∈ ((R.st k).srv p).decs →
    (x, w) ∈ ((R.st k').srv q).decs → v = w

/-! ### Basic run lemmas -/

section RunLemmas

variable (hq : 1 ≤ S.q)
include hq

lemma Run.ginv (k : ℕ) : GInv S (R.st k) := by
  induction k with
  | zero => obtain ⟨c0, d0, h⟩ := R.init; rw [h]; exact GInv.init S c0 d0
  | succ k ih =>
    rcases R.step k with h | ⟨a, ha, h⟩
    · rw [h]; exact ih
    · rw [h]; exact ih.step S hq a ha

omit hq in
lemma Run.lstep (k : ℕ) (p : P) : LStep S ((R.st k).srv p) ((R.st (k + 1)).srv p) := by
  rcases R.step k with h | ⟨a, ha, h⟩
  · rw [h]; exact LStep.refl _
  · rw [h]; exact exec_srv_lstep S _ a ha p

omit hq in
lemma Run.mono_of_lstep {β : Type*} [Preorder β]
    (f : SState P C M T → β) (hf : ∀ l l', LStep S l l' → f l ≤ f l') (p : P) {k k' : ℕ}
    (h : k ≤ k') : f ((R.st k).srv p) ≤ f ((R.st k').srv p) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (hf _ _ (R.lstep _ p))

omit hq in
lemma Run.props_mono (p : P) {k k' : ℕ} (h : k ≤ k') :
    ((R.st k).srv p).props ⊆ ((R.st k').srv p).props :=
  R.mono_of_lstep (fun l => l.props) (fun _ _ h => h.props_mono) p h

omit hq in
lemma Run.cands_mono (p : P) {k k' : ℕ} (h : k ≤ k') :
    ((R.st k).srv p).cands ⊆ ((R.st k').srv p).cands :=
  R.mono_of_lstep (fun l => l.cands) (fun _ _ h => h.cands_mono) p h

omit hq in
lemma Run.obox_prefix (p : P) {k k' : ℕ} (h : k ≤ k') :
    ((R.st k).srv p).obox <+: ((R.st k').srv p).obox := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (R.lstep _ p).obox_prefix

omit hq in
lemma Run.orders_prefix (p : P) {k k' : ℕ} (h : k ≤ k') :
    ((R.st k).srv p).orders <+: ((R.st k').srv p).orders := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (R.lstep _ p).orders_prefix

lemma Run.lockTime_mono (p : P) {k k' : ℕ} (h : k ≤ k') :
    lockTime S.q ((R.st k).srv p).remote ≤ lockTime S.q ((R.st k').srv p).remote :=
  R.mono_of_lstep (fun l => lockTime S.q l.remote) (fun _ _ h => h.lockTime_mono hq) p h

end RunLemmas

/-! ### No Duplication and Integrity -/

/-- Theorem 6 of [Monti–Camaioni–Roman] (No Duplication): a correct server never delivers the
same message from the same client twice. -/
theorem theorem6 (hq : 1 ≤ S.q) (k : ℕ) (p : P) : ((R.st k).srv p).dels.Nodup := by
  rw [((R.ginv hq k).linv p).dels]; exact delSeq_nodup _

/-- Theorem 7 of [Monti–Camaioni–Roman] (Integrity): a correct server delivers `m` from a correct
client `θ` only if `θ` broadcast `m`. -/
theorem theorem7 (hq : 1 ≤ S.q) (hval : ConRepValidity R) (k : ℕ) (p : P) (hp : p ∉ S.F)
    (θ : C) (hθ : θ ∉ S.G) (m : M) (h : (θ, m) ∈ ((R.st k).srv p).dels) :
    ∃ k', m ∈ ((R.st k').cli θ).bcast := by
  have hI := (R.ginv hq k).linv p
  rw [hI.dels, mem_delSeq] at h
  obtain ⟨x, hx, hxe⟩ := h
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨rfl, rfl⟩ := hxe
  have hdec := (hI.procd x true (hI.orders_procd x hx)).1
  obtain ⟨k', hk'⟩ := hval k p x true hp hdec
  obtain ⟨ρ, hρ⟩ := Finset.card_pos.mp (by omega : 0 < #{ρ | ρ ∉ S.F ∧ (x, true) ∈ ((R.st k').srv ρ).props})
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  have hmsg := (R.ginv hq k').props ρ x hρ.2 hθ
  exact ⟨k', ((R.ginv hq k').cinv x.client).cbox _ _ hmsg⟩

/-! ### Lemma 16 -/

/-- Discrete intermediate values for a counter that grows by at most one per step. -/
lemma exists_step_of_lt (g : ℕ → ℕ) (hg : ∀ k, g (k + 1) ≤ g k + 1) (hg0 : g 0 = 0) {j K : ℕ}
    (h : j < g K) : ∃ k < K, g k = j ∧ g (k + 1) = j + 1 := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases hK : j < g K
    · obtain ⟨k, hk, h1, h2⟩ := ih hK
      exact ⟨k, by omega, h1, h2⟩
    · have := hg K
      exact ⟨K, by omega, by omega, by omega⟩

lemma Run.dlv_init (x y : Node P C) : (R.st 0).dlv x y = 0 := by
  obtain ⟨c0, d0, h⟩ := R.init; rw [h]; rfl

/-- Lemma 16 of [Monti–Camaioni–Roman], safety form: if `f + 1` correct servers propose `True` for
`y` (at some time) and the lock time of a correct server `p` reaches `y.bet`, then `p` has already
marked `y` as a candidate. Requires `n < (f + 1) + q` (paper: `n = 5f + 1`, `q = 4f + 1`). -/
theorem lemma16 (hq : 1 ≤ S.q) (hn : Fintype.card P < S.f + 1 + S.q) (y : Tag C M T)
    (hSig : ∃ k', S.f + 1 ≤ #{ρ | ρ ∉ S.F ∧ (y, true) ∈ ((R.st k').srv ρ).props})
    (p : P) (k : ℕ) (hk : (y.bet : WithBot T) ≤ lockTime S.q ((R.st k).srv p).remote) :
    y ∈ ((R.st k).srv p).cands := by
  classical
  obtain ⟨k', hk'⟩ := hSig
  let Pr : ℕ → Prop := fun j => (y.bet : WithBot T) ≤ lockTime S.q ((R.st j).srv p).remote
  have hex : ∃ j, Pr j := ⟨k, hk⟩
  set kp := Nat.find hex with hkp
  have hkp_spec : Pr kp := Nat.find_spec hex
  have hkp_le : kp ≤ k := Nat.find_min' hex hk
  suffices y ∈ ((R.st kp).srv p).cands from R.cands_mono p hkp_le this
  -- the quorum of servers whose `Time` reached `y.bet` at `p`
  have hΦ := (le_lockTime_iff hq y.bet).mp hkp_spec
  set K := max k' kp
  have hsub : #{ρ | ρ ∉ S.F ∧ (y, true) ∈ ((R.st k').srv ρ).props} ≤
      #{ρ | ρ ∉ S.F ∧ (y, true) ∈ ((R.st K).srv ρ).props} :=
    Finset.card_le_card fun ρ hρ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      exact ⟨hρ.1, R.props_mono ρ (le_max_left _ _) hρ.2⟩
  have hlt : #(Finset.univ : Finset P) < #{ρ | ρ ∉ S.F ∧ (y, true) ∈ ((R.st K).srv ρ).props} +
      #{ρ | (y.bet : WithBot T) ≤ ((R.st kp).srv p).remote ρ} := by
    rw [Finset.card_univ]; omega
  obtain ⟨ρ, hρ⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ _)
    (Finset.subset_univ _) hlt
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  obtain ⟨⟨hρF, hρprop⟩, hρtime⟩ := hρ
  -- `remote_times[ρ]` at `p` is a delivered `Time t` message of `ρ` with `t ≥ y.bet`
  obtain ⟨t, ht⟩ : ∃ t : T, ((R.st kp).srv p).remote ρ = t := by
    cases h : ((R.st kp).srv p).remote ρ with
    | bot => rw [h] at hρtime; exact absurd hρtime (by simp)
    | coe t => exact ⟨t, rfl⟩
  have hyt : y.bet ≤ t := by rw [ht] at hρtime; exact WithBot.coe_le_coe.mp hρtime
  obtain ⟨i, hi, hi'⟩ := (R.ginv hq kp).remote p ρ hρF t ht
  -- Lemma 15 at time `K`: an `Observe y` precedes it on the FIFO link `ρ → p`
  have hpreK := R.obox_prefix ρ (le_max_right k' kp)
  obtain ⟨j, hj, hj'⟩ :=
    ((R.ginv hq K).linv ρ).lemma15 y hρprop i t (prefix_getElem? hpreK hi') hyt
  have hilen : i < ((R.st kp).srv ρ).obox.length := (List.getElem?_eq_some_iff.mp hi').1
  have hjkp : ((R.st kp).srv ρ).obox[j]? = some (.observe y) := by
    have h1 := List.prefix_iff_getElem?.mp hpreK j (by omega)
    rw [hj'] at h1
    rw [List.getElem?_eq_getElem (by omega), h1]
  -- the step at which `p` delivered message `j` from `ρ`
  let g : ℕ → ℕ := fun k => (R.st k).dlv (.inl ρ) (.inl p)
  have hg : ∀ k, g (k + 1) ≤ g k + 1 := fun k => by
    rcases R.step k with h | ⟨a, -, h⟩
    · simp [g, h]
    · simp only [g, h]
      rcases exec_dlv_srv S (R.st k) a ρ p with h' | ⟨_, _, _, h'⟩ <;> omega
  obtain ⟨k'', hk'', hg1, hg2⟩ := exists_step_of_lt g hg (R.dlv_init _ _)
    (show j < g kp by simp only [g]; omega)
  simp only [g] at hg1 hg2
  rcases R.step k'' with hst | ⟨a, ha, hst⟩
  · rw [hst] at hg2; omega
  rcases exec_dlv_srv S (R.st k'') a ρ p with h' | ⟨msg, rfl, -, -⟩
  · rw [hst] at hg2; omega
  -- the delivered message is `Observe y`
  have hmsg : msg = .observe y := by
    have hn := ha.2.resolve_left hρF
    simp only [State.next, (R.ginv hq k'').srv ρ p] at hn
    rw [show (R.st k'').dlv (.inl ρ) (.inl p) = j from hg1] at hn
    have := prefix_getElem? (R.obox_prefix ρ (show k'' ≤ kp by omega)) hn
    rw [hjkp] at this
    exact (Option.some.inj this).symm
  subst hmsg
  -- at that time the lock time of `p` was below `y.bet`, so `y` became a candidate
  have hnot : ¬ Pr k'' := Nat.find_min hex hk''
  have hc : y ∈ ((R.st (k'' + 1)).srv p).cands := by
    rw [hst]
    simp only [exec, State.onSrv, spot_srv_self, recv_srv, SState.spotL, spotCands]
    rw [ite_eq_left (not_le.mp hnot)]
    exact Finset.mem_insert_self _ _
  exact R.cands_mono p (show k'' + 1 ≤ kp by omega) hc

/-! ### Order calls -/

/-- The set `F` of tags decided `True` by some correct server (Definition 2). -/
def decidedTrue : Set (Tag C M T) := {y | ∃ k q, q ∉ S.F ∧ (y, true) ∈ ((R.st k).srv q).decs}

/-- Lemmas 17, 18 and 20 of [Monti–Camaioni–Roman], safety form: the order calls of a correct
server are strictly increasing, decided `True`, and include every tag decided `True` that is
smaller than one of them. -/
theorem orders_gapFree (hq : 1 ≤ S.q) (hn : Fintype.card P < S.f + 1 + S.q)
    (hval : ConRepValidity R) (hagr : ConAgreement R) (k : ℕ) (p : P) (hp : p ∉ S.F) :
    ((R.st k).srv p).orders.SortedLT ∧ (∀ x ∈ ((R.st k).srv p).orders, x ∈ decidedTrue R) ∧
    ∀ x ∈ ((R.st k).srv p).orders, ∀ y ∈ decidedTrue R, y < x → y ∈ ((R.st k).srv p).orders := by
  have hI := (R.ginv hq k).linv p
  refine ⟨hI.sorted, fun x hx => ⟨k, p, hp, (hI.procd x true (hI.orders_procd x hx)).1⟩, ?_⟩
  intro x hx y ⟨k0, q, hqF, hy⟩ hyx
  -- `x ≤ last_processed`, whose bet is below the lock time
  have hxl := hI.orders_le x hx
  obtain ⟨z, hz⟩ : ∃ z : Tag C M T, ((R.st k).srv p).lp = z := by
    cases h : ((R.st k).srv p).lp with
    | bot => rw [h] at hxl; exact absurd hxl (by simp)
    | coe z => exact ⟨z, rfl⟩
  have hxz : x ≤ z := by rw [hz] at hxl; exact WithBot.coe_le_coe.mp hxl
  have hyb : (y.bet : WithBot T) ≤ lockTime S.q ((R.st k).srv p).remote :=
    (WithBot.coe_le_coe.mpr (Tag.bet_le_of_le (hyx.le.trans hxz))).trans (hI.lp_lock z hz)
  -- by Lemma 16, `y` is a candidate, hence processed, with decision `True`
  have hyc := lemma16 R hq hn y (hval k0 q y true hqF hy) p k hyb
  obtain ⟨v, hv⟩ := hI.cands y hyc (hz ▸ WithBot.coe_le_coe.mpr (hyx.le.trans hxz))
  have hv' := hI.procd y v hv
  have : v = true := hagr k k0 p q y v true hp hqF hv'.1 hy
  exact hv'.2 this

/-- Two strictly increasing lists, both contained in `D` and downward closed in `D`, are
prefixes of one another. -/
lemma prefix_or_prefix_of_downClosed {α : Type*} [LinearOrder α] (D : Set α) :
    ∀ (l₁ l₂ : List α), l₁.SortedLT → l₂.SortedLT → (∀ x ∈ l₁, x ∈ D) → (∀ x ∈ l₂, x ∈ D) →
    (∀ x ∈ l₁, ∀ y ∈ D, y < x → y ∈ l₁) → (∀ x ∈ l₂, ∀ y ∈ D, y < x → y ∈ l₂) →
    l₁ <+: l₂ ∨ l₂ <+: l₁ := by
  intro l₁
  induction l₁ generalizing D with
  | nil => intros; exact Or.inl (List.nil_prefix)
  | cons a l₁ ih =>
    intro l₂ h₁ h₂ hD₁ hD₂ hc₁ hc₂
    cases l₂ with
    | nil => exact Or.inr List.nil_prefix
    | cons b l₂ =>
      rw [List.sortedLT_iff_pairwise, List.pairwise_cons] at h₁ h₂
      -- the heads agree
      have hab : a = b := by
        rcases lt_trichotomy a b with h | h | h
        · have := hc₂ b (List.mem_cons_self) a (hD₁ a List.mem_cons_self) h
          rcases List.mem_cons.mp this with h' | h'
          · exact h'
          · exact absurd (h₂.1 a h') (not_lt.mpr h.le)
        · exact h
        · have := hc₁ a (List.mem_cons_self) b (hD₂ b List.mem_cons_self) h
          rcases List.mem_cons.mp this with h' | h'
          · exact h'.symm
          · exact absurd (h₁.1 b h') (not_lt.mpr h.le)
      subst hab
      have := ih {y | y ∈ D ∧ a < y} l₂ (List.sortedLT_iff_pairwise.mpr h₁.2)
        (List.sortedLT_iff_pairwise.mpr h₂.2)
        (fun x hx => ⟨hD₁ x (List.mem_cons_of_mem _ hx), h₁.1 x hx⟩)
        (fun x hx => ⟨hD₂ x (List.mem_cons_of_mem _ hx), h₂.1 x hx⟩)
        (fun x hx y hy hyx => by
          rcases List.mem_cons.mp (hc₁ x (List.mem_cons_of_mem _ hx) y hy.1 hyx) with h | h
          · exact absurd h (ne_of_gt hy.2)
          · exact h)
        (fun x hx y hy hyx => by
          rcases List.mem_cons.mp (hc₂ x (List.mem_cons_of_mem _ hx) y hy.1 hyx) with h | h
          · exact absurd h (ne_of_gt hy.2)
          · exact h)
      rcases this with h | h
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      · exact Or.inr (List.cons_prefix_cons.mpr ⟨rfl, h⟩)

/-- Corollary 4 of [Monti–Camaioni–Roman], safety form: at any two times, the sequences of order
calls of two correct servers are prefixes of one another. -/
theorem corollary4 (hq : 1 ≤ S.q) (hn : Fintype.card P < S.f + 1 + S.q)
    (hval : ConRepValidity R) (hagr : ConAgreement R) (k k' : ℕ) (p p' : P) (hp : p ∉ S.F)
    (hp' : p' ∉ S.F) :
    ((R.st k).srv p).orders <+: ((R.st k').srv p').orders ∨
    ((R.st k').srv p').orders <+: ((R.st k).srv p).orders := by
  obtain ⟨h1, h2, h3⟩ := orders_gapFree R hq hn hval hagr k p hp
  obtain ⟨h1', h2', h3'⟩ := orders_gapFree R hq hn hval hagr k' p' hp'
  exact prefix_or_prefix_of_downClosed _ _ _ h1 h1' h2 h2' h3 h3'

/-- Theorem 8 of [Monti–Camaioni–Roman] (Agreement and Total Order), safety part: at any two
times, the delivery sequences of two correct servers are prefixes of one another. Requires
`n < (f + 1) + q` (paper: `n = 5f + 1`, `q = 4f + 1`). -/
theorem theorem8_totalOrder (hq : 1 ≤ S.q) (hn : Fintype.card P < S.f + 1 + S.q)
    (hval : ConRepValidity R) (hagr : ConAgreement R) (k k' : ℕ) (p p' : P) (hp : p ∉ S.F)
    (hp' : p' ∉ S.F) :
    ((R.st k).srv p).dels <+: ((R.st k').srv p').dels ∨
    ((R.st k').srv p').dels <+: ((R.st k).srv p).dels := by
  rw [((R.ginv hq k).linv p).dels, ((R.ginv hq k').linv p').dels]
  rcases corollary4 R hq hn hval hagr k k' p p' hp hp' with h | h
  · exact Or.inl (delSeq_prefix h)
  · exact Or.inr (delSeq_prefix h)

/-- Theorem 8 (safety part) with the paper's parameters: lock quorum `4f + 1`, `n = 5f + 1`. -/
theorem theorem8_totalOrder_paper (hq : S.q = 4 * S.f + 1) (hn : Fintype.card P = 5 * S.f + 1)
    (hval : ConRepValidity R) (hagr : ConAgreement R) (k k' : ℕ) (p p' : P) (hp : p ∉ S.F)
    (hp' : p' ∉ S.F) :
    ((R.st k).srv p).dels <+: ((R.st k').srv p').dels ∨
    ((R.st k').srv p').dels <+: ((R.st k).srv p).dels :=
  theorem8_totalOrder R (by omega) (by omega) hval hagr k k' p p' hp hp'

/-- Theorem 8 (safety part) for any `n > f` with the lock quorum `n − f` instead of `4f + 1`. -/
theorem theorem8_totalOrder_general (hq : S.q = Fintype.card P - S.f) (hn : S.f < Fintype.card P)
    (hval : ConRepValidity R) (hagr : ConAgreement R) (k k' : ℕ) (p p' : P) (hp : p ∉ S.F)
    (hp' : p' ∉ S.F) :
    ((R.st k).srv p).dels <+: ((R.st k').srv p').dels ∨
    ((R.st k').srv p').dels <+: ((R.st k).srv p).dels :=
  theorem8_totalOrder R (by omega) (by omega) hval hagr k k' p p' hp hp'

end Podc.FastByzantineTOB.Flutter
