import Podc.PartialSync.Omission

/-!
# All Byzantine Agreement Problems Are Expensive — §3: the lower bound for weak consensus

The core of the paper: in the synchronous **omission** model, any algorithm with Termination and
Agreement whose fault-free executions decide differently for two input vectors `x₀`, `x₁`
(e.g. weak consensus: all-`0` decides `0`, all-`1` decides `1`) has an execution in which correct
processes send `Ω(t²)` messages.

Executions (`isoExec x G k H k'`): inputs `x`; group `G` is *isolated from time `k`* (its
processes do not receive messages sent from outside `G` at times `≥ k`), and likewise `H` from
time `k'` (Definition 1; time `k` here is round `k + 1` of the paper).

* `lemma2`: Lemma 2 (a majority of an isolated group decides as the correct processes).
* `merge_st`, `lemma3`: Lemma 16 and Lemma 3 (mergeable executions).
* `chain`: Lemmas 4 and 5 (the critical round).
* `omission_lower_bound`: Lemma 1 for general `x₀`, `x₁`, with explicit parameters
  `β` (= `|B| = |C|`, the paper takes `t/4`) and `σ` (the paper's `t/2`).
* `weak_consensus_lower_bound_om`: Lemma 1 (≥ `t²/32` messages, for every `t`).
-/

namespace AllBAExpensive

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO : Type*} [Fintype P] [DecidableEq P] {t : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO}

/-- Inputs `x`; group `G` isolated from time `k` and group `H` isolated from time `k'`. -/
def isoExec (x : P → VI) (G : Finset P) (k : ℕ) (H : Finset P) (k' : ℕ) : OmExec P VI where
  inp := x
  ok τ q p := !(decide (p ∈ G ∧ q ∉ G ∧ k ≤ τ)) && !(decide (p ∈ H ∧ q ∉ H ∧ k' ≤ τ))

/-- The fault-free execution with inputs `x`. -/
abbrev ffExec (x : P → VI) : OmExec P VI := OmExec.ff x

omit [Fintype P] in
/-- With no isolated group, `isoExec` is the fault-free execution. -/
theorem isoExec_empty (x : P → VI) (k k' : ℕ) : isoExec x ∅ k ∅ k' = ffExec x := by
  simp [isoExec, OmExec.ff]

omit [Fintype P] in
theorem isoExec_comm (x : P → VI) (G : Finset P) (k : ℕ) (H : Finset P) (k' : ℕ) :
    isoExec x G k H k' = isoExec x H k' G k := by
  simp only [isoExec, OmExec.mk.injEq, true_and]
  funext τ q p; exact Bool.and_comm _ _

omit [Fintype P] in
theorem isoExec_admits (x : P → VI) (G : Finset P) (k : ℕ) (H : Finset P) (k' : ℕ) :
    (isoExec x G k H k').Admits A (G ∪ H) := by
  intro τ q p h _
  simp only [isoExec, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at h
  rcases h with ⟨hp, hq, -⟩ | ⟨hp, hq, -⟩
  · exact ⟨fun e => hq (e ▸ hp), Or.inr (mem_union_left _ hp)⟩
  · exact ⟨fun e => hq (e ▸ hp), Or.inr (mem_union_right _ hp)⟩

omit [Fintype P] in
theorem isoExec_admits' (x : P → VI) (G : Finset P) (k : ℕ) :
    (isoExec x G k ∅ 0).Admits A G := by
  simpa using isoExec_admits (A := A) x G k ∅ 0

omit [Fintype P] in
/-- In `isoExec`, a batch is only omitted at a member of `G ∪ H`. -/
theorem isoExec_ok_of_not_mem {x : P → VI} {G H : Finset P} {k k' τ : ℕ} {q p : P}
    (hp : p ∉ G ∪ H) : (isoExec x G k H k').ok τ q p = true := by
  simp only [mem_union, not_or] at hp
  simp [isoExec, hp.1, hp.2]

omit [Fintype P] in
theorem isoExec_ok_eq_false {x : P → VI} {G H : Finset P} {k k' τ : ℕ} {q p : P}
    (h : (isoExec x G k H k').ok τ q p = false) : p ∈ G ∪ H := by
  by_contra hp; rw [isoExec_ok_of_not_mem hp] at h; exact Bool.noConfusion h

/-! ### Lemma 2 -/

theorem card_compl_eq (F : Finset P) : (univ.filter (· ∉ F)).card = Fintype.card P - F.card := by
  rw [filter_not, card_sdiff_of_subset (by simp)]; simp

/-- **Lemma 2.** Let `F` be the faulty processes of `E` (at most `t`), `Y ⊆ F` a group whose
members only omit (non-empty) batches sent to `F`, and suppose correct processes send fewer than
`⌈|Y|/2⌉ σ` messages. If a correct process `x` decides `b`, then more than half of `Y` decides `b`
(and nothing else). Requires `|F| + σ ≤ t + 2` and `σ ≤ n - |F|` (the paper: `|F| ≤ t/2`,
`σ = t/2`). -/
theorem lemma2 (hS : OmSolves t A val) {E : OmExec P VI} {F Y : Finset P} {σ : ℕ}
    (hE : E.Admits A F) (hFt : F.card ≤ t) (hYF : Y ⊆ F) (hcard : F.card + σ ≤ t + 2)
    (hσ : σ ≤ Fintype.card P - F.card)
    (hsend : ∀ p ∈ Y, ∀ τ r, E.ok τ p r = false → A.send p (E.st A τ p) r ≠ [] → r ∈ F)
    (hK : ∀ N, E.msgsUpTo A F N < (Y.card + 1) / 2 * σ)
    {x : P} (hx : x ∉ F) {b : VO} (hb : E.Decides A x b) :
    ∃ Y' ⊆ Y, Y.card < 2 * Y'.card ∧ ∀ p ∈ Y', E.Decides A p b ∧ ∀ v, E.Decides A p v → v = b := by
  classical
  set D := E.dropSenders A F
  -- few processes of `Y` have `≥ σ` omitted senders
  set Bad := Y.filter fun p => σ ≤ (D p).card
  have hBad : Bad.card < (Y.card + 1) / 2 := by
    by_contra hc
    push Not at hc
    obtain ⟨N, hN⟩ : ∃ N, ∑ p ∈ Bad, (D p).card ≤ E.msgsUpTo A F N :=
      OmExec.sum_card_dropSenders_le (A := A) (E := E)
        (fun p hp => hYF (mem_filter.mp hp).1 : Bad ⊆ F)
    have : Bad.card * σ ≤ ∑ p ∈ Bad, (D p).card := by
      rw [← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun p hp => (mem_filter.mp hp).2
    have := hK N
    have := Nat.mul_le_mul_right σ hc
    omega
  refine ⟨Y.filter fun p => (D p).card < σ, filter_subset _ _, ?_, ?_⟩
  · have h1 := card_filter_add_card_filter_not (s := Y) (fun p => (D p).card < σ)
    have h2 : (Y.filter fun p => ¬ (D p).card < σ) = Bad := by
      simp only [Bad, not_lt]
    rw [h2] at h1
    omega
  intro p hp
  obtain ⟨hpY, hpD⟩ := mem_filter.mp hp
  have hpF := hYF hpY
  -- swap the omissions of `p` for omissions of the senders `D p`
  obtain ⟨F', hF'⟩ : ∃ F', F' = F.erase p ∪ D p := ⟨_, rfl⟩
  have hE' : E.Admits A F' := hF' ▸ hE.swap fun τ r h1 h2 => hsend p hpY τ r h1 h2
  have hF'card : F'.card ≤ t := by
    rw [hF']
    have := card_union_le (F.erase p) (D p)
    have := card_erase_of_mem hpF
    have := card_pos.mpr ⟨p, hpF⟩
    omega
  have hpF' : p ∉ F' := by
    simp only [hF', mem_union, mem_erase, not_or, not_and]
    exact ⟨fun h => absurd rfl h, OmExec.not_mem_dropSenders hpF⟩
  -- a correct process outside `F ∪ D p`
  obtain ⟨x', hx'⟩ : ((univ.filter (· ∉ F)) \ D p).Nonempty := by
    rw [← card_pos]
    have := le_card_sdiff (D p) (univ.filter (· ∉ F))
    rw [card_compl_eq] at this
    omega
  simp only [mem_sdiff, mem_filter, mem_univ, true_and] at hx'
  have hx'F' : x' ∉ F' := by
    simp only [hF', mem_union, mem_erase, not_or, not_and]
    exact ⟨fun _ h => hx'.1 h, hx'.2⟩
  obtain ⟨w, hw⟩ := hS.termination E F hE hFt x' hx'.1
  obtain rfl : w = b := hS.agreement E F hE hFt x' hx'.1 x hx w b hw hb
  obtain ⟨v, hv⟩ := hS.termination E F' hE' hF'card p hpF'
  obtain rfl : v = w := hS.agreement E F' hE' hF'card p hpF' x' hx'F' v w hv hw
  exact ⟨hv, fun u hu => hS.agreement E F' hE' hF'card p hpF' p hpF' u v hu hv⟩

/-! ### Lemma 3 (merging) -/

/-- **Lemma 16 (merge), states.** In the merged execution (`G` isolated from `k₁`, `H` from
`k₂`), the processes of `G` behave as in the execution where only `G` is isolated from `k₁`,
provided `k₁ = 0` or (same inputs and `k₁ ≤ k₂ + 1`). -/
theorem merge_st {z x : P → VI} {G H : Finset P} (hGH : Disjoint G H) {k₁ k₂ : ℕ}
    (hzx : ∀ p ∈ G, z p = x p) (hm : k₁ = 0 ∨ (z = x ∧ k₁ ≤ k₂ + 1)) :
    ∀ τ, ∀ p ∈ G, (isoExec z G k₁ H k₂).st A τ p = (isoExec x G k₁ ∅ 0).st A τ p := by
  have hpH : ∀ p ∈ G, p ∉ H := fun p hp hpH => disjoint_left.mp hGH hp hpH
  rcases hm with rfl | ⟨rfl, hk⟩
  · intro τ p hp
    refine OmExec.st_eq_of_inbox_eq (E := isoExec z G 0 H k₂) (E' := isoExec x G 0 ∅ 0)
      (X := fun _ => (G : Set P)) (fun _ => le_rfl)
      (fun p hp => hzx p hp) (fun τ ih p hp => ?_) τ p hp
    funext q
    have hp' : p ∈ G := hp
    have h1 : (isoExec z G 0 H k₂).ok τ q p = decide (q ∈ G) := by
      simp [isoExec, hp', hpH p hp']
    have h2 : (isoExec x G 0 ∅ 0).ok τ q p = decide (q ∈ G) := by simp [isoExec, hp']
    simp only [OmExec.inbox, h1, h2]
    by_cases hq : q ∈ G
    · simp [hq, ih q hq]
    · simp [hq]
  · intro τ p hp
    refine OmExec.st_eq_of_inbox_eq (E := isoExec z G k₁ H k₂) (E' := isoExec z G k₁ ∅ 0)
      (X := fun τ => if τ ≤ min k₁ k₂ then Set.univ else (G : Set P))
      (fun τ => ?_) (fun _ _ => rfl) (fun τ ih p hp => ?_) τ p (by split_ifs <;> simp [hp])
    · split_ifs with h1 h2 <;> simp
      omega
    funext q
    have hpG' : ¬ τ + 1 ≤ min k₁ k₂ → p ∈ G := by
      intro h; simp only [h, ite_false] at hp; exact hp
    refine OmExec.inbox_congr ?_ fun hok => ?_
    · by_cases hpG : p ∈ G
      · simp [isoExec, hpG, hpH p hpG]
      · have : ¬ k₁ ≤ τ ∧ ¬ k₂ ≤ τ := by
          by_contra h; exact hpG (hpG' (by omega))
        simp [isoExec, this.1, this.2]
    · by_cases hτ : τ ≤ min k₁ k₂
      · exact ih q (by simp [hτ])
      · by_cases hq : q ∈ G
        · exact ih q (by simp [hτ, hq])
        · have hpG := hpG' (by omega)
          simp [isoExec, hpG, hq, hpH p hpG] at hok
          omega

theorem merge_decides {z x : P → VI} {G H : Finset P} (hGH : Disjoint G H) {k₁ k₂ : ℕ}
    (hzx : ∀ p ∈ G, z p = x p) (hm : k₁ = 0 ∨ (z = x ∧ k₁ ≤ k₂ + 1)) {p : P} (hp : p ∈ G)
    {v : VO} : (isoExec z G k₁ H k₂).Decides A p v → (isoExec x G k₁ ∅ 0).Decides A p v := by
  rintro ⟨τ, h⟩; exact ⟨τ, by rwa [← merge_st hGH hzx hm τ p hp]⟩

/-- Standing assumptions on the parameters `β = |G| = |H|` and `σ`. -/
structure Params (P : Type*) [Fintype P] (t β σ : ℕ) : Prop where
  two_beta_le_t : 2 * β ≤ t
  le_t : 2 * β + σ ≤ t + 2
  le_n : 2 * β + σ ≤ Fintype.card P

omit [Fintype P] in
/-- In the two-group execution, the members of `Y ∈ {G, H}` only omit batches sent to `G ∪ H`. -/
theorem isoExec_send {x : P → VI} {G H : Finset P} {k k' : ℕ} {p : P} :
    ∀ τ r, (isoExec x G k H k').ok τ p r = false → A.send p ((isoExec x G k H k').st A τ p) r ≠ [] →
      r ∈ G ∪ H := fun _ _ h _ => isoExec_ok_eq_false h

/-- **Lemma 3.** Two *mergeable* executions — `G` isolated from `k₁` with inputs `x`, `H` isolated
from `k₂` with inputs `y` — make the processes outside `G ∪ H` decide the same value. Mergeable:
there are merged inputs `z` (`= x` on `G`, `= y` on `H`) with `k₁ = 0` or `z = x ∧ k₁ ≤ k₂ + 1`,
and `k₂ = 0` or `z = y ∧ k₂ ≤ k₁ + 1` (the paper: `k₁ = k₂ = 1`, or `b = 0` and `|k₁ - k₂| ≤ 1`). -/
theorem lemma3 (hS : OmSolves t A val) {β σ : ℕ} (hp : Params P t β σ)
    (hK : ∀ (E : OmExec P VI) (F : Finset P), E.Admits A F → F.card ≤ t →
      ∀ N, E.msgsUpTo A F N < (β + 1) / 2 * σ)
    {G H : Finset P} (hGH : Disjoint G H) (hG : G.card = β) (hH : H.card = β)
    {x y z : P → VI} {k₁ k₂ : ℕ} (hzx : ∀ p ∈ G, z p = x p) (hzy : ∀ p ∈ H, z p = y p)
    (hm₁ : k₁ = 0 ∨ (z = x ∧ k₁ ≤ k₂ + 1)) (hm₂ : k₂ = 0 ∨ (z = y ∧ k₂ ≤ k₁ + 1))
    {a : P} (ha : a ∉ G ∪ H) {v w : VO}
    (hv : (isoExec x G k₁ ∅ 0).Decides A a v) (hw : (isoExec y H k₂ ∅ 0).Decides A a w) :
    v = w := by
  have hcardGH : (G ∪ H).card = 2 * β := by rw [card_union_of_disjoint hGH]; omega
  have haG : a ∉ G := fun h => ha (mem_union_left _ h)
  have haH : a ∉ H := fun h => ha (mem_union_right _ h)
  -- the merged execution
  set E := isoExec z G k₁ H k₂
  have hE : E.Admits A (G ∪ H) := isoExec_admits z G k₁ H k₂
  have hEt : (G ∪ H).card ≤ t := by have := hp.two_beta_le_t; omega
  obtain ⟨u, hu⟩ := hS.termination E _ hE hEt a ha
  -- a majority of `Y` decides like the correct processes, in a single-group execution
  have single : ∀ (Y : Finset P) (xx : P → VI) (k : ℕ) (b : VO), Y.card = β →
      a ∉ Y → (isoExec xx Y k ∅ 0).Decides A a b →
      ∃ Y' ⊆ Y, Y.card < 2 * Y'.card ∧ ∀ p ∈ Y',
        ∀ v, (isoExec xx Y k ∅ 0).Decides A p v → v = b := by
    intro Y xx k b hY haY hb
    obtain ⟨Y', h1, h2, h3⟩ := lemma2 (F := Y) (Y := Y) (σ := σ) hS (isoExec_admits' xx Y k)
      (by have := hp.two_beta_le_t; omega) le_rfl (by have := hp.le_t; omega) (by have := hp.le_n; omega)
      (fun p _ τ r h1 h2 => by simpa using isoExec_send (A := A) τ r h1 h2)
      (by rw [hY]; exact hK _ _ (isoExec_admits' xx Y k) (by have := hp.two_beta_le_t; omega)) haY hb
    exact ⟨Y', h1, h2, fun p hp => (h3 p hp).2⟩
  -- a majority of `Y` decides `u` in the merged execution
  have merged : ∀ Y ⊆ G ∪ H, Y.card = β → ∃ Y' ⊆ Y, Y.card < 2 * Y'.card ∧
      ∀ p ∈ Y', E.Decides A p u := by
    intro Y hY hYc
    obtain ⟨Y', h1, h2, h3⟩ := lemma2 (F := G ∪ H) (Y := Y) (σ := σ) hS hE hEt hY (by have := hp.le_t; omega)
      (by have := hp.le_n; omega) (fun p _ τ r h1 h2 => isoExec_send (A := A) τ r h1 h2)
      (by rw [hYc]; exact hK _ _ hE hEt) ha hu
    exact ⟨Y', h1, h2, fun p hp => (h3 p hp).1⟩
  have inter : ∀ Y Y₁ Y₂ : Finset P, Y₁ ⊆ Y → Y₂ ⊆ Y → Y.card < 2 * Y₁.card →
      Y.card < 2 * Y₂.card → (Y₁ ∩ Y₂).Nonempty := by
    intro Y Y₁ Y₂ h1 h2 h3 h4
    rw [← card_pos]
    have := card_union_add_card_inter Y₁ Y₂
    have := card_le_card (union_subset h1 h2)
    omega
  -- `u = v`
  obtain ⟨G₁, hG₁, hG₁c, hG₁d⟩ := single G x k₁ v hG haG hv
  obtain ⟨G₂, hG₂, hG₂c, hG₂d⟩ := merged G subset_union_left hG
  obtain ⟨p, hp₁⟩ := inter G G₁ G₂ hG₁ hG₂ hG₁c hG₂c
  rw [mem_inter] at hp₁
  have huv : u = v := hG₁d p hp₁.1 u (merge_decides hGH hzx hm₁ (hG₁ hp₁.1) (hG₂d p hp₁.2))
  -- `u = w`
  obtain ⟨H₁, hH₁, hH₁c, hH₁d⟩ := single H y k₂ w hH haH hw
  obtain ⟨H₂, hH₂, hH₂c, hH₂d⟩ := merged H subset_union_right hH
  obtain ⟨q, hq⟩ := inter H H₁ H₂ hH₁ hH₂ hH₁c hH₂c
  rw [mem_inter] at hq
  have huw : u = w := by
    refine hH₁d q hq.1 u (merge_decides (disjoint_comm.mp hGH) hzy hm₂ (hH₁ hq.1) ?_)
    have := hH₂d q hq.2
    rw [show E = isoExec z H k₂ G k₁ from isoExec_comm _ _ _ _ _] at this
    exact this
  exact huv.symm.trans huw

/-! ### Lemmas 4 and 5 -/

omit [Fintype P] in
/-- Before the isolation time, an isolated execution is the fault-free one. -/
theorem isoExec_st_eq_ff (x : P → VI) (G : Finset P) (k : ℕ) :
    ∀ τ ≤ k, ∀ p, (isoExec x G k ∅ 0).st A τ p = (ffExec x).st A τ p := by
  intro τ hτ p
  refine OmExec.st_eq_of_inbox_eq (E := isoExec x G k ∅ 0) (E' := ffExec x)
    (X := fun τ => if τ ≤ k then Set.univ else ∅)
    (fun τ => ?_) (fun _ _ => rfl) (fun τ ih p hp => ?_) τ p (by simp [hτ])
  · split_ifs with h1 h2 <;> first | omega | simp
  · have hτk : τ < k := by
      by_contra h
      simp only [show ¬ (τ + 1 ≤ k) from by omega, ↓reduceIte] at hp
      exact absurd hp (by simp)
    funext q
    refine OmExec.inbox_congr (by simp [isoExec, show ¬ k ≤ τ by omega]) fun _ => ?_
    exact ih q (by simp [hτk.le])

/-- **Lemmas 4 and 5.** If the processes outside `G ∪ H` decide `v` in the fault-free execution
with inputs `x`, but something else when `G` is isolated from the start, then (under the message
bound) we get a contradiction: at the critical time `R` (Lemma 4), merging `G` isolated from `R`
or `R + 1` with `H` isolated from `R` (Lemma 3, twice) forces equal decisions. -/
theorem chain (hS : OmSolves t A val) {β σ : ℕ} (hp : Params P t β σ)
    (hK : ∀ (E : OmExec P VI) (F : Finset P), E.Admits A F → F.card ≤ t →
      ∀ N, E.msgsUpTo A F N < (β + 1) / 2 * σ)
    {G H : Finset P} (hGH : Disjoint G H) (hG : G.card = β) (hH : H.card = β)
    {x : P → VI} {a : P} (ha : a ∉ G ∪ H) {v v' : VO} (hff : (ffExec x).Decides A a v)
    (h0 : (isoExec x G 0 ∅ 0).Decides A a v') (hne : v' ≠ v) : False := by
  classical
  have haG : a ∉ G := fun h => ha (mem_union_left _ h)
  have haH : a ∉ H := fun h => ha (mem_union_right _ h)
  have hGt : G.card ≤ t := by have := hp.two_beta_le_t; omega
  have hHt : H.card ≤ t := by have := hp.two_beta_le_t; omega
  have hex : ∃ k, (isoExec x G k ∅ 0).Decides A a v := by
    obtain ⟨τ₀, h⟩ := hff
    exact ⟨τ₀, τ₀, by rw [isoExec_st_eq_ff x G τ₀ τ₀ le_rfl]; exact h⟩
  set k := Nat.find hex with hk
  have hkv : (isoExec x G k ∅ 0).Decides A a v := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0'
    rw [h0'] at hkv
    exact hne (hS.agreement _ G (isoExec_admits' x G 0) hGt a haG a haG v' v h0 hkv)
  obtain ⟨R, hR⟩ : ∃ R, k = R + 1 := ⟨k - 1, by omega⟩
  have hRv : ¬ (isoExec x G R ∅ 0).Decides A a v := Nat.find_min hex (by omega)
  obtain ⟨u, hu⟩ := hS.termination _ G (isoExec_admits' x G R) hGt a haG
  obtain ⟨u', hu'⟩ := hS.termination _ H (isoExec_admits' x H R) hHt a haH
  have e1 : u = u' := lemma3 hS hp hK hGH hG hH (z := x) (fun _ _ => rfl) (fun _ _ => rfl)
    (Or.inr ⟨rfl, by omega⟩) (Or.inr ⟨rfl, by omega⟩) ha hu hu'
  have e2 : v = u' := lemma3 hS hp hK hGH hG hH (z := x) (fun _ _ => rfl) (fun _ _ => rfl)
    (Or.inr ⟨rfl, by omega⟩) (Or.inr ⟨rfl, by omega⟩) ha (hR ▸ hkv) hu'
  exact hRv (by rw [e2, ← e1]; exact hu)

/-- **Lemma 1 (general form).** Let `A` satisfy Termination and Agreement in the synchronous
omission model with at most `t` faults, and let the fault-free executions with inputs `x₀` and
`x₁` decide different values. Then for all parameters `β, σ` with `2β ≤ t`, `2β + σ ≤ t + 2`,
`2β + σ ≤ n`, `σ ≥ 1`, some execution (with an admissible faulty set of size `≤ t`) has at least
`⌈β/2⌉ · σ` messages sent by correct processes, within a finite time `N`. -/
theorem omission_lower_bound (hS : OmSolves t A val) {β σ : ℕ} (hp : Params P t β σ)
    (hσ : 1 ≤ σ) {x₀ x₁ : P → VI} {p₀ p₁ : P} {v₀ v₁ : VO} (hne : v₀ ≠ v₁)
    (h₀ : (ffExec x₀).Decides A p₀ v₀) (h₁ : (ffExec x₁).Decides A p₁ v₁) :
    ∃ (E : OmExec P VI) (F : Finset P), E.Admits A F ∧ F.card ≤ t ∧
      ∃ N, (β + 1) / 2 * σ ≤ E.msgsUpTo A F N := by
  classical
  by_contra hK
  push Not at hK
  have hK' : ∀ (E : OmExec P VI) (F : Finset P), E.Admits A F → F.card ≤ t →
      ∀ N, E.msgsUpTo A F N < (β + 1) / 2 * σ := fun E F h1 h2 => hK E F h1 h2
  -- the groups `B = G`, `C = H`
  obtain ⟨G, -, hG⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := β)
    (by simp; have := hp.le_n; omega)
  obtain ⟨H, hHs, hH⟩ := exists_subset_card_eq (s := univ \ G) (n := β)
    (by rw [card_sdiff_of_subset (subset_univ _), card_univ, hG]; have := hp.le_n; omega)
  have hGH : Disjoint G H := by
    rw [disjoint_left]; intro p hp hpH; exact (mem_sdiff.mp (hHs hpH)).2 hp
  obtain ⟨a, ha⟩ : (univ \ (G ∪ H)).Nonempty := by
    rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ, card_union_of_disjoint hGH]
    have := hp.le_n; omega
  have ha : a ∉ G ∪ H := (mem_sdiff.mp ha).2
  have hGt : G.card ≤ t := by have := hp.two_beta_le_t; omega
  have hHt : H.card ≤ t := by have := hp.two_beta_le_t; omega
  -- `a` decides `v₀` / `v₁` in the fault-free executions
  have hff : ∀ x : P → VI, ∀ p v, (ffExec x).Decides A p v → (ffExec x).Decides A a v := by
    intro x p v hpv
    obtain ⟨w, hw⟩ := hS.termination (ffExec x) ∅ (OmExec.ff_admits ∅)
      (by simp) a (by simp)
    rwa [hS.agreement (ffExec x) ∅ (OmExec.ff_admits ∅) (by simp) a
      (by simp) p (by simp) w v hw hpv] at hw
  have hGa : a ∉ G := fun h => ha (mem_union_left _ h)
  have hHa : a ∉ H := fun h => ha (mem_union_right _ h)
  obtain ⟨d, hd⟩ := hS.termination _ G (isoExec_admits' x₀ G 0) hGt a hGa
  obtain ⟨d', hd'⟩ := hS.termination _ H (isoExec_admits' x₁ H 0) hHt a hHa
  -- `E₀^{B(1)}` and `E₁^{C(1)}` are mergeable
  have hdd : d = d' := lemma3 hS hp hK' hGH hG hH (z := fun p => if p ∈ H then x₁ p else x₀ p)
    (fun p hp => by simp [disjoint_left.mp hGH hp]) (fun p hp => by simp [hp])
    (Or.inl rfl) (Or.inl rfl) ha hd hd'
  by_cases hd0 : d = v₀
  · -- the "default" is `v₀`: use the executions with inputs `x₁`, roles of `G` and `H` swapped
    refine chain hS hp hK' (disjoint_comm.mp hGH) hH hG (by rwa [union_comm]) (hff x₁ p₁ v₁ h₁)
      hd' ?_
    rw [← hdd, hd0]; exact hne
  · exact chain hS hp hK' hGH hG hH ha (hff x₀ p₀ v₀ h₀) hd hd0

end AllBAExpensive
