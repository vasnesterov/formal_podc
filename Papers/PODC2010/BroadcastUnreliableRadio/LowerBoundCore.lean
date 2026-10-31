import Papers.PODC2010.BroadcastUnreliableRadio.Model

/-!
# The candidate-set argument of Theorem 12 (Claim 13), at the level of processes

One stage of the proof of Theorem 12 starts from a configuration `c₀` in which exactly one
process `j*` of the set `P` of processes placed so far (layers `L₀ … L_k`) is about to send alone.
For a pair `{a, b}` of unplaced processes, the execution `β_{a,b}` places `a, b` on layer `L_{k+1}`
and uses the adversary rules (`pairDel P a b`):

* a lone message of a process of `P` reaches exactly `P ∪ {a, b}`;
* every other message reaches everybody.

`claim_13` is the paper's Claim 13 (iterated): from a candidate set `C₀` of at least `2^(L+1)`
unplaced processes we keep a candidate set `C_ℓ` of at least `2^(L+1-ℓ)` processes such that
(2) a process in both or neither of two candidate pairs cannot distinguish the two executions after
round `ℓ` (of `β`, round `0` being the lone message of `j*`), and (3) no candidate sends alone in
rounds `1, …, ℓ` of its own execution. `exists_pair` extracts the pair used to extend the execution
by `L + 1` rounds.

Deviation from the paper's proof (Subcases IIIa/IIIb): processes removed from the candidate set in
earlier steps may send in round `ℓ + 1`; the paper's claim "no process in `I − (A_k ∪ {i₁, i₁'})`
sends" overlooks them. We argue instead that in Case III the sets of senders of the two executions
coincide and avoid both pairs, which covers these processes.
-/

namespace Podc.BroadcastUnreliableRadio

open Finset

variable {I S M : Type*} [Fintype I] [DecidableEq I]

/-- The adversary rules of stage `k + 1` (after the end of `α_k`): a lone message of a process of
`P` reaches exactly `P ∪ {a, b}`, every other message reaches everybody. -/
def pairDel (P : Finset I) (a b : I) : Delivery I :=
  fun _ B j => if B.card = 1 ∧ j ∈ P then insert a (insert b P) else univ

theorem pairDel_comm (P : Finset I) (a b : I) : pairDel P a b = pairDel P b a := by
  funext t B j
  simp [pairDel, Finset.insert_comm]

theorem mem_pairDel_iff {P : Finset I} {a₁ b₁ a₂ b₂ j : I}
    (hj : j = a₁ ∨ j = b₁ ↔ j = a₂ ∨ j = b₂) (t : ℕ) (B : Finset I) (x : I) :
    j ∈ pairDel P a₁ b₁ t B x ↔ j ∈ pairDel P a₂ b₂ t B x := by
  unfold pairDel
  split_ifs
  · simp only [mem_insert]; tauto
  · simp

namespace Algorithm

variable (A : Algorithm I S M)

/-- A process receives the same value in a round of two executions if its state, the senders,
their states, and whether their messages reach it coincide. -/
theorem step_apply_eq {D D' : Delivery I} {t : ℕ} {c c' : I → S} {j : I}
    (hj : c j = c' j) (hs : A.senders c = A.senders c')
    (hc : ∀ x ∈ A.senders c, c x = c' x)
    (hD : ∀ x ∈ A.senders c, (j ∈ D t (A.senders c) x ↔ j ∈ D' t (A.senders c) x)) :
    A.step D t c j = A.step D' t c' j := by
  have hH : A.hearers D t c j = A.hearers D' t c' j := by
    ext x
    simp only [mem_hearers, ← hs]
    constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, by rwa [← hD x hx]⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, by rwa [hD x hx]⟩
  simp only [step, hj, hH]
  congr 1
  apply A.rx_congr
  intro x hx
  exact hc x (by rw [hs]; exact A.hearers_subset _ _ _ _ hx)

/-- Under `pairDel`, two or more senders make everybody receive `⊤`. -/
theorem step_pairDel_of_one_lt (P : Finset I) (a b : I) {t : ℕ} {c : I → S} (j : I)
    (h : 1 < (A.senders c).card) :
    A.step (pairDel P a b) t c j = A.trans (c j) Rx.collision := by
  have : A.hearers (pairDel P a b) t c j = A.senders c :=
    A.hearers_eq_senders (fun x _ => by simp [pairDel, h.ne'])
  simp only [step, this, A.rx_of_one_lt_card _ h]

theorem senders_iff_of_eq {c c' : I → S} {x : I} (h : c x = c' x) :
    x ∈ A.senders c ↔ x ∈ A.senders c' := by
  simp only [mem_senders, h]

/-- **Claim 13** of the paper (iterated over `ℓ`). -/
theorem claim_13 (c₀ : I → S) (P : Finset I) (jstar : I) (hstar : A.senders c₀ = {jstar})
    (hjP : jstar ∈ P) (C₀ : Finset I) (L : ℕ) (hC₀card : 2 ^ (L + 1) ≤ C₀.card) :
    ∀ ℓ ≤ L, ∃ C ⊆ C₀, 2 ^ (L + 1 - ℓ) ≤ C.card ∧
      (∀ a₁ ∈ C, ∀ b₁ ∈ C, ∀ a₂ ∈ C, ∀ b₂ ∈ C, a₁ ≠ b₁ → a₂ ≠ b₂ → ∀ j,
        (j = a₁ ∨ j = b₁ ↔ j = a₂ ∨ j = b₂) →
        A.run c₀ (pairDel P a₁ b₁) (ℓ + 1) j = A.run c₀ (pairDel P a₂ b₂) (ℓ + 1) j) ∧
      (∀ a ∈ C, ∀ b ∈ C, a ≠ b → ∀ r, 1 ≤ r → r ≤ ℓ →
        A.senders (A.run c₀ (pairDel P a b) r) ≠ {a}) := by
  classical
  intro ℓ
  induction ℓ with
  | zero =>
    intro _
    refine ⟨C₀, subset_rfl, by simpa using hC₀card, ?_, fun _ _ _ _ _ r h1 h2 => by omega⟩
    intro a₁ _ b₁ _ a₂ _ b₂ _ _ _ j hj
    simp only [zero_add, run_succ, run_zero]
    apply A.step_apply_eq rfl rfl (fun _ _ => rfl)
    intro x hx
    rw [hstar, Finset.mem_singleton] at hx
    subst hx
    simp only [pairDel, hstar, card_singleton, hjP, and_self, if_true, mem_insert]
    tauto
  | succ ℓ ih =>
    intro hℓ
    obtain ⟨C, hC, hcard, hP2, hP3⟩ := ih (by omega)
    -- configurations after round `ℓ` of `β` (time `ℓ + 1`)
    set c : I → I → I → S := fun a b => A.run c₀ (pairDel P a b) (ℓ + 1) with hc_def
    have hcomm : ∀ a b, c a b = c b a := fun a b => by simp only [hc_def, pairDel_comm P a b]
    have hnext : ∀ a b j, A.run c₀ (pairDel P a b) (ℓ + 1 + 1) j =
        A.step (pairDel P a b) (ℓ + 1 + 1) (c a b) j := fun _ _ _ => rfl
    -- `S`: candidates that send in round `ℓ + 1` if placed on the layer;
    -- `N`: candidates that send in round `ℓ + 1` if not placed on the layer.
    set Sx := C.filter fun i => ∃ i' ∈ C, i' ≠ i ∧ i ∈ A.senders (c i i') with hSx
    set Nx := C.filter fun i => ∃ j ∈ C, ∃ j' ∈ C, j ≠ j' ∧ i ≠ j ∧ i ≠ j' ∧
      i ∈ A.senders (c j j') with hNx
    have hS : ∀ i ∈ Sx, ∀ i' ∈ C, i' ≠ i → i ∈ A.senders (c i i') := by
      intro i hi i' hi' hne
      obtain ⟨hiC, i'', hi'', hne', hs⟩ := Finset.mem_filter.1 hi
      rw [A.senders_iff_of_eq (hP2 i hiC i'' hi'' i hiC i' hi' (Ne.symm hne') (Ne.symm hne) i
        (by simp))] at hs
      exact hs
    have hnS : ∀ i ∈ C, i ∉ Sx → ∀ i' ∈ C, i' ≠ i → i ∉ A.senders (c i i') :=
      fun i hi hiS i' hi' hne hs => hiS (Finset.mem_filter.2 ⟨hi, i', hi', hne, hs⟩)
    have hN : ∀ i ∈ Nx, ∀ j ∈ C, ∀ j' ∈ C, j ≠ j' → i ≠ j → i ≠ j' → i ∈ A.senders (c j j') := by
      intro i hi j hj j' hj' hjj' hij hij'
      obtain ⟨-, k, hk, k', hk', hkk', hik, hik', hs⟩ := Finset.mem_filter.1 hi
      rw [A.senders_iff_of_eq (hP2 k hk k' hk' j hj j' hj' hkk' hjj' i (by tauto))] at hs
      exact hs
    have hnN : ∀ i ∈ C, i ∉ Nx → ∀ j ∈ C, ∀ j' ∈ C, j ≠ j' → i ≠ j → i ≠ j' →
        i ∉ A.senders (c j j') :=
      fun i hi hiN j hj j' hj' hjj' hij hij' hs =>
        hiN (Finset.mem_filter.2 ⟨hi, j, hj, j', hj', hjj', hij, hij', hs⟩)
    -- sizes
    have hpow : 2 ^ (L + 1 - ℓ) = 2 * 2 ^ (L + 1 - (ℓ + 1)) := by
      rw [show L + 1 - ℓ = (L + 1 - (ℓ + 1)) + 1 by omega, pow_succ]; ring
    have hh2 : 2 ≤ 2 ^ (L + 1 - (ℓ + 1)) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hpow] at hcard
    set h := 2 ^ (L + 1 - (ℓ + 1))
    -- `P(ℓ+1)` (2) when every candidate pair execution has at least two senders
    have coll : ∀ C' ⊆ C, (∀ a ∈ C', ∀ b ∈ C', a ≠ b → 1 < (A.senders (c a b)).card) →
        ∀ a₁ ∈ C', ∀ b₁ ∈ C', ∀ a₂ ∈ C', ∀ b₂ ∈ C', a₁ ≠ b₁ → a₂ ≠ b₂ → ∀ j,
        (j = a₁ ∨ j = b₁ ↔ j = a₂ ∨ j = b₂) →
        A.run c₀ (pairDel P a₁ b₁) (ℓ + 1 + 1) j = A.run c₀ (pairDel P a₂ b₂) (ℓ + 1 + 1) j := by
      intro C' hC' hmany a₁ h₁ b₁ h₁' a₂ h₂ b₂ h₂' n₁ n₂ j hj
      rw [hnext, hnext, A.step_pairDel_of_one_lt _ _ _ _ (hmany a₁ h₁ b₁ h₁' n₁),
        A.step_pairDel_of_one_lt _ _ _ _ (hmany a₂ h₂ b₂ h₂' n₂)]
      congr 1
      exact hP2 a₁ (hC' h₁) b₁ (hC' h₁') a₂ (hC' h₂) b₂ (hC' h₂') n₁ n₂ j hj
    have P3old : ∀ C' ⊆ C, (∀ a ∈ C', ∀ b ∈ C', a ≠ b → A.senders (c a b) ≠ {a}) →
        ∀ a ∈ C', ∀ b ∈ C', a ≠ b → ∀ r, 1 ≤ r → r ≤ ℓ + 1 →
        A.senders (A.run c₀ (pairDel P a b) r) ≠ {a} := by
      intro C' hC' hnew a ha b hb hab r hr1 hr2
      rcases Nat.lt_or_ge r (ℓ + 1) with hr | hr
      · exact hP3 a (hC' ha) b (hC' hb) hab r hr1 (by omega)
      · obtain rfl : r = ℓ + 1 := by omega
        exact hnew a ha b hb hab
    have ne_single : ∀ {X : Finset I} {a : I}, 1 < X.card → X ≠ {a} :=
      fun h e => by rw [e] at h; simp at h
    by_cases hI : 2 ≤ Nx.card
    · -- Case I: two processes that send if not placed are removed
      obtain ⟨n₁, hn₁, n₂, hn₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < Nx.card)
      have hn₁C : n₁ ∈ C := (Finset.mem_filter.1 hn₁).1
      have hn₂C : n₂ ∈ C := (Finset.mem_filter.1 hn₂).1
      set C' := (C.erase n₁).erase n₂
      have hC'C : C' ⊆ C := (erase_subset _ _).trans (erase_subset _ _)
      have hmem : ∀ a ∈ C', a ∈ C ∧ a ≠ n₁ ∧ a ≠ n₂ := by
        intro a ha
        simp only [C', mem_erase] at ha
        exact ⟨ha.2.2, ha.2.1, ha.1⟩
      have hmany : ∀ a ∈ C', ∀ b ∈ C', a ≠ b → 1 < (A.senders (c a b)).card := by
        intro a ha b hb hab
        obtain ⟨haC, ha1, ha2⟩ := hmem a ha
        obtain ⟨hbC, hb1, hb2⟩ := hmem b hb
        exact Finset.one_lt_card.2 ⟨n₁, hN n₁ hn₁ a haC b hbC hab (Ne.symm ha1) (Ne.symm hb1),
          n₂, hN n₂ hn₂ a haC b hbC hab (Ne.symm ha2) (Ne.symm hb2), hne⟩
      refine ⟨C', hC'C.trans hC, ?_, coll C' hC'C hmany,
        P3old C' hC'C (fun a ha b hb hab => ne_single (hmany a ha b hb hab))⟩
      have h1 := Finset.card_erase_of_mem hn₁C
      have h2 : n₂ ∈ C.erase n₁ := Finset.mem_erase.2 ⟨Ne.symm hne, hn₂C⟩
      have h3 := Finset.card_erase_of_mem h2
      simp only [C']
      omega
    by_cases hII : C.card ≤ 2 * Sx.card
    · -- Case II: keep exactly the processes that send if placed
      have hSC : Sx ⊆ C := Finset.filter_subset _ _
      have hmany : ∀ a ∈ Sx, ∀ b ∈ Sx, a ≠ b → 1 < (A.senders (c a b)).card := by
        intro a ha b hb hab
        refine Finset.one_lt_card.2 ⟨a, hS a ha b (hSC hb) (Ne.symm hab), b, ?_, hab⟩
        rw [hcomm]; exact hS b hb a (hSC ha) hab
      exact ⟨Sx, hSC.trans hC, by omega, coll Sx hSC hmany,
        P3old Sx hSC (fun a ha b hb hab => ne_single (hmany a ha b hb hab))⟩
    · -- Case III: keep the candidates that send neither if placed nor if not placed
      set C' := C \ (Sx ∪ Nx)
      have hC'C : C' ⊆ C := sdiff_subset
      have hmem : ∀ a ∈ C', a ∈ C ∧ a ∉ Sx ∧ a ∉ Nx := by
        intro a ha
        simp only [C', mem_sdiff, mem_union, not_or] at ha
        exact ha
      -- candidates of `C'` never send in round `ℓ + 1` of candidate-pair executions
      have hsilent : ∀ x ∈ C', ∀ a ∈ C', ∀ b ∈ C', a ≠ b → x ∉ A.senders (c a b) := by
        intro x hx a ha b hb hab
        obtain ⟨hxC, hxS, hxN⟩ := hmem x hx
        obtain ⟨haC, -, -⟩ := hmem a ha
        obtain ⟨hbC, -, -⟩ := hmem b hb
        by_cases hxa : x = a
        · subst hxa; exact hnS x hxC hxS b hbC (Ne.symm hab)
        by_cases hxb : x = b
        · subst hxb; rw [hcomm]; exact hnS x hxC hxS a haC hab
        exact hnN x hxC hxN a haC b hbC hab hxa hxb
      refine ⟨C', hC'C.trans hC, ?_, ?_, P3old C' hC'C ?_⟩
      · have h1 := Finset.card_le_card_sdiff_add_card (s := C) (t := Sx ∪ Nx)
        have h2 := Finset.card_union_le Sx Nx
        simp only [C']
        omega
      · intro a₁ h₁ b₁ h₁' a₂ h₂ b₂ h₂' n₁ n₂ j hj
        rw [hnext, hnext]
        have hneither : ∀ x, x ∉ C' → ¬ (x = a₁ ∨ x = b₁) ∧ ¬ (x = a₂ ∨ x = b₂) := by
          intro x hx
          refine ⟨?_, ?_⟩ <;> rintro (rfl | rfl) <;> contradiction
        have hst : ∀ x, x ∉ C' → c a₁ b₁ x = c a₂ b₂ x := fun x hx =>
          hP2 a₁ (hC'C h₁) b₁ (hC'C h₁') a₂ (hC'C h₂) b₂ (hC'C h₂') n₁ n₂ x
            (iff_of_false (hneither x hx).1 (hneither x hx).2)
        have hsend : A.senders (c a₁ b₁) = A.senders (c a₂ b₂) := by
          ext x
          by_cases hx : x ∈ C'
          · exact iff_of_false (hsilent x hx a₁ h₁ b₁ h₁' n₁) (hsilent x hx a₂ h₂ b₂ h₂' n₂)
          · exact A.senders_iff_of_eq (hst x hx)
        apply A.step_apply_eq
          (hP2 a₁ (hC'C h₁) b₁ (hC'C h₁') a₂ (hC'C h₂) b₂ (hC'C h₂') n₁ n₂ j hj) hsend
        · intro x hx
          exact hst x (fun hxC => hsilent x hxC a₁ h₁ b₁ h₁' n₁ hx)
        · intro x _
          exact mem_pairDel_iff hj _ _ _
      · intro a ha b _ hab hS1
        exact hsilent a ha a ha b ‹_› hab (by rw [hS1]; exact mem_singleton_self _)

/-- The pair chosen in a stage of Theorem 12: two distinct candidates neither of which sends alone
in rounds `0, …, L` of `β_{a,b}`. -/
theorem exists_pair (c₀ : I → S) (P : Finset I) (jstar : I) (hstar : A.senders c₀ = {jstar})
    (hjP : jstar ∈ P) (C₀ : Finset I) (hdisj : Disjoint C₀ P) (L : ℕ)
    (hC₀card : 2 ^ (L + 1) ≤ C₀.card) :
    ∃ a ∈ C₀, ∃ b ∈ C₀, a ≠ b ∧ ∀ r ≤ L,
      A.senders (A.run c₀ (pairDel P a b) r) ≠ {a} ∧
      A.senders (A.run c₀ (pairDel P a b) r) ≠ {b} := by
  obtain ⟨C, hC, hcard, -, hP3⟩ := A.claim_13 c₀ P jstar hstar hjP C₀ L hC₀card L le_rfl
  have : 1 < C.card := by simp at hcard; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 this
  have hnot : ∀ x ∈ C₀, jstar ≠ x := fun x hx e => Finset.disjoint_left.1 hdisj hx (e ▸ hjP)
  refine ⟨a, hC ha, b, hC hb, hab, fun r hr => ?_⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp only [run_zero, hstar, ne_eq, Finset.singleton_inj]
    exact ⟨hnot a (hC ha), hnot b (hC hb)⟩
  · refine ⟨hP3 a ha b hb hab r hr0 hr, ?_⟩
    rw [pairDel_comm]
    exact hP3 b hb a ha (Ne.symm hab) r hr0 hr

/-- During `β_{a,b}`, as long as neither `a` nor `b` has sent alone, only processes of
`P ∪ {a, b}` can be informed. -/
theorem informed_pairDel_subset (c₀ : I → S) (P : Finset I) (a b : I) (inf₀ : I → Prop)
    (h0 : ∀ x, inf₀ x → x ∈ P) (T : ℕ)
    (hT : ∀ r < T, A.senders (A.run c₀ (pairDel P a b) r) ≠ {a} ∧
      A.senders (A.run c₀ (pairDel P a b) r) ≠ {b}) :
    ∀ x, A.informed c₀ (pairDel P a b) inf₀ T x → x ∈ insert a (insert b P) := by
  intro x hx
  refine A.informed_of_invariant c₀ (pairDel P a b) inf₀
    (fun t x => t ≤ T → x ∈ insert a (insert b P))
    (fun x hx _ => by simp [h0 x hx]) (fun t x h ht => h (by omega)) ?_ T x hx le_rfl
  intro t x j _ hH hj htT
  have hjH : j ∈ A.hearers (pairDel P a b) (t + 1) (A.run c₀ (pairDel P a b) t) x := by
    rw [hH]; exact mem_singleton_self _
  rw [mem_hearers] at hjH
  obtain ⟨hjs, hjx⟩ := hjH
  set B := A.senders (A.run c₀ (pairDel P a b) t)
  rcases hjx with hjx | rfl
  · by_cases h1 : B.card = 1
    · obtain ⟨y, hy⟩ := Finset.card_eq_one.1 h1
      have hjy : j = y := by rw [hy] at hjs; simpa using hjs
      subst hjy
      have hjm := hj (by omega)
      by_cases hjP : j ∈ P
      · simpa [pairDel, h1, hjP] using hjx
      · exfalso
        simp only [mem_insert, hjP, or_false] at hjm
        rcases hjm with rfl | rfl
        · exact (hT t (by omega)).1 hy
        · exact (hT t (by omega)).2 hy
    · exfalso
      have hall : A.hearers (pairDel P a b) (t + 1) (A.run c₀ (pairDel P a b) t) x = B :=
        A.hearers_eq_senders (fun y _ => by simp [B, pairDel, h1])
      rw [hall] at hH
      exact h1 (by rw [hH]; simp)
  · exact hj (by omega)

/-- With all messages reaching everybody, only `i₀` is informed until it sends alone. -/
theorem informed_univ_subset (c₀ : I → S) (i₀ : I) (T : ℕ)
    (hT : ∀ r < T, A.senders (A.run c₀ (fun _ _ _ => univ) r) ≠ {i₀}) :
    ∀ x, A.informed c₀ (fun _ _ _ => univ) (· = i₀) T x → x = i₀ := by
  intro x hx
  refine A.informed_of_invariant c₀ (fun _ _ _ => univ) (· = i₀)
    (fun t x => t ≤ T → x = i₀) (fun x hx _ => hx) (fun t x h ht => h (by omega)) ?_ T x hx le_rfl
  intro t x j _ hH hj htT
  have hall : A.hearers (fun _ _ _ => univ) (t + 1) (A.run c₀ (fun _ _ _ => univ) t) x =
      A.senders (A.run c₀ (fun _ _ _ => univ) t) := A.hearers_eq_senders (fun y _ => mem_univ _)
  rw [hall, hj (by omega)] at hH
  exact absurd hH (hT t (by omega))

end Algorithm

end Podc.BroadcastUnreliableRadio
