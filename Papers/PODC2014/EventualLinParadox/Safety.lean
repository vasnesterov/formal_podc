import Papers.PODC2014.EventualLinParadox.Basic

/-!
# Linearizability is a safety property; `t`-linearizability is not (Section 3.2)

Guerraoui, Ruppert. *A Paradox of Eventual Linearizability in Shared Memory.* PODC 2014.

* `linearizable_of_forall_take` — linearizability is **limit-closed** for types with finite
  nondeterminism and finitely many initial states (cited by the paper from Lynch and
  Guerraoui–Ruppert [8]; used for Proposition 11 / Theorem 12). Together with `Lemma 6`
  (`TLinearizable.prefix`) this says that linearizability is a safety property.
* `tLinearizable_not_limitClosed` — for `t > 0`, `t`-linearizability is not limit-closed, even
  for the deterministic fetch&increment type (the example of Section 3.2, with `t = 2`).
* `linearizable_not_limitClosed_of_infiniteNondet` — the finite-nondeterminism hypothesis is
  needed: for a type with infinite nondeterminism (`chooseType`), linearizability is not
  limit-closed.

The proof of limit-closure is König's lemma: the nodes of the tree are finite gap-free prefixes
`[(a₀, r₀), …, (aₙ₋₁, rₙ₋₁)]` of linearizations, a node is *good* if it is a prefix of a
(compacted) linearization of `take H m` for infinitely many `m`; each node has finitely many
possible children (the operation at index `n` is invoked before the `(n+1)`-st response of `H`,
its response is bounded by finite nondeterminism along the finitely many reachable states), so
pigeonhole gives a good child. Legality of the limit is a second, per-object application of
König's lemma, to the state trajectories.
-/

namespace Podc.EventualLinParadox

section Konig

/-- König's lemma in the form used here: if the root is good and every good node has a good
child, then there is an infinite branch all of whose finite prefixes are good. -/
lemma exists_seq_of_good {E : Type} (Good : List E → Prop) (h0 : Good [])
    (hs : ∀ L, Good L → ∃ e, Good (L ++ [e])) :
    ∃ f : ℕ → E, ∀ n, Good ((List.range n).map f) := by
  choose g hg using hs
  let seq : ℕ → {L // Good L} := fun n =>
    Nat.rec ⟨[], h0⟩ (fun _ L => ⟨L.1 ++ [g L.1 L.2], hg L.1 L.2⟩) n
  have key : ∀ n, (seq n).1 = (List.range n).map (fun n => g (seq n).1 (seq n).2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, ← ih]; rfl
  exact ⟨fun n => g (seq n).1 (seq n).2, fun n => key n ▸ (seq n).2⟩

/-- Pigeonhole: if `L` extends to infinitely many `m`, and (for large `m`) every extension
continues with a child from a finite set `C`, then some child extends to infinitely many `m`. -/
lemma exists_infinite_child {E : Type} {Pm : List E → ℕ → Prop} {L : List E}
    (hL : {m | Pm L m}.Infinite) {C : Set E} (hC : C.Finite) (M : ℕ)
    (h : ∀ m, M ≤ m → Pm L m → ∃ e ∈ C, Pm (L ++ [e]) m) :
    ∃ e, {m | Pm (L ++ [e]) m}.Infinite := by
  by_contra hne
  push Not at hne
  apply hL
  refine ((Set.finite_lt_nat M).union (hC.biUnion fun e _ => hne e)).subset ?_
  intro m hm
  by_cases hmM : m < M
  · exact Or.inl hmM
  · obtain ⟨e, he, hPe⟩ := h m (by omega) hm
    exact Or.inr (Set.mem_biUnion he hPe)

/-- König's lemma for state trajectories: with finitely many initial states and finitely many
successors, if there are trajectories of every finite length, there is an infinite one. -/
lemma exists_traj_of_forall {Q : Type} {init : Set Q} (hinit : init.Finite)
    {step : ℕ → Q → Q → Prop} (hstep : ∀ k q, {q' | step k q q'}.Finite)
    (h : ∀ n, ∃ qs : ℕ → Q, qs 0 ∈ init ∧ ∀ k < n, step k (qs k) (qs (k + 1))) :
    ∃ qs : ℕ → Q, qs 0 ∈ init ∧ ∀ k, step k (qs k) (qs (k + 1)) := by
  let Pm : List Q → ℕ → Prop := fun L n => ∃ qs : ℕ → Q, qs 0 ∈ init ∧
    (∀ k < n, step k (qs k) (qs (k + 1))) ∧ ∀ i (hi : i < L.length), qs i = L[i]
  have hroot : {n | Pm [] n}.Infinite := by
    convert Set.infinite_univ (α := ℕ)
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨qs, h0, hs⟩ := h n
    exact ⟨qs, h0, hs, fun i hi => absurd hi (by simp)⟩
  have hchild : ∀ L, {n | Pm L n}.Infinite → ∃ e, {n | Pm (L ++ [e]) n}.Infinite := by
    intro L hL
    refine exists_infinite_child hL (C := init ∪ ⋃ i : Fin L.length, {q' | step i L[i] q'})
      (hinit.union (Set.finite_iUnion fun i => hstep _ _)) (L.length + 1) ?_
    rintro n hn ⟨qs, h0, hs, hq⟩
    refine ⟨qs L.length, ?_, qs, h0, hs, fun i hi => ?_⟩
    · rcases Nat.eq_zero_or_pos L.length with hl | hl
      · left; rw [hl]; exact h0
      · right
        refine Set.mem_iUnion.2 ⟨⟨L.length - 1, by omega⟩, ?_⟩
        have := hs (L.length - 1) (by omega)
        rw [Nat.sub_add_cancel hl, hq _ (by omega)] at this
        exact this
    · rw [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [List.getElem_append_left hi]; exact hq i hi
      · subst hi; simp
  obtain ⟨f, hf⟩ := exists_seq_of_good _ hroot hchild
  refine ⟨f, ?_, fun k => ?_⟩
  · obtain ⟨n, ⟨qs, h0, -, hq⟩⟩ := (hf 1).nonempty
    have := hq 0 (by simp)
    simp only [List.getElem_map, List.getElem_range] at this
    rw [← this]; exact h0
  · obtain ⟨n, ⟨qs, -, hs, hq⟩, hn⟩ := (hf (k + 2)).exists_gt k
    have e1 := hq k (by simp)
    have e2 := hq (k + 1) (by simp)
    simp only [List.getElem_map, List.getElem_range] at e1 e2
    rw [← e1, ← e2]; exact hs k hn

end Konig

variable {P X Op Res Q : Type}

section Reach

/-- The states reachable in `n` steps of `step` from `init`. -/
def reach (init : Set Q) (step : ℕ → Q → Q → Prop) : ℕ → Set Q
  | 0 => init
  | n + 1 => {q' | ∃ q ∈ reach init step n, step n q q'}

lemma reach_finite {init : Set Q} (hinit : init.Finite) {step : ℕ → Q → Q → Prop}
    (hstep : ∀ k q, {q' | step k q q'}.Finite) : ∀ n, (reach init step n).Finite
  | 0 => hinit
  | n + 1 => by
    refine ((reach_finite hinit hstep n).biUnion fun q _ => hstep n q).subset ?_
    rintro q' ⟨q, hq, hs⟩
    exact Set.mem_biUnion hq hs

lemma mem_reach {init : Set Q} {step : ℕ → Q → Q → Prop} (qs : ℕ → Q) (h0 : qs 0 ∈ init) :
    ∀ n, (∀ k < n, step k (qs k) (qs (k + 1))) → qs n ∈ reach init step n
  | 0, _ => h0
  | n + 1, h => ⟨qs n, mem_reach qs h0 n (fun k hk => h k (by omega)), h n (by omega)⟩

lemma seqStep_finite {T : ObjType Q Op Res} (hT : T.FiniteNondet) (H : History P X Op Res)
    (x : X) (e : Option (ℕ × Res)) (q : Q) : {q' | SeqStep T H x e q q'}.Finite := by
  rcases e with _ | ⟨a, r⟩
  · exact (Set.finite_singleton q).subset fun q' (h : q' = q) => h
  · have hsub : {op | ∃ p, H a = some (.inv p x op)}.Subsingleton := by
      rintro o ⟨p, hp⟩ o' ⟨p', hp'⟩; rw [hp] at hp'; cases hp'; rfl
    refine ((Set.finite_singleton q).union
      (hsub.finite.biUnion fun op _ => (hT q op).image Prod.snd)).subset ?_
    rintro q' (⟨p, op, hHa, hδ⟩ | ⟨-, rfl⟩)
    · right; exact Set.mem_biUnion ⟨p, hHa⟩ ⟨(r, q'), hδ, rfl⟩
    · left; rfl

end Reach

section Compact

variable {spec : X → ObjType Q Op Res} {H : History P X Op Res}

/-- A sequential history without gaps: its entries occupy an initial segment of positions. -/
def SeqHist.DownClosed (S : SeqHist Res) : Prop := ∀ i j, i ≤ j → S j ≠ none → S i ≠ none

/-- Remove position `i` of a sequential history (shifting the later entries down). -/
def SeqHist.erase (S : SeqHist Res) (i : ℕ) : SeqHist Res :=
  fun k => if k < i then S k else S (k + 1)

/-- Removing a gap preserves being a `t`-linearization. -/
lemma IsTLin.erase {t i : ℕ} {S : SeqHist Res} (h : IsTLin spec H t S) (hi : S i = none) :
    IsTLin spec H t (S.erase i) := by
  have hφ : ∀ k, S.erase i k = S (if k < i then k else k + 1) := fun k => by
    unfold SeqHist.erase; split_ifs <;> rfl
  have hpre : ∀ k e, S k = some e → S.erase i (if k < i then k else k - 1) = some e := by
    intro k e hk
    have : k ≠ i := by rintro rfl; rw [hi] at hk; cases hk
    by_cases hki : k < i
    · rw [ite_eq_left hki, hφ, ite_eq_left hki]; exact hk
    · rw [ite_eq_right hki, hφ, ite_eq_right (by omega), show k - 1 + 1 = k by omega]; exact hk
  have hpre_lt : ∀ k k', k < k' → S k ≠ none → S k' ≠ none →
      (if k < i then k else k - 1) < (if k' < i then k' else k' - 1) := by
    intro k k' hkk' hk hk'
    have : k ≠ i := by rintro rfl; exact hk hi
    have : k' ≠ i := by rintro rfl; exact hk' hi
    split_ifs <;> omega
  have hmem : ∀ a, (S.erase i).Mem a → S.Mem a := by
    rintro a ⟨k, r, hk⟩; rw [hφ] at hk; exact ⟨_, r, hk⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k k' a r r' hk hk'
    rw [hφ] at hk hk'
    have := h.nodup _ _ a r r' hk hk'
    split_ifs at this <;> omega
  · obtain ⟨hinv, hq⟩ := h.legal
    refine ⟨fun k a r hk => by rw [hφ] at hk; exact hinv _ a r hk, fun x => ?_⟩
    obtain ⟨q, hq0, hqs⟩ := hq x
    have hgap : q (i + 1) = q i := by have := hqs i; rw [hi] at this; exact this
    refine ⟨fun k => if k ≤ i then q k else q (k + 1), by simpa using hq0, fun k => ?_⟩
    rw [hφ]
    dsimp only
    rcases lt_trichotomy k i with hk | rfl | hk
    · rw [ite_eq_left hk, ite_eq_left hk.le, ite_eq_left (by omega : k + 1 ≤ i)]; exact hqs k
    · rw [ite_eq_right (lt_irrefl _), ite_eq_left le_rfl, ite_eq_right (by omega : ¬ k + 1 ≤ k),
        ← hgap]
      exact hqs (k + 1)
    · rw [ite_eq_right (by omega : ¬ k < i), ite_eq_right (by omega : ¬ k ≤ i),
        ite_eq_right (by omega : ¬ k + 1 ≤ i)]
      exact hqs (k + 1)
  · intro a j r hj
    obtain ⟨k, r', hk⟩ := h.complete a j r hj
    exact ⟨_, r', hpre k _ hk⟩
  · intro a b j r hj htj hjb hb hbm
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ := h.rt a b j r hj htj hjb hb (hmem b hbm)
    exact ⟨_, _, r1, r2, hpre_lt k1 k2 h12 (by rw [h1]; simp) (by rw [h2]; simp),
      hpre k1 _ h1, hpre k2 _ h2⟩
  · intro a j r hj htj
    obtain ⟨k, hk⟩ := h.resp a j r hj htj
    exact ⟨_, hpre k _ hk⟩

/-- A `t`-linearization with finitely many entries can be compacted to a gap-free one. -/
lemma exists_downClosed {t : ℕ} : ∀ (K : ℕ) (S : SeqHist Res), IsTLin spec H t S →
    (∀ k, K ≤ k → S k = none) → ∃ S', IsTLin spec H t S' ∧ S'.DownClosed
  | 0, S, h, hK => ⟨S, h, fun _ j _ hj => absurd (hK j (Nat.zero_le _)) hj⟩
  | K + 1, S, h, hK => by
    by_cases hdc : S.DownClosed
    · exact ⟨S, h, hdc⟩
    · simp only [SeqHist.DownClosed, not_forall, not_not] at hdc
      obtain ⟨i, j, hij, hj, hi⟩ := hdc
      have hjK : j < K + 1 := by by_contra hc; exact hj (hK j (by omega))
      exact exists_downClosed K (S.erase i) (h.erase hi) (fun k hk => by
        unfold SeqHist.erase; rw [ite_eq_right (by omega)]; exact hK _ (by omega))

/-- A `t`-linearization of a finite prefix has finitely many entries. -/
lemma IsTLin.exists_bound_take {t m : ℕ} {S : SeqHist Res} (h : IsTLin spec (take H m) t S) :
    ∃ K, ∀ k, K ≤ k → S k = none := by
  have hfin : {k | S k ≠ none}.Finite := by
    apply Set.Finite.of_finite_image (f := fun k => ((S k).map Prod.fst).getD 0)
    · refine (Set.finite_lt_nat m).subset ?_
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨⟨a, r⟩, he⟩ := Option.ne_none_iff_exists'.1 hk
      have := ((invoked_take H).1 (h.legal.1 k a r he)).1
      simp [he, this]
    · intro k hk k' hk' hkk'
      obtain ⟨⟨a, r⟩, he⟩ := Option.ne_none_iff_exists'.1 hk
      obtain ⟨⟨a', r'⟩, he'⟩ := Option.ne_none_iff_exists'.1 hk'
      simp only [he, he', Option.map_some, Option.getD_some] at hkk'
      subst hkk'
      exact h.nodup k k' a r r' he he'
  obtain ⟨K, hK⟩ := hfin.bddAbove
  exact ⟨K + 1, fun k hk => by by_contra hc; have := hK hc; omega⟩

lemma exists_downClosed_take {t m : ℕ} (h : TLinearizable spec (take H m) t) :
    ∃ S, IsTLin spec (take H m) t S ∧ S.DownClosed := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨K, hK⟩ := hS.exists_bound_take
  exact exists_downClosed K S hS hK

end Compact

section Counting

variable {spec : X → ObjType Q Op Res} {H : History P X Op Res}

open Classical in
/-- The positions `< B` of `H` carrying a response. -/
noncomputable def respSet (H : History P X Op Res) (B : ℕ) : Finset ℕ :=
  (Finset.range B).filter fun j => ∃ a r, H j = some (.res a r)

lemma mem_respSet {B j : ℕ} : j ∈ respSet H B ↔ j < B ∧ ∃ a r, H j = some (.res a r) := by
  classical
  simp [respSet]

/-- The operation answered at position `j` (junk if there is no response at `j`). -/
def opOf (H : History P X Op Res) (j : ℕ) : ℕ :=
  match H j with
  | some (.res a _) => a
  | _ => 0

lemma opOf_eq {j a : ℕ} {r : Res} (h : H j = some (.res a r)) : opOf H j = a := by
  simp [opOf, h]

lemma opOf_injOn (hH : WellFormed H) (B : ℕ) : Set.InjOn (opOf H) (respSet H B) := by
  intro j hj j' hj' he
  obtain ⟨-, a, r, ha⟩ := mem_respSet.1 hj
  obtain ⟨-, a', r', ha'⟩ := mem_respSet.1 hj'
  rw [opOf_eq ha, opOf_eq ha'] at he
  subst he
  exact hH.res_unique a j j' r r' ha ha'

/-- If the operations `g j` (`j ∈ J`, `g` injective) all occur at positions `< N`, then
`|J| ≤ N`. -/
lemma card_le_of_forall_idx {S : SeqHist Res} {J : Finset ℕ} {g : ℕ → ℕ} (hg : Set.InjOn g J)
    {N : ℕ} (h : ∀ j ∈ J, ∃ k < N, ∃ r, S k = some (g j, r)) : J.card ≤ N := by
  classical
  rw [← Finset.card_image_of_injOn hg]
  calc (J.image g).card
      ≤ ((Finset.range N).image fun k => ((S k).map Prod.fst).getD 0).card := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨k, hk, r, hS⟩ := h j hj
        exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk, by simp [hS]⟩
    _ ≤ N := Finset.card_image_le.trans (by simp)

lemma Legal.of_take {m : ℕ} {S : SeqHist Res} (h : Legal spec (take H m) S) : Legal spec H S :=
  h.congr fun k a r hk => (take_of_lt H ((invoked_take H).1 (h.1 k a r hk)).1).symm

/-- The operation at index `k` of a linearization of a prefix is invoked before the
`(k+1)`-st response of `H`. -/
lemma IsTLin.lt_of_card (hH : WellFormed H) {m : ℕ} {S : SeqHist Res}
    (hS : IsTLin spec (take H m) 0 S) {k a : ℕ} {r : Res} (hk : S k = some (a, r)) {B : ℕ}
    (hB : k + 1 ≤ (respSet H B).card) : a < B := by
  by_contra hab
  push Not at hab
  have ham : a < m := ((invoked_take H).1 (hS.legal.1 k a r hk)).1
  have := card_le_of_forall_idx (S := S) (opOf_injOn hH B) (N := k) fun j hj => by
    obtain ⟨hjB, c, rc, hc⟩ := mem_respSet.1 hj
    have hc' : take H m j = some (.res c rc) := by rw [take_of_lt H (by omega)]; exact hc
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ :=
      hS.rt c a j rc hc' (Nat.zero_le _) (by omega) (hS.legal.1 k a r hk) ⟨k, r, hk⟩
    have := hS.nodup k2 k a r2 r h2 hk
    exact ⟨k1, by omega, r1, by rw [opOf_eq hc]; exact h1⟩
  omega

/-- A gap-free linearization of a prefix with at least `n + 1` responses has an entry at
index `n`. -/
lemma IsTLin.ne_none_of_card (hH : WellFormed H) {m : ℕ} {S : SeqHist Res}
    (hS : IsTLin spec (take H m) 0 S) (hdc : S.DownClosed) {n B : ℕ} (hBm : B ≤ m)
    (hB : n + 1 ≤ (respSet H B).card) : S n ≠ none := by
  intro hn
  have := card_le_of_forall_idx (S := S) (opOf_injOn hH B) (N := n) fun j hj => by
    obtain ⟨hjB, c, rc, hc⟩ := mem_respSet.1 hj
    have hc' : take H m j = some (.res c rc) := by rw [take_of_lt H (by omega)]; exact hc
    obtain ⟨k, r', hk⟩ := hS.complete c j rc hc'
    refine ⟨k, ?_, r', by rw [opOf_eq hc]; exact hk⟩
    by_contra hkn
    exact hdc n k (by omega) (by rw [hk]; simp) hn
  omega

/-- In a gap-free linearization of a prefix, an operation responding at position `j` sits at an
index `< j` (all operations before it are invoked before its response). -/
lemma IsTLin.idx_lt (hH : WellFormed H) {m : ℕ} {S : SeqHist Res}
    (hS : IsTLin spec (take H m) 0 S) (hdc : S.DownClosed) {a j : ℕ} {r : Res}
    (hj : H j = some (.res a r)) (hjm : j < m) : ∃ k < j, S k = some (a, r) := by
  have hj' : take H m j = some (.res a r) := by rw [take_of_lt H hjm]; exact hj
  obtain ⟨k, hk⟩ := hS.resp a j r hj' (Nat.zero_le _)
  refine ⟨k, ?_, hk⟩
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range (k + 1)) (t := Finset.range j)
    (fun i => ((S i).map Prod.fst).getD 0) ?_ ?_
  · simpa using hcard
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢
    obtain ⟨⟨b, rb⟩, hb⟩ := Option.ne_none_iff_exists'.1
      (hdc i k (by omega) (by rw [hk]; simp))
    simp only [hb, Option.map_some, Option.getD_some]
    by_cases hba : b = a
    · subst hba; exact (hH.res_inv b j r hj).1
    · by_contra hbj
      have hbinv := hS.legal.1 i b rb hb
      have hbm := ((invoked_take H).1 hbinv).1
      have hne : b ≠ j := by
        rintro rfl
        obtain ⟨p, x, op, hp⟩ := ((invoked_take H).1 hbinv).2
        rw [hp] at hj; cases hj
      obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ :=
        hS.rt a b j r hj' (Nat.zero_le _) (by omega) hbinv ⟨i, rb, hb⟩
      have := hS.nodup k1 k a r1 r h1 hk
      have := hS.nodup k2 i b r2 rb h2 hb
      omega
  · intro i hi i' hi' he
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    obtain ⟨⟨b, rb⟩, hb⟩ := Option.ne_none_iff_exists'.1
      (hdc i k (by omega) (by rw [hk]; simp))
    obtain ⟨⟨b', rb'⟩, hb'⟩ := Option.ne_none_iff_exists'.1
      (hdc i' k (by omega) (by rw [hk]; simp))
    simp only [hb, hb', Option.map_some, Option.getD_some] at he
    subst he
    exact hS.nodup i i' b rb rb' hb hb'

/-- With finitely many processes, a well-formed history with finitely many responses has
finitely many events. -/
lemma exists_take_eq_of_finite [Finite P] (hH : WellFormed H)
    (hR : {j | ∃ a r, H j = some (.res a r)}.Finite) : ∃ m, take H m = H := by
  obtain ⟨B0, hB0⟩ := hR.bddAbove
  let procOf : ℕ → Option P := fun a =>
    match H a with
    | some (.inv p _ _) => some p
    | _ => none
  have hI : {a | B0 < a ∧ ∃ p x op, H a = some (.inv p x op)}.Finite := by
    apply Set.Finite.of_finite_image (f := procOf) (Set.toFinite _)
    rintro a ⟨ha, p, x, op, hp⟩ b ⟨hb, p', x', op', hp'⟩ he
    simp only [procOf, hp, hp', Option.some.injEq] at he
    subst he
    by_contra hab
    have key : ∀ a b x x' op op', B0 < a → H a = some (.inv p x op) →
        H b = some (.inv p x' op') → a < b → False := by
      intro a b x x' op op' ha hpa hpb hab
      obtain ⟨j, r, hjb, hj⟩ := hH.seq a b p x x' op op' hpa hpb hab
      have := (hH.res_inv a j r hj).1
      have := hB0 ⟨a, r, hj⟩
      omega
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key a b x x' op op' ha hp hp' h
    · exact key b a x' x op' op hb hp' hp h
  obtain ⟨B1, hB1⟩ := hI.bddAbove
  refine ⟨B0 + B1 + 1, funext fun i => ?_⟩
  rw [take_apply]
  split_ifs with hi
  · rfl
  · cases hHi : H i with
    | none => rfl
    | some e =>
      cases e with
      | inv p x op => have := hB1 ⟨by omega, p, x, op, hHi⟩; omega
      | res a r => have := hB0 ⟨a, r, hHi⟩; omega

lemma exists_card_respSet (hR : {j | ∃ a r, H j = some (.res a r)}.Infinite) (n : ℕ) :
    ∃ B, n ≤ (respSet H B).card := by
  obtain ⟨t, ht, hcard⟩ := hR.exists_subset_card_eq n
  refine ⟨t.sup id + 1, hcard ▸ Finset.card_le_card fun j hj => mem_respSet.2 ⟨?_, ht hj⟩⟩
  have := Finset.le_sup (f := id) hj
  simp only [id] at this
  omega

end Counting

section Main

/-- **Linearizability is limit-closed** for types with finite nondeterminism and finitely many
initial states (Section 3.2: "For deterministic objects, Lynch proved that linearizability is a
safety property. The proof extends easily to objects with finite non-determinism [8]."): if every
finite prefix of a well-formed history `H` over finitely many processes is linearizable, then
`H` is linearizable. Together with `TLinearizable.prefix` (Lemma 6, `t = 0`) this makes
linearizability a safety property. -/
theorem linearizable_of_forall_take [Finite P] {spec : X → ObjType Q Op Res}
    (hfin : ∀ x, (spec x).FiniteNondet) (hinit : ∀ x, (spec x).init.Finite)
    {H : History P X Op Res} (hH : WellFormed H) (h : ∀ m, Linearizable spec (take H m)) :
    Linearizable spec H := by
  classical
  by_cases hR : {j | ∃ a r, H j = some (.res a r)}.Finite
  · obtain ⟨m, hm⟩ := exists_take_eq_of_finite hH hR
    rw [← hm]; exact h m
  choose B hB using exists_card_respSet hR
  let Pm : List (ℕ × Res) → ℕ → Prop := fun L m => ∃ S, IsTLin spec (take H m) 0 S ∧
    S.DownClosed ∧ ∀ i (hi : i < L.length), S i = some L[i]
  have hroot : {m | Pm [] m}.Infinite := by
    convert Set.infinite_univ (α := ℕ)
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨S, hS, hdc⟩ := exists_downClosed_take (h m)
    exact ⟨S, hS, hdc, fun i hi => absurd hi (by simp)⟩
  have hchild : ∀ L, {m | Pm L m}.Infinite → ∃ e, {m | Pm (L ++ [e]) m}.Infinite := by
    intro L hL
    -- the possible responses of operation `a` at index `L.length`
    let R : ℕ → Set Res := fun a => {r | ∃ p x o, H a = some (.inv p x o) ∧
      ∃ q ∈ reach (spec x).init (fun k => SeqStep (spec x) H x L[k]?) L.length,
        ∃ q', (spec x).δ q o r q'}
    have hRfin : ∀ a, (R a).Finite := by
      intro a
      have hsub : {pxo : P × X × Op | H a = some (.inv pxo.1 pxo.2.1 pxo.2.2)}.Subsingleton := by
        rintro ⟨p, x, o⟩ h1 ⟨p', x', o'⟩ h2
        simp only [Set.mem_ofPred_eq] at h1 h2
        rw [h1] at h2; cases h2; rfl
      refine (hsub.finite.biUnion fun pxo _ =>
        (reach_finite (hinit pxo.2.1) (fun k q => seqStep_finite (hfin pxo.2.1) H pxo.2.1 L[k]? q)
          L.length).biUnion fun q _ => (hfin pxo.2.1 q pxo.2.2).image Prod.fst).subset ?_
      rintro r ⟨p, x, o, hpxo, q, hq, q', hδ⟩
      exact Set.mem_biUnion (x := (p, x, o)) hpxo (Set.mem_biUnion hq ⟨(r, q'), hδ, rfl⟩)
    have hCfin : {e : ℕ × Res | e.1 < B (L.length + 1) ∧ e.2 ∈ R e.1}.Finite := by
      refine ((Set.finite_lt_nat (B (L.length + 1))).biUnion fun a _ =>
        (Set.finite_singleton a).prod (hRfin a)).subset ?_
      rintro ⟨a, r⟩ ⟨ha, hr⟩
      exact Set.mem_biUnion ha ⟨rfl, hr⟩
    refine exists_infinite_child hL hCfin (B (L.length + 1)) ?_
    rintro m hm ⟨S, hS, hdc, hpre⟩
    obtain ⟨⟨a, r⟩, hSa⟩ := Option.ne_none_iff_exists'.1
      (hS.ne_none_of_card hH hdc hm (hB (L.length + 1)))
    refine ⟨(a, r), ⟨hS.lt_of_card hH hSa (hB (L.length + 1)), ?_⟩, S, hS, hdc, ?_⟩
    · obtain ⟨p, x, o, hHa⟩ := ((invoked_take H).1 (hS.legal.1 _ a r hSa)).2
      obtain ⟨qs, hq0, hqs⟩ := hS.legal.of_take.2 x
      refine ⟨p, x, o, hHa, qs L.length, mem_reach qs hq0 _ fun k hk => ?_, qs (L.length + 1), ?_⟩
      · have := hqs k
        rw [hpre k hk] at this
        rw [List.getElem?_eq_getElem hk]; exact this
      · have := hqs L.length
        rw [hSa] at this
        obtain ⟨p', o', hp', hδ⟩ := this.onObj ⟨p, o, hHa⟩
        rw [hHa] at hp'; cases hp'
        exact hδ
    · intro i hi
      rw [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [List.getElem_append_left hi]; exact hpre i hi
      · subst hi; simpa using hSa
  obtain ⟨f, hf⟩ := exists_seq_of_good _ hroot hchild
  have key : ∀ n M, ∃ m, M < m ∧ ∃ S, IsTLin spec (take H m) 0 S ∧ S.DownClosed ∧
      ∀ i < n, S i = some (f i) := by
    intro n M
    obtain ⟨m, ⟨S, hS, hdc, hpre⟩, hm⟩ := (hf n).exists_gt M
    refine ⟨m, hm, S, hS, hdc, fun i hi => ?_⟩
    have := hpre i (by simpa using hi)
    rwa [List.getElem_map, List.getElem_range] at this
  have hcomp : ∀ a j r, H j = some (.res a r) → ∃ k, f k = (a, r) := by
    intro a j r hj
    obtain ⟨m, hm, S, hS, hdc, hpre⟩ := key j j
    obtain ⟨k, hk, hSk⟩ := hS.idx_lt hH hdc hj hm
    exact ⟨k, Option.some.inj ((hpre k hk).symm.trans hSk)⟩
  refine ⟨fun k => some (f k), ⟨?_, ⟨?_, fun x => ?_⟩, ?_, ?_, ?_⟩⟩
  · intro k k' a r r' hk hk'
    obtain ⟨m, -, S, hS, -, hpre⟩ := key (max k k' + 1) 0
    exact hS.nodup k k' a r r' ((hpre k (by omega)).trans hk) ((hpre k' (by omega)).trans hk')
  · intro k a r hk
    obtain ⟨m, -, S, hS, -, hpre⟩ := key (k + 1) 0
    exact ((invoked_take H).1 (hS.legal.1 k a r ((hpre k (by omega)).trans hk))).2
  · exact exists_traj_of_forall (hinit x) (fun k q => seqStep_finite (hfin x) H x _ q) fun n => by
      obtain ⟨m, -, S, hS, -, hpre⟩ := key n 0
      obtain ⟨qs, hq0, hqs⟩ := hS.legal.of_take.2 x
      exact ⟨qs, hq0, fun k hk => by dsimp only; rw [← hpre k hk]; exact hqs k⟩
  · intro a j r hj
    obtain ⟨k, hk⟩ := hcomp a j r hj
    exact ⟨k, r, by dsimp only; rw [hk]⟩
  · rintro a b j r hj - hjb hb ⟨kb, rb, hkb⟩
    obtain ⟨m, hm, S, hS, hdc, hpre⟩ := key (max j (kb + 1)) b
    have hjm : j < m := by omega
    obtain ⟨ka, hka, hSa⟩ := hS.idx_lt hH hdc hj hjm
    have hSb : S kb = some (b, rb) := (hpre kb (by omega)).trans hkb
    have hj' : take H m j = some (.res a r) := by rw [take_of_lt H hjm]; exact hj
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ := hS.rt a b j r hj' (Nat.zero_le _) hjb
      ((invoked_take H).2 ⟨by omega, hb⟩) ⟨kb, rb, hSb⟩
    have e1 := hS.nodup k1 ka a r1 r h1 hSa
    have e2 := hS.nodup k2 kb b r2 rb h2 hSb
    refine ⟨ka, kb, r, rb, by omega, ?_, hkb⟩
    dsimp only; rw [← hpre ka (by omega)]; exact hSa
  · intro a j r hj _
    obtain ⟨k, hk⟩ := hcomp a j r hj
    exact ⟨k, by rw [hk]⟩

end Main

section NotSafety

/-- The history of Section 3.2 over one fetch&increment object: process `0` performs
`fetch&inc` and gets `0` (positions `0, 1`); then process `1` performs `fetch&inc` forever,
getting `0, 1, 2, …` (invocation at `2i + 2`, response `i` at `2i + 3`). -/
def faiHist : History (Fin 2) Unit Unit ℕ := fun n =>
  if n = 0 then some (.inv 0 () ())
  else if n = 1 then some (.res 0 0)
  else if n % 2 = 0 then some (.inv 1 () ())
  else some (.res (n - 1) ((n - 3) / 2))

lemma faiHist_zero : faiHist 0 = some (.inv 0 () ()) := rfl

lemma faiHist_one : faiHist 1 = some (.res 0 0) := rfl

lemma faiHist_even (i : ℕ) : faiHist (2 * i + 2) = some (.inv 1 () ()) := by
  unfold faiHist
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]

lemma faiHist_odd (i : ℕ) : faiHist (2 * i + 3) = some (.res (2 * i + 2) i) := by
  unfold faiHist
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show 2 * i + 3 - 1 = 2 * i + 2 by omega, show (2 * i + 3 - 3) / 2 = i by omega]

lemma faiHist_inv {n : ℕ} {p : Fin 2} {x : Unit} {op : Unit}
    (h : faiHist n = some (.inv p x op)) : (n = 0 ∧ p = 0) ∨ (∃ i, n = 2 * i + 2 ∧ p = 1) := by
  unfold faiHist at h
  split_ifs at h with h1 h2 h3 <;> cases h
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨(n - 2) / 2, by omega, rfl⟩

lemma faiHist_res {n a r : ℕ} (h : faiHist n = some (.res a r)) :
    (n = 1 ∧ a = 0 ∧ r = 0) ∨ (n = 2 * r + 3 ∧ a = 2 * r + 2) := by
  unfold faiHist at h
  split_ifs at h with h1 h2 h3 <;> cases h
  · exact Or.inl ⟨h2, rfl, rfl⟩
  · exact Or.inr ⟨by omega, by omega⟩

lemma faiHist_wellFormed : WellFormed faiHist where
  res_inv a j r h := by
    rcases faiHist_res h with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
    · subst h1 h2; exact ⟨by omega, 0, (), (), faiHist_zero⟩
    · subst h1 h2; exact ⟨by omega, 1, (), (), faiHist_even r⟩
  res_unique a j j' r r' h h' := by
    rcases faiHist_res h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;>
      rcases faiHist_res h' with ⟨h1', h2', h3'⟩ | ⟨h1', h2'⟩ <;> omega
  seq a b p x x' op op' ha hb hab := by
    rcases faiHist_inv ha with ⟨h1, h2⟩ | ⟨i, h1, h2⟩ <;>
      rcases faiHist_inv hb with ⟨h1', h2'⟩ | ⟨i', h1', h2'⟩
    · omega
    · rw [h2] at h2'; exact absurd h2' (by decide)
    · omega
    · subst h1; exact ⟨2 * i + 3, i, by omega, faiHist_odd i⟩

/-- The `2`-linearization of the prefix `take faiHist (2c+2)`: process `1`'s `c` completed
operations in order, then process `0`'s operation (moved to the end, response `c`). -/
def faiLin (c : ℕ) : SeqHist ℕ := fun k =>
  if k < c then some (2 * k + 2, k) else if k = c then some (0, c) else none

lemma faiLin_eq_some {c k a r : ℕ} (h : faiLin c k = some (a, r)) :
    (k < c ∧ a = 2 * k + 2 ∧ r = k) ∨ (k = c ∧ a = 0 ∧ r = c) := by
  unfold faiLin at h
  split_ifs at h with h1 h2 <;> cases h
  · exact Or.inl ⟨h1, rfl, rfl⟩
  · exact Or.inr ⟨h2, rfl, rfl⟩

lemma faiLin_lt {c k : ℕ} (h : k < c) : faiLin c k = some (2 * k + 2, k) := by
  unfold faiLin; rw [ite_eq_left h]

lemma faiLin_self (c : ℕ) : faiLin c c = some (0, c) := by
  unfold faiLin; rw [ite_eq_right (lt_irrefl c), ite_eq_left rfl]

lemma isTLin_faiLin (c : ℕ) :
    IsTLin (fun _ => fai) (take faiHist (2 * c + 2)) 2 (faiLin c) where
  nodup k k' a r r' hk hk' := by
    rcases faiLin_eq_some hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      rcases faiLin_eq_some hk' with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩ <;> omega
  legal := by
    refine ⟨fun k a r hk => ?_, fun x => ⟨fun k => min k (c + 1), rfl, fun k => ?_⟩⟩
    · rcases faiLin_eq_some hk with ⟨h1, h2, -⟩ | ⟨-, h2, -⟩ <;> subst h2
      · exact (invoked_take _).2 ⟨by omega, 1, (), (), faiHist_even k⟩
      · exact (invoked_take _).2 ⟨by omega, 0, (), (), faiHist_zero⟩
    · rcases lt_trichotomy k c with h | h | h
      · rw [faiLin_lt h]
        refine Or.inl ⟨1, (), by rw [take_of_lt _ (by omega), faiHist_even], ?_, ?_⟩ <;>
          simp only <;> omega
      · subst h
        rw [faiLin_self]
        refine Or.inl ⟨0, (), by rw [take_of_lt _ (by omega), faiHist_zero], ?_, ?_⟩ <;>
          simp only <;> omega
      · unfold faiLin
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        show min (k + 1) (c + 1) = min k (c + 1)
        omega
  complete a j r hj := by
    rw [take_eq_some] at hj
    rcases faiHist_res hj.2 with ⟨h1, h2, -⟩ | ⟨h1, h2⟩
    · subst h2; exact ⟨c, c, faiLin_self c⟩
    · subst h2; exact ⟨r, r, faiLin_lt (by omega)⟩
  rt a b j r hj htj hjb hb hbm := by
    rw [take_eq_some] at hj
    obtain ⟨kb, rb, hkb⟩ := hbm
    rcases faiHist_res hj.2 with ⟨h1, -, -⟩ | ⟨h1, h2⟩
    · omega
    · rcases faiLin_eq_some hkb with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
      · subst h2 h2'
        exact ⟨r, kb, r, rb, by omega, faiLin_lt (by omega), hkb⟩
      · omega
  resp a j r hj htj := by
    rw [take_eq_some] at hj
    rcases faiHist_res hj.2 with ⟨h1, -, -⟩ | ⟨h1, h2⟩
    · omega
    · subst h2; exact ⟨r, faiLin_lt (by omega)⟩

lemma take_take_of_le (H : History P X Op Res) {m M : ℕ} (h : m ≤ M) :
    take (take H M) m = take H m := by
  funext i; simp only [take_apply]; split_ifs <;> first | rfl | omega

/-- **Section 3.2: for `t > 0`, `t`-linearizability is not a safety property, even for
deterministic types.** The history `faiHist` over a single fetch&increment object is
well-formed, each of its finite prefixes is `2`-linearizable (the first operation is moved to the
end), but `faiHist` itself is not `2`-linearizable. So `2`-linearizability is not
limit-closed. -/
theorem tLinearizable_not_limitClosed : ∃ H : History (Fin 2) Unit Unit ℕ, WellFormed H ∧
    (∀ m, TLinearizable (fun _ => fai) (take H m) 2) ∧ ¬ TLinearizable (fun _ => fai) H 2 := by
  refine ⟨faiHist, faiHist_wellFormed, fun m => ?_, ?_⟩
  · have hM : m ≤ 2 * m + 2 := by omega
    rw [← take_take_of_le faiHist hM]
    exact TLinearizable.prefix (fun _ => fai_deterministic.total)
      (wellFormed_take faiHist_wellFormed _) ⟨_, isTLin_faiLin m⟩ m
  · rintro ⟨S, hS⟩
    obtain ⟨k0, r0, hk0⟩ := hS.complete 0 1 0 faiHist_one
    obtain ⟨k1, hk1⟩ := hS.resp (2 * r0 + 2) (2 * r0 + 3) r0 (faiHist_odd r0) (by omega)
    obtain ⟨q, -, hqs⟩ := hS.legal.2 ()
    have hmono : Monotone q := by
      refine monotone_nat_of_le_succ fun k => ?_
      have := hqs k
      cases hk : S k with
      | none => rw [hk] at this; exact this.ge
      | some e =>
        obtain ⟨a, r⟩ := e
        rw [hk] at this
        rcases this with ⟨-, -, -, -, h⟩ | ⟨-, h⟩ <;> omega
    have step : ∀ k a, S k = some (a, r0) → OnObj faiHist () a →
        r0 = q k ∧ q (k + 1) = q k + 1 := by
      intro k a hk ha
      have := hqs k
      rw [hk] at this
      obtain ⟨p, op, hp, h1, h2⟩ := this.onObj ha
      exact ⟨h1, h2⟩
    obtain ⟨e0, e0'⟩ := step k0 0 hk0 ⟨0, (), faiHist_zero⟩
    obtain ⟨e1, e1'⟩ := step k1 _ hk1 ⟨1, (), faiHist_even r0⟩
    rcases lt_trichotomy k0 k1 with h | h | h
    · have := hmono (show k0 + 1 ≤ k1 by omega); omega
    · subst h; rw [hk0] at hk1; cases hk1
    · have := hmono (show k1 + 1 ≤ k0 by omega); omega

end NotSafety

section InfiniteNondet

/-- A type with **infinite nondeterminism** (Section 3.2, after [8]): the state is `none`
initially; `choose` (operation `none`) moves from `none` to an arbitrary `some n`; `query i`
(operation `some i`) answers `true` and leaves the state unchanged, but is only enabled in a
state `some n` with `i < n`. -/
def chooseType : ObjType (Option ℕ) (Option ℕ) Bool where
  init := {none}
  δ q op r q' := (op = none ∧ q = none ∧ r = true ∧ q' ≠ none) ∨
    (∃ i n, op = some i ∧ q = some n ∧ i < n ∧ r = true ∧ q' = q)

/-- Process `0` invokes `choose` (pending forever); process `1` performs `query 0`, `query 1`,
… (invocation of `query i` at `2i + 1`, response `true` at `2i + 2`). -/
def chooseHist : History (Fin 2) Unit (Option ℕ) Bool := fun n =>
  if n = 0 then some (.inv 0 () none)
  else if n % 2 = 1 then some (.inv 1 () (some ((n - 1) / 2)))
  else some (.res (n - 1) true)

lemma chooseHist_zero : chooseHist 0 = some (.inv 0 () none) := rfl

lemma chooseHist_odd (i : ℕ) : chooseHist (2 * i + 1) = some (.inv 1 () (some i)) := by
  unfold chooseHist
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (2 * i + 1 - 1) / 2 = i by omega]

lemma chooseHist_even (i : ℕ) : chooseHist (2 * i + 2) = some (.res (2 * i + 1) true) := by
  unfold chooseHist
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show 2 * i + 2 - 1 = 2 * i + 1 by omega]

lemma chooseHist_inv {n : ℕ} {p : Fin 2} {x : Unit} {op : Option ℕ}
    (h : chooseHist n = some (.inv p x op)) :
    (n = 0 ∧ p = 0 ∧ op = none) ∨ (∃ i, n = 2 * i + 1 ∧ p = 1 ∧ op = some i) := by
  unfold chooseHist at h
  split_ifs at h with h1 h2 <;> cases h
  · exact Or.inl ⟨h1, rfl, rfl⟩
  · exact Or.inr ⟨(n - 1) / 2, by omega, rfl, rfl⟩

lemma chooseHist_res {n a : ℕ} {r : Bool} (h : chooseHist n = some (.res a r)) :
    ∃ i, n = 2 * i + 2 ∧ a = 2 * i + 1 ∧ r = true := by
  unfold chooseHist at h
  split_ifs at h with h1 h2 <;> cases h
  exact ⟨(n - 2) / 2, by omega, by omega, rfl⟩

lemma chooseHist_wellFormed : WellFormed chooseHist where
  res_inv a j r h := by
    obtain ⟨i, h1, h2, -⟩ := chooseHist_res h
    subst h1 h2
    exact ⟨by omega, 1, (), _, chooseHist_odd i⟩
  res_unique a j j' r r' h h' := by
    obtain ⟨i, h1, h2, -⟩ := chooseHist_res h
    obtain ⟨i', h1', h2', -⟩ := chooseHist_res h'
    omega
  seq a b p x x' op op' ha hb hab := by
    rcases chooseHist_inv ha with ⟨h1, h2, -⟩ | ⟨i, h1, h2, -⟩ <;>
      rcases chooseHist_inv hb with ⟨h1', h2', -⟩ | ⟨i', h1', h2', -⟩
    · omega
    · rw [h2] at h2'; exact absurd h2' (by decide)
    · omega
    · subst h1; exact ⟨2 * i + 2, true, by omega, chooseHist_even i⟩

/-- Linearization of the prefixes of length `2c + 1` and `2c + 2`: `choose` picks `c`, then
`query 0, …, query (c-1)`. -/
def chooseLin (c : ℕ) : SeqHist Bool := fun k =>
  if k = 0 then some (0, true) else if k ≤ c then some (2 * k - 1, true) else none

lemma chooseLin_eq_some {c k a : ℕ} {r : Bool} (h : chooseLin c k = some (a, r)) :
    r = true ∧ ((k = 0 ∧ a = 0) ∨ (1 ≤ k ∧ k ≤ c ∧ a = 2 * k - 1)) := by
  unfold chooseLin at h
  split_ifs at h with h1 h2 <;> cases h
  · exact ⟨rfl, Or.inl ⟨h1, rfl⟩⟩
  · exact ⟨rfl, Or.inr ⟨by omega, h2, rfl⟩⟩

lemma chooseLin_succ {c i : ℕ} (h : i < c) : chooseLin c (i + 1) = some (2 * i + 1, true) := by
  unfold chooseLin
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show 2 * (i + 1) - 1 = 2 * i + 1 by omega]

lemma isTLin_chooseLin {c m : ℕ} (hm1 : 2 * c + 1 ≤ m) (hm2 : m ≤ 2 * c + 2) :
    IsTLin (fun _ => chooseType) (take chooseHist m) 0 (chooseLin c) where
  nodup k k' a r r' hk hk' := by
    obtain ⟨-, h⟩ := chooseLin_eq_some hk
    obtain ⟨-, h'⟩ := chooseLin_eq_some hk'
    omega
  legal := by
    refine ⟨fun k a r hk => ?_, fun x =>
      ⟨fun k => if k = 0 then none else some c, rfl, fun k => ?_⟩⟩
    · obtain ⟨-, ⟨-, rfl⟩ | ⟨h1, h2, rfl⟩⟩ := chooseLin_eq_some hk
      · exact (invoked_take _).2 ⟨by omega, 0, (), _, chooseHist_zero⟩
      · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega]
        exact (invoked_take _).2 ⟨by omega, 1, (), _, chooseHist_odd i⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · refine Or.inl ⟨0, none, by rw [take_of_lt _ (by omega), chooseHist_zero], ?_⟩
        exact Or.inl ⟨rfl, rfl, rfl, by simp⟩
      · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        by_cases hic : i < c
        · rw [chooseLin_succ hic]
          refine Or.inl ⟨1, some i, by rw [take_of_lt _ (by omega), chooseHist_odd], ?_⟩
          exact Or.inr ⟨i, c, rfl, by simp, hic, rfl, by simp⟩
        · unfold chooseLin
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          show (if i + 1 + 1 = 0 then none else some c) = if i + 1 = 0 then none else some c
          simp
  complete a j r hj := by
    rw [take_eq_some] at hj
    obtain ⟨i, h1, h2, -⟩ := chooseHist_res hj.2
    subst h2
    exact ⟨i + 1, true, chooseLin_succ (by omega)⟩
  rt a b j r hj _ hjb hb hbm := by
    rw [take_eq_some] at hj
    obtain ⟨i, h1, h2, -⟩ := chooseHist_res hj.2
    obtain ⟨kb, rb, hkb⟩ := hbm
    obtain ⟨-, ⟨h3, h4⟩ | ⟨h3, h4, h5⟩⟩ := chooseLin_eq_some hkb
    · omega
    · subst h2
      exact ⟨i + 1, kb, true, rb, by omega, chooseLin_succ (by omega), hkb⟩
  resp a j r hj _ := by
    rw [take_eq_some] at hj
    obtain ⟨i, h1, h2, h3⟩ := chooseHist_res hj.2
    subst h2 h3
    exact ⟨i + 1, chooseLin_succ (by omega)⟩

/-- Section 3.2 (after [8]): **linearizability is not a safety property for types with infinite
nondeterminism.** `chooseType` has a single initial state but infinite nondeterminism (`choose`);
every prefix of `chooseHist` is linearizable (`choose` picks the number of queries in the
prefix), but `chooseHist` itself is not (whatever `choose` picks, some later `query` fails). -/
theorem linearizable_not_limitClosed_of_infiniteNondet :
    ∃ H : History (Fin 2) Unit (Option ℕ) Bool, WellFormed H ∧
      (∀ m, Linearizable (fun _ => chooseType) (take H m)) ∧
      ¬ Linearizable (fun _ => chooseType) H := by
  refine ⟨chooseHist, chooseHist_wellFormed, fun m => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨fun _ => none, ⟨(fun _ _ _ _ _ h => by cases h),
        legal_empty (spec := fun _ => chooseType) fun _ => ⟨none, rfl⟩, ?_, ?_, ?_⟩⟩ <;>
        intros <;> simp_all [take_apply]
    · exact ⟨_, isTLin_chooseLin (c := (m - 1) / 2) (by omega) (by omega)⟩
  · rintro ⟨S, hS⟩
    obtain ⟨q, -, hqs⟩ := hS.legal.2 ()
    -- once the state is `some n`, it stays `some n`
    have hpers : ∀ k n, q k = some n → ∀ d, q (k + d) = some n := by
      intro k n hk d
      induction d with
      | zero => exact hk
      | succ d ih =>
        have := hqs (k + d)
        rw [← add_assoc]
        cases he : S (k + d) with
        | none => rw [he] at this; exact this.trans ih
        | some e =>
          obtain ⟨a, r⟩ := e
          rw [he] at this
          rcases this with ⟨p, op, -, ⟨-, h, -⟩ | ⟨i, n', -, -, -, -, h⟩⟩ | ⟨-, h⟩
          · rw [ih] at h; cases h
          · rw [h, ih]
          · rw [h, ih]
    -- the state at the index of `query i` is some `some n` with `i < n`
    have hquery : ∀ i, ∃ k n, q k = some n ∧ i < n := by
      intro i
      obtain ⟨k, hk⟩ := hS.resp (2 * i + 1) (2 * i + 2) true (chooseHist_even i) (Nat.zero_le _)
      have := hqs k
      rw [hk] at this
      obtain ⟨p, op, hp, hδ⟩ := this.onObj ⟨1, some i, chooseHist_odd i⟩
      rw [chooseHist_odd] at hp
      cases hp
      rcases hδ with ⟨h, -⟩ | ⟨i', n, h1, h2, h3, -⟩
      · cases h
      · cases h1; exact ⟨k, n, h2, h3⟩
    obtain ⟨k, N, hk, -⟩ := hquery 0
    obtain ⟨k', M, hk', hNM⟩ := hquery N
    rcases le_total k k' with h | h
    · have := hpers k N hk (k' - k)
      rw [Nat.add_sub_cancel' h, hk'] at this
      cases this; omega
    · have := hpers k' M hk' (k - k')
      rw [Nat.add_sub_cancel' h, hk] at this
      cases this; omega

end InfiniteNondet

end Podc.EventualLinParadox
