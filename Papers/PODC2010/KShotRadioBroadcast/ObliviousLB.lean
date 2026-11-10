import Papers.PODC2010.KShotRadioBroadcast.Chain
import Podc.Foundations.Combinatorics.SelectiveFamily

/-!
# The `Ω(n²/k)` lower bound for oblivious `k`-shot broadcasting (Section 3)

* `exists_seq_exhausted`: the combinatorial core of Lemma 3.2 (the sequence `R = ⟨r₁ … r_k⟩`).
* `lemma_3_1`: some node of `Q` has a transmission (when informed at `T`) at step `≥ T + |Q| - 1`;
  proved via the selective-family bound `Cslib.card_le_of_forall_exists_card_inter_eq_one`.
* `lemma_3_2`: a sequence `R` of at most `k` fresh nodes whose first occurrence after `T` is at
  step `≥ T + n - |S| - k`.
* `theorem_3_3`: for every oblivious `k`-shot schedule there is a connected undirected network on
  which broadcasting is not complete at any step `t ≤ ∑_{j=1}^{m} (n - 1 - j k)`,
  `m = ⌊(n-2)/k⌋`; `theorem_3_3'` turns this into `2 k t + k (n-1) < (n-1)²`.
-/

namespace Podc.KShotRadioBroadcast

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

section count

variable {σ : Schedule V}

/-- One more appearance in `(b, b']` adds one to the count. -/
theorem count_succ_le {v : V} {a b b' x : ℕ} (hab : a < x) (hbx : b ≤ x) (hxb : x < b')
    (hx : v ∈ σ x) : count σ v a b + 1 ≤ count σ v a b' := by
  unfold count
  have hsub : insert x ((Ioo a b).filter (fun t => v ∈ σ t)) ⊆
      (Ioo a b').filter (fun t => v ∈ σ t) := by
    intro y hy
    rcases mem_insert.1 hy with rfl | hy
    · simp [mem_filter, mem_Ioo]; exact ⟨⟨hab, hxb⟩, hx⟩
    · simp only [mem_filter, mem_Ioo] at hy ⊢; exact ⟨⟨hy.1.1, by omega⟩, hy.2⟩
  have hnot : x ∉ (Ioo a b).filter (fun t => v ∈ σ t) := by simp [mem_Ioo]; omega
  have := card_le_card hsub
  rwa [card_insert_of_notMem hnot] at this

end count

/-- Node `q`, informed at step `T`, has *finished transmitting by step `τ`*: all its `k`-shot
transmission steps are `≤ τ`. -/
def Exhausted (σ : Schedule V) (k T : ℕ) (q : V) (τ : ℕ) : Prop :=
  ∀ a, TransmitsAt σ k T q a → a ≤ τ

/-- **Core of Lemma 3.2.** Let every node of a nonempty set `W` (all informed at step `T`) have at
least `k - |W|` appearances in `(T, τ]`. Then some sequence `R` of distinct nodes of `W`, of length
at most `|W|`, first occurs after `τ` at a step `τ'` (if at all) by which some node of `W` has
finished all its transmissions. The sequence is built greedily: `r` is the node of `W` whose next
appearance after `τ` is the latest. -/
theorem exists_seq_exhausted (σ : Schedule V) (k T : ℕ) :
    ∀ (N : ℕ) (W : Finset V) (τ : ℕ), W.card = N → T ≤ τ → W.Nonempty →
      (∀ q ∈ W, k ≤ count σ q T (τ + 1) + W.card) →
      ∃ R : List V, R.Nodup ∧ (∀ x ∈ R, x ∈ W) ∧ R.length ≤ W.card ∧
        ∀ τ', occ σ R τ = some τ' → ∃ q ∈ W, Exhausted σ k T q τ' := by
  intro N
  induction N with
  | zero => intro W τ hW _ hne; simp_all
  | succ N ih =>
    intro W τ hW hTτ hne hcnt
    by_cases hex : ∃ q ∈ W, Exhausted σ k T q τ
    · exact ⟨[], List.nodup_nil, by simp, by simp, fun τ' h => by
        simp [occ] at h; subst h; exact hex⟩
    push Not at hex
    -- every node of `W` appears again after `τ`
    have hnext : ∀ q ∈ W, ∃ b, nextApp σ q τ = some b := by
      intro q hq
      obtain ⟨a, ha, hτa⟩ := by simpa [Exhausted] using hex q hq
      obtain ⟨b, hb, -⟩ := nextApp_isSome hτa ha.2.1
      exact ⟨b, hb⟩
    let f : V → ℕ := fun q => (nextApp σ q τ).getD 0
    obtain ⟨r, hrW, hrmax⟩ := W.exists_max_image f hne
    obtain ⟨τ', hτ'⟩ := hnext r hrW
    have hfr : f r = τ' := by simp [f, hτ']
    have hττ' := (nextApp_spec hτ').1
    -- the count of every node grows by one up to `τ'`
    have hgrow : ∀ q ∈ W, count σ q T (τ + 1) + 1 ≤ count σ q T (τ' + 1) := by
      intro q hq
      obtain ⟨b, hb⟩ := hnext q hq
      have hbτ' : b ≤ τ' := by
        have := hrmax q hq; simp only [f, hb, hτ', Option.getD_some] at this; omega
      obtain ⟨h1, h2, -⟩ := nextApp_spec hb
      exact count_succ_le (by omega) (by omega) (by omega) h2
    set W' := W.erase r with hW'
    have hW'card : W'.card = N := by rw [card_erase_of_mem hrW, hW]; simp
    by_cases hW'e : W'.Nonempty
    · obtain ⟨R', hnd, hsub, hlen, hR'⟩ := ih W' τ' hW'card (by omega) hW'e (by
        intro q hq
        have hqW := mem_of_mem_erase hq
        have := hcnt q hqW; have := hgrow q hqW
        rw [hW] at *; rw [hW'card]; omega)
      refine ⟨r :: R', ?_, ?_, ?_, ?_⟩
      · exact List.nodup_cons.2 ⟨fun h => by simpa [hW'] using hsub r h, hnd⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hrW
        · exact mem_of_mem_erase (hsub x hx)
      · simp; rw [hW]; omega
      · intro τ'' h
        rw [occ_cons, hτ'] at h
        obtain ⟨q, hq, hqe⟩ := hR' τ'' h
        exact ⟨q, mem_of_mem_erase hq, hqe⟩
    · -- `W = {r}`: `r` has used all its shots by `τ'`
      refine ⟨[r], by simp, by simpa using hrW, by
        simp; exact hne, ?_⟩
      intro τ'' h
      simp only [occ_cons, hτ', Option.bind_some, occ_nil, Option.some.injEq] at h
      subst h
      refine ⟨r, hrW, fun a ha => ?_⟩
      by_contra hlt; push Not at hlt
      have hN : N = 0 := by
        rw [← hW'card]; exact card_eq_zero.2 (not_nonempty_iff_eq_empty.1 hW'e)
      have h1 := hcnt r hrW
      have h2 := hgrow r hrW
      have h3 := count_mono (σ := σ) (v := r) (a := T) (show τ' + 1 ≤ a by omega)
      have h4 := ha.2.2
      rw [hW, hN] at h1
      omega

/-! ## Lemma 3.1 -/

section lemma31

variable {σ : Schedule V} {k : ℕ} {s : V} {c : ℕ → V} {ℓ : ℕ}

/-- The extra edges of the collision network of Lemma 3.1: the last chain node and `vt` are both
linked to every node of `P`, and `vt` is linked to all remaining nodes. -/
def collisionX (c : ℕ → V) (ℓ : ℕ) (P : Finset V) (vt : V) (u v : V) : Prop :=
  (u = c (ℓ - 1) ∧ v ∈ P) ∨ (u = vt ∧ v ∈ P) ∨ (u = vt ∧ (∀ i < ℓ, c i ≠ v) ∧ v ∉ P ∧ v ≠ vt)

/-- **The collision network of Lemma 3.1.** Let the sequence `S = c 0, …, c (ℓ-1)` first occur at
step `T`, and let `P` (nonempty) and `vt ∉ P` be nodes outside `S`. If at no step exactly one node
of `P` transmits (all nodes of `P` being informed at `T`), then the protocol fails on the connected
network made of the chain `S`, the last node of `S` and `vt` linked to all of `P`, and `vt` linked to
all other nodes: `vt` never receives the message. -/
theorem exists_blocked_network (hk : 1 ≤ k) (hpos : 1 ≤ ℓ) (hhead : c 0 = s)
    (hinj : ∀ i j, i < ℓ → j < ℓ → c i = c j → i = j) {T : ℕ} (hT : chainTime σ c ℓ = some T)
    (P : Finset V) (vt : V) (hP : ∀ p ∈ P, ∀ i < ℓ, c i ≠ p) (hvt : ∀ i < ℓ, c i ≠ vt)
    (hvtP : vt ∉ P) (hPne : P.Nonempty)
    (hblock : ∀ a, (P.filter (fun w => TransmitsAt σ k T w a)).card ≠ 1) :
    ∃ G : SimpleGraph V, G.Connected ∧ ∀ t, ¬ Complete σ k G.Adj s t := by
  set X := collisionX c ℓ P vt with hXdef
  set G := chainGraph c ℓ X
  have hlast : ∀ i, i + 1 < ℓ → c (ℓ - 1) ≠ c i := fun i hi h => by
    have := hinj (ℓ - 1) i (by omega) (by omega) h; omega
  have hX : ∀ u v, X u v → ∀ i, i + 1 < ℓ → u ≠ c i ∧ v ≠ c i := by
    rintro u v (⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv, -⟩) i hi
    · exact ⟨hlast i hi, fun h => hP v hv i (by omega) h.symm⟩
    · exact ⟨fun h => hvt i (by omega) h.symm, fun h => hP v hv i (by omega) h.symm⟩
    · exact ⟨fun h => hvt i (by omega) h.symm, fun h => hv i (by omega) h.symm⟩
  have hC : StartsWithChain G.Adj s c ℓ := startsWithChain_chainGraph hpos hhead hinj hX
  -- `Rest`: the nodes outside `S ∪ P ∪ {vt}`
  let Rest : V → Prop := fun v => (∀ i < ℓ, c i ≠ v) ∧ v ∉ P ∧ v ≠ vt
  have hPvt : ∀ p ∈ P, p ≠ vt := fun p hp h => hvtP (h ▸ hp)
  have hadjP : ∀ p ∈ P, G.Adj (c (ℓ - 1)) p := fun p hp =>
    chainGraph_adj_of_X (fun h => hP p hp (ℓ - 1) (by omega) h) (Or.inl ⟨rfl, hp⟩)
  have hadjvt : ∀ p ∈ P, G.Adj p vt := fun p hp =>
    (chainGraph_adj_of_X (fun h => hPvt p hp h.symm) (Or.inr (Or.inl ⟨rfl, hp⟩))).symm
  -- neighbours of `vt` and of `Rest` nodes
  have hnbvt : ∀ u, G.Adj u vt → u ∈ P ∨ Rest u := by
    intro u hu
    obtain ⟨hne, h⟩ := chainGraph_adj.1 hu
    rcases h with (⟨i, hi, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩) | (⟨i, hi, h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩)
    · exact absurd h.symm (hvt (i + 1) hi)
    · exact absurd h hvtP
    · exact absurd h hvtP
    · exact absurd h.2.2 (by simp)
    · exact absurd h.symm (hvt i (by omega))
    · exact absurd h.symm (hvt (ℓ - 1) (by omega))
    · exact Or.inl h
    · exact Or.inr h
  have hnbRest : ∀ v u, Rest v → G.Adj u v → u = vt := by
    intro v u hv hu
    obtain ⟨-, h⟩ := chainGraph_adj.1 hu
    rcases h with (⟨i, hi, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩) | (⟨i, hi, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h.symm (hv.1 (i + 1) hi)
    · exact absurd h hv.2.1
    · exact absurd h hv.2.1
    · exact h
    · exact absurd h.symm (hv.1 i (by omega))
    · exact absurd h.symm (hv.1 (ℓ - 1) (by omega))
    · exact absurd h hv.2.2
    · exact absurd h hv.2.2
  refine ⟨G, ?_, ?_⟩
  · -- connectivity
    obtain ⟨p0, hp0⟩ := hPne
    have hreach := reachable_chainGraph (X := X) hhead hinj
    have hrlast : G.Reachable s (c (ℓ - 1)) := hreach (ℓ - 1) (by omega)
    have hrP : ∀ p ∈ P, G.Reachable s p := fun p hp => hrlast.trans (hadjP p hp).reachable
    have hrvt : G.Reachable s vt := (hrP p0 hp0).trans (hadjvt p0 hp0).reachable
    refine connected_of_reachable s fun v => ?_
    by_cases hv : ∃ i < ℓ, c i = v
    · obtain ⟨i, hi, rfl⟩ := hv; exact hreach i hi
    push Not at hv
    by_cases hvP : v ∈ P
    · exact hrP v hvP
    by_cases hvv : v = vt
    · exact hvv ▸ hrvt
    exact hrvt.trans (chainGraph_adj_of_X (Ne.symm hvv) (Or.inr (Or.inr ⟨rfl, hv, hvP, hvv⟩))).reachable
  · -- `vt` is never informed
    have hTpos : 0 < T := chainTime_pos (by omega) hT
    have hPT : ∀ p ∈ P, recvTime σ k G.Adj s T p = some T := fun p hp =>
      chain_last_informs hk hC hT (hP p hp) (hadjP p hp)
    have hbefore : ∀ t, t < T → ∀ u, (∀ i < ℓ, c i ≠ u) → recvTime σ k G.Adj s t u = none :=
      fun t ht u hu => chain_outside_none hk hC (fun T' hT' => by rw [hT] at hT'; cases hT'; exact ht) hu
    have hclaim : ∀ t, recvTime σ k G.Adj s t vt = none ∧
        ∀ v, Rest v → recvTime σ k G.Adj s t v = none := by
      intro t
      induction t with
      | zero => exact ⟨hbefore 0 hTpos vt hvt, fun v hv => hbefore 0 hTpos v hv.1⟩
      | succ t ih =>
        by_cases htT : t + 1 < T
        · exact ⟨hbefore _ htT vt hvt, fun v hv => hbefore _ htT v hv.1⟩
        obtain ⟨ih1, ih2⟩ := ih
        constructor
        · rw [recvTime_succ_of_none ih1]
          split_ifs with hu
          · exfalso
            obtain ⟨u0, ⟨hadj0, htx0⟩, huniq⟩ := hu
            have htxP : ∀ p ∈ P, Transmits σ k G.Adj s t p ↔ TransmitsAt σ k T p (t + 1) := by
              intro p hp
              constructor
              · rintro ⟨r, hr, htr⟩
                by_cases htT' : t < T
                · rw [hbefore t htT' p (hP p hp)] at hr; cases hr
                · rw [recvTime_mono (by omega) (hPT p hp)] at hr; cases hr; exact htr
              · intro htr
                exact ⟨T, recvTime_mono (by have := htr.1; omega) (hPT p hp), htr⟩
            rcases hnbvt u0 hadj0 with hu0P | hu0R
            · apply hblock (t + 1)
              rw [card_eq_one]
              refine ⟨u0, ?_⟩
              ext p
              simp only [mem_filter, mem_singleton]
              constructor
              · rintro ⟨hp, htr⟩
                exact huniq p ⟨hadjvt p hp, (htxP p hp).2 htr⟩
              · intro hp; rw [hp]; exact ⟨hu0P, (htxP u0 hu0P).1 htx0⟩
            · obtain ⟨r, hr, -⟩ := htx0
              rw [ih2 u0 hu0R] at hr; cases hr
          · rfl
        · intro v hv
          rw [recvTime_succ_of_none (ih2 v hv)]
          split_ifs with hu
          · exfalso
            obtain ⟨u0, ⟨hadj0, ⟨r, hr, -⟩⟩, -⟩ := hu
            rw [hnbRest v u0 hv hadj0, ih1] at hr; cases hr
          · rfl
    intro t hcomp
    have := hcomp vt
    rw [(hclaim t).1] at this
    simp at this

/-- **Lemma 3.1.** Let `P` correctly broadcast from `s` on undirected networks, let the sequence
`S = c 0, …, c (ℓ-1)` (distinct, starting at the source) first occur at step `T`, and let `Q` be a
set of at least two nodes outside `S`. Then some `w ∈ Q`, if informed at step `T`, transmits at a
step `≥ T + |Q| - 1`, i.e. `t_{≤k}(w, T) ≥ T + |Q| - 1`.

(The paper allows `|Q| ≥ 1`; for `|Q| = 1` the claim can fail when `S ∪ Q` is the whole node set,
since the single node of `Q` then never has to transmit.) -/
theorem lemma_3_1 (hk : 1 ≤ k) (hcorr : CorrectOnUndirected σ k s) (hpos : 1 ≤ ℓ)
    (hhead : c 0 = s) (hinj : ∀ i j, i < ℓ → j < ℓ → c i = c j → i = j) {T : ℕ}
    (hT : chainTime σ c ℓ = some T) (Q : Finset V) (hQ : ∀ q ∈ Q, ∀ i < ℓ, c i ≠ q)
    (hQ2 : 2 ≤ Q.card) :
    ∃ w ∈ Q, ∃ a, T + Q.card - 1 ≤ a ∧ TransmitsAt σ k T w a := by
  obtain ⟨vt, hvt⟩ : Q.Nonempty := card_pos.1 (by omega)
  set Q' := Q.erase vt with hQ'
  have hQ'card : Q'.card = Q.card - 1 := card_erase_of_mem hvt
  by_contra hcon
  push Not at hcon
  have hsmall : ∀ w ∈ Q', ∀ a, TransmitsAt σ k T w a → a < T + Q'.card := by
    intro w hw a ha
    by_contra h
    exact hcon w (mem_of_mem_erase hw) a (by omega) ha
  let F : {t // t ∈ Ioo T (T + Q'.card)} → Finset {x // x ∈ Q'} :=
    fun t => univ.filter (fun w => TransmitsAt σ k T w.1 t.1)
  have hF := Cslib.card_le_of_forall_exists_card_inter_eq_one F (by
    intro P hPne
    by_contra hno
    push Not at hno
    obtain ⟨G, hG, hnot⟩ := exists_blocked_network hk hpos hhead hinj hT
      (P.map (Function.Embedding.subtype _)) vt
      (fun p hp => by
        obtain ⟨x, -, rfl⟩ := mem_map.1 hp
        exact hQ x.1 (mem_of_mem_erase x.2))
      (hQ vt hvt)
      (by
        intro h
        obtain ⟨x, -, hx⟩ := mem_map.1 h
        have := x.2
        rw [Function.Embedding.subtype_apply] at hx
        rw [hx, hQ'] at this
        simp at this)
      (hPne.map)
      (by
        intro a hcard
        obtain ⟨p, hp⟩ := card_eq_one.1 hcard
        have hpmem : p ∈ (P.map (Function.Embedding.subtype _)).filter
            (fun w => TransmitsAt σ k T w a) := by rw [hp]; exact mem_singleton_self p
        obtain ⟨hpP, hptx⟩ := mem_filter.1 hpmem
        obtain ⟨x, hxP, rfl⟩ := mem_map.1 hpP
        have ha1 := hptx.1
        have ha2 := hsmall x.1 x.2 a hptx
        apply hno ⟨a, mem_Ioo.2 ⟨ha1, ha2⟩⟩
        rw [card_eq_one]
        refine ⟨x, ?_⟩
        ext y
        simp only [F, mem_inter, mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · rintro ⟨hy, hyP⟩
          have : y.1 ∈ (P.map (Function.Embedding.subtype _)).filter
              (fun w => TransmitsAt σ k T w a) :=
            mem_filter.2 ⟨mem_map_of_mem _ hyP, hy⟩
          rw [hp, mem_singleton] at this
          exact Subtype.ext this
        · intro hy; rw [hy]; exact ⟨hptx, hxP⟩)
    obtain ⟨t, ht⟩ := hcorr G hG
    exact hnot t ht)
  simp only [Fintype.card_coe, Nat.card_Ioo] at hF
  omega

/-- The nodes outside the chain `c 0, …, c (ℓ-1)`: there are `n - ℓ` of them. -/
theorem card_outside {c : ℕ → V} {ℓ : ℕ} (hinj : ∀ i j, i < ℓ → j < ℓ → c i = c j → i = j) :
    (univ.filter (fun v => ∀ i < ℓ, c i ≠ v)).card = Fintype.card V - ℓ := by
  have h1 : univ.filter (fun v => ∀ i < ℓ, c i ≠ v) = univ \ (range ℓ).image c := by
    ext v; simp
  have h2 : ((range ℓ).image c).card = ℓ := by
    rw [card_image_of_injOn (fun i hi j hj h => hinj i j (by simpa using hi) (by simpa using hj) h)]
    simp
  rw [h1, card_sdiff_of_subset (subset_univ _), card_univ, h2]

/-- **Lemma 3.2.** Let `P` correctly broadcast from `s` on undirected networks and let the sequence
`S = c 0, …, c (ℓ-1)` (distinct, starting at the source) first occur at step `T`. Then there is a
sequence `R` of at most `k` distinct nodes outside `S` whose first occurrence after `T` (if any) is
at a step `T' ≥ T + n - |S| - k`. -/
theorem lemma_3_2 (hk : 1 ≤ k) (hcorr : CorrectOnUndirected σ k s) (hpos : 1 ≤ ℓ)
    (hhead : c 0 = s) (hinj : ∀ i j, i < ℓ → j < ℓ → c i = c j → i = j) {T : ℕ}
    (hT : chainTime σ c ℓ = some T) :
    ∃ R : List V, R.Nodup ∧ (∀ x ∈ R, ∀ i < ℓ, c i ≠ x) ∧ R.length ≤ k ∧
      ∀ T', occ σ R T = some T' → T + (Fintype.card V - ℓ) ≤ T' + k := by
  set Q := univ.filter (fun v => ∀ i < ℓ, c i ≠ v) with hQdef
  have hQcard : Q.card = Fintype.card V - ℓ := card_outside hinj
  rw [← hQcard]
  by_cases hQk : Q.card ≤ k
  · exact ⟨[], List.nodup_nil, by simp, by simp, fun T' h => by
      simp [occ] at h; subst h; omega⟩
  push Not at hQk
  -- the set `W` of Lemma 3.2: `k` nodes of `Q`, each transmitting at a step `≥ T + |Q| - k`
  have hW : ∀ j ≤ k, ∃ W ⊆ Q, W.card = j ∧
      ∀ w ∈ W, ∃ a, T + Q.card - k ≤ a ∧ TransmitsAt σ k T w a := by
    intro j
    induction j with
    | zero => intro _; exact ⟨∅, empty_subset _, rfl, by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨W, hWQ, hWc, hWa⟩ := ih (by omega)
      have hcard : (Q \ W).card = Q.card - j := by rw [card_sdiff_of_subset hWQ, hWc]
      obtain ⟨w, hw, a, ha, htx⟩ := lemma_3_1 hk hcorr hpos hhead hinj hT (Q \ W)
        (fun q hq => (mem_filter.1 (mem_sdiff.1 hq).1).2) (by omega)
      have hwW : w ∉ W := (mem_sdiff.1 hw).2
      refine ⟨insert w W, insert_subset (mem_sdiff.1 hw).1 hWQ, by
        rw [card_insert_of_notMem hwW, hWc], ?_⟩
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact ⟨a, by omega, htx⟩
      · exact hWa x hx
  obtain ⟨W, hWQ, hWc, hWa⟩ := hW k le_rfl
  obtain ⟨R, hnd, hRW, hlen, hR⟩ := exists_seq_exhausted σ k T k W T hWc le_rfl
    (card_pos.1 (by omega)) (fun q _ => by omega)
  refine ⟨R, hnd, fun x hx => (mem_filter.1 (hWQ (hRW x hx))).2, by omega, ?_⟩
  intro T' hT'
  obtain ⟨q, hq, hqe⟩ := hR T' hT'
  obtain ⟨a, ha, htx⟩ := hWa q hq
  have := hqe a htx
  omega

end lemma31

/-! ## Theorem 3.3 -/

section theorem33

variable {σ : Schedule V} {k : ℕ} {s : V}

/-- The stages of the proof of Theorem 3.3: after `m` applications of Lemma 3.2 we have a sequence
`S` of `ℓ ≤ 1 + m k` distinct nodes starting at the source whose first occurrence is at a step
`≥ 1 + ∑_{j=1}^{m} (n - 1 - j k)` (or never). -/
theorem exists_chain_stages (hk : 1 ≤ k) (hcorr : CorrectOnUndirected σ k s) (m : ℕ) :
    ∃ (c : ℕ → V) (ℓ : ℕ), 1 ≤ ℓ ∧ ℓ ≤ 1 + m * k ∧ c 0 = s ∧
      (∀ i j, i < ℓ → j < ℓ → c i = c j → i = j) ∧
      ∀ T, chainTime σ c ℓ = some T →
        1 + ∑ j ∈ Icc 1 m, (Fintype.card V - 1 - j * k) ≤ T := by
  induction m with
  | zero =>
    refine ⟨fun _ => s, 1, le_rfl, by simp, rfl, fun i j hi hj _ => by omega, ?_⟩
    intro T hT
    have := chainTime_pos (σ := σ) (c := fun _ => s) (i := 1) one_pos hT
    simp; omega
  | succ m ih =>
    obtain ⟨c, ℓ, hpos, hℓ, hhead, hinj, hbound⟩ := ih
    cases hT : chainTime σ c ℓ with
    | none =>
      refine ⟨c, ℓ, hpos, ?_, hhead, hinj, fun T h => by rw [hT] at h; cases h⟩
      have : m * k ≤ (m + 1) * k := Nat.mul_le_mul_right _ (by omega)
      omega
    | some T =>
      obtain ⟨R, hnd, hRout, hRlen, hRT⟩ := lemma_3_2 hk hcorr hpos hhead hinj hT
      let c' : ℕ → V := fun i => if i < ℓ then c i else R.getD (i - ℓ) s
      have hc'lt : ∀ i < ℓ, c' i = c i := fun i hi => by simp [c', hi]
      have hc'ge : ∀ j (hj : j < R.length), c' (ℓ + j) = R[j] := by
        intro j hj; simp [c', List.getElem?_eq_getElem hj]
      refine ⟨c', ℓ + R.length, by omega, ?_, by rw [hc'lt 0 hpos, hhead], ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · intro i j hi hj h
        rcases Nat.lt_or_ge i ℓ with hil | hil <;> rcases Nat.lt_or_ge j ℓ with hjl | hjl
        · rw [hc'lt i hil, hc'lt j hjl] at h; exact hinj i j hil hjl h
        · obtain ⟨j', rfl⟩ : ∃ j', j = ℓ + j' := ⟨j - ℓ, by omega⟩
          rw [hc'lt i hil, hc'ge j' (by omega)] at h
          exact absurd h (hRout _ (List.getElem_mem _) i hil)
        · obtain ⟨i', rfl⟩ : ∃ i', i = ℓ + i' := ⟨i - ℓ, by omega⟩
          rw [hc'lt j hjl, hc'ge i' (by omega)] at h
          exact absurd h.symm (hRout _ (List.getElem_mem _) j hjl)
        · obtain ⟨i', rfl⟩ : ∃ i', i = ℓ + i' := ⟨i - ℓ, by omega⟩
          obtain ⟨j', rfl⟩ : ∃ j', j = ℓ + j' := ⟨j - ℓ, by omega⟩
          rw [hc'ge i' (by omega), hc'ge j' (by omega)] at h
          have := (List.Nodup.getElem_inj_iff hnd).1 h
          omega
      · intro T' hT'
        rw [chainTime_add_length R hc'ge, chainTime_congr hc'lt, hT] at hT'
        simp only [Option.bind_some] at hT'
        have h1 := hRT T' hT'
        have h2 := le_of_occ hT'
        have h3 := hbound T hT
        rw [Finset.sum_Icc_succ_top (by omega)]
        rw [Nat.succ_mul] at *
        omega

/-- **Theorem 3.3** (explicit form). For every oblivious `k`-shot broadcasting protocol (schedule
`σ`, `k ≥ 1`) and source `s` on `n ≥ 2` nodes there is a connected undirected network on which
broadcasting is not complete at any step `t ≤ ∑_{j=1}^{m} (n - 1 - j k)`, `m = ⌊(n-2)/k⌋`.

The paper's sum is `1 + ∑_{j=1}^{⌊n/k⌋} (n - j k)`; the `- 1` per stage comes from `|S| ≤ 1 + j k`
(the paper drops the source), and we stop at `m = ⌊(n-2)/k⌋` so that one node remains outside the
chain. The protocol need not be correct: if it fails on some connected network, that network
works. -/
theorem theorem_3_3 (σ : Schedule V) (hk : 1 ≤ k) (s : V) (hn : 2 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V, G.Connected ∧
      ∀ t, t ≤ ∑ j ∈ Icc 1 ((Fintype.card V - 2) / k), (Fintype.card V - 1 - j * k) →
        ¬ Complete σ k G.Adj s t := by
  by_cases hcorr : CorrectOnUndirected σ k s
  swap
  · unfold CorrectOnUndirected at hcorr
    push Not at hcorr
    obtain ⟨G, hG, hnot⟩ := hcorr
    exact ⟨G, hG, fun t _ => hnot t⟩
  set m := (Fintype.card V - 2) / k
  obtain ⟨c, ℓ, hpos, hℓ, hhead, hinj, hbound⟩ := exists_chain_stages hk hcorr m
  have hmk : m * k ≤ Fintype.card V - 2 := Nat.div_mul_le_self _ _
  have hℓn : ℓ < Fintype.card V := by omega
  let X : V → V → Prop := fun u v => u = c (ℓ - 1) ∧ ∀ i < ℓ, c i ≠ v
  have hX : ∀ u v, X u v → ∀ i, i + 1 < ℓ → u ≠ c i ∧ v ≠ c i := by
    rintro u v ⟨rfl, hv⟩ i hi
    exact ⟨fun h => by have := hinj (ℓ - 1) i (by omega) (by omega) h; omega,
      fun h => hv i (by omega) h.symm⟩
  have hC := startsWithChain_chainGraph (s := s) hpos hhead hinj hX
  refine ⟨chainGraph c ℓ X, ?_, ?_⟩
  · have hreach := reachable_chainGraph (X := X) hhead hinj
    refine connected_of_reachable s fun v => ?_
    by_cases hv : ∃ i < ℓ, c i = v
    · obtain ⟨i, hi, rfl⟩ := hv; exact hreach i hi
    push Not at hv
    exact (hreach (ℓ - 1) (by omega)).trans
      (chainGraph_adj_of_X (fun h => hv (ℓ - 1) (by omega) h) ⟨rfl, hv⟩).reachable
  · intro t ht hcomp
    have hcard := card_outside hinj
    obtain ⟨u, hu⟩ : (univ.filter (fun v => ∀ i < ℓ, c i ≠ v)).Nonempty :=
      card_pos.1 (by omega)
    have hnone := chain_outside_none (σ := σ) (t := t) hk hC
      (fun T hT => by have := hbound T hT; omega) (mem_filter.1 hu).2
    have := hcomp u
    rw [hnone] at this
    simp at this

/-- `∑_{j=1}^{m} (N - j k)` in closed form (times two). -/
theorem two_mul_sum_sub (N k : ℕ) : ∀ m, m * k ≤ N →
    2 * ∑ j ∈ Icc 1 m, (N - j * k) + m * (m + 1) * k = 2 * m * N := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    have hm' : m * k ≤ N := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ m)) hm
    rw [Finset.sum_Icc_succ_top (by omega), mul_add]
    obtain ⟨d, hd⟩ : ∃ d, N = (m + 1) * k + d := ⟨N - (m + 1) * k, by omega⟩
    have h := ih hm'
    rw [show N - (m + 1) * k = d by omega]
    subst hd
    nlinarith [h]

/-- The arithmetic of Theorem 3.3: with `N = n - 1` and `m = ⌊(N-1)/k⌋`,
`N² ≤ 2 k ∑_{j=1}^{m} (N - j k) + k N`. -/
theorem sq_le_sum (N k : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    N ^ 2 ≤ 2 * k * ∑ j ∈ Icc 1 ((N - 1) / k), (N - j * k) + k * N := by
  set m := (N - 1) / k
  have hdm := Nat.div_add_mod (N - 1) k
  have hmod := Nat.mod_lt (N - 1) (show 0 < k by omega)
  set q := (N - 1) % k + 1
  have hN' : N = m * k + q := by simp only [q, m]; rw [mul_comm]; omega
  have hmk : m * k ≤ N := by omega
  have hsum := two_mul_sum_sub N k m hmk
  have hqk : q ≤ k := by omega
  have : q * q ≤ k * q := Nat.mul_le_mul_right _ hqk
  nlinarith [hsum]

/-- **Theorem 3.3** (`Ω(n²/k)`). For every oblivious `k`-shot broadcasting protocol (`k ≥ 1`) and
source on `n ≥ 2` nodes there is a connected undirected network on which broadcasting is not
complete at any step `t` with `2 k t + k (n - 1) < (n - 1)²`; i.e. broadcasting needs more than
`(n-1)²/(2k) - (n-1)/2` steps. -/
theorem theorem_3_3' (σ : Schedule V) (hk : 1 ≤ k) (s : V) (hn : 2 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V, G.Connected ∧
      ∀ t, 2 * k * t + k * (Fintype.card V - 1) < (Fintype.card V - 1) ^ 2 →
        ¬ Complete σ k G.Adj s t := by
  obtain ⟨G, hG, h⟩ := theorem_3_3 σ hk s hn
  refine ⟨G, hG, fun t ht => h t ?_⟩
  have hsq := sq_le_sum (Fintype.card V - 1) k hk (by omega)
  rw [show Fintype.card V - 1 - 1 = Fintype.card V - 2 by omega] at hsq
  by_contra hlt
  push Not at hlt
  have : 2 * k * ∑ j ∈ Icc 1 ((Fintype.card V - 2) / k), (Fintype.card V - 1 - j * k) ≤
      2 * k * t := Nat.mul_le_mul_left _ hlt.le
  omega

end theorem33

end Podc.KShotRadioBroadcast
