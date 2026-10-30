import Papers.PODC2023.AmortizedByzantineBroadcast.Act

/-!
# Consistency of Algorithm 4 (Lemma 1, Lemma 2, Theorem 1 of [WXMRS23])

We prove that in every run of the Algorithm 4 model with at most `f` Byzantine nodes and an
unforgeability-respecting adversary, where `G_ε` expands every set of `n - 2f` nodes to more than
`2f` nodes (which follows from the paper's assumptions `f ≤ (1/2 - ε) n` and `G_ε` an
`(n, 2ε, 1 - 2ε)`-expander, `expands_of_isExpander`), two honest nodes never commit different
values in the same slot. The proof follows the paper:

* `lemma1`: two certificates of the same epoch certify the same value (expander argument);
* `lemma2`: after a commit-proof of epoch `i`, every certificate of a later epoch certifies the same
  value (induction over epochs, through the freshness check of Propagate-1);
* `theorem1`: consistency.

The proofs hold for each of the three readings of the skip condition (`pol` is arbitrary).
-/

namespace Podc.AmortizedByzantineBroadcast

open Finset

variable {n : ℕ} {V : Type} [DecidableEq V]

/-! ### Membership in the derived lists -/

lemma mem_certsOf {xs : List (Item n V)} {k j : ℕ} {m : V} :
    (j, m) ∈ certsOf xs k ↔ Item.cert k j m ∈ xs ∨ ∃ L i, Item.prop L k i m (some j) ∈ xs := by
  simp only [certsOf, List.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    rcases y with ⟨L, k', i, m', c⟩ | _ | ⟨k', j', m'⟩ | _ | _ | _ | _ | _ | _
    · rcases c with _ | c <;> simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨L, i, hy⟩
    · simp at h
    · simp at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl hy
    all_goals simp at h
  · rintro (h | ⟨L, i, h⟩)
    · exact ⟨_, h, by simp⟩
    · exact ⟨_, h, by simp⟩

lemma mem_voters {xs : List (Item n V)} {k i : ℕ} {m : V} {u : Fin n} :
    u ∈ voters xs k i m ↔ Item.vote u k i m ∈ xs := by
  simp only [voters, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    cases y <;> simp at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    exact hy
  · intro h; exact ⟨_, h, by simp⟩

lemma mem_sharers {xs : List (Item n V)} {k i : ℕ} {m : V} {u : Fin n} :
    u ∈ sharers xs k i m ↔ Item.cshare u k i m ∈ xs := by
  simp only [sharers, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    cases y <;> simp at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    exact hy
  · intro h; exact ⟨_, h, by simp⟩

lemma mem_accusers {xs : List (Item n V)} {v u : Fin n} :
    u ∈ accusers xs v ↔ Item.accuse u v ∈ xs := by
  simp only [accusers, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    cases y <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact hy
  · intro h; exact ⟨_, h, by simp⟩

lemma mem_propVals {xs : List (Item n V)} {L : Fin n} {k i : ℕ} {m : V} :
    m ∈ propVals xs L k i ↔ ∃ c, Item.prop L k i m c ∈ xs := by
  simp only [propVals, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨y, hy, h⟩
    cases y <;> simp at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    exact ⟨_, hy⟩
  · rintro ⟨c, h⟩; exact ⟨_, h, by simp⟩

lemma two_le_length_of_mem {α : Type*} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 2 ≤ l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp at ha
  · simp at ha hb; exact absurd (ha.trans hb.symm) hab
  · simp

/-- The length of a deduplicated list is the cardinality of its `toFinset`. -/
lemma length_dedup_eq {α : Type*} [DecidableEq α] (l : List α) :
    l.dedup.length = l.dedup.toFinset.card :=
  (List.toFinset_card_of_nodup (List.nodup_dedup l)).symm

lemma freshest_ge {cs : List (ℕ × V)} {c : ℕ × V} (h : c ∈ cs) :
    ∃ c₀, freshest cs = some c₀ ∧ c.1 ≤ c₀.1 := by
  unfold freshest
  suffices ∀ (l : List (ℕ × V)) (acc : Option (ℕ × V)),
      (c ∈ l ∨ ∃ a, acc = some a ∧ c.1 ≤ a.1) →
      ∃ c₀, l.foldl (fun acc c => match acc with
        | none => some c
        | some a => if a.1 < c.1 then some c else some a) acc = some c₀ ∧ c.1 ≤ c₀.1 from
    this cs none (Or.inl h)
  intro l
  induction l with
  | nil =>
    rintro acc (h | ⟨a, rfl, ha⟩)
    · simp at h
    · exact ⟨a, rfl, ha⟩
  | cons x l ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    rcases hacc with h | ⟨a, rfl, ha⟩
    · rcases List.mem_cons.mp h with rfl | h
      · right
        rcases acc with _ | a
        · exact ⟨_, rfl, le_rfl⟩
        · simp only
          split_ifs with hlt
          · exact ⟨_, rfl, le_rfl⟩
          · exact ⟨a, rfl, by omega⟩
      · exact Or.inl h
    · right
      simp only
      split_ifs with hlt
      · exact ⟨_, rfl, by omega⟩
      · exact ⟨a, rfl, ha⟩

/-! ### The run -/

variable [NeZero n] (P : Params n V) (pol : Skip) (sc : Scenario n V)

lemma sentByHonest_mono {r r' : ℕ} (h : r ≤ r') {x : Item n V} (hx : sentByHonest P pol sc r x) :
    sentByHonest P pol sc r' x := by
  obtain ⟨t, ht, rest⟩ := hx; exact ⟨t, ht.trans h, rest⟩

lemma atomAvail_mono {r r' : ℕ} (h : r ≤ r') {x : Item n V} (hx : atomAvail P pol sc r x) :
    atomAvail P pol sc r' x :=
  hx.imp id (sentByHonest_mono P pol sc h)

lemma availAt_mono {r r' : ℕ} (h : r ≤ r') {x : Item n V} (hx : availAt P pol sc r x) :
    availAt P pol sc r' x := by
  have hA : ∀ {y : Item n V}, atomAvail P pol sc r y → atomAvail P pol sc r' y :=
    atomAvail_mono P pol sc h
  cases x with
  | prop L k i m c =>
    exact ⟨hA hx.1, fun j hj => (hx.2 j hj).imp fun σ hσ => ⟨hσ.1, fun u hu => hA (hσ.2 u hu)⟩⟩
  | cert k i m => exact hx.imp fun σ hσ => ⟨hσ.1, fun u hu => hA (hσ.2 u hu)⟩
  | cproof k i m => exact hx.imp fun σ hσ => ⟨hσ.1, fun u hu => hA (hσ.2 u hu)⟩
  | cpf v => exact hx.imp fun σ hσ => ⟨hσ.1, fun u hu => hA (hσ.2 u hu)⟩
  | vote => exact hA hx
  | cshare => exact hA hx
  | accuse => exact hA hx
  | query1 => exact hA hx
  | query2 => exact hA hx

/-- The certificate part of a held certificate: `C_{k,j}(m)` is available as soon as an honest
node holds it (as a certificate or inside a proposal). -/
lemma cert_avail_of_mem_certsOf {r : ℕ} {xs : List (Item n V)}
    (hxs : ∀ x ∈ xs, availAt P pol sc r x) {k j : ℕ} {m : V} (h : (j, m) ∈ certsOf xs k) :
    availAt P pol sc r (.cert k j m) := by
  rcases mem_certsOf.mp h with h | ⟨L, i, h⟩
  · exact hxs _ h
  · exact (hxs _ h).2 j rfl

/-- Aggregation: `n - f` shares held make the threshold signature available. -/
lemma avail_of_shares {r : ℕ} {l : List (Fin n)} (hl : n - P.f ≤ l.length) (hd : l.Nodup)
    {a : Fin n → Item n V} (ha : ∀ u ∈ l, atomAvail P pol sc r (a u)) :
    ∃ σ : Finset (Fin n), n - P.f ≤ σ.card ∧ ∀ u ∈ σ, atomAvail P pol sc r (a u) :=
  ⟨l.toFinset, by rw [List.toFinset_card_of_nodup hd]; exact hl, fun u hu =>
    ha u (List.mem_toFinset.mp hu)⟩

variable {P pol sc}

/-- Everything an honest node sends, and everything an honest node receives, is available to
the adversary at that round (honest nodes do not forge). -/
theorem honest_out_avail (hadv : sc.AdvValid P pol) :
    ∀ r u, u ∉ sc.F → ∀ w x, (w, x) ∈ outs P pol sc r (exec P pol sc r) u →
      availAt P pol sc r x := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro u hu w x hx
  -- items held by `u` are available
  have hheld : ∀ y ∈ held (exec P pol sc r u) r, availAt P pol sc r y := by
    intro y hy
    rw [mem_held_exec P pol sc le_rfl] at hy
    obtain ⟨t, s, ht, hs⟩ := hy
    refine availAt_mono P pol sc ht.le ?_
    by_cases hsF : s ∈ sc.F
    · simp only [outs, hsF, ↓reduceIte] at hs
      exact hadv t s u y hsF hu hs
    · exact ih t ht s hsF u y hs
  have hatom : atomAvail P pol sc r x := Or.inr ⟨r, le_rfl, u, hu, w, hx⟩
  simp only [outs, hu, ↓reduceIte] at hx
  rcases act_justified P pol hx with ⟨hsig, hprop⟩ | hh | ⟨k, j, m, rfl, hc | hc⟩ |
      ⟨k, j, m, rfl, hc⟩ | ⟨v, rfl, hc⟩
  · cases x with
    | prop L k i m c =>
      refine ⟨hatom, fun j hj => ?_⟩
      exact cert_avail_of_mem_certsOf P pol sc hheld (hprop L k i m j (by rw [hj]))
    | cert => simp [Item.signer] at hsig
    | cproof => simp [Item.signer] at hsig
    | cpf => simp [Item.signer] at hsig
    | vote => exact hatom
    | cshare => exact hatom
    | accuse => exact hatom
    | query1 => exact hatom
    | query2 => exact hatom
  · exact hheld x hh
  · exact cert_avail_of_mem_certsOf P pol sc hheld hc
  · exact avail_of_shares P pol sc hc (List.nodup_dedup _) fun u' hu' =>
      hheld _ (mem_voters.mp hu')
  · exact avail_of_shares P pol sc hc (List.nodup_dedup _) fun u' hu' =>
      hheld _ (mem_sharers.mp hu')
  · exact avail_of_shares P pol sc hc (List.nodup_dedup _) fun u' hu' =>
      hheld _ (mem_accusers.mp hu')

/-- Items held by an honest node are available. -/
theorem held_avail (hadv : sc.AdvValid P pol) {r t : ℕ} (htr : t ≤ r) {w : Fin n}
    (hw : w ∉ sc.F) {x : Item n V} (hx : x ∈ held (exec P pol sc r w) t) :
    availAt P pol sc t x := by
  rw [mem_held_exec P pol sc htr] at hx
  obtain ⟨t', s, ht, hs⟩ := hx
  refine availAt_mono P pol sc ht.le ?_
  by_cases hsF : s ∈ sc.F
  · simp only [outs, hsF, ↓reduceIte] at hs
    exact hadv t' s w x hsF hw hs
  · exact honest_out_avail hadv t' s hsF w x hs

/-! ### What honest votes and shares imply -/

/-- An honest vote `⟨vote,k,i,m⟩_u` is sent only in step (4) of epoch `i` of slot `k`, by `u`
itself, after `u` forwarded a proposal of `L_i` on `m` (received in this epoch, at least as fresh
as its Collect certificate) to all its neighbours in Propagate-1, and without equivocation
detected. -/
theorem honest_vote_facts {ρ : ℕ} {u w u' : Fin n} {k i : ℕ} {m : V} (hu : u ∉ sc.F)
    (h : (w, .vote u' k i m) ∈ outs P pol sc ρ (exec P pol sc ρ) u) :
    u' = u ∧ ρ = roundOf P k i 3 ∧ 1 ≤ k ∧ i < P.f + 2 ∧
    (propVals (held (exec P pol sc ρ u) ρ) (leader P k i) k i).length < 2 ∧
    ∃ c, Item.prop (leader P k i) k i m c ∈
        heldIn (exec P pol sc (roundOf P k i 2) u) (roundOf P k i 0) (roundOf P k i 2) ∧
      fle (collectVal P (roundOf P k i 2) (exec P pol sc (roundOf P k i 2) u)) c = true ∧
      ∀ w'', P.G u w'' = true → (w'', .prop (leader P k i) k i m c) ∈
        outs P pol sc (roundOf P k i 2) (exec P pol sc (roundOf P k i 2)) u := by
  simp only [outs, hu, ↓reduceIte] at h
  obtain ⟨rfl, h3, hk, hi, hlen, w', c, hsent⟩ := act_vote P pol h
  have hk1 := one_le_slotOf P ρ
  have hi1 := epochOf_lt P ρ
  have hρ : ρ = roundOf P k i 3 := by rw [← hk, ← hi, ← h3, roundOf_slotOf]
  subst hk hi
  have hes : epochStart ρ + 2 = roundOf P (slotOf P ρ) (epochOf P ρ) 2 := by
    rw [epochStart_eq P]; unfold roundOf; omega
  rw [hes, mem_sent_exec] at hsent
  obtain ⟨-, hsent⟩ := hsent
  simp only [outs, hu, ↓reduceIte] at hsent
  have h2 := stepOf_roundOf P (slotOf P ρ) (epochOf P ρ) 2 (by norm_num)
  obtain ⟨hheld, -, -, -, hfle, hall⟩ := act_prop_step2 P pol h2 hsent
  have hes2 : epochStart (roundOf P (slotOf P ρ) (epochOf P ρ) 2) =
      roundOf P (slotOf P ρ) (epochOf P ρ) 0 := by
    rw [epochStart_eq P, slotOf_roundOf P hk1 hi1 (by norm_num), epochOf_roundOf P hi1 (by norm_num)]
  rw [hes2] at hheld
  refine ⟨rfl, hρ, hk1, hi1, hlen, c, hheld, hfle, fun w'' hw'' => ?_⟩
  simp only [outs, hu, ↓reduceIte]
  exact hall w'' hw''

/-- An honest share `⟨C_{k,i}(m)⟩_u` is sent only in step (6) of epoch `i` of slot `k`, by `u`
itself, holding `C_{k,i}(m)`, which it sends to all its neighbours in the same round. -/
theorem honest_cshare_facts {ρ : ℕ} {u w u' : Fin n} {k i : ℕ} {m : V} (hu : u ∉ sc.F)
    (h : (w, .cshare u' k i m) ∈ outs P pol sc ρ (exec P pol sc ρ) u) :
    u' = u ∧ ρ = roundOf P k i 5 ∧ 1 ≤ k ∧ i < P.f + 2 ∧
    (i, m) ∈ certsOf (held (exec P pol sc ρ u) ρ) k ∧
    ∀ w'', P.G u w'' = true → (w'', .cert k i m) ∈ outs P pol sc ρ (exec P pol sc ρ) u := by
  simp only [outs, hu, ↓reduceIte] at h ⊢
  obtain ⟨rfl, h5, hk, hi, hc, hall⟩ := act_cshare P pol h
  have hk1 := one_le_slotOf P ρ
  have hi1 := epochOf_lt P ρ
  have hρ : ρ = roundOf P k i 5 := by rw [← hk, ← hi, ← h5, roundOf_slotOf]
  subst hk hi
  exact ⟨rfl, hρ, hk1, hi1, hc, hall⟩

/-- The signers of an available certificate: Byzantine, or honest nodes that really voted. -/
theorem voters_of_avail {r k i : ℕ} {m : V} (h : availAt P pol sc r (.cert k i m)) :
    ∃ σ : Finset (Fin n), n - P.f ≤ σ.card ∧ ∀ u ∈ σ, u ∉ sc.F →
      ∃ ρ ≤ r, ∃ w, (w, .vote u k i m) ∈ outs P pol sc ρ (exec P pol sc ρ) u := by
  obtain ⟨σ, hσ, hall⟩ := h
  refine ⟨σ, hσ, fun u hu huF => ?_⟩
  rcases hall u hu with ⟨s, hs, hsF⟩ | ⟨ρ, hρ, u', hu', w, hw⟩
  · simp only [Item.signer, Option.some.injEq] at hs; subst hs; exact absurd hsF huF
  · obtain ⟨rfl, -⟩ := honest_vote_facts hu' hw
    exact ⟨ρ, hρ, w, hw⟩

/-- The signers of an available commit-proof: Byzantine, or honest nodes that really sent a
share. -/
theorem sharers_of_avail {r k i : ℕ} {m : V} (h : availAt P pol sc r (.cproof k i m)) :
    ∃ σ : Finset (Fin n), n - P.f ≤ σ.card ∧ ∀ u ∈ σ, u ∉ sc.F →
      ∃ ρ ≤ r, ∃ w, (w, .cshare u k i m) ∈ outs P pol sc ρ (exec P pol sc ρ) u := by
  obtain ⟨σ, hσ, hall⟩ := h
  refine ⟨σ, hσ, fun u hu huF => ?_⟩
  rcases hall u hu with ⟨s, hs, hsF⟩ | ⟨ρ, hρ, u', hu', w, hw⟩
  · simp only [Item.signer, Option.some.injEq] at hs; subst hs; exact absurd hsF huF
  · obtain ⟨rfl, -⟩ := honest_cshare_facts hu' hw
    exact ⟨ρ, hρ, w, hw⟩

/-! ### Counting -/

/-- The neighbourhood of a set in `G`. -/
def nbrs (G : Fin n → Fin n → Bool) (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter fun w => ∃ u ∈ S, G u w = true

/-- The expansion property used by the proofs: every set of `n - 2f` nodes, together with its
neighbours, has more than `2f` nodes. -/
def Expands (P : Params n V) : Prop :=
  ∀ S : Finset (Fin n), n - 2 * P.f ≤ S.card → 2 * P.f < (S ∪ nbrs P.G S).card

/-- An `(n, α, β)`-expander in the sense of [WXMRS23] §3 (here in the weaker closed-neighbourhood
form: a set `S` of at least `α n` vertices has more than `β n` vertices in `S ∪ N(S)`). -/
def IsExpander (G : Fin n → Fin n → Bool) (α β : ℝ) : Prop :=
  ∀ S : Finset (Fin n), α * n ≤ S.card → β * n < (S ∪ nbrs G S).card

/-- The paper's assumptions `0 < ε`, `f ≤ (1/2 - ε) n` and `G_ε` an `(n, 2ε, 1 - 2ε)`-expander give
the expansion property used in the proofs and `2f < n`. -/
theorem expands_of_isExpander {ε : ℝ} (hε : 0 < ε) (hf : (P.f : ℝ) ≤ (1 / 2 - ε) * n)
    (hG : IsExpander P.G (2 * ε) (1 - 2 * ε)) : Expands P ∧ 2 * P.f < n := by
  have hn : (0 : ℝ) < n := by
    have := NeZero.pos n
    exact_mod_cast this
  have h2f : 2 * P.f < n := by
    have : (2 * P.f : ℝ) < n := by nlinarith
    exact_mod_cast this
  refine ⟨fun S hS => ?_, h2f⟩
  have hS' : 2 * ε * n ≤ S.card := by
    have : ((n - 2 * P.f : ℕ) : ℝ) = n - 2 * P.f := by
      rw [Nat.cast_sub h2f.le]; push_cast; ring
    have h1 : ((n - 2 * P.f : ℕ) : ℝ) ≤ S.card := by exact_mod_cast hS
    rw [this] at h1
    nlinarith
  have := hG S hS'
  have : (2 * P.f : ℝ) < (S ∪ nbrs P.G S).card := by nlinarith
  exact_mod_cast this

variable (sc) in
/-- The honest part of a quorum has at least `n - 2f` members. -/
lemma card_honest_part {σ : Finset (Fin n)} (hσ : n - P.f ≤ σ.card) (hF : sc.F.card ≤ P.f) :
    n - 2 * P.f ≤ (σ.filter (· ∉ sc.F)).card := by
  have h1 : σ ⊆ σ.filter (· ∉ sc.F) ∪ sc.F := by
    intro u hu
    by_cases h : u ∈ sc.F
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_filter.mpr ⟨hu, h⟩)
  have h2 := (card_le_card h1).trans (card_union_le _ _)
  omega

variable (sc) in
/-- `S ∪ N(S)` minus the Byzantine nodes has more than `f` nodes. -/
lemma card_T (hexp : Expands P) (hF : sc.F.card ≤ P.f) {S : Finset (Fin n)}
    (hS : n - 2 * P.f ≤ S.card) : P.f + 1 ≤ ((S ∪ nbrs P.G S) \ sc.F).card := by
  have h1 := hexp S hS
  have h2 := le_card_sdiff sc.F (S ∪ nbrs P.G S)
  omega

/-- A quorum of `n - f` cannot avoid a set of `f + 1` nodes. -/
lemma quorum_meets {σ T : Finset (Fin n)} (hσ : n - P.f ≤ σ.card) (hT : P.f + 1 ≤ T.card)
    (hfn : P.f < n) (hdisj : ∀ u ∈ σ, u ∉ T) : False := by
  have hd : Disjoint σ T := disjoint_left.mpr hdisj
  have := card_union_of_disjoint hd
  have := card_le_univ (σ ∪ T)
  simp only [Fintype.card_fin] at this
  omega

/-! ### Lemma 1, Lemma 2, Theorem 1 -/

lemma certsOf_mono {xs ys : List (Item n V)} (h : ∀ x ∈ xs, x ∈ ys) {k j : ℕ} {m : V}
    (hc : (j, m) ∈ certsOf xs k) : (j, m) ∈ certsOf ys k := by
  rcases mem_certsOf.mp hc with h1 | ⟨L, i, h1⟩
  · exact mem_certsOf.mpr (Or.inl (h _ h1))
  · exact mem_certsOf.mpr (Or.inr ⟨L, i, h _ h1⟩)

lemma heldIn_avail (hadv : sc.AdvValid P pol) {r a b : ℕ} (hbr : b ≤ r) {w : Fin n}
    (hw : w ∉ sc.F) {x : Item n V} (hx : x ∈ heldIn (exec P pol sc r w) a b) :
    ∃ t, a ≤ t ∧ t < b ∧ availAt P pol sc t x := by
  rw [mem_heldIn_exec P pol sc hbr] at hx
  obtain ⟨t, s, hat, htb, hs⟩ := hx
  refine ⟨t, hat, htb, ?_⟩
  by_cases hsF : s ∈ sc.F
  · simp only [outs, hsF, ↓reduceIte] at hs
    exact hadv t s w x hsF hw hs
  · exact honest_out_avail hadv t s hsF w x hs

lemma exists_honest_of_quorum (hF : sc.F.card ≤ P.f) (hfn : 2 * P.f < n) {σ : Finset (Fin n)}
    (hσ : n - P.f ≤ σ.card) : ∃ u ∈ σ, u ∉ sc.F := by
  have h := card_honest_part sc hσ hF
  obtain ⟨u, hu⟩ : (σ.filter (· ∉ sc.F)).Nonempty := by
    rw [← card_pos]; omega
  exact ⟨u, (mem_filter.mp hu).1, (mem_filter.mp hu).2⟩

/-- **Lemma 1** of [WXMRS23]. If certificates `C_{k,i}(m)` and `C_{k,i}(m')` both exist, then
`m = m'`. -/
theorem lemma1 (hF : sc.F.card ≤ P.f) (hexp : Expands P)
    (hfn : 2 * P.f < n) {k i : ℕ} {m m' : V} {r r' : ℕ} (h : availAt P pol sc r (.cert k i m))
    (h' : availAt P pol sc r' (.cert k i m')) : m = m' := by
  by_contra hne
  obtain ⟨σ, hσ, hσv⟩ := voters_of_avail h
  obtain ⟨σ', hσ', hσv'⟩ := voters_of_avail h'
  have hS := card_honest_part sc hσ hF
  set S := σ.filter (· ∉ sc.F)
  -- honest voters of `m` forwarded a proposal on `m` to all their neighbours
  have hSv : ∀ u ∈ S, ∃ c, Item.prop (leader P k i) k i m c ∈
        held (exec P pol sc (roundOf P k i 3) u) (roundOf P k i 3) ∧
      ∀ w'', P.G u w'' = true → (w'', .prop (leader P k i) k i m c) ∈
        outs P pol sc (roundOf P k i 2) (exec P pol sc (roundOf P k i 2)) u := by
    intro u hu
    obtain ⟨huσ, huF⟩ := mem_filter.mp hu
    obtain ⟨ρ, -, w, hw⟩ := hσv u huσ huF
    obtain ⟨-, -, -, -, -, c, hc, -, hall⟩ := honest_vote_facts huF hw
    refine ⟨c, held_mono P pol sc le_rfl le_rfl ?_ u (heldIn_sub_held _ _ _ _ hc), hall⟩
    unfold roundOf; omega
  -- so every honest node of `S ∪ N(S)` holds a proposal on `m` when voting
  have hT : ∀ w ∈ (S ∪ nbrs P.G S) \ sc.F, ∃ c, Item.prop (leader P k i) k i m c ∈
      held (exec P pol sc (roundOf P k i 3) w) (roundOf P k i 3) := by
    intro w hw
    rcases mem_union.mp (mem_sdiff.mp hw).1 with hwS | hwN
    · obtain ⟨c, hc, -⟩ := hSv w hwS; exact ⟨c, hc⟩
    · obtain ⟨u, hu, hG⟩ := (mem_filter.mp hwN).2
      obtain ⟨c, -, hall⟩ := hSv u hu
      refine ⟨c, (mem_held_exec P pol sc le_rfl w _).mpr ⟨_, u, ?_, hall w hG⟩⟩
      unfold roundOf; omega
  apply quorum_meets hσ' (card_T sc hexp hF hS) (by omega)
  intro u hu huT
  have huF : u ∉ sc.F := (mem_sdiff.mp huT).2
  obtain ⟨ρ, -, w, hw⟩ := hσv' u hu huF
  obtain ⟨-, rfl, -, -, hlen, c', hc', -, -⟩ := honest_vote_facts huF hw
  obtain ⟨c, hc⟩ := hT u huT
  have hc'' : Item.prop (leader P k i) k i m' c' ∈
      held (exec P pol sc (roundOf P k i 3) u) (roundOf P k i 3) :=
    held_mono P pol sc le_rfl le_rfl (by unfold roundOf; omega) u (heldIn_sub_held _ _ _ _ hc')
  have := two_le_length_of_mem (mem_propVals.mpr ⟨c, hc⟩) (mem_propVals.mpr ⟨c', hc''⟩) hne
  omega

/-- **Lemma 2** of [WXMRS23]. If there exists a commit-proof `thsig(C_{k,i}(m))`, then for all
epochs `j > i`, there cannot exist a certificate `C_{k,j}(m')` on `m' ≠ m`. -/
theorem lemma2 (hadv : sc.AdvValid P pol) (hF : sc.F.card ≤ P.f) (hexp : Expands P)
    (hfn : 2 * P.f < n) {k i j : ℕ} {m m' : V} {r r' : ℕ}
    (h : availAt P pol sc r (.cproof k i m)) (hij : i < j)
    (h' : availAt P pol sc r' (.cert k j m')) : m' = m := by
  obtain ⟨σ, hσ, hσv⟩ := sharers_of_avail h
  have hS := card_honest_part sc hσ hF
  set S := σ.filter (· ∉ sc.F)
  have hSv : ∀ u ∈ S, (i, m) ∈ certsOf (held (exec P pol sc (roundOf P k i 5) u)
        (roundOf P k i 5)) k ∧
      ∀ w'', P.G u w'' = true → (w'', .cert k i m) ∈
        outs P pol sc (roundOf P k i 5) (exec P pol sc (roundOf P k i 5)) u := by
    intro u hu
    obtain ⟨huσ, huF⟩ := mem_filter.mp hu
    obtain ⟨ρ, -, w, hw⟩ := hσv u huσ huF
    obtain ⟨-, rfl, -, -, hc, hall⟩ := honest_cshare_facts huF hw
    exact ⟨hc, hall⟩
  -- the certificate `C_{k,i}(m)` exists
  obtain ⟨u₀, hu₀, hu₀F⟩ := exists_honest_of_quorum hF hfn hσ
  have hcert : availAt P pol sc (roundOf P k i 5) (.cert k i m) :=
    cert_avail_of_mem_certsOf P pol sc (fun x hx => held_avail hadv le_rfl hu₀F hx)
      (hSv u₀ (mem_filter.mpr ⟨hu₀, hu₀F⟩)).1
  -- every honest node of `S ∪ N(S)` holds `C_{k,i}(m)` from round `roundOf k i 6` on
  have hT : ∀ w ∈ (S ∪ nbrs P.G S) \ sc.F, ∀ t, roundOf P k i 6 ≤ t →
      (i, m) ∈ certsOf (held (exec P pol sc t w) t) k := by
    intro w hw t ht
    rcases mem_union.mp (mem_sdiff.mp hw).1 with hwS | hwN
    · refine certsOf_mono (fun x hx => ?_) (hSv w hwS).1
      exact held_mono P pol sc le_rfl le_rfl (by unfold roundOf at ht ⊢; omega) w hx
    · obtain ⟨u, hu, hG⟩ := (mem_filter.mp hwN).2
      refine mem_certsOf.mpr (Or.inl ((mem_held_exec P pol sc le_rfl w _).mpr
        ⟨_, u, ?_, (hSv u hu).2 w hG⟩))
      unfold roundOf at ht ⊢; omega
  have hTc := card_T sc hexp hF hS
  induction j using Nat.strong_induction_on generalizing r' m' with
  | _ j ih =>
  by_contra hne
  obtain ⟨σ', hσ', hσv'⟩ := voters_of_avail h'
  apply quorum_meets hσ' hTc (by omega)
  intro u hu huT
  have huF : u ∉ sc.F := (mem_sdiff.mp huT).2
  obtain ⟨ρ, -, w, hw⟩ := hσv' u hu huF
  obtain ⟨-, rfl, hk1, hj1, -, c, hc, hfle, -⟩ := honest_vote_facts huF hw
  -- the Collect certificate of `u` in epoch `j` is at least as fresh as epoch `i`
  have hcol : (i, m) ∈ certsOf (held (exec P pol sc (roundOf P k j 2) u) (roundOf P k j 0)) k :=
    certsOf_mono (fun x hx => held_mono P pol sc le_rfl (by unfold roundOf; omega) le_rfl u hx)
      (hT u huT (roundOf P k j 0) (by unfold roundOf; omega))
  obtain ⟨c₀, hc₀, hic₀⟩ := freshest_ge hcol
  have hcv : collectVal P (roundOf P k j 2) (exec P pol sc (roundOf P k j 2) u) = some c₀.1 := by
    unfold collectVal
    rw [epochStart_eq P, slotOf_roundOf P hk1 hj1 (by norm_num), epochOf_roundOf P hj1 (by norm_num),
      hc₀]
    rfl
  rw [hcv] at hfle
  obtain ⟨j'', rfl⟩ : ∃ j'', c = some j'' := by
    rcases c with _ | j''
    · simp [fle] at hfle
    · exact ⟨j'', rfl⟩
  simp only [fle, decide_eq_true_eq] at hfle
  -- the proposal carries an existing certificate `C_{k,j''}(m')`
  obtain ⟨t, ht0, ht2, hpt⟩ := heldIn_avail hadv le_rfl huF hc
  have hcert'' : availAt P pol sc t (.cert k j'' m') := hpt.2 j'' rfl
  rcases lt_trichotomy j'' j with hlt | rfl | hgt
  · rcases Nat.lt_or_eq_of_le (hic₀.trans hfle) with hlt' | rfl
    · exact hne (ih j'' hlt hlt' hcert'')
    · exact hne (lemma1 hF hexp hfn hcert'' hcert)
  all_goals
    -- a certificate of epoch `≥ j` cannot exist before epoch `j`'s Vote round
    obtain ⟨σ'', hσ'', hσv''⟩ := voters_of_avail hcert''
    obtain ⟨u'', hu'', hu''F⟩ := exists_honest_of_quorum hF hfn hσ''
    obtain ⟨ρ'', hρ'', w'', hw''⟩ := hσv'' u'' hu'' hu''F
    obtain ⟨-, rfl, -, -, -⟩ := honest_vote_facts hu''F hw''
    unfold roundOf at ht2 hρ''
    omega

/-- **Theorem 1** of [WXMRS23] (consistency). If two honest nodes `u` and `v` commit `m_u` and
`m_v` respectively at slot `k`, then `m_u = m_v`. -/
theorem theorem1 (hadv : sc.AdvValid P pol) (hF : sc.F.card ≤ P.f) (hexp : Expands P)
    (hfn : 2 * P.f < n) {u v : Fin n} (hu : u ∉ sc.F) (hv : v ∉ sc.F) {k : ℕ} {m m' : V}
    (hm : Commits P pol sc u k m) (hm' : Commits P pol sc v k m') : m = m' := by
  -- a commit-proof gives a certificate of the same epoch
  have hcert : ∀ {w : Fin n} {m : V} {r j : ℕ}, w ∉ sc.F →
      Item.cproof k j m ∈ held (exec P pol sc r w) r →
      availAt P pol sc r (.cproof k j m) ∧ ∃ r', availAt P pol sc r' (.cert k j m) := by
    intro w m r j hw hx
    have hp := held_avail hadv le_rfl hw hx
    refine ⟨hp, ?_⟩
    obtain ⟨σ, hσ, hσv⟩ := sharers_of_avail hp
    obtain ⟨u', hu', hu'F⟩ := exists_honest_of_quorum hF hfn hσ
    obtain ⟨ρ, -, w', hw'⟩ := hσv u' hu' hu'F
    obtain ⟨-, -, -, -, hc, -⟩ := honest_cshare_facts hu'F hw'
    exact ⟨ρ, cert_avail_of_mem_certsOf P pol sc (fun x hx => held_avail hadv le_rfl hu'F hx) hc⟩
  obtain ⟨r, j, hx⟩ := hm
  obtain ⟨r', j', hx'⟩ := hm'
  obtain ⟨hp, ρ, hc⟩ := hcert hu hx
  obtain ⟨hp', ρ', hc'⟩ := hcert hv hx'
  rcases lt_trichotomy j j' with hlt | rfl | hgt
  · exact (lemma2 hadv hF hexp hfn hp hlt hc').symm
  · exact lemma1 hF hexp hfn hc hc'
  · exact lemma2 hadv hF hexp hfn hp' hgt hc

end Podc.AmortizedByzantineBroadcast
