import Papers.PODC2020.NonEquivocation.Majority
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Algorithm 2 and Theorem 5.1: interactive consistency under weak non-equivocation, `n > 2t`

Madsen–Debois, PODC 2020, Section 5.

`psl t S τ p q` is Algorithm 2 (`PSL(σ_p, n, t, p, q, P)`): process `p` with local view `τ`
(`τ w = σ(p|w)`) computes the entry of source `q`, among the active processes `S`:

1. lines 1–7: own entry: `p`'s private value (`⟨⊥⟩` if it is `⊥`);
2. lines 8–10: if `p` has a consistent `q`-majority (Definition 4.3) for a value `v`, return `v`;
3. lines 11–19: otherwise recursively compute an interactive-consistency vector of the instance
   `σ̂(p|w) = σ(p|w|q)` on `S \ {q}` with `t - 1` faults;
4. lines 20–24: return a value `v ≠ ⟨⊥⟩` that occurs at least `t` times in that vector, or `⟨⊥⟩`.

**Readings fixed here** (see `differencies.md`): the value `v` of line 8 is a genuine value (not
`⊥`; this is the type-consistent reading, since line 2 says `⊥ ∉ V`; a reading allowing `⊥`
breaks agreement, see `literal_line8_fails`); the choice in line 20 is
deterministic (any fixed choice function: `Classical.choose`); for `t = 0` without majority the
algorithm returns `⟨⊥⟩` (this never happens in admissible runs).

`theorem_5_1`: with `t + 1` rounds, `psl t` solves interactive consistency in the weak
non-equivocation fault model whenever `n > 2t`.
-/

namespace NonEquivocation

open Classical

variable {P V : Type*} [OmitVal V]

variable [DecidableEq P]

/-- Lines 1–10 of Algorithm 2, with `fb` the result of lines 11–24. -/
noncomputable def pickMaj (t : ℕ) (S : Finset P) (τ : List P → Option V) (p q : P) (fb : V) : V :=
  if p = q then rep (τ [])
  else if h : ∃ v, ∃ Q ⊆ S, Maj t τ p q Q v then h.choose else fb

/-- Lines 20–24 of Algorithm 2: a value `≠ ⟨⊥⟩` with at least `t` votes in `vec` among `S`, else
`⟨⊥⟩`. -/
noncomputable def vote (t : ℕ) (S : Finset P) (vec : P → V) : V :=
  if h : ∃ v, v ≠ omitted ∧ t ≤ S.countEq vec v then h.choose else omitted

/-! ### Unfolding lemmas -/

lemma pickMaj_self {t : ℕ} {S : Finset P} {τ : List P → Option V} {p : P} {fb : V} :
    pickMaj t S τ p p fb = rep (τ []) := by simp [pickMaj]

lemma pickMaj_of_maj {t : ℕ} {S Q : Finset P} {τ : List P → Option V} {p q : P} {fb v : V}
    (hpq : p ≠ q) (hQ : Q ⊆ S) (h : Maj t τ p q Q v) : pickMaj t S τ p q fb = v := by
  have hex : ∃ v, ∃ Q ⊆ S, Maj t τ p q Q v := ⟨v, Q, hQ, h⟩
  simp only [pickMaj, hpq, ↓reduceIte, hex, ↓reduceDIte]
  obtain ⟨Q', -, hQ'⟩ := hex.choose_spec
  exact lemma_4_6 hpq hQ' h

lemma pickMaj_of_not {t : ℕ} {S : Finset P} {τ : List P → Option V} {p q : P} {fb : V}
    (hpq : p ≠ q) (h : ¬ ∃ v, ∃ Q ⊆ S, Maj t τ p q Q v) : pickMaj t S τ p q fb = fb := by
  simp only [pickMaj, hpq, ↓reduceIte, h, ↓reduceDIte]

omit [DecidableEq P] in
lemma vote_congr {t : ℕ} {S : Finset P} {f g : P → V} (h : ∀ r ∈ S, f r = g r) :
    vote t S f = vote t S g := by
  have : ∀ v, S.countEq f v = S.countEq g v := Finset.countEq_congr h
  simp only [vote, this]

omit [DecidableEq P] in
/-- `vote` returns the unique value that qualifies, if any. -/
lemma vote_eq {t : ℕ} {S : Finset P} {f : P → V} {v : V}
    (huniq : ∀ u, u ≠ omitted → t ≤ S.countEq f u → u = v)
    (hv : v ≠ omitted → t ≤ S.countEq f v) : vote t S f = v := by
  unfold vote
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h.choose_spec
    exact huniq _ h1 h2
  · by_contra hne
    by_cases hvo : v = omitted
    · exact hne hvo.symm
    · exact h ⟨v, hvo, hv hvo⟩

/-- **Algorithm 2** (`PSL`). -/
noncomputable def psl : ℕ → Finset P → (List P → Option V) → P → P → V
  | 0, S, τ, p, q => pickMaj 0 S τ p q omitted
  | t + 1, S, τ, p, q => pickMaj (t + 1) S τ p q
      (vote (t + 1) (S.erase q) (fun r => psl t (S.erase q) (fun w => τ (w ++ [q])) p r))

/-- Algorithm 2 as an interactive-consistency algorithm on all processes. -/
noncomputable def alg2 [Fintype P] (t : ℕ) : Alg P V := fun p τ q => psl t Finset.univ τ p q

lemma psl_eq_pickMaj (t : ℕ) (S : Finset P) (τ : List P → Option V) (p q : P) :
    ∃ fb, psl t S τ p q = pickMaj t S τ p q fb := by
  cases t <;> exact ⟨_, rfl⟩

lemma psl_self (t : ℕ) (S : Finset P) (τ : List P → Option V) (p : P) :
    psl t S τ p p = rep (τ []) := by
  obtain ⟨fb, h⟩ := psl_eq_pickMaj t S τ p p
  rw [h, pickMaj_self]

lemma psl_of_maj {t : ℕ} {S Q : Finset P} {τ : List P → Option V} {p q : P} {v : V}
    (hpq : p ≠ q) (hQ : Q ⊆ S) (h : Maj t τ p q Q v) : psl t S τ p q = v := by
  obtain ⟨fb, e⟩ := psl_eq_pickMaj t S τ p q
  rw [e, pickMaj_of_maj hpq hQ h]

/-! ### Only `t + 1` rounds are read -/

theorem psl_congr : ∀ (t : ℕ) (S : Finset P) (τ τ' : List P → Option V) (p q : P),
    (∀ w : List P, w.length ≤ t + 1 → τ w = τ' w) → psl t S τ p q = psl t S τ' p q := by
  intro t
  induction t with
  | zero =>
    intro S τ τ' p q h
    have hm : ∀ v Q, Maj 0 τ p q Q v ↔ Maj 0 τ' p q Q v := fun v Q => by
      refine and_congr Iff.rfl (forall_congr' fun w => ?_)
      refine imp_congr_right fun _ => imp_congr_right fun hw => imp_congr_right fun _ => ?_
      rw [h _ (by simp only [List.length_append, List.length_singleton]; omega)]
    simp only [psl, pickMaj, hm, h [] (by simp)]
  | succ t ih =>
    intro S τ τ' p q h
    have hm : ∀ v Q, Maj (t + 1) τ p q Q v ↔ Maj (t + 1) τ' p q Q v := fun v Q => by
      refine and_congr Iff.rfl (forall_congr' fun w => ?_)
      refine imp_congr_right fun _ => imp_congr_right fun hw => imp_congr_right fun _ => ?_
      rw [h _ (by simp only [List.length_append, List.length_singleton]; omega)]
    have hrec : ∀ r, psl t (S.erase q) (fun w => τ (w ++ [q])) p r =
        psl t (S.erase q) (fun w => τ' (w ++ [q])) p r := fun r =>
      ih _ _ _ _ _ fun w hw => h _ (by simp only [List.length_append, List.length_singleton]; omega)
    simp only [psl, pickMaj, hm, h [] (by simp), hrec]

/-! ### Correctness -/

/-- The recursive instance: remove the source `q`, `σ̂(x|w) = σ(x|w|q)`. -/
def sub (σ : MsgMap P V) (q : P) : MsgMap P V := fun l => σ (l ++ [q])

omit [OmitVal V] [DecidableEq P] in
lemma loc_sub (σ : MsgMap P V) (p q : P) : loc (sub σ q) p = fun w => loc σ p (w ++ [q]) := rfl

lemma mem_erase_of_list {S : Finset P} {q : P} (hq : q ∈ S) {w : List P}
    (hw : ∀ x ∈ w, x ∈ S.erase q) :
    (∀ x ∈ w ++ [q], x ∈ S) ∧ ∀ x ∈ w.getLast?, x ≠ q := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact Finset.mem_of_mem_erase (hw x hx)
    · simp at hx; subst hx; exact hq
  · exact Finset.ne_of_mem_erase (hw x (List.mem_of_getLast? hx))


lemma sub_nonFaulty {k : ℕ} {S F : Finset P} {σ : MsgMap P V} (hσ : NonFaulty (k + 1) S F σ)
    {q : P} (hq : q ∈ S) : NonFaulty k (S.erase q) F (sub σ q) := by
  intro r hr hrF x hx w hw hs hk
  obtain ⟨hwS, hlast⟩ := mem_erase_of_list hq hw
  have hs' : Seq (x :: r :: (w ++ [q])) := by
    have : x :: r :: (w ++ [q]) = (x :: r :: w) ++ [q] := rfl
    rw [this, seq_append_singleton]
    refine ⟨hs, fun y hy => ?_⟩
    have hy' : y ∈ x :: r :: w := List.mem_of_getLast? hy
    have : y ∈ S.erase q := by
      simp only [List.mem_cons] at hy'
      rcases hy' with rfl | rfl | hy'
      · exact hx
      · exact hr
      · exact hw y hy'
    exact Finset.ne_of_mem_erase this
  exact hσ r (Finset.mem_of_mem_erase hr) hrF x (Finset.mem_of_mem_erase hx) (w ++ [q]) hwS hs'
    (by simp; omega)

omit [OmitVal V] in
lemma sub_weakNE {k : ℕ} {S : Finset P} {σ : MsgMap P V} (hσ : WeakNE (k + 1) S σ)
    {q : P} (hq : q ∈ S) : WeakNE k (S.erase q) (sub σ q) := by
  intro y hy r hr r' hr' w hw hs hs' hk h1 h2
  obtain ⟨hwS, -⟩ := mem_erase_of_list hq hw
  have key : ∀ z ∈ S.erase q, Seq (z :: y :: w) → Seq (z :: y :: (w ++ [q])) := by
    intro z hz hzs
    have : z :: y :: (w ++ [q]) = (z :: y :: w) ++ [q] := rfl
    rw [this, seq_append_singleton]
    refine ⟨hzs, fun u hu => ?_⟩
    have hu' : u ∈ z :: y :: w := List.mem_of_getLast? hu
    have : u ∈ S.erase q := by
      simp only [List.mem_cons] at hu'
      rcases hu' with rfl | rfl | hu'
      · exact hz
      · exact hy
      · exact hw u hu'
    exact Finset.ne_of_mem_erase this
  exact hσ y (Finset.mem_of_mem_erase hy) r (Finset.mem_of_mem_erase hr) r'
    (Finset.mem_of_mem_erase hr') (w ++ [q]) hwS (key r hr hs) (key r' hr' hs') (by simp; omega)
    h1 h2

lemma card_inter_erase {S F : Finset P} {q : P} (hqS : q ∈ S) (hqF : q ∈ F) :
    ((S.erase q) ∩ F).card + 1 = (S ∩ F).card := by
  rw [Finset.erase_inter]
  exact Finset.card_erase_add_one (Finset.mem_inter.2 ⟨hqS, hqF⟩)

lemma card_sdiff_ge {t : ℕ} {S F : Finset P} (hS : 2 * t < S.card) (hF : (S ∩ F).card ≤ t) :
    t + 1 ≤ (S \ F).card := by
  have := Finset.card_sdiff_add_card_inter S F
  omega

/-- Validity of `psl t` (Lemma 4.4 + Lemma 4.6): the entry of a non-faulty source is its private
value. -/
theorem psl_valid {t : ℕ} {S F : Finset P} {σ : MsgMap P V} (hS : 2 * t < S.card)
    (hF : (S ∩ F).card ≤ t) (hσ : NonFaulty (t + 1) S F σ) {p q : P} (hp : p ∈ S) (hq : q ∈ S)
    (hqF : q ∉ F) : psl t S (loc σ p) p q = rep (σ [q]) := by
  by_cases hpq : p = q
  · subst hpq; rw [psl_self]; rfl
  · exact psl_of_maj hpq Finset.sdiff_subset (lemma_4_4 hσ hp hq hqF (card_sdiff_ge hS hF))

/-- Main induction behind Theorem 5.1: validity and agreement of `psl t` on an active set `S` with
`|S| > 2t` and at most `t` faulty processes in `S`, given `t + 1` rounds. -/
theorem psl_correct (t : ℕ) : ∀ (S F : Finset P) (σ : MsgMap P V), 2 * t < S.card →
    (S ∩ F).card ≤ t → NonFaulty (t + 1) S F σ → WeakNE (t + 1) S σ →
    (∀ p ∈ S, p ∉ F → ∀ q ∈ S, q ∉ F → psl t S (loc σ p) p q = rep (σ [q])) ∧
    (∀ p ∈ S, p ∉ F → ∀ p' ∈ S, p' ∉ F → ∀ q ∈ S,
      psl t S (loc σ p) p q = psl t S (loc σ p') p' q) := by
  induction t with
  | zero =>
    intro S F σ hS hF hσ _
    refine ⟨fun p hp _ q hq hqF => psl_valid hS hF hσ hp hq hqF, ?_⟩
    intro p hp hpF p' hp' hp'F q hq
    by_cases hqF : q ∈ F
    · exfalso
      have : 0 < (S ∩ F).card := Finset.card_pos.2 ⟨q, Finset.mem_inter.2 ⟨hq, hqF⟩⟩
      omega
    · rw [psl_valid hS hF hσ hp hq hqF, psl_valid hS hF hσ hp' hq hqF]
  | succ t ih =>
    intro S F σ hS hF hσ hw
    refine ⟨fun p hp _ q hq hqF => psl_valid hS hF hσ hp hq hqF, ?_⟩
    intro p hp hpF p' hp' hp'F q hq
    by_cases hqF : q ∉ F
    · rw [psl_valid hS hF hσ hp hq hqF, psl_valid hS hF hσ hp' hq hqF]
    push Not at hqF
    -- the recursive instance
    have hcard := card_inter_erase hq hqF
    have hS' : 2 * t < (S.erase q).card := by
      rw [Finset.card_erase_of_mem hq]; omega
    have hF' : ((S.erase q) ∩ F).card ≤ t := by omega
    obtain ⟨ihv, iha⟩ := ih (S.erase q) F (sub σ q) hS' hF' (sub_nonFaulty hσ hq)
      (sub_weakNE hw hq)
    have hne : ∀ x, x ∉ F → x ≠ q := fun x hx h => hx (h ▸ hqF)
    have unf : ∀ x, psl (t + 1) S (loc σ x) x q = pickMaj (t + 1) S (loc σ x) x q
        (vote (t + 1) (S.erase q) (fun r => psl t (S.erase q) (loc (sub σ q) x) x r)) :=
      fun x => rfl
    -- the case where exactly one of them has a consistent majority
    have one_sided : ∀ x ∈ S, x ∉ F → ∀ y ∈ S, y ∉ F → ∀ (v : V) (Q : Finset P), Q ⊆ S →
        Maj (t + 1) (loc σ x) x q Q v → (¬ ∃ v, ∃ Q ⊆ S, Maj (t + 1) (loc σ y) y q Q v) →
        psl (t + 1) S (loc σ y) y q = v := by
      intro x hx hxF y hy hyF v Q hQS hm hno
      have hxq := hne x hxF
      have hyq := hne y hyF
      rw [unf, pickMaj_of_not hyq hno]
      have hvx : σ [x, q] = some v := hm.direct hxq
      have hvecx : ∀ r ∈ Q.erase q, psl t (S.erase q) (loc (sub σ q) x) x r = v := by
        intro r hr
        by_cases hrx : x = r
        · subst hrx; rw [psl_self]; show rep (σ [x, q]) = v; rw [hvx]; rfl
        · refine psl_of_maj hrx (Finset.erase_subset_erase q hQS) ⟨?_, ?_⟩
          · have := Finset.pred_card_le_card_erase (s := Q) (a := q)
            have := hm.1
            omega
          · intro w hw' hl hs
            have hrq : r ≠ q := Finset.ne_of_mem_erase hr
            show σ (x :: ((w ++ [r]) ++ [q])) = some v
            refine hm.2 (w ++ [r]) (fun z hz => ?_) (by simp; omega) ?_
            · rcases List.mem_append.1 hz with hz | hz
              · exact Finset.mem_of_mem_erase (hw' z hz)
              · simp at hz; subst hz; exact Finset.mem_of_mem_erase hr
            · rw [show x :: ((w ++ [r]) ++ [q]) = (x :: (w ++ [r])) ++ [q] from rfl,
                seq_append_singleton]
              refine ⟨hs, fun z hz => ?_⟩
              rw [show x :: (w ++ [r]) = (x :: w) ++ [r] from rfl, List.getLast?_append] at hz
              simp at hz
              exact hz ▸ hrq
      have hxS' : x ∈ S.erase q := Finset.mem_erase.2 ⟨hxq, hx⟩
      have hyS' : y ∈ S.erase q := Finset.mem_erase.2 ⟨hyq, hy⟩
      apply vote_eq
      · intro u hu hcu
        obtain ⟨r, hrS', hrF', hru⟩ :=
          Finset.exists_mem_notMem_of_card_lt_countEq (F := S.erase q ∩ F) (hF'.trans_lt hcu)
        have hrF : r ∉ F := fun h => hrF' (Finset.mem_inter.2 ⟨hrS', h⟩)
        rw [ihv y hyS' hyF r hrS' hrF] at hru
        have hrq : r ≠ q := Finset.ne_of_mem_erase hrS'
        show u = v
        change rep (σ [r, q]) = u at hru
        cases hrq' : σ [r, q] with
        | none => rw [hrq'] at hru; exact absurd hru.symm hu
        | some a =>
          rw [hrq'] at hru
          simp only [rep_some] at hru
          subst hru
          have := hw q hq x hx r (Finset.mem_of_mem_erase hrS') [] (by simp) (seq_pair.2 hxq)
            (seq_pair.2 hrq) (by simp) (by rw [hvx]; simp) (by rw [hrq']; simp)
          rw [hvx, hrq'] at this
          exact (Option.some.inj this).symm
      · intro _
        have hsub : Q.erase q ⊆ (S.erase q).filter
            (fun r => psl t (S.erase q) (loc (sub σ q) y) y r = v) := by
          intro r hr
          have hrS' : r ∈ S.erase q := Finset.erase_subset_erase q hQS hr
          refine Finset.mem_filter.2 ⟨hrS', ?_⟩
          rw [iha y hyS' hyF x hxS' hxF r hrS', hvecx r hr]
        have h1 : (Q.erase q).card ≤ (S.erase q).countEq
            (fun r => psl t (S.erase q) (loc (sub σ q) y) y r) v := Finset.card_le_card hsub
        have h2 := Finset.pred_card_le_card_erase (s := Q) (a := q)
        have h3 := hm.1
        omega
    have hpq := hne p hpF
    have hp'q := hne p' hp'F
    by_cases h1 : ∃ v, ∃ Q ⊆ S, Maj (t + 1) (loc σ p) p q Q v <;>
      by_cases h2 : ∃ v, ∃ Q ⊆ S, Maj (t + 1) (loc σ p') p' q Q v
    · obtain ⟨v, Q, hQ, hm⟩ := h1
      obtain ⟨v', Q', hQ', hm'⟩ := h2
      rw [psl_of_maj hpq hQ hm, psl_of_maj hp'q hQ' hm']
      exact lemma_4_8 (by omega) hw hp hp' hq hpq hp'q hm hm'
    · obtain ⟨v, Q, hQ, hm⟩ := h1
      rw [psl_of_maj hpq hQ hm, one_sided p hp hpF p' hp' hp'F v Q hQ hm h2]
    · obtain ⟨v, Q, hQ, hm⟩ := h2
      rw [psl_of_maj hp'q hQ hm, one_sided p' hp' hp'F p hp hpF v Q hQ hm h1]
    · rw [unf, unf, pickMaj_of_not hpq h1, pickMaj_of_not hp'q h2]
      refine vote_congr fun r hr => ?_
      exact iha p (Finset.mem_erase.2 ⟨hpq, hp⟩) hpF p' (Finset.mem_erase.2 ⟨hp'q, hp'⟩) hp'F r hr

lemma alg2_eq [Fintype P] (t : ℕ) (σ : MsgMap P V) (p q : P) :
    alg2 t p (view (t + 1) σ p) q = psl t Finset.univ (loc σ p) p q :=
  psl_congr _ _ _ _ _ _ fun _ hw => view_of_le hw

/-- **Theorem 5.1**: Algorithm 2 is correct — with `t + 1` rounds it solves interactive consistency
in the weak non-equivocation fault model whenever `n > 2t`. -/
theorem theorem_5_1 [Fintype P] {t : ℕ} (h : 2 * t < Fintype.card P) :
    SolvesIC wne (t + 1) t (alg2 (P := P) (V := V) t) := by
  intro F σ hF hm hpriv
  obtain ⟨hv, ha⟩ := psl_correct t Finset.univ F σ (by simpa using h)
    (by simpa using hF) hm.1 hm.2
  refine ⟨fun p q hp hq => ?_, fun p p' q hp hp' => ?_⟩
  · rw [alg2_eq, hv p (Finset.mem_univ _) hp q (Finset.mem_univ _) hq]
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hpriv q hq)
    rw [ha]; rfl
  · rw [alg2_eq, alg2_eq]
    exact ha p (Finset.mem_univ _) hp p' (Finset.mem_univ _) hp' q (Finset.mem_univ _)

end NonEquivocation
