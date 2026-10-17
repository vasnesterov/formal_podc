import Papers.PODC2025.BAWithPredictions.AuthBB
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Authenticated Byzantine Agreement with classification (Section 8.3: Lemmas 24–27, Theorem 6)

Model: synchronous authenticated round executions `E : RoundRun (alg k t) F inp` with
`E.SyncFrom 0` and `E.AuthValid auth` (ideal unforgeable signatures, rushing eavesdropping
adversary; `alg_unforging`); inputs `inp i = (x_i, c_i)` (value, classification vector).
Hypotheses of Theorem 6: `|F| ≤ t`, `2t < n`, `2k + 1 ≤ n - t - k`, and `k_A ≤ k` for the
classification vectors `c_i` of the honest processes (`(mis F c).card ≤ k`).

* `lemma24_faulty`, `lemma24_card`, `lemma24_honest`: **Lemma 24** for `Csup ⊇ C`:
  `|Csup ∩ F| ≤ k_F ≤ k`, `|Csup| ≤ 2k + 1 + k_A ≤ 3k + 1`, `|C ∩ H| ≥ k + 1`.
* `lemma25`, `lemma26` (agreement), `lemma27` (strong unanimity), `theorem6`.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions.AuthBA

open Finset Cslib.Byzantine.PartialSync

variable {P V : Type*} [Fintype P] [LinearOrder P] [LinearOrder V]

/-! ### Lemma 24 -/

section L24

variable {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}

/-- **Lemma 24**, `|C ∩ F| ≤ k_F`: every faulty process that received an honest vote is
misclassified (as honest) by that honest process (Corollary 1). -/
theorem lemma24_faulty (hF : F.card ≤ t) (hn : 2 * k + 1 ≤ Fintype.card P - t - k)
    (hk : (mis F fun i => (inp i).2).card ≤ k) :
    (F.filter (· ∈ Csup k F inp)).card ≤ ((mis F fun i => (inp i).2).filter (· ∈ F)).card := by
  apply card_le_card
  intro j hj
  obtain ⟨hjF, hjC⟩ := mem_filter.mp hj
  obtain ⟨i, hi, hpos⟩ := mem_Csup.mp hjC
  have h1 := corollary1 (c := fun i => (inp i).2) hF hi (j := j) (by omega)
  refine mem_filter.mpr ⟨?_, hjF⟩
  simp only [mis, mem_filter, mem_univ, true_and]
  exact ⟨i, hi, by simp [h1, hjF]⟩

/-- **Lemma 24**, `|C| ≤ 3k + 1` (in the exact form `|Csup| ≤ 2k + 1 + k_A`). -/
theorem lemma24_card (hF : F.card ≤ t) (hn : 2 * k + 1 ≤ Fintype.card P - t - k)
    (hk : (mis F fun i => (inp i).2).card ≤ k) :
    (Csup k F inp).card ≤ 2 * k + 1 + (mis F fun i => (inp i).2).card := by
  have h6 := lemma6 (F := F) (c := fun i => (inp i).2) (r := 2 * k + 1) (by omega)
  have hsub : Csup k F inp ⊆ (univ.filter fun j => j ∉ F ∧ ∃ i ∉ F, pos (inp i).2 j ≤ 2 * k + 1) ∪
      F.filter (· ∈ Csup k F inp) := by
    intro j hj
    by_cases hjF : j ∈ F
    · exact mem_union_right _ (mem_filter.mpr ⟨hjF, hj⟩)
    · exact mem_union_left _ (by simpa [hjF] using mem_Csup.mp hj)
  have h24 := lemma24_faulty hF hn hk
  have hsplit := card_filter_add_card_filter_not (s := mis F fun i => (inp i).2) (fun j => j ∈ F)
  have := card_le_card hsub
  have := card_union_le (univ.filter fun j => j ∉ F ∧ ∃ i ∉ F, pos (inp i).2 j ≤ 2 * k + 1)
    (F.filter (· ∈ Csup k F inp))
  omega

theorem lemma24_card' (hF : F.card ≤ t) (hn : 2 * k + 1 ≤ Fintype.card P - t - k)
    (hk : (mis F fun i => (inp i).2).card ≤ k) : (Csup k F inp).card ≤ 3 * k + 1 := by
  have := lemma24_card hF hn hk; omega

theorem lemma24_faulty' (hF : F.card ≤ t) (hn : 2 * k + 1 ≤ Fintype.card P - t - k)
    (hk : (mis F fun i => (inp i).2).card ≤ k) : (F.filter (· ∈ Csup k F inp)).card ≤ k :=
  (lemma24_faulty hF hn hk).trans ((card_le_card (filter_subset _ _)).trans hk)

/-- **Lemma 24**, `|C ∩ H| ≥ k + 1`: the honest processes of a core set (Lemma 5) receive the
votes of all `n - f ≥ n - t ≥ t + 1` honest processes. This uses `t < n / 2`. -/
theorem lemma24_honest (E : RoundRun (alg (P := P) (V := V) k t) F inp) (hsync : E.SyncFrom 0)
    (hF : F.card ≤ t) (htn : 2 * t < Fintype.card P) (hn : 2 * k + 1 ≤ Fintype.card P - t - k)
    (hk : (mis F fun i => (inp i).2).card ≤ k) : k + 1 ≤ (CH E).card := by
  obtain ⟨G, hGH, hGcard, hGpos⟩ :=
    lemma5 (F := F) (c := fun i => (inp i).2) (ℓ := 1) (r := 2 * k + 1) le_rfl (by omega)
  have hsub : G ⊆ CH E := by
    intro j hj
    simp only [CH, mem_filter, mem_univ, true_and]
    refine ⟨hGH j hj, ?_⟩
    have hvot : (univ.filter fun i => i ∉ F) ⊆ voters j (E.rcv 0 j) := by
      intro i hi
      have hi := (mem_filter.mp hi).2
      simp only [voters, mem_filter, mem_univ, true_and]
      rw [hsync 0 le_rfl j i (hGH j hj) hi]
      rw [send_eq, ifp rfl, c_eq, ifp (hGpos i hi j hj).2]
    have h1 := card_le_card hvot
    rw [card_filter_notMem_univ] at h1
    rw [cert_eq, ifp (by omega)]
    rfl
  have := card_le_card hsub
  omega

end L24

/-! ### Lemmas 25–27 -/

section Main

variable {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}
  (E : RoundRun (alg (P := P) (V := V) k t) F inp)
  (hF : F.card ≤ t) (hsync : E.SyncFrom 0) (hA : E.AuthValid auth)
  (htn : 2 * t < Fintype.card P) (hn : 2 * k + 1 ≤ Fintype.card P - t - k)
  (hk : (mis F fun i => (inp i).2).card ≤ k)

theorem plurality_eq (p : P) : plurality (E.s (k + 2) p) =
    Finset.pluralityMin (univ.filter fun s => (bb E p s).isSome) (fun s => (bb E p s).getD (inp p).1)
      (inp p).1 := by
  unfold plurality; rw [x_eq]; rfl

omit [Fintype P] in
theorem plurVal_eq_some {t : ℕ} {q : P} {mo : Option (Msg P V)} {v : V} :
    plurVal t q mo = some v ↔ ∃ cc, mo = some (.plur q v cc) ∧ t + 1 ≤ cc.card := by
  rcases mo with _ | ⟨_ | _ | ⟨i, w, cc⟩⟩ <;> simp only [plurVal, reduceCtorEq,
    Option.some.injEq, Msg.plur.injEq, false_and, exists_false]
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨cc, ⟨h.1, rfl, rfl⟩, h.2⟩
    · rintro ⟨cc', ⟨-, rfl, rfl⟩, -⟩; rfl
  · simp only [false_iff, not_exists, not_and]
    rintro cc' ⟨rfl, rfl, rfl⟩ h'; exact h ⟨rfl, h'⟩

theorem send_plur (q p : P) : (alg k t).send (k + 2) q (E.s (k + 2) q) p =
    (cert E q).map fun cc => Msg.plur q (plurality (E.s (k + 2) q)) cc := by
  rw [send_eq, ifn (by omega), ifn (by omega), ifp rfl, cc_eq E (by omega)]

include hF hsync hA in
/-- The core of **Lemma 26**: if all honest processes with a certificate broadcast the same value
`w` in round `k + 2`, there are at least `k + 1` of them and at most `k` faulty processes in
`Csup`, every honest process decides `w`. -/
theorem decision_eq {w : V} (hw : ∀ q ∈ CH E, plurality (E.s (k + 2) q) = w)
    (hCH : k + 1 ≤ (CH E).card) (hCF : (F.filter (· ∈ Csup k F inp)).card ≤ k) {p : P}
    (hp : p ∉ F) (x : V) : decision t x (E.rcv (k + 2) p) = w := by
  unfold decision
  apply Finset.pluralityMin_eq_of_card_lt_two_mul_countEq
  set X := univ.filter fun q => (plurVal t q (E.rcv (k + 2) p q)).isSome with hXdef
  have hCHv : ∀ q ∈ CH E, plurVal t q (E.rcv (k + 2) p q) = some w := by
    intro q hq
    obtain ⟨hqF, hqc⟩ := by simpa [CH] using hq
    obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hqc
    rw [hsync _ (Nat.zero_le _) p q hp hqF, send_plur, hS, ← hw q hq]
    exact plurVal_eq_some.mpr ⟨S, rfl, (cert_some E hS).2⟩
  have h1 : CH E ⊆ X.filter fun q => (plurVal t q (E.rcv (k + 2) p q)).getD x = w := by
    intro q hq
    rw [mem_filter, hXdef, mem_filter, hCHv q hq]
    simp
  have h2 : X ⊆ CH E ∪ F.filter (· ∈ Csup k F inp) := by
    intro q hq
    rw [hXdef, mem_filter] at hq
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq.2
    obtain ⟨cc, hcc, hcard⟩ := plurVal_eq_some.mp hv
    by_cases hqF : q ∈ F
    · refine mem_union_right _ (mem_filter.mpr ⟨hqF, ?_⟩)
      exact mem_Csup_of_cert E hF hA hp hcc hcard (fun j hj => ⟨j, hj, rfl⟩)
    · refine mem_union_left _ ?_
      have := E.honest _ p q _ hqF hcc
      rw [send_plur] at this
      simp only [CH, mem_filter, mem_univ, true_and]
      refine ⟨hqF, ?_⟩
      cases hc : cert E q with
      | none => rw [hc] at this; simp at this
      | some _ => rfl
  have := card_le_card h1
  have := card_le_card h2
  have := card_union_le (CH E) (F.filter (· ∈ Csup k F inp))
  unfold Finset.countEq
  beta_reduce
  omega

include hF hsync hA htn hn hk in
/-- **Lemma 25.** All honest processes that have a committee certificate broadcast the same value
on line 11. -/
theorem lemma25 {i j : P} (hi : i ∈ CH E) (hj : j ∈ CH E) :
    plurality (E.s (k + 2) i) = plurality (E.s (k + 2) j) := by
  have hCF := lemma24_faulty' hF hn hk
  have hbb : bb E i = bb E j := funext (lemma23 E hF hsync hA hCF hi hj)
  obtain ⟨s, hs⟩ : (CH E).Nonempty := by
    rw [← card_pos]; have := lemma24_honest E hsync hF htn hn hk; omega
  have hne : (univ.filter fun s => (bb E i s).isSome).Nonempty :=
    ⟨s, by simp [lemma21 E hsync hA hs (mem_filter.mp hi).2.1]⟩
  rw [plurality_eq, plurality_eq, hbb]
  rw [hbb] at hne
  exact Finset.pluralityMin_congr hne (fun s hs => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (mem_filter.mp hs).2
    simp [hv])

theorem decide_eq {r : ℕ} {p : P} {d : V} (h : (alg k t).decide p (E.s r p) = some d) :
    d = decision t (inp p).1 (E.rcv (k + 2) p) := by
  change (E.s r p).dec = some d at h
  rcases Nat.lt_or_ge r (k + 3) with hr | hr
  · rw [dec_early E (by omega)] at h; cases h
  · rw [dec_eq E hr] at h; exact (Option.some.inj h).symm

include hF hsync hA htn hn hk in
/-- **Lemma 26 (Agreement).** All honest processes return the same value. -/
theorem lemma26 {p q : P} (hp : p ∉ F) (hq : q ∉ F) {r r' : ℕ} {a b : V}
    (ha : (alg k t).decide p (E.s r p) = some a) (hb : (alg k t).decide q (E.s r' q) = some b) :
    a = b := by
  obtain ⟨i, hi⟩ : (CH E).Nonempty := by
    rw [← card_pos]; have := lemma24_honest E hsync hF htn hn hk; omega
  have hw : ∀ j ∈ CH E, plurality (E.s (k + 2) j) = plurality (E.s (k + 2) i) :=
    fun j hj => lemma25 E hF hsync hA htn hn hk hj hi
  have hCH := lemma24_honest E hsync hF htn hn hk
  have hCF := lemma24_faulty' hF hn hk
  rw [decide_eq E ha, decide_eq E hb, decision_eq E hF hsync hA hw hCH hCF hp,
    decision_eq E hF hsync hA hw hCH hCF hq]

include hF hsync hA htn hn hk in
/-- **Lemma 27**, first step: if all honest processes with a certificate have input `v`, every
honest process with a certificate has plurality value `v`. -/
theorem plurality_unanimous {v : V} (hv : ∀ p ∈ CH E, (inp p).1 = v) {j : P} (hj : j ∈ CH E) :
    plurality (E.s (k + 2) j) = v := by
  rw [plurality_eq]
  apply Finset.pluralityMin_eq_of_card_lt_two_mul_countEq
  have hjF := (mem_filter.mp hj).2.1
  set X := univ.filter fun s => (bb E j s).isSome with hXdef
  have h1 : CH E ⊆ X.filter fun s => (bb E j s).getD (inp j).1 = v := by
    intro s hs
    have := lemma21 E hsync hA hs hjF
    rw [hv s hs] at this
    simp [hXdef, this]
  have h2 : X ⊆ CH E ∪ F.filter (· ∈ Csup k F inp) := by
    intro s hs
    have hs' := (mem_filter.mp hs).2
    by_cases hsF : s ∈ F
    · refine mem_union_right _ (mem_filter.mpr ⟨hsF, ?_⟩)
      by_contra hC
      rw [lemma22_faulty E hF hA hC hjF] at hs'; simp at hs'
    · refine mem_union_left _ ?_
      simp only [CH, mem_filter, mem_univ, true_and]
      refine ⟨hsF, ?_⟩
      cases hc : cert E s with
      | none => rw [lemma22_honest E hA hsF hc hjF] at hs'; simp at hs'
      | some _ => rfl
  have := card_le_card h1
  have := card_le_card h2
  have := card_union_le (CH E) (F.filter (· ∈ Csup k F inp))
  have := lemma24_honest E hsync hF htn hn hk
  have := lemma24_faulty' hF hn hk
  unfold Finset.countEq
  beta_reduce
  omega

include hF hsync hA htn hn hk in
/-- **Lemma 27 (Strong Unanimity).** If every honest process (with a committee certificate) has
the same input value `v`, every honest process returns `v`. -/
theorem lemma27 {v : V} (hv : ∀ p ∈ CH E, (inp p).1 = v) {p : P} (hp : p ∉ F) {r : ℕ} {a : V}
    (ha : (alg k t).decide p (E.s r p) = some a) : a = v := by
  rw [decide_eq E ha]
  exact decision_eq E hF hsync hA (fun j hj => plurality_unanimous E hF hsync hA htn hn hk hv hj)
    (lemma24_honest E hsync hF htn hn hk) (lemma24_faulty' hF hn hk) hp _

/-- Every process returns after exactly `k + 3` rounds (whatever the classification). -/
theorem decide_k3 (p : P) {r : ℕ} :
    (alg k t).decide p (E.s r p) = if k + 3 ≤ r then
      some (decision t (inp p).1 (E.rcv (k + 2) p)) else none := by
  change (E.s r p).dec = _
  split_ifs with h
  · exact dec_eq E h p
  · exact dec_early E (by omega) p

end Main

/-- **Theorem 6.** If `k` bounds the number of processes misclassified by the honest processes'
classification vectors, `2k + 1 ≤ n - t - k`, `t < n / 2` and `|F| ≤ t`, then in every synchronous
execution with unforgeable signatures Algorithm 7 (`alg k t`, the paper says "Algorithm 5")
satisfies Agreement and Strong Unanimity; moreover (with no hypothesis on the classification)
every process returns at the end of round `k + 3` (i.e. its decision is exhibited from round
`k + 3` on, and not before). The message bounds are `theorem6_messages`,
`theorem6_messages_per_process`. -/
theorem theorem6 {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}
    (E : RoundRun (alg (P := P) (V := V) k t) F inp) (hsync : E.SyncFrom 0)
    (hA : E.AuthValid auth) (hF : F.card ≤ t) (htn : 2 * t < Fintype.card P)
    (hn : 2 * k + 1 ≤ Fintype.card P - t - k) (hk : (mis F fun i => (inp i).2).card ≤ k) :
    (∀ p ∉ F, ∀ q ∉ F, ∀ r r' a b, (alg k t).decide p (E.s r p) = some a →
        (alg k t).decide q (E.s r' q) = some b → a = b) ∧
    (∀ v, (∀ p ∉ F, (inp p).1 = v) → ∀ p ∉ F, ∀ r a, (alg k t).decide p (E.s r p) = some a →
        a = v) ∧
    (∀ p, (∀ r < k + 3, (alg k t).decide p (E.s r p) = none) ∧
        ∃ a, (alg k t).decide p (E.s (k + 3) p) = some a) :=
  ⟨fun _ hp _ hq _ _ _ _ ha hb => lemma26 E hF hsync hA htn hn hk hp hq ha hb,
    fun _ hv _ hp _ _ ha => lemma27 E hF hsync hA htn hn hk
      (fun q hq => hv q (mem_filter.mp hq).2.1) hp ha,
    fun p => ⟨fun r hr => by rw [decide_k3, ifn (by omega)],
      ⟨_, by rw [decide_k3, ifp le_rfl]⟩⟩⟩

end BAWithPredictions.AuthBA
