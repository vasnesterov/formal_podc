import Papers.PODC2017.NoisyRadioBroadcast.Prob

/-!
# Lemma 25, combinatorial part: the meta-round transformation

Given a static faultless schedule `b` for `k` messages that delivers within `R` rounds, we build an
adaptive schedule for `k * x` messages (message `(i, j) : Fin k × Fin x` is the `j`-th sub-message
of `mᵢ`) that runs `R` meta-rounds of `L` rounds each. In meta-round `t`, a node `u` which
broadcasts `mᵢ` in round `t` of the faultless run broadcasts the least sub-message `(i, j)` that is
still unknown to one of its faultless receivers (and is silent if there is none). If every node has
at least `x` clean coins in every meta-round, all messages are delivered (`delivered_of_good`).
-/

namespace Podc.NoisyRadioBroadcast

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section General

variable (G : SimpleGraph V) {k : ℕ}

omit [DecidableEq V] in
theorem senderTransform_mem_stepKnow {f : FaultModel} {K : Know V k} {a : V → Option (Fin k)}
    {c : V → Bool} {u : V} {i : Fin k} :
    i ∈ stepKnow G f K a c u ↔ i ∈ K u ∨ heard G f (effective K a) c u = some i := by
  unfold stepKnow
  split
  · next j h => simp [h, eq_comm, or_comm]
  · next h => simp [h]

theorem senderTransform_run_subset_succ (s : V) (f : FaultModel) (sch : AdaptiveSchedule V k)
    (ω : ℕ → V → Bool) (r : ℕ) (u : V) :
    run G s f sch ω r u ⊆ run G s f sch ω (r + 1) u := fun i hi => by
  show i ∈ stepKnow G f _ _ _ u
  exact (senderTransform_mem_stepKnow G).2 (Or.inl hi)

theorem senderTransform_run_mono (s : V) (f : FaultModel) (sch : AdaptiveSchedule V k)
    (ω : ℕ → V → Bool) {r r' : ℕ} (h : r ≤ r') (u : V) :
    run G s f sch ω r u ⊆ run G s f sch ω r' u := by
  induction r', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (senderTransform_run_subset_succ G s f sch ω n u)

omit [Fintype V] [DecidableEq V] in
theorem senderTransform_effective_eq_some {K : Know V k} {a : V → Option (Fin k)} {u : V}
    {i : Fin k} : effective K a u = some i ↔ a u = some i ∧ i ∈ K u := by
  unfold effective
  split
  · next j h =>
    split_ifs with h'
    · simp only [Option.some.injEq]; constructor
      · rintro rfl; exact ⟨h, h'⟩
      · rintro ⟨h1, -⟩; rw [h] at h1; exact Option.some_injective _ h1
    · simp only [false_iff, not_and]
      intro h1; rw [h] at h1; cases h1; exact h'
  · next h => simp [h]

omit [Fintype V] [DecidableEq V] in
theorem senderTransform_effective_of_none {K : Know V k} {a : V → Option (Fin k)} {u : V}
    (h : a u = none) : effective K a u = none := by
  unfold effective; rw [h]

end General

namespace SenderTransform

variable (G : SimpleGraph V) (s : V) {k : ℕ} (b : StaticSchedule V k)

/-- The knowledge before round `t` of the faultless run of `b`. -/
noncomputable def K0 (t : ℕ) : Know V k := run G s .receiver b.toAdaptive (fun _ _ => true) t

/-- The effective actions of round `t` of the faultless run of `b`. -/
noncomputable def e0 (t : ℕ) : V → Option (Fin k) := effective (K0 G s b t) (b t)

/-- Sub-message `j` of message `i`. -/
def enc {x : ℕ} (i : Fin k) (j : Fin x) : Fin (k * x) := finProdFinEquiv (i, j)

open Classical in
/-- The faultless receivers of `u` in round `t`. -/
noncomputable def rcv (t : ℕ) (u : V) : Finset V := univ.filter fun v => Hears G (e0 G s b t) v u

open Classical in
/-- The sub-messages of `mᵢ` still unknown to some faultless receiver of `u` in round `t`. -/
noncomputable def missing {x : ℕ} (t : ℕ) (u : V) (i : Fin k) (K : Know V (k * x)) :
    Finset (Fin x) :=
  univ.filter fun j => ∃ v ∈ rcv G s b t u, enc i j ∉ K v

/-- The action of `u` in meta-round `t` given the knowledge state `K`. -/
noncomputable def act (x t : ℕ) (K : Know V (k * x)) (u : V) : Option (Fin (k * x)) :=
  match e0 G s b t u with
  | none => none
  | some i =>
    if h : (missing G s b t u i K).Nonempty then some (enc i ((missing G s b t u i K).min' h))
    else none

/-- The transformed adaptive schedule: round `r` belongs to meta-round `r / L`. -/
noncomputable def sch (x L : ℕ) : AdaptiveSchedule V (k * x) := fun r K => act G s b x (r / L) K

variable {G s b}

theorem act_of_none {x t : ℕ} {K : Know V (k * x)} {u : V} (h : e0 G s b t u = none) :
    act G s b x t K u = none := by
  unfold act; rw [h]

theorem act_of_some {x t : ℕ} {K : Know V (k * x)} {u : V} {i : Fin k}
    (h : e0 G s b t u = some i) (hne : (missing G s b t u i K).Nonempty) :
    act G s b x t K u = some (enc i ((missing G s b t u i K).min' hne)) := by
  unfold act; simp [h, hne]

theorem act_eq_some {x t : ℕ} {K : Know V (k * x)} {u : V} {m : Fin (k * x)}
    (h : act G s b x t K u = some m) : ∃ i j, e0 G s b t u = some i ∧ m = enc i j := by
  unfold act at h
  split at h
  · simp at h
  · next i hi =>
    split_ifs at h
    exact ⟨i, _, hi, (Option.some_injective _ h).symm⟩

theorem isSome_of_act {x t : ℕ} {K : Know V (k * x)} {u : V}
    (h : (act G s b x t K u).isSome) : (e0 G s b t u).isSome := by
  cases he : e0 G s b t u
  · rw [act_of_none he] at h; simp at h
  · rfl

theorem mem_K0_of_e0 {t : ℕ} {u : V} {i : Fin k} (h : e0 G s b t u = some i) :
    i ∈ K0 G s b t u :=
  (senderTransform_effective_eq_some.1 h).2

theorem div_eq {t L ℓ : ℕ} (hℓ : ℓ < L) : (t * L + ℓ) / L = t := by
  have hL : 0 < L := by omega
  rw [mul_comm, Nat.mul_add_div hL, Nat.div_eq_of_lt hℓ, add_zero]

variable (G s b)

/-- The knowledge before round `r` of the transformed run. -/
noncomputable abbrev Kr (x L : ℕ) (ω : ℕ → V → Bool) (r : ℕ) : Know V (k * x) :=
  run G s .sender (sch G s b x L) ω r

/-- The invariant at the start of meta-round `t`. -/
def Inv (x L : ℕ) (ω : ℕ → V → Bool) (t : ℕ) : Prop :=
  ∀ v i, i ∈ K0 G s b t v → ∀ j : Fin x, enc i j ∈ Kr G s b x L ω (t * L) v

/-- The number of clean coins of `u` in the first `ℓ` rounds of meta-round `t`. -/
def clean (L : ℕ) (ω : ℕ → V → Bool) (t : ℕ) (u : V) (ℓ : ℕ) : ℕ :=
  #((range ℓ).filter fun ℓ' => ω (t * L + ℓ') u = true)

variable {G s b}

theorem eff_eq {x L t ℓ : ℕ} {ω : ℕ → V → Bool} (hI : Inv G s b x L ω t) (hℓ : ℓ < L) :
    effective (Kr G s b x L ω (t * L + ℓ)) (sch G s b x L (t * L + ℓ) (Kr G s b x L ω (t * L + ℓ)))
      = act G s b x t (Kr G s b x L ω (t * L + ℓ)) := by
  funext w
  have hs : sch G s b x L (t * L + ℓ) (Kr G s b x L ω (t * L + ℓ)) =
      act G s b x t (Kr G s b x L ω (t * L + ℓ)) := by
    unfold sch; rw [div_eq hℓ]
  rw [hs]
  cases h : act G s b x t (Kr G s b x L ω (t * L + ℓ)) w with
  | none => exact senderTransform_effective_of_none h
  | some m =>
    obtain ⟨i, j, he, rfl⟩ := act_eq_some h
    refine senderTransform_effective_eq_some.2 ⟨h, ?_⟩
    exact senderTransform_run_mono G s _ _ _ (Nat.le_add_right _ _) w
      (hI w i (mem_K0_of_e0 he) j)

theorem deliver {x L t ℓ : ℕ} {ω : ℕ → V → Bool} (hI : Inv G s b x L ω t) (hℓ : ℓ < L) {u v : V}
    {i : Fin k} (hu : e0 G s b t u = some i) (hv : v ∈ rcv G s b t u)
    (hne : (missing G s b t u i (Kr G s b x L ω (t * L + ℓ))).Nonempty)
    (hc : ω (t * L + ℓ) u = true) :
    enc i ((missing G s b t u i (Kr G s b x L ω (t * L + ℓ))).min' hne) ∈
      Kr G s b x L ω (t * L + ℓ + 1) v := by
  classical
  show _ ∈ stepKnow G .sender _ _ _ v
  refine (senderTransform_mem_stepKnow G).2 (Or.inr ?_)
  rw [eff_eq hI hℓ, heard_eq_some_iff]
  have hH : Hears G (e0 G s b t) v u := (mem_filter.1 hv).2
  refine ⟨u, ⟨act_of_none hH.1, hH.2.1, by rw [act_of_some hu hne]; rfl, fun w' hw' hs' =>
    hH.2.2.2 w' hw' (isSome_of_act hs')⟩, hc, act_of_some hu hne⟩

theorem missing_anti {x t : ℕ} {u : V} {i : Fin k} {K K' : Know V (k * x)}
    (h : ∀ v, K v ⊆ K' v) : missing G s b t u i K' ⊆ missing G s b t u i K := by
  intro j hj
  simp only [missing, mem_filter, mem_univ, true_and] at hj ⊢
  obtain ⟨v, hv, hn⟩ := hj
  exact ⟨v, hv, fun h' => hn (h v h')⟩

omit [Fintype V] [DecidableEq V] in
theorem clean_succ (L : ℕ) (ω : ℕ → V → Bool) (t : ℕ) (u : V) (ℓ : ℕ) :
    clean L ω t u (ℓ + 1) = clean L ω t u ℓ + if ω (t * L + ℓ) u = true then 1 else 0 := by
  unfold clean
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem card_missing_le {x L t : ℕ} {ω : ℕ → V → Bool} (hI : Inv G s b x L ω t) {u : V}
    {i : Fin k} (hu : e0 G s b t u = some i) :
    ∀ ℓ ≤ L, #(missing G s b t u i (Kr G s b x L ω (t * L + ℓ))) ≤ x - clean L ω t u ℓ := by
  intro ℓ hℓ
  induction ℓ with
  | zero =>
    simp only [clean, range_zero, filter_empty, card_empty, Nat.sub_zero]
    exact (card_le_univ _).trans_eq (Fintype.card_fin x)
  | succ ℓ ih =>
    have hℓ' : ℓ < L := by omega
    have ih := ih hℓ'.le
    have hsub : missing G s b t u i (Kr G s b x L ω (t * L + (ℓ + 1))) ⊆
        missing G s b t u i (Kr G s b x L ω (t * L + ℓ)) :=
      missing_anti fun v => senderTransform_run_subset_succ G s .sender _ ω _ v
    rw [clean_succ]
    split_ifs with hc
    · by_cases hne : (missing G s b t u i (Kr G s b x L ω (t * L + ℓ))).Nonempty
      · have hsub' : missing G s b t u i (Kr G s b x L ω (t * L + (ℓ + 1))) ⊆
            (missing G s b t u i (Kr G s b x L ω (t * L + ℓ))).erase
              ((missing G s b t u i (Kr G s b x L ω (t * L + ℓ))).min' hne) := by
          intro j hj
          refine mem_erase.2 ⟨?_, hsub hj⟩
          rintro rfl
          simp only [missing, mem_filter, mem_univ, true_and] at hj
          obtain ⟨v, hv, hn⟩ := hj
          exact hn (deliver hI hℓ' hu hv hne hc)
        have := card_le_card hsub'
        rw [card_erase_of_mem (min'_mem _ _)] at this
        omega
      · rw [not_nonempty_iff_eq_empty] at hne
        rw [hne, subset_empty] at hsub
        rw [hsub]; simp
    · have := card_le_card hsub
      omega

theorem inv_zero (x L : ℕ) (ω : ℕ → V → Bool) : Inv G s b x L ω 0 := by
  intro v i hi j
  simp only [K0, run, initKnow] at hi
  simp only [zero_mul, Kr, run, initKnow]
  split_ifs at hi ⊢ with h
  · exact mem_univ _
  · simp at hi

theorem inv_succ {x L t : ℕ} {ω : ℕ → V → Bool} (hI : Inv G s b x L ω t)
    (hgood : ∀ u, x ≤ clean L ω t u L) : Inv G s b x L ω (t + 1) := by
  intro v i hi j
  have hmono : Kr G s b x L ω (t * L) v ⊆ Kr G s b x L ω ((t + 1) * L) v :=
    senderTransform_run_mono G s _ _ _ (Nat.mul_le_mul_right _ (Nat.le_succ t)) v
  have hi' : i ∈ stepKnow G .receiver (K0 G s b t) (b t) (fun _ => true) v := hi
  rcases (senderTransform_mem_stepKnow G).1 hi' with h | h
  · exact hmono (hI v i h j)
  · obtain ⟨u, hH, -, hu⟩ := (heard_eq_some_iff G).1 h
    have hc := card_missing_le hI hu L le_rfl
    have hg := hgood u
    have hemp : missing G s b t u i (Kr G s b x L ω (t * L + L)) = ∅ :=
      card_eq_zero.1 (by omega)
    have hj : j ∉ missing G s b t u i (Kr G s b x L ω (t * L + L)) := by simp [hemp]
    classical
    simp only [missing, mem_filter, mem_univ, true_and, not_exists, not_and, not_not] at hj
    have hv : v ∈ rcv G s b t u := by
      simp only [rcv, mem_filter, mem_univ, true_and]; exact hH
    have := hj v hv
    rwa [show (t + 1) * L = t * L + L by ring]

theorem inv_of_good {x L R : ℕ} {ω : ℕ → V → Bool}
    (hgood : ∀ t < R, ∀ u, x ≤ clean L ω t u L) : ∀ t ≤ R, Inv G s b x L ω t := by
  intro t ht
  induction t with
  | zero => exact inv_zero x L ω
  | succ t ih => exact inv_succ (ih (by omega)) (hgood t (by omega))

/-- If every node has at least `x` clean coins in each of the `R` meta-rounds, the transformed
schedule delivers all `k * x` messages within `R * L` rounds. -/
theorem delivered_of_good {x L R : ℕ}
    (hb : Delivered (run G s .receiver b.toAdaptive (fun _ _ => true) R)) {ω : ℕ → V → Bool}
    (hgood : ∀ t < R, ∀ u, x ≤ clean L ω t u L) : Delivered (Kr G s b x L ω (R * L)) := by
  intro v
  refine eq_univ_iff_forall.2 fun m => ?_
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective m
  have hi : i ∈ K0 G s b R v := by
    have := hb v
    simp only [K0, this, mem_univ]
  exact inv_of_good hgood R le_rfl v i hi j


/-! ### The failure probability -/

omit [DecidableEq V] in
theorem round_lt {R L t ℓ : ℕ} (ht : t < R) (hℓ : ℓ < L) : t * L + ℓ < R * L :=
  calc t * L + ℓ < t * L + L := by omega
    _ = (t + 1) * L := by ring
    _ ≤ R * L := Nat.mul_le_mul_right _ ht

/-- The (round, node) coins of `u` in meta-round `t < R`. -/
def coinSet {R L t : ℕ} (ht : t < R) (u : V) : Finset (Fin (R * L) × V) :=
  (univ : Finset (Fin L)).map ⟨fun ℓ : Fin L => (⟨t * L + ℓ, round_lt ht ℓ.2⟩, u), fun a c h => by
    simp only [Prod.mk.injEq, Fin.mk.injEq, add_right_inj] at h
    exact Fin.ext h.1⟩

omit [Fintype V] [DecidableEq V] in
theorem card_coinSet {R L t : ℕ} (ht : t < R) (u : V) : #(coinSet (L := L) ht u) = L := by
  simp [coinSet]

omit [Fintype V] [DecidableEq V] in
theorem card_filter_coinSet {R L t : ℕ} (ht : t < R) (u : V) (ω : ℕ → V → Bool) :
    #((coinSet (L := L) ht u).filter fun z => ω z.1 z.2 = true) = clean L ω t u L := by
  unfold coinSet clean
  rw [filter_map, card_map, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, filter_map, card_map]
  rfl

variable (G s b) in
/-- **Round-level form of Lemma 25.** If the faultless static schedule `b` delivers `k` messages
within `R` rounds, then `k * x` messages can be delivered in the sender faults model within `R * L`
rounds, provided the Chernoff bound for "some node has fewer than `x` clean coins in some
meta-round of length `L`" is at most `1 / (k x)`. -/
theorem routingRounds_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℕ}
    (hb : Delivered (run G s .receiver b.toAdaptive (fun _ _ => true) R)) {x L : ℕ} {l : ℝ}
    (hl0 : 0 < l) (hl1 : l ≤ 1)
    (h : (R * Fintype.card V : ℝ) * ((l ^ (x - 1))⁻¹ * (1 - (1 - l) * (1 - p)) ^ L) ≤
      1 / ((k * x : ℕ) : ℝ)) :
    routingRounds G s .sender p (k * x) ≤ ((R * L : ℕ) : ℕ∞) := by
  classical
  refine iInf₂_le (R * L) ⟨sch G s b x L, ?_⟩
  set B : ℝ := (l ^ (x - 1))⁻¹ * (1 - (1 - l) * (1 - p)) ^ L
  let Bad : (ℕ → V → Bool) → Prop := fun ω =>
    ∃ z ∈ range R ×ˢ (univ : Finset V), clean L ω z.1 z.2 L ≤ x - 1
  have hBad : prob p (R * L) Bad ≤ R * Fintype.card V * B := by
    refine (prob_exists_le hp0 hp1 _ _).trans ?_
    calc ∑ z ∈ range R ×ˢ (univ : Finset V), prob p (R * L) (fun ω => clean L ω z.1 z.2 L ≤ x - 1)
        ≤ ∑ _z ∈ range R ×ˢ (univ : Finset V), B := by
          refine sum_le_sum fun z hz => ?_
          have ht : z.1 < R := mem_range.1 (mem_product.1 hz).1
          rw [prob_congr (F := fun ω => #((coinSet (L := L) ht z.2).filter
            fun y => ω y.1 y.2 = true) ≤ x - 1) fun ω => by rw [card_filter_coinSet]]
          have := prob_card_le_le hp0 hp1 (coinSet (L := L) ht z.2) (x - 1) hl0 hl1
          rwa [card_coinSet] at this
      _ = R * Fintype.card V * B := by
          rw [sum_const, card_product, card_range, card_univ, nsmul_eq_mul]; push_cast; ring
  have hgood : prob p (R * L) (fun ω => ¬ Bad ω) ≤
      prob p (R * L) (fun ω => Delivered (run G s .sender (sch G s b x L) ω (R * L))) := by
    refine prob_mono hp0 hp1 fun ω hω => delivered_of_good hb fun t ht u => ?_
    by_contra hc
    exact hω ⟨(t, u), mem_product.2 ⟨mem_range.2 ht, mem_univ u⟩, by simp only; omega⟩
  rw [prob_not] at hgood
  show 1 - 1 / ((k * x : ℕ) : ℝ) ≤ _
  linarith

end SenderTransform

end Podc.NoisyRadioBroadcast
