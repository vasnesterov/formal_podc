import Papers.PODC2026.PLSTradeoff.RandomCarving
import Papers.PODC2026.PLSTradeoff.CertifyTS

/-!
# Certifying a TS partition with `O(1)` bits on connected graphs (Section 5.2)

Given a scheme that shares a string of `rS` bits with all nodes of a connected graph
(`ShareScheme`, Lemma 5.6) and the family `F` of radius assignments of Lemma 5.5, the honest
prover shares the index `i_G` of an assignment that is good for `G`, marks the taken centres
(`InT`) and the separating set (`InX`). Every node then runs `FindMyCluster` (`fmc`) in its
localized view, reconstructs the clusters near it, and checks for its own cluster the weak
diameter, the cost ratio `1/t` and two separation at itself.

`tsCertGeneral` is the resulting `(40K + 32)`-PLS certifying and outputting a
`(16K + 12, 1/t)`-TS partition on connected graphs, with `K = t⌈log₂ n⌉`, of cost
`2 cS + 7` where `cS` is the cost of the sharing scheme.

Deviation: the reconstructed cluster of `u` only contains nodes within distance `2ρ` of `u`
(`ρ` the largest radius); this makes the verifier local without changing the clusters.
-/

namespace PLSTradeoff

open SimpleGraph Finset Classical

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Lemma 5.6 as an interface: a scheme sharing a string of length `r` with all nodes of a
connected graph, with radius `ρ` and cost `c`. -/
structure ShareScheme (V : Type*) (r c ρ : ℕ) where
  prov : SimpleGraph V → List Bool → V → Label
  ver : SimpleGraph V → (V → Label) → V → Option (List Bool)
  isLocal : IsLocal (ι := Unit) ρ (fun G _ ℓ v => ver G ℓ v)
  complete : ∀ G : SimpleGraph V, G.Connected → ∀ S : List Bool, S.length = r → ∀ v,
    ver G (prov G S) v = some S
  sound : ∀ G : SimpleGraph V, G.Connected → ∀ ℓ : V → Label, (∀ v, (ver G ℓ v).isSome) →
    ∃ S', ∀ v, ver G ℓ v = some S'
  cost : ∀ G S v, S.length = r → (prov G S v).length ≤ c

/-! ### FindMyCluster -/

/-- The least candidate, if any. -/
noncomputable def fmcOf (C : V → Prop) : Option V :=
  if h : ∃ w, C w then some ((univ.filter C).min' (by obtain ⟨w, hw⟩ := h; exact ⟨w, by simpa⟩))
  else none

lemma fmcOf_eq_some_iff {C : V → Prop} {c : V} :
    fmcOf C = some c ↔ C c ∧ ∀ w, C w → c ≤ w := by
  unfold fmcOf
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      have := (univ.filter C).min'_mem (by obtain ⟨w, hw⟩ := h; exact ⟨w, by simpa⟩)
      exact ⟨by simpa using this, fun w hw => min'_le _ _ (by simpa using hw)⟩
    · rintro ⟨hc, hmin⟩
      exact le_antisymm (min'_le _ _ (by simpa using hc))
        (le_min' _ _ _ (fun w hw => hmin w (by simpa using hw)))
  · simp only [false_iff, not_and, not_forall]
    exact fun hc => absurd ⟨c, hc⟩ h

lemma fmcOf_eq_none_iff {C : V → Prop} : fmcOf C = none ↔ ∀ w, ¬ C w := by
  unfold fmcOf
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]; exact h
  · push Not at h; simpa using h

lemma fmcOf_congr {C C' : V → Prop} (h : ∀ w, C w ↔ C' w) : fmcOf C = fmcOf C' := by
  have : C = C' := funext fun w => propext (h w)
  rw [this]

/-- `FindMyCluster(u)`: the least marked `w` whose ball (radius `rad K (Rn w)`) contains `u`. -/
noncomputable def fmc (H : SimpleGraph V) (K : ℕ) (T : V → Prop) (Rn : V → ℕ) (u : V) :
    Option V :=
  fmcOf (fun w => T w ∧ H.edist w u ≤ rad K (Rn w))

/-- The cluster of `u` reconstructed in `H`: nodes within `2ρ` with the same `FindMyCluster`. -/
def recFmc (H : SimpleGraph V) (K ρ : ℕ) (T : V → Prop) (Rn : V → ℕ) (u : V) : Set V :=
  {y | H.edist u y ≤ (2 * ρ : ℕ) ∧ fmc H K T Rn y = fmc H K T Rn u}

/-! ### Labels -/

/-- Splitting a label `(ShareLabel, InT, InX)`. -/
def parse3 (w : Label) : Label × Label × Label :=
  match decList w with
  | [a, b, c] => (a, b, c)
  | _ => ([], [], [])

@[simp] lemma parse3_encList (a b c : Label) : parse3 (encList [a, b, c]) = (a, b, c) := by
  simp [parse3]

def shPart (ℓ : V → Label) : V → Label := fun u => (parse3 (ℓ u)).1
def inT (ℓ : V → Label) (u : V) : Prop := (parse3 (ℓ u)).2.1 = [true]
def inXs (ℓ : V → Label) : Set V := {u | (parse3 (ℓ u)).2.2 = [true]}

/-- Decoding the shared index. -/
noncomputable def decIdx (m w : ℕ) (hm : 0 < m) (S : List Bool) : Fin m :=
  if h : ∃ i : Fin m, bitsW w i = S then Classical.choose h else ⟨0, hm⟩

lemma decIdx_bitsW {m w : ℕ} (hm : 0 < m) (hw : m ≤ 2 ^ w) (i : Fin m) :
    decIdx m w hm (bitsW w i) = i := by
  unfold decIdx
  have h : ∃ j : Fin m, bitsW w j = bitsW w i := ⟨i, rfl⟩
  rw [dite_eq_left h]
  exact Fin.ext (bitsW_inj ((Classical.choose h).isLt.trans_le hw) (i.isLt.trans_le hw)
    (Classical.choose_spec h))

/-! ### The scheme -/

section Scheme

variable (t K rS cS ρS : ℕ)

/-- The largest radius `ρ = rad K (3K+2) = 8K + 6`. -/
def rhoMax (K : ℕ) : ℕ := rad K (3 * K + 2)

/-- The radius of the scheme. -/
def genR (K : ℕ) : ℕ := 5 * rhoMax K + 2

/-- The checks of node `v` in its view `(H, ℓ)` with radius indices `Rn`. -/
def GenCheck (H : SimpleGraph V) (ℓ : V → Label) (Rn : V → ℕ) (v : V) : Prop :=
  fmc H K (inT ℓ) Rn v ≠ none ∧
  (∀ a ∈ recFmc H K (rhoMax K) (inT ℓ) Rn v, ∀ b ∈ recFmc H K (rhoMax K) (inT ℓ) Rn v,
    H.edist a b ≤ (2 * rhoMax K : ℕ)) ∧
  (((recFmc H K (rhoMax K) (inT ℓ) Rn v ∩ inXs ℓ).ncard : ℝ) ≤
    (1 / t : ℝ) * (recFmc H K (rhoMax K) (inT ℓ) Rn v).ncard) ∧
  (∀ w, w ∉ recFmc H K (rhoMax K) (inT ℓ) Rn v → v ∉ inXs ℓ → w ∉ inXs ℓ →
    (2 : ℕ∞) < H.edist v w)

variable {t K rS cS ρS}

/-- The verifier. -/
noncomputable def genVer (SS : ShareScheme V rS cS ρS) {m : ℕ} (hm : 0 < m)
    (F : Fin m → V → Fin (3 * K + 3)) (G : SimpleGraph V) (ℓ : V → Label) (v : V) :
    Option (TSOut V) :=
  match SS.ver G (shPart ℓ) v with
  | none => none
  | some S =>
    if GenCheck t K (loc G v (genR K)) (mask G v (genR K) ℓ)
        (fun u => (F (decIdx m rS hm S) u : ℕ)) v then
      some (recFmc (loc G v (genR K)) K (rhoMax K) (inT (mask G v (genR K) ℓ))
          (fun u => (F (decIdx m rS hm S) u : ℕ)),
        inXs (mask G v (genR K) ℓ))
    else none

lemma genVer_isLocal (SS : ShareScheme V rS cS ρS) {m : ℕ} (hm : 0 < m)
    (F : Fin m → V → Fin (3 * K + 3)) (hρ : ρS ≤ genR K) :
    IsLocal (ι := Unit) (genR K) (fun G _ ℓ v => genVer (t := t) SS hm F G ℓ v) := by
  intro G I ℓ G' I' ℓ' v h
  have hsh : SS.ver G (shPart ℓ) v = SS.ver G' (shPart ℓ') v :=
    SS.isLocal G (fun _ => ()) (shPart ℓ) G' (fun _ => ()) (shPart ℓ') v
      ⟨h.1.mono_radius hρ, fun u hu => ⟨rfl, by
        simp only [shPart, (h.2 u (hu.trans (by exact_mod_cast hρ))).2]⟩⟩
  simp only [genVer]
  rw [hsh, viewEq_loc_eq h, (viewEq_mask_eq h).2]

/-! ### Transfer lemmas -/

variable {G : SimpleGraph V}

lemma rad_le_rhoMax {x : ℕ} (hx : x < 3 * K + 3) : rad K x ≤ rhoMax K := by
  simp only [rhoMax, rad]; omega

/-- `fmc` is computed exactly in the localized view near `v`. -/
lemma fmc_loc {ℓ : V → Label} {Rn : V → ℕ} (hRn : ∀ w, Rn w < 3 * K + 3) {v y : V} {a : ℕ}
    (hy : G.edist v y ≤ a) (ha : a + rhoMax K ≤ genR K) :
    fmc (loc G v (genR K)) K (inT (mask G v (genR K) ℓ)) Rn y = fmc G K (inT ℓ) Rn y := by
  apply fmcOf_congr
  intro w
  have key : ∀ r ≤ rhoMax K, ((loc G v (genR K)).edist w y ≤ r ↔ G.edist w y ≤ r) := by
    intro r hr
    rw [SimpleGraph.edist_comm, SimpleGraph.edist_comm (u := w)]
    exact loc_edist_le_iff hy ha hr
  rw [key _ (rad_le_rhoMax (hRn w))]
  constructor
  · rintro ⟨hT, hd⟩
    refine ⟨?_, hd⟩
    have hvw : G.edist v w ≤ genR K := by
      have := edist_le_add hy (by rw [SimpleGraph.edist_comm]; exact hd)
      exact this.trans (by exact_mod_cast (by have := rad_le_rhoMax (hRn w); omega))
    simpa [inT, mask_of_le hvw] using hT
  · rintro ⟨hT, hd⟩
    refine ⟨?_, hd⟩
    have hvw : G.edist v w ≤ genR K := by
      have := edist_le_add hy (by rw [SimpleGraph.edist_comm]; exact hd)
      exact this.trans (by exact_mod_cast (by have := rad_le_rhoMax (hRn w); omega))
    simpa [inT, mask_of_le hvw] using hT

omit [Fintype V] [LinearOrder V] in
lemma inXs_mask {ℓ : V → Label} {v w : V} (hw : G.edist v w ≤ genR K) :
    w ∈ inXs (mask G v (genR K) ℓ) ↔ w ∈ inXs ℓ := by
  simp [inXs, mask_of_le hw]

/-- Two nodes with the same (non-`none`) `FindMyCluster` are within `2ρ`. -/
lemma edist_of_fmc_eq {T : V → Prop} {Rn : V → ℕ} (hRn : ∀ w, Rn w < 3 * K + 3) {u y c : V}
    (hu : fmc G K T Rn u = some c) (hy : fmc G K T Rn y = some c) :
    G.edist u y ≤ (2 * rhoMax K : ℕ) := by
  have h1 := ((fmcOf_eq_some_iff.1 hu).1).2
  have h2 := ((fmcOf_eq_some_iff.1 hy).1).2
  rw [SimpleGraph.edist_comm] at h1
  have := edist_le_add h1 h2
  exact this.trans (by exact_mod_cast (by have := rad_le_rhoMax (K := K) (hRn c); omega))

/-- The reconstructed cluster near `v` is the true one. -/
lemma recFmc_loc {ℓ : V → Label} {Rn : V → ℕ} (hRn : ∀ w, Rn w < 3 * K + 3) {v u : V} {a : ℕ}
    (hu : G.edist v u ≤ a) (ha : a + 2 * rhoMax K + rhoMax K ≤ genR K) :
    recFmc (loc G v (genR K)) K (rhoMax K) (inT (mask G v (genR K) ℓ)) Rn u =
      recFmc G K (rhoMax K) (inT ℓ) Rn u := by
  ext y
  simp only [recFmc, Set.mem_ofPred_eq]
  rw [loc_edist_le_iff hu (by omega : a + 2 * rhoMax K ≤ genR K) le_rfl,
    fmc_loc hRn hu (by omega : a + rhoMax K ≤ genR K)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [fmc_loc hRn (edist_le_add hu h1) (by omega)] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [fmc_loc hRn (edist_le_add hu h1) (by omega)]

end Scheme

/-! ### Lemma 5.6 + Lemmas 5.7–5.12: the `O(1)` TS certification -/

section Main

variable {t K rS cS ρS : ℕ}

lemma genVer_eq_some (SS : ShareScheme V rS cS ρS) {m : ℕ} (hm : 0 < m)
    (F : Fin m → V → Fin (3 * K + 3)) {G : SimpleGraph V} {ℓ : V → Label} {v : V}
    {S : List Bool} (hS : SS.ver G (shPart ℓ) v = some S)
    (hc : GenCheck t K (loc G v (genR K)) (mask G v (genR K) ℓ)
      (fun u => (F (decIdx m rS hm S) u : ℕ)) v) :
    genVer (t := t) SS hm F G ℓ v =
      some (recFmc (loc G v (genR K)) K (rhoMax K) (inT (mask G v (genR K) ℓ))
          (fun u => (F (decIdx m rS hm S) u : ℕ)), inXs (mask G v (genR K) ℓ)) := by
  simp only [genVer, hS]
  exact ite_eq_left hc

lemma genVer_isSome (SS : ShareScheme V rS cS ρS) {m : ℕ} (hm : 0 < m)
    (F : Fin m → V → Fin (3 * K + 3)) {G : SimpleGraph V} {ℓ : V → Label} {v : V}
    (h : (genVer (t := t) SS hm F G ℓ v).isSome) :
    ∃ S, SS.ver G (shPart ℓ) v = some S ∧ GenCheck t K (loc G v (genR K))
      (mask G v (genR K) ℓ) (fun u => (F (decIdx m rS hm S) u : ℕ)) v := by
  cases hS : SS.ver G (shPart ℓ) v with
  | none => simp [genVer, hS] at h
  | some S =>
    refine ⟨S, rfl, ?_⟩
    by_contra hc
    simp only [genVer, hS] at h
    rw [ite_eq_right hc] at h
    exact absurd h (by simp)

/-- The honest labels for a good radius assignment `i`. -/
noncomputable def genLabel (SS : ShareScheme V rS cS ρS) {m : ℕ}
    (F : Fin m → V → Fin (3 * K + 3)) (G : SimpleGraph V) (i : Fin m) (v : V) : Label :=
  encList [SS.prov G (bitsW rS i) v,
    [decide (taken G t K (fun u => (F i u : ℕ)) v)],
    [decide (∃ u, cidx G t K (fun u => (F i u : ℕ)) v < cidx G t K (fun u => (F i u : ℕ)) u ∧
      G.edist v u ≤ 2)]]

/-- **Section 5.2** of [Filtser–Fischer, PODC 2026] (Lemmas 5.7–5.12, with Lemma 5.5): given a
string-sharing scheme (Lemma 5.6) for strings of `rS ≥ log₂(n²+1)` bits with cost `cS`, there is
a `(40K+32)`-PLS that certifies and outputs a `(16K+12, 1/t)`-TS partition on every family of
connected graphs, with cost `2 cS + 7` (`K = t⌈log₂ n⌉`). -/
theorem tsCertGeneral (ht : 1 ≤ t) (hK : K = t * Nat.clog 2 (Fintype.card V))
    (𝒢 : Set (SimpleGraph V)) (h𝒢 : ∀ G ∈ 𝒢, G.Connected)
    (hrS : Fintype.card V * Fintype.card V + 1 ≤ 2 ^ rS)
    (SS : ShareScheme V rS cS ρS) (hρ : ρS ≤ genR K) :
    ∃ S : TSCert 𝒢 (2 * rhoMax K) (1 / t) (genR K), S.CostLE (2 * cS + 7) := by
  set n := Fintype.card V
  set m := n * n + 1
  have hm : 0 < m := by omega
  obtain ⟨F, hF⟩ := exists_good_family (V := V) ht hK
  have hRn : ∀ (i : Fin m) w, ((fun u => (F i u : ℕ)) w) < 3 * K + 3 := fun i w => (F i w).isLt
  let prov : SimpleGraph V → V → Label := fun G =>
    if h : G.Connected then genLabel (t := t) SS F G (Classical.choose (hF G h)) else fun _ => []
  have hρ5 : ∀ {a b : ℕ}, a ≤ b → b ≤ genR K → a ≤ genR K := fun h1 h2 => h1.trans h2
  refine ⟨{ prov := prov
            ver := genVer (t := t) SS hm F
            isLocal := genVer_isLocal SS hm F hρ
            complete := fun G hG _ v => ?_
            sound := fun G hG ℓ hall => ?_ }, fun G hG v => ?_⟩
  · ------------------------------------------------ completeness
    have hc := h𝒢 G hG
    set i := Classical.choose (hF G hc)
    have hgood : AllClustered G t K (fun u => (F i u : ℕ)) := Classical.choose_spec (hF G hc)
    set Rn : V → ℕ := fun u => (F i u : ℕ)
    set ℓ := prov G
    have hℓ : ℓ = genLabel (t := t) SS F G i := by simp only [ℓ, prov, dite_eq_left hc]; rfl
    have hsh : shPart ℓ = SS.prov G (bitsW rS i) := by
      funext u; simp [hℓ, shPart, genLabel]
    have hSv : SS.ver G (shPart ℓ) v = some (bitsW rS i) := by
      rw [hsh]; exact SS.complete G hc _ (length_bitsW _ _) v
    have hdec : decIdx m rS hm (bitsW rS i) = i := decIdx_bitsW hm hrS i
    let ts := TSPartition.ofDegenerate (isDegenerate_of_allClustered ht hgood)
      (isWeaklyBounded_of_allClustered (Mx := 3 * K + 2) (fun w => by
        simp only [Rn]; have := (F i w).isLt; omega) hgood)
    have hT : ∀ w, inT ℓ w ↔ taken G t K Rn w := by
      intro w; simp [inT, hℓ, genLabel, Rn]
    have hX : ∀ w, w ∈ inXs ℓ ↔ w ∈ ts.X := by
      intro w; simp [inXs, hℓ, genLabel, ts, TSPartition.ofDegenerate, Rn]
    have hfmc : ∀ u, fmc G K (inT ℓ) Rn u = some (cen G t K Rn u) := by
      intro u
      rw [fmc, fmcOf_congr (C' := fun w => taken G t K Rn w ∧ G.edist w u ≤ rad K (Rn w))
        (fun w => by rw [hT])]
      obtain ⟨h1, h2, h3⟩ := cen_spec (hgood u)
      exact fmcOf_eq_some_iff.2 ⟨⟨h1, h2⟩, fun w hw => h3 w hw.1 hw.2⟩
    have hcl : ∀ u, ts.cl u = {y | cen G t K Rn y = cen G t K Rn u} := by
      intro u; ext y
      simp only [ts, TSPartition.ofDegenerate, Set.mem_ofPred_eq]
      exact cidx_eq_iff
    have hrec : ∀ u, recFmc G K (rhoMax K) (inT ℓ) Rn u = ts.cl u := by
      intro u; ext y
      rw [hcl]
      simp only [recFmc, Set.mem_ofPred_eq, hfmc, Option.some.injEq]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      exact edist_of_fmc_eq (fun w => hRn i w) (hfmc u) (h ▸ hfmc y)
    have hv0 : G.edist v v ≤ (0 : ℕ) := by simp
    have hrecv : recFmc (loc G v (genR K)) K (rhoMax K) (inT (mask G v (genR K) ℓ)) Rn v =
        ts.cl v := by
      rw [recFmc_loc (fun w => hRn i w) hv0 (by unfold genR; omega), hrec]
    have hvC : ∀ {y}, y ∈ ts.cl v → G.edist v y ≤ (2 * rhoMax K : ℕ) :=
      fun hy => ts.diam v v (ts.mem_cl v) _ hy
    have hcheck : GenCheck t K (loc G v (genR K)) (mask G v (genR K) ℓ) Rn v := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [fmc_loc (fun w => hRn i w) hv0 (by unfold genR; omega), hfmc]; simp
      · intro a ha b hb
        rw [hrecv] at ha hb
        exact (loc_edist_le_iff (hvC ha) (by unfold genR; omega : 2 * rhoMax K + 2 * rhoMax K ≤
          genR K) le_rfl).2 (ts.diam v a ha b hb)
      · rw [hrecv]
        have : ts.cl v ∩ inXs (mask G v (genR K) ℓ) = ts.cl v ∩ ts.X := by
          ext y
          simp only [Set.mem_inter_iff]
          refine and_congr_right fun hy => ?_
          rw [inXs_mask ((hvC hy).trans (by unfold genR; exact_mod_cast (by omega))), hX]
        rw [this]; exact ts.ratio v
      · intro w hw hvX hwX
        rw [hrecv] at hw
        have hvX' : v ∉ ts.X := by
          rw [← hX, ← inXs_mask (K := K) (ℓ := ℓ) (v := v) (w := v) (by simp)]; exact hvX
        by_cases hvw : G.edist v w ≤ genR K
        · have hwX' : w ∉ ts.X := by rw [← hX, ← inXs_mask hvw]; exact hwX
          have hne : ts.cl v ≠ ts.cl w := fun h => hw (h ▸ ts.mem_cl w)
          exact (ts.sep v w hvX' hwX' hne).trans_le edist_le_edist_loc
        · push Not at hvw
          exact lt_of_lt_of_le (lt_of_le_of_lt (by exact_mod_cast (by unfold genR; omega :
            2 ≤ genR K)) hvw) edist_le_edist_loc
    have := genVer_eq_some (t := t) SS hm F hSv (by rw [hdec]; exact hcheck)
    rw [this]; rfl
  · ------------------------------------------------ soundness
    have hc := h𝒢 G hG
    have hsh : ∀ v, (SS.ver G (shPart ℓ) v).isSome := by
      intro v
      obtain ⟨S, hS, -⟩ := genVer_isSome (t := t) SS hm F (hall v)
      simp [hS]
    obtain ⟨S', hS'⟩ := SS.sound G hc _ hsh
    set Rn : V → ℕ := fun u => (F (decIdx m rS hm S') u : ℕ)
    have hcheck : ∀ v, GenCheck t K (loc G v (genR K)) (mask G v (genR K) ℓ) Rn v := by
      intro v
      obtain ⟨S, hS, hc⟩ := genVer_isSome (t := t) SS hm F (hall v)
      rw [hS'] at hS; cases hS; exact hc
    have hRn' : ∀ w, Rn w < 3 * K + 3 := fun w => hRn _ w
    set fG := fmc G K (inT ℓ) Rn
    have hv0 : ∀ v : V, G.edist v v ≤ (0 : ℕ) := by simp
    have hfne : ∀ v, fG v ≠ none := by
      intro v
      have := (hcheck v).1
      rwa [fmc_loc hRn' (hv0 v) (by unfold genR; omega)] at this
    have hrecG : ∀ u, recFmc G K (rhoMax K) (inT ℓ) Rn u = {y | fG y = fG u} := by
      intro u; ext y
      simp only [recFmc, Set.mem_ofPred_eq]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (hfne u)
      exact edist_of_fmc_eq hRn' hc (h.trans hc)
    have hrecv : ∀ v, recFmc (loc G v (genR K)) K (rhoMax K) (inT (mask G v (genR K) ℓ)) Rn v =
        {y | fG y = fG v} := by
      intro v
      rw [recFmc_loc hRn' (hv0 v) (by unfold genR; omega), hrecG]
    have hclose : ∀ {v y}, fG y = fG v → G.edist v y ≤ (2 * rhoMax K : ℕ) := by
      intro v y h
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (hfne v)
      exact edist_of_fmc_eq hRn' hc (h.trans hc)
    let ts : TSPartition G (2 * rhoMax K) (1 / t) :=
      { cl := fun u => {y | fG y = fG u}
        mem_cl := fun u => rfl
        cl_eq := fun u v h => by ext y; simp only [Set.mem_ofPred_eq] at h ⊢; rw [h]
        X := inXs ℓ
        twoSep := twoSep_of_distSep (by
          intro u w hu hw hne
          by_contra hle
          push Not at hle
          have hw' : w ∉ recFmc (loc G u (genR K)) K (rhoMax K) (inT (mask G u (genR K) ℓ))
              Rn u := by
            rw [hrecv]; intro h; apply hne; ext y; simp only [Set.mem_ofPred_eq] at h ⊢; rw [h]
          have := (hcheck u).2.2.2 w hw' (by rw [inXs_mask (by simp)]; exact hu)
            (by rw [inXs_mask (hle.trans (by unfold genR; exact_mod_cast (by omega)))]; exact hw)
          rw [← not_le] at this
          exact this ((loc_edist_le_iff (hv0 u) (by unfold genR; omega : 0 + 2 ≤ genR K)
            le_rfl).2 hle))
        diam := by
          intro v a ha b hb
          have := (hcheck v).2.1 a (by rw [hrecv]; exact ha) b (by rw [hrecv]; exact hb)
          exact edist_le_edist_loc.trans this
        ratio := by
          intro v
          have h := (hcheck v).2.2.1
          rw [hrecv] at h
          have : {y | fG y = fG v} ∩ inXs (mask G v (genR K) ℓ) = {y | fG y = fG v} ∩ inXs ℓ := by
            ext y
            simp only [Set.mem_inter_iff]
            refine and_congr_right fun hy => ?_
            exact inXs_mask ((hclose hy).trans (by unfold genR; exact_mod_cast (by omega)))
          rwa [this] at h }
    refine ⟨ts, fun v o ho => ?_⟩
    have ho' := genVer_eq_some (t := t) SS hm F (hS' v) (hcheck v)
    rw [ho', Option.some.injEq] at ho
    subst ho
    intro u ⟨w, hw, hwu⟩
    have hvw : G.edist v w ≤ (2 * rhoMax K : ℕ) := hclose hw
    have hvu : G.edist v u ≤ (2 * rhoMax K + 2 : ℕ) := edist_le_add hvw hwu
    refine ⟨?_, fun y hy => ?_⟩
    · show recFmc (loc G v (genR K)) K (rhoMax K) (inT (mask G v (genR K) ℓ)) Rn u = _
      rw [recFmc_loc hRn' hvu (by unfold genR; omega), hrecG]
    · have huy : G.edist u y ≤ (2 * rhoMax K : ℕ) := by
        rw [SimpleGraph.edist_comm]; exact hclose (show fG u = fG y from hy.symm)
      exact inXs_mask ((edist_le_add hvu huy).trans (by unfold genR; exact_mod_cast (by omega)))
  · ------------------------------------------------ cost
    show (prov G v).length ≤ _
    by_cases hc : G.Connected
    · simp only [prov, dite_eq_left hc, genLabel]
      rw [length_encList]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil]
      have := SS.cost G (bitsW rS ((Classical.choose (hF G hc) : Fin m) : ℕ)) v (length_bitsW _ _)
      omega
    · simp only [prov, dite_eq_right hc]
      simp

end Main

end PLSTradeoff
