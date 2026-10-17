import Papers.PODC2022.AsyncSpeedup.LowerBounds

/-!
# Equations (2) and (3): the converse inclusions of Claims 2–4 and tightness

* `eq3` — the one-round map of Equation (3): a process that sees the values `{y_j : j ∈ J}` outputs
  `min (max_J y, min_J y + ε)`.
* `claim3` / `claim4` — **Claims 3 and 4** (equalities): the closure of the liberal
  `ε`-agreement w.r.t. IIS (resp. IIS + test&set) is the liberal `2ε`-agreement (`n` arbitrary,
  `ε ≥ 0`).
* `aa_solvable_many` — tightness (Remark after Corollary 3): `ε`-approximate agreement is solvable
  in IIS in `t` rounds whenever `1 ≤ 2^t ε` (Equation (3) used as a uniform one-round step).
* `eq2` — the one-round map of Equation (2) for two processes, `claim2` — **Claim 2** (equality)
  for two processes, `aa_solvable_two` — tightness for two processes (`1 ≤ 3^t ε` suffices).
-/

set_option linter.unusedSectionVars false

namespace AsyncSpeedup

open Cslib.Iterated

variable {P : Type} [DecidableEq P]

/-! ### Equation (3) -/

/-- Equation (3): `min (max_S v, min_S v + e)` (and `0` for an empty `S`). -/
def eq3 (e : ℤ) (S : Finset P) (v : P → ℤ) : ℤ :=
  if h : S.Nonempty then min (S.sup' h v) (S.inf' h v + e) else 0

lemma eq3_congr {e : ℤ} {S : Finset P} {v w : P → ℤ} (h : ∀ l ∈ S, v l = w l) :
    eq3 e S v = eq3 e S w := by
  unfold eq3
  split_ifs with hS
  · rw [Finset.sup'_congr hS rfl h, Finset.inf'_congr hS rfl h]
  · rfl

lemma inf'_le_sup' {S : Finset P} (hS : S.Nonempty) (v : P → ℤ) : S.inf' hS v ≤ S.sup' hS v := by
  obtain ⟨a, ha⟩ := hS
  exact (Finset.inf'_le v ha).trans (Finset.le_sup' v ha)

lemma eq3_bounds {e : ℤ} (he : 0 ≤ e) {S : Finset P} (hS : S.Nonempty) (v : P → ℤ) :
    S.inf' hS v ≤ eq3 e S v ∧ eq3 e S v ≤ S.sup' hS v := by
  have := inf'_le_sup' hS v
  simp only [eq3, hS, ↓reduceDIte]
  constructor <;> omega

lemma eq3_singleton {e : ℤ} (he : 0 ≤ e) (i : P) (v : P → ℤ) : eq3 e {i} v = v i := by
  simp only [eq3, Finset.singleton_nonempty, ↓reduceDIte, Finset.sup'_singleton,
    Finset.inf'_singleton]
  omega

/-- The key estimate of the proof of Claim 3: nested views of a `2e`-close configuration yield
`e`-close outputs. -/
lemma eq3_close {e : ℤ} {S S' : Finset P} (hS' : S'.Nonempty) (hsub : S' ⊆ S) {v : P → ℤ}
    (hv : ∀ a ∈ S, ∀ b ∈ S, v a - v b ≤ 2 * e) : abs (eq3 e S v - eq3 e S' v) ≤ e := by
  have hS : S.Nonempty := hS'.mono hsub
  obtain ⟨a, ha, hav⟩ := Finset.exists_mem_eq_sup' hS v
  obtain ⟨b, hb, hbv⟩ := Finset.exists_mem_eq_inf' hS v
  have h1 := Finset.sup'_mono v hsub hS'
  have h2 := Finset.inf'_mono v hsub hS'
  have h3 := inf'_le_sup' hS' v
  have h4 := hv a ha b hb
  simp only [eq3, hS, hS', ↓reduceDIte]
  rw [← hav, ← hbv] at h4
  rw [abs_le]; constructor <;> omega

/-- Views of an immediate-snapshot round of a `2e`-close configuration give `e`-close outputs. -/
lemma eq3_round {e : ℤ} {I J : Finset P} {S : P → Finset P} (hIS : IsIS J S) (hJI : J ⊆ I)
    {v : P → ℤ} (hv : ∀ a ∈ I, ∀ b ∈ I, v a - v b ≤ 2 * e) {i j : P} (hi : i ∈ J) (hj : j ∈ J) :
    abs (eq3 e (S i) v - eq3 e (S j) v) ≤ e := by
  have hv' : ∀ (T : Finset P), T ⊆ I → ∀ a ∈ T, ∀ b ∈ T, v a - v b ≤ 2 * e :=
    fun T hT a ha b hb => hv a (hT ha) b (hT hb)
  rcases hIS.2.1 i hi j hj with h | h
  · exact eq3_close ⟨j, (hIS.1 j hj).1⟩ (hIS.2.2 i hi j hj h)
      (hv' _ ((hIS.1 i hi).2.trans hJI))
  · rw [abs_sub_comm]
    exact eq3_close ⟨i, (hIS.1 i hi).1⟩ (hIS.2.2 j hj i hi h)
      (hv' _ ((hIS.1 j hj).2.trans hJI))

/-- The output of `eq3` on a view stays in the range of the inputs. -/
lemma eq3_inRange {e : ℤ} (he : 0 ≤ e) {I : Finset P} {x : P → ℤ} {T : Finset P}
    (hT : T.Nonempty) (hTI : T ⊆ I) {v : P → ℤ} (hv : ∀ l ∈ I, InRange I x (v l)) :
    InRange I x (eq3 e T v) := by
  obtain ⟨a, ha, hav⟩ := Finset.exists_mem_eq_sup' hT v
  obtain ⟨b, hb, hbv⟩ := Finset.exists_mem_eq_inf' hT v
  have := eq3_bounds he hT v
  rw [hav, hbv] at this
  exact InRange.of_between (hv b (hTI hb)) (hv a (hTI ha)) this.1 this.2

/-- The set of processes seen in a view. -/
def seen [Fintype P] {α : Type} (z : P → Option α) : Finset P :=
  Finset.univ.filter fun l => (z l).isSome

/-- Equation (3) computed from a one-round view (values read from the view). -/
def eq3Dec [Fintype P] {B : Type} (e : ℤ) (w : B × (P → Option ℤ)) : ℤ :=
  eq3 e (seen w.2) (fun l => (w.2 l).getD 0)

lemma eq3Dec_step [Fintype P] {B : Type} (e : ℤ) (d : P → ℤ) (p : Pattern P B) (i : P) :
    eq3Dec e (p.out i, fun j => if j ∈ p.sees i then some (d j) else none) =
      eq3 e (p.sees i) d := by
  have hseen : seen (fun j => if j ∈ p.sees i then some (d j) else none) = p.sees i := by
    ext l; by_cases hl : l ∈ p.sees i <;> simp [seen, hl]
  simp only [eq3Dec, hseen]
  exact eq3_congr fun l hl => by simp [hl]

/-- The one-round algorithm of Equation (3) (box inputs `a₀`, box outputs ignored). -/
def eq3Alg [Fintype P] {A B : Type} (a₀ : P → A) (e : ℤ) : Alg P ℤ A B ℤ 1 where
  inp _ i _ := a₀ i
  dec _ w := eq3Dec e w

/-- Equation (3) solves the local task `Π_{τ,σ}` of the liberal `ε`-agreement whenever all values
of `τ` are in range and pairwise `2ε`-close, in any model whose rounds are immediate snapshots. -/
theorem eq3Alg_solves [Fintype P] {A B : Type} {M : Model P A B}
    (hIS : ∀ J a, ∀ p ∈ M.Pat J a, IsIS J p.sees) (a₀ : P → A) {S : Finset P} {m e : ℤ}
    (he : 0 ≤ e) {I : Finset P} {x τ : P → ℤ} (hrange : ∀ l ∈ I, InRange I x (τ l))
    (hclose : ∀ a ∈ I, ∀ b ∈ I, τ a - τ b ≤ 2 * e) :
    Solves M (localTask (libAA S m e) I x τ) (eq3Alg a₀ e) := by
  rintro J τ' ⟨⟨j₀, hj₀⟩, hJI, hτ'⟩ W hW
  change τ' = τ at hτ'
  change j₀ ∈ J at hj₀
  change J ⊆ I at hJI
  subst τ'
  obtain ⟨V, p, hV, hp, rfl⟩ := reach_succ_iff.1 hW
  rw [reach_zero_iff] at hV
  subst V
  have hpIS := hIS J _ p hp
  have hdec : ∀ l, (eq3Alg (B := B) a₀ e).dec l (step (X := ℤ) (r := 0) τ p l) =
      eq3 e (p.sees l) τ := fun l => eq3Dec_step e τ p l
  refine ⟨fun l => eq3 e (p.sees l) τ, ⟨fun hcard j hj => ?_, fun _ => ?_⟩, fun l _ => hdec l⟩
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hcard
    rw [Finset.mem_singleton] at hj; subst hj
    have h1 := hpIS.1 j (Finset.mem_singleton_self j)
    have hs : p.sees j = {j} := Finset.Subset.antisymm h1.2 (Finset.singleton_subset_iff.2 h1.1)
    simp only [hs]
    exact eq3_singleton he j τ
  · refine ⟨fun l => if l ∈ J then eq3 e (p.sees l) τ else eq3 e (p.sees j₀) τ,
      fun i _ => ⟨?_, fun _ j _ => ?_⟩, fun l hl => by simp [hl]⟩
    · dsimp only
      have key : ∀ l ∈ J, InRange I x (eq3 e (p.sees l) τ) := fun l hl =>
        eq3_inRange he ⟨l, (hpIS.1 l hl).1⟩ ((hpIS.1 l hl).2.trans hJI) hrange
      split_ifs with h
      · exact key i h
      · exact key j₀ hj₀
    · dsimp only
      split_ifs with h1 h2 h2
      · exact eq3_round hpIS hJI hclose h1 h2
      · exact eq3_round hpIS hJI hclose h1 hj₀
      · exact eq3_round hpIS hJI hclose hj₀ h2
      · simp; omega

/-- The local task `Π_{τ,σ}` of the liberal `ε`-agreement is solvable in one round, with any
prescribed box inputs `a₀`, whenever `τ` is a legal output of the liberal `2ε`-agreement. -/
theorem libAA_local_solvable [Fintype P] {A B : Type} {M : Model P A B}
    (hIS : ∀ J a, ∀ p ∈ M.Pat J a, IsIS J p.sees) (a₀ : P → A) {S : Finset P} {m e : ℤ}
    (he : 0 ≤ e) {I : Finset P} {x τ : P → ℤ} (hτ : τ ∈ (libAA S m (2 * e)).Δ I x) :
    ∃ alg : Alg P ℤ A B ℤ 1, (∀ r i v, alg.inp r i v = a₀ i) ∧
      Solves M (localTask (libAA S m e) I x τ) alg := by
  by_cases hI : I.card ≤ 2
  · -- `τ` itself is a legal output of the liberal `ε`-agreement
    have hτ' : τ ∈ (libAA S m e).Δ I x := by
      intro i hi
      refine ⟨(hτ i hi).1, fun hI2 j hj => ?_⟩
      have h1 : I.card ≤ 1 := by omega
      have : i = j := Finset.card_le_one.1 h1 i hi j hj
      subst this; simp; omega
    exact ⟨constAlg a₀ τ, fun _ _ _ => rfl, constAlg_solves M _ hτ' _⟩
  · refine ⟨eq3Alg a₀ e, fun _ _ _ => rfl, eq3Alg_solves hIS _ he (fun l hl => (hτ l hl).1)
      fun a ha b hb => ?_⟩
    have := (hτ a ha).2 (by omega) b hb
    rw [abs_le] at this; omega

lemma libAA_inVertices {S : Finset P} {m e : ℤ} (he : 0 ≤ e) {I : Finset P} {x τ : P → ℤ}
    (hτ : τ ∈ (libAA S m (2 * e)).Δ I x) : InVertices (libAA S m e) I x τ :=
  fun i hi => ⟨fun _ => τ i, fun _ _ => ⟨(hτ i hi).1, fun _ _ _ => by simp; omega⟩, rfl⟩

/-- **Claims 3 and 4** (converse inclusion `Δ_{2ε} ⊆ Δ'_ε`) for any model whose rounds are
immediate snapshots (IIS, IIS + test&set, …). -/
theorem libAA_supset [Fintype P] {A B : Type} [Inhabited A] {M : Model P A B}
    (hIS : ∀ J a, ∀ p ∈ M.Pat J a, IsIS J p.sees) {S : Finset P} {m e : ℤ} (he : 0 ≤ e)
    (I : Finset P) (x : P → ℤ) :
    (libAA S m (2 * e)).Δ I x ⊆ (closure M (libAA S m e)).Δ I x := fun _ hτ =>
  let ⟨alg, _, h⟩ := libAA_local_solvable hIS (fun _ => default) he hτ
  ⟨libAA_inVertices he hτ, alg, h⟩

lemma iis_isIS : ∀ (J : Finset P) a, ∀ p ∈ (iis : Model P Unit Unit).Pat J a, IsIS J p.sees :=
  fun _ _ _ hp => hp

lemma iisTS_isIS : ∀ (J : Finset P) a, ∀ p ∈ (iisTS : Model P Unit Bool).Pat J a,
    IsIS J p.sees :=
  fun _ _ _ hp => hp.1

/-- **Claim 3**: for `ε ≥ 0`, the closure of the liberal `ε`-agreement w.r.t. IIS is the liberal
`2ε`-agreement. -/
theorem claim3 [Fintype P] {S : Finset P} {m e : ℤ} (he : 0 ≤ e) (I : Finset P) (x : P → ℤ) :
    (closure iis (libAA S m e)).Δ I x = (libAA S m (2 * e)).Δ I x :=
  Set.Subset.antisymm (claim3_subset I x) (libAA_supset iis_isIS he I x)

/-- **Claim 4**: for `ε ≥ 0`, the closure of the liberal `ε`-agreement w.r.t. IIS augmented with
test&set is the liberal `2ε`-agreement. -/
theorem claim4 [Fintype P] {S : Finset P} {m e : ℤ} (he : 0 ≤ e) (I : Finset P) (x : P → ℤ) :
    (closure iisTS (libAA S m e)).Δ I x = (libAA S m (2 * e)).Δ I x :=
  Set.Subset.antisymm (claim4_subset I x) (libAA_supset iisTS_isIS he I x)

lemma iisBC_isIS : ∀ (J : Finset P) a, ∀ p ∈ (iisBC : Model P Bool Bool).Pat J a,
    IsIS J p.sees :=
  fun _ _ _ hp => hp.1

/-- **Claim 6** (equality): when only processes of `S' = {l ∈ S | β l = b}` participate, the
closure w.r.t. `β` of the liberal `ε`-agreement (IIS + binary consensus) is the liberal
`2ε`-agreement. -/
theorem claim6 [Fintype P] {S : Finset P} {m e : ℤ} (he : 0 ≤ e) (β : P → Bool) (b : Bool)
    {I : Finset P} (hI : I ⊆ S.filter (fun l => β l = b)) (x : P → ℤ) :
    (closureβ iisBC (libAA S m e) β).Δ I x = (libAA S m (2 * e)).Δ I x := by
  refine Set.Subset.antisymm (claim6_subset β b hI x) fun τ hτ => ?_
  obtain ⟨alg, hinp, h⟩ := libAA_local_solvable iisBC_isIS β he hτ
  exact ⟨libAA_inVertices he hτ, alg, hinp, h⟩

/-! ### Tightness for `n ≥ 3` -/

/-- Zero rounds suffice when `ε ≥ 1` (decide your input). -/
theorem aa_solvable_zero {A B : Type} [Inhabited A] (M : Model P A B) {S : Finset P} {m e : ℤ} (hme : m ≤ e) :
    Solvable M (aa S m e) 0 := by
  refine ⟨⟨fun _ _ _ => default, fun _ v => v⟩, fun I x hI V hV => ?_⟩
  rw [reach_zero_iff] at hV
  subst V
  obtain ⟨-, -, hx⟩ := hI
  refine ⟨x, fun i hi => ⟨⟨⟨i, hi, le_rfl⟩, ⟨i, hi, le_rfl⟩⟩, fun j hj => ?_⟩, fun _ _ => rfl⟩
  have h1 := hx i hi
  have h2 := hx j hj
  dsimp only at h1 h2
  rw [abs_le]; constructor <;> omega

/-- **Tightness for `n ≥ 3`** (Remark after Corollary 3): `ε`-approximate agreement is solvable in
`t` rounds of IIS as soon as `1 ≤ 2^t ε` (iterate Equation (3)), so Corollary 3 is tight. -/
theorem aa_solvable_many [Fintype P] {S : Finset P} {m : ℤ} :
    ∀ (t : ℕ) (e : ℤ), 0 ≤ e → m ≤ 2 ^ t * e → Solvable iis (aa S m e) t
  | 0, e, _, h => aa_solvable_zero iis (by simpa using h)
  | t + 1, e, he, h => by
    have ih := aa_solvable_many (S := S) t (2 * e) (by omega)
      (h.trans (le_of_eq (by ring)))
    refine solvable_succ_of_reduction (T₂ := aa S m (2 * e)) (fun _ h => h) ih (fun _ _ => ())
      (fun _ w => eq3Dec e w) ?_
    rintro I x hI d ⟨y, hy, hdy⟩ p hp
    have hpIS := iis_isIS I _ p hp
    have hclose : ∀ a ∈ I, ∀ b ∈ I, d a - d b ≤ 2 * e := fun a ha b hb => by
      have := (hy a ha).2 b hb
      rw [abs_le, ← hdy a ha, ← hdy b hb] at this; omega
    refine ⟨fun i => eq3 e (p.sees i) d, fun i hi => ⟨?_, fun j hj => ?_⟩,
      fun i _ => eq3Dec_step e d p i⟩
    · exact eq3_inRange he ⟨i, (hpIS.1 i hi).1⟩ (hpIS.1 i hi).2
        (fun l hl => by rw [hdy l hl]; exact (hy l hl).1)
    · exact eq3_round hpIS le_rfl hclose hi hj

/-! ### Equation (2): two processes -/

/-- Clamp `d` into `[-c, c]`. -/
def clampI (c d : ℤ) : ℤ := max (-c) (min d c)

/-- Equation (2) as a uniform one-round map for two processes `p₀ ≠ p₁`: a process seeing only
itself outputs its value; seeing both values `v₀, v₁`, process `p₁` outputs
`v₀ + clamp(v₁ - v₀, ε)` and process `p₀` outputs `v₀ + clamp(v₁ - v₀, 2ε)`. For `v₀ ≤ v₁` these
are `z = min(v₁, v₀ + ε)` and `min(v₁, z + ε)`, exactly Equation (2); for `v₀ > v₁` it is the
mirror image (the paper's "w.l.o.g."). -/
def eq2Dec {B : Type} (p₀ p₁ : P) (e : ℤ) (i : P) (w : B × (P → Option ℤ)) : ℤ :=
  match w.2 p₀, w.2 p₁ with
  | some v₀, some v₁ =>
    if i = p₁ then v₀ + clampI e (v₁ - v₀) else v₀ + clampI (2 * e) (v₁ - v₀)
  | _, _ => (w.2 i).getD 0

lemma eq2Dec_step {B : Type} (p₀ p₁ : P) (e : ℤ) (d : P → ℤ) (p : Pattern P B) (i : P) :
    eq2Dec p₀ p₁ e i (p.out i, fun j => if j ∈ p.sees i then some (d j) else none) =
      if p₀ ∈ p.sees i ∧ p₁ ∈ p.sees i then
        (if i = p₁ then d p₀ + clampI e (d p₁ - d p₀) else d p₀ + clampI (2 * e) (d p₁ - d p₀))
      else (if i ∈ p.sees i then d i else 0) := by
  by_cases h0 : p₀ ∈ p.sees i <;> by_cases h1 : p₁ ∈ p.sees i <;>
    by_cases hi : i ∈ p.sees i <;> simp [eq2Dec, h0, h1, hi]

/-- The core computation of Claim 2 / Equation (2). -/
lemma eq2_round {B : Type} {p₀ p₁ : P} (h01 : p₀ ≠ p₁) {e : ℤ} (he : 0 ≤ e) {J : Finset P}
    (hJ : J ⊆ {p₀, p₁}) {p : Pattern P B} (hIS : IsIS J p.sees) {d : P → ℤ}
    (hd : ∀ a ∈ J, ∀ b ∈ J, d a - d b ≤ 3 * e) :
    let o := fun i => eq2Dec p₀ p₁ e i (p.out i, fun j => if j ∈ p.sees i then some (d j) else none)
    (∀ i ∈ J, p.sees i = {i} → o i = d i) ∧
    (∀ i ∈ J, (o i = d i) ∨ (p₀ ∈ J ∧ p₁ ∈ J ∧ min (d p₀) (d p₁) ≤ o i ∧ o i ≤ max (d p₀) (d p₁)))
    ∧ ∀ i ∈ J, ∀ j ∈ J, abs (o i - o j) ≤ e := by
  intro o
  have ho : ∀ i, o i = _ := fun i => eq2Dec_step p₀ p₁ e d p i
  have hmem : ∀ i ∈ J, i = p₀ ∨ i = p₁ := fun i hi => by simpa using hJ hi
  refine ⟨fun i hi hs => ?_, fun i hi => ?_, fun i hi j hj => ?_⟩
  · rw [ho, hs]
    rcases hmem i hi with rfl | rfl <;> simp [h01, h01.symm]
  · rw [ho]
    have hii := (hIS.1 i hi).1
    by_cases hb : p₀ ∈ p.sees i ∧ p₁ ∈ p.sees i
    · have h0J := (hIS.1 i hi).2 hb.1
      have h1J := (hIS.1 i hi).2 hb.2
      have := hd p₀ h0J p₁ h1J
      have := hd p₁ h1J p₀ h0J
      right; refine ⟨h0J, h1J, ?_⟩
      simp only [hb, and_self, ite_true, clampI]
      split_ifs <;> constructor <;> omega
    · left; simp [hb, hii]
  · rw [ho i, ho j]
    have hii := (hIS.1 i hi).1
    have hjj := (hIS.1 j hj).1
    by_cases hij : i = j
    · subst hij; simp [he]
    -- `{i, j} = {p₀, p₁}`
    have hcmp := hIS.2.1 i hi j hj
    have hsi := (hIS.1 i hi).2
    have hsj := (hIS.1 j hj).2
    rcases hmem i hi with rfl | rfl <;> rcases hmem j hj with rfl | rfl
    · exact absurd rfl hij
    · have := hd i hi j hj
      have := hd j hj i hi
      by_cases a : j ∈ p.sees i <;> by_cases b : i ∈ p.sees j <;>
        simp [a, b, hii, hjj, h01, clampI] at hcmp ⊢ <;> rw [abs_le] <;>
        constructor <;> omega
    · have := hd i hi j hj
      have := hd j hj i hi
      by_cases a : j ∈ p.sees i <;> by_cases b : i ∈ p.sees j <;>
        simp [a, b, hii, hjj, h01, clampI] at hcmp ⊢ <;> rw [abs_le] <;>
        constructor <;> omega
    · exact absurd rfl hij

lemma inRange_min_max {I : Finset P} {x : P → ℤ} {a b v : ℤ} (ha : InRange I x a)
    (hb : InRange I x b) (h1 : min a b ≤ v) (h2 : v ≤ max a b) : InRange I x v := by
  rcases le_total a b with h | h
  · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
    exact InRange.of_between ha hb h1 h2
  · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
    exact InRange.of_between hb ha h1 h2

/-- The outputs of Equation (2) on a round of `J ⊇ I` form a legal output of `ε`-agreement. -/
lemma eq2_mem_aa {B : Type} {p₀ p₁ : P} (h01 : p₀ ≠ p₁) {e : ℤ} (he : 0 ≤ e) {S : Finset P}
    {m : ℤ} {I J : Finset P} (hJ : J ⊆ {p₀, p₁}) (hIJ : I ⊆ J) {p : Pattern P B}
    (hIS : IsIS J p.sees) {x d : P → ℤ} (hd : ∀ a ∈ J, ∀ b ∈ J, d a - d b ≤ 3 * e)
    (hrange : ∀ l ∈ J, InRange I x (d l)) :
    (fun i => eq2Dec p₀ p₁ e i (p.out i, fun j => if j ∈ p.sees i then some (d j) else none)) ∈
      (aa S m e).Δ I x := by
  obtain ⟨h1, h2, h3⟩ := eq2_round h01 he hJ hIS hd
  intro i hi
  refine ⟨?_, fun j hj => h3 i (hIJ hi) j (hIJ hj)⟩
  rcases h2 i (hIJ hi) with h | ⟨h0J, h1J, hlo, hhi⟩
  · rw [h]; exact hrange i (hIJ hi)
  · exact inRange_min_max (hrange p₀ h0J) (hrange p₁ h1J) hlo hhi

lemma univ_eq_pair [Fintype P] (hP : Fintype.card P = 2) :
    ∃ p₀ p₁ : P, p₀ ≠ p₁ ∧ (Finset.univ : Finset P) = {p₀, p₁} := by
  obtain ⟨p₀, p₁, h01⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
  refine ⟨p₀, p₁, h01, (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm⟩
  rw [Finset.card_univ, hP, Finset.card_pair h01]

/-- **Tightness for two processes** (Remark after Corollary 3): `ε`-approximate agreement between
two processes is solvable in `t` rounds of IIS as soon as `1 ≤ 3^t ε` (iterate Equation (2)). -/
theorem aa_solvable_two [Fintype P] (hP : Fintype.card P = 2) {m : ℤ} :
    ∀ (t : ℕ) (e : ℤ), 0 ≤ e → m ≤ 3 ^ t * e → Solvable iis (aa (Finset.univ : Finset P) m e) t
  | 0, e, _, h => aa_solvable_zero iis (by simpa using h)
  | t + 1, e, he, h => by
    obtain ⟨p₀, p₁, h01, huniv⟩ := univ_eq_pair hP
    have ih := aa_solvable_two hP t (3 * e) (by omega) (h.trans (le_of_eq (by ring)))
    refine solvable_succ_of_reduction (T₂ := aa Finset.univ m (3 * e)) (fun _ h => h) ih
      (fun _ _ => ()) (eq2Dec p₀ p₁ e) ?_
    rintro I x hI d ⟨y, hy, hdy⟩ p hp
    refine ⟨_, eq2_mem_aa h01 he (huniv ▸ Finset.subset_univ I) le_rfl (iis_isIS I _ p hp)
      (fun a ha b hb => ?_) (fun l hl => by rw [hdy l hl]; exact (hy l hl).1), fun _ _ => rfl⟩
    have := (hy a ha).2 b hb
    rw [abs_le, ← hdy a ha, ← hdy b hb] at this; omega

/-- **Claim 2**: for two processes and `ε ≥ 0`, the closure of `ε`-approximate agreement w.r.t.
IIS is `3ε`-approximate agreement. -/
theorem claim2 [Fintype P] (hP : Fintype.card P = 2) {m e : ℤ} (he : 0 ≤ e) (I : Finset P)
    (x : P → ℤ) :
    (closure iis (aa (Finset.univ : Finset P) m e)).Δ I x =
      (aa (Finset.univ : Finset P) m (3 * e)).Δ I x := by
  refine Set.Subset.antisymm (closure_aa_subset I x) fun τ hτ => ?_
  obtain ⟨p₀, p₁, h01, huniv⟩ := univ_eq_pair hP
  refine ⟨fun i hi => ⟨fun _ => τ i, fun l _ => ⟨(hτ i hi).1, fun _ _ => by simp [he]⟩, rfl⟩,
    ⟨⟨fun _ _ _ => (), fun i w => eq2Dec p₀ p₁ e i w⟩, ?_⟩⟩
  rintro J τ' ⟨hJne, hJI, hτ'⟩ W hW
  change τ' = τ at hτ'
  change J.Nonempty at hJne
  change J ⊆ I at hJI
  subst τ'
  obtain ⟨V, p, hV, hp, rfl⟩ := reach_succ_iff.1 hW
  rw [reach_zero_iff] at hV
  subst V
  have hpIS := iis_isIS J _ p hp
  have hJ2 : J ⊆ {p₀, p₁} := huniv ▸ Finset.subset_univ J
  have hd : ∀ a ∈ J, ∀ b ∈ J, τ a - τ b ≤ 3 * e := fun a ha b hb => by
    have := (hτ a (hJI ha)).2 b (hJI hb); rw [abs_le] at this; omega
  obtain ⟨h1, -, -⟩ := eq2_round h01 he hJ2 hpIS hd
  refine ⟨_, ⟨fun hcard j hj => ?_, fun hcard => ?_⟩, fun _ _ => rfl⟩
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hcard
    rw [Finset.mem_singleton] at hj; subst hj
    have h1' := hpIS.1 j (Finset.mem_singleton_self j)
    exact h1 j (Finset.mem_singleton_self j)
      (Finset.Subset.antisymm h1'.2 (Finset.singleton_subset_iff.2 h1'.1))
  · have hIJ : I ⊆ J := by
      have h2 : 2 ≤ J.card := by
        have := Finset.card_pos.2 hJne; omega
      have hJu : J = Finset.univ := Finset.eq_univ_of_card J (by
        have := Finset.card_le_card hJ2; rw [Finset.card_pair h01] at this; omega)
      rw [hJu]; exact Finset.subset_univ I
    exact ⟨_, eq2_mem_aa h01 he hJ2 hIJ hpIS hd (fun l hl => (hτ l (hJI hl)).1),
      fun _ _ => rfl⟩

end AsyncSpeedup
