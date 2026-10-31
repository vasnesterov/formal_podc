import Papers.PODC2015.WeakestFDEventualConsistency.Driver

/-!
# Lemma 4: from eventual consensus to eventual irrevocable consensus (Algorithm 6)

Algorithm 6 of [DGKPS15] (Appendix A.2): a process keeps the sequence `decision` of its current
decisions. On invocation of `proposeEIC_ℓ(v)` it invokes `proposeEC_ℓ(decision.v)`; on a
response `decision'` of the EC black box to instance `ℓ`, it (re)decides `decision'[k]` for every
`k ≤ ℓ` with `decision'[k] ≠ decision[k]`, and sets `decision := decision'`.

Modelling (see `Driver`): the application is folded in (`inp p j` is the value `p` proposes to
EIC instance `j`; instance `0` is invoked at the first step, instance `j + 1` in the step
returning the first response to `j`). The EC black box takes sequences `List V`; its invocations
are outputs, its responses input events. The transformation invokes `proposeEC_{ℓ+1}` in the
step of the response to `proposeEC_ℓ` and ignores responses to other instances (with a black box
satisfying EC, which is used properly, there are none).

Hypotheses on the black box: it responds only to invoked instances, and satisfies (uniform) `EC`
whenever it is used properly. The usage assumption is `ProperUseEIC` ("invoke `j + 1` exactly
at the *first* response to `j`"): it coincides with `ECHist.ProperUse` for histories satisfying
EC-Integrity (`properUse_iff_properUseEIC`), but unlike `ProperUse` it can be guaranteed by a
user whatever the black box does (`Driver.bbHist_properUseEIC`).

Result (`lemma4`): EIC with agreement among **correct** processes (`EICCorrect`). The literal,
uniform EIC-Agreement fails: see `ECtoEICCounterexample`.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

variable {P V : Type*}

/-- For a history satisfying EC-Integrity, the usage assumptions `ProperUse` and `ProperUseEIC`
coincide. -/
lemma properUse_iff_properUseEIC {h : ECHist P V} (hint : ECIntegrity h) :
    h.ProperUse ↔ h.ProperUseEIC := by
  constructor
  · intro hu
    refine ⟨hu.inv_once, fun p j v t hi => ?_, fun p j v t hr _ => hu.resp_inv p j v t hr⟩
    obtain ⟨v', hr⟩ := hu.inv_succ p j v t hi
    exact ⟨v', hr, fun t' v'' ht' hr' => by have := (hint p j v' v'' t t' hr hr').1; omega⟩
  · intro hu
    refine ⟨hu.inv_once, fun p j v t hi => ?_, fun p j v t hr => hu.resp_inv p j v t hr ?_⟩
    · obtain ⟨v', hr, -⟩ := hu.inv_succ p j v t hi; exact ⟨v', hr⟩
    · intro t' v'' ht' hr'; have := (hint p j v v'' t t' hr hr').1; omega

namespace ECHist

variable {h : ECHist P V} {p : P} {j : ℕ} {v : V} {t : ℕ}

lemma Current.succ_of_resp (hr : h.resp p j v t) : h.Current p j v (t + 1) :=
  ⟨t, Nat.lt_succ_self t, hr, fun _ _ h1 h2 _ => by omega⟩

lemma Current.succ (hc : h.Current p j v t) (hn : ∀ v', ¬ h.resp p j v' t) :
    h.Current p j v (t + 1) := by
  obtain ⟨t₀, ht₀, hr, hno⟩ := hc
  refine ⟨t₀, by omega, hr, fun t₁ v₁ h1 h2 hr₁ => ?_⟩
  rcases Nat.lt_or_ge t₁ t with h3 | h3
  · exact hno t₁ v₁ h1 h3 hr₁
  · exact hn v₁ (by rw [show t = t₁ by omega]; exact hr₁)

lemma Current.unique {v' : V} (hfun : ∀ t₀ v v', h.resp p j v t₀ → h.resp p j v' t₀ → v = v')
    (hc : h.Current p j v t) (hc' : h.Current p j v' t) : v = v' := by
  obtain ⟨t₀, ht₀, hr, hno⟩ := hc
  obtain ⟨t₀', ht₀', hr', hno'⟩ := hc'
  rcases lt_trichotomy t₀ t₀' with hlt | rfl | hgt
  · exact absurd hr' (hno t₀' v' hlt ht₀')
  · exact hfun t₀ v v' hr hr'
  · exact absurd hr (hno' t₀ v hgt ht₀)

end ECHist

lemma getElem?_eq_of_prefix {l₁ l₂ : List V} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁[i]? = l₂[i]? := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getElem?_append_left hi]

namespace Alg6

variable [DecidableEq V]

/-- The decisions taken on the response `x` to instance `c` when the current decisions are `d`:
`x[k]` for every `k ≤ c` with `x[k] ≠ d[k]`. -/
def decides (c : ℕ) (x d : List V) : List (AOut V) :=
  (List.range (c + 1)).filterMap fun k => if x[k]? ≠ d[k]? then (x[k]?).map (AOut.resp k) else none

lemma mem_decides {c k : ℕ} {x d : List V} {v : V} :
    AOut.resp k v ∈ decides c x d ↔ k ≤ c ∧ x[k]? = some v ∧ d[k]? ≠ some v := by
  simp only [decides, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨k', hk', hx⟩
    split_ifs at hx with hne
    rcases hxk : x[k']? with _ | w
    · simp [hxk] at hx
    · simp only [hxk, Option.map_some, Option.some.injEq, AOut.resp.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨by omega, hxk, fun h => hne (by rw [hxk, h])⟩
  · rintro ⟨hk, hx, hd⟩
    have hne : x[k]? ≠ d[k]? := by rw [hx]; exact fun h => hd h.symm
    exact ⟨k, by omega, by simp [hx]; exact fun h => hd h.symm⟩

lemma not_inv_mem_decides {c j : ℕ} {x d : List V} {v : V} : AOut.inv j v ∉ decides c x d := by
  simp only [decides, List.mem_filterMap, List.mem_range, not_exists, not_and]
  intro k _ h
  split_ifs at h
  rcases hxk : x[k]? with _ | w <;> simp [hxk] at h

/-- **Algorithm 6** of [DGKPS15] (with the application folded in). -/
def driver (inp : P → ℕ → V) : Driver P (List V) (List V) (AOut V) where
  d0 := []
  startOut p := [.inv 0 (inp p 0)]
  upd _ _ x _ := x
  respOut p c x d := decides c x d ++ [.inv (c + 1) (inp p (c + 1))]
  prop p j d := d ++ [inp p j]

variable [DecidableEq P] {R : Type*} {inp : P → ℕ → V} {r : Run P R (ℕ × List V)}

open Driver

lemma app_resp_iff {p : P} {k : ℕ} {v : V} {t : ℕ} :
    ((driver inp).appHist r).resp p k v t ↔ ∃ c x, (driver inp).n r p t = c + 1 ∧ r.σ t = some (p, .input (c, x)) ∧
      k ≤ c ∧ x[k]? = some v ∧ ((driver inp).dat r p t)[k]? ≠ some v := by
  simp only [appHist, out_app_iff]
  constructor
  · rintro (⟨-, -, -, h⟩ | ⟨c, x, hc, hσ, h⟩)
    · simp [driver] at h
    · simp only [driver, List.mem_append, List.mem_singleton, reduceCtorEq, or_false,
        mem_decides] at h
      exact ⟨c, x, hc, hσ, h⟩
  · rintro ⟨c, x, hc, hσ, h⟩
    exact Or.inr ⟨c, x, hc, hσ, List.mem_append_left _ (mem_decides.2 h)⟩

lemma app_inv_iff {p : P} {j : ℕ} {v : V} {t : ℕ} :
    ((driver inp).appHist r).inv p j v t ↔ (driver inp).n r p t = j ∧ (driver inp).n r p (t + 1) = j + 1 ∧ v = inp p j := by
  simp only [appHist, out_iff']
  rcases (driver inp).step_cases r t p with ⟨h1, h⟩ | ⟨h0, hσ, h1, hout⟩ | ⟨c, x, hc, hσ, h1, hout⟩
  · simp only [out_iff'] at h
    refine ⟨fun h' => absurd h' (h _), fun ⟨h2, h3, _⟩ => ?_⟩
    simp only [n] at h2 h3; rw [h1] at h3; omega
  · obtain ⟨c0, hc0⟩ := hσ
    rw [hout]; simp only [n] at h0 h1 ⊢; rw [h1, h0]
    simp only [driver, hc0]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      DOut.app.injEq, AOut.inv.injEq, reduceCtorEq, List.not_mem_nil, or_false, Option.some.injEq,
      Prod.mk.injEq, true_and, exists_eq', true_and]
    constructor
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, -, rfl⟩; simp
  · rw [hout]; simp only [n] at hc h1 ⊢; rw [h1, hc]
    simp [driver, hσ, not_inv_mem_decides]
    constructor
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; simp

/-- Shape of the invocations of the EC black box. -/
lemma bb_inv_shape {p : P} {j : ℕ} {w : List V} {t : ℕ} (h : ((driver inp).bbHist r).inv p j w t) :
    ((driver inp).appHist r).inv p j (inp p j) t ∧
      ((j = 0 ∧ w = [inp p 0]) ∨ (∃ c x, j = c + 1 ∧ ((driver inp).bbHist r).resp p c x t ∧ w = x ++ [inp p j])) := by
  obtain ⟨h0, h1, rfl⟩ := out_bb_iff.1 h
  refine ⟨app_inv_iff.2 ⟨h0, h1, rfl⟩, ?_⟩
  rcases j with _ | c
  · obtain ⟨-, hd, -⟩ := trans_zero h0 h1
    refine Or.inl ⟨rfl, ?_⟩
    show (driver inp).dat r p (t + 1) ++ [inp p 0] = [inp p 0]
    rw [hd, dat_of_n_zero h0]; rfl
  · obtain ⟨x, hσ, hd, -⟩ := trans_succ h0 h1
    exact Or.inr ⟨c, x, rfl, hσ, by
      show (driver inp).dat r p (t + 1) ++ [inp p (c + 1)] = x ++ [inp p (c + 1)]
      rw [hd]; rfl⟩

section EC

variable (hval : ECValidity ((driver inp).bbHist r))
include hval

/-- Lengths: every value proposed to (hence returned by) instance `j` has length `j + 1`. -/
lemma length_of_inv : ∀ j p w t, ((driver inp).bbHist r).inv p j w t → w.length = j + 1 := by
  intro j
  induction j with
  | zero => intro p w t h; rcases (bb_inv_shape h).2 with ⟨-, rfl⟩ | ⟨c, x, hc, -⟩ <;> simp_all
  | succ c ih =>
    intro p w t h
    rcases (bb_inv_shape h).2 with ⟨h', -⟩ | ⟨c', x, hc, hr, rfl⟩
    · omega
    · obtain rfl : c' = c := by omega
      obtain ⟨q, t', -, hi⟩ := hval p c' x t hr
      simp [ih q x t' hi]

lemma length_of_resp {p : P} {j : ℕ} {x : List V} {t : ℕ} (h : ((driver inp).bbHist r).resp p j x t) :
    x.length = j + 1 := by
  obtain ⟨q, t', -, hi⟩ := hval p j x t h
  exact length_of_inv hval j q x t' hi

/-- Every entry `k` of a value proposed to the black box was previously proposed to EIC
instance `k` (the induction behind EIC-Validity). -/
lemma entry_of_inv : ∀ j p w t, ((driver inp).bbHist r).inv p j w t → ∀ k v, w[k]? = some v →
    ∃ q t', t' ≤ t ∧ ((driver inp).appHist r).inv q k v t' := by
  intro j
  induction j with
  | zero =>
    intro p w t h k v hk
    obtain ⟨hi, h'⟩ := bb_inv_shape h
    rcases h' with ⟨-, rfl⟩ | ⟨c, x, hc, -⟩
    · rcases k with _ | k
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
        exact ⟨p, t, le_rfl, hi⟩
      · simp at hk
    · omega
  | succ c ih =>
    intro p w t h k v hk
    obtain ⟨hi, h'⟩ := bb_inv_shape h
    rcases h' with ⟨h', -⟩ | ⟨c', x, hc, hr, rfl⟩
    · omega
    obtain rfl : c' = c := by omega
    have hlen := length_of_resp hval hr
    rcases Nat.lt_or_ge k x.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hk
      obtain ⟨q, t', ht', hi'⟩ := hval p c' x t hr
      obtain ⟨q', t'', ht'', hi''⟩ := ih q x t' hi' k v hk
      exact ⟨q', t'', by omega, hi''⟩
    · rw [List.getElem?_append_right hge] at hk
      rcases hkk : k - x.length with _ | m
      · rw [hkk] at hk
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
        obtain rfl : k = c' + 1 := by omega
        exact ⟨p, t, le_rfl, hi⟩
      · rw [hkk] at hk; simp at hk

omit hval in
/-- The data of a process is its last response from the black box. -/
lemma dat_spec (p : P) : ∀ t, ((driver inp).n r p t ≤ 1 ∧ (driver inp).dat r p t = []) ∨
    (2 ≤ (driver inp).n r p t ∧ ∃ t' < t, ((driver inp).bbHist r).resp p ((driver inp).n r p t - 2) ((driver inp).dat r p t) t') := by
  intro t
  induction t with
  | zero => exact Or.inl ⟨by simp, by simp [driver]⟩
  | succ t ih =>
    rcases n_succ (Dr := driver inp) (r := r) p t with h | h
    · have hs := (stay_of_n_eq h).1
      simp only [dat, n] at ih ⊢; rw [hs]
      rcases ih with ih | ⟨h2, t', ht', hr⟩
      · exact Or.inl ih
      · exact Or.inr ⟨h2, t', by omega, hr⟩
    · rcases hn : (driver inp).n r p t with _ | c
      · obtain ⟨-, hd, -⟩ := trans_zero hn (by omega)
        exact Or.inl ⟨by omega, by rw [hd, dat_of_n_zero hn]; rfl⟩
      · obtain ⟨x, hσ, hd, -⟩ := trans_succ hn (by omega)
        refine Or.inr ⟨by omega, t, by omega, ?_⟩
        rw [h, hn, hd]; exact hσ

lemma length_dat (p : P) (t : ℕ) : ((driver inp).dat r p t).length = (driver inp).n r p t - 1 := by
  rcases dat_spec (inp := inp) (r := r) p t with ⟨h1, h2⟩ | ⟨h1, t', -, hr⟩
  · rw [h2]; simp; omega
  · rw [length_of_resp hval hr]; omega

/-- The step of the response to the current instance `j` decides `j` (for the first time). -/
lemma resp_at_trans {p : P} {j : ℕ} {x : List V} {t : ℕ} (hn : (driver inp).n r p t = j + 1)
    (hσ : r.σ t = some (p, .input (j, x))) : ∃ v, ((driver inp).appHist r).resp p j v t := by
  have hlen := length_of_resp hval hσ
  obtain ⟨v, hv⟩ : ∃ v, x[j]? = some v := ⟨x[j], List.getElem?_eq_getElem (by omega)⟩
  refine ⟨v, app_resp_iff.2 ⟨j, x, hn, hσ, le_rfl, hv, ?_⟩⟩
  rw [List.getElem?_eq_none (by rw [length_dat hval]; omega)]; simp

omit hval in
/-- A process decides at most one value per instance in a step. -/
lemma resp_fun {p : P} {k : ℕ} {v v' : V} {t : ℕ} (h : ((driver inp).appHist r).resp p k v t) (h' : ((driver inp).appHist r).resp p k v' t) :
    v = v' := by
  obtain ⟨c, x, -, hσ, -, hx, -⟩ := app_resp_iff.1 h
  obtain ⟨c', x', -, hσ', -, hx', -⟩ := app_resp_iff.1 h'
  rw [hσ] at hσ'
  simp only [Option.some.injEq, Prod.mk.injEq, Choice.input.injEq, true_and] at hσ'
  obtain ⟨-, rfl⟩ := hσ'
  rw [hx] at hx'; exact Option.some.inj hx'

/-- **Invariant**: the current decision of `p` for every instance `ℓ` covered by its sequence
`decision` is `decision[ℓ]`. -/
lemma current_dat (p : P) : ∀ t ℓ (hℓ : ℓ < ((driver inp).dat r p t).length), ((driver inp).appHist r).Current p ℓ ((driver inp).dat r p t)[ℓ] t := by
  intro t
  induction t with
  | zero => intro ℓ hℓ; simp [driver] at hℓ
  | succ t ih =>
    intro ℓ hℓ
    rcases n_succ (Dr := driver inp) (r := r) p t with h | h
    · obtain ⟨hs, hno⟩ := stay_of_n_eq h
      have hd : (driver inp).dat r p (t + 1) = (driver inp).dat r p t := by simp only [dat]; rw [hs]
      have hℓ' : ℓ < ((driver inp).dat r p t).length := hd ▸ hℓ
      have := ih ℓ hℓ'
      simp only [hd]
      exact this.succ fun v' hr => hno _ hr
    · rcases hn : (driver inp).n r p t with _ | c
      · obtain ⟨-, hd, -⟩ := trans_zero hn (by omega)
        rw [hd, dat_of_n_zero hn] at hℓ; simp [driver] at hℓ
      · obtain ⟨x, hσ, hd, -⟩ := trans_succ hn (by omega)
        have hd' : (driver inp).dat r p (t + 1) = x := hd
        have hlen := length_of_resp hval hσ
        have hl : ℓ < x.length := by rw [← hd']; exact hℓ
        have hx : x[ℓ]? = some ((driver inp).dat r p (t + 1))[ℓ] := by
          have : ∀ (l : List V) (h : ℓ < l.length), l = x → x[ℓ]? = some l[ℓ] := by
            rintro l h rfl; simp
          exact this _ hℓ hd'
        by_cases hne : ((driver inp).dat r p t)[ℓ]? = some ((driver inp).dat r p (t + 1))[ℓ]
        · -- unchanged entry: no new decision for `ℓ`
          have hℓt : ℓ < ((driver inp).dat r p t).length := by
            by_contra hc; rw [List.getElem?_eq_none (by omega)] at hne; simp at hne
          have hc := ih ℓ hℓt
          have heq : ((driver inp).dat r p t)[ℓ] = ((driver inp).dat r p (t + 1))[ℓ] := by
            rw [List.getElem?_eq_getElem hℓt] at hne; exact Option.some.inj hne
          rw [← heq]
          refine hc.succ fun v' hr => ?_
          obtain ⟨c', x', hc', hσ', -, hx', hd''⟩ := app_resp_iff.1 hr
          rw [hσ] at hσ'
          simp only [Option.some.injEq, Prod.mk.injEq, Choice.input.injEq, true_and] at hσ'
          obtain ⟨-, rfl⟩ := hσ'
          rw [hx] at hx'; rw [Option.some.inj hx'] at hne; exact hd'' hne
        · exact ECHist.Current.succ_of_resp
            (app_resp_iff.2 ⟨c, x, hn, hσ, by omega, hx, hne⟩)

variable {k : ℕ} (hagr : ECAgreementFrom ((driver inp).bbHist r) k)
include hagr

/-- Beyond the agreement index, every response extends every response to an earlier
instance. -/
lemma prefix_of_resp : ∀ m c, k ≤ c → ∀ p q x y t t', ((driver inp).bbHist r).resp p c x t →
    ((driver inp).bbHist r).resp q (c + m) y t' → x <+: y := by
  intro m
  induction m with
  | zero =>
    intro c hc p q x y t t' h h'
    rw [hagr c hc p q x y t t' h h']
  | succ m ih =>
    intro c hc p q x y t t' h h'
    obtain ⟨q', t'', -, hi⟩ := hval q (c + (m + 1)) y t' h'
    rcases (bb_inv_shape hi).2 with ⟨h0, -⟩ | ⟨c', x', hc', hr, rfl⟩
    · omega
    · obtain rfl : c' = c + m := by omega
      exact (ih c hc p q' x x' t t'' h hr).trans (List.prefix_append _ _)

/-- Beyond the agreement index, a process decides instance `ℓ` only in the step of the response
to EC instance `ℓ`. -/
lemma count_eq_of_resp {p : P} {ℓ : ℕ} {v : V} {t : ℕ} (hℓ : k ≤ ℓ) (h : ((driver inp).appHist r).resp p ℓ v t) :
    (driver inp).n r p t = ℓ + 1 ∧ ∃ x, r.σ t = some (p, .input (ℓ, x)) ∧ x[ℓ]? = some v := by
  obtain ⟨c, x, hc, hσ, hle, hx, hd⟩ := app_resp_iff.1 h
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · exfalso
    rcases dat_spec (inp := inp) (r := r) p t with ⟨h1, -⟩ | ⟨h1, t', -, hr⟩
    · omega
    have hc' : (driver inp).n r p t - 2 = (c - 1) := by omega
    rw [hc'] at hr
    have hpre := prefix_of_resp hval hagr 1 (c - 1) (by omega) p p _ x t' t hr
      (by rw [show c - 1 + 1 = c by omega]; exact hσ)
    have hlen := length_dat hval p t
    rw [getElem?_eq_of_prefix hpre (by omega), hx] at hd
    exact hd rfl
  · exact ⟨hc, x, hσ, hx⟩

end EC

/-- **Lemma 4** of [DGKPS15] (Algorithm 6): eventual consensus can be transformed into eventual
irrevocable consensus. In every run of Algorithm 6 whose EC black box responds only to invoked
instances and satisfies (uniform) EC when used properly, the application history satisfies EIC
with agreement among correct processes (`EICCorrect`) and respects EIC's usage assumption.

Admissibility of the run is not needed. The literal (uniform) EIC-Agreement does not hold:
`ECtoEICCounterexample.not_EICAgreement`. -/
theorem lemma4 (hR : ((driver inp).bbHist r).RespAfterInv) (hbb : ((driver inp).bbHist r).ProperUseEIC → EC r.F ((driver inp).bbHist r)) :
    EICCorrect r.F ((driver inp).appHist r) ∧ ((driver inp).appHist r).ProperUseEIC := by
  obtain ⟨hterm, hint, hval, k, hagr⟩ := hbb (bbHist_properUseEIC hR)
  -- the transition from instance `j` happens at every correct process
  have hreach : ∀ p, r.F.Correct p → ∀ j, ∃ t₁ x₁, (driver inp).n r p t₁ = j + 1 ∧
      (driver inp).n r p (t₁ + 1) = j + 2 ∧ r.σ t₁ = some (p, .input (j, x₁)) := by
    intro p hp j
    obtain ⟨v, t, h⟩ := hterm p hp j
    obtain ⟨t₁, x₁, -, h₁, h₂, hσ⟩ := exists_trans_of_resp hR h
    exact ⟨t₁, x₁, h₁, h₂, hσ⟩
  refine ⟨⟨?_, ⟨k, ?_⟩, ?_, ?_⟩, ?_⟩
  · -- EIC-Termination
    intro p hp j
    obtain ⟨t₁, x₁, h₁, -, hσ⟩ := hreach p hp j
    obtain ⟨v, hv⟩ := resp_at_trans hval h₁ hσ
    exact ⟨v, t₁, hv⟩
  · -- EIC-Integrity from the EC agreement index on
    intro ℓ hℓ p v v' t t' h h'
    obtain ⟨h0, x, hσ, hx⟩ := count_eq_of_resp hval hagr hℓ h
    obtain ⟨h0', x', hσ', hx'⟩ := count_eq_of_resp hval hagr hℓ h'
    have := trans_unique (Dr := driver inp) (r := r) p (h0.trans h0'.symm)
      (by rw [trans_of_input hσ h0, h0]) (by rw [trans_of_input hσ' h0', h0'])
    subst this
    exact ⟨rfl, resp_fun h h'⟩
  · -- EIC-Agreement among correct processes
    intro p q ℓ hp hq hinf
    obtain ⟨tp, -, -, hp2, -⟩ := hreach p hp (max k ℓ)
    obtain ⟨tq, -, -, hq2, -⟩ := hreach q hq (max k ℓ)
    obtain ⟨t, ht, v, v', hne, hcp, hcq⟩ := hinf (max tp tq + 1)
    have hnp : max k ℓ + 2 ≤ (driver inp).n r p t := hp2 ▸ n_mono p (by omega)
    have hnq : max k ℓ + 2 ≤ (driver inp).n r q t := hq2 ▸ n_mono q (by omega)
    have hlp := length_dat hval p t
    have hlq := length_dat hval q t
    have hcp' := current_dat hval p t ℓ (by omega)
    have hcq' := current_dat hval q t ℓ (by omega)
    have e1 := ECHist.Current.unique (fun _ _ _ => resp_fun) hcp hcp'
    have e2 := ECHist.Current.unique (fun _ _ _ => resp_fun) hcq hcq'
    have key : ((driver inp).dat r p t)[ℓ]? = ((driver inp).dat r q t)[ℓ]? := by
      rcases dat_spec (inp := inp) (r := r) p t with ⟨h1, -⟩ | ⟨-, t₁, -, hr₁⟩
      · omega
      rcases dat_spec (inp := inp) (r := r) q t with ⟨h1, -⟩ | ⟨-, t₂, -, hr₂⟩
      · omega
      rcases le_total ((driver inp).n r p t) ((driver inp).n r q t) with hle | hle
      · have hpre := prefix_of_resp hval hagr ((driver inp).n r q t - (driver inp).n r p t) ((driver inp).n r p t - 2) (by omega) p q _ _
          t₁ t₂ hr₁ (by rw [show (driver inp).n r p t - 2 + ((driver inp).n r q t - (driver inp).n r p t) = (driver inp).n r q t - 2 by omega]; exact hr₂)
        exact getElem?_eq_of_prefix hpre (by omega)
      · have hpre := prefix_of_resp hval hagr ((driver inp).n r p t - (driver inp).n r q t) ((driver inp).n r q t - 2) (by omega) q p _ _
          t₂ t₁ hr₂ (by rw [show (driver inp).n r q t - 2 + ((driver inp).n r p t - (driver inp).n r q t) = (driver inp).n r p t - 2 by omega]; exact hr₁)
        exact (getElem?_eq_of_prefix hpre (by omega)).symm
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at key
    exact hne (e1.trans ((Option.some.inj key).trans e2.symm))
  · -- EIC-Validity
    intro p ℓ v t h
    obtain ⟨c, x, -, hσ, -, hx, -⟩ := app_resp_iff.1 h
    obtain ⟨q, t', ht', hi⟩ := hval p c x t hσ
    obtain ⟨q', t'', ht'', hi'⟩ := entry_of_inv hval c q x t' hi ℓ v hx
    exact ⟨q', t'', by omega, hi'⟩
  · -- the usage assumption of EIC is respected by the folded application
    refine ⟨fun p j v v' t t' h h' => ?_, fun p j v t h => ?_, fun p j v t h hfirst => ?_⟩
    · obtain ⟨h0, h1, rfl⟩ := app_inv_iff.1 h
      obtain ⟨h0', h1', rfl⟩ := app_inv_iff.1 h'
      exact ⟨trans_unique (Dr := driver inp) (r := r) p (h0.trans h0'.symm) (by omega)
        (by omega), rfl⟩
    · obtain ⟨h0, h1, -⟩ := app_inv_iff.1 h
      obtain ⟨x, hσ, -⟩ := trans_succ h0 h1
      obtain ⟨v', hv'⟩ := resp_at_trans hval h0 hσ
      refine ⟨v', hv', fun t' v'' ht' hr => ?_⟩
      obtain ⟨c, x', hc, hσ', hle, -⟩ := app_resp_iff.1 hr
      have := n_mono (Dr := driver inp) (r := r) p ht'.le
      have := trans_unique (Dr := driver inp) (r := r) p (show (driver inp).n r p t' = (driver inp).n r p t by omega)
        (by rw [trans_of_input hσ' hc, hc]) (by omega)
      omega
    · obtain ⟨c, x, hc, hσ, hle, -⟩ := app_resp_iff.1 h
      rcases Nat.lt_or_eq_of_le hle with hlt | rfl
      · exfalso
        obtain ⟨t₁, -, ht₁, h₁, h₂⟩ := exists_trans (Dr := driver inp) (r := r) p (Nat.zero_le t)
          (m := j + 1) (by simp) (by omega)
        obtain ⟨x₁, hσ₁, -⟩ := trans_succ h₁ h₂
        obtain ⟨v₁, hv₁⟩ := resp_at_trans hval h₁ hσ₁
        exact hfirst t₁ v₁ ht₁ hv₁
      · exact ⟨_, app_inv_iff.2 ⟨hc, trans_of_input hσ hc, rfl⟩⟩

end Alg6

end Podc.WeakestFDEventualConsistency
