import Papers.PODC2015.CrashConsensusDigraph.SyncModel

/-!
# The agreement argument of Algorithm Min-Max (proof of Theorem 3), abstractly

We analyse an arbitrary binary trajectory `x : ℕ → V → Bool` (`x r u` = value of `u` after `r`
rounds) that follows the Min/Max update rule in a window of `(2f + 2)·D` rounds, split into
`2f + 2` phases of `D` rounds; even phases (`0, 2, …`, the paper's phases `p = 1, 3, …`) are Max
phases, odd ones are Min phases. This is used both for Algorithm Min-Max (`MinMax.lean`) and for
the INNER-LOOP of Algorithm MVC (`MVC.lean`, Claim 2), which carries extra data.

For binary values, "set `v` to the maximum (minimum) of the received values, including one's
own" is the *absorbing rule* `AbsStep … a` with absorbing value `a = true` (`a = false`): the new
value is `a` iff the node or some node whose message it received had `a`.

Main result (`minmax_core`): if `G` satisfies `f` CT node connectivity and `D` bounds the
fault-tolerant diameter, then after the window all nodes that have not crashed hold the same
value. Proof as in the paper: some pair of consecutive phases `2k, 2k + 1` contains no crash
(`exists_clean_pair`, pigeonhole over the `f + 1` disjoint pairs — so the clean pair is always a
Max phase followed by a Min phase, no "WLOG" needed); let `F` be the nodes crashed before it.
Case I: some root of `G_F` holds `1` — it floods `1` in the Max phase (`spread`). Case II: all
roots hold `0` — they keep `0` during the Max phase (`roots_keep`; the roots form the source
component, which has no incoming edges in `G_F`) and flood `0` in the Min phase. Afterwards
agreement is preserved (`unanimity`).
-/

open Finset

-- CSLib candidate (synchronous crash-prone message passing on digraphs)

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open AsyncApproxBCDirected

variable {V : Type*} [DecidableEq V] {G : Digraph V} {adv : Adversary V}

/-- Round `r` of the trajectory `x` follows the absorbing rule with absorbing value `a`
(a Max round for `a = true`, a Min round for `a = false`). -/
def AbsStep (G : Digraph V) (adv : Adversary V) (x : ℕ → V → Bool) (r : ℕ) (a : Bool) : Prop :=
  ∀ w, x (r + 1) w = a ↔ (x r w = a ∨ ∃ u, Delivers G adv r u w ∧ x r u = a)

/-- The type of the phase containing round `r` of a window starting at `r₀` with phases of
length `D`: `true` (Max) for even phases, `false` (Min) for odd phases. -/
def phaseVal (D r₀ r : ℕ) : Bool := (r - r₀) / D % 2 == 0

theorem phaseVal_even {D r₀ k j : ℕ} (hj : j < D) : phaseVal D r₀ (r₀ + 2 * k * D + j) = true := by
  have hD : 0 < D := by omega
  simp only [phaseVal, beq_iff_eq]
  rw [show r₀ + 2 * k * D + j - r₀ = D * (2 * k) + j by ring_nf; omega, Nat.mul_add_div hD,
    Nat.div_eq_of_lt hj]
  omega

theorem phaseVal_odd {D r₀ k j : ℕ} (hj : j < D) :
    phaseVal D r₀ (r₀ + 2 * k * D + D + j) = false := by
  have hD : 0 < D := by omega
  simp only [phaseVal, beq_eq_false_iff_ne, ne_eq]
  rw [show r₀ + 2 * k * D + D + j - r₀ = D * (2 * k + 1) + j by ring_nf; omega,
    Nat.mul_add_div hD, Nat.div_eq_of_lt hj]
  omega

variable {x : ℕ → V → Bool}

theorem AbsStep.sticky {r : ℕ} {a : Bool} (h : AbsStep G adv x r a) {w : V} (hw : x r w = a) :
    x (r + 1) w = a := (h w).mpr (Or.inl hw)

/-- **Agreement is preserved**: if all nodes alive at `r₁` hold `c`, they keep holding `c`. -/
theorem unanimity {r₁ r₂ : ℕ} (hstep : ∀ r, r₁ ≤ r → r < r₂ → ∃ a, AbsStep G adv x r a)
    {c : Bool} (h : ∀ u, adv.Alive r₁ u → x r₁ u = c) :
    ∀ r, r₁ ≤ r → r ≤ r₂ → ∀ u, adv.Alive r u → x r u = c := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact fun _ => h
  | succ r hr ih =>
    intro hr2 u hu
    obtain ⟨a, ha⟩ := hstep r hr (by omega)
    have hxu : x r u = c := ih (by omega) u hu.of_succ
    have hdel : ∀ u', Delivers G adv r u' u → x r u' = c := fun u' hd => ih (by omega) u' hd.alive
    have key := ha u
    rw [hxu] at key
    by_cases hca : c = a
    · subst hca; exact key.mpr (Or.inl rfl)
    · have : x (r + 1) u ≠ a := fun h' => by
        rcases key.mp h' with h'' | ⟨u', hd, hu'⟩
        · exact hca h''
        · exact hca ((hdel u' hd).symm.trans hu')
      cases c <;> cases a
      · exact absurd rfl hca
      · simpa using this
      · simpa using this
      · exact absurd rfl hca

/-- **Flooding from a root** (Case I of the proof of Theorem 3): in a phase of `D` rounds with
absorbing value `a` during which no node outside `F` crashes, a root of `G_F` holding `a` at the
start makes every node of `G_F` hold `a` at the end. -/
theorem spread {f D : ℕ} (hD : FTDiamLE G f D) {F : Finset V} (hF : F.card ≤ f) {s : V}
    (hs : IsRoot G F s) (ps : ℕ) (a : Bool) (hstep : ∀ k < D, AbsStep G adv x (ps + k) a)
    (hal : ∀ u, u ∉ F → adv.Alive (ps + D) u) (hx : x ps s = a) :
    ∀ v, v ∉ F → x (ps + D) v = a := by
  have key : ∀ k ≤ D, ∀ v, ReachesWithin G F k s v → x (ps + k) v = a := by
    intro k
    induction k with
    | zero => intro _ v hv; rw [← hv.zero_eq]; simpa using hx
    | succ k ih =>
      intro hk v hv
      have hst := hstep k (by omega)
      rw [← Nat.add_assoc]
      cases hv with
      | refl _ h => exact hst.sticky (ih (by omega) s (.refl k hs.1))
      | tail hb e hc =>
        rename_i b
        have hxb := ih (by omega) b hb
        refine (hst v).mpr (Or.inr ⟨b, delivers_of_alive ?_ e, hxb⟩)
        exact (hal b hb.notMem_right).mono (by omega)
  intro v hv
  exact key D le_rfl v (hD F hF s hs v hv)

/-- **Roots keep their value** (Case II of the proof of Theorem 3): if all roots of `G_F` hold
`!a` at the start of a phase with absorbing value `a`, and the nodes of `F` have crashed before
the phase, then the roots still hold `!a` at the end of the phase. -/
theorem roots_keep {D : ℕ} {F : Finset V} (ps : ℕ) (a : Bool)
    (hstep : ∀ k < D, AbsStep G adv x (ps + k) a) (hdead : ∀ u ∈ F, ¬ adv.Alive ps u)
    (h0 : ∀ s, IsRoot G F s → x ps s = !a) :
    ∀ k ≤ D, ∀ s, IsRoot G F s → x (ps + k) s = !a := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk w hw
    have hst := hstep k (by omega)
    have hne : x (ps + (k + 1)) w ≠ a := by
      rw [← Nat.add_assoc]
      intro h'
      rcases (hst w).mp h' with h'' | ⟨u, hd, hu⟩
      · rw [ih (by omega) w hw] at h''; cases a <;> simp at h''
      · have huF : u ∉ F := fun hu' => hdead u hu' (hd.alive.mono (by omega))
        rw [ih (by omega) u (hw.of_adj hd.adj huF)] at hu
        cases a <;> simp at hu
    cases a <;> simpa using hne

/-- **Pigeonhole**: among the `f + 1` disjoint pairs of phases `(2k, 2k + 1)`, `k ≤ f`, of a
window starting at `r₀`, some pair contains no crash round. -/
theorem exists_clean_pair {f : ℕ} (hadm : adv.Admissible f) (r₀ D : ℕ) :
    ∃ k, k ≤ f ∧ ∀ u c, adv.crash u = some c → ¬ (r₀ + 2 * k * D ≤ c ∧ c < r₀ + 2 * k * D + 2 * D) := by
  classical
  obtain ⟨F₀, hF₀, hmem⟩ := hadm
  by_contra hcon
  push Not at hcon
  have h' : ∀ k : Fin (f + 1), ∃ u c, adv.crash u = some c ∧ r₀ + 2 * k * D ≤ c ∧
      c < r₀ + 2 * k * D + 2 * D := fun k => hcon k (by omega)
  choose g c hg using h'
  have hinj : Set.InjOn g (univ : Finset (Fin (f + 1))) := by
    intro k _ k' _ hkk
    have hc : c k = c k' := by
      have h1 := (hg k).1
      have h2 := (hg k').1
      rw [hkk, h2] at h1
      exact (Option.some_injective _ h1).symm
    by_contra hne
    have hk := hg k
    have hk' := hg k'
    rw [hc] at hk
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have : 2 * (k : ℕ) * D + 2 * D ≤ 2 * k' * D := by
        have := Nat.mul_le_mul_right D (show 2 * (k : ℕ) + 2 ≤ 2 * k' by omega); linarith
      omega
    · have : 2 * (k' : ℕ) * D + 2 * D ≤ 2 * k * D := by
        have := Nat.mul_le_mul_right D (show 2 * (k' : ℕ) + 2 ≤ 2 * k by omega); linarith
      omega
  have := Finset.card_le_card_of_injOn g (fun k _ => hmem (g k) (c k) (hg k).1) hinj
  simp at this
  omega

/-- **Agreement of the Min/Max phases** (the core of Theorem 3 and of Claim 2): if `G` satisfies
`f` CT node connectivity, `D` bounds the fault-tolerant diameter, at most `f` nodes crash and the
trajectory `x` follows the Min/Max rule in the `2f + 2` phases of the window starting at `r₀`,
then at the end of the window all nodes that have not crashed hold the same value. -/
theorem minmax_core [Fintype V] {f D : ℕ} (hG : CTConn G f) (hD : FTDiamLE G f D)
    (hadm : adv.Admissible f) (r₀ : ℕ)
    (hstep : ∀ r, r₀ ≤ r → r < r₀ + (2 * f + 2) * D → AbsStep G adv x r (phaseVal D r₀ r)) :
    ∃ c, ∀ u, adv.Alive (r₀ + (2 * f + 2) * D) u → x (r₀ + (2 * f + 2) * D) u = c := by
  classical
  obtain ⟨k, hk, hclean⟩ := exists_clean_pair hadm r₀ D
  set ps := r₀ + 2 * k * D with hps
  set E := r₀ + (2 * f + 2) * D with hE
  have hkE : ps + 2 * D ≤ E := by
    have := Nat.mul_le_mul_right D (show 2 * k + 2 ≤ 2 * f + 2 by omega)
    simp only [hps, hE]; nlinarith
  set F : Finset V := univ.filter fun u => ¬ adv.Alive ps u
  have hFcard : F.card ≤ f := by
    obtain ⟨F₀, hF₀, hmem⟩ := hadm
    refine le_trans (card_le_card fun u hu => ?_) hF₀
    have hu' : ¬ adv.Alive ps u := (Finset.mem_filter.mp hu).2
    simp only [Adversary.Alive] at hu'
    push Not at hu'
    obtain ⟨c, hc, -⟩ := hu'
    exact hmem u c hc
  have hdead : ∀ u ∈ F, ¬ adv.Alive ps u := fun u hu => (Finset.mem_filter.mp hu).2
  have halive : ∀ u, u ∉ F → adv.Alive (ps + 2 * D) u := by
    intro u hu c hc
    have h1 : ps ≤ c := by
      by_contra h1
      exact hu (Finset.mem_filter.mpr ⟨mem_univ _, fun h2 => h1 (h2 c hc)⟩)
    have := hclean u c hc
    omega
  have hst : ∀ r, r₀ ≤ r → r < E → ∃ a, AbsStep G adv x r a := fun r h1 h2 => ⟨_, hstep r h1 h2⟩
  by_cases hne : ∃ v, v ∉ F
  swap
  · refine ⟨true, fun u hu => absurd (hu.mono (by omega : ps ≤ E)) ?_⟩
    push Not at hne
    exact hdead u (hne u)
  obtain ⟨s, hs⟩ := hG F hFcard hne
  have hroot : IsRoot G F s := hs
  have hmax : ∀ j < D, AbsStep G adv x (ps + j) true := fun j hj => by
    have := hstep (ps + j) (by omega) (by omega)
    rwa [phaseVal_even hj] at this
  have hmin : ∀ j < D, AbsStep G adv x (ps + D + j) false := fun j hj => by
    have := hstep (ps + D + j) (by omega) (by omega)
    rwa [phaseVal_odd hj] at this
  by_cases h1 : ∃ s', IsRoot G F s' ∧ x ps s' = true
  · -- Case I
    obtain ⟨s', hs', hxs'⟩ := h1
    have hall := spread hD hFcard hs' ps true hmax
      (fun u hu => (halive u hu).mono (by omega)) hxs'
    refine ⟨true, unanimity (r₁ := ps + D) (r₂ := E) (fun r h1 h2 => hst r (by omega) h2) ?_ E
      (by omega) le_rfl⟩
    intro u hu
    exact hall u fun huF => hdead u huF (hu.mono (by omega))
  · -- Case II
    push Not at h1
    have hkeep := roots_keep (D := D) ps true hmax hdead
      (fun s' hs' => by simpa using h1 s' hs')
    have hall := spread hD hFcard hroot (ps + D) false hmin
      (fun u hu => by simpa [Nat.add_assoc, two_mul] using halive u hu)
      (by simpa using hkeep D le_rfl s hroot)
    refine ⟨false, unanimity (r₁ := ps + D + D) (r₂ := E)
      (fun r h1 h2 => hst r (by omega) h2) ?_ E (by omega) le_rfl⟩
    intro u hu
    exact hall u fun huF => hdead u huF (hu.mono (by omega))

end CrashConsensusDigraph
