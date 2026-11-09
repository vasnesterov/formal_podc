import Papers.PODC2012.TVGWaitingExpressivity.BoundedWait
import Papers.PODC2012.TVGWaitingExpressivity.FromDFA
import Papers.PODC2012.TVGWaitingExpressivity.Wait
import Mathlib.Computability.Halting

/-!
# Computable versions of the results

The paper requires the presence `ρ` and latency `ζ` of a TVG to be computable functions; the main
files prove the constructions for arbitrary `ρ`, `ζ`. Here we restrict to TVGs on `Fin n` over
`Fin q` with `TVG.IsComputable` (presence a `ComputablePred`, latency `Computable`).

* `numDec`, `phiDec`: a primitive recursive decoder of base-`b` numerals; `phiInv_eq_phiDec`
  shows the classical `φ⁻¹` agrees with it (including the junk value `ε` off the range of `φ`).
* Theorem 3.1: `G2d_isComputable`, `G2_isComputable` (for decidable `L`),
  `theorem_3_1_computable`, `computable_subset_LwaitAtMostComp`.
* Theorem 5.1: `TVGAutomaton.relabel` (renaming nodes along an equivalence preserves every
  language), `dilate_isComputable`, `withPauseFin_isComputable`, `theorem_5_1_computable`.
* Theorem 4.1: `isRegular_mem_LwaitComp` and, with `Lwait_isRegular` (file `Wait`),
  `theorem_4_1_computable : LwaitComp q = {L | L.IsRegular}`.
* Converse of Theorem 3.1: without waiting, the reachable configurations `(node, time)` after
  reading `w` form a finite, computable list (`runCfg`), so `L_nowait` of a computable TVG is
  decidable (`computablePred_mem_Lnowait`). Hence `LnowaitComp_eq_computable` and
  `LwaitAtMostComp_eq_computable`: with computable `ρ`, `ζ`, `𝓛_nowait = 𝓛_wait[d]` is exactly
  the class of decidable languages.
-/

namespace Podc.TVGWaitingExpressivity

open TVG TVGAutomaton

/-! ### A computable decoder of base-`b` numerals -/

section Decoder

variable (c q : ℕ)

/-- Decoder of the base-`(c + 2)` numerals `1.w`: `numDec c q t = some w` iff
`numeral (c + 2) w = t`. -/
def numDec (t : ℕ) : Option (List (Fin q)) :=
  if t ≤ 1 then (if t = 1 then some [] else none) else
    ((List.finRange q)[t % (c + 2)]?).bind fun a => (numDec (t / (c + 2))).map (· ++ [a])
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- One step of `numDec`, reading the previously computed values from a table. -/
def numDecStep (l : List (Option (List (Fin q)))) : Option (List (Fin q)) :=
  if l.length ≤ 1 then (if l.length = 1 then some [] else none) else
    ((List.finRange q)[l.length % (c + 2)]?).bind fun a =>
      ((l[l.length / (c + 2)]?).bind id).map (· ++ [a])

theorem numDecStep_range (n : ℕ) :
    numDecStep c q ((List.range n).map (numDec c q)) = numDec c q n := by
  rw [numDec, numDecStep]
  simp only [List.length_map, List.length_range]
  by_cases h1 : n ≤ 1
  · simp only [h1, ite_true]
  · simp only [h1, ite_false]
    rw [List.getElem?_map, List.getElem?_range (Nat.div_lt_self (by omega) (by omega))]
    rfl

theorem primrec_numDec : Primrec (numDec c q) := by
  have hstep : Primrec (numDecStep c q) := by
    unfold numDecStep
    refine Primrec.ite (PrimrecRel.comp Primrec.nat_le Primrec.list_length (Primrec.const 1))
      (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.list_length (Primrec.const 1))
        (Primrec.const _) (Primrec.const _)) ?_
    refine Primrec.option_bind ?_ ?_
    · exact Primrec.list_getElem?.comp (Primrec.const _)
        (Primrec.nat_mod.comp Primrec.list_length (Primrec.const _))
    · refine Primrec.option_map ?_ ?_
      · exact Primrec.option_bind (Primrec.list_getElem?.comp Primrec.fst
          (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const _)))
          (Primrec.snd.to₂)
      · exact (Primrec.list_append.comp Primrec.snd
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) (Primrec.const []))).to₂
  have := Primrec.nat_strong_rec (fun (_ : Unit) n => numDec c q n)
    (g := fun _ l => some (numDecStep c q l))
    (Primrec.option_some.comp (hstep.comp Primrec.snd)).to₂
    (fun _ n => by rw [numDecStep_range])
  exact this.comp (Primrec.const ()) Primrec.id

theorem getElem?_finRange_eq_some {r : ℕ} {a : Fin q} :
    (List.finRange q)[r]? = some a ↔ (a : ℕ) = r := by
  simp only [List.getElem?_eq_some_iff, List.length_finRange, List.getElem_finRange]
  constructor
  · rintro ⟨h, rfl⟩; rfl
  · rintro rfl; exact ⟨a.2, rfl⟩

theorem numDec_numeral (hq : q ≤ c + 2) (w : List (Fin q)) :
    numDec c q (numeral (c + 2) w) = some w := by
  induction w using List.reverseRecOn with
  | nil => rw [numDec]; simp
  | append_singleton w a ih =>
    have h1 := numeral_pos (b := c + 2) (by omega) w
    have ha : (a : ℕ) < c + 2 := lt_of_lt_of_le a.2 hq
    rw [numDec, numeral_append_singleton]
    have hmod : ((c + 2) * numeral (c + 2) w + a) % (c + 2) = a := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha]
    have hdiv : ((c + 2) * numeral (c + 2) w + a) / (c + 2) = numeral (c + 2) w := by
      rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt ha, Nat.add_zero]
    have hle : ¬ (c + 2) * numeral (c + 2) w + a ≤ 1 := by nlinarith
    simp only [hle, ite_false]
    rw [hmod, hdiv, ih, (getElem?_finRange_eq_some q).2 rfl]
    rfl

theorem numeral_of_numDec {t : ℕ} {w : List (Fin q)} (h : numDec c q t = some w) :
    numeral (c + 2) w = t := by
  induction t using Nat.strong_induction_on generalizing w with
  | _ t ih =>
    rw [numDec] at h
    split_ifs at h with h1 h2
    · cases h; subst h2; rfl
    · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [getElem?_finRange_eq_some] at ha
      rw [numeral_append_singleton, ih _ (Nat.div_lt_self (by omega) (by omega)) hw', ha]
      exact Nat.div_add_mod t (c + 2)

/-- The computable inverse of `φ` in base `c + 2`. -/
def phiDec (t : ℕ) : Option (List (Fin q)) :=
  if t = 0 then some [] else if t = 1 then none else numDec c q t

theorem primrec_phiDec : Primrec (phiDec c q) :=
  Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const 0)) (Primrec.const _)
    (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const 1)) (Primrec.const _)
      (primrec_numDec c q))

theorem phiDec_eq_some_iff (hq : q ≤ c + 2) {t : ℕ} {w : List (Fin q)} :
    phiDec c q t = some w ↔ phi (c + 2) w = t := by
  constructor
  · intro h
    unfold phiDec at h
    split_ifs at h with ht ht1
    · cases h; simp [ht]
    · have := numeral_of_numDec c q h
      have hw : w ≠ [] := by rintro rfl; simp at this; omega
      rw [phi_of_ne_nil hw, this]
  · rintro rfl
    by_cases hw : w = []
    · subst hw; rfl
    · have := numeral_pos (b := c + 2) (by omega) w
      have h2 : 2 ≤ numeral (c + 2) w := by
        obtain ⟨w, a, rfl⟩ := (List.eq_nil_or_concat w).resolve_left hw
        rw [List.concat_eq_append]
        rw [numeral_append_singleton]
        have := numeral_pos (b := c + 2) (by omega) w
        nlinarith
      rw [phi_of_ne_nil hw, phiDec]
      simp only [show numeral (c + 2) w ≠ 0 by omega, show numeral (c + 2) w ≠ 1 by omega,
        ite_false]
      exact numDec_numeral c q hq w

theorem phiInv_eq_phiDec (hq : q ≤ c + 2) (t : ℕ) : phiInv (c + 2) t = (phiDec c q t).getD [] := by
  cases h : phiDec c q t with
  | none =>
    have : ¬ ∃ w, phi (q := q) (c + 2) w = t := by
      rintro ⟨w, hw⟩; rw [← phiDec_eq_some_iff c q hq, h] at hw; cases hw
    simp [phiInv, this]
  | some w =>
    rw [phiDec_eq_some_iff c q hq] at h
    subst h
    exact phiInv_phi (by omega) hq w

theorem mem_range_phi_iff (hq : q ≤ c + 2) (t : ℕ) :
    t ∈ Set.range (phi (q := q) (c + 2)) ↔ (phiDec c q t).isSome := by
  rw [Option.isSome_iff_exists]
  simp [phiDec_eq_some_iff c q hq]

end Decoder

/-! ### Helpers -/

-- CSLib candidate
/-- A predicate is computable if it agrees with a computable Boolean function. -/
theorem computablePred_of_bool {α : Type*} [Primcodable α] {p : α → Prop} {f : α → Bool}
    (hf : Computable f) (h : ∀ a, p a ↔ f a = true) : ComputablePred p :=
  ComputablePred.computable_iff.2 ⟨f, hf, funext fun a => propext (h a)⟩

theorem primrec_numeral (b q : ℕ) : Primrec (numeral (q := q) b) := by
  refine (Primrec.list_foldl (f := fun w : List (Fin q) => w) Primrec.id (Primrec.const 1)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const b) (Primrec.fst.comp Primrec.snd))
      (Primrec.fin_val.comp (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun w => ?_
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    simp only [List.foldl_append, numeral_append_singleton] at ih ⊢
    rw [ih]; rfl

/-! ### Relabelling the nodes of a TVG-automaton -/

section Relabel

variable {V W α : Type*}

-- CSLib candidate
/-- Relabel the nodes of a TVG-automaton along an equivalence `σ : V ≃ W`. -/
def TVGAutomaton.relabel (σ : V ≃ W) (A : TVGAutomaton V α) : TVGAutomaton W α where
  present e t := A.present (σ.symm e.1, e.2.1, σ.symm e.2.2) t
  latency e t := A.latency (σ.symm e.1, e.2.1, σ.symm e.2.2) t
  init := {x | σ.symm x ∈ A.init}
  accept := {x | σ.symm x ∈ A.accept}
  start := A.start

theorem TVGAutomaton.relabel_journey_iff (σ : V ≃ W) (A : TVGAutomaton V α) (P : PauseRule)
    (u : W) (t : ℕ) (w : List α) (v : W) (t' : ℕ) :
    (A.relabel σ).Journey P u t w v t' ↔ A.Journey P (σ.symm u) t w (σ.symm v) t' := by
  induction w generalizing u t with
  | nil =>
    simp only [journey_nil_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by rw [h1], h2⟩, fun ⟨h1, h2⟩ => ⟨σ.symm.injective h1, h2⟩⟩
  | cons a w ih =>
    simp only [journey_cons_iff]
    constructor
    · rintro ⟨v', t₁, hp, hpres, hj⟩
      exact ⟨σ.symm v', t₁, hp, hpres, (ih _ _).1 hj⟩
    · rintro ⟨v', t₁, hp, hpres, hj⟩
      refine ⟨σ v', t₁, hp, ?_, (ih _ _).2 ?_⟩
      · simpa [relabel] using hpres
      · simpa [relabel] using hj

-- CSLib candidate
/-- Relabelling the nodes does not change the language, whatever the pause rule. -/
theorem TVGAutomaton.relabel_lang (σ : V ≃ W) (A : TVGAutomaton V α) (P : PauseRule) :
    (A.relabel σ).lang P = A.lang P := by
  ext w
  simp only [lang]
  show (∃ s, σ.symm s ∈ A.init ∧ ∃ f, σ.symm f ∈ A.accept ∧ ∃ t', _) ↔ _
  simp only [relabel_journey_iff]
  constructor
  · rintro ⟨s, hs, f, hf, t', h⟩; exact ⟨_, hs, _, hf, t', h⟩
  · rintro ⟨s, hs, f, hf, t', h⟩
    exact ⟨σ s, by simpa using hs, σ f, by simpa using hf, t', by simpa [relabel] using h⟩

end Relabel

/-! ### Theorem 3.1 with computable `ρ` and `ζ` -/

section NoWait

variable {q : ℕ}

/-- If `L` is decidable, the TVG `G_{2,d}` (and thus `G₂ = G_{2,0}`) has computable presence and
latency. -/
theorem G2d_isComputable {b : ℕ} (hb : 2 ≤ b) (hq : q ≤ b) (d : ℕ) {L : Language (Fin q)}
    (hL : ComputablePred (· ∈ L)) : (G2d b d L).IsComputable := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
  obtain ⟨inst, hL⟩ := hL
  have hdec : Primrec fun p : (Fin 3 × Fin q × Fin 3) × ℕ => phiDec c q (p.2 / (d + 1)) :=
    (primrec_phiDec c q).comp (Primrec.nat_div.comp Primrec.snd (Primrec.const _))
  have hword : Primrec fun p : (Fin 3 × Fin q × Fin 3) × ℕ =>
      (phiDec c q (p.2 / (d + 1))).getD [] ++ [p.1.2.1] :=
    Primrec.list_append.comp (Primrec.option_getD.comp hdec (Primrec.const _))
      (Primrec.list_cons.comp ((Primrec.dom_finite fun e : Fin 3 × Fin q × Fin 3 => e.2.1).comp
        Primrec.fst) (Primrec.const []))
  let g : (Fin 3 × Fin q × Fin 3) × Bool → Bool := fun x =>
    decide (x.1.2.2 ≠ 0) && (decide (x.1.2.2 = 1) == x.2)
  have hg : Computable fun p : (Fin 3 × Fin q × Fin 3) × ℕ =>
      g (p.1, decide ((phiDec c q (p.2 / (d + 1))).getD [] ++ [p.1.2.1] ∈ L)) :=
    (Primrec.dom_finite g).to_comp.comp (Computable.pair Computable.fst (hL.comp hword.to_comp))
  have hf : Computable fun p : (Fin 3 × Fin q × Fin 3) × ℕ =>
      ((phiDec c q (p.2 / (d + 1))).isSome &&
        g (p.1, decide ((phiDec c q (p.2 / (d + 1))).getD [] ++ [p.1.2.1] ∈ L))) :=
    Primrec.and.to_comp.comp (Primrec.option_isSome.comp hdec).to_comp hg
  constructor
  · refine computablePred_of_bool hf ?_
    rintro ⟨e, t⟩
    show (_ ≠ _ ∧ t / (d + 1) ∈ Set.range (phi (q := q) (c + 2)) ∧
      (_ ↔ phiInv (c + 2) (t / (d + 1)) ++ [e.2.1] ∈ L)) ↔ _
    rw [mem_range_phi_iff c q hq, phiInv_eq_phiDec c q hq]
    cases (phiDec c q (t / (d + 1))).isSome <;> simp [g]
  · have hl : Computable fun p : (Fin 3 × Fin q × Fin 3) × ℕ =>
        (d + 1) * numeral (c + 2) ((phiDec c q (p.2 / (d + 1))).getD [] ++ [p.1.2.1]) - p.2 :=
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const _)
        ((primrec_numeral _ _).comp hword)) Primrec.snd).to_comp
    refine hl.of_eq ?_
    rintro ⟨e, t⟩
    show _ = (d + 1) * phi (c + 2) (phiInv (c + 2) (t / (d + 1)) ++ [e.2.1]) - t
    rw [phiInv_eq_phiDec c q hq, phi_of_ne_nil (by simp)]

theorem G2_isComputable {b : ℕ} (hb : 2 ≤ b) (hq : q ≤ b) {L : Language (Fin q)}
    (hL : ComputablePred (· ∈ L)) : (G2 b L).IsComputable := by
  rw [G2_eq_G2d]; exact G2d_isComputable hb hq 0 hL

/-- **Theorem 3.1** of [CFGSY'12], with computable `ρ` and `ζ` as in the paper: every decidable
language over `Fin q` is `L_nowait` of a computable 3-node TVG. -/
theorem theorem_3_1_computable (q : ℕ) :
    {L : Language (Fin q) | ComputablePred (· ∈ L)} ⊆ LnowaitComp q :=
  fun L hL => ⟨3, G2 (q + 2) L, G2_isComputable (by omega) (by omega) hL,
    theorem_3_1 (by omega) (by omega) L⟩

/-- Every decidable language over `Fin q` is `L_wait[d]` of a computable 3-node TVG
(the construction `G_{2,d}` of the proof of Theorem 5.1). -/
theorem computable_subset_LwaitAtMostComp (q d : ℕ) :
    {L : Language (Fin q) | ComputablePred (· ∈ L)} ⊆ LwaitAtMostComp q d :=
  fun L hL => ⟨3, G2d (q + 2) d L, G2d_isComputable (by omega) (by omega) d hL,
    G2d_LwaitAtMost (by omega) (by omega) d L⟩

end NoWait

/-! ### Theorem 5.1 with computable `ρ` and `ζ` -/

section BoundedWait

variable {n q : ℕ}

/-- Time dilation preserves computability of `ρ` and `ζ`. -/
theorem dilate_isComputable (d : ℕ) {A : TVGAutomaton (Fin n) (Fin q)} (hA : A.IsComputable) :
    (dilate d A).IsComputable := by
  obtain ⟨⟨inst, hp⟩, hl⟩ := hA
  have hdiv : Computable fun p : (Fin n × Fin q × Fin n) × ℕ => (p.1, p.2 / (d + 1)) :=
    (Primrec.pair Primrec.fst (Primrec.nat_div.comp Primrec.snd (Primrec.const _))).to_comp
  constructor
  · refine computablePred_of_bool (f := fun p : (Fin n × Fin q × Fin n) × ℕ =>
      (p.2 % (d + 1) == 0) && @decide _ (inst (p.1, p.2 / (d + 1)))) ?_ ?_
    · exact Primrec.and.to_comp.comp
        (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const _))
          (Primrec.const 0)).to_comp (hp.comp hdiv)
    · rintro ⟨e, t⟩
      rw [Bool.and_eq_true, @decide_eq_true_iff _ (inst _)]
      simp [dilate, Nat.dvd_iff_mod_eq_zero]
  · exact (Primrec.nat_mul.to_comp.comp (Computable.const _) (hl.comp hdiv)).of_eq fun _ => rfl

/-- `withPause d A`, with nodes `Fin n × Fin (d + 1)` renamed to `Fin (n * (d + 1))`. -/
def withPauseFin (d : ℕ) (A : TVGAutomaton (Fin n) (Fin q)) :
    TVGAutomaton (Fin (n * (d + 1))) (Fin q) :=
  (withPause d A).relabel finProdFinEquiv

theorem withPauseFin_Lnowait (d : ℕ) (A : TVGAutomaton (Fin n) (Fin q)) :
    (withPauseFin d A).Lnowait = A.LwaitAtMost d := by
  rw [withPauseFin, Lnowait, relabel_lang]
  exact withPause_Lnowait d A

/-- Making the pauses explicit preserves computability of `ρ` and `ζ`. -/
theorem withPauseFin_isComputable (d : ℕ) {A : TVGAutomaton (Fin n) (Fin q)}
    (hA : A.IsComputable) : (withPauseFin d A).IsComputable := by
  obtain ⟨⟨inst, hp⟩, hl⟩ := hA
  let k : Fin (n * (d + 1)) × Fin q × Fin (n * (d + 1)) → (Fin n × Fin q × Fin n) × ℕ :=
    fun e => (((finProdFinEquiv.symm e.1).1, e.2.1, (finProdFinEquiv.symm e.2.2).1),
      ((finProdFinEquiv.symm e.1).2 : ℕ))
  have hg : Computable fun p : (Fin (n * (d + 1)) × Fin q × Fin (n * (d + 1))) × ℕ =>
      ((k p.1).1, p.2 + (k p.1).2) :=
    (Primrec.pair ((Primrec.dom_finite fun e => (k e).1).comp Primrec.fst)
      (Primrec.nat_add.comp Primrec.snd
        ((Primrec.dom_finite fun e => (k e).2).comp Primrec.fst))).to_comp
  constructor
  · exact computablePred_of_bool (hp.comp hg) fun x =>
      (@decide_eq_true_iff _ (inst ((k x.1).1, x.2 + (k x.1).2))).symm
  · exact (Primrec.nat_add.to_comp.comp
      ((Primrec.dom_finite fun e => (k e).2).to_comp.comp Computable.fst) (hl.comp hg)).of_eq
      fun _ => rfl

/-- **Theorem 5.1** of [CFGSY'12] for computable TVGs: `𝓛_wait[d] = 𝓛_nowait`. -/
theorem theorem_5_1_computable (q d : ℕ) : LwaitAtMostComp q d = LnowaitComp q := by
  ext L
  constructor
  · rintro ⟨n, A, hA, rfl⟩
    exact ⟨_, withPauseFin d A, withPauseFin_isComputable d hA, withPauseFin_Lnowait d A⟩
  · rintro ⟨n, A, hA, rfl⟩
    exact ⟨n, dilate d A, dilate_isComputable d hA, dilate_LwaitAtMost d A⟩

end BoundedWait

/-! ### Theorem 4.1 with computable `ρ` and `ζ` -/

section Regular

variable {q : ℕ}

/-- The static TVG of a DFA, with states renamed to `Fin n`. -/
noncomputable def ofDFAFin {σ : Type} [Fintype σ] (M : DFA (Fin q) σ) :
    TVGAutomaton (Fin (Fintype.card σ)) (Fin q) :=
  (ofDFA M).relabel (Fintype.equivFin σ)

theorem ofDFAFin_isComputable {σ : Type} [Fintype σ] (M : DFA (Fin q) σ) :
    (ofDFAFin M).IsComputable := by
  classical
  constructor
  · exact computablePred_of_bool
      ((Primrec.dom_finite fun e => decide ((ofDFAFin M).present e 0)).to_comp.comp Computable.fst)
      fun _ => (decide_eq_true_iff).symm
  · exact (Computable.const 0).of_eq fun _ => rfl

/-- Regular languages are accepted (with or without waiting) by computable TVGs: the first
inclusion of Theorem 4.1. -/
theorem isRegular_mem_LwaitComp {L : Language (Fin q)} (hL : L.IsRegular) : L ∈ LwaitComp q := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine ⟨_, ofDFAFin M, ofDFAFin_isComputable M, ?_⟩
  rw [ofDFAFin, Lwait, relabel_lang]
  exact ofDFA_Lwait M

/-- **Theorem 4.1** of [CFGSY'12] for computable TVGs: `𝓛_wait` is the class of regular
languages. -/
theorem theorem_4_1_computable (q : ℕ) : LwaitComp q = {L : Language (Fin q) | L.IsRegular} := by
  ext L
  constructor
  · rintro ⟨n, A, -, rfl⟩
    exact Lwait_isRegular A
  · exact isRegular_mem_LwaitComp

end Regular

/-! ### Converse: `L_nowait` of a computable TVG is decidable

Without waiting, the configurations `(node, time)` reachable after reading `w` from the start date
form a finite list, computed letter by letter. So the paper's "as powerful as a Turing machine"
is exact: `𝓛_nowait` (for computable `ρ`, `ζ`) is the class of decidable languages. -/

-- CSLib candidate
/-- `List.foldl` with a computable step function is computable. -/
theorem computable_list_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → σ × β → σ} (hf : Computable f) (hg : Computable g)
    (hh : Computable₂ h) : Computable fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  have hstep : Computable₂ fun (a : α) (p : ℕ × σ) =>
      (Option.casesOn ((f a)[p.1]?) p.2 fun b => h a (p.2, b) : σ) :=
    (Computable.option_casesOn (Computable.list_getElem?.comp (hf.comp Computable.fst)
      (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
      (hh.comp (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp (Computable.snd.comp Computable.fst))
          Computable.snd)).to₂).to₂
  refine (Computable.nat_rec (Computable.list_length.comp hf) hg hstep).of_eq fun a => ?_
  suffices H : ∀ i ≤ (f a).length, Nat.rec (motive := fun _ => σ) (g a)
      (fun y IH => (Option.casesOn ((f a)[y]?) IH fun b => h a (IH, b) : σ)) i =
      ((f a).take i).foldl (fun s b => h a (s, b)) (g a) by
    simpa using H _ le_rfl
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.take_add_one, List.foldl_append, ← ih (by omega)]
    show (Option.casesOn ((f a)[i]?) _ _ : σ) = _
    rw [List.getElem?_eq_getElem (by omega)]
    rfl

theorem mem_foldl_bif {β γ : Type*} (P : β → Bool) (F : β → γ) (y : γ) (L : List β)
    (acc : List γ) :
    y ∈ L.foldl (fun acc v => bif P v then acc ++ [F v] else acc) acc ↔
      y ∈ acc ∨ ∃ v ∈ L, P v = true ∧ y = F v := by
  induction L generalizing acc with
  | nil => simp
  | cons v L ih =>
    rw [List.foldl_cons, ih]
    cases hP : P v <;> simp [hP]
    aesop

theorem mem_foldl_of {β γ : Type*} (G : β → List γ → List γ) (R : β → γ → Prop) (y : γ)
    (hG : ∀ c acc, y ∈ G c acc ↔ y ∈ acc ∨ R c y) (l : List β) (acc : List γ) :
    y ∈ l.foldl (fun acc c => G c acc) acc ↔ y ∈ acc ∨ ∃ c ∈ l, R c y := by
  induction l generalizing acc with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih, hG]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem foldl_or_eq_true {β : Type*} (P : β → Bool) (l : List β) (b : Bool) :
    l.foldl (fun b y => b || P y) b = true ↔ b = true ∨ ∃ y ∈ l, P y = true := by
  induction l generalizing b with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons, ih]
    simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

section Converse

variable {n q : ℕ}

/-- The configurations reachable from the list `l` by reading the letter `a` without waiting,
for a TVG given by the Boolean presence `pr` and latency `lat`. -/
def stepCfg (pr : (Fin n × Fin q × Fin n) × ℕ → Bool) (lat : (Fin n × Fin q × Fin n) × ℕ → ℕ)
    (a : Fin q) (l : List (Fin n × ℕ)) : List (Fin n × ℕ) :=
  l.foldl (fun acc c => (List.finRange n).foldl (fun acc' v =>
    bif pr ((c.1, a, v), c.2) then acc' ++ [(v, c.2 + lat ((c.1, a, v), c.2))] else acc') acc) []

/-- The configurations reachable from `l` by reading the word `w` without waiting. -/
def runCfg (pr : (Fin n × Fin q × Fin n) × ℕ → Bool) (lat : (Fin n × Fin q × Fin n) × ℕ → ℕ)
    (w : List (Fin q)) (l : List (Fin n × ℕ)) : List (Fin n × ℕ) :=
  w.foldl (fun l a => stepCfg pr lat a l) l

theorem mem_stepCfg (pr : (Fin n × Fin q × Fin n) × ℕ → Bool)
    (lat : (Fin n × Fin q × Fin n) × ℕ → ℕ) (a : Fin q) (l : List (Fin n × ℕ)) (y : Fin n × ℕ) :
    y ∈ stepCfg pr lat a l ↔
      ∃ c ∈ l, ∃ v, pr ((c.1, a, v), c.2) = true ∧ y = (v, c.2 + lat ((c.1, a, v), c.2)) := by
  rw [stepCfg, mem_foldl_of _ (fun c y => ∃ v, pr ((c.1, a, v), c.2) = true ∧
    y = (v, c.2 + lat ((c.1, a, v), c.2))) y]
  · simp
  · intro c acc
    rw [mem_foldl_bif]
    simp

theorem mem_runCfg (A : TVG (Fin n) (Fin q)) {pr : (Fin n × Fin q × Fin n) × ℕ → Bool}
    {lat : (Fin n × Fin q × Fin n) × ℕ → ℕ} (hpr : ∀ x, pr x = true ↔ A.present x.1 x.2)
    (hlat : ∀ x, lat x = A.latency x.1 x.2) (w : List (Fin q)) (l : List (Fin n × ℕ))
    (y : Fin n × ℕ) :
    y ∈ runCfg pr lat w l ↔ ∃ c ∈ l, A.Journey noWait c.1 c.2 w y.1 y.2 := by
  induction w generalizing l with
  | nil =>
    simp only [runCfg, List.foldl_nil, journey_nil_iff]
    constructor
    · intro h; exact ⟨y, h, rfl, rfl⟩
    · rintro ⟨c, hc, h1, h2⟩; rwa [Prod.ext h1 h2]
  | cons a w ih =>
    simp only [runCfg, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [mem_stepCfg, journey_cons_iff, noWait, hpr, hlat]
    constructor
    · rintro ⟨_, ⟨c, hc, v, hv, rfl⟩, hj⟩
      exact ⟨c, hc, v, _, rfl, hv, hj⟩
    · rintro ⟨c, hc, v, _, rfl, hv, hj⟩
      exact ⟨_, ⟨c, hc, v, hv, rfl⟩, hj⟩

theorem computable_stepCfg {pr : (Fin n × Fin q × Fin n) × ℕ → Bool}
    {lat : (Fin n × Fin q × Fin n) × ℕ → ℕ} (hpr : Computable pr) (hlat : Computable lat) :
    Computable fun x : Fin q × List (Fin n × ℕ) => stepCfg pr lat x.1 x.2 := by
  let P := (Fin q × List (Fin n × ℕ)) × (List (Fin n × ℕ) × (Fin n × ℕ))
  let S := List (Fin n × ℕ) × Fin n
  have he : Primrec fun z : P × S => ((z.1.2.2.1, z.1.1.1, z.2.2), z.1.2.2.2) :=
    Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hin : Computable fun z : P × S =>
      bif pr ((z.1.2.2.1, z.1.1.1, z.2.2), z.1.2.2.2) then
        z.2.1 ++ [(z.2.2, z.1.2.2.2 + lat ((z.1.2.2.1, z.1.1.1, z.2.2), z.1.2.2.2))] else z.2.1 :=
    Computable.cond (hpr.comp he.to_comp)
      (Primrec.list_append.to_comp.comp (Primrec.fst.comp Primrec.snd).to_comp
        (Primrec.list_cons.to_comp.comp
          (Computable.pair (Primrec.snd.comp Primrec.snd).to_comp
            (Primrec.nat_add.to_comp.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to_comp
              (hlat.comp he.to_comp)))
          (Computable.const [])))
      (Primrec.fst.comp Primrec.snd).to_comp
  have hinner : Computable fun p : P => (List.finRange n).foldl (fun s v =>
      bif pr ((p.2.2.1, p.1.1, v), p.2.2.2) then
        s ++ [(v, p.2.2.2 + lat ((p.2.2.1, p.1.1, v), p.2.2.2))] else s) p.2.1 :=
    computable_list_foldl (Computable.const _) (Primrec.fst.comp Primrec.snd).to_comp hin.to₂
  exact (computable_list_foldl Computable.snd (Computable.const []) hinner.to₂).of_eq fun x => rfl

/-- For a TVG-automaton with computable `ρ` and `ζ`, membership in `L_nowait` is decidable by a
computable function (reachable configurations are computed letter by letter). -/
theorem computablePred_mem_Lnowait {A : TVGAutomaton (Fin n) (Fin q)} (hA : A.IsComputable) :
    ComputablePred (· ∈ A.Lnowait) := by
  classical
  obtain ⟨⟨inst, hp⟩, hl⟩ := hA
  let pr : (Fin n × Fin q × Fin n) × ℕ → Bool := fun x => @decide _ (inst x)
  let lat : (Fin n × Fin q × Fin n) × ℕ → ℕ := fun x => A.latency x.1 x.2
  let init : List (Fin n × ℕ) :=
    ((List.finRange n).filter fun s => decide (s ∈ A.init)).map (·, A.start)
  let acc : Fin n → Bool := fun v => decide (v ∈ A.accept)
  have hrun : Computable fun w : List (Fin q) => runCfg pr lat w init :=
    computable_list_foldl Computable.id (Computable.const _)
      ((computable_stepCfg hp hl).comp (Computable.pair (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.snd))).to₂
  have hf : Computable fun w : List (Fin q) =>
      (runCfg pr lat w init).foldl (fun b y => b || acc y.1) false :=
    computable_list_foldl hrun (Computable.const false)
      (Primrec.or.comp (Primrec.fst.comp Primrec.snd)
        ((Primrec.dom_finite acc).comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).to_comp.to₂
  refine computablePred_of_bool hf fun w => ?_
  rw [foldl_or_eq_true]
  simp only [mem_runCfg A.toTVG (pr := pr) (lat := lat) (fun x => @decide_eq_true_iff _ (inst x))
    (fun _ => rfl), init, acc, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨s, hs, f, hf, t', h⟩
    exact ⟨(f, t'), ⟨_, ⟨s, hs, rfl⟩, h⟩, hf⟩
  · rintro ⟨y, ⟨_, ⟨s, hs, rfl⟩, h⟩, hf⟩
    exact ⟨s, hs, y.1, hf, y.2, h⟩

/-- `𝓛_nowait` for computable TVGs consists of decidable languages. -/
theorem LnowaitComp_subset_computable (q : ℕ) :
    LnowaitComp q ⊆ {L : Language (Fin q) | ComputablePred (· ∈ L)} := by
  rintro L ⟨n, A, hA, rfl⟩
  exact computablePred_mem_Lnowait hA

/-- **Theorem 3.1** of [CFGSY'12], sharpened: with computable `ρ` and `ζ`, `𝓛_nowait` is exactly
the class of decidable languages. -/
theorem LnowaitComp_eq_computable (q : ℕ) :
    LnowaitComp q = {L : Language (Fin q) | ComputablePred (· ∈ L)} :=
  (LnowaitComp_subset_computable q).antisymm (theorem_3_1_computable q)

/-- **Theorem 5.1** of [CFGSY'12], sharpened: with computable `ρ` and `ζ`, `𝓛_wait[d]` is exactly
the class of decidable languages. -/
theorem LwaitAtMostComp_eq_computable (q d : ℕ) :
    LwaitAtMostComp q d = {L : Language (Fin q) | ComputablePred (· ∈ L)} := by
  rw [theorem_5_1_computable, LnowaitComp_eq_computable]

end Converse

end Podc.TVGWaitingExpressivity
