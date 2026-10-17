import Papers.PODC2026.ConsistentRefereeing.OneShot

/-!
# The critical execution of Theorem 5 and its simple cases

`Crit I ref` packages a critical execution (Claim 10 of [ACE26]) of an implementation `I` of the
one-shot contest object: an admissible execution `α` ending in `C`, in which the referee has not
invoked, every competitor `c` has a next label `lbl c`, and `α · lbl c` is `v c`-univalent.
`Crit.exists_pair` gives two competitors with different values.

`Crit.contra` is the contradiction scheme used in every case: an extension of `α · lbl i` and an
extension of `α · lbl j` (with `v i ≠ v j`) whose final configurations agree on the memory, the
referee and a third competitor `k` cannot exist.

The simple cases of the proof of Theorem 5:
* `Crit.invisible` — a step that does not change the memory (an invocation, a response, a read,
  or any primitive leaving its object unchanged): `α·i·j` and `α·j` agree on everybody but `i`;
* `Crit.distinct` — steps on distinct objects commute;
* `Crit.interfering` — steps on the same interfering object commute or one overwrites the other.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Referee

open Impl

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι]

/-- A critical execution (Claim 10 of [ACE26]). -/
structure Crit (I : Impl (contestObj P) B P L) (ref : P) where
  α : List (Label P (contestObj P))
  C : Config (contestObj P) B P L
  run : I.run α = some C
  adm : Adm ref α
  noref : opsOf α ref = []
  /-- The next label of every competitor. -/
  lbl : P → Label P (contestObj P)
  nxt_eq : ∀ c, c ≠ ref → nxt I ref α C c = some (lbl c)
  /-- The value of the univalent execution `α · lbl c`. -/
  v : P → P
  uni : ∀ c, c ≠ ref → ∀ w ∈ Val I ref (α ++ [lbl c]), w = v c
  multi : Multi I ref α

variable (I : Impl (contestObj P) B P L) (ref : P)

/-- Claim 10 of [ACE26], packaged. -/
theorem exists_crit [Fintype P] (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref))
    (hallow : ∀ p, I.allowed p (roleOp ref p)) {c₁ c₂ : P} (h₁ : c₁ ≠ ref) (h₂ : c₂ ≠ ref)
    (h₁₂ : c₁ ≠ c₂) : Nonempty (Crit I ref) := by
  classical
  obtain ⟨α, C, hC, hA, href, hM, hcrit⟩ := exists_critical I ref hlf hsl hallow h₁ h₂ h₁₂
  -- every competitor has a next label
  have hnx : ∀ c, c ≠ ref → ∃ ℓ, nxt I ref α C c = some ℓ := by
    intro c hc
    by_contra hno
    push Not at hno
    have hnone : nxt I ref α C c = none := Option.eq_none_iff_forall_ne_some.2 hno
    unfold nxt at hnone
    split_ifs at hnone with h1 h2
    obtain ⟨w₁, w₂, hne, hw₁, hw₂⟩ := hM
    exact hne (val_subsingleton I ref hsl ⟨C, hC⟩ hA hc
      (Impl.respsOf_ne_nil_of_idle hC h2 h1) hw₁ hw₂)
  have : Nonempty (Label P (contestObj P)) := ⟨.tau c₁⟩
  have : Nonempty P := ⟨c₁⟩
  choose! lbl hlbl using hnx
  -- every next step is univalent
  have huni : ∀ c, c ≠ ref → ∃ v, ∀ w ∈ Val I ref (α ++ [lbl c]), w = v := by
    intro c hc
    obtain ⟨C', hC', hA'⟩ := nxt_step I ref hallow hC hA (hlbl c hc) (fun h => absurd h hc)
    have hr' : I.run (α ++ [lbl c]) = some C' := by
      rw [run_append_of_eq I hC, runFrom_singleton, hC']
    have hp := nxt_proc I ref (hlbl c hc)
    obtain ⟨v, hv⟩ := val_nonempty I ref hlf hsl hallow hr' hA'
      (by rw [opsOf_append, href, opsOf_cons, Label.invOf_eq_none_of_proc_ne
        (by rw [hp]; exact hc)]; simp) hc
    refine ⟨v, fun w hw => ?_⟩
    by_contra hne
    exact hcrit c (lbl c) hc (hlbl c hc) ⟨w, v, hne, hw, hv⟩
  choose! v hv using huni
  exact ⟨⟨α, C, hC, hA, href, lbl, hlbl, v, hv, hM⟩⟩

namespace Crit

variable {I ref} (K : Crit I ref)

lemma lbl_proc {c : P} (hc : c ≠ ref) : (K.lbl c).proc = c := nxt_proc I ref (K.nxt_eq c hc)

lemma opsOf_lbl {c q : P} (hc : c ≠ ref) (hq : q ≠ c) : opsOf [K.lbl c] q = [] := by
  rw [opsOf_cons, Label.invOf_eq_none_of_proc_ne (by rw [K.lbl_proc hc]; exact Ne.symm hq)]
  simp

/-- Two competitors with different values (from multivalence). -/
theorem exists_pair (hsl : I.StrongLinOn (Adm ref)) :
    ∃ i j, i ≠ ref ∧ j ≠ ref ∧ K.v i ≠ K.v j := by
  -- every value of `α` is a value of some `α · lbl c`
  have hcover : ∀ w ∈ Val I ref K.α, ∃ c, c ≠ ref ∧ w = K.v c := by
    rintro w ⟨β, hV, hA, hr⟩
    rcases β with _ | ⟨ℓ, β⟩
    · -- the referee has not responded in `α`
      simp only [List.append_nil] at hr
      have := respsOf_eq_nil_of_opsOf I K.run K.noref
      simp [respOf, this] at hr
    · obtain ⟨D, hD⟩ := hV
      rw [show K.α ++ ℓ :: β = K.α ++ [ℓ] ++ β by simp] at hD hA hr
      have hD₀ : I.runFrom K.C ([ℓ] ++ β) = some D := by
        rw [← run_append_of_eq I K.run]; simpa using hD
      obtain ⟨C', hC', hD'⟩ := I.runFrom_eq_some_of_append hD₀
      rw [runFrom_singleton] at hC'
      have hA' : Adm ref (K.α ++ [ℓ]) := hA.of_append
      have hnx := Referee.nxt_eq I ref K.run hA' hC'
      by_cases hp : ℓ.proc = ref
      · -- the referee cannot start: no competitor has completed
        rw [hp] at hnx
        have : nxt I ref K.α K.C ref = some (.inv ref (roleOp ref ref)) := by
          simp [nxt, K.noref]
        rw [this] at hnx
        cases hnx
        obtain ⟨c, hc, hcomp⟩ := hA'.late K.α [] _ rfl
        obtain ⟨w₁, w₂, hne, hw₁, hw₂⟩ := K.multi
        exact absurd (val_subsingleton I ref hsl ⟨_, K.run⟩ K.adm hc hcomp hw₁ hw₂) hne
      · refine ⟨ℓ.proc, hp, K.uni _ hp w ?_⟩
        have hl : K.lbl ℓ.proc = ℓ := Option.some_inj.1 ((K.nxt_eq _ hp).symm.trans hnx)
        rw [hl]
        exact ⟨β, ⟨D, by simpa using hD⟩, by simpa using hA, by simpa using hr⟩
  obtain ⟨w₁, w₂, hne, hw₁, hw₂⟩ := K.multi
  obtain ⟨i, hi, rfl⟩ := hcover w₁ hw₁
  obtain ⟨j, hj, rfl⟩ := hcover w₂ hw₂
  exact ⟨i, j, hi, hj, hne⟩

/-- The contradiction scheme: extensions of `α · lbl i` and `α · lbl j` (with `v i ≠ v j`)
whose final configurations agree on the memory, the referee and a competitor `k` with the same
invocation status. -/
theorem contra (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref))
    (hallow : ∀ p, I.allowed p (roleOp ref p)) {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref)
    (hk : k ≠ ref) (hv : K.v i ≠ K.v j) {β₁ β₂ : List (Label P (contestObj P))}
    {D₁ D₂ : Config (contestObj P) B P L}
    (h₁ : I.run (K.α ++ [K.lbl i] ++ β₁) = some D₁) (h₂ : I.run (K.α ++ [K.lbl j] ++ β₂) = some D₂)
    (hA₁ : Adm ref (K.α ++ [K.lbl i] ++ β₁)) (hA₂ : Adm ref (K.α ++ [K.lbl j] ++ β₂))
    (href₁ : opsOf β₁ ref = []) (href₂ : opsOf β₂ ref = [])
    (hk₁₂ : opsOf (K.α ++ [K.lbl i] ++ β₁) k = [] ↔ opsOf (K.α ++ [K.lbl j] ++ β₂) k = [])
    (hag : Impl.AgreeOn {k, ref} D₁ D₂) : False := by
  obtain ⟨w, hw₁, hw₂, -⟩ := exists_common_gen I ref hlf hsl hallow h₁ h₂ hA₁ hA₂
    (by simp [opsOf_append, K.noref, Label.invOf_eq_none_of_proc_ne
      (show (K.lbl i).proc ≠ ref by rw [K.lbl_proc hi]; exact hi), href₁])
    (by simp [opsOf_append, K.noref, Label.invOf_eq_none_of_proc_ne
      (show (K.lbl j).proc ≠ ref by rw [K.lbl_proc hj]; exact hj), href₂]) hk hk₁₂ hag
  have e₁ := K.uni i hi w (val_mono I ref hw₁)
  have e₂ := K.uni j hj w (val_mono I ref hw₂)
  exact hv (e₁.symm.trans e₂)

/-- The step of a competitor is enabled and keeps the execution admissible. -/
lemma step₁ (hallow : ∀ p, I.allowed p (roleOp ref p)) {c : P} (hc : c ≠ ref) :
    ∃ C', I.step K.C (K.lbl c) = some C' ∧ Adm ref (K.α ++ [K.lbl c]) :=
  nxt_step I ref hallow K.run K.adm (K.nxt_eq c hc) (fun h => absurd h hc)

/-- After a step of `i`, the step of `j ≠ i` is still enabled. -/
lemma step₂ (hallow : ∀ p, I.allowed p (roleOp ref p)) {i j : P} (hi : i ≠ ref) (hj : j ≠ ref)
    (hij : i ≠ j) {C₁ : Config (contestObj P) B P L} (h₁ : I.step K.C (K.lbl i) = some C₁)
    (hA₁ : Adm ref (K.α ++ [K.lbl i])) :
    ∃ C₂, I.step C₁ (K.lbl j) = some C₂ ∧ Adm ref (K.α ++ [K.lbl i] ++ [K.lbl j]) := by
  have hr₁ : I.run (K.α ++ [K.lbl i]) = some C₁ := by
    rw [run_append_of_eq I K.run, runFrom_singleton, h₁]
  have hnx : nxt I ref (K.α ++ [K.lbl i]) C₁ j = some (K.lbl j) := by
    rw [nxt_other I ref h₁ (by rw [K.lbl_proc hi]; exact hij)]; exact K.nxt_eq j hj
  exact nxt_step I ref hallow hr₁ hA₁ hnx (fun h => absurd h hj)

/-- Configurations reached from the same configuration by steps of processes outside `Q` agree
on `Q` as soon as they have the same memory. -/
lemma agreeOn_of_mem {Q : Set P} {C₀ D₁ D₂ : Config (contestObj P) B P L}
    {β₁ β₂ : List (Label P (contestObj P))} (h₁ : I.runFrom C₀ β₁ = some D₁)
    (h₂ : I.runFrom C₀ β₂ = some D₂) (hQ₁ : ∀ ℓ ∈ β₁, ℓ.proc ∉ Q) (hQ₂ : ∀ ℓ ∈ β₂, ℓ.proc ∉ Q)
    (hmem : D₁.mem = D₂.mem) : Impl.AgreeOn Q D₁ D₂ := by
  refine ⟨hmem, fun q hq => ?_, fun q hq => ?_⟩
  · rw [(I.runFrom_other h₁ (fun ℓ hℓ h => hQ₁ ℓ hℓ (h ▸ hq))).1,
      (I.runFrom_other h₂ (fun ℓ hℓ h => hQ₂ ℓ hℓ (h ▸ hq))).1]
  · rw [(I.runFrom_other h₁ (fun ℓ hℓ h => hQ₁ ℓ hℓ (h ▸ hq))).2,
      (I.runFrom_other h₂ (fun ℓ hℓ h => hQ₂ ℓ hℓ (h ▸ hq))).2]

/-- The memory effect of a `tau` step whose action is known. -/
lemma step_tau_mem {C C' : Config (contestObj P) B P L} {p : P} (hs : I.step C (.tau p) = some C')
    {a : ι} {o : (B a).Op} {k : (B a).Resp → L} (hact : I.act p (C.loc p) = .access a o k) :
    C'.mem = Function.update C.mem a ((B a).δ (C.mem a) o).1 ∧
      C'.loc = Function.update C.loc p (k ((B a).δ (C.mem a) o).2) ∧ C'.pend = C.pend := by
  obtain ⟨-, hpend, a', o', k', hact', hmem, hloc⟩ := step_tau hs
  rw [hact] at hact'
  cases hact'
  exact ⟨hmem, hloc, hpend⟩

/-- Every competitor's step either leaves the memory unchanged or is a `tau` step modifying a
base object. -/
lemma kind {c : P} (hc : c ≠ ref) {C' : Config (contestObj P) B P L}
    (hs : I.step K.C (K.lbl c) = some C') :
    C'.mem = K.C.mem ∨ ∃ a o k, K.lbl c = .tau c ∧ I.act c (K.C.loc c) = .access a o k ∧
      ((B a).δ (K.C.mem a) o).1 ≠ K.C.mem a := by
  have hp := K.lbl_proc hc
  cases h : K.lbl c with
  | inv q o' => rw [h] at hs; exact Or.inl (step_inv hs).2.2.2.2
  | ret q r => rw [h] at hs; exact Or.inl (step_ret hs).2.2.1
  | tau q =>
    rw [h] at hp hs; simp only [Label.proc] at hp; subst hp
    obtain ⟨-, -, a, o, k, hact, hmem, -⟩ := step_tau hs
    by_cases hch : ((B a).δ (K.C.mem a) o).1 = K.C.mem a
    · left; rw [hmem, hch, Function.update_eq_self]
    · exact Or.inr ⟨a, o, k, rfl, hact, hch⟩

end Crit

end Referee

end Cslib.SharedMemory
