import Papers.PODC2026.ConsistentRefereeing.CaseStack
import Podc.SharedMemory.Covering

/-!
# Theorem 5 of [ACE26]

**Theorem 5.** There is no lock-free strongly linearizable implementation of the one-shot
contest object, for `n ≥ 4` processes, from base objects each of which is interfering, an
`(n − 2)`-window register (more generally: window-like with window `n − 2`), or a stack.

The paper states the theorem for wait-free implementations; its introduction, Corollary 12 and
the proof itself only need lock-freedom. We assume lock-freedom and strong linearizability only on
the admissible executions `Adm ref` (`theorem5`) and derive the versions for the unrestricted
notions (`theorem5_lockFree`, `theorem5_waitFree`).

Proof structure (`Crit` from `Critical.lean`): pick a critical execution and two competitors `i`,
`j` whose steps lead to different values. `Crit.pair`: unless both steps write to the same
window register, the cases of `Cases.lean` and `CaseStack.lean` give a contradiction. Then every
other competitor `c` also writes to that register (apply `Crit.pair` to `c` and whichever of
`i`, `j` has a different value), and `Crit.window` concludes: after the writes of all competitors
but `i`, the window has forgotten the write of `i` (case 3b).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Referee

open Impl

variable {P ι L : Type} {B : ι → ObjSpec} [DecidableEq P] [DecidableEq ι]
variable {I : Impl (contestObj P) B P L} {ref : P}

namespace Crit

variable (K : Crit I ref) (H : Hyps I ref)
include H

/-- Case 4: the steps of `i` and `j` modify the same stack. -/
theorem stack {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j) {V : Type} {R : ι} (rep : StackRep (B R) V)
    {oi oj : (B R).Op} {ki kj : (B R).Resp → L} (hli : K.lbl i = .tau i)
    (hai : I.act i (K.C.loc i) = .access R oi ki)
    (hmi : ((B R).δ (K.C.mem R) oi).1 ≠ K.C.mem R) (hlj : K.lbl j = .tau j)
    (haj : I.act j (K.C.loc j) = .access R oj kj)
    (hmj : ((B R).δ (K.C.mem R) oj).1 ≠ K.C.mem R) : False := by
  cases hpj : rep.push oj with
  | some uj => exact K.stack_push H hi hj hk hij hik hjk hv rep hli hai hmi hlj haj hpj
  | none =>
    cases hpi : rep.push oi with
    | some ui =>
      exact K.stack_push H hj hi hk hij.symm hjk hik hv.symm rep hlj haj hmj hli hai hpi
    | none =>
      -- 4a: two pops commute
      refine K.interfering_at H hi hj hk hij hik hjk hv hli hai hlj haj (Or.inl ?_)
      apply rep.inj
      rw [rep.pop_state _ _ hpj, rep.pop_state _ _ hpi, rep.pop_state _ _ hpi,
        rep.pop_state _ _ hpj]

/-- **The pair analysis.** For competitors `i ≠ j` with different values and a third competitor,
the steps of `i` and `j` are writes to the same window-like base object. -/
theorem pair [Fintype P] (hB : ∀ a, (B a).Interfering ∨ (B a).WindowLike (Fintype.card P - 2) ∨
      (B a).StackLike)
    {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j) :
    ∃ (R : ι) (oi oj : (B R).Op) (ki kj : (B R).Resp → L), K.lbl i = .tau i ∧
      I.act i (K.C.loc i) = .access R oi ki ∧ ((B R).δ (K.C.mem R) oi).1 ≠ K.C.mem R ∧
      K.lbl j = .tau j ∧ I.act j (K.C.loc j) = .access R oj kj ∧
      ((B R).δ (K.C.mem R) oj).1 ≠ K.C.mem R ∧ (B R).WindowLike (Fintype.card P - 2) := by
  obtain ⟨C₁, h₁, -⟩ := K.step₁ H.allowed hi
  obtain ⟨C₂, h₂, -⟩ := K.step₁ H.allowed hj
  rcases K.kind hi h₁ with hm | ⟨a, oa, ka, hli, hai, hma⟩
  · exact (K.invisible H hi hj hk hij hik hjk hv h₁ hm).elim
  rcases K.kind hj h₂ with hm | ⟨b, ob, kb, hlj, hbj, hmb⟩
  · exact (K.invisible H hj hi hk hij.symm hjk hik hv.symm h₂ hm).elim
  by_cases hab : a = b
  · subst hab
    rcases hB a with hI | hW | ⟨V, ⟨rep⟩⟩
    · exact (K.interfering H hi hj hk hij hik hjk hv hli hai hlj hbj hI).elim
    · exact ⟨a, oa, ob, ka, kb, hli, hai, hma, hlj, hbj, hmb, hW⟩
    · exact (K.stack H hi hj hk hij hik hjk hv rep hli hai hma hlj hbj hmb).elim
  · exact (K.distinct H hi hj hk hij hik hjk hv hli hai hlj hbj hab).elim

end Crit

/-! ## Runs of writes -/

/-- Processes of a list `cs`, each poised to apply `o c` to the object `R`, take one step each. -/
lemma run_writes {R : ι} (o : P → (B R).Op) (kk : P → (B R).Resp → L) :
    ∀ (cs : List P) (D : Config (contestObj P) B P L), cs.Nodup →
    (∀ c ∈ cs, D.pend c ≠ none ∧ I.act c (D.loc c) = .access R (o c) (kk c)) →
    ∃ D', I.runFrom D (cs.map Label.tau) = some D' ∧
      D'.mem = Function.update D.mem R ((B R).runOps (D.mem R) (cs.map o)) ∧
      D'.pend = D.pend ∧ (∀ q, q ∉ cs → D'.loc q = D.loc q) ∧
      ∀ c ∈ cs, ∃ s, D'.loc c = kk c ((B R).δ s (o c)).2 := by
  intro cs D hnd hD
  set es := cs.map fun c => (c, (⟨R, o c⟩ : Σ i, (B i).Op))
  have hfst : es.map Prod.fst = cs := by simp [es, Function.comp_def]
  have hsnd : es.map Prod.snd = (cs.map o).map (Sigma.mk R) := by simp [es, Function.comp_def]
  obtain ⟨D', h1, h2, h3, h4, h5⟩ := I.runFrom_poised_block (es := es) (hfst ▸ hnd)
    (fun e he => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      exact ⟨(hD c hc).1, kk c, (hD c hc).2⟩)
  rw [hfst] at h1 h4
  refine ⟨D', h1, by rw [h2, hsnd, applyAccesses_map_mk], h3, h4, fun c hc => ?_⟩
  obtain ⟨k, s, hk, hl⟩ := h5 (c, ⟨R, o c⟩) (by simp [es, hc])
  rw [(hD c hc).2] at hk
  simp only [Action.access.injEq, heq_eq_eq, true_and] at hk
  subst hk
  exact ⟨s, hl⟩

namespace Crit

variable (K : Crit I ref) (H : Hyps I ref)
include H

/-- Case 3b: all competitors write to the same window-like object with window `n − 2`. After the
writes of all competitors other than `i` and `j`, the configurations `α·i·j·γ` and `α·j·γ` have
the same memory. -/
theorem window [Fintype P] {R : ι} (hW : (B R).WindowLike (Fintype.card P - 2))
    (hall : ∀ c, c ≠ ref → K.lbl c = .tau c ∧ ∃ oc kc, I.act c (K.C.loc c) = .access R oc kc ∧
      ¬ (B R).ReadOnly oc)
    {i j k : P} (hi : i ≠ ref) (hj : j ≠ ref) (hk : k ≠ ref) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hv : K.v i ≠ K.v j) : False := by
  classical
  have : Nonempty ((B R).Resp → L) := ⟨fun _ => K.C.loc i⟩
  obtain ⟨o₀, -⟩ := (hall i hi).2
  have : Nonempty (B R).Op := ⟨o₀⟩
  choose! o kk hact hro using fun c (hc : c ≠ ref) => (hall c hc).2
  have hlbl : ∀ c, c ≠ ref → K.lbl c = .tau c := fun c hc => (hall c hc).1
  -- the other competitors
  let cs : List P := (Finset.univ.filter (fun c => c ≠ ref ∧ c ≠ i ∧ c ≠ j)).toList
  have hcs : ∀ c, c ∈ cs ↔ c ≠ ref ∧ c ≠ i ∧ c ≠ j := fun c => by simp [cs]
  have hnd : cs.Nodup := Finset.nodup_toList _
  have hlen : cs.length = Fintype.card P - 3 := by
    simp only [cs, Finset.length_toList]
    have : (Finset.univ.filter (fun c => c ≠ ref ∧ c ≠ i ∧ c ≠ j)) =
        Finset.univ \ {ref, i, j} := by ext c; simp
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    rw [Finset.card_insert_of_notMem (by simp [hi.symm, hj.symm]),
      Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
  have hkcs : k ∈ cs := (hcs k).2 ⟨hk, hik.symm, hjk.symm⟩
  -- the two prefixes
  obtain ⟨C₁, h₁, hA₁⟩ := K.step₁ H.allowed hi
  obtain ⟨C₁₂, h₁₂, hA₁₂⟩ := K.step₂ H.allowed hi hj hij h₁ hA₁
  obtain ⟨C₂, h₂, hA₂⟩ := K.step₁ H.allowed hj
  simp only [hlbl i hi, hlbl j hj] at h₁ h₁₂ h₂ hA₁ hA₁₂ hA₂
  obtain ⟨m₁, l₁, p₁⟩ := step_tau_mem h₁ (hact i hi)
  have hai' : I.act j (C₁.loc j) = .access R (o j) (kk j) := by
    rw [l₁, Function.update_of_ne (Ne.symm hij)]; exact hact j hj
  obtain ⟨m₁₂, l₁₂, p₁₂⟩ := step_tau_mem h₁₂ hai'
  obtain ⟨m₂, l₂, p₂⟩ := step_tau_mem h₂ (hact j hj)
  -- the remaining writes
  have hready : ∀ (D : Config (contestObj P) B P L), D.pend = K.C.pend →
      (∀ c ∈ cs, D.loc c = K.C.loc c) →
      ∀ c ∈ cs, D.pend c ≠ none ∧ I.act c (D.loc c) = .access R (o c) (kk c) := by
    intro D hp hl c hc
    obtain ⟨hcr, hci, hcj⟩ := (hcs c).1 hc
    obtain ⟨C', hC', -⟩ := K.step₁ H.allowed hcr
    rw [hlbl c hcr] at hC'
    exact ⟨by rw [hp]; exact (step_tau hC').1, by rw [hl c hc]; exact hact c hcr⟩
  obtain ⟨E₁, hE₁, mE₁, pE₁, lE₁, lE₁'⟩ := run_writes o kk cs C₁₂ hnd (hready C₁₂
    (by rw [p₁₂, p₁]) (fun c hc => by
      obtain ⟨-, hci, hcj⟩ := (hcs c).1 hc
      rw [l₁₂, l₁, Function.update_of_ne hcj, Function.update_of_ne hci]))
  obtain ⟨E₂, hE₂, mE₂, pE₂, lE₂, lE₂'⟩ := run_writes o kk cs C₂ hnd (hready C₂ p₂
    (fun c hc => by
      obtain ⟨-, -, hcj⟩ := (hcs c).1 hc
      rw [l₂, Function.update_of_ne hcj]))
  -- the memories agree: the window forgets the write of `i`
  have hmem : E₁.mem = E₂.mem := by
    rw [mE₁, mE₂, m₁₂, m₂, m₁]
    simp only [Function.update_self, Function.update_idem]
    congr 1
    have hw := hW.2 (o j :: cs.map o) (by simp) (by simp only [List.length_cons, List.length_map, hlen]; omega)
      (fun o' ho' => by
        simp only [List.mem_cons, List.mem_map] at ho'
        rcases ho' with rfl | ⟨c, hc, rfl⟩
        · exact hro j hj
        · exact hro c ((hcs c).1 hc).1)
      ((B R).δ (K.C.mem R) (o i)).1 (K.C.mem R)
    simpa [ObjSpec.runOps] using hw
  -- they agree on `k` and the referee
  have hag : Impl.AgreeOn {k, ref} E₁ E₂ := by
    refine ⟨hmem, fun q hq => ?_, fun q hq => by rw [pE₁, pE₂, p₁₂, p₁, p₂]⟩
    rcases hq with rfl | hq
    · obtain ⟨s₁, hs₁⟩ := lE₁' q hkcs
      obtain ⟨s₂, hs₂⟩ := lE₂' q hkcs
      rw [hs₁, hs₂]
      congr 1
      exact ((hW.1 (o q)).resolve_left (hro q hk)) s₁ s₂
    · have hq : q = ref := hq
      subst hq
      have hrcs : q ∉ cs := fun h => ((hcs q).1 h).1 rfl
      rw [lE₁ q hrcs, lE₂ q hrcs, l₁₂, l₁, l₂, Function.update_of_ne (Ne.symm hj),
        Function.update_of_ne (Ne.symm hi), Function.update_of_ne (Ne.symm hj)]
  have hr₁ : I.runFrom K.C ([.tau i] ++ [.tau j] ++ cs.map Label.tau) = some E₁ := by
    simp [runFrom_cons, h₁, h₁₂, hE₁]
  have hr₂ : I.runFrom K.C ([.tau j] ++ cs.map Label.tau) = some E₂ := by
    simp [runFrom_cons, h₂, hE₂]
  have hops : ∀ q, opsOf (cs.map Label.tau : List (Label P (contestObj P))) q = [] :=
    opsOf_blockWrite cs
  refine K.contra H.lf H.sl H.allowed hi hj hk hv (β₁ := [K.lbl j] ++ cs.map Label.tau)
    (β₂ := cs.map Label.tau) ?_ ?_ ?_ ?_ ?_ (hops ref) ?_ hag
  · rw [hlbl i hi, hlbl j hj]
    have := K.run_ext hr₁; simpa using this
  · rw [hlbl j hj]
    have := K.run_ext hr₂; simpa using this
  · rw [hlbl i hi, hlbl j hj, ← List.append_assoc]
    exact hA₁₂.append_noInv ref hops
  · rw [hlbl j hj]; exact hA₂.append_noInv ref hops
  · rw [hlbl j hj]; simp [hops]
  · rw [hlbl i hi, hlbl j hj]; simp [opsOf_append, hops]

end Crit

/-- **Theorem 5 of [ACE26]** (for implementations correct and lock-free on admissible
executions). For `n ≥ 4` processes, there is no implementation of the one-shot contest object
that is lock-free and strongly linearizable on the admissible executions, from base objects each
of which is interfering, window-like with window `n − 2` (e.g. an `(n − 2)`-window register) or a
stack. -/
theorem theorem5 {P ι L : Type} {B : ι → ObjSpec} [Fintype P] [DecidableEq P] [DecidableEq ι]
    (ref : P) (hP : 4 ≤ Fintype.card P)
    (hB : ∀ i, (B i).Interfering ∨ (B i).WindowLike (Fintype.card P - 2) ∨ (B i).StackLike)
    (I : Impl (contestObj P) B P L) (hallow : ∀ p, I.allowed p (roleOp ref p))
    (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref)) : False := by
  classical
  have H : Hyps I ref := ⟨hlf, hsl, hallow⟩
  -- three competitors
  have hcomp : 3 ≤ (Finset.univ.erase ref).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  obtain ⟨c₁, hc₁, c₂, hc₂, h₁₂⟩ : ∃ c₁ ∈ Finset.univ.erase ref, ∃ c₂ ∈ Finset.univ.erase ref,
      c₁ ≠ c₂ := Finset.one_lt_card.1 (by omega)
  obtain ⟨K⟩ := exists_crit I ref hlf hsl hallow (Finset.ne_of_mem_erase hc₁)
    (Finset.ne_of_mem_erase hc₂) h₁₂
  obtain ⟨i, j, hi, hj, hv⟩ := K.exists_pair hsl
  have hij : i ≠ j := fun h => hv (h ▸ rfl)
  -- a third competitor
  have hthird : ∀ a b, ∃ k, k ≠ ref ∧ k ≠ a ∧ k ≠ b := by
    intro a b
    have : 0 < ((Finset.univ.erase ref).erase a |>.erase b).card := by
      have h1 := Finset.pred_card_le_card_erase (s := (Finset.univ.erase ref).erase a) (a := b)
      have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.erase ref) (a := a)
      omega
    obtain ⟨k, hk⟩ := Finset.card_pos.1 this
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    exact ⟨k, hk.2.2, hk.2.1, hk.1⟩
  obtain ⟨k, hk, hki, hkj⟩ := hthird i j
  obtain ⟨R, oi, oj, ki, kj, hli, hai, hmi, hlj, haj, hmj, hW⟩ :=
    K.pair H hB hi hj hk hij (Ne.symm hki) (Ne.symm hkj) hv
  -- every competitor writes to `R`
  have hall : ∀ c, c ≠ ref → K.lbl c = .tau c ∧ ∃ oc kc, I.act c (K.C.loc c) = .access R oc kc ∧
      ¬ (B R).ReadOnly oc := by
    intro c hc
    have hnro : ∀ {o : (B R).Op}, ((B R).δ (K.C.mem R) o).1 ≠ K.C.mem R → ¬ (B R).ReadOnly o :=
      fun h hro => h (hro _)
    by_cases hci : c = i
    · subst hci; exact ⟨hli, oi, ki, hai, hnro hmi⟩
    by_cases hcj : c = j
    · subst hcj; exact ⟨hlj, oj, kj, haj, hnro hmj⟩
    by_cases hvc : K.v c ≠ K.v i
    · obtain ⟨R', oc, oi', kc, ki', hlc, hac, hmc, -, hai', -⟩ :=
        K.pair H hB hc hi hj hci hcj hij hvc
      have e := hai.symm.trans hai'
      cases e
      exact ⟨hlc, oc, kc, hac, hnro hmc⟩
    · have hvc' : K.v c ≠ K.v j := by push Not at hvc; rw [hvc]; exact hv
      obtain ⟨R', oc, oj', kc, kj', hlc, hac, hmc, -, haj', -⟩ :=
        K.pair H hB hc hj hi hcj hci hij.symm hvc'
      have e := haj.symm.trans haj'
      cases e
      exact ⟨hlc, oc, kc, hac, hnro hmc⟩
  exact K.window H hW hall hi hj hk hij (Ne.symm hki) (Ne.symm hkj) hv

/-- Theorem 5 of [ACE26] for the unrestricted notions: no lock-free strongly linearizable contest
implementation (for `n ≥ 4`) from interfering objects, `(n − 2)`-window registers and stacks. -/
theorem theorem5_lockFree {P ι L : Type} {B : ι → ObjSpec} [Fintype P] [DecidableEq P]
    [DecidableEq ι] (ref : P) (hP : 4 ≤ Fintype.card P)
    (hB : ∀ i, (B i).Interfering ∨ (B i).WindowLike (Fintype.card P - 2) ∨ (B i).StackLike)
    (I : Impl (contestObj P) B P L) (hallow : ∀ p, I.allowed p (roleOp ref p)) :
    ¬ (I.LockFree ∧ I.StronglyLinearizable) := fun ⟨hlf, hsl⟩ =>
  theorem5 ref hP hB I hallow (hlf.lockFreeOn _) (hsl.strongLinOn _)

/-- Theorem 5 of [ACE26] as stated in the paper (wait-free implementations). -/
theorem theorem5_waitFree {P ι L : Type} {B : ι → ObjSpec} [Fintype P] [DecidableEq P]
    [DecidableEq ι] (ref : P) (hP : 4 ≤ Fintype.card P)
    (hB : ∀ i, (B i).Interfering ∨ (B i).WindowLike (Fintype.card P - 2) ∨ (B i).StackLike)
    (I : Impl (contestObj P) B P L) (hallow : ∀ p, I.allowed p (roleOp ref p)) :
    ¬ (I.WaitFree ∧ I.StronglyLinearizable) := fun ⟨hwf, hsl⟩ =>
  theorem5 ref hP hB I hallow ((hwf.waitFreeOn _).lockFreeOn (fun _ h => h.oneShot))
    (hsl.strongLinOn _)

end Referee

end Cslib.SharedMemory
