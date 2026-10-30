import Papers.PODC2026.ConflictFreedom.Alg1Inv2

/-!
# Algorithm 1: commands, completed operations and real-time order

`Inv3 α C` relates the configuration `C` reached by the execution `α` to the history of `α`:

* the command of the current operation of `i` is `(op, i, seq)` for the `seq`-th invocation;
* every command occurring in an input of a GCA object belongs to an invoked operation, and if an
  operation `x` precedes (in real time) the operation of a command occurring in an input to
  `GCA_r`, then `x` committed at a round `< r`;
* every completed operation committed (ghost `cr`) a trace containing its command at a round
  `≤ S[i]`, and returned `ret*` of its command in that trace.
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable {A : ObjSpec} {n : ℕ}

/-- The operation instance of a command `(op, i, seq)`. -/
def opId (c : Cmd A n) : OpId (Fin n) := (c.2.1, c.2.2 - 1)

/-- The command `c` belongs to an invoked operation of `α`. -/
def ValidCmd (α : List (Label (Fin n) A)) (c : Cmd A n) : Prop :=
  1 ≤ c.2.2 ∧ opOf α (opId c) = some c.1

/-- The commit round of the operation instance `x` (ghost). -/
def crOf (C : Cfg A n) (x : OpId (Fin n)) : ℕ := (C.loc x.1).cr (x.2 + 1)

variable [Inhabited A.Resp]

/-- Per-process part of `Inv3`. -/
structure Inv3At (α : List (Label (Fin n) A)) (C : Cfg A n) (i : Fin n) : Prop where
  seq : (C.loc i).seq = (opsOf α i).length
  cmd : (C.loc i).phase ≠ .idle → (C.loc i).cmd.2 = (i, (C.loc i).seq) ∧ 1 ≤ (C.loc i).seq ∧
    opOf α (i, (C.loc i).seq - 1) = some (C.loc i).cmd.1
  wd : (C.loc i).phase = .writeS ∨ (C.loc i).phase = .done →
    (C.loc i).cr (C.loc i).seq = (C.loc i).r ∧
      ∃ g, (C.loc i).hist (C.loc i).r = some g ∧ g.output = ((C.loc i).s, true)
  compl : ∀ k, k < (respsOf α i).length → ∃ g o,
    (C.loc i).hist ((C.loc i).cr (k + 1)) = some g ∧ g.output.2 = true ∧
    (C.loc i).cr (k + 1) ≤ (C.mem (.S i)).1 ∧ opOf α (i, k) = some o ∧
    (o, i, k + 1) ∈ g.output.1.supp ∧ respOf α (i, k) = some (retT g.output.1 (o, i, k + 1))
  preS : ∀ j best, (C.loc i).phase = .readS j best → ∀ x, Precedes α x (i, (C.loc i).seq - 1) →
    x.1.val < j → crOf C x ≤ best.1

/-- Commands in GCA inputs belong to invoked operations, and their real-time predecessors
committed earlier. -/
def KnownOK (α : List (Label (Fin n) A)) (C : Cfg A n) : Prop :=
  ∀ r j g, locAt (C.loc j) r = some g → ∀ c ∈ g.inp.supp, ValidCmd α c ∧
    ∀ x, Precedes α x (opId c) → crOf C x < r

/-- The history invariant. -/
structure Inv3 (α : List (Label (Fin n) A)) (C : Cfg A n) : Prop where
  at_ : ∀ i, Inv3At α C i
  known : KnownOK α C

variable [Inhabited A.Op] [NeZero n]

/-- Pending operations and the counts of invocations and responses. -/
lemma counts {α : List (Label (Fin n) A)} {C : Cfg A n}
    (h : (impl (A := A) (n := n)).run α = some C) (hI : Inv1 C) (i : Fin n) :
    ((C.loc i).phase = .idle ∧ (opsOf α i).length = (respsOf α i).length) ∨
    ((C.loc i).phase ≠ .idle ∧ (opsOf α i).length = (respsOf α i).length + 1) := by
  rcases Impl.run_counts _ h i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨(hI.loc i).pend_iff.1 h1, h2⟩
  · exact Or.inr ⟨fun h' => h1 ((hI.loc i).pend_iff.2 h'), h2⟩

/-- The commit rounds of completed operations never change. -/
lemma crOf_step {α : List (Label (Fin n) A)} {C C' : Cfg A n}
    (hrun : (impl (A := A) (n := n)).run α = some C) (hI : Inv1 C) (hseq : ∀ i, Inv3At α C i)
    {ℓ : Label (Fin n) A} (h : (impl (A := A) (n := n)).step C ℓ = some C')
    {x : OpId (Fin n)} (hx : Completed α x) : crOf C' x = crOf C x := by
  unfold crOf
  by_cases hi : ℓ.proc = x.1
  swap
  · rw [(Impl.step_other h hi).1]
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv h
    simp only [Label.proc] at hi; subst hi
    rw [hloc]; simp [impl, invoke]
  | ret p r' =>
    simp only [Label.proc] at hi; subst hi
    obtain ⟨-, -, hC'⟩ := step_ret_cases h (hI.loc x.1)
    rw [hC']; simp
  | tau p =>
    simp only [Label.proc] at hi; subst hi
    obtain ⟨-, -, hT⟩ := step_tau_cases h
    cases hT with
    | readS => simp
    | readLast => simp [Loc.afterRead, Loc.startRound]
    | gca0 => simp
    | gca1 => simp
    | gca2 => simp
    | gca3 g hph hpc =>
      simp only [setLoc_loc, Function.update_self]
      have hne : x.2 + 1 ≠ (C.loc x.1).seq := by
        rcases counts hrun hI x.1 with ⟨h1, -⟩ | ⟨-, h2⟩
        · rw [hph] at h1; cases h1
        · have := (hseq x.1).seq; unfold Completed at hx; omega
      unfold Loc.afterGCA
      split_ifs <;> simp [Loc.startRound, Function.update_of_ne hne]
    | writeS => simp

/-- GCA Validity, for the letters of traces: a command in an output of `GCA_r` occurs in some
input of `GCA_r`. -/
lemma mem_input_of_mem_output {C : Cfg A n} (hI : Inv1 C) {r : ℕ} {q : Fin n}
    {gq : GCA.Loc n (Tr A n)} (hq : locAt (C.loc q) r = some gq) (hpc : gq.pc = 4)
    {c : Cmd A n} (hc : c ∈ gq.output.1.supp) :
    ∃ j g, locAt (C.loc j) r = some g ∧ c ∈ g.inp.supp := by
  have hv := GCA.validity_of_reach (hI.reach r) (fun t => (t.supp : Set (Cmd A n)))
    (fun x y hxy => by simpa using NTrace.supp_mono hxy)
    (fun S hS => by
      intro a ha
      have := NTrace.supp_lub_subset (S := S) hS (by simpa [lub_eq] using ha)
      simpa using this) q gq ⟨hq, hpc⟩ (by simpa using hc)
  simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop] at hv
  obtain ⟨x, ⟨j, l, hl, rfl⟩, hx⟩ := hv
  exact ⟨j, l, hl, hx⟩

section Hist

variable {α : List (Label (Fin n) A)} {ℓ : Label (Fin n) A}

lemma ValidCmd.invoked {c : Cmd A n} (h : ValidCmd α c) : Invoked α (opId c) :=
  Invoked.of_opOf_eq_some h.2

lemma ValidCmd.append {c : Cmd A n} (h : ValidCmd α c) : ValidCmd (α ++ [ℓ]) c :=
  ⟨h.1, by rw [opOf_append_of_invoked h.invoked]; exact h.2⟩

lemma precedes_concat_iff {x y : OpId (Fin n)} (hy : Invoked α y) :
    Precedes (α ++ [ℓ]) x y ↔ Precedes α x y := precedes_append_iff_of_invoked hy

lemma knownOK_transfer {C C' : Cfg A n} (hK : KnownOK α C)
    (hcr : ∀ x, Completed α x → crOf C' x = crOf C x)
    (hnew : ∀ r j g, locAt (C'.loc j) r = some g → locAt (C.loc j) r = some g ∨
      ∀ c ∈ g.inp.supp, ValidCmd α c ∧ ∀ x, Precedes α x (opId c) → crOf C x < r) :
    KnownOK (α ++ [ℓ]) C' := by
  intro r j g hg c hc
  have key : ValidCmd α c ∧ ∀ x, Precedes α x (opId c) → crOf C x < r := by
    rcases hnew r j g hg with h | h
    · exact hK r j g h c hc
    · exact h c hc
  refine ⟨key.1.append, fun x hx => ?_⟩
  have hx' := (precedes_concat_iff key.1.invoked).1 hx
  rw [hcr x hx'.completed]; exact key.2 x hx'

end Hist

variable {α : List (Label (Fin n) A)} {ℓ : Label (Fin n) A}

/-- Only process `i` writes `S[i]`. -/
lemma mem_S_other {C C' : Cfg A n} (hI : Inv1 C)
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {i : Fin n} (hi : ℓ.proc ≠ i) :
    C'.mem (.S i) = C.mem (.S i) := by
  cases ℓ with
  | inv p o => rw [(Impl.step_inv h).2.2.2.2]
  | ret p r => rw [(Impl.step_ret h).2.2.1]
  | tau p =>
    obtain ⟨-, -, hT⟩ := step_tau_cases h
    simp only [Label.proc] at hi
    cases hT <;> simp [Function.update_of_ne (show Obj.S i ≠ Obj.S p by simpa using Ne.symm hi)]

lemma Inv3At.transfer_other {C C' : Cfg A n} (hI : Inv1 C)
    (hcr : ∀ x, Completed α x → crOf C' x = crOf C x)
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {i : Fin n} (hK : Inv3At α C i)
    (hi : ℓ.proc ≠ i) (hS : C'.mem (.S i) = C.mem (.S i))
    (hhist : ∀ r g, (C.loc i).hist r = some g → (C'.loc i).hist r = some g) :
    Inv3At (α ++ [ℓ]) C' i := by
  have hl : C'.loc i = C.loc i := (Impl.step_other h hi).1
  have hnotinv : ∀ o, ℓ ≠ .inv i o := fun o he => hi (by rw [he]; rfl)
  have hnotret : ∀ r, ℓ ≠ .ret i r := fun r he => hi (by rw [he]; rfl)
  have hops : opsOf (α ++ [ℓ]) i = opsOf α i := opsOf_concat_of_ne hnotinv
  have hresps : respsOf (α ++ [ℓ]) i = respsOf α i := respsOf_concat_of_ne hnotret
  have hop : ∀ k, opOf (α ++ [ℓ]) (i, k) = opOf α (i, k) := fun k => by simp only [opOf, hops]
  have hresp : ∀ k, respOf (α ++ [ℓ]) (i, k) = respOf α (i, k) := fun k => by
    simp only [respOf, hresps]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hl, hops]; exact hK.seq
  · rw [hl, hop]; exact hK.cmd
  · rw [hl]; exact hK.wd
  · intro k hk
    rw [hresps] at hk
    obtain ⟨g, o, h1, h2, h3, h4, h5, h6⟩ := hK.compl k hk
    exact ⟨g, o, by rw [hl]; exact h1, h2, by rw [hl, hS]; exact h3, by rw [hop]; exact h4, h5,
      by rw [hresp]; exact h6⟩
  · intro j best hph x hx hxj
    rw [hl] at hph hx
    have hne : (C.loc i).phase ≠ .idle := by rw [hph]; simp
    obtain ⟨-, hs1, -⟩ := hK.cmd hne
    have hinv : Invoked α (i, (C.loc i).seq - 1) := by
      simp only [Invoked, ← hK.seq]; omega
    have hx' := (precedes_concat_iff hinv).1 hx
    rw [hcr x hx'.completed]
    exact hK.preS j best hph x hx' hxj

/-- Assemble `Inv3` after a step of `p`. -/
lemma Inv3.step_of {C C' : Cfg A n} (hK : Inv3 α C) (hI : Inv1 C)
    (h : (impl (A := A) (n := n)).step C ℓ = some C')
    (hcr : ∀ x, Completed α x → crOf C' x = crOf C x)
    (p : Fin n) (hpr : ℓ.proc = p)
    (hp : Inv3At (α ++ [ℓ]) C' p) (hknown : KnownOK (α ++ [ℓ]) C') :
    Inv3 (α ++ [ℓ]) C' := by
  refine ⟨fun i => ?_, hknown⟩
  by_cases hi : ℓ.proc = i
  · rw [← hi, hpr]; exact hp
  · exact (hK.at_ i).transfer_other hI hcr h hi (mem_S_other hI h hi)
      (fun r g hg => hist_mono_step hI h hg)

/-- Commands of a new proposal `t · cmd` to `GCA_R`, where `t` is `ε` or contains only commands
of inputs to `GCA_{R-1}`. -/
lemma known_snoc {C : Cfg A n} (hK : KnownOK α C) {R : ℕ} {t : Tr A n} {cmd : Cmd A n}
    (ht : ∀ c ∈ t.supp, ∃ j g, locAt (C.loc j) (R - 1) = some g ∧ c ∈ g.inp.supp)
    (hR : 1 ≤ R) (hcmd : ValidCmd α cmd ∧ ∀ x, Precedes α x (opId cmd) → crOf C x < R) :
    ∀ c ∈ (t.snoc cmd).supp, ValidCmd α c ∧ ∀ x, Precedes α x (opId c) → crOf C x < R := by
  intro c hc
  rw [NTrace.supp_snoc, Finset.mem_insert] at hc
  rcases hc with rfl | hc
  · exact hcmd
  · obtain ⟨j, g, hg, hcg⟩ := ht c hc
    obtain ⟨h1, h2⟩ := hK _ j g hg c hcg
    exact ⟨h1, fun x hx => by have := h2 x hx; omega⟩

/-- Steps inside `GCA_r` that keep the input, round, history and register. -/
lemma gca_step3 {C C' : Cfg A n} {p : Fin n} (hK : Inv3 α C) (hI : Inv1 C)
    (h : (impl (A := A) (n := n)).step C (.tau p) = some C')
    (hcr : ∀ x, Completed α x → crOf C' x = crOf C x)
    (base : ∀ (l' : Loc A n), l'.seq = (C.loc p).seq → l'.cmd = (C.loc p).cmd →
        (l'.phase ≠ .idle) → (∀ k, k < (respsOf α p).length → l'.cr (k + 1) = (C.loc p).cr (k + 1)) →
        (∀ r g, (C.loc p).hist r = some g → l'.hist r = some g) →
        (C.mem (.S p)).1 ≤ (C'.mem (.S p)).1 → C'.loc p = l' →
        (l'.phase = .writeS ∨ l'.phase = .done →
          l'.cr l'.seq = l'.r ∧ ∃ g, l'.hist l'.r = some g ∧ g.output = (l'.s, true)) →
        (∀ j best, l'.phase = .readS j best → ∀ x, Precedes α x (p, l'.seq - 1) →
          x.1.val < j → crOf C x ≤ best.1) →
        Inv3At (α ++ [.tau p]) C' p)
    {g g' : GCA.Loc n (Tr A n)} (hph : (C.loc p).phase = .gca g) (hinp : g'.inp = g.inp)
    (hlp : C'.loc p = { C.loc p with phase := .gca g' })
    (hS : C'.mem (.S p) = C.mem (.S p)) : Inv3 (α ++ [.tau p]) C' := by
  refine hK.step_of hI h hcr p rfl
    (base { C.loc p with phase := .gca g' } rfl rfl (by simp) (fun _ _ => rfl) (fun _ _ hg => hg)
      (by rw [hS]) hlp (by simp) (by simp)) (knownOK_transfer hK.known hcr ?_)
  intro r j g'' hg
  by_cases hj : j = p
  · subst hj
    rw [hlp, locAt_gca_step (l' := { C.loc j with phase := .gca g' }) hph rfl rfl rfl] at hg
    split_ifs at hg with hr
    · right; simp only [Option.some.injEq] at hg; subst hg
      rw [hinp]; exact hK.known r j g (by rw [locAt_gca hph]; simp [hr])
    · left; exact hg
  · left; rw [(Impl.step_other h (show (Label.tau p : Label (Fin n) A).proc ≠ j from Ne.symm hj)).1] at hg
    exact hg

theorem Inv3.step {C C' : Cfg A n} (hrun : (impl (A := A) (n := n)).run α = some C)
    (hI : Inv1 C) (hJ : Inv2 C) (hK : Inv3 α C)
    (h : (impl (A := A) (n := n)).step C ℓ = some C') : Inv3 (α ++ [ℓ]) C' := by
  have hI' := hI.step h
  have hcr : ∀ x, Completed α x → crOf C' x = crOf C x := fun x hx => crOf_step hrun hI hK.at_ h hx
  cases ℓ with
  | inv p o =>
    obtain ⟨hpd, -, -, hloc, hmem⟩ := Impl.step_inv h
    have hidle := (hI.loc p).pend_iff.1 hpd
    have hlp : C'.loc p = invoke p (C.loc p) o := by rw [hloc]; simp; rfl
    have hKp := hK.at_ p
    have hcnt : (opsOf α p).length = (respsOf α p).length := by
      rcases counts hrun hI p with h1 | h1
      · exact h1.2
      · exact absurd hidle h1.1
    refine hK.step_of hI h hcr p rfl ⟨?_, ?_, ?_, ?_, ?_⟩ (knownOK_transfer hK.known hcr ?_)
    · rw [hlp]; simp [invoke, opsOf_concat, hKp.seq]
    · rw [hlp]; intro _
      refine ⟨rfl, by simp [invoke], ?_⟩
      simp [invoke, opOf_concat_inv, hKp.seq]
    · rw [hlp]; simp [invoke]
    · intro k hk
      simp [respsOf_concat] at hk
      obtain ⟨g, o', h1, h2, h3, h4, h5, h6⟩ := hKp.compl k hk
      have hinv : Invoked α (p, k) := by simp only [Invoked]; omega
      refine ⟨g, o', ?_, h2, ?_, ?_, h5, ?_⟩
      · rw [hlp]; exact h1
      · rw [hlp, hmem]; exact h3
      · rw [opOf_append_of_invoked hinv]; exact h4
      · rw [respOf_append_of_completed (by simp only [Completed]; omega)]; exact h6
    · rw [hlp]; intro j best hph x _ hxj
      simp only [invoke, Phase.readS.injEq] at hph; omega
    · intro r j g hg; left
      by_cases hj : j = p
      · subst hj; rw [hlp] at hg; unfold locAt at hg ⊢; simpa [invoke, hidle] using hg
      · rw [hloc] at hg; simpa [hj] using hg
  | ret p r' =>
    obtain ⟨hdone, hr', hC'⟩ := step_ret_cases h (hI.loc p)
    have hlp : C'.loc p = { C.loc p with phase := .idle } := by rw [hC']; simp
    have hmem : C'.mem = C.mem := by rw [hC']
    have hKp := hK.at_ p
    have hne : (C.loc p).phase ≠ .idle := by rw [hdone]; simp
    obtain ⟨hcmd2, hs1, hop⟩ := hKp.cmd hne
    obtain ⟨hcrs, g, hgh, hgo⟩ := hKp.wd (Or.inr hdone)
    have hcnt : (opsOf α p).length = (respsOf α p).length + 1 := by
      rcases counts hrun hI p with h1 | h1
      · exact absurd h1.1 hne
      · exact h1.2
    have hseq := hKp.seq
    refine hK.step_of hI h hcr p rfl ⟨?_, ?_, ?_, ?_, ?_⟩ (knownOK_transfer hK.known hcr ?_)
    · rw [hlp]; simp [opsOf_concat, hseq]
    · rw [hlp]; simp
    · rw [hlp]; simp
    · intro k hk
      simp [respsOf_concat] at hk
      rcases Nat.lt_or_eq_of_le hk with hk | hk
      · obtain ⟨g', o', h1, h2, h3, h4, h5, h6⟩ := hKp.compl k hk
        refine ⟨g', o', by rw [hlp]; exact h1, h2, by rw [hlp, hmem]; exact h3, ?_, h5, ?_⟩
        · rw [opOf_append_of_invoked (by simp only [Invoked]; omega)]; exact h4
        · rw [respOf_append_of_completed (by simp only [Completed]; omega)]; exact h6
      · subst hk
        have hk1 : (respsOf α p).length + 1 = (C.loc p).seq := by omega
        have hcmd : (C.loc p).cmd = ((C.loc p).cmd.1, p, (respsOf α p).length + 1) := by
          rw [hk1]; ext <;> simp [hcmd2]
        obtain ⟨-, hmemcmd⟩ := hJ.com p (Or.inr hdone)
        refine ⟨g, (C.loc p).cmd.1, ?_, by rw [hgo], ?_, ?_, ?_, ?_⟩
        · rw [hlp]; simpa [hk1, hcrs] using hgh
        · rw [hlp, hmem]; simp [hk1, hcrs, (hI.loc p).sreg_done hdone]
        · rw [opOf_append_of_invoked (by simp only [Invoked]; omega)]
          rw [show (respsOf α p).length = (C.loc p).seq - 1 by omega]; exact hop
        · rw [hgo]; rw [← hcmd]; exact hmemcmd
        · rw [respOf_append_ret, if_pos rfl, hgo, hr', ← hcmd]
    · rw [hlp]; intro j best hph; simp at hph
    · intro r j g' hg; left
      by_cases hj : j = p
      · subst hj; rw [hlp] at hg; unfold locAt at hg ⊢; simpa [hdone] using hg
      · rw [hC'] at hg; simpa [hj] using hg
  | tau p =>
    obtain ⟨hpn, -, hT⟩ := step_tau_cases h
    have hnotinv : ∀ i o, Label.tau p ≠ (.inv i o : Label (Fin n) A) := fun _ _ => by simp
    have hnotret : ∀ i r, Label.tau p ≠ (.ret i r : Label (Fin n) A) := fun _ _ => by simp
    have hops : ∀ i, opsOf (α ++ [.tau p]) i = opsOf α i := fun i => opsOf_concat_of_ne (hnotinv i)
    have hresps : ∀ i, respsOf (α ++ [.tau p]) i = respsOf α i :=
      fun i => respsOf_concat_of_ne (hnotret i)
    have hop : ∀ x, opOf (α ++ [.tau p]) x = opOf α x := fun x => by simp only [opOf, hops]
    have hresp : ∀ x, respOf (α ++ [.tau p]) x = respOf α x := fun x => by
      simp only [respOf, hresps]
    have hprec : ∀ x y, Precedes (α ++ [.tau p]) x y ↔ Precedes α x y :=
      fun x y => ⟨Precedes.of_concat_of_not_ret hnotret, Precedes.mono⟩
    have hKp := hK.at_ p
    have hL := hI.loc p
    -- the part of `Inv3At` that only depends on unchanged data
    have base : ∀ (l' : Loc A n), l'.seq = (C.loc p).seq → l'.cmd = (C.loc p).cmd →
        (l'.phase ≠ .idle) → (∀ k, k < (respsOf α p).length → l'.cr (k + 1) = (C.loc p).cr (k + 1)) →
        (∀ r g, (C.loc p).hist r = some g → l'.hist r = some g) →
        (C.mem (.S p)).1 ≤ (C'.mem (.S p)).1 → C'.loc p = l' →
        (l'.phase = .writeS ∨ l'.phase = .done →
          l'.cr l'.seq = l'.r ∧ ∃ g, l'.hist l'.r = some g ∧ g.output = (l'.s, true)) →
        (∀ j best, l'.phase = .readS j best → ∀ x, Precedes α x (p, l'.seq - 1) →
          x.1.val < j → crOf C x ≤ best.1) →
        Inv3At (α ++ [.tau p]) C' p := by
      intro l' hseq hcmd hne hcr' hhist hS hl' hwd hpre
      have hne0 : (C.loc p).phase ≠ .idle := fun h' => hpn ((hI.loc p).pend_iff.2 h')
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hl']
      · rw [hops, hseq]; exact hKp.seq
      · intro _; rw [hseq, hcmd, hop]; exact hKp.cmd hne0
      · exact hwd
      · intro k hk
        rw [hresps] at hk
        obtain ⟨g, o, h1, h2, h3, h4, h5, h6⟩ := hKp.compl k hk
        exact ⟨g, o, by rw [hcr' k hk]; exact hhist _ _ h1, h2, by rw [hcr' k hk]; omega,
          by rw [hop]; exact h4, h5, by rw [hresp]; exact h6⟩
      · intro j best hph x hx hxj
        rw [hprec] at hx
        rw [hcr x hx.completed]
        exact hpre j best hph x hx hxj
    -- `crOf C x ≤ (S[x.1]).1` for completed operations
    have hcrS : ∀ x, Completed α x → crOf C x ≤ (C.mem (.S x.1)).1 := fun x hx => by
      obtain ⟨g, o, -, -, h3, -⟩ := (hK.at_ x.1).compl x.2 hx; exact h3
    cases hT with
    | readS j best hj hph hlt =>
      refine hK.step_of hI h hcr p rfl
        (base { C.loc p with phase := .readS (j + 1) (better best (C.mem (.S ⟨j, hj⟩))) } rfl rfl
          (by simp) (fun _ _ => rfl) (fun _ _ hg => hg) le_rfl (by simp) (by simp) ?_)
        (knownOK_transfer hK.known hcr ?_)
      · rintro j' b' hb x hx hxj
        simp only [Phase.readS.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
        rcases Nat.lt_succ_iff_lt_or_eq.1 hxj with hxj | hxj
        · exact (hKp.preS j best hph x hx hxj).trans (better_left _ _)
        · have hx1 : x.1 = ⟨j, hj⟩ := Fin.ext hxj
          have := hcrS x hx.completed
          rw [hx1] at this
          exact this.trans (better_right _ _)
      · intro r j' g hg; left
        by_cases hj' : j' = p
        · subst hj'; simp only [setLoc_loc, Function.update_self] at hg
          unfold locAt at hg ⊢; simpa [hph] using hg
        · simpa [hj'] using hg
    | readLast j best hj hph hlt =>
      set b := better best (C.mem (.S ⟨j, hj⟩)) with hbdef
      have hne0 : (C.loc p).phase ≠ .idle := by rw [hph]; simp
      obtain ⟨hcmd2, hs1, hopc⟩ := hKp.cmd hne0
      have hvalid : ValidCmd α (C.loc p).cmd := ⟨by rw [hcmd2]; exact hs1, by
        simp only [opId, hcmd2]; exact hopc⟩
      have hprecb : ∀ x, Precedes α x (opId (C.loc p).cmd) → crOf C x < b.1 + 1 := by
        intro x hx
        simp only [opId, hcmd2] at hx
        have hxj : x.1.val ≤ j := by have := x.1.isLt; omega
        suffices crOf C x ≤ b.1 by omega
        rw [hbdef]
        rcases Nat.lt_or_eq_of_le hxj with hxj | hxj
        · exact (hKp.preS j best hph x hx hxj).trans (better_left best _)
        · have hx1 : x.1 = ⟨j, hj⟩ := Fin.ext hxj
          have := hcrS x hx.completed
          rw [hx1] at this
          exact this.trans (better_right best _)
      have hsvb := sv_better (hJ.best p j best hph) (hJ.sv ⟨j, hj⟩)
      have ht : ∀ c ∈ b.2.supp, ∃ j' g, locAt (C.loc j') (b.1 + 1 - 1) = some g ∧
          c ∈ g.inp.supp := by
        intro c hc
        rcases hsvb with ⟨-, h2⟩ | ⟨-, q, gq, hq, hpcq, hout, -⟩
        · rw [h2, NTrace.supp_bot] at hc; simp at hc
        · simp only [Nat.add_sub_cancel]
          exact mem_input_of_mem_output hI hq hpcq (by rw [hout]; exact hc)
      refine hK.step_of hI h hcr p rfl
        (base ((C.loc p).afterRead b) (by simp [Loc.afterRead, Loc.startRound])
          (by simp [Loc.afterRead, Loc.startRound]) (by simp [Loc.afterRead, Loc.startRound])
          (fun _ _ => rfl) (fun _ _ hg => hg) le_rfl (by simp)
          (by simp [Loc.afterRead, Loc.startRound]) (by simp [Loc.afterRead, Loc.startRound]))
        (knownOK_transfer hK.known hcr ?_)
      intro r j' g hg
      by_cases hj' : j' = p
      · subst hj'
        simp only [setLoc_loc, Function.update_self] at hg
        rw [locAt_gca (g := GCA.Loc.init (b.2.snoc (C.loc j').cmd))
          (by simp [Loc.afterRead, Loc.startRound])] at hg
        split_ifs at hg with hr
        · right
          simp only [Option.some.injEq] at hg; subst hg
          simp only [Loc.afterRead, Loc.startRound] at hr; subst hr
          exact known_snoc hK.known ht (by omega) ⟨hvalid, hprecb⟩
        · left; rw [locAt_of_not_gca (by simp [hph])]
          simpa [Loc.afterRead, Loc.startRound] using hg
      · left; simpa [hj'] using hg
    | gca0 g hph hpc =>
      exact gca_step3 (g' := { g with pc := 1 }) hK hI h hcr base hph rfl (by simp)
        (by simp [Function.update_of_ne (show Obj.S p ≠ Obj.A (C.loc p).r by simp)])
    | gca1 g hph hpc =>
      exact gca_step3 (g' := { g with pc := 2, av := C.mem (.A (C.loc p).r) }) hK hI h hcr base hph
        rfl (by simp) (by simp)
    | gca2 g hph hpc =>
      exact gca_step3 (g' := { g with pc := 3 }) hK hI h hcr base hph rfl (by simp)
        (by simp [Function.update_of_ne (show Obj.S p ≠ Obj.B (C.loc p).r by simp)])
    | gca3 g hph hpc =>
      have hne0 : (C.loc p).phase ≠ .idle := by rw [hph]; simp
      obtain ⟨hcmd2, hs1, hopc⟩ := hKp.cmd hne0
      obtain ⟨hr1, hrn, -⟩ := hL.gca g hph
      have hcnt : (opsOf α p).length = (respsOf α p).length + 1 := by
        rcases counts hrun hI p with h1 | h1
        · exact absurd h1.1 hne0
        · exact h1.2
      have hseq := hKp.seq
      have hkne : ∀ k, k < (respsOf α p).length → k + 1 ≠ (C.loc p).seq := fun k hk => by omega
      set g4 : GCA.Loc n (Tr A n) := { g with pc := 4, bv := C.mem (.B (C.loc p).r) } with hg4
      have hhist' : ∀ r g', (C.loc p).hist r = some g' →
          Function.update (C.loc p).hist (C.loc p).r (some g4) r = some g' := by
        intro r g' hg'
        have hr : r ≠ (C.loc p).r := by rintro rfl; rw [hrn] at hg'; cases hg'
        rw [Function.update_of_ne hr]; exact hg'
      have hknown_r : ∀ c ∈ g4.inp.supp, ValidCmd α c ∧
          ∀ x, Precedes α x (opId c) → crOf C x < (C.loc p).r :=
        hK.known (C.loc p).r p g (by rw [locAt_gca hph]; simp)
      by_cases hex : g4.output.2 = true ∧ (C.loc p).cmd ∈ g4.output.1.supp
      · have hl' : (C.loc p).afterGCA g4 = { C.loc p with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4), s := g4.output.1,
            phase := .writeS, cr := Function.update (C.loc p).cr (C.loc p).seq (C.loc p).r } := by
          simp [Loc.afterGCA, hex]
        refine hK.step_of hI h hcr p rfl
          (base { C.loc p with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4), s := g4.output.1,
            phase := .writeS, cr := Function.update (C.loc p).cr (C.loc p).seq (C.loc p).r }
            rfl rfl (by simp) (fun k hk => by simp [Function.update_of_ne (hkne k hk)])
            hhist' le_rfl (by simp [hl']) ?_ (by simp)) (knownOK_transfer hK.known hcr ?_)
        · intro _
          refine ⟨by simp, g4, by simp, ?_⟩
          simp only
          rw [← hex.1]
        · intro r j g'' hg
          by_cases hj : j = p
          · subst hj
            simp only [setLoc_loc, Function.update_self, hl'] at hg
            rw [locAt_of_not_gca (by simp)] at hg
            by_cases hr : r = (C.loc j).r
            · right; subst hr; simp only [Function.update_self, Option.some.injEq] at hg
              subst hg; exact hknown_r
            · left; simp only [Function.update_of_ne hr] at hg
              rw [locAt_gca hph]; simp [hr, hg]
          · left; simpa [hj] using hg
      · have hl' : (C.loc p).afterGCA g4 = { (C.loc p).startRound (C.loc p).r g4.output.1 with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4) } := by
          simp only [Loc.afterGCA, hex, if_false]
        refine hK.step_of hI h hcr p rfl
          (base { (C.loc p).startRound (C.loc p).r g4.output.1 with
            hist := Function.update (C.loc p).hist (C.loc p).r (some g4) }
            (by simp [Loc.startRound]) (by simp [Loc.startRound]) (by simp [Loc.startRound])
            (fun k hk => by simp [Loc.startRound]) hhist' le_rfl (by simp [hl'])
            (by simp [Loc.startRound]) (by simp [Loc.startRound]))
          (knownOK_transfer hK.known hcr ?_)
        intro r j g'' hg
        by_cases hj : j = p
        · subst hj
          simp only [setLoc_loc, Function.update_self, hl'] at hg
          rw [locAt_gca (g := GCA.Loc.init (g4.output.1.snoc (C.loc j).cmd))
            (by simp [Loc.startRound])] at hg
          split_ifs at hg with hr
          · right
            simp only [Option.some.injEq] at hg; subst hg
            simp only [Loc.startRound] at hr; subst hr
            refine known_snoc hK.known ?_ (by omega) ?_
            · intro c hc
              have hloc4 : locAt ((setLoc C j ((C.loc j).afterGCA g4)).loc j) (C.loc j).r =
                  some g4 := by
                simp only [setLoc_loc, Function.update_self, hl']
                rw [locAt_eq_hist_of_ne (by simp [Loc.startRound])]; simp
              obtain ⟨j', g', hg', hc'⟩ := mem_input_of_mem_output hI' hloc4 rfl hc
              simp only [Nat.add_sub_cancel]
              by_cases hj' : j' = j
              · subst hj'
                rw [hloc4] at hg'; simp only [Option.some.injEq] at hg'; subst hg'
                exact ⟨j', g, by rw [locAt_gca hph]; simp, hc'⟩
              · exact ⟨j', g', by simpa [hj'] using hg', hc'⟩
            · obtain ⟨t, -, ht⟩ := hJ.cur j g hph
              have hcm : (C.loc j).cmd ∈ g4.inp.supp := by
                simp [hg4, ht, NTrace.supp_snoc]
              obtain ⟨hv, hpr⟩ := hknown_r _ hcm
              exact ⟨hv, fun x hx => by have := hpr x hx; omega⟩
          · by_cases hr' : r = (C.loc j).r
            · right; subst hr'; simp only [Loc.startRound, Function.update_self,
                Option.some.injEq] at hg
              subst hg; exact hknown_r
            · left; simp only [Loc.startRound, Function.update_of_ne hr'] at hg
              rw [locAt_gca hph]; simp [hr', hg]
        · left; simpa [hj] using hg
    | writeS hph =>
      have hlt := hL.sreg_writeS hph
      refine hK.step_of hI h hcr p rfl
        (base { C.loc p with phase := .done } rfl rfl (by simp) (fun _ _ => rfl) (fun _ _ hg => hg)
          (by simp; omega) (by simp) (fun _ => by simpa using hKp.wd (Or.inl hph)) (by simp))
        (knownOK_transfer hK.known hcr ?_)
      intro r j g hg; left
      by_cases hj : j = p
      · subst hj; simp only [setMemLoc_loc, Function.update_self] at hg
        unfold locAt at hg ⊢; simpa [hph] using hg
      · simpa [hj] using hg

theorem inv3_init : Inv3 ([] : List (Label (Fin n) A)) (impl (A := A) (n := n)).initCfg := by
  refine ⟨fun i => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Impl.initCfg, impl, KnownOK, locAt]

/-- The invariants `Inv1`, `Inv2`, `Inv3` hold along every execution. -/
theorem inv_of_run {α : List (Label (Fin n) A)} {C : Cfg A n}
    (h : (impl (A := A) (n := n)).run α = some C) : Inv1 C ∧ Inv2 C ∧ Inv3 α C :=
  Impl.run_induction (Q := fun α C => Inv1 C ∧ Inv2 C ∧ Inv3 α C) ⟨inv1_init, inv2_init, inv3_init⟩
    (fun α C ℓ C' hrun hQ hs => ⟨hQ.1.step hs, hQ.2.1.step hQ.1 hs, hQ.2.2.step hrun hQ.1 hQ.2.1 hs⟩)
    h

end Alg1

end Podc.ConflictFreedom
