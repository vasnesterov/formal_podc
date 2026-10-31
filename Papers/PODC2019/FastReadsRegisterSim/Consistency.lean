import Papers.PODC2019.FastReadsRegisterSim.Defs

/-!
# Atomic ⇒ regular ⇒ safe; responses of reads in a linearization

* `regularHist_of_atomicHist`, `safeHist_of_regularHist` and the simulation-level versions
  `Sim.Atomic.regular`, `Sim.Regular.safe`.
* `resp_of_split`, `lt_of_split`, `resp_reads`: in a linearization of a history in which only
  `c` changes the state, a completed operation `x` gets the response it would get after a prefix
  of `c`'s operations whose length is at least the number of `c`'s operations preceding `x`; for
  two operations `x → y` (real time) the prefix of `y` is at least as long as the prefix of `x`
  (no new–old inversion). -- CSLib candidate (`SharedMemory/Linearization.lean`)
-/

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory Cslib.SharedMemory.IsLinearization List

/-! ## General facts on linearizations (any object) -/

section General

variable {P : Type} [DecidableEq P] {A : ObjSpec} {α : List (Label P A)}
  {Lin : List (OpId P × A.Op)}

/-- Response of an operation at a given position of a linearization. -- CSLib candidate -/
lemma resp_of_split (hL : IsLinearization α Lin) (hα : WellFormed α) (c : P)
    (hro : ∀ y ∈ Lin, y.1.1 ≠ c → A.ReadOnly y.2) {L₁ L₂ : List (OpId P × A.Op)}
    {x : OpId P} {o : A.Op} {r : A.Resp}
    (hs : Lin = L₁ ++ (x, o) :: L₂) (hx : respOf α x = some r) :
    opOf α x = some o ∧
      r = (A.δ (A.runOps A.init ((opsOf α c).take (procIds L₁ c).length)) o).2 := by
  have hseq := (seqOK_append (α := α) A.init L₁ ((x, o) :: L₂)).1 (hs ▸ hL.seq)
  refine ⟨hL.op_eq (x, o) (by rw [hs]; simp), ?_⟩
  rw [← hseq.2.1 r hx, hL.runOps_prefix hα c hro L₁ _ hs]

/-- Operations of `c` that precede `x` in real time are linearized before `x`.
-- CSLib candidate -/
lemma lt_of_split (hL : IsLinearization α Lin) (hα : WellFormed α) (c : P)
    {L₁ L₂ : List (OpId P × A.Op)} {x : OpId P} {o : A.Op}
    (hs : Lin = L₁ ++ (x, o) :: L₂) {j : ℕ} (hpre : Precedes α (c, j) x) :
    j < (procIds L₁ c).length := by
  have hp := hL.realtime _ _ hpre (by rw [hs]; simp)
  rw [hs, map_append, map_cons] at hp
  have hnd := hL.nodup; rw [hs, map_append, map_cons] at hnd
  have hm := mem_left_of_sublist_pair hnd hp
  have hm' : (c, j) ∈ procIds L₁ c := by simp [procIds, hm]
  have heq := hL.procIds_eq hα c
  have hpre' : procIds L₁ c <+: procIds Lin c := by
    rw [hs]; simp only [procIds, map_append, filter_append]; exact prefix_append _ _
  obtain ⟨t, ht⟩ := hpre'
  have hform : procIds L₁ c = (procIds Lin c).take (procIds L₁ c).length := by
    rw [← ht]; simp
  rw [hform, heq, ← map_take, take_range] at hm'
  simp only [mem_map, mem_range, Prod.mk.injEq, true_and, lt_min_iff] at hm'
  omega

lemma procIds_split_le (hL : IsLinearization α Lin) (hα : WellFormed α) (c : P)
    {L₁ L₂ : List (OpId P × A.Op)} (hs : Lin = L₁ ++ L₂) :
    (procIds L₁ c).length ≤ (opsOf α c).length := by
  have h1 : (procIds L₁ c).length ≤ (procIds Lin c).length := by
    simp only [procIds, hs, map_append, filter_append, length_append]; omega
  exact h1.trans (hL.procIds_length hα c).2

/-- **Responses of two reads `x → y`** (no new–old inversion): if only `c` changes the state,
the responses of completed operations `x`, `y` with `x → y` are the responses after prefixes of
`c`'s operations of lengths `j ≤ j'`, where `j` is at least the number `M₀` of `c`'s operations
that precede `x`. -- CSLib candidate -/
theorem resp_reads (hL : IsLinearization α Lin) (hα : WellFormed α) (c : P)
    (hro : ∀ y ∈ Lin, y.1.1 ≠ c → A.ReadOnly y.2) {x y : OpId P} {r r' : A.Resp}
    (hx : respOf α x = some r) (hy : respOf α y = some r') (hxy : Precedes α x y)
    (M₀ : ℕ) (hpre : ∀ j < M₀, Precedes α (c, j) x) :
    ∃ j j', M₀ ≤ j ∧ j ≤ j' ∧ j' ≤ (opsOf α c).length ∧
      (∃ o, opOf α x = some o ∧ r = (A.δ (A.runOps A.init ((opsOf α c).take j)) o).2) ∧
      (∃ o', opOf α y = some o' ∧ r' = (A.δ (A.runOps A.init ((opsOf α c).take j')) o').2) := by
  have hxc : Completed α x := by
    simp only [respOf] at hx; exact (List.getElem?_eq_some_iff.1 hx).1
  have hyc : Completed α y := by
    simp only [respOf] at hy; exact (List.getElem?_eq_some_iff.1 hy).1
  obtain ⟨⟨x', o⟩, hxL, hxx⟩ := mem_map.1 (hL.complete x hxc)
  simp only at hxx; subst hxx
  obtain ⟨L₁, L₂, hs⟩ := append_of_mem hxL
  -- `y` comes after `x`
  have hsub := hL.realtime _ _ hxy (hL.complete y hyc)
  have hnd := hL.nodup
  rw [hs, map_append, map_cons] at hsub hnd
  have hyL₂ : y ∈ L₂.map Prod.fst := by
    obtain ⟨r₁, r₂, he, hx1, hy2⟩ := sublist_pair_iff.1 hsub
    by_contra hny
    have hyx : y ≠ x' := by
      rintro rfl
      exact not_sublist_pair_both hnd hsub hsub
    have hy1 : y ∈ L₁.map Prod.fst := by
      have : y ∈ L₁.map Prod.fst ++ x' :: L₂.map Prod.fst := by
        rw [he]; exact mem_append_right _ hy2
      simp only [mem_append, mem_cons] at this
      rcases this with h | h | h
      · exact h
      · exact absurd h hyx
      · exact absurd h hny
    exact not_sublist_pair_both hnd hsub
      ((sublist_pair_iff).2 ⟨L₁.map Prod.fst, x' :: L₂.map Prod.fst, rfl, hy1, by simp⟩)
  obtain ⟨⟨y', o'⟩, hyL, hyy⟩ := mem_map.1 hyL₂
  simp only at hyy; subst hyy
  obtain ⟨L₃, L₄, hs₂⟩ := append_of_mem hyL
  have hs' : Lin = (L₁ ++ (x', o) :: L₃) ++ (y', o') :: L₄ := by rw [hs, hs₂]; simp
  obtain ⟨hox, hrx⟩ := resp_of_split hL hα c hro hs hx
  obtain ⟨hoy, hry⟩ := resp_of_split hL hα c hro hs' hy
  refine ⟨_, _, ?_, ?_, procIds_split_le hL hα c hs', ⟨o, hox, hrx⟩, ⟨o', hoy, hry⟩⟩
  · rcases Nat.eq_zero_or_pos M₀ with h0 | h0
    · omega
    · have := lt_of_split hL hα c hs (hpre (M₀ - 1) (by omega)); omega
  · simp only [procIds, map_append, filter_append, length_append]; omega

end General

/-! ## Registers -/

section Register

variable {V : Type} {v₀ : V} {P : Type} [DecidableEq P]

omit [DecidableEq P] in
/-- The state of a register after a list of operations: the last written value, or the initial
state if nothing is written. -/
lemma runOps_register_cases (q : V) (Ls : List (OpId P × RWOp V)) :
    ((∀ e ∈ Ls, e.2 = .read) ∧ (register V v₀).runOps q (Ls.map Prod.snd) = q) ∨
    ∃ As y u Bs, Ls = As ++ (y, .write u) :: Bs ∧ (∀ e ∈ Bs, e.2 = .read) ∧
      (register V v₀).runOps q (Ls.map Prod.snd) = u := by
  induction Ls using List.reverseRecOn with
  | nil => left; exact ⟨by simp, rfl⟩
  | append_singleton Ls e ih =>
    obtain ⟨y, o⟩ := e
    cases o with
    | read =>
      rcases ih with ⟨h1, h2⟩ | ⟨As, y', u, Bs, h1, h2, h3⟩
      · left
        refine ⟨fun e he => ?_, ?_⟩
        · rcases mem_append.1 he with h | h
          · exact h1 e h
          · simp at h; rw [h]
        · rw [map_append, ObjSpec.runOps_append, h2]; rfl
      · right
        refine ⟨As, y', u, Bs ++ [(y, .read)], by rw [h1]; simp, fun e he => ?_, ?_⟩
        · rcases mem_append.1 he with h | h
          · exact h2 e h
          · simp at h; rw [h]
        · rw [map_append, ObjSpec.runOps_append, h3]; rfl
    | write v =>
      right
      exact ⟨Ls, y, v, [], rfl, by simp, by rw [map_append, ObjSpec.runOps_append]; rfl⟩

variable {ι L : Type} [DecidableEq ι]

/-- **Atomicity implies regularity** (for histories of a register; any number of writers). -/
theorem regularHist_of_atomicHist {α : List (Label P (register V v₀))}
    (h : AtomicHist v₀ α) : RegularHist v₀ α := by
  obtain ⟨Lin, hL⟩ := h
  intro x v ⟨hop, hresp⟩
  have hxc : Completed α x := by
    simp only [respOf] at hresp; exact (List.getElem?_eq_some_iff.1 hresp).1
  obtain ⟨⟨x', o⟩, hxL, hxx⟩ := mem_map.1 (hL.complete x hxc)
  simp only at hxx; subst hxx
  obtain ⟨L₁, L₂, hs⟩ := append_of_mem hxL
  have ho : o = .read := by
    have := hL.op_eq _ hxL; rw [hop] at this; simp only [Option.some.injEq] at this
    exact this.symm
  subst ho
  have hseq := (seqOK_append (α := α) (register V v₀).init L₁ ((x', .read) :: L₂)).1
    (hs ▸ hL.seq)
  have hv : (register V v₀).runOps v₀ (L₁.map Prod.snd) = v := hseq.2.1 v hresp
  have hnd := hL.nodup
  rw [hs, map_append, map_cons] at hnd
  -- writes preceding `x` are linearized in `L₁`
  have hbefore : ∀ y u, IsWrite v₀ α y u → Precedes α y x' →
      ∃ e ∈ L₁, e = (y, .write u) := by
    intro y u hy hyx
    have hp := hL.realtime _ _ hyx (by rw [hs]; simp)
    rw [hs, map_append, map_cons] at hp
    have hm := mem_left_of_sublist_pair hnd hp
    obtain ⟨e, he, rfl⟩ := mem_map.1 hm
    refine ⟨e, he, ?_⟩
    have := hL.op_eq e (by rw [hs]; exact mem_append_left _ he)
    rw [hy] at this; simp only [Option.some.injEq] at this
    exact Prod.ext rfl this.symm
  rcases runOps_register_cases (v₀ := v₀) v₀ L₁ with ⟨hr, hq⟩ | ⟨As, y, u, Bs, hL₁, hBs, hq⟩
  · left
    refine ⟨by rw [← hv, hq], fun y u hy hyx => ?_⟩
    obtain ⟨e, he, rfl⟩ := hbefore y u hy hyx
    simpa using hr _ he
  · right
    have huv : u = v := by rw [← hv, hq]
    subst huv
    have hyL : (y, RWOp.write u) ∈ Lin := by rw [hs, hL₁]; simp
    refine ⟨y, hL.op_eq _ hyL, ?_, ?_⟩
    · intro hxy
      have hp := hL.realtime _ _ hxy (mem_map.2 ⟨_, hyL, rfl⟩)
      apply not_sublist_pair_both hL.nodup hp
      rw [hs, hL₁]
      simp only [map_append, map_cons, append_assoc, cons_append]
      exact (sublist_pair_iff).2 ⟨As.map Prod.fst ++ [y], Bs.map Prod.fst ++ x' :: L₂.map Prod.fst,
        by simp, by simp, by simp⟩
    · rintro y' u' hy' ⟨h1, h2⟩
      obtain ⟨e, he, rfl⟩ := hbefore y' u' hy' h2
      have hp := hL.realtime _ _ h1 (by rw [hs]; exact mem_map.2 ⟨_, mem_append_left _ he, rfl⟩)
      rw [hL₁] at he
      rcases mem_append.1 he with he | he
      · -- `y'` linearized before `y`
        apply not_sublist_pair_both hL.nodup hp
        rw [hs, hL₁]
        simp only [map_append, map_cons, append_assoc, cons_append]
        exact (sublist_pair_iff).2 ⟨As.map Prod.fst, y :: (Bs.map Prod.fst ++ x' :: L₂.map Prod.fst),
          by simp, mem_map.2 ⟨_, he, rfl⟩, by simp⟩
      · rcases mem_cons.1 he with he | he
        · simp only [Prod.mk.injEq] at he
          rw [he.1] at hp
          have := hL.nodup.sublist hp; simp at this
        · simpa using hBs _ he

/-- Regularity implies safety. -/
theorem safeHist_of_regularHist {α : List (Label P (register V v₀))}
    (h : RegularHist v₀ α) : SafeHist v₀ α :=
  fun x v hx _ => h x v hx

theorem Sim.Atomic.regular {I : Sim V v₀ ι P L} {w : P} (h : I.Atomic w) : I.Regular w :=
  fun α hα hsw => regularHist_of_atomicHist (h α hα hsw)

theorem Sim.Regular.safe {I : Sim V v₀ ι P L} {w : P} (h : I.Regular w) : I.Safe w :=
  fun α hα hsw => safeHist_of_regularHist (h α hα hsw)

end Register

end Podc.FastReadsRegisterSim
