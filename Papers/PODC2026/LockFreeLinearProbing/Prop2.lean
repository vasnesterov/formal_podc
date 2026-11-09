import Papers.PODC2026.LockFreeLinearProbing.Lemma4
import Papers.PODC2026.LockFreeLinearProbing.Lookup

/-!
# Proposition 2: no spurious `ABORT`

If `insert(v)` is invoked when some cell is `EMPTY` or `TOMBSTONE` and no cell contains `v`, then
before the operation returns, some available cell (`EMPTY`/`TOMBSTONE`) is overwritten with a
(tentative) key.

The proof classifies the writes of the algorithm (`writeRel`): the only write that overwrites an
available cell is line 43 (a tentative copy), and the only writes that create a copy of `v` in a
cell that holds no copy of `v` are again line 43.
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ}

/-- The possible overwrites `u ↦ w` by a successful `SC` of an operation on key `k`. -/
def writeRel (k : K) (u w : Cell K) : Prop :=
  (u = .key k .tent ∧ w = .key k .reval) ∨ (u = .key k .fin ∧ w = .tomb) ∨
  (u.key? = some k ∧ u ≠ .key k .fin ∧ w = .deleted) ∨
  ((u = .empty ∨ u = .tomb) ∧ w = .key k .tent) ∨ (u = .key k .tent ∧ w = .collided) ∨
  (u = .key k .reval ∧ w = .key k .tent) ∨ (u = .key k .tent ∧ w = .key k .fin) ∨
  (OwnCell k u ∧ w = .tomb)

/-- The `SC`s of the program: where they write and what. -/
lemma act_sc {q q' : P} {l : Loc K m} {x : Fin m} {w : Cell K}
    {k : Cell K × Bool → Loc K m} (hact : act h q l = .access x (.sc q' w) k) :
    q' = q ∧ (∃ y w0, recorded l = some (y, w0) ∧ y = x) ∧
    ((l.pc = .vcSC ∧ w = .key l.op.key .reval) ∨ (l.pc = .tdSCF ∧ w = .tomb) ∨
     (l.pc = .tdSCD ∧ w = .deleted) ∨ (l.pc = .iSC ∧ w = .key l.op.key .tent) ∨
     (l.pc = .docSC ∧ w = .collided) ∨ (l.pc = .l58SC ∧ w = .key l.op.key .tent) ∨
     (l.pc = .l67SC ∧ w = .key l.op.key .fin) ∨ (l.pc = .l69SC ∧ w = .key l.op.key .tent) ∨
     (l.pc = .dcSC78 ∧ w = .key l.op.key .tent) ∨ (l.pc = .dcSC80 ∧ w = .tomb)) := by
  unfold act at hact
  rcases hpc : l.pc <;> rw [hpc] at hact <;> simp only at hact <;> cases hact <;>
    simp [recorded, hpc]

/-- A successful `SC` performs one of the overwrites of `writeRel`. -/
lemma writeRel_of_sc {C : Cfg K m P} (hI : Inv h N ts C) {q : P} {x : Fin m} {w : Cell K}
    {k : Cell K × Bool → Loc K m} (hact : act h q (C.loc q) = .access x (.sc q w) k)
    (hsc : q ∈ C.lks x) : writeRel (C.loc q).op.key (C.val x) w := by
  obtain ⟨-, ⟨y, w0, hrec, rfl⟩, hcase⟩ := act_sc hact
  have hval := hI.link q y w0 hrec hsc
  have hl := hI.loc q
  unfold writeRel
  rcases hcase with ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ |
    ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ <;>
    simp only [recorded, hpc, Option.some.injEq, Prod.mk.injEq] at hrec <;>
    obtain ⟨rfl, rfl⟩ := hrec <;> simp only [LocInv, hpc] at hl
  · exact Or.inl ⟨hval.trans hl, rfl⟩
  · exact Or.inr (Or.inl ⟨hval.trans hl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by rw [hval]; exact hl.1, by rw [hval]; exact hl.2, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hval]; exact hl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hval.trans hl.1, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hval.trans hl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hval.trans hl, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hval.trans hl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hval.trans hl, rfl⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, rfl⟩))))))
    have := hI.own q (by simp [hpc, PC.isVal]); rw [hval] at this ⊢; exact this

/-- The effect of an internal step on the memory: one cell `x` changes, either keeping its
value and gaining a link, or by a successful `SC` (a `writeRel` overwrite). -/
lemma tau_mem {C C' : Cfg K m P} (hI : Inv h N ts C) {q : P}
    (hs : (impl h).step C (.tau q) = some C') :
    ∃ x, (∀ y, y ≠ x → C'.mem y = C.mem y) ∧
      ((C'.val x = C.val x ∧ ∀ r, r ∈ C.lks x → r ∈ C'.lks x) ∨
       (q ∈ C.lks x ∧ C'.lks x = [] ∧ writeRel (C.loc q).op.key (C.val x) (C'.val x))) := by
  obtain ⟨-, -, x, o, k, hact, hmem, -⟩ := Impl.step_tau hs
  refine ⟨x, fun y hy => by rw [hmem, update_of_ne hy], ?_⟩
  have hv : C'.val x = ((Mem K m P x).δ (C.mem x) o).1.1 := by
    simp only [Cfg.val, hmem, update_self]
  have hl : C'.lks x = ((Mem K m P x).δ (C.mem x) o).1.2 := by
    simp only [Cfg.lks, hmem, update_self]
  rw [hv, hl]
  dsimp only [Mem]
  rcases o with q' | ⟨q', w⟩ | q'
  · left
    simp only [llscObj.δ_ll]
    refine ⟨rfl, fun r hr => ?_⟩
    split_ifs
    · exact hr
    · exact List.mem_cons_of_mem _ hr
  · have hq := (act_sc (h := h) hact).1; subst hq
    simp only [llscObj.δ_sc]
    split_ifs with hsc
    · right; exact ⟨hsc, rfl, writeRel_of_sc hI hact hsc⟩
    · left; exact ⟨rfl, fun _ hr => hr⟩
  · left; exact ⟨rfl, fun _ hr => hr⟩

lemma writeRel_ne {k : K} {u w : Cell K} (hw : writeRel k u w) : u ≠ w := by
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, -, rfl⟩ | ⟨h1 | h1, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1 | h1 | h1 | h1, rfl⟩ <;> simp_all
  rintro rfl; simp at h1

/-- A step overwrites an available cell with a (tentative) key. -/
def Reclaim (D D' : Cfg K m P) : Prop :=
  ∃ x w, (D.val x = .empty ∨ D.val x = .tomb) ∧ D'.val x = .key w .tent

/-- The situation of Proposition 2 while no available cell has been reclaimed: no copy of `v`,
the available cell `c` is still available, and the `insert(v)` of `p` has not passed `c`. -/
structure P2 (h : K → Fin m) (p : P) (v : K) (c : Fin m) (C : Cfg K m P) : Prop where
  nov : ∀ x t, C.val x ≠ .key v t
  free : C.val c = .empty ∨ C.val c = .tomb
  pend : C.pend p = some (.insert v)
  op : (C.loc p).op = .insert v
  pc : (C.loc p).pc = .fsLL ∨ (C.loc p).pc = .bsLL ∨ (C.loc p).pc = .iLL ∨ (C.loc p).pc = .iSC
  jc : ((C.loc p).pc = .iLL ∨ (C.loc p).pc = .iSC) → dist h v (C.loc p).j ≤ dist h v c
  lk : (C.loc p).pc = .iSC → (C.loc p).j = c → p ∈ C.lks c

lemma fsBody_ins {l : Loc K m} {v : K} (hop : l.op = .insert v) (hk : l.val.key? ≠ some v) :
    ((fsBody h l).pc = .fsLL ∨ (fsBody h l).pc = .bsLL) ∧ (fsBody h l).op = l.op := by
  have e1 : ∀ l' : Loc K m, l'.op = .insert v →
      (fsEnd h l').pc = .bsLL ∧ (fsEnd h l').op = l'.op := by
    intro l' hop'; unfold fsEnd fsReturn; split_ifs <;> simp [hop']
  have hk' : ¬ l.val.key? = some l.op.key := by rw [hop, DOp.key_insert]; exact hk
  unfold fsBody
  rw [if_neg hk']
  split_ifs <;> first
    | exact ⟨Or.inr (e1 _ (by exact hop)).1, (e1 _ (by exact hop)).2⟩
    | exact ⟨Or.inl rfl, rfl⟩
    | (unfold fsNext; split_ifs <;> first
        | exact ⟨Or.inr (e1 _ (by exact hop)).1, (e1 _ (by exact hop)).2⟩
        | exact ⟨Or.inl rfl, rfl⟩)

lemma bsBody_ins {l : Loc K m} {v : K} (hop : l.op = .insert v) (hk : l.val.key? ≠ some v) :
    ((bsBody h l).pc = .bsLL ∨ ((bsBody h l).pc = .iLL ∧ (bsBody h l).j = h v)) ∧
      (bsBody h l).op = l.op := by
  have hk' : ¬ l.val.key? = some l.op.key := by rw [hop, DOp.key_insert]; exact hk
  unfold bsBody
  rw [if_neg hk']
  · unfold bsCheck; split_ifs
    · simp [bsReturn, hop]
    · exact ⟨Or.inl rfl, rfl⟩

lemma p2_step {C C' : Cfg K m P} (hI : Inv h N ts C) {p : P} {v : K} {c : Fin m}
    (hP : P2 h p v c C) {ℓ : Label P (dict K)} (hs : (impl h).step C ℓ = some C')
    (hno : ¬ Reclaim C C') : P2 h p v c C' := by
  have hpne : C.pend p ≠ none := by rw [hP.pend]; simp
  -- `p`'s next action is an access
  have hacc : ∀ r l, (impl h).act p (C.loc p) ≠ .ret r l := by
    intro r l h1
    simp only [impl] at h1
    rcases hP.pc with h2 | h2 | h2 | h2 <;> simp [act, h2] at h1
  cases ℓ with
  | inv q o =>
    have hqp : q ≠ p := by rintro rfl; exact hpne (Impl.step_inv hs).1
    obtain ⟨h1, h2⟩ := Impl.step_other hs (q := p) (show q ≠ p from hqp)
    have hmem := (Impl.step_inv hs).2.2.2.2
    exact ⟨fun x t => by simpa [Cfg.val, hmem] using hP.nov x t,
      by simpa [Cfg.val, hmem] using hP.free, by rw [h2]; exact hP.pend, by rw [h1]; exact hP.op,
      by rw [h1]; exact hP.pc, by rw [h1]; exact hP.jc,
      by rw [h1]; simpa [Cfg.lks, hmem] using hP.lk⟩
  | ret q r =>
    have hqp : q ≠ p := by
      rintro rfl
      obtain ⟨-, -, -, l, hact, -⟩ := Impl.step_ret hs
      exact hacc _ _ hact
    obtain ⟨h1, h2⟩ := Impl.step_other hs (q := p) (show q ≠ p from hqp)
    have hmem := (Impl.step_ret hs).2.2.1
    exact ⟨fun x t => by simpa [Cfg.val, hmem] using hP.nov x t,
      by simpa [Cfg.val, hmem] using hP.free, by rw [h2]; exact hP.pend, by rw [h1]; exact hP.op,
      by rw [h1]; exact hP.pc, by rw [h1]; exact hP.jc,
      by rw [h1]; simpa [Cfg.lks, hmem] using hP.lk⟩
  | tau q =>
    obtain ⟨x, hoth, hx⟩ := tau_mem hI hs
    have hval : ∀ y, C'.val y = C.val y ∨ (y = x ∧ q ∈ C.lks x ∧ C'.lks x = [] ∧
        writeRel (C.loc q).op.key (C.val x) (C'.val x)) := by
      intro y; by_cases hy : y = x
      · subst hy; rcases hx with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
        · exact Or.inl h1
        · exact Or.inr ⟨rfl, h1, h2, h3⟩
      · left; simp only [Cfg.val, hoth y hy]
    -- no write creates a copy of `v` or overwrites the available cell `c`
    have hnov : ∀ y t, C'.val y ≠ .key v t := by
      intro y t hy
      rcases hval y with h1 | ⟨rfl, -, -, hw⟩
      · exact hP.nov y t (h1 ▸ hy)
      · rw [hy] at hw
        rcases hw with ⟨h2, h3⟩ | ⟨-, h3⟩ | ⟨-, -, h3⟩ | ⟨h2, h3⟩ | ⟨-, h3⟩ | ⟨h2, h3⟩ |
          ⟨h2, h3⟩ | ⟨-, h3⟩ <;> simp only [Cell.key.injEq, reduceCtorEq] at h3
        · obtain ⟨rfl, -⟩ := h3; exact hP.nov _ _ h2
        · exact hno ⟨y, (C.loc q).op.key, h2, by rw [hy, h3.1, h3.2]⟩
        · obtain ⟨rfl, -⟩ := h3; exact hP.nov _ _ h2
        · obtain ⟨rfl, -⟩ := h3; exact hP.nov _ _ h2
    have hcx : ∀ y, (C.val y = .empty ∨ C.val y = .tomb) → C'.val y = C.val y := by
      intro y hy
      rcases hval y with h1 | ⟨rfl, -, -, hw⟩
      · exact h1
      · exfalso
        rcases hw with ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -, -⟩ | ⟨h2, h3⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ |
          ⟨h2, -⟩ | ⟨h2 | h2 | h2 | h2, -⟩
        all_goals first
          | exact hno ⟨y, (C.loc q).op.key, hy, h3⟩
          | (rcases hy with h4 | h4 <;> rw [h4] at h2 <;> simp at h2)
    have hlc : p ∈ C.lks c → p ∈ C'.lks c := by
      intro h1
      by_cases hcx' : c = x
      · subst hcx'
        rcases hx with ⟨-, h2⟩ | ⟨-, -, hw⟩
        · exact h2 p h1
        · exact absurd (hcx c hP.free) (writeRel_ne hw).symm
      · simpa [Cfg.lks, hoth c hcx'] using h1
    have hfree : C'.val c = .empty ∨ C'.val c = .tomb := by rw [hcx c hP.free]; exact hP.free
    by_cases hqp : q = p
    · subst hqp
      have hpend' : C'.pend = C.pend := (Impl.step_tau hs).2.1
      have hpend : C'.pend q = some (.insert v) := by rw [hpend']; exact hP.pend
      set l := C.loc q with hl
      -- the next cell of the free-cell search
      have hnext : ∀ l' : Loc K m, l'.op = .insert v → l'.j = l.j → l'.j ≠ c →
          dist h v l'.j ≤ dist h v c → C'.loc q = iNext h l' → P2 h q v c C' := by
        intro l' hop hj hjc hd hloc
        have hlt : dist h v l'.j < dist h v c :=
          lt_of_le_of_ne hd (fun e => hjc (dist_inj h v e))
        rcases iNext_cases (h := h) l' with ⟨h1, he⟩ | ⟨h1, he⟩
        · rw [hop, DOp.key_insert] at h1
          have := dist_of_succ_eq h v _ h1
          have := dist_lt h v c
          omega
        · rw [hop, DOp.key_insert] at h1
          rw [he] at hloc
          refine ⟨hnov, hfree, hpend, by rw [hloc]; exact hop, by rw [hloc]; simp, ?_, ?_⟩
          · intro _; rw [hloc]; simp only; rw [dist_succ h v _ h1]; omega
          · intro h2; rw [hloc] at h2; cases h2
      rcases hP.pc with hpc | hpc | hpc | hpc
      · have hact : act h q l = .access l.i (.ll q) (fun r => fsBody h { l with val := r.1 }) := by
          simp only [act, hpc, l]
        obtain ⟨-, hC⟩ := step_tau_access hs hact
        have hloc : C'.loc q = fsBody h { l with val := C.val l.i } := by rw [hC]; simp [Cfg.val]
        obtain ⟨h1, h2⟩ := fsBody_ins (h := h) (l := { l with val := C.val l.i }) hP.op
          (by intro e; rcases hk : C.val l.i with _ | _ | _ | _ | ⟨w, t⟩ <;> rw [hk] at e <;>
                simp [Cell.key?] at e; subst e; exact hP.nov _ _ hk)
        refine ⟨hnov, hfree, hpend, by rw [hloc, h2]; exact hP.op, ?_, ?_, ?_⟩
        · rw [hloc]; rcases h1 with h1 | h1 <;> simp [h1]
        · rw [hloc]; rcases h1 with h1 | h1 <;> simp [h1]
        · rw [hloc]; rcases h1 with h1 | h1 <;> simp [h1]
      · have hact : act h q l = .access l.i (.ll q) (fun r => bsBody h { l with val := r.1 }) := by
          simp only [act, hpc, l]
        obtain ⟨-, hC⟩ := step_tau_access hs hact
        have hloc : C'.loc q = bsBody h { l with val := C.val l.i } := by rw [hC]; simp [Cfg.val]
        obtain ⟨h1, h2⟩ := bsBody_ins (h := h) (l := { l with val := C.val l.i }) hP.op
          (by intro e; rcases hk : C.val l.i with _ | _ | _ | _ | ⟨w, t⟩ <;> rw [hk] at e <;>
                simp [Cell.key?] at e; subst e; exact hP.nov _ _ hk)
        refine ⟨hnov, hfree, hpend, by rw [hloc, h2]; exact hP.op, ?_, ?_, ?_⟩
        · rw [hloc]; rcases h1 with h1 | ⟨h1, -⟩ <;> simp [h1]
        · rw [hloc]; rcases h1 with h1 | ⟨h1, h3⟩
          · simp [h1]
          · intro _; rw [h3, dist_self]; exact Nat.zero_le _
        · rw [hloc]; rcases h1 with h1 | ⟨h1, -⟩ <;> simp [h1]
      · have hact : act h q l = .access l.j (.ll q) (fun r => iBody h { l with val := r.1 }) := by
          simp only [act, hpc, l]
        obtain ⟨-, hC⟩ := step_tau_access hs hact
        have hloc : C'.loc q = iBody h { l with val := C.val l.j } := by rw [hC]; simp [Cfg.val]
        have hjd := hP.jc (Or.inl hpc)
        rcases iBody_cases (h := h) { l with val := C.val l.j } with ⟨h1, he⟩ | ⟨h1, he⟩ <;>
          rw [he] at hloc
        · refine ⟨hnov, hfree, hpend, by rw [hloc]; exact hP.op, by rw [hloc]; simp,
            fun _ => by rw [hloc]; exact hjd, fun _ h3 => ?_⟩
          rw [hloc] at h3; simp only at h3; subst h3
          rw [hC]; simp [Cfg.lks, mem_addLink_self]
        · refine hnext { l with val := C.val l.j } hP.op rfl ?_ hjd hloc
          intro e; apply h1; simp only; rw [e]; exact hP.free
      · have hl0 : l.val = .empty ∨ l.val = .tomb := by
          have := hI.loc q; simp only [LocInv, hpc] at this; exact this
        have hact : act h q l = .access l.j (.sc q (.key l.op.key .tent))
            (fun r => if r.2 then ds48 h l else iNext h l) := by
          simp only [act, hpc, l]
        obtain ⟨-, hC⟩ := step_tau_access hs hact
        have hjd := hP.jc (Or.inr hpc)
        by_cases hsc : q ∈ C.lks l.j
        · exfalso; apply hno
          refine ⟨l.j, l.op.key, ?_, ?_⟩
          · rw [hI.link q l.j l.val (by simp [recorded, hpc, l]) hsc]; exact hl0
          · rw [hC]; simp only [Cfg.lks] at hsc; simp [Cfg.val, hsc]
        · have hloc : C'.loc q = iNext h l := by
            rw [hC]; simp only [Cfg.lks] at hsc; simp [hsc]
          refine hnext l hP.op rfl ?_ hjd hloc
          intro e; exact hsc (e ▸ hP.lk hpc e)
    · obtain ⟨h1, h2⟩ := Impl.step_other hs (q := p) (show q ≠ p from hqp)
      exact ⟨hnov, hfree, by rw [h2]; exact hP.pend, by rw [h1]; exact hP.op,
        by rw [h1]; exact hP.pc, by rw [h1]; exact hP.jc,
        fun h3 h4 => hlc (hP.lk (by rwa [h1] at h3) (by rwa [h1] at h4))⟩

/-- **Proposition 2** of the paper: if `insert(v)` is invoked (by `p`, after the execution `α`)
in a configuration in which some cell `c` is `EMPTY` or `TOMBSTONE` and no cell contains the key
`v`, then before the operation returns, some step overwrites an available cell (`EMPTY` or
`TOMBSTONE`) with a key (`Reclaim`). In particular, an `insert` running solo in such a
configuration does not abort. -/
theorem prop2 {α : List (Label P (dict K))} {C₀ : Cfg K m P} (hα : (impl h).run α = some C₀)
    {p : P} {v : K} {c : Fin m}
    (hc : C₀.val c = .empty ∨ C₀.val c = .tomb) (hnov : ∀ x t, C₀.val x ≠ .key v t)
    {γ : List (Label P (dict K))} {C₁ : Cfg K m P}
    (hγ : (impl h).runFrom C₀ (.inv p (.insert v) :: γ) = some C₁) {r : (dict K).Resp}
    (hr : .ret p r ∈ γ) :
    ∃ β ℓ δ D D', γ = β ++ ℓ :: δ ∧ (impl h).runFrom C₀ (.inv p (.insert v) :: β) = some D ∧
      (impl h).step D ℓ = some D' ∧ Reclaim D D' := by
  by_contra hcon
  push Not at hcon
  -- the configuration after the invocation
  simp only [Impl.runFrom_cons] at hγ
  cases hi : (impl h).step C₀ (.inv p (.insert v)) with
  | none => simp [hi] at hγ
  | some Ci =>
  rw [hi, Option.bind_some] at hγ
  obtain ⟨-, -, hpend, hloc, hmem⟩ := Impl.step_inv hi
  have hP0 : P2 h p v c Ci := by
    have hl : Ci.loc p = start h (.insert v) := by rw [hloc, update_self]; rfl
    refine ⟨fun x t => by simpa [Cfg.val, hmem] using hnov x t, by simpa [Cfg.val, hmem] using hc,
      by rw [hpend, update_self], by rw [hl]; rfl, by rw [hl]; simp [start], ?_, ?_⟩ <;>
      rw [hl] <;> simp [start]
  have hrun0 : (impl h).run (α ++ [.inv p (.insert v)]) = some Ci := by
    rw [(impl h).run_append_of_eq hα, Impl.runFrom_singleton]; exact hi
  -- the invariant along the prefixes of `γ`
  have key : ∀ n ≤ γ.length, ∃ D, (impl h).runFrom Ci (γ.take n) = some D ∧ P2 h p v c D := by
    intro n hn
    induction n with
    | zero => exact ⟨Ci, rfl, hP0⟩
    | succ n ih =>
      obtain ⟨D, hD, hPD⟩ := ih (by omega)
      have hlt : n < γ.length := by omega
      have htake : γ.take (n + 1) = γ.take n ++ [γ[n]] := List.take_succ_eq_append_getElem hlt
      have hsplit : γ = γ.take n ++ γ[n] :: γ.drop (n + 1) := by
        have := List.take_append_drop n γ; rw [List.drop_eq_getElem_cons hlt] at this
        exact this.symm
      have hrest := hγ
      rw [hsplit, Impl.runFrom_append, hD, Option.bind_some, Impl.runFrom_cons] at hrest
      cases hs : (impl h).step D γ[n] with
      | none => simp [hs] at hrest
      | some D' =>
        refine ⟨D', by rw [htake, Impl.runFrom_append, hD, Option.bind_some,
          Impl.runFrom_singleton, hs], ?_⟩
        have hrunD : (impl h).run (α ++ [.inv p (.insert v)] ++ γ.take n) = some D := by
          rw [(impl h).run_append_of_eq hrun0]; exact hD
        obtain ⟨ts, hI⟩ := inv_of_run hrunD
        refine p2_step hI hPD hs ?_
        exact hcon (γ.take n) γ[n] (γ.drop (n + 1)) D D' hsplit
          (by rw [Impl.runFrom_cons, hi, Option.bind_some]; exact hD) hs
  -- the response of `p` is impossible
  obtain ⟨n, hn, hγn⟩ := List.getElem_of_mem hr
  obtain ⟨D, hD, hPD⟩ := key n (by omega)
  have hsplit : γ = γ.take n ++ γ[n] :: γ.drop (n + 1) := by
    have := List.take_append_drop n γ; rw [List.drop_eq_getElem_cons hn] at this
    exact this.symm
  have hrest := hγ
  rw [hsplit, Impl.runFrom_append, hD, Option.bind_some, Impl.runFrom_cons, hγn] at hrest
  cases hs : (impl h).step D (.ret p r) with
  | none => simp [hs] at hrest
  | some D' =>
    obtain ⟨-, -, -, l, hact, -⟩ := Impl.step_ret hs
    simp only [impl] at hact
    rcases hPD.pc with h1 | h1 | h1 | h1 <;> simp [act, h1] at hact

end Podc.LockFreeLinearProbing
