import Papers.PODC2024.HistoryIndependent.ClassC
import Cslib.Computability.Distributed.SharedMemory.Indist
import Mathlib

/-!
# Perfect history independence: Proposition 6 and Proposition 14

Proposition 6 and Proposition 14 of Attiya, Bender, Farach-Colton, Oshman, Schiller,
*History-Independent Concurrent Objects*, PODC 2024.
-/

namespace Cslib.SharedMemory

open List Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

/-- **Proposition 6.** In an obstruction-free perfect HI implementation (with linearization
function `h`), if `q₁` is reachable by a sequence of operations `os` of a process `p`, and `q₂`
is reached from `q₁` by one more operation `o` of `p`, then the canonical memory representations
of `q₁` and `q₂` (the memory of any execution whose linearization ends in `q₁`, resp. `q₂`)
differ in at most one base object. -/
theorem prop6 {I : Impl A B P L} (hof : I.ObstructionFree)
    {h : List (Label P A) → List (OpId P × A.Op)} (hHI : I.HIwrtWith h (fun _ _ => True))
    (p : P) (os : List A.Op) (hos : ∀ o ∈ os, I.allowed p o) (o : A.Op) (ho : I.allowed p o)
    {α₁ α₂ : List (Label P A)} {C₁ C₂ : Config A B P L}
    (h₁ : I.run α₁ = some C₁) (h₂ : I.run α₂ = some C₂)
    (hq₁ : linState (h α₁) = A.runOps A.init os)
    (hq₂ : linState (h α₂) = (A.δ (A.runOps A.init os) o).1) :
    MemDist1 C₁.mem C₂.mem := by
  obtain ⟨hlin, hhi⟩ := hHI
  obtain ⟨C₀, h0run, h0q, h0lin, -, h0ops, h0resps, h0other, -⟩ :=
    I.soloOps_init_spec hof hlin p os hos
  set β₀ := I.soloOps p I.initCfg os with hβ₀
  have hm1 : C₁.mem = C₀.mem := hhi _ _ _ _ h₁ h0run trivial trivial (hq₁.trans h0lin.symm)
  obtain ⟨C', h'run, h'c, h'procs, h'ops, h'resps⟩ := I.soloOp_spec hof p o ho h0run (h0q p)
  set S := I.soloOp p o C₀ with hS
  have hβrun : I.run (β₀ ++ S) = some C' := by rw [Impl.run_append_of_eq I h0run, h'run]
  have hβlin : linState (h (β₀ ++ S)) = (A.δ (A.runOps A.init os) o).1 := by
    rw [(hlin _ ⟨_, hβrun⟩).linState_of_changer (Valid.wellFormed I ⟨_, hβrun⟩) p]
    · rw [opsOf_append, h'ops, h0ops, ObjSpec.runOps_append]; rfl
    · intro q hq o' ho'
      rw [opsOf_append, h0other q hq, opsOf_eq_nil_of_proc_ne
        (fun ℓ hℓ => by rw [h'procs ℓ hℓ]; exact Ne.symm hq)] at ho'
      simp at ho'
    · rw [opsOf_append, respsOf_append, length_append, length_append, h'ops, h'resps, h0ops,
        h0resps]; rfl
  have hm2 : C₂.mem = C'.mem := hhi _ _ _ _ h₂ hβrun trivial trivial (hq₂.trans hβlin.symm)
  rw [hm1, hm2]
  apply I.memDist1_of_run h'run rfl
  intro γ₁ γ₂ E hSγ hE
  have hrunE : I.run (β₀ ++ γ₁) = some E := by rw [Impl.run_append_of_eq I h0run, hE]
  have hL := hlin _ ⟨E, hrunE⟩
  have hγp : ∀ ℓ ∈ γ₁, ℓ.proc = p := fun ℓ hℓ => h'procs ℓ (hSγ ▸ mem_append_left _ hℓ)
  have hother : ∀ q, q ≠ p → opsOf (β₀ ++ γ₁) q = [] := by
    intro q hq
    rw [opsOf_append, h0other q hq,
      opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hγp ℓ hℓ]; exact Ne.symm hq)]; rfl
  obtain ⟨m, hm₁, hm₂, hm₃⟩ := hL.linState_eq (Valid.wellFormed I ⟨E, hrunE⟩) p
    (fun y hy hyc => by
      have := hL.op_mem hy; rw [hother _ hyc] at this; simp at this)
  have hpre : opsOf γ₁ p <+: [o] := by
    rw [← h'ops, hSγ, opsOf_append]; exact prefix_append _ _
  rw [opsOf_append, h0ops] at hm₂ hm₃
  rw [respsOf_append, length_append, h0resps] at hm₁
  rcases hγo : opsOf γ₁ p with _ | ⟨x, rest⟩
  · rw [hγo] at hm₂ hm₃
    simp only [append_nil] at hm₂ hm₃
    left
    apply hhi _ _ _ _ hrunE h0run trivial trivial
    rw [hm₃, take_of_length_le (by omega), h0lin]
  · rw [hγo] at hpre hm₂ hm₃
    obtain ⟨rfl, hrest⟩ := cons_prefix_cons.1 hpre
    have : rest = [] := prefix_nil.1 hrest
    subst this
    simp only [length_append, length_singleton] at hm₂
    rcases (show m = os.length ∨ m = os.length + 1 by omega) with rfl | rfl
    · left
      apply hhi _ _ _ _ hrunE h0run trivial trivial
      rw [hm₃, take_left, h0lin]
    · right
      apply hhi _ _ _ _ hrunE hβrun trivial trivial
      rw [hm₃, hβlin, take_of_length_le (by simp), ObjSpec.runOps_append]; rfl

omit [DecidableEq P] [DecidableEq ι] in
/-- If `t ≥ 2` pairwise distinct memory representations are pairwise at distance `≤ 1`, they all
differ in one and the same base object, which therefore takes `t` distinct values. -/
lemma exists_injective_coord {t : ℕ} (ht : 2 ≤ t) (M : Fin t → (i : ι) → (B i).State)
    (hinj : Function.Injective M) (hd : ∀ a b, MemDist1 (M a) (M b)) :
    ∃ ℓ, Function.Injective (fun a => M a ℓ) := by
  have h01 : M ⟨0, by omega⟩ ≠ M ⟨1, by omega⟩ :=
    fun h => by have := hinj h; simp [Fin.ext_iff] at this
  obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.1 h01
  refine ⟨ℓ, fun a b hab => ?_⟩
  by_contra hne
  obtain ⟨ℓ', hℓ'⟩ := Function.ne_iff.1 (fun h => hne (hinj h))
  simp only at hab
  have hℓℓ' : ℓ' ≠ ℓ := by rintro rfl; exact hℓ' hab
  -- one of `M 0`, `M 1` differs from `M a` (and `M b`) at `ℓ`
  obtain ⟨c, hc⟩ : ∃ c, M c ℓ ≠ M a ℓ := by
    by_cases h0 : M ⟨0, by omega⟩ ℓ = M a ℓ
    · exact ⟨⟨1, by omega⟩, fun h1 => hℓ (h0.trans h1.symm)⟩
    · exact ⟨_, h0⟩
  have e1 : M c ℓ' = M a ℓ' := by
    by_contra h1; exact hℓℓ' (hd c a ℓ' ℓ h1 hc)
  have e2 : M c ℓ' = M b ℓ' := by
    by_contra h1; exact hℓℓ' (hd c b ℓ' ℓ h1 (hab ▸ hc))
  exact hℓ' (e1.symm.trans e2)

/-- **Proposition 14.** There is no obstruction-free perfect HI implementation of an object in
`C_t`, `t ≥ 2` (the paper states `t ≥ 3`; `t = 2` is trivial), from base objects with fewer
than `t` states — in any system with two processes `p ≠ p'` where `p` may invoke the `ochange`
operations and `p'` may invoke `oread`. (With a single process the statement is false: the
process can keep the state locally.) -/
theorem prop14 {t : ℕ} (ht : 2 ≤ t) (K : ClassC A t) (I : Impl A B P L) (p p' : P)
    (hpp : p ≠ p') (hp : ∀ q q', I.allowed p (K.ochange q q')) (hp' : I.allowed p' K.oread)
    (hB : ∀ j, Finite (B j).State ∧ Nat.card (B j).State < t) :
    ¬ (I.ObstructionFree ∧ I.PerfectHI) := by
  classical
  rintro ⟨hof, h, hlin, hhi⟩
  have hHI : I.HIwrtWith h (fun _ _ => True) := ⟨hlin, hhi⟩
  let D := K.avoidData
  have hstart : ∀ a, ∀ o ∈ D.start a, I.allowed p o := by
    intro a o ho
    simp only [D, ClassC.avoidData] at ho; split_ifs at ho
    · simp at ho
    · simp at ho; subst ho; exact hp _ _
  choose C hC using fun a => I.soloOps_init_spec hof hlin p (D.start a) (hstart a)
  let M : Fin t → (i : ι) → (B i).State := fun a => (C a).mem
  -- pairwise distance ≤ 1 (Proposition 6)
  have hd : ∀ a b, MemDist1 (M a) (M b) := by
    intro a b
    by_cases hab : a = b
    · subst hab; exact memDist1_refl _
    · have hrep : K.rep a ≠ K.rep b := fun h' => hab (by rw [← K.cls_rep a, h', K.cls_rep])
      apply prop6 hof hHI p (D.start a) (hstart a) (K.ochange (K.rep a) (K.rep b)) (hp _ _)
        (hC a).1 (hC b).1 (hC a).2.2.1
      rw [(hC b).2.2.1, D.start_end, D.start_end]
      exact (K.ochange_spec _ _ hrep).symm
  -- pairwise distinct (a solo `oread` by `p'` tells the states apart)
  have hinj : Function.Injective M := by
    intro a b hab
    by_contra hne
    have hresp : ∀ c : Fin t, ∃ x, respsOf (I.soloOp p' K.oread (C c)) p' = [x] ∧
        x = (A.δ (K.rep c) K.oread).2 := by
      intro c
      obtain ⟨hrun, hq, hlinc, hloc, hops, hresps, hother, hother'⟩ := hC c
      obtain ⟨C', h'run, -, h'procs, h'ops, h'resps⟩ :=
        I.soloOp_spec hof p' K.oread hp' hrun (hq p')
      obtain ⟨x, hx⟩ : ∃ x, respsOf (I.soloOp p' K.oread (C c)) p' = [x] :=
        length_eq_one_iff.1 h'resps
      refine ⟨x, hx, ?_⟩
      set S := I.soloOp p' K.oread (C c)
      set α := I.soloOps p I.initCfg (D.start c)
      have hrun' : I.run (α ++ S) = some C' := by rw [Impl.run_append_of_eq I hrun, h'run]
      have hL := hlin _ ⟨_, hrun'⟩
      have hSp : opsOf S p = [] := opsOf_eq_nil_of_proc_ne
        (fun ℓ hℓ => by rw [h'procs ℓ hℓ]; exact hpp.symm)
      have hro : ∀ y ∈ h (α ++ S), y.1.1 ≠ p → A.ReadOnly y.2 := by
        intro y hy hyp
        have hm := hL.op_mem hy
        rw [opsOf_append, hother _ hyp, nil_append] at hm
        by_cases hyp' : y.1.1 = p'
        · rw [hyp', h'ops] at hm; simp at hm; rw [hm]; exact K.oread_ro
        · rw [opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [h'procs ℓ hℓ]; exact Ne.symm hyp')]
            at hm
          simp at hm
      have hrespx : respOf (α ++ S) (p', 0) = some x := by
        simp [respOf, hother' p' hpp.symm, hx]
      obtain ⟨j, hj1, hj2, o, ho, hxo⟩ := hL.resp_eq (Valid.wellFormed I ⟨_, hrun'⟩) p hro
        hrespx (D.start c).length (fun j hj => ⟨α, S, rfl, by
          simp only [Completed]; rw [hresps]; exact hj, by
          simp [Invoked, hother p' hpp.symm]⟩)
      rw [opsOf_append, hops, hSp, append_nil] at hj2 hxo
      have hoe : o = K.oread := by
        simp [opOf, hother p' hpp.symm, h'ops] at ho; exact ho.symm
      rw [hxo, hoe, take_of_length_le hj1, D.start_end]; rfl
    obtain ⟨xa, hxa, hxa'⟩ := hresp a
    obtain ⟨xb, hxb, hxb'⟩ := hresp b
    have hag : Agree p' (C a) (C b) :=
      ⟨hab, by rw [(hC a).2.2.2.1 p' hpp.symm, (hC b).2.2.2.1 p' hpp.symm],
        by rw [(hC a).2.1 p', (hC b).2.1 p']⟩
    rw [I.soloOp_eq_of_agree hag, hxb] at hxa
    simp only [cons.injEq, and_true] at hxa
    subst hxa
    apply K.oread_sep (K.rep a) (K.rep b) (by rw [K.cls_rep, K.cls_rep]; exact hne)
    rw [← hxa', ← hxb']
  obtain ⟨ℓ, hℓ⟩ := exists_injective_coord ht M hinj hd
  have := (hB ℓ).1
  have h1 := Nat.card_le_card_of_injective _ hℓ
  have h2 := (hB ℓ).2
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  omega

end Cslib.SharedMemory
