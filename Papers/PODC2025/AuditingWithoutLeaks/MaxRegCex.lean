import Papers.PODC2025.AuditingWithoutLeaks.MaxRegInv

/-!
# Lemma 38 (uncompromised writeMax) of Algorithm 2 is false

Lemma 38 of the paper claims: for every finite execution `α`, every value `w` and every reader
`p_j`, either `p_j` has a `w`-effective read in `α`, or there is an execution `α' ∼_{p_j} α` in
which no `writeMax` has input `w`.

Counterexample (one reader `p_0`, two writers `A = wr 0`, `B = wr 1`, no auditors, initial pair
`v₀ = (0, 0)`): `A` runs `writeMax(0)` solo with nonce `N_A`, then `B` runs `writeMax(1)` solo
with nonce `N_B`, then `p_0` runs one read, which fetches `R = (2, (1, N_B), _)` and returns `1`.
Hence `p_0` has no `0`-effective read. But in every execution indistinguishable to `p_0`, its
fetch&xor returns the same triple, so `R.seq = 2` and `R.val = (1, N_B)` at that point; since the
pairs successively stored in `R` strictly increase with `R.seq` (`MaxRegInv.lean`), the pair with
sequence number `1` lies strictly between `(0, 0)` and `(1, N_B)`.

* With `N_A = 1`, `N_B = 0` (`θ₁`): that pair is `(0, N)`, `N ≥ 1`, so a `writeMax(0)` was invoked
  (`lemma38_false`, over all coins).
* With `N_A = 2`, `N_B = 1` (`θ₂`) and *fresh* nonces (pairwise distinct and different from
  `N₀ = 0`): that pair is `(0, N)` with `N ≥ 1` (the only other candidate, `(1, 0)`, would reuse
  the nonce `N₀`), so again a `writeMax(0)` was invoked (`lemma38_false_fresh`).

The paper's proof picks "the largest input `u` of a writeMax smaller than `w`", which does not
exist when `w` is the initial value `w₀` (and in general the gap between `(u, N)` and `(w, N')` in
`R`'s history can be empty for discrete nonces).
-/

namespace Podc.AuditingWithoutLeaks.MaxReg

open Cslib.SharedMemory

section Generic

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

-- CSLib candidate (View.lean)
/-- An observation of `p` along `α` is the observation of some label of `α`, taken in the
configuration reached by the preceding labels. -/
lemma mem_obsFrom (I : Impl A B P L) (p : P) {ob : ProcObs A B} :
    ∀ {C : Config A B P L} {α : List (Label P A)}, ob ∈ I.obsFrom p C α →
      ∃ α₁ ℓ α₂ D, α = α₁ ++ ℓ :: α₂ ∧ I.runFrom C α₁ = some D ∧ I.obsStep D p ℓ = some ob
  | _, [], h => by simp at h
  | C, ℓ :: α, h => by
    simp only [Impl.obsFrom, List.mem_append] at h
    rcases h with h | h
    · exact ⟨[], ℓ, α, C, rfl, rfl, by simpa using h⟩
    · cases hs : I.step C ℓ with
      | none => simp [hs] at h
      | some C' =>
        rw [hs] at h
        obtain ⟨α₁, ℓ', α₂, D, rfl, hD, hob⟩ := mem_obsFrom I p h
        exact ⟨ℓ :: α₁, ℓ', α₂, D, rfl, by simp [hs, hD], hob⟩

/-- The observation of the label `ℓ` after a prefix is an observation of the whole execution. -/
lemma mem_obsFrom_of_runFrom (I : Impl A B P L) (p : P) {C D : Config A B P L}
    {α₁ : List (Label P A)} (h : I.runFrom C α₁ = some D) {ℓ : Label P A} {ob : ProcObs A B}
    (hob : I.obsStep D p ℓ = some ob) (α₂ : List (Label P A)) :
    ob ∈ I.obsFrom p C (α₁ ++ ℓ :: α₂) := by
  rw [Impl.obsFrom_append_of_runFrom I p h]
  refine List.mem_append_right _ ?_
  simp [Impl.obsFrom, hob]

end Generic

section Model

variable {m : ℕ} {W Au : Type} [DecidableEq W] [DecidableEq Au]

/-- A primitive applied to `R` that returns a triple (read or fetch&xor) returns the current
contents of `R`. -/
lemma obs_R_eq {θ : Coins m W} {D : Cfg m W Au} {p : Proc m W Au} {ℓ : Lbl m W Au}
    {r : RVal m Pr} (h : (alg2 θ).obsStep D p ℓ = some (.tau MObj.R (Sum.inl r))) :
    r = rOf D := by
  cases ℓ with
  | inv q o => simp only [Impl.obsStep] at h; split_ifs at h; simp at h
  | ret q x => simp only [Impl.obsStep] at h; split_ifs at h; simp at h
  | tau q =>
    simp only [Impl.obsStep] at h
    split_ifs at h with hq
    split at h
    · rename_i i o k hact
      simp only [Option.some.injEq, ProcObs.tau.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have h := eq_of_heq h
      cases o with
      | read => simpa [rOf] using h.symm
      | fx j => simpa [rOf] using h.symm
      | cas old new => simp only at h; split_ifs at h
    · simp at h

/-- In a history whose `R.seq = 2`, the pair with sequence number `1` is good and lies strictly
between `v₀` and the current pair. -/
lemma Hist.two {G : Pr → Prop} {r : RVal m Pr} (h : Hist G r) (hs : r.seq = 2) :
    ∃ v, v₀ < v ∧ v < r.val ∧ G v := by
  obtain ⟨f, h0, h1, h2, h3⟩ := h
  refine ⟨f 1, ?_, ?_, h3 1 (by omega)⟩
  · rw [← h0]; exact h1 0 (by omega)
  · rw [← h2, hs]; exact h1 1 (by omega)

/-- If reader `j`'s view contains a fetch of the triple `r` with `r.seq = 2`, then some pair
strictly between `v₀` and `r.val` is good for the whole execution. -/
lemma good_of_fetch {θ : Coins m W} {α : List (Lbl m W Au)} (hα : (alg2 θ).Valid α)
    {p : Proc m W Au} {r : RVal m Pr} (hs : r.seq = 2)
    (hob : ProcObs.tau MObj.R (Sum.inl r) ∈ (alg2 θ).obsFrom p (alg2 θ).initCfg α) :
    ∃ v, v₀ < v ∧ v < r.val ∧ Good θ.nc α v := by
  obtain ⟨α₁, ℓ, α₂, D, rfl, hD, hobs⟩ := mem_obsFrom _ _ hob
  have hI : Inv θ.nc α₁ D := Inv.of_run hD
  obtain rfl := obs_R_eq hobs
  obtain ⟨v, h1, h2, h3⟩ := hI.hist.two hs
  exact ⟨v, h1, h2, h3.append _⟩

end Model

/-! ## The counterexample -/

/-- Processes of the counterexample: one reader, two writers, no auditors. -/
abbrev P := Proc 1 (Fin 2) Empty

/-- The family of all instances of Algorithm 2 with one reader and two writers. -/
abbrev I : Coins 1 (Fin 2) → Impl (amaxReg 1) (MBO 1) P (MLoc 1) := fun θ => alg2 θ

/-- Lemma 38 of the paper, for a family `I` of instances of Algorithm 2: for every finite
execution `(θ, α)`, every value `w` and every reader `p_j`, either some read operation of `p_j`
in `α` is `w`-effective, or some execution indistinguishable from `(θ, α)` to `p_j` invokes no
`writeMax(w)`. -/
def Lemma38 {m : ℕ} {W Au : Type} [DecidableEq W] [DecidableEq Au] {Θ : Type}
    (I : Θ → Impl (amaxReg m) (MBO m) (Proc m W Au) (MLoc m)) : Prop :=
  ∀ θ α, (I θ).Valid α → ∀ (w : ℕ) (j : Fin m),
    (∃ k, opOf α (Proc.rd j, k) = some (MOp.read j) ∧
      Impl.EffectiveFam I θ α (Proc.rd j, k) (MResp.val w)) ∨
    ∃ θ' α', (I θ').Valid α' ∧ Impl.IndistFam I (Proc.rd j) (θ, α) (θ', α') ∧
      ∀ p, MOp.writeMax w ∉ opsOf α' p

/-- A complete `writeMax(w)` of writer `x` run solo (7 primitive steps). -/
def wm (x : Fin 2) (w : ℕ) : List (Label P (amaxReg 1)) :=
  [.inv (.wr x) (.writeMax w)] ++ List.replicate 7 (.tau (.wr x)) ++ [.ret (.wr x) .ack]

/-- The reader's invocation and its first step (reading `SN`). -/
def rdPre : List (Label P (amaxReg 1)) := [.inv (.rd 0) (.read 0), .tau (.rd 0)]

/-- The reader's fetch&xor, `SN.compare&swap` and return of `1`. -/
def rdPost : List (Label P (amaxReg 1)) := [.tau (.rd 0), .ret (.rd 0) (.val 1)]

/-- The execution: `A` runs `writeMax(0)`, then `B` runs `writeMax(1)`, then `p_0` reads. -/
def αc : List (Label P (amaxReg 1)) := wm 0 0 ++ wm 1 1 ++ rdPre ++ .tau (.rd 0) :: rdPost

/-- Coins: trivial pads, nonce `1` for `A` and `0` for `B`. -/
def θ₁ : Coins 1 (Fin 2) := ⟨fun _ _ => false, fun x _ => if x = 0 then 1 else 0⟩

/-- Coins: trivial pads, nonces `2k + 2` for `A` and `2k + 1` for `B` (fresh). -/
def θ₂ : Coins 1 (Fin 2) := ⟨fun _ _ => false, fun x k => 2 * k + 2 - x.val⟩

lemma opsOf_αc_rd : opsOf αc (Proc.rd 0 : P) = [MOp.read 0] := by decide

lemma respOf_αc_rd : respOf αc ((Proc.rd 0 : P), 0) = some (MResp.val 1) := by decide

/-- No read of `p_0` in `αc` is `0`-effective (its only read returns `1`). -/
lemma not_effective (θ : Coins 1 (Fin 2)) (hv : (alg2 (Au := Empty) θ).Valid αc) (k : ℕ)
    (hk : opOf αc ((Proc.rd 0 : P), k) = some (MOp.read 0)) :
    ¬ Impl.EffectiveFam I θ αc (Proc.rd 0, k) (MResp.val 0) := by
  intro he
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · simp [opOf, opsOf_αc_rd] at hk
  subst hk0
  have := he θ αc hv (Impl.IndistFam.refl _ _ _) [] (by simpa using hv) (MResp.val 1)
    (by simpa using respOf_αc_rd)
  simp at this

/-- The run of `αc` up to the reader's fetch&xor. -/
lemma run_pre (θ : Coins 1 (Fin 2)) (h : ((alg2 (Au := Empty) θ).crun (wm 0 0 ++ wm 1 1 ++ rdPre)).map
      (fun D => (D.loc (.rd 0), (D.mem .R : RVal 1 Pr))) =
      some (.rFX none 2, ⟨2, toLex (1, θ.nc 1 0), θ.rnd 2⟩)) :
    ∃ D, (alg2 (Au := Empty) θ).runFrom (alg2 θ).initCfg (wm 0 0 ++ wm 1 1 ++ rdPre) = some D ∧
      (alg2 (Au := Empty) θ).obsStep D (.rd 0) (.tau (.rd 0)) =
        some (.tau MObj.R (Sum.inl ⟨2, toLex (1, θ.nc 1 0), θ.rnd 2⟩)) := by
  rw [← Impl.run_eq_crun (alg2 (Au := Empty) θ)] at h
  cases hD : (alg2 (Au := Empty) θ).run (wm 0 0 ++ wm 1 1 ++ rdPre) with
  | none => rw [hD] at h; simp at h
  | some D =>
    rw [hD] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hl, hR⟩ := h
    refine ⟨D, hD, ?_⟩
    simp [Impl.obsStep, hl, alg2, readerAct, hR]

/-- In `αc`, reader `p_0`'s fetch&xor returns `(2, (1, N_B), _)`. -/
lemma fetch_mem (θ : Coins 1 (Fin 2))
    (h : ((alg2 (Au := Empty) θ).crun (wm 0 0 ++ wm 1 1 ++ rdPre)).map
      (fun D => (D.loc (.rd 0), (D.mem .R : RVal 1 Pr))) =
      some (.rFX none 2, ⟨2, toLex (1, θ.nc 1 0), θ.rnd 2⟩)) :
    ProcObs.tau MObj.R (Sum.inl ⟨2, toLex (1, θ.nc 1 0), θ.rnd 2⟩) ∈
      (alg2 (Au := Empty) θ).obsFrom (.rd 0) (alg2 θ).initCfg αc := by
  obtain ⟨D, hD, hob⟩ := run_pre θ h
  exact mem_obsFrom_of_runFrom _ _ hD hob _

/-- Any execution indistinguishable from `(θ, αc)` to `p_0` contains a good pair strictly between
`v₀` and `(1, N_B)`. -/
lemma good_of_indist (θ θ' : Coins 1 (Fin 2))
    (h : ((alg2 (Au := Empty) θ).crun (wm 0 0 ++ wm 1 1 ++ rdPre)).map
      (fun D => (D.loc (.rd 0), (D.mem .R : RVal 1 Pr))) =
      some (.rFX none 2, ⟨2, toLex (1, θ.nc 1 0), θ.rnd 2⟩))
    {α' : List (Label P (amaxReg 1))} (hv : (alg2 θ').Valid α')
    (hind : Impl.IndistFam I (Proc.rd 0) (θ, αc) (θ', α')) :
    ∃ v, v₀ < v ∧ v < toLex (1, θ.nc 1 0) ∧ Good θ'.nc α' v := by
  have hobs := congrArg Prod.snd hind
  simp only [Impl.procView] at hobs
  exact good_of_fetch hv rfl (hobs ▸ fetch_mem θ h)

lemma run_pre_θ₁ : ((alg2 (Au := Empty) θ₁).crun (wm 0 0 ++ wm 1 1 ++ rdPre)).map
    (fun D => (D.loc (.rd 0), (D.mem .R : RVal 1 Pr))) =
    some (.rFX none 2, ⟨2, toLex (1, θ₁.nc 1 0), θ₁.rnd 2⟩) := by decide

lemma run_pre_θ₂ : ((alg2 (Au := Empty) θ₂).crun (wm 0 0 ++ wm 1 1 ++ rdPre)).map
    (fun D => (D.loc (.rd 0), (D.mem .R : RVal 1 Pr))) =
    some (.rFX none 2, ⟨2, toLex (1, θ₂.nc 1 0), θ₂.rnd 2⟩) := by decide

lemma valid_θ₁ : (alg2 (Au := Empty) θ₁).Valid αc := Impl.valid_of_crun _ (by decide)

lemma valid_θ₂ : (alg2 (Au := Empty) θ₂).Valid αc := Impl.valid_of_crun _ (by decide)

/-- **Counterexample to Lemma 38** (all coins). In `αc` with coins `θ₁`, reader `p_0` has no
`0`-effective read, yet every execution indistinguishable from it to `p_0` invokes `writeMax(0)`:
the `writeMax(0)` of `A` is compromised by `p_0`. -/
theorem lemma38_counterexample :
    (I θ₁).Valid αc ∧
    (∀ k, opOf αc ((Proc.rd 0 : P), k) = some (MOp.read 0) →
      ¬ Impl.EffectiveFam I θ₁ αc (Proc.rd 0, k) (MResp.val 0)) ∧
    ∀ θ' α', (I θ').Valid α' → Impl.IndistFam I (Proc.rd 0) (θ₁, αc) (θ', α') →
      ∃ x, MOp.writeMax 0 ∈ opsOf α' (Proc.wr x) := by
  refine ⟨valid_θ₁, not_effective θ₁ valid_θ₁, fun θ' α' hv hind => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := good_of_indist θ₁ θ' run_pre_θ₁ hv hind
  rcases h3 with h3 | ⟨x, k, h3, -⟩
  · exact absurd h1 (by rw [h3]; exact lt_irrefl _)
  · have : v.val = 0 := by
      rw [Prod.Lex.lt_iff] at h2
      simp only [θ₁, show (1 : Fin 2) ≠ 0 by decide, ite_false, ofLex_toLex] at h2
      show (ofLex v).1 = 0
      omega
    exact ⟨x, this ▸ h3⟩

/-- **Lemma 38 of the paper is false** for Algorithm 2 (one reader, two writers, nonces in `ℕ`). -/
theorem lemma38_false : ¬ Lemma38 I := by
  intro h
  obtain ⟨hv, hne, hcomp⟩ := lemma38_counterexample
  rcases h θ₁ αc hv 0 0 with ⟨k, hk, he⟩ | ⟨θ', α', hv', hind, hno⟩
  · exact hne k hk he
  · obtain ⟨x, hx⟩ := hcomp θ' α' hv' hind
    exact hno _ hx

/-- Fresh nonces: never equal to the initial nonce `N₀ = 0`, and pairwise distinct. -/
def Fresh {m : ℕ} {W : Type} (θ : Coins m W) : Prop :=
  (∀ x k, θ.nc x k ≠ 0) ∧ ∀ x k x' k', θ.nc x k = θ.nc x' k' → x = x' ∧ k = k'

lemma fresh_θ₂ : Fresh θ₂ := by
  refine ⟨fun x k => by simp only [θ₂]; omega, fun x k x' k' h => ?_⟩
  simp only [θ₂] at h
  have hx : x.val = x'.val := by omega
  exact ⟨Fin.ext hx, by omega⟩

/-- The family of instances of Algorithm 2 with fresh nonces. -/
abbrev IF : {θ : Coins 1 (Fin 2) // Fresh θ} → Impl (amaxReg 1) (MBO 1) P (MLoc 1) :=
  fun θ => alg2 θ.1

/-- **Counterexample to Lemma 38 with fresh nonces.** -/
theorem lemma38_counterexample_fresh :
    (IF ⟨θ₂, fresh_θ₂⟩).Valid αc ∧
    (∀ k, opOf αc ((Proc.rd 0 : P), k) = some (MOp.read 0) →
      ¬ Impl.EffectiveFam IF ⟨θ₂, fresh_θ₂⟩ αc (Proc.rd 0, k) (MResp.val 0)) ∧
    ∀ θ' α', (IF θ').Valid α' → Impl.IndistFam IF (Proc.rd 0) (⟨θ₂, fresh_θ₂⟩, αc) (θ', α') →
      ∃ x, MOp.writeMax 0 ∈ opsOf α' (Proc.wr x) := by
  refine ⟨valid_θ₂, fun k hk he => ?_, fun θ' α' hv hind => ?_⟩
  · have hk0 : k = 0 := by
      rcases k with _ | k
      · rfl
      · simp [opOf, opsOf_αc_rd] at hk
    subst hk0
    have := he ⟨θ₂, fresh_θ₂⟩ αc valid_θ₂ (Impl.IndistFam.refl _ _ _) [] (by simpa using valid_θ₂)
      (MResp.val 1) (by simpa using respOf_αc_rd)
    simp at this
  · obtain ⟨v, h1, h2, h3⟩ := good_of_indist θ₂ θ'.1 run_pre_θ₂ hv hind
    rcases h3 with h3 | ⟨x, k, h3, h4⟩
    · exact absurd h1 (by rw [h3]; exact lt_irrefl _)
    · have hne := θ'.2.1 x k
      have : v.val = 0 := by
        rw [Prod.Lex.lt_iff] at h2
        simp only [θ₂, ofLex_toLex] at h2 h4
        show (ofLex v).1 = 0
        simp only [Pr.nonce] at h4
        omega
      exact ⟨x, this ▸ h3⟩

/-- **Lemma 38 of the paper is false** even when nonces are required to be fresh. -/
theorem lemma38_false_fresh : ¬ Lemma38 IF := by
  intro h
  obtain ⟨hv, hne, hcomp⟩ := lemma38_counterexample_fresh
  rcases h ⟨θ₂, fresh_θ₂⟩ αc hv 0 0 with ⟨k, hk, he⟩ | ⟨θ', α', hv', hind, hno⟩
  · exact hne k hk he
  · obtain ⟨x, hx⟩ := hcomp θ' α' hv' hind
    exact hno _ hx

end Podc.AuditingWithoutLeaks.MaxReg
