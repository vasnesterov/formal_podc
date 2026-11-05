import Papers.PODC2012.LimitedUseSnapshots.SnapshotMWUp
import Papers.PODC2012.LimitedUseSnapshots.SnapshotCost

/-!
# Theorem 5.1 of Aspnes–Attiya–Censor-Hillel–Ellen (multi-writer snapshots, Algorithm 4)

* `theorem_5_1`: Algorithm 4 (with an atomic single-writer snapshot `s` and an atomic max
  register `timestamp`) is a linearizable `c`-component multi-writer snapshot.
* `theorem_5_1_update_cost`, `theorem_5_1_scan_cost`: an `MW-Update` costs one `ReadMax` and one
  `WriteMax` (`GetTS`) plus one `Update(s)`; an `MW-Scan` costs one `Scan(s)`. With `s`
  implemented by Algorithm 3 (Lemma 4.3) and `timestamp` a `(b − 1)`-limited-use max register
  (`O(log b)`), this is the paper's `O(log² b log n)` and `O(log b)`.

The paper says the `MW-Update` "is always linearized after it performs Line 2"; this is not
quite so (another process with a larger timestamp, obtained from the same `ReadMax` value, can
write `s` between the `ReadMax` and the `WriteMax` of the operation), but the linearization
point always follows the operation's `ReadMax`, hence its invocation, which is all the proof
needs (`detTs`: the timestamp is determined from the `ReadMax` on).
-/

namespace Podc.LimitedUseSnapshots.Snapshot.MW

open Cslib.SharedMemory

variable {n c : ℕ} {W : Type} {w₀ : Fin c → W} [NeZero n]

theorem inv4_step {α : List (Label (Fin n) (mwSnap c W w₀))} {C C' : Cfg4 n c W w₀}
    {L : Lin4 c W w₀ n} (hα : (alg4 n w₀).run α = some C) (hI : Inv4 α C L)
    {ℓ : Label (Fin n) (mwSnap c W w₀)} (h : (alg4 n w₀).step C ℓ = some C') :
    ∃ L', Inv4 (α ++ [ℓ]) C' L' := by
  cases ℓ with
  | inv p o => exact ⟨L, inv4_step_inv hα hI h⟩
  | ret p r => exact ⟨L, inv4_step_ret hα hI h⟩
  | tau p =>
    have hP := hI.proc p
    have hstep := Impl.step_tau h
    cases hpc : (C.loc p).pc with
    | idle => simp only [PInv4, hpc] at hP; exact absurd hP.1 hstep.1
    | rd j v => exact ⟨L, inv4_step_rd hI hpc h⟩
    | wr j v r => exact ⟨L, inv4_step_wr hI hpc h⟩
    | up j => exact inv4_step_up hα hI hpc h
    | sc => exact ⟨_, inv4_step_sc hα hI hpc h⟩
    | ack =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := hstep
      simp [act4, hpc] at hact
    | retS val =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := hstep
      simp [act4, hpc] at hact

theorem exists_inv4 {α : List (Label (Fin n) (mwSnap c W w₀))} {C : Cfg4 n c W w₀}
    (h : (alg4 n w₀).run α = some C) : ∃ L, Inv4 α C L :=
  Impl.run_induction (Q := fun α C => ∃ L, Inv4 α C L) ⟨[], inv4_init⟩
    (fun _ _ _ _ hα ⟨_, hI⟩ hs => inv4_step hα hI hs) h

/-- **Theorem 5.1** of [Aspnes–Attiya–Censor-Hillel–Ellen] (linearizability): Algorithm 4 is a
linearizable implementation of a `c`-component multi-writer snapshot for `n ≥ 1` processes
(with an atomic single-writer snapshot and an atomic max register as base objects). -/
theorem theorem_5_1 : (alg4 n w₀).Linearizable :=
  Impl.linearizable_of_run fun _ _ h => let ⟨L, hI⟩ := exists_inv4 h; ⟨L, hI.lin⟩

/-! ### Step complexity -/

/-- Costs of the operations on the base objects of Algorithm 4. -/
structure Costs4 where
  /-- `Update(s, i, ·)`. -/
  upd : ℕ
  /-- `Scan(s)`. -/
  scan : ℕ
  /-- `ReadMax(timestamp)`. -/
  rmax : ℕ
  /-- `WriteMax(timestamp, ·)`. -/
  wmax : ℕ

variable (K : Costs4)

variable (n c W w₀) in
/-- The cost of a primitive operation of Algorithm 4. -/
def opCost4 : (o : Obj4) → (obj4 n c W w₀ o).Op → ℕ
  | .s, .update _ _ => K.upd
  | .s, .scan => K.scan
  | .ts, .readMax => K.rmax
  | .ts, .writeMax _ => K.wmax

/-- Remaining cost of an operation. -/
def μ4 (_ : Fin n) (l : Loc4 c W) : ℕ :=
  match l.pc with
  | .rd _ _ => K.rmax + K.wmax + K.upd
  | .wr _ _ _ => K.wmax + K.upd
  | .up _ => K.upd
  | .sc => K.scan
  | _ => 0

lemma μ4_drop (i : Fin n) (l : Loc4 c W) {o : Obj4} {op : (obj4 n c W w₀ o).Op}
    {k : (obj4 n c W w₀ o).Resp → Loc4 c W} (h : act4 i l = .access o op k) (x) :
    μ4 K i (k x) + opCost4 n c W w₀ K o op ≤ μ4 K i l := by
  rcases l with ⟨rcd, pc⟩
  cases pc with
  | idle | ack | retS _ => simp only [act4] at h; cases h
  | rd j v => simp only [act4] at h; cases h; simp [μ4, opCost4]; omega
  | wr j v r => simp only [act4] at h; cases h; simp [μ4, opCost4]; omega
  | up j => simp only [act4] at h; cases h; simp [μ4, opCost4]
  | sc => simp only [act4] at h; cases h; simp [μ4, opCost4]

lemma loc_after_inv4 {α : List (Label (Fin n) (mwSnap c W w₀))} {p : Fin n} {o : MOp c W}
    {C₁ : Cfg4 n c W w₀} (h₁ : (alg4 n w₀).run (α ++ [.inv p o]) = some C₁) :
    ∃ r, C₁.loc p = ⟨r, match o with | .update j v => .rd j v | .scan => .sc⟩ := by
  rw [Impl.run_concat] at h₁
  cases hα : (alg4 n w₀).run α with
  | none => simp [hα] at h₁
  | some C₀ =>
    simp only [hα, Option.bind_some] at h₁
    obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv h₁
    refine ⟨(C₀.loc p).rcd, ?_⟩
    rw [hloc, Function.update_self]; cases o <;> rfl

/-- **Theorem 5.1** of [Aspnes–Attiya–Censor-Hillel–Ellen] (step complexity of `MW-Update`):
`GetTS` (one `ReadMax`, one `WriteMax`) plus one `Update(s)`. -/
theorem theorem_5_1_update_cost {α γ : List (Label (Fin n) (mwSnap c W w₀))} {p : Fin n}
    {j : Fin c} {v : W} {C₁ C' : Cfg4 n c W w₀}
    (h₁ : (alg4 n w₀).run (α ++ [.inv p (.update j v)]) = some C₁)
    (h : (alg4 n w₀).runFrom C₁ γ = some C') (hret : ∀ r, .ret p r ∉ γ) :
    tauCost (alg4 n w₀) (opCost4 n c W w₀ K) p C₁ γ ≤ K.rmax + K.wmax + K.upd := by
  have hb := tauCost_le_of_inv (alg4 n w₀) (opCost4 n c W w₀ K) (μ4 K)
    (fun i l _ _ _ h x => μ4_drop K i l h x) h₁ h hret
  obtain ⟨r, hr⟩ := loc_after_inv4 h₁
  rw [hr] at hb
  simpa only [μ4] using hb

/-- **Theorem 5.1** of [Aspnes–Attiya–Censor-Hillel–Ellen] (step complexity of `MW-Scan`): one
`Scan(s)`. -/
theorem theorem_5_1_scan_cost {α γ : List (Label (Fin n) (mwSnap c W w₀))} {p : Fin n}
    {C₁ C' : Cfg4 n c W w₀} (h₁ : (alg4 n w₀).run (α ++ [.inv p .scan]) = some C₁)
    (h : (alg4 n w₀).runFrom C₁ γ = some C') (hret : ∀ r, .ret p r ∉ γ) :
    tauCost (alg4 n w₀) (opCost4 n c W w₀ K) p C₁ γ ≤ K.scan := by
  have hb := tauCost_le_of_inv (alg4 n w₀) (opCost4 n c W w₀ K) (μ4 K)
    (fun i l _ _ _ h x => μ4_drop K i l h x) h₁ h hret
  obtain ⟨r, hr⟩ := loc_after_inv4 h₁
  rw [hr] at hb
  simpa only [μ4] using hb

end Podc.LimitedUseSnapshots.Snapshot.MW
