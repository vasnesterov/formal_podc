import Papers.PODC2015.SetAgreementSpace.Algorithm

/-!
# Figure 3 is not obstruction-free

The algorithm of Figure 3 (`fig3 false`) satisfies validity and `k`-agreement (`Safety.lean`), but
**not** `m`-obstruction-freedom, for any parameters `1 ≤ m ≤ k < n`.

The flaw: a process adopts (lines 11–13) the value `w` of a duplicated pair `(w, q)` written by
another process `q`, but afterwards it writes `(w, id)`, a *different pair*. If the duplicated pair
stays in memory, the next scan again satisfies line 11 and the process adopts `w` again, forever,
without changing `i`; it never decides when more than `m` different pairs are in memory. The proof
of Lemma 5 (Case 2) assumes that adopting changes the preferred value, which is false here.

Smallest instance (`n = 2`, `k = m = 1`, `r = 3`): `p₁` runs solo and decides, leaving
`A = [(v,p₁),(v,p₁),(v,p₁)]`; then `p₀` runs solo: it writes `(v₀,p₀)` into `A[0]`, sees two
different pairs and the duplicate `(v,p₁)`, adopts `v`, writes `(v,p₀)` into `A[0]`, sees two
different pairs and the duplicate `(v,p₁)` again, … forever.

General instance: processes `1, …, m` write `(v, j)` into prefixes of `A` of decreasing length and
stop (crash), so that `A[1..r-1]` holds the `m` pairs `(v,1), …, (v,m)` with `(v,1)` duplicated;
then process `0` runs solo forever.

## Main results
* `fig3_not_obstructionFree`: from a reachable one-shot configuration, process `0` running solo
  never returns.
* `fig3_not_mObstructionFree`: Figure 3 is not `m`-obstruction-free (on one-shot executions), for
  all `1 ≤ m ≤ k < n` and `r = n + 2m - k` — the termination claim of Theorem 7 (Section 4.1) for
  this algorithm is false.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

variable {V : Type} [DecidableEq V] [Inhabited V] {n m r : ℕ} [NeZero r] {fix : Bool}

section Steps

variable {C : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} {p : Fin n}

lemma fig3_step_upd (hp : C.pend p ≠ none) (hpc : (C.loc p).pc = .upd) :
    (fig3 fix n m r).step C (.tau p) = some
      { C with mem := Function.update C.mem ()
                 (Function.update (C.mem ()) (C.loc p).i (some ((C.loc p).pref, p))),
               loc := Function.update C.loc p { C.loc p with pc := .scan } } := by
  have hact : (fig3 fix n m r).act p (C.loc p) =
      .access () (.update (C.loc p).i ((C.loc p).pref, p)) (fun _ => { C.loc p with pc := .scan }) := by
    simp only [fig3, hpc]
  rw [Impl.step_tau_eq_some hp hact]

lemma fig3_step_scan (hp : C.pend p ≠ none) (hpc : (C.loc p).pc = .scan) :
    (fig3 fix n m r).step C (.tau p) = some
      { C with loc := Function.update C.loc p (afterScan fix m p (C.loc p) (C.mem ())) } := by
  have hact : (fig3 fix n m r).act p (C.loc p) =
      .access () .scan (fun s => afterScan fix m p (C.loc p) s) := by
    simp only [fig3, hpc]
  rw [Impl.step_tau_eq_some hp hact]
  have hm : Function.update C.mem () ((Mem V n r ()).δ (C.mem ()) SnapOpOpt.scan).1 = C.mem := by
    funext u; cases u; simp
  simp only [hm]

lemma fig3_step_inv (hp : C.pend p = none) (v : V) :
    (fig3 fix n m r).step C (.inv p v) = some
      { C with pend := Function.update C.pend p (some v),
               loc := Function.update C.loc p ⟨.upd, v, 0, none⟩ } := by
  rw [Impl.step_inv_eq_some hp trivial]
  rfl

end Steps

section Advance

variable {C : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} {p : Fin n}

/-- If some component other than `i` holds `⊥`, a scan neither decides nor adopts: `i` advances. -/
lemma afterScan_of_bot (l : Loc V r) (s : Fin r → Cell V n) {j : Fin r} (hj : j ≠ l.i)
    (hs : s j = none) : afterScan fix m p l s = { l with pc := .upd, i := l.i + 1 } := by
  unfold afterScan
  rw [if_neg (fun h => h.2 j hs), if_neg (fun h => (h.1 j hj).1 hs)]

/-- One loop iteration (update + scan) while some other component is `⊥`. -/
lemma run_iter_of_bot (hp : C.pend p ≠ none) (hpc : (C.loc p).pc = .upd) {j : Fin r}
    (hj : j ≠ (C.loc p).i) (hs : C.mem () j = none) :
    ∃ C', (fig3 fix n m r).runFrom C [.tau p, .tau p] = some C' ∧ C'.pend = C.pend ∧
      (∀ q, q ≠ p → C'.loc q = C.loc q) ∧ C'.loc p = { C.loc p with i := (C.loc p).i + 1 } ∧
      C'.mem () = Function.update (C.mem ()) (C.loc p).i (some ((C.loc p).pref, p)) := by
  refine ⟨{ C with
      mem := Function.update C.mem () (Function.update (C.mem ()) (C.loc p).i
        (some ((C.loc p).pref, p))),
      loc := Function.update C.loc p { C.loc p with i := (C.loc p).i + 1 } }, ?_, rfl,
    fun q hq => by simp [Function.update_of_ne hq], by simp, by simp⟩
  rw [Impl.runFrom_cons, fig3_step_upd hp hpc, Option.bind_some, Impl.runFrom_cons,
    fig3_step_scan (by simpa using hp) (by simp), Option.bind_some, Impl.runFrom_nil]
  simp only [Function.update_self]
  rw [afterScan_of_bot (j := j) _ _ (by simpa using hj)
    (by simp [Function.update_of_ne hj, hs])]
  simp only [Function.update_idem]
  congr 3
  cases h : C.loc p; simp_all

/-- `x` loop iterations of a process starting at `i = 0` while the last component is `⊥`:
the process writes `(pref, p)` into components `0, …, x - 1`. -/
lemma run_iters (v : V) (x : ℕ) (hp : C.pend p ≠ none) (hpc : (C.loc p).pc = .upd)
    (hi : (C.loc p).i = 0) (hpref : (C.loc p).pref = v) (hr : 2 ≤ r)
    (hbot : C.mem () ⟨r - 1, by omega⟩ = none) (hx : x ≤ r - 1) :
    ∃ C', (fig3 fix n m r).runFrom C (List.replicate (2 * x) (.tau p)) = some C' ∧
      C'.pend = C.pend ∧ (∀ q, q ≠ p → C'.loc q = C.loc q) ∧ (C'.loc p).pc = .upd ∧
      (C'.loc p).pref = v ∧ ((C'.loc p).i).val = x ∧
      ∀ ℓ : Fin r, C'.mem () ℓ = if ℓ.val < x then some (v, p) else C.mem () ℓ := by
  induction x with
  | zero =>
    refine ⟨C, by simp, rfl, fun _ _ => rfl, hpc, hpref, by simp [hi], fun ℓ => by simp⟩
  | succ x ih =>
    obtain ⟨C₁, h₁, hpend₁, hloc₁, hpc₁, hpref₁, hi₁, hmem₁⟩ := ih (by omega)
    have hj : (⟨r - 1, by omega⟩ : Fin r) ≠ (C₁.loc p).i := by
      intro h; rw [← h] at hi₁; simp at hi₁; omega
    obtain ⟨C₂, h₂, hpend₂, hloc₂, hlocp₂, hmem₂⟩ := run_iter_of_bot (fix := fix) (m := m)
      (hpend₁ ▸ hp) hpc₁ hj (by rw [hmem₁]; simp only; rw [if_neg (by omega), hbot])
    refine ⟨C₂, ?_, hpend₂.trans hpend₁, fun q hq => (hloc₂ q hq).trans (hloc₁ q hq), ?_, ?_, ?_,
      ?_⟩
    · rw [show 2 * (x + 1) = 2 * x + 2 by omega, List.replicate_add,
        Impl.runFrom_append, h₁, Option.bind_some]
      exact h₂
    · rw [hlocp₂]; exact hpc₁
    · rw [hlocp₂]; exact hpref₁
    · rw [hlocp₂]; simp only [Fin.val_add, hi₁]
      rw [Fin.val_one', Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    · intro ℓ
      rw [hmem₂, hpref₁]
      by_cases hℓ : ℓ = (C₁.loc p).i
      · subst hℓ; simp [hi₁]
      · rw [Function.update_of_ne hℓ, hmem₁]
        have : ℓ.val ≠ x := fun h => hℓ (Fin.ext (h.trans hi₁.symm))
        by_cases h : ℓ.val < x
        · simp [h, show ℓ.val < x + 1 by omega]
        · simp [h, show ¬ ℓ.val < x + 1 by omega]

end Advance

section Loop

variable {C : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} {p : Fin n}

lemma fig3_soloStep_of_step (hp : C.pend p ≠ none) (hpc : (C.loc p).pc = .upd ∨ (C.loc p).pc = .scan)
    {C' : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)}
    (h : (fig3 fix n m r).step C (.tau p) = some C') : (fig3 fix n m r).soloStep p C = C' := by
  have hnl : (fig3 fix n m r).nextLabel C p = .tau p := by
    rcases hpc with hpc | hpc <;> simp [Impl.nextLabel, fig3, hpc]
  simp [Impl.soloStep, hp, hnl, h]

/-- Facts about the frozen memory `M` (outside component `0`) that make process `p₀` livelock:
no `⊥` and no pair of `p₀`, a duplicated pair, and `m` different pairs. -/
structure LoopMem (m : ℕ) (p₀ : Fin n) (M : Fin r → Cell V n) : Prop where
  ne_bot : ∀ ℓ, ℓ ≠ 0 → M ℓ ≠ none
  ne_self : ∀ ℓ, ℓ ≠ 0 → ∀ w, M ℓ ≠ some (w, p₀)
  dup : ∃ j₁ j₂, j₁ ≠ j₂ ∧ j₁ ≠ 0 ∧ j₂ ≠ 0 ∧ M j₁ = M j₂
  many : ∃ g : Fin m → Fin r, (∀ t, g t ≠ 0) ∧ Function.Injective (M ∘ g)

/-- The livelock invariant of process `p₀`: it stays at component `0`, and the other components
are frozen to `M`. -/
def LoopInv (p₀ : Fin n) (M : Fin r → Cell V n) (C : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)) :
    Prop :=
  C.pend p₀ ≠ none ∧ (C.loc p₀).i = 0 ∧
    ((C.loc p₀).pc = .upd ∨ ((C.loc p₀).pc = .scan ∧ C.mem () 0 = some ((C.loc p₀).pref, p₀))) ∧
    ∀ ℓ, ℓ ≠ 0 → C.mem () ℓ = M ℓ

lemma not_decideCond_of_loopMem {p₀ : Fin n} {M : Fin r → Cell V n} (hM : LoopMem m p₀ M)
    {s : Fin r → Cell V n} (hs : ∀ ℓ, ℓ ≠ 0 → s ℓ = M ℓ) {w : V} (h0 : s 0 = some (w, p₀)) :
    ¬ DecideCond m s := by
  rintro ⟨hcard, -⟩
  obtain ⟨g, hg0, hinj⟩ := hM.many
  have hsub : insert (s 0) (Finset.univ.image (M ∘ g)) ⊆ Finset.univ.image s := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_image.2 ⟨g t, Finset.mem_univ _, hs _ (hg0 t)⟩
  have hnot : s 0 ∉ Finset.univ.image (M ∘ g) := by
    intro hx
    obtain ⟨t, -, ht⟩ := Finset.mem_image.1 hx
    exact hM.ne_self _ (hg0 t) w (by simpa [h0] using ht)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin] at this
  omega

lemma loopInv_soloStep {p₀ : Fin n} {M : Fin r → Cell V n} (hM : LoopMem m p₀ M)
    (hC : LoopInv p₀ M C) : LoopInv p₀ M ((fig3 false n m r).soloStep p₀ C) := by
  obtain ⟨hp, hi, hpc, hmem⟩ := hC
  rcases hpc with hpc | ⟨hpc, h0⟩
  · rw [fig3_soloStep_of_step hp (.inl hpc) (fig3_step_upd hp hpc)]
    refine ⟨hp, by simp [hi], .inr ⟨by simp, by simp [hi]⟩, fun ℓ hℓ => ?_⟩
    simp only [Function.update_self]
    rw [Function.update_of_ne (by rwa [hi]), hmem ℓ hℓ]
  · rw [fig3_soloStep_of_step hp (.inr hpc) (fig3_step_scan hp hpc)]
    have hnd : ¬ DecideCond m (C.mem ()) := not_decideCond_of_loopMem hM hmem h0
    have had : AdoptCond false (C.mem ()) (C.loc p₀).i (C.loc p₀).pref p₀ := by
      refine ⟨fun j hj => ?_, ?_, by simp⟩
      · rw [hi] at hj
        rw [hmem j hj]
        exact ⟨hM.ne_bot j hj, hM.ne_self j hj _⟩
      · obtain ⟨j₁, j₂, hne, h₁, h₂, heq⟩ := hM.dup
        exact ⟨j₁, j₂, hne, by rw [hmem _ h₁, hmem _ h₂, heq]⟩
    simp only [Function.update_self, afterScan, if_neg hnd, if_pos had]
    exact ⟨hp, by simpa using hi, .inl (by simp), hmem⟩

/-- Process `p₀` never returns when running solo from a configuration satisfying the livelock
invariant. -/
lemma loopInv_iterate {p₀ : Fin n} {M : Fin r → Cell V n} (hM : LoopMem m p₀ M)
    (hC : LoopInv p₀ M C) (k : ℕ) : (((fig3 false n m r).soloStep p₀)^[k] C).pend p₀ ≠ none := by
  suffices ∀ k, LoopInv p₀ M (((fig3 false n m r).soloStep p₀)^[k] C) from (this k).1
  intro k
  induction k with
  | zero => exact hC
  | succ k ih => rw [Function.iterate_succ_apply']; exact loopInv_soloStep hM ih

end Loop

section Construction

/-- The last component `r - 1`. -/
def lastIdx (r : ℕ) [NeZero r] : Fin r := ⟨r - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne r)) one_pos⟩

variable {C : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} {q : Fin n}

/-- A fresh process proposes `v` and performs `x` loop iterations while the last component is `⊥`:
it writes `(v, q)` into components `0, …, x - 1`. -/
lemma run_phase (v : V) (x : ℕ) (hq : C.pend q = none) (hr : 2 ≤ r)
    (hbot : C.mem () (lastIdx r) = none) (hx : x ≤ r - 1) :
    ∃ C', (fig3 fix n m r).runFrom C (.inv q v :: List.replicate (2 * x) (.tau q)) = some C' ∧
      C'.pend = Function.update C.pend q (some v) ∧ (∀ q', q' ≠ q → C'.loc q' = C.loc q') ∧
      (C'.loc q).pc = .upd ∧ (C'.loc q).pref = v ∧ ((C'.loc q).i).val = x ∧
      ∀ ℓ : Fin r, C'.mem () ℓ = if ℓ.val < x then some (v, q) else C.mem () ℓ := by
  set C₁ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r) :=
    { C with pend := Function.update C.pend q (some v),
             loc := Function.update C.loc q ⟨.upd, v, 0, none⟩ } with hC₁
  obtain ⟨C', h, hpend, hloc, hpc, hpref, hi, hmem⟩ := run_iters (fix := fix) (m := m) (C := C₁)
    (p := q) v x (by simp [C₁]) (by simp [C₁]) (by simp [C₁]) (by simp [C₁]) hr
    (by simpa [C₁, lastIdx] using hbot) hx
  refine ⟨C', ?_, hpend, fun q' hq' => by rw [hloc q' hq']; simp [C₁, Function.update_of_ne hq'],
    hpc, hpref, hi, hmem⟩
  rw [Impl.runFrom_cons, fig3_step_inv hq, Option.bind_some]
  exact h

lemma opsOf_replicate_tau (k : ℕ) (q q' : Fin n) :
    opsOf (List.replicate k (Label.tau q : Label (Fin n) (saObj V))) q' = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, opsOf_cons, ih]; rfl

/-- Owner of component `ℓ < r - 1` after processes `1, …, j` have run (see `PhInv`). -/
def own (m j ℓ : ℕ) : ℕ := if ℓ ≤ m + 1 - j then j else if ℓ ≤ m - 1 then m + 1 - ℓ else 1

/-- The configuration after processes `1, …, j` have run: process `1` wrote `(v,1)` into
components `0, …, r - 2` and is poised to write component `r - 1` (still `⊥`); process `j' ≥ 2`
then wrote `(v, j')` into components `0, …, m + 1 - j'`; processes `0` and `> j` have not
invoked. -/
def PhInv (m j : ℕ) (v : V) (α : List (Label (Fin n) (saObj V)))
    (C : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)) : Prop :=
  (fig3 false n m r).run α = some C ∧ OneShot α ∧
    (∀ q : Fin n, (q.val = 0 ∨ j < q.val) → opsOf α q = [] ∧ C.pend q = none) ∧
    C.mem () (lastIdx r) = none ∧
    (∀ ℓ : Fin r, ℓ.val < r - 1 → ∃ q : Fin n, C.mem () ℓ = some (v, q) ∧ q.val = own m j ℓ.val) ∧
    (∀ q : Fin n, q.val = 1 →
      C.pend q ≠ none ∧ (C.loc q).pc = .upd ∧ ((C.loc q).i).val = r - 1 ∧ (C.loc q).pref = v)

lemma phInv_one (v : V) (hn : 2 ≤ n) (hr : 2 ≤ r) :
    ∃ α C, PhInv (n := n) (r := r) m 1 v α C := by
  set p₁ : Fin n := ⟨1, by omega⟩
  obtain ⟨C, h, hpend, hloc, hpc, hpref, hi, hmem⟩ :=
    run_phase (fix := false) (m := m) (C := (fig3 false n m r).initCfg) (q := p₁) v (r - 1)
      rfl hr rfl le_rfl
  refine ⟨_, C, h, fun q' => ?_, fun q' hq' => ⟨?_, ?_⟩, ?_, fun ℓ hℓ => ⟨p₁, ?_, ?_⟩,
    fun q' hq' => ?_⟩
  · simp only [opsOf_cons, opsOf_replicate_tau, List.append_nil]
    cases h : (Label.inv p₁ v : Label (Fin n) (saObj V)).invOf q' <;> simp
  · have : p₁ ≠ q' := fun h => by subst h; simp [p₁] at hq'
    simp [opsOf_replicate_tau, Label.invOf, this]
  · have : q' ≠ p₁ := fun h => by subst h; simp [p₁] at hq'
    rw [hpend, Function.update_of_ne this]; rfl
  · rw [hmem]; simp [lastIdx]; rfl
  · rw [hmem]; simp [hℓ]
  · simp [own, p₁]; omega
  · have : q' = p₁ := Fin.ext hq'
    subst this
    exact ⟨by simp [hpend], hpc, hi, hpref⟩

lemma oneShot_append_phase {α : List (Label (Fin n) (saObj V))} (h : OneShot α) {q : Fin n}
    (hq : opsOf α q = []) (v : V) (k : ℕ) :
    OneShot (α ++ (.inv q v :: List.replicate k (.tau q))) := by
  rw [← List.singleton_append, ← List.append_assoc]
  exact (h.append_inv hq v).append_of_opsOf_nil (fun _ => opsOf_replicate_tau _ _ _)

lemma opsOf_phase_of_ne {q q' : Fin n} (h : q' ≠ q) (v : V) (k : ℕ) :
    opsOf (.inv q v :: List.replicate k (.tau q) : List (Label (Fin n) (saObj V))) q' = [] := by
  simp [opsOf_replicate_tau, Label.invOf, Ne.symm h]

lemma phInv_succ {v : V} {j : ℕ} {α : List (Label (Fin n) (saObj V))}
    {C : Config (saObj V) (Mem V n r) (Fin n) (Loc V r)} (hC : PhInv m j v α C) (hj : 1 ≤ j)
    (hjm : j + 1 ≤ m) (hmn : m < n) (hmr : m + 2 ≤ r) :
    ∃ α' C', PhInv (n := n) (r := r) m (j + 1) v α' C' := by
  obtain ⟨hrun, hos, hidle, hbot, hmem, hp₁⟩ := hC
  set q : Fin n := ⟨j + 1, by omega⟩
  obtain ⟨hqops, hqpend⟩ := hidle q (.inr (by simp [q]))
  obtain ⟨C₂, h₂, hpend₂, hloc₂, hpc₂, hpref₂, hi₂, hmem₂⟩ :=
    run_phase (fix := false) (m := m) (C := C) (q := q) v (m - j) hqpend (by omega) hbot
      (by omega)
  have hq₂ : C₂.pend q ≠ none := by simp [hpend₂]
  set C₃ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r) :=
    { C₂ with
      mem := Function.update C₂.mem () (Function.update (C₂.mem ()) (C₂.loc q).i
        (some ((C₂.loc q).pref, q)))
      loc := Function.update C₂.loc q { C₂.loc q with pc := .scan } } with hC₃
  have h₃ := fig3_step_upd (fix := false) (m := m) hq₂ hpc₂
  have hmem₃ : ∀ ℓ : Fin r, C₃.mem () ℓ = if ℓ.val ≤ m - j then some (v, q) else C.mem () ℓ := by
    intro ℓ
    simp only [C₃, Function.update_self, hpref₂]
    by_cases hℓ : ℓ = (C₂.loc q).i
    · subst hℓ; simp [hi₂]
    · rw [Function.update_of_ne hℓ, hmem₂]
      have : ℓ.val ≠ m - j := fun h => hℓ (Fin.ext (h.trans hi₂.symm))
      by_cases h : ℓ.val < m - j
      · simp [h, show ℓ.val ≤ m - j by omega]
      · simp [h, show ¬ ℓ.val ≤ m - j by omega]
  refine ⟨α ++ (.inv q v :: List.replicate (2 * (m - j)) (.tau q)) ++ [.tau q], C₃, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [Impl.run_append_of_eq _ (Impl.run_append_of_eq _ hrun _ |>.trans h₂), Impl.runFrom_singleton]
    exact h₃
  · exact (oneShot_append_phase hos hqops v _).append_of_opsOf_nil
      (fun _ => opsOf_replicate_tau 1 _ _)
  · intro q' hq'
    have hne : q' ≠ q := fun h => by subst h; simp [q] at hq'
    obtain ⟨h1, h2⟩ := hidle q' (by omega)
    refine ⟨?_, ?_⟩
    · rw [opsOf_append, opsOf_append, h1, opsOf_phase_of_ne hne]; rfl
    · simp only [C₃, hpend₂, Function.update_of_ne hne]; exact h2
  · rw [hmem₃, if_neg (by simp [lastIdx]; omega)]; exact hbot
  · intro ℓ hℓ
    rw [hmem₃]
    by_cases h : ℓ.val ≤ m - j
    · refine ⟨q, by simp [h], ?_⟩
      simp only [own, q]; rw [if_pos (by omega)]
    · obtain ⟨q', hq', hown⟩ := hmem ℓ hℓ
      refine ⟨q', by simp [h, hq'], ?_⟩
      rw [hown]; simp only [own]
      split_ifs <;> omega
  · intro q' hq'
    have hne : q' ≠ q := fun h => by subst h; simp [q] at hq'; omega
    obtain ⟨a, b, c, d⟩ := hp₁ q' hq'
    have hl : C₃.loc q' = C.loc q' := by
      simp only [C₃, Function.update_of_ne hne]; exact hloc₂ q' hne
    refine ⟨?_, by rw [hl]; exact b, by rw [hl]; exact c, by rw [hl]; exact d⟩
    simp only [C₃, hpend₂, Function.update_of_ne hne]; exact a

lemma phInv_m (v : V) (hm : 1 ≤ m) (hmn : m < n) (hmr : m + 2 ≤ r) :
    ∃ α C, PhInv (n := n) (r := r) m m v α C := by
  suffices ∀ j, 1 ≤ j → j ≤ m → ∃ α C, PhInv (n := n) (r := r) m j v α C from this m hm le_rfl
  intro j hj hjm
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · exact phInv_one v (by omega) (by omega)
    · obtain ⟨α, C, hC⟩ := ih hj' (by omega)
      exact phInv_succ hC hj' hjm hmn hmr

/-- The frozen memory: component `r - 1` holds `(v, 1)`, the others `(v, own m m ℓ)`. -/
lemma loopMem_of_owner {M : Fin r → Cell V n} {v : V} (hm : 1 ≤ m) (hmn : m < n)
    (hr : 2 * m + 1 ≤ r)
    (hM : ∀ ℓ : Fin r, ∃ q : Fin n, M ℓ = some (v, q) ∧
      q.val = if ℓ.val = r - 1 then 1 else own m m ℓ.val) :
    LoopMem m (⟨0, by omega⟩ : Fin n) M := by
  have hpos : ∀ ℓ : Fin r, ∀ q : Fin n, M ℓ = some (v, q) → q.val ≠ 0 := by
    intro ℓ q hq h0
    obtain ⟨q', hq', hown⟩ := hM ℓ
    rw [hq] at hq'; cases hq'
    rw [h0] at hown
    split_ifs at hown with h1 <;> simp [own] at hown <;> split_ifs at hown <;> omega
  refine ⟨fun ℓ _ h => ?_, fun ℓ _ w h => ?_, ?_, ?_⟩
  · obtain ⟨q, hq, -⟩ := hM ℓ; rw [hq] at h; cases h
  · obtain ⟨q, hq, -⟩ := hM ℓ
    rw [hq] at h; cases h
    exact hpos ℓ _ hq rfl
  · refine ⟨⟨r - 2, by omega⟩, lastIdx r, ?_, ?_, ?_, ?_⟩
    · simp [lastIdx, Fin.ext_iff]; omega
    · simp [Fin.ext_iff]; omega
    · simp [lastIdx, Fin.ext_iff]; omega
    · obtain ⟨q₁, hq₁, ho₁⟩ := hM ⟨r - 2, by omega⟩
      obtain ⟨q₂, hq₂, ho₂⟩ := hM (lastIdx r)
      rw [hq₁, hq₂]
      have : q₁ = q₂ := by
        apply Fin.ext
        simp only [lastIdx] at ho₂
        rw [ho₁, ho₂]
        simp only [own]
        split_ifs <;> omega
      rw [this]
  · refine ⟨fun t => if t.val = 0 then lastIdx r else ⟨m - t.val, by omega⟩, fun t => ?_, ?_⟩
    · dsimp only
      split_ifs
      · simp [lastIdx, Fin.ext_iff]; omega
      · simp [Fin.ext_iff]; omega
    · have key : ∀ t : Fin m, ∃ q : Fin n,
          M (if t.val = 0 then lastIdx r else ⟨m - t.val, by omega⟩) = some (v, q) ∧
          q.val = t.val + 1 := by
        intro t
        split_ifs with ht
        · obtain ⟨q, hq, ho⟩ := hM (lastIdx r)
          exact ⟨q, hq, by rw [ho]; simp [lastIdx, ht]⟩
        · obtain ⟨q, hq, ho⟩ := hM ⟨m - t.val, by omega⟩
          refine ⟨q, hq, ?_⟩
          rw [ho]; simp only [own]
          split_ifs <;> omega
      intro t₁ t₂ h
      obtain ⟨q₁, hq₁, ho₁⟩ := key t₁
      obtain ⟨q₂, hq₂, ho₂⟩ := key t₂
      simp only [Function.comp_apply] at h
      rw [hq₁, hq₂] at h
      cases h
      exact Fin.ext (by omega)

/-- **The livelock.** For `1 ≤ m < n` and `r ≥ 2m + 1`, Figure 3 has a one-shot execution after
which process `0` has a pending `Propose` and never returns when running solo. -/
theorem fig3_livelock (v : V) (hm : 1 ≤ m) (hmn : m < n) (hr : 2 * m + 1 ≤ r) :
    ∃ α C, (fig3 (V := V) false n m r).run α = some C ∧ OneShot α ∧
      C.pend ⟨0, by omega⟩ ≠ none ∧
      ∀ k, (((fig3 (V := V) false n m r).soloStep ⟨0, by omega⟩)^[k] C).pend ⟨0, by omega⟩ ≠ none := by
  obtain ⟨α, C, hrun, hos, hidle, hbot, hmem, hp₁⟩ :=
    phInv_m (n := n) (r := r) (m := m) v hm hmn (by omega)
  set p₀ : Fin n := ⟨0, by omega⟩
  set p₁ : Fin n := ⟨1, by omega⟩
  obtain ⟨hp, hpc, hi, hpref⟩ := hp₁ p₁ rfl
  obtain ⟨h0ops, h0pend⟩ := hidle p₀ (.inl rfl)
  have hne : p₀ ≠ p₁ := by simp [p₀, p₁, Fin.ext_iff]
  have h₁ := fig3_step_upd (fix := false) (m := m) hp hpc
  set C₁ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r) :=
    { C with
      mem := Function.update C.mem () (Function.update (C.mem ()) (C.loc p₁).i
        (some ((C.loc p₁).pref, p₁)))
      loc := Function.update C.loc p₁ { C.loc p₁ with pc := .scan } }
  have hp₀₁ : C₁.pend p₀ = none := h0pend
  have h₂ := fig3_step_inv (fix := false) (m := m) hp₀₁ v
  set C₂ : Config (saObj V) (Mem V n r) (Fin n) (Loc V r) :=
    { C₁ with pend := Function.update C₁.pend p₀ (some v),
              loc := Function.update C₁.loc p₀ ⟨.upd, v, 0, none⟩ }
  have hlast : (C.loc p₁).i = lastIdx r := Fin.ext (by simp [hi, lastIdx])
  have hM : ∀ ℓ : Fin r, ∃ q : Fin n, C₂.mem () ℓ = some (v, q) ∧
      q.val = if ℓ.val = r - 1 then 1 else own m m ℓ.val := by
    intro ℓ
    simp only [C₂, C₁, Function.update_self, hlast, hpref]
    by_cases hℓ : ℓ = lastIdx r
    · subst hℓ; exact ⟨p₁, by simp, by simp [lastIdx, p₁]⟩
    · rw [Function.update_of_ne hℓ]
      have hlt : ℓ.val < r - 1 := by
        have := ℓ.isLt; have : ℓ.val ≠ r - 1 := fun h => hℓ (Fin.ext h); omega
      obtain ⟨q, hq, ho⟩ := hmem ℓ hlt
      exact ⟨q, hq, by rw [ho, if_neg (by omega)]⟩
  refine ⟨α ++ [.tau p₁, .inv p₀ v], C₂, ?_, ?_, by simp [C₂], fun k => ?_⟩
  · rw [Impl.run_append_of_eq _ hrun, Impl.runFrom_cons, h₁, Option.bind_some,
      Impl.runFrom_cons, h₂, Option.bind_some, Impl.runFrom_nil]
  · rw [show α ++ [.tau p₁, .inv p₀ v] = α ++ [.tau p₁] ++ [.inv p₀ v] by simp]
    refine (hos.append_of_opsOf_nil (fun _ => opsOf_replicate_tau 1 _ _)).append_inv ?_ v
    rw [opsOf_append, h0ops]; rfl
  · exact loopInv_iterate (loopMem_of_owner hm hmn hr hM) ⟨by simp [C₂, p₀], by simp [C₂, p₀],
      .inl (by simp [C₂, p₀]), fun _ _ => rfl⟩ k

/-- **Figure 3 is not `m`-obstruction-free** (refutes the termination part of Theorem 7 for the
algorithm of Figure 3): for all `1 ≤ m ≤ k < n`, with `r = n + 2m - k` components, the algorithm
is not `m'`-obstruction-free on one-shot executions for any `m' ≥ 1` — in particular neither
`m`-obstruction-free nor obstruction-free. -/
theorem fig3_not_mObstructionFree {k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k < n)
    [NeZero (n + 2 * m - k)] {m' : ℕ} (hm' : 1 ≤ m') :
    ¬ (fig3 (V := V) false n m (n + 2 * m - k)).MObstructionFreeOn m' OneShot := by
  obtain ⟨α, C, hrun, hos, -, hloop⟩ :=
    fig3_livelock (V := V) (n := n) (m := m) (r := n + 2 * m - k) default hm (by omega)
      (by omega)
  refine Impl.not_mObstructionFreeOn_of_solo prefixClosed_oneShot
    (fun β p h => h.append_of_opsOf_nil (fun _ => opsOf_replicate_tau 1 _ _)) hrun hos hloop hm'

/-- Corollary: Figure 3 is not even obstruction-free (solo-terminating) on one-shot executions. -/
theorem fig3_not_obstructionFree {k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k < n)
    [NeZero (n + 2 * m - k)] :
    ¬ (fig3 (V := V) false n m (n + 2 * m - k)).ObstructionFreeOn OneShot := by
  intro h
  obtain ⟨α, C, hrun, hos, hp, hloop⟩ :=
    fig3_livelock (V := V) (n := n) (m := m) (r := n + 2 * m - k) default hm (by omega)
      (by omega)
  obtain ⟨j, hj⟩ := h α C _ hrun hos hp
  exact hloop j hj

end Construction

end Podc.SetAgreementSpace
