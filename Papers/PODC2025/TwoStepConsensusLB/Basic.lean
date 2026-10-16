import Papers.PODC2025.TwoStepConsensusLB.Merge

/-!
# Basic facts used by the lower bounds

* `decide_init_ne`: a consensus protocol never decides in its initial state (needs two values);
  hence a process that decides by `2Δ` in an `E`-faulty synchronous run is not in `E`
  (`not_mem_of_decidesAt`).
* `syncRun_st_eq`: the states of an `E`-faulty synchronous run do not depend on the inputs of the
  processes of `E` (Lemma 2 of the paper), and its consequence `syncRun_decides_eq`: if all
  processes outside `E` propose `w`, only `w` can be decided.
* `splitRun`: the classical partition argument (Dwork–Lynch–Stockmeyer): with `n ≤ 2f` (and
  `n ≥ 2`) neither the task nor the object can be implemented (`two_f_lt_task`,
  `two_f_lt_object`).
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus

open _root_.Cslib.CrashPartialSync

open Finset

variable {P V M S : Type*} [Fintype P] [DecidableEq P]

theorem decide_init_ne {A : Protocol P V M S} {f : ℕ} (hA : SolvesTask A f) {a b : V}
    (hab : a ≠ b) (p : P) (v : V) : A.decide p (A.init p) ≠ some v := by
  intro h
  obtain ⟨w, hw⟩ : ∃ w, w ≠ v := by
    by_cases hv : a = v
    · exact ⟨b, fun h' => hab (hv.trans h'.symm)⟩
    · exact ⟨a, hv⟩
  set R : Run P V M := syncRun ∅ (taskInv fun _ => w) (fun _ _ l => l)
  have hR : R.Valid f := syncRun_valid (by simp) _ IsOrder.id
  obtain ⟨q, hq⟩ := hA.validity R _ hR rfl p 0 v (by simpa [Run.DecidesAt, R] using h)
  exact hw hq

/-- A process that crashed at time `0` never decides. -/
theorem not_mem_of_decidesAt {A : Protocol P V M S} {f : ℕ} (hA : SolvesTask A f) {a b : V}
    (hab : a ≠ b) {E : Finset P} {inv : P → ℕ → Option V}
    {o : P → ℕ → List (P × M) → List (P × M)} {d : P} {τ : ℕ} {v : V}
    (h : (syncRun E inv o).DecidesAt A d τ v) : d ∉ E := by
  intro hd
  unfold Run.DecidesAt at h
  rw [Run.st_of_crash_zero _ _ (syncRun_crash_of_mem hd)] at h
  exact decide_init_ne hA hab d v h

/-- **Lemma 2.** The states of an `E`-faulty synchronous run do not depend on the invocations of
the processes of `E`. -/
theorem syncRun_st_eq (A : Protocol P V M S) {E : Finset P} {i i' : P → ℕ → Option V}
    (hi : ∀ x ∉ E, i x = i' x) (o : P → ℕ → List (P × M) → List (P × M)) (τ : ℕ) (x : P) :
    (syncRun E i o).st A τ x = (syncRun E i' o).st A τ x := by
  set R : Run P V M := syncRun E i o
  set R' : Run P V M := syncRun E i' o
  refine R.st_eq_of_inbox_eq A (ref := fun _ => R') (X := Set.univ) (T := τ) ?_ ?_ ?_ τ le_rfl x
    trivial
  · intro _ _ _ _; rfl
  · intro y _ t _ hy
    have : y ∉ E := by
      intro h; simp [R, Run.alive, syncRun, h] at hy
    simp [R, R', syncRun, hi y this]
  · intro t _ IH y _ _
    refine R.inbox_eq_of_dlv_eq A rfl ?_
    intro q τ' hτ'
    have hal : R'.alive q τ' = R.alive q τ' := rfl
    have hdl : R'.dl q τ' y = R.dl q τ' y := rfl
    unfold Run.dlv
    rw [hdl]
    split_ifs
    · by_cases ha : R.alive q τ'
      · rw [R.out_of_alive A ha, R'.out_of_alive A (hal ▸ ha), IH q trivial _ (by omega)]
      · rw [R.out_of_not_alive A (by simpa using ha),
          R'.out_of_not_alive A (by rw [hal]; simpa using ha)]
    · rfl

/-- If all processes outside `E` propose `w`, a task protocol can only decide `w` in an
`E`-faulty synchronous run. -/
theorem syncRun_decides_eq {A : Protocol P V M S} {f : ℕ} (hA : SolvesTask A f) {E : Finset P}
    (hE : E.card ≤ f) {I : P → V} {w : V} (hI : ∀ x ∉ E, I x = w)
    {o : P → ℕ → List (P × M) → List (P × M)} (ho : IsOrder o) {d : P} {τ : ℕ} {v : V}
    (h : (syncRun E (taskInv I) o).DecidesAt A d τ v) : v = w := by
  have h' : (syncRun E (taskInv fun _ => w) o).DecidesAt A d τ v := by
    unfold Run.DecidesAt at h ⊢
    rwa [← syncRun_st_eq A (i := taskInv I) (fun x hx => by funext t; simp [taskInv, hI x hx])]
  obtain ⟨q, hq⟩ := hA.validity _ _ (syncRun_valid hE _ ho) rfl d τ v h'
  exact hq.symm

/-- If a task protocol decides by time `2Δ` in an `E`-faulty synchronous run, the decision is the
input of a process. -/
theorem syncRun_decides_mem {A : Protocol P V M S} {f : ℕ} (hA : SolvesTask A f) {E : Finset P}
    (hE : E.card ≤ f) {I : P → V} {o : P → ℕ → List (P × M) → List (P × M)} (ho : IsOrder o)
    {d : P} {τ : ℕ} {v : V} (h : (syncRun E (taskInv I) o).DecidesAt A d τ v) : ∃ q, I q = v :=
  hA.validity _ _ (syncRun_valid hE _ ho) rfl d τ v h

/-! ### The classical bound `n ≥ 2f + 1` -/

/-- The run of the partition argument: no crashes, GST `T`, messages between `G` and `Gᶜ`
delivered only after `T`. -/
def splitRun (G : Finset P) (inv : P → ℕ → Option V) (T : ℕ) : Run P V M where
  crash _ := none
  gst := T
  inv := inv
  dl q τ x := if (q ∈ G ↔ x ∈ G) then τ + 1 else max τ T + 1
  ord _ _ l := l

theorem splitRun_compl (G : Finset P) (inv : P → ℕ → Option V) (T : ℕ) :
    splitRun (M := M) Gᶜ inv T = splitRun G inv T := by
  simp only [splitRun, mem_compl, not_iff_not]

theorem splitRun_valid (f : ℕ) (G : Finset P) (inv : P → ℕ → Option V) (T : ℕ) :
    (splitRun (M := M) G inv T).Valid f where
  card_faulty := by simp [Run.faulty, splitRun]
  ord_perm := IsOrder.id
  dl_ge q τ x _ _ := by simp only [splitRun]; split_ifs <;> omega
  dl_le q τ x _ _ := by simp only [splitRun]; split_ifs <;> omega

/-- In `splitRun G inv T`, the processes of `G` behave as in the `Gᶜ`-faulty synchronous run
until time `T + 1`. -/
theorem splitRun_st (A : Protocol P V M S) (G : Finset P) {inv i : P → ℕ → Option V} (T : ℕ)
    (hi : ∀ x ∈ G, inv x = i x) :
    ∀ τ ≤ T + 1, ∀ x ∈ G, (splitRun G inv T).st A τ x =
      (syncRun (M := M) Gᶜ i (fun _ _ l => l)).st A τ x := by
  set R : Run P V M := splitRun G inv T
  set σ : Run P V M := syncRun Gᶜ i (fun _ _ l => l)
  intro τ hτ x hx
  refine R.st_eq_of_inbox_eq A (ref := fun _ => σ) (X := (G : Set P)) (T := T + 1) ?_ ?_ ?_ τ hτ
    x hx
  · intro y hy t _
    have hy : y ∈ G := hy
    rw [Run.alive_of_crash_none _ rfl, Run.alive_of_crash_none _ (by simp [σ, syncRun, hy])]
  · intro y hy t _ _
    have hy : y ∈ G := hy
    simp [R, σ, splitRun, syncRun, hi y hy]
  · intro t ht IH y hy _
    have hy : y ∈ G := hy
    refine R.inbox_eq_of_dlv_eq A rfl ?_
    intro q τ' hτ'
    by_cases hq : q ∈ G
    · have hdl : R.dl q τ' y = σ.dl q τ' y := by simp [R, σ, splitRun, syncRun, hq, hy]
      unfold Run.dlv
      rw [hdl]
      split_ifs
      · rw [R.out_of_alive A (Run.alive_of_crash_none R rfl _),
          σ.out_of_alive A (Run.alive_of_crash_none σ (by simp [σ, syncRun, hq]) _),
          IH q hq _ (by omega)]
      · rfl
    · rw [R.dlv_eq_nil_of_ne A (by simp [R, splitRun, hq, hy]; omega), Run.dlv,
        σ.out_of_not_alive A (by simp [σ, Run.alive, syncRun, hq])]
      simp

/-- Two nonempty complementary sets of size at most `f`, when `2 ≤ n ≤ 2f`. -/
theorem exists_split {f : ℕ} (hn : 2 ≤ Fintype.card P) (hnf : Fintype.card P ≤ 2 * f) :
    ∃ G : Finset P, G.Nonempty ∧ Gᶜ.Nonempty ∧ G.card ≤ f ∧ Gᶜ.card ≤ f := by
  obtain ⟨G, -, hG⟩ := Finset.exists_subset_card_eq (s := (univ : Finset P))
    (n := min f (Fintype.card P - 1)) (by simp)
  have hc : Gᶜ.card = Fintype.card P - G.card := card_compl G
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · rw [← card_pos, hG]
    have : 1 ≤ f := by omega
    omega
  · rw [← card_pos, hc, hG]; omega
  · rw [hG]; omega
  · rw [hc, hG]; omega

/-- **`n ≥ 2f + 1` for the task** ([DLS88], used in Theorem 1 "only if"): an `f`-resilient
consensus task protocol for `n ≥ 2` processes and at least two values needs `n ≥ 2f + 1`. -/
theorem two_f_lt_task {A : Protocol P V M S} {f : ℕ} (hA : SolvesTask A f) {a b : V}
    (hab : a ≠ b) (hn : 2 ≤ Fintype.card P) : 2 * f + 1 ≤ Fintype.card P := by
  by_contra hlt
  obtain ⟨G, ⟨x, hx⟩, ⟨y, hy⟩, hG, hGc⟩ := exists_split (f := f) hn (by omega)
  -- `G` alone (with `Gᶜ` crashed) decides `a`; `Gᶜ` alone decides `b`.
  set α : Run P V M := syncRun Gᶜ (taskInv fun _ => a) (fun _ _ l => l)
  set β : Run P V M := syncRun Gᶜᶜ (taskInv fun _ => b) (fun _ _ l => l)
  obtain ⟨T₁, u, hu⟩ := hA.termination α _ (syncRun_valid hGc _ IsOrder.id) rfl x
    (syncRun_crash_of_not_mem (by simpa using hx))
  obtain ⟨T₂, u', hu'⟩ := hA.termination β _ (syncRun_valid (by simpa using hG) _ IsOrder.id) rfl
    y (syncRun_crash_of_not_mem (by simpa using hy))
  obtain ⟨q, rfl⟩ := hA.validity α _ (syncRun_valid hGc _ IsOrder.id) rfl x T₁ u hu
  obtain ⟨q', rfl⟩ := hA.validity β _ (syncRun_valid (by simpa using hG) _ IsOrder.id) rfl y T₂
    u' hu'
  -- the run `γ` in which the two halves do not hear from each other until `T₁ + T₂`
  set I : P → V := fun z => if z ∈ G then a else b
  set T := T₁ + T₂
  set γ : Run P V M := splitRun G (taskInv I) T
  have h1 : γ.DecidesAt A x T₁ a := by
    unfold Run.DecidesAt at hu ⊢
    rw [splitRun_st A G (i := taskInv fun _ => a) T
      (fun z hz => by funext t; simp [taskInv, I, hz]) T₁ (by omega) x hx]
    exact hu
  have h2 : γ.DecidesAt A y T₂ b := by
    unfold Run.DecidesAt at hu' ⊢
    rw [show γ = splitRun Gᶜ (taskInv I) T from (splitRun_compl G _ T).symm,
      splitRun_st A Gᶜ (i := taskInv fun _ => b) T
      (fun z hz => by funext t; simp_all [taskInv, I]) T₂ (by omega) y hy]
    exact hu'
  exact hab (hA.agreement γ _ (splitRun_valid f G _ T) rfl x y T₁ T₂ a b h1 h2)

/-- **`n ≥ 2f + 1` for the object** ([DLS88], used in Theorem 2 "only if"). -/
theorem two_f_lt_object {A : Protocol P V M S} {f : ℕ} (hA : SolvesObject A f) {a b : V}
    (hab : a ≠ b) (hn : 2 ≤ Fintype.card P) : 2 * f + 1 ≤ Fintype.card P := by
  by_contra hlt
  obtain ⟨G, ⟨x, hx⟩, ⟨y, hy⟩, hG, hGc⟩ := exists_split (f := f) hn (by omega)
  have hwf : ∀ (E : Finset P) (v : V), (syncRun (M := M) E (allInv E v) (fun _ _ l => l)).WellFormed :=
    fun E v p τ τ' h h' => by
      simp only [syncRun, allInv] at h h'
      split_ifs at h h' <;> simp_all
  set α : Run P V M := syncRun Gᶜ (allInv Gᶜ a) (fun _ _ l => l)
  set β : Run P V M := syncRun Gᶜᶜ (allInv Gᶜᶜ b) (fun _ _ l => l)
  have hαv : α.Valid f := syncRun_valid hGc _ IsOrder.id
  have hβv : β.Valid f := syncRun_valid (by simpa using hG) _ IsOrder.id
  obtain ⟨T₁, u, hu⟩ := hA.waitFree α hαv (hwf _ _) x 0 a
    (syncRun_crash_of_not_mem (by simpa using hx)) (by simp [α, syncRun, allInv, hx])
  obtain ⟨T₂, u', hu'⟩ := hA.waitFree β hβv (hwf _ _) y 0 b
    (syncRun_crash_of_not_mem (by simpa using hy : y ∉ Gᶜᶜ)) (by simp [β, syncRun, allInv, Finset.mem_compl.mp hy])
  obtain ⟨q, t, -, hq⟩ := hA.validity α hαv (hwf _ _) x T₁ u hu
  obtain ⟨q', t', -, hq'⟩ := hA.validity β hβv (hwf _ _) y T₂ u' hu'
  simp only [α, β, syncRun, allInv] at hq hq'
  split_ifs at hq hq' with h₁ h₂
  simp only [Option.some.injEq] at hq hq'
  subst hq hq'
  set inv : P → ℕ → Option V := fun z τ => if τ = 0 then some (if z ∈ G then a else b) else none
  set T := T₁ + T₂
  set γ : Run P V M := splitRun G inv T
  have hγw : γ.WellFormed := fun p τ τ' h h' => by
    simp only [γ, splitRun, inv] at h h'; split_ifs at h h' <;> simp_all
  have h1 : γ.RespondsAt A x T₁ a := by
    obtain ⟨⟨t₀, ht₀, hinv⟩, hdec⟩ := hu
    have ht0 : t₀ = 0 := by
      by_contra h; simp [α, syncRun, allInv, h] at hinv
    subst ht0
    refine ⟨⟨0, ht₀, by simp [γ, splitRun, inv]⟩, ?_⟩
    unfold Run.DecidesAt at hdec ⊢
    rw [splitRun_st A G (i := allInv Gᶜ a) T
      (fun z hz => by funext t; simp [allInv, inv, hz]) T₁ (by omega) x hx]
    exact hdec
  have h2 : γ.RespondsAt A y T₂ b := by
    obtain ⟨⟨t₀, ht₀, hinv⟩, hdec⟩ := hu'
    have ht0 : t₀ = 0 := by
      by_contra h; simp [β, syncRun, allInv, h] at hinv
    subst ht0
    refine ⟨⟨0, ht₀, by simp [γ, splitRun, inv]⟩, ?_⟩
    unfold Run.DecidesAt at hdec ⊢
    rw [show γ = splitRun Gᶜ inv T from (splitRun_compl G _ T).symm,
      splitRun_st A Gᶜ (i := allInv Gᶜᶜ b) T
      (fun z hz => by funext t; simp_all [allInv, inv]) T₂ (by omega) y hy]
    exact hdec
  exact hab (hA.agreement γ (splitRun_valid f G _ T) hγw x y T₁ T₂ a b h1 h2)

end TwoStepConsensus
