import Podc.Computability.Distributed.Byzantine.AsyncBroadcast
import Papers.PODC2022.MultipleSpending.Uniform

/-!
# `k`-Consistent Broadcast and the lower bound of Theorem 5.1 (§5)

We use the asynchronous Byzantine broadcast model `Cslib.Byzantine.AsyncBroadcast`
(guards over the inbox, authenticated channels, adaptive corruption, weak fairness) with up to
`|Π|` corruptions, and restrict attention to executions that *comply* with the fault model:
the set of processes ever corrupted belongs to `F`.

* A broadcast instance has a dedicated source `s`; its input is `srcInput s mo` (`mo = some m`
  iff the source broadcasts `m`). Delivery is the (single, persistent) decision `dec`.
* `IsKCB T s k A`: Validity, `k`-Consistency and Integrity of `k`-CB.
* `LocalProgress T s A` (the paper's assumption) and the per-value strengthening
  `LocalProgressAll T s A` (for *every* value the source may broadcast).
* `trivialAlg s`: the source sends its value, everybody delivers the first value received from the
  source. `trivialAlg_isKCB`: it is a `k`-CB with `k = max 1 (max_{F ∈ F, s ∈ F} |Π − F|)`.
* `theorem_5_1_false`: in the uniform model with `n = 3`, `q = 1`, `f = 1` the inconsistency number
  is `3`, but `trivialAlg` implements `2`-CB (with Local Progress, even per value), for every
  source. Theorem 5.1 ("no algorithm implements `k`-CB with `k < k_max`") is false: its proof
  needs the source to be faulty in a faulty set that maximizes the independence number.
-/

namespace Podc.MultipleSpending

open Cslib.Byzantine.AsyncBroadcast Finset

variable {P M V : Type*} [Fintype P] [DecidableEq P]

/-- Inputs of a broadcast instance with source `s`. -/
def srcInput (s : P) (mo : Option V) : P → Option V := fun p => if p = s then mo else none

/-- Executions of a broadcast algorithm with source `s` (Byzantine faults, no a priori bound on
their number: compliance with the fault model is required separately). -/
abbrev BExec (A : Protocol P M (Option V) V) (s : P) (mo : Option V) :=
  Exec A (srcInput s mo) .byzantine (Fintype.card P)

/-- The set of faulty (ever corrupted) processes of an execution. -/
noncomputable def faultySet {A : Protocol P M (Option V) V} {x : P → Option V} {k : FaultKind}
    {t : ℕ} (E : Exec A x k t) : Finset P := by
  classical exact Finset.univ.filter fun p => ¬ E.Correct p

/-- The set `M` of values delivered by correct processes. -/
def delivered {A : Protocol P M (Option V) V} {x : P → Option V} {k : FaultKind} {t : ℕ}
    (E : Exec A x k t) : Set V := {v | ∃ p i, E.Correct p ∧ (E.σ i).dec p = some v}

/-- `k`-Consistent Broadcast (§5) with source `s` in the trust model `T`. A correct process
delivers at most one value by construction of the model (`dec` is set once). -/
structure IsKCB (T : TrustModel P) (s : P) (k : ℕ) (A : Protocol P M (Option V) V) : Prop where
  /-- If the source is correct and broadcasts `m`, every live correct process delivers `m`. -/
  validity : ∀ m (E : BExec A s (some m)), E.Fair → faultySet E ∈ T.F → E.Correct s →
    ∀ p, E.Correct p → T.Live (faultySet E) p → ∃ i, (E.σ i).dec p = some m
  /-- At most `k` values are delivered by correct processes. -/
  consistency : ∀ mo (E : BExec A s mo), faultySet E ∈ T.F → (delivered E).encard ≤ k
  /-- If the source is correct, a correct process delivers only the value it broadcast. -/
  integrity : ∀ mo (E : BExec A s mo), faultySet E ∈ T.F → E.Correct s →
    ∀ p i v, E.Correct p → (E.σ i).dec p = some v → mo = some v

/-- The inconsistency number restricted to faulty sets containing the source `s`:
`λ_s = max {α(G_{F,S}) | F ∈ F, s ∈ F, S ∈ 𝒮}`. The paper's lower-bound argument (proof of
Theorem 5.1) only works for these graphs. -/
noncomputable def srcInconsistencyNumber (T : TrustModel P) (s : P) : ℕ :=
  inconsistencyNumber ⟨T.Q, {F | F ∈ T.F ∧ s ∈ F}⟩

/-- Only the processes of `R` took steps (sent, received or delivered) to reach `σ`. -/
def OnlyBy (σ : State P M V) (R : Finset P) : Prop :=
  (∀ q m, (q, m) ∈ σ.sent → q ∈ R) ∧ (∀ q r m, (q, r, m) ∈ σ.rcv → q ∈ R) ∧
    ∀ q, σ.dec q ≠ none → q ∈ R

/-- **Local Progress** (§5.1): for every `p` and `Q ∈ Q(p)` there is an execution in which only
the source and `Q` take steps, nobody is faulty and `p` delivers a value. -/
def LocalProgress (T : TrustModel P) (s : P) (A : Protocol P M (Option V) V) : Prop :=
  ∀ p, ∀ Q ∈ T.Q p, ∃ m σ, Reachable A (srcInput s (some m)) .byzantine (Fintype.card P) σ ∧
    σ.bad = ∅ ∧ σ.dec p ≠ none ∧ OnlyBy σ (insert s Q)

/-- Per-value Local Progress: as `LocalProgress`, for every value broadcast by the source. -/
def LocalProgressAll (T : TrustModel P) (s : P) (A : Protocol P M (Option V) V) : Prop :=
  ∀ p, ∀ Q ∈ T.Q p, ∀ m, ∃ σ, Reachable A (srcInput s (some m)) .byzantine (Fintype.card P) σ ∧
    σ.bad = ∅ ∧ σ.dec p ≠ none ∧ OnlyBy σ (insert s Q)

theorem LocalProgressAll.localProgress [Nonempty V] {T : TrustModel P} {s : P}
    {A : Protocol P M (Option V) V} (h : LocalProgressAll T s A) : LocalProgress T s A :=
  fun p Q hQ => ⟨Classical.arbitrary V, h p Q hQ _⟩

/-! ### The trivial algorithm -/

/-- The source sends its value and delivers it; every other process delivers the first value
received from the source. -/
def trivialAlg (s : P) : Protocol P V (Option V) V where
  send _ xp _ _ m := xp = some m
  decide _ xp ib _ v := xp = some v ∨ v ∈ ib s

section Trivial

variable {s : P} {mo : Option V}

theorem trivial_sent {σ : State P V V}
    (h : Reachable (trivialAlg s) (srcInput s mo) .byzantine (Fintype.card P) σ) {p : P} {m : V}
    (hm : (p, m) ∈ σ.sent) : mo = some m := by
  have := h.sent_just (J := fun p m _ _ => srcInput s mo p = some m)
    (fun _ _ _ _ _ _ _ _ h => h) (fun _ _ _ _ h => h) hm
  simp only [srcInput] at this
  split_ifs at this; exact this

/-- If the source is not corrupted, every decision is the source's value. -/
theorem trivial_dec {σ : State P V V}
    (h : Reachable (trivialAlg s) (srcInput s mo) .byzantine (Fintype.card P) σ)
    (hs : s ∉ σ.bad) {p : P} {v : V} (hv : σ.dec p = some v) : mo = some v := by
  have := h.dec_just (J := fun p v ib _ => srcInput s mo p = some v ∨ v ∈ ib s)
    (fun _ _ _ _ _ _ hib _ h => h.imp_right fun h' => hib _ h') (fun _ _ _ _ h => h) hv
  rcases this with h1 | h1
  · simp only [srcInput] at h1; split_ifs at h1; exact h1
  · exact trivial_sent h (h.genuine h1 hs)

theorem trivial_integrity (E : BExec (trivialAlg s) s mo) (hs : E.Correct s) {p : P} {i : ℕ}
    {v : V} (hv : (E.σ i).dec p = some v) : mo = some v :=
  trivial_dec (E.reachable i) (hs i) hv

omit [Fintype P] in
/-- Each process delivers at most one value over an execution. -/
theorem dec_unique {A : Protocol P M (Option V) V} {x : P → Option V} {k : FaultKind} {t : ℕ}
    (E : Exec A x k t) {p : P} {i j : ℕ} {v w : V} (hv : (E.σ i).dec p = some v)
    (hw : (E.σ j).dec p = some w) : v = w := by
  have h1 := E.dec_mono (le_max_left i j) hv
  have h2 := E.dec_mono (le_max_right i j) hw
  rw [h1] at h2; exact Option.some_injective _ h2

/-- The number of values delivered by correct processes is at most the number of correct
processes. -/
theorem encard_delivered_le {A : Protocol P M (Option V) V} {x : P → Option V} {k : FaultKind}
    {t : ℕ} (E : Exec A x k t) : (delivered E).encard ≤ Fintype.card P - (faultySet E).card := by
  classical
  rcases (delivered E).eq_empty_or_nonempty with he | ⟨v₀, p₀, -⟩
  · simp [he]
  have : Nonempty P := ⟨p₀⟩
  let f : V → P := fun v => Classical.epsilon fun p => ∃ i, E.Correct p ∧ (E.σ i).dec p = some v
  have hf : ∀ v ∈ delivered E, ∃ i, E.Correct (f v) ∧ (E.σ i).dec (f v) = some v := by
    rintro v ⟨p, i, hp, hv⟩
    exact Classical.epsilon_spec (p := fun p => ∃ i, E.Correct p ∧ (E.σ i).dec p = some v)
      ⟨p, i, hp, hv⟩
  have hcorr : ((faultySet E)ᶜ : Finset P) = Finset.univ.filter fun p => E.Correct p := by
    ext p; simp [faultySet]
  calc (delivered E).encard
      ≤ (↑((faultySet E)ᶜ) : Set P).encard := by
        apply Set.encard_le_encard_of_injOn (f := f)
        · intro v hv
          obtain ⟨i, hc, -⟩ := hf v hv
          rw [hcorr]; simp [hc]
        · intro v hv w hw he
          obtain ⟨i, -, hi⟩ := hf v hv
          obtain ⟨j, -, hj⟩ := hf w hw
          rw [he] at hi
          exact dec_unique E hi hj
    _ = ((Fintype.card P - (faultySet E).card : ℕ) : ℕ∞) := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_compl]

/-- **The trivial algorithm is a `k`-CB** with `k` the largest number of correct processes
when the source is faulty (and at least `1`). -/
theorem trivialAlg_isKCB (T : TrustModel P) (s : P) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : ∀ F ∈ T.F, s ∈ F → Fintype.card P - F.card ≤ K) :
    IsKCB (V := V) T s K (trivialAlg s) where
  validity := by
    intro m E hF _ hs p hp _
    -- the source sends `m`
    obtain ⟨j, hj⟩ := hF.send s m 0 hs fun _ _ => by simp [trivialAlg, srcInput]
    -- `p` receives it
    obtain ⟨j', hj'⟩ := hF.deliver p s m j hp hs hj
    -- `p`'s decision guard holds from then on, so `p` decides, and only `m` can be decided
    obtain ⟨j'', hj''⟩ := hF.decide p m j' hp fun l hl =>
      Or.inr (E.rcv_mono hl hj')
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hj''
    have := trivial_integrity E hs hv
    exact ⟨j'', by rw [hv, ← this]⟩
  consistency := by
    intro mo E hFT
    by_cases hs : E.Correct s
    · calc (delivered E).encard ≤ 1 := by
            rw [Set.encard_le_one_iff]
            rintro v w ⟨p, i, -, hv⟩ ⟨q, j, -, hw⟩
            have h1 := trivial_integrity E hs hv
            have h2 := trivial_integrity E hs hw
            rw [h1] at h2; exact Option.some_injective _ h2
        _ ≤ K := by exact_mod_cast hK1
    · have hsF : s ∈ faultySet E := by classical simp [faultySet, hs]
      exact (encard_delivered_le E).trans (by exact_mod_cast hK _ hFT hsF)
  integrity := fun mo E _ hs _ _ _ _ hv => trivial_integrity E hs hv

/-- The trivial algorithm satisfies per-value Local Progress (hence Local Progress). -/
theorem trivialAlg_localProgressAll (T : TrustModel P) (hself : T.SelfMem) (s : P) :
    LocalProgressAll (V := V) T s (trivialAlg s) := by
  intro p Q hQ m
  have hpQ : p ∈ Q := hself p Q hQ
  let σ1 : State P V V := { (State.init : State P V V) with sent := insert (s, m) ∅ }
  let σ2 : State P V V := { σ1 with rcv := insert (p, s, m) ∅ }
  let σ3 : State P V V := { σ2 with dec := Function.update σ2.dec p (some m) }
  have h1 : Step (trivialAlg s) (srcInput s (some m)) .byzantine (Fintype.card P)
      State.init σ1 :=
    Step.send _ s m (by simp [State.init]) (by simp [trivialAlg, srcInput])
  have h2 : Step (trivialAlg s) (srcInput s (some m)) .byzantine (Fintype.card P) σ1 σ2 :=
    Step.deliver _ p s m (by simp [σ1])
  have h3 : Step (trivialAlg s) (srcInput s (some m)) .byzantine (Fintype.card P) σ2 σ3 :=
    Step.decide _ p m (by simp [σ2, σ1, State.init]) (by simp [σ2, σ1, State.init])
      (Or.inr (by simp [σ2, State.inbox]))
  refine ⟨σ3, ((Relation.ReflTransGen.refl.tail h1).tail h2).tail h3,
    by simp [σ3, σ2, σ1, State.init], by simp [σ3], ?_, ?_, ?_⟩
  · intro q m' hq
    simp only [σ3, σ2, σ1, Set.mem_insert_iff, Prod.mk.injEq, Set.mem_empty_iff_false,
      or_false] at hq
    rw [hq.1]; exact Finset.mem_insert_self _ _
  · intro q r m' hq
    simp only [σ3, σ2, Set.mem_insert_iff, Prod.mk.injEq, Set.mem_empty_iff_false,
      or_false] at hq
    rw [hq.1]; exact Finset.mem_insert_of_mem hpQ
  · intro q hq
    by_cases hqp : q = p
    · rw [hqp]; exact Finset.mem_insert_of_mem hpQ
    · simp [σ3, σ2, σ1, State.init, Function.update_of_ne hqp] at hq

end Trivial

/-- **Theorem 5.1 is false.** Three processes, every process's only quorum is itself (the uniform
model with `q = 1`), at most one process may fail. The inconsistency number is `3`, yet for every
choice of source the trivial algorithm implements `2`-Consistent Broadcast and satisfies Local
Progress (even for every value). -/
theorem theorem_5_1_false :
    let T := uniform (P := Fin 3) 1 1
    T.SelfMem ∧ T.DownClosed ∧ inconsistencyNumber T = 3 ∧
      ∀ s : Fin 3, IsKCB (V := ℕ) T s 2 (trivialAlg s) ∧
        LocalProgressAll (V := ℕ) T s (trivialAlg s) := by
  refine ⟨uniform_selfMem 1 1, uniform_downClosed 1 1, ?_, fun s => ⟨?_, ?_⟩⟩
  · rw [theorem_3_6_needs_q_gt_f (by norm_num) le_rfl (by simp)]; simp
  · apply trivialAlg_isKCB _ s (by norm_num)
    intro F hF hsF
    have : 1 ≤ F.card := Finset.card_pos.mpr ⟨s, hsF⟩
    simp only [Fintype.card_fin]
    omega
  · exact trivialAlg_localProgressAll _ (uniform_selfMem 1 1) s

end Podc.MultipleSpending
