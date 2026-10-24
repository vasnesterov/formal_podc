import Papers.PODC2017.ZigzagCausality.Coordination

/-!
# Theorem 3 fails for full-information protocols that do not flood

Theorem 3 is stated for an arbitrary protocol; its proof uses Lemma 3 (full information) and
Lemma 4, whose proof uses flooding. Here is a full-information protocol (every message carries the
sender's whole local state) that implements `Late⟨a --0--> b⟩` but for which the conclusion of
Theorem 3 fails: `B` learns that `C` received `μ_go` from the *absence* of a message.

Processes `D = 0`, `C = 1`, `A = 2`, `B = 3`; channels `D → C`, `D → B`, `C → A`, `C → B` with
exact delays `1, 2, 1, 1` (`L = U`). External messages `e_D = 0`, `μ_go = 1`, `e' = 2`.
* `D`, when activated, sends to `C` and `B`;
* `C`, when activated, sends to `A` if `μ_go` is in its current batch ("go"), and to `B` otherwise
  ("no go yet");
* `B` performs `b` when it receives a message from `D` and, in the same batch, none from `C`.

If `D` sends at time `t`, `C` is activated at `t + 1` and its reply (if any) reaches `B` exactly
together with `D`'s direct message at `t + 2`. So `b` at `t + 2` implies that `C` received `μ_go`
at `t + 1`, hence `a` happens at `t + 2`: the protocol implements `Late⟨a --0--> b⟩`
(`implementsLate`). In the run `r₁` (`D` gets `e_D` at time 1, `C` gets `μ_go` at time 2) `B`
performs `b` at `σ = (B, r_B(3))`, and `C` sends "go" at `σ_C = (C, r_C(2))`. But in the run `r₂`
where `C` gets `e'` together with `μ_go`, `B` has the same local state while `σ_C` does not appear,
so `K_σ(σ_C·A --0--> σ)` fails (`theorem_3_false_for_FIP`). (Also, `σ_C` is not in the past of
`σ`, so Lemma 4 fails as well.)
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

namespace CounterexampleFIP

open Sys

/-- Exact delays. -/
def lu : Fin 4 → Fin 4 → ℕ
  | 0, 3 => 2
  | _, _ => 1

/-- Channels `0 → 1`, `0 → 3`, `1 → 2`, `1 → 3`. -/
def ch : Fin 4 → Fin 4 → Bool
  | 0, 1 => true
  | 0, 3 => true
  | 1, 2 => true
  | 1, 3 => true
  | _, _ => false

/-- The network (`L = U`). -/
def net : Net (Fin 4) where
  Chan i j := ch i j = true
  L := lu
  U := lu
  one_le_L i j _ := by fin_cases i <;> fin_cases j <;> decide
  L_le_U _ _ _ := le_rfl

abbrev LS := LState (Fin 4) Unit ℕ (Fin 3)
abbrev BN := BNode (Fin 4) Unit ℕ (Fin 3)
abbrev GN := GNode (Fin 4) Unit ℕ (Fin 3)

instance : Countable LS := by
  refine Function.Injective.countable
    (f := fun ℓ : LS => (ℓ.init, ℓ.hist.map fun b => (b.msgs, b.ext))) ?_
  rintro ⟨a, h⟩ ⟨a', h'⟩ he
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, he⟩ := he
  have ha : a = a' := Subsingleton.elim _ _
  subst ha
  have : h = h' := by
    refine List.map_injective_iff.2 ?_ he
    rintro ⟨m, e⟩ ⟨m', e'⟩ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl
  rw [this]

/-- An injective encoding of local states into message contents. -/
noncomputable def enc : LS → ℕ := Classical.choose (Countable.exists_injective_nat LS)

theorem enc_injective : Function.Injective enc :=
  Classical.choose_spec (Countable.exists_injective_nat LS)

/-- The external messages of the last batch. -/
def lastExt (ℓ : LS) : Finset (Fin 3) := (ℓ.hist.getLast?.map Batch.ext).getD ∅

/-- Who sends to whom. -/
def sendsTo (i : Fin 4) (ℓ : LS) (j : Fin 4) : Prop :=
  (i = 0 ∧ (j = 1 ∨ j = 3)) ∨ (i = 1 ∧ j = 2 ∧ 1 ∈ lastExt ℓ) ∨ (i = 1 ∧ j = 3 ∧ 1 ∉ lastExt ℓ)

open Classical in
/-- The full-information (non-flooding) protocol. -/
noncomputable def γ : Sys (Fin 4) Unit ℕ (Fin 3) where
  net := net
  send i ℓ j := if sendsTo i ℓ j then some (enc ℓ) else none
  G0 := Set.univ

theorem isFIP : γ.IsFIP := by
  intro i j j' ℓ ℓ' m h h'
  simp only [γ] at h h'
  split_ifs at h h'
  cases h
  exact enc_injective (Option.some.inj h').symm

theorem send_eq_some {i j : Fin 4} {ℓ : LS} {m : ℕ} : γ.send i ℓ j = some m ↔ sendsTo i ℓ j ∧ m = enc ℓ := by
  simp only [γ]
  split_ifs with h <;> simp [h, eq_comm]

/-- `B` performs `b`: its last batch contains a message from `D` and none from `C`. -/
def doB (ℓ : LS) : Prop :=
  ∃ b, ℓ.hist.getLast? = some b ∧ (∃ m, ((0 : Fin 4), m) ∈ b.msgs) ∧ ∀ m, ((1 : Fin 4), m) ∉ b.msgs

/-- `σ_C` is a node at which `C` receives `μ_go` (and sends "go" to `A`). -/
def GoNode (r : Sched (Fin 4) Unit (Fin 3)) (σ : BN) : Prop :=
  γ.appears r σ ∧ σ.1 = 1 ∧ 1 ∈ lastExt σ.2

/-- The protocol implements `Late⟨a --x--> b⟩`: whenever `B` performs `b` at `σ`, some go-node
`σ_C` exists and `a` (at `σ_C·A`) happened at least `x` before. -/
def ImplementsLate (x : ℤ) : Prop :=
  ∀ r, γ.Valid r → ∀ σ : BN, γ.appears r σ → σ.1 = 3 → doB σ.2 →
    ∃ σC, GoNode r σC ∧ γ.Prec r ⟨σC, [2]⟩ x (GNode.ofB σ)

theorem netL (i j : Fin 4) : γ.net.L i j = lu i j := rfl
theorem netU (i j : Fin 4) : γ.net.U i j = lu i j := rfl

/-- A node that is activated and whose protocol sends to `j` along a channel. -/
theorem recv_exists {r : Sched (Fin 4) Unit (Fin 3)} (hr : γ.Valid r) {σ : BN}
    (ha : γ.appears r σ) (h0 : 0 < γ.timer r σ) {j : Fin 4} (hc : ch σ.1 j = true)
    (hs : sendsTo σ.1 σ.2 j) : ∃ σ', γ.recv r σ j = some σ' ∧ σ'.1 = j ∧ γ.appears r σ' ∧
      γ.timer r σ' = γ.timer r σ + lu σ.1 j := by
  have : (γ.recv r σ j).isSome := by
    rw [recv_isSome_iff]
    refine ⟨γ.active_timer r ha h0, hc, ?_⟩
    rw [γ.st_timer r ha]
    simp [γ, hs]
  obtain ⟨σ', h⟩ := Option.isSome_iff_exists.1 this
  have sp := recv_spec hr h
  rw [netL, netU] at sp
  exact ⟨σ', h, sp.1, sp.2.1, by omega⟩

/-- The protocol implements `Late⟨a --0--> b⟩`. -/
theorem implementsLate : ImplementsLate 0 := by
  intro r hr σ ha hB hb
  obtain ⟨b, hlast, ⟨m, hm⟩, hnC⟩ := hb
  obtain ⟨σD, hD1, hrecv, -⟩ := exists_recv_of_mem_last hr ha hlast hm
  have sD := recv_spec hr hrecv
  rw [netL, netU, hD1, hB] at sD
  obtain ⟨haD, h0D⟩ := recv_appears_left hrecv
  obtain ⟨γC, hC, pC, aC, tC⟩ := recv_exists hr haD h0D (j := 1) (by rw [hD1]; rfl)
    (by simp [sendsTo, hD1])
  rw [hD1] at tC
  have h0C : 0 < γ.timer r γC := by rw [tC]; omega
  by_cases hgo : 1 ∈ lastExt γC.2
  · obtain ⟨α, hA, pA, aA, tA⟩ := recv_exists hr aC h0C (j := 2) (by rw [pC]; rfl)
      (by simp [sendsTo, pC, hgo])
    rw [pC] at tA
    refine ⟨γC, ⟨aC, pC, hgo⟩, α, σ, by simp [basic, hA, aA], γ.basic_ofB r ha, ?_⟩
    simp only [lu] at tA tC sD
    omega
  · obtain ⟨β, hβ, pβ, aβ, tβ⟩ := recv_exists hr aC h0C (j := 3) (by rw [pC]; rfl)
      (by simp [sendsTo, pC, hgo])
    rw [pC] at tβ
    have hβσ : β = σ := γ.eq_of_timer_eq r (by rw [pβ, hB]) aβ ha (by simp only [lu] at tβ tC sD; omega)
    subst hβσ
    obtain ⟨m', -, b', hb', hm'⟩ := recv_mem_last hr hβ
    rw [hlast] at hb'; cases hb'
    rw [pC] at hm'
    exact (hnC m' hm').elim

/-! ### Two concrete runs -/

/-- `D` receives `e_D` at time 1, `C` receives the external messages `X` (containing `μ_go`) at
time 2, every message takes exactly its delay. -/
def sched (X : Finset (Fin 3)) : Sched (Fin 4) Unit (Fin 3) where
  g _ := ()
  dlv i s j := s + lu i j
  ext t p := if t = 1 ∧ p = 0 then {0} else if t = 2 ∧ p = 1 then X else ∅

variable {X : Finset (Fin 3)}

theorem valid_sched (hX0 : 0 ∉ X) : γ.Valid (sched X) where
  init := Set.mem_univ _
  bounds _ _ _ _ := ⟨le_rfl, le_rfl⟩
  ext_unique e t j t' j' h h' := by
    simp only [sched] at h h'
    split_ifs at h h' <;> simp_all

/-- The local state of `D` after receiving `e_D`. -/
def dS : LS := ⟨(), [⟨∅, {0}⟩]⟩

theorem ch_eq {i j : Fin 4} (h : γ.net.Chan i j) : ch i j = true := h

theorem batch_D_msgs (t : ℕ) : (γ.batch (sched X) t 0).msgs = ∅ := by
  ext ⟨i, m⟩
  simp only [mem_batch_msgs, Finset.notMem_empty, iff_false, not_exists, not_and]
  intro s _ _ hc
  have := ch_eq hc
  revert this; fin_cases i <;> simp [ch]

theorem active_D (t : ℕ) : γ.Active (sched X) 0 t ↔ t = 1 := by
  rcases t with _ | t
  · simp [Active, ActiveH]
  · rw [active_succ_iff, batch_D_msgs, batch_ext]
    simp only [sched, true_and]
    by_cases ht : t = 0
    · subst ht; simp
    · simp [ht, show ¬ (t + 1 = 1) by omega]

theorem st_D_one : γ.st (sched X) 1 0 = dS := by
  have ha : γ.Active (sched X) 0 (0 + 1) := (active_D _).2 rfl
  rw [γ.st_succ_of_active _ ha]
  have hb : γ.batch (sched X) 0 0 = ⟨∅, {0}⟩ := by
    have e : γ.batch (sched X) 0 0 =
      ⟨(γ.batch (sched X) 0 0).msgs, (γ.batch (sched X) 0 0).ext⟩ := rfl
    rw [e, batch_D_msgs, batch_ext]
    simp [sched]
  rw [hb]
  simp [dS, st_zero, sched]

theorem mem_C_msgs {t : ℕ} {i : Fin 4} {m : ℕ} :
    (i, m) ∈ (γ.batch (sched X) t 1).msgs ↔ i = 0 ∧ t = 1 ∧ m = enc dS := by
  rw [mem_batch_msgs]
  constructor
  · rintro ⟨s, hs, ha, hc, hd, hm⟩
    have hc := ch_eq hc
    have hi : i = 0 := by revert hc; fin_cases i <;> simp [ch]
    subst hi
    rw [active_D] at ha
    subst ha
    rw [send_eq_some] at hm
    simp only [sched, lu] at hd
    refine ⟨rfl, by omega, ?_⟩
    rw [hm.2, st_D_one]
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨1, by omega, (active_D _).2 rfl, rfl, rfl, ?_⟩
    rw [send_eq_some, st_D_one]
    simp [sendsTo]

theorem C_msgs_empty {t : ℕ} (ht : t ≠ 1) : (γ.batch (sched X) t 1).msgs = ∅ := by
  ext ⟨i, m⟩
  simp only [mem_C_msgs, Finset.notMem_empty, iff_false]
  omega

theorem active_C (hX1 : 1 ∈ X) (t : ℕ) : γ.Active (sched X) 1 t ↔ t = 2 := by
  rcases t with _ | t
  · simp [Active, ActiveH]
  · rw [active_succ_iff, batch_ext]
    by_cases ht : t = 1
    · subst ht
      simp only [sched, show ¬ ((1 : ℕ) + 1 = 1) by omega, false_and, if_false, and_self,
        if_true, iff_true]
      rintro ⟨-, he⟩
      rw [he] at hX1; simp at hX1
    · rw [C_msgs_empty ht]
      simp only [sched, show ¬ (t + 1 = 1 ∧ (1 : Fin 4) = 0) by simp,
        show ¬ (t + 1 = 2 ∧ (1 : Fin 4) = 1) by omega, if_false]
      rw [if_neg (by omega)]
      simp only [and_self, not_true_eq_false, false_iff]
      omega

/-- The internal part of `C`'s first batch (and of `B`'s). -/
noncomputable def cM : Finset (Fin 4 × ℕ) := {((0 : Fin 4), enc dS)}

theorem st_C_one (hX1 : 1 ∈ X) : γ.st (sched X) 1 1 = ⟨(), []⟩ := by
  rw [γ.st_succ_of_not_active _ (by rw [active_C hX1]; omega), st_zero]

theorem st_C_two (hX1 : 1 ∈ X) : γ.st (sched X) 2 1 = ⟨(), [⟨cM, X⟩]⟩ := by
  have ha : γ.Active (sched X) 1 (1 + 1) := (active_C hX1 _).2 rfl
  rw [γ.st_succ_of_active _ ha, st_C_one hX1]
  have hb : γ.batch (sched X) 1 1 = ⟨cM, X⟩ := by
    refine Batch.ext' ?_ ?_
    · ext ⟨i, m⟩
      simp only [mem_C_msgs, cM, Finset.mem_singleton, Prod.mk.injEq]
      tauto
    · rw [batch_ext]; simp [sched]
  rw [hb]; rfl

theorem mem_B_msgs (hX1 : 1 ∈ X) {t : ℕ} {i : Fin 4} {m : ℕ} :
    (i, m) ∈ (γ.batch (sched X) t 3).msgs ↔ i = 0 ∧ t = 2 ∧ m = enc dS := by
  rw [mem_batch_msgs]
  constructor
  · rintro ⟨s, hs, ha, hc, hd, hm⟩
    have hc := ch_eq hc
    rw [send_eq_some] at hm
    have hi : i = 0 ∨ i = 1 := by revert hc; fin_cases i <;> simp [ch]
    rcases hi with rfl | rfl
    · rw [active_D] at ha
      subst ha
      simp only [sched, lu] at hd
      refine ⟨rfl, by omega, ?_⟩
      rw [hm.2, st_D_one]
    · rw [active_C hX1] at ha
      subst ha
      exfalso
      have := hm.1
      simp only [sendsTo, st_C_two hX1, lastExt] at this
      simp [hX1] at this
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨1, by omega, (active_D _).2 rfl, rfl, rfl, ?_⟩
    rw [send_eq_some, st_D_one]
    simp [sendsTo]

theorem active_B (hX1 : 1 ∈ X) (t : ℕ) : γ.Active (sched X) 3 t ↔ t = 3 := by
  rcases t with _ | t
  · simp [Active, ActiveH]
  · rw [active_succ_iff, batch_ext]
    have he : (sched X).ext (t + 1) 3 = ∅ := by simp [sched]
    rw [he]
    by_cases ht : t = 2
    · subst ht
      simp only [and_true, iff_true]
      intro h
      have : ((0 : Fin 4), enc dS) ∈ (γ.batch (sched X) 2 3).msgs := (mem_B_msgs hX1).2 ⟨rfl, rfl, rfl⟩
      rw [h] at this; simp at this
    · have : (γ.batch (sched X) t 3).msgs = ∅ := by
        ext ⟨i, m⟩
        simp only [mem_B_msgs hX1, Finset.notMem_empty, iff_false]
        omega
      simp only [this, and_self, not_true_eq_false, false_iff]
      omega

/-- `B`'s local state at time 3 does not depend on `X`. -/
theorem st_B_three (hX1 : 1 ∈ X) : γ.st (sched X) 3 3 = ⟨(), [⟨cM, ∅⟩]⟩ := by
  have h1 : γ.st (sched X) 1 3 = ⟨(), []⟩ := by
    rw [γ.st_succ_of_not_active _ (by rw [active_B hX1]; omega), st_zero]
  have h2 : γ.st (sched X) 2 3 = ⟨(), []⟩ := by
    rw [γ.st_succ_of_not_active _ (by rw [active_B hX1]; omega), h1]
  have ha : γ.Active (sched X) 3 (2 + 1) := (active_B hX1 _).2 rfl
  rw [γ.st_succ_of_active _ ha, h2]
  have hb : γ.batch (sched X) 2 3 = ⟨cM, ∅⟩ := by
    refine Batch.ext' ?_ ?_
    · ext ⟨i, m⟩
      simp only [mem_B_msgs hX1, cM, Finset.mem_singleton, Prod.mk.injEq]
      tauto
    · rw [batch_ext]; simp [sched]
  rw [hb]; rfl

/-! ### The counterexample -/

/-- The coordination task: `A = 2`, `B = 3`, `C = 1`, `μ_go = 1`, and `B`'s rule `doB`. -/
def T : CoordTask (Fin 4) Unit ℕ (Fin 3) := ⟨2, 3, 1, 1, doB⟩

theorem goNode_iff {r : Sched (Fin 4) Unit (Fin 3)} {σ : BN} : γ.GoNode r T σ ↔ GoNode r σ := by
  simp only [Sys.GoNode, GoNode, T, lastExt]
  constructor
  · rintro ⟨h1, h2, b, hb, hg⟩; exact ⟨h1, h2, by simp [hb, hg]⟩
  · rintro ⟨h1, h2, hg⟩
    refine ⟨h1, h2, ?_⟩
    rcases hb : σ.2.hist.getLast? with _ | b
    · simp [hb] at hg
    · exact ⟨b, rfl, by simpa [hb] using hg⟩

/-- The protocol implements `Late⟨a --0--> b⟩` in the sense of `Coordination.lean`. -/
theorem implementsLate_T : γ.ImplementsLate T 0 := by
  intro r hr σ ⟨ha, hB, hb⟩
  obtain ⟨σC, hC, hp⟩ := implementsLate r hr σ ha hB hb
  exact ⟨σC, goNode_iff.2 hC, hp⟩

/-- The run `r₁`: `C` receives only `μ_go` at time 2. -/
def r₁ := sched {1}
/-- The run `r₂`: `C` receives `μ_go` and `e'` at time 2. -/
def r₂ := sched {1, 2}

/-- **Theorem 3 fails for full-information protocols that do not flood.** The protocol is a FIP
and implements `Late⟨a --0--> b⟩`; in `r₁`, `C` sends "go" at `σ_C` and `B` performs `b` at `σ`,
but `K_σ(σ_C·A --0--> σ)` is false: in `r₂` the node `σ` appears and `σ_C` does not. -/
theorem theorem_3_false_for_FIP : γ.IsFIP ∧ γ.ImplementsLate T 0 ∧
    ∃ r σC σ, γ.Valid r ∧ γ.GoNode r T σC ∧ γ.Performs r T σ ∧
      ¬ γ.Knows σ (fun r' => γ.Prec r' (T.aNode σC) 0 (GNode.ofB σ)) := by
  refine ⟨isFIP, implementsLate_T, r₁, (1, γ.st r₁ 2 1), (3, γ.st r₁ 3 3), valid_sched (by decide),
    ?_, ?_, ?_⟩
  · rw [goNode_iff]
    refine ⟨γ.appears_st _ _ _, rfl, ?_⟩
    simp [r₁, st_C_two (X := {1}) (by decide), lastExt]
  · refine ⟨γ.appears_st _ _ _, rfl, ?_⟩
    simp only [T, r₁, st_B_three (X := {1}) (by decide)]
    refine ⟨⟨cM, ∅⟩, rfl, ⟨enc dS, by simp [cM]⟩, fun m => by simp [cM]⟩
  · intro hK
    have hB : γ.appears r₂ (3, γ.st r₁ 3 3) :=
      ⟨3, by simp [r₁, r₂, st_B_three (X := {1}) (by decide), st_B_three (X := {1, 2}) (by decide)]⟩
    obtain ⟨α, -, hα, -, -⟩ := hK r₂ (valid_sched (by decide)) hB
    have hC := (gbasic_appears γ r₂ hα).1
    obtain ⟨t, ht⟩ := hC
    simp only [r₁, st_C_two (X := {1}) (by decide), CoordTask.aNode, T] at ht
    rcases Nat.lt_or_ge t 2 with h | h
    · have h0 : (γ.st r₂ t 1).hist = [] := by
        interval_cases t
        · rfl
        · rw [r₂, st_C_one (by decide)]
      rw [ht] at h0; simp at h0
    · have hp := γ.hist_prefix r₂ h 1
      rw [ht, r₂, st_C_two (by decide)] at hp
      have := hp.eq_of_length (by simp)
      simp only [List.cons.injEq, and_true, Batch.mk.injEq, true_and] at this
      revert this; decide

end CounterexampleFIP

end Podc.ZigzagCausality
