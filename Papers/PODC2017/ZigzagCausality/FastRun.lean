import Papers.PODC2017.ZigzagCausality.Knowledge

/-!
# The fast run of the proof of Theorem 4 (⇒) — Appendix C, Definitions 16, 23, 24, Lemma 18

Dan, Manohar, Moses, *On Using Time Without Clocks via Zigzag Causality*, PODC 2017.

Fix a run `r` and a basic node `σ` of `r`. Given a timing `T` of the non-initial nodes of
`past(r, σ)` (`FData`), we build a run `r' = FData.run` in which

* every non-initial node `σ' ⇝_r σ` appears exactly at time `T σ'` (so `r' ∼_σ r`), and
* every other node of process `j` is created no earlier than `ψ j` (`FData.psi`), the time of the
  auxiliary node `ψ_j` of the extended bounds graph `G_E(r, σ)` (Definition 16).

`ψ j` is given in closed form: it is the longest path into `ψ_j` in `G_E(r, σ)` that starts at a
boundary edge, `ψ j = max(1, max {T b + 1 − U(q)})` over non-initial past nodes `b` and channel
paths `q` from `j` to the process of `b` (the edges `ψ_i → ψ_j` of weight `−U_ji` and `b → ψ_{b.1}`
of weight `1`). Delivery in `r'` (Definition 24):

1. a message sent at a past node `u` and received in `r` at a past node `v` is delivered at `T v`;
2. a message whose sender time and channel are in the "slow" set `Sl` is delivered at its upper
   bound (used to delay the message chain of the first node of the precedence);
3. every other message is delivered at `max(t + L, ψ j)` (the earliest legal time after the
   auxiliary node).

The conditions on `T` (`FData.Good`) are exactly the constraints of `G_E(r, σ)` that matter:
`L`/`U` bounds of messages inside the past (`T_recv`), monotonicity along timelines (`T_mono`),
and the `E'`–`E'''`–`E''` constraints of messages that leave the past (`T_esc`).
The main results are `FData.run_valid` (Lemma 18.1), `FData.timer_run`, `FData.appears_run`
(Lemma 18.2, 18.3), and the computation of message chains leaving the past (`FData.chain_fwd`,
`FData.chain_slow`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

/-- `q` is a path of channels starting at `i` (the hops `i → q₁ → q₂ → …`). -/
def Net.ChanPath (N : Net P) : P → List P → Prop
  | _, [] => True
  | i, j :: q => N.Chan i j ∧ N.ChanPath j q

@[simp] theorem Net.chanPath_nil (N : Net P) (i : P) : N.ChanPath i [] := trivial

@[simp] theorem Net.chanPath_cons (N : Net P) (i j : P) (q : List P) :
    N.ChanPath i (j :: q) ↔ N.Chan i j ∧ N.ChanPath j q := Iff.rfl

theorem Net.chanPath_append (N : Net P) (i : P) (q q' : List P) :
    N.ChanPath i (q ++ q') ↔ N.ChanPath i q ∧ N.ChanPath (lastP i q) q' := by
  induction q generalizing i with
  | nil => simp
  | cons j q ih => simp [ih, and_assoc]

namespace Sys

variable {γ : Sys P S M E} {r : Sched P S E} [Finite P]

/-! ### Preliminaries on runs -/

/-- The past of a node is finite. -/
theorem past_finite (hr : γ.Valid r) (σ : BNode P S M E) : {v | γ.HB r v σ}.Finite := by
  have hfin : (Set.univ ×ˢ Set.Iic (γ.timer r σ) : Set (P × ℕ)).Finite :=
    Set.finite_univ.prod (Set.finite_Iic _)
  refine (hfin.image fun p => (p.1, γ.st r p.2 p.1)).subset ?_
  intro v hv
  have hle := HB.timer_le hr hv
  refine ⟨(v.1, γ.timer r v), ⟨Set.mem_univ _, hle⟩, ?_⟩
  simp only
  rw [γ.st_timer r (HB.appears hv).1]

/-- Message chains of a run follow channel paths. -/
theorem gbasic_chanPath (hr : γ.Valid r) :
    ∀ {q : List P} {w z : BNode P S M E}, γ.gbasic r w q = some z → γ.net.ChanPath w.1 q
  | [], _, _, _ => trivial
  | j :: q, w, z, h => by
    simp only [gbasic_cons] at h
    obtain ⟨w1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have hs := recv_spec hr h1
    refine ⟨hs.2.2.1, ?_⟩
    have := gbasic_chanPath hr h2
    rwa [hs.1] at this

/-- In a flooding protocol, message chains from non-initial nodes exist along every channel
path. -/
theorem flood_chain (hF : γ.IsFFIP) (hr : γ.Valid r) :
    ∀ (q : List P) {w : BNode P S M E}, γ.appears r w → 0 < γ.timer r w →
      γ.net.ChanPath w.1 q → ∃ z, γ.gbasic r w q = some z ∧ 0 < γ.timer r z
  | [], w, ha, h0, _ => ⟨w, γ.gbasic_self r ha, h0⟩
  | j :: q, w, ha, h0, hq => by
    obtain ⟨w1, h1⟩ := Option.isSome_iff_exists.1 (recv_isSome_of_FFIP hF ha h0 hq.1)
    have hs := recv_spec hr h1
    have := γ.net.one_le_L _ _ hq.1
    obtain ⟨z, hz, hz0⟩ := flood_chain hF hr q hs.2.1 (by omega) (hs.1 ▸ hq.2)
    exact ⟨z, by simp only [gbasic_cons, h1, Option.bind_some]; exact hz, hz0⟩

/-- A node outside the past of `σ` is later than every node of its process in the past. -/
theorem timer_lt_of_not_past {σ b z : BNode P S M E} (hb : γ.HB r b σ) (hz : γ.appears r z)
    (hzn : ¬ γ.HB r z σ) (hp : z.1 = b.1) : γ.timer r b < γ.timer r z := by
  by_contra hc
  push Not at hc
  exact hzn ((HB.of_local hz (HB.appears hb).1 hp hc).trans hb)

/-! ### The data of a fast run -/

/-- The data of a fast run: the node `σ`, the timing `T` of the past of `σ`, and the set `Sl` of
(sender, sending time, receiver) of messages that are delivered at their upper bound. -/
structure FData (γ : Sys P S M E) (r : Sched P S E) where
  σ : BNode P S M E
  T : BNode P S M E → ℕ
  Sl : P → ℕ → P → Prop

namespace FData

variable (D : γ.FData r)

/-- The non-initial nodes of the past of `σ`. -/
def Pos (v : BNode P S M E) : Prop := γ.HB r v D.σ ∧ 0 < γ.timer r v

/-- `u` is a non-initial past `j`-node with `T u = t`. -/
def At (j : P) (t : ℕ) (u : BNode P S M E) : Prop := D.Pos u ∧ u.1 = j ∧ D.T u = t

/-- The candidate values for the time `ψ j` of the auxiliary node of `j`. -/
def psiSet (k : P) : Set ℤ :=
  {1} ∪ {z | ∃ b q, D.Pos b ∧ γ.net.ChanPath k q ∧ b.1 = lastP k q ∧
    z = (D.T b : ℤ) + 1 - γ.net.Up k q}

/-- The time of the auxiliary node `ψ_k` (as an integer). -/
noncomputable def psiZ (k : P) : ℤ := sSup (D.psiSet k)

/-- The time of the auxiliary node `ψ_k`. -/
noncomputable def psi (k : P) : ℕ := (D.psiZ k).toNat

/-- Rule 1 of the fast run applies to the message sent by `i` at time `s` to `j`: it is sent at a
past node and received in `r` at the past node `v`. -/
def Rule1 (i : P) (s : ℕ) (j : P) (v : BNode P S M E) : Prop :=
  (∃ u, D.At i s u ∧ γ.recv r u j = some v) ∧ γ.HB r v D.σ

/-- The fast run (Definition 24). -/
noncomputable def run : Sched P S E where
  g := r.g
  dlv i s j := if h : ∃ v, D.Rule1 i s j v then D.T h.choose else
    if D.Sl i s j then s + γ.net.U i j else max (s + γ.net.L i j) (D.psi j)
  ext t j := if h : ∃ u, D.At j t u then r.ext (γ.timer r h.choose) j else ∅

/-- The constraints of `G_E(r, σ)` that a timing must satisfy. -/
structure Good : Prop where
  T_pos : ∀ v, D.Pos v → 0 < D.T v
  T_recv : ∀ u v j, D.Pos v → γ.recv r u j = some v →
    D.T u + γ.net.L u.1 j ≤ D.T v ∧ D.T v ≤ D.T u + γ.net.U u.1 j
  T_mono : ∀ u v, D.Pos u → D.Pos v → u.1 = v.1 → γ.timer r u < γ.timer r v → D.T u < D.T v
  T_esc : ∀ u j w q b, D.Pos u → γ.recv r u j = some w → ¬ γ.HB r w D.σ →
    γ.net.ChanPath j q → D.Pos b → b.1 = lastP j q →
    (D.T b : ℤ) + 1 ≤ D.T u + γ.net.U u.1 j + γ.net.Up j q
  Sl_ok : ∀ i s j, D.Sl i s j → (D.psi j : ℤ) ≤ s + γ.net.U i j

variable {D}

/-! ### The auxiliary times `ψ` -/

section Psi

variable (hr : γ.Valid r)
include hr

theorem psiSet_bdd (k : P) : BddAbove (D.psiSet k) := by
  obtain ⟨B, hB⟩ := ((past_finite hr D.σ).image fun b => (D.T b : ℤ) + 1).bddAbove
  refine ⟨max 1 B, ?_⟩
  rintro z (hz | ⟨b, q, hb, -, -, rfl⟩)
  · rw [Set.mem_singleton_iff.1 hz]; exact le_max_left _ _
  · have h1 : (D.T b : ℤ) + 1 ≤ B := hB ⟨b, hb.1, rfl⟩
    have : (0 : ℤ) ≤ γ.net.Up k q := by positivity
    exact le_max_of_le_right (by omega)

theorem one_le_psiZ (k : P) : 1 ≤ D.psiZ k :=
  le_csSup (psiSet_bdd hr k) (Or.inl rfl)

theorem psi_eq (k : P) : (D.psi k : ℤ) = D.psiZ k := by
  have := one_le_psiZ hr (D := D) k
  simp only [psi]; omega

theorem one_le_psi (k : P) : 1 ≤ D.psi k := by
  have := one_le_psiZ hr (D := D) k
  have := psi_eq hr (D := D) k
  omega

theorem le_psi {b : BNode P S M E} {k : P} {q : List P} (hb : D.Pos b) (hq : γ.net.ChanPath k q)
    (hl : b.1 = lastP k q) : (D.T b : ℤ) + 1 - γ.net.Up k q ≤ D.psi k := by
  rw [psi_eq hr]
  exact le_csSup (psiSet_bdd hr k) (Or.inr ⟨b, q, hb, hq, hl, rfl⟩)

theorem T_lt_psi {b : BNode P S M E} (hb : D.Pos b) : D.T b < D.psi b.1 := by
  have := le_psi hr hb (q := []) trivial rfl
  simp only [Net.Up_nil, Nat.cast_zero, sub_zero] at this
  omega

theorem psi_cases (k : P) : D.psi k = 1 ∨ ∃ b q, D.Pos b ∧ γ.net.ChanPath k q ∧
    b.1 = lastP k q ∧ (D.psi k : ℤ) = D.T b + 1 - γ.net.Up k q := by
  have hmem := Int.csSup_mem (s := D.psiSet k) ⟨1, Or.inl rfl⟩ (psiSet_bdd hr k)
  rw [← psiZ, ← psi_eq hr] at hmem
  rcases hmem with h | ⟨b, q, hb, hq, hl, h⟩
  · left; have := Set.mem_singleton_iff.1 h; omega
  · exact Or.inr ⟨b, q, hb, hq, hl, h⟩

theorem psi_chan {i j : P} (hc : γ.net.Chan i j) :
    (D.psi j : ℤ) ≤ D.psi i + γ.net.U i j := by
  have h1 := one_le_psi hr (D := D) i
  rcases psi_cases hr (D := D) j with h | ⟨b, q, hb, hq, hl, h⟩
  · rw [h]; push_cast; omega
  · have := le_psi hr hb (k := i) (q := j :: q) ⟨hc, hq⟩ (by rw [hl, lastP_cons])
    simp only [Net.Up_cons, Nat.cast_add] at this
    omega

end Psi

/-! ### Basic facts about the timing -/

section Timing

variable (hr : γ.Valid r) (hD : D.Good)
include hr hD

theorem Pos.appears {v : BNode P S M E} (h : D.Pos v) : γ.appears r v := (HB.appears h.1).1

theorem Pos.hist_ne_nil {v : BNode P S M E} (h : D.Pos v) : v.2.hist ≠ [] :=
  (γ.timer_pos_iff r (h.appears hr hD)).1 h.2

theorem T_inj {u v : BNode P S M E} (hu : D.Pos u) (hv : D.Pos v) (hp : u.1 = v.1)
    (hT : D.T u = D.T v) : u = v := by
  rcases lt_trichotomy (γ.timer r u) (γ.timer r v) with h | h | h
  · exact absurd (hD.T_mono u v hu hv hp h) (by omega)
  · exact γ.eq_of_timer_eq r hp (hu.appears hr hD) (hv.appears hr hD) h
  · exact absurd (hD.T_mono v u hv hu hp.symm h) (by omega)

theorem timer_lt_of_T_lt {u v : BNode P S M E} (hu : D.Pos u) (hv : D.Pos v) (hp : u.1 = v.1)
    (hT : D.T u < D.T v) : γ.timer r u < γ.timer r v := by
  rcases lt_trichotomy (γ.timer r u) (γ.timer r v) with h | h | h
  · exact h
  · have := γ.eq_of_timer_eq r hp (hu.appears hr hD) (hv.appears hr hD) h
    subst this; omega
  · exact absurd (hD.T_mono v u hv hu hp.symm h) (by omega)

theorem prefix_of_T_le {u v : BNode P S M E} (hu : D.Pos u) (hv : D.Pos v) (hp : u.1 = v.1)
    (hT : D.T u ≤ D.T v) : u.2.hist <+: v.2.hist := by
  refine (γ.timer_le_iff_prefix r hp (hu.appears hr hD) (hv.appears hr hD)).1 ?_
  rcases hT.lt_or_eq with h | h
  · exact (timer_lt_of_T_lt hr hD hu hv hp h).le
  · rw [T_inj hr hD hu hv hp h]

theorem At.unique {j : P} {t : ℕ} {u u' : BNode P S M E} (h : D.At j t u) (h' : D.At j t u') :
    u = u' :=
  T_inj hr hD h.1 h'.1 (h.2.1.trans h'.2.1.symm) (h.2.2.trans h'.2.2.symm)

theorem At.lt_psi {j : P} {t : ℕ} {u : BNode P S M E} (h : D.At j t u) : t < D.psi j := by
  obtain ⟨hp, rfl, rfl⟩ := h
  exact T_lt_psi hr hp

theorem Rule1.spec {i j : P} {s : ℕ} {v : BNode P S M E} (h : D.Rule1 i s j v) :
    D.Pos v ∧ v.1 = j ∧ ∃ u, D.At i s u ∧ γ.recv r u j = some v := by
  obtain ⟨⟨u, hu, hrecv⟩, hv⟩ := h
  have hs := recv_spec hr hrecv
  have := γ.net.one_le_L _ _ hs.2.2.1
  exact ⟨⟨hv, by omega⟩, hs.1, u, hu, hrecv⟩

theorem Rule1.unique {i j : P} {s : ℕ} {v v' : BNode P S M E} (h : D.Rule1 i s j v)
    (h' : D.Rule1 i s j v') : v = v' := by
  obtain ⟨⟨u, hu, h1⟩, -⟩ := h
  obtain ⟨⟨u', hu', h2⟩, -⟩ := h'
  obtain rfl := hu.unique hr hD hu'
  rw [h1] at h2
  exact Option.some.inj h2

theorem dlv_rule1 {i j : P} {s : ℕ} {v : BNode P S M E} (h : D.Rule1 i s j v) :
    D.run.dlv i s j = D.T v := by
  have he : ∃ v, D.Rule1 i s j v := ⟨v, h⟩
  simp only [run, he, ↓reduceDIte]
  rw [he.choose_spec.unique hr hD h]

theorem dlv_not_rule1 {i j : P} {s : ℕ} (h : ¬ ∃ v, D.Rule1 i s j v) :
    D.run.dlv i s j =
      if D.Sl i s j then s + γ.net.U i j else max (s + γ.net.L i j) (D.psi j) := by
  simp only [run, h, ↓reduceDIte]

theorem psi_le_dlv {i j : P} {s : ℕ} (h : ¬ ∃ v, D.Rule1 i s j v) :
    D.psi j ≤ D.run.dlv i s j := by
  rw [dlv_not_rule1 hr hD h]
  split_ifs with hS
  · have := hD.Sl_ok i s j hS; omega
  · exact le_max_right _ _

theorem no_rule1_of_psi_le {i j : P} {s : ℕ} (h : D.psi i ≤ s) : ¬ ∃ v, D.Rule1 i s j v := by
  rintro ⟨v, ⟨u, hu, -⟩, -⟩
  have := hu.lt_psi hr hD
  omega

theorem ext_run_of_at {j : P} {t : ℕ} {u : BNode P S M E} (h : D.At j t u) :
    D.run.ext t j = r.ext (γ.timer r u) j := by
  have he : ∃ u, D.At j t u := ⟨u, h⟩
  simp only [run, he, ↓reduceDIte]
  rw [he.choose_spec.unique hr hD h]

theorem ext_run_of_not {j : P} {t : ℕ} (h : ¬ ∃ u, D.At j t u) : D.run.ext t j = ∅ := by
  simp only [run, h, ↓reduceDIte]

/-- A message from a past node that leaves the past can be delivered after `ψ`. -/
theorem psi_le_esc {u w : BNode P S M E} {j : P} (hu : D.Pos u) (hw : γ.recv r u j = some w)
    (hn : ¬ γ.HB r w D.σ) : (D.psi j : ℤ) ≤ D.T u + γ.net.U u.1 j := by
  have h1 := hD.T_pos u hu
  rcases psi_cases hr (D := D) j with h | ⟨b, q, hb, hq, hl, h⟩
  · rw [h]; push_cast; omega
  · have := hD.T_esc u j w q b hu hw hn hq hb hl
    omega

end Timing

/-! ### The invariant of the fast run -/

/-- `ℓ` is the state of the latest non-initial past `j`-node `u` with `T u ≤ t`, or the initial
state of `j` if there is none. -/
def IsLatest (j : P) (t : ℕ) (ℓ : LState P S M E) : Prop :=
  (∀ u, D.Pos u → u.1 = j → D.T u ≤ t → u.2.hist <+: ℓ.hist) ∧
    (ℓ = ⟨r.g j, []⟩ ∨ (D.Pos (j, ℓ) ∧ D.T (j, ℓ) ≤ t))

/-- The invariant of the fast run up to time `t`. -/
def Inv (t : ℕ) : Prop :=
  ∀ s ≤ t, ∀ i, (s < D.psi i → D.IsLatest i s (γ.st D.run s i)) ∧
    (γ.Active D.run i s → (∃ u, D.At i s u) ∨ D.psi i ≤ s)

section Inv

variable (hr : γ.Valid r) (hD : D.Good)
include hr hD

theorem IsLatest.unique {j : P} {t t' : ℕ} {ℓ ℓ' : LState P S M E} (h : D.IsLatest j t ℓ)
    (h' : D.IsLatest j t' ℓ') (h1 : ∀ u, D.Pos u → u.1 = j → D.T u ≤ t → D.T u ≤ t')
    (h2 : ∀ u, D.Pos u → u.1 = j → D.T u ≤ t' → D.T u ≤ t) : ℓ = ℓ' := by
  rcases h.2 with rfl | ⟨hp, hT⟩ <;> rcases h'.2 with rfl | ⟨hp', hT'⟩
  · rfl
  · exact absurd (List.eq_nil_of_prefix_nil (h.1 _ hp' rfl (h2 _ hp' rfl hT')))
      (hp'.hist_ne_nil hr hD)
  · exact absurd (List.eq_nil_of_prefix_nil (h'.1 _ hp rfl (h1 _ hp rfl hT)))
      (hp.hist_ne_nil hr hD)
  · have a := h.1 _ hp' rfl (h2 _ hp' rfl hT')
    have b := h'.1 _ hp rfl (h1 _ hp rfl hT)
    refine LState.ext' ?_ (a.eq_of_length (le_antisymm a.length_le b.length_le)).symm
    rw [init_of_appears (hp.appears hr hD), init_of_appears (hp'.appears hr hD)]

theorem IsLatest.eq {j : P} {t : ℕ} {ℓ : LState P S M E} {u : BNode P S M E}
    (h : D.IsLatest j t ℓ) (hu : D.At j t u) : ℓ = u.2 := by
  obtain ⟨hp, rfl, rfl⟩ := hu
  have a := h.1 u hp rfl le_rfl
  rcases h.2 with rfl | ⟨hq, hT⟩
  · exact absurd (List.eq_nil_of_prefix_nil a) (hp.hist_ne_nil hr hD)
  · have b := prefix_of_T_le hr hD hq hp rfl hT
    exact LState.ext' (by rw [init_of_appears (hq.appears hr hD),
      init_of_appears (hp.appears hr hD)])
      (b.eq_of_length (le_antisymm b.length_le a.length_le))

theorem IsLatest.ne {j : P} {t : ℕ} {ℓ : LState P S M E} {u : BNode P S M E}
    (h : D.IsLatest j t ℓ) (hp : D.Pos u) (hj : u.1 = j) (ht : t < D.T u) : ℓ ≠ u.2 := by
  rintro rfl
  rcases h.2 with he | ⟨_, hT⟩
  · exact hp.hist_ne_nil hr hD (by rw [he])
  · have : ((j, u.2) : BNode P S M E) = u := by rw [← hj]
    rw [this] at hT; omega

section Step

variable {t : ℕ} (H : D.Inv t)
include H

theorem st_run_of_at' {s : ℕ} (hs : s ≤ t) {i : P} {u : BNode P S M E} (h : D.At i s u) :
    γ.st D.run s i = u.2 :=
  ((H s hs i).1 (h.lt_psi hr hD)).eq hr hD h

theorem active_run_of_at' {s : ℕ} (hs : s ≤ t) {i : P} {u : BNode P S M E} (h : D.At i s u) :
    γ.Active D.run i s := by
  have hpos := hD.T_pos u h.1
  have hT := h.2.2
  have hlt := h.lt_psi hr hD
  refine ⟨by omega, ?_⟩
  rw [st_run_of_at' hr hD H hs h]
  exact (((H (s - 1) (by omega) i).1 (by omega)).ne hr hD h.1 h.2.1 (by omega)).symm

/-- The messages delivered at time `t + 1`. -/
theorem msg_cases {i j : P} {m : M} (hm : (i, m) ∈ (γ.batch D.run t j).msgs) :
    (∃ u v, D.Pos u ∧ u.1 = i ∧ γ.recv r u j = some v ∧ D.At j (t + 1) v ∧
      γ.send i u.2 j = some m) ∨ D.psi j ≤ t + 1 := by
  rw [mem_batch_msgs] at hm
  obtain ⟨s, hs, -, -, hd, hsend⟩ := hm
  by_cases hR : ∃ v, D.Rule1 i s j v
  · obtain ⟨v, hv⟩ := hR
    obtain ⟨hpv, hvj, u, hu, hrecv⟩ := hv.spec hr hD
    rw [dlv_rule1 hr hD hv] at hd
    rw [st_run_of_at' hr hD H (by omega) hu] at hsend
    exact Or.inl ⟨u, v, hu.1, hu.2.1, hrecv, ⟨hpv, hvj, hd⟩, hsend⟩
  · right
    have := psi_le_dlv hr hD hR
    omega

theorem batch_run_of_not {j : P} (hn : ¬ ∃ u, D.At j (t + 1) u) (hlt : t + 1 < D.psi j) :
    γ.batch D.run t j = ⟨∅, ∅⟩ := by
  refine Batch.ext' ?_ (by rw [batch_ext, ext_run_of_not hr hD hn])
  ext ⟨i, m⟩
  simp only [Finset.notMem_empty, iff_false]
  intro hm
  rcases msg_cases hr hD H hm with ⟨_, v, -, -, -, hv, -⟩ | h
  · exact hn ⟨v, hv⟩
  · omega

theorem batch_run_of_at {j : P} {u : BNode P S M E} (hu : D.At j (t + 1) u) :
    γ.batch D.run t j = γ.batch r (γ.timer r u - 1) j := by
  have hpos := hu.1.2
  refine Batch.ext' ?_ ?_
  · ext ⟨i, m⟩
    constructor
    · intro hm
      rcases msg_cases hr hD H hm with ⟨u', v, hu', rfl, hrecv, hv, hsend⟩ | h
      · obtain rfl := hv.unique hr hD hu
        have hs := recv_spec hr hrecv
        have := γ.net.one_le_L _ _ hs.2.2.1
        rw [mem_batch_msgs]
        refine ⟨γ.timer r u', by omega, γ.active_timer r (hu'.appears hr hD) hu'.2, hs.2.2.1,
          by omega, ?_⟩
        rw [γ.st_timer r (hu'.appears hr hD)]; exact hsend
      · have := hu.lt_psi hr hD; omega
    · intro hm
      rw [mem_batch_msgs] at hm
      obtain ⟨s', hs', ha, hc, hd, hsend⟩ := hm
      set u' : BNode P S M E := (i, γ.st r s' i) with hu'def
      have hti : γ.timer r u' = s' := γ.timer_eq_of_active r ha
      obtain ⟨hp, hj, hT⟩ := hu
      have hrecv : γ.recv r u' j = some u := by
        rw [recv_eq_some]
        refine ⟨⟨by rw [hti]; exact ha, hc, by rw [hti, hsend]; rfl⟩, ?_⟩
        rw [hti, hd, Nat.sub_add_cancel hpos, ← hj, γ.st_timer r (hp.appears hr hD)]
      have hp' : D.Pos u' := ⟨(HB.of_recv hrecv).trans hp.1, by rw [hti]; exact ha.1⟩
      have hTr := hD.T_recv u' u j hp hrecv
      have := γ.net.one_le_L u'.1 j hc
      have hAt : D.At i (D.T u') u' := ⟨hp', rfl, rfl⟩
      rw [mem_batch_msgs]
      refine ⟨D.T u', by omega, active_run_of_at' hr hD H (by omega) hAt, hc, ?_, ?_⟩
      · rw [dlv_rule1 hr hD (v := u) ⟨⟨u', hAt, hrecv⟩, hp.1⟩, hT]
      · rw [st_run_of_at' hr hD H (by omega) hAt]; exact hsend
  · rw [batch_ext, batch_ext, ext_run_of_at hr hD hu, Nat.sub_add_cancel hpos]

theorem isLatest_succ {j : P} (hlt : t + 1 < D.psi j) :
    D.IsLatest j (t + 1) (γ.st D.run (t + 1) j) := by
  by_cases hex : ∃ u, D.At j (t + 1) u
  · obtain ⟨u, hu⟩ := hex
    obtain ⟨hp, rfl, hT⟩ := id hu
    have hua := hp.appears hr hD
    set π : BNode P S M E := (u.1, γ.st r (γ.timer r u - 1) u.1) with hπ
    have hπa : γ.appears r π := γ.appears_st r _ _
    have hπt : γ.timer r π < γ.timer r u := by
      have h1 : γ.timer r π ≤ γ.timer r u - 1 := γ.timer_st_le r _ _
      have := hp.2; omega
    have hlat : D.IsLatest u.1 t π.2 := by
      refine ⟨fun w hw hj hTw => ?_, ?_⟩
      · have := timer_lt_of_T_lt hr hD hw hp hj (by omega)
        rw [← γ.st_timer r (hw.appears hr hD), hj]
        exact γ.hist_prefix r (by omega) _
      · by_cases h0 : 0 < γ.timer r π
        · have hπp : D.Pos π :=
            ⟨(HB.of_local hπa hua rfl hπt.le).trans hp.1, h0⟩
          have := hD.T_mono π u hπp hp rfl hπt
          exact Or.inr ⟨hπp, show D.T π ≤ t by omega⟩
        · left
          have := γ.st_timer r hπa
          rw [show γ.timer r π = 0 by omega] at this
          rw [← this, st_zero]
    have hprev : γ.st D.run t u.1 = π.2 :=
      IsLatest.unique hr hD ((H t le_rfl u.1).1 (by omega)) hlat (fun _ _ _ h => h)
        (fun _ _ _ h => h)
    have hnew : γ.st D.run (t + 1) u.1 = u.2 := by
      rw [st_succ, hprev, batch_run_of_at hr hD H hu, hπ]
      simp only
      rw [← st_succ, Nat.sub_add_cancel hp.2, γ.st_timer r hua]
    rw [hnew]
    exact ⟨fun w hw hj hTw => prefix_of_T_le hr hD hw hp hj (by omega),
      Or.inr ⟨hp, show D.T u ≤ t + 1 by omega⟩⟩
  · have hst : γ.st D.run (t + 1) j = γ.st D.run t j := by
      rw [st_succ, batch_run_of_not hr hD H hex hlt, step_eq]; simp
    rw [hst]
    obtain ⟨h1, h2⟩ := (H t le_rfl j).1 (by omega)
    refine ⟨fun w hp hj hTw => h1 w hp hj ?_, h2.imp_right fun h => ⟨h.1, by omega⟩⟩
    rcases Nat.lt_or_ge (D.T w) (t + 1) with h | h
    · omega
    · exact absurd ⟨w, hp, hj, by omega⟩ hex

theorem active_succ {j : P} (ha : γ.Active D.run j (t + 1)) :
    (∃ u, D.At j (t + 1) u) ∨ D.psi j ≤ t + 1 := by
  by_cases hex : ∃ u, D.At j (t + 1) u
  · exact Or.inl hex
  rw [active_succ_iff] at ha
  have he : (γ.batch D.run t j).ext = ∅ := by rw [batch_ext, ext_run_of_not hr hD hex]
  have hm : (γ.batch D.run t j).msgs ≠ ∅ := fun h => ha ⟨h, he⟩
  obtain ⟨⟨i, m⟩, hmem⟩ := Finset.nonempty_iff_ne_empty.2 hm
  rcases msg_cases hr hD H hmem with ⟨_, v, -, -, -, hv, -⟩ | h
  · exact Or.inl ⟨v, hv⟩
  · exact Or.inr h

end Step

theorem inv_all (t : ℕ) : D.Inv t := by
  induction t with
  | zero =>
    intro s hs i
    obtain rfl : s = 0 := by omega
    refine ⟨fun _ => ⟨fun u hu _ hT => absurd (hD.T_pos u hu) (by omega), Or.inl rfl⟩, ?_⟩
    rintro ⟨h, -⟩
    omega
  | succ t ih =>
    intro s hs i
    rcases Nat.lt_or_ge s (t + 1) with h | h
    · exact ih s (by omega) i
    · obtain rfl : s = t + 1 := by omega
      exact ⟨fun hlt => isLatest_succ hr hD ih hlt, fun ha => active_succ hr hD ih ha⟩

/-! ### Properties of the fast run (Lemma 18) -/

theorem st_run {u : BNode P S M E} (h : D.Pos u) : γ.st D.run (D.T u) u.1 = u.2 :=
  st_run_of_at' hr hD (inv_all hr hD _) le_rfl ⟨h, rfl, rfl⟩

theorem active_run_of_at {i : P} {s : ℕ} {u : BNode P S M E} (h : D.At i s u) :
    γ.Active D.run i s :=
  active_run_of_at' hr hD (inv_all hr hD s) le_rfl h

/-- **Lemma 18.3.** The non-initial past nodes appear in the fast run at their `T`-times. -/
theorem timer_run {u : BNode P S M E} (h : D.Pos u) : γ.timer D.run u = D.T u := by
  have := γ.timer_eq_of_active D.run (active_run_of_at hr hD (u := u) ⟨h, rfl, rfl⟩)
  rwa [st_run hr hD h] at this

theorem active_run_cases {i : P} {s : ℕ} (h : γ.Active D.run i s) :
    (∃ u, D.At i s u) ∨ D.psi i ≤ s :=
  ((inv_all hr hD s) s le_rfl i).2 h

/-- **Lemma 18.2.** The past of `σ` appears in the fast run. -/
theorem appears_run {v : BNode P S M E} (h : γ.HB r v D.σ) : γ.appears D.run v := by
  by_cases h0 : 0 < γ.timer r v
  · exact ⟨D.T v, st_run hr hD ⟨h, h0⟩⟩
  · refine ⟨0, ?_⟩
    have := γ.st_timer r (HB.appears h).1
    rw [show γ.timer r v = 0 by omega, st_zero] at this
    rw [st_zero, ← this]
    rfl

theorem timer_run_init {v : BNode P S M E} (h : γ.HB r v D.σ) (h0 : γ.timer r v = 0) :
    γ.timer D.run v = 0 := by
  have := γ.st_timer r (HB.appears h).1
  rw [h0, st_zero] at this
  have h' : γ.st D.run 0 v.1 = v.2 := by rw [st_zero, ← this]; rfl
  exact Nat.le_zero.1 (γ.timer_le D.run h')

/-- **Lemma 18.1.** The fast run is a run of the system. -/
theorem run_valid (hF : γ.IsFFIP) : γ.Valid D.run where
  init := hr.init
  bounds i s j hs := by
    by_cases hR : ∃ v, D.Rule1 i s j v
    · obtain ⟨v, hv⟩ := hR
      rw [dlv_rule1 hr hD hv]
      obtain ⟨hpv, -, u, ⟨hu, hui, hus⟩, hrecv⟩ := hv.spec hr hD
      have := hD.T_recv u v j hpv hrecv
      rw [hui, hus] at this
      exact ⟨this.1, this.2⟩
    · rw [dlv_not_rule1 hr hD hR]
      have hLU := γ.net.L_le_U i j hs.2.1
      split_ifs with hS
      · exact ⟨by omega, le_rfl⟩
      · refine ⟨le_max_left _ _, max_le (by omega) ?_⟩
        rcases active_run_cases hr hD hs.1 with ⟨u, hu⟩ | hpsi
        · obtain ⟨hp, rfl, rfl⟩ := hu
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
            (recv_isSome_of_FFIP hF (hp.appears hr hD) hp.2 hs.2.1)
          have hn : ¬ γ.HB r w D.σ := fun hw' => hR ⟨w, ⟨u, ⟨hp, rfl, rfl⟩, hw⟩, hw'⟩
          have := psi_le_esc hr hD hp hw hn
          omega
        · have := psi_chan hr (D := D) hs.2.1
          omega
  ext_unique e t j t' j' h h' := by
    by_cases hex : ∃ u, D.At j t u
    · by_cases hex' : ∃ u, D.At j' t' u
      · obtain ⟨u, hu⟩ := hex
        obtain ⟨u', hu'⟩ := hex'
        rw [ext_run_of_at hr hD hu] at h
        rw [ext_run_of_at hr hD hu'] at h'
        obtain ⟨e1, e2⟩ := hr.ext_unique _ _ _ _ _ h h'
        have := γ.eq_of_timer_eq r (hu.2.1.trans (e2.trans hu'.2.1.symm)) (hu.1.appears hr hD)
          (hu'.1.appears hr hD) e1
        subst this
        exact ⟨hu.2.2.symm.trans hu'.2.2, e2⟩
      · rw [ext_run_of_not hr hD hex'] at h'; simp at h'
    · rw [ext_run_of_not hr hD hex] at h; simp at h

end Inv

/-! ### Message chains in the fast run -/

/-- The arrival time of a message chain along `q` that leaves `i` at time `t`, when every message
is delivered by rule 3 (at `max(t + L, ψ)`). -/
noncomputable def fwd : ℕ → P → List P → ℕ
  | t, _, [] => t
  | t, i, j :: q => fwd (max (t + γ.net.L i j) (D.psi j)) j q

/-- `fwd t i q` is either `t + L(i·q)`, or `ψ k + L(k·q₂)` for a split `q = q₁ ++ q₂` with
`q₁ ≠ []` ending at `k`. -/
theorem fwd_cases : ∀ (t : ℕ) (i : P) (q : List P),
    D.fwd t i q = t + γ.net.Lp i q ∨ ∃ q₁ q₂, q = q₁ ++ q₂ ∧ q₁ ≠ [] ∧
      D.fwd t i q = D.psi (lastP i q₁) + γ.net.Lp (lastP i q₁) q₂
  | t, i, [] => Or.inl (by simp [fwd])
  | t, i, j :: q => by
    rcases fwd_cases (max (t + γ.net.L i j) (D.psi j)) j q with h | ⟨q₁, q₂, rfl, hne, h⟩
    · rcases le_total (t + γ.net.L i j) (D.psi j) with hm | hm
      · refine Or.inr ⟨[j], q, rfl, by simp, ?_⟩
        simp only [fwd, lastP_cons, lastP_nil] at h ⊢
        rw [h, max_eq_right hm]
      · left
        simp only [fwd, Net.Lp_cons] at h ⊢
        rw [h, max_eq_left hm]; omega
    · exact Or.inr ⟨j :: q₁, q₂, rfl, by simp, by simpa [fwd] using h⟩

section Chains

variable (hr : γ.Valid r) (hD : D.Good) (hF : γ.IsFFIP)
include hr hD hF

/-- One hop of a message chain in the fast run. -/
theorem hop {w : BNode P S M E} {j : P} (hw : γ.appears D.run w) (h0 : 0 < γ.timer D.run w)
    (hc : γ.net.Chan w.1 j) : ∃ w1, γ.recv D.run w j = some w1 ∧ w1.1 = j ∧
      γ.timer D.run w1 = D.run.dlv w.1 (γ.timer D.run w) j := by
  obtain ⟨w1, h1⟩ := Option.isSome_iff_exists.1 (recv_isSome_of_FFIP hF hw h0 hc)
  have hs := recv_spec (run_valid hr hD hF) h1
  exact ⟨w1, h1, hs.1, hs.2.2.2.1⟩

/-- A message chain of the fast run that starts at a node created after `ψ` (and no slow
messages): its arrival time is `fwd`. -/
theorem chain_fwd (hSl : ∀ i s j, ¬ D.Sl i s j) :
    ∀ (q : List P) {w : BNode P S M E}, γ.appears D.run w → 0 < γ.timer D.run w →
      D.psi w.1 ≤ γ.timer D.run w → γ.net.ChanPath w.1 q →
      ∃ w', γ.gbasic D.run w q = some w' ∧ γ.timer D.run w' = D.fwd (γ.timer D.run w) w.1 q
  | [], w, hw, _, _, _ => ⟨w, γ.gbasic_self _ hw, rfl⟩
  | j :: q, w, hw, h0, hpsi, hq => by
    obtain ⟨w1, h1, hj, ht⟩ := hop hr hD hF hw h0 hq.1
    rw [dlv_not_rule1 hr hD (no_rule1_of_psi_le hr hD hpsi)] at ht
    simp only [hSl, ↓reduceIte] at ht
    have hs := recv_spec (run_valid hr hD hF) h1
    have h1p := one_le_psi hr (D := D) j
    have hge : D.psi w1.1 ≤ γ.timer D.run w1 := by rw [ht, hj]; exact le_max_right _ _
    obtain ⟨w', hw', ht'⟩ := chain_fwd hSl q hs.2.1 (by rw [hj] at hge; omega) hge
      (hj ▸ hq.2)
    refine ⟨w', by simp only [gbasic_cons, h1, Option.bind_some]; exact hw', ?_⟩
    rw [ht', ht, hj]
    rfl

omit hF in
/-- Rule 1 does not apply to a message from a past node that leaves the past. -/
theorem no_rule1_esc {a w : BNode P S M E} {j : P} (ha : D.Pos a) (hw : γ.recv r a j = some w)
    (hn : ¬ γ.HB r w D.σ) : ¬ ∃ v, D.Rule1 a.1 (D.T a) j v := by
  rintro ⟨v, ⟨u, hu, hrecv⟩, hv⟩
  obtain rfl := hu.unique hr hD ⟨ha, rfl, rfl⟩
  rw [hw] at hrecv
  cases hrecv
  exact hn hv

/-- A message chain of the fast run that leaves the past of `σ` at its first hop (no slow
messages): its arrival time is `fwd`. -/
theorem chain_first (hSl : ∀ i s j, ¬ D.Sl i s j) {a w : BNode P S M E} {j : P} {q : List P}
    (ha : D.Pos a) (hw : γ.recv r a j = some w) (hn : ¬ γ.HB r w D.σ)
    (hq : γ.net.ChanPath j q) :
    ∃ w', γ.gbasic D.run a (j :: q) = some w' ∧
      γ.timer D.run w' = D.fwd (D.T a) a.1 (j :: q) := by
  have hc := (recv_spec hr hw).2.2.1
  have hta := timer_run hr hD ha
  obtain ⟨w1, h1, hj, ht⟩ := hop hr hD hF (appears_run hr hD ha.1) (by rw [hta]; exact hD.T_pos a ha)
    hc
  have hR := no_rule1_esc hr hD ha hw hn
  rw [hta, dlv_not_rule1 hr hD hR] at ht
  simp only [hSl, ↓reduceIte] at ht
  have hs := recv_spec (run_valid hr hD hF) h1
  have h1p := one_le_psi hr (D := D) j
  have hge : D.psi w1.1 ≤ γ.timer D.run w1 := by rw [ht, hj]; exact le_max_right _ _
  obtain ⟨w', hw', ht'⟩ := chain_fwd hr hD hF hSl q hs.2.1 (by rw [hj] at hge; omega) hge
    (hj ▸ hq)
  refine ⟨w', by simp only [gbasic_cons, h1, Option.bind_some]; exact hw', ?_⟩
  rw [ht', ht, hj]
  rfl

end Chains

end FData

/-- The slow messages of the chain along `q` that leaves `i` at time `t` and is delivered at the
upper bounds: `(i', s, j') ∈ SlowSet i t q` iff the chain sends from `i'` at time `s` to `j'`. -/
def _root_.Podc.ZigzagCausality.Net.SlowSet (N : Net P) : P → ℕ → List P → P → ℕ → P → Prop
  | _, _, [], _, _, _ => False
  | i, t, j :: q, i', s, j' => (i' = i ∧ s = t ∧ j' = j) ∨ Net.SlowSet N j (t + N.U i j) q i' s j'

namespace FData

variable {D : γ.FData r}

/-- The slow chain can be delivered after the auxiliary nodes. -/
theorem slowSet_ok (hr : γ.Valid r) :
    ∀ (q : List P) (i : P) (t : ℕ), γ.net.ChanPath i q →
      (∀ j q', q = j :: q' → (D.psi j : ℤ) ≤ t + γ.net.U i j) →
      ∀ i' s j', γ.net.SlowSet i t q i' s j' → (D.psi j' : ℤ) ≤ s + γ.net.U i' j'
  | [], _, _, _, _, _, _, _, h => h.elim
  | j :: q, i, t, hq, h0, i', s, j', h => by
    rcases h with ⟨rfl, rfl, rfl⟩ | h
    · exact h0 _ _ rfl
    · refine slowSet_ok hr q j (t + γ.net.U i j) hq.2 ?_ i' s j' h
      rintro k q' rfl
      have := psi_chan hr (D := D) hq.2.1
      have := h0 j _ rfl
      push_cast
      omega

/-- A message chain delivered at the upper bounds (rule 2). -/
theorem chain_slow (hr : γ.Valid r) (hD : D.Good) (hF : γ.IsFFIP) :
    ∀ (q : List P) {w : BNode P S M E}, γ.appears D.run w → 0 < γ.timer D.run w →
      γ.net.ChanPath w.1 q →
      (∀ j q', q = j :: q' → ¬ ∃ v, D.Rule1 w.1 (γ.timer D.run w) j v) →
      (∀ i' s j', γ.net.SlowSet w.1 (γ.timer D.run w) q i' s j' → D.Sl i' s j') →
      ∃ w', γ.gbasic D.run w q = some w' ∧
        γ.timer D.run w' = γ.timer D.run w + γ.net.Up w.1 q
  | [], w, hw, _, _, _, _ => ⟨w, γ.gbasic_self _ hw, by simp⟩
  | j :: q, w, hw, h0, hq, hR, hSl => by
    obtain ⟨w1, h1, hj, ht⟩ := hop hr hD hF hw h0 hq.1
    have hS : D.Sl w.1 (γ.timer D.run w) j := hSl _ _ _ (Or.inl ⟨rfl, rfl, rfl⟩)
    rw [dlv_not_rule1 hr hD (hR j q rfl)] at ht
    simp only [hS, ↓reduceIte] at ht
    have hs := recv_spec (run_valid hr hD hF) h1
    have hpsi := hD.Sl_ok _ _ _ hS
    have hU := γ.net.one_le_L _ _ hq.1
    have hLU := γ.net.L_le_U _ _ hq.1
    obtain ⟨w', hw', ht'⟩ := chain_slow hr hD hF q hs.2.1 (by omega) (hj ▸ hq.2)
      (fun k q' _ => no_rule1_of_psi_le hr hD (by rw [ht, hj]; omega))
      (fun i' s j' h => hSl i' s j' (Or.inr (by rw [ht, hj] at h; exact h)))
    refine ⟨w', by simp only [gbasic_cons, h1, Option.bind_some]; exact hw', ?_⟩
    rw [ht', ht, hj]
    simp only [Net.Up_cons]
    omega

end FData

end Sys

end Podc.ZigzagCausality
