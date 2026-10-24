import Papers.PODC2017.ZigzagCausality.FastRun

/-!
# The Visible Zigzag Theorem, direction (⇒), repaired — Theorem 4, Appendix C

Dan, Manohar, Moses, *On Using Time Without Clocks via Zigzag Causality*, PODC 2017.

The necessity direction of Theorem 4 is false in general (`Counterexample.lean`). We prove it in
the two cases needed for timed coordination (Theorem 5), for flooding full-information protocols:

* `visible_zigzag_necessity_early` — `θ₁ = σ₁` is a basic node of `past(r, σ)` and `θ₂` is any
  σ-recognized node (this covers `Early⟨b --x--> a⟩`, with `θ₁ = σ`, `θ₂ = σ_C · A`);
* `visible_zigzag_necessity_late` — `θ₂ = σ₂` is a basic node of `past(r, σ)` and `θ₁` is any
  σ-recognized node (this covers `Late⟨a --x--> b⟩`, with `θ₁ = σ_C · A`, `θ₂ = σ`);
* `visible_zigzag_necessity_basic` — both nodes are basic nodes of the past.

**Proof.** Instead of longest paths in the extended bounds graph `G_E(r, σ)` (Definition 16) we
use directly the *zigzag potential* `Dz v = max {wt(Z) | Z σ-visible zigzag from θ₁ ending at
v}` of the past nodes `v` (it is bounded by Theorem 1 in `r`; this replaces Lemmas 10–16, the
conversion of `G_E`-paths into zigzags). The fast timing (Definition 23) is
`T v = C + Dz v` for the nodes reachable from `θ₁` by such zigzags and `T v = timer_r(v)` for the
others, for a large constant `C`. Every constraint of `G_E(r, σ)` from a reachable node leads to a
reachable node (appending one fork to a zigzag: `zreach_recv`, `zreach_recv_back`,
`zreach_local`, `zreach_esc`), so `T` satisfies the constraints (`zT_good`), and the fast run
`FData.run` (Definition 24, Lemma 18) realizes it. In the fast run the arrival time of the chain
of the other node is computed explicitly (`FData.chain_first`, `FData.chain_slow`); each of its
possible values is the weight of a σ-visible zigzag (this is Lemma 18.5 in the cases where it is
correct), or else it is so small that the precedence fails in the fast run.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

namespace Sys

variable {γ : Sys P S M E} {r : Sched P S E} [Finite P]

/-! ### Appending a fork to a visible zigzag -/

/-- Appending a fork to a σ-visible zigzag pattern whose last head is in the past of `σ`. -/
theorem zigzag_snoc {σ v : BNode P S M E} {G : Fork P S M E} (hG : γ.ForkIn r G)
    (hroot : γ.HB r G.base.root σ) :
    ∀ {Z : List (Fork P S M E)} {θ₀ θ : GNode P S M E}, γ.IsZigzag r Z θ₀ θ →
      γ.Visible r σ Z → γ.basic r θ = some v → γ.HB r v σ → γ.Adj r θ G.tail →
      γ.IsZigzag r (Z ++ [G]) θ₀ G.head ∧ γ.Visible r σ (Z ++ [G]) ∧
        γ.wtZ r (Z ++ [G]) = γ.wtZ r Z + γ.gap r θ G.tail + G.wt γ.net
  | [], _, _, h, _, _, _, _ => h.elim
  | [F], θ₀, θ, ⟨hF, h1, h2⟩, _, hb, hv, hadj => by
    subst h1 h2
    exact ⟨⟨hF, rfl, hadj, hG, rfl, rfl⟩, ⟨⟨v, hb, hv⟩, hroot⟩, rfl⟩
  | F :: F' :: Z, θ₀, θ, ⟨hF, h1, hadj', hZ⟩, ⟨hh, hV'⟩, hb, hv, hadj => by
    obtain ⟨h1', h2', h3'⟩ := zigzag_snoc hG hroot hZ hV' hb hv hadj
    rw [show (F :: F' :: Z) ++ [G] = F :: F' :: (Z ++ [G]) from rfl]
    rw [show (F' :: Z) ++ [G] = F' :: (Z ++ [G]) from rfl] at h1' h2' h3'
    refine ⟨⟨hF, h1, hadj', h1'⟩, ⟨hh, h2'⟩, ?_⟩
    simp only [wtZ] at h3' ⊢
    rw [h3']
    ring

variable (γ r) in
/-- `v` (a node of the past of `σ`) is the end of a σ-visible zigzag pattern of weight `w` from
`θ₀`. -/
def ZReach (σ : BNode P S M E) (θ₀ : GNode P S M E) (v : BNode P S M E) (w : ℤ) : Prop :=
  ∃ Z θ, γ.IsZigzag r Z θ₀ θ ∧ γ.Visible r σ Z ∧ γ.basic r θ = some v ∧ γ.HB r v σ ∧
    γ.wtZ r Z = w

theorem ZReach.ext {σ v : BNode P S M E} {θ₀ : GNode P S M E} {w : ℤ}
    (h : γ.ZReach r σ θ₀ v w) {G : Fork P S M E} {τ v' : BNode P S M E} (hG : γ.ForkIn r G)
    (hroot : γ.HB r G.base.root σ) (ht : γ.basic r G.tail = some τ) (hp : v.1 = τ.1)
    (hle : γ.timer r v ≤ γ.timer r τ) (hh : γ.basic r G.head = some v') (hv' : γ.HB r v' σ) :
    γ.ZReach r σ θ₀ v' (w + (if v = τ then 0 else 1) + G.wt γ.net) := by
  obtain ⟨Z, θ, hZ, hV, hb, hv, rfl⟩ := h
  obtain ⟨h1, h2, h3⟩ := zigzag_snoc hG hroot hZ hV hb hv ⟨v, τ, hb, ht, hp, hle⟩
  refine ⟨Z ++ [G], G.head, h1, h2, hh, hv', ?_⟩
  rw [h3]
  simp only [gap, hb, ht, Option.some.injEq]

/-- The basic node of `⟨u, [j]⟩` is the receiver of the message. -/
theorem basic_single {u v : BNode P S M E} {j : P} (h : γ.recv r u j = some v) :
    γ.basic r ⟨u, [j]⟩ = some v := by
  have ha : γ.appears r v := ((γ.recv_eq_some r).1 h).2 ▸ γ.appears_st r _ _
  simp [basic, h, ha]

/-! ### Closure of the zigzag potential under the constraints of `G_E(r, σ)` -/

section Closure

variable (hr : γ.Valid r) {σ : BNode P S M E} {θ₀ : GNode P S M E}
include hr

/-- A message `u → v` inside the past: an `L`-edge (a fork `⟨u, u·j, u⟩`). -/
theorem zreach_recv {u v : BNode P S M E} {j : P} {w : ℤ} (h : γ.ZReach r σ θ₀ u w)
    (hrecv : γ.recv r u j = some v) (hv : γ.HB r v σ) :
    γ.ZReach r σ θ₀ v (w + γ.net.L u.1 j) := by
  have hu := (recv_appears_left hrecv).1
  have hb : γ.basic r (GNode.ofB u) = some u := γ.basic_ofB r hu
  have h' := h.ext (G := ⟨GNode.ofB u, [j], []⟩) (τ := u) (v' := v)
    ⟨by simp [Fork.head, GNode.ext, GNode.ofB, appearsG, basic_single hrecv],
      by simp [Fork.tail, appearsG, hb]⟩
    ((HB.of_recv hrecv).trans hv) (by simpa [Fork.tail] using hb) rfl le_rfl
    (by simpa [Fork.head, GNode.ext, GNode.ofB] using basic_single hrecv) hv
  simpa [Fork.wt, GNode.ofB, GNode.proc] using h'

/-- A message `u → v` inside the past: a `−U`-edge (a fork `⟨u, u, u·j⟩`). -/
theorem zreach_recv_back {u v : BNode P S M E} {j : P} {w : ℤ} (h : γ.ZReach r σ θ₀ v w)
    (hrecv : γ.recv r u j = some v) (hv : γ.HB r v σ) :
    γ.ZReach r σ θ₀ u (w - γ.net.U u.1 j) := by
  have hu := (recv_appears_left hrecv).1
  have hb : γ.basic r (GNode.ofB u) = some u := γ.basic_ofB r hu
  have h' := h.ext (G := ⟨GNode.ofB u, [], [j]⟩) (τ := v) (v' := u)
    ⟨by simp [Fork.head, appearsG, hb],
      by simp [Fork.tail, GNode.ext, GNode.ofB, appearsG, basic_single hrecv]⟩
    ((HB.of_recv hrecv).trans hv)
    (by simpa [Fork.tail, GNode.ext, GNode.ofB] using basic_single hrecv) rfl le_rfl
    (by simpa [Fork.head] using hb) ((HB.of_recv hrecv).trans hv)
  simp only [ite_true, add_zero, Fork.wt, GNode.ofB, GNode.proc, lastP_nil, Net.Lp_nil,
    Net.Up_cons, Net.Up_nil, Nat.cast_zero, zero_sub] at h'
  convert h' using 1
  ring

/-- Successive past nodes of a process: a `1`-edge (a trivial fork at the later node). -/
theorem zreach_local {u v : BNode P S M E} {w : ℤ} (h : γ.ZReach r σ θ₀ u w)
    (hv : γ.HB r v σ) (hp : u.1 = v.1) (hlt : γ.timer r u < γ.timer r v) :
    γ.ZReach r σ θ₀ v (w + 1) := by
  have hva := (HB.appears hv).1
  have hb : γ.basic r (GNode.ofB v) = some v := γ.basic_ofB r hva
  have hne : u ≠ v := by rintro rfl; omega
  have h' := h.ext (G := Fork.triv (GNode.ofB v)) (τ := v) (v' := v)
    ⟨by simp [appearsG, hb], by simp [appearsG, hb]⟩ hv
    (by simpa using hb) hp hlt.le (by simpa using hb) hv
  simpa [hne] using h'

/-- A message from a past node `u` to `j` that leaves the past, followed by a channel path `q`
from `j` to the process of a past node `b`: the path `b → ψ_{b.1} → … → ψ_j → u` of `G_E(r, σ)`
(a fork `⟨u, u, u·(j·q)⟩` not joined with `b`). -/
theorem zreach_esc (hF : γ.IsFFIP) {u b w₁ : BNode P S M E} {j : P} {q : List P} {w : ℤ}
    (h : γ.ZReach r σ θ₀ b w) (hu : γ.HB r u σ) (hrecv : γ.recv r u j = some w₁)
    (hn : ¬ γ.HB r w₁ σ) (hq : γ.net.ChanPath j q) (hl : b.1 = lastP j q) (hb : γ.HB r b σ) :
    γ.ZReach r σ θ₀ u (w + 1 - γ.net.Up u.1 (j :: q)) := by
  have hua := (HB.appears hu).1
  have hbu : γ.basic r (GNode.ofB u) = some u := γ.basic_ofB r hua
  have hs := recv_spec hr hrecv
  have hL := γ.net.one_le_L _ _ hs.2.2.1
  obtain ⟨z, hz, -⟩ := flood_chain hF hr q hs.2.1 (by omega) (hs.1 ▸ hq)
  have hzn : ¬ γ.HB r z σ := fun hz' => hn ((HB.of_gbasic hz).trans hz')
  have hzp : z.1 = b.1 := by rw [γ.gbasic_proc r hz, hs.1, hl]
  have hza := (γ.gbasic_appears r hz).2
  have hlt := timer_lt_of_not_past hb hza hzn hzp
  have htail : γ.basic r ⟨u, j :: q⟩ = some z := by
    simp only [basic, gbasic_cons, hrecv, Option.bind_some]; exact hz
  have hne : b ≠ z := fun e => hzn (e ▸ hb)
  have h' := h.ext (G := ⟨GNode.ofB u, [], j :: q⟩) (τ := z) (v' := u)
    ⟨by simp [Fork.head, appearsG, hbu],
      by simp [Fork.tail, GNode.ext, GNode.ofB, appearsG, htail]⟩ hu
    (by simpa [Fork.tail, GNode.ext, GNode.ofB] using htail) hzp.symm hlt.le
    (by simpa [Fork.head] using hbu) hu
  simp only [hne, ite_false, Fork.wt, GNode.ofB, GNode.proc, lastP_nil, Net.Lp_nil,
    Nat.cast_zero, zero_sub] at h'
  convert h' using 1
  ring

end Closure

/-! ### The zigzag potential and the fast timing -/

variable (γ r) in
/-- The zigzag potential: the largest weight of a σ-visible zigzag from `θ₀` ending at `v`. -/
noncomputable def Dz (σ : BNode P S M E) (θ₀ : GNode P S M E) (v : BNode P S M E) : ℤ :=
  sSup {w | γ.ZReach r σ θ₀ v w}

section Potential

variable (hr : γ.Valid r) {σ : BNode P S M E} {θ₀ : GNode P S M E}
include hr

theorem ZReach.le_timer {v : BNode P S M E} {w : ℤ} (h : γ.ZReach r σ θ₀ v w) :
    w ≤ γ.timer r v := by
  obtain ⟨Z, θ, hZ, -, hb, -, rfl⟩ := h
  obtain ⟨a, b, -, hb', hab⟩ := zigzag_sufficiency hr hZ
  rw [hb] at hb'
  cases hb'
  omega

theorem zreach_bdd (v : BNode P S M E) : BddAbove {w | γ.ZReach r σ θ₀ v w} :=
  ⟨γ.timer r v, fun _ h => h.le_timer hr⟩

theorem le_Dz {v : BNode P S M E} {w : ℤ} (h : γ.ZReach r σ θ₀ v w) : w ≤ γ.Dz r σ θ₀ v :=
  le_csSup (zreach_bdd hr v) h

theorem zreach_Dz {v : BNode P S M E} {w : ℤ} (h : γ.ZReach r σ θ₀ v w) :
    γ.ZReach r σ θ₀ v (γ.Dz r σ θ₀ v) :=
  Int.csSup_mem ⟨w, h⟩ (zreach_bdd hr v)

/-- The potential is bounded below on the (finite) past. -/
theorem Dz_bddBelow : ∃ m, ∀ v, γ.HB r v σ → m ≤ γ.Dz r σ θ₀ v := by
  obtain ⟨m, hm⟩ := ((past_finite hr σ).image (γ.Dz r σ θ₀)).bddBelow
  exact ⟨m, fun v hv => hm ⟨v, hv, rfl⟩⟩

end Potential

variable (γ r) in
/-- The fast timing (Definition 23, simplified): `C + Dz v` for the nodes reachable from `θ₀` by
σ-visible zigzags, `timer_r(v)` for the others. -/
noncomputable def zT (σ : BNode P S M E) (θ₀ : GNode P S M E) (C : ℤ) (v : BNode P S M E) : ℕ :=
  if ∃ w, γ.ZReach r σ θ₀ v w then (C + γ.Dz r σ θ₀ v).toNat else γ.timer r v

variable (γ r) in
/-- The data of the fast run with the fast timing. -/
noncomputable abbrev zD (σ : BNode P S M E) (θ₀ : GNode P S M E) (C : ℤ) (Sl : P → ℕ → P → Prop) :
    γ.FData r :=
  ⟨σ, γ.zT r σ θ₀ C, Sl⟩

@[simp] theorem zD_T (σ : BNode P S M E) (θ₀ : GNode P S M E) (C : ℤ)
    (Sl : P → ℕ → P → Prop) : (γ.zD r σ θ₀ C Sl).T = γ.zT r σ θ₀ C := rfl

section Timing

variable (hr : γ.Valid r) (hF : γ.IsFFIP) {σ : BNode P S M E} {θ₀ : GNode P S M E} {C : ℤ}
  (hC : ∀ v, γ.HB r v σ → 2 * (γ.timer r σ : ℤ) + 1 ≤ C + γ.Dz r σ θ₀ v)
include hr hC

theorem zT_reach {v : BNode P S M E} (hv : γ.HB r v σ) (h : ∃ w, γ.ZReach r σ θ₀ v w) :
    (γ.zT r σ θ₀ C v : ℤ) = C + γ.Dz r σ θ₀ v := by
  have := hC v hv
  simp only [zT, h, ↓reduceIte]
  omega

theorem zT_cases {v : BNode P S M E} (hv : γ.HB r v σ) :
    ((∃ w, γ.ZReach r σ θ₀ v w) ∧ (γ.zT r σ θ₀ C v : ℤ) = C + γ.Dz r σ θ₀ v ∧
      2 * (γ.timer r σ : ℤ) + 1 ≤ γ.zT r σ θ₀ C v) ∨
    ((¬ ∃ w, γ.ZReach r σ θ₀ v w) ∧ γ.zT r σ θ₀ C v = γ.timer r v ∧
      γ.timer r v ≤ γ.timer r σ) := by
  by_cases h : ∃ w, γ.ZReach r σ θ₀ v w
  · have e := zT_reach hr hC hv h
    exact Or.inl ⟨h, e, e ▸ hC v hv⟩
  · exact Or.inr ⟨h, by simp only [zT, h, ↓reduceIte], HB.timer_le hr hv⟩

include hF in
/-- The fast timing satisfies the constraints of `G_E(r, σ)` (Lemma 17). -/
theorem zT_good (Sl : P → ℕ → P → Prop)
    (hSl : ∀ i s j, Sl i s j → ((γ.zD r σ θ₀ C Sl).psi j : ℤ) ≤ s + γ.net.U i j) :
    (γ.zD r σ θ₀ C Sl).Good where
  T_pos v hv := by
    have hv1 : γ.HB r v σ := hv.1
    show 0 < γ.zT r σ θ₀ C v
    rcases zT_cases hr hC hv1 with ⟨-, -, h⟩ | ⟨-, h, -⟩
    · omega
    · rw [h]; exact hv.2
  T_recv u v j hv' hrecv := by
    have hv : γ.HB r v σ ∧ 0 < γ.timer r v := hv'
    have hu : γ.HB r u σ := (HB.of_recv hrecv).trans hv.1
    have hs := recv_spec hr hrecv
    have hσv := HB.timer_le hr hv.1
    show γ.zT r σ θ₀ C u + _ ≤ γ.zT r σ θ₀ C v ∧ γ.zT r σ θ₀ C v ≤ γ.zT r σ θ₀ C u + _
    rcases zT_cases hr hC hu with ⟨hru, eu, -⟩ | ⟨hru, eu, -⟩
    · obtain ⟨w, hw⟩ := hru
      have h1 := le_Dz hr (zreach_recv hr (zreach_Dz hr hw) hrecv hv.1)
      rcases zT_cases hr hC hv.1 with ⟨hrv, ev, -⟩ | ⟨hrv, -, -⟩
      · obtain ⟨w', hw'⟩ := hrv
        have h2 := le_Dz hr (zreach_recv_back hr (zreach_Dz hr hw') hrecv hv.1)
        constructor <;> zify <;> omega
      · exact absurd ⟨_, zreach_recv hr (zreach_Dz hr hw) hrecv hv.1⟩ hrv
    · rcases zT_cases hr hC hv.1 with ⟨hrv, ev, hbig⟩ | ⟨-, ev, -⟩
      · obtain ⟨w', hw'⟩ := hrv
        exact absurd ⟨_, zreach_recv_back hr (zreach_Dz hr hw') hrecv hv.1⟩ hru
      · rw [eu, ev]; omega
  T_mono u v hu' hv' hp hlt := by
    have hv : γ.HB r v σ ∧ 0 < γ.timer r v := hv'
    have hu : γ.HB r u σ ∧ 0 < γ.timer r u := hu'
    have hσv := HB.timer_le hr hv.1
    have hσu := HB.timer_le hr hu.1
    show γ.zT r σ θ₀ C u < γ.zT r σ θ₀ C v
    rcases zT_cases hr hC hu.1 with ⟨⟨w, hw⟩, eu, -⟩ | ⟨-, eu, -⟩
    · have hr' := zreach_local hr (zreach_Dz hr hw) hv.1 hp hlt
      have := le_Dz hr hr'
      have ev := zT_reach hr hC hv.1 ⟨_, hr'⟩
      zify; omega
    · rcases zT_cases hr hC hv.1 with ⟨-, -, hbig⟩ | ⟨-, ev, -⟩
      · zify; omega
      · rw [eu, ev]; exact hlt
  T_esc u j w₁ q b hu' hrecv hn' hq hb' hl := by
    have hu : γ.HB r u σ ∧ 0 < γ.timer r u := hu'
    have hb : γ.HB r b σ ∧ 0 < γ.timer r b := hb'
    have hn : ¬ γ.HB r w₁ σ := hn'
    show (γ.zT r σ θ₀ C b : ℤ) + 1 ≤ γ.zT r σ θ₀ C u + _ + _
    have hσu := HB.timer_le hr hu.1
    rcases zT_cases hr hC hb.1 with ⟨⟨w, hw⟩, eb, -⟩ | ⟨-, eb, hbM⟩
    · have hr' := zreach_esc hr hF (zreach_Dz hr hw) hu.1 hrecv hn hq hl hb.1
      have := le_Dz hr hr'
      have eu := zT_reach hr hC hu.1 ⟨_, hr'⟩
      simp only [Net.Up_cons, Nat.cast_add] at this
      omega
    · rw [eb]
      rcases zT_cases hr hC hu.1 with ⟨-, -, hbig⟩ | ⟨-, eu, -⟩
      · have : (0 : ℤ) ≤ γ.net.U u.1 j + γ.net.Up j q := by positivity
        omega
      · rw [eu]
        have hs := recv_spec hr hrecv
        have hL := γ.net.one_le_L _ _ hs.2.2.1
        obtain ⟨z, hz, -⟩ := flood_chain hF hr q hs.2.1 (by omega) (hs.1 ▸ hq)
        have hzn : ¬ γ.HB r z σ := fun hz' => hn ((HB.of_gbasic hz).trans hz')
        have hzp : z.1 = b.1 := by rw [γ.gbasic_proc r hz, hs.1, hl]
        have hlt := timer_lt_of_not_past hb.1 (γ.gbasic_appears r hz).2 hzn hzp
        have hchain : γ.gbasic r u (j :: q) = some z := by
          simp only [gbasic_cons, hrecv, Option.bind_some]; exact hz
        have := (gbasic_timer hr hchain).2
        simp only [Net.Up_cons] at this
        omega
  Sl_ok := hSl

end Timing

/-! ### Proof of Theorem 4 (⇒) in the repaired cases -/

/-- Splitting a message chain from the past of `σ` at its last node in the past. -/
theorem past_split {σ : BNode P S M E} :
    ∀ (p : List P) {ρ z : BNode P S M E}, γ.HB r ρ σ → γ.gbasic r ρ p = some z →
      γ.HB r z σ ∨ ∃ p' j q a w, p = p' ++ j :: q ∧ γ.gbasic r ρ p' = some a ∧
        γ.HB r a σ ∧ γ.recv r a j = some w ∧ ¬ γ.HB r w σ
  | [], ρ, z, hρ, h => by
    simp only [gbasic_nil] at h
    split_ifs at h
    cases h
    exact Or.inl hρ
  | j :: q, ρ, z, hρ, h => by
    simp only [gbasic_cons] at h
    obtain ⟨ρ1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    by_cases hp1 : γ.HB r ρ1 σ
    · rcases past_split q hp1 h2 with hz | ⟨p', j', q', a, w, rfl, ha, haσ, hw, hn⟩
      · exact Or.inl hz
      · refine Or.inr ⟨j :: p', j', q', a, w, rfl, ?_, haσ, hw, hn⟩
        simp only [gbasic_cons, h1, Option.bind_some]
        exact ha
    · exact Or.inr ⟨[], j, q, ρ, ρ1, rfl, γ.gbasic_self r (HB.appears hρ).1, hρ, h1, hp1⟩

theorem exists_C (hr : γ.Valid r) (σ : BNode P S M E) (θ₀ : GNode P S M E) (K : ℕ) :
    ∃ C : ℤ, ∀ v, γ.HB r v σ → 2 * (γ.timer r σ : ℤ) + 1 + K ≤ C + γ.Dz r σ θ₀ v := by
  obtain ⟨m, hm⟩ := Dz_bddBelow hr (σ := σ) (θ₀ := θ₀)
  exact ⟨2 * γ.timer r σ + 1 + K - m, fun v hv => by have := hm v hv; omega⟩

theorem exists_basic_of_timerG {θ : GNode P S M E} (h : 0 < γ.timerG r θ) :
    ∃ z, γ.basic r θ = some z ∧ 0 < γ.timer r z := by
  rcases e : γ.basic r θ with _ | z
  · simp [timerG, e] at h
  · exact ⟨z, rfl, by rwa [γ.timerG_of_basic r e] at h⟩

/-- The trivial zigzag pattern `(⟨θ, θ, θ⟩)`. -/
theorem zreach_triv {σ z : BNode P S M E} {θ : GNode P S M E} (hθ : γ.HB r θ.root σ)
    (hz : γ.basic r θ = some z) (hzσ : γ.HB r z σ) : γ.ZReach r σ θ z 0 :=
  ⟨[Fork.triv θ], θ, ⟨by simp [ForkIn, appearsG, hz], by simp, by simp⟩, hθ, hz, hzσ,
    by simp [wtZ]⟩

/-- The end of the proof for `θ₂ = σ₂` basic: either `σ₂` is reachable by a visible zigzag from
`θ₁` with weight at least `x`, or the precedence fails in the fast run. -/
theorem late_finish (hr : γ.Valid r) {σ σ₂ a : BNode P S M E}
    {θ₁ : GNode P S M E} {x w₀ C : ℤ} {Sl : P → ℕ → P → Prop}
    (hC : ∀ v, γ.HB r v σ → 2 * (γ.timer r σ : ℤ) + 1 + x.natAbs ≤ C + γ.Dz r σ θ₁ v)
    (hD : (γ.zD r σ θ₁ C Sl).Good) (ha : γ.HB r a σ) (hseed : γ.ZReach r σ θ₁ a w₀)
    (hw₀ : w₀ ≤ 0) (h₂ : γ.HB r σ₂ σ) {s₁ : BNode P S M E}
    (hs₁ : γ.basic (γ.zD r σ θ₁ C Sl).run θ₁ = some s₁)
    (ht₁ : (γ.timer (γ.zD r σ θ₁ C Sl).run s₁ : ℤ) = γ.zT r σ θ₁ C a - w₀)
    (hprec : γ.Prec (γ.zD r σ θ₁ C Sl).run θ₁ x (GNode.ofB σ₂)) :
    ∃ Z, γ.IsZigzag r Z θ₁ (GNode.ofB σ₂) ∧ γ.Visible r σ Z ∧ x ≤ γ.wtZ r Z := by
  have hC0 : ∀ v, γ.HB r v σ → 2 * (γ.timer r σ : ℤ) + 1 ≤ C + γ.Dz r σ θ₁ v :=
    fun v hv => by have := hC v hv; omega
  obtain ⟨s₁', s₂, e₁, e₂, hle⟩ := hprec
  rw [hs₁] at e₁
  cases e₁
  have h₂' := FData.appears_run hr hD h₂
  rw [γ.basic_ofB _ h₂'] at e₂
  cases e₂
  have eA := zT_reach hr hC0 ha ⟨_, hseed⟩
  have hA := hC a ha
  have hDa := le_Dz hr hseed
  have hx : -x ≤ (x.natAbs : ℤ) := by omega
  by_cases hpos : 0 < γ.timer r σ₂
  · have e2 := FData.timer_run hr hD (D := γ.zD r σ θ₁ C Sl) ⟨h₂, hpos⟩
    rcases zT_cases hr hC0 h₂ with ⟨⟨w, hw⟩, e, -⟩ | ⟨-, e, hM⟩
    · obtain ⟨Z, θ, hZ, hV, hb, hv, hwt⟩ := zreach_Dz hr hw
      have hb2 : γ.basic r (GNode.ofB σ₂) = some σ₂ := γ.basic_ofB r (HB.appears h₂).1
      obtain ⟨h1, h2, h3⟩ := zigzag_snoc (G := Fork.triv (GNode.ofB σ₂))
        (by simp [ForkIn, appearsG, hb2]) h₂ hZ hV hb hv
        ⟨σ₂, σ₂, hb, by simpa using hb2, rfl, le_rfl⟩
      refine ⟨Z ++ [Fork.triv (GNode.ofB σ₂)], by simpa using h1, h2, ?_⟩
      rw [h3, hwt]
      simp only [gap, hb, Fork.triv_tail, hb2, ↓reduceIte, Fork.triv_wt, add_zero]
      rw [e2] at hle
      push_cast at hle
      omega
    · rw [e2] at hle
      push_cast at hle
      omega
  · rw [FData.timer_run_init hr hD h₂ (by omega)] at hle
    push_cast at hle
    omega

/-- **Theorem 4 (Visible Zigzag Theorem), direction (⇒), for `θ₂` a basic node of the past.**
Let `P` be an FFIP, `σ` a basic node of `r ∈ R(P, γ)`, `θ₁` a σ-recognized node with
`timer_r(θ₁) > 0` and `σ₂ ⇝_r σ`. If `(R, r) ⊨ K_σ(θ₁ --x--> σ₂)`, then there is a σ-visible
zigzag pattern `Z` from `θ₁` to `σ₂` in `r` with `wt(Z) ≥ x`. (This covers `Late⟨a --x--> b⟩`
with `θ₁ = σ_C · A` and `σ₂ = σ`.)

The paper's proof (Lemma 18.5) assumes that the chain of `θ₁` leaves the past of `σ` at its root;
here it may leave the past later (the zigzag then starts with the fork
`⟨⟨σ₁, p'⟩, ⟨σ₁, p'⟩, θ₁⟩`, where `⟨σ₁, p'⟩` is the last node of the chain in the past). -/
theorem visible_zigzag_necessity_late (hF : γ.IsFFIP) (hr : γ.Valid r) {σ σ₂ : BNode P S M E}
    {θ₁ : GNode P S M E} {x : ℤ} (h₁ : γ.Recognized r σ θ₁) (h₁0 : 0 < γ.timerG r θ₁)
    (h₂ : γ.HB r σ₂ σ) (hK : γ.Knows σ (fun r' => γ.Prec r' θ₁ x (GNode.ofB σ₂))) :
    ∃ Z, γ.IsZigzag r Z θ₁ (GNode.ofB σ₂) ∧ γ.Visible r σ Z ∧ x ≤ γ.wtZ r Z := by
  obtain ⟨ρ, p⟩ := θ₁
  have hρ : γ.HB r ρ σ := h₁
  obtain ⟨z, hz, hz0⟩ := exists_basic_of_timerG h₁0
  have hσ := (HB.appears h₂).2
  obtain ⟨C, hC⟩ := exists_C hr σ ⟨ρ, p⟩ x.natAbs
  have hC0 : ∀ v, γ.HB r v σ → 2 * (γ.timer r σ : ℤ) + 1 ≤ C + γ.Dz r σ ⟨ρ, p⟩ v :=
    fun v hv => by have := hC v hv; omega
  have hD₀ := zT_good hr hF hC0 (fun _ _ _ => False) (fun _ _ _ h => h.elim)
  rcases past_split p hρ hz with hzσ | ⟨p', j, q, a, w, rfl, ha, haσ, hw, hn⟩
  · -- the node `θ₁` itself is in the past of `σ`
    have hr' := FData.run_valid hr hD₀ hF
    have hσ' := FData.appears_run hr hD₀ (HB.refl hσ)
    obtain ⟨υ, hυ, e, -⟩ := basic_transfer hF hr hr' hσ' hρ hz
    rw [e hzσ] at hυ
    exact late_finish hr hC hD₀ hzσ (zreach_triv hρ hz hzσ) le_rfl h₂ hυ
      (by rw [FData.timer_run hr hD₀ ⟨hzσ, hz0⟩]; simp) (hK _ hr' hσ')
  · -- the chain of `θ₁` leaves the past of `σ` after its last past node `a`
    have hza : γ.gbasic r a (j :: q) = some z := by
      have : γ.gbasic r ρ (p' ++ j :: q) = some z := hz
      rwa [gbasic_append, ha, Option.bind_some] at this
    have hchan := gbasic_chanPath hr hza
    have hapos : 0 < γ.timer r a := (recv_appears_left hw).2
    have hproc : (⟨ρ, p'⟩ : GNode P S M E).proc = a.1 := (γ.gbasic_proc r ha).symm
    -- the seed: the fork `⟨⟨ρ, p'⟩, ⟨ρ, p'⟩, θ₁⟩`
    have hb0 : γ.basic r ⟨ρ, p'⟩ = some a := ha
    have hhead : γ.basic r (GNode.ext ⟨ρ, p'⟩ []) = some a := by
      simp only [GNode.ext_nil]; exact hb0
    have hseed : γ.ZReach r σ ⟨ρ, p' ++ j :: q⟩ a (-(γ.net.Up a.1 (j :: q) : ℤ)) := by
      refine ⟨[⟨⟨ρ, p'⟩, [], j :: q⟩], GNode.ext ⟨ρ, p'⟩ [],
        ⟨⟨by simp [Fork.head, appearsG, hb0], by simp [Fork.tail, GNode.ext, appearsG, hz]⟩,
          rfl, rfl⟩, hρ, hhead, haσ, ?_⟩
      simp [wtZ, Fork.wt, hproc]
    set Sl := γ.net.SlowSet a.1 (γ.zT r σ ⟨ρ, p' ++ j :: q⟩ C a) (j :: q) with hSldef
    have hSl : ∀ i s j', Sl i s j' →
        ((γ.zD r σ ⟨ρ, p' ++ j :: q⟩ C Sl).psi j' : ℤ) ≤ s + γ.net.U i j' :=
      FData.slowSet_ok hr (D := γ.zD r σ ⟨ρ, p' ++ j :: q⟩ C (fun _ _ _ => False)) (j :: q) a.1 _
        hchan (fun j' q' h => by
          cases h
          exact FData.psi_le_esc hr hD₀ ⟨haσ, hapos⟩ hw hn)
    have hD := zT_good hr hF hC0 Sl hSl
    have hr' := FData.run_valid hr hD hF
    have hσ' := FData.appears_run hr hD (HB.refl hσ)
    obtain ⟨υ, hυ, e, -⟩ := basic_transfer hF hr hr' hσ' (θ := ⟨ρ, p'⟩) hρ ha
    rw [e haσ] at hυ
    have hta := FData.timer_run hr hD (D := γ.zD r σ ⟨ρ, p' ++ j :: q⟩ C Sl) ⟨haσ, hapos⟩
    obtain ⟨w', hw', ht'⟩ := FData.chain_slow hr hD hF (j :: q) (w := a)
      (FData.appears_run hr hD haσ) (by rw [hta]; exact hD.T_pos a ⟨haσ, hapos⟩) hchan
      (fun j' q' h => by
        cases h
        rw [hta]
        exact FData.no_rule1_esc hr hD ⟨haσ, hapos⟩ hw hn)
      (fun i s j' h => by rw [hta] at h; exact h)
    have hb1 : γ.basic (γ.zD r σ ⟨ρ, p' ++ j :: q⟩ C Sl).run ⟨ρ, p' ++ j :: q⟩ = some w' := by
      have : γ.gbasic (γ.zD r σ ⟨ρ, p' ++ j :: q⟩ C Sl).run ρ p' = some a := hυ
      show γ.gbasic _ ρ (p' ++ j :: q) = some w'
      rw [gbasic_append, this, Option.bind_some]
      exact hw'
    refine late_finish hr hC hD haσ hseed (by simp) h₂ hb1 ?_ (hK _ hr' hσ')
    rw [ht', hta]
    simp only [Net.Up_cons]
    push_cast
    ring

/-- **Theorem 4 (⇒) for basic nodes of the past.** If `σ₁, σ₂ ⇝_r σ`, `σ₁` is not initial and
`(R, r) ⊨ K_σ(σ₁ --x--> σ₂)`, then there is a σ-visible zigzag pattern from `σ₁` to `σ₂` in `r`
with weight at least `x`. -/
theorem visible_zigzag_necessity_basic (hF : γ.IsFFIP) (hr : γ.Valid r)
    {σ σ₁ σ₂ : BNode P S M E} {x : ℤ} (h₁ : γ.HB r σ₁ σ) (h₁0 : 0 < γ.timer r σ₁)
    (h₂ : γ.HB r σ₂ σ)
    (hK : γ.Knows σ (fun r' => γ.Prec r' (GNode.ofB σ₁) x (GNode.ofB σ₂))) :
    ∃ Z, γ.IsZigzag r Z (GNode.ofB σ₁) (GNode.ofB σ₂) ∧ γ.Visible r σ Z ∧ x ≤ γ.wtZ r Z :=
  visible_zigzag_necessity_late hF hr h₁
    (by rwa [γ.timerG_of_basic r (γ.basic_ofB r (HB.appears h₁).1)]) h₂ hK

/-- **Theorem 4 (Visible Zigzag Theorem), direction (⇒), for `θ₁` a basic node of the past.**
Let `P` be an FFIP, `σ` a basic node of `r ∈ R(P, γ)`, `σ₁ ⇝_r σ` a non-initial node and `θ₂` a
σ-recognized node with `timer_r(θ₂) > 0`. If `(R, r) ⊨ K_σ(σ₁ --x--> θ₂)`, then there is a
σ-visible zigzag pattern `Z` from `σ₁` to `θ₂` in `r` with `wt(Z) ≥ x`. (This covers
`Early⟨b --x--> a⟩` with `σ₁ = σ` and `θ₂ = σ_C · A`.) -/
theorem visible_zigzag_necessity_early (hF : γ.IsFFIP) (hr : γ.Valid r)
    {σ σ₁ : BNode P S M E} {θ₂ : GNode P S M E} {x : ℤ} (h₁ : γ.HB r σ₁ σ)
    (h₁0 : 0 < γ.timer r σ₁) (h₂ : γ.Recognized r σ θ₂) (h₂0 : 0 < γ.timerG r θ₂)
    (hK : γ.Knows σ (fun r' => γ.Prec r' (GNode.ofB σ₁) x θ₂)) :
    ∃ Z, γ.IsZigzag r Z (GNode.ofB σ₁) θ₂ ∧ γ.Visible r σ Z ∧ x ≤ γ.wtZ r Z := by
  obtain ⟨ρ, p⟩ := θ₂
  have hρ : γ.HB r ρ σ := h₂
  obtain ⟨z, hz, hz0⟩ := exists_basic_of_timerG h₂0
  have hσ := (HB.appears h₁).2
  have hb1 : γ.basic r (GNode.ofB σ₁) = some σ₁ := γ.basic_ofB r (HB.appears h₁).1
  have hseed : γ.ZReach r σ (GNode.ofB σ₁) σ₁ 0 := zreach_triv h₁ hb1 h₁
  obtain ⟨C, hC⟩ := exists_C hr σ (GNode.ofB σ₁) (x.natAbs + γ.net.Lp ρ.1 p + 1)
  have hC0 : ∀ v, γ.HB r v σ → 2 * (γ.timer r σ : ℤ) + 1 ≤ C + γ.Dz r σ (GNode.ofB σ₁) v :=
    fun v hv => by have := hC v hv; omega
  have hD := zT_good hr hF hC0 (fun _ _ _ => False) (fun _ _ _ h => h.elim)
  have hr' := FData.run_valid hr hD hF
  have hσ' := FData.appears_run hr hD (HB.refl hσ)
  obtain ⟨s₁, s₂, e₁, e₂, hle⟩ := hK _ hr' hσ'
  rw [γ.basic_ofB _ (FData.appears_run hr hD h₁)] at e₁
  cases e₁
  rw [FData.timer_run hr hD ⟨h₁, h₁0⟩] at hle
  simp only at hle
  have e1 := zT_reach hr hC0 h₁ ⟨_, hseed⟩
  have hA := hC σ₁ h₁
  have hD1 := le_Dz hr hseed
  have hx : -x ≤ (x.natAbs : ℤ) := by omega
  have hσM := HB.timer_le hr h₁
  rcases past_split p hρ hz with hzσ | ⟨p', j, q, a, w, rfl, ha, haσ, hw, hn⟩
  · -- the node `θ₂` itself is in the past of `σ`
    obtain ⟨υ, hυ, e, -⟩ := basic_transfer hF hr hr' hσ' hρ hz
    rw [e hzσ, e₂] at hυ
    cases hυ
    rw [FData.timer_run hr hD ⟨hzσ, hz0⟩] at hle
    simp only at hle
    rcases zT_cases hr hC0 hzσ with ⟨⟨w0, hw0⟩, ez, -⟩ | ⟨-, ez, hzM⟩
    · obtain ⟨Z, θ, hZ, hV, hb, hv, hwt⟩ := zreach_Dz hr hw0
      obtain ⟨h1, h2, h3⟩ := zigzag_snoc (G := Fork.triv ⟨ρ, p⟩)
        (by simp [ForkIn, appearsG, hz]) hρ hZ hV hb hv ⟨z, z, hb, by simpa using hz, rfl, le_rfl⟩
      refine ⟨Z ++ [Fork.triv ⟨ρ, p⟩], by simpa using h1, h2, ?_⟩
      rw [h3, hwt]
      simp only [gap, hb, Fork.triv_tail, hz, ↓reduceIte, Fork.triv_wt, add_zero]
      omega
    · rw [ez] at hle
      have : (0 : ℤ) ≤ γ.net.Lp ρ.1 p := by positivity
      omega
  · -- the chain of `θ₂` leaves the past of `σ` after its last past node `a`
    have hza : γ.gbasic r a (j :: q) = some z := by
      have : γ.gbasic r ρ (p' ++ j :: q) = some z := hz
      rwa [gbasic_append, ha, Option.bind_some] at this
    have hchan := gbasic_chanPath hr hza
    have hapos : 0 < γ.timer r a := (recv_appears_left hw).2
    have hlastP : lastP ρ.1 p' = a.1 := (γ.gbasic_proc r ha).symm
    have hLp : γ.net.Lp ρ.1 (p' ++ j :: q) = γ.net.Lp ρ.1 p' + γ.net.Lp a.1 (j :: q) := by
      rw [Net.Lp_append, hlastP]
    have hb0 : γ.basic r ⟨ρ, p'⟩ = some a := ha
    obtain ⟨υ, hυ, e, -⟩ := basic_transfer hF hr hr' hσ' (θ := ⟨ρ, p'⟩) hρ ha
    rw [e haσ] at hυ
    obtain ⟨w', hw', ht'⟩ := FData.chain_first hr hD hF (fun _ _ _ h => h) ⟨haσ, hapos⟩ hw hn
      hchan.2
    have hb2 : γ.basic (γ.zD r σ (GNode.ofB σ₁) C (fun _ _ _ => False)).run
        ⟨ρ, p' ++ j :: q⟩ = some w' := by
      have : γ.gbasic (γ.zD r σ (GNode.ofB σ₁) C (fun _ _ _ => False)).run ρ p' = some a := hυ
      show γ.gbasic _ ρ (p' ++ j :: q) = some w'
      rw [gbasic_append, this, Option.bind_some]
      exact hw'
    rw [hb2] at e₂
    cases e₂
    rw [ht'] at hle
    simp only at hle
    rcases FData.fwd_cases (D := γ.zD r σ (GNode.ofB σ₁) C (fun _ _ _ => False)) _ a.1 (j :: q)
      with hf | ⟨q₁, q₂, hsplit, hne, hf⟩
    · -- every message after `a` is delivered at its lower bound
      rw [hf] at hle
      push_cast at hle
      rcases zT_cases hr hC0 haσ with ⟨⟨w0, hw0⟩, ea, -⟩ | ⟨-, ea, haM⟩
      · obtain ⟨Z, θ, hZ, hV, hb, hv, hwt⟩ := zreach_Dz hr hw0
        have htl : γ.basic r (GNode.ext ⟨ρ, p'⟩ []) = some a := by
          simp only [GNode.ext_nil]; exact hb0
        obtain ⟨h1, h2, h3⟩ := zigzag_snoc (G := ⟨⟨ρ, p'⟩, j :: q, []⟩)
          ⟨by simp [Fork.head, GNode.ext, appearsG, hz], by simp [Fork.tail, appearsG, hb0]⟩ hρ
          hZ hV hb hv ⟨a, a, hb, htl, rfl, le_rfl⟩
        refine ⟨_, h1, h2, ?_⟩
        rw [h3, hwt]
        simp only [gap, hb, Fork.tail, htl, ↓reduceIte, Fork.wt, add_zero]
        simp only [GNode.proc, hlastP, Net.Up_nil, Nat.cast_zero, sub_zero]
        omega
      · rw [ea] at hle
        have : (0 : ℤ) ≤ γ.net.Lp ρ.1 p' := by positivity
        push_cast [hLp] at hC
        omega
    · -- the last message delivered after an auxiliary node arrives at `k = lastP a.1 q₁`
      have hLp2 : γ.net.Lp a.1 (j :: q) = γ.net.Lp a.1 q₁ + γ.net.Lp (lastP a.1 q₁) q₂ := by
        rw [hsplit, Net.Lp_append]
      rw [hf] at hle
      push_cast at hle
      have hpos1 : (0 : ℤ) ≤ γ.net.Lp ρ.1 p' := by positivity
      have hpos2 : (0 : ℤ) ≤ γ.net.Lp a.1 q₁ := by positivity
      rcases FData.psi_cases hr (D := γ.zD r σ (GNode.ofB σ₁) C (fun _ _ _ => False))
        (lastP a.1 q₁) with hk | ⟨b, q₃, hb, hq₃, hl, hk⟩
      · rw [hk] at hle
        push_cast [hLp, hLp2] at hC
        omega
      · rw [hk] at hle
        simp only at hle
        have hU3 : (0 : ℤ) ≤ γ.net.Up (lastP a.1 q₁) q₃ := by positivity
        have hbσ : γ.HB r b σ := hb.1
        rcases zT_cases hr hC0 hbσ with ⟨⟨w0, hw0⟩, eb, -⟩ | ⟨-, eb, hbM⟩
        · obtain ⟨c, q₁', rfl⟩ := List.exists_cons_of_ne_nil hne
          obtain ⟨rfl, rfl⟩ : c = j ∧ q₁' ++ q₂ = q := by
            simpa [List.cons_append] using hsplit.symm
          -- the node `y = basic(⟨ρ, p' ++ q₁⟩)` outside the past
          have hza' : γ.gbasic r w (q₁' ++ q₂) = some z := by
            simpa [gbasic_cons, hw] using hza
          obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.1 (by rwa [gbasic_append] at hza')
          have hyn : ¬ γ.HB r y σ := fun h => hn ((HB.of_gbasic hy).trans h)
          have hs := recv_spec hr hw
          have hL := γ.net.one_le_L _ _ hs.2.2.1
          have hy0 : 0 < γ.timer r y := by have := (gbasic_timer hr hy).1; omega
          have hay : γ.gbasic r a (c :: q₁') = some y := by
            simp only [gbasic_cons, hw, Option.bind_some]; exact hy
          have hyp : y.1 = lastP a.1 (c :: q₁') := γ.gbasic_proc r hay
          have hya := (γ.gbasic_appears r hy).2
          obtain ⟨z₃, hz₃, -⟩ := flood_chain hF hr q₃ hya hy0 (hyp ▸ hq₃)
          have hz₃n : ¬ γ.HB r z₃ σ := fun h => hyn ((HB.of_gbasic hz₃).trans h)
          have hz₃p : z₃.1 = b.1 := by rw [γ.gbasic_proc r hz₃, hyp, hl]
          have hlt := timer_lt_of_not_past hbσ (γ.gbasic_appears r hz₃).2 hz₃n hz₃p
          have hne3 : b ≠ z₃ := fun e => hz₃n (e ▸ hbσ)
          have hbase : γ.gbasic r ρ (p' ++ c :: q₁') = some y := by
            rw [gbasic_append, ha, Option.bind_some]; exact hay
          have htail : γ.basic r ⟨ρ, (p' ++ c :: q₁') ++ q₃⟩ = some z₃ := by
            show γ.gbasic r ρ _ = _
            rw [gbasic_append, hbase, Option.bind_some]; exact hz₃
          have hhead : (⟨ρ, (p' ++ c :: q₁') ++ q₂⟩ : GNode P S M E) = ⟨ρ, p' ++ c :: (q₁' ++ q₂)⟩ := by
            simp
          have hproc : (⟨ρ, p' ++ c :: q₁'⟩ : GNode P S M E).proc = lastP a.1 (c :: q₁') := by
            simp only [GNode.proc, lastP_append, hlastP]
          obtain ⟨Z, θ, hZ, hV, hbθ, hv, hwt⟩ := zreach_Dz hr hw0
          obtain ⟨h1, h2, h3⟩ := zigzag_snoc (G := ⟨⟨ρ, p' ++ c :: q₁'⟩, q₂, q₃⟩)
            ⟨by simp only [Fork.head, GNode.ext]; rw [hhead]; simp [appearsG, hz],
              by show (γ.basic r ⟨ρ, (p' ++ c :: q₁') ++ q₃⟩).isSome; rw [htail]; rfl⟩
            hρ hZ hV hbθ hv
            ⟨b, z₃, hbθ, htail, hz₃p.symm, hlt.le⟩
          have hGh : (⟨⟨ρ, p' ++ c :: q₁'⟩, q₂, q₃⟩ : Fork P S M E).head =
              ⟨ρ, p' ++ c :: (q₁' ++ q₂)⟩ := hhead
          rw [hGh] at h1
          refine ⟨_, h1, h2, ?_⟩
          rw [h3, hwt]
          have hgap : γ.gap r θ (⟨⟨ρ, p' ++ c :: q₁'⟩, q₂, q₃⟩ : Fork P S M E).tail = 1 := by
            have : γ.basic r (⟨⟨ρ, p' ++ c :: q₁'⟩, q₂, q₃⟩ : Fork P S M E).tail = some z₃ := htail
            simp only [gap, hbθ, this, Option.some.injEq, hne3, ↓reduceIte]
          rw [hgap]
          simp only [Fork.wt, hproc]
          omega
        · rw [eb] at hle
          push_cast [hLp, hLp2] at hC
          omega

end Sys

end Podc.ZigzagCausality
