import Papers.PODC2020.AsyncApproxBCDirected.BW

/-!
# Correctness of one round (Theorems 10, 11, Lemma 15, Theorem 16)

* `Witnessed Mz z Ft xq 𝒲` — the conclusion of Theorems 10 + 11 for one node `z`: for every
  potential cover `H` (`|H| ≤ f`, `z ∉ H`) there is an index set `W ∈ 𝒲` such that `z` holds, for
  every `q ∈ S_{Ft,W}`, a message from `q` with the common value `xq q` on a path avoiding `H`.
* `theorem10` — any two correct nodes executing Filter-and-Average are witnessed for a common
  fault set `Ft ∈ {Fv, Fu}`, common values `xq` and a common family `𝒲`.
* `pair_le` — the core of **Lemma 15**: two witnessed nodes produce new values that differ by at
  most half the spread of the correct values. (The paper goes through Lemma 13 and Theorem 14
  — a common value in both trimmed vectors —; we use Theorem 12 directly.)
* `output_valid` (**Theorem 16**, one round), `output_conv` (**Lemma 15**), `output_exists`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-- Conclusion of Theorems 10–11 for one node (see the module docstring). -/
def Witnessed (G : Digraph V) (f : ℕ) (Mz : Finset (Msg V)) (z : V) (Ft : Finset V)
    (xq : V → ℝ) (𝒲 : Finset V → Prop) : Prop :=
  ∀ H : Finset V, H.card ≤ f → z ∉ H → ∃ W, 𝒲 W ∧ W.card ≤ f ∧
    ∀ q ∈ srcComp G Ft W, ∃ m ∈ Mz, m.1 = xq q ∧ Avoids m.2 H

/-- **Lemma 15** (core): if `v` and `u` are witnessed for the same `Ft`, `xq`, `𝒲`, and every
message avoiding the actual fault set carries a value in `[lo, hi]`, then the outputs of
Filter-and-Average satisfy `y_v − y_u ≤ (hi − lo)/2`. -/
theorem pair_le (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {Ft : Finset V}
    (hFt : Ft.card ≤ f) {xq : V → ℝ} {𝒲 : Finset V → Prop} {v u : V} {Mv Mu : Finset (Msg V)}
    (hwv : Witnessed G f Mv v Ft xq 𝒲) (hwu : Witnessed G f Mu u Ft xq 𝒲) {F : Finset V}
    (hF : F.card ≤ f) (hvF : v ∉ F) (huF : u ∉ F) {lo hi : ℝ}
    (hMv : ∀ m ∈ Mv, Avoids m.2 F → lo ≤ m.1 ∧ m.1 ≤ hi)
    (hMu : ∀ m ∈ Mu, Avoids m.2 F → lo ≤ m.1 ∧ m.1 ≤ hi) {y z : ℝ}
    (hy : IsFA f v Mv y) (hz : IsFA f u Mu z) : y - z ≤ (hi - lo) / 2 := by
  obtain ⟨av, bv, rfl, -, ⟨Hlo, hHlo, hvHlo, hlo⟩, -, -, hbv⟩ := hy.props
  obtain ⟨au, bu, rfl, -, -, ⟨Hhi, hHhi, huHhi, hhi⟩, hau, -⟩ := hz.props
  obtain ⟨W₁, -, hW₁, h₁⟩ := hwv Hlo hHlo hvHlo
  obtain ⟨W₂, -, hW₂, h₂⟩ := hwu Hhi hHhi huHhi
  obtain ⟨q, hq⟩ := hG.theorem12 hn hFt hW₁ hW₂
  obtain ⟨m₁, hm₁, hm₁v, hm₁H⟩ := h₁ q (mem_inter.mp hq).1
  obtain ⟨m₂, hm₂, hm₂v, hm₂H⟩ := h₂ q (mem_inter.mp hq).2
  have e1 := hlo m₁ hm₁ hm₁H
  have e2 := hhi m₂ hm₂ hm₂H
  have e3 := hbv F hi hF hvF fun m hm hav => (hMv m hm hav).2
  have e4 := hau F lo hF huF fun m hm hav => (hMu m hm hav).1
  rw [hm₁v] at e1; rw [hm₂v] at e2
  linarith

/-- **Theorem 16** (one round): the output lies between any bounds on the messages avoiding the
actual fault set. -/
theorem isFA_valid {v : V} {Mv : Finset (Msg V)} {y : ℝ} (hy : IsFA f v Mv y) {F : Finset V}
    (hF : F.card ≤ f) (hvF : v ∉ F) {lo hi : ℝ}
    (hM : ∀ m ∈ Mv, Avoids m.2 F → lo ≤ m.1 ∧ m.1 ≤ hi) : lo ≤ y ∧ y ≤ hi := by
  obtain ⟨a, b, rfl, hab, -, -, hlo, hhi⟩ := hy.props
  have := hlo F lo hF hvF fun m hm hav => (hM m hm hav).1
  have := hhi F hi hF hvF fun m hm hav => (hM m hm hav).2
  constructor <;> linarith

namespace RoundExec

variable (E : RoundExec G f)

/-- Messages avoiding the actual fault set carry inputs of correct nodes. -/
theorem bounds_of_avoids {v : V} (hv : v ∉ E.F) {lo hi : ℝ}
    (hx : ∀ w ∉ E.F, lo ≤ E.x w ∧ E.x w ≤ hi) (t : ℕ) :
    ∀ m ∈ E.M v t, Avoids m.2 E.F → lo ≤ m.1 ∧ m.1 ≤ hi := by
  rintro ⟨y, p⟩ hm hp
  obtain ⟨s, hs⟩ : ∃ s, p.head? = some s := by
    have := E.M_last v hv t _ hm
    cases p with
    | nil => simp at this
    | cons s _ => exact ⟨s, rfl⟩
  rw [E.value_of_avoids hv hm hp hs]
  exact hx s (hp s (List.mem_of_head? hs))

/-- A node executing Filter-and-Average in thread `Fz` has sent `COMPLETE(Fz)` before. -/
theorem executes_sent {z : V} (hz : z ∉ E.F) {Fz : Finset V} {tz : ℕ}
    (h : E.Executes z Fz tz) : Sent G f E.M z Fz ∧ mcTime G E.M z Fz ≤ tz := by
  obtain ⟨hzF, -, ⟨⟨t', ht', hfifo⟩, -⟩, -⟩ := h
  obtain ⟨Mc, hMc⟩ := hfifo z
  have hm := hMc [z] isSimplePath_singleton (by simpa using Reaches.refl (G := G) hzF)
  obtain ⟨-, hs, -, ht⟩ := E.CR_honest z hz t' z [z] Mc Fz hm (by simpa [Avoids] using hz)
  exact ⟨hs, ht.trans ht'⟩

theorem mcMsg_subset {z : V} {Fz : Finset V} {tz : ℕ} (h : mcTime G E.M z Fz ≤ tz) :
    mcMsg G E.M z Fz ⊆ E.M z tz := fun _ hm => E.M_mono z h (mem_excl.mp hm).1

/-- Theorem 11 for the leading node: a node that passed Maximal-Consistency on `Ft` holds the
common values on paths avoiding any potential cover `H`. -/
theorem leader_witnessed (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {z c : V}
    (hz : z ∉ E.F) (hc : c ∉ E.F) {Ft : Finset V} (hsz : Sent G f E.M z Ft)
    (hsc : Sent G f E.M c Ft) {tz : ℕ} (htz : mcTime G E.M z Ft ≤ tz) {𝒲 : Finset V → Prop}
    (h𝒲 : ∀ H : Finset V, H.card ≤ f → z ∉ H →
      ∃ W, 𝒲 W ∧ W.card ≤ f ∧ ∀ h ∈ H, h ∉ srcComp G Ft W) :
    Witnessed G f (E.M z tz) z Ft (valueOf (mcMsg G E.M c Ft)) 𝒲 := by
  intro H hH hzH
  obtain ⟨W, hW𝒲, hW, hHS⟩ := h𝒲 H hH hzH
  refine ⟨W, hW𝒲, hW, fun q hq => ?_⟩
  have hzb : z ∉ Ft ∪ H := by simp [hsz.1, hzH]
  obtain ⟨p, hp, hpF⟩ := (reaches_from_srcComp hG hn hsz.2.1 hW hH hq hHS hzb).exists_simplePath
  obtain ⟨y, hy⟩ := (hsz.full G f) p hp.isRedundant (avoids_union.mp hpF).1 hp.1.2.1
  refine ⟨(y, p), E.mcMsg_subset htz hy, ?_, (avoids_union.mp hpF).2⟩
  rw [(hsz.consistent G f).eq_valueOf hy hp.1.1]
  exact (E.lemma7 hG hn hc hz hsc hsz hW hq).1.symm

/-- Theorem 11 for the non-leading node: `Completeness` for the leader's set yields the common
values on paths avoiding any potential cover. -/
theorem follower_witnessed (hn : 2 ≤ Fintype.card V) {w c : V} {Ft : Finset V}
    (hsc : Sent G f E.M c Ft) {Mw : Finset (Msg V)}
    (hcomp : Completeness G f w Mw (mcMsg G E.M c Ft) Ft)
    {W₀ : Finset V} (hW₀ : W₀ ≠ Ft) (hW₀c : W₀.card ≤ f) :
    Witnessed G f Mw w Ft (valueOf (mcMsg G E.M c Ft)) (· ≠ Ft) := by
  classical
  intro H hH hwH
  have key : ∀ W : Finset V, W.card ≤ f → W ≠ Ft → (∀ h ∈ H, h ∉ srcComp G Ft W) →
      ∀ q ∈ srcComp G Ft W, ∃ m ∈ Mw, m.1 = valueOf (mcMsg G E.M c Ft) q ∧ Avoids m.2 H := by
    intro W hW hne hHS q hq
    obtain ⟨m, hm, hmq, hno⟩ := hcomp W hW hne q hq
    by_contra hcon
    push Not at hcon
    refine hno ⟨H, hH, hwH, hHS, fun m' hm' hm'q hm'v hav => ?_⟩
    exact hcon m' hm' (by rw [hm'v]; exact (hsc.consistent G f).eq_valueOf hm hmq) hav
  by_cases hHt : H = Ft
  · subst hHt
    exact ⟨W₀, hW₀, hW₀c, key W₀ hW₀c hW₀ fun h hh hhS =>
      notMem_of_mem_srcComp hn hhS (mem_union_left _ hh)⟩
  · exact ⟨H, hHt, hH, key H hH hHt fun h hh hhS =>
      notMem_of_mem_srcComp hn hhS (mem_union_right _ hh)⟩

/-- Theorem 10 in the asymmetric case: `u` is the leading node (its set `Fu` is the common fault
set) and `v` has verified `Completeness` for a genuine `COMPLETE(Fu)` of a correct node `c`. -/
theorem theorem10_asym (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {v u c : V}
    (hu : u ∉ E.F) (hc : c ∉ E.F) {Fu : Finset V} {tv tu : ℕ}
    (hsu : Sent G f E.M u Fu) (htu : mcTime G E.M u Fu ≤ tu) (hsc : Sent G f E.M c Fu)
    (hcomp : Completeness G f v (E.M v tv) (mcMsg G E.M c Fu) Fu) (hf : 1 ≤ f) :
    ∃ xq 𝒲, Witnessed G f (E.M v tv) v Fu xq 𝒲 ∧ Witnessed G f (E.M u tu) u Fu xq 𝒲 := by
  classical
  set W₀ : Finset V := if Fu = ∅ then {v} else ∅
  have hW₀ : W₀ ≠ Fu := by
    by_cases h : Fu = ∅ <;> simp [W₀, h, eq_comm]
  have hW₀c : W₀.card ≤ f := by
    by_cases h : Fu = ∅ <;> simp [W₀, h, hf]
  refine ⟨_, _, E.follower_witnessed hn hsc hcomp hW₀ hW₀c,
    E.leader_witnessed hG hn hu hc hsu hsc htu fun H hH _ => ?_⟩
  by_cases hHt : H = Fu
  · subst hHt
    exact ⟨W₀, hW₀, hW₀c, fun h hh hhS => notMem_of_mem_srcComp hn hhS (mem_union_left _ hh)⟩
  · exact ⟨H, hHt, hH, fun h hh hhS => notMem_of_mem_srcComp hn hhS (mem_union_right _ hh)⟩

/-- **Theorem 10** (with Theorem 11): for any two correct nodes executing Filter-and-Average there
is a common fault set `Ft` (`Fv` or `Fu`) with common values `xq` such that both nodes are
witnessed. -/
theorem theorem10 (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {v u : V} (hv : v ∉ E.F)
    (hu : u ∉ E.F) {Fv Fu : Finset V} {tv tu : ℕ} (ev : E.Executes v Fv tv)
    (eu : E.Executes u Fu tu) :
    ∃ Ft xq 𝒲, Ft.card ≤ f ∧ Witnessed G f (E.M v tv) v Ft xq 𝒲 ∧
      Witnessed G f (E.M u tu) u Ft xq 𝒲 := by
  obtain ⟨hsv, htv⟩ := E.executes_sent hv ev
  obtain ⟨hsu, htu⟩ := E.executes_sent hu eu
  by_cases hvu : Fv = Fu
  · subst hvu
    have h𝒲 : ∀ (z : V) (H : Finset V), H.card ≤ f → z ∉ H →
        ∃ W, (fun _ => True) W ∧ W.card ≤ f ∧ ∀ h ∈ H, h ∉ srcComp G Fv W :=
      fun _ H hH _ => ⟨H, trivial, hH, fun h hh hhS =>
        notMem_of_mem_srcComp hn hhS (mem_union_right _ hh)⟩
    exact ⟨Fv, _, _, hsv.2.1, E.leader_witnessed hG hn hv hu hsv hsu htv (h𝒲 v),
      E.leader_witnessed hG hn hu hu hsu hsu htu (h𝒲 u)⟩
  -- the witness `c` of 3-reach
  have hf : 1 ≤ f := by
    by_contra h
    have h1 : Fv = ∅ := card_eq_zero.mp (by have := hsv.2.1; omega)
    have h2 : Fu = ∅ := card_eq_zero.mp (by have := hsu.2.1; omega)
    exact hvu (h1.trans h2.symm)
  obtain ⟨c, hcv, hcu⟩ := hG E.F Fu Fv u v E.card_F hsu.2.1 hsv.2.1 (by simp [hu, hsu.1])
    (by simp [hv, hsv.1])
  have hcF : c ∉ E.F := fun h => hcv.1 (mem_union_left _ h)
  obtain ⟨pv, hpv, hpvF⟩ := hcv.exists_simplePath
  obtain ⟨pu, hpu, hpuF⟩ := hcu.exists_simplePath
  have hpvR : ∀ y ∈ pv, Reaches G Fv y v := fun y hy =>
    (hpv.1.reaches_of_mem hpvF y hy).mono subset_union_right
  have hpuR : ∀ y ∈ pu, Reaches G Fu y u := fun y hy =>
    (hpu.1.reaches_of_mem hpuF y hy).mono subset_union_right
  obtain ⟨-, -, ⟨⟨tv', htv', hfv⟩, hverv⟩, -⟩ := ev
  obtain ⟨-, -, ⟨⟨tu', htu', hfu⟩, hveru⟩, -⟩ := eu
  obtain ⟨Mcv, hMcv⟩ := hfv c
  obtain ⟨Mcu, hMcu⟩ := hfu c
  have hmv := hMcv pv hpv hpvR
  have hmu := hMcu pu hpu hpuR
  obtain ⟨-, hscv, -, -⟩ := E.CR_honest v hv tv' c pv Mcv Fv hmv (avoids_union.mp hpvF).1
  obtain ⟨-, hscu, -, -⟩ := E.CR_honest u hu tu' c pu Mcu Fu hmu (avoids_union.mp hpuF).1
  have hidx : E.idx c Fv ≠ E.idx c Fu := fun h => hvu (E.idx_inj c hcF Fv Fu hscv hscu h)
  rcases lt_or_gt_of_ne hidx with h | h
  · -- `c` sent `COMPLETE(Fv)` first: `u` is informed about `Fv`, `v` leads
    have hm := E.CR_mono u htu' (E.CR_fifo u hu tu' c pu Mcu Fu Fv hmu
      (avoids_union.mp hpuF).1 hscv h)
    have hcomp := hveru c pu _ Fv hm hpuR (hscv.consistent G f)
    obtain ⟨xq, 𝒲, h1, h2⟩ := E.theorem10_asym hG hn hv hcF hsv htv hscv hcomp hf
    exact ⟨Fv, xq, 𝒲, hsv.2.1, h2, h1⟩
  · -- `c` sent `COMPLETE(Fu)` first: `v` is informed about `Fu`, `u` leads
    have hm := E.CR_mono v htv' (E.CR_fifo v hv tv' c pv Mcv Fv Fu hmv
      (avoids_union.mp hpvF).1 hscu h)
    have hcomp := hverv c pv _ Fu hm hpvR (hscu.consistent G f)
    obtain ⟨xq, 𝒲, h1, h2⟩ := E.theorem10_asym hG hn hu hcF hsu htu hscu hcomp hf
    exact ⟨Fu, xq, 𝒲, hsu.2.1, h1, h2⟩

/-! ## The round theorems -/

/-- Every correct node eventually computes a new value (Theorem 9 + Filter-and-Average is well
defined). -/
theorem output_exists (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {v : V} (hv : v ∉ E.F) :
    ∃ y, E.Output v y := by
  obtain ⟨Fv, t, ev⟩ := E.exists_executes hG hn hv
  obtain ⟨hs, ht⟩ := E.executes_sent hv ev
  obtain ⟨y, hy⟩ := (hs.full G f) [v] isSimplePath_singleton.isRedundant
    (by simpa [Avoids] using hs.1) (by simp)
  obtain ⟨z, hz⟩ := IsFA.exists (f := f) (Mv := E.M v t) ⟨(y, [v]), E.mcMsg_subset ht hy, rfl⟩
  exact ⟨z, Fv, t, ev, hz⟩

/-- **Theorem 16** (validity, one round): new values stay within any bounds of the current values
of the correct nodes. -/
theorem output_valid {v : V} (hv : v ∉ E.F) {y : ℝ} (hy : E.Output v y) {lo hi : ℝ}
    (hx : ∀ w ∉ E.F, lo ≤ E.x w ∧ E.x w ≤ hi) : lo ≤ y ∧ y ≤ hi := by
  obtain ⟨Fv, t, -, hfa⟩ := hy
  exact isFA_valid hfa E.card_F hv (E.bounds_of_avoids hv hx t)

/-- **Lemma 15**: the new values of any two correct nodes differ by at most half the spread of the
current values of the correct nodes. -/
theorem output_conv (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {v u : V} (hv : v ∉ E.F)
    (hu : u ∉ E.F) {y z : ℝ} (hy : E.Output v y) (hz : E.Output u z) {lo hi : ℝ}
    (hx : ∀ w ∉ E.F, lo ≤ E.x w ∧ E.x w ≤ hi) : |y - z| ≤ (hi - lo) / 2 := by
  obtain ⟨Fv, tv, ev, hfv⟩ := hy
  obtain ⟨Fu, tu, eu, hfu⟩ := hz
  obtain ⟨Ft, xq, 𝒲, hFt, hwv, hwu⟩ := E.theorem10 hG hn hv hu ev eu
  rw [abs_le]
  constructor
  · have := pair_le hG hn hFt hwu hwv E.card_F hu hv (E.bounds_of_avoids hu hx tu)
      (E.bounds_of_avoids hv hx tv) hfu hfv
    linarith
  · exact pair_le hG hn hFt hwv hwu E.card_F hv hu (E.bounds_of_avoids hv hx tv)
      (E.bounds_of_avoids hu hx tu) hfv hfu

end RoundExec

end AsyncApproxBCDirected
