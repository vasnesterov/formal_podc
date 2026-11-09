import Papers.PODC2020.SelfStabHighDynamics.Alg3.Round

/-!
# Algorithm 3: executions

Invariants of the configurations, Lemma 10 (fake timestamps), Lemma 11 (propagation along
journeys), closure of the legitimate configurations, and convergence once every process has
reached every other one.

Times are 0-indexed: `X G γ t` is the configuration at the end of the paper's Round `t`, and the
graph `G t` is the snapshot of the paper's Round `t + 1`.
-/

namespace Podc.SelfStabHighDynamics.Alg3

open Cslib.HeardOf Cslib.DynNet StabilizingLEDynamic

variable {ι : Type*} [LinearOrder ι]

/-- The configuration at the end of Round `t`. -/
noncomputable abbrev X (G : DG ι) (γ : ι → MSt ι) : ℕ → ι → MSt ι :=
  (alg : SAlg ι (MSt ι)).exec G γ

/-- The received pairs of `q` in round `t` (0-indexed), in processing order. -/
noncomputable def mbx (G : DG ι) (γ : ι → MSt ι) (t : ℕ) (q : ι) : List (ι × ℕ) :=
  (rfin sent q (msgs (G t) (X G γ t) q)).toList

theorem X_succ (G : DG ι) (γ : ι → MSt ι) (t : ℕ) (q : ι) :
    X G γ (t + 1) q = round q (X G γ t q) (mbx G γ t q) := by
  show (alg : SAlg ι (MSt ι)).step q (msgs (G t) (X G γ t) q) = _
  simp only [alg, msgs_self, Option.getD_some]
  rfl

variable {V : Finset ι} {G : DG ι} {γ : ι → MSt ι}

theorem mem_mbx (hG : IsDG V G) {t : ℕ} {q : ι} {x : ι × ℕ} :
    x ∈ mbx G γ t q ↔ ∃ k, G t k q ∧ x ∈ (X G γ t k).mem := by
  simp only [mbx, Finset.mem_toList]
  rw [mem_rfin_msgs (fun s => s.mem.finite_toSet) hG]
  rfl

theorem mem_mbx' (hG : IsDG V G) {t : ℕ} {q : ι} {x : ι × ℕ} (hx : x ∈ mbx G γ t q) :
    ∃ k ∈ V, x ∈ (X G γ t k).mem := by
  obtain ⟨k, hk, hx⟩ := (mem_mbx hG).mp hx
  exact ⟨k, (hG t k q hk).1, hx⟩

/-! ### Configurations -/

theorem mem_cfg_iff {γ : ι → MSt ι} :
    γ ∈ (alg : SAlg ι (MSt ι)).Cfg V ↔ ∀ p ∈ V, (γ p).n = V.card ∧ WF (γ p).n (γ p).mem := by
  simp only [SAlg.Cfg, alg, Set.mem_ofPred_eq, WF]
  exact forall₂_congr fun _ _ => ⟨fun ⟨a, b, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨a, b, c⟩⟩

/-- Every execution from a configuration for `V` stays in the configurations for `V` (`n = |V|`,
at most `n` entries, distinct keys). -/
theorem X_cfg (hγ : γ ∈ (alg : SAlg ι (MSt ι)).Cfg V) (t : ℕ) :
    X G γ t ∈ (alg : SAlg ι (MSt ι)).Cfg V := by
  induction t with
  | zero => exact hγ
  | succ t ih =>
    rw [mem_cfg_iff] at ih ⊢
    intro p hp
    rw [X_succ, round_n]
    exact ⟨(ih p hp).1, round_wf p (ih p hp).2 _⟩

/-- After every round, `⟨id(p), 0⟩ ∈ members(p)`. -/
theorem X_self (hγ : γ ∈ (alg : SAlg ι (MSt ι)).Cfg V) (t : ℕ) {p : ι} (hp : p ∈ V) :
    (p, 0) ∈ (X G γ (t + 1) p).mem := by
  rw [X_succ]
  refine round_self p ?_ _
  rw [((mem_cfg_iff.mp (X_cfg hγ t)) p hp).1]
  exact Finset.card_pos.mpr ⟨p, hp⟩

/-! ### Lemma 10 -/

/-- Lemma 10 (strong form): at the end of Round `t`, every fake timestamp is `≥ t`. Holds for
every initial configuration. -/
theorem X_fakeGe (hG : IsDG V G) (t : ℕ) : ∀ p ∈ V, FakeGe V t (X G γ t p).mem := by
  induction t with
  | zero => intro p _ y _ _; exact Nat.zero_le _
  | succ t ih =>
    intro p hp
    rw [X_succ]
    refine round_fakeGe hp (ih p hp) ?_
    intro y hy
    obtain ⟨k, hk, hy⟩ := mem_mbx' hG hy
    exact ih k hk y hy

theorem mbx_fakeGe (hG : IsDG V G) (t : ℕ) (q : ι) : FakeGe V t (mbx G γ t q) := by
  intro y hy
  obtain ⟨k, hk, hy⟩ := mem_mbx' hG hy
  exact X_fakeGe hG t k hk y hy

/-! ### Lemma 11 -/

/-- Lemma 11, journey form: if there is a journey from `p` at time `1` to `q` at time `i ≥ 1`,
then at the end of Round `i`, `p ∈ members(q)` with timestamp `≤ i - 1`. -/
theorem lemma11_journey (hG : IsDG V G) (hγ : γ ∈ (alg : SAlg ι (MSt ι)).Cfg V) {p q : ι}
    (hp : p ∈ V) {i : ℕ} (hJ : Journey G 1 p i q) :
    q ∈ V ∧ ∃ x ∈ (X G γ i q).mem, x.1 = p ∧ x.2 + 1 ≤ i := by
  refine hJ.of_inv (P := fun τ b => b ∈ V ∧ ∃ x ∈ (X G γ τ b).mem, x.1 = p ∧ x.2 + 1 ≤ τ)
    ⟨hp, (p, 0), X_self hγ 0 hp, rfl, le_rfl⟩ ?_
  rintro τ a b hτ - ⟨ha, ⟨p', ts⟩, hx, rfl, hts⟩ hab
  have hcfg := (mem_cfg_iff.mp (X_cfg (G := G) hγ τ))
  rcases hab with rfl | hab
  · obtain ⟨t', ht', hm⟩ := round_keep ha (hcfg a ha).1 (hcfg a ha).2 (X_fakeGe hG τ a ha)
      (mbx_fakeGe hG τ a) hx (B := τ) (by simp only at hts; omega)
    exact ⟨ha, (p', t'), by rw [X_succ]; exact hm, rfl, by simp only at hts ⊢; omega⟩
  · have hb : b ∈ V := (hG τ a b hab).2.1
    refine ⟨hb, ?_⟩
    by_cases hpb : p' = b
    · subst hpb; exact ⟨(p', 0), X_self hγ τ hb, rfl, by omega⟩
    · have hmb : (p', ts) ∈ mbx G γ τ b := (mem_mbx hG).mpr ⟨a, hab, hx⟩
      obtain ⟨t', ht', hm⟩ := round_add hb (hcfg b hb).1 (hcfg b hb).2 (X_fakeGe hG τ b hb)
        (mbx_fakeGe hG τ b) hmb hp hpb (B := τ) (by simp only at hts; omega)
      exact ⟨(p', t'), by rw [X_succ]; exact hm, rfl, by simp only at hts ht' ⊢; omega⟩

/-! ### Legitimate configurations -/

/-- The legitimate configurations of Algorithm 3 for `V` (Section 6.2): every process of `V`
elects `ℓ = min V` and the identifiers in `members(p)` are exactly those of `V`. -/
def Legit (V : Finset ι) (hV : V.Nonempty) (γ : ι → MSt ι) : Prop :=
  ∀ p ∈ V, (γ p).lid = V.min' hV ∧ ∀ x, x ∈ keys (γ p).mem ↔ x ∈ V

/-- Closure: legitimacy is preserved in every dynamic graph with vertex set `V`. -/
theorem legit_X (hG : IsDG V G) {hV : V.Nonempty} (hγ : Legit V hV γ) (t : ℕ) :
    Legit V hV (X G γ t) := by
  induction t with
  | zero => exact hγ
  | succ t ih =>
    intro p hp
    have hk : keys (X G γ (t + 1) p).mem = keys (X G γ t p).mem := by
      rw [X_succ]
      refine keys_round hp (ih p hp).2 fun x hx => ?_
      obtain ⟨k, hk, hx⟩ := mem_mbx' hG hx
      exact ((ih k hk).2 x.1).mp (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have hk' : ∀ x, x ∈ keys (X G γ (t + 1) p).mem ↔ x ∈ V := by rw [hk]; exact (ih p hp).2
    refine ⟨?_, hk'⟩
    rw [X_succ, round_lid, ← X_succ]
    exact minKey_eq_min' hV hk' hp

/-- Convergence: once (at time `t ≥ 1`) every `members(q)` contains every identifier of `V`, the
configuration is legitimate. -/
theorem legit_of_cover (hγ : γ ∈ (alg : SAlg ι (MSt ι)).Cfg V) (hV : V.Nonempty) {t : ℕ}
    (ht : 1 ≤ t) (hcov : ∀ p ∈ V, ∀ q ∈ V, p ∈ keys (X G γ t q).mem) :
    Legit V hV (X G γ t) := by
  have hcfg := mem_cfg_iff.mp (X_cfg (G := G) hγ t)
  have hkeys : ∀ q ∈ V, ∀ x, x ∈ keys (X G γ t q).mem ↔ x ∈ V := by
    intro q hq
    obtain ⟨hn, hnd, hlen⟩ := hcfg q hq
    have hsub : V ⊆ (keys (X G γ t q).mem).toFinset := fun p hp =>
      List.mem_toFinset.mpr (hcov p hp q hq)
    have hcard : (keys (X G γ t q).mem).toFinset.card ≤ V.card := by
      rw [List.toFinset_card_of_nodup hnd, keys, List.length_map]; omega
    have := Finset.eq_of_subset_of_card_le hsub hcard
    intro x
    rw [← List.mem_toFinset, ← this]
  intro q hq
  refine ⟨?_, hkeys q hq⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [X_succ, round_lid, ← X_succ]
  exact minKey_eq_min' hV (hkeys q hq) hq

end Podc.SelfStabHighDynamics.Alg3
