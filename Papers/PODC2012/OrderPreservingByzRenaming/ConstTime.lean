import Papers.PODC2012.OrderPreservingByzRenaming.TwoRound

/-!
# The constant-time algorithm of the PODC-era version (arXiv:1205.0477v1/v2, Algorithm 1)

Algorithm 1 of arXiv:1205.0477v2 has the same two communication rounds as `TwoRound.alg`
(Round 1: ids; Round 2: echo of the ids received; same sanity check `isValid`), but the offset of an
id is `N` if its counter is at least `N - t` and the counter itself otherwise (Lines 24–27), instead
of `min(counter, N - t)`. We reuse the message type, the inboxes and the counters of `TwoRound`.

* **Lemma 1** (`lemma_1`): correct ids `a < b` get `newId[a] + N ≤ newId[b]` at every correct process.
* **Lemma 2** (`lemma_2`): `Skew ≤ 3t²`, proved for `N > 2t² + t` (in particular for `N > 3t²`).
  The paper says that Lemmas 1 and 2 hold for `N > 3t`; Lemma 2 does not (`ConstTimeCex.lean`).
* **Theorem 3** (`theorem_3`): for `N > 3t²` Algorithm 1 solves order-preserving renaming with
  target namespace `{1, …, N² + Nt}`.
-/

namespace Podc.OrderPreservingByzRenaming.ConstTime

open Cslib.Byzantine.LockStep TwoRound

variable {n : ℕ}

/-- The offset of an id with `c` echoes (Lines 24–27): `N` if `c ≥ N - t`, else `c`. -/
def off (n t c : ℕ) : ℕ := if n - t ≤ c then n else c

/-- `newId[v]` of Algorithm 1: accumulated offsets of the known ids `≤ v`. -/
def newidG (t : ℕ) (ib1 ib2 : Fin n → Option Msg) (v : ℕ) : ℕ :=
  ∑ z ∈ (accepted t ib1 ib2).filter (· ≤ v), off n t (counter t ib1 ib2 z)

/-- **Algorithm 1** of arXiv:1205.0477v2 as a `LockStep` protocol (sends as `TwoRound.alg`). -/
def alg1 (n t : ℕ) : Protocol (Fin n) ℕ Msg ℕ where
  send := (TwoRound.alg n t).send
  decide p x h := match h with
    | [ib1, ib2] =>
      let ib1' := Function.update ib1 p (some (.ident x))
      let ib2' := Function.update ib2 p (some (.echo (timely ib1')))
      some (newidG t ib1' ib2' x)
    | _ => none

lemma alg1_decide_eq_none (t : ℕ) (p : Fin n) (x : ℕ) (h : History (Fin n) Msg) (hl : h.length ≠ 2) :
    (alg1 n t).decide p x h = none := by
  match h with
  | [] => rfl
  | [_] => rfl
  | [_, _] => simp at hl
  | _ :: _ :: _ :: _ => rfl

/-- An honest process decides `newId[my id]` computed from its two inboxes. -/
theorem decides_iff {s : Scenario (Fin n) ℕ Msg} (t : ℕ) (hs : s.Reliable) (p : Fin n) (o : ℕ) :
    Decides ⊤ (alg1 n t) s p o ↔ o = newidG t (inb1 s p) (inb2 s p) (s.input p) := by
  have hh : hist ⊤ (alg1 n t) s = hist ⊤ (TwoRound.alg n t) s := hist_eq_of_send_eq ⊤ (alg1 n t) s rfl
  rw [decides_iff_firstSome, firstSome_iff_of_ne 2]
  · simp only [status, hh]
    rw [hist_two']
    show some (newidG t _ _ _) = some o ↔ _
    rw [raw_zero t hs, raw_one t hs]
    simp [eq_comm]
  · intro r hr
    simp only [status]
    exact alg1_decide_eq_none t p _ _ (by simpa using hr)

/-! ### Counting -/

section Counting

variable (t : ℕ) (ib1 ib2 : Fin n → Option Msg)

lemma newidG_eq_sum_range (htn : t < n) (v : ℕ) :
    newidG t ib1 ib2 v = ∑ z ∈ Finset.range (v + 1), off n t (counter t ib1 ib2 z) := by
  unfold newidG
  apply Finset.sum_subset
  · intro z hz
    simp only [Finset.mem_filter] at hz
    simp only [Finset.mem_range]; omega
  · intro z _ hz
    by_cases h : z ∈ accepted t ib1 ib2
    · simp only [Finset.mem_filter, not_and] at hz
      have : z ≤ v := by simp only [Finset.mem_range] at *; omega
      exact absurd this (hz h)
    · have : counter t ib1 ib2 z = 0 := by
        by_contra h0; exact h (mem_accepted_of_counter_pos t ib1 ib2 (Nat.pos_of_ne_zero h0))
      simp only [this, off]; split_ifs <;> omega

lemma newidG_add_le {a b : ℕ} (hab : a < b) (htn : t < n) (hb : n - t ≤ counter t ib1 ib2 b) :
    newidG t ib1 ib2 a + n ≤ newidG t ib1 ib2 b := by
  rw [newidG_eq_sum_range t ib1 ib2 htn, newidG_eq_sum_range t ib1 ib2 htn]
  have hsub : insert b (Finset.range (a + 1)) ⊆ Finset.range (b + 1) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_range] at hz ⊢
    omega
  have hnot : b ∉ Finset.range (a + 1) := by simp; omega
  have hoff : off n t (counter t ib1 ib2 b) = n := by simp [off, hb]
  calc _ = ∑ z ∈ insert b (Finset.range (a + 1)), off n t (counter t ib1 ib2 z) := by
        rw [Finset.sum_insert hnot, hoff, add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- The offset function is monotone up to a jump of `t` at `N - t`. -/
lemma off_le {x y b : ℕ} (h : x ≤ y + b) :
    off n t x ≤ off n t y + b + (if n - t ≤ x then t else 0) := by
  unfold off; split_ifs <;> omega

end Counting

section Correct

variable {s : Scenario (Fin n) ℕ Msg} (t : ℕ)
variable (hinj : Set.InjOn s.input s.honest) (hf : (byzF s).card ≤ t)
include hinj hf

/-- All valid echoes received by `p` contain at most `f (N + t)` non-correct ids in total. -/
lemma sum_card_vEcho_sdiff (p : Fin n) :
    ∑ j, (vEcho t (inb1 s p) (inb2 s p) j \ corrIds s).card ≤ (byzF s).card * (n + t) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ s.byz)]
  have h1 : ∑ j ∈ Finset.univ.filter (· ∈ s.byz), (vEcho t (inb1 s p) (inb2 s p) j \ corrIds s).card
      ≤ ∑ _j ∈ byzF s, (t + (byzF s).card) := by
    apply Finset.sum_le_sum
    intro j _
    exact card_vEcho_sdiff_le t p j
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ s.byz),
      (vEcho t (inb1 s p) (inb2 s p) j \ corrIds s).card
      ≤ ∑ _j ∈ Finset.univ.filter (fun j => j ∉ s.byz), (byzF s).card := by
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [vEcho_honest t hinj hf p hj]
    exact card_timely_sdiff_le j
  have hH : (Finset.univ.filter fun j : Fin n => j ∉ s.byz).card = n - (byzF s).card := by
    have : (Finset.univ.filter fun j : Fin n => j ∉ s.byz) = (byzF s)ᶜ := by ext; simp [byzF]
    rw [this, Finset.card_compl, Fintype.card_fin]
  have hfn : (byzF s).card ≤ n := (Finset.card_le_univ _).trans (by simp)
  simp only [Finset.sum_const, smul_eq_mul, hH] at h1 h2
  change ∑ j ∈ byzF s, _ + _ ≤ _ at *
  have : (n - (byzF s).card) * (byzF s).card + (byzF s).card * (t + (byzF s).card) =
      (byzF s).card * (n + t) := by
    zify [hfn]; ring
  calc _ ≤ (byzF s).card * (t + (byzF s).card) + (n - (byzF s).card) * (byzF s).card :=
        Nat.add_le_add h1 h2
    _ = _ := by rw [add_comm, this]

/-- At most `f` non-correct ids reach `N - t` echoes at a correct process (if `N > 2t² + t`). -/
lemma card_crossing_le (hn : 2 * t ^ 2 + t < n) (p : Fin n) (S : Finset ℕ)
    (hS : ∀ z ∈ S, z ∉ corrIds s) :
    (S.filter fun z => n - t ≤ counter t (inb1 s p) (inb2 s p) z).card ≤ (byzF s).card := by
  set K : Finset ℕ := (S.filter fun z => n - t ≤ counter t (inb1 s p) (inb2 s p) z)
  have hmass : K.card * (n - t) ≤ (byzF s).card * (n + t) := by
    calc K.card * (n - t) ≤ ∑ z ∈ K, counter t (inb1 s p) (inb2 s p) z := by
          rw [← smul_eq_mul]
          exact Finset.card_nsmul_le_sum K (fun z => counter t (inb1 s p) (inb2 s p) z) (n - t)
            fun z hz => (Finset.mem_filter.1 hz).2
      _ = ∑ j, (K.filter fun z => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card := by
          unfold counter; simp only [Finset.card_filter]; exact Finset.sum_comm
      _ ≤ ∑ j, (vEcho t (inb1 s p) (inb2 s p) j \ corrIds s).card := by
          refine Finset.sum_le_sum fun j _ => Finset.card_le_card fun z hz => ?_
          simp only [Finset.mem_filter, K] at hz
          exact Finset.mem_sdiff.2 ⟨hz.2, hS z hz.1.1⟩
      _ ≤ _ := sum_card_vEcho_sdiff t hinj hf p
  by_contra hK
  push Not at hK
  have h1 : ((byzF s).card + 1) * (n - t) ≤ K.card * (n - t) := Nat.mul_le_mul_right _ hK
  have h2 : (byzF s).card * (n + t) < ((byzF s).card + 1) * (n - t) := by
    have htn : t ≤ n := by nlinarith
    zify [htn]
    have : ((byzF s).card : ℤ) ≤ t := by exact_mod_cast hf
    nlinarith
  omega

/-- **Lemma 2** (for `N > 2t² + t`, in particular `N > 3t²`): `Skew ≤ 3t²`. -/
theorem lemma_2 (hn : 2 * t ^ 2 + t < n) (p q : Fin n) (hp : p ∉ s.byz) (hq : q ∉ s.byz) (v : ℕ) :
    newidG t (inb1 s p) (inb2 s p) v ≤ newidG t (inb1 s q) (inb2 s q) v + 3 * t ^ 2 := by
  have htn : t < n := by nlinarith
  rw [newidG_eq_sum_range t _ _ htn, newidG_eq_sum_range t _ _ htn]
  set R := Finset.range (v + 1)
  have hpt : ∀ z ∈ R, off n t (counter t (inb1 s p) (inb2 s p) z) ≤
      off n t (counter t (inb1 s q) (inb2 s q) z) +
        (if z ∈ corrIds s then 0 else ((byzF s).filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card +
          (if n - t ≤ counter t (inb1 s p) (inb2 s p) z then t else 0)) := by
    intro z _
    split_ifs with hz h1
    · have h1 := counter_corr t hinj hf p hz
      have h2 := counter_corr t hinj hf q hz
      simp [off, h1, h2]
    · have := off_le (n := n) t (counter_le t hinj hf p q hp hq z)
      simp only [h1, if_true] at this
      omega
    · have := off_le (n := n) t (counter_le t hinj hf p q hp hq z)
      simp only [h1, if_false] at this
      omega
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  gcongr
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_add_distrib]
  set S := R.filter fun z => z ∉ corrIds s
  have hA : ∑ z ∈ S, ((byzF s).filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card ≤
      2 * t ^ 2 := by
    calc ∑ z ∈ S, ((byzF s).filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card
        = ∑ j ∈ byzF s, (S.filter fun z => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card := by
          simp only [Finset.card_filter]; exact Finset.sum_comm
      _ ≤ ∑ _j ∈ byzF s, (t + (byzF s).card) := by
          refine Finset.sum_le_sum fun j _ => le_trans (Finset.card_le_card ?_)
            (card_vEcho_sdiff_le t p j)
          intro z hz
          simp only [Finset.mem_filter, S] at hz
          exact Finset.mem_sdiff.2 ⟨hz.2, hz.1.2⟩
      _ = (byzF s).card * (t + (byzF s).card) := by simp
      _ ≤ t * (t + t) := Nat.mul_le_mul hf (by omega)
      _ = 2 * t ^ 2 := by ring
  have hB : ∑ z ∈ S, (if n - t ≤ counter t (inb1 s p) (inb2 s p) z then t else 0) ≤ t ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, sq]
    exact Nat.mul_le_mul_right _ ((card_crossing_le t hinj hf hn p S
      fun z hz => (Finset.mem_filter.1 hz).2).trans hf)
  omega

/-- **Lemma 1.** Correct ids `a < b` get `newId[a] + N ≤ newId[b]` at every process. -/
theorem lemma_1 (htn : t < n) (p : Fin n) {a b : ℕ} (hb : b ∈ corrIds s) (hab : a < b) :
    newidG t (inb1 s p) (inb2 s p) a + n ≤ newidG t (inb1 s p) (inb2 s p) b :=
  newidG_add_le t _ _ hab htn (counter_corr t hinj hf p hb)

/-- Validity: `newId ≤ N² + Nt` (for `N > 2t² + t`). -/
lemma newidG_le (hn : 2 * t ^ 2 + t < n) (p : Fin n) (v : ℕ) :
    newidG t (inb1 s p) (inb2 s p) v ≤ n ^ 2 + n * t := by
  set A := accepted t (inb1 s p) (inb2 s p)
  have hcross : (A.filter fun z => n - t ≤ counter t (inb1 s p) (inb2 s p) z).card ≤ n := by
    set X : Finset ℕ := A.filter fun z => n - t ≤ counter t (inb1 s p) (inb2 s p) z
    rw [← Finset.card_filter_add_card_filter_not (s := X) (fun z => z ∈ corrIds s)]
    have h1 : (X.filter fun z => z ∈ corrIds s).card ≤ n - (byzF s).card := by
      rw [← card_corrIds hinj]; exact Finset.card_le_card fun z hz => (Finset.mem_filter.1 hz).2
    have h2 := card_crossing_le t hinj hf hn p (X.filter fun z => z ∉ corrIds s)
      fun z hz => (Finset.mem_filter.1 hz).2
    have h3 : ((X.filter fun z => z ∉ corrIds s).filter
        fun z => n - t ≤ counter t (inb1 s p) (inb2 s p) z) = X.filter fun z => z ∉ corrIds s := by
      apply Finset.filter_true_of_mem
      intro z hz
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).2
    rw [h3] at h2
    have hfn : (byzF s).card ≤ n := (Finset.card_le_univ _).trans (by simp)
    omega
  calc newidG t (inb1 s p) (inb2 s p) v
      ≤ ∑ z ∈ A, off n t (counter t (inb1 s p) (inb2 s p) z) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ ∑ z ∈ A, (counter t (inb1 s p) (inb2 s p) z +
          (if n - t ≤ counter t (inb1 s p) (inb2 s p) z then t else 0)) :=
        Finset.sum_le_sum fun z _ => by unfold off; split_ifs <;> omega
    _ = ∑ z ∈ A, counter t (inb1 s p) (inb2 s p) z +
          t * (A.filter fun z => n - t ≤ counter t (inb1 s p) (inb2 s p) z).card := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ n ^ 2 + t * n := by
        gcongr
        exact (sum_counter_eq t _ _).trans_le ((Finset.sum_le_sum fun j _ =>
          card_vEcho_le t (inb1 s p) (inb2 s p) j).trans (by simp [sq]))
    _ = n ^ 2 + n * t := by ring

end Correct

/-- **Theorem 3** (arXiv:1205.0477v2). For `N > 3t²`, Algorithm 1 solves order-preserving renaming
with target namespace `{1, …, N² + Nt}` in two communication rounds. -/
theorem theorem_3 (t : ℕ) (hn : 3 * t ^ 2 < n) :
    Solves (⊤ : SimpleGraph (Fin n)) (alg1 n t) (atMost t) (OPRenaming (n ^ 2 + n * t)) := by
  rintro s hbyz hs ⟨hinj, -⟩
  have hn' : 2 * t ^ 2 + t < n := by nlinarith
  have htn : t < n := by nlinarith
  have hf : (byzF s).card ≤ t := by
    have : s.byz = ↑(byzF s) := by ext p; simp [byzF]
    rw [mem_atMost, this, Set.ncard_coe_finset] at hbyz
    exact hbyz
  have hdec := decides_iff (s := s) t hs
  have hmem : ∀ p ∈ s.honest, s.input p ∈ corrIds s := fun p hp =>
    Finset.mem_image.2 ⟨p, by simpa [Scenario.honest] using hp, rfl⟩
  have hord : ∀ p ∈ s.honest, ∀ q ∈ s.honest, s.input p < s.input q →
      newidG t (inb1 s p) (inb2 s p) (s.input p) < newidG t (inb1 s q) (inb2 s q) (s.input q) := by
    intro p hp q hq hlt
    have h1 := lemma_2 t hinj hf hn' p q hp hq (s.input p)
    have h2 := lemma_1 t hinj hf htn q (hmem q hq) hlt
    omega
  refine ⟨fun p _ => ⟨_, (hdec p _).2 rfl⟩, fun p hp o ho => ?_,
    fun p hp q hq o o' ho ho' hne => ?_, fun p hp q hq o o' ho ho' hlt => ?_⟩
  · rw [hdec] at ho
    subst ho
    refine ⟨?_, newidG_le t hinj hf hn' p _⟩
    rw [newidG_eq_sum_range t _ _ htn]
    have hoff : off n t (counter t (inb1 s p) (inb2 s p) (s.input p)) = n := by
      simp [off, counter_corr t hinj hf p (hmem p hp)]
    calc 1 ≤ n := by omega
      _ = off n t (counter t (inb1 s p) (inb2 s p) (s.input p)) := hoff.symm
      _ ≤ _ := Finset.single_le_sum (f := fun z => off n t (counter t (inb1 s p) (inb2 s p) z))
          (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ _)
  · rw [hdec] at ho ho'
    subst ho ho'
    have hx : s.input p ≠ s.input q := fun h => hne (hinj hp hq h)
    rcases Nat.lt_or_gt_of_ne hx with h | h
    · exact (hord p hp q hq h).ne
    · exact (hord q hq p hp h).ne'
  · rw [hdec] at ho ho'
    subst ho ho'
    exact hord p hp q hq hlt

end Podc.OrderPreservingByzRenaming.ConstTime

namespace Podc.OrderPreservingByzRenaming.ConstTime

open Cslib.Byzantine.LockStep

/-- Non-vacuity: Theorem 3 applies e.g. to `N = 4`, `t = 1`. -/
example : Solves (⊤ : SimpleGraph (Fin 4)) (alg1 4 1) (atMost 1) (OPRenaming (4 ^ 2 + 4 * 1)) :=
  theorem_3 1 (by norm_num)

end Podc.OrderPreservingByzRenaming.ConstTime
