import Papers.PODC2018.FairLeaderElection.Attacks

/-!
# Resilience against consecutive coalitions (Claim D.1 of [YM18], after [Abraham et al.])

Let the coalition `C` be one block of consecutive processors, ending with the adversary `e`, so
that the honest processors are `h_s = e + s`, `1 ≤ s ≤ l` (`l = n - k`). If `2k + 1 ≤ n`, then for
every (deterministic) deviation of `C` and every `j`, `Pr(outcome = j) ≤ 1/n` (`claim_D_1`).

Proof (as in the paper): by Lemma 3.3, if the outcome is `j`, then the first `n` messages `m` of `e`
sum to `j` and end with the secrets of the segment, the last one being the secret of `h_1`. The
secret of `h_1` reaches the coalition (at `a_1 = e + l + 1`) only as its `l`-th incoming message,
i.e. after `e` sent at least `l - 1 ≥ k` messages. Hence the first `k` messages of `e` do not depend
on `d h_1` (`prefixSent_update`, proved by simulating executions with different `d h_1` as long as
the coalition has not seen it, `reach_tau`), and `j = (first k messages) + ∑ segment secrets` holds
for at most one value of `d h_1` once the other secrets are fixed.

As a consequence, `A-LEADuni` is `0`-`1`-unbiased and `0`-`1`-resilient for `n ≥ 3`
(`isResilient_aLead_one`): no single processor can bias the election (against deterministic
deviations).
-/

namespace Podc.FairLeaderElection

open Cslib.UniRing
open Fin.NatCast Fin.CommRing

variable {n : ℕ} [NeZero n]

theorem aLead_sent_eq (d : Fin n → Fin n) (i : Fin n) (h : List (Fin n)) :
    (aLead d i).sent h = (d i :: h).take (if i = 0 then min (h.length + 1) n else min h.length n) := by
  unfold aLead; split_ifs <;> rfl

/-- Setting an element commutes with appending the next element of a list that the history is a
prefix of. -/
theorem set_snoc_of_prefix {L M : List (Fin n)} (hLM : L <+: M) {y : Fin n}
    (hy : M[L.length]? = some y) (j : ℕ) (x : Fin n) :
    ∃ y', (M.set j x)[L.length]? = some y' ∧ (L ++ [y]).set j x = L.set j x ++ [y'] := by
  have hlt : L.length < M.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hy; simp at hy
  rcases lt_trichotomy j L.length with hj | rfl | hj
  · refine ⟨y, ?_, ?_⟩
    · rw [List.getElem?_set, if_neg (by omega), hy]
    · rw [List.set_append, if_pos hj]
  · refine ⟨x, ?_, ?_⟩
    · rw [List.getElem?_set, if_pos rfl, if_pos hlt]
    · rw [List.set_append, if_neg (by omega), Nat.sub_self, List.set_cons_zero,
        List.set_eq_of_length_le le_rfl]
  · refine ⟨y, ?_, ?_⟩
    · rw [List.getElem?_set, if_neg (by omega), hy]
    · rw [List.set_eq_of_length_le (by simp; omega), List.set_eq_of_length_le (by omega)]

/-- The coalition is one block `e - k + 1, …, e`; the honest processors are `e + 1, …, e + l`. -/
structure Block (C : Finset (Fin n)) (e : Fin n) (l : ℕ) : Prop where
  mem : e ∈ C
  one_le : 1 ≤ l
  lt : l < n
  honest_iff : ∀ x, x ∉ C ↔ ∃ s, 1 ≤ s ∧ s ≤ l ∧ x = e + ((s : ℕ) : Fin n)

namespace Block

variable {C : Finset (Fin n)} {e : Fin n} {l : ℕ} (hB : Block C e l)
include hB

theorem val_sub_e {s : ℕ} (hs : s < n) : ((e + ((s : ℕ) : Fin n)) - e).val = s := by
  simp [Fin.val_natCast, Nat.mod_eq_of_lt hs]

/-- Processors at positions `1 … l` after `e` are honest. -/
theorem not_mem_iff (x : Fin n) : x ∉ C ↔ 1 ≤ (x - e).val ∧ (x - e).val ≤ l := by
  rw [hB.honest_iff]
  constructor
  · rintro ⟨s, h1, h2, rfl⟩; rw [hB.val_sub_e (by have := hB.lt; omega)]; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(x - e).val, h1, h2, by simp⟩

theorem card : C.card = n - l := by
  have hcompl : (Finset.univ.filter (· ∉ C)).card = l := by
    have : Finset.univ.filter (· ∉ C) = (Finset.Icc 1 l).image fun s => e + ((s : ℕ) : Fin n) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_Icc, hB.honest_iff]
      constructor
      · rintro ⟨s, h1, h2, rfl⟩; exact ⟨s, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; exact ⟨s, h1, h2, rfl⟩
    rw [this, Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have := congrArg (fun y => (y - e).val) hab
      simp only at this
      rwa [hB.val_sub_e (by have := hB.lt; omega), hB.val_sub_e (by have := hB.lt; omega)] at this
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at hcompl
  have := Finset.card_le_univ C
  simp at hcompl this; omega

end Block

variable {C : Finset (Fin n)} {e : Fin n} {l : ℕ} {A : Profile n (Fin n)} {d : Fin n → Fin n}
  {x : Fin n}

/-- The modification of a configuration when the secret of `h_1 = e + 1` is replaced by `x`: the
copy of that secret held by `h_s` (at index `s - 2`, `2 ≤ s ≤ l`) is replaced by `x`. -/
def tau (e : Fin n) (l : ℕ) (x : Fin n) (c : Config n (Fin n)) : Config n (Fin n) := fun i =>
  if 2 ≤ (i - e).val ∧ (i - e).val ≤ l then (c i).set ((i - e).val - 2) x else c i

/-- The first adversary of the block. -/
def firstAdv (e : Fin n) (l : ℕ) : Fin n := e + ((l + 1 : ℕ) : Fin n)

/-- The coalition has not yet received the secret of `h_1`. -/
def Untainted (e : Fin n) (l : ℕ) (c : Config n (Fin n)) : Prop := (c (firstAdv e l)).length + 1 ≤ l

theorem tau_length (c : Config n (Fin n)) (i : Fin n) : (tau e l x c i).length = (c i).length := by
  unfold tau; split_ifs <;> simp

theorem tau_init : tau e l x (init : Config n (Fin n)) = init := by
  funext i; unfold tau; split_ifs <;> simp [init]

theorem tau_update (c : Config n (Fin n)) (i : Fin n) (L : List (Fin n)) :
    tau e l x (Function.update c i L) = Function.update (tau e l x c) i (tau e l x
      (Function.update c i L) i) := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp only [tau, Function.update_of_ne hj]

namespace Block

variable (hB : Block C e l)
include hB

theorem two_le_n : 2 ≤ n := by have := hB.one_le; have := hB.lt; omega

theorem pred_pos (i : Fin n) {t : ℕ} (ht : ((i - 1) - e).val = t) (ht1 : 1 ≤ t) :
    (i - e).val = (t + 1) % n := by
  have : i - e = ((i - 1) - e) + 1 := by ring
  rw [this, Fin.val_add, ht]
  simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n from hB.two_le_n)]

theorem eq_h1_iff (i : Fin n) : i = e + 1 ↔ (i - e).val = 1 := by
  constructor
  · rintro rfl; simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n from hB.two_le_n)]
  · intro h
    have : i - e = 1 := Fin.ext (by rw [h]; simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n from hB.two_le_n)])
    rw [← this]; ring

theorem inbox_tau (c : Config n (Fin n)) (i : Fin n) :
    inbox (dev C A (Function.update d (e + 1) x)) (tau e l x c) i =
      if 1 ≤ ((i - 1) - e).val ∧ ((i - 1) - e).val ≤ l then
        (inbox (dev C A d) c i).set (((i - 1) - e).val - 1) x
      else inbox (dev C A d) c i := by
  simp only [inbox]
  split_ifs with ht
  · have hh : i - 1 ∉ C := (hB.not_mem_iff _).mpr ht
    rw [dev_honest hh, dev_honest hh, aLead_sent_eq, aLead_sent_eq, tau_length, ← List.take_set]
    congr 1
    unfold tau
    rcases Nat.lt_or_ge 1 ((i - 1) - e).val with h2 | h2
    · rw [if_pos ⟨h2, ht.2⟩]
      have hne : i - 1 ≠ e + 1 := fun h => by rw [hB.eq_h1_iff] at h; omega
      rw [Function.update_of_ne hne, show ((i - 1) - e).val - 1 = (((i - 1) - e).val - 2) + 1 by
        omega, List.set_cons_succ]
    · have h1 : ((i - 1) - e).val = 1 := by omega
      rw [if_neg (by omega), h1, Nat.sub_self, List.set_cons_zero,
        (hB.eq_h1_iff (i - 1)).mpr h1, Function.update_self]
  · have hm : i - 1 ∈ C := by by_contra h; exact ht ((hB.not_mem_iff _).mp h)
    rw [dev_adv hm, dev_adv hm]
    unfold tau
    rw [if_neg (by omega)]

theorem out_tau (c : Config n (Fin n)) (i : Fin n) :
    (dev C A (Function.update d (e + 1) x) i).out (tau e l x c i) = none ↔
      (dev C A d i).out (c i) = none := by
  by_cases hi : i ∈ C
  · rw [dev_adv hi, dev_adv hi]
    unfold tau; rw [if_neg (by have := (hB.not_mem_iff i).not.mp (not_not.mpr hi); omega)]
  · rw [dev_honest hi, dev_honest hi, aLead_out, aLead_out]
    simp only [validate, tau_length]
    split_ifs <;> simp

theorem pred_val (i : Fin n) (h : 1 ≤ (i - e).val) : ((i - 1) - e).val = (i - e).val - 1 := by
  have : (i - 1) - e = (i - e) - 1 := by ring
  have h2 := hB.two_le_n
  rw [this, Fin.sub_val_of_le]
  · simp [Nat.mod_eq_of_lt (show 1 < n by omega)]
  · rw [Fin.le_def]; simp [Nat.mod_eq_of_lt (show 1 < n by omega)]; omega

theorem eq_firstAdv (i : Fin n) (h : ((i - 1) - e).val = l) : i = firstAdv e l := by
  have h1 : (i - 1) - e = ((l : ℕ) : Fin n) := Fin.ext (by
    rw [h, Fin.val_natCast, Nat.mod_eq_of_lt hB.lt])
  simp only [firstAdv]
  have : i = ((i - 1) - e) + e + 1 := by ring
  rw [this, h1]; push_cast; ring

theorem step_tau {c : Config n (Fin n)} (hinv : Inv (dev C A d) c) {i : Fin n}
    (he : Enabled (dev C A d) c i)
    (hu : Untainted e l (deliver (dev C A d) c i)) :
    Enabled (dev C A (Function.update d (e + 1) x)) (tau e l x c) i ∧
      tau e l x (deliver (dev C A d) c i) =
        deliver (dev C A (Function.update d (e + 1) x)) (tau e l x c) i := by
  have hen : Enabled (dev C A (Function.update d (e + 1) x)) (tau e l x c) i := by
    refine ⟨(hB.out_tau c i).mpr he.1, ?_⟩
    rw [hB.inbox_tau, tau_length]
    split_ifs <;> simp [he.2]
  refine ⟨hen, ?_⟩
  obtain ⟨y, hy, hd⟩ := deliver_of_enabled he
  obtain ⟨y', hy', hd'⟩ := deliver_of_enabled hen
  rw [hd, hd', tau_update]
  congr 1
  rw [tau_length, hB.inbox_tau] at hy'
  have hpre : c i <+: inbox (dev C A d) c i := (hinv i).1
  simp only [tau, Function.update_self]
  by_cases hs : 2 ≤ (i - e).val ∧ (i - e).val ≤ l
  · have ht := hB.pred_val i (by omega)
    rw [if_pos ⟨by omega, by omega⟩, ht, show (i - e).val - 1 - 1 = (i - e).val - 2 by omega] at hy'
    rw [if_pos hs, if_pos hs]
    obtain ⟨y'', hy'', heq⟩ := set_snoc_of_prefix hpre hy ((i - e).val - 2) x
    rw [heq, Option.some_injective _ (hy''.symm.trans hy')]
  · rw [if_neg hs, if_neg hs]
    congr 2
    split_ifs at hy' with ht
    · -- `i - 1 = h_l`, so `i` is the first adversary, which is untainted after the step
      have hsv := hB.pred_pos i rfl ht.1
      have htl : ((i - 1) - e).val = l := by
        rcases Nat.lt_or_ge (((i - 1) - e).val + 1) n with h | h
        · rw [Nat.mod_eq_of_lt h] at hsv; omega
        · have := hB.lt; omega
      have hi := hB.eq_firstAdv i htl
      have hu' : (c i).length + 2 ≤ l := by
        have := hu; simp only [Untainted, ← hi, hd, Function.update_self, List.length_append,
          List.length_singleton] at this; omega
      rw [htl, List.getElem?_set, if_neg (by omega), hy] at hy'
      exact Option.some_injective _ hy'
    · rw [hy] at hy'; exact Option.some_injective _ hy'

/-- **Simulation.** As long as the coalition has not received the secret of `h_1`, executions with a
different secret `x` of `h_1` look the same to the coalition. -/
theorem reach_tau {c : Config n (Fin n)} (hc : Reach (dev C A d) c) (hu : Untainted e l c) :
    Reach (dev C A (Function.update d (e + 1) x)) (tau e l x c) := by
  induction hc with
  | refl => rw [tau_init]; exact Relation.ReflTransGen.refl
  | tail hb hs ih =>
    rename_i b c'
    obtain ⟨i, he, rfl⟩ := hs
    have hub : Untainted e l b := le_trans (Nat.add_le_add_right
      (le_deliver (P := dev C A d) b i (firstAdv e l)).length_le 1) hu
    obtain ⟨hen, heq⟩ := hB.step_tau (show Reach (dev C A d) b from hb).inv he hu
    rw [heq]
    exact (ih hub).tail ⟨i, hen, rfl⟩

theorem tau_adv (c : Config n (Fin n)) {i : Fin n} (hi : i ∈ C) : tau e l x c i = c i := by
  unfold tau; rw [if_neg (by have := (hB.not_mem_iff i).not.mp (not_not.mpr hi); omega)]

/-- Messages flow through the honest segment at most one ahead (the origin may add one). -/
theorem sent_seg_le {b : Config n (Fin n)} (hb : Reach (dev C A d) b) :
    ∀ s ≤ l, ((dev C A d (e + ((s : ℕ) : Fin n))).sent (b (e + ((s : ℕ) : Fin n)))).length ≤
      ((dev C A d e).sent (b e)).length +
        (if 1 ≤ ((0 : Fin n) - e).val ∧ ((0 : Fin n) - e).val ≤ s then 1 else 0) := by
  intro s hs
  induction s with
  | zero => simp
  | succ s ih =>
    have hlt := hB.lt
    set h := e + ((s + 1 : ℕ) : Fin n)
    have hh : h ∉ C := (hB.not_mem_iff h).mpr (by
      rw [hB.val_sub_e (by omega)]; omega)
    have hpred : h - 1 = e + ((s : ℕ) : Fin n) := by simp only [h]; push_cast; ring
    have h1 : (b h).length ≤ ((dev C A d (e + ((s : ℕ) : Fin n))).sent
        (b (e + ((s : ℕ) : Fin n)))).length := by
      have := (hb.inv h).1.length_le; rwa [inbox, hpred] at this
    have h2 : ((dev C A d h).sent (b h)).length ≤ (b h).length + (if h = 0 then 1 else 0) := by
      rw [dev_honest hh, aLead_sent_eq]; split_ifs <;> simp <;> omega
    have ih' := ih (by omega)
    have h0 : h = 0 ↔ ((0 : Fin n) - e).val = s + 1 := by
      constructor
      · intro h0; rw [← h0]; simp only [h, add_sub_cancel_left, Fin.val_natCast,
          Nat.mod_eq_of_lt (show s + 1 < n by omega)]
      · intro h0
        have : (0 : Fin n) - e = ((s + 1 : ℕ) : Fin n) := Fin.ext (by
          rw [h0, Fin.val_natCast, Nat.mod_eq_of_lt (show s + 1 < n by omega)])
        simp only [h]; rw [← this]; ring
    by_cases hz : h = 0
    · have := h0.mp hz
      rw [if_pos hz] at h2; rw [if_neg (by omega)] at ih'; rw [if_pos (by omega)]; omega
    · rw [if_neg hz] at h2
      have : ((0 : Fin n) - e).val ≠ s + 1 := fun h' => hz (h0.mpr h')
      split_ifs at ih' ⊢ <;> omega

/-- Before `e` has sent `n - l = k` messages, the coalition cannot know the secret of `h_1`:
some reachable untainted configuration already has `e` sending `k` messages. -/
theorem exists_untainted (hk : n - l + 1 ≤ l) {c : Config n (Fin n)} (hc : Reach (dev C A d) c)
    (hm : n - l ≤ ((dev C A d e).sent (c e)).length) :
    ∃ c₀, Reach (dev C A d) c₀ ∧ Untainted e l c₀ ∧
      n - l ≤ ((dev C A d e).sent (c₀ e)).length := by
  induction hc with
  | refl => exact ⟨init, Relation.ReflTransGen.refl, by simp [Untainted, init]; exact hB.one_le, hm⟩
  | tail hb hs ih =>
    rename_i b c'
    by_cases hbm : n - l ≤ ((dev C A d e).sent (b e)).length
    · exact ih hbm
    push_neg at hbm
    obtain ⟨i, he, rfl⟩ := hs
    refine ⟨_, Relation.ReflTransGen.tail hb ⟨i, he, rfl⟩, ?_, hm⟩
    have hiC : i ∈ C := by
      by_contra hi
      have : deliver (dev C A d) b i e = b e := deliver_ne b (fun h => hi (h ▸ hB.mem))
      rw [this] at hm; omega
    have hlt := hB.lt
    have hhl : e + ((l : ℕ) : Fin n) ∉ C := (hB.not_mem_iff _).mpr (by
      rw [hB.val_sub_e (by omega)]; omega)
    have hne : e + ((l : ℕ) : Fin n) ≠ i := fun h => hhl (h ▸ hiC)
    have hc' : Reach (dev C A d) (deliver (dev C A d) b i) := (show Reach _ b from hb).deliver i
    have h1 := (hc'.inv (firstAdv e l)).1.length_le
    have hpred : firstAdv e l - 1 = e + ((l : ℕ) : Fin n) := by simp only [firstAdv]; push_cast; ring
    rw [inbox, hpred, deliver_ne b hne] at h1
    have h2 := hB.sent_seg_le (show Reach _ b from hb) l le_rfl
    simp only [Untainted]
    split_ifs at h2 <;> omega

/-- `p`-prefix of the messages eventually sent by `i`. -/
def PrefixSent (P : Profile n (Fin n)) (i : Fin n) (p : ℕ) (L : List (Fin n)) : Prop :=
  ∃ c, Reach P c ∧ p ≤ ((P i).sent (c i)).length ∧ L = ((P i).sent (c i)).take p

omit hB in
theorem PrefixSent.unique {P : Profile n (Fin n)} {i : Fin n} {p : ℕ} {L L' : List (Fin n)}
    (h : PrefixSent P i p L) (h' : PrefixSent P i p L') : L = L' := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  obtain ⟨c', hc', hp', rfl⟩ := h'
  obtain ⟨r, -, hle⟩ := exists_reach_ge (P := P) ![c, c'] (by intro j; fin_cases j <;> assumption)
  have h1 := (P i).sent_mono (hle 0 i)
  have h2 := (P i).sent_mono (hle 1 i)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  obtain ⟨t, ht⟩ := h1
  obtain ⟨t', ht'⟩ := h2
  have e1 := congrArg (List.take p) ht
  have e2 := congrArg (List.take p) ht'
  rw [List.take_append_of_le_length hp] at e1
  rw [List.take_append_of_le_length hp'] at e2
  rw [e1, e2]

/-- **The first `k` messages of `e` do not depend on the secret of `h_1`.** -/
theorem prefixSent_update (hk : n - l + 1 ≤ l) {L : List (Fin n)}
    (h : PrefixSent (dev C A d) e (n - l) L) :
    PrefixSent (dev C A (Function.update d (e + 1) x)) e (n - l) L := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  obtain ⟨c₀, hc₀, hu, hp₀⟩ := hB.exists_untainted hk hc hp
  have huniq := PrefixSent.unique ⟨c, hc, hp, rfl⟩ ⟨c₀, hc₀, hp₀, rfl⟩
  rw [huniq]
  refine ⟨_, hB.reach_tau (x := x) hc₀ hu, ?_, ?_⟩
  · rw [hB.tau_adv _ hB.mem, dev_adv hB.mem]; rwa [dev_adv hB.mem] at hp₀
  · rw [hB.tau_adv _ hB.mem, dev_adv hB.mem, dev_adv hB.mem]

theorem gap_eq : gap C e = l := by
  have hlt := hB.lt
  rw [gap_eq_iff hB.mem]
  constructor
  · by_contra h
    have := (hB.not_mem_iff _).mp h
    rcases Nat.lt_or_ge (l + 1) n with h1 | h1
    · rw [hB.val_sub_e h1] at this; omega
    · have : l + 1 = n := by omega
      simp only [this, Fin.natCast_self, add_zero, sub_self, Fin.val_zero] at *
      omega
  · intro s hs
    rw [hB.not_mem_iff, hB.val_sub_e (by omega)]; omega

end Block

theorem list_sum_map_range (m : ℕ) (g : ℕ → Fin n) :
    (List.map g (List.range m)).sum = ∑ t ∈ Finset.range m, g t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_of_getElem? {D : List (Fin n)} {m : ℕ} (hD : D.length = m) {v : ℕ → Fin n}
    (h : ∀ s < m, D[m - 1 - s]? = some (v s)) : D.sum = ∑ s ∈ Finset.range m, v s := by
  have e : D = (List.range m).map fun t => v (m - 1 - t) := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < m
    · rw [List.getElem?_map, List.getElem?_range ht, Option.map_some]
      have := h (m - 1 - t) (by omega)
      rwa [show m - 1 - (m - 1 - t) = t by omega] at this
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  rw [e, list_sum_map_range, Finset.sum_range_reflect]

theorem card_filter_eq_zero (a : Fin n) :
    (Finset.univ.filter fun d : Fin n → Fin n => d a = 0).card * n = n ^ n := by
  classical
  let eqv : (Fin n → Fin n) ≃ {d : Fin n → Fin n // d a = 0} × Fin n :=
    { toFun := fun d => (⟨Function.update d a 0, by simp⟩, d a)
      invFun := fun p => Function.update p.1.1 a p.2
      left_inv := fun d => by simp
      right_inv := fun p => by
        obtain ⟨⟨d, hd⟩, v⟩ := p
        ext
        · simp only [Function.update_idem]
          rw [← hd, Function.update_eq_self]
        · simp }
  have := Fintype.card_congr eqv
  rw [Fintype.card_prod, Fintype.card_subtype, Fintype.card_fun, Fintype.card_fin] at this
  exact this.symm

namespace Block

variable (hB : Block C e l)
include hB

/-- If the outcome is `j`, then `j` is the sum of the first `k` messages of `e` and of the secrets of
the segment. -/
theorem outcome_imp (hk : n - l + 1 ≤ l) {d : Fin n → Fin n} {j : Fin n}
    (h : outcome (dev C A d) = some j) :
    ∃ L, PrefixSent (dev C A d) e (n - l) L ∧
      L.sum + ∑ s ∈ Finset.range l, d (e + ((s + 1 : ℕ) : Fin n)) = j := by
  have hC : C.Nonempty := ⟨e, hB.mem⟩
  have hlt := hB.lt
  obtain ⟨g, hg, hcond⟩ := (lemma_3_3 hC j).mp (fun h' hh' => outcome_eq_some.mp h h')
  have he1 : e + 1 ∉ C := (hB.not_mem_iff _).mpr (by
    rw [(hB.eq_h1_iff (e + 1)).mp rfl]; exact ⟨le_rfl, hB.one_le⟩)
  obtain ⟨hm, hsum, hsec⟩ := hcond e hB.mem he1
  rw [hB.gap_eq] at hsec
  set m := (A e).sent (g e)
  refine ⟨m.take (n - l), ⟨g, hg, by rw [dev_adv hB.mem]; show n - l ≤ m.length; omega,
    by rw [dev_adv hB.mem]⟩, ?_⟩
  rw [← hsum, ← List.take_append_drop (n - l) (m.take n), List.sum_append, List.take_take,
    min_eq_left (by omega)]
  congr 1
  symm
  apply sum_of_getElem? (by simp; omega)
  intro s hs
  rw [List.getElem?_drop, List.getElem?_take, if_pos (by omega),
    show n - l + (l - 1 - s) = n - 1 - s by omega]
  exact hsec s hs

theorem card_le (hk : n - l + 1 ≤ l) (j : Fin n) :
    (Finset.univ.filter fun d : Fin n → Fin n => outcome (dev C A d) = some j).card ≤
      (Finset.univ.filter fun d : Fin n → Fin n => d (e + 1) = 0).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun d => Function.update d (e + 1) 0)
  · intro d _; simp
  · intro d1 hd1 d2 hd2 heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hd1 hd2
    have hoff : ∀ i, i ≠ e + 1 → d1 i = d2 i := fun i hi => by
      have := congrFun heq i; simpa [Function.update_of_ne hi] using this
    have hd2' : d2 = Function.update d1 (e + 1) (d2 (e + 1)) := by
      funext i; rcases eq_or_ne i (e + 1) with rfl | hi
      · simp
      · rw [Function.update_of_ne hi, hoff i hi]
    obtain ⟨L1, hL1, hs1⟩ := hB.outcome_imp hk hd1
    obtain ⟨L2, hL2, hs2⟩ := hB.outcome_imp hk hd2
    have hL1' := hB.prefixSent_update (x := d2 (e + 1)) hk hL1
    rw [← hd2'] at hL1'
    have := hL1'.unique hL2
    subst this
    have hlt := hB.lt
    have hsums : ∑ s ∈ Finset.range l, d1 (e + ((s + 1 : ℕ) : Fin n)) =
        ∑ s ∈ Finset.range l, d2 (e + ((s + 1 : ℕ) : Fin n)) := by
      rw [← hs2] at hs1; exact add_left_cancel hs1
    obtain ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hB.one_le; omega⟩
    rw [hl', Finset.sum_range_succ', Finset.sum_range_succ'] at hsums
    have hrest : ∑ s ∈ Finset.range l', d1 (e + ((s + 1 + 1 : ℕ) : Fin n)) =
        ∑ s ∈ Finset.range l', d2 (e + ((s + 1 + 1 : ℕ) : Fin n)) := by
      refine Finset.sum_congr rfl fun s hs => hoff _ ?_
      simp only [Finset.mem_range] at hs
      intro h
      have := congrArg (fun y => (y - e).val) h
      simp only [add_sub_cancel_left, Fin.val_natCast, Fin.val_one',
        Nat.mod_eq_of_lt (show s + 1 + 1 < n by omega),
        Nat.mod_eq_of_lt (show 1 < n by omega)] at this
      omega
    rw [hrest] at hsums
    have h0 : d1 (e + 1) = d2 (e + 1) := by
      have := add_left_cancel hsums; simpa using this
    funext i
    rcases eq_or_ne i (e + 1) with rfl | hi
    · exact h0
    · exact hoff i hi

end Block

/-- **Claim D.1** (resilience of `A-LEADuni` against consecutive coalitions, after Abraham et al.):
if the coalition is one block of `k` consecutive processors and `2k + 1 ≤ n`, then every
(deterministic) deviation elects each processor with probability at most `1/n`. -/
theorem claim_D_1 {C : Finset (Fin n)} {e : Fin n} {l : ℕ} (hB : Block C e l)
    (hk : 2 * C.card + 1 ≤ n) (A : Profile n (Fin n)) {σ : ℕ → Fin n} (hσ : Fair σ) (j : Fin n) :
    prob (deviate aLead C A) σ (some j) ≤ 1 / n := by
  classical
  rw [hB.card] at hk
  have hk' : n - l + 1 ≤ l := by have := hB.lt; omega
  have h1 := hB.card_le (A := A) hk' j
  have h2 := card_filter_eq_zero (n := n) (e + 1)
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  unfold prob
  simp only [outcomeUnder_eq _ hσ]
  rw [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [div_le_div_iff₀ (pow_pos hn n) hn]
  have : ((Finset.univ.filter fun d : Fin n → Fin n => outcome (dev C A d) = some j).card : ℝ) * n
      ≤ (n : ℝ) ^ n := by exact_mod_cast (Nat.mul_le_mul_right n h1).trans h2.le
  simpa [mul_comm] using this

/-- A singleton coalition is a block. -/
theorem block_singleton (hn : 2 ≤ n) (e : Fin n) : Block {e} e (n - 1) where
  mem := Finset.mem_singleton_self e
  one_le := by omega
  lt := by omega
  honest_iff x := by
    rw [Finset.mem_singleton]
    constructor
    · intro hx
      refine ⟨(x - e).val, ?_, by have := (x - e).isLt; omega, by simp⟩
      rw [Nat.one_le_iff_ne_zero, Ne, Fin.val_eq_zero_iff, sub_eq_zero]; exact hx
    · rintro ⟨s, h1, h2, rfl⟩ h
      have := congrArg (fun y => (y - e).val) h
      simp only [add_sub_cancel_left, sub_self, Fin.val_zero, Fin.val_natCast,
        Nat.mod_eq_of_lt (show s < n by omega)] at this
      omega

/-- `A-LEADuni` is `0`-`1`-unbiased for `n ≥ 3`: no single processor can bias the election. -/
theorem isUnbiased_aLead_one (hn : 3 ≤ n) : IsUnbiased (n := n) aLead 0 1 := by
  intro σ hσ C hC A j
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hC
  rw [add_zero]
  exact claim_D_1 (block_singleton (by omega) e) (by simp; omega) A hσ j

/-- `A-LEADuni` is `0`-`1`-resilient for `n ≥ 3` (a strong `1`-Nash equilibrium against
deterministic deviations), the result of Abraham et al. recalled in the paper. -/
theorem isResilient_aLead_one (hn : 3 ≤ n) : IsResilient (n := n) aLead 0 1 := by
  have := (lemma_2_4 aLead isFLE_aLead 0 1).2 le_rfl le_rfl (isUnbiased_aLead_one hn)
  simpa using this

/-- **Claim D.1 is false without a bound on `k`** (the paper states it for every consecutive
coalition; its proof needs `k` smaller than the honest segment, i.e. `2k < n`). For `n ≥ 3` the
block of all processors but the origin (`k = n - 1`) forces the outcome by the attack of
Lemma 4.1. -/
theorem claim_D_1_false (hn : 3 ≤ n) :
    ∃ (C : Finset (Fin n)) (e : Fin n) (l : ℕ), Block C e l ∧ ∃ A : Profile n (Fin n),
      ∀ σ, Fair σ → prob (deviate aLead C A) σ (some 0) = 1 := by
  classical
  have h1n : (1 : Fin n) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega)] at this
  set C : Finset (Fin n) := Finset.univ.erase 0
  have hB : Block C (-1) 1 := by
    refine ⟨by simp [C, h1n.symm, neg_eq_zero]; omega, le_rfl, by omega, fun x => ?_⟩
    simp only [C, Finset.mem_erase, Finset.mem_univ, and_true, not_not]
    constructor
    · rintro rfl; exact ⟨1, le_rfl, le_rfl, by simp⟩
    · rintro ⟨s, h1, h2, rfl⟩; obtain rfl : s = 1 := by omega
      simp
  have hcard : C.card = n - 1 := by simp [C]
  obtain ⟨A, hA⟩ := lemma_4_1 (C := C) ⟨-1, hB.mem⟩ (by simp [C]) (by
    intro a ha
    rw [hcard]
    by_contra hg; push_neg at hg
    have h1 := not_mem_of_lt_gap ha (s := 0) (by omega)
    have h2 := not_mem_of_lt_gap ha (s := 1) (by omega)
    simp only [C, Finset.mem_erase, Finset.mem_univ, and_true, not_not] at h1 h2
    push_cast at h1 h2
    apply h1n
    have : (a + 1) + 1 = a + 2 := by ring
    rw [h1, zero_add] at this; rw [this, h2]) 0
  exact ⟨C, -1, 1, hB, A, fun σ hσ => prob_eq_one_of_forall (fun d => (hA d).1) hσ⟩

end Podc.FairLeaderElection
