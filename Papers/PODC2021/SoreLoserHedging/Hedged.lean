import Papers.PODC2021.SoreLoserHedging.Model

/-!
# Lemmas 1–6 of §7.1: premium accounting of the hedged multi-party swap

All statements are about an admissible execution `X` (`S.Admissible X C`) and a conforming party
`v ∉ C`; the coalition `C` is arbitrary.
-/

namespace Podc.SoreLoserHedging

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Swap

variable {S : Swap V} {X : Exec V} {C : Finset V}

/-! ### Basic facts about paths -/

lemma PPath.ne_nil {G : Digraph V} {i v : V} {q : List V} (h : PPath G i v q) : q ≠ [] := by
  rintro rfl; simp [PPath] at h

lemma KPath.ne_nil {G : Digraph V} {i v : V} {q : List V} (h : KPath G i v q) : q ≠ [] := by
  rintro rfl; simp [KPath] at h

lemma head_eq_getElem_zero {q : List V} {v : V} (h : q.head? = some v) (h0 : 0 < q.length) :
    q[0] = v := by
  cases q with
  | nil => simp at h0
  | cons a q => simpa using h

lemma getLast_eq_getElem {q : List V} {i : V} (h : q.getLast? = some i) (h0 : 0 < q.length) :
    q[q.length - 1] = i := by
  rw [List.getLast?_eq_getElem?] at h
  rw [List.getElem?_eq_getElem (by omega)] at h
  exact Option.some.inj h

/-- If `v` occurs in `q` and `q` starts with some `w ≠ v`, then `v` occurs at a positive
index. -/
lemma exists_pos_index {q : List V} {v w : V} (hq : q.head? = some w) (hne : w ≠ v)
    (hv : v ∈ q) : ∃ k, ∃ hk : k < q.length, 0 < k ∧ q[k] = v := by
  obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
  refine ⟨k, hk, Nat.pos_of_ne_zero ?_, hkv⟩
  rintro rfl
  exact hne ((head_eq_getElem_zero hq hk).symm.trans hkv)


lemma allIn_isSome {f : V → V → Option ℕ} {v : V} :
    (S.allIn f v).isSome ↔ ∀ u ∈ inN S.G v, (f u v).isSome := by
  unfold allIn; split_ifs with h
  · simpa using h
  · simpa using h

lemma allIn_le {f : V → V → Option ℕ} {v : V} {m d : ℕ} (h : S.allIn f v = some m)
    (hd : ∀ u ∈ inN S.G v, ∀ t, f u v = some t → t ≤ d) : m ≤ d := by
  unfold allIn at h
  split_ifs at h with hall
  cases h
  refine Finset.sup_le fun u hu => ?_
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hall u hu)
  rw [ht]
  exact hd u hu t ht

variable (hA : S.Admissible X C)
include hA

/-! ### Unforgeability consequences -/

/-- The first redemption premium a conforming party observes does not contain it, so `v ∥ q`
is a path. -/
lemma not_mem_fp {v i : V} {q : List V} {t0 : ℕ} (hv : v ∉ C) (hi : i ≠ v)
    (h : X.fp i v = some (t0, q)) : v ∉ q := by
  intro hmem
  obtain ⟨⟨w, hw, hrw⟩, -⟩ := hA.fp_some i v t0 q h
  obtain ⟨-, -, hpp, -⟩ := hA.rp_ok i v w t0 q hrw
  have hne : w ≠ v := by rintro rfl; exact S.loopless w (mem_outN.1 hw)
  obtain ⟨k, hk, hk0, hkv⟩ := exists_pos_index hpp.1 hne hmem
  obtain ⟨u', t', hr', -⟩ := hA.rp_sig i v w t0 q hrw k hk hk0 (hkv ▸ hv)
  rw [hkv] at hr'
  have hu' : u' ∈ inN S.G v := mem_inN.2 (hA.rp_ok _ _ _ _ _ hr').1
  rw [hA.conf_rp v hv i hi u' hu', h] at hr'
  simp [hmem] at hr'

/-- A conforming party's first observed hashkey does not contain it; hence its forwarded key
`v ∥ q` is accepted on every entering arc, one step later. -/
lemma ky_fwd {v i : V} {q : List V} {tf : ℕ} (hv : v ∉ C) (hi : i ≠ v)
    (h : X.fk i v = some (tf, q)) : ∀ u ∈ inN S.G v, X.ky i u v = some (tf + 1, v :: q) := by
  obtain ⟨⟨w, hw, hkw⟩, -⟩ := hA.fk_some i v tf q h
  obtain ⟨-, -, hkp, htf⟩ := hA.ky_ok i v w tf q hkw
  have hne : w ≠ v := by rintro rfl; exact S.loopless w (mem_outN.1 hw)
  have hnot : v ∉ q := by
    intro hmem
    obtain ⟨k, hk, hk0, hkv⟩ := exists_pos_index hkp.1 hne hmem
    have hs := hA.ky_sig i v w tf q hkw k hk hk0 (hkv ▸ hv)
    rw [hkv] at hs
    simp only [Signed, if_neg hi.symm] at hs
    obtain ⟨tf', h', hle⟩ := hs
    rw [h] at h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    omega
  have hq0 := KPath.ne_nil hkp
  have hkp' : KPath S.G i v (v :: q) := by
    obtain ⟨h1, h2, h3, h4⟩ := hkp
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [List.getLast?_cons, h2]; rfl
    · cases q with
      | nil => exact absurd rfl hq0
      | cons a q =>
        simp only [List.head?_cons, Option.some.injEq] at h1
        subst h1
        exact List.IsChain.cons_cons (mem_outN.1 hw) h3
    · rw [List.dropLast_cons_of_ne_nil hq0]
      exact List.nodup_cons.2 ⟨fun hm => hnot (List.mem_of_mem_dropLast hm), h4⟩
  intro u hu
  rw [hA.conf_ky v hv i hi u hu, h]
  simp only [List.length_cons]
  rw [if_pos ⟨hkp', by omega⟩]

/-- A conforming leader that never releases its secret: no hashkey for it is ever accepted. -/
lemma ky_none_of_rel {v : V} (hv : v ∉ C) (hvL : v ∈ S.L) (hrel : S.rel X v = none) :
    ∀ u w, X.ky v u w = none := by
  intro u w
  by_contra hne
  obtain ⟨⟨t, q⟩, hk⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨hadj, -, hkp, -⟩ := hA.ky_ok v u w t q hk
  by_cases hw : w = v
  · subst hw
    rw [hA.conf_ky_lead w hv hvL u (mem_inN.2 hadj), hrel] at hk
    simp at hk
  · have hq0 := KPath.ne_nil hkp
    have hlen : 0 < q.length := List.length_pos_iff.2 hq0
    have hlast := getLast_eq_getElem hkp.2.1 hlen
    have hk0 : 0 < q.length - 1 := by
      rcases Nat.lt_or_ge 1 q.length with h1 | h1
      · omega
      · exfalso
        have h0 := head_eq_getElem_zero hkp.1 hlen
        have : q.length - 1 = 0 := by omega
        simp only [this] at hlast
        exact hw (h0.symm.trans hlast)
    have hs := hA.ky_sig v u w t q hk (q.length - 1) (by omega) hk0 (hlast ▸ hv)
    rw [hlast] at hs
    simp only [Signed, if_pos rfl] at hs
    obtain ⟨-, r, hr, -⟩ := hs
    rw [hrel] at hr
    simp at hr

/-! ### Activation propagates backwards through a conforming party -/

/-- A conforming leader deposited its redemption premium iff all its entering escrow premiums
arrived; then every entering arc carries an escrow premium. -/
lemma lead_dep {v : V} (hv : v ∉ C) (hvL : v ∈ S.L) {u : V} (hu : u ∈ inN S.G v)
    (h : (X.rp v u v).isSome) :
    X.rp v u v = some (S.t1 + 1, [v]) ∧ ∀ u' ∈ inN S.G v, (X.ep u' v).isSome := by
  rw [hA.conf_rp_lead v hv hvL u hu] at h ⊢
  split_ifs at h ⊢ with hc
  · refine ⟨rfl, fun u' hu' => ?_⟩
    have := hc u' hu'
    cases he : X.ep u' v <;> simp_all [OptLe]
  · simp at h

/-- If a conforming party `v` has an activated leaving arc, all arcs entering `v` are
activated. This is what lets `v` pass escrow premiums through (Lemma 3). -/
lemma act_in {v w : V} (hv : v ∉ C) (hw : w ∈ outN S.G v) (hact : S.Act X v w) :
    ∀ u ∈ inN S.G v, S.Act X u v := by
  have hnemp : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  have t2ge := S.t2_ge
  -- the leader case: `v` deposited its own redemption premium
  have hlead : v ∈ S.L → ∃ u ∈ inN S.G v, (X.rp v u v).isSome := by
    intro hvL
    obtain ⟨t, q, hr, -⟩ := optLe_iff.1 (hact.2 v hvL)
    obtain ⟨-, -, hpp, -⟩ := hA.rp_ok v v w t q hr
    have hne : w ≠ v := by rintro rfl; exact S.loopless w (mem_outN.1 hw)
    have hlen : 0 < q.length := List.length_pos_iff.2 (PPath.ne_nil hpp)
    have hlast := getLast_eq_getElem hpp.2.1 hlen
    have hk0 : 0 < q.length - 1 := by
      rcases Nat.lt_or_ge 1 q.length with h1 | h1
      · omega
      · exfalso
        have h0 := head_eq_getElem_zero hpp.1 hlen
        have : q.length - 1 = 0 := by omega
        simp only [this] at hlast
        exact hne (h0.symm.trans hlast)
    obtain ⟨u', t', hr', -⟩ := hA.rp_sig v v w t q hr (q.length - 1) (by omega) hk0 (hlast ▸ hv)
    rw [hlast] at hr'
    exact ⟨u', mem_inN.2 (hA.rp_ok _ _ _ _ _ hr').1, by rw [hr']; rfl⟩
  intro u hu
  refine ⟨?_, fun i hi => ?_⟩
  · -- escrow premium on `(u, v)`
    by_cases hvL : v ∈ S.L
    · obtain ⟨u', hu', h'⟩ := hlead hvL
      exact (lead_dep hA hv hvL hu' h').2 u hu
    · have h := hact.1
      rw [hA.conf_ep v hv w hw, if_neg hvL] at h
      have : (S.allIn X.ep v).isSome := by
        cases hm : S.allIn X.ep v <;> simp_all
      exact allIn_isSome.1 this u hu
  · by_cases hiv : i = v
    · subst hiv
      obtain ⟨u', hu', h'⟩ := hlead hi
      have hall := (lead_dep hA hv hi hu' h').2
      rw [hA.conf_rp_lead i hv hi u hu, if_pos]
      · simp only [OptLe]; omega
      · intro u'' hu''
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hall u'' hu'')
        rw [ht]
        exact (hA.ep_ok _ _ _ ht).2.trans (S.dl1_le _)
    · obtain ⟨t, q, hr, -⟩ := optLe_iff.1 (hact.2 i hi)
      cases hf : X.fp i v with
      | none => rw [hA.fp_none i v hf w hw] at hr; simp at hr
      | some a =>
        obtain ⟨t0, q0⟩ := a
        have hnm := not_mem_fp hA hv hiv hf
        obtain ⟨⟨w0, hw0, hr0⟩, -⟩ := hA.fp_some i v t0 q0 hf
        obtain ⟨-, -, hpp, ht0⟩ := hA.rp_ok i v w0 t0 q0 hr0
        have hcard := (List.nodup_cons.2 ⟨hnm, hpp.2.2.2⟩).length_le_card
        rw [hA.conf_rp v hv i hiv u hu, hf]
        simp only [hnm, not_false_eq_true, if_true, OptLe]
        simp only [List.length_cons] at hcard
        omega

/-! ### Escrow premiums (Lemmas 3 and 5) -/

lemma act_of_es {v w : V} (hv : v ∉ C) (hw : w ∈ outN S.G v) (h : (X.es v w).isSome) :
    S.Act X v w := by
  rw [hA.conf_es v hv w hw] at h
  by_contra hn
  simp [hn] at h

lemma es_of_act {v w : V} (hv : v ∉ C) (hw : w ∈ outN S.G v) (hact : S.Act X v w)
    (h : v ∈ S.L ∨ (S.allIn X.es v).isSome) : (X.es v w).isSome := by
  rw [hA.conf_es v hv w hw, if_pos hact]
  have h3 := S.dl3_ge v
  by_cases hvL : v ∈ S.L
  · simp [hvL, acc, h3]
  · rw [if_neg hvL]
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (h.resolve_left hvL)
    have hle : m + 1 ≤ S.dl3 v := by
      have := allIn_le hm (d := S.dl3 v - 1) fun u hu t ht => by
        have h1 := (hA.es_ok u v t ht).2
        have h2 := S.dl3_fol u v (mem_inN.1 hu) hvL
        omega
      omega
    rw [hm]
    simp [acc]
    omega

lemma flowE_out_zero {v : V} (hv : v ∉ C) (h : v ∈ S.L ∨ (S.allIn X.es v).isSome) :
    ∀ w ∈ outN S.G v, S.flowE X v w = 0 := by
  intro w hw
  unfold flowE
  rw [if_neg]
  rintro ⟨hact, hes⟩
  have := es_of_act hA hv hw hact h
  simp [hes] at this

omit hA in
lemma flowE_le (u v : V) : S.flowE X u v ≤ Ein S.G S.L S.p S.fvs v := by
  unfold flowE; split_ifs <;> omega

omit hA in
lemma flowE_eq {u v : V} (hact : S.Act X u v) (hes : X.es u v = none) :
    S.flowE X u v = Ein S.G S.L S.p S.fvs v := by
  unfold flowE; rw [if_pos ⟨hact, hes⟩]

/-- A conforming party never loses escrow premiums (the escrow parts of Lemmas 3 and 5). -/
theorem netE_nonneg {v : V} (hv : v ∉ C) : 0 ≤ S.netE X v := by
  unfold netE
  have hin : (0 : ℤ) ≤ ∑ u ∈ inN S.G v, (S.flowE X u v : ℤ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  by_cases h : v ∈ S.L ∨ (S.allIn X.es v).isSome
  · rw [Finset.sum_eq_zero (s := outN S.G v) fun w hw => by
      rw [flowE_out_zero hA hv h w hw]; rfl]
    simpa using hin
  · push_neg at h
    obtain ⟨hvL, hno⟩ := h
    have hno' : ¬ ∀ u ∈ inN S.G v, (X.es u v).isSome := fun h' =>
      by rw [← allIn_isSome] at h'; simp_all
    push_neg at hno'
    obtain ⟨u, hu, hes⟩ := hno'
    have hes : X.es u v = none := by simpa using hes
    by_cases hact : ∃ w ∈ outN S.G v, S.Act X v w
    · obtain ⟨w, hw, hw'⟩ := hact
      have hactu := act_in hA hv hw hw' u hu
      have hout : ∑ w ∈ outN S.G v, (S.flowE X v w : ℤ) ≤ S.flowE X u v := by
        rw [flowE_eq hactu hes, Ein_eq, if_neg hvL]
        push_cast
        exact Finset.sum_le_sum fun w _ => by exact_mod_cast flowE_le v w
      have : (S.flowE X u v : ℤ) ≤ ∑ u ∈ inN S.G v, (S.flowE X u v : ℤ) :=
        Finset.single_le_sum (f := fun u => (S.flowE X u v : ℤ)) (fun _ _ => by positivity) hu
      linarith
    · push_neg at hact
      rw [Finset.sum_eq_zero (s := outN S.G v) fun w hw => ?_]
      · simpa using hin
      · unfold flowE; rw [if_neg]; · rfl
        exact fun h => hact w hw h.1

/-- A conforming leader with an activated entering arc whose asset was not escrowed collects at
least its own redemption premium `R(v)` in escrow premiums (Lemma 3, leader case). -/
lemma netE_lead {v u : V} (hv : v ∉ C) (hvL : v ∈ S.L) (hu : u ∈ inN S.G v)
    (hact : S.Act X u v) (hes : X.es u v = none) : (Rlead S.G S.p v : ℤ) ≤ S.netE X v := by
  unfold netE
  rw [Finset.sum_eq_zero (s := outN S.G v) fun w hw => by
    rw [flowE_out_zero hA hv (Or.inl hvL) w hw]; rfl]
  have : (S.flowE X u v : ℤ) ≤ ∑ u ∈ inN S.G v, (S.flowE X u v : ℤ) :=
    Finset.single_le_sum (f := fun u => (S.flowE X u v : ℤ)) (fun _ _ => by positivity) hu
  rw [flowE_eq hact hes, Ein_eq, if_pos hvL] at this
  simpa using this

/-! ### Redemption premiums (Lemma 2) -/

omit hA in
lemma flowR_some {i u v : V} {t : ℕ} {q : List V} (h : X.rp i u v = some (t, q)) :
    S.flowR X i u v = if OptLe (X.ky i u v) (S.B + q.length) then 0 else R S.G S.p q u := by
  unfold flowR; rw [h]

omit hA in
lemma flowR_none {i u v : V} (h : X.rp i u v = none) : S.flowR X i u v = 0 := by
  unfold flowR; rw [h]

omit hA in
lemma flowR_le {i u v : V} {t : ℕ} {q : List V} (h : X.rp i u v = some (t, q)) :
    S.flowR X i u v ≤ R S.G S.p q u := by
  rw [flowR_some h]; split_ifs <;> omega

omit hA in
lemma flowR_key {i u v : V} {t : ℕ} {q : List V} (h : X.rp i u v = some (t, q))
    {tk : ℕ} {qk : List V} (hk : X.ky i u v = some (tk, qk)) (hle : tk ≤ S.B + q.length) :
    S.flowR X i u v = 0 := by
  rw [flowR_some h, if_pos]; rw [hk]; exact hle

omit hA in
lemma flowR_of_aw {i v w : V} (h : S.Aw X i v w) : S.p ≤ S.flowR X i v w := by
  unfold Aw at h
  split at h
  · rename_i t q hr
    rw [flowR_some hr, if_neg h]; exact p_le_R _ _ _ _
  · exact h.elim

omit hA in
lemma sum_flowR_ge (i v : V) :
    S.p * #(S.awd X i v) ≤ ∑ w ∈ outN S.G v, S.flowR X i v w := by
  calc S.p * #(S.awd X i v) = ∑ _w ∈ S.awd X i v, S.p := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ w ∈ S.awd X i v, S.flowR X i v w :=
        Finset.sum_le_sum fun w hw => flowR_of_aw (Finset.mem_filter.1 hw).2
    _ ≤ ∑ w ∈ outN S.G v, S.flowR X i v w :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The release time of a conforming leader meets the deadline `B + 1` of its key `[v]`. -/
lemma rel_le {v : V} {r : ℕ} (h : S.rel X v = some r) : r ≤ S.B + 1 := by
  have h3 := S.dl3_ge v
  have h4 := S.dl3_le v
  unfold rel at h
  split_ifs at h
  · cases h; omega
  · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h
    have := allIn_le hm (d := S.B) fun u _ t ht => (hA.es_ok u v t ht).2.trans (S.dl3_le u)
    omega

/-- Lemma 2, core (for a party that is not the leader `i`): a conforming `v` gains at least `p`
from every leaving arc on which it is awarded the redemption premium for `i`. -/
theorem netR_ge {v i : V} (hv : v ∉ C) (hi : i ≠ v) :
    (S.p * #(S.awd X i v) : ℤ) ≤ S.netR X i v := by
  unfold netR
  have hsum := sum_flowR_ge (S := S) (X := X) i v
  cases hf : X.fp i v with
  | none =>
    rw [Finset.sum_eq_zero (s := inN S.G v) fun u hu => by
      unfold flowR; rw [hA.conf_rp v hv i hi u hu, hf]; rfl]
    simp only [sub_zero]; exact_mod_cast hsum
  | some a =>
    obtain ⟨t0, q0⟩ := a
    have hnm := not_mem_fp hA hv hi hf
    obtain ⟨⟨w0, hw0, hr0⟩, -⟩ := hA.fp_some i v t0 q0 hf
    obtain ⟨-, -, hpp, -⟩ := hA.rp_ok i v w0 t0 q0 hr0
    have hdep : ∀ u ∈ inN S.G v, X.rp i u v = some (t0 + 1, v :: q0) := fun u hu => by
      rw [hA.conf_rp v hv i hi u hu, hf]; simp [hnm]
    by_cases hk : OptLe (X.ky i v w0) (S.B + q0.length)
    · -- the key reached `v` in time: `v` forwards it and all its premiums are refunded
      obtain ⟨tk, qk, hkw, htk⟩ := optLe_iff.1 hk
      cases hfk : X.fk i v with
      | none => rw [hA.fk_none i v hfk w0 hw0] at hkw; simp at hkw
      | some b =>
        obtain ⟨tf, qf⟩ := b
        have htf := (hA.fk_some i v tf qf hfk).2 w0 hw0 tk qk hkw
        rw [Finset.sum_eq_zero (s := inN S.G v) fun u hu => by
          rw [flowR_key (hdep u hu) (ky_fwd hA hv hi hfk u hu) (by simp; omega)]; rfl]
        simp only [sub_zero]; exact_mod_cast hsum
    · -- `v` is awarded `R(q0, v) = p + ∑ R(v ∥ q0, u)`, which covers everything it pays
      have hw0a : w0 ∈ S.awd X i v := by
        refine Finset.mem_filter.2 ⟨hw0, ?_⟩
        unfold Aw; rw [hr0]; exact hk
      have hR : S.flowR X i v w0 = S.p + ∑ u ∈ inN S.G v, R S.G S.p (v :: q0) u := by
        rw [flowR_some hr0, if_neg hk]
        exact R_of_not_mem _ _ hpp.2.2.2 hnm
      have hout : ∑ u ∈ inN S.G v, S.flowR X i u v ≤ ∑ u ∈ inN S.G v, R S.G S.p (v :: q0) u :=
        Finset.sum_le_sum fun u hu => flowR_le (hdep u hu)
      -- split off `w0` from the awarded arcs
      have hrest : S.p * (#(S.awd X i v) - 1) ≤ ∑ w ∈ (outN S.G v).erase w0, S.flowR X i v w := by
        calc S.p * (#(S.awd X i v) - 1) = ∑ _w ∈ (S.awd X i v).erase w0, S.p := by
              rw [sum_const, smul_eq_mul, mul_comm, card_erase_of_mem hw0a]
          _ ≤ ∑ w ∈ (S.awd X i v).erase w0, S.flowR X i v w :=
              Finset.sum_le_sum fun w hw =>
                flowR_of_aw (Finset.mem_filter.1 (Finset.mem_of_mem_erase hw)).2
          _ ≤ ∑ w ∈ (outN S.G v).erase w0, S.flowR X i v w :=
              Finset.sum_le_sum_of_subset (Finset.erase_subset_erase _ (Finset.filter_subset _ _))
      have hsplit := Finset.add_sum_erase (outN S.G v) (fun w => S.flowR X i v w) hw0
      have hpos : 1 ≤ #(S.awd X i v) := Finset.card_pos.2 ⟨w0, hw0a⟩
      have e1 : (S.p * #(S.awd X i v) : ℤ) = S.p + S.p * ((#(S.awd X i v) - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hpos]; ring
      have hsplitZ : (∑ w ∈ outN S.G v, (S.flowR X i v w : ℤ)) =
          S.flowR X i v w0 + ∑ w ∈ (outN S.G v).erase w0, (S.flowR X i v w : ℤ) := by
        exact_mod_cast hsplit.symm
      have houtZ : (∑ u ∈ inN S.G v, (S.flowR X i u v : ℤ)) ≤
          ∑ u ∈ inN S.G v, (R S.G S.p (v :: q0) u : ℤ) := by exact_mod_cast hout
      have hRZ : (S.flowR X i v w0 : ℤ) = S.p + ∑ u ∈ inN S.G v, (R S.G S.p (v :: q0) u : ℤ) := by
        exact_mod_cast hR
      have hrestZ : (S.p * ((#(S.awd X i v) - 1 : ℕ) : ℤ)) ≤
          ∑ w ∈ (outN S.G v).erase w0, (S.flowR X i v w : ℤ) := by exact_mod_cast hrest
      linarith

/-- The leader's own hashkey, released: all its redemption premiums are refunded. -/
theorem netR_lead_rel {v : V} (hv : v ∉ C) (hvL : v ∈ S.L) {r : ℕ} (hr : S.rel X v = some r) :
    (S.p * #(S.awd X v v) : ℤ) ≤ S.netR X v v := by
  unfold netR
  have hsum := sum_flowR_ge (S := S) (X := X) v v
  rw [Finset.sum_eq_zero (s := inN S.G v) fun u hu => by
    have hky : X.ky v u v = some (r, [v]) := by
      rw [hA.conf_ky_lead v hv hvL u hu, hr]; simp [rel_le hA hr]
    have hrp := hA.conf_rp_lead v hv hvL u hu
    split_ifs at hrp
    · rw [flowR_key hrp hky (by simpa using rel_le hA hr)]; rfl
    · rw [flowR_none hrp]; rfl]
  simp only [sub_zero]; exact_mod_cast hsum

/-- The leader's own hashkey, withheld: the leader pays at most `R(v)` and is awarded `p` on
every leaving arc carrying its redemption premium. (Lemma 2 as stated in the paper claims a
profit of at least `p` per escrowed asset here, which is false: see `Examples.lean`.) -/
theorem netR_lead_norel {v : V} (hv : v ∉ C) (hvL : v ∈ S.L) (hr : S.rel X v = none) :
    (S.p * #(S.awd X v v) : ℤ) - Rlead S.G S.p v ≤ S.netR X v v := by
  unfold netR Rlead
  have hsum := sum_flowR_ge (S := S) (X := X) v v
  have hout : ∑ u ∈ inN S.G v, S.flowR X v u v ≤ ∑ u ∈ inN S.G v, R S.G S.p [v] u :=
    Finset.sum_le_sum fun u hu => by
      have hrp := hA.conf_rp_lead v hv hvL u hu
      split_ifs at hrp
      · exact flowR_le hrp
      · rw [flowR_none hrp]; exact Nat.zero_le _
  have houtZ : (∑ u ∈ inN S.G v, (S.flowR X v u v : ℤ)) ≤
      ∑ u ∈ inN S.G v, (R S.G S.p [v] u : ℤ) := by exact_mod_cast hout
  have hsumZ : (S.p * #(S.awd X v v) : ℤ) ≤ ∑ w ∈ outN S.G v, (S.flowR X v v w : ℤ) := by
    exact_mod_cast hsum
  push_cast
  linarith

/-! ### Lemma 6: the protocol is hedged -/

lemma lost_subset {v : V} (hv : v ∉ C) : S.lost X v ⊆ S.L.biUnion fun i => S.awd X i v := by
  intro w hw
  obtain ⟨hwo, hes, hnr⟩ := Finset.mem_filter.1 hw
  have hact := act_of_es hA hv hwo hes
  have : ∃ i ∈ S.L, X.ky i v w = none := by
    by_contra hc
    push_neg at hc
    exact hnr ⟨hes, fun i hi => Option.ne_none_iff_isSome.1 (hc i hi)⟩
  obtain ⟨i, hi, hk⟩ := this
  refine Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_filter.2 ⟨hwo, ?_⟩⟩
  obtain ⟨t, q, hr, -⟩ := optLe_iff.1 (hact.2 i hi)
  unfold Aw; rw [hr, hk]; exact id

lemma card_lost_le {v : V} (hv : v ∉ C) : #(S.lost X v) ≤ ∑ i ∈ S.L, #(S.awd X i v) :=
  (Finset.card_le_card (lost_subset hA hv)).trans Finset.card_biUnion_le

/-- A conforming leader withholds its secret only if it escrowed something and some entering
arc lacks its asset; that arc is then activated. -/
lemma rel_none {v : V} (hv : v ∉ C) (hr : S.rel X v = none) :
    ∃ u ∈ inN S.G v, S.Act X u v ∧ X.es u v = none := by
  unfold rel at hr
  split_ifs at hr with h
  push_neg at h
  obtain ⟨w, hw, hact⟩ := h
  have hn : ¬ (S.allIn X.es v).isSome := by simpa using hr
  rw [allIn_isSome] at hn
  push_neg at hn
  obtain ⟨u, hu, hes⟩ := hn
  exact ⟨u, hu, act_in hA hv hw hact u hu, by simpa using hes⟩

/-- **Lemma 6 (the multi-party swap protocol is hedged).** In every execution, whatever the
deviating coalition does, a conforming party ends up with a net premium profit of at least `p`
for every asset it escrowed that was not redeemed. -/
theorem lemma_6 {v : V} (hv : v ∉ C) : (S.p * #(S.lost X v) : ℤ) ≤ S.net X v := by
  have hcard : (S.p * #(S.lost X v) : ℤ) ≤ ∑ i ∈ S.L, (S.p * #(S.awd X i v) : ℤ) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_lost_le hA hv) (by positivity)
  unfold net
  by_cases hw : v ∈ S.L ∧ S.rel X v = none
  · obtain ⟨hvL, hr⟩ := hw
    obtain ⟨u, hu, hact, hes⟩ := rel_none hA hv hr
    have hE := netE_lead hA hv hvL hu hact hes
    have hRv := netR_lead_norel hA hv hvL hr
    have hrest : ∑ i ∈ S.L.erase v, (S.p * #(S.awd X i v) : ℤ) ≤
        ∑ i ∈ S.L.erase v, S.netR X i v :=
      Finset.sum_le_sum fun i hi => netR_ge hA hv (Finset.ne_of_mem_erase hi)
    rw [← Finset.add_sum_erase _ _ hvL] at hcard ⊢
    linarith
  · have hE := netE_nonneg hA hv
    have hR : ∑ i ∈ S.L, (S.p * #(S.awd X i v) : ℤ) ≤ ∑ i ∈ S.L, S.netR X i v := by
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases hiv : i = v
      · subst hiv
        obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 fun h => hw ⟨hi, h⟩
        exact netR_lead_rel hA hv hi hr
      · exact netR_ge hA hv hiv
    linarith

/-- A conforming party never loses premiums. -/
theorem net_nonneg {v : V} (hv : v ∉ C) : 0 ≤ S.net X v :=
  le_trans (by positivity) (lemma_6 hA hv)

/-! ### Lemmas 1–5 -/

/-- **Lemma 1.** If every party conforms and the swap completes (every asset is escrowed), every
premium is refunded: no premium changes hands. -/
theorem lemma_1 (hC : C = ∅) (hall : ∀ u v, S.G.Adj u v → (X.es u v).isSome) (u v : V) :
    S.flowE X u v = 0 ∧ ∀ i, S.flowR X i u v = 0 := by
  have hnc : ∀ x, x ∉ C := by simp [hC]
  refine ⟨?_, fun i => ?_⟩
  · unfold flowE
    rw [if_neg]
    rintro ⟨hact, hes⟩
    have := hall u v (by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hact.1
      exact (hA.ep_ok u v t ht).1)
    simp [hes] at this
  · -- every redemption premium is matched by a hashkey in time
    have key : ∀ n, ∀ i u v t q, X.rp i u v = some (t, q) → q.length ≤ n →
        OptLe (X.ky i u v) (S.B + q.length) := by
      intro n
      induction n with
      | zero =>
        intro i u v t q hr hn
        have := PPath.ne_nil (hA.rp_ok i u v t q hr).2.2.1
        simp_all
      | succ n ih =>
        intro i u v t q hr hn
        obtain ⟨hadj, hiL, hpp, -⟩ := hA.rp_ok i u v t q hr
        have hu : u ∈ inN S.G v := mem_inN.2 hadj
        by_cases hiv : i = v
        · subst hiv
          obtain ⟨hr', -⟩ := lead_dep hA (hnc i) hiL hu (by rw [hr]; rfl)
          rw [hr] at hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at hr'
          obtain ⟨-, rfl⟩ := hr'
          have hrel : ∃ r, S.rel X i = some r := by
            unfold rel
            split_ifs
            · exact ⟨_, rfl⟩
            · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1
                (allIn_isSome.2 fun u hu => hall u i (mem_inN.1 hu))
              exact ⟨_, by rw [hm]; rfl⟩
          obtain ⟨r, hrel⟩ := hrel
          rw [hA.conf_ky_lead i (hnc i) hiL u hu, hrel]
          simp [rel_le hA hrel, OptLe]
        · have hr' := hr
          rw [hA.conf_rp v (hnc v) i hiv u hu] at hr'
          cases hf : X.fp i v with
          | none => rw [hf] at hr'; simp at hr'
          | some a =>
            obtain ⟨t0, q0⟩ := a
            rw [hf] at hr'
            have hnm := not_mem_fp hA (hnc v) hiv hf
            simp only [hnm, not_false_eq_true, if_true, Option.some.injEq,
              Prod.mk.injEq] at hr'
            obtain ⟨-, rfl⟩ := hr'
            obtain ⟨⟨w0, hw0, hr0⟩, -⟩ := hA.fp_some i v t0 q0 hf
            have hk := ih i v w0 t0 q0 hr0 (by simp at hn; omega)
            obtain ⟨tk, qk, hkw, htk⟩ := optLe_iff.1 hk
            cases hfk : X.fk i v with
            | none => rw [hA.fk_none i v hfk w0 hw0] at hkw; simp at hkw
            | some b =>
              obtain ⟨tf, qf⟩ := b
              have htf := (hA.fk_some i v tf qf hfk).2 w0 hw0 tk qk hkw
              rw [ky_fwd hA (hnc v) hiv hfk u hu]
              simp only [OptLe, List.length_cons]
              omega
    cases hr : X.rp i u v with
    | none => exact flowR_none hr
    | some a =>
      obtain ⟨t, q⟩ := a
      rw [flowR_some hr, if_pos (key _ i u v t q hr le_rfl)]

/-- **Lemma 1**, net form: if every party conforms and every asset is escrowed, every party's
net premium profit is zero. -/
theorem lemma_1_net (hC : C = ∅) (hall : ∀ u v, S.G.Adj u v → (X.es u v).isSome) (v : V) :
    S.net X v = 0 := by
  have h := lemma_1 hA hC hall
  simp [net, netE, netR, h]

/-- **Lemma 2** (for a party `v` other than the leader `i`; for `v = i` it is false, see
`Examples.lean`): if no hashkey for `i` ever appears on `v`'s leaving arcs, `v` makes a net
redemption-premium profit of at least `p` per escrowed asset. -/
theorem lemma_2 {v i : V} (hv : v ∉ C) (hiL : i ∈ S.L) (hi : i ≠ v)
    (hnone : ∀ w ∈ outN S.G v, X.ky i v w = none) :
    (S.p * #(S.esc X v) : ℤ) ≤ S.netR X i v := by
  refine le_trans ?_ (netR_ge hA hv hi)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨hwo, hes⟩ := Finset.mem_filter.1 hw
  refine Finset.mem_filter.2 ⟨hwo, ?_⟩
  obtain ⟨t, q, hr, -⟩ := optLe_iff.1 ((act_of_es hA hv hwo hes).2 i hiL)
  unfold Aw; rw [hr, hnone w hwo]; exact id

/-- Lemma 2 also holds for the leader `v = i` itself when it released its secret. -/
theorem lemma_2_leader_released {v : V} (hv : v ∉ C) (hvL : v ∈ S.L) {r : ℕ}
    (hr : S.rel X v = some r) (hnone : ∀ w ∈ outN S.G v, X.ky v v w = none) :
    (S.p * #(S.esc X v) : ℤ) ≤ S.netR X v v := by
  refine le_trans ?_ (netR_lead_rel hA hv hvL hr)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨hwo, hes⟩ := Finset.mem_filter.1 hw
  refine Finset.mem_filter.2 ⟨hwo, ?_⟩
  obtain ⟨t, q, hr, -⟩ := optLe_iff.1 ((act_of_es hA hv hwo hes).2 v hvL)
  unfold Aw; rw [hr, hnone w hwo]; exact id

/-- **Lemma 3** (repaired: the paper splits the profit into a net escrow-premium profit `≥ 0`
and a net redemption-premium profit `≥ p` per escrowed asset; the second part fails for a
leader, see `Examples.lean`, but the total holds). If an asset entering `v` is not escrowed,
`v` loses no escrow premiums, and its total premium profit is at least `p` per escrowed asset. -/
theorem lemma_3 {u v : V} (hv : v ∉ C) (hu : u ∈ inN S.G v) (hes : X.es u v = none) :
    0 ≤ S.netE X v ∧ (S.p * #(S.esc X v) : ℤ) ≤ S.net X v := by
  refine ⟨netE_nonneg hA hv, le_trans ?_ (lemma_6 hA hv)⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨hwo, hesw⟩ := Finset.mem_filter.1 hw
  have hact := act_of_es hA hv hwo hesw
  have hnall : S.allIn X.es v = none := by
    unfold allIn; rw [if_neg]; intro h; exact absurd (h u hu) (by simp [hes])
  refine Finset.mem_filter.2 ⟨hwo, hesw, fun hred => ?_⟩
  by_cases hvL : v ∈ S.L
  · have hrel : S.rel X v = none := by
      unfold rel; rw [if_neg (fun h => h w hwo hact), hnall]; rfl
    have := hred.2 v hvL
    rw [ky_none_of_rel hA hv hvL hrel v w] at this
    simp at this
  · have h := hA.conf_es v hv w hwo
    rw [if_pos hact, if_neg hvL, hnall] at h
    simp [h] at hesw

/-- **Lemma 4.** If no redemption premium for some leader's hashkey reaches `v`'s leaving arcs,
`v` loses neither escrow nor redemption premiums. -/
theorem lemma_4 {v i : V} (hv : v ∉ C) (hiL : i ∈ S.L)
    (hnone : ∀ w ∈ outN S.G v, X.rp i v w = none) :
    0 ≤ S.netE X v ∧ 0 ≤ ∑ j ∈ S.L, S.netR X j v := by
  refine ⟨netE_nonneg hA hv, Finset.sum_nonneg fun j hj => ?_⟩
  by_cases hjv : j = v
  · subst hjv
    have hrel : S.rel X j = some (S.t2 + 1) := by
      unfold rel
      rw [if_pos]
      intro w hw hact
      have := hact.2 i hiL
      rw [hnone w hw] at this
      exact this
    exact le_trans (by positivity) (netR_lead_rel hA hv hj hrel)
  · exact le_trans (by positivity) (netR_ge hA hv hjv)

/-- **Lemma 5.** If an escrow premium entering `v` is missing, `v` loses no escrow premiums
(indeed a conforming party never does, `netE_nonneg`). -/
theorem lemma_5 {u v : V} (hv : v ∉ C) (_hu : u ∈ inN S.G v) (_hep : X.ep u v = none) :
    0 ≤ S.netE X v :=
  netE_nonneg hA hv

end Swap

end Podc.SoreLoserHedging
