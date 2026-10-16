import Papers.PODC2025.TwoShotConsensusObjects.AlgC2Inv

/-!
# Class `C₂`, sufficiency: preservation of the invariant
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

variable {O : ObjSpec} {s : O.State} {f g : O.Op} {c : ℕ → O.Op} {k : ℕ}

lemma upd_inl_self {ρ : Type} (M : (i : Reg ⊕ Unit) → ((withRW (RegS ρ) O) i).State) (j : Reg)
    (v : RV ρ) : Function.update M (.inl j) v (.inl j) = v :=
  Function.update_self _ _ _

lemma upd_inl_ne {ρ : Type} (M : (i : Reg ⊕ Unit) → ((withRW (RegS ρ) O) i).State) {j0 j : Reg}
    (v : RV ρ) (hj : j ≠ j0) : Function.update M (.inl j0) v (.inl j) = M (.inl j) :=
  Function.update_of_ne (by simpa using hj) _ _

lemma upd_inl_inr {ρ : Type} (M : (i : Reg ⊕ Unit) → ((withRW (RegS ρ) O) i).State) (j0 : Reg)
    (v : RV ρ) : Function.update M (.inl j0) v (.inr ()) = M (.inr ()) :=
  Function.update_of_ne (by simp) _ _

lemma upd_inr_inl {ρ : Type} (M : (i : Reg ⊕ Unit) → ((withRW (RegS ρ) O) i).State) (j : Reg)
    (v : O.State) : Function.update M (.inr ()) v (.inl j) = M (.inl j) :=
  Function.update_of_ne (by simp) _ _

lemma fin2_cases (p q : Fin 2) : p = q ∨ p = 1 - q := by
  fin_cases p <;> fin_cases q <;> simp

@[simp] lemma one_sub_ne (q : Fin 2) : 1 - q ≠ q := by
  fin_cases q <;> decide

@[simp] lemma ne_one_sub (q : Fin 2) : q ≠ 1 - q := fun h => one_sub_ne q h.symm

@[simp] lemma one_sub_one_sub (q : Fin 2) : 1 - (1 - q) = q := sub_sub_cancel _ _

@[simp] lemma upd_q {α : Type} (L : Fin 2 → α) (q : Fin 2) (l : α) :
    Function.update L q l (1 - q) = L (1 - q) :=
  Function.update_of_ne (one_sub_ne q) _ _

section Frame

variable {x : Fin 2 → Bool} {L : Fin 2 → LS O.Resp} {h : List (Fin 2 × O.Op)}

/-- **Frame lemma**: a step of `q` that changes neither `rs` nor the history of `O`. -/
lemma InvL.frame (hI : InvL s f g c k x L h) (q : Fin 2) (l' : LS O.Resp)
    (hid : l'.id = q) (hinp : l'.inp = x q) (hpc : l'.pc ≤ 10) (hrs : l'.rs = (L q).rs)
    (hl0 : l'.pc ≤ 2 → l'.rs = []) (hl1 : l'.pc ≤ 4 → l'.rs.length < k)
    (hl2 : 5 ≤ l'.pc → l'.rs.length = k) (hwr : (L q).wr ≤ l'.wr)
    (hops : opsL f g c q l' = opsL f g c q (L q)) (hresp : respL l' = respL (L q))
    (hw : 8 ≤ l'.pc → l'.w = none ∨ l'.w = (view O s h (1 - q)).head?)
    (ht2 : 8 ≤ l'.pc → l'.w = none →
      ∃ u v, h = u ++ v ∧ (u.filter (·.1 = 1 - q)).length ≤ 1 ∧ ∀ e ∈ v, e.1 = 1 - q)
    (hdec : 9 ≤ l'.pc → h.head?.map Prod.fst = some l'.dec)
    (hout : l'.pc = 10 → l'.out = x l'.dec) :
    InvL s f g c k x (Function.update L q l') h := by
  obtain ⟨Iid, Iinp, Ipc, Il0, Il1, Il2, Ihist, Ivw, Iseen, Iun, Ibnd, It1, Iw, It2, Idec,
    Iout⟩ := hI
  have hrsall : ∀ p, (Function.update L q l' p).rs = (L p).rs := by
    intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hrs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hid, Iid]
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hinp, Iinp]
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hpc, Ipc]
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hl0
    · simpa using Il0 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hl1
    · simpa using Il1 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hl2
    · simpa using Il2 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa [hops] using Ihist p
    · simpa using Ihist (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa [hresp] using Ivw p
    · simpa using Ivw (1 - q)
  · intro p r y hy
    rw [hrsall] at hy
    rcases fin2_cases p q with rfl | rfl
    · simpa using Iseen p r y hy
    · obtain ⟨h1, h2⟩ := Iseen (1 - q) r y hy
      simp only [one_sub_one_sub, Function.update_self] at h1 h2 ⊢
      exact ⟨lt_of_lt_of_le h1 hwr, by rw [hrs]; exact h2⟩
  · intro r; rw [hrsall, hrsall]; exact Iun r
  · intro p r; rw [hrsall]; exact Ibnd p r
  · intro p; rw [hrsall]; exact It1 p
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hw
    · simpa using Iw (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using ht2
    · simpa using It2 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hdec
    · simpa using Idec (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hout
    · simpa using Iout (1 - q)

lemma resps_append (st : O.State) (h1 h2 : List (Fin 2 × O.Op)) :
    resps O st (h1 ++ h2) = resps O st h1 ++ resps O (after O st h1) h2 := by
  induction h1 generalizing st with
  | nil => simp
  | cons e h1 ih => obtain ⟨p, o⟩ := e; simp [ih]

lemma after_append (st : O.State) (h1 h2 : List (Fin 2 × O.Op)) :
    after O st (h1 ++ h2) = after O (after O st h1) h2 := by
  induction h1 generalizing st with
  | nil => simp
  | cons e h1 ih => obtain ⟨p, o⟩ := e; simp [ih]

lemma view_append_single (st : O.State) (h : List (Fin 2 × O.Op)) (q p : Fin 2) (o : O.Op) :
    view O st (h ++ [(q, o)]) p =
      view O st h p ++ (if q = p then [(O.δ (after O st h) o).2] else []) := by
  simp only [view, resps_append, List.filterMap_append]
  by_cases hqp : q = p <;> simp [resps, hqp]

lemma take_two_append (h : List (Fin 2 × O.Op)) (e : Fin 2 × O.Op) (hl : 2 ≤ h.length) :
    (h ++ [e]).take 2 = h.take 2 := List.take_append_of_le_length hl

/-- A step of `q` applying operation `o` to `O` (the history grows by `(q, o)`). -/
lemma InvL.ostep (hI : InvL s f g c k x L h) (q : Fin 2) (o : O.Op) (l' : LS O.Resp)
    (hid : l'.id = q) (hinp : l'.inp = x q) (hpc : l'.pc ≤ 10) (hrs : l'.rs = (L q).rs)
    (hl0 : l'.pc ≤ 2 → l'.rs = []) (hl1 : l'.pc ≤ 4 → l'.rs.length < k)
    (hl2 : 5 ≤ l'.pc → l'.rs.length = k) (hwr : (L q).wr ≤ l'.wr)
    (hops : opsL f g c q l' = opsL f g c q (L q) ++ [(q, o)])
    (hresp : respL l' = respL (L q) ++ [some (O.δ (after O s h) o).2])
    (hpc8 : l'.pc < 8) :
    InvL s f g c k x (Function.update L q l') (h ++ [(q, o)]) := by
  obtain ⟨Iid, Iinp, Ipc, Il0, Il1, Il2, Ihist, Ivw, Iseen, Iun, Ibnd, It1, Iw, It2, Idec,
    Iout⟩ := hI
  have hrsall : ∀ p, (Function.update L q l' p).rs = (L p).rs := by
    intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hrs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hid, Iid]
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hinp, Iinp]
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hpc, Ipc]
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hl0
    · simpa using Il0 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hl1
    · simpa using Il1 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simpa using hl2
    · simpa using Il2 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simp [List.filter_append, hops, Ihist p]
    · simp [List.filter_append, Ihist (1 - q)]
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simp [view_append_single, hresp, ← Ivw p]
    · simp [view_append_single, Ivw (1 - q)]
  · intro p r y hy
    rw [hrsall] at hy
    rcases fin2_cases p q with rfl | rfl
    · simpa using Iseen p r y hy
    · obtain ⟨h1, h2⟩ := Iseen (1 - q) r y hy
      simp only [one_sub_one_sub, Function.update_self] at h1 h2 ⊢
      exact ⟨lt_of_lt_of_le h1 hwr, by rw [hrs]; exact h2⟩
  · intro r; rw [hrsall, hrsall]; exact Iun r
  · intro p r; rw [hrsall]; exact Ibnd p r
  · intro p hp
    rw [hrsall]
    by_cases hl : 2 ≤ h.length
    · rw [take_two_append h _ hl] at hp; exact It1 p hp
    · obtain ⟨e, he⟩ : ∃ e, h = [e] := by
        rcases h with _ | ⟨e, _ | ⟨e', h⟩⟩
        · simp at hp
        · exact ⟨e, rfl⟩
        · simp at hl
      subst he
      obtain ⟨p', o'⟩ := e
      simp only [List.cons_append, List.nil_append] at hp
      obtain ⟨rfl, -⟩ := hp
      have hf := Ihist (1 - q)
      simp [opsL] at hf
      have hwr0 : (L (1 - q)).wr = 0 := by simp [LS.wr]; omega
      show ∀ o ∈ (L q).rs, o = none
      intro o'' ho''
      cases o'' with
      | none => rfl
      | some y =>
        obtain ⟨r, hr⟩ := List.mem_iff_getElem?.1 ho''
        have := (Iseen q r y hr).1
        omega
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · simp at hp; omega
    · simp only [upd_q] at hp ⊢
      rcases Iw (1 - q) hp with h0 | h0
      · exact Or.inl h0
      · cases hv : view O s h q with
        | nil => left; rw [h0, one_sub_one_sub, hv]; rfl
        | cons y ys => right; rw [h0, one_sub_one_sub, view_append_single, hv]; simp
  · intro p hp hw0; rcases fin2_cases p q with rfl | rfl
    · simp at hp; omega
    · simp only [upd_q] at hp hw0
      obtain ⟨u, v, rfl, hu, hv⟩ := It2 (1 - q) hp hw0
      refine ⟨u, v ++ [(q, o)], by simp, hu, ?_⟩
      intro e he; simp at he; rcases he with he | rfl
      · exact hv e he
      · simp
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · simp at hp; omega
    · simp only [upd_q] at hp ⊢
      have := Idec (1 - q) hp
      rcases h with _ | ⟨e, h⟩
      · simp at this
      · simpa using this
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · simp at hp; omega
    · simpa using Iout (1 - q) (by simpa using hp)

lemma len_le_wr {ρ : Type} {l : LS ρ} (h0 : l.pc ≤ 2 → l.rs = []) : l.rs.length ≤ l.wr := by
  unfold LS.wr
  split_ifs with h1 h2
  · simp [h0 (by omega)]
  · omega
  · omega

lemma take2_filter {h : List (Fin 2 × O.Op)} {p : Fin 2}
    (hp : (h.take 2).map Prod.fst = [p, p]) : 2 ≤ (h.filter (·.1 = p)).length := by
  rcases h with _ | ⟨⟨p1, o1⟩, _ | ⟨⟨p2, o2⟩, h⟩⟩ <;> simp at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp

lemma opsL_length_le {p : Fin 2} {l : LS O.Resp} (hl : l.pc < 7) :
    (opsL f g c p l).length ≤ 1 := by
  unfold opsL; split_ifs <;> simp <;> omega

/-- The step of `q` reading `Round[1-q][cnt]` (line 10 of Algorithm 3). -/
lemma InvL.rstep (hI : InvL s f g c k x L h) (q : Fin 2) (hq : (L q).pc = 4) :
    InvL s f g c k x (Function.update L q { L q with
      pc := if (L q).rs.length + 1 < k then 3 else 5
      rs := (L q).rs ++ [if (L q).rs.length < (L (1 - q)).wr then
        some (opOf (1 - q) ((L (1 - q)).rs.take (L q).rs.length)) else none] }) h := by
  obtain ⟨Iid, Iinp, Ipc, Il0, Il1, Il2, Ihist, Ivw, Iseen, Iun, Ibnd, It1, Iw, It2, Idec,
    Iout⟩ := hI
  have hlk : (L q).rs.length < k := Il1 q (by omega)
  set n := (L q).rs.length with hn
  set v : Option ℕ := if n < (L (1 - q)).wr then
    some (opOf (1 - q) ((L (1 - q)).rs.take n)) else none with hv
  set l' : LS O.Resp := { L q with pc := if n + 1 < k then 3 else 5, rs := (L q).rs ++ [v] }
    with hl'
  have hwr' : l'.wr = n + 1 := by
    by_cases hk' : n + 1 < k <;> simp [hl', hk', LS.wr, ← hn]
  have hwr : (L q).wr = n + 1 := by simp [LS.wr, hq, ← hn]
  have hops : opsL f g c q l' = opsL f g c q (L q) := by
    by_cases hk' : n + 1 < k <;> simp [hl', hk', opsL, hq]
  have hresp : respL l' = respL (L q) := by
    by_cases hk' : n + 1 < k <;> simp [hl', hk', respL, hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hl', Iid]
  · intro p; rcases fin2_cases p q with rfl | rfl <;> simp [hl', Iinp]
  · intro p; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k <;> simp [hl', hk']
    · simpa using Ipc (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k <;> simp [hl', hk']
    · simpa using Il0 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k
      · simp [hl', hk']; omega
      · simp [hl', hk']
    · simpa using Il1 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k
      · simp [hl', hk']
      · simp [hl', hk']; omega
    · simpa using Il2 (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simp [hops, Ihist p]
    · simpa using Ihist (1 - q)
  · intro p; rcases fin2_cases p q with rfl | rfl
    · simp [hresp, Ivw p]
    · simpa using Ivw (1 - q)
  · intro p r y hy
    rcases fin2_cases p q with rfl | rfl
    · simp only [Function.update_self, upd_q, hl'] at hy ⊢
      rcases lt_trichotomy r n with hr | rfl | hr
      · rw [List.getElem?_append_left (by omega)] at hy
        exact Iseen p r y hy
      · rw [List.getElem?_append_right (by omega)] at hy
        rw [← hn, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, hv] at hy
        split_ifs at hy with hw
        · simp only [Option.some.injEq] at hy
          exact ⟨hw, hy.symm⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hy
        simp at hy
    · obtain ⟨h1, h2⟩ := Iseen (1 - q) r y (by simpa using hy)
      simp only [one_sub_one_sub, Function.update_self] at h1 h2 ⊢
      refine ⟨by rw [hwr']; omega, ?_⟩
      rw [h2, hl', List.take_append_of_le_length (by omega)]
  · intro r hr
    have hl0' := len_le_wr (Il0 0)
    have hl1' := len_le_wr (Il0 1)
    obtain rfl | rfl : q = 0 ∨ q = 1 := by fin_cases q <;> simp
    · simp only [Function.update_self, Fin.isValue, ne_eq, not_false_eq_true,
        Function.update_of_ne, one_ne_zero, hl'] at hr ⊢
      rcases lt_trichotomy r n with hr' | rfl | hr'
      · rw [List.getElem?_append_left (by omega)] at hr
        exact Iun r hr
      · rw [List.getElem?_append_right (by omega), ← hn, Nat.sub_self,
          List.getElem?_cons_zero, hv] at hr
        split_ifs at hr with hw
        · simp at hr
        · rw [List.getElem?_eq_none (by simp at hw; omega)]; simp
      · rw [List.getElem?_eq_none (by simp; omega)] at hr; simp at hr
    · simp only [Function.update_self, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
        Function.update_of_ne, hl'] at hr ⊢
      rcases lt_trichotomy r n with hr' | rfl | hr'
      · rw [List.getElem?_append_left (by omega)]
        exact Iun r hr
      · rw [List.getElem?_append_right (by omega), ← hn, Nat.sub_self,
          List.getElem?_cons_zero, hv]
        have : n < (L 0).rs.length := by
          by_contra hc; rw [List.getElem?_eq_none (by omega)] at hr; simp at hr
        split_ifs with hc
        · simp
        · simp at hc; omega
      · rw [List.getElem?_eq_none (by simp; omega)]; simp
  · intro p r
    rcases fin2_cases p q with rfl | rfl
    · simp only [Function.update_self, hl']
      refine opOf_bound_append (Ibnd p) ?_ r
      intro y hy
      simp only [hv] at hy
      split_ifs at hy
      · simp only [Option.some.injEq] at hy
        rw [← hy]; exact Ibnd (1 - p) n
    · simpa using Ibnd (1 - q) r
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · have h1 := take2_filter hp
      rw [Ihist] at h1
      have := opsL_length_le (f := f) (g := g) (c := c) (p := p) (l := L p) (by omega)
      omega
    · simpa using It1 (1 - q) hp
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k <;> simp [hl', hk'] at hp
    · simpa using Iw (1 - q) (by simpa using hp)
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k <;> simp [hl', hk'] at hp
    · simpa using It2 (1 - q) (by simpa using hp)
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k <;> simp [hl', hk'] at hp
    · simpa using Idec (1 - q) (by simpa using hp)
  · intro p hp; rcases fin2_cases p q with rfl | rfl
    · by_cases hk' : n + 1 < k <;> simp [hl', hk'] at hp
    · simpa using Iout (1 - q) (by simpa using hp)

lemma v_nil_of_last {h u v : List (Fin 2 × O.Op)} {p p' : Fin 2} (hh : h = u ++ v)
    (hv : ∀ e ∈ v, e.1 = p') (hlast : h.getLast?.map Prod.fst = some p) (hp : p ≠ p') :
    v = [] := by
  by_contra hne
  obtain ⟨v', e, rfl⟩ := List.eq_nil_or_concat v |>.resolve_left hne
  subst hh
  have := hv e (by simp)
  simp [← List.append_assoc] at hlast
  exact hp (hlast ▸ this)

lemma opsL_cases (p : Fin 2) (l : LS O.Resp) :
    (opsL f g c p l = [] ∧ l.pc < 2) ∨
    (opsL f g c p l = [(p, if p = 0 then f else g)] ∧ 2 ≤ l.pc ∧ l.pc < 7) ∨
    (opsL f g c p l = [(p, if p = 0 then f else g), (p, c (opOf p l.rs))] ∧ 7 ≤ l.pc) := by
  unfold opsL
  by_cases h2 : 2 ≤ l.pc <;> by_cases h7 : 7 ≤ l.pc <;> simp [h2, h7] <;> omega

/-- The decision of `q` (at line 8 of the code, reading `Next_op[1-q]`) is the index of the
process whose first operation on `O` is first in the history (Lemma 4). -/
lemma InvL.dec_ok {m : Fin 2 → Set O.Op} (hk : 1 ≤ k) (hC : C2At O m s f g (3 ^ k) c)
    (hI : InvL s f g c k x L h) (q : Fin 2) (hq : (L q).pc = 8) :
    h.head?.map Prod.fst = some (decideC2 s f g (3 ^ k) c q (opOf q (L q).rs) (L q).r0
      (L q).r1 (L q).w (regLoc (L (1 - q)) (.next (1 - q))).nat) := by
  obtain ⟨Iid, Iinp, Ipc, Il0, Il1, Il2, Ihist, Ivw, Iseen, Iun, Ibnd, It1, Iw, It2, Idec,
    Iout⟩ := hI
  have hN3 : 3 ≤ 3 ^ k := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- the values of `op` of both processes
  have hop_le : ∀ p, 5 ≤ (L p).pc → opOf p (L p).rs ≤ 3 ^ k := by
    intro p hp
    have := Ibnd p k
    rwa [List.take_of_length_le (by rw [Il2 p hp])] at this
  have hadj : 5 ≤ (L 0).pc → 5 ≤ (L 1).pc →
      opOf 0 (L 0).rs + 1 = opOf 1 (L 1).rs ∨ opOf 1 (L 1).rs + 1 = opOf 0 (L 0).rs := by
    intro h0 h1
    have := opOf_adj (rs0 := (L 0).rs) (rs1 := (L 1).rs)
      (fun r y hy => (Iseen 0 r y hy).2) (fun r y hy => (Iseen 1 r y hy).2) Iun k
      (by rw [Il2 0 h0]) (by rw [Il2 1 h1])
    rwa [List.take_of_length_le (by rw [Il2 0 h0]),
      List.take_of_length_le (by rw [Il2 1 h1])] at this
  have hT : ∀ p, (h.take 2).map Prod.fst = [p, p] → 7 ≤ (L p).pc := by
    intro p hp
    have h1 := take2_filter hp
    rw [Ihist] at h1
    rcases opsL_cases (f := f) (g := g) (c := c) p (L p) with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, e⟩
    · rw [e] at h1; simp at h1
    · rw [e] at h1; simp at h1
    · exact e
  have hall : ∀ p, (h.take 2).map Prod.fst = [p, p] → opOf p (L p).rs = p.val * 3 ^ k := by
    intro p hp
    rw [opOf_all_none p _ (It1 p hp), Il2 p (by have := hT p hp; omega)]
  have hw2 : (h.getLast?).map Prod.fst = some q → (h.filter (·.1 = 1 - q)).length = 2 →
      (L q).w ≠ none := by
    intro hlast hlen hw0
    obtain ⟨u, v, hh, hu, hv⟩ := It2 q (by omega) hw0
    have := v_nil_of_last hh hv hlast (ne_one_sub q)
    subst this
    simp at hh
    subst hh
    omega
  have hv := Ivw q
  simp only [respL, hq] at hv
  simp only [show 2 ≤ 8 from by norm_num, show 7 ≤ 8 from by norm_num, ite_true,
    List.singleton_append] at hv
  have hfq : h.filter (·.1 = q) = [(q, if q = 0 then f else g), (q, c (opOf q (L q).rs))] := by
    rw [Ihist]; simp [opsL, hq]
  have hnx : (regLoc (L (1 - q)) (.next (1 - q))).nat =
      if 6 ≤ (L (1 - q)).pc then some (opOf (1 - q) (L (1 - q)).rs) else none := by
    simp only [regLoc]; split_ifs <;> rfl
  rw [hnx]
  have hwq := Iw q (by omega)
  have hmod := opOf_mod q (L q).rs
  have hmod' := opOf_mod (1 - q) (L (1 - q)).rs
  have hle := hop_le q (by omega)
  obtain rfl | rfl : q = 0 ∨ q = 1 := by fin_cases q <;> simp
  · simp only [Fin.isValue, sub_zero] at *
    refine (decide0_ok hC h _ (opOf 1 (L 1).rs) _ _ _ _ hfq ?_ hv hle hmod ?_ ?_ ?_ ?_ hwq hw2
      hN3).symm
    · rw [Ihist]
      rcases opsL_cases (f := f) (g := g) (c := c) 1 (L 1) with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;>
        simp [e]
    · split_ifs with h6
      · exact Or.inr ⟨rfl, hadj (by omega) (by omega), hop_le 1 (by omega), by simpa using hmod'⟩
      · exact Or.inl rfl
    · intro hf1
      rw [Ihist] at hf1
      rcases opsL_cases (f := f) (g := g) (c := c) 1 (L 1) with ⟨e, h7⟩ | ⟨e, h7⟩ | ⟨e, h7⟩
      · rw [e] at hf1; simp at hf1
      · rw [e] at hf1; simp at hf1
      · split_ifs <;> first | rfl | omega
    · intro h2; have := hall 0 h2; simpa using this
    · intro h2; have := hall 1 h2; simpa using this
  · simp only [Fin.isValue, sub_self] at *
    refine (decide1_ok hC h (opOf 0 (L 0).rs) _ _ _ _ _ hfq ?_ hv hle hmod ?_ ?_ ?_ ?_ hwq hw2
      hN3).symm
    · rw [Ihist]
      rcases opsL_cases (f := f) (g := g) (c := c) 0 (L 0) with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;>
        simp [e]
    · split_ifs with h6
      · exact Or.inr ⟨rfl, hadj (by omega) (by omega), hop_le 0 (by omega), by simpa using hmod'⟩
      · exact Or.inl rfl
    · intro hf1
      rw [Ihist] at hf1
      rcases opsL_cases (f := f) (g := g) (c := c) 0 (L 0) with ⟨e, h7⟩ | ⟨e, h7⟩ | ⟨e, h7⟩
      · rw [e] at hf1; simp at hf1
      · rw [e] at hf1; simp at hf1
      · split_ifs <;> first | rfl | omega
    · intro h2; have := hall 0 h2; simpa using this
    · intro h2; have := hall 1 h2; simpa using this

end Frame

section Cfg

variable {C : Cfg (algC2 s f g c k)} {h : List (Fin 2 × O.Op)}

lemma regOf_update {ρ : Type} (L : Fin 2 → LS ρ) (q : Fin 2) (l' : LS ρ) (j : Reg) :
    regOf (Function.update L q l') j = if j.owner = q then regLoc l' j else regOf L j := by
  unfold regOf
  by_cases hj : j.owner = q
  · subst hj; simp
  · simp [hj]

/-- Memory consistency after a register write by `q`. -/
lemma reg_write (hreg : ∀ j, C.mem (.inl j) = regOf C.loc j) (q : Fin 2) (j0 : Reg)
    (v : RV O.Resp) (l' : LS O.Resp) (hj0 : j0.owner = q) (hv : regLoc l' j0 = v)
    (hother : ∀ j, j ≠ j0 → j.owner = q → regLoc l' j = regLoc (C.loc q) j) (j : Reg) :
    Function.update C.mem (.inl j0) v (.inl j) = regOf (Function.update C.loc q l') j := by
  refine Eq.trans ?_ (regOf_update C.loc q l' j).symm
  by_cases hj : j = j0
  · subst hj
    refine (upd_inl_self _ _ _).trans ?_
    split_ifs
    · exact hv.symm
  · refine (upd_inl_ne _ _ hj).trans ?_
    refine (hreg j).trans ?_
    split_ifs with ho
    · rw [hother j hj ho]; unfold regOf; rw [ho]
    · rfl

/-- Memory consistency after a step of `q` that writes no register. -/
lemma reg_same (hreg : ∀ j, C.mem (.inl j) = regOf C.loc j) (q : Fin 2) (l' : LS O.Resp)
    (hother : ∀ j, j.owner = q → regLoc l' j = regLoc (C.loc q) j) (j : Reg) :
    C.mem (.inl j) = regOf (Function.update C.loc q l') j := by
  refine (hreg j).trans (Eq.trans ?_ (regOf_update C.loc q l' j).symm)
  split_ifs with ho
  · rw [hother j ho]; unfold regOf; rw [ho]
  · rfl

lemma step0 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 0) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) = .access (.inl (.val q))
      (RWOp.write (.b (C.loc q).inp)) (fun _ => { C.loc q with pc := 1 }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_of_access _ hact]
  have hrs := hL.len0 q (by omega)
  refine ⟨?_, ?_, ?_⟩
  · refine hL.frame q _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp [hrs])
      (by simpa using hL.len1 q (by omega)) (by simp) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) (by simp [respL, hq]) (by simp) (by simp) (by simp) (by simp)
  · intro j
    exact reg_write hreg q _ _ _ rfl (by simp [regLoc]) (by
      intro j hj ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · dsimp only
    refine (Function.update_of_ne ?_ _ _).trans hobj
    simp

lemma step2 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 2) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) = .access (.inl (.ret q))
      (RWOp.write (.r (C.loc q).r0)) (fun _ => { C.loc q with pc := 3 }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_of_access _ hact]
  have hrs := hL.len0 q (by omega)
  refine ⟨?_, ?_, ?_⟩
  · refine hL.frame q _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp)
      (by simpa using hL.len1 q (by omega)) (by simp) (by simp [LS.wr, hq, hrs])
      (by simp [opsL, hq]) (by simp [respL, hq]) (by simp) (by simp) (by simp) (by simp)
  · intro j
    exact reg_write hreg q _ _ _ rfl (by simp [regLoc]) (by
      intro j hj ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · dsimp only
    refine (Function.update_of_ne ?_ _ _).trans hobj
    simp

lemma step3 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 3) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) = .access (.inl (.round q (C.loc q).rs.length))
      (RWOp.write (.n (opOf q (C.loc q).rs))) (fun _ => { C.loc q with pc := 4 }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_of_access _ hact]
  refine ⟨?_, ?_, ?_⟩
  · refine hL.frame q _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp)
      (by simpa using hL.len1 q (by omega)) (by simp) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) (by simp [respL, hq]) (by simp) (by simp) (by simp) (by simp)
  · intro j
    refine reg_write hreg q _ _ _ rfl (by simp [regLoc, LS.wr]) ?_ j
    intro j hj ho
    cases j with
    | round p r =>
      simp only [Reg.owner] at ho; subst ho
      have : r ≠ (C.loc p).rs.length := fun e => hj (by rw [e])
      simp only [regLoc, LS.wr, hq]
      split_ifs <;> first | rfl | omega
    | _ => simp_all [regLoc, Reg.owner]
  · dsimp only
    refine (Function.update_of_ne ?_ _ _).trans hobj
    simp

lemma step5 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 5) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) = .access (.inl (.next q))
      (RWOp.write (.n (opOf q (C.loc q).rs))) (fun _ => { C.loc q with pc := 6 }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_of_access _ hact]
  refine ⟨?_, ?_, ?_⟩
  · refine hL.frame q _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp) (by simp)
      (by simpa using hL.len2 q (by omega)) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) (by simp [respL, hq]) (by simp) (by simp) (by simp) (by simp)
  · intro j
    exact reg_write hreg q _ _ _ rfl (by simp [regLoc]) (by
      intro j hj ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · dsimp only
    refine (Function.update_of_ne ?_ _ _).trans hobj
    simp

lemma step1 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 1) :
    Inv s f g c k (C.stepP q) (h ++ [(q, if q = 0 then f else g)]) := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) = .access (.inr ())
      (if q = 0 then f else g) (fun r => { C.loc q with pc := 2, r0 := some r }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_of_access _ hact]
  have hrs := hL.len0 q (by omega)
  refine ⟨?_, ?_, ?_⟩
  · refine hL.ostep q _ _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp [hrs])
      (by simpa using hL.len1 q (by omega)) (by simp) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) ?_ (by simp)
    simp only [respL, hq]
    simp
    exact hobj ▸ rfl
  · intro j
    dsimp only
    refine (Function.update_of_ne ?_ _ _).trans ?_
    · simp
    exact reg_same hreg q _ (by intro j ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · dsimp only
    refine (Function.update_self _ _ _).trans ?_
    rw [after_append]
    simp only [after_cons, after_nil]
    exact hobj ▸ rfl

lemma step6 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 6) :
    Inv s f g c k (C.stepP q) (h ++ [(q, c (opOf q (C.loc q).rs))]) := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) = .access (.inr ())
      (c (opOf q (C.loc q).rs)) (fun r => { C.loc q with pc := 7, r1 := some r }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_of_access _ hact]
  refine ⟨?_, ?_, ?_⟩
  · refine hL.ostep q _ _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp)
      (by simp) (by simpa using hL.len2 q (by omega)) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) ?_ (by simp)
    simp only [respL, hq]
    simp
    exact hobj ▸ rfl
  · intro j
    dsimp only
    refine (Function.update_of_ne ?_ _ _).trans ?_
    · simp
    exact reg_same hreg q _ (by intro j ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · dsimp only
    refine (Function.update_self _ _ _).trans ?_
    rw [after_append]
    simp only [after_cons, after_nil]
    exact hobj ▸ rfl

lemma stepP_read {q : Fin 2} {j0 : Reg} {κ : RV O.Resp → LS O.Resp}
    (hact : (algC2 s f g c k).act (C.loc q) = .access (.inl j0) RWOp.read κ) :
    C.stepP q = { C with loc := Function.update C.loc q (κ (C.mem (.inl j0))) } := by
  rw [stepP_of_access _ hact]
  congr 1
  exact Function.update_eq_self _ _

lemma step4 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 4) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) =
      .access (.inl (.round (1 - q) (C.loc q).rs.length)) RWOp.read
      (fun v => { C.loc q with
        pc := if (C.loc q).rs.length + 1 < k then 3 else 5
        rs := (C.loc q).rs ++ [RV.nat v] }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_read hact]
  have hval : RV.nat (C.mem (.inl (.round (1 - q) (C.loc q).rs.length))) =
      if (C.loc q).rs.length < (C.loc (1 - q)).wr then
        some (opOf (1 - q) ((C.loc (1 - q)).rs.take (C.loc q).rs.length)) else none := by
    rw [hreg]; simp only [regOf, Reg.owner, regLoc]
    by_cases h3 : (C.loc q).rs.length < (C.loc (1 - q)).wr <;> simp [h3, RV.nat]
  refine ⟨?_, ?_, ?_⟩
  · have key := hL.rstep q hq
    rw [← hval] at key
    exact key
  · intro j
    refine reg_same hreg q _ ?_ j
    intro j ho
    cases j with
    | round p r =>
      simp only [Reg.owner] at ho; subst ho
      have hlk := hL.len1 p (by omega)
      by_cases hr : r < (C.loc p).rs.length + 1
      · have : r ≤ (C.loc p).rs.length := by omega
        by_cases hk' : (C.loc p).rs.length + 1 < k <;>
          simp [regLoc, LS.wr, hq, hk', hr, List.take_append_of_le_length this]
      · by_cases hk' : (C.loc p).rs.length + 1 < k <;> simp [regLoc, LS.wr, hq, hk', hr]
    | val p | ret p | next p =>
      simp only [Reg.owner] at ho; subst ho
      by_cases hk' : (C.loc p).rs.length + 1 < k <;> simp [regLoc, hq, hk']
  · exact hobj

lemma step7 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 7) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) =
      .access (.inl (.ret (1 - q))) RWOp.read
      (fun v => { C.loc q with pc := 8, w := RV.resp v }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_read hact]
  have hval : RV.resp (C.mem (.inl (.ret (1 - q)))) =
      if 3 ≤ (C.loc (1 - q)).pc then (C.loc (1 - q)).r0 else none := by
    rw [hreg]; simp only [regOf, Reg.owner, regLoc]
    by_cases h3 : 3 ≤ (C.loc (1 - q)).pc <;> simp [h3, RV.resp]
  have hvw := hL.vw (1 - q)
  refine ⟨?_, ?_, ?_⟩
  · refine hL.frame q _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp) (by simp)
      (by simpa using hL.len2 q (by omega)) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) (by simp [respL, hq]) ?_ ?_ (by simp) (by simp)
    · intro _
      dsimp only
      rw [hval]
      split_ifs with h3
      · right
        simp only [respL, show 2 ≤ (C.loc (1 - q)).pc by omega, ite_true,
          List.singleton_append] at hvw
        cases hv : view O s h (1 - q) with
        | nil => rw [hv] at hvw; simp at hvw
        | cons y ys => rw [hv] at hvw; simp at hvw; simp [hvw.1]
      · left; rfl
    · intro _ hw0
      dsimp only at hw0
      rw [hval] at hw0
      split_ifs at hw0 with h3
      · simp only [respL, show 2 ≤ (C.loc (1 - q)).pc by omega, ite_true,
          List.singleton_append] at hvw
        cases hv : view O s h (1 - q) with
        | nil => rw [hv] at hvw; simp at hvw
        | cons y ys => rw [hv] at hvw; simp at hvw; rw [hw0] at hvw; simp at hvw
      · refine ⟨h, [], by simp, ?_, by simp⟩
        rw [hL.hist]
        exact opsL_length_le (by omega)
  · intro j
    exact reg_same hreg q _ (by intro j ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · exact hobj

lemma step8 {m : Fin 2 → Set O.Op} (hk : 1 ≤ k) (hC : C2At O m s f g (3 ^ k) c)
    (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 8) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) =
      .access (.inl (.next (1 - q))) RWOp.read
      (fun v => { C.loc q with
        pc := 9
        dec := decideC2 s f g (3 ^ k) c q (opOf q (C.loc q).rs) (C.loc q).r0 (C.loc q).r1
          (C.loc q).w (RV.nat v) }) := by
    simp only [algC2, actC2, hq]
    rw [hid]
  rw [stepP_read hact]
  have hval : C.mem (.inl (.next (1 - q))) = regLoc (C.loc (1 - q)) (.next (1 - q)) := hreg _
  refine ⟨?_, ?_, ?_⟩
  · refine hL.frame q _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp) (by simp)
      (by simpa using hL.len2 q (by omega)) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) (by simp [respL, hq]) ?_ ?_ ?_ (by simp)
    · intro _; simpa using hL.w q (by omega)
    · intro _ hw0; exact hL.t2 q (by omega) hw0
    · intro _
      dsimp only
      rw [hval]
      exact hL.dec_ok hk hC q hq
  · intro j
    exact reg_same hreg q _ (by intro j ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · exact hobj

lemma step9 (hI : Inv s f g c k C h) (q : Fin 2) (hq : (C.loc q).pc = 9) :
    Inv s f g c k (C.stepP q) h := by
  obtain ⟨hL, hreg, hobj⟩ := hI
  have hid := hL.id q
  have hact : (algC2 s f g c k).act (C.loc q) =
      .access (.inl (.val (C.loc q).dec)) RWOp.read
      (fun v => { C.loc q with pc := 10, out := RV.bool v }) := by
    simp only [algC2, actC2, hq]
  rw [stepP_read hact]
  have hdec := hL.dec q (by omega)
  -- the decided process has applied an operation to `O`
  have hpc : 2 ≤ (C.loc (C.loc q).dec).pc := by
    obtain ⟨e, t, rfl⟩ : ∃ e t, h = e :: t := by
      cases h with
      | nil => simp at hdec
      | cons e t => exact ⟨e, t, rfl⟩
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hdec
    have hf := hL.hist (C.loc q).dec
    rcases opsL_cases (f := f) (g := g) (c := c) (C.loc q).dec (C.loc (C.loc q).dec) with
      ⟨e', h2⟩ | ⟨_, h2, _⟩ | ⟨_, h2⟩
    · rw [e'] at hf; simp [hdec] at hf
    · exact h2
    · omega
  have hval : RV.bool (C.mem (.inl (.val (C.loc q).dec))) = C.inp (C.loc q).dec := by
    rw [hreg]
    have h1 : 1 ≤ (C.loc (C.loc q).dec).pc := by omega
    simp [regOf, Reg.owner, regLoc, h1, RV.bool, hL.inp]
  refine ⟨?_, ?_, ?_⟩
  · refine hL.frame q _ (by simp [hid]) (by simp [hL.inp]) (by simp) rfl (by simp) (by simp)
      (by simpa using hL.len2 q (by omega)) (by simp [LS.wr, hq])
      (by simp [opsL, hq]) (by simp [respL, hq]) ?_ ?_ ?_ ?_
    · intro _; simpa using hL.w q (by omega)
    · intro _ hw0; exact hL.t2 q (by omega) hw0
    · intro _; simpa using hdec
    · intro _; simpa using hval
  · intro j
    exact reg_same hreg q _ (by intro j ho; cases j <;> simp_all [regLoc, Reg.owner, LS.wr]) j
  · exact hobj

end Cfg

end TwoShotCons
