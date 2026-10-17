import Papers.PODC2019.LocalBroadcastBC.Phase

/-!
# Flooding (step (a) of Algorithm 1): Observation B.1 and completeness

For a run of `alg1` in a reliable local-broadcast scenario we compute the local states
(`stAt r v`), and show that in every phase the values accepted by non-faulty nodes form a
`FloodOutcome` (`floodOutcome`): values received along paths whose nodes other than the first are
non-faulty are the values *flooded* by the first node (`fv`), and along simple such paths they are
indeed received. For a faulty node `a`, the flooded value `fv a` is what its (identically
received, by local broadcast) first-round message says about the empty path.
-/

open Finset Cslib.Byzantine.LockStep

namespace LocalBroadcastBC

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : ℕ}
  {sel : Finset V → V → V → List V}

/-! ### `readVal` and `newVal` -/

omit [Fintype V] [DecidableEq V] in
lemma readVal_single {j : ℕ} {P : List V} {c b : Bool}
    (h : readVal j P (some ({(c, [])} : Msg V)) = some b) : P = [] ∧ b = c := by
  unfold readVal at h
  by_cases hP : P = []
  · subst hP
    cases c <;> simp_all
  · simp_all

omit [Fintype V] [DecidableEq V] in
lemma readVal_single_nil (c : Bool) : readVal 0 ([] : List V) (some ({(c, [])} : Msg V)) = some c := by
  unfold readVal; cases c <;> simp

omit [Fintype V] [DecidableEq V] in
lemma readVal_fresh {j : ℕ} (hj : j ≠ 0) (fr : List V → Option Bool) (P : List V) :
    readVal j P (some ({q | fr q.2 = some q.1} : Msg V)) = fr P := by
  unfold readVal
  rcases h : fr P with _ | b
  · simp [h, hj]
  · cases b <;> simp [h]

omit [Fintype V] [DecidableEq V] in
lemma readVal_zero_nil_isSome (m : Option (Msg V)) : (readVal 0 ([] : List V) m).isSome := by
  unfold readVal; split_ifs <;> simp_all

omit [Fintype V] in
lemma newVal_eq_some {v : V} {j : ℕ} {acc : List V → Option Bool} {I : V → Option (Msg V)}
    {K : List V} {b : Bool} :
    newVal G v j acc I K = some b ↔ ∃ u, K.getLast? = some u ∧ acc K = none ∧ G.Adj u v ∧
      IsWalkList G K ∧ v ∉ K ∧ readVal j K.dropLast (I u) = some b := by
  unfold newVal
  rcases h : K.getLast? with _ | u
  · simp
  · simp only [Option.some.injEq, exists_eq_left']
    split_ifs with hc
    · exact ⟨fun h' => ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, h'⟩, fun h' => h'.2.2.2.2⟩
    · simp only [false_iff]
      rintro ⟨h1, h2, h3, h4, -⟩
      exact hc ⟨h1, h2, h3, h4⟩

omit [Fintype V] [DecidableEq V] in
lemma eq_singleton_of_dropLast_nil {K : List V} {u : V} (h : K.getLast? = some u)
    (h2 : K.dropLast = []) : K = [u] := by
  have := List.dropLast_append_getLast? u h
  rw [h2] at this; simpa using this.symm

/-! ### Runs of `alg1` -/

variable (G f sel) (s : Scenario V Bool (Msg V))

/-- The local state of `v` after `r` rounds. -/
noncomputable def stAt (r : ℕ) (v : V) : LState V :=
  state G f sel v (s.input v) (hist G (alg1 G f sel) s r v)

/-- The inbox of `v` in round `r`. -/
noncomputable def inboxAt (r : ℕ) (v : V) : V → Option (Msg V) :=
  fun p => deliver G (alg1 G f sel) s (hist G (alg1 G f sel) s r) r p v

/-- Values newly received by `v` in round `r`. -/
noncomputable def freshAt (r : ℕ) (v : V) : List V → Option Bool :=
  newVal G v (r % rounds (V := V)) (stAt G f sel s r v).acc (inboxAt G f sel s r v)

/-- Values received by `v` up to round `r` of the current phase. -/
noncomputable def accAt (r : ℕ) (v : V) : List V → Option Bool :=
  fun K => ((stAt G f sel s r v).acc K).or (freshAt G f sel s r v K)

variable {G f sel s}

lemma stAt_succ (r : ℕ) (v : V) :
    stAt G f sel s (r + 1) v = stepState G f sel v (stAt G f sel s r v) (inboxAt G f sel s r v) := by
  simp only [stAt, state, hist_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

lemma stAt_t (r : ℕ) (v : V) : (stAt G f sel s r v).t = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [stAt_succ]
    dsimp only [stepState]
    split <;> simp [ih]

lemma stAt_zero (v : V) : stAt G f sel s 0 v = initState (s.input v) := rfl

lemma stAt_succ_of_ne {r : ℕ} {v : V} (h : r % rounds (V := V) + 1 ≠ rounds (V := V)) :
    stAt G f sel s (r + 1) v = LState.mk (stAt G f sel s r v).γ (r + 1)
      (accAt G f sel s r v) (freshAt G f sel s r v) := by
  rw [stAt_succ]
  unfold stepState
  rw [stAt_t] at *
  simp only [h, ite_false]
  rfl

lemma stAt_succ_of_eq {r : ℕ} {v : V} (h : r % rounds (V := V) + 1 = rounds (V := V)) :
    stAt G f sel s (r + 1) v = LState.mk (phaseUpdate G f sel (r / rounds (V := V)) v
      (stAt G f sel s r v).γ (accAt G f sel s r v)) (r + 1) (fun _ => none) (fun _ => none) := by
  rw [stAt_succ]
  unfold stepState
  rw [stAt_t] at *
  simp only [h, ite_true]
  rfl

lemma inboxAt_honest (hrel : s.Reliable) {r : ℕ} {p v : V} (hp : p ∉ s.byz) (hadj : G.Adj p v) :
    inboxAt G f sel s r v p = some (outMsg (stAt G f sel s r p)) :=
  deliver_honest G _ s hrel hp hadj

lemma inboxAt_byz {r : ℕ} {p v : V} (hp : p ∈ s.byz) (hadj : G.Adj p v) :
    inboxAt G f sel s r v p = s.adv r p v :=
  deliver_byz G _ s hp hadj

open Classical in
/-- The value flooded by `a` in phase `k`: its state if it is non-faulty, otherwise what its
(broadcast) first message of the phase says about the empty path. -/
noncomputable def fv (G : SimpleGraph V) (f : ℕ) (sel : Finset V → V → V → List V)
    (s : Scenario V Bool (Msg V)) (k : ℕ) (a : V) : Bool :=
  if a ∈ s.byz then (readVal 0 ([] : List V) (s.adv (k * rounds (V := V)) a a)).getD true
  else (stAt G f sel s (k * rounds (V := V)) a).γ

/-- Non-faulty tail: all nodes of `K` except possibly the first are non-faulty. -/
def HonTail (s : Scenario V Bool (Msg V)) (K : List V) : Prop := ∀ z ∈ K.tail, z ∉ s.byz

omit [Fintype V] [DecidableEq V] in
lemma HonTail.dropLast {s : Scenario V Bool (Msg V)} {K : List V} (h : HonTail s K) :
    HonTail s K.dropLast := fun z hz => h z (by
  rw [List.tail_dropLast] at hz; exact List.dropLast_subset _ hz)

omit [Fintype V] [DecidableEq V] in
lemma mem_tail_of_getLast {K : List V} {u : V} (h : K.getLast? = some u) (h2 : 2 ≤ K.length) :
    u ∈ K.tail := by
  rcases K with _ | ⟨a, t⟩
  · simp at h2
  · rcases t with _ | ⟨b, t'⟩
    · simp at h2
    · simp only [List.tail_cons]
      have : (a :: b :: t').getLast? = (b :: t').getLast? := by simp [List.getLast?_cons_cons]
      rw [this] at h
      exact List.mem_of_getLast? h

lemma freshAt_acc {r : ℕ} {v : V} {K : List V} {b : Bool}
    (h : freshAt G f sel s r v K = some b) : accAt G f sel s r v K = some b := by
  obtain ⟨u, -, hacc, -⟩ := newVal_eq_some.1 h
  simp [accAt, hacc, h]

/-! ### Phases -/

variable (hR : 0 < rounds (V := V))
include hR

omit [DecidableEq V] hR in
lemma mod_phase {k j : ℕ} (hj : j < rounds (V := V)) : (k * rounds (V := V) + j) % rounds (V := V) = j := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

omit [DecidableEq V] in
lemma div_phase {k j : ℕ} (hj : j < rounds (V := V)) : (k * rounds (V := V) + j) / rounds (V := V) = k := by
  rw [Nat.mul_comm, Nat.mul_add_div hR, Nat.div_eq_of_lt hj, Nat.add_zero]

lemma acc_phase_start (k : ℕ) (v : V) : (stAt G f sel s (k * rounds (V := V)) v).acc = fun _ => none := by
  rcases k with _ | k
  · simp [stAt_zero, initState]
  · have : (k + 1) * rounds (V := V) = (k * rounds (V := V) + (rounds (V := V) - 1)) + 1 := by
      rw [Nat.add_mul]; omega
    rw [this, stAt_succ_of_eq]
    rw [mod_phase (by omega)]; omega

omit hR in
/-- During a phase, the state `γ` does not change. -/
lemma γ_phase {k j : ℕ} (hj : j < rounds (V := V)) (v : V) :
    (stAt G f sel s (k * rounds (V := V) + j) v).γ = (stAt G f sel s (k * rounds (V := V)) v).γ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, stAt_succ_of_ne (by rw [mod_phase (by omega)]; omega)]
    exact ih (by omega)

omit hR in
lemma acc_succ {k j : ℕ} (hj : j + 1 < rounds (V := V)) (v : V) :
    (stAt G f sel s (k * rounds (V := V) + (j + 1)) v).acc = accAt G f sel s (k * rounds (V := V) + j) v := by
  rw [← Nat.add_assoc, stAt_succ_of_ne (by rw [mod_phase (by omega)]; omega)]

omit hR in
lemma fresh_succ {k j : ℕ} (hj : j + 1 < rounds (V := V)) (v : V) :
    (stAt G f sel s (k * rounds (V := V) + (j + 1)) v).fresh = freshAt G f sel s (k * rounds (V := V) + j) v := by
  rw [← Nat.add_assoc, stAt_succ_of_ne (by rw [mod_phase (by omega)]; omega)]

/-- The state at the end of phase `k`. -/
lemma γ_phase_end (k : ℕ) (v : V) :
    (stAt G f sel s ((k + 1) * rounds (V := V)) v).γ =
      phaseUpdate G f sel k v (stAt G f sel s (k * rounds (V := V)) v).γ
        (accAt G f sel s (k * rounds (V := V) + (rounds (V := V) - 1)) v) := by
  have : (k + 1) * rounds (V := V) = (k * rounds (V := V) + (rounds (V := V) - 1)) + 1 := by
    rw [Nat.add_mul]; omega
  rw [this, stAt_succ_of_eq (by rw [mod_phase (by omega)]; omega), div_phase hR (by omega),
    γ_phase (by omega)]

/-- The flooding invariant for round `j` of phase `k`. -/
structure FloodInv (k j : ℕ) : Prop where
  sound : ∀ y, y ∉ s.byz → ∀ K b, accAt G f sel s (k * rounds (V := V) + j) y K = some b → HonTail s K →
    ∃ a, K.head? = some a ∧ b = fv G f sel s k a
  len : ∀ y, y ∉ s.byz → ∀ K b, accAt G f sel s (k * rounds (V := V) + j) y K = some b → HonTail s K →
    K.length ≤ j + 1
  fresh : ∀ y, y ∉ s.byz → ∀ K b, freshAt G f sel s (k * rounds (V := V) + j) y K = some b → HonTail s K →
    K.length = j + 1 ∧ ∃ a, K.head? = some a ∧ b = fv G f sel s k a
  freshC : ∀ y, y ∉ s.byz → ∀ K a, K.head? = some a → IsPathList G (K ++ [y]) → HonTail s K →
    K.length = j + 1 → freshAt G f sel s (k * rounds (V := V) + j) y K = some (fv G f sel s k a)
  complete : ∀ y, y ∉ s.byz → ∀ K a, K.head? = some a → IsPathList G (K ++ [y]) → HonTail s K →
    K.length ≤ j + 1 → accAt G f sel s (k * rounds (V := V) + j) y K = some (fv G f sel s k a)

omit hR in
omit [Fintype V] [DecidableEq V] in
lemma path_append_singleton {K : List V} {y u : V} (h : IsPathList G (K ++ [y]))
    (hu : K.getLast? = some u) : G.Adj u y ∧ IsWalkList G K ∧ y ∉ K ∧ IsPathList G K := by
  obtain ⟨hc, hn⟩ := h
  rw [List.isChain_append] at hc
  rw [List.nodup_append] at hn
  refine ⟨hc.2.2 u hu y (by simp), hc.1, fun hy => hn.2.2 y hy y (by simp) rfl, hc.1, hn.1⟩

omit hR in
omit [Fintype V] [DecidableEq V] in
lemma path_dropLast {K : List V} {u : V} (h : IsPathList G K) (hu : K.getLast? = some u) :
    IsPathList G (K.dropLast ++ [u]) := by
  rwa [List.dropLast_append_getLast? u hu]

omit hR in
omit [Fintype V] [DecidableEq V] in
lemma head?_dropLast_of_two_le {K : List V} (h : 2 ≤ K.length) : K.dropLast.head? = K.head? := by
  rcases K with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp_all

omit hR in
omit [Fintype V] [DecidableEq V] in
lemma length_le_one_of_honTail {s : Scenario V Bool (Msg V)} {K : List V} {u : V}
    (hK : HonTail s K) (hu : K.getLast? = some u) (hb : u ∈ s.byz) : K = [u] := by
  by_cases h2 : 2 ≤ K.length
  · exact absurd hb (hK u (mem_tail_of_getLast hu h2))
  · rcases K with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hu
    · simp at hu; simp [hu]
    · simp at h2

lemma acc_phase_start' (k : ℕ) (v : V) (K : List V) :
    (stAt G f sel s (k * rounds (V := V) + 0) v).acc K = none := by
  rw [Nat.add_zero, acc_phase_start hR]

omit hR in
lemma outMsg_zero (k : ℕ) (u : V) :
    outMsg (stAt G f sel s (k * rounds (V := V) + 0) u) =
      {((stAt G f sel s (k * rounds (V := V)) u).γ, [])} := by
  rw [Nat.add_zero]
  simp [outMsg, stAt_t, Nat.mul_mod_left]

omit hR in
lemma outMsg_succ {k j : ℕ} (hj : j + 1 < rounds (V := V)) (u : V) :
    outMsg (stAt G f sel s (k * rounds (V := V) + (j + 1)) u) =
      {q | freshAt G f sel s (k * rounds (V := V) + j) u q.2 = some q.1} := by
  have h1 : (stAt G f sel s (k * rounds (V := V) + (j + 1)) u).t % rounds (V := V) ≠ 0 := by
    rw [stAt_t, mod_phase hj]; omega
  simp only [outMsg, h1, ite_false, fresh_succ hj]

omit hR in
lemma fv_honest {k : ℕ} {u : V} (hu : u ∉ s.byz) :
    fv G f sel s k u = (stAt G f sel s (k * rounds (V := V)) u).γ := by
  simp [fv, hu]

omit hR in
lemma readVal_byz (hlb : IsLocalBroadcast s) {k : ℕ} {u y : V} (hu : u ∈ s.byz)
    (hadj : G.Adj u y) :
    readVal 0 [] (inboxAt G f sel s (k * rounds (V := V) + 0) y u) = some (fv G f sel s k u) := by
  rw [inboxAt_byz hu hadj, Nat.add_zero, hlb _ u y u]
  simp only [fv, hu, ite_true]
  have := readVal_zero_nil_isSome (V := V) (s.adv (k * rounds (V := V)) u u)
  rcases h : readVal 0 ([] : List V) (s.adv (k * rounds (V := V)) u u) with _ | b
  · simp [h] at this
  · rfl

/-- **Flooding invariant** (Observation B.1 and its converse), by induction on the round `j` of
the phase. -/
theorem floodInv (hrel : s.Reliable) (hlb : IsLocalBroadcast s) (k : ℕ) :
    ∀ j, j < rounds (V := V) → FloodInv (G := G) (f := f) (sel := sel) (s := s) k j := by
  intro j
  induction j with
  | zero =>
    intro hj
    -- round 0: nothing received before
    have hfresh : ∀ y, y ∉ s.byz → ∀ K b,
        freshAt G f sel s (k * rounds (V := V) + 0) y K = some b → HonTail s K →
        K.length = 0 + 1 ∧ ∃ a, K.head? = some a ∧ b = fv G f sel s k a := by
      intro y hy K b hK hT
      obtain ⟨u, hu, -, hadj, -, -, hr⟩ := newVal_eq_some.1 hK
      rw [mod_phase hj] at hr
      by_cases hub : u ∈ s.byz
      · have := length_le_one_of_honTail hT hu hub
        subst this
        rw [List.dropLast_singleton, readVal_byz hlb hub hadj] at hr
        exact ⟨rfl, u, rfl, (Option.some.inj hr).symm⟩
      · rw [inboxAt_honest hrel hub hadj, outMsg_zero] at hr
        obtain ⟨h1, rfl⟩ := readVal_single hr
        have := eq_singleton_of_dropLast_nil hu h1
        subst this
        exact ⟨rfl, u, rfl, (fv_honest hub).symm⟩
    have hfreshC : ∀ y, y ∉ s.byz → ∀ K a, K.head? = some a → IsPathList G (K ++ [y]) →
        HonTail s K → K.length = 0 + 1 →
        freshAt G f sel s (k * rounds (V := V) + 0) y K = some (fv G f sel s k a) := by
      intro y hy K a ha hP hT hl
      obtain ⟨a', rfl⟩ := List.length_eq_one_iff.1 hl
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst ha
      obtain ⟨hadj, hw, hyK, -⟩ := path_append_singleton hP (u := a') (by simp)
      refine newVal_eq_some.2 ⟨a', by simp, acc_phase_start' hR k y _, hadj, hw, hyK, ?_⟩
      rw [mod_phase hj]
      simp only [List.dropLast_singleton]
      by_cases hab : a' ∈ s.byz
      · exact readVal_byz hlb hab hadj
      · rw [inboxAt_honest hrel hab hadj, outMsg_zero, readVal_single_nil, fv_honest hab]
    have hacc : ∀ y K, accAt G f sel s (k * rounds (V := V) + 0) y K =
        freshAt G f sel s (k * rounds (V := V) + 0) y K := by
      intro y K; simp [accAt, acc_phase_start hR]
    refine ⟨fun y hy K b h hT => ?_, fun y hy K b h hT => ?_, hfresh, hfreshC,
      fun y hy K a ha hP hT hl => ?_⟩
    · rw [hacc] at h; exact (hfresh y hy K b h hT).2
    · rw [hacc] at h; exact (hfresh y hy K b h hT).1.le
    · rw [hacc]
      have : K.length = 0 + 1 := by
        rcases K with _ | ⟨x, t⟩
        · simp at ha
        · simp at hl ⊢; omega
      exact hfreshC y hy K a ha hP hT this
  | succ j ih =>
    intro hj
    have IH := ih (by omega)
    have hbef : ∀ y, (stAt G f sel s (k * rounds (V := V) + (j + 1)) y).acc =
        accAt G f sel s (k * rounds (V := V) + j) y := fun y => acc_succ hj y
    have hfresh : ∀ y, y ∉ s.byz → ∀ K b,
        freshAt G f sel s (k * rounds (V := V) + (j + 1)) y K = some b → HonTail s K →
        K.length = j + 1 + 1 ∧ ∃ a, K.head? = some a ∧ b = fv G f sel s k a := by
      intro y hy K b hK hT
      obtain ⟨u, hu, hnone, hadj, -, -, hr⟩ := newVal_eq_some.1 hK
      rw [mod_phase hj] at hr
      by_cases hub : u ∈ s.byz
      · have := length_le_one_of_honTail hT hu hub
        subst this
        rw [hbef, IH.complete y hy [u] u rfl
          ⟨by simp [hadj], by simp [hadj.ne]⟩ (by simp [HonTail]) (by simp)] at hnone
        exact absurd hnone (by simp)
      · rw [inboxAt_honest hrel hub hadj, outMsg_succ hj, readVal_fresh (by omega)] at hr
        obtain ⟨hl, a, ha, rfl⟩ := IH.fresh u hub _ b hr hT.dropLast
        have hlen : K.length = j + 1 + 1 := by
          rw [List.length_dropLast] at hl
          have : K ≠ [] := by rintro rfl; simp at hu
          have := List.length_pos_iff.2 this
          omega
        refine ⟨hlen, a, ?_, rfl⟩
        rw [← head?_dropLast_of_two_le (by omega), ha]
    have hfreshC : ∀ y, y ∉ s.byz → ∀ K a, K.head? = some a → IsPathList G (K ++ [y]) →
        HonTail s K → K.length = j + 1 + 1 →
        freshAt G f sel s (k * rounds (V := V) + (j + 1)) y K = some (fv G f sel s k a) := by
      intro y hy K a ha hP hT hl
      obtain ⟨u, hu⟩ : ∃ u, K.getLast? = some u := by
        rcases h : K.getLast? with _ | u
        · rw [List.getLast?_eq_none_iff] at h; subst h; simp at hl
        · exact ⟨u, rfl⟩
      obtain ⟨hadj, hw, hyK, hPK⟩ := path_append_singleton hP hu
      have hub : u ∉ s.byz := hT u (mem_tail_of_getLast hu (by omega))
      have hnone : (stAt G f sel s (k * rounds (V := V) + (j + 1)) y).acc K = none := by
        rw [hbef]
        rcases h : accAt G f sel s (k * rounds (V := V) + j) y K with _ | b
        · rfl
        · have := IH.len y hy K b h hT; omega
      refine newVal_eq_some.2 ⟨u, hu, hnone, hadj, hw, hyK, ?_⟩
      rw [mod_phase hj, inboxAt_honest hrel hub hadj, outMsg_succ hj,
        readVal_fresh (by omega)]
      exact IH.freshC u hub _ a (by rw [head?_dropLast_of_two_le (by omega), ha])
        (path_dropLast hPK hu) hT.dropLast (by rw [List.length_dropLast]; omega)
    have hor : ∀ y K, accAt G f sel s (k * rounds (V := V) + (j + 1)) y K =
        (accAt G f sel s (k * rounds (V := V) + j) y K).or
          (freshAt G f sel s (k * rounds (V := V) + (j + 1)) y K) := by
      intro y K; simp [accAt, hbef]
    refine ⟨fun y hy K b h hT => ?_, fun y hy K b h hT => ?_, hfresh, hfreshC,
      fun y hy K a ha hP hT hl => ?_⟩
    · rw [hor] at h
      rcases h' : accAt G f sel s (k * rounds (V := V) + j) y K with _ | c
      · rw [h', Option.none_or] at h; exact (hfresh y hy K b h hT).2
      · rw [h', Option.some_or, Option.some.injEq] at h; subst h; exact IH.sound y hy K _ h' hT
    · rw [hor] at h
      rcases h' : accAt G f sel s (k * rounds (V := V) + j) y K with _ | c
      · rw [h', Option.none_or] at h; exact (hfresh y hy K b h hT).1.le
      · have := IH.len y hy K c h' hT; omega
    · rw [hor]
      by_cases hl' : K.length ≤ j + 1
      · rw [IH.complete y hy K a ha hP hT hl', Option.some_or]
      · rcases h' : accAt G f sel s (k * rounds (V := V) + j) y K with _ | c
        · rw [Option.none_or]; exact hfreshC y hy K a ha hP hT (by omega)
        · have := IH.len y hy K c h' hT; omega

open Classical in
/-- The outcome of step (a) of phase `k` is a `FloodOutcome` (Observation B.1 + completeness). -/
theorem floodOutcome (hrel : s.Reliable) (hlb : IsLocalBroadcast s) (k : ℕ) :
    FloodOutcome G s.byz.toFinset (fv G f sel s k)
      (fun v => accAt G f sel s (k * rounds (V := V) + (rounds (V := V) - 1)) v) := by
  have I := floodInv (G := G) (f := f) (sel := sel) hR hrel hlb k (rounds (V := V) - 1) (by omega)
  refine ⟨fun v hv K b h hT => ?_, fun v hv K a ha hP hT => ?_⟩
  · simp only [Set.mem_toFinset] at hv hT
    exact I.sound v hv K b h hT
  · simp only [Set.mem_toFinset] at hv hT
    refine I.complete v hv K a ha hP hT ?_
    have := hP.2.length_le_card
    simp only [List.length_append, List.length_singleton] at this
    unfold rounds
    omega

end LocalBroadcastBC
