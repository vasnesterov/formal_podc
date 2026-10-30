import Papers.PODC2023.MBroadcast.CausalModel

/-!
# Algorithm 2: invariants of reachable configurations

`Inv t C` collects the invariants of the global log and of the local states used in the safety
and liveness proofs; `Reachable.inv` proves that every reachable configuration satisfies them.
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Causal

open Finset

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]

/-- `p` received, at a position `< bound`, an `ack(m)` sent by `k`. -/
def AckRcvd (L : List (GEv P M)) (p : P) (m : M) (k : P) (bound : ℕ) : Prop :=
  ∃ w : ℕ, w < bound ∧ ∃ (y : ℕ) (r : Rec P M), L[w]? = some (.rcv p y) ∧ L[y]? = some (.snd r) ∧ r.src = k ∧
    r.body = .ack m

/-- `p` sent `init(m)` at a position `< bound`. -/
def InitSent (L : List (GEv P M)) (p : P) (m : M) (bound : ℕ) : Prop :=
  ∃ x : ℕ, x < bound ∧ ∃ r0 : Rec P M, L[x]? = some (.snd r0) ∧ r0.src = p ∧ r0.body = .init m

/-- The invariants of reachable configurations. -/
structure Inv (t : ℕ) (C : Cfg P M) : Prop where
  /-- Every reception is of a message sent earlier to the receiver, and respects causal
  delivery. -/
  rcv : ∀ (w : ℕ) (p : P) (y : ℕ), C.log[w]? = some (.rcv p y) → ∃ r, C.log[y]? = some (.snd r) ∧ y < w ∧
    p ∈ r.dst ∧ ∀ x ∈ r.dep, ∀ r' : Rec P M, C.log[x]? = some (.snd r') → p ∈ r'.dst →
      ∃ w' : ℕ, w' < w ∧ C.log[w']? = some (.rcv p x)
  /-- The causal past of a send contains the earlier sends and receptions of the sender. -/
  dep : ∀ (y : ℕ) (r : Rec P M), C.log[y]? = some (.snd r) →
    (∀ x : ℕ, x < y → ∀ r' : Rec P M, C.log[x]? = some (.snd r') → r'.src = r.src → x ∈ r.dep) ∧
    (∀ z : ℕ, z < y → ∀ x : ℕ, C.log[z]? = some (.rcv r.src x) → x ∈ r.dep)
  depLt : ∀ (y : ℕ) (r : Rec P M), C.log[y]? = some (.snd r) → ∀ x ∈ r.dep, x < y
  past : ∀ k : P, (∀ (x : ℕ) (r' : Rec P M), C.log[x]? = some (.snd r') → r'.src = k → x ∈ C.past k) ∧
    (∀ z x : ℕ, C.log[z]? = some (.rcv k x) → x ∈ C.past k)
  pastLt : ∀ k : P, ∀ x ∈ C.past k, x < C.log.length
  /-- `init(m)` is causally broadcast to all other processes, right after `bc`. -/
  init : ∀ (x : ℕ) (r : Rec P M) (m : M), C.log[x]? = some (.snd r) → r.body = .init m →
    r.dst = univ.erase r.src ∧ ∃ x' : ℕ, x' < x ∧ C.log[x']? = some (.mb (.bc r.src m))
  initU : ∀ (x x' : ℕ) (r r' : Rec P M) (m : M), C.log[x]? = some (.snd r) → C.log[x']? = some (.snd r') →
    r.body = .init m → r'.body = .init m → r.src = r'.src → x = x'
  /-- An `ack(m)` is sent right after the reception of `init(m)`, and is followed by the
  mdelivery of `m`. -/
  ack : ∀ (y : ℕ) (r : Rec P M) (m : M), C.log[y]? = some (.snd r) → r.body = .ack m → ∃ (z x : ℕ) (r0 : Rec P M), y = z + 1 ∧
    C.log[z]? = some (.rcv r.src x) ∧ C.log[x]? = some (.snd r0) ∧ r0.body = .init m ∧
    r.dst = {r0.src} ∧ r0.src ≠ r.src ∧ C.log[z + 2]? = some (.mb (.dl r.src r0.src m))
  /-- The handler of `init(m)` (lines 5–6) runs right after its reception. -/
  hdl : ∀ (z : ℕ) (p : P) (x : ℕ) (r0 : Rec P M) (m : M), C.log[z]? = some (.rcv p x) → C.log[x]? = some (.snd r0) →
    r0.body = .init m → ∃ r : Rec P M, C.log[z + 1]? = some (.snd r) ∧ r.src = p ∧ r.dst = {r0.src} ∧
      r.body = .ack m ∧ C.log[z + 2]? = some (.mb (.dl p r0.src m))
  /-- Origin of mdeliveries: own (line 3, after enough acks) or from the handler (line 6). -/
  dl : ∀ (j : ℕ) (p q : P) (m : M), C.log[j]? = some (.mb (.dl p q m)) →
    (q = p ∧ InitSent C.log p m j ∧ ∃ A : Finset P, p ∉ A ∧
        Fintype.card P - t - 1 ≤ A.card ∧ ∀ k ∈ A, AckRcvd C.log p m k j) ∨
    (q ≠ p ∧ ∃ (z x : ℕ) (r0 : Rec P M), j = z + 2 ∧ C.log[z]? = some (.rcv p x) ∧
        C.log[x]? = some (.snd r0) ∧ r0.src = q ∧ r0.body = .init m)
  phase : ∀ (p : P) (m : M) (A : Finset P), C.phase p = .wait m A → InitSent C.log p m C.log.length ∧ p ∉ A ∧
    (∀ k ∈ A, AckRcvd C.log p m k C.log.length) ∧ GEv.mb (.dl p p m) ∉ C.log
  ackIn : ∀ (p : P) (m : M) (A : Finset P), C.phase p = .wait m A →
    ∀ (w y : ℕ) (r : Rec P M), C.log[w]? = some (.rcv p y) →
    C.log[y]? = some (.snd r) → r.body = .ack m → r.src ∈ A
  live : ∀ (p : P) (m : M), GEv.mb (.bc p m) ∈ C.log →
    (∃ A : Finset P, C.phase p = .wait m A) ∨ GEv.mb (.dl p p m) ∈ C.log
  bcU : ∀ (p : P) (m : M), C.log.count (.mb (.bc p m)) ≤ 1
  dlU : ∀ (p q : P) (m : M), C.log.count (.mb (.dl p q m)) ≤ 1

lemma inv_init (t : ℕ) : Inv t (initCfg : Cfg P M) where
  rcv := by simp [initCfg]
  dep := by simp [initCfg]
  depLt := by simp [initCfg]
  past := by simp [initCfg]
  pastLt := by simp [initCfg]
  init := by simp [initCfg]
  initU := by simp [initCfg]
  ack := by simp [initCfg]
  hdl := by simp [initCfg]
  dl := by simp [initCfg]
  phase := by simp [initCfg]
  ackIn := by simp [initCfg]
  live := by simp [initCfg]
  bcU := by simp [initCfg]
  dlU := by simp [initCfg]

section Derived

variable {t : ℕ} {C : Cfg P M}

/-- Log-level validity. -/
lemma Inv.bc_of_dl (I : Inv t C) {j : ℕ} {p q : P} {m : M}
    (h : C.log[j]? = some (.mb (.dl p q m))) : ∃ j' < j, C.log[j']? = some (.mb (.bc q m)) := by
  rcases I.dl j p q m h with ⟨rfl, ⟨x, hx, r0, h1, h2, h3⟩, -⟩ | ⟨-, z, x, r0, rfl, h1, h2, h3, h4⟩
  · obtain ⟨-, x', hx', h'⟩ := I.init x r0 m h1 h3
    exact ⟨x', by omega, h2 ▸ h'⟩
  · obtain ⟨r, hr, hxz, -⟩ := I.rcv z p x h1
    rw [hr] at h2; cases h2
    obtain ⟨-, x', hx', h'⟩ := I.init x r0 m hr h4
    exact ⟨x', by omega, h3 ▸ h'⟩

lemma Inv.not_dl_of_not_bc (I : Inv t C) {p q : P} {m : M}
    (h : GEv.mb (.bc q m) ∉ C.log) : GEv.mb (.dl p q m) ∉ C.log := by
  intro hm
  obtain ⟨j, hj⟩ := mem_iff_getElem?'.1 hm
  obtain ⟨j', -, hj'⟩ := I.bc_of_dl hj
  exact h (List.mem_of_getElem? hj')

lemma Inv.no_init_of_not_bc (I : Inv t C) {p : P} {m : M}
    (h : GEv.mb (.bc p m) ∉ C.log) {x : ℕ} {r : Rec P M} (hx : C.log[x]? = some (.snd r))
    (hs : r.src = p) (hb : r.body = .init m) : False := by
  obtain ⟨-, x', -, h'⟩ := I.init x r m hx hb
  exact h (hs ▸ List.mem_of_getElem? h')

end Derived

section Lift

variable {L l : List (GEv P M)}

lemma AckRcvd.append {p : P} {m : M} {k : P} {b b' : ℕ} (h : AckRcvd L p m k b) (hb : b ≤ b') :
    AckRcvd (L ++ l) p m k b' := by
  obtain ⟨w, hw, y, r, h1, h2, h3, h4⟩ := h
  exact ⟨w, by omega, y, r, getElem?_append_of_some h1, getElem?_append_of_some h2, h3, h4⟩

lemma InitSent.append {p : P} {m : M} {b b' : ℕ} (h : InitSent L p m b) (hb : b ≤ b') :
    InitSent (L ++ l) p m b' := by
  obtain ⟨x, hx, r0, h1, h2, h3⟩ := h
  exact ⟨x, by omega, r0, getElem?_append_of_some h1, h2, h3⟩

lemma getElem?_old {i : ℕ} {a : GEv P M} (hi : i < L.length) (h : (L ++ l)[i]? = some a) :
    L[i]? = some a := by
  rwa [List.getElem?_append_left hi] at h

end Lift


/-! ## Preservation: invocation -/

section Invoke

variable {t : ℕ} {C : Cfg P M}

theorem Inv.invoke (I : Inv t C) {p : P} {m : M} (hid : C.phase p = .idle)
    (hbc : GEv.mb (.bc p m) ∉ C.log) :
    Inv t { C with
        log := C.log ++ [.mb (.bc p m), .snd ⟨p, univ.erase p, .init m, C.past p⟩]
        past := Function.update C.past p (insert (C.log.length + 1) (C.past p))
        phase := Function.update C.phase p (.wait m ∅) } := by
  refine ⟨?rcv, ?dep, ?depLt, ?past, ?pastLt, ?init, ?initU, ?ack, ?hdl, ?dl, ?phase, ?ackIn,
    ?live, ?bcU, ?dlU⟩ <;> dsimp only
  case rcv =>
    intro w q y h
    rcases getElem?_append_two h with h | ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨r, hr, hyw, hq, hc⟩ := I.rcv w q y h
      refine ⟨r, getElem?_append_of_some hr, hyw, hq, fun x hx r' hr' hq' => ?_⟩
      have hxl : x < C.log.length := by
        have := I.depLt y r hr x hx; have := lt_of_getElem?_eq_some hr; omega
      obtain ⟨w', hw', h'⟩ := hc x hx r' (getElem?_old hxl hr') hq'
      exact ⟨w', hw', getElem?_append_of_some h'⟩
    · cases h
    · cases h
  case dep =>
    intro y r h
    rcases getElem?_append_two h with h | ⟨rfl, he⟩ | ⟨rfl, he⟩
    · obtain ⟨h1, h2⟩ := I.dep y r h
      have hy := lt_of_getElem?_eq_some h
      exact ⟨fun x hx r' hr' => h1 x hx r' (getElem?_old (by omega) hr'),
        fun z hz x hzx => h2 z hz x (getElem?_old (by omega) hzx)⟩
    · cases he
    · cases he
      refine ⟨fun x hx r' hr' hsrc => ?_, fun z hz x hzx => ?_⟩
      · rcases getElem?_append_two hr' with hr' | ⟨-, hr'⟩ | ⟨hxe, -⟩
        · exact (I.past p).1 x r' hr' hsrc
        · cases hr'
        · omega
      · rcases getElem?_append_two hzx with hzx | ⟨-, hzx⟩ | ⟨-, hzx⟩
        · exact (I.past p).2 z x hzx
        · cases hzx
        · cases hzx
  case depLt =>
    intro y r h
    rcases getElem?_append_two h with h | ⟨rfl, he⟩ | ⟨rfl, he⟩
    · exact I.depLt y r h
    · cases he
    · cases he; intro x hx; have := I.pastLt p x hx; omega
  case past =>
    intro k
    refine ⟨fun x r' hr' hsrc => ?_, fun z x hzx => ?_⟩
    · rcases getElem?_append_two hr' with hr' | ⟨-, he⟩ | ⟨rfl, he⟩
      · have := (I.past k).1 x r' hr' hsrc
        by_cases hk : k = p
        · subst hk; simp [this]
        · simp [Function.update_of_ne hk, this]
      · cases he
      · cases he; subst hsrc; simp
    · rcases getElem?_append_two hzx with hzx | ⟨-, hzx⟩ | ⟨-, hzx⟩
      · have := (I.past k).2 z x hzx
        by_cases hk : k = p
        · subst hk; simp [this]
        · simp [Function.update_of_ne hk, this]
      · cases hzx
      · cases hzx
  case pastLt =>
    intro k x hx
    simp only [List.length_append, List.length_cons, List.length_nil]
    by_cases hk : k = p
    · subst hk
      simp only [Function.update_self, mem_insert] at hx
      rcases hx with rfl | hx
      · omega
      · have := I.pastLt k x hx; omega
    · rw [Function.update_of_ne hk] at hx
      have := I.pastLt k x hx; omega
  case init =>
    intro x r m' h hb
    rcases getElem?_append_two h with h | ⟨rfl, he⟩ | ⟨rfl, he⟩
    · obtain ⟨h1, x', hx', h'⟩ := I.init x r m' h hb
      exact ⟨h1, x', hx', getElem?_append_of_some h'⟩
    · cases he
    · cases he
      simp only [Body.init.injEq] at hb; subst hb
      refine ⟨rfl, C.log.length, by omega, ?_⟩
      simp
  case initU =>
    intro x x' r r' m' h h' hb hb' hsrc
    rcases getElem?_append_two h with h | ⟨rfl, he⟩ | ⟨rfl, he⟩ <;>
    rcases getElem?_append_two h' with h' | ⟨rfl, he'⟩ | ⟨rfl, he'⟩
    all_goals first | rfl | (cases he; done) | (cases he'; done) | skip
    · exact I.initU x x' r r' m' h h' hb hb' hsrc
    · cases he'
      simp only [Body.init.injEq] at hb'; subst hb'
      exact (I.no_init_of_not_bc hbc h hsrc hb).elim
    · cases he
      simp only [Body.init.injEq] at hb; subst hb
      exact (I.no_init_of_not_bc hbc h' hsrc.symm hb').elim
  case ack =>
    intro y r m' h hb
    rcases getElem?_append_two h with h | ⟨-, he⟩ | ⟨-, he⟩
    · obtain ⟨z, x, r0, h1, h2, h3, h4, h5, h6, h7⟩ := I.ack y r m' h hb
      exact ⟨z, x, r0, h1, getElem?_append_of_some h2, getElem?_append_of_some h3, h4, h5, h6,
        getElem?_append_of_some h7⟩
    · cases he
    · cases he; cases hb
  case hdl =>
    intro z q x r0 m' h hx hb
    rcases getElem?_append_two h with h | ⟨-, h⟩ | ⟨-, h⟩
    · obtain ⟨r, hr, hxz, -⟩ := I.rcv z q x h
      have := lt_of_getElem?_eq_some h
      obtain ⟨r1, h1, h2, h3, h4, h5⟩ := I.hdl z q x r0 m' h (getElem?_old (by omega) hx) hb
      exact ⟨r1, getElem?_append_of_some h1, h2, h3, h4, getElem?_append_of_some h5⟩
    · cases h
    · cases h
  case dl =>
    intro j q q' m' h
    rcases getElem?_append_two h with h | ⟨-, h⟩ | ⟨-, h⟩
    · rcases I.dl j q q' m' h with ⟨h1, h2, A, h3, h4, h5⟩ | ⟨h1, z, x, r0, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨h1, h2.append le_rfl, A, h3, h4, fun k hk => (h5 k hk).append le_rfl⟩
      · exact Or.inr ⟨h1, z, x, r0, h2, getElem?_append_of_some h3, getElem?_append_of_some h4,
          h5, h6⟩
    · cases h
    · cases h
  case phase =>
    intro q m' A h
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self, Phase.wait.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨C.log.length + 1, by simp, ⟨q, univ.erase q, .init m, C.past q⟩, by simp, rfl, rfl⟩,
        by simp, by simp, ?_⟩
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨I.not_dl_of_not_bc hbc, by simp, by simp⟩
    · rw [Function.update_of_ne hq] at h
      obtain ⟨h1, h2, h3, h4⟩ := I.phase q m' A h
      refine ⟨h1.append (by simp), h2, fun k hk => (h3 k hk).append (by simp), ?_⟩
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h4, by simp, by simp⟩
  case ackIn =>
    intro q m' A h w y r hw hy hb
    rcases getElem?_append_two hw with hw | ⟨-, hw⟩ | ⟨-, hw⟩
    · obtain ⟨r1, hr1, hyw, hq1, -⟩ := I.rcv w q y hw
      have := lt_of_getElem?_eq_some hw
      have hy' := getElem?_old (by omega) hy
      rw [hy'] at hr1; cases hr1
      by_cases hq : q = p
      · subst hq
        simp only [Function.update_self, Phase.wait.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exfalso
        obtain ⟨z, x, r0, -, -, h3, h4, h5, -, -⟩ := I.ack y r _ hy' hb
        rw [h5, mem_singleton] at hq1
        exact I.no_init_of_not_bc hbc h3 hq1.symm h4
      · rw [Function.update_of_ne hq] at h
        exact I.ackIn q m' A h w y r hw hy' hb
    · cases hw
    · cases hw
  case live =>
    intro q m' h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · rcases I.live q m' h with ⟨A, hA⟩ | h'
      · by_cases hq : q = p
        · subst hq; rw [hid] at hA; cases hA
        · exact Or.inl ⟨A, by rw [Function.update_of_ne hq]; exact hA⟩
      · exact Or.inr (List.mem_append_left _ h')
    · simp only [GEv.mb.injEq, Ev.bc.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨∅, by simp⟩
    · cases h
  case bcU =>
    intro q m'
    have := I.bcU q m'
    simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
    by_cases h : q = p ∧ m' = m
    · obtain ⟨rfl, rfl⟩ := h
      rw [List.count_eq_zero_of_not_mem hbc]; simp
    · have : ¬ (GEv.mb (.bc p m) : GEv P M) = .mb (.bc q m') := by
        simp only [GEv.mb.injEq, Ev.bc.injEq]; tauto
      simp [this]; omega
  case dlU =>
    intro q q' m'
    have := I.dlU q q' m'
    simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
    simp; omega

end Invoke

/-! ## Preservation: own mdelivery (line 3) -/

section Own

variable {t : ℕ} {C : Cfg P M}

theorem Inv.own (I : Inv t C) {p : P} {m : M} {A : Finset P} (hph : C.phase p = .wait m A)
    (hA : Fintype.card P - t - 1 ≤ A.card) :
    Inv t { C with
        log := C.log ++ [.mb (.dl p p m)]
        phase := Function.update C.phase p .idle } := by
  obtain ⟨hP1, hP2, hP3, hP4⟩ := I.phase p m A hph
  refine ⟨?rcv, ?dep, ?depLt, ?past, ?pastLt, ?init, ?initU, ?ack, ?hdl, ?dl, ?phase, ?ackIn,
    ?live, ?bcU, ?dlU⟩ <;> dsimp only
  case rcv =>
    intro w q y h
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨r, hr, hyw, hq, hc⟩ := I.rcv w q y h
      refine ⟨r, getElem?_append_of_some hr, hyw, hq, fun x hx r' hr' hq' => ?_⟩
      have hxl : x < C.log.length := by
        have := I.depLt y r hr x hx; have := lt_of_getElem?_eq_some hr; omega
      obtain ⟨w', hw', h'⟩ := hc x hx r' (getElem?_old hxl hr') hq'
      exact ⟨w', hw', getElem?_append_of_some h'⟩
    · cases he
  case dep =>
    intro y r h
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨h1, h2⟩ := I.dep y r h
      have hy := lt_of_getElem?_eq_some h
      exact ⟨fun x hx r' hr' => h1 x hx r' (getElem?_old (by omega) hr'),
        fun z hz x hzx => h2 z hz x (getElem?_old (by omega) hzx)⟩
    · cases he
  case depLt =>
    intro y r h
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · exact I.depLt y r h
    · cases he
  case past =>
    intro k
    refine ⟨fun x r' hr' hsrc => ?_, fun z x hzx => ?_⟩
    · rcases getElem?_append_one hr' with hr' | ⟨-, he⟩
      · exact (I.past k).1 x r' hr' hsrc
      · cases he
    · rcases getElem?_append_one hzx with hzx | ⟨-, he⟩
      · exact (I.past k).2 z x hzx
      · cases he
  case pastLt =>
    intro k x hx
    have := I.pastLt k x hx; simp; omega
  case init =>
    intro x r m' h hb
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨h1, x', hx', h'⟩ := I.init x r m' h hb
      exact ⟨h1, x', hx', getElem?_append_of_some h'⟩
    · cases he
  case initU =>
    intro x x' r r' m' h h' hb hb' hsrc
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · rcases getElem?_append_one h' with h' | ⟨-, he'⟩
      · exact I.initU x x' r r' m' h h' hb hb' hsrc
      · cases he'
    · cases he
  case ack =>
    intro y r m' h hb
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨z, x, r0, h1, h2, h3, h4, h5, h6, h7⟩ := I.ack y r m' h hb
      exact ⟨z, x, r0, h1, getElem?_append_of_some h2, getElem?_append_of_some h3, h4, h5, h6,
        getElem?_append_of_some h7⟩
    · cases he
  case hdl =>
    intro z q x r0 m' h hx hb
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨r, hr, hxz, -⟩ := I.rcv z q x h
      have := lt_of_getElem?_eq_some h
      obtain ⟨r1, h1, h2, h3, h4, h5⟩ := I.hdl z q x r0 m' h (getElem?_old (by omega) hx) hb
      exact ⟨r1, getElem?_append_of_some h1, h2, h3, h4, getElem?_append_of_some h5⟩
    · cases he
  case dl =>
    intro j q q' m' h
    rcases getElem?_append_one h with h | ⟨rfl, he⟩
    · rcases I.dl j q q' m' h with ⟨h1, h2, A, h3, h4, h5⟩ | ⟨h1, z, x, r0, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨h1, h2.append le_rfl, A, h3, h4, fun k hk => (h5 k hk).append le_rfl⟩
      · exact Or.inr ⟨h1, z, x, r0, h2, getElem?_append_of_some h3, getElem?_append_of_some h4,
          h5, h6⟩
    · simp only [GEv.mb.injEq, Ev.dl.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inl ⟨rfl, hP1.append le_rfl, A, hP2, hA, fun k hk => (hP3 k hk).append le_rfl⟩
  case phase =>
    intro q m' A' h
    by_cases hq : q = p
    · subst hq; simp at h
    · rw [Function.update_of_ne hq] at h
      obtain ⟨h1, h2, h3, h4⟩ := I.phase q m' A' h
      refine ⟨h1.append (by simp), h2, fun k hk => (h3 k hk).append (by simp), ?_⟩
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨h4, ?_⟩
      simp only [GEv.mb.injEq, Ev.dl.injEq]; tauto
  case ackIn =>
    intro q m' A' h w y r hw hy hb
    by_cases hq : q = p
    · subst hq; simp at h
    rw [Function.update_of_ne hq] at h
    rcases getElem?_append_one hw with hw | ⟨-, he⟩
    · obtain ⟨r1, hr1, hyw, -, -⟩ := I.rcv w q y hw
      have := lt_of_getElem?_eq_some hw
      exact I.ackIn q m' A' h w y r hw (getElem?_old (by omega) hy) hb
    · cases he
  case live =>
    intro q m' h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · rcases I.live q m' h with ⟨A', hA'⟩ | h'
      · by_cases hq : q = p
        · subst hq
          rw [hph] at hA'
          simp only [Phase.wait.injEq] at hA'
          obtain ⟨rfl, -⟩ := hA'
          exact Or.inr (by simp)
        · exact Or.inl ⟨A', by rw [Function.update_of_ne hq]; exact hA'⟩
      · exact Or.inr (List.mem_append_left _ h')
    · cases h
  case bcU =>
    intro q m'
    have := I.bcU q m'
    simp; omega
  case dlU =>
    intro q q' m'
    have := I.dlU q q' m'
    simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
    by_cases h : q = p ∧ q' = p ∧ m' = m
    · obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.count_eq_zero_of_not_mem hP4]; simp
    · have : ¬ (GEv.mb (.dl p p m) : GEv P M) = .mb (.dl q q' m') := by
        simp only [GEv.mb.injEq, Ev.dl.injEq]; tauto
      simp [this]; omega

end Own

/-! ## Preservation: reception -/

section Recv

variable {t : ℕ} {C : Cfg P M}

/-- The new reception respects causal delivery (common part of both kinds of messages). -/
lemma Inv.rcv_new (I : Inv t C) {p : P} {x : ℕ} {r : Rec P M} (l : List (GEv P M))
    (hx : C.log[x]? = some (.snd r)) (hcaus : CausalReady C.log p r) :
    ∀ x' ∈ r.dep, ∀ r' : Rec P M, (C.log ++ l)[x']? = some (.snd r') → p ∈ r'.dst →
      ∃ w' : ℕ, w' < C.log.length ∧ (C.log ++ l)[w']? = some (.rcv p x') := by
  intro x' hx' r' hr' hp'
  have h1 := I.depLt x r hx x' hx'
  have h2 := lt_of_getElem?_eq_some hx
  have hr'' := getElem?_old (by omega) hr'
  obtain ⟨w', hw'⟩ := mem_iff_getElem?'.1 (hcaus x' hx' (needs_iff.2 ⟨r', hr'', hp'⟩))
  exact ⟨w', lt_of_getElem?_eq_some hw', getElem?_append_of_some hw'⟩

theorem Inv.recvInit (I : Inv t C) {p : P} {x : ℕ} {r : Rec P M} {m : M}
    (hx : C.log[x]? = some (.snd r)) (hdst : p ∈ r.dst) (hnr : GEv.rcv p x ∉ C.log)
    (hcaus : CausalReady C.log p r) (hb : r.body = .init m) (hsp : r.src ≠ p) :
    Inv t { C with
        log := C.log ++ [.rcv p x, .snd ⟨p, {r.src}, .ack m, C.past p ∪ r.dep ∪ {x}⟩,
          .mb (.dl p r.src m)]
        past := Function.update C.past p (insert (C.log.length + 1) (C.past p ∪ r.dep ∪ {x})) } := by
  have hxl := lt_of_getElem?_eq_some hx
  refine ⟨?rcv, ?dep, ?depLt, ?past, ?pastLt, ?init, ?initU, ?ack, ?hdl, ?dl, ?phase, ?ackIn,
    ?live, ?bcU, ?dlU⟩ <;> dsimp only
  case rcv =>
    intro w q y h
    rcases getElem?_append_three h with h | ⟨rfl, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
    · obtain ⟨r, hr, hyw, hq, hc⟩ := I.rcv w q y h
      refine ⟨r, getElem?_append_of_some hr, hyw, hq, fun x hx r' hr' hq' => ?_⟩
      have hxl : x < C.log.length := by
        have := I.depLt y r hr x hx; have := lt_of_getElem?_eq_some hr; omega
      obtain ⟨w', hw', h'⟩ := hc x hx r' (getElem?_old hxl hr') hq'
      exact ⟨w', hw', getElem?_append_of_some h'⟩
    · cases he
      exact ⟨r, getElem?_append_of_some hx, hxl, hdst, I.rcv_new _ hx hcaus⟩
    · cases he
    · cases he
  case dep =>
    intro y r' h
    rcases getElem?_append_three h with h | ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩
    · obtain ⟨h1, h2⟩ := I.dep y r' h
      have hy := lt_of_getElem?_eq_some h
      exact ⟨fun x hx r' hr' => h1 x hx r' (getElem?_old (by omega) hr'),
        fun z hz x hzx => h2 z hz x (getElem?_old (by omega) hzx)⟩
    · cases he
    · cases he
      refine ⟨fun x0 hx0 r' hr' hsrc => ?_, fun z hz x0 hzx => ?_⟩
      · rcases getElem?_append_three hr' with hr' | ⟨-, he⟩ | ⟨hxe, -⟩ | ⟨hxe, -⟩
        · simp [(I.past p).1 x0 r' hr' hsrc]
        · cases he
        · omega
        · omega
      · rcases getElem?_append_three hzx with hzx | ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
        · simp [(I.past p).2 z x0 hzx]
        · cases he; simp
        · cases he
        · cases he
    · cases he
  case depLt =>
    intro y r' h
    rcases getElem?_append_three h with h | ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩
    · exact I.depLt y r' h
    · cases he
    · cases he
      intro x0 hx0
      simp only [mem_union, mem_singleton] at hx0
      rcases hx0 with (hx0 | hx0) | rfl
      · have := I.pastLt p x0 hx0; omega
      · have := I.depLt x r hx x0 hx0; omega
      · omega
    · cases he
  case past =>
    intro k
    refine ⟨fun x0 r' hr' hsrc => ?_, fun z x0 hzx => ?_⟩
    · rcases getElem?_append_three hr' with hr' | ⟨-, he⟩ | ⟨rfl, he⟩ | ⟨-, he⟩
      · have := (I.past k).1 x0 r' hr' hsrc
        by_cases hk : k = p
        · subst hk; simp [this]
        · simp [Function.update_of_ne hk, this]
      · cases he
      · cases he; subst hsrc; simp
      · cases he
    · rcases getElem?_append_three hzx with hzx | ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
      · have := (I.past k).2 z x0 hzx
        by_cases hk : k = p
        · subst hk; simp [this]
        · simp [Function.update_of_ne hk, this]
      · cases he; simp
      · cases he
      · cases he
  case pastLt =>
    intro k x0 hx0
    simp only [List.length_append, List.length_cons, List.length_nil]
    by_cases hk : k = p
    · subst hk
      simp only [Function.update_self, mem_insert, mem_union, mem_singleton] at hx0
      rcases hx0 with rfl | (hx0 | hx0) | rfl
      · omega
      · have := I.pastLt k x0 hx0; omega
      · have := I.depLt x r hx x0 hx0; omega
      · omega
    · rw [Function.update_of_ne hk] at hx0
      have := I.pastLt k x0 hx0; omega
  case init =>
    intro x0 r' m' h hb'
    rcases getElem?_append_three h with h | ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
    · obtain ⟨h1, x', hx', h'⟩ := I.init x0 r' m' h hb'
      exact ⟨h1, x', hx', getElem?_append_of_some h'⟩
    · cases he
    · cases he; cases hb'
    · cases he
  case initU =>
    intro x0 x' r1 r2 m' h h' hb1 hb2 hsrc
    rcases getElem?_append_three h with h | ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
    · rcases getElem?_append_three h' with h' | ⟨-, he'⟩ | ⟨-, he'⟩ | ⟨-, he'⟩
      · exact I.initU x0 x' r1 r2 m' h h' hb1 hb2 hsrc
      · cases he'
      · cases he'; cases hb2
      · cases he'
    · cases he
    · cases he; cases hb1
    · cases he
  case ack =>
    intro y r' m' h hb'
    rcases getElem?_append_three h with h | ⟨-, he⟩ | ⟨rfl, he⟩ | ⟨-, he⟩
    · obtain ⟨z, x, r0, h1, h2, h3, h4, h5, h6, h7⟩ := I.ack y r' m' h hb'
      exact ⟨z, x, r0, h1, getElem?_append_of_some h2, getElem?_append_of_some h3, h4, h5, h6,
        getElem?_append_of_some h7⟩
    · cases he
    · cases he
      simp only [Body.ack.injEq] at hb'; subst hb'
      refine ⟨C.log.length, x, r, rfl, by simp, getElem?_append_of_some hx, hb, rfl, hsp, ?_⟩
      simp
    · cases he
  case hdl =>
    intro z q x0 r0 m' h hx0 hb0
    rcases getElem?_append_three h with h | ⟨rfl, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
    · obtain ⟨r1, hr1, hxz, -⟩ := I.rcv z q x0 h
      have := lt_of_getElem?_eq_some h
      obtain ⟨r1, h1, h2, h3, h4, h5⟩ := I.hdl z q x0 r0 m' h (getElem?_old (by omega) hx0) hb0
      exact ⟨r1, getElem?_append_of_some h1, h2, h3, h4, getElem?_append_of_some h5⟩
    · cases he
      rw [getElem?_old hxl hx0] at hx; cases hx
      rw [hb] at hb0; cases hb0
      exact ⟨⟨p, {r.src}, .ack m, C.past p ∪ r.dep ∪ {x}⟩, by simp, rfl, rfl, rfl, by simp⟩
    · cases he
    · cases he
  case dl =>
    intro j q q' m' h
    rcases getElem?_append_three h with h | ⟨-, he⟩ | ⟨-, he⟩ | ⟨rfl, he⟩
    · rcases I.dl j q q' m' h with ⟨h1, h2, A, h3, h4, h5⟩ | ⟨h1, z, x, r0, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨h1, h2.append le_rfl, A, h3, h4, fun k hk => (h5 k hk).append le_rfl⟩
      · exact Or.inr ⟨h1, z, x, r0, h2, getElem?_append_of_some h3, getElem?_append_of_some h4,
          h5, h6⟩
    · cases he
    · cases he
    · simp only [GEv.mb.injEq, Ev.dl.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr ⟨hsp, C.log.length, x, r, rfl, by simp, getElem?_append_of_some hx, rfl, hb⟩
  case phase =>
    intro q m' A' h
    obtain ⟨h1, h2, h3, h4⟩ := I.phase q m' A' h
    refine ⟨h1.append (by simp), h2, fun k hk => (h3 k hk).append (by simp), ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨h4, by simp, by simp, ?_⟩
    simp only [GEv.mb.injEq, Ev.dl.injEq]
    rintro ⟨rfl, h, -⟩; exact hsp h.symm
  case ackIn =>
    intro q m' A' h w y r' hw hy hb'
    rcases getElem?_append_three hw with hw | ⟨rfl, he⟩ | ⟨-, he⟩ | ⟨-, he⟩
    · obtain ⟨r1, hr1, hyw, -, -⟩ := I.rcv w q y hw
      have := lt_of_getElem?_eq_some hw
      exact I.ackIn q m' A' h w y r' hw (getElem?_old (by omega) hy) hb'
    · cases he
      rw [getElem?_old hxl hy] at hx; cases hx
      rw [hb] at hb'; cases hb'
    · cases he
    · cases he
  case live =>
    intro q m' h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · rcases I.live q m' h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_append_left _ h')
    · cases h
    · cases h
    · simp at h
  case bcU =>
    intro q m'
    have := I.bcU q m'
    simp; omega
  case dlU =>
    intro q q' m'
    have := I.dlU q q' m'
    simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
    by_cases h : q = p ∧ q' = r.src ∧ m' = m
    · obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.count_eq_zero_of_not_mem]
      · simp
      intro hm
      obtain ⟨j, hj⟩ := mem_iff_getElem?'.1 hm
      rcases I.dl j q r.src m' hj with ⟨h1, -⟩ | ⟨-, z, x', r0, -, h2, h3, h4, h5⟩
      · exact hsp h1
      · have := I.initU x' x r0 r m' h3 hx h5 hb h4
        subst this
        exact hnr (List.mem_of_getElem? h2)
    · have : ¬ (GEv.mb (.dl p r.src m) : GEv P M) = .mb (.dl q q' m') := by
        simp only [GEv.mb.injEq, Ev.dl.injEq]; tauto
      simp [this]; omega

theorem Inv.recvAck (I : Inv t C) {p : P} {x : ℕ} {r : Rec P M} {m : M}
    (hx : C.log[x]? = some (.snd r)) (hdst : p ∈ r.dst)
    (hcaus : CausalReady C.log p r) (hb : r.body = .ack m) (ph' : P → Phase P M)
    (hph1 : ∀ q, q ≠ p → ph' q = C.phase q)
    (hph2 : (∃ A, C.phase p = .wait m A ∧ ph' p = .wait m (insert r.src A)) ∨
      ((∀ A, C.phase p ≠ .wait m A) ∧ ph' p = C.phase p)) :
    Inv t { C with
        log := C.log ++ [.rcv p x]
        past := Function.update C.past p (C.past p ∪ r.dep ∪ {x})
        phase := ph' } := by
  have hxl := lt_of_getElem?_eq_some hx
  have hsp : r.src ≠ p := by
    obtain ⟨z, x0, r0, -, -, -, -, h5, h6, -⟩ := I.ack x r m hx hb
    rw [h5, mem_singleton] at hdst; rw [hdst]; exact h6.symm
  refine ⟨?rcv, ?dep, ?depLt, ?past, ?pastLt, ?init, ?initU, ?ack, ?hdl, ?dl, ?phase, ?ackIn,
    ?live, ?bcU, ?dlU⟩ <;> dsimp only
  case rcv =>
    intro w q y h
    rcases getElem?_append_one h with h | ⟨rfl, he⟩
    · obtain ⟨r, hr, hyw, hq, hc⟩ := I.rcv w q y h
      refine ⟨r, getElem?_append_of_some hr, hyw, hq, fun x hx r' hr' hq' => ?_⟩
      have hxl : x < C.log.length := by
        have := I.depLt y r hr x hx; have := lt_of_getElem?_eq_some hr; omega
      obtain ⟨w', hw', h'⟩ := hc x hx r' (getElem?_old hxl hr') hq'
      exact ⟨w', hw', getElem?_append_of_some h'⟩
    · cases he
      exact ⟨r, getElem?_append_of_some hx, hxl, hdst, I.rcv_new _ hx hcaus⟩
  case dep =>
    intro y r' h
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨h1, h2⟩ := I.dep y r' h
      have hy := lt_of_getElem?_eq_some h
      exact ⟨fun x hx r' hr' => h1 x hx r' (getElem?_old (by omega) hr'),
        fun z hz x hzx => h2 z hz x (getElem?_old (by omega) hzx)⟩
    · cases he
  case depLt =>
    intro y r' h
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · exact I.depLt y r' h
    · cases he
  case past =>
    intro k
    refine ⟨fun x0 r' hr' hsrc => ?_, fun z x0 hzx => ?_⟩
    · rcases getElem?_append_one hr' with hr' | ⟨-, he⟩
      · have := (I.past k).1 x0 r' hr' hsrc
        by_cases hk : k = p
        · subst hk; simp [this]
        · simp [Function.update_of_ne hk, this]
      · cases he
    · rcases getElem?_append_one hzx with hzx | ⟨-, he⟩
      · have := (I.past k).2 z x0 hzx
        by_cases hk : k = p
        · subst hk; simp [this]
        · simp [Function.update_of_ne hk, this]
      · cases he; simp
  case pastLt =>
    intro k x0 hx0
    simp only [List.length_append, List.length_cons, List.length_nil]
    by_cases hk : k = p
    · subst hk
      simp only [Function.update_self, mem_union, mem_singleton] at hx0
      rcases hx0 with (hx0 | hx0) | rfl
      · have := I.pastLt k x0 hx0; omega
      · have := I.depLt x r hx x0 hx0; omega
      · omega
    · rw [Function.update_of_ne hk] at hx0
      have := I.pastLt k x0 hx0; omega
  case init =>
    intro x0 r' m' h hb'
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨h1, x', hx', h'⟩ := I.init x0 r' m' h hb'
      exact ⟨h1, x', hx', getElem?_append_of_some h'⟩
    · cases he
  case initU =>
    intro x0 x' r1 r2 m' h h' hb1 hb2 hsrc
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · rcases getElem?_append_one h' with h' | ⟨-, he'⟩
      · exact I.initU x0 x' r1 r2 m' h h' hb1 hb2 hsrc
      · cases he'
    · cases he
  case ack =>
    intro y r' m' h hb'
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · obtain ⟨z, x, r0, h1, h2, h3, h4, h5, h6, h7⟩ := I.ack y r' m' h hb'
      exact ⟨z, x, r0, h1, getElem?_append_of_some h2, getElem?_append_of_some h3, h4, h5, h6,
        getElem?_append_of_some h7⟩
    · cases he
  case hdl =>
    intro z q x0 r0 m' h hx0 hb0
    rcases getElem?_append_one h with h | ⟨rfl, he⟩
    · obtain ⟨r1, hr1, hxz, -⟩ := I.rcv z q x0 h
      have := lt_of_getElem?_eq_some h
      obtain ⟨r1, h1, h2, h3, h4, h5⟩ := I.hdl z q x0 r0 m' h (getElem?_old (by omega) hx0) hb0
      exact ⟨r1, getElem?_append_of_some h1, h2, h3, h4, getElem?_append_of_some h5⟩
    · cases he
      rw [getElem?_old hxl hx0] at hx; cases hx
      rw [hb] at hb0; cases hb0
  case dl =>
    intro j q q' m' h
    rcases getElem?_append_one h with h | ⟨-, he⟩
    · rcases I.dl j q q' m' h with ⟨h1, h2, A, h3, h4, h5⟩ | ⟨h1, z, x, r0, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨h1, h2.append le_rfl, A, h3, h4, fun k hk => (h5 k hk).append le_rfl⟩
      · exact Or.inr ⟨h1, z, x, r0, h2, getElem?_append_of_some h3, getElem?_append_of_some h4,
          h5, h6⟩
    · cases he
  case phase =>
    intro q m' A' h
    have hnot : GEv.mb (.dl q q m') ∉ C.log → GEv.mb (.dl q q m') ∉ C.log ++ [.rcv p x] := by
      intro h4; simp [h4]
    by_cases hq : q = p
    · subst hq
      rcases hph2 with ⟨A, hA, hA'⟩ | ⟨-, hA'⟩
      · rw [hA'] at h
        simp only [Phase.wait.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3, h4⟩ := I.phase q m A hA
        refine ⟨h1.append (by simp), ?_, fun k hk => ?_, hnot h4⟩
        · simp only [mem_insert, not_or]; exact ⟨fun h => hsp h.symm, h2⟩
        · rw [mem_insert] at hk
          rcases hk with rfl | hk
          · exact ⟨C.log.length, by simp, x, r, by simp, getElem?_append_of_some hx, rfl, hb⟩
          · exact (h3 k hk).append (by simp)
      · rw [hA'] at h
        obtain ⟨h1, h2, h3, h4⟩ := I.phase q m' A' h
        exact ⟨h1.append (by simp), h2, fun k hk => (h3 k hk).append (by simp), hnot h4⟩
    · rw [hph1 q hq] at h
      obtain ⟨h1, h2, h3, h4⟩ := I.phase q m' A' h
      exact ⟨h1.append (by simp), h2, fun k hk => (h3 k hk).append (by simp), hnot h4⟩
  case ackIn =>
    intro q m' A' h w y r' hw hy hb'
    rcases getElem?_append_one hw with hw' | ⟨rfl, he⟩
    · obtain ⟨r1, hr1, hyw, -, -⟩ := I.rcv w q y hw'
      have := lt_of_getElem?_eq_some hw'
      have hy' := getElem?_old (by omega) hy
      by_cases hq : q = p
      · subst hq
        rcases hph2 with ⟨A, hA, hA'⟩ | ⟨-, hA'⟩
        · rw [hA'] at h
          simp only [Phase.wait.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact mem_insert_of_mem (I.ackIn q m A hA w y r' hw' hy' hb')
        · rw [hA'] at h
          exact I.ackIn q m' A' h w y r' hw' hy' hb'
      · rw [hph1 q hq] at h
        exact I.ackIn q m' A' h w y r' hw' hy' hb'
    · cases he
      rw [getElem?_old hxl hy] at hx; cases hx
      rw [hb] at hb'; cases hb'
      rcases hph2 with ⟨A, hA, hA'⟩ | ⟨hA, hA'⟩
      · rw [hA'] at h
        simp only [Phase.wait.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact mem_insert_self _ _
      · rw [hA'] at h; exact absurd h (hA A')
  case live =>
    intro q m' h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · rcases I.live q m' h with ⟨A', hA'⟩ | h'
      · by_cases hq : q = p
        · subst hq
          rcases hph2 with ⟨A, hA, hA''⟩ | ⟨-, hA''⟩
          · rw [hA] at hA'
            simp only [Phase.wait.injEq] at hA'
            obtain ⟨rfl, -⟩ := hA'
            exact Or.inl ⟨_, hA''⟩
          · exact Or.inl ⟨A', hA''.trans hA'⟩
        · exact Or.inl ⟨A', (hph1 q hq).trans hA'⟩
      · exact Or.inr (List.mem_append_left _ h')
    · cases h
  case bcU =>
    intro q m'
    have := I.bcU q m'
    simp; omega
  case dlU =>
    intro q q' m'
    have := I.dlU q q' m'
    simp; omega

/-- Preservation of the invariants by a reception. -/
theorem Inv.deliver (I : Inv t C) {p : P} {x : ℕ} {r : Rec P M}
    (hx : C.log[x]? = some (.snd r)) (hdst : p ∈ r.dst) (hnr : GEv.rcv p x ∉ C.log)
    (hcaus : CausalReady C.log p r) : Inv t (deliver C p x r) := by
  unfold Causal.deliver
  cases hb : r.body with
  | init m =>
    have hsp : r.src ≠ p := by
      obtain ⟨h1, -⟩ := I.init x r m hx hb
      rw [h1, mem_erase] at hdst; exact hdst.1.symm
    simp only [ne_eq, hsp, not_false_eq_true, ite_true]
    exact I.recvInit hx hdst hnr hcaus hb hsp
  | ack m =>
    dsimp only
    split
    · rename_i m' A hA
      split_ifs with hm
      · subst hm
        exact I.recvAck hx hdst hcaus hb _ (fun q hq => Function.update_of_ne hq _ _)
          (Or.inl ⟨A, hA, by simp⟩)
      · exact I.recvAck hx hdst hcaus hb _ (fun q hq => rfl)
          (Or.inr ⟨fun A' h => (by rw [hA] at h; cases h; exact hm rfl), rfl⟩)
    · rename_i hA
      exact I.recvAck hx hdst hcaus hb _ (fun q hq => rfl)
        (Or.inr ⟨fun A' h => (by rw [hA] at h; cases h), rfl⟩)

/-- **Invariants of reachable configurations.** -/
theorem Reachable.inv {C : Cfg P M} (h : Reachable t C) : Inv t C := by
  induction h with
  | init => exact inv_init t
  | step a _ hs ih =>
    cases a with
    | invoke p m =>
      obtain ⟨-, hid, hbc, rfl⟩ := step_invoke hs
      exact ih.invoke hid hbc
    | recv p x =>
      obtain ⟨r, hx, -, hdst, hnr, hcaus, rfl⟩ := step_recv hs
      exact ih.deliver hx hdst hnr hcaus
    | own p =>
      obtain ⟨m, A, hph, -, hA, rfl⟩ := step_own hs
      exact ih.own hph hA
    | crash p =>
      rw [step_crash hs]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := ih
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩
    | skip => rw [step_skip hs]; exact ih

end Recv

end Podc.MBroadcast.Causal
