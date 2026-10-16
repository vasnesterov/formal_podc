import Papers.PODC2020.UnknownParticipantsBA.GoodRound

/-!
# Invariants of the candidate-set layer (Lemmas 1–3 of the BA)

For any extension `Ex` (rotor-coordinator or consensus), as long as the correct nodes are running:

* `G ⊆ heard ⊆ G ∪ F` (every correct node broadcasts `init` in round 1);
* only existing nodes are echoed or become candidates (`E_real`, `C_real`) — Byzantine nodes
  cannot introduce invented identifiers;
* all correct identifiers are candidates from the first loop iteration on (`G_sub_C`);
* **relay** (Lemma 3 of the BA, Lemma 6 of the full version): if a correct node has `p` as a
  candidate after step `s`, every correct node has it after step `s + 1` (`relay`).

Combined with `exists_good_round`: a good iteration occurs among the first `f + 1` selections
(`layer_good`).

-- CSLib candidate (with `Rotor.lean`'s layer and `GoodRound.lean`).
-/

namespace UnknownBA

variable {I X A T : Type*} [DecidableEq I] [DecidableEq A]
variable (Ex : Ext I X A T) (E : Env I X (Msg I A))

local notation "R" => run (withRotor Ex) E

/-- Node `v` has not halted after step `s`. -/
def Alive (s : ℕ) (v : I) : Prop := Ex.halted (R s v).ext = false

/-- Number of correct senders of `m` at the end of step `s`. -/
def corr (s : ℕ) (m : Msg I A) : ℕ :=
  (E.G.filter fun q => m ∈ (withRotor Ex).out (R s q)).card

lemma withRotor_out_of_halted {st : St I T} (h : Ex.halted st.ext = true) :
    (withRotor (X := X) Ex).out st = ∅ := by
  simp [withRotor, h]

lemma mem_withRotor_out_echo {st : St I T} {p : I} :
    Msg.echo p ∈ (withRotor (X := X) Ex).out st ↔ Ex.halted st.ext = false ∧ p ∈ st.core.E := by
  by_cases h : Ex.halted st.ext <;> by_cases h' : st.t = 0 <;> simp [withRotor, h, h']

lemma mem_withRotor_out_app {st : St I T} {a : A} :
    Msg.app a ∈ (withRotor (X := X) Ex).out st ↔ Ex.halted st.ext = false ∧ a ∈ Ex.out st.ext := by
  by_cases h : Ex.halted st.ext <;> by_cases h' : st.t = 0 <;> simp [withRotor, h, h']

lemma mem_withRotor_out_init {st : St I T} :
    Msg.init ∈ (withRotor (X := X) Ex).out st ↔ Ex.halted st.ext = false ∧ st.t = 0 := by
  by_cases h : Ex.halted st.ext <;> by_cases h' : st.t = 0 <;> simp [withRotor, h, h']

lemma withRotor_step_of_not_halted {st : St I T} (h : Ex.halted st.ext = false)
    (B : Finset (I × Msg I A)) :
    (withRotor (X := X) Ex).step st B =
      ⟨st.t + 1, if st.t = 0 then st.core.recvInit B else st.core.update B,
        Ex.step st.t (if st.t = 0 then st.core.recvInit B else st.core.update B) st.ext B⟩ := by
  simp [withRotor, h]

variable {Ex E}

lemma alive_of_succ {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) : Alive Ex E s v := by
  unfold Alive at *
  by_contra hs
  simp only [Bool.not_eq_false] at hs
  rw [run_succ, withRotor_step_of_halted _ hs] at h
  rw [h] at hs; exact absurd hs (by simp)

lemma alive_of_le {s s' : ℕ} {v : I} (h : Alive Ex E s' v) (hs : s ≤ s') : Alive Ex E s v := by
  induction hs with
  | refl => exact h
  | step _ ih => exact ih (alive_of_succ h)

lemma run_succ_of_alive {s : ℕ} {v : I} (h : Alive Ex E s v) :
    R (s + 1) v =
      ⟨(R s v).t + 1,
        if (R s v).t = 0 then (R s v).core.recvInit (inbox (withRotor Ex) E (R s) s v)
        else (R s v).core.update (inbox (withRotor Ex) E (R s) s v),
        Ex.step (R s v).t
          (if (R s v).t = 0 then (R s v).core.recvInit (inbox (withRotor Ex) E (R s) s v)
            else (R s v).core.update (inbox (withRotor Ex) E (R s) s v))
          (R s v).ext (inbox (withRotor Ex) E (R s) s v)⟩ := by
  rw [run_succ, withRotor_step_of_not_halted _ h]

lemma t_eq {s : ℕ} {v : I} (h : Alive Ex E s v) : (R s v).t = s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h' := alive_of_succ h
    rw [run_succ_of_alive h', ih h']

lemma core_succ {s : ℕ} {v : I} (h : Alive Ex E s v) :
    (R (s + 1) v).core =
      if s = 0 then (R s v).core.recvInit (inbox (withRotor Ex) E (R s) s v)
      else (R s v).core.update (inbox (withRotor Ex) E (R s) s v) := by
  rw [run_succ_of_alive h, t_eq h]

lemma ext_succ {s : ℕ} {v : I} (h : Alive Ex E s v) :
    (R (s + 1) v).ext = Ex.step s (R (s + 1) v).core (R s v).ext
      (inbox (withRotor Ex) E (R s) s v) := by
  rw [core_succ h, run_succ_of_alive h, t_eq h]

lemma mem_out_echo {s : ℕ} {q p : I} :
    Msg.echo p ∈ (withRotor Ex).out (R s q) ↔ Alive Ex E s q ∧ p ∈ (R s q).core.E :=
  mem_withRotor_out_echo Ex

lemma mem_out_init {s : ℕ} {q : I} :
    Msg.init ∈ (withRotor Ex).out (R s q) ↔ Alive Ex E s q ∧ s = 0 := by
  rw [mem_withRotor_out_init]
  constructor
  · rintro ⟨ha, ht⟩; exact ⟨ha, (t_eq ha).symm.trans ht⟩
  · rintro ⟨ha, rfl⟩; exact ⟨ha, t_eq ha⟩

lemma mem_out_app {s : ℕ} {q : I} {a : A} :
    Msg.app a ∈ (withRotor Ex).out (R s q) ↔ Alive Ex E s q ∧ a ∈ Ex.out (R s q).ext :=
  mem_withRotor_out_app Ex

lemma heard_succ {s : ℕ} {v : I} (h : Alive Ex E s v) :
    (R (s + 1) v).core.heard =
      (R s v).core.heard ∪ senders (inbox (withRotor Ex) E (R s) s v) := by
  rw [core_succ h]; split_ifs <;> rfl

variable (hinit : ∀ v x, Ex.halted (Ex.init v x) = false)
include hinit

omit hinit in
lemma alive_zero_of (hinit : ∀ v x, Ex.halted (Ex.init v x) = false) (v : I) :
    Alive Ex E 0 v := hinit _ _

lemma alive_zero (v : I) : Alive Ex E 0 v := hinit _ _

lemma G_sub_heard {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) :
    E.G ⊆ (R (s + 1) v).core.heard := by
  induction s with
  | zero =>
    rw [heard_succ (alive_of_succ h)]
    intro q hq
    refine Finset.mem_union_right _ (mem_senders_inbox_of_correct _ _ _ _ _ hq (m := Msg.init) ?_)
    exact mem_out_init.mpr ⟨alive_zero hinit q, rfl⟩
  | succ s ih =>
    rw [heard_succ (alive_of_succ h)]
    exact (ih (alive_of_succ h)).trans Finset.subset_union_left

lemma G_sub_heard_succ {s : ℕ} {v : I} (h : Alive Ex E s v) :
    E.G ⊆ (R (s + 1) v).core.heard := by
  rcases s with _ | s
  · rw [heard_succ h]
    intro q hq
    refine Finset.mem_union_right _ (mem_senders_inbox_of_correct _ _ _ _ _ hq (m := Msg.init) ?_)
    exact mem_out_init.mpr ⟨alive_zero hinit q, rfl⟩
  · rw [heard_succ h]; exact (G_sub_heard hinit h).trans Finset.subset_union_left

omit hinit in
lemma heard_sub {s : ℕ} {v : I} (h : Alive Ex E s v) : (R s v).core.heard ⊆ E.G ∪ E.F := by
  induction s with
  | zero => simp [withRotor]
  | succ s ih =>
    rw [heard_succ (alive_of_succ h)]
    exact Finset.union_subset (ih (alive_of_succ h)) (senders_inbox_subset _ _ _ _ _)

omit hinit in
lemma heard_sub_succ {s : ℕ} {v : I} (h : Alive Ex E s v) :
    (R (s + 1) v).core.heard ⊆ E.G ∪ E.F := by
  rw [heard_succ h]
  exact Finset.union_subset (heard_sub h) (senders_inbox_subset _ _ _ _ _)

/-- Counting at a correct receiver: `n_v = g + h` with `h ≤ |F|` faulty nodes heard of, and the
number of copies of `m` is between `corr` and `corr + h`. -/
lemma count_bound {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) (m : Msg I A) :
    ∃ k ≤ E.F.card, (R (s + 1) v).core.heard.card = E.G.card + k ∧
      corr Ex E s m ≤ cnt (inbox (withRotor Ex) E (R s) s v) m ∧
      cnt (inbox (withRotor Ex) E (R s) s v) m ≤ corr Ex E s m + k := by
  set H := (R (s + 1) v).core.heard
  have hG := G_sub_heard hinit h
  have hH := heard_sub h
  refine ⟨(H ∩ E.F).card, Finset.card_le_card Finset.inter_subset_right, ?_, ?_, ?_⟩
  · have : H = E.G ∪ (H ∩ E.F) := by
      ext x; constructor
      · intro hx
        rcases Finset.mem_union.mp (hH hx) with h1 | h1
        · exact Finset.mem_union_left _ h1
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, h1⟩)
      · intro hx
        rcases Finset.mem_union.mp hx with h1 | h1
        · exact hG h1
        · exact (Finset.mem_inter.mp h1).1
    conv_lhs => rw [this]
    rw [Finset.card_union_of_disjoint]
    exact Finset.disjoint_of_subset_right Finset.inter_subset_right E.disj
  · rw [cnt_inbox, corr]; omega
  · rw [cnt_inbox, corr]
    have : (E.F.filter fun q => m ∈ E.adv s q v) ⊆ H ∩ E.F := by
      intro q hq
      simp only [Finset.mem_filter] at hq
      refine Finset.mem_inter.mpr ⟨?_, hq.1⟩
      change q ∈ (R (s + 1) v).core.heard
      rw [heard_succ (alive_of_succ h)]
      refine Finset.mem_union_right _ ?_
      simp only [senders, inbox, Finset.mem_image]
      exact ⟨(q, m), Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨q, hq.1, by simp [hq.2]⟩), rfl⟩
    have := Finset.card_le_card this
    omega

omit hinit in
/-- A positive `corr` yields a correct sender. -/
lemma exists_of_corr_pos {s : ℕ} {m : Msg I A} (h : 0 < corr Ex E s m) :
    ∃ q ∈ E.G, m ∈ (withRotor Ex).out (R s q) := by
  rw [corr, Finset.card_pos] at h
  obtain ⟨q, hq⟩ := h
  simp only [Finset.mem_filter] at hq
  exact ⟨q, hq⟩

variable (hres : 2 * E.F.card < E.G.card)
include hres

/-- Lemma 1 (BA): `n_v/3` copies contain one from a correct node. -/
lemma lemma1 {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) {m : Msg I A}
    (hc : (R (s + 1) v).core.heard.card ≤ 3 * cnt (inbox (withRotor Ex) E (R s) s v) m) :
    ∃ q ∈ E.G, m ∈ (withRotor Ex).out (R s q) := by
  obtain ⟨k, hk, h1, h2, h3⟩ := count_bound hinit h m
  exact exists_of_corr_pos (by omega)

/-- Lemma 2 (BA): `2n_v/3` copies at a correct node give more than `(g + f)/3` correct senders. -/
lemma lemma2 {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) {m : Msg I A}
    (hc : 2 * (R (s + 1) v).core.heard.card ≤ 3 * cnt (inbox (withRotor Ex) E (R s) s v) m) :
    E.G.card + E.F.card < 3 * corr Ex E s m := by
  obtain ⟨k, hk, h1, h2, h3⟩ := count_bound hinit h m
  exact lemma2_arith (b := cnt (inbox (withRotor Ex) E (R s) s v) m - corr Ex E s m) (h := k)
    (by omega) hk hres (by omega)

/-- Lemma 9 (full version): two `2n/3` quorums in the same step share a correct sender. -/
lemma lemma9 {s : ℕ} {v u : I} (hv : Alive Ex E (s + 1) v) (hu : Alive Ex E (s + 1) u)
    {m m' : Msg I A}
    (hc : 2 * (R (s + 1) v).core.heard.card ≤ 3 * cnt (inbox (withRotor Ex) E (R s) s v) m)
    (hc' : 2 * (R (s + 1) u).core.heard.card ≤ 3 * cnt (inbox (withRotor Ex) E (R s) s u) m') :
    ∃ q ∈ E.G, m ∈ (withRotor Ex).out (R s q) ∧ m' ∈ (withRotor Ex).out (R s q) := by
  obtain ⟨k, hk, h1, h2, h3⟩ := count_bound hinit hv m
  obtain ⟨k', hk', h1', h2', h3'⟩ := count_bound hinit hu m'
  have hlt : E.G.card < corr Ex E s m + corr Ex E s m' :=
    lemma9_arith (b := cnt (inbox (withRotor Ex) E (R s) s v) m - corr Ex E s m) (h := k)
      (b' := cnt (inbox (withRotor Ex) E (R s) s u) m' - corr Ex E s m') (h' := k')
      (by omega) (by omega) hk hk' hres (by omega) (by omega)
  rw [corr, corr, ← Finset.card_union_add_card_inter] at hlt
  have : (E.G.filter fun q => m ∈ (withRotor Ex).out (R s q)) ∪
      (E.G.filter fun q => m' ∈ (withRotor Ex).out (R s q)) ⊆ E.G :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have := Finset.card_le_card this
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < ((E.G.filter fun q => m ∈ (withRotor Ex).out (R s q)) ∩
      (E.G.filter fun q => m' ∈ (withRotor Ex).out (R s q))).card by omega)
  simp only [Finset.mem_inter, Finset.mem_filter] at hq
  exact ⟨q, hq.1.1, hq.1.2, hq.2.2⟩

/-! ### One step of the layer -/

omit hinit hres in
lemma C_succ {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) (hs : s ≠ 0) {p : I} :
    p ∈ (R (s + 1) v).core.C ↔ p ∈ (R s v).core.C ∨
      (p ∈ echoIds (inbox (withRotor Ex) E (R s) s v) ∧
        2 * (R (s + 1) v).core.heard.card ≤
          3 * cnt (inbox (withRotor Ex) E (R s) s v) (Msg.echo p)) := by
  rw [core_succ (alive_of_succ h)]
  simp [hs, Core.update]

omit hinit hres in
lemma E_succ {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) (hs : s ≠ 0) {p : I} :
    p ∈ (R (s + 1) v).core.E ↔
      p ∈ echoIds (inbox (withRotor Ex) E (R s) s v) ∧ p ∉ (R s v).core.C ∧
        (R (s + 1) v).core.heard.card ≤
          3 * cnt (inbox (withRotor Ex) E (R s) s v) (Msg.echo p) := by
  rw [core_succ (alive_of_succ h)]
  simp [hs, Core.update]

omit hinit hres in
lemma core_one {v : I} (h : Alive Ex E 1 v) :
    (R 1 v).core.C = ∅ ∧
      (R 1 v).core.E = senders ((inbox (withRotor Ex) E (R 0) 0 v).filter fun e => e.2 = Msg.init) := by
  rw [core_succ (alive_of_succ h)]
  exact ⟨rfl, rfl⟩

omit hinit hres in
lemma core_zero (v : I) : (R 0 v).core.C = ∅ ∧ (R 0 v).core.E = ∅ := ⟨rfl, rfl⟩

omit hinit hres in
lemma C_mono_succ {s : ℕ} {v : I} (h : Alive Ex E (s + 1) v) :
    (R s v).core.C ⊆ (R (s + 1) v).core.C := by
  rw [core_succ (alive_of_succ h)]
  split_ifs
  · exact le_rfl
  · exact Finset.subset_union_left

omit hinit hres in
lemma C_mono {s s' : ℕ} {v : I} (h : Alive Ex E s' v) (hle : s ≤ s') :
    (R s v).core.C ⊆ (R s' v).core.C := by
  induction hle with
  | refl => exact le_rfl
  | step hle ih => exact (ih (alive_of_succ h)).trans (C_mono_succ h)

omit hinit hres in
lemma corr_eq_card {s : ℕ} {m : Msg I A} (h : ∀ q ∈ E.G, m ∈ (withRotor Ex).out (R s q)) :
    corr Ex E s m = E.G.card := by
  rw [corr, Finset.filter_true_of_mem h]

/-! ### Invariants -/

/-- Only existing nodes are echoed by correct nodes. -/
lemma E_real {s : ℕ} {v : I} (hv : v ∈ E.G) (h : Alive Ex E s v) :
    (R s v).core.E ⊆ E.G ∪ E.F := by
  induction s generalizing v with
  | zero => intro p hp; rw [(core_zero v).2] at hp; simp at hp
  | succ s ih =>
    intro p hp
    by_cases hs : s = 0
    · subst hs
      rw [(core_one h).2] at hp
      exact senders_inbox_subset _ _ _ _ _
        (Finset.image_subset_image (Finset.filter_subset _ _) hp)
    · obtain ⟨-, -, hc⟩ := (E_succ h hs).mp hp
      obtain ⟨q, hq, hm⟩ := lemma1 hinit hres h hc
      obtain ⟨hqa, hqE⟩ := mem_out_echo.mp hm
      exact ih hq hqa hqE

/-- Only existing nodes become candidates. -/
lemma C_real {s : ℕ} {v : I} (hv : v ∈ E.G) (h : Alive Ex E s v) :
    (R s v).core.C ⊆ E.G ∪ E.F := by
  induction s generalizing v with
  | zero => intro p hp; rw [(core_zero v).1] at hp; simp at hp
  | succ s ih =>
    intro p hp
    by_cases hs : s = 0
    · subst hs; rw [(core_one h).1] at hp; simp at hp
    · rcases (C_succ h hs).mp hp with hp | ⟨-, hc⟩
      · exact ih hv (alive_of_succ h) hp
      · obtain ⟨q, hq, hm⟩ := lemma1 hinit hres h (m := Msg.echo p) (by omega)
        obtain ⟨hqa, hqE⟩ := mem_out_echo.mp hm
        exact E_real hinit hres hq hqa hqE

/-- **Unforgeability** (Lemma 3 of the full version, for the candidate layer): if a correct node
echoes `p`, then `p` itself sent `init` to some correct node in round 1. -/
lemma E_origin {s : ℕ} {v : I} (hv : v ∈ E.G) (h : Alive Ex E s v) {p : I}
    (hp : p ∈ (R s v).core.E) :
    ∃ q ∈ E.G, (p, Msg.init) ∈ inbox (withRotor Ex) E (R 0) 0 q := by
  induction s generalizing v with
  | zero => rw [(core_zero v).2] at hp; simp at hp
  | succ s ih =>
    by_cases hs : s = 0
    · subst hs
      rw [(core_one h).2] at hp
      simp only [senders, Finset.mem_image, Finset.mem_filter] at hp
      obtain ⟨⟨q, m⟩, ⟨hm, rfl⟩, rfl⟩ := hp
      exact ⟨v, hv, hm⟩
    · obtain ⟨-, -, hc⟩ := (E_succ h hs).mp hp
      obtain ⟨q, hq, hm⟩ := lemma1 hinit hres h hc
      obtain ⟨hqa, hqE⟩ := mem_out_echo.mp hm
      exact ih hq hqa hqE

/-- Unforgeability for candidates: a candidate `p` of a correct node sent `init` to some correct
node in round 1. -/
lemma C_origin {s : ℕ} {v : I} (hv : v ∈ E.G) (h : Alive Ex E s v) {p : I}
    (hp : p ∈ (R s v).core.C) :
    ∃ q ∈ E.G, (p, Msg.init) ∈ inbox (withRotor Ex) E (R 0) 0 q := by
  induction s generalizing v with
  | zero => rw [(core_zero v).1] at hp; simp at hp
  | succ s ih =>
    by_cases hs : s = 0
    · subst hs; rw [(core_one h).1] at hp; simp at hp
    · rcases (C_succ h hs).mp hp with hp | ⟨-, hc⟩
      · exact ih hv (alive_of_succ h) hp
      · obtain ⟨q, hq, hm⟩ := lemma1 hinit hres h (m := Msg.echo p) (by omega)
        obtain ⟨hqa, hqE⟩ := mem_out_echo.mp hm
        exact E_origin hinit hres hq hqa hqE

/-- All correct identifiers are candidates from the first loop iteration (step 2) on. -/
lemma G_sub_C (hall1 : ∀ q ∈ E.G, Alive Ex E 1 q) {s : ℕ} {v : I} (h : Alive Ex E s v)
    (hs : 2 ≤ s) : E.G ⊆ (R s v).core.C := by
  have h2 : E.G ⊆ (R 2 v).core.C := by
    intro p hp
    have ha2 : Alive Ex E (1 + 1) v := alive_of_le h hs
    refine (C_succ ha2 one_ne_zero).mpr (Or.inr ?_)
    have hcorr : corr Ex E 1 (Msg.echo p) = E.G.card := by
      refine corr_eq_card fun q hq => mem_out_echo.mpr ⟨hall1 q hq, ?_⟩
      rw [(core_one (hall1 q hq)).2]
      simp only [senders, Finset.mem_image, Finset.mem_filter]
      exact ⟨(p, Msg.init), ⟨(mem_inbox_correct _ _ _ _ _ hp _).mpr
        (mem_out_init.mpr ⟨alive_zero hinit p, rfl⟩), rfl⟩, rfl⟩
    obtain ⟨k, hk, h1, h2, -⟩ := count_bound hinit ha2 (Msg.echo p)
    refine ⟨echoIds_of_cnt_pos ?_, ?_⟩
    · have : 0 < E.G.card := by omega
      omega
    · omega
  exact h2.trans (C_mono h hs)

/-- **Relay** (Lemma 3 of the BA / Lemma 6 of the full version): while all correct nodes are
running, a candidate of one correct node is a candidate of every correct node one step later. -/
lemma relay {T : ℕ} (hall : ∀ q ∈ E.G, Alive Ex E T q) {s : ℕ} (hsT : s + 1 ≤ T) {v : I}
    (hv : v ∈ E.G) {p : I} (hp : p ∈ (R s v).core.C) {u : I} (hu : u ∈ E.G) :
    p ∈ (R (s + 1) u).core.C := by
  classical
  have hP : ∃ s', ∃ w ∈ E.G, p ∈ (R s' w).core.C := ⟨s, v, hv, hp⟩
  obtain ⟨w, hw, hpw⟩ := Nat.find_spec hP
  have hle : Nat.find hP ≤ s := Nat.find_min' hP ⟨v, hv, hp⟩
  have hmin : ∀ s' < Nat.find hP, ∀ w ∈ E.G, p ∉ (R s' w).core.C := fun s' hs' w hw hpw =>
    Nat.find_min hP hs' ⟨w, hw, hpw⟩
  obtain ⟨s1, hs1⟩ : ∃ s1, Nat.find hP = s1 + 1 := by
    rcases Nat.exists_eq_succ_of_ne_zero (n := Nat.find hP) (fun h0 => by
      rw [h0, (core_zero w).1] at hpw; simp at hpw) with ⟨s1, h⟩
    exact ⟨s1, h⟩
  rw [hs1] at hpw hle hmin
  have alive : ∀ q ∈ E.G, ∀ s' ≤ s + 1, Alive Ex E s' q := fun q hq s' hs' =>
    alive_of_le (hall q hq) (by omega)
  have hs1ne : s1 ≠ 0 := by
    rintro rfl; rw [(core_one (alive w hw 1 (by omega))).1] at hpw; simp at hpw
  -- `w` added `p` in step `s1 + 1`
  have hadd : 2 * (R (s1 + 1) w).core.heard.card ≤
      3 * cnt (inbox (withRotor Ex) E (R s1) s1 w) (Msg.echo p) := by
    rcases (C_succ (alive w hw _ (by omega)) hs1ne).mp hpw with h | ⟨-, h⟩
    · exact absurd h (hmin s1 (by omega) w hw)
    · exact h
  have hbig := lemma2 hinit hres (alive w hw _ (by omega)) hadd
  -- hence every correct node echoes `p` at the end of step `s1 + 1`
  have hecho : ∀ q ∈ E.G, Msg.echo p ∈ (withRotor Ex).out (R (s1 + 1) q) := by
    intro q hq
    have hqa := alive q hq (s1 + 1) (by omega)
    refine mem_out_echo.mpr ⟨hqa, (E_succ hqa hs1ne).mpr ⟨?_, hmin s1 (by omega) q hq, ?_⟩⟩
    · obtain ⟨k, hk, h1, h2, -⟩ := count_bound hinit hqa (Msg.echo p)
      exact echoIds_of_cnt_pos (by omega)
    · obtain ⟨k, hk, h1, h2, -⟩ := count_bound hinit hqa (Msg.echo p)
      omega
  -- and everybody adds `p` in step `s1 + 2`
  have hua := alive u hu (s1 + 1 + 1) (by omega)
  have hpu : p ∈ (R (s1 + 1 + 1) u).core.C := by
    refine (C_succ hua (by omega)).mpr (Or.inr ?_)
    have hcorr := corr_eq_card hecho
    obtain ⟨k, hk, h1, h2, -⟩ := count_bound hinit hua (Msg.echo p)
    refine ⟨echoIds_of_cnt_pos (by omega), by omega⟩
  exact C_mono (alive u hu _ le_rfl) (by omega) hpu

/-- **A good round among the first `|F| + 1` selections.** If the correct nodes select at steps
`σ 0 < σ 1 < …` (with `σ 0 ≥ 2`), choosing `C[r mod |C|]` at the `r`-th selection, and they are
still running at step `σ |F|`, then for some `r ≤ |F|` all correct nodes select the same correct
node. -/
theorem layer_good [LinearOrder I] (σ : ℕ → ℕ) (hσ0 : 2 ≤ σ 0) (hσ : ∀ r, σ r < σ (r + 1))
    (hall : ∀ q ∈ E.G, Alive Ex E (σ E.F.card) q) :
    ∃ r ≤ E.F.card, ∃ p ∈ E.G, ∀ v ∈ E.G, selSet (R (σ r) v).core.C r = {p} := by
  have hmono : StrictMono σ := strictMono_nat_of_lt_succ hσ
  have hall1 : ∀ q ∈ E.G, Alive Ex E 1 q := fun q hq =>
    alive_of_le (hall q hq) (by have := hmono.monotone (Nat.zero_le E.F.card); omega)
  refine exists_good_round E.G E.F (by omega) (fun v r => (R (σ r) v).core.C) ?_ ?_ ?_
  · intro v hv r hr
    exact G_sub_C hinit hres hall1 (alive_of_le (hall v hv) (hmono.monotone hr))
      (hσ0.trans (hmono.monotone (Nat.zero_le r)))
  · intro v hv r hr
    exact C_real hinit hres hv (alive_of_le (hall v hv) (hmono.monotone hr))
  · intro v hv u hu r hr p hp
    have h1 : σ r + 1 ≤ σ E.F.card := (hσ r).trans_le (hmono.monotone hr)
    exact C_mono (alive_of_le (hall u hu) (hmono.monotone (Nat.succ_le_of_lt hr))) (hσ r)
      (relay hinit hres hall h1 hv hp hu)

end UnknownBA
