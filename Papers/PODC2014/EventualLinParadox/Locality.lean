import Papers.PODC2014.EventualLinParadox.Basic

/-!
# Locality (Section 3.2: Lemmas 7, 8, Proposition 9)

Guerraoui, Ruppert. *A Paradox of Eventual Linearizability in Shared Memory.* PODC 2014.

* `weaklyConsistent_iff_restrict` — **Lemma 8**: `H` is weakly consistent iff every `H|x` is.
  The paper's "if" proof inserts the process's earlier operations on other objects "with
  responses as dictated by the objects' sequential specifications", which needs total
  operations. We avoid totality: for every other object `y` we take the weak-consistency witness
  (in `H|y`) of the process's *last* operation on `y` before `op`; it contains all earlier
  operations of the process on `y`. These finitely many witnesses (on pairwise distinct objects)
  are concatenated, followed by the witness of `op` in `H|x`.
* `TLinearizable.restrict`, `exists_tLinearizable_of_restrict` — **Lemma 7** (from Serafini et
  al.), for finitely many objects and for finite or infinite histories. The "if" direction needs
  well-formedness (a response without invocation can never be linearized but is invisible in
  every `H|x`). The merge of the per-object linearizations orders an entry `e` of `S_x` by
  `key(e)`, the largest "late" operation (invoked at a position `≥ t`) at or before `e` in `S_x`.
* `eventuallyLinearizable_iff_restrict` — **Proposition 9** (finitely many objects).
* `prop9_false_infinite_objects` — the paper's counterexample with infinitely many registers.
-/

namespace Podc.EventualLinParadox

variable {P X Op Res Q : Type}

section Restrict

variable {H : History P X Op Res} {x : X}

lemma restrict_eq_some {i : ℕ} {e : Ev P X Op Res} (h : restrict H x i = some e) :
    H i = some e := by
  unfold restrict at h
  split at h <;> (try split_ifs at h) <;> simp_all

lemma restrict_inv_iff {i : ℕ} {p : P} {y : X} {op : Op} :
    restrict H x i = some (.inv p y op) ↔ H i = some (.inv p y op) ∧ y = x := by
  unfold restrict
  split <;> (try split_ifs) <;> simp_all
  intros; subst_vars; simp_all

lemma restrict_res_iff {i a : ℕ} {r : Res} :
    restrict H x i = some (.res a r) ↔ H i = some (.res a r) ∧ OnObj H x a := by
  unfold restrict
  split <;> (try split_ifs) <;> simp_all <;> (intros; subst_vars; simp_all)

lemma restrict_of_onObj {b : ℕ} (h : OnObj H x b) : restrict H x b = H b := by
  obtain ⟨p, op, hb⟩ := h
  rw [hb]; exact restrict_inv_iff.2 ⟨hb, rfl⟩

lemma onObj_restrict {y : X} {b : ℕ} : OnObj (restrict H x) y b ↔ OnObj H y b ∧ y = x := by
  simp only [OnObj, restrict_inv_iff]
  constructor
  · rintro ⟨p, op, h1, h2⟩; exact ⟨⟨p, op, h1⟩, h2⟩
  · rintro ⟨⟨p, op, h1⟩, h2⟩; exact ⟨p, op, h1, h2⟩

lemma invoked_restrict {b : ℕ} : Invoked (restrict H x) b ↔ OnObj H x b := by
  constructor
  · rintro ⟨p, y, op, h⟩
    obtain ⟨h1, rfl⟩ := restrict_inv_iff.1 h
    exact ⟨p, op, h1⟩
  · rintro ⟨p, op, h⟩; exact ⟨p, x, op, restrict_inv_iff.2 ⟨h, rfl⟩⟩

lemma sameProc_of_restrict {a b : ℕ} (h : SameProc (restrict H x) b a) : SameProc H b a := by
  obtain ⟨p, y, y', op, op', h1, h2⟩ := h
  exact ⟨p, y, y', op, op', restrict_eq_some h1, restrict_eq_some h2⟩

lemma precedes_of_restrict {a b : ℕ} (h : Precedes (restrict H x) b a) : Precedes H b a := by
  obtain ⟨j, r, h1, h2, h3⟩ := h
  obtain ⟨p, y, op, h3⟩ := h3
  exact ⟨j, r, restrict_eq_some h1, h2, p, y, op, restrict_eq_some h3⟩

lemma WellFormed.restrict (hH : WellFormed H) (x : X) : WellFormed (restrict H x) where
  res_inv a j r hj := by
    obtain ⟨hj, hx⟩ := restrict_res_iff.1 hj
    exact ⟨(hH.res_inv a j r hj).1, invoked_restrict.2 hx⟩
  res_unique a j j' r r' hj hj' :=
    hH.res_unique a j j' r r' (restrict_eq_some hj) (restrict_eq_some hj')
  seq a b p y y' op op' ha hb hab := by
    obtain ⟨ha', rfl⟩ := restrict_inv_iff.1 ha
    obtain ⟨j, r, hj, hjr⟩ := hH.seq a b p y y' op op' ha' (restrict_eq_some hb) hab
    exact ⟨j, r, hj, restrict_res_iff.2 ⟨hjr, p, op, ha'⟩⟩

end Restrict

section SeqTools

variable {H : History P X Op Res}

/-- The entry `e` of a sequential history does not touch object `z`. -/
def Idle (H : History P X Op Res) (z : X) (e : Option (ℕ × Res)) : Prop :=
  ∀ b r, e = some (b, r) → ¬ OnObj H z b

lemma idle_none {z : X} : Idle H z none := fun _ _ h => by cases h

lemma SeqStep.of_idle {T : ObjType Q Op Res} {z : X} {e : Option (ℕ × Res)} (h : Idle H z e)
    (q : Q) : SeqStep T H z e q q := by
  match e, h with
  | none, _ => rfl
  | some (b, r), h => exact Or.inr ⟨h b r rfl, rfl⟩

lemma SeqStep.eq_of_idle {T : ObjType Q Op Res} {z : X} {e : Option (ℕ × Res)} {q q' : Q}
    (h : Idle H z e) (hs : SeqStep T H z e q q') : q' = q := by
  match e, h, hs with
  | none, _, hs => exact hs
  | some (b, r), h, hs => exact hs.not_onObj (h b r rfl)

/-- The state-trajectory part of legality, for one object `z`. -/
def LegalAt (T : ObjType Q Op Res) (H : History P X Op Res) (z : X) (S : SeqHist Res) : Prop :=
  ∃ q : ℕ → Q, q 0 ∈ T.init ∧ ∀ k, SeqStep T H z (S k) (q k) (q (k + 1))

lemma Legal.legalAt {spec : X → ObjType Q Op Res} {S : SeqHist Res} (h : Legal spec H S)
    (z : X) : LegalAt (spec z) H z S := h.2 z

lemma LegalAt.const {T : ObjType Q Op Res} {z : X} {S : SeqHist Res} {q₀ : Q} (hq : q₀ ∈ T.init)
    (h : ∀ k, Idle H z (S k)) : LegalAt T H z S :=
  ⟨fun _ => q₀, hq, fun k => SeqStep.of_idle (h k) q₀⟩

/-- Legality for one object is preserved by a strictly monotone reindexing, as long as the
entries that are changed or added do not touch the object. -/
lemma LegalAt.reindex {T : ObjType Q Op Res} {z : X} {S S' : SeqHist Res} {g : ℕ → ℕ}
    (hg : StrictMono g) (h : LegalAt T H z S)
    (hgk : ∀ k, S' (g k) = S k ∨ (Idle H z (S k) ∧ Idle H z (S' (g k))))
    (hout : ∀ n, (∀ k, g k ≠ n) → Idle H z (S' n)) : LegalAt T H z S' := by
  classical
  obtain ⟨q, hq0, hq⟩ := h
  have hex : ∀ n, ∃ k, n ≤ g k := fun n => ⟨n, hg.id_le n⟩
  let c : ℕ → ℕ := fun n => Nat.find (hex n)
  have hc_g : ∀ k, c (g k) = k := by
    intro k
    refine (Nat.find_eq_iff _).2 ⟨le_rfl, fun k' hk' => ?_⟩
    have := hg hk'; omega
  have hc_g1 : ∀ k, c (g k + 1) = k + 1 := by
    intro k
    refine (Nat.find_eq_iff _).2 ⟨hg (Nat.lt_succ_self k), fun k' hk' => ?_⟩
    have := hg.monotone (Nat.lt_succ_iff.1 hk'); omega
  have hc_out : ∀ n, (∀ k, g k ≠ n) → c (n + 1) = c n := by
    intro n hn
    apply le_antisymm
    · exact Nat.find_mono (fun k hk => by have := hn k; omega)
    · exact Nat.find_mono (fun k hk => by omega)
  refine ⟨fun n => q (c n), ?_, fun n => ?_⟩
  · have : c 0 = 0 := (Nat.find_eq_zero _).2 (Nat.zero_le _)
    simp only [this]; exact hq0
  · by_cases hn : ∃ k, g k = n
    · obtain ⟨k, rfl⟩ := hn
      simp only [hc_g, hc_g1]
      rcases hgk k with h1 | ⟨h1, h2⟩
      · rw [h1]; exact hq k
      · rw [SeqStep.eq_of_idle h1 (hq k)]; exact SeqStep.of_idle h2 _
    · push Not at hn
      simp only [hc_out n hn]
      exact SeqStep.of_idle (hout n hn) _

/-- Concatenation: `S` on positions `< K`, then `T` shifted by `K`. -/
def SeqHist.concat (S T : SeqHist Res) (K : ℕ) : SeqHist Res :=
  fun k => if k < K then S k else T (k - K)

lemma concat_of_lt {S T : SeqHist Res} {K k : ℕ} (h : k < K) : S.concat T K k = S k := ite_eq_left h

lemma concat_of_ge {S T : SeqHist Res} {K k : ℕ} (h : K ≤ k) : S.concat T K k = T (k - K) :=
  ite_eq_right (by omega)

lemma concat_add {S T : SeqHist Res} {K k : ℕ} : S.concat T K (K + k) = T k := by
  rw [concat_of_ge (by omega), Nat.add_sub_cancel_left]

lemma concat_eq_some {S T : SeqHist Res} {K k : ℕ} {e : ℕ × Res} (h : S.concat T K k = some e) :
    S k = some e ∨ T (k - K) = some e := by
  unfold SeqHist.concat at h; split_ifs at h
  · exact Or.inl h
  · exact Or.inr h

lemma mem_concat {S T : SeqHist Res} {K : ℕ} (hK : ∀ k, K ≤ k → S k = none) {b : ℕ} :
    (S.concat T K).Mem b ↔ S.Mem b ∨ T.Mem b := by
  constructor
  · rintro ⟨k, r, hk⟩
    rcases concat_eq_some hk with h | h
    · exact Or.inl ⟨k, r, h⟩
    · exact Or.inr ⟨k - K, r, h⟩
  · rintro (⟨k, r, hk⟩ | ⟨k, r, hk⟩)
    · have : k < K := by by_contra h'; rw [hK k (by omega)] at hk; cases hk
      exact ⟨k, r, by rw [concat_of_lt this]; exact hk⟩
    · exact ⟨K + k, r, by rw [concat_add]; exact hk⟩

lemma nodup_concat {S T : SeqHist Res} {K : ℕ} (hS : S.Nodup) (hT : T.Nodup)
    (hdis : ∀ b, S.Mem b → T.Mem b → False) :
    (S.concat T K).Nodup := by
  intro k k' a r r' hk hk'
  by_cases h1 : k < K <;> by_cases h2 : k' < K
  · rw [concat_of_lt h1] at hk; rw [concat_of_lt h2] at hk'; exact hS k k' a r r' hk hk'
  · rw [concat_of_lt h1] at hk; rw [concat_of_ge (by omega)] at hk'
    exact (hdis a ⟨k, r, hk⟩ ⟨_, r', hk'⟩).elim
  · rw [concat_of_lt h2] at hk'; rw [concat_of_ge (by omega)] at hk
    exact (hdis a ⟨k', r', hk'⟩ ⟨_, r, hk⟩).elim
  · rw [concat_of_ge (by omega)] at hk hk'
    have := hT _ _ a r r' hk hk'; omega

lemma legal_concat {spec : X → ObjType Q Op Res} {S T : SeqHist Res} {K : ℕ}
    (hS : Legal spec H S) (hT : Legal spec H T) (hK : ∀ k, K ≤ k → S k = none)
    (hdis : ∀ z, (∀ k, Idle H z (S k)) ∨ (∀ k, Idle H z (T k))) :
    Legal spec H (S.concat T K) := by
  refine ⟨fun k a r hk => ?_, fun z => ?_⟩
  · rcases concat_eq_some hk with h | h
    · exact hS.1 _ _ _ h
    · exact hT.1 _ _ _ h
  · rcases hdis z with hz | hz
    · refine (hT.legalAt z).reindex (g := fun k => K + k) (fun a b h => Nat.add_lt_add_left h K)
        (fun k => Or.inl concat_add) (fun n hn => ?_)
      have : n < K := by by_contra h; exact hn (n - K) (by omega)
      rw [concat_of_lt this]; exact hz n
    · refine (hS.legalAt z).reindex (g := id) strictMono_id (fun k => ?_)
        (fun n hn => (hn n rfl).elim)
      by_cases hk : k < K
      · exact Or.inl (concat_of_lt hk)
      · right; rw [hK k (by omega)]
        exact ⟨idle_none, by simp only [id]; rw [concat_of_ge (by omega)]; exact hz _⟩

open Classical in
/-- The entries of `S` on object `x` (positions kept): `S|x`. -/
noncomputable def SeqHist.restrictObj (H : History P X Op Res) (S : SeqHist Res) (x : X) :
    SeqHist Res :=
  fun k => if ∃ b r, S k = some (b, r) ∧ OnObj H x b then S k else none

lemma restrictObj_eq_some {S : SeqHist Res} {x : X} {k : ℕ} {b : ℕ} {r : Res} :
    S.restrictObj H x k = some (b, r) ↔ S k = some (b, r) ∧ OnObj H x b := by
  unfold SeqHist.restrictObj
  split_ifs with h
  · constructor
    · intro hk; obtain ⟨b', r', h1, h2⟩ := h; rw [h1] at hk ⊢; cases hk; exact ⟨rfl, h2⟩
    · exact fun h => h.1
  · simp only [false_iff, not_and]
    exact fun hk hx => h ⟨b, r, hk, hx⟩

lemma restrictObj_of_onObj {S : SeqHist Res} {x : X} {k : ℕ} {b : ℕ} {r : Res}
    (hk : S k = some (b, r)) (hx : OnObj H x b) : S.restrictObj H x k = some (b, r) :=
  restrictObj_eq_some.2 ⟨hk, hx⟩

lemma SeqHist.Nodup.restrictObj {S : SeqHist Res} (h : S.Nodup) (x : X) :
    (S.restrictObj H x).Nodup := fun k k' a r r' hk hk' =>
  h k k' a r r' (restrictObj_eq_some.1 hk).1 (restrictObj_eq_some.1 hk').1

/-- `S|x` is a legal sequential history of `H|x`. -/
lemma Legal.restrictObj {spec : X → ObjType Q Op Res} {S : SeqHist Res} (h : Legal spec H S)
    (x : X) : Legal spec (restrict H x) (S.restrictObj H x) := by
  classical
  have hH : Legal spec H (S.restrictObj H x) := by
    refine ⟨fun k a r hk => h.1 k a r (restrictObj_eq_some.1 hk).1, fun z => ?_⟩
    by_cases hz : z = x
    · subst hz
      refine (h.legalAt z).reindex (g := id) strictMono_id (fun k => ?_)
        (fun n hn => (hn n rfl).elim)
      cases hk : S k with
      | none =>
        right; refine ⟨idle_none, fun b r h' => ?_⟩
        simp only [id] at h'; rw [restrictObj_eq_some, hk] at h'; cases h'.1
      | some e =>
        obtain ⟨b, r⟩ := e
        by_cases hb : OnObj H z b
        · exact Or.inl (restrictObj_of_onObj hk hb)
        · right
          refine ⟨fun b' r' h' => by cases h'; exact hb, fun b' r' h' => ?_⟩
          simp only [id] at h'; rw [restrictObj_eq_some, hk] at h'
          obtain ⟨h1, h2⟩ := h'; cases h1; exact (hb h2).elim
    · obtain ⟨q, hq0, -⟩ := h.legalAt z
      exact LegalAt.const hq0 fun k b r hk hb =>
        hz (onObj_unique hb (restrictObj_eq_some.1 hk).2)
  exact hH.congr fun k a r hk => restrict_of_onObj (restrictObj_eq_some.1 hk).2

end SeqTools

section Lemma8

variable {spec : X → ObjType Q Op Res} {H : History P X Op Res}

/-- **Lemma 8**, "only if": if `H` is weakly consistent then so is `H|x`. -/
theorem weaklyConsistent_restrict (h : WeaklyConsistent spec H) (x : X) :
    WeaklyConsistent spec (restrict H x) := by
  intro a j r hj
  obtain ⟨hj, hax⟩ := restrict_res_iff.1 hj
  obtain ⟨S, hnd, hleg, hlt, hproc, k, hk, hk'⟩ := h a j r hj
  refine ⟨S.restrictObj H x, hnd.restrictObj x, hleg.restrictObj x,
    fun b ⟨k, rb, hb⟩ => hlt b ⟨k, rb, (restrictObj_eq_some.1 hb).1⟩,
    fun b hb hpre => ?_, k, restrictObj_of_onObj hk hax, fun k' hk'' => ?_⟩
  · obtain ⟨kb, rb, hkb⟩ := hproc b (sameProc_of_restrict hb) (precedes_of_restrict hpre)
    obtain ⟨p, y, y', op, op', h1, -⟩ := hb
    have hbx : OnObj H x b := by
      obtain ⟨h1', rfl⟩ := restrict_inv_iff.1 h1; exact ⟨p, op, h1'⟩
    exact ⟨kb, rb, restrictObj_of_onObj hkb hbx⟩
  · unfold SeqHist.restrictObj; rw [hk' k' hk'']; simp

/-- **Lemma 8**, "if" (no totality needed): if every `H|x` is weakly consistent then so is `H`. -/
theorem weaklyConsistent_of_restrict (hH : WellFormed H)
    (h : ∀ x, WeaklyConsistent spec (restrict H x)) : WeaklyConsistent spec H := by
  classical
  intro a j r hj
  obtain ⟨haj, p, x, op, ha⟩ := hH.res_inv a j r hj
  obtain ⟨Sx, hndx, hlegx, hltx, hprocx, kx, hkx, hkx'⟩ :=
    h x a j r (restrict_res_iff.2 ⟨hj, p, op, ha⟩)
  have hI : ∀ z, (spec z).init.Nonempty := fun z =>
    let ⟨_, hq, _⟩ := hlegx.legalAt z; ⟨_, hq⟩
  have hSx_on : ∀ k b rb, Sx k = some (b, rb) → OnObj H x b := fun k b rb hk =>
    invoked_restrict.1 (hlegx.1 k b rb hk)
  have hlegxH : Legal spec H Sx :=
    hlegx.congr fun k b rb hk => (restrict_of_onObj (hSx_on k b rb hk)).symm
  have hproc_of : ∀ b, SameProc H b a → ∃ y op', H b = some (.inv p y op') := by
    rintro b ⟨p', y, x', op', op'', h1, h2⟩
    rw [ha] at h2; cases h2; exact ⟨y, op', h1⟩
  -- the concatenated witnesses for the process's operations on the objects of `s`
  have claim : ∀ s : Finset X, ∃ (S : SeqHist Res) (K : ℕ), S.Nodup ∧ Legal spec H S ∧
      (∀ k, K ≤ k → S k = none) ∧
      (∀ k b rb, S k = some (b, rb) → b < a ∧ ∃ y ∈ s, OnObj H y b) ∧
      (∀ b y, y ∈ s → SameProc H b a → b < a → OnObj H y b → S.Mem b) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => none, 0, fun _ _ _ _ _ h => (by cases h), legal_empty hI, fun _ _ => rfl,
        fun _ _ _ h => (by cases h), fun b y hy => (by simp at hy)⟩
    | insert y s hy ih =>
      obtain ⟨S, K, hnd, hleg, hK, hent, hmem⟩ := ih
      by_cases hex : ∃ b, b < a ∧ SameProc H b a ∧ OnObj H y b
      · obtain ⟨b0, hb0⟩ := hex
        -- the process's last operation on `y` before `a`
        set Pb : ℕ → Prop := fun b => b < a ∧ SameProc H b a ∧ OnObj H y b with hPb
        set bl := Nat.findGreatest Pb a with hbl_def
        have hbl : bl < a ∧ SameProc H bl a ∧ OnObj H y bl :=
          Nat.findGreatest_spec (P := Pb) hb0.1.le hb0
        have hmax : ∀ c, c < a ∧ SameProc H c a ∧ OnObj H y c → c ≤ bl :=
          fun c hc => Nat.le_findGreatest (P := Pb) hc.1.le hc
        obtain ⟨y', opy, hblH⟩ := hproc_of bl hbl.2.1
        have hy' : y' = y := onObj_unique ⟨p, opy, hblH⟩ hbl.2.2
        rw [hy'] at hblH
        obtain ⟨jy, ry, hjya, hjy⟩ := hH.seq bl a p y x opy op hblH ha hbl.1
        obtain ⟨W, hndW, hlegW, hltW, hprocW, kW, hkW, hkW'⟩ :=
          h y bl jy ry (restrict_res_iff.2 ⟨hjy, p, opy, hblH⟩)
        have hW_on : ∀ k b rb, W k = some (b, rb) → OnObj H y b := fun k b rb hk =>
          invoked_restrict.1 (hlegW.1 k b rb hk)
        have hlegWH : Legal spec H W :=
          hlegW.congr fun k b rb hk => (restrict_of_onObj (hW_on k b rb hk)).symm
        have hS_not : ∀ k b rb, S k = some (b, rb) → ¬ OnObj H y b := by
          intro k b rb hk hb
          obtain ⟨-, z, hz, hzb⟩ := hent k b rb hk
          exact hy (onObj_unique hb hzb ▸ hz)
        refine ⟨S.concat W K, K + kW + 1, nodup_concat hnd hndW ?_,
          legal_concat hleg hlegWH hK ?_, ?_, ?_, ?_⟩
        · rintro b ⟨k, rb, hk⟩ ⟨k', rb', hk'⟩; exact hS_not k b rb hk (hW_on k' b rb' hk')
        · intro z
          by_cases hz : z = y
          · rw [hz]; left; intro k b rb hk; exact hS_not k b rb hk
          · right; intro k b rb hk hb; exact hz (onObj_unique hb (hW_on k b rb hk))
        · intro k hk; rw [concat_of_ge (by omega)]; exact hkW' _ (by omega)
        · intro k b rb hk
          rcases concat_eq_some hk with h1 | h1
          · obtain ⟨h2, z, hz, h3⟩ := hent k b rb h1
            exact ⟨h2, z, Finset.mem_insert_of_mem hz, h3⟩
          · exact ⟨by have := hltW b ⟨_, _, h1⟩; omega, y, Finset.mem_insert_self _ _,
              hW_on _ _ _ h1⟩
        · intro c z hz hc hca hcz
          rw [mem_concat hK]
          rcases Finset.mem_insert.1 hz with hzy | hz
          · rw [hzy] at hcz
            right
            have hcle := hmax c ⟨hca, hc, hcz⟩
            rcases hcle.lt_or_eq with hlt | hceq
            · obtain ⟨y'', opc, hcH⟩ := hproc_of c hc
              have hy'' : y'' = y := onObj_unique ⟨p, opc, hcH⟩ hcz
              rw [hy''] at hcH
              obtain ⟨jc, rc, hjc, hjcH⟩ := hH.seq c bl p y y opc opy hcH hblH hlt
              exact hprocW c ⟨p, y, y, opc, opy, restrict_inv_iff.2 ⟨hcH, rfl⟩,
                restrict_inv_iff.2 ⟨hblH, rfl⟩⟩ ⟨jc, rc, restrict_res_iff.2 ⟨hjcH, p, opc, hcH⟩,
                hjc, p, y, opy, restrict_inv_iff.2 ⟨hblH, rfl⟩⟩
            · rw [hceq]; exact ⟨kW, ry, hkW⟩
          · left; exact hmem c z hz hc hca hcz
      · refine ⟨S, K, hnd, hleg, hK, fun k b rb hk => ?_, fun c z hz hc hca hcz => ?_⟩
        · obtain ⟨h2, z, hz, h3⟩ := hent k b rb hk
          exact ⟨h2, z, Finset.mem_insert_of_mem hz, h3⟩
        · rcases Finset.mem_insert.1 hz with hzy | hz
          · rw [hzy] at hcz; exact (hex ⟨c, hca, hc, hcz⟩).elim
          · exact hmem c z hz hc hca hcz
  -- the other objects on which the process operated before `a`
  have hfin : {z : X | z ≠ x ∧ ∃ b < a, OnObj H z b}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio a) fun b _ =>
      Set.Subsingleton.finite (s := {z : X | OnObj H z b}) fun z1 h1 z2 h2 => onObj_unique h1 h2) ?_
    rintro z ⟨-, b, hb, hzb⟩
    exact Set.mem_biUnion (x := b) hb hzb
  obtain ⟨S, K, hnd, hleg, hK, hent, hmem⟩ := claim hfin.toFinset
  have hS_not : ∀ k b rb, S k = some (b, rb) → ¬ OnObj H x b := by
    intro k b rb hk hb
    obtain ⟨-, z, hz, hzb⟩ := hent k b rb hk
    exact ((Set.Finite.mem_toFinset _).1 hz).1 (onObj_unique hzb hb)
  refine ⟨S.concat Sx K, nodup_concat hnd hndx ?_, legal_concat hleg hlegxH hK ?_, ?_, ?_,
    K + kx, ?_, ?_⟩
  · rintro b ⟨k, rb, hk⟩ ⟨k', rb', hk'⟩; exact hS_not k b rb hk (hSx_on k' b rb' hk')
  · intro z
    by_cases hz : z = x
    · rw [hz]; left; intro k b rb hk; exact hS_not k b rb hk
    · right; intro k b rb hk hb; exact hz (onObj_unique hb (hSx_on k b rb hk))
  · intro b hb
    rcases (mem_concat hK).1 hb with ⟨k, rb, hk⟩ | hb
    · have := (hent k b rb hk).1; omega
    · exact hltx b hb
  · intro b hb hpre
    obtain ⟨j', r', h1, h2, -⟩ := hpre
    have hba : b < a := by have := (hH.res_inv b j' r' h1).1; omega
    obtain ⟨z, opb, hbH⟩ := hproc_of b hb
    rw [mem_concat hK]
    by_cases hz : z = x
    · rw [hz] at hbH; right
      exact hprocx b ⟨p, x, x, opb, op, restrict_inv_iff.2 ⟨hbH, rfl⟩,
        restrict_inv_iff.2 ⟨ha, rfl⟩⟩ ⟨j', r', restrict_res_iff.2 ⟨h1, p, opb, hbH⟩, h2, p, x, op,
        restrict_inv_iff.2 ⟨ha, rfl⟩⟩
    · left
      exact hmem b z ((Set.Finite.mem_toFinset _).2 ⟨hz, b, hba, p, opb, hbH⟩) hb hba
        ⟨p, opb, hbH⟩
  · rw [concat_add]; exact hkx
  · intro k' hk'; rw [concat_of_ge (by omega)]; exact hkx' _ (by omega)

/-- **Lemma 8.** A (well-formed) history `H` is weakly consistent iff `H|x` is weakly consistent
for every object `x`. No totality assumption is needed. -/
theorem weaklyConsistent_iff_restrict (hH : WellFormed H) :
    WeaklyConsistent spec H ↔ ∀ x, WeaklyConsistent spec (restrict H x) :=
  ⟨fun h x => weaklyConsistent_restrict h x, weaklyConsistent_of_restrict hH⟩

end Lemma8

section Lemma7

variable {spec : X → ObjType Q Op Res} {H : History P X Op Res}

lemma isTLin_restrict {t : ℕ} {S : SeqHist Res} (h : IsTLin spec H t S) (x : X) :
    IsTLin spec (restrict H x) t (S.restrictObj H x) where
  nodup := h.nodup.restrictObj x
  legal := h.legal.restrictObj x
  complete a j r hj := by
    obtain ⟨hj, hx⟩ := restrict_res_iff.1 hj
    obtain ⟨k, r', hk⟩ := h.complete a j r hj
    exact ⟨k, r', restrictObj_of_onObj hk hx⟩
  rt a b j r hj htj hjb hb hbS := by
    obtain ⟨hj, hx⟩ := restrict_res_iff.1 hj
    have hbx : OnObj H x b := invoked_restrict.1 hb
    obtain ⟨kb, rb, hkb⟩ := hbS
    obtain ⟨p, op, hbH⟩ := hbx
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ :=
      h.rt a b j r hj htj hjb ⟨p, x, op, hbH⟩ ⟨kb, rb, (restrictObj_eq_some.1 hkb).1⟩
    exact ⟨k1, k2, r1, r2, h12, restrictObj_of_onObj h1 hx, restrictObj_of_onObj h2 ⟨p, op, hbH⟩⟩
  resp a j r hj htj := by
    obtain ⟨hj, hx⟩ := restrict_res_iff.1 hj
    obtain ⟨k, hk⟩ := h.resp a j r hj htj
    exact ⟨k, restrictObj_of_onObj hk hx⟩

/-- **Lemma 7**, "only if": a `t`-linearization of `H` restricts to a `t`-linearization of
`H|x`. -/
theorem tLinearizable_restrict {t : ℕ} (h : TLinearizable spec H t) (x : X) :
    TLinearizable spec (restrict H x) t :=
  let ⟨_, hS⟩ := h; ⟨_, isTLin_restrict hS x⟩

/-- The operation at position `k` of `S` if it is *late* (invoked at a position `≥ t`), else `0`. -/
def lateOp (S : SeqHist Res) (t k : ℕ) : ℕ :=
  match S k with
  | some (b, _) => if t ≤ b then b else 0
  | none => 0

/-- The largest late operation at or before position `k` of `S` (or `0`). -/
def lateKey (S : SeqHist Res) (t k : ℕ) : ℕ := (Finset.range (k + 1)).sup (lateOp S t)

lemma lateKey_mono (S : SeqHist Res) (t : ℕ) : Monotone (lateKey S t) := fun k k' h =>
  Finset.sup_mono (Finset.range_subset_range.2 (by omega))

lemma le_lateKey {S : SeqHist Res} {t k b : ℕ} {r : Res} (hk : S k = some (b, r)) (hb : t ≤ b) :
    b ≤ lateKey S t k := by
  have : lateOp S t k = b := by simp [lateOp, hk, hb]
  rw [← this]; exact Finset.le_sup (f := lateOp S t) (Finset.self_mem_range_succ k)

lemma op_le_of_lateKey_le {S : SeqHist Res} {t k b v : ℕ} {r : Res} (hk : S k = some (b, r))
    (hv : lateKey S t k ≤ v) : b ≤ max v t := by
  by_cases hb : t ≤ b
  · exact le_max_of_le_left ((le_lateKey hk hb).trans hv)
  · exact le_max_of_le_right (by omega)

lemma lateKey_lt {S : SeqHist Res} {t k j : ℕ} (hj : 0 < j)
    (h : ∀ k' ≤ k, ∀ b r, S k' = some (b, r) → t ≤ b → b < j) : lateKey S t k < j := by
  refine (Finset.sup_lt_iff hj).2 fun k' hk' => ?_
  have hk'' : k' ≤ k := by simp at hk'; omega
  cases hS : S k' with
  | none => simp [lateOp, hS, hj]
  | some e =>
    obtain ⟨b, r⟩ := e
    simp only [lateOp, hS]
    split_ifs with hb
    · exact h k' hk'' b r hS hb
    · exact hj

lemma SeqHist.Nodup.exists_bound {S : SeqHist Res} (hS : S.Nodup) (m : ℕ) :
    ∃ N, ∀ k b r, S k = some (b, r) → b < m → k < N := by
  induction m with
  | zero => exact ⟨0, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hm : ∃ k0 r0, S k0 = some (m, r0)
    · obtain ⟨k0, r0, hk0⟩ := hm
      refine ⟨max N (k0 + 1), fun k b r hk hb => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · have := hN k b r hk hb; omega
      · have := hS k k0 b r r0 hk hk0; omega
    · refine ⟨N, fun k b r hk hb => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · exact hN k b r hk hb
      · exact (hm ⟨k, r, hk⟩).elim

/-- **Lemma 7**, "if" (finitely many objects, finite or infinite histories): if every `H|x` is
`t_x`-linearizable then `H` is `t`-linearizable for some `t`. The per-object linearizations are
merged by ordering an entry of `S_x` at position `k` by `(lateKey S_x t k, k)`, interleaving the
objects. -/
theorem exists_tLinearizable_of_restrict [Finite X] (hH : WellFormed H)
    (h : ∀ x, ∃ t, TLinearizable spec (restrict H x) t) : ∃ t, TLinearizable spec H t := by
  classical
  have := Fintype.ofFinite X
  choose tx Sx hSx using h
  set t := Finset.univ.sup tx + 1 with ht
  have hS : ∀ x, IsTLin spec (restrict H x) t (Sx x) := fun x =>
    (hSx x).mono (by have := Finset.le_sup (f := tx) (Finset.mem_univ x); omega)
  have hon : ∀ x k b r, Sx x k = some (b, r) → OnObj H x b := fun x k b r hk =>
    invoked_restrict.1 ((hS x).legal.1 k b r hk)
  -- bounds on the positions of entries with small operations
  have hbd : ∀ m, ∃ N, ∀ x k b r, Sx x k = some (b, r) → b < m → k < N := by
    intro m
    choose Nx hNx using fun x => (hS x).nodup.exists_bound m
    refine ⟨Finset.univ.sup Nx, fun x k b r hk hb => ?_⟩
    have := hNx x k b r hk hb
    have := Finset.le_sup (f := Nx) (Finset.mem_univ x); omega
  choose NN hNN using hbd
  set N : ℕ → ℕ := fun v => NN (max v t + 1) with hNdef
  have hN : ∀ x k b r v, Sx x k = some (b, r) → lateKey (Sx x) t k ≤ v → k < N v :=
    fun x k b r v hk hv => hNN _ x k b r hk (Nat.lt_succ_of_le (op_le_of_lateKey_le hk hv))
  set M : ℕ → ℕ := fun v => ∑ u ∈ Finset.range v, N u with hMdef
  have hM : ∀ v v', v < v' → M v + N v ≤ M v' := by
    intro v v' hvv'
    have : M v + N v = M (v + 1) := (Finset.sum_range_succ N v).symm
    rw [this]; exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hvv')
  have hMmono : Monotone M := fun v v' h =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)
  set e := Finite.equivFin X with he
  set n := Nat.card X with hn
  set f : X → ℕ → ℕ := fun x k => n * (M (lateKey (Sx x) t k) + k) + e x with hf
  have hfmono : ∀ x, StrictMono (f x) := by
    intro x k k' hkk'
    have h1 := hMmono (lateKey_mono (Sx x) t hkk'.le)
    have hn0 : 0 < n := Fin.pos (e x)
    have : n * (M (lateKey (Sx x) t k) + k) < n * (M (lateKey (Sx x) t k') + k') :=
      mul_lt_mul_of_pos_left (by omega) hn0
    simp only [hf]; omega
  have hfkey : ∀ x1 k1 b r x2 k2, Sx x1 k1 = some (b, r) →
      lateKey (Sx x1) t k1 < lateKey (Sx x2) t k2 → f x1 k1 < f x2 k2 := by
    intro x1 k1 b r x2 k2 hk1 hkey
    have h1 := hN x1 k1 b r _ hk1 le_rfl
    have h2 := hM _ _ hkey
    have h3 : n * (M (lateKey (Sx x1) t k1) + k1 + 1) ≤ n * (M (lateKey (Sx x2) t k2) + k2) :=
      Nat.mul_le_mul_left n (by omega)
    have h4 := (e x1).isLt
    simp only [hf]
    rw [mul_add n _ 1, mul_one] at h3
    omega
  have hfinj : ∀ x1 k1 x2 k2, f x1 k1 = f x2 k2 → x1 = x2 ∧ k1 = k2 := by
    intro x1 k1 x2 k2 heq
    have hmod := congrArg (· % n) heq
    simp only [hf, Nat.mul_add_mod, Nat.mod_eq_of_lt (e x1).isLt,
      Nat.mod_eq_of_lt (e x2).isLt] at hmod
    have hx : x1 = x2 := e.injective (Fin.ext hmod)
    subst hx
    exact ⟨rfl, (hfmono x1).injective heq⟩
  -- the merged sequential history
  set S : SeqHist Res := fun m =>
    if hm : ∃ p : X × ℕ, f p.1 p.2 = m then Sx hm.choose.1 hm.choose.2 else none with hSdef
  have hSf : ∀ x k, S (f x k) = Sx x k := by
    intro x k
    have hm : ∃ p : X × ℕ, f p.1 p.2 = f x k := ⟨(x, k), rfl⟩
    simp only [hSdef, hm, ↓reduceDIte]
    obtain ⟨h1, h2⟩ := hfinj _ _ _ _ hm.choose_spec
    rw [h1, h2]
  have hSsome : ∀ m e', S m = some e' → ∃ x k, f x k = m ∧ Sx x k = some e' := by
    intro m e' hm
    simp only [hSdef] at hm
    split_ifs at hm with hm'
    exact ⟨_, _, hm'.choose_spec, hm⟩
  have hres_on : ∀ a j r, H j = some (.res a r) → ∃ x, OnObj H x a := by
    intro a j r hj
    obtain ⟨-, p, x, op, ha⟩ := hH.res_inv a j r hj
    exact ⟨x, p, op, ha⟩
  refine ⟨t, S, ⟨?_, ⟨?_, fun z => ?_⟩, ?_, ?_, ?_⟩⟩
  · -- nodup
    intro m m' a r r' hm hm'
    obtain ⟨x, k, rfl, hk⟩ := hSsome m _ hm
    obtain ⟨x', k', rfl, hk'⟩ := hSsome m' _ hm'
    have hxx : x = x' := onObj_unique (hon _ _ _ _ hk) (hon _ _ _ _ hk')
    subst hxx
    rw [(hS x).nodup k k' a r r' hk hk']
  · intro m a r hm
    obtain ⟨x, k, -, hk⟩ := hSsome m _ hm
    obtain ⟨p, op, h⟩ := hon _ _ _ _ hk
    exact ⟨p, x, op, h⟩
  · -- legality for object `z`
    have hz : LegalAt (spec z) H z (Sx z) :=
      ((hS z).legal.congr fun k b r hk => (restrict_of_onObj (hon _ _ _ _ hk)).symm).legalAt z
    refine hz.reindex (hfmono z) (fun k => Or.inl (hSf z k)) fun m hm b r hb hzb => ?_
    obtain ⟨x, k, rfl, hk⟩ := hSsome m _ hb
    have hxz : x = z := onObj_unique (hon _ _ _ _ hk) hzb
    subst hxz
    exact hm k rfl
  · -- completeness
    intro a j r hj
    obtain ⟨x, hx⟩ := hres_on a j r hj
    obtain ⟨k, r', hk⟩ := (hS x).complete a j r (restrict_res_iff.2 ⟨hj, hx⟩)
    exact ⟨f x k, r', by rw [hSf]; exact hk⟩
  · -- real-time order
    intro a b j r hj htj hjb hbinv hbmem
    obtain ⟨x1, hx1⟩ := hres_on a j r hj
    have hj1 : restrict H x1 j = some (.res a r) := restrict_res_iff.2 ⟨hj, hx1⟩
    obtain ⟨k1, r1, hk1⟩ := (hS x1).complete a j r hj1
    obtain ⟨m, rb, hm⟩ := hbmem
    obtain ⟨x2, k2, rfl, hk2⟩ := hSsome m _ hm
    by_cases hx12 : x1 = x2
    · subst hx12
      obtain ⟨k1', k2', r1', r2', hlt, h1, h2⟩ := (hS x1).rt a b j r hj1 htj hjb
        (invoked_restrict.2 (hon _ _ _ _ hk2)) ⟨k2, rb, hk2⟩
      exact ⟨f x1 k1', f x1 k2', r1', r2', hfmono x1 hlt, by rw [hSf]; exact h1,
        by rw [hSf]; exact h2⟩
    · have hkey1 : lateKey (Sx x1) t k1 < j := by
        refine lateKey_lt (by omega) fun k' hk' w rw hw htw => ?_
        by_contra hjw
        have hwj : w ≠ j := by
          intro hwj
          obtain ⟨p, op, hwH⟩ := hon _ _ _ _ hw
          rw [hwj, hj] at hwH; cases hwH
        obtain ⟨ka, kw, ra, rw', hlt, h1, h2⟩ := (hS x1).rt a w j r hj1 htj (by omega)
          (invoked_restrict.2 (hon _ _ _ _ hw)) ⟨k', rw, hw⟩
        have e1 := (hS x1).nodup ka k1 a ra r1 h1 hk1
        have e2 := (hS x1).nodup kw k' w rw' rw h2 hw
        omega
      have hkey2 : b ≤ lateKey (Sx x2) t k2 := le_lateKey hk2 (by omega)
      exact ⟨f x1 k1, f x2 k2, r1, rb, hfkey _ _ _ _ _ _ hk1 (by omega), by rw [hSf]; exact hk1,
        by rw [hSf]; exact hk2⟩
  · -- responses
    intro a j r hj htj
    obtain ⟨x, hx⟩ := hres_on a j r hj
    obtain ⟨k, hk⟩ := (hS x).resp a j r (restrict_res_iff.2 ⟨hj, hx⟩) htj
    exact ⟨f x k, by rw [hSf]; exact hk⟩

/-- **Lemma 7** (Serafini et al.; for finitely many objects, finite or infinite well-formed
histories). -/
theorem exists_tLinearizable_iff_restrict [Finite X] (hH : WellFormed H) :
    (∃ t, TLinearizable spec H t) ↔ ∀ x, ∃ t, TLinearizable spec (restrict H x) t :=
  ⟨fun ⟨t, ht⟩ x => ⟨t, tLinearizable_restrict ht x⟩, exists_tLinearizable_of_restrict hH⟩

/-- **Proposition 9.** A well-formed history involving finitely many objects is eventually
linearizable iff each `H|x` is. -/
theorem eventuallyLinearizable_iff_restrict [Finite X] (hH : WellFormed H) :
    EventuallyLinearizable spec H ↔ ∀ x, EventuallyLinearizable spec (restrict H x) := by
  constructor
  · rintro ⟨hwc, t, ht⟩ x
    exact ⟨weaklyConsistent_restrict hwc x, t, tLinearizable_restrict ht x⟩
  · intro h
    exact ⟨weaklyConsistent_of_restrict hH fun x => (h x).1,
      exists_tLinearizable_of_restrict hH fun x => (h x).2⟩

end Lemma7

section Counterexample

/-- Read/write register operations. -/
inductive RegOp
  | read
  | write (v : ℕ)

/-- A read/write register over `ℕ`, initialized to `0`; a `write` returns the acknowledgement
`0`. -/
def register : ObjType ℕ RegOp ℕ where
  init := {0}
  δ q op r q' := match op with
    | .read => r = q ∧ q' = q
    | .write v => r = 0 ∧ q' = v

/-- The paper's history with infinitely many registers `R₀, R₁, …` (all initialized to `0`):
for each `i`, process `0` writes `1` to `R_i` (positions `4i`, `4i+1`), then process `1` reads
`R_i` and gets `0` (positions `4i+2`, `4i+3`). -/
def regHist : History (Fin 2) ℕ RegOp ℕ := fun n =>
  if n % 4 = 0 then some (.inv 0 (n / 4) (.write 1))
  else if n % 4 = 2 then some (.inv 1 (n / 4) .read)
  else some (.res (n - 1) 0)

lemma regHist_eq_inv {n : ℕ} {p : Fin 2} {y : ℕ} {op : RegOp} :
    regHist n = some (.inv p y op) ↔
      (n % 4 = 0 ∧ p = 0 ∧ y = n / 4 ∧ op = .write 1) ∨
      (n % 4 = 2 ∧ p = 1 ∧ y = n / 4 ∧ op = .read) := by
  unfold regHist
  split_ifs with h1 h2
  · simp only [Option.some.injEq, Ev.inv.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact Or.inl ⟨h1, rfl, rfl, rfl⟩
    · rintro (⟨-, rfl, rfl, rfl⟩ | ⟨h, -⟩)
      · exact ⟨rfl, rfl, rfl⟩
      · omega
  · simp only [Option.some.injEq, Ev.inv.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact Or.inr ⟨h2, rfl, rfl, rfl⟩
    · rintro (⟨h, -⟩ | ⟨-, rfl, rfl, rfl⟩)
      · omega
      · exact ⟨rfl, rfl, rfl⟩
  · simp only [Option.some.injEq, reduceCtorEq, false_iff]
    omega

lemma regHist_eq_res {n a r : ℕ} :
    regHist n = some (.res a r) ↔ (n % 4 = 1 ∨ n % 4 = 3) ∧ a = n - 1 ∧ r = 0 := by
  unfold regHist
  split_ifs with h1 h2
  · simp only [Option.some.injEq, reduceCtorEq, false_iff]; omega
  · simp only [Option.some.injEq, reduceCtorEq, false_iff]; omega
  · simp only [Option.some.injEq, Ev.res.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨by omega, rfl, rfl⟩
    · rintro ⟨-, rfl, rfl⟩; exact ⟨rfl, rfl⟩

lemma onObj_regHist {i b : ℕ} : OnObj regHist i b ↔ (b % 4 = 0 ∨ b % 4 = 2) ∧ b / 4 = i := by
  constructor
  · rintro ⟨p, op, h⟩; have := regHist_eq_inv.1 h; omega
  · rintro ⟨h1 | h1, h2⟩
    · exact ⟨0, .write 1, regHist_eq_inv.2 (Or.inl ⟨h1, rfl, h2.symm, rfl⟩)⟩
    · exact ⟨1, .read, regHist_eq_inv.2 (Or.inr ⟨h1, rfl, h2.symm, rfl⟩)⟩

lemma invoked_regHist {b : ℕ} : Invoked regHist b ↔ b % 4 = 0 ∨ b % 4 = 2 := by
  constructor
  · rintro ⟨p, y, op, h⟩; have := regHist_eq_inv.1 h; omega
  · intro h; obtain ⟨p, op, h⟩ := onObj_regHist.2 ⟨h, rfl⟩; exact ⟨p, _, op, h⟩

lemma wellFormed_regHist : WellFormed regHist where
  res_inv a j r hj := by
    obtain ⟨h1, rfl, -⟩ := regHist_eq_res.1 hj
    exact ⟨by omega, invoked_regHist.2 (by omega)⟩
  res_unique a j j' r r' hj hj' := by
    have := regHist_eq_res.1 hj; have := regHist_eq_res.1 hj'; omega
  seq a b p x x' op op' ha hb hab := by
    have h1 := regHist_eq_inv.1 ha; have h2 := regHist_eq_inv.1 hb
    refine ⟨a + 1, 0, ?_, regHist_eq_res.2 (by omega)⟩
    rcases h1 with ⟨h1, rfl, -⟩ | ⟨h1, rfl, -⟩ <;> rcases h2 with ⟨h2, hp, -⟩ | ⟨h2, hp, -⟩ <;>
      omega

/-- A one-entry sequential history. -/
lemma legal_single {spec : X → ObjType Q Op Res} {H : History P X Op Res} {a : ℕ} {p : P}
    {x : X} {op : Op} {r : Res} {q₀ q' : Q} (ha : H a = some (.inv p x op))
    (hq₀ : q₀ ∈ (spec x).init) (hδ : (spec x).δ q₀ op r q')
    (hI : ∀ z, (spec z).init.Nonempty) :
    Legal spec H (fun k => if k = 0 then some (a, r) else none) := by
  refine ⟨fun k b rb hk => ?_, fun z => ?_⟩
  · dsimp only at hk; split_ifs at hk; cases hk; exact ⟨p, x, op, ha⟩
  · by_cases hz : z = x
    · subst hz
      refine ⟨fun k => if k = 0 then q₀ else q', by simpa using hq₀, fun k => ?_⟩
      rcases k with _ | k
      · exact Or.inl ⟨p, op, ha, hδ⟩
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]; rfl
    · obtain ⟨q₁, hq₁⟩ := hI z
      refine LegalAt.const hq₁ fun k b rb hk hb => ?_
      split_ifs at hk; cases hk
      exact hz (onObj_unique hb ⟨p, op, ha⟩)

lemma regHist_restrict_eventuallyLinearizable (i : ℕ) :
    EventuallyLinearizable (fun _ => register) (restrict regHist i) := by
  have hI : ∀ z : ℕ, (register.init).Nonempty := fun _ => ⟨0, rfl⟩
  refine ⟨fun a j r hj => ?_, 4 * i + 4, ?_⟩
  · -- weak consistency: each operation alone
    obtain ⟨hj, hai⟩ := restrict_res_iff.1 hj
    obtain ⟨hj1, rfl, rfl⟩ := regHist_eq_res.1 hj
    obtain ⟨p, op, hp⟩ := hai
    have hpr : restrict regHist i (j - 1) = some (.inv p i op) := restrict_inv_iff.2 ⟨hp, rfl⟩
    have hlegal : Legal (fun _ => register) (restrict regHist i)
        (fun k => if k = 0 then some (j - 1, 0) else none) := by
      rcases regHist_eq_inv.1 hp with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
      · exact legal_single (q₀ := 0) (q' := 1) hpr rfl ⟨rfl, rfl⟩ hI
      · exact legal_single (q₀ := 0) (q' := 0) hpr rfl ⟨rfl, rfl⟩ hI
    refine ⟨_, fun k k' a r r' hk hk' => ?_, hlegal, fun b ⟨k, rb, hk⟩ => ?_,
      fun b hb hpre => ?_, 0, rfl, fun k' hk' => ite_eq_right (by omega)⟩
    · split_ifs at hk hk' with h1 h2; omega
    · dsimp only at hk; split_ifs at hk; cases hk; omega
    · exfalso
      obtain ⟨p1, y1, y2, op1, op2, h1, h2⟩ := hb
      obtain ⟨h1', rfl⟩ := restrict_inv_iff.1 h1
      obtain ⟨h2', hy2⟩ := restrict_inv_iff.1 h2
      obtain ⟨j', r', h3, h4, -⟩ := hpre
      have e3 := regHist_eq_res.1 (restrict_eq_some h3)
      rcases regHist_eq_inv.1 h1' with ⟨e1, hp1, hy1, -⟩ | ⟨e1, hp1, hy1, -⟩ <;>
        rcases regHist_eq_inv.1 h2' with ⟨e2, hp2, hy2', -⟩ | ⟨e2, hp2, hy2', -⟩ <;> omega
  · -- `(4i+4)`-linearization: the read (returning `0`) then the write
    have hw : restrict regHist i (4 * i) = some (.inv 0 i (.write 1)) :=
      restrict_inv_iff.2 ⟨regHist_eq_inv.2 (Or.inl ⟨by omega, rfl, by omega, rfl⟩), rfl⟩
    have hr : restrict regHist i (4 * i + 2) = some (.inv 1 i .read) :=
      restrict_inv_iff.2 ⟨regHist_eq_inv.2 (Or.inr ⟨by omega, rfl, by omega, rfl⟩), rfl⟩
    have hlate : ∀ a j r, restrict regHist i j = some (.res a r) → j < 4 * i + 4 ∧
        (a = 4 * i ∨ a = 4 * i + 2) := by
      intro a j r hj
      obtain ⟨hj, hai⟩ := restrict_res_iff.1 hj
      have := regHist_eq_res.1 hj; have := onObj_regHist.1 hai; omega
    refine ⟨fun k => if k = 0 then some (4 * i + 2, 0) else if k = 1 then some (4 * i, 0)
      else none, ⟨fun k k' a r r' hk hk' => ?_, ⟨fun k a r hk => ?_, fun z => ?_⟩,
      fun a j r hj => ?_, fun a b j r hj htj => ?_, fun a j r hj htj => ?_⟩⟩
    · split_ifs at hk hk' <;> simp only [Option.some.injEq, Prod.mk.injEq] at hk hk' <;> omega
    · dsimp only at hk; split_ifs at hk <;> cases hk
      · exact ⟨_, _, _, hr⟩
      · exact ⟨_, _, _, hw⟩
    · by_cases hz : z = i
      · subst hz
        refine ⟨fun k => if k ≤ 1 then 0 else 1, rfl, fun k => ?_⟩
        rcases k with _ | _ | k
        · exact Or.inl ⟨1, .read, hr, rfl, rfl⟩
        · exact Or.inl ⟨0, .write 1, hw, rfl, rfl⟩
        · simp only [show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ↓reduceIte,
            show ¬ k + 1 + 1 ≤ 1 by omega, show ¬ k + 1 + 1 + 1 ≤ 1 by omega]
          rfl
      · refine LegalAt.const (q₀ := 0) rfl fun k b rb hk hb => ?_
        have := (onObj_restrict.1 hb).2
        exact hz this
    · obtain ⟨-, h | h⟩ := hlate a j r hj
      · exact ⟨1, 0, by simp [h]⟩
      · exact ⟨0, 0, by simp [h]⟩
    · have := (hlate a j r hj).1; omega
    · have := (hlate a j r hj).1; omega

lemma regHist_not_tLinearizable (t : ℕ) : ¬ TLinearizable (fun _ => register) regHist t := by
  rintro ⟨S, hS⟩
  have hj : regHist (4 * t + 1) = some (.res (4 * t) 0) := regHist_eq_res.2 (by omega)
  have hj' : regHist (4 * t + 3) = some (.res (4 * t + 2) 0) := regHist_eq_res.2 (by omega)
  have hbinv : Invoked regHist (4 * t + 2) := invoked_regHist.2 (by omega)
  obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ :=
    hS.rt _ _ _ _ hj (by omega) (by omega) hbinv (hS.complete _ _ _ hj')
  obtain ⟨k2', hk2'⟩ := hS.resp _ _ _ hj' (by omega)
  have := hS.nodup _ _ _ _ _ h2 hk2'
  subst this
  rw [h2] at hk2'; cases hk2'
  obtain ⟨q, -, hq⟩ := hS.legal.legalAt t
  have hw := hq k1
  rw [h1] at hw
  replace hw := hw.onObj (onObj_regHist.2 ⟨by omega, by omega⟩)
  obtain ⟨p, op, hop, hδ⟩ := hw
  obtain ⟨-, -, -, rfl⟩ | ⟨h, -⟩ := regHist_eq_inv.1 hop
  swap; · omega
  have hconst : ∀ m, k1 + 1 + m ≤ k2 → q (k1 + 1 + m) = 1 := by
    intro m
    induction m with
    | zero => intro; exact hδ.2
    | succ m ih =>
      intro hm
      have hidle : Idle regHist t (S (k1 + 1 + m)) := by
        intro c rc hc hct
        have := onObj_regHist.1 hct
        have hc' : c = 4 * t ∨ c = 4 * t + 2 := by omega
        rcases hc' with rfl | rfl
        · have := hS.nodup _ _ _ _ _ hc h1; omega
        · have := hS.nodup _ _ _ _ _ hc h2; omega
      rw [show k1 + 1 + (m + 1) = k1 + 1 + m + 1 by omega, SeqStep.eq_of_idle hidle (hq _)]
      exact ih (by omega)
  have hk2 := hconst (k2 - k1 - 1) (by omega)
  rw [show k1 + 1 + (k2 - k1 - 1) = k2 by omega] at hk2
  have hr := hq k2
  rw [h2] at hr
  replace hr := hr.onObj (onObj_regHist.2 ⟨by omega, by omega⟩)
  obtain ⟨p', op', hop', hδ'⟩ := hr
  obtain ⟨h, -⟩ | ⟨-, -, -, rfl⟩ := regHist_eq_inv.1 hop'
  · omega
  · have := hδ'.1; rw [hk2] at this; cases this

/-- The paper's remark after **Proposition 9**: Proposition 9 fails for infinitely many
objects. In the history `regHist` (registers `R₀, R₁, …`), every `H|R_i` is eventually
linearizable, but `H` is not (it is not `t`-linearizable for any `t`). -/
theorem prop9_false_infinite_objects :
    ∃ H : History (Fin 2) ℕ RegOp ℕ, WellFormed H ∧
      (∀ i, EventuallyLinearizable (fun _ => register) (restrict H i)) ∧
      ¬ EventuallyLinearizable (fun _ => register) H :=
  ⟨regHist, wellFormed_regHist, regHist_restrict_eventuallyLinearizable,
    fun ⟨_, t, ht⟩ => regHist_not_tLinearizable t ht⟩

end Counterexample

end Podc.EventualLinParadox
