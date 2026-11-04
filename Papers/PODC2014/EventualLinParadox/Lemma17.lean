import Papers.PODC2014.EventualLinParadox.Basic

/-!
# Lemma 17: limits of `t`-linearizable fetch&increment histories

Guerraoui, Ruppert. *A Paradox of Eventual Linearizability in Shared Memory.* PODC 2014.

**Lemma 17.** If a history `H` of a fetch&increment object is `t₀`-linearizable for some `t₀`
(e.g. a history of an eventually linearizable implementation) and every finite prefix of `H` is
`t`-linearizable, then `H` is `t`-linearizable.

We follow the paper's proof: operations with a response at a position `≥ t` ("late" operations)
are put at the slot equal to their response value; the remaining slots `E` are filled first by the
operations with a response before `t` (`A1`) and then by the pending operations (`A4`) in the
order of their invocations. The paper's argument for the real-time order between a late
operation `op₁` and a pending operation `op₂` contains a gap (a late operation that is still
pending in the prefix considered by the paper may occupy a slot of `E`); we repair it by
considering a prefix that contains the responses of all late operations invoked before `op₁`'s
response (`count_E_le`).
-/

namespace Podc.EventualLinParadox

section FaiLegal

variable {P : Type} {H : History P Unit Unit ℕ}

/-- In a legal fetch&increment sequential history, the response of an entry is the number of
entries before it. -/
lemma legal_fai_resp {S : SeqHist ℕ} (h : Legal (fun _ => fai) H S) {k a r : ℕ}
    (hk : S k = some (a, r)) : r = Nat.count (fun i => S i ≠ none) k := by
  obtain ⟨hinv, hq⟩ := h
  obtain ⟨q, hq0, hqs⟩ := hq ()
  have step : ∀ k, (S k = none → q (k + 1) = q k) ∧
      ∀ a r, S k = some (a, r) → r = q k ∧ q (k + 1) = q k + 1 := by
    intro k
    refine ⟨fun h0 => ?_, fun a r h1 => ?_⟩
    · have := hqs k; rw [h0] at this; exact this
    · have := hqs k; rw [h1] at this
      obtain ⟨p, x, op, hp⟩ := hinv k a r h1
      exact (SeqStep.onObj this ⟨p, op, hp⟩).choose_spec.choose_spec.2
  have key : ∀ k, q k = Nat.count (fun i => S i ≠ none) k := by
    intro k
    induction k with
    | zero => simpa [fai] using hq0
    | succ k ih =>
      rw [Nat.count_succ]
      cases hS : S k with
      | none => simp [(step k).1 hS, ih]
      | some e =>
        obtain ⟨a, r⟩ := e
        simp [((step k).2 a r hS).2, ih]
  rw [← key]; exact ((step k).2 a r hk).1

lemma legal_fai_lt {S : SeqHist ℕ} (h : Legal (fun _ => fai) H S) {k k' a a' r r' : ℕ}
    (hk : S k = some (a, r)) (hk' : S k' = some (a', r')) (hkk' : k < k') : r < r' := by
  rw [legal_fai_resp h hk, legal_fai_resp h hk']
  exact Nat.count_strict_mono (by simp [hk]) hkk'

lemma legal_fai_slot_eq {S : SeqHist ℕ} (h : Legal (fun _ => fai) H S) {k k' a a' r : ℕ}
    (hk : S k = some (a, r)) (hk' : S k' = some (a', r)) : k = k' := by
  rcases lt_trichotomy k k' with hl | hl | hl
  · exact absurd (legal_fai_lt h hk hk' hl) (lt_irrefl _)
  · exact hl
  · exact absurd (legal_fai_lt h hk' hk hl) (lt_irrefl _)

/-- In a legal fetch&increment sequential history, every value below the response of an entry is
the response of an earlier entry (namely of the `w`-th entry). -/
lemma legal_fai_nth {S : SeqHist ℕ} (h : Legal (fun _ => fai) H S) {k a r w : ℕ}
    (hk : S k = some (a, r)) (hw : w < r) :
    Nat.nth (fun i => S i ≠ none) w < k ∧
      ∃ a', S (Nat.nth (fun i => S i ≠ none) w) = some (a', w) := by
  classical
  rw [legal_fai_resp h hk] at hw
  have hc : ∀ hf : (Set.ofPred fun i => S i ≠ none).Finite, w < hf.toFinset.card :=
    fun hf => lt_of_lt_of_le hw (Nat.count_le_card hf k)
  have h1 := Nat.nth_mem w hc
  have h2 := Nat.count_nth hc
  have h3 := Nat.nth_lt_of_lt_count hw
  obtain ⟨⟨a', r'⟩, he⟩ := Option.ne_none_iff_exists'.1 h1
  refine ⟨h3, a', ?_⟩
  rw [he, legal_fai_resp h he, h2]

/-- A gap-free sequential history whose `k`-th entry has response `k` is legal. -/
lemma legal_fai_of {f : ℕ → ℕ} (hf : ∀ k, Invoked H (f k)) :
    Legal (fun _ => fai) H (fun k => some (f k, k)) := by
  refine ⟨fun k a r hk => ?_, fun x => ⟨id, rfl, fun k => ?_⟩⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, -⟩ := hk; exact hf k
  · obtain ⟨p, y, op, hp⟩ := hf k
    exact Or.inl ⟨p, op, by rw [hp], rfl, rfl⟩

end FaiLegal

section Counting

lemma count_le_of_bound {p : ℕ → Prop} [DecidablePred p] {N : ℕ} (h : ∀ c, p c → c < N)
    (n : ℕ) : Nat.count p n ≤ Nat.count p N := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro x
  simp only [Finset.mem_filter, Finset.mem_range]
  exact fun ⟨_, hx⟩ => ⟨h x hx, hx⟩

lemma count_or_le {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (n : ℕ) :
    Nat.count (fun c => p c ∨ q c) n ≤ Nat.count p n + Nat.count q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.count_succ]
    split_ifs <;> simp_all <;> omega

lemma nth_spec_of_lt_count {p : ℕ → Prop} [DecidablePred p] {k n : ℕ} (h : k < Nat.count p n) :
    p (Nat.nth p k) ∧ Nat.count p (Nat.nth p k) = k ∧ Nat.nth p k < n := by
  have hc : ∀ hf : (Set.ofPred p).Finite, k < hf.toFinset.card :=
    fun hf => lt_of_lt_of_le h (Nat.count_le_card hf n)
  exact ⟨Nat.nth_mem k hc, Nat.count_nth hc, Nat.nth_lt_of_lt_count h⟩

end Counting

section Hist

variable {P : Type} {H : History P Unit Unit ℕ} {t : ℕ}

/-- Operation `a` responds with value `v` at a position `≥ t` (a "late" operation). -/
def LateR (H : History P Unit Unit ℕ) (t a v : ℕ) : Prop := ∃ j, H j = some (.res a v) ∧ t ≤ j

/-- The slot `w` is not the response value of a late operation (the paper's set `E`). -/
def FreeSlot (H : History P Unit Unit ℕ) (t w : ℕ) : Prop := ¬ ∃ b, LateR H t b w

/-- `c` is an operation that is not late (the paper's `A1 ∪ A4`). -/
def NotLate (H : History P Unit Unit ℕ) (t c : ℕ) : Prop := Invoked H c ∧ ¬ ∃ w, LateR H t c w

/-- `c` responds at a position `< t` (the paper's `A1`). -/
def Early (H : History P Unit Unit ℕ) (t c : ℕ) : Prop := ∃ jc r, H jc = some (.res c r) ∧ jc < t

/-- `c` is invoked and never responds (the paper's `A4`). -/
def Pending (H : History P Unit Unit ℕ) (c : ℕ) : Prop := Invoked H c ∧ ¬ Completed H c

lemma resp_unique (hH : WellFormed H) {a j j' r r' : ℕ} (h : H j = some (.res a r))
    (h' : H j' = some (.res a r')) : j = j' ∧ r = r' := by
  have := hH.res_unique a j j' r r' h h'
  subst this
  rw [h] at h'
  cases h'
  exact ⟨rfl, rfl⟩

lemma exists_resp_bound (hH : WellFormed H) (n : ℕ) :
    ∃ m, ∀ c < n, ∀ jc r, H jc = some (.res c r) → jc < m := by
  induction n with
  | zero => exact ⟨0, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    by_cases h : ∃ jn rn, H jn = some (.res n rn)
    · obtain ⟨jn, rn, hn⟩ := h
      refine ⟨max m (jn + 1), fun c hc jc r hjc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · have := hm c hc jc r hjc; omega
      · have := (resp_unique hH hjc hn).1; omega
    · refine ⟨m, fun c hc jc r hjc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact hm c hc jc r hjc
      · exact absurd ⟨jc, r, hjc⟩ h

/-- With finitely many processes, there are finitely many pending operations (at most one per
process). -/
lemma exists_pending_bound [Finite P] (hH : WellFormed H) : ∃ B, ∀ c, Pending H c → c < B := by
  let s : Set ℕ := {c | Pending H c}
  let f : s → P := fun c => Classical.choose c.2.1
  have hf : Function.Injective f := by
    intro c d hcd
    obtain ⟨x, op, hc⟩ := Classical.choose_spec c.2.1
    obtain ⟨x', op', hd⟩ := Classical.choose_spec d.2.1
    have hcd' : Classical.choose c.2.1 = Classical.choose d.2.1 := hcd
    rw [← hcd'] at hd
    rcases lt_trichotomy c.1 d.1 with h | h | h
    · obtain ⟨j, r, -, hj⟩ := hH.seq _ _ _ _ _ _ _ hc hd h
      exact absurd ⟨j, r, hj⟩ c.2.2
    · exact Subtype.ext h
    · obtain ⟨j, r, -, hj⟩ := hH.seq _ _ _ _ _ _ _ hd hc h
      exact absurd ⟨j, r, hj⟩ d.2.2
  have hs : s.Finite := Set.finite_coe_iff.1 (Finite.of_injective f hf)
  obtain ⟨B, hB⟩ := hs.bddAbove
  exact ⟨B + 1, fun c hc => Nat.lt_succ_of_le (hB hc)⟩

lemma early_lt (hH : WellFormed H) {c : ℕ} (h : Early H t c) : c < t := by
  obtain ⟨jc, r, hjc, hlt⟩ := h
  have := (hH.res_inv c jc r hjc).1; omega

lemma early_notLate (hH : WellFormed H) {c : ℕ} (h : Early H t c) : NotLate H t c := by
  obtain ⟨jc, r, hjc, hlt⟩ := h
  refine ⟨(hH.res_inv c jc r hjc).2, fun ⟨w, j, hj, htj⟩ => ?_⟩
  have := (resp_unique hH hjc hj).1; omega

lemma pending_notLate {c : ℕ} (h : Pending H c) : NotLate H t c :=
  ⟨h.1, fun ⟨w, j, hj, _⟩ => h.2 ⟨j, w, hj⟩⟩

lemma notLate_cases {c : ℕ} (h : NotLate H t c) : Early H t c ∨ Pending H c := by
  by_cases hc : Completed H c
  · obtain ⟨jc, r, hjc⟩ := hc
    by_cases htj : t ≤ jc
    · exact absurd ⟨r, jc, hjc, htj⟩ h.2
    · exact Or.inl ⟨jc, r, hjc, by omega⟩
  · exact Or.inr ⟨h.1, hc⟩

lemma count_notLate_le [DecidablePred (NotLate H t)] [DecidablePred (Early H t)]
    [DecidablePred (Pending H)] (n : ℕ) :
    Nat.count (NotLate H t) n ≤ Nat.count (Early H t) n + Nat.count (Pending H) n := by
  classical
  calc Nat.count (NotLate H t) n ≤ Nat.count (fun c => Early H t c ∨ Pending H c) n :=
        Nat.count_mono_left fun c _ hc => notLate_cases hc
    _ ≤ _ := count_or_le n

/-- If finitely many responses occur, the history is one of its prefixes. -/
lemma exists_eq_take [Finite P] (hH : WellFormed H) {M : ℕ}
    (hM : ∀ j, M ≤ j → ∀ a r, H j ≠ some (.res a r)) : ∃ N, H = take H N := by
  obtain ⟨B, hB⟩ := exists_pending_bound hH
  refine ⟨max M B, funext fun i => ?_⟩
  rw [take_apply]
  split_ifs with hi
  · rfl
  · cases hHi : H i with
    | none => rfl
    | some e =>
      cases e with
      | inv p x op =>
        have : i < B := hB i ⟨⟨p, x, op, hHi⟩, fun ⟨jc, r, hjc⟩ => by
          have := (hH.res_inv i jc r hjc).1
          exact hM jc (by omega) i r hjc⟩
        omega
      | res a r => exact absurd hHi (hM i (by omega) a r)

end Hist

section Prefix

variable {P : Type} {H : History P Unit Unit ℕ} {t : ℕ}

/-- Two late operations with values `v`, `w`, the first responding before the second is invoked,
satisfy `v < w` (a prefix containing both responses is `t`-linearizable). -/
lemma late_lt (hH : WellFormed H) (hpre : ∀ m, TLinearizable (fun _ => fai) (take H m) t)
    {a b v w ja jb : ℕ} (ha : H ja = some (.res a v)) (hta : t ≤ ja)
    (hb : H jb = some (.res b w)) (htb : t ≤ jb) (hab : ja < b) : v < w := by
  obtain ⟨S, hS⟩ := hpre (max ja jb + 1)
  have ha' := (take_eq_some H).2 ⟨(by omega : ja < max ja jb + 1), ha⟩
  have hb' := (take_eq_some H).2 ⟨(by omega : jb < max ja jb + 1), hb⟩
  obtain ⟨ka, hka⟩ := hS.resp a ja v ha' hta
  obtain ⟨kb, hkb⟩ := hS.resp b jb w hb' htb
  have hbinv := hH.res_inv b jb w hb
  obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ := hS.rt a b ja v ha' hta hab
    ((invoked_take H).2 ⟨by omega, hbinv.2⟩) ⟨kb, w, hkb⟩
  have e1 := hS.nodup _ _ _ _ _ h1 hka
  have e2 := hS.nodup _ _ _ _ _ h2 hkb
  subst e1 e2
  exact legal_fai_lt hS.legal hka hkb h12

/-- Distinct late operations return distinct values. -/
lemma late_inj (hpre : ∀ m, TLinearizable (fun _ => fai) (take H m) t)
    {a b v : ℕ} (ha : LateR H t a v) (hb : LateR H t b v) : a = b := by
  obtain ⟨ja, ha, hta⟩ := ha
  obtain ⟨jb, hb, htb⟩ := hb
  obtain ⟨S, hS⟩ := hpre (max ja jb + 1)
  have ha' := (take_eq_some H).2 ⟨(by omega : ja < max ja jb + 1), ha⟩
  have hb' := (take_eq_some H).2 ⟨(by omega : jb < max ja jb + 1), hb⟩
  obtain ⟨ka, hka⟩ := hS.resp a ja v ha' hta
  obtain ⟨kb, hkb⟩ := hS.resp b jb v hb' htb
  have := legal_fai_slot_eq hS.legal hka hkb
  subst this
  rw [hka] at hkb
  simp only [Option.some.injEq, Prod.mk.injEq] at hkb
  exact hkb.1

/-- The key counting step (repairing the paper's argument): if a late operation `a` responds
with `v` at position `j`, then the free slots below `v` are at most the not-late operations
invoked before `j`. We use a prefix containing `a`'s response and the responses of all late
operations invoked before `j`: in its `t`-linearization, the entries before `a` are invoked
before `j` (real-time order) and the late ones among them sit at their own values, so the
entries with a free value are not late. -/
lemma count_free_le (hH : WellFormed H) (hpre : ∀ m, TLinearizable (fun _ => fai) (take H m) t)
    [DecidablePred (FreeSlot H t)] [DecidablePred (NotLate H t)]
    {a v j : ℕ} (ha : H j = some (.res a v)) (htj : t ≤ j) :
    Nat.count (FreeSlot H t) v ≤ Nat.count (NotLate H t) j := by
  classical
  obtain ⟨m, hm⟩ := exists_resp_bound hH j
  obtain ⟨S, hS⟩ := hpre (max m (j + 1))
  have haj := (take_eq_some H).2 ⟨(by omega : j < max m (j + 1)), ha⟩
  obtain ⟨ka, hka⟩ := hS.resp a j v haj htj
  let g : ℕ → ℕ := fun w => ((S (Nat.nth (fun i => S i ≠ none) w)).map Prod.fst).getD 0
  have hg : ∀ w < v, Nat.nth (fun i => S i ≠ none) w < ka ∧
      S (Nat.nth (fun i => S i ≠ none) w) = some (g w, w) := by
    intro w hw
    obtain ⟨hlt, a', he⟩ := legal_fai_nth hS.legal hka hw
    refine ⟨hlt, ?_⟩
    rw [he]
    simp [g, he]
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  refine Finset.card_le_card_of_injOn g (fun w hw => ?_) (fun w hw w' hw' hww' => ?_)
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hw
    obtain ⟨hwv, hfree⟩ := hw
    obtain ⟨hlt, he⟩ := hg w hwv
    set k' := Nat.nth (fun i => S i ≠ none) w
    have hinv := (invoked_take H).1 (hS.legal.1 _ _ _ he)
    have hgj : g w < j := by
      by_contra hge
      have hne : g w ≠ j := by
        rintro heq
        obtain ⟨p, x, op, hp⟩ := hinv.2
        rw [heq, ha] at hp; cases hp
      obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ :=
        hS.rt a (g w) j v haj htj (by omega) ((invoked_take H).2 hinv) ⟨k', w, he⟩
      have e1 := hS.nodup _ _ _ _ _ h1 hka
      have e2 := hS.nodup _ _ _ _ _ h2 he
      omega
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨hgj, hinv.2, fun ⟨w', jc, hjc, htjc⟩ => hfree ⟨g w, ?_⟩⟩
    have hjcm := hm (g w) hgj jc w' hjc
    obtain ⟨k'', hk''⟩ :=
      hS.resp (g w) jc w' ((take_eq_some H).2 ⟨by omega, hjc⟩) htjc
    have := hS.nodup _ _ _ _ _ hk'' he
    rw [this, he] at hk''
    simp only [Option.some.injEq, Prod.mk.injEq] at hk''
    rw [← hk''.2] at hjc
    exact ⟨jc, hjc, htjc⟩
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hw hw'
    obtain ⟨-, he⟩ := hg w hw.1
    obtain ⟨-, he'⟩ := hg w' hw'.1
    rw [hww'] at he
    have := hS.nodup _ _ _ _ _ he he'
    rw [this, he'] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    exact he.2.symm

/-- With infinitely many responses, late operations return arbitrarily large values. -/
lemma late_unbounded (hH : WellFormed H) (hpre : ∀ m, TLinearizable (fun _ => fai) (take H m) t)
    (hinf : ∀ M, ∃ j, M ≤ j ∧ ∃ a r, H j = some (.res a r)) (V : ℕ) :
    ∃ a v j, H j = some (.res a v) ∧ t ≤ j ∧ V ≤ v := by
  by_contra hcon
  push Not at hcon
  let L : Set ℕ := {j | t ≤ j ∧ ∃ a r, H j = some (.res a r)}
  have hL : L.Infinite := Set.infinite_of_forall_exists_gt fun n => by
    obtain ⟨j, hj, hres⟩ := hinf (max t (n + 1))
    exact ⟨j, ⟨by omega, hres⟩, by omega⟩
  let g : ℕ → ℕ := fun j => match H j with
    | some (.res _ r) => r
    | _ => 0
  have hgj : ∀ j a r, H j = some (.res a r) → g j = r := fun j a r h => by simp [g, h]
  have hinj : Set.InjOn g L := by
    rintro j ⟨htj, a, r, hj⟩ j' ⟨htj', a', r', hj'⟩ hgg
    rw [hgj j a r hj, hgj j' a' r' hj'] at hgg
    subst hgg
    have := late_inj hpre ⟨j, hj, htj⟩ ⟨j', hj', htj'⟩
    subst this
    exact (resp_unique hH hj hj').1
  have hmaps : Set.MapsTo g L (Set.Iio V) := by
    rintro j ⟨htj, a, r, hj⟩
    rw [Set.mem_Iio, hgj j a r hj]
    exact hcon a r j hj htj
  exact Set.infinite_of_injOn_mapsTo hinj hmaps hL (Set.finite_Iio V)

end Prefix

section Main

variable {P : Type} {H : History P Unit Unit ℕ} {t : ℕ}

open Classical in
/-- The response of operation `c` in the sequential history `S` (junk `0` if absent). -/
noncomputable def respOf (S : SeqHist ℕ) (c : ℕ) : ℕ :=
  if h : ∃ k r, S k = some (c, r) then Classical.choose (Classical.choose_spec h) else 0

lemma respOf_eq {S : SeqHist ℕ} (hS : S.Nodup) {k c r : ℕ} (hk : S k = some (c, r)) :
    respOf S c = r := by
  have h : ∃ k r, S k = some (c, r) := ⟨k, r, hk⟩
  unfold respOf
  rw [dite_eq_left h]
  have hs := Classical.choose_spec (Classical.choose_spec h)
  have e : S (Classical.choose h) = S k := congrArg S (hS _ _ _ _ _ hs hk)
  rw [hs, hk] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  exact e.2

open Classical in
/-- The value returned by a late operation `c` (junk `0` otherwise). -/
noncomputable def lateVal (H : History P Unit Unit ℕ) (t c : ℕ) : ℕ :=
  if h : ∃ v, LateR H t c v then Classical.choose h else 0

lemma lateVal_eq (hH : WellFormed H) {c v : ℕ} (h : LateR H t c v) : lateVal H t c = v := by
  have h' : ∃ v, LateR H t c v := ⟨v, h⟩
  unfold lateVal
  rw [dite_eq_left h']
  obtain ⟨j', hj', -⟩ := Classical.choose_spec h'
  obtain ⟨j, hj, -⟩ := h
  exact (resp_unique hH hj' hj).2

/-- The paper's inequality `|A1| ≤ |E|` (in the form: some initial segment of `E` has at least
`|A1|` elements), obtained from a `t₀`-linearization `S'` of `H` with `t ≤ t₀`: `S'` puts the
operations responding before `t₀` (`A1 ∪ A2`) at distinct slots that are not values of
operations responding after `t₀` (`A3`); those slots are free or values of `A2`. -/
lemma exists_count_early_le (hH : WellFormed H) {t₀ : ℕ} (htt₀ : t ≤ t₀) {S' : SeqHist ℕ}
    (hS' : IsTLin (fun _ => fai) H t₀ S') [DecidablePred (Early H t)]
    [DecidablePred (FreeSlot H t)] :
    ∃ V, Nat.count (Early H t) t ≤ Nat.count (FreeSlot H t) V := by
  classical
  let ρ := respOf S'
  let V := (Finset.range t₀).sup (fun c => ρ c + 1)
  let A2 : ℕ → Prop := fun c => ∃ jc r, H jc = some (.res c r) ∧ t ≤ jc ∧ jc < t₀
  let A1s := (Finset.range t).filter (Early H t)
  let A2s := (Finset.range t₀).filter A2
  let T := (Finset.range V).filter (fun w => ¬ ∃ b, LateR H t₀ b w)
  have hslot : ∀ c jc r, H jc = some (.res c r) → jc < t₀ →
      c < t₀ ∧ ∃ k, S' k = some (c, ρ c) := by
    intro c jc r hjc hlt
    have hc := (hH.res_inv c jc r hjc).1
    obtain ⟨k, r', hk⟩ := hS'.complete c jc r hjc
    exact ⟨by omega, k, by rw [hk, show ρ c = r' from respOf_eq hS'.nodup hk]⟩
  have hearly : ∀ c ∈ A1s ∪ A2s, ∃ jc r, H jc = some (.res c r) ∧ jc < t₀ := by
    intro c hc
    simp only [A1s, A2s, A2, Early, Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hc
    rcases hc with ⟨-, jc, r, hjc, hlt⟩ | ⟨-, jc, r, hjc, -, hlt⟩
    · exact ⟨jc, r, hjc, by omega⟩
    · exact ⟨jc, r, hjc, hlt⟩
  have h1 : (A1s ∪ A2s).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn ρ (fun c hc => ?_) (fun c hc c' hc' hcc' => ?_)
    · obtain ⟨jc, r, hjc, hlt⟩ := hearly c hc
      obtain ⟨hct, k, hk⟩ := hslot c jc r hjc hlt
      simp only [T, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      refine ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Finset.le_sup (f := fun c => ρ c + 1) (Finset.mem_range.2 hct)), ?_⟩
      rintro ⟨b, jb, hjb, htjb⟩
      obtain ⟨kb, hkb⟩ := hS'.resp b jb (ρ c) hjb htjb
      have := legal_fai_slot_eq hS'.legal hk hkb
      subst this
      rw [hk] at hkb
      simp only [Option.some.injEq, Prod.mk.injEq] at hkb
      rw [← hkb.1] at hjb
      have := (resp_unique hH hjc hjb).1
      omega
    · obtain ⟨jc, r, hjc, hlt⟩ := hearly c hc
      obtain ⟨-, k, hk⟩ := hslot c jc r hjc hlt
      obtain ⟨jc', r', hjc', hlt'⟩ := hearly c' hc'
      obtain ⟨-, k', hk'⟩ := hslot c' jc' r' hjc' hlt'
      rw [hcc'] at hk
      have := legal_fai_slot_eq hS'.legal hk hk'
      subst this
      rw [hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      exact hk'.1
  have hdisj : Disjoint A1s A2s := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [A1s, A2s, A2, Early, Finset.mem_filter, Finset.mem_range] at hc1 hc2
    obtain ⟨-, jc, r, hjc, hlt⟩ := hc1
    obtain ⟨-, jc', r', hjc', hle, -⟩ := hc2
    have := (resp_unique hH hjc hjc').1
    omega
  have h2 : T ⊆ (Finset.range V).filter (FreeSlot H t) ∪ A2s.image (lateVal H t) := by
    intro w hw
    simp only [T, Finset.mem_filter, Finset.mem_range] at hw
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    by_cases hfree : FreeSlot H t w
    · exact Or.inl ⟨hw.1, hfree⟩
    · right
      obtain ⟨b, jb, hjb, htjb⟩ := not_not.1 hfree
      have hjb0 : jb < t₀ := by
        by_contra hge
        exact hw.2 ⟨b, jb, hjb, by omega⟩
      have hb := (hH.res_inv b jb w hjb).1
      refine ⟨b, ?_, lateVal_eq hH ⟨jb, hjb, htjb⟩⟩
      simp only [A2s, A2, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, jb, w, hjb, htjb, hjb0⟩
  refine ⟨V, ?_⟩
  have h3 := Finset.card_le_card h2
  have h4 := Finset.card_union_le ((Finset.range V).filter (FreeSlot H t))
    (A2s.image (lateVal H t))
  have h5 := Finset.card_image_le (s := A2s) (f := lateVal H t)
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have e1 : Nat.count (Early H t) t = A1s.card := by rw [Nat.count_eq_card_filter_range]
  have e2 : Nat.count (FreeSlot H t) V = ((Finset.range V).filter (FreeSlot H t)).card := by
    rw [Nat.count_eq_card_filter_range]
  omega

open Classical in
/-- The paper's construction of the `t`-linearization `S` (gap-free, slot `k` has response `k`):
slot `v` holds the late operation returning `v`; the `i`-th free slot holds the `i`-th
operation of `A1` for `i < |A1|`, and the `(i - |A1|)`-th pending operation otherwise.
Hypotheses: late values are unbounded, pending operations are bounded (finitely many), and
`|A1| ≤ |E|`. -/
lemma tLinearizable_of_bounds (hH : WellFormed H)
    (hpre : ∀ m, TLinearizable (fun _ => fai) (take H m) t)
    (hunb : ∀ V, ∃ a v j, H j = some (.res a v) ∧ t ≤ j ∧ V ≤ v)
    {B : ℕ} (hB : ∀ c, Pending H c → c < B)
    {V₀ : ℕ} (hV₀ : Nat.count (Early H t) t ≤ Nat.count (FreeSlot H t) V₀) :
    TLinearizable (fun _ => fai) H t := by
  set n1 := Nat.count (Early H t) t with hn1
  have hEarly_le : ∀ n, Nat.count (Early H t) n ≤ n1 :=
    count_le_of_bound (fun c hc => early_lt hH hc)
  have hNL : ∀ n, Nat.count (NotLate H t) n ≤ n1 + Nat.count (Pending H) B := fun n =>
    (count_notLate_le n).trans (Nat.add_le_add (hEarly_le n) (count_le_of_bound hB n))
  have hfree_lt : ∀ k, FreeSlot H t k →
      Nat.count (FreeSlot H t) k < n1 + Nat.count (Pending H) B := by
    intro k hk
    obtain ⟨a, v, j, ha, htj, hv⟩ := hunb (k + 1)
    calc Nat.count (FreeSlot H t) k < Nat.count (FreeSlot H t) (k + 1) :=
          Nat.count_lt_count_succ_iff.2 hk
      _ ≤ Nat.count (FreeSlot H t) v := Nat.count_monotone _ hv
      _ ≤ Nat.count (NotLate H t) j := count_free_le hH hpre ha htj
      _ ≤ _ := hNL j
  -- the operation at slot `k`
  let opE : ℕ → ℕ := fun i =>
    if i < n1 then Nat.nth (Early H t) i else Nat.nth (Pending H) (i - n1)
  let f : ℕ → ℕ := fun k =>
    if h : ∃ b, LateR H t b k then Classical.choose h else opE (Nat.count (FreeSlot H t) k)
  have hf_late : ∀ b k, LateR H t b k → f k = b := by
    intro b k hb
    have h : ∃ b, LateR H t b k := ⟨b, hb⟩
    simp only [f, dite_eq_left h]
    exact late_inj hpre (Classical.choose_spec h) hb
  have hf_free : ∀ k, FreeSlot H t k →
      (Nat.count (FreeSlot H t) k < n1 →
        Early H t (f k) ∧ Nat.count (Early H t) (f k) = Nat.count (FreeSlot H t) k) ∧
      (n1 ≤ Nat.count (FreeSlot H t) k →
        Pending H (f k) ∧ n1 + Nat.count (Pending H) (f k) = Nat.count (FreeSlot H t) k) := by
    intro k hk
    have hfk : f k = opE (Nat.count (FreeSlot H t) k) := dite_eq_right hk
    rw [hfk]
    refine ⟨fun hlt => ?_, fun hge => ?_⟩
    · simp only [opE, ite_eq_left hlt]
      obtain ⟨h1, h2, -⟩ := nth_spec_of_lt_count hlt
      exact ⟨h1, h2⟩
    · simp only [opE, ite_eq_right (not_lt.2 hge)]
      have hlt : Nat.count (FreeSlot H t) k - n1 < Nat.count (Pending H) B := by
        have := hfree_lt k hk; omega
      obtain ⟨h1, h2, -⟩ := nth_spec_of_lt_count hlt
      exact ⟨h1, by omega⟩
  have hf_notLate : ∀ k, FreeSlot H t k → NotLate H t (f k) := by
    intro k hk
    by_cases hlt : Nat.count (FreeSlot H t) k < n1
    · exact early_notLate hH ((hf_free k hk).1 hlt).1
    · exact pending_notLate ((hf_free k hk).2 (not_lt.1 hlt)).1
  have hf_inv : ∀ k, Invoked H (f k) := by
    intro k
    by_cases hk : FreeSlot H t k
    · exact (hf_notLate k hk).1
    · obtain ⟨b, j, hj, htj⟩ := not_not.1 hk
      rw [hf_late b k ⟨j, hj, htj⟩]
      exact (hH.res_inv b j k hj).2
  have hrank : ∀ k k', FreeSlot H t k → FreeSlot H t k' → f k = f k' → k = k' := by
    intro k k' hk hk' hkk'
    apply Nat.count_injective hk hk'
    rcases lt_or_ge (Nat.count (FreeSlot H t) k) n1 with h | h <;>
    rcases lt_or_ge (Nat.count (FreeSlot H t) k') n1 with h' | h'
    · rw [← ((hf_free k hk).1 h).2, ← ((hf_free k' hk').1 h').2, hkk']
    · exfalso
      have e := ((hf_free k hk).1 h).1
      have p := ((hf_free k' hk').2 h').1
      rw [hkk'] at e
      obtain ⟨jc, r, hjc, -⟩ := e
      exact p.2 ⟨jc, r, hjc⟩
    · exfalso
      have e := ((hf_free k' hk').1 h').1
      have p := ((hf_free k hk).2 h).1
      rw [← hkk'] at e
      obtain ⟨jc, r, hjc, -⟩ := e
      exact p.2 ⟨jc, r, hjc⟩
    · have e := ((hf_free k hk).2 h).2
      have e' := ((hf_free k' hk').2 h').2
      rw [hkk'] at e
      omega
  have hf_inj : ∀ k k', f k = f k' → k = k' := by
    intro k k' hkk'
    by_cases hk : FreeSlot H t k <;> by_cases hk' : FreeSlot H t k'
    · exact hrank k k' hk hk' hkk'
    · exfalso
      obtain ⟨b, hb⟩ := not_not.1 hk'
      refine (hf_notLate k hk).2 ⟨k', ?_⟩
      rw [hkk', hf_late b k' hb]; exact hb
    · exfalso
      obtain ⟨b, hb⟩ := not_not.1 hk
      refine (hf_notLate k' hk').2 ⟨k, ?_⟩
      rw [← hkk', hf_late b k hb]; exact hb
    · obtain ⟨b, hb⟩ := not_not.1 hk
      obtain ⟨b', hb'⟩ := not_not.1 hk'
      have e := hf_late b k hb
      rw [hkk', hf_late b' k' hb'] at e
      subst e
      rw [← lateVal_eq hH hb, ← lateVal_eq hH hb']
  refine ⟨fun k => some (f k, k), ⟨fun k k' a r r' hk hk' => ?_, legal_fai_of hf_inv,
    fun a j r hj => ?_, fun a b j r hj htj hjb hbinv hbmem => ?_, fun a j r hj htj => ?_⟩⟩
  · -- nodup
    simp only [Option.some.injEq, Prod.mk.injEq] at hk hk'
    exact hf_inj k k' (hk.1.trans hk'.1.symm)
  · -- every completed operation is in `S`
    by_cases htj : t ≤ j
    · exact ⟨r, r, by simp only [hf_late a r ⟨j, hj, htj⟩]⟩
    · have hea : Early H t a := ⟨j, r, hj, by omega⟩
      have hi : Nat.count (Early H t) a < n1 := Nat.count_strict_mono hea (early_lt hH hea)
      obtain ⟨hk1, hk2, -⟩ := nth_spec_of_lt_count (lt_of_lt_of_le hi hV₀)
      have := (hf_free _ hk1).1 (by rw [hk2]; exact hi)
      have hfa : f (Nat.nth (FreeSlot H t) (Nat.count (Early H t) a)) = a :=
        Nat.count_injective this.1 hea (by rw [this.2, hk2])
      exact ⟨Nat.nth (FreeSlot H t) (Nat.count (Early H t) a),
        Nat.nth (FreeSlot H t) (Nat.count (Early H t) a), by simp only [hfa]⟩
  · -- real-time order
    obtain ⟨kb, rb, hkb⟩ := hbmem
    simp only [Option.some.injEq, Prod.mk.injEq] at hkb
    obtain ⟨hfb, hrb⟩ := hkb
    subst hrb
    refine ⟨r, kb, r, kb, ?_, by simp only [hf_late a r ⟨j, hj, htj⟩], by simp only [hfb]⟩
    by_cases hk : FreeSlot H t kb
    · rcases lt_or_ge (Nat.count (FreeSlot H t) kb) n1 with h | h
      · exfalso
        obtain ⟨jb, rb, hjb', hlt⟩ := ((hf_free kb hk).1 h).1
        rw [hfb] at hjb'
        have := (hH.res_inv b jb rb hjb').1
        omega
      · obtain ⟨hp, hc⟩ := (hf_free kb hk).2 h
        rw [hfb] at hp hc
        have hr : ¬ FreeSlot H t r := fun hr => hr ⟨a, j, hj, htj⟩
        have c1 := count_free_le hH hpre hj htj
        have c2 := Nat.count_monotone (NotLate H t) hjb.le
        have c3 := count_notLate_le (H := H) (t := t) b
        have c4 := hEarly_le b
        by_contra hle
        rcases (not_lt.1 hle).lt_or_eq with hlt | heq
        · have := Nat.count_strict_mono hk hlt; omega
        · subst heq; exact hr hk
    · obtain ⟨b', jb, hjb', htjb⟩ := not_not.1 hk
      have := hf_late b' kb ⟨jb, hjb', htjb⟩
      rw [hfb] at this
      subst this
      exact late_lt hH hpre hj htj hjb' htjb hjb
  · -- late operations keep their responses
    exact ⟨r, by simp only [hf_late a r ⟨j, hj, htj⟩]⟩

end Main

/-- **Lemma 17** of [Guerraoui–Ruppert, PODC 2014]. Let `H` be a well-formed history of a
fetch&increment object (finitely many processes) that is `t₀`-linearizable for some `t₀` (the
paper: `H` is an infinite history of an eventually linearizable implementation). If every finite
prefix of `H` is `t`-linearizable, then `H` is `t`-linearizable.

(The paper assumes `t > 0` and `H` infinite; neither is needed. The hypothesis `h₀` cannot be
dropped: `t`-linearizability is not a safety property, Section 3.2.) -/
theorem lemma17 {P : Type} [Finite P] {H : History P Unit Unit ℕ} (hH : WellFormed H) {t t₀ : ℕ}
    (h₀ : TLinearizable (fun _ => fai) H t₀)
    (hpre : ∀ m, TLinearizable (fun _ => fai) (take H m) t) :
    TLinearizable (fun _ => fai) H t := by
  classical
  rcases le_total t₀ t with ht | ht
  · exact h₀.mono ht
  by_cases hinf : ∀ M, ∃ j, M ≤ j ∧ ∃ a r, H j = some (.res a r)
  · obtain ⟨S', hS'⟩ := h₀
    obtain ⟨B, hB⟩ := exists_pending_bound hH
    obtain ⟨V₀, hV₀⟩ := exists_count_early_le hH ht hS'
    exact tLinearizable_of_bounds hH hpre (late_unbounded hH hpre hinf) hB hV₀
  · push Not at hinf
    obtain ⟨M, hM⟩ := hinf
    obtain ⟨N, hN⟩ := exists_eq_take hH hM
    rw [hN]
    exact hpre N

end Podc.EventualLinParadox
