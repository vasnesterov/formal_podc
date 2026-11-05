import Papers.PODC2020.StoreCollectChurn.Snapshot

/-!
# Theorem 8 of the paper, complexity half: the number of collects of a scan

The termination paragraph before Theorem 8: a double collect of a scan `sop_q` that neither
succeeds (Line 75) nor borrows (Line 77) is caused by an update `uop_p` that is observed by the
second collect but not by the first; `uop_p` is still pending at the time `t` at which the
Line-71 store of `sop_q` completes (its `ACK`), and distinct unsuccessful double collects are
caused by updates of distinct nodes.  Hence a scan performs at most `n + 2` collects (one Line-72
collect, at most `n` unsuccessful double collects and one final successful or borrowing one), where
`n` is the number of nodes with an `UPDATE` pending at `t` (`theorem8_collects`).

Positions: `st` is the position of the Line-71 store of `q` (`q`'s program counter is at Line 71,
`PC.scStore emb`, just before `st`), `t` the position of its `ACK` (`NextE E st t`).  We count the
collect responses of `q` strictly between `t` and any `j` such that `q` has no high-level event
(invocation or response) strictly between `t` and `j`; all of them belong to the scan (taking `j`
to be the position of the scan's response gives all collects of the scan).
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P]

section Defs

variable (E : List (Ev P V))

/-- Node `p` has an `UPDATE` pending at position `t`: it was invoked at some `h < t` and `p` has
no response strictly between `h` and `t`. -/
def PendingUpd (t : ℕ) (p : P) : Prop :=
  ∃ h v, h < t ∧ E[h]? = some (.hinv p (.update v)) ∧
    ∀ m r, h < m → m < t → E[m]? ≠ some (.hret p r)

open Classical in
/-- The nodes with an `UPDATE` pending at position `t` (a `Finset`: only the finitely many nodes
taking steps in `E` can have one). -/
noncomputable def pendSet (t : ℕ) : Finset P := (nodes E).filter (PendingUpd E t)

open Classical in
/-- Number of collect responses (`RETURN_q(V)`) of node `q` strictly between positions `a`
and `b`. -/
noncomputable def colCount (q : P) (a b : ℕ) : ℕ :=
  ((Finset.Ioo a b).filter fun k => ∃ W, E[k]? = some (.sc (.ret q W))).card

end Defs

variable {E : List (Ev P V)} {pk : Pick P V}

open Classical in
lemma colCount_succ (q : P) {a k : ℕ} (hak : a < k) :
    colCount E q a (k + 1) =
      colCount E q a k + (if ∃ W, E[k]? = some (.sc (.ret q W)) then 1 else 0) := by
  classical
  have hI : Finset.Ioo a (k + 1) = insert k (Finset.Ioo a k) := by
    ext m; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
  unfold colCount
  rw [hI, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma colCount_le_of_length (q : P) (a j : ℕ) :
    colCount E q a j ≤ colCount E q a (min j E.length) := by
  classical
  unfold colCount
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_Ioo] at hm ⊢
  obtain ⟨⟨h1, h2⟩, W, hW⟩ := hm
  have : m < E.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hW; cases hW
  exact ⟨⟨h1, by omega⟩, W, hW⟩

lemma lt_length_of_getElem? {i : ℕ} {e : Ev P V} (h : E[i]? = some e) : i < E.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h

/-- Between two invocations of `p` there is a response of `p`. -/
lemma exists_hret_between (hrun : run pk E ≠ none) {h h₂ : ℕ} {p : P} {o o₂ : HOp V}
    (hh : E[h]? = some (.hinv p o)) (hh₂ : E[h₂]? = some (.hinv p o₂)) (hlt : h < h₂) :
    ∃ m r, h < m ∧ m < h₂ ∧ E[m]? = some (.hret p r) := by
  have c1 := count_at_hinv hrun hh
  have c2 := count_at_hinv hrun hh₂
  have c3 := fIdx_lt (invG p) hh (invG_hinv _ _) hlt
  by_contra hc
  push Not at hc
  have : fIdx (retG p) E h = fIdx (retG p) E h₂ := by
    apply fIdx_eq_of_none _ hlt.le
    intro m hm1 hm2 e he
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hm1
    · rw [hh] at he; cases he; simp
    · rcases hr : retG p e with _ | r
      · rfl
      · rw [retG_eq_some hr] at he; exact absurd he (hc m r hm1 hm2)
  omega

/-- **The unsuccessful double collect** (termination paragraph before Theorem 8).  Let the scan
of `q` store `x₀` at `st` (Line 71), with `ACK` at `t`, and let `q` store nothing else before the
collect `(ic, k)` returns.  If two collects `(i₁, j₁)` and `(ic, k)` of `q`, both invoked after `t`,
form a double collect that neither succeeds nor borrows, then some node `p` has an update pending
at `t`, observed by the second collect but not by the first: in terms of update counts,
`usq (V₁ p) < updCnt E t p ≤ usq (W p)` (the pending update is `p`'s `updCnt E t p`-th). -/
lemma fail_attr (hrun : run pk E ≠ none) (hreg : Regular (scSched E)) {q : P}
    {st t i₁ j₁ ic k : ℕ} {x₀ : SCVal P V} {V₁ W : SCView P V}
    (hst : StE E st q x₀) (hnext : NextE E st t)
    (hnoSt : ∀ a y, st < a → a < k → ¬ StE E a q y)
    (h1 : ColE E i₁ j₁ q V₁) (h2 : ColE E ic k q W) (ht : t < i₁) (hj : j₁ < ic)
    (hne : ¬ ∀ r, rU W r = rU V₁ r)
    (hnb : ∀ r y, W r = some y → y.scounts q ≠ some x₀.ssqno) :
    ∃ p, usq (V₁ p) < updCnt E t p ∧ updCnt E t p ≤ usq (W p) ∧ PendingUpd E t p := by
  have hp := past hrun hreg
  obtain ⟨p, hpne⟩ : ∃ p, rU W p ≠ rU V₁ p := by push Not at hne; exact hne
  have hle := usq_le_of_before hrun hreg h1 h2 hj p
  have hlt : usq (V₁ p) < usq (W p) := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso; apply hpne; rw [rU_eq hrun hreg hp h2, rU_eq hrun hreg hp h1, h]
  obtain ⟨y, hy⟩ : ∃ y, W p = some y := by
    rcases hW : W p with _ | y
    · rw [hW] at hlt; simp [usq] at hlt
    · exact ⟨y, rfl⟩
  have hK : usq (W p) = y.usqno := by rw [hy]; rfl
  obtain ⟨a, hak, hay, -⟩ := reg1_some hreg h2 hy
  have haL : a < E.length := lt_length_of_getElem? hay
  have hf := hp.1 a haL p y hay
  obtain ⟨l', l, WL, hL, hla, hsc, -, h, v, hhl, hh, hcnt⟩ := hf.ok.2.2 (by omega)
  have hack := next_of_store hrun hst hnext
  have htk : t < k := by have := h1.2.2.1; have := h2.2.2.1; omega
  -- (1) the Line-79 collect of `p` was invoked before `t`
  have hl't : l' < t := by
    by_contra hc
    have hne' : l' ≠ t := by
      intro e; subst e; rw [hL.1] at hack; cases hack
    have htl : t < l' := by omega
    rcases hWq : WL q with _ | z
    · exact reg1_none hreg hL hWq ⟨st, t, ⟨⟨x₀, hst⟩, hnext⟩, htl⟩
    · obtain ⟨az, hazl, haz, hno⟩ := reg1_some hreg hL hWq
      rcases lt_trichotomy az st with h' | rfl | h'
      · exact hno ⟨st, t, h', ⟨⟨x₀, hst⟩, hnext⟩, htl⟩
      · have : z = x₀ := by
          rw [StE] at haz hst; rw [haz] at hst; simpa using hst
        subst this
        apply hnb p y hy
        rw [hsc]; simp [ssqVec, hWq]
      · exact hnoSt az z h' (by omega) haz
  -- (2) the update of `p` invoked at `h` is still pending at `t`
  have hpend : ∀ m r, h < m → m < t → E[m]? ≠ some (.hret p r) := by
    classical
    by_contra hc
    push Not at hc
    have hc' : ∃ m, ∃ r, h < m ∧ m < t ∧ E[m]? = some (.hret p r) := by
      obtain ⟨m, r, h1, h2, h3⟩ := hc; exact ⟨m, r, h1, h2, h3⟩
    obtain ⟨r, hm1, hm2, hm3⟩ := Nat.find_spec hc'
    have hmL := lt_length_of_getElem? hm3
    obtain ⟨h', hh'm, hH', hcase⟩ := hp.2 _ hmL p r hm3
    have hinv' : ∃ o, E[h']? = some (.hinv p o) := by
      rcases hcase with ⟨e, -⟩ | ⟨v', e, -⟩
      · exact ⟨_, e⟩
      · exact ⟨_, e⟩
    rcases lt_trichotomy h' h with c | rfl | c
    · obtain ⟨cc, hcc⟩ := hH' h c hm1 _ hh rfl
      cases hcc
    · rcases hcase with ⟨e, -⟩ | ⟨v', -, -, a₂, b₂, x₂, -, hb₂, ha₂, hab₂, hx₂⟩
      · rw [hh] at e; cases e
      · have e1 := usq_ge_of_storeDone hrun hreg ha₂ hab₂ (by omega : b₂ < i₁) h1
        have e2 : updCnt E (h' + 1) p ≤ updCnt E (Nat.find hc') p := updCnt_mono (by omega)
        omega
    · obtain ⟨o', ho'⟩ := hinv'
      obtain ⟨m', r', hm'1, hm'2, hm'3⟩ := exists_hret_between hrun hh ho' c
      exact Nat.find_min hc' (show m' < Nat.find hc' by omega) ⟨r', hm'1, by omega, hm'3⟩
  -- (3) it is `p`'s last update invoked before `t`
  have hcntT : updCnt E t p = y.usqno := by
    have hge : updCnt E (h + 1) p ≤ updCnt E t p := updCnt_mono (by omega)
    by_contra hne2
    have : ∃ h₂, h < h₂ ∧ h₂ < t ∧ ∃ w, E[h₂]? = some (.hinv p (.update w)) := by
      by_contra hc
      push Not at hc
      apply hne2
      rw [← hcnt]
      unfold updCnt
      symm
      apply fIdx_eq_of_none _ (by omega)
      intro m hm1 hm2 e he
      rcases hu : updOf p e with _ | w
      · rfl
      · rw [updOf_eq_some hu] at he; exact absurd he (hc m (by omega) hm2 w)
    obtain ⟨h₂, c1, c2, w, hw⟩ := this
    obtain ⟨m', r', hm'1, hm'2, hm'3⟩ := exists_hret_between hrun hh hw c1
    exact hpend m' r' hm'1 (by omega) hm'3
  exact ⟨p, by omega, by omega, h, v, by omega, hh, hpend⟩

/-! ## Tracking the scan after its Line-71 store -/

/-- Post-decision states of a scan: a free-standing scan about to return (Line 76/78), or the
enclosing update at Lines 83–84. -/
def PC.post : PC (P := P) (V := V) → Prop
  | .scRet _ | .upStore | .upStoreW | .upRet => True
  | _ => False

variable (E) in
/-- The invariant of the scan of `q` (embedded in `emb`) whose Line-71 store `x₀` is at `st` with
`ACK` at `t`, at position `k`, with local state `s` and `c` collect responses since `t`. -/
def RInv (q : P) (emb : Option V) (st t : ℕ) (x₀ : SCVal P V) (k : ℕ) (s : LState P V)
    (c : ℕ) : Prop :=
  (s.pc.post ∧ c ≤ (pendSet E t).card + 2) ∨
  (s.ssqno = x₀.ssqno ∧ (∀ a y, st < a → a < k → ¬ StE E a q y) ∧
    ((s.pc = .scCol1 emb ∧ c = 0) ∨
     (s.pc = .scColW emb true ∧ c = 0 ∧ ∃ ic, t < ic ∧ ic < k ∧
        E[ic]? = some (.sc (.colInv q)) ∧ NoEvIn E q ic k) ∨
     (∃ i₁ j₁ F, t < i₁ ∧ ColE E i₁ j₁ q s.V1 ∧ F ⊆ pendSet E t ∧ c = F.card + 1 ∧
        (∀ p ∈ F, updCnt E t p ≤ usq (s.V1 p)) ∧
        ((s.pc = .scColN emb ∧ j₁ < k) ∨
         (s.pc = .scColW emb false ∧ ∃ ic, j₁ < ic ∧ ic < k ∧
            E[ic]? = some (.sc (.colInv q)) ∧ NoEvIn E q ic k)))))

lemma RInv.bound {q : P} {emb : Option V} {st t : ℕ} {x₀ : SCVal P V} {k : ℕ}
    {s : LState P V} {c : ℕ} (h : RInv E q emb st t x₀ k s c) :
    c ≤ (pendSet E t).card + 2 := by
  rcases h with ⟨-, h⟩ | ⟨-, -, ⟨-, rfl⟩ | ⟨-, rfl, -⟩ | ⟨i₁, j₁, F, -, -, hF, rfl, -⟩⟩
  · exact h
  · omega
  · omega
  · have := Finset.card_le_card hF; omega

/-- A step of another node preserves the invariant. -/
lemma RInv.frame {q : P} {emb : Option V} {st t : ℕ} {x₀ : SCVal P V} {k : ℕ}
    {s : LState P V} {c : ℕ} {e : Ev P V} (h : RInv E q emb st t x₀ k s c)
    (he : E[k]? = some e) (hp : e.proc ≠ q) : RInv E q emb st t x₀ (k + 1) s c := by
  have hst : ∀ y, ¬ StE E k q y := fun y => not_stE_of_proc_ne he hp
  have ext : (∀ a y, st < a → a < k → ¬ StE E a q y) →
      ∀ a y, st < a → a < k + 1 → ¬ StE E a q y := fun H a y h1 h2 => by
    rcases Nat.lt_or_ge a k with h3 | h3
    · exact H a y h1 h3
    · obtain rfl : a = k := by omega
      exact hst y
  rcases h with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  refine Or.inr ⟨h1, ext h2, ?_⟩
  rcases h3 with h3 | ⟨a1, a2, ic, b1, b2, b3, b4⟩ | ⟨i₁, j₁, F, a1, a2, a3, a4, a5, a6⟩
  · exact Or.inl h3
  · exact Or.inr (Or.inl ⟨a1, a2, ic, b1, by omega, b3, b4.succ he hp⟩)
  · refine Or.inr (Or.inr ⟨i₁, j₁, F, a1, a2, a3, a4, a5, ?_⟩)
    rcases a6 with ⟨b1, b2⟩ | ⟨b1, ic, b2, b3, b4, b5⟩
    · exact Or.inl ⟨b1, by omega⟩
    · exact Or.inr ⟨b1, ic, b2, by omega, b4, b5.succ he hp⟩

lemma post_finishScan (s : LState P V) (emb : Option V) (W : P → Option V) :
    (finishScan s emb W).pc.post := by
  cases emb <;> trivial

lemma mem_nodes_of_getElem? {i : ℕ} {e : Ev P V} (h : E[i]? = some e) : e.proc ∈ nodes E := by
  simp only [nodes, List.mem_toFinset, List.mem_map]
  exact ⟨e, List.mem_of_getElem? h, rfl⟩

lemma mem_pendSet {t : ℕ} {p : P} (h : PendingUpd E t p) : p ∈ pendSet E t := by
  classical
  simp only [pendSet, Finset.mem_filter]
  obtain ⟨h', v, -, hh, -⟩ := id h
  exact ⟨mem_nodes_of_getElem? hh, h⟩

open Classical in
/-- A step of `q` itself preserves the invariant. -/
lemma RInv.own (hrun : run pk E ≠ none) (hreg : Regular (scSched E)) {q : P}
    {emb : Option V} {st t : ℕ} {x₀ : SCVal P V} {k : ℕ} {s s' : LState P V} {c : ℕ}
    {ce : SCEv P (SCVal P V)} (h : RInv E q emb st t x₀ k s c) (hx₀ : StE E st q x₀)
    (hnext : NextE E st t) (htk : t < k) (he : E[k]? = some (.sc ce)) (hp : ce.proc = q)
    (hs : lstep pk q s (.sc ce) = some s') :
    RInv E q emb st t x₀ (k + 1) s'
      (c + if ∃ W, E[k]? = some (.sc (.ret q W)) then 1 else 0) := by
  have ext : (∀ y, ce ≠ .stInv q y) → (∀ a y, st < a → a < k → ¬ StE E a q y) →
      ∀ a y, st < a → a < k + 1 → ¬ StE E a q y := fun hne H a y h1 h2 => by
    rcases Nat.lt_or_ge a k with h3 | h3
    · exact H a y h1 h3
    · obtain rfl : a = k := by omega
      intro hy; rw [StE, he] at hy; cases hy; exact hne y rfl
  rcases h with ⟨hpost, hc⟩ | ⟨h1, h2, h3⟩
  · left
    rcases hpc : s.pc <;> rw [hpc] at hpost <;> simp only [PC.post] at hpost <;>
      rcases ce with ⟨q', x⟩ | q' | q' | ⟨q', W⟩ <;> simp [lstep, hpc] at hs
    · obtain ⟨-, rfl⟩ := hs; simpa [he, PC.post] using hc
    · subst hs; simpa [he, PC.post] using hc
  rcases h3 with ⟨hpc, rfl⟩ | ⟨hpc, rfl, ic, b1, b2, b3, b4⟩ |
    ⟨i₁, j₁, F, a1, a2, a3, a4, a5, ⟨hpc, b1⟩ | ⟨hpc, ic, b2, b3, b4, b5⟩⟩ <;>
    rcases ce with ⟨q', x⟩ | q' | q' | ⟨q', W⟩ <;> simp [lstep, hpc] at hs <;>
    simp only [SCEv.proc] at hp <;> subst hp
  · subst hs
    exact Or.inr ⟨h1, ext (by simp) h2, Or.inr (Or.inl ⟨rfl, by simp [he], k, htk, by omega, he,
      NoEvIn.self⟩)⟩
  · subst hs
    have hcol : ColE E ic k q' W := ⟨b3, he, nextE_of_noEvIn b2 b3 he rfl rfl b4⟩
    exact Or.inr ⟨h1, ext (by simp) h2, Or.inr (Or.inr ⟨ic, k, ∅, b1, hcol, by simp, by simp [he],
      by simp, Or.inl ⟨rfl, by omega⟩⟩)⟩
  · subst hs
    exact Or.inr ⟨h1, ext (by simp) h2, Or.inr (Or.inr ⟨i₁, j₁, F, a1, a2, a3, by simp [he, a4],
      a5, Or.inr ⟨rfl, k, b1, by omega, he, NoEvIn.self⟩⟩)⟩
  · have hcol : ColE E ic k q' W := ⟨b4, he, nextE_of_noEvIn b3 b4 he rfl rfl b5⟩
    have hcnt : (c + if ∃ W', E[k]? = some (.sc (.ret q' W')) then 1 else 0) = F.card + 2 := by
      simp only [he, Option.some.injEq, Ev.sc.injEq, SCEv.ret.injEq, true_and, exists_eq',
        ↓reduceIte]; omega
    rw [hcnt]
    have hFle := Finset.card_le_card a3
    by_cases hd : ∀ r, rU W r = rU s.V1 r
    · simp only [hd, implies_true, ↓reduceIte] at hs
      simp only [Option.some.injEq] at hs; subst hs
      exact Or.inl ⟨post_finishScan _ _ _, by omega⟩
    · simp only [hd, ↓reduceIte] at hs
      rcases hpk : pk.f W q' s.ssqno with _ | q''
      · rw [hpk] at hs
        simp only [Option.some.injEq] at hs; subst hs
        obtain ⟨p, hp1, hp2, hpend⟩ := fail_attr hrun hreg hx₀ hnext h2 a2 hcol a1 b2 hd
          (fun r y hy hsc => pk.total W q' s.ssqno r y hy (by rw [h1]; exact hsc) hpk)
        have hpF : p ∉ F := fun hm => by have := a5 p hm; omega
        have hij := a2.2.2.1
        refine Or.inr ⟨h1, ext (by simp) h2, Or.inr (Or.inr ⟨ic, k, insert p F, by omega, hcol,
          Finset.insert_subset (mem_pendSet hpend) a3,
          by rw [Finset.card_insert_of_notMem hpF], ?_, Or.inl ⟨rfl, by omega⟩⟩)⟩
        intro r hr
        rcases Finset.mem_insert.1 hr with rfl | hr
        · exact hp2
        · exact (a5 r hr).trans (usq_le_of_before hrun hreg a2 hcol b2 r)
      · rw [hpk] at hs
        simp only [Option.some.injEq] at hs; subst hs
        exact Or.inl ⟨post_finishScan _ _ _, by omega⟩

/-- Right after the `ACK` of the Line-71 store the invariant holds. -/
lemma RInv.init (hrun : run pk E ≠ none) {q : P} {emb : Option V} {st t : ℕ}
    {x₀ : SCVal P V} (hpc : (cfgAt pk E st q).pc = .scStore emb) (hx₀ : StE E st q x₀)
    (hnext : NextE E st t) :
    RInv E q emb st t x₀ (t + 1) (cfgAt pk E (t + 1) q) (colCount E q t (t + 1)) := by
  have hstL : st < E.length := lt_length_of_getElem? hx₀
  have hack := next_of_store hrun hx₀ hnext
  have htL : t < E.length := lt_length_of_getElem? hack
  obtain ⟨hlt, e, e', hea, heb, hpe, hno⟩ := hnext
  rw [StE, hea] at hx₀
  cases hx₀
  -- the Line-71 step
  have h1 := (cfgAt_step hrun hstL).1
  have hEst : E[st] = .sc (.stInv q x₀) := by
    rw [List.getElem?_eq_getElem hstL] at hea; exact Option.some.inj hea
  rw [hEst] at h1
  simp only [Ev.proc, SCEv.proc] at h1
  simp [lstep, hpc] at h1
  obtain ⟨hx, h1⟩ := h1
  -- nothing happens to `q` until the `ACK`
  have hconst : ∀ m, st < m → m ≤ t → cfgAt pk E m q = cfgAt pk E (st + 1) q := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h1' h2'
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt h1') with h3 | h3
      · rw [← h3]
      have ih' := ih (by omega) (by omega)
      have hmL : m < E.length := by omega
      by_cases hq : E[m].proc = q
      · exfalso
        have hs := (cfgAt_step hrun hmL).1
        rw [hq, ih', ← h1] at hs
        rcases hE : E[m] with ⟨q', o⟩ | ⟨q', r⟩ | c
        · rw [hE] at hs; simp [lstep] at hs
        · rw [hE] at hs; simp [lstep] at hs
        · rw [hE] at hq
          exact hno m (by omega) (by omega) c (by rw [List.getElem?_eq_getElem hmL, hE])
            (by simpa [Ev.proc, SCEv.proc] using hq)
      · rw [(cfgAt_step hrun hmL).2 q (Ne.symm hq), ih']
  have hct := hconst t hlt le_rfl
  have h2 := (cfgAt_step hrun htL).1
  have hEt : E[t] = .sc (.ack q) := by
    rw [List.getElem?_eq_getElem htL] at hack; exact Option.some.inj hack
  rw [hEt] at h2
  simp only [Ev.proc, SCEv.proc] at h2
  rw [hct, ← h1] at h2
  simp only [lstep, Option.some.injEq] at h2
  refine Or.inr ⟨by rw [← h2, hx], fun a y ha1 ha2 hy => ?_, Or.inl ⟨by rw [← h2], ?_⟩⟩
  · rcases Nat.lt_or_ge a t with h3 | h3
    · exact hno a ha1 h3 _ hy rfl
    · obtain rfl : a = t := by omega
      rw [StE, hack] at hy; cases hy
  · simp [colCount]

/-- The invariant at every position after the `ACK` up to the next high-level event of `q`. -/
lemma RInv.all (hrun : run pk E ≠ none) (hreg : Regular (scSched E)) {q : P} {emb : Option V}
    {st t : ℕ} {x₀ : SCVal P V} (hpc : (cfgAt pk E st q).pc = .scStore emb)
    (hx₀ : StE E st q x₀) (hnext : NextE E st t) :
    ∀ k, t < k → k ≤ E.length → NoHIn E q t k →
      RInv E q emb st t x₀ k (cfgAt pk E k q) (colCount E q t k) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro h1 h2 h3
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h1) with rfl | hk
    · exact RInv.init hrun hpc hx₀ hnext
    have hkL : k < E.length := by omega
    have IH := ih hk (by omega) (h3.mono (by omega))
    have he : E[k]? = some E[k] := List.getElem?_eq_getElem hkL
    rw [colCount_succ q hk]
    by_cases hq : E[k].proc = q
    · obtain ⟨ce, hce⟩ := h3 k hk (by omega) _ he hq
      have hs := (cfgAt_step hrun hkL).1
      rw [hq, hce] at hs
      rw [hce] at he hq
      exact IH.own hrun hreg hx₀ hnext hk he hq hs
    · have hn : ¬ ∃ W, E[k]? = some (.sc (.ret q W)) := by
        rintro ⟨W, hW⟩; rw [he] at hW
        have : E[k] = .sc (.ret q W) := Option.some.inj hW
        rw [this] at hq; exact hq rfl
      simp only [hn, ↓reduceIte, Nat.add_zero]
      rw [(cfgAt_step hrun hkL).2 q (Ne.symm hq)]
      exact IH.frame he hq

variable (pk) in
/-- **Theorem 8 of [AKSW20] (complexity)**: in every execution of Algorithm 7 on top of a regular
store-collect object, let node `q` perform the Line-71 store of a scan at position `st` (`q` is at
Line 71 just before `st`; the scan is free-standing if `emb = none` and embedded in
`UPDATE(v)` if `emb = some v`) and let `t` be the position of its `ACK`.  Then for every `j` such
that `q` has no invocation or response strictly between `t` and `j`, `q` receives at most
`n + 2` collect responses strictly between `t` and `j`, where `n` is the number of nodes with an
`UPDATE` pending at `t`.  So the scan performs at most `n + 2` collects and one store (an
`UPDATE` adds its Line-79 collect and its Line-83 store); the paper's bound `O(N(t))` follows
since a node with a pending operation is present (as in the paper's count, nodes that left with an
`UPDATE` pending are ignored). -/
theorem theorem8_collects (E : List (Ev P V)) (hrun : run pk E ≠ none)
    (hreg : Regular (scSched E)) {q : P} {emb : Option V} {st t : ℕ} {x₀ : SCVal P V}
    (hpc : (cfgAt pk E st q).pc = .scStore emb) (hx₀ : StE E st q x₀) (hnext : NextE E st t)
    (j : ℕ) (hj : NoHIn E q t j) :
    colCount E q t j ≤ (pendSet E t).card + 2 := by
  refine (colCount_le_of_length q t j).trans ?_
  rcases Nat.lt_or_ge t (min j E.length) with h | h
  · exact (RInv.all hrun hreg hpc hx₀ hnext _ h (min_le_right _ _)
      (hj.mono (min_le_left _ _))).bound
  · have : colCount E q t (min j E.length) = 0 := by
      classical
      unfold colCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m hm; simp only [Finset.mem_Ioo] at hm; omega
    omega

end Podc.StoreCollectChurn.Snap
