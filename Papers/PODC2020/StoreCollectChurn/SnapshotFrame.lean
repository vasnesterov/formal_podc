import Papers.PODC2020.StoreCollectChurn.SnapshotInv

/-!
# Helper lemmas for the invariants of Algorithm 7: counting, runs, and the frame lemma
(a step of another node preserves a node's invariant).
-/

namespace Podc.StoreCollectChurn.Snap

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P] {E : List (Ev P V)}

/-! ## `fIdx` and update counts -/

lemma fIdx_succ {α β : Type} (f : α → Option β) {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : fIdx f l (i + 1) = fIdx f l i + (f a).toList.length := by
  unfold fIdx
  rw [List.take_add_one, h, List.filterMap_append, List.length_append]
  rcases hf : f a with _ | b <;> simp [hf]

lemma updOf_eq_none_of_proc_ne {p : P} {e : Ev P V} (h : e.proc ≠ p) : updOf p e = none := by
  rcases e with ⟨q, _ | v⟩ | ⟨q, r⟩ | c <;> simp_all [updOf, Ev.proc]

lemma updCnt_succ_of_none {i : ℕ} {p : P} {e : Ev P V} (h : E[i]? = some e)
    (hu : updOf p e = none) : updCnt E (i + 1) p = updCnt E i p := by
  simp [updCnt, fIdx_succ _ h, hu]

lemma updCnt_succ_of_some {i : ℕ} {p : P} {e : Ev P V} {v : V} (h : E[i]? = some e)
    (hu : updOf p e = some v) : updCnt E (i + 1) p = updCnt E i p + 1 := by
  simp [updCnt, fIdx_succ _ h, hu]

lemma updArgs_getElem {i : ℕ} {p : P} {v : V} (h : E[i]? = some (.hinv p (.update v))) :
    (updArgs E p)[updCnt E i p]? = some v :=
  getElem?_filterMap_fIdx _ h (by simp [updOf])

lemma updCnt_mono {i j : ℕ} {p : P} (h : i ≤ j) : updCnt E i p ≤ updCnt E j p :=
  fIdx_mono _ h

/-- Between `h` and `i` only store-collect events of `p`: the update count is constant. -/
lemma updCnt_eq_of_noHIn {h i : ℕ} {p : P} (hh : h < i) (hn : NoHIn E p h i) :
    updCnt E i p = updCnt E (h + 1) p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show h + 1 ≤ i by omega)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih (by omega) (fun m h1 h2 => hn m h1 (by omega))]
    rcases hE : E[h + 1 + k]? with _ | e
    · have : E.length ≤ h + 1 + k := by
        by_contra hc; simp [List.getElem?_eq_getElem (by omega : h + 1 + k < E.length)] at hE
      unfold updCnt fIdx
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    · rw [show h + 1 + (k + 1) = h + 1 + k + 1 by omega]
      apply updCnt_succ_of_none hE
      by_cases hp : e.proc = p
      · obtain ⟨c, rfl⟩ := hn _ (by omega) (by omega) e hE hp
        rfl
      · exact updOf_eq_none_of_proc_ne hp

/-! ## Certificates and intervals -/

lemma Cert.mono {W : P → Option V} {lo hi lo' hi' : ℕ} (h : Cert E W lo hi) (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : Cert E W lo' hi' := by
  obtain ⟨i₁, j₁, q₁, W₁, i₂, j₂, q₂, W₂, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨i₁, j₁, q₁, W₁, i₂, j₂, q₂, W₂, h1, h2, by omega, h4, by omega, h6, h7⟩

lemma NoEvIn.succ {p : P} {a i : ℕ} {e : Ev P V} (h : NoEvIn E p a i) (he : E[i]? = some e)
    (hp : e.proc ≠ p) : NoEvIn E p a (i + 1) := by
  intro k h1 h2 e' he'
  rcases Nat.lt_or_ge k i with hk | hk
  · exact h k h1 hk e' he'
  · obtain rfl : k = i := by omega
    rw [he] at he'; cases he'; exact hp

lemma NoEvIn.self {p : P} {a : ℕ} : NoEvIn E p a (a + 1) := fun k h1 h2 => by omega

lemma NoHIn.succ {p : P} {a i : ℕ} {e : Ev P V} (h : NoHIn E p a i) (he : E[i]? = some e)
    (hp : e.proc = p → ∃ c, e = .sc c) : NoHIn E p a (i + 1) := by
  intro k h1 h2 e' he' hp'
  rcases Nat.lt_or_ge k i with hk | hk
  · exact h k h1 hk e' he' hp'
  · obtain rfl : k = i := by omega
    rw [he] at he'; cases he'; exact hp hp'

lemma NoHIn.self {p : P} {a : ℕ} : NoHIn E p a (a + 1) := fun k h1 h2 => by omega

lemma NoHIn.mono {p : P} {a b b' : ℕ} (h : NoHIn E p a b) (hb : b' ≤ b) : NoHIn E p a b' :=
  fun k h1 h2 => h k h1 (by omega)

lemma NoEvIn.mono {p : P} {a b b' : ℕ} (h : NoEvIn E p a b) (hb : b' ≤ b) : NoEvIn E p a b' :=
  fun k h1 h2 => h k h1 (by omega)

lemma NoEvIn.noHIn {p : P} {a b : ℕ} (h : NoEvIn E p a b) : NoHIn E p a b :=
  fun k h1 h2 e he hp => absurd hp (h k h1 h2 e he)

lemma nextE_of_noEvIn {p : P} {a i : ℕ} {e e' : SCEv P (SCVal P V)} (hai : a < i)
    (ha : E[a]? = some (.sc e)) (hi : E[i]? = some (.sc e')) (hp : e.proc = p)
    (hp' : e'.proc = p) (hn : NoEvIn E p a i) : NextE E a i := by
  refine ⟨hai, e, e', ha, hi, by rw [hp, hp'], fun k h1 h2 e'' hk => ?_⟩
  have := hn k h1 h2 (.sc e'') hk
  simpa [Ev.proc, hp] using this

/-! ## Store events -/

lemma StE.proc {a : ℕ} {p : P} {x : SCVal P V} {e : Ev P V} (h : StE E a p x)
    (he : E[a]? = some e) : e = .sc (.stInv p x) := by
  rw [StE, he] at h; exact (Option.some.inj h)

lemma not_stE_of_proc_ne {a : ℕ} {p : P} {x : SCVal P V} {e : Ev P V} (he : E[a]? = some e)
    (hp : e.proc ≠ p) : ¬ StE E a p x := by
  intro h; rw [h.proc he] at hp; exact hp rfl

/-! ## The frame lemma -/

lemma ScanCtx.mono {i i' : ℕ} {p : P} {s : LState P V} {emb : Option V} {h lo lo' : ℕ}
    (hc : ScanCtx E i p s emb h lo) (hi : i ≤ i') (hlo : lo ≤ lo') (hH : NoHIn E p h i')
    (hU : updCnt E i' p = updCnt E i p) : ScanCtx E i' p s emb h lo' := by
  obtain ⟨h1, -, h3, h4, h5⟩ := hc
  refine ⟨by omega, hH, h3, by omega, ?_⟩
  rcases emb with _ | v
  · exact ⟨h5.1, h5.2.trans hU.symm⟩
  · obtain ⟨⟨u1, u2, u3⟩, l', l, W, hl1, hl2, hl3, hl4⟩ := h5
    exact ⟨⟨u1, hU.trans u2, u3⟩, l', l, W, hl1, hl2, by omega, hl4⟩

lemma AfterStore.succ_of_ne {i : ℕ} {p : P} {s : LState P V} {st : ℕ} {e : Ev P V}
    (h : AfterStore E i p s st) (he : E[i]? = some e) (hp : e.proc ≠ p) :
    AfterStore E (i + 1) p s st := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, h2, h3, fun a ha y hy hs => ?_⟩
  rcases Nat.lt_or_ge a i with hai | hai
  · exact h4 a hai y hy hs
  · obtain rfl : a = i := by omega
    exact absurd hy (not_stE_of_proc_ne he hp)

lemma StoredOK.mono {i i' : ℕ} {p : P} {x : SCVal P V} (h : StoredOK E i p x) (hi : i ≤ i') :
    StoredOK E i' p x := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun hx => ?_⟩
  obtain ⟨l', l, W, hc, hl, hs, hcert, hupd⟩ := h3 hx
  exact ⟨l', l, W, hc, by omega, hs, hcert.mono le_rfl hi, hupd⟩

/-- **Frame lemma**: an event of another node preserves the invariant of `q`. -/
lemma NInv.frame {i : ℕ} {q : P} {s : LState P V} {e : Ev P V} (hI : NInv E i q s)
    (he : E[i]? = some e) (hp : e.proc ≠ q) : NInv E (i + 1) q s := by
  obtain ⟨hst, h2, h3, hok, hpc⟩ := hI
  have hU : updCnt E (i + 1) q = updCnt E i q :=
    updCnt_succ_of_none he (updOf_eq_none_of_proc_ne hp)
  have hH : ∀ {h}, NoHIn E q h i → NoHIn E q h (i + 1) := fun hh =>
    hh.succ he (fun h' => absurd h' hp)
  have hEv : ∀ {a}, NoEvIn E q a i → NoEvIn E q a (i + 1) := fun hh => hh.succ he hp
  have hAS : ∀ {st}, AfterStore E i q s st → AfterStore E (i + 1) q s st := fun hh =>
    hh.succ_of_ne he hp
  refine ⟨fun a ha x hx => ?_, h2, h3, hok.mono (by omega), ?_⟩
  · rcases Nat.lt_or_ge a i with hai | hai
    · exact hst a hai x hx
    · obtain rfl : a = i := by omega
      exact absurd hx (not_stE_of_proc_ne he hp)
  · unfold PCInv at hpc ⊢
    rcases hpc' : s.pc with _ | emb | emb | emb | ⟨emb, _ | _⟩ | emb | W | v | v | _ | _ | _ <;>
      rw [hpc'] at hpc
    · exact ⟨hpc.1.trans hU.symm, hpc.2⟩
    · obtain ⟨h, hc, hlt⟩ := hpc
      refine ⟨h, hc.mono (by omega) (by omega) (hH hc.2.1) hU, fun a ha y hy => ?_⟩
      rcases Nat.lt_or_ge a i with hai | hai
      · exact hlt a hai y hy
      · obtain rfl : a = i := by omega
        exact absurd hy (not_stE_of_proc_ne he hp)
    · obtain ⟨h, st, hc, hst', has⟩ := hpc
      exact ⟨h, st, hc.mono (by omega) le_rfl (hH hc.2.1) hU, hst', hAS has⟩
    · obtain ⟨h, st, hc, hst', has⟩ := hpc
      exact ⟨h, st, hc.mono (by omega) le_rfl (hH hc.2.1) hU, hst', hAS has⟩
    · obtain ⟨h, st, hc, hst', has, i₁, j₁, ic, h1, h2, h3, h4, h5, h6⟩ := hpc
      exact ⟨h, st, hc.mono (by omega) le_rfl (hH hc.2.1) hU, hst', hAS has, i₁, j₁, ic, h1, h2,
        h3, by omega, h5, hEv h6⟩
    · obtain ⟨h, st, hc, hst', has, ic, h1, h2, h3, h4⟩ := hpc
      exact ⟨h, st, hc.mono (by omega) le_rfl (hH hc.2.1) hU, hst', hAS has, ic, h1, by omega, h3,
        hEv h4⟩
    · obtain ⟨h, st, hc, hst', has, i₁, j₁, h1, h2, h3⟩ := hpc
      exact ⟨h, st, hc.mono (by omega) le_rfl (hH hc.2.1) hU, hst', hAS has, i₁, j₁, h1, h2,
        by omega⟩
    · obtain ⟨h, h1, h2, h3, h4, h5, h6⟩ := hpc
      exact ⟨h, by omega, h2, hH h3, h4.mono le_rfl (by omega), h5.trans hU.symm, h6⟩
    · obtain ⟨h, h1, h2, ⟨u1, u2, u3⟩, h4⟩ := hpc
      exact ⟨h, by omega, hH h2, ⟨u1, hU.trans u2, u3⟩, h4⟩
    · obtain ⟨h, h1, h2, ⟨u1, u2, u3⟩, h4, ic, h5, h6, h7, h8⟩ := hpc
      exact ⟨h, by omega, hH h2, ⟨u1, hU.trans u2, u3⟩, h4, ic, h5, by omega, h7, hEv h8⟩
    · obtain ⟨h, v, h1, h2, h3, h4, h5, h6, l', l, W, h7, h8, h9, h10, h11⟩ := hpc
      exact ⟨h, v, by omega, h2, hH h3, h4.trans hU.symm, h5, h6, l', l, W, h7, h8, by omega, h10,
        h11.mono le_rfl (by omega)⟩
    · obtain ⟨h, v, a, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpc
      exact ⟨h, v, a, h1, by omega, h3, hH h4, h5, h6.trans hU.symm, h7, hEv h8⟩
    · obtain ⟨h, v, a, b, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpc
      exact ⟨h, v, a, b, h1, by omega, h3, hH h4, h5, h6, h7.trans hU.symm, h8⟩

end Podc.StoreCollectChurn.Snap
