import Papers.PODC2020.LongLivedSnapshotsPolylog.LinDefs

/-!
# Linearizability of Algorithm 1: preservation of the invariant
-/

namespace Podc.LongLivedSnapshotsPolylog

open Cslib.SharedMemory
open Podc.LimitedUseSnapshots (maxArrObj MAOp invoked_take_mono)

variable {n m X : ℕ}

/-! ### Transfer of past facts to extensions of the execution -/

section Transfer

variable {α β : List (Lbl n)}

lemma cert_append {V : ℕ × ℕ} {t0 t1 : ℕ} (h : Cert m X α V t0 t1) :
    Cert m X (α ++ β) V t0 t1 := by
  obtain ⟨h01, h1l, ⟨a, b, hab, hV⟩, h3, h4, h5, h6, ⟨t', ht', h7⟩, ⟨t'', ht'', h8⟩⟩ := h
  refine ⟨h01, by simp; omega, ⟨a, b, fun t ht0 ht1 => ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨t', ht', ?_⟩, ⟨t'', ht'', ?_⟩⟩
  · rw [cfgAt_append (by omega)]; exact hab t ht0 ht1
  · rw [cfgAt_append h1l]; exact hV
  all_goals first
    | rwa [cfgAt_append (by omega)]

lemma take_append_of_le {t : ℕ} (ht : t ≤ α.length) : (α ++ β).take t = α.take t :=
  List.take_append_of_le_length ht

lemma invoked_of_take {x : OpId (Fin n)} {t : ℕ} (h : Invoked (α.take t) x) : Invoked α x := by
  have := (List.take_append_drop t α)
  rw [← this]; exact h.mono

/-- Facts about the current operation of `p` survive appending labels that are not responses of
`p`. -/
lemma ctx_append {p : Fin n} {cs : CS n} {bt : ℕ} (hcur : curOp (α ++ β) p = curOp α p)
    (h : Ctx m X α p cs bt) : Ctx m X (α ++ β) p cs bt := by
  obtain ⟨hbt, hinv, h1, h2, h3, h4⟩ := h
  have hop : opOf (α ++ β) (curOp α p) = opOf α (curOp α p) :=
    opOf_append_of_invoked (invoked_of_take hinv)
  refine ⟨by simp; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcur, take_append_of_le hbt]; exact hinv
  · intro v hv; rw [hcur, hop] at hv; rw [cfgAt_append hbt]; exact h1 v hv
  · intro v hv; rw [hcur, hop] at hv; rw [cfgAt_append hbt]; exact h2 v hv
  · rw [hcur, hop]; exact h3
  · intro h0 hh j
    obtain ⟨t, ht1, ht2, ht3⟩ := h4 h0 hh j
    exact ⟨t, ht1, by simp; omega, by rw [cfgAt_append ht2]; exact ht3⟩

lemma rd_append {C C' : Cfg n} {p : Fin n} {cs : CS n} {l r2 bt t0 t2 : ℕ}
    (hcur : curOp (α ++ β) p = curOp α p) (hts : (C'.loc p).ts = (C.loc p).ts)
    (h : Rd m X α C p cs l r2 bt t0 t2) : Rd m X (α ++ β) C' p cs l r2 bt t0 t2 := by
  obtain ⟨hc, h1, h2, h3, ⟨tr, htr, htr'⟩, h5, h6, h7⟩ := h
  refine ⟨ctx_append hcur hc, h1, h2, by simp; omega, ⟨tr, htr, ?_⟩, ?_, ?_, ?_⟩
  · rw [cfgAt_append (by omega)]; exact htr'
  · rw [cfgAt_append (by omega)]; exact h5
  · rw [cfgAt_append h3]; exact h6
  · rw [cfgAt_append (by omega), hts]; exact h7

lemma scanOK_append {l r2 t1 : ℕ} {v : ℕ × ℕ} (ht1 : t1 ≤ α.length)
    (h : ScanOK m X α l r2 v t1) : ScanOK m X (α ++ β) l r2 v t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by rw [cfgAt_append ht1]; exact h1, h2, h3, by rw [cfgAt_append ht1]; exact h4,
    by rw [cfgAt_append ht1]; exact h5, fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨t', ht', e⟩ := h6 hp
    exact ⟨t', ht', by rw [cfgAt_append (by omega)]; exact e⟩
  · obtain ⟨t', ht', e⟩ := h7 hp
    exact ⟨t', ht', by rw [cfgAt_append (by omega)]; exact e⟩

lemma retOK_append {p : Fin n} {r V : ℕ × ℕ} (hcur : curOp (α ++ β) p = curOp α p)
    (hinv : Invoked α (curOp α p)) (h : RetOK α p r V) : RetOK (α ++ β) p r V := by
  have hop : opOf (α ++ β) (curOp α p) = opOf α (curOp α p) := opOf_append_of_invoked hinv
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun h => h1 (by rwa [hcur, hop] at h), fun v h => h2 v (by rwa [hcur, hop] at h),
    fun v h => h3 v (by rwa [hcur, hop] at h)⟩

/-- Frame: the per-process invariant of `p` survives steps that do not touch `p`. -/
lemma pfl_append {C C' : Cfg n} {p : Fin n} {pc : PC n}
    (hcur : curOp (α ++ β) p = curOp α p) (hts : (C'.loc p).ts = (C.loc p).ts)
    (hMA : ∀ j, vMA C j ≤ vMA C' j) (h : PFL m X α C p pc) : PFL m X (α ++ β) C' p pc := by
  cases pc with
  | idle => trivial
  | wm s v =>
    simp only [PFL] at h ⊢
    rw [hcur, opOf_append_of_eq_some h]
  | rdR1 cs => obtain ⟨bt, h⟩ := h; exact ⟨bt, ctx_append hcur h⟩
  | rdL cs r1 =>
    obtain ⟨bt, tr, h1, h2, h3, h4⟩ := h
    exact ⟨bt, tr, ctx_append hcur h1, h2, by simp; omega, by rw [cfgAt_append h3]; exact h4⟩
  | rdR2 cs r1 l =>
    obtain ⟨bt, tr, t0, h1, h2, h3, h4, h5, h6, h7⟩ := h
    refine ⟨bt, tr, t0, ctx_append hcur h1, h2, h3, by simp; omega, ?_, ?_, ?_⟩
    · rw [cfgAt_append (by omega)]; exact h5
    · rw [cfgAt_append h4]; exact h6
    · rw [cfgAt_append h4, hts]; exact h7
  | upL cs l r2 =>
    obtain ⟨bt, t0, t2, h⟩ := h; exact ⟨bt, t0, t2, rd_append hcur hts h⟩
  | upR cs l r2 =>
    obtain ⟨bt, t0, t2, h, h'⟩ := h
    exact ⟨bt, t0, t2, rd_append hcur hts h, h'.trans (hMA _).1⟩
  | scanMA cs l r2 =>
    obtain ⟨bt, t0, t2, h, h', h''⟩ := h
    exact ⟨bt, t0, t2, rd_append hcur hts h, h'.trans (hMA _).1, h''.trans (hMA _).2⟩
  | chkL cs l r2 v =>
    obtain ⟨bt, t0, t2, t1, h, h1, h2, h3⟩ := h
    exact ⟨bt, t0, t2, t1, rd_append hcur hts h, h1, by simp; omega, scanOK_append h2 h3⟩
  | chkR cs l r2 v =>
    obtain ⟨bt, t0, t2, t1, te, h, h1, h2, h3, h4, h5⟩ := h
    exact ⟨bt, t0, t2, t1, te, rd_append hcur hts h, h1, h2, by simp; omega,
      scanOK_append (by omega) h4, by rw [cfgAt_append h3]; exact h5⟩
  | wH cs V =>
    obtain ⟨bt, t0, t1, h1, h2, h3, h4⟩ := h
    exact ⟨bt, t0, t1, ctx_append hcur h1, h2, cert_append h3,
      by rw [cfgAt_append (by have := h3.2.1; have := h3.1; omega), hts]; exact h4⟩
  | col cs f k acc =>
    obtain ⟨bt, h1, h2⟩ := h
    refine ⟨bt, ctx_append hcur h1, fun j hj => ?_⟩
    obtain ⟨t, ht1, ht2, ht3, ht4⟩ := h2 j hj
    refine ⟨t, ht1, by simp; omega, by rw [cfgAt_append ht2]; exact ht3, fun hp => ?_⟩
    obtain ⟨t0, t1, hc, he⟩ := ht4 hp
    exact ⟨t0, t1, cert_append hc,
      by rw [cfgAt_append (by have := hc.2.1; have := hc.1; omega)]; exact he⟩
  | retV r =>
    obtain ⟨V, t0, t1, h1, h2, h3⟩ := h
    refine ⟨V, t0, t1, cert_append h1, ?_, retOK_append hcur (invoked_of_take h2) h3⟩
    rw [hcur, take_append_of_le (by have := h1.2.1; have := h1.1; omega)]; exact h2

lemma maInv_frame_at {C C' : Cfg n} (h : MAInv m X α C) (hL : vL C ≤ vL C')
    (hR : vR C ≤ vR C') (j : ℕ) (hMA : vMA C' j = vMA C j) (hj : vMA C' j ≠ (0, 0)) :
    ∃ t, t ≤ (α ++ β).length ∧
    vL (cfgAt m X (α ++ β) t) / m + vR (cfgAt m X (α ++ β) t) / m = j ∧
    vL (cfgAt m X (α ++ β) t) / m * m + (vMA C' j).1 ≤ vL C' ∧
    vR (cfgAt m X (α ++ β) t) / m * m + (vMA C' j).2 ≤ vR C' ∧
    (0 < (vMA C' j).1 → ∃ t', t' ≤ (α ++ β).length ∧
      vL (cfgAt m X (α ++ β) t') = vL (cfgAt m X (α ++ β) t) / m * m + (vMA C' j).1) ∧
    (0 < (vMA C' j).2 → ∃ t', t' ≤ (α ++ β).length ∧
      vR (cfgAt m X (α ++ β) t') = vR (cfgAt m X (α ++ β) t) / m * m + (vMA C' j).2) := by
  rw [hMA] at hj ⊢
  obtain ⟨t, ht, h1, h2, h3, h4, h5⟩ := h j hj
  refine ⟨t, by simp; omega, ?_, ?_, ?_, fun hp => ?_, fun hp => ?_⟩
  · rw [cfgAt_append ht]; exact h1
  · rw [cfgAt_append ht]; omega
  · rw [cfgAt_append ht]; omega
  · obtain ⟨t', ht', e⟩ := h4 hp
    exact ⟨t', by simp; omega, by rw [cfgAt_append ht', cfgAt_append ht]; exact e⟩
  · obtain ⟨t', ht', e⟩ := h5 hp
    exact ⟨t', by simp; omega, by rw [cfgAt_append ht', cfgAt_append ht]; exact e⟩

lemma maInv_frame {C C' : Cfg n} (h : MAInv m X α C) (hL : vL C ≤ vL C') (hR : vR C ≤ vR C')
    (hMA : ∀ j, vMA C' j = vMA C j) : MAInv m X (α ++ β) C' :=
  fun j hj => maInv_frame_at h hL hR j (hMA j) hj

lemma hInv_frame {C C' : Cfg n} (h : HInv m X α C) (hH : ∀ j, vH C' j = vH C j) :
    HInv m X (α ++ β) C' := by
  intro j hj
  rw [hH] at hj ⊢
  obtain ⟨t0, t1, hc, he⟩ := h j hj
  exact ⟨t0, t1, cert_append hc,
    by rw [cfgAt_append (by have := hc.2.1; have := hc.1; omega)]; exact he⟩

lemma wInv_frame {C C' : Cfg n} (h : WInv α C) (hL : vL C' = vL C) (hR : vR C' = vR C) :
    WInv (α ++ β) C' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · rw [hL] at hp ⊢
    obtain ⟨u, hu, hi⟩ := h1 hp
    exact ⟨u, opOf_append_of_eq_some hu _, hi.mono⟩
  · rw [hR] at hp ⊢
    obtain ⟨u, hu, hi⟩ := h2 hp
    exact ⟨u, opOf_append_of_eq_some hu _, hi.mono⟩

lemma opCert_append {x : OpId (Fin n)} (hx : Completed α x) (h : OpCert m X α x) :
    OpCert m X (α ++ β) x := by
  obtain ⟨V, t0, t1, hc, hi, hnc, h1, h2, h3⟩ := h
  have hle : t0 ≤ α.length := by have := hc.2.1; have := hc.1; omega
  have hop : opOf (α ++ β) x = opOf α x := opOf_append_of_invoked (invoked_of_take hi)
  have hrp : respOf (α ++ β) x = respOf α x := respOf_append_of_completed hx
  refine ⟨V, t0, t1, cert_append hc, by rw [take_append_of_le hle]; exact hi,
    by rw [take_append_of_le hc.2.1]; exact hnc, ?_, ?_, ?_⟩
  · rw [hop, hrp]; exact h1
  · rw [hop, hrp]; exact h2
  · rw [hop, hrp]; exact h3

end Transfer

lemma cfgAt_snoc_len {α : List (Lbl n)} {C : Cfg n} {ℓ : Lbl n}
    (h : (alg1 n m X).run α = some C) : cfgAt m X (α ++ [ℓ]) α.length = C := by
  rw [cfgAt_append le_rfl, cfgAt_length h]

lemma cfgAt_snoc_succ {α : List (Lbl n)} {C C' : Cfg n} {ℓ : Lbl n}
    (h : (alg1 n m X).run α = some C) (hs : (alg1 n m X).step C ℓ = some C') :
    cfgAt m X (α ++ [ℓ]) (α.length + 1) = C' := by
  have : (alg1 n m X).run (α ++ [ℓ]) = some C' := by
    rw [Impl.run_concat, h, Option.bind_some, hs]
  simpa using cfgAt_length (X := X) this

/-! ### The steps of process `p`, one program counter at a time -/

section Steps

variable {α : List (Lbl n)} {C : Cfg n} {p : Fin n}

lemma pfl_afterFail {cs : CS n} {bt : ℕ} {C'' : Cfg n} {β : List (Lbl n)}
    (h : Ctx m X β p cs bt) : PFL m X β C'' p (afterFail X p cs) := by
  unfold afterFail
  split_ifs
  · exact ⟨bt, h, fun j hj => by simp at hj⟩
  · exact ⟨bt, h, fun j hj => by simp at hj⟩
  · exact ⟨bt, by simpa [Ctx] using h⟩

lemma pfl_wm (hrun : (alg1 n m X).run α = some C) (hc : C.pend p ≠ none) {s : Bool} {v : ℕ}
    (hPp : PFL m X α C p (.wm s v)) {C'' : Cfg n}
    (hv : if s then v ≤ vR (cfgAt m X (α ++ [.tau p]) (α.length + 1))
      else v ≤ vL (cfgAt m X (α ++ [.tau p]) (α.length + 1))) :
    PFL m X (α ++ [.tau p]) C'' p (.rdR1 (csInit true)) := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hc
  have hinv := ((alg1 n m X).run_pend_curOp hrun ho).1
  simp only [PFL] at hPp
  have hop : opOf (α ++ [.tau p]) (curOp (α ++ [.tau p]) p) =
      some (if s then MAOp.upd1 v else MAOp.upd0 v) := by
    rw [curOp_append_tau, opOf_append_of_invoked hinv, hPp]
  refine ⟨α.length + 1, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.take_of_length_le (by simp), curOp_append_tau]; exact hinv.mono
  · intro v' hv'; rw [hop] at hv'; cases s <;> simp at hv'; subst hv'; simpa using hv
  · intro v' hv'; rw [hop] at hv'; cases s <;> simp at hv'; subst hv'; simpa using hv
  · rw [hop]; cases s <;> simp [csInit]
  · simp [csInit]

lemma pfl_rdR1 (hrun : (alg1 n m X).run α = some C) {cs : CS n}
    (hPp : PFL m X α C p (.rdR1 cs)) {C'' : Cfg n} :
    PFL m X (α ++ [.tau p]) C'' p (.rdL cs (vR C)) := by
  obtain ⟨bt, h⟩ := hPp
  exact ⟨bt, α.length, ctx_append (curOp_append_tau α p p) h, h.1, by simp,
    by rw [cfgAt_snoc_len hrun]⟩

lemma pfl_rdL (hrun : (alg1 n m X).run α = some C) {cs : CS n} {r1 : ℕ}
    (hPp : PFL m X α C p (.rdL cs r1)) {C'' : Cfg n} (hts : (C''.loc p).ts = (C.loc p).ts) :
    PFL m X (α ++ [.tau p]) C'' p (.rdR2 cs r1 (vL C)) := by
  obtain ⟨bt, tr, h, h1, h2, h3⟩ := hPp
  refine ⟨bt, tr, α.length, ctx_append (curOp_append_tau α p p) h, h1, h2, by simp, ?_, ?_, ?_⟩
  · rw [cfgAt_append h2]; exact h3
  · rw [cfgAt_snoc_len hrun]
  · rw [cfgAt_snoc_len hrun, hts]; exact (basicInv_run hrun).2 p

lemma pfl_rdR2 (hrun : (alg1 n m X).run α = some C) {cs : CS n} {r1 l : ℕ}
    (hPp : PFL m X α C p (.rdR2 cs r1 l)) {C'' : Cfg n} (hts : (C''.loc p).ts = (C.loc p).ts) :
    PFL m X (α ++ [.tau p]) C'' p
      (if r1 / m = vR C / m then .upL cs l (vR C) else afterFail X p cs) := by
  obtain ⟨bt, tr, t0, h, h1, h2, h3, h4, h5, h6⟩ := hPp
  have h' := ctx_append (β := [.tau p]) (curOp_append_tau α p p) h
  split_ifs with hr
  · refine ⟨bt, t0, α.length, h', by omega, h3, by simp, ⟨tr, h2, ?_⟩, ?_, ?_, ?_⟩
    · rw [cfgAt_append (by omega), h4, hr]
    · rw [cfgAt_append h3]; exact h5
    · rw [cfgAt_snoc_len hrun]
    · rw [cfgAt_append h3, hts]; exact h6
  · exact pfl_afterFail h'

lemma pfl_upL {cs : CS n} {l r2 : ℕ} (hPp : PFL m X α C p (.upL cs l r2)) {C'' : Cfg n}
    (hts : (C''.loc p).ts = (C.loc p).ts) (hb : l % m ≤ (vMA C'' (idx m l r2)).1) :
    PFL m X (α ++ [.tau p]) C'' p (.upR cs l r2) := by
  obtain ⟨bt, t0, t2, h⟩ := hPp
  exact ⟨bt, t0, t2, rd_append (curOp_append_tau α p p) hts h, hb⟩

lemma pfl_upR {cs : CS n} {l r2 : ℕ} (hPp : PFL m X α C p (.upR cs l r2)) {C'' : Cfg n}
    (hts : (C''.loc p).ts = (C.loc p).ts)
    (hle : vMA C (idx m l r2) ≤ vMA C'' (idx m l r2))
    (hb : r2 % m ≤ (vMA C'' (idx m l r2)).2) :
    PFL m X (α ++ [.tau p]) C'' p (.scanMA cs l r2) := by
  obtain ⟨bt, t0, t2, h, h'⟩ := hPp
  exact ⟨bt, t0, t2, rd_append (curOp_append_tau α p p) hts h, h'.trans hle.1, hb⟩

/-- Squeeze: a value between two values with the same high-order bits has these bits too. -/
lemma div_squeeze {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) (h : x / m = z / m) :
    y / m = x / m := by
  have h1 := Nat.div_le_div_right (c := m) hxy
  have h2 := Nat.div_le_div_right (c := m) hyz
  omega

lemma pair_of_sum (hv : (alg1 n m X).Valid α) {t t' : ℕ} (ht : t ≤ α.length)
    (ht' : t' ≤ α.length)
    (hsum : vL (cfgAt m X α t) / m + vR (cfgAt m X α t) / m =
      vL (cfgAt m X α t') / m + vR (cfgAt m X α t') / m) :
    vL (cfgAt m X α t) / m = vL (cfgAt m X α t') / m ∧
      vR (cfgAt m X α t) / m = vR (cfgAt m X α t') / m := by
  rcases le_total t t' with h | h
  · have h1 := Nat.div_le_div_right (c := m) (monoL (X := X) hv h ht')
    have h2 := Nat.div_le_div_right (c := m) (monoR (X := X) hv h ht')
    omega
  · have h1 := Nat.div_le_div_right (c := m) (monoL (X := X) hv h ht)
    have h2 := Nat.div_le_div_right (c := m) (monoR (X := X) hv h ht)
    omega

/-- The facts on `MA_{a+b}` given by `MAInv`, for a pair `(a, b)` of high-order bits that was
current at some time `t0`. -/
lemma ma_facts (hrun : (alg1 n m X).run α = some C) (hMAI : MAInv m X α C) {t0 a b : ℕ}
    (ht0 : t0 ≤ α.length) (ha : vL (cfgAt m X α t0) / m = a)
    (hb : vR (cfgAt m X α t0) / m = b) :
    a * m + (vMA C (a + b)).1 ≤ vL C ∧ b * m + (vMA C (a + b)).2 ≤ vR C ∧
    (0 < (vMA C (a + b)).1 → ∃ t', t' ≤ α.length ∧
      vL (cfgAt m X α t') = a * m + (vMA C (a + b)).1) ∧
    (0 < (vMA C (a + b)).2 → ∃ t', t' ≤ α.length ∧
      vR (cfgAt m X α t') = b * m + (vMA C (a + b)).2) := by
  have hv : (alg1 n m X).Valid α := ⟨C, hrun⟩
  have hCe : cfgAt m X α α.length = C := cfgAt_length hrun
  by_cases h0 : vMA C (a + b) = (0, 0)
  · rw [h0]
    have hL := monoL (X := X) hv ht0 le_rfl
    have hR := monoR (X := X) hv ht0 le_rfl
    rw [hCe] at hL hR
    have e1 := Nat.div_mul_le_self (vL (cfgAt m X α t0)) m
    have e2 := Nat.div_mul_le_self (vR (cfgAt m X α t0)) m
    refine ⟨?_, ?_, fun h => by simp at h, fun h => by simp at h⟩
    · rw [ha] at e1; simp; omega
    · rw [hb] at e2; simp; omega
  · obtain ⟨t, ht, hsum, h1, h2, h3, h4⟩ := hMAI (a + b) h0
    obtain ⟨e1, e2⟩ := pair_of_sum hv ht ht0 (by rw [hsum, ha, hb])
    rw [ha] at e1; rw [hb] at e2
    rw [e1] at h1 h3; rw [e2] at h2 h4
    exact ⟨h1, h2, h3, h4⟩

lemma pfl_scanMA (hrun : (alg1 n m X).run α = some C) (hMAI : MAInv m X α C) {cs : CS n}
    {l r2 : ℕ} (hPp : PFL m X α C p (.scanMA cs l r2)) {C'' : Cfg n}
    (hts : (C''.loc p).ts = (C.loc p).ts) :
    PFL m X (α ++ [.tau p]) C'' p (.chkL cs l r2 (vMA C (idx m l r2))) := by
  have hv : (alg1 n m X).Valid α := ⟨C, hrun⟩
  obtain ⟨bt, t0, t2, h, hb1, hb2⟩ := hPp
  obtain ⟨hc, h1, h2, h3, ⟨tr, htr, htr'⟩, h5, h6, h7⟩ := h
  have hR0 : vR (cfgAt m X α t0) / m = r2 / m := by
    have := div_squeeze (m := m) (monoR (X := X) hv htr (by omega))
      (monoR (X := X) hv h2 h3) (by rw [htr', h6])
    rw [this, htr']
  obtain ⟨f1, f2, f3, f4⟩ := ma_facts hrun hMAI (by omega) (by rw [h5]) hR0
  refine ⟨bt, t0, t2, α.length,
    rd_append (curOp_append_tau α p p) hts ⟨hc, h1, h2, h3, ⟨tr, htr, htr'⟩, h5, h6, h7⟩,
    h3, by simp, ?_⟩
  have hCe : cfgAt m X (α ++ [.tau p]) α.length = C := cfgAt_snoc_len hrun
  refine ⟨by rw [hCe], hb1, hb2, by rw [hCe]; exact f1, by rw [hCe]; exact f2,
    fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨t', ht', e⟩ := f3 hp
    exact ⟨t', ht', by rw [cfgAt_append ht']; exact e⟩
  · obtain ⟨t', ht', e⟩ := f4 hp
    exact ⟨t', ht', by rw [cfgAt_append ht']; exact e⟩

lemma pfl_chkL (hrun : (alg1 n m X).run α = some C) {cs : CS n} {l r2 : ℕ} {v : ℕ × ℕ}
    (hPp : PFL m X α C p (.chkL cs l r2 v)) {C'' : Cfg n}
    (hts : (C''.loc p).ts = (C.loc p).ts) :
    PFL m X (α ++ [.tau p]) C'' p
      (if vL C / m = l / m then .chkR cs l r2 v else afterFail X p cs) := by
  obtain ⟨bt, t0, t2, t1, h, h1, h2, h3⟩ := hPp
  have h' := rd_append (β := [.tau p]) (curOp_append_tau α p p) hts h
  split_ifs with hl
  · exact ⟨bt, t0, t2, t1, α.length, h', h1, h2, by simp, scanOK_append h2 h3,
      by rw [cfgAt_snoc_len hrun]; exact hl⟩
  · exact pfl_afterFail h'.1

/-- A `CompScan` whose view `V` has a certificate after its start returns a correct response. -/
lemma pfl_retOf {β : List (Lbl n)} (hv : (alg1 n m X).Valid β) {cs : CS n} {bt t0 t1 : ℕ}
    {V : ℕ × ℕ} (hc : Ctx m X β p cs bt) (hbt : bt ≤ t0) (hcert : Cert m X β V t0 t1)
    {C'' : Cfg n} : PFL m X β C'' p (retOf cs V) := by
  obtain ⟨hbtl, hinv, hu0, hu1, hupd, -⟩ := hc
  have hcert' := hcert
  obtain ⟨h01, h1l, -, hL0, hR0, -⟩ := hcert'
  have hL := monoL (X := X) hv hbt (by omega)
  have hR := monoR (X := X) hv hbt (by omega)
  have hinv' : Invoked (β.take t0) (curOp β p) := invoked_take_mono hbt hinv
  unfold retOf
  split_ifs with hu
  · refine ⟨V, t0, t1, ⟨h01, h1l, hcert.2.2⟩, hinv', fun h => ?_, fun v hv' => ?_,
      fun v hv' => ?_⟩
    · rw [hupd.2 h] at hu; cases hu
    · exact ⟨by have := hu0 v hv'; omega, rfl⟩
    · exact ⟨by have := hu1 v hv'; omega, rfl⟩
  · have hs : opOf β (curOp β p) = some .scan := hupd.1 (by simpa using hu)
    have := hcert
    refine ⟨V, t0, t1, ⟨h01, h1l, hcert.2.2⟩, hinv', fun _ => rfl, fun v hv' => ?_,
      fun v hv' => ?_⟩
    · rw [hs] at hv'; cases hv'
    · rw [hs] at hv'; cases hv'

lemma pfl_chkR (hrun : (alg1 n m X).run α = some C) {cs : CS n} {l r2 : ℕ} {v : ℕ × ℕ}
    (hPp : PFL m X α C p (.chkR cs l r2 v)) {C'' : Cfg n}
    (hts : (C''.loc p).ts = (C.loc p).ts) :
    PFL m X (α ++ [.tau p]) C'' p
      (if vR C / m = r2 / m then .wH cs (l / m * m + v.1, r2 / m * m + v.2)
        else afterFail X p cs) := by
  have hv : (alg1 n m X).Valid α := ⟨C, hrun⟩
  obtain ⟨bt, t0, t2, t1, te, h, h1, h2, h3, ⟨hvv, s1, s2, s3, s4, s5, s6⟩, hte⟩ := hPp
  have h' := rd_append (β := [.tau p]) (curOp_append_tau α p p) hts h
  split_ifs with hr
  · obtain ⟨hc, hbt, h02, h2l, ⟨tr, htr, htr'⟩, hl0, hr2, hts0⟩ := h
    have hCe : cfgAt m X α α.length = C := cfgAt_length hrun
    refine ⟨bt, t0, t1, h'.1, hbt, ?_, by rw [cfgAt_append (by omega), hts]; exact hts0⟩
    refine cert_append ⟨by omega, by omega, ⟨l / m, r2 / m, fun t ht0 ht1 => ⟨?_, ?_⟩, ?_⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := div_squeeze (m := m) (monoL (X := X) hv ht0 (by omega))
        (monoL (X := X) hv (ht1.trans h2) (by omega)) (by rw [hl0, hte])
      rw [this, hl0]
    · have := div_squeeze (m := m) (monoR (X := X) hv (htr.trans ht0) (by omega))
        (monoR (X := X) hv (show t ≤ α.length by omega) le_rfl) (by rw [htr', hCe, hr])
      rw [this, htr']
    · rw [hvv]; rfl
    · rw [hl0]; have := Nat.div_add_mod l m; simp only; rw [Nat.mul_comm] at this; omega
    · have := monoR (X := X) hv h02 h2l; rw [hr2] at this
      have e := Nat.div_add_mod r2 m; simp only; rw [Nat.mul_comm] at e; omega
    · exact s3
    · exact s4
    · simp only
      by_cases hp : 0 < v.1
      · exact s5 hp
      · refine ⟨t0, by omega, ?_⟩
        have e := Nat.div_add_mod l m; rw [Nat.mul_comm] at e
        rw [hl0]; omega
    · simp only
      by_cases hp : 0 < v.2
      · exact s6 hp
      · refine ⟨t2, h1, ?_⟩
        have e := Nat.div_add_mod r2 m; rw [Nat.mul_comm] at e
        rw [hr2]; omega
  · exact pfl_afterFail h'.1

lemma pfl_wH (hrun : (alg1 n m X).run α = some C) {cs : CS n} {v : ℕ × ℕ}
    (hPp : PFL m X α C p (.wH cs v)) {C'' : Cfg n} (hs : (alg1 n m X).step C (.tau p) = some C'') :
    PFL m X (α ++ [.tau p]) C'' p (retOf cs v) := by
  have hv' : (alg1 n m X).Valid (α ++ [.tau p]) :=
    ⟨C'', by rw [Impl.run_concat, hrun, Option.bind_some, hs]⟩
  obtain ⟨bt, t0, t1, hc, hbt, hcert, -⟩ := hPp
  exact pfl_retOf hv' (ctx_append (curOp_append_tau α p p) hc) hbt (cert_append hcert)

lemma findHelp_some {h0 h1 : Fin n → HEntry} {V : ℕ × ℕ} (h : findHelp h0 h1 = some V) :
    ∃ j, (h0 j).1 + 1 < (h1 j).1 ∧ V = (h1 j).2 := by
  unfold findHelp at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
  have := List.find?_some hj
  exact ⟨j, by simpa using this, rfl⟩

lemma pfl_col (hrun : (alg1 n m X).run α = some C) (hHI : HInv m X α C) {cs : CS n} {f : Bool}
    {k : Fin n} {acc : Fin n → HEntry} (hPp : PFL m X α C p (.col cs f k acc)) {C'' : Cfg n}
    (hs : (alg1 n m X).step C (.tau p) = some C'') :
    PFL m X (α ++ [.tau p]) C'' p
      (if h : k.1 + 1 < n then .col cs f ⟨k.1 + 1, h⟩ (Function.update acc k (vH C k))
        else afterCollect cs f (Function.update acc k (vH C k))) := by
  have hv' : (alg1 n m X).Valid (α ++ [.tau p]) :=
    ⟨C'', by rw [Impl.run_concat, hrun, Option.bind_some, hs]⟩
  obtain ⟨bt, hc, hacc⟩ := hPp
  have hc' := ctx_append (β := [.tau p]) (curOp_append_tau α p p) hc
  have hCe : cfgAt m X (α ++ [.tau p]) α.length = C := cfgAt_snoc_len hrun
  -- the facts on the entries read so far, including `H[k]`
  have hacc' : ∀ j : Fin n, j.1 < k.1 + 1 → ∃ t, bt ≤ t ∧ t ≤ (α ++ [Label.tau p]).length ∧
      vH (cfgAt m X (α ++ [.tau p]) t) j = Function.update acc k (vH C k) j ∧
      (0 < (Function.update acc k (vH C k) j).1 → ∃ t0 t1,
        Cert m X (α ++ [.tau p]) (Function.update acc k (vH C k) j).2 t0 t1 ∧
        (vH (cfgAt m X (α ++ [.tau p]) t0) j).1 + 1 = (Function.update acc k (vH C k) j).1) := by
    intro j hj
    by_cases hjk : j = k
    · subst hjk
      simp only [Function.update_self]
      refine ⟨α.length, hc.1, by simp, by rw [hCe], fun hp => ?_⟩
      obtain ⟨t0, t1, hcert, he⟩ := hHI j hp
      exact ⟨t0, t1, cert_append hcert,
        by rw [cfgAt_append (by have := hcert.2.1; have := hcert.1; omega)]; exact he⟩
    · rw [Function.update_of_ne hjk]
      have hjk' : j.1 < k.1 := by
        have : j.1 ≠ k.1 := fun h => hjk (Fin.ext h)
        omega
      obtain ⟨t, ht1, ht2, ht3, ht4⟩ := hacc j hjk'
      refine ⟨t, ht1, by simp; omega, by rw [cfgAt_append ht2]; exact ht3, fun hp => ?_⟩
      obtain ⟨t0, t1, hcert, he⟩ := ht4 hp
      exact ⟨t0, t1, cert_append hcert,
        by rw [cfgAt_append (by have := hcert.2.1; have := hcert.1; omega)]; exact he⟩
  split_ifs with hk
  · exact ⟨bt, hc', fun j hj => hacc' j hj⟩
  · have hall : ∀ j : Fin n, j.1 < k.1 + 1 := fun j => by have := j.2; omega
    unfold afterCollect
    cases f with
    | true =>
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := hc'
      refine ⟨bt, h1, h2, h3, h4, h5, fun h0 hh j => ?_⟩
      simp only [Option.some.injEq] at hh
      subst hh
      obtain ⟨t, ht1, ht2, ht3, -⟩ := hacc' j (hall j)
      exact ⟨t, ht1, ht2, by rw [ht3]⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i V hV
        obtain ⟨h0, hh0, hfh⟩ := Option.bind_eq_some_iff.1 hV
        obtain ⟨j, hj, rfl⟩ := findHelp_some hfh
        obtain ⟨t, ht1, ht2, ht3, ht4⟩ := hacc' j (hall j)
        obtain ⟨t0, t1, hcert, he⟩ := ht4 (by omega)
        obtain ⟨th, hth1, hth2, hth3⟩ := hc'.2.2.2.2.2 h0 hh0 j
        have hbt : bt ≤ t0 := by
          by_contra hlt
          have := monoH (X := X) hv' (show t0 ≤ th by omega) hth2 j
          omega
        exact pfl_retOf hv' hc' hbt hcert
      · exact ⟨bt, by simpa [Ctx] using hc'⟩

/-- The pair of high-order bits at the time `t0` of the line-11 read. -/
lemma rd_pair (hrun : (alg1 n m X).run α = some C) {cs : CS n} {l r2 bt t0 t2 : ℕ}
    (h : Rd m X α C p cs l r2 bt t0 t2) :
    vL (cfgAt m X α t0) / m = l / m ∧ vR (cfgAt m X α t0) / m = r2 / m := by
  have hv : (alg1 n m X).Valid α := ⟨C, hrun⟩
  obtain ⟨-, -, h2, h3, ⟨tr, htr, htr'⟩, h5, h6, -⟩ := h
  refine ⟨by rw [h5], ?_⟩
  have := div_squeeze (m := m) (monoR (X := X) hv htr (by omega))
    (monoR (X := X) hv h2 h3) (by rw [htr', h6])
  rw [this, htr']

lemma maInv_upL (hrun : (alg1 n m X).run α = some C) (hMAI : MAInv m X α C) {cs : CS n}
    {l r2 : ℕ} (hPp : PFL m X α C p (.upL cs l r2)) {C' : Cfg n}
    (hL : vL C' = vL C) (hR : vR C' = vR C)
    (hMA : ∀ j, vMA C' j = if j = idx m l r2 then
      (max (vMA C j).1 (l % m), (vMA C j).2) else vMA C j) :
    MAInv m X (α ++ [.tau p]) C' := by
  have hv : (alg1 n m X).Valid α := ⟨C, hrun⟩
  have hCe : cfgAt m X α α.length = C := cfgAt_length hrun
  obtain ⟨bt, t0, t2, h⟩ := hPp
  obtain ⟨pa, pb⟩ := rd_pair hrun h
  obtain ⟨-, -, h2, h3, -, h5, h6, -⟩ := h
  intro j hj
  by_cases hjh : j = idx m l r2
  · subst hjh
    rw [hMA, ite_eq_left_of_eq_true _ _ (eq_true rfl)] at hj ⊢
    obtain ⟨f1, f2, f3, f4⟩ := ma_facts hrun hMAI (by omega) pa pb
    have hl := monoL (X := X) hv (show t0 ≤ α.length by omega) le_rfl
    have hr := monoR (X := X) hv h3 le_rfl
    rw [hCe, h5] at hl; rw [hCe, h6] at hr
    have el := Nat.div_add_mod l m; rw [Nat.mul_comm] at el
    have er := Nat.div_add_mod r2 m; rw [Nat.mul_comm] at er
    refine ⟨t0, by simp; omega, ?_, ?_, ?_, fun hp => ?_, fun hp => ?_⟩
    · rw [cfgAt_append (by omega), pa, pb]; rfl
    · rw [cfgAt_append (by omega), pa, hL]; simp only [idx] at f1 ⊢; omega
    · rw [cfgAt_append (by omega), pb, hR]; simp only [idx] at f2 ⊢; omega
    · rw [cfgAt_append (by omega), pa]
      by_cases hlo : (vMA C (idx m l r2)).1 ≤ l % m
      · refine ⟨t0, by simp; omega, ?_⟩
        rw [cfgAt_append (by omega), h5, max_eq_right hlo]; omega
      · rw [max_eq_left (by omega)]
        obtain ⟨t', ht', e⟩ := f3 (by simp only [idx] at hlo; omega)
        exact ⟨t', by simp; omega, by rw [cfgAt_append ht']; exact e⟩
    · rw [cfgAt_append (by omega), pb]
      obtain ⟨t', ht', e⟩ := f4 hp
      exact ⟨t', by simp; omega, by rw [cfgAt_append ht']; exact e⟩
  · exact maInv_frame_at hMAI (by rw [hL]) (by rw [hR]) j
      (by rw [hMA, ite_eq_right_of_eq_false _ _ (eq_false hjh)]) hj

lemma maInv_upR (hrun : (alg1 n m X).run α = some C) (hMAI : MAInv m X α C) {cs : CS n}
    {l r2 : ℕ} (hPp : PFL m X α C p (.upR cs l r2)) {C' : Cfg n}
    (hL : vL C' = vL C) (hR : vR C' = vR C)
    (hMA : ∀ j, vMA C' j = if j = idx m l r2 then
      ((vMA C j).1, max (vMA C j).2 (r2 % m)) else vMA C j) :
    MAInv m X (α ++ [.tau p]) C' := by
  have hv : (alg1 n m X).Valid α := ⟨C, hrun⟩
  have hCe : cfgAt m X α α.length = C := cfgAt_length hrun
  obtain ⟨bt, t0, t2, h, -⟩ := hPp
  obtain ⟨pa, pb⟩ := rd_pair hrun h
  obtain ⟨-, -, h2, h3, -, h5, h6, -⟩ := h
  intro j hj
  by_cases hjh : j = idx m l r2
  · subst hjh
    rw [hMA, ite_eq_left_of_eq_true _ _ (eq_true rfl)] at hj ⊢
    obtain ⟨f1, f2, f3, f4⟩ := ma_facts hrun hMAI (by omega) pa pb
    have hl := monoL (X := X) hv (show t0 ≤ α.length by omega) le_rfl
    have hr := monoR (X := X) hv h3 le_rfl
    rw [hCe, h5] at hl; rw [hCe, h6] at hr
    have el := Nat.div_add_mod l m; rw [Nat.mul_comm] at el
    have er := Nat.div_add_mod r2 m; rw [Nat.mul_comm] at er
    refine ⟨t0, by simp; omega, ?_, ?_, ?_, fun hp => ?_, fun hp => ?_⟩
    · rw [cfgAt_append (by omega), pa, pb]; rfl
    · rw [cfgAt_append (by omega), pa, hL]; simp only [idx] at f1 ⊢; omega
    · rw [cfgAt_append (by omega), pb, hR]; simp only [idx] at f2 ⊢; omega
    · rw [cfgAt_append (by omega), pa]
      obtain ⟨t', ht', e⟩ := f3 (by simp only [idx] at hp ⊢; omega)
      exact ⟨t', by simp; omega, by rw [cfgAt_append ht']; exact e⟩
    · rw [cfgAt_append (by omega), pb]
      by_cases hlo : (vMA C (idx m l r2)).2 ≤ r2 % m
      · refine ⟨t2, by simp; omega, ?_⟩
        rw [cfgAt_append (by omega), h6, max_eq_right hlo]; omega
      · rw [max_eq_left (by omega)]
        obtain ⟨t', ht', e⟩ := f4 (by simp only [idx] at hlo; omega)
        exact ⟨t', by simp; omega, by rw [cfgAt_append ht']; exact e⟩
  · exact maInv_frame_at hMAI (by rw [hL]) (by rw [hR]) j
      (by rw [hMA, ite_eq_right_of_eq_false _ _ (eq_false hjh)]) hj

lemma hInv_wH (hHI : HInv m X α C) {cs : CS n}
    {v : ℕ × ℕ} (hPp : PFL m X α C p (.wH cs v)) {C' : Cfg n}
    (hH : ∀ j, vH C' j = if j = p then ((C.loc p).ts + 1, v) else vH C j) :
    HInv m X (α ++ [.tau p]) C' := by
  obtain ⟨bt, t0, t1, -, -, hcert, hts⟩ := hPp
  intro j hj
  by_cases hjp : j = p
  · subst hjp
    rw [hH, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    exact ⟨t0, t1, cert_append hcert,
      by rw [cfgAt_append (by have := hcert.2.1; have := hcert.1; omega), hts]⟩
  · rw [hH, ite_eq_right_of_eq_false _ _ (eq_false hjp)] at hj ⊢
    obtain ⟨t0, t1, hcert, he⟩ := hHI j hj
    exact ⟨t0, t1, cert_append hcert,
      by rw [cfgAt_append (by have := hcert.2.1; have := hcert.1; omega)]; exact he⟩

lemma wInv_wm (hrun : (alg1 n m X).run α = some C) (hW : WInv α C) (hc : C.pend p ≠ none)
    {s : Bool} {v : ℕ} (hPp : PFL m X α C p (.wm s v)) {C' : Cfg n}
    (hL : vL C' = if s then vL C else max (vL C) v)
    (hR : vR C' = if s then max (vR C) v else vR C) :
    WInv (α ++ [.tau p]) C' := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hc
  have hinv := ((alg1 n m X).run_pend_curOp hrun ho).1
  simp only [PFL] at hPp
  obtain ⟨w1, w2⟩ := hW
  cases s with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hL hR hPp
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [hL] at hp ⊢
      rcases le_total v (vL C) with hle | hle
      · rw [max_eq_left hle] at hp ⊢
        obtain ⟨u, hu, hi⟩ := w1 hp
        exact ⟨u, opOf_append_of_eq_some hu _, hi.mono⟩
      · rw [max_eq_right hle]
        exact ⟨curOp α p, opOf_append_of_eq_some hPp _, hinv.mono⟩
    · rw [hR] at hp ⊢
      obtain ⟨u, hu, hi⟩ := w2 hp
      exact ⟨u, opOf_append_of_eq_some hu _, hi.mono⟩
  | true =>
    simp only [↓reduceIte] at hL hR hPp
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [hL] at hp ⊢
      obtain ⟨u, hu, hi⟩ := w1 hp
      exact ⟨u, opOf_append_of_eq_some hu _, hi.mono⟩
    · rw [hR] at hp ⊢
      rcases le_total v (vR C) with hle | hle
      · rw [max_eq_left hle] at hp ⊢
        obtain ⟨u, hu, hi⟩ := w2 hp
        exact ⟨u, opOf_append_of_eq_some hu _, hi.mono⟩
      · rw [max_eq_right hle]
        exact ⟨curOp α p, opOf_append_of_eq_some hPp _, hinv.mono⟩

end Steps


/-- Assembling the invariant after a tau step of `p` from its parts that concern `p` and the
memory. -/
lemma inv_tau_of {α : List (Lbl n)} {C C' : Cfg n} {p : Fin n}
    (hI : Inv m X α C) (hs : (alg1 n m X).step C (.tau p) = some C')
    (hloc : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hMA' : MAInv m X (α ++ [.tau p]) C') (hH' : HInv m X (α ++ [.tau p]) C')
    (hW' : WInv (α ++ [.tau p]) C') (hPp : PFL m X (α ++ [.tau p]) C' p (C'.loc p).pc) :
    Inv m X (α ++ [.tau p]) C' := by
  obtain ⟨hB, -, -, -, hComp, hP⟩ := hI
  obtain ⟨hB', -, -, hMAm, -⟩ := step_basic hB hs
  refine ⟨hB', hMA', hH', hW', fun x hx => ?_, fun q => ?_⟩
  · have hx' := (completed_append_of_not_ret (fun _ _ h => by cases h) x).1 hx
    exact opCert_append hx' (hComp x hx')
  · by_cases hq : q = p
    · subst hq; exact hPp
    · rw [hloc q hq]
      exact pfl_append (C := C) (curOp_append_tau α p q) (by rw [hloc q hq]) hMAm (hP q)

/-- Preservation for a tau step (all program counters). -/
theorem inv_tau {α : List (Lbl n)} {C C' : Cfg n} {p : Fin n}
    (hrun : (alg1 n m X).run α = some C) (hI : Inv m X α C)
    (hs : (alg1 n m X).step C (.tau p) = some C') : Inv m X (α ++ [.tau p]) C' := by
  have hs0 := hs
  have hv' : (alg1 n m X).Valid (α ++ [.tau p]) :=
    ⟨C', by rw [Impl.run_concat, hrun, Option.bind_some, hs]⟩
  have hc0 : cfgAt m X (α ++ [.tau p]) α.length = C := cfgAt_snoc_len hrun
  have hc1 : cfgAt m X (α ++ [.tau p]) (α.length + 1) = C' := cfgAt_snoc_succ hrun hs
  have hlen : (α ++ [Label.tau p]).length = α.length + 1 := by simp
  obtain ⟨hB, hMA, hH, hW, hComp, hP⟩ := hI
  have hPp := hP p
  simp only [Impl.step] at hs
  split_ifs at hs with hc
  rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
    ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ | ⟨cs, f, k, acc⟩ | r <;>
    simp [act, hpc] at hs <;> subst hs <;> rw [hpc] at hPp
  all_goals
    refine inv_tau_of ⟨hB, hMA, hH, hW, hComp, hP⟩ hs0
      (fun q hq => by simp [Function.update_of_ne hq]) ?_ ?_ ?_ ?_
  all_goals try (refine maInv_frame hMA ?_ ?_ ?_ <;> intros <;> simp [vL, vR, vMA] <;> done)
  all_goals try (refine hInv_frame hH ?_ <;> intros <;> simp [vH] <;> done)
  all_goals try (refine wInv_frame hW ?_ ?_ <;> simp [vL, vR] <;> done)
  all_goals try simp only [Function.update_self]
  case neg.wm.false.refine_3 => exact wInv_wm hrun hW hc hPp (by simp [vL]) (by simp [vR])
  case neg.wm.false.refine_4 => exact pfl_wm hrun hc hPp (by rw [hc1]; simp [vL])
  case neg.wm.true.refine_3 => exact wInv_wm hrun hW hc hPp (by simp [vL]) (by simp [vR])
  case neg.wm.true.refine_4 => exact pfl_wm hrun hc hPp (by rw [hc1]; simp [vR])
  case neg.rdR1.refine_4 => exact pfl_rdR1 hrun hPp
  case neg.rdL.refine_4 => exact pfl_rdL hrun hPp (by simp)
  case neg.rdR2.refine_4 => exact pfl_rdR2 hrun hPp (by simp)
  case neg.upL.refine_1 =>
    refine maInv_upL hrun hMA hPp (by simp [vL]) (by simp [vR]) (fun j => ?_)
    by_cases hj : j = idx m l r2
    · subst hj; simp [vMA]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]; simp only [vMA]
      rw [Function.update_of_ne (by simpa using hj)]
  case neg.upL.refine_4 => exact pfl_upL hPp (by simp) (by simp [vMA])
  case neg.upR.refine_1 =>
    refine maInv_upR hrun hMA hPp (by simp [vL]) (by simp [vR]) (fun j => ?_)
    by_cases hj : j = idx m l r2
    · subst hj; simp [vMA]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]; simp only [vMA]
      rw [Function.update_of_ne (by simpa using hj)]
  case neg.upR.refine_4 =>
    exact pfl_upR hPp (by simp) (by simp [vMA, Prod.le_def]) (by simp [vMA])
  case neg.scanMA.refine_4 => exact pfl_scanMA hrun hMA hPp (by simp)
  case neg.chkL.refine_4 => exact pfl_chkL hrun hPp (by simp)
  case neg.chkR.refine_4 => exact pfl_chkR hrun hPp (by simp)
  case neg.wH.refine_2 =>
    refine hInv_wH hH hPp (fun j => ?_)
    by_cases hj : j = p
    · subst hj; simp [vH]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]; simp only [vH]
      rw [Function.update_of_ne (by simpa using hj)]
  case neg.wH.refine_4 => exact pfl_wH hrun hPp hs0
  case neg.col.refine_4 => exact pfl_col hrun hH hPp hs0

/-- Preservation of the invariant by one step. -/
theorem inv_step {α : List (Lbl n)} {C C' : Cfg n} {ℓ : Lbl n}
    (hrun : (alg1 n m X).run α = some C) (hI : Inv m X α C)
    (hs : (alg1 n m X).step C ℓ = some C') : Inv m X (α ++ [ℓ]) C' := by
  obtain ⟨hB, hMA, hH, hW, hComp, hP⟩ := hI
  have hB' := (step_basic hB hs).1
  cases ℓ with
  | tau p => exact inv_tau hrun ⟨hB, hMA, hH, hW, hComp, hP⟩ hs
  | inv p o =>
    have hs0 := hs
    simp only [Impl.step] at hs
    split_ifs at hs with hc
    cases hs
    refine ⟨hB', maInv_frame hMA le_rfl le_rfl (fun _ => rfl), hInv_frame hH (fun _ => rfl),
      wInv_frame hW rfl rfl, fun x hx => ?_, fun q => ?_⟩
    · have hx' := (completed_append_of_not_ret (fun _ _ h => by cases h) x).1 hx
      exact opCert_append hx' (hComp x hx')
    · by_cases hq : q = p
      · subst hq
        have hidle : (opsOf α q).length = (respsOf α q).length :=
          (alg1 n m X).run_idle_counts hrun hc.1
        have hop : opOf (α ++ [.inv q o]) (curOp (α ++ [.inv q o]) q) = some o := by
          rw [curOp_append_inv, opOf_concat_inv]; simp [curOp, hidle]
        cases o with
        | upd0 v => simpa [PFL] using hop
        | upd1 v => simpa [PFL] using hop
        | scan =>
          simp only [Function.update_self, PFL]
          refine ⟨α.length + 1, by simp, ?_, ?_, ?_, ?_, ?_⟩
          · rw [List.take_of_length_le (by simp)]; exact Invoked.of_opOf_eq_some hop
          · intro v hv; rw [hop] at hv; cases hv
          · intro v hv; rw [hop] at hv; cases hv
          · simp only [csInit, hop]
          · simp [csInit]
      · simp only [Function.update_of_ne hq]
        exact pfl_append (C := C) (curOp_append_inv α p q o)
          (by simp [Function.update_of_ne hq]) (fun _ => le_rfl) (hP q)
  | ret p r =>
    simp only [Impl.step] at hs
    split_ifs at hs with hc
    have hPp := hP p
    rcases hpc : (C.loc p).pc with _ | ⟨_ | _, v⟩ | cs | ⟨cs, r1⟩ | ⟨cs, r1, l⟩ | ⟨cs, l, r2⟩ |
      ⟨cs, l, r2⟩ | ⟨cs, l, r2⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, l, r2, v⟩ | ⟨cs, v⟩ |
      ⟨cs, f, k, acc⟩ | r' <;>
      simp [act, hpc] at hs
    · exact absurd ((hB.1 p).2 hpc) hc
    obtain ⟨rfl, rfl⟩ := hs
    rw [hpc] at hPp
    obtain ⟨V, t0, t1, hcert, hinv, hret⟩ := hPp
    have hlen : t1 ≤ α.length := hcert.2.1
    refine ⟨hB', maInv_frame hMA le_rfl le_rfl (fun _ => rfl), hInv_frame hH (fun _ => rfl),
      wInv_frame hW rfl rfl, fun x hx => ?_, fun q => ?_⟩
    · rcases (completed_append_ret x).1 hx with hx' | rfl
      · exact opCert_append hx' (hComp x hx')
      · have hcur : (p, (respsOf α p).length) = curOp α p := rfl
        rw [hcur]
        have hinvα := invoked_of_take hinv
        have hop : opOf (α ++ [.ret p r]) (curOp α p) = opOf α (curOp α p) :=
          opOf_append_of_invoked hinvα
        have hrp : respOf (α ++ [.ret p r]) (curOp α p) = some r := by
          rw [respOf_append_ret]; simp [curOp]
        obtain ⟨h1, h2, h3⟩ := hret
        refine ⟨V, t0, t1, cert_append hcert,
          by rw [take_append_of_le (by have := hcert.1; omega)]; exact hinv,
          by
            rw [take_append_of_le hlen]; intro h
            have := h.mono (β := α.drop t1)
            rw [List.take_append_drop] at this
            exact not_completed_curOp α p this, ?_, ?_, ?_⟩
        · rw [hop, hrp]; intro h; rw [h1 h]
        · rw [hop, hrp]; intro v h; exact ⟨(h2 v h).1, by rw [(h2 v h).2]⟩
        · rw [hop, hrp]; intro v h; exact ⟨(h3 v h).1, by rw [(h3 v h).2]⟩
    · by_cases hq : q = p
      · subst hq; simp [PFL]
      · simp only [Function.update_of_ne hq]
        exact pfl_append (C := C) (curOp_append_ret_of_ne α r (Ne.symm hq))
          (by simp [Function.update_of_ne hq]) (fun _ => le_rfl) (hP q)

/-- The invariant holds in every reachable configuration. -/
theorem inv_run {α : List (Lbl n)} {C : Cfg n} (h : (alg1 n m X).run α = some C) :
    Inv m X α C := by
  refine Impl.run_induction (Q := fun α C => Inv m X α C) ?_
    (fun α C ℓ C' hr hI hs => inv_step hr hI hs) h
  refine ⟨basicInv_run (α := []) rfl, fun j hj => ?_, fun j hj => ?_, ⟨fun h => ?_, fun h => ?_⟩,
    fun x hx => ?_, fun q => ?_⟩
  · simp [vMA, Impl.initCfg, memInit] at hj
  · simp [vH, Impl.initCfg, memInit] at hj
  · simp [vL, Impl.initCfg, memInit] at h
  · simp [vR, Impl.initCfg, memInit] at h
  · simp [Completed] at hx
  · simp [Impl.initCfg, PFL]

end Podc.LongLivedSnapshotsPolylog
