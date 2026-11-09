import Papers.PODC2012.OptimismConcurrency.IRMInv
import Papers.PODC2012.OptimismConcurrency.KeptIdx

/-!
# `I_RM` rejects `σ_bad`; Theorem 3 is false

`irm_rejects : ¬ Accepts IRM sigmaBad`. In `σ_bad`, `remove(3)` returns `ok` from its write to
`X₁` (so, by Algorithm 1, it has set `r[X₃]`, `X₃` being the other object of its `rbuf`) before
`contains(4)` invokes its read of `X₃`; that read therefore returns `⊥` (line 15) in every
execution, so `contains(4)` cannot complete.

`theorem_3_false`: `σ_bad` is observable (`sigmaBad_observableStrong`) but rejected by `I_RM`,
contradicting Theorem 3 ("`I_RM` accepts all schedules that are observable").
-/

namespace Podc.OptimismConcurrency

/-! ## History lemmas -/

lemma Ev.erase_eq_inv {e : LEv ℕ} {p : ℕ} {o : SetOp} (h : e.erase = .inv p () o) :
    e = .inv p () o := by cases e <;> simp_all [Ev.erase]

lemma Ev.erase_eq_rinv {e : LEv ℕ} {p : ℕ} {y : Loc} (h : e.erase = .rinv p () y) :
    e = .rinv p () y := by cases e <;> simp_all [Ev.erase]

lemma Ev.erase_eq_winv {e : LEv ℕ} {p : ℕ} {y : Loc} {n : NodeV} (h : e.erase = .winv p () y n) :
    e = .winv p () y n := by cases e <;> simp_all [Ev.erase]

lemma Ev.erase_eq_rres {e : LEv ℕ} {p : ℕ} (h : e.erase = .rres p ()) :
    ∃ v, e = .rres p () v := by cases e <;> simp_all [Ev.erase]

lemma Ev.erase_eq_wres {e : LEv ℕ} {p : ℕ} (h : e.erase = .wres p ()) :
    ∃ b, e = .wres p () b := by cases e <;> simp_all [Ev.erase]

lemma Ev.isRes_erase {e : LEv ℕ} {p : ℕ} (hp : e.proc = p) (hr : e.isRes = true) :
    e.erase = .res p () := by cases e <;> simp_all [Ev.erase, Ev.isRes]

/-- The `a`-th event of the exported schedule is the erasure of the event at position
`kidx keepC H a` of `H`. -/
lemma exports_at {H : LHist ℕ} {σ : LSched ℕ} (h : Exports H σ) {a : ℕ} (ha : a < σ.length) :
    ∃ e, H[kidx keepC H a]? = some e ∧ σ[a]? = some e.erase ∧
      keepC e (H.drop (kidx keepC H a + 1)) = true ∧ (complete H)[a]? = some e := by
  have hlen : (complete H).length = σ.length := by rw [← h]; simp [sched]
  have haL : a < (lookFilter keepC H).length := by
    show a < (complete H).length; omega
  obtain ⟨h1, h2⟩ := getElem?_lookFilter keepC H a haL
  obtain ⟨hk, hkept⟩ := kidx_kept keepC H a haL
  refine ⟨H[kidx keepC H a], List.getElem?_eq_getElem hk, ?_, hkept, ?_⟩
  · rw [← h]; simp only [sched, List.getElem?_map]
    show (lookFilter keepC H)[a]?.map Ev.erase = _
    rw [h1, List.getElem?_eq_getElem hk]; rfl
  · show (lookFilter keepC H)[a]? = _
    rw [h1, List.getElem?_eq_getElem hk]

lemma exports_complete_at {H : LHist ℕ} {σ : LSched ℕ} (h : Exports H σ) {c : ℕ} {e : LEv ℕ}
    (he : (complete H)[c]? = some e) : σ[c]? = some e.erase := by
  rw [← h]; simp [sched, List.getElem?_map, he]

/-- Events of `p` before position `i`: one more event of `p` at `j`, none in between. -/
lemma evOf_take_step {H : LHist ℕ} {p : ℕ} {i j : ℕ} (hji : j < i) (hi : i ≤ H.length)
    (hj : H[j].proc = p)
    (hno : ∀ m (hm : m < H.length), j < m → m < i → H[m].proc ≠ p) :
    evOf (H.take i) p = evOf (H.take j) p ++ [H[j]] := by
  have e1 : H.take i = H.take j ++ [H[j]] ++ (H.drop (j + 1)).take (i - (j + 1)) := by
    rw [← List.take_succ_eq_append_getElem (by omega), ← List.take_add]
    congr 1; omega
  rw [e1, evOf, List.filter_append, List.filter_append]
  have e2 : List.filter (fun e => decide (e.proc = p)) ((H.drop (j + 1)).take (i - (j + 1))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
    simp only [List.length_take, List.length_drop] at hk
    simp only [List.getElem_take, List.getElem_drop, decide_eq_true_eq]
    exact hno (j + 1 + k) (by omega) (by omega) (by omega)
  rw [e2]; simp [evOf, hj]

lemma split_at {α : Type*} (H : List α) (j : ℕ) (hj : j < H.length) :
    H = H.take j ++ H[j] :: H.drop (j + 1) := by
  rw [List.getElem_cons_drop, List.take_append_drop]

lemma drop_split {α : Type*} (H : List α) {i j : ℕ} (hij : i < j) (hj : j < H.length) :
    H.drop (i + 1) = (H.drop (i + 1)).take (j - i - 1) ++ H[j] :: H.drop (j + 1) := by
  have h := split_at (H.drop (i + 1)) (j - i - 1) (by simp; omega)
  rw [h]; congr 2
  · simp only [List.getElem_drop]; congr 1; omega
  · rw [List.drop_drop]; congr 1; omega

lemma mem_take_drop {α : Type*} {H : List α} {i d : ℕ} {e : α}
    (he : e ∈ (H.drop (i + 1)).take d) : ∃ m, ∃ hm : m < H.length, i < m ∧ m < i + 1 + d ∧ H[m] = e := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
  simp only [List.length_take, List.length_drop] at hk
  exact ⟨i + 1 + k, by omega, by omega, by omega, by simp [List.getElem_take, List.getElem_drop]⟩

/-! ## The rejection -/

/-- **`I_RM` rejects `σ_bad`.** -/
theorem irm_rejects : ¬ Accepts IRM sigmaBad := by
  rintro ⟨H, ⟨tv, L, c, hrun, hH⟩, hexp⟩
  have hlen : sigmaBad.length = 50 := by decide
  have hcl : (complete H).length = 50 := by
    rw [← hlen, ← hexp]; simp [sched]
  set K := kidx keepC H with hK
  -- the events at the relevant positions
  have ev : ∀ a, a < 50 → ∃ e, H[K a]? = some e ∧ sigmaBad[a]? = some e.erase ∧
      keepC e (H.drop (K a + 1)) = true ∧ (complete H)[a]? = some e :=
    fun a ha => exports_at hexp (by omega)
  have hKlt : ∀ a, a < 50 → K a < H.length := fun a ha =>
    (getElem?_lookFilter keepC H a (by show a < (complete H).length; omega)).2
  have hKmono : ∀ a b, a < 50 → b < 50 → (K a < K b ↔ a < b) := fun a b ha hb =>
    kidx_lt_iff keepC H (by show a < (complete H).length; omega)
      (by show b < (complete H).length; omega)
  -- windows
  have win : ∀ a b p, a < b → b < 50 →
      (∀ e : LEv ℕ, sigmaBad[a]? = some e.erase → e.proc = p ∧ e.isRes = false) →
      (∀ c, a < c → c < b → sigmaBad[c]? ≠ some (.res p ())) →
      ∀ m (hm : m < H.length), K a < m → m < K b → H[m].proc = p →
        ∃ c, a < c ∧ c < b ∧ K c = m := by
    intro a b p hab hb hpa hno m hm h1 h2 hp
    refine window H hab (by omega) (p := p) (x := ()) ?_ ?_ m hm h1 h2 hp rfl
    · intro e he
      obtain ⟨e', he', hs, -⟩ := ev a (by omega)
      rw [he'] at he; injection he with he; subst he
      exact ⟨(hpa _ hs).1, rfl, (hpa _ hs).2⟩
    · rintro c hac hcb e he ⟨hp', -, hr⟩
      exact hno c hac hcb (by rw [exports_complete_at hexp he, Ev.isRes_erase hp' hr])
  -- no events of `p` strictly between consecutive positions
  have gap : ∀ a b p, a < b → b < 50 →
      (∀ e : LEv ℕ, sigmaBad[a]? = some e.erase → e.proc = p ∧ e.isRes = false) →
      (∀ c, a < c → c < b → sigmaBad[c]? ≠ some (.res p ())) →
      ∀ d, a ≤ d → d + 1 ≤ b → ∀ m (hm : m < H.length), K d < m → m < K (d + 1) →
        H[m].proc ≠ p := by
    intro a b p hab hb hpa hno d had hdb m hm h1 h2 hp
    have hKad : K a ≤ K d := by
      rcases had.lt_or_eq with h | h
      · exact ((hKmono a d (by omega) (by omega)).2 h).le
      · rw [h]
    have hKdb : K (d + 1) ≤ K b := by
      rcases (show d + 1 ≤ b from hdb).lt_or_eq with h | h
      · exact ((hKmono _ b (by omega) (by omega)).2 h).le
      · rw [h]
    obtain ⟨c, -, hcb, hc⟩ := win a b p hab hb hpa hno m hm (by omega) (by omega) hp
    have hc1 : c < 50 := by omega
    have := (hKmono d c (by omega) hc1).1 (by rw [hc]; exact h1)
    have := (hKmono c (d + 1) hc1 (by omega)).1 (by rw [hc]; exact h2)
    omega
  -- the events of `σ_bad` at the relevant positions
  have get : ∀ a (ha : a < 50) (σa : SEv ℕ Unit SetOp Loc NodeV), sigmaBad[a]? = some σa →
      ∃ e, H[K a]? = some e ∧ e.erase = σa ∧ keepC e (H.drop (K a + 1)) = true := by
    intro a ha σa hσ
    obtain ⟨e, h1, h2, h3, -⟩ := ev a ha
    rw [hσ] at h2; injection h2 with h2
    exact ⟨e, h1, h2.symm, h3⟩
  obtain ⟨e35, h35, s35, -⟩ := get 35 (by norm_num) _ (by decide : sigmaBad[35]? = some (.inv 2 () (.remove 3)))
  obtain ⟨e36, h36, s36, -⟩ := get 36 (by norm_num) _ (by decide : sigmaBad[36]? = some (.rinv 2 () headL))
  obtain ⟨e37, h37, s37, -⟩ := get 37 (by norm_num) _ (by decide : sigmaBad[37]? = some (.rres 2 ()))
  obtain ⟨e38, h38, s38, -⟩ := get 38 (by norm_num) _ (by decide : sigmaBad[38]? = some (.rinv 2 () (Xl 1)))
  obtain ⟨e39, h39, s39, k39⟩ := get 39 (by norm_num) _ (by decide : sigmaBad[39]? = some (.rres 2 ()))
  obtain ⟨e40, h40, s40, -⟩ := get 40 (by norm_num) _ (by decide : sigmaBad[40]? = some (.rinv 2 () (Xl 3)))
  obtain ⟨e41, h41, s41, k41⟩ := get 41 (by norm_num) _ (by decide : sigmaBad[41]? = some (.rres 2 ()))
  obtain ⟨e42, h42, s42, -⟩ := get 42 (by norm_num) _
    (by decide : sigmaBad[42]? = some (.winv 2 () (Xl 1) ⟨.fin 1, Xl 4⟩))
  obtain ⟨e43, h43, s43, k43⟩ := get 43 (by norm_num) _ (by decide : sigmaBad[43]? = some (.wres 2 ()))
  obtain ⟨e45, h45, s45, -⟩ := get 45 (by norm_num) _ (by decide : sigmaBad[45]? = some (.rinv 1 () (Xl 3)))
  obtain ⟨e46, h46, s46, k46⟩ := get 46 (by norm_num) _ (by decide : sigmaBad[46]? = some (.rres 1 ()))
  obtain rfl := Ev.erase_eq_inv s35
  obtain rfl := Ev.erase_eq_rinv s36
  obtain ⟨v37, rfl⟩ := Ev.erase_eq_rres s37
  obtain rfl := Ev.erase_eq_rinv s38
  obtain ⟨v39, rfl⟩ := Ev.erase_eq_rres s39
  obtain rfl := Ev.erase_eq_rinv s40
  obtain ⟨v41, rfl⟩ := Ev.erase_eq_rres s41
  obtain rfl := Ev.erase_eq_winv s42
  obtain ⟨b43, rfl⟩ := Ev.erase_eq_wres s43
  obtain rfl := Ev.erase_eq_rinv s45
  obtain ⟨v46, rfl⟩ := Ev.erase_eq_rres s46
  -- kept reads and writes did not abort
  obtain ⟨n39, rfl⟩ : ∃ n, v39 = some n := by
    have := kept_not_abort k39
    cases v39 with
    | none => simp [Ev.isAbort] at this
    | some n => exact ⟨n, rfl⟩
  obtain ⟨n41, rfl⟩ : ∃ n, v41 = some n := by
    have := kept_not_abort k41
    cases v41 with
    | none => simp [Ev.isAbort] at this
    | some n => exact ⟨n, rfl⟩
  obtain ⟨n46, rfl⟩ : ∃ n, v46 = some n := by
    have := kept_not_abort k46
    cases v46 with
    | none => simp [Ev.isAbort] at this
    | some n => exact ⟨n, rfl⟩
  obtain rfl : b43 = true := by
    have := kept_not_abort k43
    cases b43 with
    | false => simp [Ev.isAbort] at this
    | true => rfl
  -- no other events of process 2 between positions `K 35` and `K 43`
  have gap2 := gap 35 44 2 (by norm_num) (by norm_num)
    (fun e he => by
      rw [(by decide : sigmaBad[35]? = some (.inv 2 () (.remove 3)))] at he
      injection he with he; rw [Ev.erase_eq_inv he.symm]; simp [Ev.isRes])
    (fun c h1 h2 => by interval_cases c <;> decide)
  have gap1 := gap 45 46 1 (by norm_num) (by norm_num)
    (fun e he => by
      rw [(by decide : sigmaBad[45]? = some (.rinv 1 () (Xl 3)))] at he
      injection he with he; rw [Ev.erase_eq_rinv he.symm]; simp [Ev.isRes])
    (fun c h1 h2 => by omega)
  have hget : ∀ a (ha : a < 50) e, H[K a]? = some e → H[K a]'(hKlt a ha) = e := fun a ha e he => by
    rw [List.getElem?_eq_getElem (hKlt a ha)] at he; exact Option.some.inj he
  have stepE : ∀ d (hd : d < 49) e, 35 ≤ d → d ≤ 42 → H[K d]? = some e → e.proc = 2 →
      evOf (H.take (K (d + 1))) 2 = evOf (H.take (K d)) 2 ++ [e] := by
    intro d hd e h1 h2 he hp
    rw [← hget d (by omega) e he]
    exact evOf_take_step ((hKmono d (d + 1) (by omega) (by omega)).2 (by omega))
      (hKlt (d + 1) (by omega)).le (by rw [hget d (by omega) e he]; exact hp)
      (fun m hm hm1 hm2 => gap2 d (by omega) (by omega) m hm hm1 hm2)
  have hev43 : evOf (H.take (K 43)) 2 = evOf (H.take (K 35)) 2 ++
      [.inv 2 () (.remove 3), .rinv 2 () headL, .rres 2 () v37, .rinv 2 () (Xl 1),
        .rres 2 () (some n39), .rinv 2 () (Xl 3), .rres 2 () (some n41),
        .winv 2 () (Xl 1) ⟨.fin 1, Xl 4⟩] := by
    rw [stepE 42 (by norm_num) _ (by norm_num) (by norm_num) h42 rfl,
      stepE 41 (by norm_num) _ (by norm_num) (by norm_num) h41 rfl,
      stepE 40 (by norm_num) _ (by norm_num) (by norm_num) h40 rfl,
      stepE 39 (by norm_num) _ (by norm_num) (by norm_num) h39 rfl,
      stepE 38 (by norm_num) _ (by norm_num) (by norm_num) h38 rfl,
      stepE 37 (by norm_num) _ (by norm_num) (by norm_num) h37 rfl,
      stepE 36 (by norm_num) _ (by norm_num) (by norm_num) h36 rfl,
      stepE 35 (by norm_num) _ (by norm_num) (by norm_num) h35 rfl]
    simp
  have hlastEv : lastEv (H.take (K 43)) 2 = some (.winv 2 () (Xl 1) ⟨.fin 1, Xl 4⟩) := by
    rw [lastEv, hev43]; simp
  have hlastInv : lastInv (H.take (K 43)) 2 = some (.remove 3) := by
    have hf : List.filterMap invOp [(Ev.inv 2 () (SetOp.remove 3) : LEv ℕ), .rinv 2 () headL,
        .rres 2 () v37, .rinv 2 () (Xl 1), .rres 2 () (some n39), .rinv 2 () (Xl 3),
        .rres 2 () (some n41), .winv 2 () (Xl 1) ⟨.fin 1, Xl 4⟩] = [SetOp.remove 3] := rfl
    rw [lastInv, hev43, List.filterMap_append, hf]; simp
  have hreads : (readObjs (H.take (K 43)) 2).take 2 = [Xl 3, Xl 1] := by
    rw [readObjs, rdState, hev43, List.foldl_append]
    rcases (evOf (H.take (K 35)) 2).foldl rdStep (none, []) with ⟨a, l⟩
    simp [rdStep]
  -- the step emitting the `ok` of the write of `remove(3)`
  obtain ⟨L1, L2, c1, c2, hr1, hst, hr2, hf1, hf2⟩ := hrun.split (A := H.take (K 43))
    (B := H.drop (K 43 + 1)) (e := .wres 2 () true)
    (by rw [hH, ← hget 43 (by norm_num) _ h43]; exact split_at H _ (hKlt 43 (by norm_num)))
  have hI1 : InvAt c1 (H.take (K 43)) 2 := by rw [← hf1]; exact hr1.inv 2
  have hmark : c2.rf (Xl 3) = true := by
    cases hst with
    | mok q y n z hpc =>
      obtain ⟨hle, -, ⟨w, hfind⟩, hrf⟩ := hI1.rm y n _ hpc
      rw [hlastEv] at hle
      simp only [Option.some.injEq, Ev.winv.injEq] at hle
      obtain ⟨-, -, rfl, rfl⟩ := hle
      have hrb := hI1.rbuf
      rw [hreads] at hrb
      obtain ⟨⟨z1, w1⟩, rest, hrb1, hz1, hrest⟩ := List.map_eq_cons_iff.1 hrb
      obtain ⟨⟨z2, w2⟩, rest2, rfl, hz2, hrest2⟩ := List.map_eq_cons_iff.1 hrest
      simp only at hz1 hz2; subst hz1; subst hz2
      rw [List.map_eq_nil_iff] at hrest2; subst hrest2
      rw [hrb1] at hfind
      simp [Xl] at hfind
      obtain ⟨rfl, -⟩ := hfind
      simpa [Xl] using hrf
    | iok q y n hpc =>
      have := (hI1.ins y n _ hpc).2 3
      rw [hI1.kind, hlastInv] at this; exact absurd rfl this
    | aok q y n hpc =>
      have := (hI1.alc y n _ hpc).2 3
      rw [hI1.kind, hlastInv] at this; exact absurd rfl this
  -- the read of `X₃` by `contains(4)` starts after the mark was set
  have h4543 : K 43 < K 45 := (hKmono 43 45 (by norm_num) (by norm_num)).2 (by norm_num)
  have h4645 : K 45 < K 46 := (hKmono 45 46 (by norm_num) (by norm_num)).2 (by norm_num)
  obtain ⟨L3, L4, c3, c4, hr3, hst45, hr4, -, hf4⟩ := hr2.split
    (A := (H.drop (K 43 + 1)).take (K 45 - K 43 - 1)) (B := H.drop (K 45 + 1))
    (e := .rinv 1 () (Xl 3))
    (by rw [hf2, ← hget 45 (by norm_num) _ h45]; exact drop_split H h4543 (hKlt 45 (by norm_num)))
  have hrf3 : c3.rf (Xl 3) = true := hr3.rf_mono hmark
  have hpc4 : (c4.loc 1).pc = some (.rd (Xl 3) true .l11) := by
    cases hst45 with
    | rinv q y hpc => simp [hrf3]
  obtain ⟨L5, L6, c5, c6, hr5, hst46, -, hf5, -⟩ := hr4.split
    (A := (H.drop (K 45 + 1)).take (K 46 - K 45 - 1)) (B := H.drop (K 46 + 1))
    (e := .rres 1 () (some n46))
    (by rw [hf4, ← hget 46 (by norm_num) _ h46]; exact drop_split H h4645 (hKlt 46 (by norm_num)))
  have hno1 : ∀ e ∈ L5.filterMap id, e.proc ≠ 1 := by
    rw [hf5]; intro e he
    obtain ⟨m, hm, hm1, hm2, rfl⟩ := mem_take_drop he
    exact gap1 45 le_rfl le_rfl m hm hm1 (by show m < K 46; omega)
  obtain ⟨s', hs'⟩ := hr5.rd_preserved hno1 hpc4
  have hrun5 : RRun (rcfg0 tv)
      (L1 ++ [some (.wres 2 () true)] ++ L3 ++ [some (.rinv 1 () (Xl 3))] ++ L5) c5 :=
    (((hr1.append (RRun.single hst)).append hr3).append (RRun.single hst45)).append hr5
  obtain ⟨-, hgood⟩ := (hrun5.inv 1).rd _ _ _ hs'
  have hg := hgood rfl
  -- the read returns `⊥`: `contains(4)` cannot complete
  cases hst46 with
  | rret q y g v1 res hpc =>
    rw [hs'] at hpc
    simp only [Option.some.injEq, RPc.rd.injEq] at hpc
    obtain ⟨-, -, rfl⟩ := hpc
    simp [RdGood] at hg

/-- **Theorem 3 (Optimality) is false.** The schedule `σ_bad` is observable (even in the strong
sense: an honest LS-linearizable history exports it, and every `contains(v)` run afterwards on
the actual memory keeps the history LS-linearizable), but `I_RM` does not accept it. -/
theorem theorem_3_false :
    ObservableStrong sigmaBad ∧ Observable sigmaBad ∧ ¬ Accepts IRM sigmaBad :=
  ⟨sigmaBad_observableStrong, sigmaBad_observable, irm_rejects⟩

/-- Theorem 3 as stated, refuted: it is not the case that `I_RM` accepts all observable
schedules. -/
theorem not_theorem_3 : ¬ ∀ σ : LSched ℕ, Observable σ → Accepts IRM σ :=
  fun h => irm_rejects (h _ sigmaBad_observable)

end Podc.OptimismConcurrency
