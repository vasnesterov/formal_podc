import Papers.PODC2010.AsymmetricProgress.Valency

-- CSLib candidate: shared memory with caller-aware, possibly blocking base objects; valency
-- toolkit (deciders, critical configurations, all processes poised on one object).

/-!
# Deciders and critical configurations: Lemmas 4–9

* `exists_exec_of_chain` — an infinite chain of finite extensions gives an infinite schedule
  (used for the bivalence-preserving scheduling disciplines of Lemmas 4 and 7);
* `lemma4` — wait-freedom of `p` gives a bivalent configuration at which `p` is a decider;
* `lemma7` — fault-freedom of one process gives a bivalent configuration with a decider;
* `lemma5` (= Lemma 8) — from a bivalent configuration with a decider `p`: a configuration `D`
  and `q ≠ p` with `D p`, `D q p` univalent and incompatible, and `p`, `q` poised on the same
  non-read/write-like object;
* `lemma6` (= Lemma 9) — moreover *all* `n` processes are poised on that object.

The proof of Lemma 6 in the paper applies Lemma 1 to the pairs `(x, y)` and `(xq, yq)`, claiming
that "the state of all the objects that `p` can access" is the same in them. This is not true
when the steps of `s` in `y − x` write registers (which `p` can access). We use instead that the
step of `p` (on `o`) commutes with the steps of `s` (which avoid `o`): `y p = x p (y − x)`
(`run_comm_of_avoids`), so `y p` is an extension of `x p` (and `y q p` of `x q p`).
-/

namespace Podc.AsymmetricProgress

set_option linter.unusedSectionVars false

variable {n : ℕ} {ι : Type} [DecidableEq ι] {T : ι → BObj n} {A : Alg n T}

/-! ## Infinite schedules from chains of extensions -/

section Chain

variable (C₀ : Cfg A) (g : ℕ → Cfg A → List (Fin n))

/-- The configurations of a chain: `C₀`, and then extend by `g k C`. -/
def chainCfg : ℕ → Cfg A
  | 0 => C₀
  | k + 1 => run (chainCfg k) (g k (chainCfg k))

/-- The schedule leading to `chainCfg C₀ g k`. -/
def chainSched : ℕ → List (Fin n)
  | 0 => []
  | k + 1 => chainSched k ++ g k (chainCfg C₀ g k)

lemma run_chainSched (k : ℕ) : run C₀ (chainSched C₀ g k) = chainCfg C₀ g k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [chainSched, chainCfg, run_append, ih]

lemma chainSched_prefix (k m : ℕ) : chainSched C₀ g k <+: chainSched C₀ g (k + m) := by
  induction m with
  | zero => exact List.prefix_refl _
  | succ m ih =>
    exact ih.trans (List.prefix_append _ _)

lemma length_chainSched (hne : ∀ k C, g k C ≠ []) (k : ℕ) : k ≤ (chainSched C₀ g k).length := by
  induction k with
  | zero => simp [chainSched]
  | succ k ih =>
    rw [chainSched, List.length_append]
    have := List.length_pos_of_ne_nil (hne k (chainCfg C₀ g k))
    omega

/-- An infinite chain of extensions `C₀ → run C₀ (g 0 C₀) → …` (each nonempty) yields an
infinite schedule `e` all of whose prefixes extend to configurations of the chain, and in which,
for every `k`, the process `r k ∈ g k _` occurs at some time `≥ k`. -/
theorem exists_exec_of_chain (P : Cfg A → Prop) (h0 : P C₀) (hg : ∀ k C, P C → P (run C (g k C)))
    (hne : ∀ k C, g k C ≠ []) (r : ℕ → Fin n) (hr : ∀ k C, r k ∈ g k C) :
    ∃ e : ℕ → Fin n, (∀ t, ∃ τ, P (run (run C₀ (pre e t)) τ)) ∧ ∀ k, ∃ t ≥ k, e t = r k := by
  set S := chainSched C₀ g with hS
  have hP : ∀ k, P (chainCfg C₀ g k) := by
    intro k; induction k with
    | zero => exact h0
    | succ k ih => exact hg k _ ih
  have hlen : ∀ k, k ≤ (S k).length := length_chainSched C₀ g hne
  have hpre : ∀ k k', S k <+: S k' ∨ S k' <+: S k := by
    intro k k'
    rcases le_total k k' with h | h
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h; exact Or.inl (chainSched_prefix _ _ _ _)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h; exact Or.inr (chainSched_prefix _ _ _ _)
  have hget : ∀ k k' t (h : t < (S k).length) (h' : t < (S k').length),
      (S k)[t] = (S k')[t] := by
    intro k k' t h h'
    rcases hpre k k' with hp | hp
    · exact (hp.getElem h).symm ▸ rfl
    · exact (hp.getElem h').symm ▸ rfl
  let e : ℕ → Fin n := fun t => (S (t + 1))[t]'(by have := hlen (t + 1); omega)
  have he : ∀ k t (h : t < (S k).length), e t = (S k)[t] := fun k t h => hget _ _ _ _ _
  have hpe : ∀ t, pre e t = (S t).take t := by
    intro t
    apply List.ext_getElem
    · simp [length_pre]; exact hlen t
    · intro l h1 h2
      simp only [pre, List.getElem_map, List.getElem_range, List.getElem_take]
      rw [length_pre] at h1
      exact he t l (by have := hlen t; omega)
  refine ⟨e, fun t => ⟨(S t).drop t, ?_⟩, fun k => ?_⟩
  · rw [hpe, ← run_append, List.take_append_drop, hS, run_chainSched]
    exact hP t
  · obtain ⟨l, hl, hlr⟩ := List.getElem_of_mem (hr k (chainCfg C₀ g k))
    refine ⟨(S k).length + l, by have := hlen k; omega, ?_⟩
    have hk1 : S (k + 1) = S k ++ g k (chainCfg C₀ g k) := rfl
    have hlt : (S k).length + l < (S (k + 1)).length := by
      rw [hk1, List.length_append]; omega
    rw [he (k + 1) _ hlt]
    simp only [hk1, List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact hlr

end Chain

/-! ## Lemma 4 and Lemma 7: a bivalent configuration with a decider -/

/-- **Lemma 4** of the paper. In a consensus algorithm (`n ≥ 2`) that is obstruction-free for
all processes and wait-free for `p` — e.g. an `(n,1)`-live consensus object — there is a
reachable bivalent configuration at which `p` is a decider. -/
theorem lemma4 (hS : Safe A) (hOF : ∀ r, OFree A r) (hn : 2 ≤ n) {p : Fin n}
    (hWF : WFree A p) : ∃ C : Cfg A, Reachable C ∧ Biv C ∧ Decider C p := by
  by_contra hcon
  push Not at hcon
  have hext : ∀ C : Cfg A, Reachable C ∧ Biv C → ∃ σ, Biv (run C (σ ++ [p])) := by
    rintro C ⟨hC, hb⟩
    have := hcon C hC hb
    simpa [Decider] using this
  obtain ⟨x, hx⟩ := lemma3 hS hOF hn
  classical
  let g : ℕ → Cfg A → List (Fin n) := fun _ C =>
    if h : Reachable C ∧ Biv C then (hext C h).choose ++ [p] else [p]
  obtain ⟨e, he1, he2⟩ := exists_exec_of_chain (initCfg A x) g (fun C => Reachable C ∧ Biv C)
    ⟨reachable_initCfg x, hx⟩
    (by
      intro k C hC
      simp only [g, hC, and_self, ↓reduceDIte]
      exact ⟨hC.1.run _, (hext C hC).choose_spec⟩)
    (by intro k C; simp only [g]; split <;> simp)
    (fun _ => p) (by intro k C; simp only [g]; split <;> simp)
  obtain ⟨t, v, ht⟩ := hWF x e (fun M => he2 M)
  obtain ⟨τ, hτ1, hτ2⟩ := he1 t
  exact hτ2.not_out hS hτ1 p v (ht.run τ)

/-- **Lemma 7** of the paper. In a consensus algorithm (`n ≥ 2`) that is obstruction-free for
all processes and fault-free for some process, there is a reachable bivalent configuration with
a decider. -/
theorem lemma7 (hS : Safe A) (hOF : ∀ r, OFree A r) (hn : 2 ≤ n) {p₀ : Fin n}
    (hFF : FFree A p₀) : ∃ (C : Cfg A) (p : Fin n), Reachable C ∧ Biv C ∧ Decider C p := by
  by_contra hcon
  push Not at hcon
  have hext : ∀ (C : Cfg A) (q : Fin n), Reachable C ∧ Biv C → ∃ σ, Biv (run C (σ ++ [q])) := by
    rintro C q ⟨hC, hb⟩
    have := hcon C q hC hb
    simpa [Decider] using this
  obtain ⟨x, hx⟩ := lemma3 hS hOF hn
  classical
  let r : ℕ → Fin n := fun k => ⟨k % n, Nat.mod_lt _ (by omega)⟩
  let g : ℕ → Cfg A → List (Fin n) := fun k C =>
    if h : Reachable C ∧ Biv C then (hext C (r k) h).choose ++ [r k] else [r k]
  obtain ⟨e, he1, he2⟩ := exists_exec_of_chain (initCfg A x) g (fun C => Reachable C ∧ Biv C)
    ⟨reachable_initCfg x, hx⟩
    (by
      intro k C hC
      simp only [g, hC, and_self, ↓reduceDIte]
      exact ⟨hC.1.run _, (hext C (r k) hC).choose_spec⟩)
    (by intro k C; simp only [g]; split <;> simp)
    r (by intro k C; simp only [g]; split <;> simp)
  have hfair : ∀ q M, ∃ t ≥ M, e t = q := by
    intro q M
    obtain ⟨t, ht, hte⟩ := he2 (M * n + q.val)
    refine ⟨t, le_trans (by nlinarith) ht, ?_⟩
    rw [hte]
    ext
    simp [r, Nat.add_mod, Nat.mod_eq_of_lt q.isLt]
  obtain ⟨t, v, ht⟩ := hFF x e hfair
  obtain ⟨τ, hτ1, hτ2⟩ := he1 t
  exact hτ2.not_out hS hτ1 p₀ v (ht.run τ)

/-! ## Lemma 5 (and Lemma 8) -/

/-- From a decision `w` reachable from `C`, one reaches a configuration `C τ p` from which `w`
can be decided, with `p ∉ τ`. -/
lemma exists_prefix_without (p : Fin n) {w : Bool} :
    ∀ (σ : List (Fin n)) (C : Cfg A) (r : Fin n), (run C σ).Out r w →
      ∃ τ, p ∉ τ ∧ CanDec (run C (τ ++ [p])) w
  | [], C, r, h => ⟨[], by simp, (h.step p).run [] |> fun h' => ⟨[], r, h'⟩⟩
  | a :: σ, C, r, h => by
    by_cases ha : a = p
    · subst ha
      exact ⟨[], by simp, σ, r, h⟩
    · obtain ⟨τ, hτ, hc⟩ := exists_prefix_without p σ (C.step a) r h
      exact ⟨a :: τ, by simp [Ne.symm ha, hτ], by simpa using hc⟩

/-- **Lemma 5** of the paper (and Lemma 8, which has the same proof). From a reachable bivalent
configuration `C` at which `p` is a decider, there are an extension `D` of `C` and a process
`q ≠ p` such that `p` is a decider at the bivalent configuration `D`, the runs `D p` and `D q p`
are univalent and not compatible, and `p` and `q` are poised on the same object, which is not
read/write-like. -/
theorem lemma5 (hOF : ∀ r, OFree A r) {C : Cfg A} {p : Fin n} (hC : Reachable C)
    (hb : Biv C) (hd : Decider C p) :
    ∃ (D : Cfg A) (q : Fin n) (v : Bool), Reachable D ∧ Biv D ∧ Decider D p ∧ p ≠ q ∧
      Val (D.step p) v ∧ Val ((D.step q).step p) (!v) ∧
      ∃ i, D.objOf p = some i ∧ D.objOf q = some i ∧ ¬ (T i).RWLike := by
  -- `C p` is univalent, say `v`-valent
  have hnb : ∀ σ, ¬ Biv (run C (σ ++ [p])) := hd
  obtain ⟨v, hv⟩ := exists_canDec (hOF p) (hC.step p)
  have hCp : Val (C.step p) v := val_of_not_biv (hnb []) hv
  -- some extension `C τ p` with `p ∉ τ` is `!v`-valent
  obtain ⟨σ, r, hr⟩ := biv_iff.1 hb (!v)
  obtain ⟨τ, hpτ, hτ⟩ := exists_prefix_without p σ C r hr
  have hτv : Val (run C (τ ++ [p])) (!v) := val_of_not_biv (hnb τ) hτ
  -- walk along `τ`
  let f : ℕ → Prop := fun j => Val (run C (τ.take j ++ [p])) v
  have hf0 : f 0 := by simpa [f] using hCp
  have hfl : ¬ f τ.length := by
    intro h
    simp only [f, List.take_length] at h
    obtain ⟨u, hu⟩ := exists_canDec (hOF p) (hC.run (τ ++ [p]))
    have := (h.eq hu).symm.trans (hτv.eq hu)
    cases v <;> simp at this
  classical
  have hex : ∃ j, ¬ f j := ⟨_, hfl⟩
  obtain ⟨j, hjf, hjmin, hjle⟩ : ∃ j, ¬ f j ∧ (∀ m < j, f m) ∧ j ≤ τ.length :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by simpa using Nat.find_min hex hm,
      Nat.find_min' hex hfl⟩
  have hj0 : j ≠ 0 := fun h => hjf (h ▸ hf0)
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hj'f : f j' := hjmin j' (by omega)
  have hj'lt : j' < τ.length := by omega
  set D := run C (τ.take j') with hD
  set q := τ[j'] with hq
  have hDq : D.step q = run C (τ.take (j' + 1)) := by
    rw [List.take_succ_eq_append_getElem hj'lt, run_concat]
  have hDp : Val (D.step p) v := by simpa [f, run_concat] using hj'f
  have hDqp : Val ((D.step q).step p) (!v) := by
    rw [hDq, ← run_concat]
    obtain ⟨u, hu⟩ := exists_canDec (hOF p) (hC.run (τ.take (j' + 1) ++ [p]))
    have hu' : Val (run C (τ.take (j' + 1) ++ [p])) u := by
      have := hd (τ.take (j' + 1))
      exact val_of_not_biv this hu
    have : u ≠ v := fun huv => hjf (by simpa [f, huv] using hu')
    have : u = !v := by cases u <;> cases v <;> simp_all
    rwa [← this]
  have hpq : p ≠ q := fun h => hpτ (by rw [h, hq]; exact List.getElem_mem _)
  have hDr : Reachable D := hC.run _
  obtain ⟨u1, hu1⟩ := exists_canDec (hOF p) (hDr.step p)
  obtain ⟨u2, hu2⟩ := exists_canDec (hOF p) ((hDr.step q).step p)
  have hbD : Biv D := by
    refine Biv.of_val (σ := [p]) (τ := [q, p]) hDp ?_ hDqp ?_
    · rw [← hDp.eq hu1]; exact hu1
    · rw [← hDqp.eq hu2]; exact hu2
  exact ⟨D, q, v, hDr, hbD, hd.run _, hpq, hDp, hDqp, lemma2 hOF hDr hpq hDp hDqp⟩

/-! ## Lemma 6 (and Lemma 9) -/

/-- The invariant of the induction in the proof of Lemma 6: `D` is reachable and bivalent, `p` is
a decider at `D`, `D p` is `v`-valent and `D q p` is `(!v)`-valent, and all processes of `K`
(which contains `p` and `q`) are poised on the object `i`. -/
def CritK (D : Cfg A) (p q : Fin n) (v : Bool) (i : ι) (K : Finset (Fin n)) : Prop :=
  Reachable D ∧ Biv D ∧ Decider D p ∧ p ≠ q ∧ Val (D.step p) v ∧ Val ((D.step q).step p) (!v) ∧
    p ∈ K ∧ q ∈ K ∧ ∀ r ∈ K, D.objOf r = some i

/-- The induction step of Lemma 6 (with the repaired argument, see the module docstring). -/
theorem CritK.extend (hS : Safe A) (hOF : ∀ r, OFree A r) {D : Cfg A} {p q : Fin n} {v : Bool}
    {i : ι} {K : Finset (Fin n)} (h : CritK D p q v i K) {s : Fin n} (hs : s ∉ K) :
    ∃ D' : Cfg A, CritK D' p q v i (insert s K) := by
  obtain ⟨hD, hb, hd, hpq, hDp, hDqp, hpK, hqK, hK⟩ := h
  have hsp : s ≠ p := fun h => hs (h ▸ hpK)
  have hsq : s ≠ q := fun h => hs (h ▸ hqK)
  have hpi : D.objOf p = some i := hK p hpK
  have hqi : D.objOf q = some i := hK q hqK
  have hnot : ∀ {r} (j : ℕ), r ≠ s → r ∉ List.replicate j s := fun j h hm =>
    h (List.eq_of_mem_replicate hm)
  -- commutation along a run of `s` avoiding `i`
  have hcomm : ∀ j, Avoids D (List.replicate j s) i →
      Val ((run D (List.replicate j s)).step p) v ∧
        Val (((run D (List.replicate j s)).step q).step p) (!v) := by
    intro j hav
    constructor
    · rw [← run_concat, run_comm_of_avoids hpi hav (hnot j hsp.symm)]
      exact hDp.run _
    · have h1 : run D (List.replicate j s ++ [q]) = run (D.step q) (List.replicate j s) :=
        run_comm_of_avoids hqi hav (hnot j hsq.symm)
      have hav' : Avoids (D.step q) (List.replicate j s) i :=
        hav.step_of_poised hqi (hnot j hsq.symm)
      have h2 : run (D.step q) (List.replicate j s ++ [p]) =
          run ((D.step q).step p) (List.replicate j s) :=
        run_comm_of_avoids (by rw [objOf_step_other D hpq]; exact hpi) hav' (hnot j hsp.symm)
      rw [← run_concat, h1, ← run_concat, h2]
      exact hDqp.run _
  have hbiv : ∀ j, Avoids D (List.replicate j s) i → Biv (run D (List.replicate j s)) := by
    intro j hav
    obtain ⟨h1, h2⟩ := hcomm j hav
    have hr := hD.run (List.replicate j s)
    obtain ⟨u1, hu1⟩ := exists_canDec (hOF p) (hr.step p)
    obtain ⟨u2, hu2⟩ := exists_canDec (hOF p) ((hr.step q).step p)
    refine Biv.of_val (σ := [p]) (τ := [q, p]) h1 ?_ h2 ?_
    · rw [← h1.eq hu1]; exact hu1
    · rw [← h2.eq hu2]; exact hu2
  -- `s` running alone eventually decides
  classical
  obtain ⟨k, u, hk⟩ := hOF s D hD
  have hex : ∃ k, ¬ Biv (run D (List.replicate k s)) :=
    ⟨k, fun hb' => hb'.not_out hS (hD.run _) s u hk⟩
  set k0 := Nat.find hex
  have hk0 : ¬ Biv (run D (List.replicate k0 s)) := Nat.find_spec hex
  have hlt : ∀ j < k0, Biv (run D (List.replicate j s)) := fun j hj => by
    have := Nat.find_min hex hj; simpa using this
  -- `s` accesses `i` before `D (s^k0)`
  have hexj : ∃ j, j < k0 ∧ (run D (List.replicate j s)).objOf s = some i := by
    by_contra hcon
    push Not at hcon
    exact hk0 (hbiv k0 (avoids_replicate hcon))
  set j0 := Nat.find hexj
  obtain ⟨hj0, hj0i⟩ := Nat.find_spec hexj
  have hav : Avoids D (List.replicate j0 s) i := by
    apply avoids_replicate
    intro l hl hli
    exact Nat.find_min hexj hl ⟨by omega, hli⟩
  obtain ⟨h1, h2⟩ := hcomm j0 hav
  refine ⟨run D (List.replicate j0 s), hD.run _, hlt j0 hj0, hd.run _, hpq, h1, h2,
    Finset.mem_insert_of_mem hpK, Finset.mem_insert_of_mem hqK, ?_⟩
  intro r hr
  rcases Finset.mem_insert.1 hr with rfl | hr
  · exact hj0i
  · rw [run_objOf_other D (hnot j0 (fun h => hs (h ▸ hr)))]
    exact hK r hr

theorem CritK.grow (hS : Safe A) (hOF : ∀ r, OFree A r) {D : Cfg A} {p q : Fin n} {v : Bool}
    {i : ι} {K : Finset (Fin n)} (h : CritK D p q v i K) :
    ∃ D' : Cfg A, CritK D' p q v i Finset.univ := by
  induction hc : (Finset.univ \ K).card generalizing D K with
  | zero =>
    have : K = Finset.univ := by
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hc
      exact Finset.eq_univ_of_forall fun r => hc (Finset.mem_univ r)
    exact ⟨D, this ▸ h⟩
  | succ m ih =>
    obtain ⟨s, hs⟩ : ∃ s, s ∉ K := by
      by_contra hcon; push Not at hcon
      have : Finset.univ \ K = ∅ := by
        rw [Finset.sdiff_eq_empty_iff_subset]; exact fun r _ => hcon r
      rw [this] at hc; simp at hc
    obtain ⟨D', hD'⟩ := h.extend hS hOF hs
    refine ih hD' ?_
    have : Finset.univ \ insert s K = (Finset.univ \ K).erase s := by
      ext r; simp [Finset.mem_sdiff, Finset.mem_erase]
    rw [this, Finset.card_erase_of_mem (by simp [hs]), hc]
    simp

/-- **Lemma 6** of the paper (and Lemma 9, which has the same proof). Let `A` be an
obstruction-free consensus algorithm with a reachable bivalent configuration at which some `p`
is a decider (Lemma 4 / Lemma 7). Then there are a reachable bivalent configuration `D`, a
process `q ≠ p` and an object `i` such that `p` is a decider at `D`, the runs `D p` and `D q p`
are univalent and not compatible, **all `n` processes are poised on `i`**, and `i` is not
read/write-like (in particular, not an atomic register). -/
theorem lemma6 (hS : Safe A) (hOF : ∀ r, OFree A r) {C : Cfg A} {p : Fin n} (hC : Reachable C)
    (hb : Biv C) (hd : Decider C p) :
    ∃ (D : Cfg A) (q : Fin n) (v : Bool) (i : ι), Reachable D ∧ Biv D ∧ Decider D p ∧ p ≠ q ∧ Val (D.step p) v ∧
      Val ((D.step q).step p) (!v) ∧ ¬ (T i).RWLike ∧ ∀ r, D.objOf r = some i := by
  obtain ⟨D, q, v, hD, hbD, hdD, hpq, h1, h2, i, hpi, hqi, hrw⟩ := lemma5 hOF hC hb hd
  have hK : CritK D p q v i {p, q} := ⟨hD, hbD, hdD, hpq, h1, h2, by simp, by simp, by
    intro r hr; simp at hr; rcases hr with rfl | rfl <;> assumption⟩
  obtain ⟨D', hD', hb', hd', hpq', h1', h2', -, -, hall⟩ := hK.grow hS hOF
  exact ⟨D', q, v, i, hD', hb', hd', hpq', h1', h2', hrw, fun r => hall r (Finset.mem_univ r)⟩

end Podc.AsymmetricProgress
