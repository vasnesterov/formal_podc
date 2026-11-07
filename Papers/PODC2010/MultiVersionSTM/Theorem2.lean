import Papers.PODC2010.MultiVersionSTM.Commute

/-!
# Theorem 2: MV-permissiveness rules out weak disjoint-access parallelism

Section 6.1 of Perelman–Fan–Keidar (PODC 2010). The proof runs the two schedules of Figure 3,

* `H1 = w₁(o₂) c₁ r₂(o₁) w₃(o₁) c₃ r₂(o₂) c₂`,
* `H2 = r₂(o₁) w₃(o₁) c₃ w₁(o₂) c₁ r₂(o₂) c₂`,

where `T₁, T₃` are update transactions and `T₂` is read-only, run by three distinct threads.

1. MV-permissiveness forces every step to succeed (only `T₁` and `T₃` could abort, but they
   access different objects, and `T₂` is read-only); since reads return written versions, the
   first read of `H2` returns the initial version of `o₁`.
2. Weak DAP, applied to the prefix `α = w₁ c₁ r₂(o₁) w₃ c₃` of `H1`, in which `T₁` is
   disjoint-access with `T₂` and with `T₃`: the base steps of `T₁` do not contend with those of
   `T₂, T₃`.
3. Hence (`STM.run_comm`) the steps of `T₁` commute with those of `T₂, T₃`: after the prefix
   `β = r₂(o₁) w₃ c₃ w₁ c₁` of `H2` the configuration is the same as after `α`, and `r₂(o₂)`
   returns the same version in `H1` and in `H2`.
4. In `H1`, strict serializability forces `r₂(o₂)` to return `T₁`'s version (`fig3_H1`).
5. Then `H2` is not strictly serializable (`fig3_H2`): `T₂ < T₃` (it read the initial `o₁`),
   `T₁ < T₂` (it read `T₁`'s `o₂`) and `T₃ < T₁` (real-time order).

**On the paper's step 2.** The paper derives the absence of contention in `H1` from an auxiliary
history `H3` in which `T₂` commits right after its first step, and claims that `thr(T₃)` does
not distinguish `H1` from `H3` after `s₃`. This is not right as stated: in `H3` the commit of
`T₂` precedes `s₃`, and its base steps may change base objects that `s₃` reads (and the step
`s₃` itself may then differ). The detour is unnecessary:
in the prefix `α` of `H1` itself, `T₁` is disjoint-access with `T₂` and with `T₃` (every
transaction of `α` accesses a single object), so weak DAP applies to `α` directly.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type}

/-! ### History predicates in terms of invocations -/

section Hist

variable {h : Hist Tx O} {T : Tx} {o : O}

/-- Accesses depend only on the invocations of a history. -/
lemma accesses_iff_mem_inv :
    Accesses h T o ↔ ∃ i ∈ h.map Event.inv, i.tx = T ∧ i.obj? = some o := by
  simp [Accesses]

/-- A history in which every transaction accesses at most one object, and the two given
transactions access different objects: they are disjoint-access. -/
lemma disjointAccess_of {A B : Tx}
    (h₁ : ∀ T x y, Accesses h T x → Accesses h T y → x = y)
    (h₂ : ∀ x y, Accesses h A x → Accesses h B y → x ≠ y) : DisjointAccess h A B := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hxy' : x = y := by
    clear hy
    induction hxy with
    | refl => rfl
    | tail _ hst ih => obtain ⟨T, -, ha, hb⟩ := hst; exact ih.trans (h₁ T _ _ ha hb)
  exact h₂ x y hx hy hxy'

end Hist

/-! ### Histories of schedules -/

namespace STM

variable (X : STM Tx O P) [TxSys Tx P]

/-- Under MV-permissiveness, a step can abort only if its transaction is an update transaction
accessing an object accessed by another update transaction. -/
lemma resp_ne_none_of_noConflict (hm : X.MVPermissive) {σ : List (Inv Tx O)} {i : Inv Tx O}
    (hw : WF (X.hist (σ ++ [i])))
    (h : ro i.tx = false → ∀ T', T' ≠ i.tx → ro T' = false → ∀ o,
      Accesses (X.hist σ ++ [⟨i, none⟩]) i.tx o → Accesses (X.hist σ ++ [⟨i, none⟩]) T' o →
        False) :
    X.resp σ i ≠ none := by
  intro hr
  obtain ⟨h1, T', h2, h3, -, o, h4, h5, -⟩ := hm _ hw (X.hist σ) i [] (by rw [hist_snoc, hr])
  exact h h1 T' h2 h3 o h4 h5

end STM

/-- A sufficient condition for `OKNext` in a history without aborts. -/
lemma okNext_of [TxSys Tx P] {h : Hist Tx O} {i : Inv Tx O} (hna : ∀ e ∈ h, e.resp ≠ none)
    (hc : Inv.commit i.tx ∉ h.map Event.inv) (hw : ∀ T o, i = .write T o → ro T = false)
    (hthr : ∀ j ∈ h.map Event.inv, thr j.tx = thr i.tx → j.tx = i.tx) : OKNext h i := by
  refine ⟨?_, hw, ?_⟩
  · rintro (⟨r, hr⟩ | ⟨e, he, -, hn⟩)
    · exact hc (List.mem_map.2 ⟨_, hr, rfl⟩)
    · exact hna e he hn
  · rintro - T' hT' hthr' ⟨e, he, rfl⟩
    exact (hT' (hthr e.inv (List.mem_map_of_mem he) hthr')).elim

/-! ### The histories of Figure 3 -/

section Fig3

variable [TxSys Tx P]

/-- The assumptions of Theorem 2 on the transactions and objects of Figure 3: three distinct
transactions run by three distinct threads, `T₁, T₃` update transactions, `T₂` read-only, and
two distinct objects. -/
structure Fig3 (T₁ T₂ T₃ : Tx) (o₁ o₂ : O) : Prop where
  h12 : T₁ ≠ T₂
  h13 : T₁ ≠ T₃
  h23 : T₂ ≠ T₃
  ho : o₁ ≠ o₂
  hp12 : thr T₁ ≠ thr T₂
  hp13 : thr T₁ ≠ thr T₃
  hp23 : thr T₂ ≠ thr T₃
  r1 : ro T₁ = false
  r2 : ro T₂ = true
  r3 : ro T₃ = false

/-- The seven invocations of Figure 3. -/
def fig3 (T₁ T₂ T₃ : Tx) (o₁ o₂ : O) : List (Inv Tx O) :=
  [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃, .read T₂ o₂, .commit T₂]

variable {T₁ T₂ T₃ : Tx} {o₁ o₂ : O}

omit [TxSys Tx P] in
lemma fig3_obj {j : Inv Tx O} {o : O} (hj : j ∈ fig3 T₁ T₂ T₃ o₁ o₂) (ho : j.obj? = some o) :
    (j.tx = T₁ ∧ o = o₂) ∨ j.tx = T₂ ∨ (j.tx = T₃ ∧ o = o₁) := by
  simp only [fig3, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

omit [TxSys Tx P] in
lemma fig3_tx {j : Inv Tx O} (hj : j ∈ fig3 T₁ T₂ T₃ o₁ o₂) :
    j.tx = T₁ ∨ j.tx = T₂ ∨ j.tx = T₃ := by
  simp only [fig3, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma Fig3.thr_inj (F : Fig3 (P := P) T₁ T₂ T₃ o₁ o₂) {i j : Inv Tx O}
    (hi : i ∈ fig3 T₁ T₂ T₃ o₁ o₂) (hj : j ∈ fig3 T₁ T₂ T₃ o₁ o₂) (h : thr j.tx = thr i.tx) :
    j.tx = i.tx := by
  have := F.hp12; have := F.hp13; have := F.hp23
  rcases fig3_tx hi with hi | hi | hi <;> rcases fig3_tx hj with hj | hj | hj <;>
    simp_all [eq_comm]

lemma Fig3.ro_of_write (F : Fig3 (P := P) T₁ T₂ T₃ o₁ o₂) {i : Inv Tx O}
    (hi : i ∈ fig3 T₁ T₂ T₃ o₁ o₂) : ∀ T o, i = .write T o → ro T = false := by
  rintro T o rfl
  simp only [fig3, List.mem_cons, List.not_mem_nil, or_false, Inv.write.injEq,
    reduceCtorEq, false_or, or_false] at hi
  rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [F.r1, F.r3]

namespace STM

variable (X : STM Tx O P)

/-- In schedules made of the invocations of Figure 3, MV-permissiveness forbids aborts. -/
lemma resp_ne_none_fig3 (hm : X.MVPermissive) (F : Fig3 T₁ T₂ T₃ o₁ o₂) {σ : List (Inv Tx O)}
    {i : Inv Tx O} (hσ : ∀ j ∈ σ, j ∈ fig3 T₁ T₂ T₃ o₁ o₂) (hi : i ∈ fig3 T₁ T₂ T₃ o₁ o₂)
    (hw : WF (X.hist (σ ++ [i]))) : X.resp σ i ≠ none := by
  apply X.resp_ne_none_of_noConflict hm hw
  intro hro T' hT' hro' o ha ha'
  rw [accesses_iff_mem_inv] at ha ha'
  simp only [List.map_append, map_inv_hist, List.map_cons, List.map_nil] at ha ha'
  have hmem : ∀ j ∈ σ ++ [i], j ∈ fig3 T₁ T₂ T₃ o₁ o₂ := by
    intro j hj
    rcases List.mem_append.1 hj with hj | hj
    · exact hσ j hj
    · rw [List.mem_singleton.1 hj]; exact hi
  obtain ⟨j, hj, hjt, hjo⟩ := ha
  obtain ⟨j', hj', hjt', hjo'⟩ := ha'
  have := F.h12; have := F.h13; have := F.h23; have := F.ho; have := F.r2
  rcases fig3_obj (hmem j hj) hjo with ⟨h1, rfl⟩ | h1 | ⟨h1, rfl⟩ <;>
    rcases fig3_obj (hmem j' hj') hjo' with ⟨h1', h2'⟩ | h1' | ⟨h1', h2'⟩ <;>
    simp_all

/-- One step of a schedule made of the invocations of Figure 3: if the history so far is
well-formed and has no abort, and the transaction of the next invocation has not committed, the
next history is well-formed and has no abort. -/
lemma step_fig3 (hm : X.MVPermissive) (F : Fig3 T₁ T₂ T₃ o₁ o₂) {σ : List (Inv Tx O)}
    {i : Inv Tx O} (hσ : ∀ j ∈ σ, j ∈ fig3 T₁ T₂ T₃ o₁ o₂) (hi : i ∈ fig3 T₁ T₂ T₃ o₁ o₂)
    (hwf : WF (X.hist σ)) (hna : ∀ e ∈ X.hist σ, e.resp ≠ none) (hc : Inv.commit i.tx ∉ σ) :
    WF (X.hist (σ ++ [i])) ∧ ∀ e ∈ X.hist (σ ++ [i]), e.resp ≠ none := by
  have hok : OKNext (X.hist σ) i :=
    okNext_of hna (by rwa [map_inv_hist]) (F.ro_of_write hi)
      (fun j hj => F.thr_inj hi (hσ j (by rwa [map_inv_hist] at hj)))
  have hw : WF (X.hist (σ ++ [i])) := by rw [hist_snoc]; exact hwf.snoc _ hok
  refine ⟨hw, ?_⟩
  rw [hist_snoc]
  simp only [List.mem_append, List.mem_singleton]
  rintro e (he | rfl)
  · exact hna e he
  · exact X.resp_ne_none_fig3 hm F hσ hi hw

end STM

/-- Claim (1) of the proof of Theorem 2: in `H1`, strict serializability forces the second read
of `T₂` (of `o₂`) to return the version written by `T₁`, which committed before `T₂` began. -/
lemma fig3_H1 {T₁ T₂ T₃ : Tx} {o₁ o₂ : O} (h12 : T₁ ≠ T₂) (ho : o₁ ≠ o₂)
    {ρ₁ ρ₃ ρ₄ ρ₅ : Resp Tx} {x₂ x₇ v : Option Tx}
    (hs : StrictSer [⟨.write T₁ o₂, ρ₁⟩, ⟨.commit T₁, some x₂⟩, ⟨.read T₂ o₁, ρ₃⟩,
      ⟨.write T₃ o₁, ρ₄⟩, ⟨.commit T₃, ρ₅⟩, ⟨.read T₂ o₂, some v⟩, ⟨.commit T₂, some x₇⟩]) :
    v = some T₁ := by
  obtain ⟨pos, -, hrt, hrd⟩ := hs
  have hc1 : Committed [(⟨.write T₁ o₂, ρ₁⟩ : Event Tx O), ⟨.commit T₁, some x₂⟩] T₁ :=
    ⟨x₂, by simp⟩
  have hc2 : Committed [(⟨.write T₁ o₂, ρ₁⟩ : Event Tx O), ⟨.commit T₁, some x₂⟩,
      ⟨.read T₂ o₁, ρ₃⟩, ⟨.write T₃ o₁, ρ₄⟩, ⟨.commit T₃, ρ₅⟩, ⟨.read T₂ o₂, some v⟩,
      ⟨.commit T₂, some x₇⟩] T₂ := ⟨x₇, by simp⟩
  have hleg := (hrd T₂ (Or.inl hc2) [⟨.write T₁ o₂, ρ₁⟩, ⟨.commit T₁, some x₂⟩, ⟨.read T₂ o₁, ρ₃⟩,
      ⟨.write T₃ o₁, ρ₄⟩, ⟨.commit T₃, ρ₅⟩] o₂ v [⟨.commit T₂, some x₇⟩] rfl).2
    (by simp [h12, ho])
  cases v with
  | none =>
    have h1 := hleg T₁ ⟨hc1.mono _, by simp⟩ h12
    have h2 := hrt T₁ T₂ (hc1.mono _) (Or.inl hc2)
      ⟨by simp, [⟨.write T₁ o₂, ρ₁⟩, ⟨.commit T₁, some x₂⟩], _, rfl, hc1, by simp [h12]⟩
    omega
  | some W =>
    obtain ⟨-, ⟨-, hW⟩, -⟩ := hleg
    simp [ho] at hW
    exact congrArg some hW.symm

/-- Claim (4) of the proof of Theorem 2: `H2` is not strictly serializable if the first read of
`T₂` (of `o₁`) returns the initial version and its second read (of `o₂`) returns the version
written by `T₁`. -/
lemma fig3_H2 {T₁ T₂ T₃ : Tx} {o₁ o₂ : O} (h12 : T₁ ≠ T₂) (h13 : T₁ ≠ T₃) (h23 : T₂ ≠ T₃)
    {ρ₂ ρ₄ : Resp Tx} {x₃ x₅ x₇ : Option Tx}
    (hs : StrictSer [⟨.read T₂ o₁, some none⟩, ⟨.write T₃ o₁, ρ₂⟩, ⟨.commit T₃, some x₃⟩,
      ⟨.write T₁ o₂, ρ₄⟩, ⟨.commit T₁, some x₅⟩, ⟨.read T₂ o₂, some (some T₁)⟩,
      ⟨.commit T₂, some x₇⟩]) : False := by
  obtain ⟨pos, -, hrt, hrd⟩ := hs
  set H : Hist Tx O := [⟨.read T₂ o₁, some none⟩, ⟨.write T₃ o₁, ρ₂⟩, ⟨.commit T₃, some x₃⟩,
      ⟨.write T₁ o₂, ρ₄⟩, ⟨.commit T₁, some x₅⟩, ⟨.read T₂ o₂, some (some T₁)⟩,
      ⟨.commit T₂, some x₇⟩] with hH
  have hc1 : Committed H T₁ := ⟨x₅, by simp [hH]⟩
  have hc2 : Committed H T₂ := ⟨x₇, by simp [hH]⟩
  have hc3 : Committed H T₃ := ⟨x₃, by simp [hH]⟩
  -- the first read of `T₂` returns the initial version of `o₁`, so `T₂` precedes `T₃`
  have h1 : pos T₂ < pos T₃ :=
    (hrd T₂ (Or.inl hc2) [] o₁ none _ rfl).2 (by simp) T₃ ⟨hc3, by simp [hH]⟩ (Ne.symm h23)
  -- the second read of `T₂` returns the version of `o₂` written by `T₁`, so `T₁` precedes `T₂`
  have h2 : pos T₁ < pos T₂ :=
    ((hrd T₂ (Or.inl hc2) [⟨.read T₂ o₁, some none⟩, ⟨.write T₃ o₁, ρ₂⟩, ⟨.commit T₃, some x₃⟩,
      ⟨.write T₁ o₂, ρ₄⟩, ⟨.commit T₁, some x₅⟩] o₂ (some T₁) [⟨.commit T₂, some x₇⟩] rfl).2
      (by simp [h12, Ne.symm h23])).2.2.1
  -- `T₃` commits before `T₁` begins
  have h3 : pos T₃ < pos T₁ :=
    hrt T₃ T₁ hc3 (Or.inl hc1) ⟨by simp [hH], [⟨.read T₂ o₁, some none⟩, ⟨.write T₃ o₁, ρ₂⟩,
      ⟨.commit T₃, some x₃⟩], _, rfl, ⟨x₃, by simp⟩, by simp [Ne.symm h12, Ne.symm h13]⟩
  omega

/-- In the prefix `α = w₁(o₂) c₁ r₂(o₁) w₃(o₁) c₃` of `H1`, `T₁` is disjoint-access with `T₂`
and with `T₃`: every transaction accesses a single object, `o₂` for `T₁` and `o₁` for `T₂, T₃`. -/
lemma disjointAccess_fig3 {T₁ T₂ T₃ : Tx} {o₁ o₂ : O} (h12 : T₁ ≠ T₂) (h13 : T₁ ≠ T₃)
    (h23 : T₂ ≠ T₃) (ho : o₁ ≠ o₂) {h : Hist Tx O}
    (hinv : h.map Event.inv =
      [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃])
    {T : Tx} (hT : T = T₂ ∨ T = T₃) : DisjointAccess h T₁ T := by
  have hacc : ∀ T x, Accesses h T x ↔
      (T₁ = T ∧ o₂ = x) ∨ (T₂ = T ∧ o₁ = x) ∨ (T₃ = T ∧ o₁ = x) := by
    intro T x; rw [accesses_iff_mem_inv, hinv]; simp
  refine disjointAccess_of (fun T' x y hx hy => ?_) (fun x y hx hy => ?_)
  · rw [hacc] at hx hy
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hy with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all
  · rw [hacc] at hx hy
    rcases hT with rfl | rfl <;>
      rcases hx with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
      rcases hy with ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ <;>
      first | exact ho | exact ho.symm | simp_all

/-- Steps 2–3 of the proof of Theorem 2: under weak DAP, the steps of `T₁` commute with those of
`T₂` and `T₃`, so the prefixes `α = w₁ c₁ r₂(o₁) w₃ c₃` of `H1` and `β = r₂(o₁) w₃ c₃ w₁ c₁` of
`H2` lead to the same configuration.

The paper argues via an auxiliary history `H3` in which `T₂` commits right after its first step,
and claims that `thr(T₃)` does not distinguish `H1` from `H3` after `s₃`; this is not right (in
`H3` the commit of `T₂` precedes `s₃`). We apply weak DAP to `α` itself instead. -/
lemma STM.conf_comm_fig3 (X : STM Tx O P) (F : Fig3 T₁ T₂ T₃ o₁ o₂) (hW : X.WDAP)
    (hwf : WF (X.hist [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃])) :
    X.conf [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃] =
      X.conf [.read T₂ o₁, .write T₃ o₁, .commit T₃, .write T₁ o₂, .commit T₁] := by
  set A : List (Inv Tx O) := [.write T₁ o₂, .commit T₁] with hA
  set B : List (Inv Tx O) := [.read T₂ o₁, .write T₃ o₁, .commit T₃] with hB
  -- weak DAP: the base steps of `T₁` contend neither with those of `T₂` nor with those of `T₃`
  have hdis : ∀ T, T = T₂ ∨ T = T₃ → ¬ X.Contend (A ++ B) T₁ T := by
    intro T hT
    refine hW _ hwf T₁ T ?_ (disjointAccess_fig3 F.h12 F.h13 F.h23 F.ho (X.map_inv_hist _) hT)
    rcases hT with rfl | rfl
    exacts [F.h12, F.h13]
  have hexec : (X.exec (A ++ B)).2 = (X.run X.init A).2 ++ (X.run (X.run X.init A).1 B).2 :=
    congrArg Prod.snd (X.run_append X.init A B)
  have hthr : ∀ i ∈ A, ∀ j ∈ B, thr i.tx ≠ thr j.tx := by
    simp [hA, hB, F.hp12, F.hp13]
  have hacc : ∀ a ∈ X.traceOf (X.run X.init A).2, ∀ a' ∈ X.traceOf (X.run (X.run X.init A).1 B).2,
      a.b = a'.b → a.old = a.new ∧ a'.old = a'.new := by
    intro a ha a' ha' hab
    obtain ⟨s, hs, has⟩ := (X.mem_traceOf).1 ha
    obtain ⟨s', hs', has'⟩ := (X.mem_traceOf).1 ha'
    have ht1 : s.1.inv.tx = T₁ := by
      have := X.inv_mem_of_mem_run hs
      simp only [hA, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h <;> rw [h] <;> rfl
    have ht2 : s'.1.inv.tx = T₂ ∨ s'.1.inv.tx = T₃ := by
      have := X.inv_mem_of_mem_run hs'
      simp only [hB, List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h <;> rw [h] <;> simp
    have hsm : s ∈ (X.exec (A ++ B)).2 := by rw [hexec]; exact List.mem_append_left _ hs
    have hsm' : s' ∈ (X.exec (A ++ B)).2 := by rw [hexec]; exact List.mem_append_right _ hs'
    by_contra hne
    refine hdis _ ht2 ⟨a.b, ⟨s, hsm, ht1, a, has, rfl⟩, ⟨s', hsm', rfl, a', has', hab.symm⟩, ?_⟩
    by_cases h1 : a.old = a.new
    · exact Or.inr ⟨s', hsm', rfl, a', has', hab.symm, fun h2 => hne ⟨h1, h2⟩⟩
    · exact Or.inl ⟨s, hsm, ht1, a, has, rfl, h1⟩
  obtain ⟨-, -, h3⟩ := X.run_comm X.init A B hthr hacc
  calc X.conf (A ++ B) = (X.run (X.run X.init A).1 B).1 := by
        rw [STM.conf, STM.exec, X.run_append]
    _ = (X.run (X.run X.init B).1 A).1 := h3.symm
    _ = X.conf (B ++ A) := by rw [STM.conf, STM.exec, X.run_append]

end Fig3

/-! ### Theorem 2 -/

/-- Theorem 2 of [Perelman–Fan–Keidar, PODC 2010]. An STM satisfying MV-permissiveness cannot be
weakly disjoint-access parallel.

The STM is strictly serializable (`Correct`), MV-permissive, and its reads return written
versions (the value semantics of reads in our version-based model). The witnesses are the
histories of Figure 3, which need three distinct transactions `T₁, T₂, T₃` run by three distinct
threads, `T₁, T₃` update transactions and `T₂` read-only, and two distinct objects `o₁, o₂`. -/
theorem theorem_2 [TxSys Tx P] (T₁ T₂ T₃ : Tx) (o₁ o₂ : O)
    (h12 : T₁ ≠ T₂) (h13 : T₁ ≠ T₃) (h23 : T₂ ≠ T₃) (ho : o₁ ≠ o₂)
    (hp12 : thr T₁ ≠ thr T₂) (hp13 : thr T₁ ≠ thr T₃) (hp23 : thr T₂ ≠ thr T₃)
    (r1 : ro T₁ = false) (r2 : ro T₂ = true) (r3 : ro T₃ = false)
    (X : STM Tx O P) (hc : X.Correct) (hm : X.MVPermissive) (hr : X.ReadsWrittenOnly) :
    ¬ X.WDAP := by
  intro hW
  have F : Fig3 T₁ T₂ T₃ o₁ o₂ := ⟨h12, h13, h23, ho, hp12, hp13, hp23, r1, r2, r3⟩
  have h21 := Ne.symm h12; have h31 := Ne.symm h13; have h32 := Ne.symm h23
  -- Step 1. All prefixes of `H1` are well-formed and have no abort (MV-permissiveness).
  have a0 : WF (X.hist []) ∧ ∀ e ∈ X.hist [], e.resp ≠ none := ⟨WF.nil, by simp⟩
  have a1 := X.step_fig3 hm F (σ := []) (i := .write T₁ o₂)
    (by simp) (by simp [fig3]) a0.1 a0.2 (by simp)
  have a2 := X.step_fig3 hm F (σ := [.write T₁ o₂]) (i := .commit T₁)
    (by simp [fig3]) (by simp [fig3]) a1.1 a1.2 (by simp)
  have a3 := X.step_fig3 hm F (σ := [.write T₁ o₂, .commit T₁]) (i := .read T₂ o₁)
    (by simp [fig3]) (by simp [fig3]) a2.1 a2.2 (by simp [h21])
  have a4 := X.step_fig3 hm F (σ := [.write T₁ o₂, .commit T₁, .read T₂ o₁]) (i := .write T₃ o₁)
    (by simp [fig3]) (by simp [fig3]) a3.1 a3.2 (by simp [h31])
  have a5 := X.step_fig3 hm F (σ := [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁])
    (i := .commit T₃) (by simp [fig3]) (by simp [fig3]) a4.1 a4.2 (by simp [h31])
  have a6 := X.step_fig3 hm F
    (σ := [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃]) (i := .read T₂ o₂)
    (by simp [fig3]) (by simp [fig3]) a5.1 a5.2 (by simp [h21, h23])
  have a7 := X.step_fig3 hm F
    (σ := [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃, .read T₂ o₂])
    (i := .commit T₂) (by simp [fig3]) (by simp [fig3]) a6.1 a6.2 (by simp [h21, h23])
  -- ... and so are all prefixes of `H2`.
  have b1 := X.step_fig3 hm F (σ := []) (i := .read T₂ o₁)
    (by simp) (by simp [fig3]) a0.1 a0.2 (by simp)
  have b2 := X.step_fig3 hm F (σ := [.read T₂ o₁]) (i := .write T₃ o₁)
    (by simp [fig3]) (by simp [fig3]) b1.1 b1.2 (by simp)
  have b3 := X.step_fig3 hm F (σ := [.read T₂ o₁, .write T₃ o₁]) (i := .commit T₃)
    (by simp [fig3]) (by simp [fig3]) b2.1 b2.2 (by simp)
  have b4 := X.step_fig3 hm F (σ := [.read T₂ o₁, .write T₃ o₁, .commit T₃]) (i := .write T₁ o₂)
    (by simp [fig3]) (by simp [fig3]) b3.1 b3.2 (by simp [h13])
  have b5 := X.step_fig3 hm F (σ := [.read T₂ o₁, .write T₃ o₁, .commit T₃, .write T₁ o₂])
    (i := .commit T₁) (by simp [fig3]) (by simp [fig3]) b4.1 b4.2 (by simp [h13])
  have b6 := X.step_fig3 hm F
    (σ := [.read T₂ o₁, .write T₃ o₁, .commit T₃, .write T₁ o₂, .commit T₁]) (i := .read T₂ o₂)
    (by simp [fig3]) (by simp [fig3]) b5.1 b5.2 (by simp [h23, h21])
  have b7 := X.step_fig3 hm F
    (σ := [.read T₂ o₁, .write T₃ o₁, .commit T₃, .write T₁ o₂, .commit T₁, .read T₂ o₂])
    (i := .commit T₂) (by simp [fig3]) (by simp [fig3]) b6.1 b6.2 (by simp [h23, h21])
  -- Steps 2–3. Weak DAP: the prefixes `α` of `H1` and `β` of `H2` reach the same configuration,
  -- so `r₂(o₂)` returns the same version after both.
  have hconf := X.conf_comm_fig3 F hW a5.1
  have hr6 : X.resp [.read T₂ o₁, .write T₃ o₁, .commit T₃, .write T₁ o₂, .commit T₁]
      (.read T₂ o₂) =
      X.resp [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃] (.read T₂ o₂) := by
    simp only [STM.resp, hconf]
  -- Step 4. In `H1`, `r₂(o₂)` returns the version written by `T₁` (strict serializability).
  have hv : X.resp [.write T₁ o₂, .commit T₁, .read T₂ o₁, .write T₃ o₁, .commit T₃]
      (.read T₂ o₂) = some (some T₁) := by
    obtain ⟨x₂, hx₂⟩ := Option.ne_none_iff_exists'.1
      (X.resp_ne_none_fig3 hm F (by simp [fig3]) (by simp [fig3]) a2.1)
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1
      (X.resp_ne_none_fig3 hm F (by simp [fig3]) (by simp [fig3]) a6.1)
    obtain ⟨x₇, hx₇⟩ := Option.ne_none_iff_exists'.1
      (X.resp_ne_none_fig3 hm F (by simp [fig3]) (by simp [fig3]) a7.1)
    have hs := hc _ a7.1
    simp only [STM.hist_eq_histFrom, STM.histFrom, List.nil_append, List.cons_append] at hs
    rw [hx₂, hv, hx₇] at hs
    rw [hv, fig3_H1 h12 ho hs]
  -- Step 1 (cont.). In `H2`, the first read `r₂(o₁)` returns the initial version (reads return
  -- written versions, and no write has been invoked yet).
  have hv1 : X.resp [] (.read T₂ o₁) = some none := by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1
      (X.resp_ne_none_fig3 hm F (by simp) (by simp [fig3]) b1.1)
    rw [hv]
    cases v with
    | none => rfl
    | some W =>
      have := hr _ b1.1 [] T₂ o₁ W [] (by rw [STM.hist_snoc, hv]; rfl)
      simp at this
  -- Step 5. `H2` is not strictly serializable.
  obtain ⟨x₃, hx₃⟩ := Option.ne_none_iff_exists'.1
    (X.resp_ne_none_fig3 hm F (by simp [fig3]) (by simp [fig3]) b3.1)
  obtain ⟨x₅, hx₅⟩ := Option.ne_none_iff_exists'.1
    (X.resp_ne_none_fig3 hm F (by simp [fig3]) (by simp [fig3]) b5.1)
  obtain ⟨x₇, hx₇⟩ := Option.ne_none_iff_exists'.1
    (X.resp_ne_none_fig3 hm F (by simp [fig3]) (by simp [fig3]) b7.1)
  have hs := hc _ b7.1
  simp only [STM.hist_eq_histFrom, STM.histFrom, List.nil_append, List.cons_append] at hs
  rw [hv1, hx₃, hx₅, hr6, hv, hx₇] at hs
  exact fig3_H2 h12 h13 h23 hs

end Podc.MultiVersionSTM
