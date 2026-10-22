import Papers.PODC2022.RecoverableHarder.Fig2Safe

/-!
# Theorem 8: `n`-recording readable types solve recoverable consensus among `n` processes

Proof as in the paper: a tournament (Proposition 30, `Cslib.SharedMemory.Recoverable.tournament`)
of instances of the recoverable team consensus algorithm of Figure 2 (`fig2_safe`), at the nodes
`π` of a binary tree; the teams of a node are obtained by restricting the `n`-recording data to a
subset of the processes (`RecOn.comap`), and swapped if `q₀ ∈ Q_B` (`RecOn.swap`).
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

variable {S : ObjSpec}

/-! ## Restricting and swapping recording data -/

/-- Recording data restricted along an injective map of processes (both teams still met). -/
theorem RecOn.comap {m n : ℕ} {u : S.State} {team : Fin n → Bool} {o : Fin n → S.Op}
    (h : RecOn S Finset.univ u team o) (f : Fin m → Fin n) (hf : Function.Injective f)
    (hA : ∃ p, team (f p) = false) (hB : ∃ p, team (f p) = true) :
    RecOn S Finset.univ u (team ∘ f) (o ∘ f) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨⟨a, by simp, ha⟩, ⟨b, by simp, hb⟩, fun p σ q τ _ _ hp hq tp tq heq => ?_,
    fun p σ _ hp heq => ?_⟩
  · rw [apply_map, apply_map] at heq
    exact h.2.2.1 (f p) (σ.map f) (f q) (τ.map f) (by simp) (by simp)
      (by simpa using hp.map hf) (by simpa using hq.map hf) tp tq (by simpa using heq)
  · rw [apply_map] at heq
    obtain ⟨q₀, ⟨-, hq₀⟩, huniq⟩ := h.2.2.2 (f p) (σ.map f) (by simp) (by simpa using hp.map hf)
      (by simpa using heq)
    have hex : ∃ q, team (f q) = !team (f p) := by
      cases h' : team (f p)
      · exact ⟨b, by simp [hb]⟩
      · exact ⟨a, by simp [ha]⟩
    obtain ⟨q, hq⟩ := hex
    refine ⟨q, ⟨by simp, by simpa using hq⟩, fun q' ⟨_, hq'⟩ => hf ?_⟩
    rw [huniq (f q') ⟨by simp, by simpa using hq'⟩, huniq (f q) ⟨by simp, hq⟩]

/-- Recording data with the teams swapped. -/
theorem RecOn.swap {n : ℕ} {R : Finset (Fin n)} {u : S.State} {team : Fin n → Bool}
    {o : Fin n → S.Op} (h : RecOn S R u team o) : RecOn S R u (fun p => !team p) o := by
  obtain ⟨⟨a, ha, ta⟩, ⟨b, hb, tb⟩, h1, h2⟩ := h
  refine ⟨⟨b, hb, by simp [tb]⟩, ⟨a, ha, by simp [ta]⟩, fun p σ q τ hp hq hpn hqn tp tq heq =>
    h1 q τ p σ hq hp hqn hpn (by simpa using tq) (by simpa using tp) heq.symm,
    fun p σ hp hpn heq => ?_⟩
  obtain ⟨q, ⟨hqR, hq⟩, huniq⟩ := h2 p σ hp hpn heq
  exact ⟨q, ⟨hqR, by simp [hq]⟩, fun q' ⟨h1', h2'⟩ => huniq q' ⟨h1', by simpa using h2'⟩⟩

lemma qx_swap {k : ℕ} {u : S.State} {team : Fin k → Bool} {o : Fin k → S.Op} {X : Bool}
    {q : S.State} : QX u (fun p => !team p) o X q ↔ QX u team o (!X) q := by
  constructor
  · rintro ⟨p, σ, h1, h2, h3⟩; exact ⟨p, σ, h1, by simp [← h2], h3⟩
  · rintro ⟨p, σ, h1, h2, h3⟩; exact ⟨p, σ, h1, by simp [h2], h3⟩

/-! ## The team consensus instances -/

/-- At a node `π`, for any split `kA + kB` with `1 ≤ kA ≤ |A|` and `1 ≤ kB ≤ |B|`, a safe and
ranked recoverable team consensus algorithm (an instance of Figure 2). -/
theorem exists_teamCons {n : ℕ} {u : S.State} {team : Fin n → Bool} {o : Fin n → S.Op}
    (h : RecOn S Finset.univ u team o) {rd : S.Op} (hrd : ∀ q, (S.δ q rd).1 = q)
    (hinj : Function.Injective fun q => (S.δ q rd).2) {kA kB : ℕ}
    (hA : kA ≤ (Finset.univ.filter fun p => team p = false).card)
    (hB : kB ≤ (Finset.univ.filter fun p => team p = true).card) (hkA : 1 ≤ kA) (hkB : 1 ≤ kB)
    (π : List Bool) :
    ∃ TC : Alg (kA + kB) (Obj S), TC.mem₀ = mem0 S u ∧
      (∀ l i o' κ, TC.act l = .access i o' κ → nodeFP π i) ∧ Safe TC SideUniform (AdmB true) ∧
      Ranked TC := by
  classical
  -- slots: distinct processes of team `A` for side `A`, of team `B` for side `B`
  obtain ⟨lA, hlA, hlenA, hmemA⟩ := Finset.exists_nodup_list hA
  obtain ⟨lB, hlB, hlenB, hmemB⟩ := Finset.exists_nodup_list hB
  let fA : Fin kA → Fin n := fun a => lA.get ⟨a, by omega⟩
  let fB : Fin kB → Fin n := fun b => lB.get ⟨b, by omega⟩
  have tA : ∀ a, team (fA a) = false := fun a => by
    have := hmemA _ (List.get_mem lA ⟨a, by omega⟩); simpa [fA] using this
  have tB : ∀ b, team (fB b) = true := fun b => by
    have := hmemB _ (List.get_mem lB ⟨b, by omega⟩); simpa [fB] using this
  have iA : Function.Injective fA := fun a a' e => Fin.ext (by
    have := (List.Nodup.get_inj_iff hlA).1 e; simpa using this)
  have iB : Function.Injective fB := fun b b' e => Fin.ext (by
    have := (List.Nodup.get_inj_iff hlB).1 e; simpa using this)
  let f : Fin (kA + kB) → Fin n := Fin.addCases fA fB
  have hf : Function.Injective f := by
    intro p q e
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left a' => simp [f] at e; rw [iA e]
      | right b' =>
        simp [f] at e; have := tA a; rw [e, tB b'] at this; cases this
    | right b =>
      induction q using Fin.addCases with
      | left a' =>
        simp [f] at e; have := tB b; rw [e, tA a'] at this; cases this
      | right b' => simp [f] at e; rw [iB e]
  have hrec := h.comap f hf ⟨Fin.castAdd kB ⟨0, hkA⟩, by
      show team (f (Fin.castAdd kB ⟨0, hkA⟩)) = false
      simp only [f, Fin.addCases_left]; exact tA _⟩
    ⟨Fin.natAdd kA ⟨0, hkB⟩, by
      show team (f (Fin.natAdd kA ⟨0, hkB⟩)) = true
      simp only [f, Fin.addCases_right]; exact tB _⟩
  have hside : ∀ p q : Fin (kA + kB), (team ∘ f) p = (team ∘ f) q ↔
      (∃ a a', p = Fin.castAdd kB a ∧ q = Fin.castAdd kB a') ∨
        (∃ b b', p = Fin.natAdd kA b ∧ q = Fin.natAdd kA b') := by
    intro p q
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left a' => simp [f, tA]
      | right b' =>
        simp [f, tA, tB]
        exact ⟨fun x hx => castAdd_ne_natAdd _ _ hx.symm, fun x hx => castAdd_ne_natAdd _ _ hx⟩
    | right b =>
      induction q using Fin.addCases with
      | left a' =>
        simp [f, tA, tB]
        exact ⟨fun x hx => castAdd_ne_natAdd _ _ hx.symm, fun x hx => castAdd_ne_natAdd _ _ hx⟩
      | right b' => simp [f, tB]
  have hgood : ∀ x : Fin (kA + kB) → Bool, SideUniform x → ∀ p q, (team ∘ f) p = (team ∘ f) q →
      x p = x q := by
    intro x hx p q hpq
    rcases (hside p q).1 hpq with ⟨a, a', rfl, rfl⟩ | ⟨b, b', rfl, rfl⟩
    · exact hx.1 a a'
    · exact hx.2 b b'
  by_cases hq0 : QX u (team ∘ f) (o ∘ f) true u
  · -- swap the teams
    have hrec' := hrec.swap
    have hB' : ¬ QX u (fun p => !(team ∘ f) p) (o ∘ f) true u := by
      rw [qx_swap]; exact fun h' => qx_disj hrec h' hq0
    refine ⟨fig2 rd π u (fun p => !(team ∘ f) p) (o ∘ f), rfl, fig2_footprint _ _ _ _ _,
      ⟨fun x hx => (fig2_safe hrd hinj hrec' hB').agree x (fun p q hpq =>
        hgood x hx p q (by simpa using hpq)),
       fun x hx => (fig2_safe hrd hinj hrec' hB').valid x (fun p q hpq =>
        hgood x hx p q (by simpa using hpq))⟩, fig2_ranked _ _ _ _ _⟩
  · refine ⟨fig2 rd π u (team ∘ f) (o ∘ f), rfl, fig2_footprint _ _ _ _ _,
      ⟨fun x hx => (fig2_safe hrd hinj hrec hq0).agree x (hgood x hx),
       fun x hx => (fig2_safe hrd hinj hrec hq0).valid x (hgood x hx)⟩, fig2_ranked _ _ _ _ _⟩

/-! ## The tournament -/

/-- The objects of the subtree rooted at `π`. -/
def subtreeFP (π : List Bool) : Idx → Prop
  | .inl (π', _) => π <+: π'
  | .inr π' => π <+: π'

lemma prefix_disj {π π' : List Bool} (h1 : π ++ [false] <+: π') (h2 : π ++ [true] <+: π') :
    False := by
  have := List.prefix_of_prefix_length_le h1 h2 (by simp)
  simp at this

/-- **Theorem 8.** A deterministic, readable, `n`-recording type `S`, together with registers,
solves recoverable consensus among `n` processes (individual crashes). -/
theorem theorem8 {n : ℕ} (hread : S.Readable) (hrecd : IsRecording n S) : RecSolvable S n := by
  classical
  obtain ⟨rd, hrd, hinj⟩ := hread
  obtain ⟨u, team, o, h⟩ := isRecording_iff.1 hrecd
  set a := (Finset.univ.filter fun p : Fin n => team p = false).card
  set b := (Finset.univ.filter fun p : Fin n => team p = true).card
  have hab : a + b = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun p => team p = false)
    simpa [a, b] using this
  have ha : 1 ≤ a := by
    obtain ⟨p, -, hp⟩ := h.1
    exact Finset.card_pos.2 ⟨p, by simp [hp]⟩
  have hb : 1 ≤ b := by
    obtain ⟨p, -, hp⟩ := h.2.1
    exact Finset.card_pos.2 ⟨p, by simp [hp]⟩
  have htour := tournament (T := Obj S) true (mem0 S u) subtreeFP nodeFP
    (fun π i hi => by
      rcases hi with rfl | rfl | rfl <;> exact List.prefix_refl π)
    (fun π c i hi => by
      cases i with
      | inl r => exact (List.prefix_append π [c]).trans hi
      | inr r => exact (List.prefix_append π [c]).trans hi)
    (fun π i h1 h2 => by
      cases i with
      | inl r => exact prefix_disj h1 h2
      | inr r => exact prefix_disj h1 h2)
    (fun π c i h1 h2 => by
      rcases h2 with rfl | rfl | rfl
      all_goals
        have := h1.length_le
        simp at this)
    n (by omega) (fun k' h1 h2 => by
      refine ⟨min a (k' - 1), k' - min a (k' - 1), by omega, by omega, by omega, fun π => ?_⟩
      exact exists_teamCons h hrd hinj (by omega) (by omega) (by omega) (by omega) π)
    []
  obtain ⟨A, -, -, hsafe, hranked⟩ := htour
  exact ⟨List Bool × Bool, List Bool, inferInstance, inferInstance, fun _ => Reg,
    fun _ => register_rwLike _ _, A, (solves_admB_true_iff A).1 (hsafe.solves hranked)⟩

end Podc.RecoverableHarder
