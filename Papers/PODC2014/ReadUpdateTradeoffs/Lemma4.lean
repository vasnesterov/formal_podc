import Papers.PODC2014.ReadUpdateTradeoffs.Lemma4Aux
import Papers.PODC2014.ReadUpdateTradeoffs.Lemma6
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Sqrt

/-!
# Lemma 4 of Hendler–Khait (PODC'14): extending an essential set by one step

From an execution with an `i`-step essential set `E` in which `m` processes of `E` are poised on a
base object, we build an execution with an `(i+1)`-step essential set `E'` with
`⌊√m⌋ ≤ 3 (|E'| + 1)` (the paper claims `|E'| ≥ √m/3 − 2`, which this implies).

Differences from the paper's proof (see `differencies.md`):
* the essential sets carry the block invariant (`Ess.blocks`), which the construction maintains;
  in the low-contention case the conflict graph uses the *owner of the block* of each object
  rather than its familiarity set, and in the high-contention case the owner of the block of the
  contended object is erased (instead of "the process the object is familiar with");
* in the high-contention case the processes are classified (read / write / value-changing CAS)
  *after* the erasure, with respect to the value the object has then (the paper classifies them
  w.r.t. the value after `E_i`, which erasing may change).
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

variable {P : Type} [Fintype P] [DecidableEq P]
variable {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable {I : Impl maxRegObj (RWC ι V v₀) P L} {W : Finset P} {val : P → ℕ}

/-- A finite set has a subset on which `f` is injective with the same image. -/
lemma exists_section {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) :
    ∃ t ⊆ s, t.image f = s.image f ∧ ∀ a ∈ t, ∀ b ∈ t, f a = f b → a = b := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, hts, himg, hinj⟩ := ih
    by_cases hfa : f a ∈ s.image f
    · refine ⟨t, hts.trans (Finset.subset_insert _ _), ?_, hinj⟩
      rw [Finset.image_insert, himg, Finset.insert_eq_of_mem hfa]
    · have hat : a ∉ t := fun h => ha (hts h)
      refine ⟨insert a t, Finset.insert_subset_insert _ hts, by
        rw [Finset.image_insert, Finset.image_insert, himg], ?_⟩
      intro x hx y hy hxy
      rcases Finset.mem_insert.1 hx with hxa | hx' <;> rcases Finset.mem_insert.1 hy with hya | hy'
      · rw [hxa, hya]
      · subst hxa; exact absurd (hxy ▸ (himg ▸ Finset.mem_image_of_mem f hy')) hfa
      · subst hya; exact absurd (hxy.symm ▸ (himg ▸ Finset.mem_image_of_mem f hx')) hfa
      · exact hinj x hx' y hy' hxy

lemma Ess.succ_of_empty {i : ℕ} {α : List (Label P maxRegObj)}
    {C : Config maxRegObj (RWC ι V v₀) P L} {G : Ghost P ι V} {H : Finset P}
    (h : Ess I W val i α C G ∅ H) : Ess I W val (i + 1) α C G ∅ H :=
  ⟨h.run, h.subW, h.disj, h.labels, h.ops, h.resps, h.pend, h.supreme, h.hidden,
    by simp, h.blocks⟩

/-! ### Case 1: low contention -/

/-- **Lemma 4, low-contention case.** If the processes of `S ⊆ E` are poised on pairwise distinct
objects, an independent third of them can take one more step each. -/
lemma lemma4_low {i : ℕ} {α : List (Label P maxRegObj)} {C : Config maxRegObj (RWC ι V v₀) P L}
    {G : Ghost P ι V} {E H : Finset P} (hE : Ess I W val i α C G E H) (S : Finset P)
    (hSE : S ⊆ E) (obj : P → ι)
    (hobj : ∀ p ∈ S, ∃ o k, I.act p (C.loc p) = .access (obj p) o k)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, obj p = obj q → p = q) :
    ∃ α' C' G' E' H', Ess I W val (i + 1) α' C' G' E' H' ∧ E' ⊆ S ∧ S.card ≤ 3 * E'.card := by
  classical
  have hI := arun_inv hE.run
  obtain ⟨J, hJS, hJcard, hJind⟩ := exists_indep (fun p => owner E (G.hist (obj p))) S
  have hJE : J ⊆ E := hJS.trans hSE
  set K := E \ J with hK
  have hKE : K ⊆ E := Finset.sdiff_subset
  have hEK : E \ K = J := Finset.sdiff_sdiff_eq_self hJE
  obtain ⟨C₁, G₁, hE₁, h1loc, -, h1hist⟩ := ess_erase hE hKE
  rw [hEK] at hE₁
  have hJK : ∀ p ∈ J, p ∉ K := fun p hp h => (Finset.mem_sdiff.1 h).2 hp
  -- no conflicts
  have hCF : ∀ p ∈ J, (∀ x ∈ J, x ∈ topAw (G₁.hist (obj p)) → x = p) ∧
      (∀ y ∈ block J (G₁.hist (obj p)), y.proc = p) := by
    intro p hp
    rw [h1hist]
    constructor
    · intro x hx hxt
      cases hf : (G.hist (obj p)).filter (fun e => decide (e.proc ∉ K)) with
      | nil => rw [hf] at hxt; simp at hxt
      | cons y t =>
        rw [hf, topAw_cons] at hxt
        have hy : y ∈ G.hist (obj p) := by
          have : y ∈ (G.hist (obj p)).filter (fun e => decide (e.proc ∉ K)) := by
            rw [hf]; exact List.mem_cons_self
          exact (List.mem_filter.1 this).1
        have hyx : y.proc = x := hE.hidden x (hJE hx) y.proc ((hI.entry _ y hy).1 hxt)
        have hyb : y ∈ block E (G.hist (obj p)) :=
          head_filter_mem_block hKE (by rw [hf]; rfl) (hyx ▸ hJE hx)
        have hown := owner_eq_of_mem_block (hE.blocks _) hyb
        rw [hyx] at hown
        exact hJind p hp x hx hown
    · intro y hy
      rw [← hEK] at hy
      have hyb := block_filter_sub hKE _ y hy
      have hown := owner_eq_of_mem_block (hE.blocks _) hyb
      have hyJ : y.proc ∈ J := hEK ▸ (mem_block hy).2
      exact hJind p hp y.proc hyJ hown
  -- run the steps
  let Q : Config maxRegObj (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop := fun C' G' D =>
    Fresh C₁ G₁ J C' G' D ∧ Hidden G' J ∧ (∀ o, BlockOK J (G'.hist o)) ∧
      (∀ q ∈ J, q ∉ D → G'.hist (obj q) = G₁.hist (obj q))
  obtain ⟨C', G', hrun, hQ⟩ := arunFrom_map_tau (I := I) Q J.toList C₁ G₁ ∅
    (Finset.nodup_toList _) (by simp)
    ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, hE₁.hidden, hE₁.blocks, fun _ _ _ => rfl⟩ (by
      intro C₂ G₂ D p ⟨hF, hhid, hblk, hfresh⟩ hpD hpl
      have hpJ : p ∈ J := Finset.mem_toList.1 hpl
      obtain ⟨hloc, hpend, hawp⟩ := hF p hpJ hpD
      obtain ⟨o, k, hact⟩ := hobj p (hJS hpJ)
      have hact' : I.act p (C₂.loc p) = .access (obj p) o k := by
        rw [hloc, (h1loc p (hJK p hpJ)).1]; exact hact
      have hpend' : C₂.pend p ≠ none := by
        rw [hpend, (h1loc p (hJK p hpJ)).2.1]; exact hE.pend p (hJE hpJ)
      have hs := Impl.step_tau_eq_some (I := I) hpend' hact'
      refine ⟨_, hs, fresh_step hF hs, ?_, ?_, ?_⟩
      · obtain ⟨haw1, haw2, -, -⟩ := gstep_tau_cases (G := G₂) hact'
        intro x hx q hq
        by_cases hqp : q = p
        · subst hqp
          rcases Finset.mem_union.1 (haw2 hq) with h | h
          · exact hhid x hx q h
          · have : G₂.F (obj q) = topAw (G₁.hist (obj q)) := by
              simp only [Ghost.F]; rw [hfresh q hpJ hpD]
            rw [this] at h
            exact ((hCF q hpJ).1 x hx h).symm
        · rw [haw1 q hqp] at hq; exact hhid x hx q hq
      · obtain ⟨-, -, hh1, hh2⟩ := gstep_tau_cases (G := G₂) hact'
        intro j
        by_cases hj : j = obj p
        · subst hj
          rcases hh2 with h | ⟨v, h⟩
          · rw [h]; exact hblk _
          · rw [h]
            apply blockOK_cons_self (hblk _)
            intro y hy
            rw [hfresh p hpJ hpD] at hy
            exact (hCF p hpJ).2 y hy
        · rw [hh1 j hj]; exact hblk j
      · obtain ⟨-, -, hh1, -⟩ := gstep_tau_cases (G := G₂) hact'
        intro q hq hqD
        have hqp : q ≠ p := fun h => hqD (h ▸ Finset.mem_insert_self _ _)
        have hobjq : obj q ≠ obj p := fun h => hqp (hinj q (hJS hq) p (hJS hpJ) h)
        rw [hh1 _ hobjq]
        exact hfresh q hq (fun h => hqD (Finset.mem_insert_of_mem h)))
  obtain ⟨-, hhid, hblk, -⟩ := hQ
  refine ⟨_, C', G', J, _, ess_step hE₁ J.toList (List.Perm.refl _) hrun subset_rfl
    (by simp) hhid hblk, hJS, hJcard⟩

/-! ### Case 2: high contention -/

/-- In the high-contention case, after erasing every essential process outside `P'` (which does
not contain the owner of the block of `o`), the top entry of `o`'s history is written by a
non-essential process. -/
lemma head_not_mem_of_owner {E P' K : Finset P} {h : List (Entry P V)} (hb : BlockOK E h)
    (hown : ∀ p ∈ P', owner E h ≠ some p) (hK1 : E \ P' ⊆ K) (hK2 : K ⊆ E) :
    ∀ y ∈ (h.filter (fun e => decide (e.proc ∉ K))).head?, y.proc ∉ E := by
  intro y hy hyE
  have hyb := head_filter_mem_block hK2 (Option.mem_def.1 hy) hyE
  have hown' := owner_eq_of_mem_block hb hyb
  have hyK : y.proc ∉ K := by
    have hmem : y ∈ h.filter (fun e => decide (e.proc ∉ K)) := by
      cases hfl : h.filter (fun e => decide (e.proc ∉ K)) with
      | nil => rw [hfl] at hy; simp at hy
      | cons a t => rw [hfl] at hy; simp only [List.head?_cons, Option.mem_def,
          Option.some.injEq] at hy; subst hy; exact List.mem_cons_self
    simpa using (List.mem_filter.1 hmem).2
  have hyP : y.proc ∈ P' := by
    by_contra h'; exact hyK (hK1 (Finset.mem_sdiff.2 ⟨hyE, h'⟩))
  exact hown y.proc hyP hown'

/-- The common situation of the high-contention case: object `o`, a set `P' ⊆ E` of processes
not owning the block of `o`, and the value `vs` of `o` once the other essential processes are
erased. -/
structure HC (hE : Ess I W val i α C G E H) (o : ι) (P' : Finset P) (vs : V) : Prop where
  sub : P' ⊆ E
  own : ∀ p ∈ P', owner E (G.hist o) ≠ some p
  val_eq : topVal (I.memInit o) ((G.hist o).filter (fun e => decide (e.proc ∉ E \ P'))) = vs

variable {i : ℕ} {α : List (Label P maxRegObj)} {C : Config maxRegObj (RWC ι V v₀) P L}
  {G : Ghost P ι V} {E H : Finset P}

/-- Erasing `K = E \ Cls` for `Cls ⊆ P'` in the high-contention situation: the value of `o` is
`vs`, its familiarity set contains no essential process, and its block is empty. -/
lemma HC.erase {hE : Ess I W val i α C G E H} {o : ι} {P' : Finset P} {vs : V}
    (hc : HC hE o P' vs) {Cls : Finset P} (hCls : Cls ⊆ P') :
    ∃ C₁ G₁, Ess I W val i (α.filter (fun ℓ => decide (ℓ.proc ∉ E \ Cls))) C₁ G₁ Cls H ∧
      (∀ q, q ∉ E \ Cls → C₁.loc q = C.loc q ∧ C₁.pend q = C.pend q ∧ G₁.aw q = G.aw q) ∧
      (∀ q, G₁.aw q ⊆ G.aw q) ∧
      C₁.mem o = vs ∧ (∀ x ∈ E, x ∉ topAw (G₁.hist o)) ∧
      (∀ y ∈ (G₁.hist o).head?, y.proc ∉ E) := by
  have hClsE : Cls ⊆ E := hCls.trans hc.sub
  have hKE : E \ Cls ⊆ E := Finset.sdiff_subset
  have hK1 : E \ P' ⊆ E \ Cls := Finset.sdiff_subset_sdiff le_rfl hCls
  obtain ⟨C₁, G₁, hE₁, h1loc, h1sub, h1hist⟩ := ess_erase hE hKE
  rw [Finset.sdiff_sdiff_eq_self hClsE] at hE₁
  have hI := arun_inv hE.run
  have hI₁ := arun_inv hE₁.run
  have hhead := head_not_mem_of_owner (hE.blocks o) hc.own hK1 hKE
  refine ⟨C₁, G₁, hE₁, h1loc, h1sub, ?_, ?_, ?_⟩
  · rw [hI₁.mem_eq, h1hist, ← hc.val_eq]
    apply topVal_eq_of_head?
    symm
    apply head_filter_eq (Finset.sdiff_subset_sdiff le_rfl hCls)
    intro y hy hyK
    have hhead' := head_not_mem_of_owner (hE.blocks o) hc.own le_rfl Finset.sdiff_subset y hy
    exact hhead' (Finset.mem_sdiff.1 hyK).1
  · intro x hx hxt
    rw [h1hist] at hxt
    cases hf : (G.hist o).filter (fun e => decide (e.proc ∉ E \ Cls)) with
    | nil => rw [hf] at hxt; simp at hxt
    | cons y t =>
      rw [hf, topAw_cons] at hxt
      have hy : y ∈ G.hist o := by
        have : y ∈ (G.hist o).filter (fun e => decide (e.proc ∉ E \ Cls)) := by
          rw [hf]; exact List.mem_cons_self
        exact (List.mem_filter.1 this).1
      have hyx : y.proc = x := hE.hidden x hx y.proc ((hI.entry _ y hy).1 hxt)
      exact hhead y (by rw [hf]; rfl) (hyx ▸ hx)
  · rw [h1hist]; exact hhead

/-- **Lemma 4, high contention, sub-case 3 (reads and value-preserving CAS).** -/
lemma lemma4_T {hE : Ess I W val i α C G E H} {o : ι} {P' : Finset P} {vs : V}
    (hc : HC hE o P' vs) (T : Finset P) (hT : T ⊆ P')
    (hop : ∀ p ∈ T, ∃ op k, I.act p (C.loc p) = .access o op k ∧ (∀ v, op ≠ .write v) ∧
      ∀ a b, op = .cas a b → ¬ (vs = a ∧ b ≠ a)) :
    ∃ α' C' G' E' H', Ess I W val (i + 1) α' C' G' E' H' ∧ E' ⊆ E ∧ T.card ≤ E'.card := by
  classical
  obtain ⟨C₁, G₁, hE₁, h1loc, -, hmem, hnoE, -⟩ := hc.erase hT
  have hTE : T ⊆ E := hT.trans hc.sub
  have hTK : ∀ p ∈ T, p ∉ E \ T := fun p hp h => (Finset.mem_sdiff.1 h).2 hp
  let Q : Config maxRegObj (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop := fun C' G' D =>
    Fresh C₁ G₁ T C' G' D ∧ G'.hist = G₁.hist ∧ C'.mem o = vs ∧ Hidden G' T
  obtain ⟨C', G', hrun, hQ⟩ := arunFrom_map_tau (I := I) Q T.toList C₁ G₁ ∅
    (Finset.nodup_toList _) (by simp) ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, rfl, hmem, hE₁.hidden⟩ (by
      intro C₂ G₂ D p ⟨hF, hh, hm, hhid⟩ hpD hpl
      have hpT : p ∈ T := Finset.mem_toList.1 hpl
      obtain ⟨hloc, hpend, hawp⟩ := hF p hpT hpD
      obtain ⟨op, k, hact, hnw, hnc⟩ := hop p hpT
      have hact' : I.act p (C₂.loc p) = .access o op k := by
        rw [hloc, (h1loc p (hTK p hpT)).1]; exact hact
      have hpend' : C₂.pend p ≠ none := by
        rw [hpend, (h1loc p (hTK p hpT)).2.1]; exact hE.pend p (hTE hpT)
      have hs := Impl.step_tau_eq_some (I := I) hpend' hact'
      have hFo : ∀ x ∈ T, x ∉ G₂.F o := fun x hx h => by
        simp only [Ghost.F, hh] at h; exact hnoE x (hTE hx) h
      refine ⟨_, hs, fresh_step hF hs, ?_, ?_, ?_⟩
      · cases op with
        | read => rw [gstep_tau_read hact']; exact hh
        | write v => exact absurd rfl (hnw v)
        | cas a b =>
          rw [gstep_tau_cas hact']
          have : ¬ (C₂.mem o = a ∧ b ≠ a) := by rw [hm]; exact hnc a b rfl
          simp only [this, if_false]; exact hh
      · cases op with
        | read => simp [hm]
        | write v => exact absurd rfl (hnw v)
        | cas a b =>
          have := hnc a b rfl
          by_cases hva : vs = a
          · have hb : b = a := by by_contra hb; exact this ⟨hva, hb⟩
            simp [hm, hva, hb]
          · simp [hm, hva]
      · intro x hx q hq
        obtain ⟨haw1, haw2, -, -⟩ := gstep_tau_cases (G := G₂) hact'
        by_cases hqp : q = p
        · subst hqp
          rcases Finset.mem_union.1 (haw2 hq) with h | h
          · exact hhid x hx q h
          · exact absurd h (hFo x hx)
        · rw [haw1 q hqp] at hq; exact hhid x hx q hq)
  obtain ⟨-, hh, -, hhid⟩ := hQ
  exact ⟨_, C', G', T, _, ess_step hE₁ T.toList (List.Perm.refl _) hrun subset_rfl (by simp) hhid
    (fun j => by rw [hh]; exact hE₁.blocks j), hTE, le_rfl⟩

/-- The process with the smallest value in a nonempty set of writers. -/
lemma exists_min_val (hinj : Set.InjOn val W) {S : Finset P} (hSW : S ⊆ W) (hne : S.Nonempty) :
    ∃ pl ∈ S, ∀ e ∈ S.erase pl, val pl < val e := by
  obtain ⟨pl, hpl, hmin⟩ := Finset.exists_min_image S val hne
  refine ⟨pl, hpl, fun e he => lt_of_le_of_ne (hmin e (Finset.mem_of_mem_erase he)) ?_⟩
  intro h
  exact (Finset.ne_of_mem_erase he) (hinj (hSW (Finset.mem_of_mem_erase he)) (hSW hpl) h.symm)

/-- **Lemma 4, high contention, sub-case 2 (writes).** -/
lemma lemma4_W (hinj : Set.InjOn val W) {hE : Ess I W val i α C G E H} {o : ι} {P' : Finset P}
    {vs : V} (hc : HC hE o P' vs) (Wc : Finset P) (hW : Wc ⊆ P') (hne : Wc.Nonempty)
    (hop : ∀ p ∈ Wc, ∃ v k, I.act p (C.loc p) = .access o (.write v) k) :
    ∃ α' C' G' E' H', Ess I W val (i + 1) α' C' G' E' H' ∧ E' ⊆ E ∧ Wc.card ≤ E'.card + 1 := by
  classical
  obtain ⟨C₁, G₁, hE₁, h1loc, -, -, -, -⟩ := hc.erase hW
  have hWE : Wc ⊆ E := hW.trans hc.sub
  have hWK : ∀ p ∈ Wc, p ∉ E \ Wc := fun p hp h => (Finset.mem_sdiff.1 h).2 hp
  obtain ⟨pl, hpl, hmin⟩ := exists_min_val hinj (hWE.trans
    (Finset.subset_union_left.trans hE.subW)) hne
  set E' := Wc.erase pl with hE'
  have hplE' : pl ∉ E' := Finset.notMem_erase pl Wc
  -- phase 1: the writes of `E'`
  let Q : Config maxRegObj (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop := fun C' G' D =>
    Fresh C₁ G₁ Wc C' G' D ∧ G'.aw = G₁.aw ∧ ∀ j, j ≠ o → G'.hist j = G₁.hist j
  have hstep : ∀ (C₂ : Config maxRegObj (RWC ι V v₀) P L) (G₂ : Ghost P ι V) (D : Finset P) (p : P),
      Q C₂ G₂ D → p ∉ D → p ∈ Wc →
      ∃ C', I.step C₂ (.tau p) = some C' ∧ Q C' (gstep I C₂ G₂ (.tau p)) (insert p D) ∧
        ∃ v, (gstep I C₂ G₂ (.tau p)).hist o = ⟨p, v, G₂.aw p⟩ :: G₂.hist o := by
    intro C₂ G₂ D p ⟨hF, haw, hh⟩ hpD hpW
    obtain ⟨hloc, hpend, -⟩ := hF p hpW hpD
    obtain ⟨v, k, hact⟩ := hop p hpW
    have hact' : I.act p (C₂.loc p) = .access o (.write v) k := by
      rw [hloc, (h1loc p (hWK p hpW)).1]; exact hact
    have hpend' : C₂.pend p ≠ none := by
      rw [hpend, (h1loc p (hWK p hpW)).2.1]; exact hE.pend p (hWE hpW)
    have hs := Impl.step_tau_eq_some (I := I) hpend' hact'
    refine ⟨_, hs, ⟨fresh_step hF hs, ?_, ?_⟩, v, ?_⟩
    · rw [gstep_tau_write hact']; exact haw
    · intro j hj; rw [gstep_tau_write hact']; simp [Function.update_of_ne hj, hh j hj]
    · rw [gstep_tau_write hact']; simp
  obtain ⟨C₂, G₂, hrun2, hQ2⟩ := arunFrom_map_tau (I := I) Q E'.toList C₁ G₁ ∅
    (Finset.nodup_toList _) (by simp) ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, rfl, fun _ _ => rfl⟩
    (fun C₂ G₂ D p hQ hpD hpl => by
      obtain ⟨C', h1, h2, -⟩ := hstep C₂ G₂ D p hQ hpD
        (Finset.mem_of_mem_erase (Finset.mem_toList.1 hpl))
      exact ⟨C', h1, h2⟩)
  -- phase 2: the write of `pl`
  obtain ⟨C₃, hs3, hQ3, v, hv⟩ := hstep C₂ G₂ _ pl hQ2 (by simpa using hplE') hpl
  have hrun : arunFrom I (C₁, G₁) ((E'.toList ++ [pl]).map .tau) =
      some (C₃, gstep I C₂ G₂ (.tau pl)) := by
    rw [List.map_append, arunFrom_append, hrun2, Option.bind_some, List.map_singleton,
      arunFrom_singleton]
    exact (astep_eq_some I).2 ⟨hs3, rfl⟩
  have hperm : (E'.toList ++ [pl]).Perm Wc.toList := by
    rw [List.perm_ext_iff_of_nodup _ (Finset.nodup_toList _)]
    · intro x
      simp only [List.mem_append, Finset.mem_toList, List.mem_singleton, hE', Finset.mem_erase]
      constructor
      · rintro (⟨-, h⟩ | rfl) <;> assumption
      · intro hx; by_cases hxp : x = pl
        · exact Or.inr hxp
        · exact Or.inl ⟨hxp, hx⟩
    · exact List.Nodup.append (Finset.nodup_toList _) (List.nodup_singleton _)
        (by simpa using hplE')
  obtain ⟨-, haw3, hh3⟩ := hQ3
  refine ⟨_, C₃, _, E', _, ess_step hE₁ _ hperm hrun (Finset.erase_subset _ _) ?_ ?_ ?_,
    (Finset.erase_subset _ _).trans hWE, ?_⟩
  · intro h hh e he
    have : h = pl := by
      by_contra hne'; exact (Finset.mem_sdiff.1 hh).2 (Finset.mem_erase.2 ⟨hne', (Finset.mem_sdiff.1 hh).1⟩)
    subst this; exact hmin e he
  · intro x hx q hq
    rw [haw3] at hq; exact hE₁.hidden x (Finset.mem_of_mem_erase hx) q hq
  · intro j
    by_cases hj : j = o
    · subst hj; rw [hv]; exact blockOK_cons_of_not_mem hplE'
    · rw [hh3 j hj]; exact (hE₁.blocks j).mono (Finset.erase_subset _ _)
  · rw [Finset.card_erase_of_mem hpl]; omega

/-- **Lemma 4, high contention, sub-case 1 (value-changing CAS).** -/
lemma lemma4_C (hinj : Set.InjOn val W) {hE : Ess I W val i α C G E H} {o : ι} {P' : Finset P}
    {vs : V} (hc : HC hE o P' vs) (Cc : Finset P) (hCc : Cc ⊆ P') (hne : Cc.Nonempty)
    (hop : ∀ p ∈ Cc, ∃ b k, I.act p (C.loc p) = .access o (.cas vs b) k ∧ b ≠ vs) :
    ∃ α' C' G' E' H', Ess I W val (i + 1) α' C' G' E' H' ∧ E' ⊆ E ∧ Cc.card ≤ E'.card + 1 := by
  classical
  obtain ⟨C₁, G₁, hE₁, h1loc, -, hmem, hnoE, -⟩ := hc.erase hCc
  have hCE : Cc ⊆ E := hCc.trans hc.sub
  have hCK : ∀ p ∈ Cc, p ∉ E \ Cc := fun p hp h => (Finset.mem_sdiff.1 h).2 hp
  obtain ⟨pl, hpl, hmin⟩ := exists_min_val hinj (hCE.trans
    (Finset.subset_union_left.trans hE.subW)) hne
  set E' := Cc.erase pl with hE'
  have hplE' : pl ∉ E' := Finset.notMem_erase pl Cc
  -- the successful CAS of `pl`
  obtain ⟨bl, kl, hactl, hbl⟩ := hop pl hpl
  have hactl' : I.act pl (C₁.loc pl) = .access o (.cas vs bl) kl := by
    rw [(h1loc pl (hCK pl hpl)).1]; exact hactl
  have hpendl : C₁.pend pl ≠ none := by
    rw [(h1loc pl (hCK pl hpl)).2.1]; exact hE.pend pl (hCE hpl)
  obtain ⟨C₂, hs2⟩ : ∃ C₂, I.step C₁ (.tau pl) = some C₂ :=
    ⟨_, Impl.step_tau_eq_some (I := I) hpendl hactl'⟩
  set G₂ := gstep I C₁ G₁ (.tau pl) with hG₂
  have hG₂eq := gstep_tau_cas (G := G₁) hactl'
  have hcond : C₁.mem o = vs ∧ bl ≠ vs := ⟨hmem, hbl⟩
  simp only [hcond, ne_eq, not_false_eq_true, and_self, if_true] at hG₂eq
  have hmem2 : C₂.mem o = bl := by
    have := (Impl.step_tau hs2).2.2
    obtain ⟨i', o', k', hact', hm', -⟩ := this
    rw [hactl'] at hact'; cases hact'
    rw [hm']; simp [hmem]
  have hloc2 : ∀ q, q ≠ pl → C₂.loc q = C₁.loc q ∧ C₂.pend q = C₁.pend q := fun q hq =>
    Impl.step_other hs2 (by simpa [Label.proc] using Ne.symm hq)
  have hpend2 : C₂.pend = C₁.pend := (Impl.step_tau hs2).2.1
  -- awareness of `pl` contains no process of `E'`
  have hawl : ∀ x ∈ E', x ∉ G₁.aw pl ∪ G₁.F o := by
    intro x hx h
    rcases Finset.mem_union.1 h with h | h
    · exact (Finset.ne_of_mem_erase hx) (hE₁.hidden x (Finset.mem_of_mem_erase hx) pl h).symm
    · exact hnoE x (hCE (Finset.mem_of_mem_erase hx)) h
  -- the failing CAS of `E'`
  let Q : Config maxRegObj (RWC ι V v₀) P L → Ghost P ι V → Finset P → Prop := fun C' G' D =>
    Fresh C₂ G₂ E' C' G' D ∧ G'.hist = G₂.hist ∧ C'.mem o = bl ∧ Hidden G' E'
  have hhid2 : Hidden G₂ E' := by
    intro x hx q hq
    by_cases hqp : q = pl
    · subst hqp; rw [hG₂, hG₂eq] at hq; simp only [Function.update_self] at hq
      exact absurd hq (hawl x hx)
    · rw [hG₂, hG₂eq] at hq; simp only [Function.update_of_ne hqp] at hq
      exact hE₁.hidden x (Finset.mem_of_mem_erase hx) q hq
  obtain ⟨C', G', hrun', hQ⟩ := arunFrom_map_tau (I := I) Q E'.toList C₂ G₂ ∅
    (Finset.nodup_toList _) (by simp) ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, rfl, hmem2, hhid2⟩ (by
      intro C₃ G₃ D p ⟨hF, hh, hm, hhid⟩ hpD hpl'
      have hpE' : p ∈ E' := Finset.mem_toList.1 hpl'
      have hpC : p ∈ Cc := Finset.mem_of_mem_erase hpE'
      have hppl : p ≠ pl := Finset.ne_of_mem_erase hpE'
      obtain ⟨hloc, hpend, -⟩ := hF p hpE' hpD
      obtain ⟨b, k, hact, hb⟩ := hop p hpC
      have hact' : I.act p (C₃.loc p) = .access o (.cas vs b) k := by
        rw [hloc, (hloc2 p hppl).1, (h1loc p (hCK p hpC)).1]; exact hact
      have hpend' : C₃.pend p ≠ none := by
        rw [hpend, hpend2, (h1loc p (hCK p hpC)).2.1]; exact hE.pend p (hCE hpC)
      have hs := Impl.step_tau_eq_some (I := I) hpend' hact'
      have hfail : ¬ (C₃.mem o = vs ∧ b ≠ vs) := by rw [hm]; exact fun h => hbl h.1
      refine ⟨_, hs, fresh_step hF hs, ?_, ?_, ?_⟩
      · rw [gstep_tau_cas hact']; simp only [hfail, if_false]; exact hh
      · have : bl ≠ vs := hbl
        simp [hm, this]
      · intro x hx q hq
        rw [gstep_tau_cas hact'] at hq
        by_cases hqp : q = p
        · subst hqp
          simp only [Function.update_self] at hq
          rcases Finset.mem_union.1 hq with h | h
          · exact hhid x hx q h
          · exfalso
            simp only [Ghost.F, hh, hG₂, hG₂eq, Function.update_self, topAw_cons] at h
            exact hawl x hx h
        · simp only [Function.update_of_ne hqp] at hq; exact hhid x hx q hq)
  obtain ⟨-, hh, -, hhid⟩ := hQ
  have hrun : arunFrom I (C₁, G₁) ((pl :: E'.toList).map .tau) = some (C', G') := by
    simp only [List.map_cons, arunFrom_cons]
    rw [show astep I (C₁, G₁) (.tau pl) = some (C₂, G₂) from (astep_eq_some I).2 ⟨hs2, rfl⟩]
    exact hrun'
  have hperm : (pl :: E'.toList).Perm Cc.toList := by
    rw [List.perm_ext_iff_of_nodup _ (Finset.nodup_toList _)]
    · intro x
      simp only [List.mem_cons, Finset.mem_toList, hE', Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨-, h⟩) <;> assumption
      · intro hx; by_cases hxp : x = pl
        · exact Or.inl hxp
        · exact Or.inr ⟨hxp, hx⟩
    · exact List.nodup_cons.2 ⟨by simpa using hplE', Finset.nodup_toList _⟩
  refine ⟨_, C', G', E', _, ess_step hE₁ _ hperm hrun (Finset.erase_subset _ _) ?_ hhid ?_,
    (Finset.erase_subset _ _).trans hCE, ?_⟩
  · intro h hh e he
    have : h = pl := by
      by_contra hne'; exact (Finset.mem_sdiff.1 hh).2 (Finset.mem_erase.2 ⟨hne', (Finset.mem_sdiff.1 hh).1⟩)
    subst this; exact hmin e he
  · intro j
    rw [hh, hG₂, hG₂eq]
    by_cases hj : j = o
    · subst hj; simp only [Function.update_self]; exact blockOK_cons_of_not_mem hplE'
    · simp only [Function.update_of_ne hj]; exact (hE₁.blocks j).mono (Finset.erase_subset _ _)
  · rw [Finset.card_erase_of_mem hpl]; omega

open Classical in
/-- **Lemma 4 of Hendler–Khait, PODC'14 (with the block invariant).** From an execution with an
`i`-step essential set `E`, of which `m` processes are poised to access a base object, there is
an execution with an `(i+1)`-step essential set `E' ⊆ E` such that `⌊√m⌋ ≤ 3 (|E'| + 1)`
(in particular `|E'| ≥ √m/3 − 2`, the paper's bound; we need no assumption `m ≥ 81`). -/
theorem lemma4 (hinj : Set.InjOn val W) (hE : Ess I W val i α C G E H) :
    ∃ α' C' G' E' H', Ess I W val (i + 1) α' C' G' E' H' ∧ E' ⊆ E ∧
      Nat.sqrt (E.filter (fun e => ∃ j o k, I.act e (C.loc e) = Action.access j o k)).card ≤
        3 * (E'.card + 1) := by
  set Ee := E.filter (fun e => ∃ j o k, I.act e (C.loc e) = Action.access j o k) with hEe
  rcases Ee.eq_empty_or_nonempty with h0 | ⟨p₀, hp₀⟩
  · obtain ⟨C₀, G₀, hE₀, -⟩ := ess_erase hE (subset_refl E)
    rw [Finset.sdiff_self] at hE₀
    exact ⟨_, C₀, G₀, ∅, H, hE₀.succ_of_empty, Finset.empty_subset _, by rw [h0, Finset.card_empty]; exact (Nat.sqrt_le_self 0).trans (by omega)⟩
  obtain ⟨o₀, -, -, -⟩ := (Finset.mem_filter.1 hp₀).2
  let obj : P → ι := fun p => match I.act p (C.loc p) with
    | .access j _ _ => j
    | .ret _ _ => o₀
  have hobj : ∀ p ∈ Ee, ∃ op k, I.act p (C.loc p) = .access (obj p) op k := by
    intro p hp
    obtain ⟨j, op, k, h⟩ := (Finset.mem_filter.1 hp).2
    have hj : obj p = j := by
      show (match I.act p (C.loc p) with
        | .access j _ _ => j
        | .ret _ _ => o₀) = j
      rw [h]
    subst hj
    exact ⟨op, k, h⟩
  have hEeE : Ee ⊆ E := Finset.filter_subset _ _
  set s := Nat.sqrt Ee.card with hs
  by_cases hhigh : ∃ o ∈ Ee.image obj, s < (Ee.filter (fun p => obj p = o)).card
  · -- high contention
    obtain ⟨o, -, ho⟩ := hhigh
    set F := Ee.filter (fun p => obj p = o) with hF
    set P' := F.filter (fun p => owner E (G.hist o) ≠ some p) with hP'
    have hFP' : F.card ≤ P'.card + 1 := by
      have h1 := Finset.card_le_card_sdiff_add_card (s := F) (t := P')
      have h2 : (F \ P').card ≤ 1 := by
        refine (Finset.card_le_card (t := (owner E (G.hist o)).toList.toFinset) ?_).trans ?_
        · intro p hp
          obtain ⟨hpF, hpP'⟩ := Finset.mem_sdiff.1 hp
          have : owner E (G.hist o) = some p := by
            by_contra h; exact hpP' (Finset.mem_filter.2 ⟨hpF, h⟩)
          simp [this]
        · cases owner E (G.hist o) <;> simp
      omega
    have hsP' : s ≤ P'.card := by omega
    have hP'F : P' ⊆ F := Finset.filter_subset _ _
    have hFEe : F ⊆ Ee := Finset.filter_subset _ _
    have hP'E : P' ⊆ E := hP'F.trans (hFEe.trans hEeE)
    set vs := topVal (I.memInit o) ((G.hist o).filter (fun e => decide (e.proc ∉ E \ P')))
    have hc : HC hE o P' vs := ⟨hP'E, fun p hp => (Finset.mem_filter.1 hp).2, rfl⟩
    have hobjo : ∀ p ∈ P', ∃ op k, I.act p (C.loc p) = .access o op k := by
      intro p hp
      have hpF := hP'F hp
      obtain ⟨op, k, h⟩ := hobj p (hFEe hpF)
      rw [(Finset.mem_filter.1 hpF).2] at h
      exact ⟨op, k, h⟩
    set Wc := P'.filter (fun p => ∃ v k, I.act p (C.loc p) = .access o (.write v) k) with hWc
    set Cc := P'.filter (fun p => ∃ b k, I.act p (C.loc p) = .access o (.cas vs b) k ∧ b ≠ vs)
      with hCc
    set T := P'.filter (fun p => p ∉ Wc ∧ p ∉ Cc) with hT
    have hsum : P'.card ≤ T.card + Wc.card + Cc.card := by
      have : P' ⊆ T ∪ Wc ∪ Cc := by
        intro p hp
        by_cases h1 : p ∈ Wc
        · simp [h1]
        · by_cases h2 : p ∈ Cc
          · simp [h2]
          · simp [hT, hp, h1, h2]
      exact (Finset.card_le_card this).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    by_cases h3T : P'.card ≤ 3 * T.card
    · obtain ⟨α', C', G', E', H', hE', hsub, hcard⟩ := lemma4_T hc T (Finset.filter_subset _ _)
        (by
          intro p hp
          obtain ⟨hpP', hpW, hpC⟩ := Finset.mem_filter.1 hp
          obtain ⟨op, k, h⟩ := hobjo p hpP'
          refine ⟨op, k, h, fun v hv => hpW (Finset.mem_filter.2 ⟨hpP', v, k, hv ▸ h⟩), ?_⟩
          rintro a b rfl ⟨hva, hb⟩
          subst hva
          exact hpC (Finset.mem_filter.2 ⟨hpP', b, k, h, hb⟩))
      exact ⟨α', C', G', E', H', hE', hsub, by omega⟩
    by_cases h3W : P'.card ≤ 3 * Wc.card
    · have hne : Wc.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨α', C', G', E', H', hE', hsub, hcard⟩ := lemma4_W hinj hc Wc
        (Finset.filter_subset _ _) hne (fun p hp => (Finset.mem_filter.1 hp).2)
      exact ⟨α', C', G', E', H', hE', hsub, by omega⟩
    · have h3C : P'.card ≤ 3 * Cc.card := by omega
      have hne : Cc.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨α', C', G', E', H', hE', hsub, hcard⟩ := lemma4_C hinj hc Cc
        (Finset.filter_subset _ _) hne (fun p hp => (Finset.mem_filter.1 hp).2)
      exact ⟨α', C', G', E', H', hE', hsub, by omega⟩
  · -- low contention
    push_neg at hhigh
    obtain ⟨S, hSEe, himg, hinjS⟩ := exists_section obj Ee
    obtain ⟨α', C', G', E', H', hE', hsub, hcard⟩ := lemma4_low hE S (hSEe.trans hEeE) obj
      (fun p hp => hobj p (hSEe hp)) hinjS
    have hSk : S.card = (Ee.image obj).card := by
      rw [← himg, Finset.card_image_of_injOn (fun a ha b hb h => hinjS a ha b hb h)]
    have hm : Ee.card ≤ s * (Ee.image obj).card :=
      Finset.card_le_mul_card_image Ee s (fun o ho => hhigh o ho)
    have hss : s * s ≤ Ee.card := Nat.sqrt_le Ee.card
    have hsS : s ≤ S.card := by
      rcases Nat.eq_zero_or_pos s with h | h
      · omega
      · rw [hSk]; exact Nat.le_of_mul_le_mul_left (hss.trans hm) h
    exact ⟨α', C', G', E', H', hE', hsub.trans (hSEe.trans hEeE), by omega⟩

end Podc.ReadUpdateTradeoffs
