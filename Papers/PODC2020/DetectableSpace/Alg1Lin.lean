import Papers.PODC2020.DetectableSpace.Alg1Defs
import Papers.PODC2020.DetectableSpace.Lin

/-!
# Linearization tools for registers (used for Algorithm 1)

Linearizations of register histories that are built incrementally, with *speculative* writes:
a write immediately followed (in the linearization) by another write can be removed without
affecting the responses of reads (`LegalG.erase_ww`).

* `LegalG ρ σ L`: legality of `L` from value `σ` where `ρ a r` collects the responses operation
  `a` returned *or has committed to* (persisted but not yet returned);
* `DL h ρ σ L`: the conditions of `DLin` with `LegalG ρ` instead of `Legal h`;
* `Good S L`: every element of `L` with identifier in `S` is a write immediately followed by a
  write; such elements can be removed (`rmId`).
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

variable {V : Type} {P : Type}

/-- Remove the entries with identifier `a`. -/
def rmId (a : ℕ) (L : List (ℕ × RWOp V)) : List (ℕ × RWOp V) := L.filter (fun x => x.1 ≠ a)

/-- Legality of a register linearization w.r.t. a set `ρ` of (committed) responses. -/
def LegalG (ρ : ℕ → V → Prop) : V → List (ℕ × RWOp V) → Prop
  | _, [] => True
  | σ, (a, .read) :: L => (∀ r, ρ a r → r = σ) ∧ LegalG ρ σ L
  | _, (a, .write v) :: L => (∀ r, ρ a r → r = v) ∧ LegalG ρ v L

/-- Value of the register after the operations of `L`. -/
def fin (σ : V) : List (ℕ × RWOp V) → V
  | [] => σ
  | (_, .read) :: L => fin σ L
  | (_, .write v) :: L => fin v L

/-- `x` is a write. -/
def IsW : RWOp V → Prop
  | .write _ => True
  | .read => False

/-- The list starts with a write. -/
def NextW : List (ℕ × RWOp V) → Prop
  | [] => False
  | y :: _ => IsW y.2

/-- Every element with identifier in `S` is a write immediately followed by a write. -/
def Good (S : ℕ → Prop) : List (ℕ × RWOp V) → Prop
  | [] => True
  | x :: L => (S x.1 → IsW x.2 ∧ NextW L) ∧ Good S L

/-- Durable detectable linearization with committed responses `ρ`. -/
structure DL (h : List (HEv P (RWOp V) V)) (ρ : ℕ → V → Prop) (σ : V)
    (L : List (ℕ × RWOp V)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  inv_of_mem : ∀ x ∈ L, ∃ p, HEv.inv x.1 p x.2 ∈ h
  mem_of_res : ∀ a r c, HEv.res a (some r) c ∈ h → a ∈ L.map Prod.fst
  not_mem_of_fail : ∀ a c, HEv.res a none c ∈ h → a ∉ L.map Prod.fst
  rt : L.Pairwise (fun x y => ¬ Prec h y.1 x.1)
  legal : LegalG ρ σ L

/-! ### `fin` -/

lemma fin_eq_runOps (v₀ : V) : ∀ (σ : V) (L : List (ℕ × RWOp V)),
    (register V v₀).runOps σ (L.map Prod.snd) = fin σ L := by
  intro σ L
  induction L generalizing σ with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    cases o with
    | read => exact ih σ
    | write v => exact ih v

lemma fin_append (σ : V) (L M : List (ℕ × RWOp V)) : fin σ (L ++ M) = fin (fin σ L) M := by
  induction L generalizing σ with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    cases o <;> simp [fin, ih]

lemma fin_write_last (σ : V) (L : List (ℕ × RWOp V)) (a : ℕ) (v : V) :
    fin σ (L ++ [(a, .write v)]) = v := by
  rw [fin_append]; rfl

lemma fin_read_last (σ : V) (L : List (ℕ × RWOp V)) (a : ℕ) :
    fin σ (L ++ [(a, .read)]) = fin σ L := by
  rw [fin_append]; rfl

/-! ### `LegalG` -/

lemma LegalG.append {ρ : ℕ → V → Prop} : ∀ {σ : V} {L M : List (ℕ × RWOp V)},
    LegalG ρ σ L → LegalG ρ (fin σ L) M → LegalG ρ σ (L ++ M) := by
  intro σ L M
  induction L generalizing σ with
  | nil => intro _ h; exact h
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    cases o with
    | read => intro h1 h2; exact ⟨h1.1, ih h1.2 h2⟩
    | write v => intro h1 h2; exact ⟨h1.1, ih h1.2 h2⟩

lemma LegalG.of_append {ρ : ℕ → V → Prop} : ∀ {σ : V} {L M : List (ℕ × RWOp V)},
    LegalG ρ σ (L ++ M) → LegalG ρ σ L ∧ LegalG ρ (fin σ L) M := by
  intro σ L M
  induction L generalizing σ with
  | nil => intro h; exact ⟨trivial, h⟩
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    cases o with
    | read => intro h; exact ⟨⟨h.1, (ih h.2).1⟩, (ih h.2).2⟩
    | write v => intro h; exact ⟨⟨h.1, (ih h.2).1⟩, (ih h.2).2⟩

/-- Changing the committed responses. -/
lemma LegalG.weaken {ρ ρ' : ℕ → V → Prop} : ∀ {σ : V} {L : List (ℕ × RWOp V)},
    LegalG ρ σ L → (∀ a r, ρ' a r → ρ a r ∨ ∀ x ∈ L, x.1 = a → x.2 = .write r) →
    LegalG ρ' σ L := by
  intro σ L
  induction L generalizing σ with
  | nil => intro _ _; trivial
  | cons x L ih =>
    obtain ⟨a, o⟩ := x
    intro hl hρ
    have hρL : ∀ a r, ρ' a r → ρ a r ∨ ∀ x ∈ L, x.1 = a → x.2 = .write r := by
      intro a' r h
      rcases hρ a' r h with h | h
      · exact .inl h
      · exact .inr fun x hx => h x (by simp [hx])
    cases o with
    | read =>
      refine ⟨fun r hr => ?_, ih hl.2 hρL⟩
      rcases hρ a r hr with h | h
      · exact hl.1 r h
      · have := h (a, .read) (by simp) rfl; simp at this
    | write v =>
      refine ⟨fun r hr => ?_, ih hl.2 hρL⟩
      rcases hρ a r hr with h | h
      · exact hl.1 r h
      · have := h (a, .write v) (by simp) rfl; simp at this; exact this.symm

/-- Removing a write immediately followed by a write. -/
lemma LegalG.erase_ww {ρ : ℕ → V → Prop} {a b : ℕ} {v w : V} :
    ∀ {σ : V} {L₁ L₂ : List (ℕ × RWOp V)},
    LegalG ρ σ (L₁ ++ (a, .write v) :: (b, .write w) :: L₂) →
    LegalG ρ σ (L₁ ++ (b, .write w) :: L₂) := by
  intro σ L₁ L₂
  induction L₁ generalizing σ with
  | nil => intro h; exact h.2
  | cons x L ih =>
    obtain ⟨c, o⟩ := x
    cases o with
    | read => intro h; exact ⟨h.1, ih h.2⟩
    | write u => intro h; exact ⟨h.1, ih h.2⟩

lemma fin_erase_ww {a b : ℕ} {v w : V} : ∀ (σ : V) (L₁ L₂ : List (ℕ × RWOp V)),
    fin σ (L₁ ++ (a, .write v) :: (b, .write w) :: L₂) = fin σ (L₁ ++ (b, .write w) :: L₂) := by
  intro σ L₁ L₂
  rw [fin_append, fin_append]; rfl

/-- Removing a read. -/
lemma LegalG.erase_r {ρ : ℕ → V → Prop} {a : ℕ} :
    ∀ {σ : V} {L₁ L₂ : List (ℕ × RWOp V)},
    LegalG ρ σ (L₁ ++ (a, .read) :: L₂) → LegalG ρ σ (L₁ ++ L₂) := by
  intro σ L₁ L₂
  induction L₁ generalizing σ with
  | nil => intro h; exact h.2
  | cons x L ih =>
    obtain ⟨c, o⟩ := x
    cases o with
    | read => intro h; exact ⟨h.1, ih h.2⟩
    | write u => intro h; exact ⟨h.1, ih h.2⟩

lemma fin_erase_r {a : ℕ} : ∀ (σ : V) (L₁ L₂ : List (ℕ × RWOp V)),
    fin σ (L₁ ++ (a, .read) :: L₂) = fin σ (L₁ ++ L₂) := by
  intro σ L₁ L₂
  rw [fin_append, fin_append]; rfl

/-! ### `rmId` -/

lemma rmId_of_not_mem {a : ℕ} {L : List (ℕ × RWOp V)} (h : a ∉ L.map Prod.fst) :
    rmId a L = L := by
  unfold rmId
  rw [List.filter_eq_self]
  intro x hx
  have : x.1 ≠ a := fun e => h (e ▸ List.mem_map_of_mem hx)
  simpa using this

lemma rmId_split {a : ℕ} {L₁ L₂ : List (ℕ × RWOp V)} {o : RWOp V}
    (hnd : ((L₁ ++ (a, o) :: L₂).map Prod.fst).Nodup) :
    rmId a (L₁ ++ (a, o) :: L₂) = L₁ ++ L₂ := by
  simp only [List.map_append, List.map_cons] at hnd
  have h1 : a ∉ L₁.map Prod.fst := by
    intro h; exact (List.nodup_append.1 hnd).2.2 _ h _ (by simp) rfl
  have h2 : a ∉ L₂.map Prod.fst := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  unfold rmId
  rw [List.filter_append, List.filter_cons]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
  rw [← rmId, ← rmId, rmId_of_not_mem h1, rmId_of_not_mem h2]

lemma mem_rmId {a : ℕ} {L : List (ℕ × RWOp V)} {x : ℕ × RWOp V} :
    x ∈ rmId a L ↔ x ∈ L ∧ x.1 ≠ a := by
  simp [rmId]

lemma mem_ids_rmId {a b : ℕ} {L : List (ℕ × RWOp V)} :
    b ∈ (rmId a L).map Prod.fst ↔ b ∈ L.map Prod.fst ∧ b ≠ a := by
  simp only [List.mem_map, mem_rmId]
  constructor
  · rintro ⟨x, ⟨hx, hxa⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hxa⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxa⟩; exact ⟨x, ⟨hx, hxa⟩, rfl⟩

lemma rmId_sublist (a : ℕ) (L : List (ℕ × RWOp V)) : (rmId a L).Sublist L :=
  List.filter_sublist

/-! ### `Good` -/

lemma Good.append {S : ℕ → Prop} : ∀ {L M : List (ℕ × RWOp V)}, Good S L → Good S M →
    Good S (L ++ M) := by
  intro L M
  induction L with
  | nil => intro _ h; exact h
  | cons x L ih =>
    intro h1 h2
    refine ⟨fun hs => ?_, ih h1.2 h2⟩
    obtain ⟨hw, hn⟩ := h1.1 hs
    refine ⟨hw, ?_⟩
    cases L with
    | nil => exact absurd hn id
    | cons y L => exact hn

lemma Good.mono {S S' : ℕ → Prop} : ∀ {L : List (ℕ × RWOp V)}, Good S L →
    (∀ x ∈ L, S' x.1 → S x.1) → Good S' L := by
  intro L
  induction L with
  | nil => intro _ _; trivial
  | cons x L ih =>
    intro h hS
    exact ⟨fun hs => h.1 (hS x (by simp) hs), ih h.2 fun y hy => hS y (by simp [hy])⟩

lemma Good.of_append {S : ℕ → Prop} : ∀ {L M : List (ℕ × RWOp V)}, Good S (L ++ M) →
    Good S M := by
  intro L M
  induction L with
  | nil => intro h; exact h
  | cons x L ih => intro h; exact ih h.2

lemma Good.split {S : ℕ → Prop} : ∀ {L₁ L₂ : List (ℕ × RWOp V)} {x : ℕ × RWOp V},
    Good S (L₁ ++ x :: L₂) → S x.1 → IsW x.2 ∧ NextW L₂ := by
  intro L₁ L₂ x
  induction L₁ with
  | nil => intro h hs; exact h.1 hs
  | cons y L ih => intro h hs; exact ih h.2 hs

/-- In a good list, an element in `S` is a write followed by a write. -/
lemma Good.decomp {S : ℕ → Prop} {L : List (ℕ × RWOp V)} (hg : Good S L) {x : ℕ × RWOp V}
    (hx : x ∈ L) (hs : S x.1) :
    ∃ L₁ L₂ v b w, L = L₁ ++ (x.1, .write v) :: (b, .write w) :: L₂ := by
  obtain ⟨L₁, L₂, rfl⟩ := List.mem_iff_append.1 hx
  obtain ⟨hw, hn⟩ := hg.split hs
  obtain ⟨a, o⟩ := x
  cases o with
  | read => exact absurd hw id
  | write v =>
    cases L₂ with
    | nil => exact absurd hn id
    | cons y L₂ =>
      obtain ⟨b, o'⟩ := y
      cases o' with
      | read => exact absurd hn id
      | write w => exact ⟨L₁, L₂, v, b, w, rfl⟩

lemma Good.erase_ww {S : ℕ → Prop} {a b : ℕ} {v w : V} :
    ∀ {L₁ L₂ : List (ℕ × RWOp V)},
    Good S (L₁ ++ (a, .write v) :: (b, .write w) :: L₂) → Good S (L₁ ++ (b, .write w) :: L₂) := by
  intro L₁ L₂
  induction L₁ with
  | nil => intro h; exact h.2
  | cons x L ih =>
    intro h
    refine ⟨fun hs => ?_, ih h.2⟩
    obtain ⟨hw, hn⟩ := h.1 hs
    refine ⟨hw, ?_⟩
    cases L with
    | nil => trivial
    | cons y L => exact hn

lemma Good.erase_r {S : ℕ → Prop} {a : ℕ} :
    ∀ {L₁ L₂ : List (ℕ × RWOp V)},
    Good S (L₁ ++ (a, .read) :: L₂) → Good S (L₁ ++ L₂) := by
  intro L₁ L₂
  induction L₁ with
  | nil => intro h; exact h.2
  | cons x L ih =>
    intro h
    refine ⟨fun hs => ?_, ih h.2⟩
    obtain ⟨hw, hn⟩ := h.1 hs
    refine ⟨hw, ?_⟩
    cases L with
    | nil => exact absurd hn id
    | cons y L => exact hn

/-- A list of writes, each in `S`, followed by a write. -/
lemma good_specs {S : ℕ → Prop} : ∀ (M : List (ℕ × RWOp V)) (a : ℕ) (v : V),
    (∀ x ∈ M, IsW x.2) → ¬ S a → Good S (M ++ [(a, .write v)]) := by
  intro M a v
  induction M with
  | nil => intro _ hs; exact ⟨fun h => absurd h hs, trivial⟩
  | cons x M ih =>
    intro hw hs
    refine ⟨fun _ => ⟨hw x (by simp), ?_⟩, ih (fun y hy => hw y (by simp [hy])) hs⟩
    cases M with
    | nil => trivial
    | cons y M => exact hw y (by simp)

/-! ### `DL` -/

variable {h : List (HEv P (RWOp V) V)} {ρ : ℕ → V → Prop} {σ : V} {L : List (ℕ × RWOp V)}

lemma DL.toDLin (v₀ : V) (hd : DL h ρ σ L) (hρ : ∀ a r c, HEv.res a (some r) c ∈ h → ρ a r) :
    DLin (register V v₀) h σ L where
  nodup := hd.nodup
  inv_of_mem := hd.inv_of_mem
  mem_of_res := hd.mem_of_res
  not_mem_of_fail := hd.not_mem_of_fail
  rt := hd.rt
  legal := by
    have key : ∀ (σ : V) (L : List (ℕ × RWOp V)), LegalG ρ σ L → Legal (register V v₀) h σ L := by
      intro σ L
      induction L generalizing σ with
      | nil => intro _; trivial
      | cons x L ih =>
        obtain ⟨a, o⟩ := x
        cases o with
        | read => intro hl; exact ⟨fun r c hr => by simpa using hl.1 r (hρ a r c hr), ih σ hl.2⟩
        | write v => intro hl; exact ⟨fun r c hr => by simpa using hl.1 r (hρ a r c hr), ih v hl.2⟩
    exact key σ L hd.legal

/-- Changing the committed responses. -/
lemma DL.weaken {ρ' : ℕ → V → Prop} (hd : DL h ρ σ L)
    (hρ : ∀ a r, ρ' a r → ρ a r ∨ ∀ x ∈ L, x.1 = a → x.2 = .write r) : DL h ρ' σ L :=
  { hd with legal := hd.legal.weaken hρ }

lemma res_of_prec {a b : ℕ} (hp : Prec h a b) : ∃ r c, HEv.res a r c ∈ h := by
  obtain ⟨h₁, h₂, rfl, ⟨r, c, hr⟩, -⟩ := hp
  exact ⟨r, c, List.mem_append_left _ hr⟩

/-- Appending events that contain no response and no invocation of a linearized operation. -/
lemma DL.append_noRes (hd : DL h ρ σ L) (δ : List (HEv P (RWOp V) V))
    (hδr : ∀ a r c, HEv.res a r c ∉ δ) (hδi : ∀ a q o, HEv.inv a q o ∈ δ → a ∉ L.map Prod.fst) :
    DL (h ++ δ) ρ σ L where
  nodup := hd.nodup
  inv_of_mem x hx := by
    obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, List.mem_append_left _ hp⟩
  mem_of_res a r c ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.mem_of_res a r c ha
    · exact absurd ha (hδr a _ c)
  not_mem_of_fail a c ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.not_mem_of_fail a c ha
    · exact absurd ha (hδr a _ c)
  rt := by
    refine hd.rt.imp_of_mem (fun {x y} hx _ hxy hp => hxy ?_)
    refine prec_append_of_ne (O := register V σ) ?_ hp ?_
    · intro c q o hc hcx
      exact hδi c q o hc (List.mem_map.2 ⟨x, hx, hcx.symm⟩)
    · obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, x.2, hp⟩
  legal := hd.legal

/-- Appending a response. -/
lemma DL.append_res (hd : DL h ρ σ L) (a : ℕ) (r : Option V) (c : Bool)
    (hL : a ∈ L.map Prod.fst ↔ r.isSome) : DL (h ++ [.res a r c]) ρ σ L where
  nodup := hd.nodup
  inv_of_mem x hx := by
    obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, List.mem_append_left _ hp⟩
  mem_of_res a' r' c' ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.mem_of_res a' r' c' ha
    · simp at ha; obtain ⟨rfl, rfl, rfl⟩ := ha; exact hL.2 rfl
  not_mem_of_fail a' c' ha := by
    rcases List.mem_append.1 ha with ha | ha
    · exact hd.not_mem_of_fail a' c' ha
    · simp at ha; obtain ⟨rfl, rfl, rfl⟩ := ha; intro h'; simpa using hL.1 h'
  rt := by
    refine hd.rt.imp_of_mem (fun {x y} hx _ hxy hp => hxy ?_)
    refine prec_append_of_ne (O := register V σ) (by simp) hp ?_
    obtain ⟨p, hp⟩ := hd.inv_of_mem x hx; exact ⟨p, x.2, hp⟩
  legal := hd.legal

/-- Removing a pending operation. -/
lemma DL.rm (hd : DL h ρ σ L) (a : ℕ) (hpend : ∀ r c, HEv.res a r c ∉ h)
    (hleg : LegalG ρ σ (rmId a L)) : DL h ρ σ (rmId a L) where
  nodup := (List.Sublist.map Prod.fst (rmId_sublist a L)).nodup hd.nodup
  inv_of_mem x hx := hd.inv_of_mem x (mem_rmId.1 hx).1
  mem_of_res b r c hb := by
    refine mem_ids_rmId.2 ⟨hd.mem_of_res b r c hb, ?_⟩
    rintro rfl; exact hpend _ _ hb
  not_mem_of_fail b c hb hm := hd.not_mem_of_fail b c hb (mem_ids_rmId.1 hm).1
  rt := hd.rt.sublist (rmId_sublist a L)
  legal := hleg

/-- Appending pending operations. -/
lemma DL.append_pending (hd : DL h ρ σ L) (M : List (ℕ × RWOp V))
    (hinv : ∀ x ∈ M, ∃ p, HEv.inv x.1 p x.2 ∈ h) (hpend : ∀ x ∈ M, ∀ r c, HEv.res x.1 r c ∉ h)
    (hnd : ((L ++ M).map Prod.fst).Nodup) (hleg : LegalG ρ σ (L ++ M)) : DL h ρ σ (L ++ M) where
  nodup := hnd
  inv_of_mem x hx := by
    rcases List.mem_append.1 hx with hx | hx
    · exact hd.inv_of_mem x hx
    · exact hinv x hx
  mem_of_res b r c hb := by
    simp only [List.map_append, List.mem_append]; exact .inl (hd.mem_of_res b r c hb)
  not_mem_of_fail b c hb hm := by
    simp only [List.map_append, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hd.not_mem_of_fail b c hb hm
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
      exact hpend x hx _ _ hb
  rt := by
    refine List.pairwise_append.2 ⟨hd.rt, ?_, ?_⟩
    · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
        (fun _ _ => trivial))
      intro x y _ hy _ hp
      obtain ⟨r, c, hr⟩ := res_of_prec hp
      exact hpend y hy r c hr
    · intro x _ y hy hp
      obtain ⟨r, c, hr⟩ := res_of_prec hp
      exact hpend y hy r c hr
  legal := hleg

end Alg1

end Papers.PODC2020.DetectableSpace
