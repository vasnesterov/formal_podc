import Papers.PODC2022.InternetComputerConsensus.Model

/-!
# Basic lemmas: monotonicity of validity and certificates, chains
-/

namespace Podc.InternetComputerConsensus

open Finset Cslib.Byzantine

variable {P V : Type*}

theorem Valid.mono {pool pool' : Set (Msg P V)} (h : pool ⊆ pool') :
    ∀ {B : Block P V}, Valid pool B → Valid pool' B
  | .root, _ => trivial
  | .mk _ _ _ _, ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨h1, h h2, h h3, Valid.mono h h4, h5.imp id (fun x => h x)⟩

theorem Notarized.mono {pool pool' : Set (Msg P V)} (h : pool ⊆ pool') {B : Block P V}
    (hB : Notarized pool B) : Notarized pool' B :=
  ⟨hB.1.mono h, hB.2.imp id (fun x => h x)⟩

@[simp] theorem valid_root (pool : Set (Msg P V)) : Valid pool (.root : Block P V) := trivial

theorem notarized_root (pool : Set (Msg P V)) : Notarized pool (.root : Block P V) :=
  ⟨trivial, Or.inl rfl⟩

theorem valid_mk_iff {pool : Set (Msg P V)} {k : ℕ} {α : P} {par : Block P V} {pl : V} :
    Valid pool (.mk k α par pl) ↔
      par.round + 1 = k ∧ Msg.block (.mk k α par pl) ∈ pool ∧ Msg.auth (.mk k α par pl) ∈ pool ∧
        Valid pool par ∧ (par = .root ∨ Msg.notar par ∈ pool) := Iff.rfl

/-- A valid block of positive round is not the root, and its parent is notarized. -/
theorem Valid.parent_notarized {pool : Set (Msg P V)} {B : Block P V} (hB : Valid pool B)
    (h1 : 1 ≤ B.round) : Notarized pool B.parent ∧ B.parent.round + 1 = B.round := by
  cases B with
  | root => simp at h1
  | mk k α par pl => exact ⟨⟨hB.2.2.2.1, hB.2.2.2.2⟩, hB.1⟩

theorem Block.ne_root_of_round {B : Block P V} (h1 : 1 ≤ B.round) :
    B ≠ .root := by
  rintro rfl; simp at h1

/-- The chain of a valid block has one block per round. -/
theorem Valid.length_chain {pool : Set (Msg P V)} :
    ∀ {B : Block P V}, Valid pool B → B.chain.length = B.round
  | .root, _ => rfl
  | .mk k α par pl, ⟨h1, _, _, h4, _⟩ => by
      simp [Valid.length_chain h4, ← h1]

/-- Prefixes of the chain of a valid block are chains of its ancestors, which are notarized
(except for the block itself). -/
theorem Valid.chain_take {pool : Set (Msg P V)} :
    ∀ {B : Block P V}, Valid pool B → ∀ j ≤ B.round,
      ∃ A, A.round = j ∧ Valid pool A ∧ (A = B ∨ Notarized pool A) ∧ B.chain.take j = A.chain
  | .root, _, j, hj => ⟨.root, by simp only [Block.round_root] at hj ⊢; omega, trivial, Or.inl rfl, by simp⟩
  | .mk k α par pl, hB, j, hj => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hB
      simp only [Block.round_mk] at hj
      rcases Nat.lt_or_ge j k with hjk | hjk
      · obtain ⟨A, hA1, hA2, hA3, hA4⟩ := Valid.chain_take h4 j (by omega)
        refine ⟨A, hA1, hA2, ?_, ?_⟩
        · rcases hA3 with rfl | hA3
          · exact Or.inr ⟨h4, h5⟩
          · exact Or.inr hA3
        · rw [Block.chain_mk, List.take_append_of_le_length (by rw [Valid.length_chain h4]; omega),
            hA4]
      · refine ⟨.mk k α par pl, by simp; omega, ⟨h1, h2, h3, h4, h5⟩, Or.inl rfl, ?_⟩
        rw [List.take_of_length_le]
        simp [Valid.length_chain h4]; omega

variable [Fintype P] {π : Params P} {F : Finset P}

theorem NotarCert.mono {S S' : Set (Msg P V)} (h : S ⊆ S') {B : Block P V}
    (hB : NotarCert π F S B) : NotarCert π F S' B :=
  Certified.mono hB (fun _ hq => hq.imp id (fun x => h x)) le_rfl

theorem FinalCert.mono {S S' : Set (Msg P V)} (h : S ⊆ S') {B : Block P V}
    (hB : FinalCert π F S B) : FinalCert π F S' B :=
  Certified.mono hB (fun _ hq => hq.imp id (fun x => h x)) le_rfl

theorem Avail.mono {S S' : Set (Msg P V)} (h : S ⊆ S') :
    ∀ {m : Msg P V}, Avail π F S m → Avail π F S' m
  | .block _, _ => trivial
  | .auth _, hm => hm.imp id (fun x => h x)
  | .notar _, hm => hm.imp id (fun x => x.mono h)
  | .notarShare _ _, hm => hm.imp id (fun x => h x)
  | .final _, hm => FinalCert.mono h hm
  | .finalShare _ _, hm => hm.imp id (fun x => h x)
  | .beacon _ _, hm => hm.imp id (fun x => h x)

/-- A notarization in a pool of available messages is certified. -/
theorem notarCert_of_pool {S pool : Set (Msg P V)} (hp : ∀ m ∈ pool, Avail π F S m)
    {B : Block P V} (hB : B ≠ .root) (h : Msg.notar B ∈ pool ∨ NotarShares π pool B) :
    NotarCert π F S B := by
  rcases h with h | h
  · exact (hp _ h).resolve_left hB
  · exact Certified.mono h (fun q hq => hp _ hq) le_rfl

/-- A finalization in a pool of available messages is certified. -/
theorem finalCert_of_pool {S pool : Set (Msg P V)} (hp : ∀ m ∈ pool, Avail π F S m)
    {B : Block P V} (h : Msg.final B ∈ pool ∨ FinalShares π pool B) :
    FinalCert π F S B := by
  rcases h with h | h
  · exact hp _ h
  · exact Certified.mono h (fun q hq => hp _ hq) le_rfl

end Podc.InternetComputerConsensus
