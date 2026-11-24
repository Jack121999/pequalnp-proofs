import Mathlib
import PEqualNP.Defs

-- Each entry of size at least two joins a point of its first part to a point of its second part.
-- These edges connect every entry contained in the target, and a connected graph on the target
-- has at least as many edges as vertices minus one.
theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro n L hL S hS
  classical
  rcases S.eq_empty_or_nonempty with hE | ⟨s0, hs0⟩
  · simp [hE]
  have hspec : ∀ j : Fin L.length, ∃ A B : Finset (Fin n), L.get j = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ L.take j) ∧ (B.card ≤ 1 ∨ B ∈ L.take j) :=
    fun j => hL j (L.get j) (by simp)
  choose A B hAB hA hB using hspec
  have hpick : ∀ P : Finset (Fin n), ∃ x : Fin n, P.Nonempty → x ∈ P := fun P =>
    if h : P.Nonempty then ⟨h.choose, fun _ => h.choose_spec⟩ else ⟨s0, fun h' => absurd h' h⟩
  choose pick hpick using hpick
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph {x // x ∈ S}, ∀ u v, G.Adj u v ↔ u ≠ v ∧
      ((∃ j : Fin L.length, (1 < (L.get j).card ∧ L.get j ⊆ S) ∧
          s(u.1, v.1) = s(pick (A j), pick (B j))) ∨
        (∃ j : Fin L.length, (1 < (L.get j).card ∧ L.get j ⊆ S) ∧
          s(v.1, u.1) = s(pick (A j), pick (B j)))) :=
    ⟨SimpleGraph.fromRel fun u v => ∃ j : Fin L.length, (1 < (L.get j).card ∧ L.get j ⊆ S) ∧
      s(u.1, v.1) = s(pick (A j), pick (B j)), fun _ _ => SimpleGraph.fromRel_adj _ _ _⟩
  let R : Fin n → Fin n → Prop := fun u v =>
    ∃ (hu : u ∈ S) (hv : v ∈ S), G.Reachable ⟨u, hu⟩ ⟨v, hv⟩
  have Rrefl : ∀ u ∈ S, R u u := fun u hu => ⟨hu, hu, SimpleGraph.Reachable.refl _⟩
  have Rtrans : ∀ u v w, R u v → R v w → R u w := fun _ _ _ ⟨hu, _, h1⟩ ⟨_, hw, h2⟩ =>
    ⟨hu, hw, h1.trans h2⟩
  have Rsymm : ∀ u v, R u v → R v u := fun _ _ ⟨hu, hv, h⟩ => ⟨hv, hu, h.symm⟩
  -- Every entry contained in the target has all its points mutually reachable.
  have key : ∀ k : ℕ, ∀ T : Finset (Fin n), L[k]? = some T → T ⊆ S → ∀ u ∈ T, ∀ v ∈ T, R u v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro T hT hTS u hu v hv
    obtain ⟨hk, hT'⟩ := List.getElem?_eq_some_iff.mp hT
    let j : Fin L.length := ⟨k, hk⟩
    have hTj : L.get j = T := by simp [j, hT']
    have hT2 : T = A j ∪ B j := hTj.symm.trans (hAB j)
    have hAT : A j ⊆ T := hT2 ▸ Finset.subset_union_left
    have hBT : B j ⊆ T := hT2 ▸ Finset.subset_union_right
    have part : ∀ P : Finset (Fin n), P ⊆ T → (P.card ≤ 1 ∨ P ∈ L.take k) →
        ∀ u ∈ P, ∀ v ∈ P, R u v := by
      intro P hPT hP u hu v hv
      rcases hP with hP | hP
      · obtain rfl : u = v := Finset.card_le_one.mp hP u hu v hv
        exact Rrefl u (hTS (hPT hu))
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hP
        rw [List.getElem?_take] at hi
        by_cases hik : i < k
        · simp only [hik, ite_true] at hi
          exact ih i hik P hi (hPT.trans hTS) u hu v hv
        · simp [hik] at hi
    have pA := part (A j) hAT (hA j)
    have pB := part (B j) hBT (hB j)
    have cross : ∀ u ∈ A j, ∀ v ∈ B j, R u v := by
      intro u hu v hv
      have haA := hpick (A j) ⟨u, hu⟩
      have hbB := hpick (B j) ⟨v, hv⟩
      refine Rtrans _ _ _ (pA u hu _ haA) (Rtrans _ _ _ ?_ (pB _ hbB v hv))
      have haS : pick (A j) ∈ S := hTS (hAT haA)
      have hbS : pick (B j) ∈ S := hTS (hBT hbB)
      by_cases hab : pick (A j) = pick (B j)
      · rw [hab]
        exact Rrefl _ hbS
      · refine ⟨haS, hbS, SimpleGraph.Adj.reachable ?_⟩
        rw [hG]
        refine ⟨fun h => hab (congrArg Subtype.val h), Or.inl ⟨j, ⟨?_, hTj ▸ hTS⟩, rfl⟩⟩
        rw [hAB j]
        exact Finset.one_lt_card.mpr ⟨_, Finset.mem_union_left _ haA, _,
          Finset.mem_union_right _ hbB, hab⟩
    rw [hT2] at hu hv
    rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
    · exact pA u hu v hv
    · exact cross u hu v hv
    · exact Rsymm _ _ (cross v hv u hu)
    · exact pB u hu v hv
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hS
  have hconn : G.Connected := by
    have : Nonempty {x // x ∈ S} := ⟨⟨s0, hs0⟩⟩
    refine ⟨fun u v => ?_⟩
    obtain ⟨_, _, h⟩ := key k S hk (Finset.Subset.refl S) u.1 u.2 v.1 v.2
    exact h
  -- Each edge comes from a counted entry, and different edges from different entries.
  have hedge : ∀ e : G.edgeSet, ∃ j : Fin L.length, (1 < (L.get j).card ∧ L.get j ⊆ S) ∧
      Sym2.map Subtype.val e.1 = s(pick (A j), pick (B j)) := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
    rw [SimpleGraph.mem_edgeSet, hG] at he
    rcases he.2 with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
    · exact ⟨j, hj, by rw [Sym2.map_mk]; exact he⟩
    · exact ⟨j, hj, by rw [Sym2.map_mk, Sym2.eq_swap]; exact he⟩
  choose f hf1 hf2 using hedge
  have hinj : Function.Injective (fun e : G.edgeSet =>
      (⟨f e, hf1 e⟩ : {j : Fin L.length // 1 < (L.get j).card ∧ L.get j ⊆ S})) := by
    intro e1 e2 h
    have h' : f e1 = f e2 := congrArg Subtype.val h
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    rw [hf2 e1, hf2 e2, h']
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have h2 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  rw [Nat.card_eq_fintype_card (α := {j : Fin L.length // _})] at h2
  omega
