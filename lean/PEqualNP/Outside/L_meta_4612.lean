import Mathlib.Data.List.Nodup
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4612

def Builds (available : List ℕ) (value : ℕ) : Prop :=
  ∃ a ∈ available, ∃ b ∈ available, value = a &&& b ∨ value = a ||| b

def Legal (inputs values : List ℕ) : Prop :=
  ∀ i : Fin values.length, Builds (inputs ++ values.take i.val) (values.get i)

lemma builds_of_subset {A B : List ℕ} {v : ℕ} (incl : ∀ a ∈ A, a ∈ B)
    (hv : Builds A v) : Builds B v := by
  obtain ⟨a, ha, b, hb, eq⟩ := hv
  exact ⟨a, incl a ha, b, incl b hb, eq⟩

lemma legal_snoc {A L : List ℕ} {v : ℕ} :
    Legal A (L ++ [v]) ↔ Legal A L ∧ Builds (A ++ L) v := by
  constructor
  · intro h
    constructor
    · intro i
      have hj : i.val < (L ++ [v]).length := by
        have := i.isLt
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [List.get_eq_getElem, List.getElem_append_left i.isLt,
        List.take_append_of_le_length i.isLt.le] using h ⟨i.val, hj⟩
    · simpa [List.get_eq_getElem] using h ⟨L.length, by simp⟩
  · rintro ⟨hL, hv⟩ i
    by_cases hi : i.val < L.length
    · simpa only [List.get_eq_getElem, List.getElem_append_left hi,
        List.take_append_of_le_length hi.le] using hL ⟨i.val, hi⟩
    · have ie : i = ⟨L.length, by simp⟩ := by
        apply Fin.ext
        change i.val = L.length
        have bound := i.isLt
        simp only [List.length_append, List.length_singleton] at bound
        omega
      subst i
      simpa [List.get_eq_getElem] using hv

lemma available_after {A F K V : List ℕ} (ports : ∀ a ∈ K, a ∈ A ++ F) :
    ∀ a ∈ K ++ V, a ∈ A ++ (F ++ V) := by
  intro a ha
  rw [← List.append_assoc]
  rcases List.mem_append.mp ha with h | h
  · exact List.mem_append_left _ (ports a h)
  · exact List.mem_append_right _ h

lemma concatenate {A F K V : List ℕ} (front : Legal A F)
    (ports : ∀ a ∈ K, a ∈ A ++ F) (back : Legal K V) : Legal A (F ++ V) := by
  induction V using List.reverseRecOn with
  | nil => simpa using front
  | append_singleton V v ih =>
    obtain ⟨hV, hv⟩ := legal_snoc.mp back
    rw [← List.append_assoc]
    exact legal_snoc.mpr ⟨ih hV, builds_of_subset (available_after ports) hv⟩

-- Keep a value only at its first appearance outside the original inputs.
lemma removeDuplicates (A L : List ℕ) (hL : Legal A L) :
    ∃ R : List ℕ, R.length ≤ L.length ∧ R.Nodup ∧ (∀ a ∈ R, a ∉ A) ∧
      Legal A R ∧ ∀ a ∈ A ++ L, a ∈ A ++ R := by
  induction L using List.reverseRecOn with
  | nil =>
    exact ⟨[], le_rfl, List.nodup_nil, by simp, hL, fun _ h => h⟩
  | append_singleton L v ih =>
    obtain ⟨hprev, hv⟩ := legal_snoc.mp hL
    obtain ⟨R, hlen, hn, hfresh, hR, hcover⟩ := ih hprev
    by_cases existing : v ∈ A ++ R
    · refine ⟨R, ?_, hn, hfresh, hR, ?_⟩
      · simpa only [List.length_append, List.length_singleton] using hlen.trans (Nat.le_succ _)
      · intro a ha
        rw [← List.append_assoc] at ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hcover a ha
        · obtain rfl := List.mem_singleton.mp ha
          exact existing
    · have notInA : v ∉ A := fun h => existing (List.mem_append_left R h)
      have notInR : v ∉ R := fun h => existing (List.mem_append_right A h)
      refine ⟨R ++ [v], by simpa only [List.length_append, List.length_singleton] using Nat.succ_le_succ hlen,
        List.Nodup.append hn (List.nodup_singleton v) (by simpa using notInR), ?_,
        legal_snoc.mpr ⟨hR, builds_of_subset hcover hv⟩, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hfresh a ha
        · obtain rfl := List.mem_singleton.mp ha
          exact notInA
      · intro a ha
        rw [← List.append_assoc] at ha ⊢
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (hcover a ha)
        · exact List.mem_append_right _ ha

end PEqualNP.Outside.L_meta_4612

open PEqualNP.Outside.L_meta_4612 in
theorem PEqualNP.Outside.L_meta_4612 :
    have x1 : List ℕ → List ℕ → Prop :=
      fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2,
        ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5;
    ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) →
      x1 x4 x5 → x6 ∈ x4 ++ x5 →
      ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧
         (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12 := by
  dsimp only
  intro A F K V t ht front ports back found
  change Legal A F at front
  change Legal K V at back
  obtain ⟨R, size, distinct, fresh, legal, cover⟩ :=
    removeDuplicates A (F ++ V) (concatenate front ports back)
  have target := cover t (available_after ports t found)
  refine ⟨R, by simpa only [List.length_append] using size, distinct, fresh, ?_, legal⟩
  exact (List.mem_append.mp target).resolve_left ht
