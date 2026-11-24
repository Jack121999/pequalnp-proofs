import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4457

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma wiresSplit (gs : List Gate) (xs : List Bool) :
    ∃ ys : List Bool, (Circuit.mk gs 0).wires xs = xs ++ ys ∧ ys.length = gs.length := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp [Circuit.wires], rfl⟩
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => xs.getD i false)
    obtain ⟨ys, hys, hlen⟩ := ih (xs ++ [value])
    refine ⟨value :: ys, ?_, ?_⟩
    · change (Circuit.mk gs 0).wires (xs ++ [value]) = xs ++ value :: ys
      simpa only [List.append_assoc, List.singleton_append] using hys
    · simp [hlen]

lemma inputValue {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

lemma appendInputOr {n k : ℕ} {f : (Fin n → Bool) → Bool} (i : Fin n)
    (h : HasCircuitSize n f k) : HasCircuitSize n (fun x => x i || f x) (k + 1) := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  let last : Gate := ⟨GateOp.or, [i.val, C.output]⟩
  let D : Circuit := ⟨C.gates ++ [last], n + C.size⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hfan g h
    · obtain rfl := List.mem_singleton.mp h
      simp [last]
  · simpa [Circuit.size, D] using hsize
  · intro x
    let xs := List.ofFn x
    let ws := C.wires xs
    obtain ⟨ys, hy, hlen⟩ := wiresSplit C.gates xs
    have shape : ws = xs ++ ys := hy
    have wireCount : ws.length = n + C.size := by
      rw [shape]
      simp [xs, hlen, Circuit.size]
    have atInput : ws.getD i.val false = x i := by
      rw [shape, List.getD_append _ _ _ _ (by simp [xs])]
      exact inputValue x i
    have atOutput : ws.getD C.output false = f x := heval x
    -- The extra gate reads the wire list before appending its own value.
    have wiring : D.wires xs = ws ++ [x i || f x] := by
      change (C.gates ++ [last]).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun u => w.getD u false)]) xs = _
      rw [List.foldl_append]
      change ws ++ [GateOp.or.eval [ws.getD i.val false, ws.getD C.output false]] = _
      rw [atInput, atOutput]
      simp [GateOp.eval]
    change (D.wires xs).getD (n + C.size) false = _
    rw [wiring, ← wireCount, List.getD_append_right _ _ _ _ le_rfl]
    simp

lemma decide_insert {n : ℕ} (s : Finset (Fin n)) (i : Fin n) (x : Fin n → Bool) :
    decide (∃ j ∈ insert i s, x j = true) = (x i || decide (∃ j ∈ s, x j = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨j, hj, hx⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hx
    · exact Or.inr ⟨j, hj, hx⟩
  · rintro (hi | ⟨j, hj, hx⟩)
    · exact ⟨i, Finset.mem_insert_self _ _, hi⟩
    · exact ⟨j, Finset.mem_insert_of_mem hj, hx⟩

end PEqualNP.Outside.L_meta_4457

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4457 in
theorem PEqualNP.Outside.L_meta_4457 :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : ℕ),
      PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x4 →
      PEqualNP.MetaComplexity.HasCircuitSize x1
        (fun (x6 : Fin x1 → Bool) => Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true) || x3 x6) (x4 + x2.card) := by
  intro n s f k hf
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | @insert i s hi ih =>
    have next := appendInputOr i ih
    simpa only [Finset.card_insert_of_notMem hi, Nat.add_assoc, decide_insert, Bool.or_assoc] using next
