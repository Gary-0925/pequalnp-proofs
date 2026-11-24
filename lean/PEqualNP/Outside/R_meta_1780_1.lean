import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The merge identity reads wires only earlier than the gate. One step is the same
-- lower bound for a laid-out circuit; the other lays a monotone circuit out without
-- increasing its size.
theorem PEqualNP.Outside.R_meta_1780_1 :
    (∀ (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit),
      199 ≤ q → n = q ^ (2 : ℕ) + q + (1 : ℕ) →
      (∀ (x8 : Fin n), Fintype.card { x9 : Fin n // R x9 x8 } = q + (1 : ℕ)) →
      (∀ (x9 x10 : Fin n), x9 ≠ x10 → ∃! x12 : Fin n, R x9 x12 ∧ R x10 x12) →
      Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) C →
      (∀ (x11 x12 : Fin n), R x11 x12 → circuitFun (n + n) C
        (fun (x14 : Fin (n + n)) => decide (x14 = Fin.castAdd n x11 ∨ x14 = Fin.natAdd n x12)) = Bool.true) →
      (∀ (x12 : Fin (n + n) → Bool),
        (¬∃ (x13 : Fin n) (x14 : Fin n), R x13 x14 ∧ x12 (Fin.castAdd n x13) = Bool.true ∧
          x12 (Fin.natAdd n x14) = Bool.true) → circuitFun (n + n) C x12 = Bool.false) →
      n * q ≤ (100 : ℕ) * C.size) →
    (∀ (N : ℕ) (C : Circuit), Monotone2 C →
      ∃ D : Circuit, Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N D ∧
        D.size ≤ C.size ∧ circuitFun N D = circuitFun N C) →
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro laidOut normalize q n R _ C hq hn hlines hpairs hmono hpos hneg
  obtain ⟨D, hDmono, hDread, hDsize, hDfun⟩ := normalize (n + n) C hmono
  have hDpos : ∀ (p w : Fin n), R p w →
      circuitFun (n + n) D
        (fun (k : Fin (n + n)) => decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n w)) = Bool.true := by
    intro p w hpw
    rw [hDfun]
    exact hpos p w hpw
  have hDneg : ∀ (z : Fin (n + n) → Bool),
      (¬∃ (p w : Fin n), R p w ∧ z (Fin.castAdd n p) = Bool.true ∧
        z (Fin.natAdd n w) = Bool.true) → circuitFun (n + n) D z = Bool.false := by
    intro z hz
    rw [hDfun]
    exact hneg z hz
  have hmain := laidOut q n R D hq hn hlines hpairs hDmono hDread hDpos hDneg
  exact hmain.trans (Nat.mul_le_mul_left 100 hDsize)
