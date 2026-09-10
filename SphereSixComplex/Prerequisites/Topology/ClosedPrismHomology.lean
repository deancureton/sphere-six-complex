module

public import SphereSixComplex.Prerequisites.Topology.ClosedHomotopyPrism
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

variable {C D : ChainComplex AddCommGrpCat ℕ} {f : C ⟶ D}
  (H : Homotopy f f) (n : ℕ)

public def closedPrismCycles : C.cycles (n + 1) ⟶ D.cycles (n + 2) :=
  D.liftCycles (C.iCycles (n + 1) ≫ H.hom (n + 1) (n + 2)) (n + 1) (by simp) (by
    rw [Category.assoc, closedHomotopyPrism_boundary, Preadditive.comp_neg,
      ← Category.assoc, iCycles_d, zero_comp, neg_zero])

public theorem closedPrismCycles_i :
    closedPrismCycles H n ≫ D.iCycles (n + 2) =
      C.iCycles (n + 1) ≫ H.hom (n + 1) (n + 2) :=
  D.liftCycles_i _ _ _ _

public theorem closedPrismCycles_boundary :
    C.toCycles (n + 2) (n + 1) ≫ closedPrismCycles H n =
      (-(H.hom (n + 2) (n + 3))) ≫ D.toCycles (n + 3) (n + 2) := by
  apply (cancel_mono (D.iCycles (n + 2))).mp
  rw [Category.assoc, closedPrismCycles_i, ← Category.assoc, toCycles_i,
    Category.assoc, toCycles_i, Preadditive.neg_comp]
  rw [closedHomotopyPrism_boundary H (n + 1), neg_neg]

public theorem closedPrismCycles_homology_boundary :
    C.toCycles (n + 2) (n + 1) ≫ closedPrismCycles H n ≫ D.homologyπ (n + 2) = 0 := by
  rw [← Category.assoc, closedPrismCycles_boundary, Category.assoc,
    toCycles_comp_homologyπ, comp_zero]

public def closedPrismHomology : C.homology (n + 1) ⟶ D.homology (n + 2) :=
  (C.homologyIsCokernel (n + 2) (n + 1) (by simp)).desc
    (CokernelCofork.ofπ (closedPrismCycles H n ≫ D.homologyπ (n + 2))
      (closedPrismCycles_homology_boundary H n))

public theorem closedPrismHomology_projection :
    C.homologyπ (n + 1) ≫ closedPrismHomology H n =
      closedPrismCycles H n ≫ D.homologyπ (n + 2) :=
  Cofork.IsColimit.π_desc (C.homologyIsCokernel (n + 2) (n + 1) (by simp))

public theorem closedPrism_cycle {A : AddCommGrpCat} (z : A ⟶ C.X (n + 1))
    (hz : z ≫ C.d (n + 1) n = 0) :
    (z ≫ H.hom (n + 1) (n + 2)) ≫ D.d (n + 2) (n + 1) = 0 := by
  rw [Category.assoc, closedHomotopyPrism_boundary, Preadditive.comp_neg,
    ← Category.assoc, hz, zero_comp, neg_zero]

public theorem closedPrismHomology_on_cycle {A : AddCommGrpCat} (z : A ⟶ C.X (n + 1))
    (hz : z ≫ C.d (n + 1) n = 0) :
    C.liftCycles z n (by simp) hz ≫ C.homologyπ (n + 1) ≫ closedPrismHomology H n =
      D.liftCycles (z ≫ H.hom (n + 1) (n + 2)) (n + 1) (by simp)
        (closedPrism_cycle H n z hz) ≫ D.homologyπ (n + 2) := by
  rw [closedPrismHomology_projection, ← Category.assoc]
  congr 1
  apply (cancel_mono (D.iCycles (n + 2))).mp
  simp only [Category.assoc, closedPrismCycles_i, liftCycles_i_assoc, liftCycles_i]

public theorem closedPrismHomology_naturality
    {C' D' : ChainComplex AddCommGrpCat ℕ} {g : C' ⟶ D'}
    (K : Homotopy g g) (u : C ⟶ C') (v : D ⟶ D')
    (h : ∀ p q, u.f p ≫ K.hom p q = H.hom p q ≫ v.f q) :
    homologyMap u (n + 1) ≫ closedPrismHomology K n =
      closedPrismHomology H n ≫ homologyMap v (n + 2) := by
  have hc : cyclesMap u (n + 1) ≫ closedPrismCycles K n =
      closedPrismCycles H n ≫ cyclesMap v (n + 2) := by
    apply (cancel_mono (D'.iCycles (n + 2))).mp
    rw [Category.assoc, closedPrismCycles_i, ← Category.assoc, cyclesMap_i,
      Category.assoc, h, ← Category.assoc, ← closedPrismCycles_i]
    simp only [Category.assoc, cyclesMap_i]
  apply (cancel_epi (C.homologyπ (n + 1))).mp
  rw [← Category.assoc, homologyπ_naturality, Category.assoc,
    closedPrismHomology_projection, ← Category.assoc, hc,
    Category.assoc, ← homologyπ_naturality, ← Category.assoc,
    ← closedPrismHomology_projection, Category.assoc]

end SphereSixComplex
