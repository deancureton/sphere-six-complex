module

public import SphereSixComplex.Prerequisites.Topology.ClosedPrismHomology
public import Mathlib.Algebra.Homology.HomologySequence

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

public theorem closedPrism_relative_boundary_on_cycle
    (S T : ShortComplex (ChainComplex AddCommGrpCat ℕ)) (hT : T.ShortExact)
    {f₁ : S.X₁ ⟶ T.X₁} {f₂ : S.X₂ ⟶ T.X₂} {f₃ : S.X₃ ⟶ T.X₃}
    (H₁ : Homotopy f₁ f₁) (H₂ : Homotopy f₂ f₂) (H₃ : Homotopy f₃ f₃)
    (h₁ : ∀ p q, S.f.f p ≫ H₂.hom p q = H₁.hom p q ≫ T.f.f q)
    (h₂ : ∀ p q, S.g.f p ≫ H₃.hom p q = H₂.hom p q ≫ T.g.f q)
    (n : ℕ) {A : AddCommGrpCat}
    (z₃ : A ⟶ S.X₃.X (n + 2)) (hz₃ : z₃ ≫ S.X₃.d (n + 2) (n + 1) = 0)
    (z₂ : A ⟶ S.X₂.X (n + 2)) (hz₂ : z₂ ≫ S.g.f (n + 2) = z₃)
    (z₁ : A ⟶ S.X₁.X (n + 1)) (hz₁ : z₁ ≫ S.f.f (n + 1) = z₂ ≫ S.X₂.d (n + 2) (n + 1))
    (hz₁cycle : z₁ ≫ S.X₁.d (n + 1) n = 0) :
    S.X₃.liftCycles z₃ (n + 1) (by simp) hz₃ ≫ S.X₃.homologyπ (n + 2) ≫
      closedPrismHomology H₃ (n + 1) ≫ hT.δ (n + 3) (n + 2) rfl =
    -(S.X₁.liftCycles z₁ n (by simp) hz₁cycle ≫ S.X₁.homologyπ (n + 1) ≫
      closedPrismHomology H₁ n) := by
  have hlift : (z₂ ≫ H₂.hom (n + 2) (n + 3)) ≫ T.g.f (n + 3) =
      z₃ ≫ H₃.hom (n + 2) (n + 3) := by
    rw [Category.assoc, ← h₂, ← Category.assoc, hz₂]
  have hboundary : (-(z₁ ≫ H₁.hom (n + 1) (n + 2))) ≫ T.f.f (n + 2) =
      (z₂ ≫ H₂.hom (n + 2) (n + 3)) ≫ T.X₂.d (n + 3) (n + 2) := by
    rw [Preadditive.neg_comp, Category.assoc, ← h₁, ← Category.assoc, hz₁]
    rw [Category.assoc, Category.assoc, closedHomotopyPrism_boundary H₂ (n + 1),
      Preadditive.comp_neg]
  have hd := hT.δ_eq (n + 3) (n + 2) rfl
    (z₃ ≫ H₃.hom (n + 2) (n + 3)) (closedPrism_cycle H₃ (n + 1) z₃ hz₃)
    (z₂ ≫ H₂.hom (n + 2) (n + 3)) hlift
    (-(z₁ ≫ H₁.hom (n + 1) (n + 2))) hboundary (n + 1) (by simp)
  erw [reassoc_of% (closedPrismHomology_on_cycle H₃ (n + 1) z₃ hz₃)]
  rw [closedPrismHomology_on_cycle H₁ n z₁ hz₁cycle]
  erw [hd]
  have he (hz) : T.X₁.liftCycles (-(z₁ ≫ H₁.hom (n + 1) (n + 2))) (n + 1) (by simp) hz =
      -(T.X₁.liftCycles (z₁ ≫ H₁.hom (n + 1) (n + 2)) (n + 1) (by simp)
        (closedPrism_cycle H₁ n z₁ hz₁cycle)) := by
    apply (cancel_mono (T.X₁.iCycles (n + 2))).mp
    rw [liftCycles_i, Preadditive.neg_comp, liftCycles_i]
  rw [he, Preadditive.neg_comp]

end SphereSixComplex
