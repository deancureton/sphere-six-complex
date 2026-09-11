module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Category.Grp.Abelian

@[expose] public section
noncomputable section
open CategoryTheory HomologicalComplex
namespace SphereSixComplex

public theorem closedHomotopyPrism_boundary
    {C D : ChainComplex AddCommGrpCat ℕ} {f : C ⟶ D}
    (H : Homotopy f f) (n : ℕ) :
    H.hom (n + 1) (n + 2) ≫ D.d (n + 2) (n + 1) =
      -(C.d (n + 1) n ≫ H.hom n (n + 1)) := by
  have h := H.comm (n + 1)
  rw [dNext_eq _ (show ComplexShape.down ℕ |>.Rel (n + 1) n from rfl),
    prevD_eq _ (show ComplexShape.down ℕ |>.Rel (n + 2) (n + 1) from rfl)] at h
  exact eq_neg_of_add_eq_zero_right (add_right_cancel (h.symm.trans (zero_add _).symm))



end SphereSixComplex
