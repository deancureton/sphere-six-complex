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

public theorem closedHomotopyPrism_boundary_element
    {C D : ChainComplex AddCommGrpCat ℕ} {f : C ⟶ D}
    (H : Homotopy f f) (n : ℕ) (c : C.X (n + 1)) :
    D.d (n + 2) (n + 1) (H.hom (n + 1) (n + 2) c) =
      -(H.hom n (n + 1) (C.d (n + 1) n c)) := by
  exact ConcreteCategory.congr_hom (closedHomotopyPrism_boundary H n) c

public theorem closedHomotopyPrism_preserves_boundaries
    {C D : ChainComplex AddCommGrpCat ℕ} {f : C ⟶ D}
    (H : Homotopy f f) (n : ℕ) (z : C.X n)
    (hz : ∃ c : C.X (n + 1), C.d (n + 1) n c = z) :
    ∃ b : D.X (n + 2), D.d (n + 2) (n + 1) b = H.hom n (n + 1) z := by
  obtain ⟨c, rfl⟩ := hz
  refine ⟨-(H.hom (n + 1) (n + 2) c), ?_⟩
  rw [map_neg, closedHomotopyPrism_boundary_element, neg_neg]

end SphereSixComplex
