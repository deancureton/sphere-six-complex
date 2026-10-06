module

public import DifferentialGeometry.Topology.SimplicialSet.ChainColimits
public import DifferentialGeometry.Topology.Homology.Algebra.PushoutExact
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
namespace DifferentialGeometry.SSet
variable {X : _root_.SSet.{u}} (A B : X.Subcomplex)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem unionChainSquare :
    IsPushout
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ B from inf_le_right)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show A ≤ A ⊔ B from le_sup_left)) R)
      (_root_.SSet.chainComplexMap (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) := by
  have sq : _root_.SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  exact ((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_isPushout sq.isPushout


abbrev unionChainShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  DifferentialGeometry.ShortComplex.pushoutShortComplex (unionChainSquare A B R)


theorem unionChainShortExact : (unionChainShortComplex A B R).ShortExact := by
  have : Mono (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R) := by
    unfold _root_.SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.ShortComplex.pushoutShortExact (unionChainSquare A B R)

def unionRelativeChainIso :
    cokernel (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R) ≅
    cokernel (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) := by
  let sq := unionChainSquare A B R
  have := isIso_cokernel_map_of_isPushout sq
  exact asIso (cokernel.map _ _ _ _ sq.w)


@[reassoc (attr := simp)]
theorem unionRelativeChainIso_projection :
    cokernel.π (_root_.SSet.chainComplexMap
      (_root_.SSet.Subcomplex.homOfLE (show A ⊓ B ≤ A from inf_le_left)) R) ≫
        (unionRelativeChainIso A B R).hom =
      _root_.SSet.chainComplexMap
        (_root_.SSet.Subcomplex.homOfLE (show A ≤ A ⊔ B from le_sup_left)) R ≫
      cokernel.π (_root_.SSet.chainComplexMap
        (_root_.SSet.Subcomplex.homOfLE (show B ≤ A ⊔ B from le_sup_right)) R) :=
  cokernel.π_desc _ _ _

end DifferentialGeometry.SSet
