module

public import DifferentialGeometry.Topology.Homology.SmallChains.Subspace
public import DifferentialGeometry.Topology.SimplicialSet.UnionChains

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s t : Set X)


def twoSetFamily : Bool → Set X := fun b => if b then s else t


theorem smallSingularSimplices_inter :
    smallSingularSimplices X (fun _ : Unit => s ∩ t) =
      smallSingularSimplices X (fun _ : Unit => s) ⊓
        smallSingularSimplices X (fun _ : Unit => t) := by
  ext n σ
  change (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s ∩ t) ↔
    ((∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s) ∧
      (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ t))
  simp only [exists_const, Set.subset_inter_iff]


theorem smallSingularSimplices_twoSet :
    smallSingularSimplices X (twoSetFamily X s t) =
      smallSingularSimplices X (fun _ : Unit => s) ⊔
        smallSingularSimplices X (fun _ : Unit => t) := by
  ext n σ
  change (∃ b : Bool, Set.range (X.toSSetObjEquiv n σ) ⊆ twoSetFamily X s t b) ↔
    ((∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s) ∨
      (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ t))
  simp only [exists_const, Bool.exists_bool, twoSetFamily, Bool.false_eq_true,
    ite_false, ite_true, or_comm]


def subspaceInclusion {s t : Set X} (h : s ⊆ t) : TopCat.of s ⟶ TopCat.of t :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩


def firstSubspaceToSmall : TopCat.toSSet.obj (TopCat.of s) ⟶
    (smallSingularSimplices X (twoSetFamily X s t) : SSet) :=
  (singularSubspaceIso X s).hom ≫ SSet.Subcomplex.homOfLE
    (smallSingularSimplices_le X (fun _ : Unit => s) (twoSetFamily X s t)
      (fun _ => ⟨true, Set.Subset.rfl⟩))


def secondSubspaceToSmall : TopCat.toSSet.obj (TopCat.of t) ⟶
    (smallSingularSimplices X (twoSetFamily X s t) : SSet) :=
  (singularSubspaceIso X t).hom ≫ SSet.Subcomplex.homOfLE
    (smallSingularSimplices_le X (fun _ : Unit => t) (twoSetFamily X s t)
      (fun _ => ⟨false, Set.Subset.rfl⟩))


@[reassoc (attr := simp)]
theorem firstSubspaceToSmall_ι :
    firstSubspaceToSmall X s t ≫ (smallSingularSimplices X (twoSetFamily X s t)).ι =
      TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := rfl


@[reassoc (attr := simp)]
theorem secondSubspaceToSmall_ι :
    secondSubspaceToSmall X s t ≫ (smallSingularSimplices X (twoSetFamily X s t)).ι =
      TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X))) := rfl


theorem subspaceSmallSquare :
    IsPushout (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)))
      (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right)))
      (firstSubspaceToSmall X s t) (secondSubspaceToSmall X s t) := by
  let A := smallSingularSimplices X (fun _ : Unit => s)
  let B := smallSingularSimplices X (fun _ : Unit => t)
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  apply sq.isPushout.of_iso'
    (singularSubspaceIso X (s ∩ t) ≪≫ SSet.Subcomplex.eqToIso (smallSingularSimplices_inter X s t))
    (singularSubspaceIso X s) (singularSubspaceIso X t)
    (SSet.Subcomplex.eqToIso (smallSingularSimplices_twoSet X s t))
  all_goals
    ext n σ
    apply Subtype.ext
    rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem subspaceSmallChainSquare :
    IsPushout
      (SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R)
      (SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R)
      (SSet.chainComplexMap (firstSubspaceToSmall X s t) R)
      (SSet.chainComplexMap (secondSubspaceToSmall X s t) R) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_isPushout (subspaceSmallSquare X s t)


abbrev subspaceSmallShortComplex : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  DifferentialGeometry.ShortComplex.pushoutShortComplex (subspaceSmallChainSquare X s t R)


theorem subspaceSmallShortExact : (subspaceSmallShortComplex X s t R).ShortExact := by
  have : Mono (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective (show s ∩ t ⊆ s from Set.inter_subset_left))
  have : Mono (SSet.chainComplexMap (TopCat.toSSet.map
      (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R) := by
    unfold SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.ShortComplex.pushoutShortExact (subspaceSmallChainSquare X s t R)

end DifferentialGeometry.Homology
