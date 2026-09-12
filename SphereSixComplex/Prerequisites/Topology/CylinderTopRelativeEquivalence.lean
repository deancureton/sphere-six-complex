module

public import SphereSixComplex.Prerequisites.Topology.RelativeSingularHomotopy
public import SphereSixComplex.Prerequisites.Topology.CylinderUpperNeighborhood

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SphereSixComplex

public def cylinderUpperSide {X : Type} (A : Set X) :=
  {p : cylinderUpperNeighborhood A | p.1.1 ∈ cylinderLowerSide A}

public def cylinderUpperSideInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of (cylinderUpperSide A) ⟶ TopCat.of (cylinderUpperNeighborhood A) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public def cylinderBaseInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

public instance mono_cylinderBaseInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (cylinderBaseInclusion A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public instance cylinderUpperSideInclusion_mono {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (cylinderUpperSideInclusion A) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

public def cylinderTopUpperPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderBaseInclusion A) (cylinderUpperSideInclusion A) where
  left := TopCat.ofHom ⟨fun x ↦ ⟨cylinderTopToUpper A x.1, Or.inr x.2⟩,
    ((cylinderTopToUpper A).continuous.comp continuous_subtype_val).subtype_mk _⟩
  right := TopCat.ofHom (cylinderTopToUpper A)
  comm := rfl

public def cylinderUpperTopPair {X : Type} [TopologicalSpace X] (A : Set X) :
    CWTopologicalPairMap (cylinderUpperSideInclusion A) (cylinderBaseInclusion A) where
  left := TopCat.ofHom ⟨fun p ↦ ⟨p.1.1.1.2,
    (cylinderUpperNeighborhood_mem_lowerSide_iff A p.1).mp p.2⟩,
    ((cylinderUpperRetraction A).continuous.comp continuous_subtype_val).subtype_mk _⟩
  right := TopCat.ofHom (cylinderUpperRetraction A)
  comm := rfl

public def cylinderUpperSideHomotopy {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.Homotopy (𝟙 (TopCat.of (cylinderUpperSide A)))
      ((cylinderUpperTopPair A).left ≫ (cylinderTopUpperPair A).left) where
  toFun p := ⟨cylinderUpperHomotopy A (p.1, p.2.1),
    cylinderUpperHomotopy_preserves_lowerSide A p.1 p.2.1 p.2.2⟩
  continuous_toFun := ((cylinderUpperHomotopy A).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left p := by apply Subtype.ext; exact (cylinderUpperHomotopy A).map_zero_left _
  map_one_left p := by apply Subtype.ext; exact (cylinderUpperHomotopy A).map_one_left _

public def cylinderTopUpperRelativeEquivalence {X : Type} [TopologicalSpace X] (A : Set X) :
    HomotopyEquiv (cwRelativeIntegralSingularChainComplex (cylinderBaseInclusion A))
      (cwRelativeIntegralSingularChainComplex (cylinderUpperSideInclusion A)) where
  hom := cwRelativeIntegralSingularChainMapOfPair (cylinderTopUpperPair A)
  inv := cwRelativeIntegralSingularChainMapOfPair (cylinderUpperTopPair A)
  homotopyHomInvId := Homotopy.ofEq (by
    rw [← cwRelativeIntegralSingularChainMapOfPair_comp]
    exact cwRelativeIntegralSingularChainMapOfPair_id _)
  homotopyInvHomId := by
    let f : CWTopologicalPairMap (cylinderUpperSideInclusion A) (cylinderUpperSideInclusion A) :=
      ⟨𝟙 _, 𝟙 _, by simp⟩
    let g : CWTopologicalPairMap (cylinderUpperSideInclusion A) (cylinderUpperSideInclusion A) :=
      ⟨(cylinderUpperTopPair A).left ≫ (cylinderTopUpperPair A).left,
        (cylinderUpperTopPair A).right ≫ (cylinderTopUpperPair A).right, rfl⟩
    have H := cwRelativeSingularHomotopy (f := f) (g := g)
      (cylinderUpperSideHomotopy A) (cylinderUpperHomotopy A) (by ext p <;> rfl)
    have hf : cwRelativeIntegralSingularChainMapOfPair f = 𝟙 _ :=
      cwRelativeIntegralSingularChainMapOfPair_id _
    have hg : cwRelativeIntegralSingularChainMapOfPair g =
      cwRelativeIntegralSingularChainMapOfPair (cylinderUpperTopPair A) ≫
        cwRelativeIntegralSingularChainMapOfPair (cylinderTopUpperPair A) :=
      cwRelativeIntegralSingularChainMapOfPair_comp _ _
    rw [hf, hg] at H
    exact H.symm

end SphereSixComplex
