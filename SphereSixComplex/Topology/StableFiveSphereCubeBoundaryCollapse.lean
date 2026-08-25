module

public import SphereSixComplex.Topology.HomotopyGroupSphereRepresentative
public import SphereSixComplex.Topology.DiskBoundaryQuotient
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The five-cube with its boundary collapsed is the clutching five-sphere

This file constructs the geometric input required to compare Mathlib's cube-based `π₅` with
the representative clutching maps used in the stable-framing argument.  The complement of the
boundary of `I⁵` is identified with `(0,1)⁵`, then with `ℝ⁵` coordinatewise by the sigmoid
homeomorphism.  One-point compactification gives the concrete unit sphere in Euclidean `ℝ⁶`.

The resulting map from the cube is continuous, collapses exactly the boundary, and is a quotient
map.  It therefore supplies the `StableFiveSphereCubeBoundaryCollapseModel` required by the
homotopy-group comparison.
-/

@[expose] public section

noncomputable section

open ContinuousMap Function Set Topology
open Topology.Homotopy
open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

public abbrev CubeFive := I^(Fin 5)
public abbrev CubeFiveBoundary := {x : CubeFive // x ∈ Cube.boundary (Fin 5)}
public abbrev CubeFiveIntervalInterior := Set.Ioo (0 : unitInterval) 1

/-- Inclusion of the topological boundary of the five-cube. -/
public def cubeFiveBoundaryInclusion :
    TopCat.of CubeFiveBoundary ⟶ TopCat.of CubeFive :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The all-zero vertex, used only to choose the collapsed quotient point. -/
public def cubeFiveBoundaryBasepoint : CubeFiveBoundary :=
  ⟨fun _ ↦ 0, ⟨0, Or.inl rfl⟩⟩

public theorem cubeFive_not_boundaryRange_iff_interior (x : CubeFive) :
    x ∉ Set.range cubeFiveBoundaryInclusion ↔
      ∀ i : Fin 5, x i ∈ Set.Ioo (0 : unitInterval) 1 := by
  constructor
  · intro hx i
    have hneZero : x i ≠ 0 := by
      intro hi
      apply hx
      exact ⟨⟨x, ⟨i, Or.inl hi⟩⟩, rfl⟩
    have hneOne : x i ≠ 1 := by
      intro hi
      apply hx
      exact ⟨⟨x, ⟨i, Or.inr hi⟩⟩, rfl⟩
    exact ⟨lt_of_le_of_ne (x i).property.1 (Ne.symm hneZero),
      lt_of_le_of_ne (x i).property.2 hneOne⟩
  · intro hx hrange
    obtain ⟨y, hy⟩ := hrange
    subst x
    obtain ⟨i, hi | hi⟩ := y.property
    · exact (hx i).1.ne' hi
    · exact (hx i).2.ne hi

/-- The complement of the collapsed boundary is open in the cube. -/
public theorem cubeFiveCollapseComplement_isOpen :
    IsOpen {x : CubeFive | x ∉ Set.range cubeFiveBoundaryInclusion} := by
  have hset : {x : CubeFive | x ∉ Set.range cubeFiveBoundaryInclusion} =
      Set.pi Set.univ (fun _ : Fin 5 ↦ Set.Ioo (0 : unitInterval) 1) := by
    ext x
    rw [Set.mem_ofPred_eq, cubeFive_not_boundaryRange_iff_interior, Set.mem_pi]
    simp
  rw [hset]
  exact isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)

/-- The sigmoid embedding, restricted to its exact range, is a homeomorphism
`ℝ ≅ (0,1) ⊆ I`. -/
public noncomputable def realHomeomorphIntervalInterior :
    ℝ ≃ₜ CubeFiveIntervalInterior :=
  Topology.isEmbedding_sigmoid.toHomeomorph |>.trans
    (Homeomorph.setCongr unitInterval.range_sigmoid)

/-- Coordinatewise sigmoid gives `ℝ⁵ ≅ (0,1)⁵`. -/
public noncomputable def realFiveHomeomorphPiIntervalInterior :
    (Fin 5 → ℝ) ≃ₜ (Fin 5 → CubeFiveIntervalInterior) :=
  Homeomorph.piCongrRight (fun _ ↦ realHomeomorphIntervalInterior)

/-- The open cube, expressed as the complement of the boundary image, is homeomorphic to the
Pi-type of its coordinate interiors. -/
public noncomputable def cubeFiveComplementHomeomorphPiInterior :
    CollapseComplement cubeFiveBoundaryInclusion ≃ₜ
      (Fin 5 → CubeFiveIntervalInterior) where
  toFun x i := ⟨x.1 i, (cubeFive_not_boundaryRange_iff_interior x.1).mp x.2 i⟩
  invFun y := ⟨fun i ↦ y i,
    (cubeFive_not_boundaryRange_iff_interior (fun i ↦ y i)).mpr (fun i ↦ (y i).2)⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    funext i
    apply Subtype.ext
    rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (continuous_apply i).comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    exact continuous_subtype_val.comp (continuous_apply i)

/-- The open five-cube is homeomorphic to `ℝ⁵`. -/
public noncomputable def cubeFiveComplementHomeomorphRealFive :
    CollapseComplement cubeFiveBoundaryInclusion ≃ₜ (Fin 5 → ℝ) :=
  cubeFiveComplementHomeomorphPiInterior.trans
    realFiveHomeomorphPiIntervalInterior.symm

/-- The one-point compactification of the open five-cube is the clutching five-sphere. -/
public noncomputable def onePointCubeFiveComplementHomeomorphSphere :
    OnePoint (CollapseComplement cubeFiveBoundaryInclusion) ≃ₜ
      StableClutchingEquatorFiveSphere :=
  cubeFiveComplementHomeomorphRealFive.onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (V := Fin 5 → ℝ) (by simp))

/-- The prequotient collapse map from the cube to the sphere.  Every boundary point goes to the
point at infinity. -/
public noncomputable def cubeFiveBoundaryCollapseToSphere :
    C(CubeFive, StableClutchingEquatorFiveSphere) where
  toFun x := onePointCubeFiveComplementHomeomorphSphere
    (collapseToOnePointComplement cubeFiveBoundaryInclusion x)
  continuous_toFun :=
    onePointCubeFiveComplementHomeomorphSphere.continuous.comp
      (continuous_collapseToOnePointComplement cubeFiveBoundaryInclusion
        cubeFiveCollapseComplement_isOpen)

/-- The point on the clutching sphere obtained by collapsing the cube boundary. -/
public noncomputable def stableFiveSphereCubeBoundaryCollapsedBase :
    StableClutchingEquatorFiveSphere :=
  onePointCubeFiveComplementHomeomorphSphere OnePoint.infty

/-- The point-set equivalence from the literal boundary-collapse quotient to the five-sphere. -/
public noncomputable def cubeFiveBoundaryQuotientEquivSphere :
    CollapseQuotient cubeFiveBoundaryInclusion ≃ StableClutchingEquatorFiveSphere :=
  (collapseQuotientEquivOnePointComplement cubeFiveBoundaryInclusion
      cubeFiveBoundaryBasepoint).trans
    onePointCubeFiveComplementHomeomorphSphere.toEquiv

public theorem continuous_cubeFiveBoundaryQuotientEquivSphere :
    Continuous cubeFiveBoundaryQuotientEquivSphere := by
  apply onePointCubeFiveComplementHomeomorphSphere.continuous.comp
  rw [isQuotientMap_quotient_mk'.continuous_iff]
  have hfun :
      (collapseQuotientEquivOnePointComplement cubeFiveBoundaryInclusion
          cubeFiveBoundaryBasepoint) ∘
          (@Quotient.mk' CubeFive (collapseSetoid cubeFiveBoundaryInclusion)) =
        collapseToOnePointComplement cubeFiveBoundaryInclusion := by
    funext x
    rfl
  rw [hfun]
  exact continuous_collapseToOnePointComplement cubeFiveBoundaryInclusion
    cubeFiveCollapseComplement_isOpen

/-- The literal quotient `I⁵/∂I⁵` is homeomorphic to the unit sphere in Euclidean `ℝ⁶`. -/
public noncomputable def cubeFiveBoundaryQuotientHomeomorphSphere :
    CollapseQuotient cubeFiveBoundaryInclusion ≃ₜ
      StableClutchingEquatorFiveSphere :=
  continuous_cubeFiveBoundaryQuotientEquivSphere.homeoOfEquivCompactToT2

public theorem cubeFiveBoundaryCollapseToSphere_boundary
    (x : CubeFive) (hx : x ∈ Cube.boundary (Fin 5)) :
    cubeFiveBoundaryCollapseToSphere x =
      stableFiveSphereCubeBoundaryCollapsedBase := by
  change onePointCubeFiveComplementHomeomorphSphere
      (collapseToOnePointComplement cubeFiveBoundaryInclusion x) =
    onePointCubeFiveComplementHomeomorphSphere OnePoint.infty
  congr 1
  apply collapseToOnePointComplement_of_mem
  exact ⟨⟨x, hx⟩, rfl⟩

public theorem cubeFiveBoundaryCollapseToSphere_surjective :
    Function.Surjective cubeFiveBoundaryCollapseToSphere := by
  intro s
  obtain ⟨p, rfl⟩ := onePointCubeFiveComplementHomeomorphSphere.surjective s
  induction p using OnePoint.rec with
  | infty =>
      refine ⟨cubeFiveBoundaryBasepoint.1, ?_⟩
      change onePointCubeFiveComplementHomeomorphSphere
          (collapseToOnePointComplement cubeFiveBoundaryInclusion
            cubeFiveBoundaryBasepoint.1) =
        onePointCubeFiveComplementHomeomorphSphere OnePoint.infty
      congr 1
      apply collapseToOnePointComplement_of_mem
      exact ⟨cubeFiveBoundaryBasepoint, rfl⟩
  | coe z =>
      refine ⟨z.1, ?_⟩
      change onePointCubeFiveComplementHomeomorphSphere
          (collapseToOnePointComplement cubeFiveBoundaryInclusion z.1) =
        onePointCubeFiveComplementHomeomorphSphere (↑z)
      congr 1
      exact collapseToOnePointComplement_of_notMem cubeFiveBoundaryInclusion z.2

/-- Compact-to-Hausdorff makes the explicit cube collapse a quotient map. -/
public theorem cubeFiveBoundaryCollapseToSphere_isQuotientMap :
    IsQuotientMap cubeFiveBoundaryCollapseToSphere :=
  IsQuotientMap.of_surjective_continuous
    cubeFiveBoundaryCollapseToSphere_surjective
    cubeFiveBoundaryCollapseToSphere.continuous

public theorem cubeFiveBoundaryCollapseToSphere_fiber
    (a b : CubeFive) (hab : cubeFiveBoundaryCollapseToSphere a =
      cubeFiveBoundaryCollapseToSphere b) :
    a = b ∨ (a ∈ Cube.boundary (Fin 5) ∧ b ∈ Cube.boundary (Fin 5)) := by
  have hcollapse :
      collapseToOnePointComplement cubeFiveBoundaryInclusion a =
        collapseToOnePointComplement cubeFiveBoundaryInclusion b :=
    onePointCubeFiveComplementHomeomorphSphere.injective hab
  have hquotient :
      (@Quotient.mk' CubeFive (collapseSetoid cubeFiveBoundaryInclusion) a) =
        @Quotient.mk' CubeFive (collapseSetoid cubeFiveBoundaryInclusion) b := by
    apply (collapseQuotientEquivOnePointComplement cubeFiveBoundaryInclusion
      cubeFiveBoundaryBasepoint).injective
    change collapseToOnePointComplement cubeFiveBoundaryInclusion a =
      collapseToOnePointComplement cubeFiveBoundaryInclusion b
    exact hcollapse
  rcases Quotient.exact hquotient with hab | ⟨ha, hb⟩
  · exact Or.inl hab
  · right
    constructor
    · obtain ⟨x, rfl⟩ := ha
      exact x.property
    · obtain ⟨x, rfl⟩ := hb
      exact x.property

/-- A fully constructed cube-boundary collapse model for the clutching five-sphere. -/
public noncomputable def stableFiveSphereCubeBoundaryCollapseModel :
    StableFiveSphereCubeBoundaryCollapseModel
      stableFiveSphereCubeBoundaryCollapsedBase where
  quotient := cubeFiveBoundaryCollapseToSphere
  boundary := cubeFiveBoundaryCollapseToSphere_boundary
  fiber := cubeFiveBoundaryCollapseToSphere_fiber
  isQuotientMap := cubeFiveBoundaryCollapseToSphere_isQuotientMap

/-- The cube-based statement `π₅(SO(7)) = 0` now implies the exact representative-level
clutching-map vanishing proposition, with no remaining sphere-model hypothesis. -/
public theorem specialOrthogonalSevenFiveSphereNullhomotopyVanishing_of_piFive_constructive
    [Subsingleton (HomotopyGroup.Pi 5 StableSpecialOrthogonalSeven
      (1 : StableSpecialOrthogonalSeven))] :
    SpecialOrthogonalSevenFiveSphereNullhomotopyVanishing :=
  specialOrthogonalSevenFiveSphereNullhomotopyVanishing_of_piFive
    stableFiveSphereCubeBoundaryCollapsedBase
    stableFiveSphereCubeBoundaryCollapseModel

/-- Buffered radial clutching geometry and cube-based `π₅(SO(7)) = 0` imply the original
rank-seven hemispherical clutching theorem. -/
public theorem
    homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_buffered_and_piFive
    [Subsingleton (HomotopyGroup.Pi 5 StableSpecialOrthogonalSeven
      (1 : StableSpecialOrthogonalSeven))]
    (hgeometry : HomotopySixSphereBufferedRadialRankSevenClutchingPresentation) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing :=
  homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_buffered_and_specialOrthogonal
    hgeometry specialOrthogonalSevenFiveSphereNullhomotopyVanishing_of_piFive_constructive

end SphereSixComplex
