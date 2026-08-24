module

public import SphereSixComplex.Geometry.CompactTorusFamilyOverBase
public import SphereSixComplex.Geometry.PaperEllipticCentralEscape
public import SphereSixComplex.Geometry.PaperFillingCompactCores

/-!
# A compact core for the paper's central family

The exact Fuchsian quotient coordinate identifies the regular base quotient with the twice
punctured affine line.  Compact subsets of that affine base have compact sets of representatives
upstairs.  Taking one real period cube over those representatives and projecting to the central
family gives a compact total-space core.

The final input is deliberately stated as a proposition, not an axiom: a compact coordinate core
whose complement is covered by the three already selected collar images.  Its existence is
paper-specific end-control work, not a generic consequence of cofinite-orbifold topology.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex Geometry
open ComplexTorus AnalyticTorusFamily TorusFamily GlobalTorusFamily
open EllipticWholeFiberCompactCover
open EllipticLinearCollarGlobalDescent

noncomputable section

namespace PaperAnalyticData

variable (P : PaperAnalyticData)

/-- The affine quotient coordinate with the two elliptic values removed. -/
public abbrev RegularCoordinateBase := ({0, 1} : Set ℂ)ᶜ

public theorem isRegularBasePoint_iff_coordinate_mem
    (z : UpperHalfPlane) :
    GlobalTorusFamily.IsRegularBasePoint
        (U := P.modular.modularParameter.toTriangleUniformization) z ↔
      P.modular.sourceCoordinate.coordinate z ∈ ({0, 1} : Set ℂ)ᶜ := by
  rw [isRegularBasePoint_iff_not_mem_orbits]
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · intro hz
    constructor
    · intro hzero
      have horbit :=
        (P.modular.sourceCoordinate.coordinate_eq_iff_orbit z fuchsianOneFixedPoint).mp
          (hzero.trans P.modular.sourceCoordinate.coordinate_at_one.symm)
      obtain ⟨g, hg⟩ := horbit
      apply hz
      left
      simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [P.modular.modularParameter.toTriangleUniformization_sourceAction]
      change z = fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint
      calc
        z = fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
        _ = fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint := congrArg _ hg
    · intro hone
      have horbit :=
        (P.modular.sourceCoordinate.coordinate_eq_iff_orbit z fuchsianTwoFixedPoint).mp
          (hone.trans P.modular.sourceCoordinate.coordinate_at_two.symm)
      obtain ⟨g, hg⟩ := horbit
      apply hz
      right
      simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff]
      refine ⟨g⁻¹, ?_⟩
      rw [P.modular.modularParameter.toTriangleUniformization_sourceAction]
      change z = fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint
      calc
        z = fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
        _ = fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint := congrArg _ hg
  · rintro ⟨hzero, hone⟩ hz
    rcases hz with hz | hz
    · apply hzero
      simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨g, rfl⟩ := hz
      change P.modular.sourceCoordinate.coordinate
        (fuchsianSourceAction g • fuchsianOneFixedPoint) = 0
      rw [P.modular.sourceCoordinate.coordinate_invariant,
        P.modular.sourceCoordinate.coordinate_at_one]
    · apply hone
      simp only [sourceOrbitSet, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨g, rfl⟩ := hz
      change P.modular.sourceCoordinate.coordinate
        (fuchsianSourceAction g • fuchsianTwoFixedPoint) = 1
      rw [P.modular.sourceCoordinate.coordinate_invariant,
        P.modular.sourceCoordinate.coordinate_at_two]

/-- The exact quotient coordinate restricted to the regular base. -/
@[expose] public noncomputable def regularCoordinate :
    RegularBase (U := P.modular.modularParameter.toTriangleUniformization) →
      RegularCoordinateBase :=
  fun z ↦ ⟨P.modular.sourceCoordinate.coordinate z.1,
    (P.isRegularBasePoint_iff_coordinate_mem z.1).mp z.2⟩

/-- The regular base is the coordinate preimage of the twice punctured affine line. -/
@[expose] public noncomputable def regularBaseCoordinatePreimageHomeomorph :
    RegularBase (U := P.modular.modularParameter.toTriangleUniformization) ≃ₜ
      P.modular.sourceCoordinate.coordinate ⁻¹' ({0, 1} : Set ℂ)ᶜ where
  toFun z := ⟨z.1, (P.isRegularBasePoint_iff_coordinate_mem z.1).mp z.2⟩
  invFun z := ⟨z.1, (P.isRegularBasePoint_iff_coordinate_mem z.1).mpr z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

public theorem regularCoordinate_isLocalHomeomorph :
    IsLocalHomeomorph P.regularCoordinate := by
  let e := P.regularBaseCoordinatePreimageHomeomorph
  let f := ({0, 1} : Set ℂ)ᶜ.restrictPreimage
    P.modular.sourceCoordinate.coordinate
  have hf : IsLocalHomeomorph f :=
    P.modular.sourceCoordinate.regular_covering.isCoveringMap_restrictPreimage.isLocalHomeomorph
  have he : IsLocalHomeomorph e := e.isLocalHomeomorph
  have hcomp : IsLocalHomeomorph (f ∘ e) := hf.comp he
  convert hcomp using 1
  rfl

public theorem regularCoordinate_surjective :
    Function.Surjective P.regularCoordinate := by
  intro w
  obtain ⟨z, hz⟩ := P.modular.sourceCoordinate.coordinate_isQuotientMap.surjective w.1
  have hzregular : IsRegularBasePoint
      (U := P.modular.modularParameter.toTriangleUniformization) z :=
    (P.isRegularBasePoint_iff_coordinate_mem z).mpr (hz ▸ w.2)
  exact ⟨⟨z, hzregular⟩, Subtype.ext hz⟩

/-- Compact coordinate sets admit compact sets of regular upper-half-plane representatives. -/
public theorem regularCoordinate_compact_has_compactRepresentatives
    (K : Set RegularCoordinateBase) (hK : IsCompact K) :
    ∃ L : Set (RegularBase
        (U := P.modular.modularParameter.toTriangleUniformization)),
      IsCompact L ∧ K ⊆ P.regularCoordinate '' L := by
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) :=
    (Set.toFinite ({0, 1} : Set ℂ)).isClosed.isOpen_compl
  let _ : LocallyCompactSpace RegularCoordinateBase := hopen.locallyCompactSpace
  exact SphereSixComplex.IsLocalHomeomorph.exists_compact_source_cover
    P.regularCoordinate_isLocalHomeomorph P.regularCoordinate_surjective hK

/-- Simultaneous real-period-cube parametrization over the regular base. -/
@[expose] public noncomputable def regularFamilyBaseCubeParam
    (p : RegularBase (U := P.modular.modularParameter.toTriangleUniformization) × RealPeriods) :
    RegularTotalSpace P.periods :=
  projection (regularParameterMap P.periods)
    (p.1, (fullRankDomain (regularParameterMap P.periods p.1)).realEquiv p.2)

public theorem regularFamilyBaseCubeParam_continuous :
    Continuous P.regularFamilyBaseCubeParam := by
  unfold regularFamilyBaseCubeParam
  rw [projection.eq_def, quotientProjection.eq_def]
  apply continuous_quot_mk.comp
  apply continuous_fst.prodMk
  let j : RegularBase
      (U := P.modular.modularParameter.toTriangleUniformization) × RealPeriods →
      UpperHalfPlane × RealPeriods := fun p ↦ (p.1.1, p.2)
  have hj : Continuous j :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  convert (periodRealLinear_parameterMap_continuous P.periods).comp hj using 1
  funext p
  simp only [Function.comp_apply, j, regularParameterMap]
  rw [fullRankDomain.eq_def, FullRank.ofSetupInequalities_realEquiv_apply]

/-- A point in a regular fibre has a representative in the closed real period cube. -/
public theorem exists_regularFamilyBaseCubeParam_eq
    (q : RegularTotalSpace P.periods) :
    ∃ r ∈ Set.Icc (0 : RealPeriods) 1,
      P.regularFamilyBaseCubeParam (regularTotalSpaceBase P.periods q, r) = q := by
  have hqfiber : regularFamilyInclusion P.periods q ∈
      familyFiber P.periods (regularTotalSpaceBase P.periods q).1 := by
    induction q using Quotient.inductionOn with
    | _ p =>
        refine ⟨p.2, ?_⟩
        rw [regularFamilyInclusion_mk, regularTotalSpaceBase_mk]
        rw [projection.eq_def]
        rfl
  rw [familyFiber_eq_image_unitCube P.periods
    (regularTotalSpaceBase P.periods q).1] at hqfiber
  obtain ⟨r, hr, heq⟩ := hqfiber
  refine ⟨r, hr, ?_⟩
  apply regularFamilyInclusion_injective P.periods
  change regularFamilyInclusion P.periods
      (Quotient.mk _
        (regularTotalSpaceBase P.periods q,
          (fullRankDomain (regularParameterMap P.periods
            (regularTotalSpaceBase P.periods q))).realEquiv r)) = _
  rw [regularFamilyInclusion_mk]
  change Quotient.mk _
      ((regularTotalSpaceBase P.periods q).1,
        (fullRankDomain (regularParameterMap P.periods
          (regularTotalSpaceBase P.periods q))).realEquiv r) = _
  rw [familyFiberRealParam, projection.eq_def, quotientProjection.eq_def] at heq
  rw [regularParameterMap.eq_def]
  exact heq

/-- Coordinate-core data at the exact remaining boundary.  The compact set lies in the regular
affine coordinate line; points outside it must already lie in one of the selected central collar
images. -/
public structure ThresholdedCentralEndCoverData where
  coordinateSubset : Set RegularCoordinateBase
  coordinateSubset_isCompact : IsCompact coordinateSubset
  threshold : Fin 3 → ℝ
  threshold_nonneg : ∀ i, 0 ≤ threshold i
  threshold_lt_outer : ∀ i, threshold i < P.starOuterRadius i
  centralEnd_covers : ∀ q : RegularTotalSpace P.periods,
    P.regularCoordinate (regularTotalSpaceBase P.periods q) ∉ coordinateSubset →
      ∃ (i : Fin 3) (z : P.starCollarSourceType i),
        P.starToCentral i z = P.centralQuotientProjection q ∧
          P.starCollarRadius i z ≤ threshold i
  outerCentral_coordinate : ∀ (i : Fin 3) (z : P.starCollarSourceType i)
    (q : RegularTotalSpace P.periods),
      P.centralQuotientProjection q = P.starToCentral i z →
        threshold i < P.starCollarRadius i z →
          P.regularCoordinate (regularTotalSpaceBase P.periods q) ∈ coordinateSubset

/-- The exact remaining paper-specific central end-cover theorem, named without assuming it. -/
@[expose] public def ThresholdedCentralEndCoverExistence : Prop :=
  Nonempty P.ThresholdedCentralEndCoverData

namespace ThresholdedCentralEndCoverData

variable {P : PaperAnalyticData} (C : P.ThresholdedCentralEndCoverData)

/-- A selected compact set of regular source representatives for the coordinate core. -/
@[expose] public noncomputable def representativeSubset :
    Set (RegularBase
      (U := P.modular.modularParameter.toTriangleUniformization)) :=
  Classical.choose
    (P.regularCoordinate_compact_has_compactRepresentatives
      C.coordinateSubset C.coordinateSubset_isCompact)

public theorem representativeSubset_isCompact : IsCompact C.representativeSubset :=
  (Classical.choose_spec
    (P.regularCoordinate_compact_has_compactRepresentatives
      C.coordinateSubset C.coordinateSubset_isCompact)).1

public theorem coordinateSubset_subset_image :
    C.coordinateSubset ⊆ P.regularCoordinate '' C.representativeSubset :=
  (Classical.choose_spec
    (P.regularCoordinate_compact_has_compactRepresentatives
      C.coordinateSubset C.coordinateSubset_isCompact)).2

/-- The compact central core obtained from one real period cube over the compact representative
set. -/
@[expose] public noncomputable def centralSubset : Set P.CentralFamily :=
  P.centralQuotientProjection ∘ P.regularFamilyBaseCubeParam ''
    (C.representativeSubset ×ˢ Set.Icc (0 : RealPeriods) 1)

public theorem centralSubset_isCompact : IsCompact C.centralSubset := by
  have hdomain : IsCompact
      (C.representativeSubset ×ˢ Set.Icc (0 : RealPeriods) 1) :=
    C.representativeSubset_isCompact.prod isCompact_Icc
  exact hdomain.image
    (P.centralQuotientProjection_isLocalHomeomorph.continuous.comp
      P.regularFamilyBaseCubeParam_continuous)

public theorem centralQuotientProjection_mem_centralSubset
    (q : RegularTotalSpace P.periods)
    (hcoord : P.regularCoordinate (regularTotalSpaceBase P.periods q) ∈
      C.coordinateSubset) :
    P.centralQuotientProjection q ∈ C.centralSubset := by
  let _ := regularFamilyDeckAction P.periods
  obtain ⟨z, hzL, hzcoord⟩ := C.coordinateSubset_subset_image hcoord
  have hcoordinate : P.modular.sourceCoordinate.coordinate z.1 =
      P.modular.sourceCoordinate.coordinate (regularTotalSpaceBase P.periods q).1 :=
    congrArg Subtype.val hzcoord
  obtain ⟨g, hg⟩ :=
    (P.modular.sourceCoordinate.coordinate_eq_iff_orbit z.1
      (regularTotalSpaceBase P.periods q).1).mp hcoordinate
  let q' := regularFamilyDeckMap P.periods g⁻¹ q
  have hbase : regularTotalSpaceBase P.periods q' = z := by
    dsimp only [q']
    rw [regularTotalSpaceBase_familyDeckMap]
    apply Subtype.ext
    change fuchsianSourceAction g⁻¹ •
      (regularTotalSpaceBase P.periods q).1 = z.1
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  obtain ⟨r, hr, hrq⟩ := P.exists_regularFamilyBaseCubeParam_eq q'
  refine ⟨(z, r), ⟨hzL, hr⟩, ?_⟩
  change P.centralQuotientProjection
      (P.regularFamilyBaseCubeParam (z, r)) = P.centralQuotientProjection q
  rw [← hbase, hrq]
  rw [centralQuotientProjection.eq_def, quotientProjection.eq_def]
  apply Quotient.sound
  change MulAction.orbitRel Delta (RegularTotalSpace P.periods) q' q
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g⁻¹, rfl⟩

/-- The thresholded end cover gives the exact central-side radial-core coverage field. -/
public theorem central_covers_radialCore : ∀ x : P.CentralFamily,
    x ∈ C.centralSubset ∨
      ∃ (i : Fin 3) (z : P.starCollarSourceType i),
        P.starToCentral i z = x ∧
          P.starToFilling i z ∈ P.starFillingRadialCore C.threshold i := by
  intro x
  obtain ⟨q, rfl⟩ := P.centralQuotientProjection_surjective x
  by_cases hcoord :
      P.regularCoordinate (regularTotalSpaceBase P.periods q) ∈ C.coordinateSubset
  · exact Or.inl (C.centralQuotientProjection_mem_centralSubset q hcoord)
  · right
    obtain ⟨i, z, hz, hradius⟩ := C.centralEnd_covers q hcoord
    refine ⟨i, z, hz, ?_⟩
    exact hradius

/-- Collar points above the selected thresholds map back into the compact central core. -/
public theorem outerCentral_covers : ∀ (i : Fin 3) (z : P.starCollarSourceType i),
    C.threshold i < P.starCollarRadius i z → P.starToCentral i z ∈ C.centralSubset := by
  intro i z hz
  obtain ⟨q, hq⟩ := P.centralQuotientProjection_surjective (P.starToCentral i z)
  rw [← hq]
  apply C.centralQuotientProjection_mem_centralSubset q
  exact C.outerCentral_coordinate i z q hq hz

/-- The thresholded coordinate core and the isolated cusp-filling sublevel theorem package the
exact compact-cover data for the selected open-embedding star. -/
public noncomputable def toOpenEmbeddingStarCompactCoverData
    (hcusp : P.ActualLocalCuspRadialCoreCompactness) :
    P.openEmbeddingStarData.CompactCoverData :=
  P.openEmbeddingStarCompactCoverData_of_radialCores hcusp C.threshold
    C.threshold_nonneg C.threshold_lt_outer C.centralSubset C.centralSubset_isCompact
    C.central_covers_radialCore C.outerCentral_covers

end ThresholdedCentralEndCoverData

end PaperAnalyticData

end

end SphereSixComplex.Geometry
