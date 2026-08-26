module

public import SphereSixComplex.Topology.EquivariantCoveringPreimageHomotopyEquivalence
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularBaseDeckCover
public import SphereSixComplex.Topology.PuncturedAffineHalfPlaneRadial

/-!
# Affine radial equivalences on the regular base cover

The two affine radial deformations are first performed in the punctured coordinate line and
then lifted through the genuine full-deck covering of the regular base.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

variable (A : PaperAnalyticData)

public abbrev orderThreeAffineDiscCoordinateRegion (r : ℝ) : Set RegularCoordinateBase :=
  {z | ‖z.1‖ < r}

public abbrev orderThreeAffineHalfPlaneCoordinateRegion : Set RegularCoordinateBase :=
  {z | z.1.re < 2 / 3}

public theorem orderThreeAffineDiscCoordinateRegion_subset_halfPlane
    {r : ℝ} (hr : r ≤ 2 / 3) :
    orderThreeAffineDiscCoordinateRegion r ⊆ orderThreeAffineHalfPlaneCoordinateRegion := by
  intro z hz
  exact (Complex.re_le_norm z.1).trans_lt (hz.trans_le hr)

theorem regularCoordinate_ne_zero (z : RegularCoordinateBase) : z.1 ≠ 0 := by
  intro hz
  apply z.2
  simp [hz]

theorem regularCoordinate_ne_one (z : RegularCoordinateBase) : z.1 ≠ 1 := by
  intro hz
  apply z.2
  simp [hz]

def orderThreeBigToRadial :
    C(orderThreeAffineHalfPlaneCoordinateRegion,
      puncturedComplexLeftHalfPlane (2 / 3)) where
  toFun z := ⟨z.1.1, regularCoordinate_ne_zero z.1, z.2⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def orderThreeSmallToRadial (r : ℝ) :
    C(orderThreeAffineDiscCoordinateRegion r, puncturedComplexDisc r) where
  toFun z := ⟨z.1.1, regularCoordinate_ne_zero z.1, z.2⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem radialLeft_mem_regularCoordinate
    (z : puncturedComplexLeftHalfPlane (2 / 3)) : z.1 ∈ RegularCoordinateBase := by
    simp only [RegularCoordinateBase, mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or]
    refine ⟨z.2.1, ?_⟩
    intro hz
    have h := z.2.2
    rw [hz] at h
    norm_num at h

def radialLeftToRegularCoordinate :
    C(puncturedComplexLeftHalfPlane (2 / 3), RegularCoordinateBase) where
  toFun z := ⟨z.1, radialLeft_mem_regularCoordinate z⟩
  continuous_toFun := continuous_subtype_val.subtype_mk
    radialLeft_mem_regularCoordinate

theorem radialDisc_mem_regularCoordinate {r : ℝ} (hr : r ≤ 2 / 3)
    (z : puncturedComplexDisc r) : z.1 ∈ RegularCoordinateBase := by
    simp only [RegularCoordinateBase, mem_compl_iff, mem_insert_iff,
      mem_singleton_iff, not_or]
    refine ⟨z.2.1, ?_⟩
    intro hz
    have h := z.2.2
    rw [hz] at h
    norm_num at h
    linarith

def radialDiscToRegularCoordinate {r : ℝ} (hr : r ≤ 2 / 3) :
    C(puncturedComplexDisc r, RegularCoordinateBase) where
  toFun z := ⟨z.1, radialDisc_mem_regularCoordinate hr z⟩
  continuous_toFun := continuous_subtype_val.subtype_mk
    (radialDisc_mem_regularCoordinate hr)

/-- The order-three coordinate deformation, including preservation of the smaller disc. -/
public noncomputable def orderThreeCoordinateDeformation
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 2 / 3) :
    CoveringPreimageDeformationData
      (orderThreeAffineDiscCoordinateRegion r)
      orderThreeAffineHalfPlaneCoordinateRegion
      (orderThreeAffineDiscCoordinateRegion_subset_halfPlane hr) where
  normalize :=
    { toFun := fun z ↦ ⟨radialDiscToRegularCoordinate hr
          ((puncturedComplexDisc_radial hs hsr).normalizeTo
            (puncturedComplexLeftHalfPlane_radial hs (hsr.trans_le hr))
              (orderThreeBigToRadial z)),
        ((puncturedComplexDisc_radial hs hsr).normalizeTo
          (puncturedComplexLeftHalfPlane_radial hs (hsr.trans_le hr))
            (orderThreeBigToRadial z)).2.2⟩
      continuous_toFun := by fun_prop }
  homotopy :=
    { toFun := fun tz ↦ ⟨radialLeftToRegularCoordinate
          ((puncturedComplexLeftHalfPlane_radial hs (hsr.trans_le hr)).radialHomotopyFunction
            (tz.1, orderThreeBigToRadial tz.2)),
        by
          change (((puncturedComplexLeftHalfPlane_radial hs
            (hsr.trans_le hr)).radialHomotopyFunction
              (tz.1, orderThreeBigToRadial tz.2)).1).re < 2 / 3
          exact ((puncturedComplexLeftHalfPlane_radial hs
            (hsr.trans_le hr)).radialHomotopyFunction
              (tz.1, orderThreeBigToRadial tz.2)).2.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact radialLeftToRegularCoordinate.continuous.comp
          ((puncturedComplexLeftHalfPlane_radial hs
            (hsr.trans_le hr)).continuous_radialHomotopyFunction.comp
              (continuous_fst.prodMk
                (orderThreeBigToRadial.continuous.comp continuous_snd)))
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        apply Subtype.ext
        change ((0 : ℝ) + (1 - (0 : ℝ)) * s * ‖z.1.1‖⁻¹) • z.1.1 =
          (s * ‖z.1.1‖⁻¹) • z.1.1
        congr 1
        ring
      map_one_left := fun z ↦ by
        apply Subtype.ext
        apply Subtype.ext
        change ((1 : ℝ) + (1 - (1 : ℝ)) * s * ‖z.1.1‖⁻¹) • z.1.1 = z.1.1
        simp }
  preservesSmall := fun t z ↦ by
    change ‖((t : ℝ) + (1 - (t : ℝ)) * s * ‖z.1.1‖⁻¹) • z.1.1‖ < r
    exact ((puncturedComplexDisc_radial hs hsr).radialHomotopyFunction
      (t, orderThreeSmallToRadial r z)).2.2

public abbrev orderThreeAffineDiscBaseLift (r : ℝ) :=
  coveringRegionPreimage A.regularCoordinate (orderThreeAffineDiscCoordinateRegion r)

public abbrev orderThreeAffineHalfPlaneBaseLift :=
  coveringRegionPreimage A.regularCoordinate orderThreeAffineHalfPlaneCoordinateRegion

/-- The literal order-three inclusion on the regular base is a full-Delta equivariant homotopy
equivalence, obtained canonically by covering-space homotopy lifting. -/
public noncomputable def orderThreeBaseRadialEquiv
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 2 / 3) :
    EquivariantHomotopyEquivData
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant (orderThreeAffineDiscCoordinateRegion r))
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant orderThreeAffineHalfPlaneCoordinateRegion) :=
  (orderThreeCoordinateDeformation hs hsr hr).equivariantHomotopyEquivData
    A.regularBaseDeckAction A.regularCoordinate A.regularCoordinate_deck_invariant
    A.regularCoordinate_isCoveringMap A.regularBaseDeckAction_continuous

public abbrev orderFourAffineDiscCoordinateRegion (r : ℝ) : Set RegularCoordinateBase :=
  {z | ‖z.1 - 1‖ < r}

public abbrev orderFourAffineHalfPlaneCoordinateRegion : Set RegularCoordinateBase :=
  {z | 1 / 3 < z.1.re}

public theorem orderFourAffineDiscCoordinateRegion_subset_halfPlane
    {r : ℝ} (hr : r ≤ 1 - 1 / 3) :
    orderFourAffineDiscCoordinateRegion r ⊆ orderFourAffineHalfPlaneCoordinateRegion := by
  intro z hz
  change ‖z.1 - 1‖ < r at hz
  have hre := Complex.abs_re_le_norm (z.1 - 1)
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hlower : -‖z.1 - 1‖ ≤ z.1.re - 1 := (abs_le.mp hre).1
  norm_num at hr ⊢
  linarith [hz]

def orderFourBigToRadial :
    C(orderFourAffineHalfPlaneCoordinateRegion,
      puncturedComplexLeftHalfPlane (2 / 3)) where
  toFun z := ⟨1 - z.1.1, by
    constructor
    · intro h
      apply regularCoordinate_ne_one z.1
      exact (sub_eq_zero.mp h).symm
    · change 1 - z.1.1.re < 2 / 3
      have hz : (1 / 3 : ℝ) < z.1.1.re := z.2
      norm_num at hz ⊢
      linarith⟩
  continuous_toFun :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      (fun z ↦ by
        constructor
        · intro h
          apply regularCoordinate_ne_one z.1
          exact (sub_eq_zero.mp h).symm
        · change 1 - z.1.1.re < 2 / 3
          have hz : (1 / 3 : ℝ) < z.1.1.re := z.2
          norm_num at hz ⊢
          linarith)

def orderFourSmallToRadial (r : ℝ) :
    C(orderFourAffineDiscCoordinateRegion r, puncturedComplexDisc r) where
  toFun z := ⟨1 - z.1.1, by
    constructor
    · intro h
      apply regularCoordinate_ne_one z.1
      exact (sub_eq_zero.mp h).symm
    · rw [show 1 - z.1.1 = -(z.1.1 - 1) by ring, norm_neg]
      exact z.2⟩
  continuous_toFun :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem radialLeft_mem_reflectedRegularCoordinate
    (z : puncturedComplexLeftHalfPlane (2 / 3)) : 1 - z.1 ∈ RegularCoordinateBase := by
  simp only [RegularCoordinateBase, mem_compl_iff, mem_insert_iff,
    mem_singleton_iff, not_or]
  constructor
  · intro hz
    have h := z.2.2
    have : z.1 = 1 := (sub_eq_zero.mp hz).symm
    rw [this] at h
    norm_num at h
  · intro hz
    apply z.2.1
    exact sub_eq_self.mp hz

def radialLeftToReflectedRegularCoordinate :
    C(puncturedComplexLeftHalfPlane (2 / 3), RegularCoordinateBase) where
  toFun z := ⟨1 - z.1, radialLeft_mem_reflectedRegularCoordinate z⟩
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk
    radialLeft_mem_reflectedRegularCoordinate

theorem radialDisc_mem_reflectedRegularCoordinate {r : ℝ} (hr : r ≤ 2 / 3)
    (z : puncturedComplexDisc r) : 1 - z.1 ∈ RegularCoordinateBase := by
  simp only [RegularCoordinateBase, mem_compl_iff, mem_insert_iff,
    mem_singleton_iff, not_or]
  constructor
  · intro hz
    have h := z.2.2
    have : z.1 = 1 := (sub_eq_zero.mp hz).symm
    rw [this] at h
    norm_num at h
    linarith
  · intro hz
    apply z.2.1
    exact sub_eq_self.mp hz

def radialDiscToReflectedRegularCoordinate {r : ℝ} (hr : r ≤ 2 / 3) :
    C(puncturedComplexDisc r, RegularCoordinateBase) where
  toFun z := ⟨1 - z.1, radialDisc_mem_reflectedRegularCoordinate hr z⟩
  continuous_toFun := (continuous_const.sub continuous_subtype_val).subtype_mk
    (radialDisc_mem_reflectedRegularCoordinate hr)

theorem orderFourCoordinateRadial_preservesSmall
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1 - 1 / 3)
    (t : unitInterval) (z : orderFourAffineDiscCoordinateRegion r) :
    radialLeftToReflectedRegularCoordinate
      ((puncturedComplexLeftHalfPlane_radial hs (by linarith [hsr, hr])).radialHomotopyFunction
        (t, orderFourBigToRadial
          (⟨z.1, by
            change (1 / 3 : ℝ) < z.1.1.re
            have hz : ‖z.1.1 - 1‖ < r := z.2
            have hre := Complex.abs_re_le_norm (z.1.1 - 1)
            simp only [Complex.sub_re, Complex.one_re] at hre
            have hlower : -‖z.1.1 - 1‖ ≤ z.1.1.re - 1 := (abs_le.mp hre).1
            norm_num at hr ⊢
            linarith⟩ :
            orderFourAffineHalfPlaneCoordinateRegion))) ∈
      orderFourAffineDiscCoordinateRegion r := by
  unfold orderFourAffineDiscCoordinateRegion radialLeftToReflectedRegularCoordinate
    ComplexRadialDomain.radialHomotopyFunction orderFourBigToRadial
  change ‖(1 - (((t : ℝ) + (1 - (t : ℝ)) * s * ‖1 - z.1.1‖⁻¹) •
    (1 - z.1.1))) - 1‖ < r
  rw [show 1 - (((t : ℝ) + (1 - (t : ℝ)) * s * ‖1 - z.1.1‖⁻¹) •
    (1 - z.1.1)) - 1 = -(((t : ℝ) + (1 - (t : ℝ)) * s * ‖1 - z.1.1‖⁻¹) •
      (1 - z.1.1)) by ring, norm_neg]
  exact ((puncturedComplexDisc_radial hs hsr).radialHomotopyFunction
    (t, orderFourSmallToRadial r z)).2.2

theorem orderFourCoordinateRadial_normalizesSmall
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1 - 1 / 3)
    (z : orderFourAffineHalfPlaneCoordinateRegion) :
    radialDiscToReflectedRegularCoordinate (by linarith [hr])
      ((puncturedComplexDisc_radial hs hsr).normalizeTo
        (puncturedComplexLeftHalfPlane_radial hs (by linarith [hsr, hr]))
          (orderFourBigToRadial z)) ∈ orderFourAffineDiscCoordinateRegion r := by
  unfold orderFourAffineDiscCoordinateRegion radialDiscToReflectedRegularCoordinate
    ComplexRadialDomain.normalizeTo orderFourBigToRadial
  simp only [ContinuousMap.coe_mk, Set.mem_ofPred_eq]
  change ‖(1 - ((s * ‖1 - z.1.1‖⁻¹) • (1 - z.1.1))) - 1‖ < r
  rw [show 1 - ((s * ‖1 - z.1.1‖⁻¹) • (1 - z.1.1)) - 1 =
    -((s * ‖1 - z.1.1‖⁻¹) • (1 - z.1.1)) by ring, norm_neg]
  exact ((puncturedComplexDisc_radial hs hsr).normalizeTo
    (puncturedComplexLeftHalfPlane_radial hs (by linarith [hsr, hr]))
      (orderFourBigToRadial z)).2.2

/-- The order-four coordinate deformation is the reflected order-three radial deformation. -/
public noncomputable def orderFourCoordinateDeformation
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1 - 1 / 3) :
    CoveringPreimageDeformationData
      (orderFourAffineDiscCoordinateRegion r)
      orderFourAffineHalfPlaneCoordinateRegion
      (orderFourAffineDiscCoordinateRegion_subset_halfPlane hr) where
  normalize :=
    { toFun := fun z ↦ ⟨radialDiscToReflectedRegularCoordinate (by linarith [hr])
          ((puncturedComplexDisc_radial hs hsr).normalizeTo
            (puncturedComplexLeftHalfPlane_radial hs (by linarith [hsr, hr]))
              (orderFourBigToRadial z)), by
        exact orderFourCoordinateRadial_normalizesSmall hs hsr hr z⟩
      continuous_toFun := by fun_prop }
  homotopy :=
    { toFun := fun tz ↦ ⟨radialLeftToReflectedRegularCoordinate
          ((puncturedComplexLeftHalfPlane_radial hs (by linarith [hsr, hr])).radialHomotopyFunction
            (tz.1, orderFourBigToRadial tz.2)), by
        change 1 / 3 < 1 - (((puncturedComplexLeftHalfPlane_radial hs
          (by linarith [hsr, hr])).radialHomotopyFunction
            (tz.1, orderFourBigToRadial tz.2)).1).re
        linarith [((puncturedComplexLeftHalfPlane_radial hs
          (by linarith [hsr, hr])).radialHomotopyFunction
            (tz.1, orderFourBigToRadial tz.2)).2.2]⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact radialLeftToReflectedRegularCoordinate.continuous.comp
          ((puncturedComplexLeftHalfPlane_radial hs
            (by linarith [hsr, hr])).continuous_radialHomotopyFunction.comp
              (continuous_fst.prodMk
                (orderFourBigToRadial.continuous.comp continuous_snd)))
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        apply Subtype.ext
        change 1 - (((0 : ℝ) + (1 - (0 : ℝ)) * s * ‖1 - z.1.1‖⁻¹) •
          (1 - z.1.1)) = 1 - (s * ‖1 - z.1.1‖⁻¹) • (1 - z.1.1)
        congr 1
        congr 1
        ring
      map_one_left := fun z ↦ by
        apply Subtype.ext
        apply Subtype.ext
        dsimp only [radialLeftToReflectedRegularCoordinate,
          ComplexRadialDomain.radialHomotopyFunction, orderFourBigToRadial,
          ContinuousMap.id_apply]
        change 1 - ((((1 : ℝ) + (1 - (1 : ℝ)) * s * ‖1 - z.1.1‖⁻¹) •
          (1 - z.1.1))) = z.1.1
        simp }
  preservesSmall := fun t z ↦ by
    exact orderFourCoordinateRadial_preservesSmall hs hsr hr t z

public abbrev orderFourAffineDiscBaseLift (r : ℝ) :=
  coveringRegionPreimage A.regularCoordinate (orderFourAffineDiscCoordinateRegion r)

public abbrev orderFourAffineHalfPlaneBaseLift :=
  coveringRegionPreimage A.regularCoordinate orderFourAffineHalfPlaneCoordinateRegion

/-- The literal order-four inclusion on the regular base is a full-Delta equivariant homotopy
equivalence, obtained canonically by the reflected covering-space lift. -/
public noncomputable def orderFourBaseRadialEquiv
    {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 1 - 1 / 3) :
    EquivariantHomotopyEquivData
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant (orderFourAffineDiscCoordinateRegion r))
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant orderFourAffineHalfPlaneCoordinateRegion) :=
  (orderFourCoordinateDeformation hs hsr hr).equivariantHomotopyEquivData
    A.regularBaseDeckAction A.regularCoordinate A.regularCoordinate_deck_invariant
    A.regularCoordinate_isCoveringMap A.regularBaseDeckAction_continuous

end SphereSixComplex.Geometry.PaperAnalyticData
