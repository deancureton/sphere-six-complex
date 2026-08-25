module

public import SphereSixComplex.Topology.StableFramingLocalFrameCoefficients
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Buffered radial rank-seven clutching presentations

The raw two-chart presentation of a sphere is not by itself suitable for an exact clutching
extension: its overlap can run all the way into the omitted centre of one chart, and the coordinate
transition need not have an invertible limit there.  This file records the geometric buffer used in
the classical clutching argument.

Local frames live on large open domains.  Smaller open sets cover the manifold, their closures lie
inside the large frame domains, and a coordinate on the large southern domain identifies the small
overlap with an outer radial collar.  The transition on this collar is required to depend only on
the angular coordinate.  A smooth radial disk fill of that angular map then gives, by composition,
the exact gauge extension used by `SmoothRankSevenClutchingExtensionSix`.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousMap Set
open scoped Bundle ContDiff Manifold

namespace SphereSixComplex

universe u

/-- The matrix general linear group used for rank-seven clutching maps. -/
public abbrev StableGeneralLinearSeven :=
  Matrix.GeneralLinearGroup (Fin 7) ℝ

namespace StableGeneralLinearSeven

/-- Regard an invertible `7 × 7` matrix as an automorphism of the frame-coordinate space. -/
public noncomputable def toLinearEquiv (A : StableGeneralLinearSeven) :
    StableFrameCoordinatesSix ≃ₗ[ℝ] StableFrameCoordinatesSix :=
  (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv

/-- A scalar matrix coefficient in the fixed coordinate basis. -/
public noncomputable def coeff (A : StableGeneralLinearSeven) (i j : Fin 7) : ℝ :=
  A.toLinearEquiv ((Pi.basisFun ℝ (Fin 7)) i) j

end StableGeneralLinearSeven

/-- The angular coordinate of a nonzero point of real six-space. -/
public noncomputable def stableClutchingDirection
    (y : RealModel) (hy : y ≠ 0) : StableClutchingEquatorFiveSphere :=
  (homeomorphUnitSphereProd RealModel ⟨y, by simpa⟩).1

/-- The angular coordinate, with nonvanishing supplied by positivity of the squared norm. -/
public noncomputable def stableClutchingDirectionOfNormSqPositive
    (y : RealModel) (hy : 0 < ‖y‖ ^ 2) : StableClutchingEquatorFiveSphere :=
  stableClutchingDirection y (by
    intro h
    subst y
    norm_num at hy)

/-- A two-patch stable frame whose smaller gluing cover is buffered inside larger frame domains.

The closure containments ensure that the large-frame transition is defined on a neighborhood of
the closed gluing collar.  This is the boundary regularity missing from an unbuffered punctured
stereographic cover. -/
public structure SmoothBufferedHemisphericalRankSevenClutchingPresentationSix
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] where
  largePresentation : SmoothRankSevenClutchingPresentationSix M
  north : Set M
  south : Set M
  north_isOpen : IsOpen north
  south_isOpen : IsOpen south
  cover : north ∪ south = Set.univ
  north_buffer : closure north ⊆ largePresentation.north
  south_buffer : closure south ⊆ largePresentation.south
  north_contractible : ContractibleSpace north
  south_contractible : ContractibleSpace south
  equatorMarking :
    {x : M // x ∈ north ∩ south} ≃ₕ StableClutchingEquatorFiveSphere

namespace SmoothBufferedHemisphericalRankSevenClutchingPresentationSix

variable {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]

/-- The small north gluing patch lies in the large north frame domain. -/
public theorem north_subset_large
    (q : SmoothBufferedHemisphericalRankSevenClutchingPresentationSix M) :
    q.north ⊆ q.largePresentation.north :=
  subset_closure.trans q.north_buffer

/-- The small south gluing patch lies in the large south frame domain. -/
public theorem south_subset_large
    (q : SmoothBufferedHemisphericalRankSevenClutchingPresentationSix M) :
    q.south ⊆ q.largePresentation.south :=
  subset_closure.trans q.south_buffer

/-- Restrict the large local frames to the smaller buffered gluing cover. -/
public def toClutchingPresentation
    (q : SmoothBufferedHemisphericalRankSevenClutchingPresentationSix M) :
    SmoothRankSevenClutchingPresentationSix M where
  north := q.north
  south := q.south
  north_isOpen := q.north_isOpen
  south_isOpen := q.south_isOpen
  cover := q.cover
  northSections := q.largePresentation.northSections
  southSections := q.largePresentation.southSections
  northFrame := q.largePresentation.northFrame.mono q.north_subset_large
  southFrame := q.largePresentation.southFrame.mono q.south_subset_large

/-- Forget the buffer while retaining the hemispherical clutching presentation. -/
public def toHemisphericalPresentation
    (q : SmoothBufferedHemisphericalRankSevenClutchingPresentationSix M) :
    SmoothHemisphericalRankSevenClutchingPresentationSix M where
  toClutchingPresentation := q.toClutchingPresentation
  north_contractible := q.north_contractible
  south_contractible := q.south_contractible
  equatorMarking := q.equatorMarking

end SmoothBufferedHemisphericalRankSevenClutchingPresentationSix

/-- A buffered presentation whose transition is constant along the radial direction of the
southern collar.

The small south patch is the radius-two coordinate ball and its overlap with the small north patch
is the outer collar `1 < ‖y‖²`.  Both numerical radii are arbitrary normalizations; their separation
is what leaves room for a smooth nullhomotopy that is constant near the disk centre. -/
public structure SmoothBufferedRadialRankSevenClutchingPresentationSix
    (M : Type u) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] where
  toBufferedPresentation :
    SmoothBufferedHemisphericalRankSevenClutchingPresentationSix M
  southCoordinates : OpenPartialHomeomorph M RealModel
  southCoordinates_source :
    southCoordinates.source = toBufferedPresentation.largePresentation.south
  southCoordinates_target : southCoordinates.target = Set.univ
  southCoordinates_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) ∞
      southCoordinates southCoordinates.source
  southCoordinates_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) ∞
      southCoordinates.symm southCoordinates.target
  south_eq_coordinate_ball :
    toBufferedPresentation.south =
      southCoordinates ⁻¹' Metric.ball (0 : RealModel) 2
  overlap_is_outer_collar (x : M) (hxS : x ∈ toBufferedPresentation.south) :
    x ∈ toBufferedPresentation.north ↔ 1 < ‖southCoordinates x‖ ^ 2
  equatorTransition : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven
  transition_eq_radial (x : M)
      (hxN : x ∈ toBufferedPresentation.north)
      (hxS : x ∈ toBufferedPresentation.south) :
    toBufferedPresentation.toClutchingPresentation.coordinateTransition x hxN hxS =
      (equatorTransition
        (stableClutchingDirectionOfNormSqPositive (southCoordinates x)
          (zero_lt_one.trans ((overlap_is_outer_collar x hxS).mp hxN)))).toLinearEquiv

namespace SmoothBufferedRadialRankSevenClutchingPresentationSix

variable {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]

/-- The underlying small clutching presentation. -/
public def toClutchingPresentation
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M) :
    SmoothRankSevenClutchingPresentationSix M :=
  q.toBufferedPresentation.toClutchingPresentation

/-- The underlying hemispherical presentation. -/
public def toHemisphericalPresentation
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M) :
    SmoothHemisphericalRankSevenClutchingPresentationSix M :=
  q.toBufferedPresentation.toHemisphericalPresentation

/-- The small southern patch lies in the source of its smooth coordinate. -/
public theorem south_subset_coordinates_source
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M) :
    q.toBufferedPresentation.south ⊆ q.southCoordinates.source := by
  rw [q.southCoordinates_source]
  exact q.toBufferedPresentation.south_subset_large

end SmoothBufferedRadialRankSevenClutchingPresentationSix

/-- A coefficientwise-smooth fill of an equatorial `GL₇(ℝ)` clutching map.

Outside the unit ball the fill is exactly the angular clutching map.  Requiring equality on the
whole outer region, rather than only on the unit sphere, makes the eventual gauge agree with the
transition throughout the open overlap. -/
public structure SmoothRadialGLSevenDiskFill
    (g : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven) where
  fill : RealModel → StableGeneralLinearSeven
  contDiff_coeff (i j : Fin 7) :
    ContDiff ℝ ∞ (fun y ↦ (fill y).coeff i j)
  agrees_outer (y : RealModel) (hy : 1 ≤ ‖y‖ ^ 2) :
    fill y = g (stableClutchingDirectionOfNormSqPositive y (zero_lt_one.trans_le hy))

/-- A smooth nullhomotopy with collars at both endpoints.

The lower collar makes its radial cone constant near the origin, while the upper collar makes that
cone agree exactly with the equatorial map on the entire outer overlap. -/
public structure SmoothCollaredGLSevenNullhomotopy
    (g : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven) where
  base : StableGeneralLinearSeven
  homotopy : C(ℝ × StableClutchingEquatorFiveSphere, StableGeneralLinearSeven)
  contMDiff_coeff (i j : Fin 7) :
    ContMDiff
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ (homotopy z).coeff i j)
  eq_base (t : ℝ) (u : StableClutchingEquatorFiveSphere) (ht : t ≤ (1 / 4 : ℝ)) :
    homotopy (t, u) = base
  eq_equator (t : ℝ) (u : StableClutchingEquatorFiveSphere) (ht : 1 ≤ t) :
    homotopy (t, u) = g u

private def puncturedRealModel : TopologicalSpace.Opens RealModel :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

private noncomputable def stableClutchingDirectionOnPunctured
    (y : puncturedRealModel) : StableClutchingEquatorFiveSphere :=
  stableClutchingDirection y y.property

private theorem contMDiff_stableClutchingDirectionOnPunctured :
    ContMDiff 𝓘(ℝ, RealModel) (𝓡 5) ∞ stableClutchingDirectionOnPunctured := by
  let normalizePunctured : puncturedRealModel → RealModel :=
    fun y ↦ ‖(y : RealModel)‖⁻¹ • (y : RealModel)
  have hnormalize :
      ContMDiff 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) ∞ normalizePunctured := by
    intro y
    apply (contMDiffAt_subtype_iff
      (f := fun z : RealModel ↦ ‖z‖⁻¹ • z) (U := puncturedRealModel)).mpr
    exact (((contDiffAt_id.norm ℝ y.property).inv
      (norm_ne_zero_iff.mpr y.property)).smul contDiffAt_id).contMDiffAt
  have hmem (y : puncturedRealModel) :
      normalizePunctured y ∈ Metric.sphere (0 : RealModel) 1 := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm y.property
  let : Fact (Module.finrank ℝ RealModel = 5 + 1) :=
    ⟨@finrank_euclideanSpace_fin ℝ _ 6⟩
  have hcod := hnormalize.codRestrict_sphere (n := 5) hmem
  have heq : stableClutchingDirectionOnPunctured =
      Set.codRestrict normalizePunctured (Metric.sphere (0 : RealModel) 1) hmem := by
    funext y
    apply Subtype.ext
    unfold stableClutchingDirectionOnPunctured stableClutchingDirection
    rw [homeomorphUnitSphereProd_apply_fst_coe]
    rfl
  rw [heq]
  exact hcod

namespace SmoothCollaredGLSevenNullhomotopy

variable {g : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven}

/-- Cone a collared nullhomotopy radially over real six-space. -/
public noncomputable def radialFill
    (H : SmoothCollaredGLSevenNullhomotopy g) (y : RealModel) :
    StableGeneralLinearSeven :=
  if hy : y = 0 then H.base else
    H.homotopy (‖y‖ ^ 2, stableClutchingDirection y hy)

/-- A smooth nullhomotopy collared at both endpoints gives a smooth radial disk fill.

The apparent singularity in the angular coordinate at the origin is removable: the lower collar
makes the radial cone constant there.  Away from the origin, normalization into the unit sphere is
smooth. -/
public noncomputable def toDiskFill
    (H : SmoothCollaredGLSevenNullhomotopy g) : SmoothRadialGLSevenDiskFill g where
  fill := radialFill H
  contDiff_coeff i j := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y = 0
    · subst y
      have hsmall : ∀ᶠ z : RealModel in nhds 0, ‖z‖ ^ 2 < (1 / 4 : ℝ) :=
        (contDiff_norm_sq ℝ (n := ∞)).continuous.continuousAt.eventually_lt
          continuousAt_const (by norm_num)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hsmall] with z hz
      change (radialFill H z).coeff i j = H.base.coeff i j
      by_cases hz0 : z = 0
      · rw [radialFill, dite_eq_left hz0]
      · rw [radialFill, dite_eq_right hz0, H.eq_base _ _ (le_of_lt hz)]
    · apply ContMDiffAt.contDiffAt
      let yU : puncturedRealModel := ⟨y, hy⟩
      apply (contMDiffAt_subtype_iff
        (f := fun z : RealModel ↦ (radialFill H z).coeff i j)
        (U := puncturedRealModel) (x := yU)).mp
      have hsq : ContMDiff 𝓘(ℝ, RealModel) 𝓘(ℝ, ℝ) ∞
          (fun z : puncturedRealModel ↦ ‖(z : RealModel)‖ ^ 2) :=
        (contDiff_norm_sq ℝ).contMDiff.comp contMDiff_subtype_val
      have hpair := hsq.prodMk contMDiff_stableClutchingDirectionOnPunctured
      have hcomp := (H.contMDiff_coeff i j).comp hpair
      apply hcomp.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [] with z
      change (radialFill H (z : RealModel)).coeff i j =
        (H.homotopy (‖(z : RealModel)‖ ^ 2,
          stableClutchingDirectionOnPunctured z)).coeff i j
      have hz0 : (z : RealModel) ≠ 0 := by
        simpa [puncturedRealModel] using z.property
      rw [radialFill, dite_eq_right hz0]
      rfl
  agrees_outer y hy := by
    have hy0 : y ≠ 0 := by
      intro h
      subst y
      norm_num at hy
    rw [radialFill, dite_eq_right hy0, H.eq_equator _ _ hy]
    rfl

end SmoothCollaredGLSevenNullhomotopy

namespace SmoothBufferedRadialRankSevenClutchingPresentationSix

variable {M : Type u} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]

/-- A smooth radial disk fill gives the exact gauge extension on the small buffered cover. -/
public noncomputable def toClutchingExtension
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M)
    (F : SmoothRadialGLSevenDiskFill q.equatorTransition) :
    SmoothRankSevenClutchingExtensionSix q.toClutchingPresentation where
  gauge x := (F.fill (q.southCoordinates x)).toLinearEquiv
  contMDiffOn_coeff i j := by
    change ContMDiffOn 𝓘(ℝ, RealModel) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ (F.fill (q.southCoordinates x)).toLinearEquiv
        ((Pi.basisFun ℝ (Fin 7)) i) j) q.toBufferedPresentation.south
    have hcoords :
        ContMDiffOn 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) ∞ q.southCoordinates
          q.toBufferedPresentation.south :=
      q.southCoordinates_contMDiffOn.mono q.south_subset_coordinates_source
    simpa only [StableGeneralLinearSeven.coeff, Function.comp_def] using
      ContMDiff.comp_contMDiffOn (ContDiff.contMDiff (F.contDiff_coeff i j)) hcoords
  agrees_transition x hxN hxS := by
    change (F.fill (q.southCoordinates x)).toLinearEquiv =
      q.toBufferedPresentation.toClutchingPresentation.coordinateTransition x hxN hxS
    rw [q.transition_eq_radial x hxN hxS]
    apply congrArg StableGeneralLinearSeven.toLinearEquiv
    simpa using F.agrees_outer (q.southCoordinates x)
      (le_of_lt ((q.overlap_is_outer_collar x hxS).mp hxN))

end SmoothBufferedRadialRankSevenClutchingPresentationSix

/-- The corrected buffered-radial clutching obligation for marked homotopy six-spheres. -/
public def HomotopySixSphereBufferedRadialRankSevenClutchingVanishing : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    ∃ q : SmoothBufferedRadialRankSevenClutchingPresentationSix S.carrier,
      Nonempty (SmoothRadialGLSevenDiskFill q.equatorTransition)

/-- The geometric and homotopical obligation phrased using a collared smooth nullhomotopy of the
equatorial clutching map. -/
public def HomotopySixSphereBufferedRadialRankSevenCollaredNullhomotopyVanishing : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    ∃ q : SmoothBufferedRadialRankSevenClutchingPresentationSix S.carrier,
      Nonempty (SmoothCollaredGLSevenNullhomotopy q.equatorTransition)

/-- Collared smooth nullhomotopies provide the radial disk fills required by buffered clutching
vanishing. -/
public theorem homotopySixSphereBufferedRadialRankSevenClutchingVanishing_of_collaredNullhomotopy
    (h : HomotopySixSphereBufferedRadialRankSevenCollaredNullhomotopyVanishing) :
    HomotopySixSphereBufferedRadialRankSevenClutchingVanishing := by
  intro S
  obtain ⟨q, ⟨H⟩⟩ := h S
  exact ⟨q, ⟨H.toDiskFill⟩⟩

/-- Buffered radial clutching vanishing supplies the original exact hemispherical extension
obligation. -/
public theorem homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_bufferedRadial
    (h : HomotopySixSphereBufferedRadialRankSevenClutchingVanishing) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing := by
  intro S
  obtain ⟨q, ⟨F⟩⟩ := h S
  exact ⟨q.toHemisphericalPresentation, ⟨q.toClutchingExtension F⟩⟩

/-- The original exact hemispherical clutching-extension obligation follows from buffered radial
presentations equipped with collared smooth nullhomotopies. -/
public theorem
    homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_collaredNullhomotopy
    (h : HomotopySixSphereBufferedRadialRankSevenCollaredNullhomotopyVanishing) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing :=
  homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_bufferedRadial
    (homotopySixSphereBufferedRadialRankSevenClutchingVanishing_of_collaredNullhomotopy h)

end SphereSixComplex
