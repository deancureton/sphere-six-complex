module

public import SphereSixComplex.Topology.StableFramingGeneralLinearSmoothApproximation
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Smooth nullhomotopies for rank-seven clutching maps

This file separates the remaining rank-seven clutching theorem into its geometric and homotopy-
group inputs.  A smooth nullhomotopy with the usual endpoint equalities is reparametrized by
`Real.smoothTransition`, making it constant on collars of both endpoints.  The radial-cone
construction from `StableFramingBufferedRadialClutching` can then turn it into an exact gauge
extension.

The final reduction has two independent hypotheses: every marked homotopy six-sphere admits a
buffered radial presentation with smooth equatorial transition, and every smooth map
`S⁵ → GL₇(ℝ)` is smoothly nullhomotopic.  The second is the precise smooth representative-level
form of the required `π₅(GL₇(ℝ)) = 0` calculation.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousMap Module Set
open scoped Bundle ContDiff Manifold Topology

namespace SphereSixComplex

/-- A smooth reparametrization which is zero up to `1 / 4` and one from `1` onwards. -/
public noncomputable def collaredNullhomotopyParameter (t : ℝ) : ℝ :=
  Real.smoothTransition ((4 * t - 1) / 3)

/-- The collar reparametrization is infinitely smooth. -/
public theorem contDiff_collaredNullhomotopyParameter :
    ContDiff ℝ ∞ collaredNullhomotopyParameter := by
  unfold collaredNullhomotopyParameter
  fun_prop

/-- The collar reparametrization is zero on its lower collar. -/
public theorem collaredNullhomotopyParameter_eq_zero
    (t : ℝ) (ht : t ≤ (1 / 4 : ℝ)) : collaredNullhomotopyParameter t = 0 := by
  unfold collaredNullhomotopyParameter
  apply Real.smoothTransition.zero_of_nonpos
  linarith

/-- The collar reparametrization is one on its upper collar. -/
public theorem collaredNullhomotopyParameter_eq_one
    (t : ℝ) (ht : 1 ≤ t) : collaredNullhomotopyParameter t = 1 := by
  unfold collaredNullhomotopyParameter
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- A coefficientwise-smooth nullhomotopy of an equatorial `GL₇(ℝ)` map.

Unlike `SmoothCollaredGLSevenNullhomotopy`, this structure asks only for the ordinary endpoint
equalities at parameters zero and one. -/
public structure SmoothGLSevenNullhomotopy
    (g : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven) where
  base : StableGeneralLinearSeven
  homotopy : C(ℝ × StableClutchingEquatorFiveSphere, StableGeneralLinearSeven)
  contMDiff_coeff (i j : Fin 7) :
    ContMDiff
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ (homotopy z).coeff i j)
  eq_base (u : StableClutchingEquatorFiveSphere) : homotopy (0, u) = base
  eq_equator (u : StableClutchingEquatorFiveSphere) : homotopy (1, u) = g u

namespace SmoothGLSevenNullhomotopy

variable {g : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven}

/-- Reparametrize a smooth nullhomotopy so that it is constant on collars of both endpoints. -/
public noncomputable def toCollared
    (H : SmoothGLSevenNullhomotopy g) : SmoothCollaredGLSevenNullhomotopy g where
  base := H.base
  homotopy :=
    { toFun := fun z ↦ H.homotopy (collaredNullhomotopyParameter z.1, z.2)
      continuous_toFun := H.homotopy.continuous.comp
        ((contDiff_collaredNullhomotopyParameter.continuous.comp continuous_fst).prodMk
          continuous_snd) }
  contMDiff_coeff i j := by
    have hpair : ContMDiff
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) ∞
        (fun z : ℝ × StableClutchingEquatorFiveSphere ↦
          (collaredNullhomotopyParameter z.1, z.2)) :=
      (contDiff_collaredNullhomotopyParameter.contMDiff.comp contMDiff_fst).prodMk
        contMDiff_snd
    exact (H.contMDiff_coeff i j).comp hpair
  eq_base t u ht := by
    change H.homotopy (collaredNullhomotopyParameter t, u) = H.base
    rw [collaredNullhomotopyParameter_eq_zero t ht, H.eq_base]
  eq_equator t u ht := by
    change H.homotopy (collaredNullhomotopyParameter t, u) = g u
    rw [collaredNullhomotopyParameter_eq_one t ht, H.eq_equator]

/-- Cone an ordinary smooth nullhomotopy over the radial disk after adding endpoint collars. -/
public noncomputable def toDiskFill
    (H : SmoothGLSevenNullhomotopy g) : SmoothRadialGLSevenDiskFill g :=
  H.toCollared.toDiskFill

end SmoothGLSevenNullhomotopy

private abbrev StableGLSevenMatrix := Matrix (Fin 7) (Fin 7) ℝ

private abbrev StableGLSevenHomotopyDomain :=
  ℝ × StableClutchingEquatorFiveSphere

private abbrev StableGLSevenHomotopyModel :=
  𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))

/-- Coefficientwise smoothness of a `GL₇(ℝ)`-valued map implies continuity. -/
public theorem continuous_stableGeneralLinearSeven_of_contMDiff_coeff
    (g : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven)
    (hg : ∀ i j : Fin 7,
      ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞ (fun u ↦ (g u).coeff i j)) :
    Continuous g := by
  let gval : StableClutchingEquatorFiveSphere → StableGLSevenMatrix :=
    fun u ↦ (g u : StableGLSevenMatrix)
  have hval : Continuous gval := by
    apply continuous_matrix
    intro r c
    simpa only [StableGeneralLinearSeven.coeff_eq_matrixEntry] using (hg c r).continuous
  have hinv : Continuous
      (fun u ↦ @Inv.inv StableGLSevenMatrix Matrix.inv (gval u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (continuousAt_matrix_inv (gval u) ?_).comp hval.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (g u).det_ne_zero
  apply Units.continuous_iff.mpr
  constructor
  · exact hval
  · convert hinv using 1
    funext u
    simp only [gval, Matrix.GeneralLinearGroup.coe_inv]

/-- A continuous nullhomotopy of a coefficientwise-smooth `S⁵ → GL₇(ℝ)` map can be smoothed
relative to its endpoint slices. -/
public theorem smoothGLSevenNullhomotopy_of_nullhomotopic
    (g : C(StableClutchingEquatorFiveSphere, StableGeneralLinearSeven))
    (hg : ∀ i j : Fin 7,
      ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞ (fun u ↦ (g u).coeff i j))
    (hnull : g.Nullhomotopic) :
    Nonempty (SmoothGLSevenNullhomotopy (fun u ↦ g u)) := by
  obtain ⟨base, ⟨F⟩⟩ := hnull
  let κ : ℝ → ℝ := fun t ↦ collaredNullhomotopyParameter (2 * t)
  have hκcont : Continuous κ := by
    exact contDiff_collaredNullhomotopyParameter.continuous.comp
      (continuous_const.mul continuous_id)
  let K : C(StableGLSevenHomotopyDomain, StableGeneralLinearSeven) :=
    { toFun := fun z ↦ F.extend (1 - κ z.1) z.2
      continuous_toFun := F.extend.uncurry.continuous.comp
        ((continuous_const.sub (hκcont.comp continuous_fst)).prodMk continuous_snd) }
  let S : Set StableGLSevenHomotopyDomain :=
    ({0} ×ˢ (univ : Set StableClutchingEquatorFiveSphere)) ∪
      ({1} ×ˢ (univ : Set StableClutchingEquatorFiveSphere))
  let U : Set StableGLSevenHomotopyDomain :=
    (Iio (1 / 8 : ℝ) ×ˢ (univ : Set StableClutchingEquatorFiveSphere)) ∪
      (Ioi (1 / 2 : ℝ) ×ˢ (univ : Set StableClutchingEquatorFiveSphere))
  have hS : IsClosed S := by
    exact (isClosed_singleton.prod isClosed_univ).union
      (isClosed_singleton.prod isClosed_univ)
  have hUopen : IsOpen U := by
    exact (isOpen_Iio.prod isOpen_univ).union (isOpen_Ioi.prod isOpen_univ)
  have hSU : S ⊆ U := by
    intro z hz
    rcases hz with hz | hz
    · left
      rcases hz with ⟨hz, hu⟩
      have hz0 : z.1 = 0 := by simpa only [mem_singleton_iff] using hz
      refine ⟨?_, hu⟩
      rw [hz0]
      norm_num
    · right
      rcases hz with ⟨hz, hu⟩
      have hz1 : z.1 = 1 := by simpa only [mem_singleton_iff] using hz
      refine ⟨?_, hu⟩
      rw [hz1]
      norm_num
  have hU : U ∈ 𝓝ˢ S := hUopen.mem_nhdsSet.mpr hSU
  have hK_lower (z : StableGLSevenHomotopyDomain)
      (hz : z ∈ Iio (1 / 8 : ℝ) ×ˢ (univ : Set StableClutchingEquatorFiveSphere)) :
      K z = base := by
    change F.extend (1 - κ z.1) z.2 = base
    have hκ : κ z.1 = 0 := by
      apply collaredNullhomotopyParameter_eq_zero
      norm_num at hz ⊢
      linarith [hz]
    rw [hκ]
    exact F.extend_apply_of_one_le (by norm_num) z.2
  have hK_upper (z : StableGLSevenHomotopyDomain)
      (hz : z ∈ Ioi (1 / 2 : ℝ) ×ˢ (univ : Set StableClutchingEquatorFiveSphere)) :
      K z = g z.2 := by
    change F.extend (1 - κ z.1) z.2 = g z.2
    have hκ : κ z.1 = 1 := by
      apply collaredNullhomotopyParameter_eq_one
      norm_num at hz ⊢
      linarith [hz]
    rw [hκ]
    exact F.extend_apply_of_le_zero (by norm_num) z.2
  have hKU : ∀ r c : Fin 7, ContMDiffOn StableGLSevenHomotopyModel 𝓘(ℝ, ℝ) ∞
      (fun z ↦ (K z : StableGLSevenMatrix) r c) U := by
    intro r c
    have hlower : ContMDiffOn StableGLSevenHomotopyModel 𝓘(ℝ, ℝ) ∞
        (fun z ↦ (K z : StableGLSevenMatrix) r c)
        (Iio (1 / 8 : ℝ) ×ˢ (univ : Set StableClutchingEquatorFiveSphere)) := by
      apply contMDiffOn_const.congr
      intro z hz
      exact congrArg (fun A : StableGeneralLinearSeven ↦ (A : StableGLSevenMatrix) r c)
        (hK_lower z hz)
    have hg_entry : ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞
        (fun u ↦ (g u : StableGLSevenMatrix) r c) := by
      simpa only [StableGeneralLinearSeven.coeff_eq_matrixEntry] using hg c r
    have hupper : ContMDiffOn StableGLSevenHomotopyModel 𝓘(ℝ, ℝ) ∞
        (fun z ↦ (K z : StableGLSevenMatrix) r c)
        (Ioi (1 / 2 : ℝ) ×ˢ (univ : Set StableClutchingEquatorFiveSphere)) := by
      apply (hg_entry.comp contMDiff_snd).contMDiffOn.congr
      intro z hz
      exact congrArg (fun A : StableGeneralLinearSeven ↦ (A : StableGLSevenMatrix) r c)
        (hK_upper z hz)
    exact hlower.union_of_isOpen hupper
      (isOpen_Iio.prod isOpen_univ) (isOpen_Ioi.prod isOpen_univ)
  obtain ⟨L, hLsmooth, hLK⟩ :=
    exists_smoothGLSevenApprox_eqOn K hS hU hKU
  refine ⟨{
    base := base
    homotopy := L
    contMDiff_coeff := hLsmooth
    eq_base := ?_
    eq_equator := ?_ }⟩
  · intro u
    rw [hLK (x := ((0 : ℝ), u)) (by left; simp)]
    apply hK_lower
    norm_num
  · intro u
    rw [hLK (x := ((1 : ℝ), u)) (by right; simp)]
    apply hK_upper
    norm_num

namespace SmoothBufferedRadialRankSevenClutchingPresentationSix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace RealModel M]
  [IsManifold 𝓘(ℝ, RealModel) ∞ M]

/-- The equatorial transition of a buffered presentation is coefficientwise smooth. -/
public def EquatorTransitionIsSmooth
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M) : Prop :=
  ∀ i j : Fin 7,
    ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞ (fun u ↦ (q.equatorTransition u).coeff i j)

/-- A fixed-radius section of the outer radial collar, used to read off the equatorial
transition. -/
public noncomputable def equatorSection
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M)
    (u : StableClutchingEquatorFiveSphere) : M :=
  q.southCoordinates.symm ((3 / 2 : ℝ) • (u : RealModel))

/-- The fixed-radius equator section is smooth. -/
public theorem equatorSection_contMDiff
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M) :
    ContMDiff (𝓡 5) 𝓘(ℝ, RealModel) ∞ q.equatorSection := by
  let _ : Fact (finrank ℝ RealModel = 5 + 1) := ⟨by simp [RealModel]⟩
  have hc : ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞
      (fun _ : StableClutchingEquatorFiveSphere ↦ (3 / 2 : ℝ)) :=
    contMDiff_const
  have hscale : ContMDiff (𝓡 5) 𝓘(ℝ, RealModel) ∞
      (fun u : StableClutchingEquatorFiveSphere ↦ (3 / 2 : ℝ) • (u : RealModel)) :=
    hc.smul (contMDiff_coe_sphere (E := RealModel) (n := 5))
  have hsymm : ContMDiff 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) ∞
      q.southCoordinates.symm := by
    rw [← contMDiffOn_univ]
    simpa only [q.southCoordinates_target] using
      q.southCoordinates_symm_contMDiffOn
  exact hsymm.comp hscale

/-- The fixed-radius section lies in the small southern patch. -/
public theorem equatorSection_mem_south
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M)
    (u : StableClutchingEquatorFiveSphere) :
    q.equatorSection u ∈ q.toBufferedPresentation.south := by
  let y : RealModel := (3 / 2 : ℝ) • (u : RealModel)
  have htarget : y ∈ q.southCoordinates.target := by
    rw [q.southCoordinates_target]
    exact mem_univ y
  have happly : q.southCoordinates (q.equatorSection u) = y := by
    exact q.southCoordinates.right_inv htarget
  have hu : ‖(u : RealModel)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hy : ‖y‖ = 3 / 2 := by
    simp [y, norm_smul, hu]
  rw [q.south_eq_coordinate_ball]
  change q.southCoordinates (q.equatorSection u) ∈ Metric.ball (0 : RealModel) 2
  rw [happly, Metric.mem_ball, dist_zero_right, hy]
  norm_num

/-- The fixed-radius section lies in the small northern patch. -/
public theorem equatorSection_mem_north
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M)
    (u : StableClutchingEquatorFiveSphere) :
    q.equatorSection u ∈ q.toBufferedPresentation.north := by
  have hxS := q.equatorSection_mem_south u
  apply (q.overlap_is_outer_collar (q.equatorSection u) hxS).mpr
  let y : RealModel := (3 / 2 : ℝ) • (u : RealModel)
  have htarget : y ∈ q.southCoordinates.target := by
    rw [q.southCoordinates_target]
    exact mem_univ y
  have happly : q.southCoordinates (q.equatorSection u) = y := by
    exact q.southCoordinates.right_inv htarget
  have hu : ‖(u : RealModel)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hy : ‖y‖ = 3 / 2 := by
    simp [y, norm_smul, hu]
  rw [happly, hy]
  norm_num

private theorem stableClutchingDirection_threeHalves_smul
    (u : StableClutchingEquatorFiveSphere)
    (h : 0 < ‖((3 / 2 : ℝ) • (u : RealModel))‖ ^ 2) :
    stableClutchingDirectionOfNormSqPositive ((3 / 2 : ℝ) • (u : RealModel)) h = u := by
  have hu : ‖(u : RealModel)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  apply Subtype.ext
  simp [stableClutchingDirectionOfNormSqPositive, stableClutchingDirection,
    homeomorphUnitSphereProd_apply_fst_coe, norm_smul, hu]
  rw [smul_smul]
  norm_num

/-- The angular coordinate of the fixed-radius section is the original equator point. -/
public theorem equatorSection_direction
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M)
    (u : StableClutchingEquatorFiveSphere) :
    stableClutchingDirectionOfNormSqPositive
      (q.southCoordinates (q.equatorSection u))
      (zero_lt_one.trans ((q.overlap_is_outer_collar (q.equatorSection u)
        (q.equatorSection_mem_south u)).mp (q.equatorSection_mem_north u))) = u := by
  let y : RealModel := (3 / 2 : ℝ) • (u : RealModel)
  have htarget : y ∈ q.southCoordinates.target := by
    rw [q.southCoordinates_target]
    exact mem_univ y
  have happly : q.southCoordinates (q.equatorSection u) = y := by
    exact q.southCoordinates.right_inv htarget
  have hypos : 0 < ‖y‖ ^ 2 := by
    have hu : ‖(u : RealModel)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    simp [y, norm_smul, hu]
  calc
    stableClutchingDirectionOfNormSqPositive
        (q.southCoordinates (q.equatorSection u)) _ =
        stableClutchingDirectionOfNormSqPositive y hypos := by
          congr 1
    _ = u := stableClutchingDirection_threeHalves_smul u hypos

/-- Smooth local frames force the angular transition of every buffered radial presentation to be
coefficientwise smooth; this is not an additional geometric hypothesis. -/
public theorem equatorTransition_isSmooth
    (q : SmoothBufferedRadialRankSevenClutchingPresentationSix M) :
    q.EquatorTransitionIsSmooth := by
  intro i j
  let p := q.toClutchingPresentation
  have hcoeff := p.contMDiffOn_coordinateTransitionCoeff i j
  have hsection := q.equatorSection_contMDiff
  have hcomposed : ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞
      (fun u ↦ p.coordinateTransitionCoeff i j (q.equatorSection u)) := by
    rw [← contMDiffOn_univ]
    apply hcoeff.comp hsection.contMDiffOn
    intro u _
    exact ⟨q.equatorSection_mem_north u, q.equatorSection_mem_south u⟩
  have heq (u : StableClutchingEquatorFiveSphere) :
      p.coordinateTransitionCoeff i j (q.equatorSection u) =
        (q.equatorTransition u).coeff i j := by
    have htrans := q.transition_eq_radial (q.equatorSection u)
      (q.equatorSection_mem_north u) (q.equatorSection_mem_south u)
    have heval := congrArg
      (fun A : StableFrameCoordinatesSix ≃ₗ[ℝ] StableFrameCoordinatesSix ↦
        A ((Pi.basisFun ℝ (Fin 7)) i) j) htrans
    change
      p.coordinateTransition (q.equatorSection u)
          (q.equatorSection_mem_north u) (q.equatorSection_mem_south u)
          ((Pi.basisFun ℝ (Fin 7)) i) j = _ at heval
    have hcoeffEq := p.coordinateTransition_apply_basis_eq_coeff
      (q.equatorSection u) (q.equatorSection_mem_north u)
      (q.equatorSection_mem_south u) i j
    have heval' : p.coordinateTransitionCoeff i j (q.equatorSection u) = _ :=
      hcoeffEq.symm.trans heval
    rw [q.equatorSection_direction] at heval'
    simpa only [StableGeneralLinearSeven.coeff] using heval'
  apply hcomposed.congr
  intro u
  exact (heq u).symm

end SmoothBufferedRadialRankSevenClutchingPresentationSix

/-- The remaining geometric input stripped of automatic regularity: every marked homotopy
six-sphere admits a buffered radial rank-seven clutching presentation. -/
public def HomotopySixSphereBufferedRadialRankSevenClutchingPresentation : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    Nonempty (SmoothBufferedRadialRankSevenClutchingPresentationSix S.carrier)

/-- The geometric input: a buffered radial presentation with smooth equatorial transition for
every marked homotopy six-sphere. -/
public def HomotopySixSphereSmoothBufferedRadialRankSevenClutchingPresentation : Prop :=
  ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
    ∃ q : SmoothBufferedRadialRankSevenClutchingPresentationSix S.carrier,
      q.EquatorTransitionIsSmooth

/-- Existence of buffered radial presentations supplies their equatorial smoothness
automatically. -/
public theorem
    homotopySixSphereSmoothBufferedRadialRankSevenClutchingPresentation_of_buffered
    (h : HomotopySixSphereBufferedRadialRankSevenClutchingPresentation) :
    HomotopySixSphereSmoothBufferedRadialRankSevenClutchingPresentation := by
  intro S
  obtain ⟨q⟩ := h S
  exact ⟨q, q.equatorTransition_isSmooth⟩

/-- The smooth representative-level form of `π₅(GL₇(ℝ)) = 0`. -/
public def SmoothGLSevenFiveSphereNullhomotopyVanishing : Prop :=
  ∀ g : StableClutchingEquatorFiveSphere → StableGeneralLinearSeven,
    (∀ i j : Fin 7,
      ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞ (fun u ↦ (g u).coeff i j)) →
    Nonempty (SmoothGLSevenNullhomotopy g)

/-- The purely topological representative-level form of `π₅(GL₇(ℝ)) = 0`. -/
public def TopologicalGLSevenFiveSphereNullhomotopyVanishing : Prop :=
  ∀ g : C(StableClutchingEquatorFiveSphere, StableGeneralLinearSeven), g.Nullhomotopic

/-- Topological `π₅(GL₇)` vanishing implies the smooth representative-level formulation. -/
public theorem smoothGLSevenFiveSphereNullhomotopyVanishing_of_topological
    (htop : TopologicalGLSevenFiveSphereNullhomotopyVanishing) :
    SmoothGLSevenFiveSphereNullhomotopyVanishing := by
  intro g hg
  let gc : C(StableClutchingEquatorFiveSphere, StableGeneralLinearSeven) :=
    ⟨g, continuous_stableGeneralLinearSeven_of_contMDiff_coeff g hg⟩
  apply smoothGLSevenNullhomotopy_of_nullhomotopic gc
  · intro i j
    change ContMDiff (𝓡 5) 𝓘(ℝ, ℝ) ∞ (fun u ↦ (g u).coeff i j)
    exact hg i j
  · exact htop gc

/-- The geometric presentation theorem and smooth `π₅(GL₇)` vanishing supply collared
nullhomotopies for every marked homotopy six-sphere. -/
public theorem
    homotopySixSphereBufferedRadialRankSevenCollaredNullhomotopyVanishing_of_smooth_piFive
    (hgeometry : HomotopySixSphereSmoothBufferedRadialRankSevenClutchingPresentation)
    (hpiFive : SmoothGLSevenFiveSphereNullhomotopyVanishing) :
    HomotopySixSphereBufferedRadialRankSevenCollaredNullhomotopyVanishing := by
  intro S
  obtain ⟨q, hq⟩ := hgeometry S
  obtain ⟨H⟩ := hpiFive q.equatorTransition hq
  exact ⟨q, ⟨H.toCollared⟩⟩

/-- The original exact hemispherical clutching-extension theorem follows from the geometric
presentation theorem and smooth `π₅(GL₇)` vanishing. -/
public theorem
    homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_smooth_piFive
    (hgeometry : HomotopySixSphereSmoothBufferedRadialRankSevenClutchingPresentation)
    (hpiFive : SmoothGLSevenFiveSphereNullhomotopyVanishing) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing :=
  homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_collaredNullhomotopy
    (homotopySixSphereBufferedRadialRankSevenCollaredNullhomotopyVanishing_of_smooth_piFive
      hgeometry hpiFive)

/-- The geometric presentation theorem and topological `π₅(GL₇)` vanishing supply the original
exact hemispherical clutching-extension theorem. -/
public theorem
    homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_topological_piFive
    (hgeometry : HomotopySixSphereSmoothBufferedRadialRankSevenClutchingPresentation)
    (hpiFive : TopologicalGLSevenFiveSphereNullhomotopyVanishing) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing :=
  homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_smooth_piFive hgeometry
    (smoothGLSevenFiveSphereNullhomotopyVanishing_of_topological hpiFive)

/-- Buffered radial presentation existence and the purely topological `π₅(GL₇)` calculation imply
the original exact hemispherical clutching-extension theorem. -/
public theorem
    homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_buffered_and_topological_piFive
    (hgeometry : HomotopySixSphereBufferedRadialRankSevenClutchingPresentation)
    (hpiFive : TopologicalGLSevenFiveSphereNullhomotopyVanishing) :
    HomotopySixSphereHemisphericalRankSevenClutchingVanishing :=
  homotopySixSphereHemisphericalRankSevenClutchingVanishing_of_topological_piFive
    (homotopySixSphereSmoothBufferedRadialRankSevenClutchingPresentation_of_buffered hgeometry)
    hpiFive

end SphereSixComplex
