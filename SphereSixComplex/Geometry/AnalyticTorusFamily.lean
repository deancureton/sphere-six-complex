module

public import SphereSixComplex.Geometry.TorusFamily
public import SphereSixComplex.Periods.Functions

/-!
# The analytic family of period tori

This file connects the holomorphic period functions with the geometric quotient construction.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.AnalyticTorusFamily

open Matrix Topology UpperHalfPlane SphereSixComplex.Geometry.ComplexTorus
  SphereSixComplex.Geometry.TorusFamily SphereSixComplex.Periods

public noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Coordinate model for the three complex period parameters. -/
public abbrev ParameterCoordinates := Fin 3 → ℂ

/-- Coordinates on the period domain. -/
@[expose] public def periodDomainCoordinates (x : PeriodDomain) : ParameterCoordinates :=
  ![x.1.tau, x.1.mu, x.1.beta]

/-- The period domain carries the topology induced by its three complex coordinates. -/
public noncomputable instance : TopologicalSpace PeriodDomain :=
  TopologicalSpace.induced periodDomainCoordinates inferInstance

/-- Period-domain coordinates are injective. -/
public theorem periodDomainCoordinates_injective : Function.Injective periodDomainCoordinates := by
  intro x y h
  apply Subtype.ext
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      cases x with
      | mk xt xm xb =>
        cases y with
        | mk yt ym yb =>
          rw [Parameters.mk.injEq]
          exact ⟨by simpa [periodDomainCoordinates] using congrFun h (0 : Fin 3),
            by simpa [periodDomainCoordinates] using congrFun h (1 : Fin 3),
            by simpa [periodDomainCoordinates] using congrFun h (2 : Fin 3)⟩

/-- Reconstruct parameters from their three coordinates. -/
@[expose] public def parametersOfCoordinates (v : ParameterCoordinates) : Parameters where
  tau := v 0
  mu := v 1
  beta := v 2

/-- Coordinate form of the two strict setup inequalities. -/
public theorem setupInequalities_parametersOfCoordinates_iff (v : ParameterCoordinates) :
    SetupInequalities (parametersOfCoordinates v) ↔
      0 < (v 0).im ∧ (v 2).im * (v 0).im - 6 * (v 1).im ^ 2 < 0 := by
  constructor
  · intro h
    refine ⟨h.tau_im_pos, ?_⟩
    have htpos : 0 < (v 0).im := by
      simpa [parametersOfCoordinates] using h.tau_im_pos
    have ht : (v 0).im ≠ 0 := ne_of_gt htpos
    have heq : (v 2).im - 6 * (v 1).im ^ 2 / (v 0).im =
        ((v 2).im * (v 0).im - 6 * (v 1).im ^ 2) / (v 0).im := by
      field_simp [ht]
    have hsch := h.schur_im_neg
    change (v 2).im - 6 * (v 1).im ^ 2 / (v 0).im < 0 at hsch
    rw [heq] at hsch
    simpa using (div_lt_iff₀ htpos).mp hsch
  · rintro ⟨ht, hs⟩
    refine ⟨ht, ?_⟩
    have ht0 : (v 0).im ≠ 0 := ne_of_gt ht
    change (v 2).im - 6 * (v 1).im ^ 2 / (v 0).im < 0
    rw [show (v 2).im - 6 * (v 1).im ^ 2 / (v 0).im =
      ((v 2).im * (v 0).im - 6 * (v 1).im ^ 2) / (v 0).im by
        field_simp [ht0]]
    exact (div_lt_iff₀ ht).mpr (by simpa using hs)

/-- The image of period-domain coordinates is open. -/
public theorem isOpen_range_periodDomainCoordinates :
    IsOpen (Set.range periodDomainCoordinates) := by
  have ht : Continuous fun v : ParameterCoordinates ↦ (v 0).im :=
    Complex.continuous_im.comp (continuous_apply 0)
  have hm : Continuous fun v : ParameterCoordinates ↦ (v 1).im :=
    Complex.continuous_im.comp (continuous_apply 1)
  have hb : Continuous fun v : ParameterCoordinates ↦ (v 2).im :=
    Complex.continuous_im.comp (continuous_apply 2)
  have hopen : IsOpen {v : ParameterCoordinates |
      0 < (v 0).im ∧ (v 2).im * (v 0).im - 6 * (v 1).im ^ 2 < 0} :=
    (isOpen_lt continuous_const ht).inter
      (isOpen_lt (hb.mul ht |>.sub (continuous_const.mul (hm.pow 2))) continuous_const)
  convert hopen using 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact (setupInequalities_parametersOfCoordinates_iff (periodDomainCoordinates x)).mp <| by
      simpa [parametersOfCoordinates, periodDomainCoordinates] using x.2
  · intro hv
    have hs : SetupInequalities (parametersOfCoordinates v) :=
      (setupInequalities_parametersOfCoordinates_iff v).mpr hv
    refine ⟨⟨parametersOfCoordinates v, hs⟩, ?_⟩
    funext i
    fin_cases i <;> rfl

/-- Period-domain coordinates form an open embedding. -/
public theorem periodDomainCoordinates_isOpenEmbedding :
    IsOpenEmbedding periodDomainCoordinates where
  eq_induced := rfl
  injective := periodDomainCoordinates_injective
  isOpen_range := isOpen_range_periodDomainCoordinates

/-- A concrete point witnesses nonemptiness of the period domain. -/
public instance : Nonempty PeriodDomain :=
  ⟨⟨⟨Complex.I, 0, -Complex.I⟩, by
    constructor <;> norm_num⟩⟩

/-- Complex manifold structure on the open period domain. -/
public noncomputable instance : ChartedSpace ParameterCoordinates PeriodDomain :=
  periodDomainCoordinates_isOpenEmbedding.singletonChartedSpace

public instance : IsManifold (modelWithCornersSelf ℂ ParameterCoordinates) ω PeriodDomain :=
  periodDomainCoordinates_isOpenEmbedding.isManifold_singleton

/-- The period-domain point determined by the three analytic period functions. -/
@[expose] public def parameterMap (z : UpperHalfPlane) : PeriodDomain :=
  ⟨periodValues F.tau F.mu F.beta z, F.setup_inequalities z⟩

@[simp]
public theorem parameterMap_val (z : UpperHalfPlane) :
    (parameterMap F z).1 = periodValues F.tau F.mu F.beta z :=
  rfl

/-- The analytic parameter map is continuous in period coordinates. -/
public theorem parameterMap_continuous : Continuous (parameterMap F) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_coe.comp F.tau_holomorphic.continuous
  · exact F.mu_holomorphic.continuous
  · exact F.beta_holomorphic.continuous

/-- A holomorphic scalar-valued function on the upper half-plane is complex smooth of every
finite or infinite order. -/
public theorem contMDiff_of_mdifferentiable {f : UpperHalfPlane → ℂ} (hf : MDiff f)
    (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n f := by
  intro z
  rw [UpperHalfPlane.contMDiffAt_iff]
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  exact (hd.contDiffOn isOpen_upperHalfPlaneSet).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- The upper-half-plane-valued period `tau`, viewed in `ℂ`, is complex smooth. -/
public theorem tau_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun z ↦ (F.tau z : ℂ)) :=
  contMDiff_of_mdifferentiable (by
    intro z
    exact MDifferentiableAt.comp z (UpperHalfPlane.mdifferentiable_coe (F.tau z))
      (F.tau_holomorphic z)) n

/-- The period `mu` is complex smooth. -/
public theorem mu_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n F.mu :=
  contMDiff_of_mdifferentiable F.mu_holomorphic n

/-- The period `beta` is complex smooth. -/
public theorem beta_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n F.beta :=
  contMDiff_of_mdifferentiable F.beta_holomorphic n

/-- The three coordinate functions of the analytic parameter map are complex smooth. -/
public theorem parameterMap_coordinates_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ParameterCoordinates) n
      (periodDomainCoordinates ∘ parameterMap F) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · exact tau_contMDiff F n
  · exact mu_contMDiff F n
  · exact beta_contMDiff F n

/-- The analytic parameter map is a complex-smooth map into the open period domain. -/
public theorem parameterMap_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ParameterCoordinates) n (parameterMap F) := by
  intro z
  rw [contMDiffAt_iff_target]
  refine ⟨parameterMap_continuous F |>.continuousAt, ?_⟩
  simpa [Function.comp_def] using (parameterMap_coordinates_contMDiff F n).contMDiffAt

/-- Every integral period section of the analytic family is holomorphic, hence complex smooth of
every order. -/
public theorem periodSection_contMDiff (a : IntegerPeriods) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n
      (fun z ↦ periodVector (parameterMap F z).1 a) := by
  rw [contMDiff_pi_space]
  intro i
  fin_cases i
  · have h0 : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
        (fun z ↦ 6 * F.mu z * (a 0 : ℂ) + (F.tau z : ℂ) * (a 1 : ℂ) +
          (a 2 : ℂ)) :=
      (((contMDiff_const.mul (mu_contMDiff F n)).mul contMDiff_const).add
        ((tau_contMDiff F n).mul contMDiff_const)).add contMDiff_const
    convert h0 using 1
    funext z
    simp [parameterMap, periodValues, periodVector, periodMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · have h1 : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
        (fun z ↦ F.beta z * (a 0 : ℂ) + F.mu z * (a 1 : ℂ) + (a 3 : ℂ)) :=
      (((beta_contMDiff F n).mul contMDiff_const).add
        ((mu_contMDiff F n).mul contMDiff_const)).add contMDiff_const
    convert h1 using 1
    funext z
    simp [parameterMap, periodValues, periodVector, periodMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring

/-- Joint continuity of the real-linear period map in the analytic parameter and its vector
argument. -/
public theorem periodRealLinear_parameterMap_continuous :
    Continuous (fun p : UpperHalfPlane × RealPeriods ↦
      periodRealLinear (parameterMap F p.1).1 p.2) := by
  have ht : Continuous (fun p : UpperHalfPlane × RealPeriods ↦ (F.tau p.1 : ℂ)) :=
    (tau_contMDiff F 0).continuous.comp continuous_fst
  have hm : Continuous (fun p : UpperHalfPlane × RealPeriods ↦ F.mu p.1) :=
    (mu_contMDiff F 0).continuous.comp continuous_fst
  have hb : Continuous (fun p : UpperHalfPlane × RealPeriods ↦ F.beta p.1) :=
    (beta_contMDiff F 0).continuous.comp continuous_fst
  have ha (i : Fin 4) : Continuous (fun p : UpperHalfPlane × RealPeriods ↦ p.2 i) :=
    (continuous_apply i).comp continuous_snd
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : UpperHalfPlane × RealPeriods ↦
      p.2 0 • (6 * F.mu p.1) + p.2 1 • F.tau p.1 + p.2 2 • (1 : ℂ))
    exact (((ha 0).smul (continuous_const.mul hm)).add ((ha 1).smul ht)).add
      ((ha 2).smul continuous_const)
  · change Continuous (fun p : UpperHalfPlane × RealPeriods ↦
      p.2 0 • F.beta p.1 + p.2 1 • F.mu p.1 + p.2 3 • (1 : ℂ))
    exact (((ha 0).smul hb).add ((ha 1).smul hm)).add ((ha 3).smul continuous_const)

/-- Quantitative compact-uniform nondegeneracy of a period family.  It is the smallest estimate
needed below: on every compact base set, period vectors dominate integral coefficient norm by a
single positive constant. -/
@[expose] public def CompactUniformLowerBound {B : Type*} [TopologicalSpace B]
    (x : B → PeriodDomain) : Prop :=
  ∀ K : Set B, IsCompact K → ∃ c : ℝ, 0 < c ∧
    ∀ b ∈ K, ∀ a : IntegerPeriods,
      c * ‖integerToReal a‖ ≤ ‖periodVector (x b).1 a‖

/-- Pointwise full rank and joint continuity of the analytic real-linear period map yield a
uniform lower bound on every compact subset of the upper half-plane. -/
public theorem parameterMap_compactUniformLowerBound :
    CompactUniformLowerBound (parameterMap F) := by
  intro K hK
  have hcompact : IsCompact (K ×ˢ Metric.sphere (0 : RealPeriods) 1) :=
    hK.prod (isCompact_sphere 0 1)
  have hpositive : ∀ p ∈ K ×ˢ Metric.sphere (0 : RealPeriods) 1,
      0 < ‖periodRealLinear (parameterMap F p.1).1 p.2‖ := by
    intro p hp
    have hpne : p.2 ≠ 0 := by
      intro hpzero
      have hsphere := hp.2
      simp [hpzero] at hsphere
    apply norm_pos_iff.mpr
    intro hzero
    apply hpne
    apply Periods.periodRealLinear_injective _ (parameterMap F p.1).2
    simpa using hzero
  obtain ⟨c, hc, hcunit⟩ := hcompact.exists_forall_le'
    (periodRealLinear_parameterMap_continuous F).norm.continuousOn hpositive
  refine ⟨c, hc, ?_⟩
  intro b hb a
  let v := integerToReal a
  have hreal : c * ‖v‖ ≤ ‖periodRealLinear (parameterMap F b).1 v‖ := by
    by_cases hv : v = 0
    · simp [hv]
    · let u : RealPeriods := ‖v‖⁻¹ • v
      have hu : u ∈ Metric.sphere (0 : RealPeriods) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]
        simp [u, norm_smul, hv]
      have hcu := hcunit (b, u) ⟨hb, hu⟩
      calc
        c * ‖v‖ ≤ ‖periodRealLinear (parameterMap F b).1 u‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right hcu (norm_nonneg v)
        _ = ‖periodRealLinear (parameterMap F b).1 v‖ := by
          rw [show periodRealLinear (parameterMap F b).1 u =
            ‖v‖⁻¹ • periodRealLinear (parameterMap F b).1 v by
              exact map_smul _ _ _]
          simp [norm_smul, hv, mul_comm]
  have hm : periodRealLinear (parameterMap F b).1 (integerToReal a) =
      periodVector (parameterMap F b).1 a := by
    rw [periodRealLinear_eq_mulVec]
    change periodMatrix (parameterMap F b).1 *ᵥ (fun j ↦ ((integerToReal a j : ℝ) : ℂ)) =
      periodMatrix (parameterMap F b).1 *ᵥ (fun j ↦ (a j : ℂ))
    congr 2
  exact hreal.trans_eq (congrArg norm hm)

/-- Only finitely many integral coefficient vectors have bounded real norm. -/
public theorem finite_integerPeriods_norm_le (R : ℝ) :
    {a : IntegerPeriods | ‖integerToReal a‖ ≤ R}.Finite := by
  have hmem : integerToReal ⁻¹' (Metric.closedBall 0 R)ᶜ ∈ Filter.cofinite :=
    integerToReal_tendsto_cofinite_cocompact
      (isCompact_closedBall (0 : RealPeriods) R).compl_mem_cocompact
  have hfinite : (integerToReal ⁻¹' Metric.closedBall 0 R).Finite := by
    simpa only [Set.preimage_compl, compl_compl, Filter.mem_cofinite] using hmem
  rw [show {a : IntegerPeriods | ‖integerToReal a‖ ≤ R} =
    integerToReal ⁻¹' Metric.closedBall 0 R by
      ext a
      simp [Metric.mem_closedBall]]
  exact hfinite

/-- A compact-uniform lower bound on period vectors implies proper discontinuity of the varying
lattice action. -/
public theorem properlyDiscontinuousSMul_of_compactUniformLowerBound
    {B : Type*} [TopologicalSpace B] (x : B → PeriodDomain)
    (hlower : CompactUniformLowerBound x) :
    ProperlyDiscontinuousSMul (FamilyPeriodGroup x) (B × ComplexTwoSpace) where
  finite_disjoint_inter_image {K} {L} hK hL := by
    let D : Set ComplexTwoSpace :=
      (fun p : (B × ComplexTwoSpace) × (B × ComplexTwoSpace) ↦ p.1.2 - p.2.2) ''
        (L ×ˢ K)
    have hdiffContinuous : Continuous
        (fun p : (B × ComplexTwoSpace) × (B × ComplexTwoSpace) ↦ p.1.2 - p.2.2) :=
      (continuous_snd.comp continuous_fst).sub (continuous_snd.comp continuous_snd)
    have hD : IsCompact D := (hL.prod hK).image hdiffContinuous
    obtain ⟨R, hR⟩ := hD.isBounded.subset_closedBall 0
    obtain ⟨c, hc, hcK⟩ := hlower (Prod.fst '' K) (hK.image continuous_fst)
    have hcoeff : {a : IntegerPeriods | ‖integerToReal a‖ ≤ R / c}.Finite :=
      finite_integerPeriods_norm_le (R / c)
    apply (hcoeff.preimage (f := FamilyPeriodGroup.coeff) (fun _ _ _ _ h ↦
      Multiplicative.toAdd.injective h)).subset
    intro g hg
    rcases hg with ⟨q, ⟨p, hp, rfl⟩, hqL⟩
    have hdiff : periodVector (x p.1).1 g.coeff ∈ D := by
      refine ⟨(g • p, p), ⟨hqL, hp⟩, ?_⟩
      change (g • p).2 - p.2 = periodVector (x p.1).1 g.coeff
      rw [family_smul_snd]
      abel
    have hupper : ‖periodVector (x p.1).1 g.coeff‖ ≤ R := by
      have := hR hdiff
      simpa [Metric.mem_closedBall, dist_zero_left] using this
    have hl := hcK p.1 ⟨p, hp, rfl⟩ g.coeff
    exact (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hl.trans hupper)

/-- A compact-uniform lower bound supplies the compact properness hypothesis used by the torus
family quotient construction. -/
public theorem compactlyUniformPeriods_of_compactUniformLowerBound
    {B : Type*} [TopologicalSpace B] (x : B → PeriodDomain)
    (hlower : CompactUniformLowerBound x) : CompactlyUniformPeriods x := by
  intro K L hK hL
  exact (properlyDiscontinuousSMul_of_compactUniformLowerBound x hlower).finite_disjoint_inter_image
    hK hL

/-- Assuming compact-uniform properness, the analytic period family has a complex-manifold total
space and a locally biholomorphic quotient projection. -/
public theorem totalSpace_isManifold_and_projection_isLocalDiffeomorph_of_compactlyUniformPeriods
    (n : WithTop ℕ∞) (hproper : CompactlyUniformPeriods (parameterMap F)) :
    letI := familyIsCancelSMul (parameterMap F)
    letI := familyContinuousConstSMul (parameterMap F)
      fun a ↦ (periodSection_contMDiff F a n).continuous
    letI := familyProperlyDiscontinuousSMul (parameterMap F) hproper
    IsManifold ((modelWithCornersSelf ℂ ℂ).prod
      (modelWithCornersSelf ℂ ComplexTwoSpace)) n (TotalSpace (parameterMap F)) ∧
      IsLocalDiffeomorph ((modelWithCornersSelf ℂ ℂ).prod
        (modelWithCornersSelf ℂ ComplexTwoSpace))
        ((modelWithCornersSelf ℂ ℂ).prod
          (modelWithCornersSelf ℂ ComplexTwoSpace)) n (projection (parameterMap F)) := by
  exact TorusFamily.totalSpace_isManifold_and_projection_isLocalDiffeomorph
    (modelWithCornersSelf ℂ ℂ) n (parameterMap F)
      (fun a ↦ periodSection_contMDiff F a n) hproper

/-- A quantitative compact-uniform lower bound on the analytic periods gives the complex-manifold
total space and locally biholomorphic quotient projection. -/
public theorem totalSpace_isManifold_and_projection_isLocalDiffeomorph_of_lowerBound
    (n : WithTop ℕ∞) (hlower : CompactUniformLowerBound (parameterMap F)) :
    letI := familyIsCancelSMul (parameterMap F)
    letI := familyContinuousConstSMul (parameterMap F)
      fun a ↦ (periodSection_contMDiff F a n).continuous
    letI := familyProperlyDiscontinuousSMul (parameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F) hlower)
    IsManifold ((modelWithCornersSelf ℂ ℂ).prod
      (modelWithCornersSelf ℂ ComplexTwoSpace)) n (TotalSpace (parameterMap F)) ∧
      IsLocalDiffeomorph ((modelWithCornersSelf ℂ ℂ).prod
        (modelWithCornersSelf ℂ ComplexTwoSpace))
        ((modelWithCornersSelf ℂ ℂ).prod
          (modelWithCornersSelf ℂ ComplexTwoSpace)) n (projection (parameterMap F)) := by
  exact totalSpace_isManifold_and_projection_isLocalDiffeomorph_of_compactlyUniformPeriods F n
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F) hlower)

/-- The analytic period family unconditionally has a complex-manifold total space, and its
quotient projection is locally biholomorphic. -/
public theorem totalSpace_isManifold_and_projection_isLocalDiffeomorph
    (n : WithTop ℕ∞) :
    letI := familyIsCancelSMul (parameterMap F)
    letI := familyContinuousConstSMul (parameterMap F)
      fun a ↦ (periodSection_contMDiff F a n).continuous
    letI := familyProperlyDiscontinuousSMul (parameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
        (parameterMap_compactUniformLowerBound F))
    IsManifold ((modelWithCornersSelf ℂ ℂ).prod
      (modelWithCornersSelf ℂ ComplexTwoSpace)) n (TotalSpace (parameterMap F)) ∧
      IsLocalDiffeomorph ((modelWithCornersSelf ℂ ℂ).prod
        (modelWithCornersSelf ℂ ComplexTwoSpace))
        ((modelWithCornersSelf ℂ ℂ).prod
          (modelWithCornersSelf ℂ ComplexTwoSpace)) n (projection (parameterMap F)) := by
  exact totalSpace_isManifold_and_projection_isLocalDiffeomorph_of_lowerBound F n
    (parameterMap_compactUniformLowerBound F)

end

end SphereSixComplex.Geometry.AnalyticTorusFamily
