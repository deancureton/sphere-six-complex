module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricComponentPreservation
public import SphereSixComplex.Geometry.StandardInfiniteA2ToricBarycentricTiling

/-!
# Quantitative regions in the standard infinite `A₂` toric model

This file isolates the precise standard toric-chart input of Lemma 4.4(ii) and proves the
generic passage from bounded rescaled-position charts and the `B_t` displacement estimate to
the compact-overlap conclusion used in Theorem 4.5.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- Choose the unique dense-torus coordinates of a point when it belongs to the dense torus,
and the identity coordinates otherwise. -/
public noncomputable def torusCoordinates (M : Model) (p : M.Carrier) : DenseTorus :=
  by
    classical
    exact if h : ∃ x, M.torusEmbedding x = p then Classical.choose h else 1

public theorem torusEmbedding_torusCoordinates
    (M : Model) {p : M.Carrier} (hp : M.t p ≠ 0) :
    M.torusEmbedding (torusCoordinates M p) = p := by
  have h : ∃ x, M.torusEmbedding x = p := by
    have hp' : p ∈ {q | M.t q ≠ 0} := hp
    rw [← M.torus_range] at hp'
    exact hp'
  simp only [torusCoordinates, dif_pos h]
  exact Classical.choose_spec h

public theorem torusCoordinates_unique
    (M : Model) {p : M.Carrier} (hp : M.t p ≠ 0) {x : DenseTorus}
    (hx : M.torusEmbedding x = p) :
    torusCoordinates M p = x := by
  apply M.torus_openEmbedding.injective
  rw [torusEmbedding_torusCoordinates M hp, hx]

public theorem torusCoordinates_last
    (M : Model) {p : M.Carrier} (hp : M.t p ≠ 0) :
    ((torusCoordinates M p 2 : ℂˣ) : ℂ) = M.t p := by
  rw [← M.t_torus (torusCoordinates M p), torusEmbedding_torusCoordinates M hp]

/-- The rescaled logarithmic position `y = log|x| / log|t|` from §4.4.  Its value on the
central fibre is irrelevant to every quantitative assertion below. -/
public noncomputable def rescaledPosition
    (M : Model) (p : M.Carrier) : Fin 2 → ℝ :=
  fun i ↦ Real.log ‖((torusCoordinates M p i.castSucc : ℂˣ) : ℂ)‖ /
    Real.log ‖M.t p‖

namespace CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

open SphereSixComplex.Periods

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D)

/-- Dense-torus coordinates transform by the actual phase correction and integral fan shear. -/
public theorem torusCoordinates_psiMap
    (M : Model) {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hphase : C.phase = N.phaseCoefficient) (lambda : ParameterLattice)
    (p : LocalCarrier M r) (hp : M.t p ≠ 0) :
    torusCoordinates M (C.psiMap lambda p) =
      phaseEmbedding (N.phaseCoefficient lambda (M.t p)) *
        denseTorusShear lambda (torusCoordinates M p) := by
  have hpq : M.t (C.psiMap lambda p) ≠ 0 := by
    rw [C.psiMap_preserves_t]
    exact hp
  apply torusCoordinates_unique M hpq
  rw [C.psiMap_coe, hphase, ← torusEmbedding_torusCoordinates M hp,
    M.fanShear_torus, ToricModel.phaseAction_apply, M.torusAction_torus]
  rw [torusCoordinates_unique M (by
    rw [M.t_torus]
    exact Units.ne_zero _) rfl]

public theorem torusCoordinates_psiMap_apply
    (M : Model) {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hphase : C.phase = N.phaseCoefficient) (lambda : ParameterLattice)
    (p : LocalCarrier M r) (hp : M.t p ≠ 0) (i : Fin 2) :
    torusCoordinates M (C.psiMap lambda p) i.castSucc =
      N.phaseCoefficient lambda (M.t p) i * torusCoordinates M p i.castSucc *
        torusCoordinates M p 2 ^ shearVector lambda i := by
  rw [torusCoordinates_psiMap N M C hphase lambda p hp]
  fin_cases i <;> simp [denseTorusShear, mul_assoc]

public theorem log_norm_torusCoordinates_psiMap
    (M : Model) {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hphase : C.phase = N.phaseCoefficient) (lambda : ParameterLattice)
    (p : LocalCarrier M r) (hp : M.t p ≠ 0) (i : Fin 2) :
    Real.log ‖((torusCoordinates M (C.psiMap lambda p) i.castSucc : ℂˣ) : ℂ)‖ =
      (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
        N (M.t p)).mulVec
          (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter
            lambda) i +
        Real.log ‖((torusCoordinates M p i.castSucc : ℂˣ) : ℂ)‖ +
          (shearVector lambda i : ℝ) * Real.log ‖M.t p‖ := by
  rw [torusCoordinates_psiMap_apply N M C hphase lambda p hp i]
  simp only [Units.val_mul, norm_mul]
  rw [Real.log_mul
      (mul_ne_zero (ne_of_gt (Units.norm_pos _)) (ne_of_gt (Units.norm_pos _)))
      (ne_of_gt (Units.norm_pos _)),
    Real.log_mul (ne_of_gt (Units.norm_pos _)) (ne_of_gt (Units.norm_pos _)),
    show ((↑(torusCoordinates M p 2 ^ shearVector lambda i) : ℂ)) =
      ((torusCoordinates M p 2 : ℂ)) ^ shearVector lambda i by
        exact map_zpow (Units.coeHom ℂ) _ _,
    norm_zpow, Real.log_zpow,
    torusCoordinates_last M hp]
  rw [CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.log_norm_phaseCoefficient]

/-- The exact rescaled-position identity `y(Psi_lambda p) - y(p) = B_t lambda`, with
`B_t = B₀ + R(t)/log|t|`. -/
public theorem rescaledPosition_psiMap_sub
    (M : Model) {r : ℝ} (hr : r < 1)
    (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hphase : C.phase = N.phaseCoefficient) (lambda : ParameterLattice)
    (p : LocalCarrier M r) (hp : M.t p ≠ 0) :
    rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p =
      fun i ↦ (shearVector lambda i : ℝ) +
        (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
          N (M.t p)).mulVec
            (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter
              lambda) i / Real.log ‖M.t p‖ := by
  have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
  have hnorm_lt : ‖M.t p‖ < 1 := by
    exact (mem_ball_zero_iff.mp p.property).trans hr
  have hlog : Real.log ‖M.t p‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt)
  funext i
  simp only [Pi.sub_apply, rescaledPosition]
  rw [C.psiMap_preserves_t]
  rw [log_norm_torusCoordinates_psiMap N M C hphase lambda p hp i]
  field_simp [hlog]
  ring

public theorem positionL1_real_shear (lambda : ParameterLattice) :
    positionL1 (fun i ↦ (shearVector lambda i : ℝ)) = latticeL1 lambda := by
  simpa only [positionL1, latticeL1,
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.parameterL1] using
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.shearVector_parameterL1
      lambda

/-- The entrywise `R(t)` bound and `4A ≤ |log|t||` imply the paper's uniform lower bound
`(1/2)|lambda|₁ ≤ |B_t lambda|₁`. -/
public theorem rescaledPosition_displacement_lower
    (M : Model) {r A : ℝ} (hr : r < 1)
    (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hphase : C.phase = N.phaseCoefficient)
    (hR : ∀ (p : LocalCarrier M r), M.t p ≠ 0 → ∀ lambda i,
      |(CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
        N (M.t p)).mulVec
          (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter
            lambda) i| ≤ A * latticeL1 lambda)
    (hlog : ∀ (p : LocalCarrier M r), M.t p ≠ 0 →
      4 * A ≤ |Real.log ‖M.t p‖|) :
    ∀ lambda (p : LocalCarrier M r), M.t p ≠ 0 →
      (1 / 2 : ℝ) * latticeL1 lambda ≤
        positionL1 (rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p) := by
  intro lambda p hp
  have hl1 : 0 ≤ latticeL1 lambda := by
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
  have hnorm_lt : ‖M.t p‖ < 1 := (mem_ball_zero_iff.mp p.property).trans hr
  have hlog_ne : Real.log ‖M.t p‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt)
  have habslog : 0 < |Real.log ‖M.t p‖| := abs_pos.mpr hlog_ne
  let correction : Fin 2 → ℝ := fun i ↦
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
      N (M.t p)).mulVec
        (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter
          lambda) i / Real.log ‖M.t p‖
  have hcorrection_i (i : Fin 2) :
      |correction i| ≤ (1 / 4 : ℝ) * latticeL1 lambda := by
    rw [show correction i =
      (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
        N (M.t p)).mulVec
          (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter
            lambda) i / Real.log ‖M.t p‖ by rfl,
      abs_div]
    apply (div_le_iff₀ habslog).2
    have hentry := hR p hp lambda i
    have hlogA := hlog p hp
    nlinarith
  have hcorrection : positionL1 correction ≤ (1 / 2 : ℝ) * latticeL1 lambda := by
    simp only [positionL1]
    linarith [hcorrection_i 0, hcorrection_i 1]
  have hposition := rescaledPosition_psiMap_sub N M hr C hphase lambda p hp
  let displacement := rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p
  have hreverse := positionL1_sub_le displacement correction
  have hsub : displacement - correction = fun i ↦ (shearVector lambda i : ℝ) := by
    rw [show displacement = fun i ↦ (shearVector lambda i : ℝ) + correction i by
      simpa only [displacement, correction] using hposition]
    funext i
    simp
  rw [hsub, positionL1_real_shear] at hreverse
  nlinarith

end CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- The open triangle dilation `sigma(eta) = {theta_i > -eta}` from §4.4. -/
public def a2TriangleDilation
    (upper : Bool) (v : ToricLattice) (eta : ℝ) : Set (Fin 2 → ℝ) :=
  {y | ∀ i, -eta < a2Barycentric upper v y i}

/-- The open coordinate polydisc of radius `S` in `ℂ³`. -/
public def openCoordinatePolydisc (S : ℝ) : Set ComplexModel :=
  (PiLp.homeomorph 2 fun _ : Fin 3 ↦ ℂ) ⁻¹'
    (Set.univ.pi fun _ ↦ Metric.ball 0 S)

/-- The closed coordinate polydisc of radius `S` in `ℂ³`. -/
public def closedCoordinatePolydisc (S : ℝ) : Set ComplexModel :=
  (PiLp.homeomorph 2 fun _ : Fin 3 ↦ ℂ) ⁻¹'
    (Set.univ.pi fun _ ↦ Metric.closedBall 0 S)

public theorem open_openCoordinatePolydisc (S : ℝ) :
    IsOpen (openCoordinatePolydisc S) := by
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ Metric.isOpen_ball).preimage
    (PiLp.homeomorph 2 fun _ : Fin 3 ↦ ℂ).continuous

public theorem compact_closedCoordinatePolydisc (S : ℝ) :
    IsCompact (closedCoordinatePolydisc S) := by
  exact (PiLp.homeomorph 2 fun _ : Fin 3 ↦ ℂ).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ : Fin 3 ↦ isCompact_closedBall (0 : ℂ) S)

public theorem mem_openCoordinatePolydisc_iff (z : ComplexModel) (S : ℝ) :
    z ∈ openCoordinatePolydisc S ↔ ∀ i, ‖z i‖ < S := by
  simp [openCoordinatePolydisc, Set.mem_pi, Metric.mem_ball, dist_zero_right,
    PiLp.homeomorph]

public theorem mem_closedCoordinatePolydisc_iff (z : ComplexModel) (S : ℝ) :
    z ∈ closedCoordinatePolydisc S ↔ ∀ i, ‖z i‖ ≤ S := by
  simp [closedCoordinatePolydisc, Set.mem_pi, Metric.mem_closedBall, dist_zero_right,
    PiLp.homeomorph]

/-- The actual open radius-`S` polydisc in an affine toric chart. -/
public def openToricPolydisc
    (M : Model) (upper : Bool) (v : ToricLattice) (S : ℝ) : Set M.Carrier :=
  (M.toricChart upper v).source ∩
    M.toricChart upper v ⁻¹' openCoordinatePolydisc S

/-- The actual closed radius-`S` polydisc in an affine toric chart. -/
public def closedToricPolydisc
    (M : Model) (upper : Bool) (v : ToricLattice) (S : ℝ) : Set M.Carrier :=
  (M.toricChart upper v).source ∩
    M.toricChart upper v ⁻¹' closedCoordinatePolydisc S

public theorem open_openToricPolydisc
    (M : Model) (upper : Bool) (v : ToricLattice) (S : ℝ) :
    IsOpen (openToricPolydisc M upper v S) := by
  exact (M.toricChart upper v).toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage
    (M.toricChart upper v).open_source (open_openCoordinatePolydisc S)

public theorem compact_closedToricPolydisc
    (M : Model) (upper : Bool) (v : ToricLattice) (S : ℝ) :
    IsCompact (closedToricPolydisc M upper v S) := by
  let e := M.toricChart upper v
  have htarget : closedCoordinatePolydisc S ⊆ e.target := by
    rw [M.toricChart_target]
    exact Set.subset_univ _
  have himage : e.symm '' closedCoordinatePolydisc S = closedToricPolydisc M upper v S := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzt : z ∈ e.target := htarget hz
      refine ⟨e.map_target hzt, ?_⟩
      have hright : e (e.symm z) = z := e.right_inv hzt
      change e (e.symm z) ∈ closedCoordinatePolydisc S
      rw [hright]
      exact hz
    · rintro ⟨hp, hz⟩
      refine ⟨e p, hz, ?_⟩
      exact e.left_inv hp
  rw [← himage]
  exact (compact_closedCoordinatePolydisc S).image_of_continuousOn
    (e.toOpenPartialHomeomorph.continuousOn_invFun.mono htarget)

public theorem closedToricPolydisc_eq
    (M : Model) (upper : Bool) (v : ToricLattice) (S : ℝ) :
    closedToricPolydisc M upper v S =
      {p | p ∈ (M.toricChart upper v).source ∧
        ∀ i, ‖M.toricChart upper v p i‖ ≤ S} := by
  ext p
  exact and_congr_right fun _ ↦ mem_closedCoordinatePolydisc_iff _ _

/-- In the standard affine charts, the logarithmic coordinate norms are the barycentric
coordinates of the rescaled torus position. -/
public theorem log_norm_toricChart_torus
    (M : Model) (upper : Bool) (v : ToricLattice) (x : DenseTorus)
    (hlog : Real.log ‖((x 2 : ℂˣ) : ℂ)‖ ≠ 0) (i : Fin 3) :
    Real.log ‖M.toricChart upper v (M.torusEmbedding x) i‖ =
      Real.log ‖((x 2 : ℂˣ) : ℂ)‖ *
        a2Barycentric upper v
          (fun j ↦ Real.log ‖((x j.castSucc : ℂˣ) : ℂ)‖ /
            Real.log ‖((x 2 : ℂˣ) : ℂ)‖) i := by
  rw [M.toricChart_torus_character, log_norm_evaluateCharacter]
  cases upper <;> fin_cases i <;>
    simp [a2DualCharacter, a2Barycentric, Fin.sum_univ_succ] <;>
    field_simp [hlog] <;> ring

public theorem log_norm_toricChart
    (M : Model) {p : M.Carrier} (hp : M.t p ≠ 0) (ht : ‖M.t p‖ < 1)
    (upper : Bool) (v : ToricLattice) (i : Fin 3) :
    Real.log ‖M.toricChart upper v p i‖ =
      Real.log ‖M.t p‖ * a2Barycentric upper v (rescaledPosition M p) i := by
  have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
  have hlog : Real.log ‖M.t p‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt ht)
  have hlogx : Real.log ‖((torusCoordinates M p 2 : ℂˣ) : ℂ)‖ ≠ 0 := by
    rw [torusCoordinates_last M hp]
    exact hlog
  have h := log_norm_toricChart_torus M upper v (torusCoordinates M p) hlogx i
  rw [torusEmbedding_torusCoordinates M hp] at h
  rw [torusCoordinates_last M hp] at h
  change Real.log ‖M.toricChart upper v p i‖ = Real.log ‖M.t p‖ *
    a2Barycentric upper v
      (fun j ↦ Real.log ‖((torusCoordinates M p j.castSucc : ℂˣ) : ℂ)‖ /
        Real.log ‖M.t p‖) i
  exact h

/-- Every noncentral point with `|t| < 1` lies in one of the closed unit toric polydiscs. -/
public theorem exists_closedUnitToricPolydisc_of_ne_zero
    (M : Model) {p : M.Carrier} (hp : M.t p ≠ 0) (ht : ‖M.t p‖ < 1) :
    ∃ upper v, p ∈ (M.toricChart upper v).source ∧
      ∀ i, ‖M.toricChart upper v p i‖ ≤ 1 := by
  obtain ⟨upper, v, hv⟩ := exists_a2Barycentric_nonneg (rescaledPosition M p)
  refine ⟨upper, v, ?_, fun i ↦ ?_⟩
  · rw [← torusEmbedding_torusCoordinates M hp]
    exact M.torus_mem_toricChart upper v (torusCoordinates M p)
  · apply (Real.log_nonpos_iff (norm_nonneg _)).mp
    rw [log_norm_toricChart M hp ht upper v i]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (Real.log_neg (norm_pos_iff.mpr hp) ht)) (hv i)

/-- Closedness and density extend the dense-torus unit-polydisc cover across the central fibre. -/
public theorem exists_closedUnitToricPolydisc
    (M : Model) {p : M.Carrier} (ht : ‖M.t p‖ < 1) :
    ∃ upper v, p ∈ (M.toricChart upper v).source ∧
      ∀ i, ‖M.toricChart upper v p i‖ ≤ 1 := by
  let c : ℝ := (‖M.t p‖ + 1) / 2
  have hpc : ‖M.t p‖ < c := by
    dsimp [c]
    linarith
  have hc : c < 1 := by
    dsimp [c]
    linarith
  let U : Set M.Carrier := cuspNeighborhood M c
  let V : Set M.Carrier := ⋃ a : Bool × ToricLattice,
    closedToricPolydisc M a.1 a.2 1 ∩ {q | ‖M.t q‖ ≤ c}
  have hVclosed : IsClosed V := by
    simpa only [V, closedToricPolydisc_eq] using
      M.closedUnitPolydisc_union_below_closed c hc
  have htorus : Dense {q : M.Carrier | M.t q ≠ 0} := by
    rw [← M.torus_range]
    exact M.torus_dense
  have hsub : U ∩ {q : M.Carrier | M.t q ≠ 0} ⊆ V := by
    intro q hq
    have hqc : ‖M.t q‖ < c := mem_ball_zero_iff.mp hq.1
    have hqt : ‖M.t q‖ < 1 := by
      exact hqc.trans hc
    obtain ⟨upper, v, hsource, hcoord⟩ :=
      exists_closedUnitToricPolydisc_of_ne_zero M hq.2 hqt
    apply Set.mem_iUnion.2
    refine ⟨(upper, v), ?_⟩
    rw [Set.mem_inter_iff, closedToricPolydisc_eq]
    exact ⟨⟨hsource, hcoord⟩, hqc.le⟩
  have hUV : U ⊆ V := by
    exact (htorus.open_subset_closure_inter (cuspNeighborhood M c).isOpen).trans
      (closure_minimal hsub hVclosed)
  have hpU : p ∈ U := mem_ball_zero_iff.mpr hpc
  obtain ⟨⟨upper, v⟩, hpV⟩ := Set.mem_iUnion.1 (hUV hpU)
  rw [Set.mem_inter_iff, closedToricPolydisc_eq] at hpV
  exact ⟨upper, v, hpV.1⟩

/-- Every fixed dilated `A₂` triangle has bounded `ℓ¹` position. -/
public theorem exists_positionL1_bound_a2TriangleDilation
    (upper : Bool) (v : ToricLattice) {eta : ℝ} (heta : 0 ≤ eta) :
    ∃ B : ℝ, ∀ y ∈ a2TriangleDilation upper v eta, positionL1 y ≤ B := by
  let T := 1 + 2 * eta
  refine ⟨|(v 0 : ℝ)| + |(v 1 : ℝ)| + 2 * T, ?_⟩
  intro y hy
  have h0 := hy 0
  have h1 := hy 1
  have h2 := hy 2
  have hdx0 : |y 0 - (v 0 : ℝ)| ≤ T := by
    apply abs_le.2
    cases upper
    · norm_num [a2Barycentric] at h0 h1 h2
      change -eta < y 1 - (v 1 : ℝ) at h2
      constructor <;> dsimp [T] <;> linarith
    · norm_num [a2Barycentric] at h0 h1 h2
      change -eta < (y 0 - (v 0 : ℝ)) + (y 1 - (v 1 : ℝ)) - 1 at h2
      constructor <;> dsimp [T] <;> linarith
  have hdx1 : |y 1 - (v 1 : ℝ)| ≤ T := by
    apply abs_le.2
    cases upper
    · norm_num [a2Barycentric] at h0 h1 h2
      change -eta < y 1 - (v 1 : ℝ) at h2
      constructor <;> dsimp [T] <;> linarith
    · norm_num [a2Barycentric] at h0 h1 h2
      change -eta < (y 0 - (v 0 : ℝ)) + (y 1 - (v 1 : ℝ)) - 1 at h2
      constructor <;> dsimp [T] <;> linarith
  have hy0 : |y 0| ≤ |(v 0 : ℝ)| + T := by
    calc
      |y 0| = |(y 0 - (v 0 : ℝ)) + (v 0 : ℝ)| := by ring_nf
      _ ≤ |y 0 - (v 0 : ℝ)| + |(v 0 : ℝ)| := abs_add_le _ _
      _ ≤ |(v 0 : ℝ)| + T := by linarith
  have hy1 : |y 1| ≤ |(v 1 : ℝ)| + T := by
    calc
      |y 1| = |(y 1 - (v 1 : ℝ)) + (v 1 : ℝ)| := by ring_nf
      _ ≤ |y 1 - (v 1 : ℝ)| + |(v 1 : ℝ)| := abs_add_le _ _
      _ ≤ |(v 1 : ℝ)| + T := by linarith
  simp only [positionL1]
  linarith

/-- The open radius-two polydiscs and the closed unit-polydisc cover from Lemma 4.4(ii), together
with the exact boundedness of their rescaled positions from Lemma 4.4(i). -/
public structure BoundedPolydiscRegions (M : Model) (r : ℝ) where
  radius_pos : 0 < r
  radius_lt_one : r < 1
  region : ToricRegionIndex → TopologicalSpace.Opens (LocalCarrier M r)
  region_mem_iff : ∀ p upper v,
    p ∈ region (upper, v) ↔
      (p : M.Carrier) ∈ (M.toricChart upper v).source ∧
        ∀ i, ‖M.toricChart upper v (p : M.Carrier) i‖ < 2
  closedUnit_cover : ∀ p : LocalCarrier M r, ∃ upper v,
    (p : M.Carrier) ∈ (M.toricChart upper v).source ∧
      ∀ i, ‖M.toricChart upper v (p : M.Carrier) i‖ ≤ 1
  position_mem_dilation : ∀ p upper v, p ∈ region (upper, v) → M.t p ≠ 0 →
    rescaledPosition M p ∈ a2TriangleDilation upper v
      (Real.log 2 / |Real.log r|)

/-- The explicit `A₂` affine charts supply the bounded polydisc regions of Lemma 4.4. -/
public noncomputable def standardBoundedPolydiscRegions
    (M : Model) (r : ℝ) (hr : 0 < r) (hrone : r < 1) :
    BoundedPolydiscRegions M r where
  radius_pos := hr
  radius_lt_one := hrone
  region a :=
    ⟨Subtype.val ⁻¹' openToricPolydisc M a.1 a.2 2,
      (open_openToricPolydisc M a.1 a.2 2).preimage continuous_subtype_val⟩
  region_mem_iff p upper v := by
    change (p : M.Carrier) ∈ openToricPolydisc M upper v 2 ↔ _
    rw [openToricPolydisc]
    exact and_congr_right fun _ ↦ mem_openCoordinatePolydisc_iff _ _
  closedUnit_cover p := by
    exact exists_closedUnitToricPolydisc M
      ((mem_ball_zero_iff.mp p.property).trans hrone)
  position_mem_dilation p upper v hpregion hpt i := by
    change (p : M.Carrier) ∈ openToricPolydisc M upper v 2 at hpregion
    have hpdata : (p : M.Carrier) ∈ (M.toricChart upper v).source ∧
        ∀ j, ‖M.toricChart upper v (p : M.Carrier) j‖ < 2 := by
      rw [openToricPolydisc] at hpregion
      exact ⟨hpregion.1, (mem_openCoordinatePolydisc_iff _ _).1 hpregion.2⟩
    have htnorm : ‖M.t p‖ < 1 := (mem_ball_zero_iff.mp p.property).trans hrone
    have htnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hpt
    have hlogt_neg : Real.log ‖M.t p‖ < 0 := Real.log_neg htnorm_pos htnorm
    have hlogr_neg : Real.log r < 0 := Real.log_neg hr hrone
    have habslogr_pos : 0 < |Real.log r| := abs_pos.mpr (ne_of_lt hlogr_neg)
    have habslogt_pos : 0 < |Real.log ‖M.t p‖| := abs_pos.mpr (ne_of_lt hlogt_neg)
    have hlog_lt : Real.log ‖M.t p‖ < Real.log r := by
      exact Real.strictMonoOn_log htnorm_pos hr (mem_ball_zero_iff.mp p.property)
    have habslog_le : |Real.log r| ≤ |Real.log ‖M.t p‖| := by
      rw [abs_of_neg hlogr_neg, abs_of_neg hlogt_neg]
      linarith
    have hratio : Real.log 2 / |Real.log ‖M.t p‖| ≤
        Real.log 2 / |Real.log r| :=
      div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) habslogr_pos habslog_le
    have hcoord_ne : M.toricChart upper v (p : M.Carrier) i ≠ 0 := by
      have htchart := M.toricChart_t upper v (p : M.Carrier) hpdata.1
      have hprod : M.toricChart upper v (p : M.Carrier) 0 *
          M.toricChart upper v (p : M.Carrier) 1 *
            M.toricChart upper v (p : M.Carrier) 2 ≠ 0 := by
        rw [← htchart]
        exact hpt
      have h01 := (mul_ne_zero_iff.mp hprod).1
      have h0 := (mul_ne_zero_iff.mp h01).1
      have h1 := (mul_ne_zero_iff.mp h01).2
      have h2 := (mul_ne_zero_iff.mp hprod).2
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hcoordlog : Real.log ‖M.toricChart upper v (p : M.Carrier) i‖ <
        Real.log 2 :=
      Real.strictMonoOn_log (norm_pos_iff.mpr hcoord_ne) (by norm_num) (hpdata.2 i)
    rw [log_norm_toricChart M hpt htnorm upper v i] at hcoordlog
    have htheta : -(Real.log 2 / |Real.log ‖M.t p‖|) <
        a2Barycentric upper v (rescaledPosition M p) i := by
      rw [← neg_div]
      apply (div_lt_iff₀ habslogt_pos).2
      rw [abs_of_neg hlogt_neg]
      nlinarith
    linarith

namespace BoundedPolydiscRegions

variable {M : Model} {r : ℝ}

public theorem cover (R : BoundedPolydiscRegions M r) (p : LocalCarrier M r) :
    ∃ a, p ∈ R.region a := by
  obtain ⟨upper, v, hp, hcoord⟩ := R.closedUnit_cover p
  refine ⟨(upper, v), (R.region_mem_iff p upper v).2 ⟨hp, ?_⟩⟩
  intro i
  exact (hcoord i).trans_lt (by norm_num)

public theorem position_bounded (R : BoundedPolydiscRegions M r) :
    ∀ a, ∃ B : ℝ, ∀ p ∈ R.region a,
      M.t p ≠ 0 → positionL1 (rescaledPosition M p) ≤ B := by
  rintro ⟨upper, v⟩
  have heta : 0 ≤ Real.log 2 / |Real.log r| :=
    div_nonneg (Real.log_nonneg (by norm_num)) (abs_nonneg _)
  obtain ⟨B, hB⟩ := exists_positionL1_bound_a2TriangleDilation upper v heta
  refine ⟨B, fun p hp hpt ↦ hB _ ?_⟩
  exact R.position_mem_dilation p upper v hp hpt

/-- Any uniform positive lower bound for rescaled-position displacement turns the standard
bounded polydiscs into the exact quantitative region cover used by Step 3. -/
public def toQuantitativeToricRegionCover
    (R : BoundedPolydiscRegions M r)
    (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hdisplacement : ∃ c : ℝ, 0 < c ∧ ∀ lambda (p : LocalCarrier M r),
      M.t p ≠ 0 →
        c * latticeL1 lambda ≤
          positionL1 (rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p)) :
    QuantitativeToricRegionCover C where
  region a := R.region a
  region_isOpen a := (R.region a).isOpen
  cover := R.cover
  position p := rescaledPosition M p
  region_position_bounded := R.position_bounded
  displacement_lower := hdisplacement

open SphereSixComplex.Periods

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}

/-- The actual phase coefficients admit a quantitative toric-region cover after shrinking the
cusp disc. -/
public theorem exists_actual_quantitativeToricRegionCover
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hradius : r ≤ cuspRadius N.height,
      Nonempty (QuantitativeToricRegionCover
        (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
          N M r hr hradius)) := by
  let rho := cuspRadius N.height / 2
  have hrho_pos : 0 < rho := div_pos (cuspRadius_pos N.height) (by norm_num)
  have hrho_lt : rho < cuspRadius N.height := by
    dsimp [rho]
    linarith [cuspRadius_pos N.height]
  obtain ⟨A, hA, hR⟩ :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exists_phaseLogMatrix_bound
      N hrho_lt
  let r := min rho (Real.exp (-(4 * A + 1)))
  have hr : 0 < r := lt_min hrho_pos (Real.exp_pos _)
  have hradius : r ≤ cuspRadius N.height :=
    (min_le_left _ _).trans (le_of_lt hrho_lt)
  have hrexp_lt : Real.exp (-(4 * A + 1)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hrone : r < 1 := (min_le_right _ _).trans_lt hrexp_lt
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M r hr hradius
  have hentry : ∀ (p : LocalCarrier M r), M.t p ≠ 0 → ∀ lambda i,
      |(CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
        N (M.t p)).mulVec
          (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter
            lambda) i| ≤ A * latticeL1 lambda := by
    intro p _hp lambda i
    have hpball : ‖M.t p‖ < r := mem_ball_zero_iff.mp p.property
    have hq : M.t p ∈ Metric.closedBall (0 : ℂ) rho := by
      rw [mem_closedBall_zero_iff]
      exact (le_of_lt hpball).trans (min_le_left _ _)
    simpa only [latticeL1,
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.parameterL1] using
        CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLog_mulVec_le
          N (hR (M.t p) hq) lambda i
  have hlog : ∀ (p : LocalCarrier M r), M.t p ≠ 0 →
      4 * A ≤ |Real.log ‖M.t p‖| := by
    intro p hp
    have hpball : ‖M.t p‖ < r := mem_ball_zero_iff.mp p.property
    have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
    have hnorm_exp : ‖M.t p‖ < Real.exp (-(4 * A + 1)) :=
      hpball.trans_le (min_le_right _ _)
    have hlog_lt := Real.strictMonoOn_log hnorm_pos (Real.exp_pos _) hnorm_exp
    rw [Real.log_exp] at hlog_lt
    have hlog_neg : Real.log ‖M.t p‖ < 0 := by
      linarith
    rw [abs_of_neg hlog_neg]
    linarith
  have hdisplacement : ∃ c : ℝ, 0 < c ∧ ∀ lambda (p : LocalCarrier M r),
      M.t p ≠ 0 →
        c * latticeL1 lambda ≤
          positionL1 (rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    exact CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.rescaledPosition_displacement_lower
      N M hrone C rfl hentry hlog
  exact ⟨r, hr, hradius,
    ⟨(standardBoundedPolydiscRegions M r hr hrone).toQuantitativeToricRegionCover
      C hdisplacement⟩⟩

/-- The resulting actual phase-corrected action satisfies the compact-overlap estimate. -/
public theorem exists_actual_compactOverlapEstimate
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hradius : r ≤ cuspRadius N.height,
      (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M r hr hradius).CompactOverlapEstimate := by
  obtain ⟨r, hr, hradius, ⟨Q⟩⟩ := exists_actual_quantitativeToricRegionCover N M
  exact ⟨r, hr, hradius, Q.compactOverlapEstimate⟩

/-- A single shrunk cusp radius carrying both estimates required by the local quotient. -/
public structure ActualLocalCuspQuotientWitness
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ cuspRadius N.height
  radius_lt_one : radius < 1
  phaseBound : ℝ
  phaseBound_nonneg : 0 ≤ phaseBound
  phaseLogMatrix_entry_bound : ∀ (p : LocalCarrier M radius) i j,
    |CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
      N (M.t p) i j| ≤ phaseBound
  phaseLog_dominates : ∀ (p : LocalCarrier M radius), M.t p ≠ 0 →
    4 * phaseBound ≤ |Real.log ‖M.t p‖|
  fixedPoint :
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M radius radius_pos radius_le).FixedPointEstimates
  compactOverlap :
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M radius radius_pos radius_le).CompactOverlapEstimate

/-- The compact-overlap shrink `exp (-(4A+1))` is already small enough for the `2A`
fixed-point estimate, so both conclusions are obtained at one radius. -/
public theorem exists_actualLocalCuspQuotientWitness
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model)
    (Q : TorusActionPreservesComponents M) :
    Nonempty (ActualLocalCuspQuotientWitness N M) := by
  let rho := cuspRadius N.height / 2
  have hrho_pos : 0 < rho := div_pos (cuspRadius_pos N.height) (by norm_num)
  have hrho_lt : rho < cuspRadius N.height := by
    dsimp [rho]
    linarith [cuspRadius_pos N.height]
  obtain ⟨A, hA, hR⟩ :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exists_phaseLogMatrix_bound
      N hrho_lt
  let r := min rho (Real.exp (-(4 * A + 1)))
  have hr : 0 < r := lt_min hrho_pos (Real.exp_pos _)
  have hradius : r ≤ cuspRadius N.height :=
    (min_le_left _ _).trans (le_of_lt hrho_lt)
  have hrexp_lt : Real.exp (-(4 * A + 1)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hrone : r < 1 := (min_le_right _ _).trans_lt hrexp_lt
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M r hr hradius
  have hentry : ∀ (p : LocalCarrier M r), M.t p ≠ 0 → ∀ lambda i,
      |(CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLogMatrix
        N (M.t p)).mulVec
          (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.realParameter
            lambda) i| ≤ A * latticeL1 lambda := by
    intro p _hp lambda i
    have hpball : ‖M.t p‖ < r := mem_ball_zero_iff.mp p.property
    have hq : M.t p ∈ Metric.closedBall (0 : ℂ) rho := by
      rw [mem_closedBall_zero_iff]
      exact (le_of_lt hpball).trans (min_le_left _ _)
    simpa only [latticeL1,
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.parameterL1] using
        CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseLog_mulVec_le
          N (hR (M.t p) hq) lambda i
  have hlog : ∀ (p : LocalCarrier M r), M.t p ≠ 0 →
      4 * A ≤ |Real.log ‖M.t p‖| := by
    intro p hp
    have hpball : ‖M.t p‖ < r := mem_ball_zero_iff.mp p.property
    have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr hp
    have hnorm_exp : ‖M.t p‖ < Real.exp (-(4 * A + 1)) :=
      hpball.trans_le (min_le_right _ _)
    have hlog_lt := Real.strictMonoOn_log hnorm_pos (Real.exp_pos _) hnorm_exp
    rw [Real.log_exp] at hlog_lt
    have hlog_neg : Real.log ‖M.t p‖ < 0 := by linarith
    rw [abs_of_neg hlog_neg]
    linarith
  have hfixed : C.FixedPointEstimates := by
    constructor
    · intro lambda p ht hfixed
      have hpball : ‖M.t p‖ < r := mem_ball_zero_iff.mp p.property
      have hq : M.t p ∈ Metric.closedBall (0 : ℂ) rho := by
        rw [mem_closedBall_zero_iff]
        exact (le_of_lt hpball).trans (min_le_left _ _)
      have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr ht
      have hnorm_lt : ‖M.t p‖ < 1 := hpball.trans hrone
      have habslog_pos : 0 < |Real.log ‖M.t p‖| := by
        exact abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hnorm_pos (ne_of_lt hnorm_lt))
      have hdominates : 2 * A < |Real.log ‖M.t p‖| := by
        nlinarith [hlog p ht]
      exact
        CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.offCentral_fixedPoint_of_log_dominates
          N M C rfl hR lambda p hq hdominates ht hfixed
    · intro lambda p ht hfixed
      exact
        CuspPhaseEstimates.CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.central_fixedPointEstimate
          C Q lambda p ht hfixed
  have hdisplacement : ∃ c : ℝ, 0 < c ∧ ∀ lambda (p : LocalCarrier M r),
      M.t p ≠ 0 →
        c * latticeL1 lambda ≤
          positionL1 (rescaledPosition M (C.psiMap lambda p) - rescaledPosition M p) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    exact CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.rescaledPosition_displacement_lower
      N M hrone C rfl hentry hlog
  let R := standardBoundedPolydiscRegions M r hr hrone
  let T : QuantitativeToricRegionCover C := R.toQuantitativeToricRegionCover C hdisplacement
  refine ⟨⟨r, hr, hradius, hrone, A, hA, ?_, hlog, hfixed,
    T.compactOverlapEstimate⟩⟩
  intro p i j
  apply hR
  rw [mem_closedBall_zero_iff]
  exact (le_of_lt (mem_ball_zero_iff.mp p.property)).trans (min_le_left _ _)

namespace ActualLocalCuspQuotientWitness

variable {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

public theorem quotient_isQuotientCoveringMap
    (W : ActualLocalCuspQuotientWitness N M) :
    let C :=
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.radius W.radius_pos W.radius_le
    letI := (C.toCuspActionData W.fixedPoint).psiAction
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel
        (Multiplicative ParameterLattice) (LocalCarrier M W.radius)))
      (Multiplicative ParameterLattice) := by
  exact CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.quotient_isQuotientCoveringMap
    _ W.fixedPoint W.compactOverlap

public theorem quotient_chartedSpace
    (W : ActualLocalCuspQuotientWitness N M) :
    let C :=
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.radius W.radius_pos W.radius_le
    letI := (C.toCuspActionData W.fixedPoint).psiAction
    Nonempty (ChartedSpace ComplexModel
      (MulAction.orbitRel.Quotient
        (Multiplicative ParameterLattice) (LocalCarrier M W.radius))) := by
  exact CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.quotient_chartedSpace
    _ W.fixedPoint W.compactOverlap

public theorem quotient_isManifold
    (W : ActualLocalCuspQuotientWitness N M) :
    let C :=
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.radius W.radius_pos W.radius_le
    letI := (C.toCuspActionData W.fixedPoint).psiAction
    let hf := C.quotient_isQuotientCoveringMap W.fixedPoint W.compactOverlap
    letI : ChartedSpace ComplexModel
      (MulAction.orbitRel.Quotient
        (Multiplicative ParameterLattice) (LocalCarrier M W.radius)) :=
      hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective
    IsManifold (modelWithCornersSelf ℂ ComplexModel) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (MulAction.orbitRel.Quotient
        (Multiplicative ParameterLattice) (LocalCarrier M W.radius)) :=
  CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.quotient_isManifold
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.radius W.radius_pos W.radius_le) W.fixedPoint W.compactOverlap

end ActualLocalCuspQuotientWitness

namespace Established

/-- The established standard infinite `A₂` model therefore carries the complete local cusp
quotient witness at one shrunk radius. -/
public theorem exists_model_with_actualLocalCuspQuotientWitness
    (N : NormalizedFuchsianCuspCoordinate E D) :
    ∃ M : Model, Nonempty (ActualLocalCuspQuotientWitness N M) := by
  obtain ⟨M, Q⟩ :=
    StandardInfiniteA2ToricModel.Established.exists_model_and_torusActionPreservesComponents
  exact ⟨M, exists_actualLocalCuspQuotientWitness N M Q⟩

end Established

end BoundedPolydiscRegions

end SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions
