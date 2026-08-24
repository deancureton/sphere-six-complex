module

public import SphereSixComplex.Geometry.CuspLocalPhaseAction
import all SphereSixComplex.LatticeData

/-!
# Quantitative cusp phase estimates

This file develops the numerical part of Theorem 4.5 from the actual descended correction matrix.
The remaining geometric input is isolated as the quantitative affine-chart statement of Lemma 4.4,
which is not contained in the current standard toric-model interface.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Geometry.CuspPhaseEstimates

open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

namespace CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

open SphereSixComplex.Periods

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D)

/-- The local action coefficients furnished by the actual cusp-period expansion. -/
public noncomputable def actualLocalPhaseCoefficients (M : Model) :
    ExactLocalHolomorphicPhaseCoefficients M (cuspRadius N.height) :=
  CuspLocalPhaseAction.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.toExactLocalHolomorphicPhaseCoefficients
    N M

/-- Restrict the actual cusp coefficients to any smaller positive disc. -/
public noncomputable def restrictedActualLocalPhaseCoefficients
    (M : Model) (r : ℝ) (hr : 0 < r) (hradius : r ≤ cuspRadius N.height) :
    ExactLocalHolomorphicPhaseCoefficients M r where
  radius_pos := hr
  phase := N.phaseCoefficient
  phase_zero := N.phaseCoefficient_zero
  phase_add := N.phaseCoefficient_add
  coefficient_holomorphicOn lambda i :=
    mdifferentiableOn_iff_differentiableOn.mp
      ((N.phaseCoefficient_holomorphicOn lambda i).mono fun _q hq ↦
        lt_of_lt_of_le hq hradius)

/-- The real matrix `R(q) = -2π Im C(q)` from §4.1. -/
public noncomputable def phaseLogMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j ↦ -2 * Real.pi * (N.correctionMatrix q i j).im

/-- The lattice parameter regarded as a real vector. -/
public def realParameter (lambda : ParameterLattice) : Fin 2 → ℝ :=
  fun i ↦ lambda i

public theorem realParameter_zero : realParameter 0 = 0 := by
  ext i
  simp [realParameter]

public theorem realParameter_add (lambda mu : ParameterLattice) :
    realParameter (lambda + mu) = realParameter lambda + realParameter mu := by
  ext i
  simp [realParameter]

/-- The logarithm of the modulus of the actual phase coefficient is exactly `R(q)λ`. -/
public theorem log_norm_phaseCoefficient
    (lambda : ParameterLattice) (q : ℂ) (i : Fin 2) :
    Real.log ‖(N.phaseCoefficient lambda q i : ℂ)‖ =
      (phaseLogMatrix N q).mulVec (realParameter lambda) i := by
  simp only [CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.phaseCoefficient,
    CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.exponentialUnit,
    Units.val_mk0, Complex.norm_exp, Real.log_exp]
  simp only [phaseLogMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, realParameter]
  fin_cases i <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Every entry of `R` is bounded on a strictly smaller closed cusp disc. -/
public theorem exists_phaseLogMatrix_entry_bound
    {rho : ℝ} (hrho : rho < cuspRadius N.height) (i j : Fin 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ q ∈ Metric.closedBall (0 : ℂ) rho,
      |phaseLogMatrix N q i j| ≤ A := by
  have hcont : ContinuousOn (fun q ↦ phaseLogMatrix N q i j)
      (Metric.closedBall (0 : ℂ) rho) := by
    apply ContinuousOn.const_mul
    exact Complex.continuous_im.comp_continuousOn
      (((N.correctionMatrix_entry_holomorphic i j).mono fun q hq ↦
        lt_of_le_of_lt hq hrho).continuousOn)
  obtain ⟨A, hA⟩ := (ProperSpace.isCompact_closedBall (0 : ℂ) rho)
    |>.exists_bound_of_continuousOn hcont
  refine ⟨max A 0, le_max_right _ _, fun q hq ↦ ?_⟩
  have h := hA q hq
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- The four entries of `R` admit one common bound on every strictly smaller closed cusp disc. -/
public theorem exists_phaseLogMatrix_bound
    {rho : ℝ} (hrho : rho < cuspRadius N.height) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ q ∈ Metric.closedBall (0 : ℂ) rho,
      ∀ i j, |phaseLogMatrix N q i j| ≤ A := by
  obtain ⟨A00, hA00, hb00⟩ := exists_phaseLogMatrix_entry_bound N hrho 0 0
  obtain ⟨A01, hA01, hb01⟩ := exists_phaseLogMatrix_entry_bound N hrho 0 1
  obtain ⟨A10, hA10, hb10⟩ := exists_phaseLogMatrix_entry_bound N hrho 1 0
  obtain ⟨A11, hA11, hb11⟩ := exists_phaseLogMatrix_entry_bound N hrho 1 1
  let A := max (max A00 A01) (max A10 A11)
  refine ⟨A, le_trans hA00 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro q hq i j
  fin_cases i <;> fin_cases j
  · exact (hb00 q hq).trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact (hb01 q hq).trans (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact (hb10 q hq).trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact (hb11 q hq).trans (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The elementary `ℓ¹` size of an integral cusp parameter. -/
public def parameterL1 (lambda : ParameterLattice) : ℝ :=
  |(lambda 0 : ℝ)| + |(lambda 1 : ℝ)|

public theorem parameterL1_nonneg (lambda : ParameterLattice) :
    0 ≤ parameterL1 lambda := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

public theorem parameterL1_eq_zero_iff (lambda : ParameterLattice) :
    parameterL1 lambda = 0 ↔ lambda = 0 := by
  constructor
  · intro h
    have h0 : |(lambda 0 : ℝ)| = 0 := by
      have hle : |(lambda 0 : ℝ)| ≤ 0 := by
        have := abs_nonneg (lambda 1 : ℝ)
        simp only [parameterL1] at h
        linarith
      exact le_antisymm hle (abs_nonneg _)
    have h1 : |(lambda 1 : ℝ)| = 0 := by
      have hle : |(lambda 1 : ℝ)| ≤ 0 := by
        have := abs_nonneg (lambda 0 : ℝ)
        simp only [parameterL1] at h
        linarith
      exact le_antisymm hle (abs_nonneg _)
    funext i
    fin_cases i
    · exact_mod_cast abs_eq_zero.mp h0
    · exact_mod_cast abs_eq_zero.mp h1
  · rintro rfl
    simp [parameterL1]

/-- The explicit integral matrix `B₀` preserves this elementary `ℓ¹` size. -/
public theorem shearVector_parameterL1 (lambda : ParameterLattice) :
    |(shearVector lambda 0 : ℝ)| + |(shearVector lambda 1 : ℝ)| =
      parameterL1 lambda := by
  simp [shearVector, SphereSixComplex.LatticeData.B₀, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, parameterL1, add_comm]

public theorem phaseLog_mulVec_le
    {A : ℝ} {q : ℂ}
    (hq : ∀ i j, |phaseLogMatrix N q i j| ≤ A)
    (lambda : ParameterLattice) (i : Fin 2) :
    |(phaseLogMatrix N q).mulVec (realParameter lambda) i| ≤
      A * parameterL1 lambda := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, realParameter]
  calc
    |phaseLogMatrix N q i 0 * (lambda 0 : ℝ) +
        phaseLogMatrix N q i 1 * (lambda 1 : ℝ)|
        ≤ |phaseLogMatrix N q i 0| * |(lambda 0 : ℝ)| +
          |phaseLogMatrix N q i 1| * |(lambda 1 : ℝ)| := by
            simpa [phaseLogMatrix, abs_mul] using
              abs_add_le ((phaseLogMatrix N q i 0) * (lambda 0 : ℝ))
                ((phaseLogMatrix N q i 1) * (lambda 1 : ℝ))
    _ ≤ A * |(lambda 0 : ℝ)| + A * |(lambda 1 : ℝ)| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hq i 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hq i 1) (abs_nonneg _))
    _ = A * parameterL1 lambda := by
      rw [parameterL1, mul_add]

end CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- The ray components containing a point of the standard toric model. -/
public def componentSupport (M : Model) (p : M.Carrier) : Set ToricLattice :=
  {v | p ∈ M.centralComponent v}

public theorem componentSupport_nonempty_of_t_eq_zero
    (M : Model) {p : M.Carrier} (hp : M.t p = 0) :
    (componentSupport M p).Nonempty := by
  have hp' : p ∈ M.t ⁻¹' ({0} : Set ℂ) := by
    simpa using hp
  rw [M.centralFiber_eq_iUnion] at hp'
  change ∃ v, p ∈ M.centralComponent v
  simpa only [Set.mem_iUnion] using hp'

/-- Only the three ray components of a selected maximal chart can contain a given point. -/
public theorem componentSupport_finite (M : Model) (p : M.Carrier) :
    (componentSupport M p).Finite := by
  obtain ⟨upper, v, hp⟩ := M.toricChart_cover p
  apply (Set.finite_range (a2Triangle upper v)).subset
  intro w hw
  by_contra hn
  exact Set.disjoint_left.mp (M.otherCentralComponent_disjoint_chart upper v w hn) hw hp

/-- A nonempty finite set in the lattice cannot be forward-invariant under a nonzero
translation. -/
public theorem translation_eq_zero_of_finite_forward_invariant
    {S : Set ToricLattice} {d : ToricLattice}
    (hS : S.Finite) (hne : S.Nonempty)
    (hforward : ∀ v ∈ S, v + d ∈ S) : d = 0 := by
  funext i
  obtain ⟨v, hv, hmax⟩ := Set.exists_max_image S (fun w ↦ w i) hS hne
  have hupper := hmax (v + d) (hforward v hv)
  obtain ⟨w, hw, hmin⟩ := Set.exists_max_image S (fun u ↦ -(u i)) hS hne
  have hlower := hmin (w + d) (hforward w hw)
  simp only [Pi.add_apply] at hupper hlower
  change d i = 0
  omega

/-- Standard orbit compatibility for the algebraic torus action.  This is the smallest toric
orbit fact absent from `StandardInfiniteA2ToricModel.Model` that is needed for the central-fibre
part of Theorem 4.5: multiplication by the dense torus preserves every ray orbit closure. -/
public structure TorusActionPreservesComponents (M : Model) : Prop where
  torusAction_component : ∀ g v p,
    M.torusAction g p ∈ M.centralComponent v ↔ p ∈ M.centralComponent v

namespace TorusActionPreservesComponents

variable {M : Model}

public theorem phaseAction_component (Q : TorusActionPreservesComponents M)
    (c : Phase) (v : ToricLattice) (p : M.Carrier) :
    CuspToricPhaseAction.ToricModel.phaseAction M c p ∈ M.centralComponent v ↔
      p ∈ M.centralComponent v :=
  TorusActionPreservesComponents.torusAction_component Q (phaseEmbedding c) v p

end TorusActionPreservesComponents

namespace CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients

variable {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)

/-- The central-fibre fixed-point estimate follows from the standard fact that torus
multiplication preserves ray components.  No analytic estimate is involved in this half of
Step 1 of Theorem 4.5. -/
public theorem central_fixedPointEstimate
    (Q : TorusActionPreservesComponents M) (lambda : ParameterLattice)
    (p : LocalCarrier M r) (ht : M.t p = 0) (hfixed : C.psiMap lambda p = p) :
    lambda = 0 := by
  have hsupport : (componentSupport M (p : M.Carrier)).Nonempty :=
    componentSupport_nonempty_of_t_eq_zero M ht
  have hforward : ∀ v ∈ componentSupport M (p : M.Carrier),
      v + shearVector lambda ∈ componentSupport M (p : M.Carrier) := by
    intro v hv
    have hshear : Additive.toMul (M.fanShear lambda) (p : M.Carrier) ∈
        M.centralComponent (v + shearVector lambda) := by
      rw [← M.fanShear_component lambda v]
      exact ⟨p, hv, rfl⟩
    have hphase := (TorusActionPreservesComponents.phaseAction_component Q
      (C.phase lambda (M.t p))
      (v + shearVector lambda)
      (Additive.toMul (M.fanShear lambda) (p : M.Carrier))).mpr hshear
    have hfixed' := congrArg Subtype.val hfixed
    rw [C.psiMap_coe] at hfixed'
    rw [hfixed'] at hphase
    exact hphase
  have hshear_zero : shearVector lambda = 0 :=
    translation_eq_zero_of_finite_forward_invariant
      (componentSupport_finite M p) hsupport hforward
  apply shearVector_injective
  simpa [shearVector] using hshear_zero

end CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients

namespace CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

open SphereSixComplex.Periods

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D)

/-- A fixed point away from the central fibre satisfies the logarithmic equation
`R(q)λ + log |q| B₀λ = 0` coordinatewise. -/
public theorem offCentral_logarithmic_equation
    (M : Model) {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hphase : C.phase = N.phaseCoefficient) (lambda : ParameterLattice)
    (p : LocalCarrier M r) (ht : M.t p ≠ 0)
    (hfixed : C.psiMap lambda p = p)
    (i : Fin 2) :
    (phaseLogMatrix N (M.t p)).mulVec (realParameter lambda) i +
      Real.log ‖M.t p‖ * (shearVector lambda i : ℝ) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, M.torusEmbedding x = (p : M.Carrier) := by
    have hp : (p : M.Carrier) ∈ {q | M.t q ≠ 0} := ht
    rw [← M.torus_range] at hp
    exact hp
  have hfixed' := congrArg Subtype.val hfixed
  rw [C.psiMap_coe] at hfixed'
  rw [← hx, M.fanShear_torus, M.t_torus,
    CuspToricPhaseAction.ToricModel.phaseAction_apply, M.torusAction_torus] at hfixed'
  rw [hphase] at hfixed'
  have htorus : phaseEmbedding (N.phaseCoefficient lambda (x 2 : ℂ)) *
      denseTorusShear lambda x = x :=
    M.torus_openEmbedding.injective hfixed'
  have hi := congrFun htorus i.castSucc
  have hi' : N.phaseCoefficient lambda (x 2 : ℂ) i *
      x 2 ^ shearVector lambda i = 1 := by
    fin_cases i
    · change N.phaseCoefficient lambda (x 2 : ℂ) 0 *
        (x 0 * x 2 ^ shearVector lambda 0) = x 0 at hi
      change N.phaseCoefficient lambda (x 2 : ℂ) 0 *
        x 2 ^ shearVector lambda 0 = 1
      apply mul_right_cancel (b := x 0)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hi
    · change N.phaseCoefficient lambda (x 2 : ℂ) 1 *
        (x 1 * x 2 ^ shearVector lambda 1) = x 1 at hi
      change N.phaseCoefficient lambda (x 2 : ℂ) 1 *
        x 2 ^ shearVector lambda 1 = 1
      apply mul_right_cancel (b := x 1)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hi
  have hnorm := congrArg (fun u : ℂˣ ↦ ‖(u : ℂ)‖) hi'
  simp only [Units.val_mul, norm_mul, Units.val_one, norm_one] at hnorm
  rw [show ((↑(x 2 ^ shearVector lambda i) : ℂ)) =
      (x 2 : ℂ) ^ shearVector lambda i by
        exact map_zpow (Units.coeHom ℂ) (x 2) (shearVector lambda i),
    norm_zpow] at hnorm
  have hlog := congrArg Real.log hnorm
  rw [Real.log_mul (ne_of_gt (Units.norm_pos _))
      (zpow_ne_zero _ (ne_of_gt (Units.norm_pos _))),
    Real.log_zpow, Real.log_one] at hlog
  rw [log_norm_phaseCoefficient] at hlog
  have htpx : M.t p = (x 2 : ℂ) := by
    rw [← hx, M.t_torus]
  rw [htpx]
  linarith

/-- The numerical contradiction in Step 1: once `|log |q||` dominates twice a common entry
bound for `R(q)`, an off-central fixed point has zero lattice parameter. -/
public theorem offCentral_fixedPoint_of_log_dominates
    (M : Model) {r rho A : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r)
    (hphase : C.phase = N.phaseCoefficient)
    (hR : ∀ q ∈ Metric.closedBall (0 : ℂ) rho,
      ∀ i j, |phaseLogMatrix N q i j| ≤ A)
    (lambda : ParameterLattice)
    (p : LocalCarrier M r)
    (hq : M.t p ∈ Metric.closedBall (0 : ℂ) rho)
    (hlog : 2 * A < |Real.log ‖M.t p‖|) (ht : M.t p ≠ 0)
    (hfixed : C.psiMap lambda p = p) :
    lambda = 0 := by
  let Rlambda := (phaseLogMatrix N (M.t p)).mulVec (realParameter lambda)
  have heq0 := offCentral_logarithmic_equation N M C hphase lambda p ht hfixed 0
  have heq1 := offCentral_logarithmic_equation N M C hphase lambda p ht hfixed 1
  have hR0 : |Rlambda 0| ≤ A * parameterL1 lambda := by
    exact phaseLog_mulVec_le N (hR (M.t p) hq) lambda 0
  have hR1 : |Rlambda 1| ≤ A * parameterL1 lambda := by
    exact phaseLog_mulVec_le N (hR (M.t p) hq) lambda 1
  have habs0 : |Real.log ‖M.t p‖| * |(shearVector lambda 0 : ℝ)| = |Rlambda 0| := by
    change Rlambda 0 + Real.log ‖M.t p‖ * (shearVector lambda 0 : ℝ) = 0 at heq0
    have h := congrArg abs (eq_neg_of_add_eq_zero_left heq0)
    simpa [abs_mul, mul_comm] using h.symm
  have habs1 : |Real.log ‖M.t p‖| * |(shearVector lambda 1 : ℝ)| = |Rlambda 1| := by
    change Rlambda 1 + Real.log ‖M.t p‖ * (shearVector lambda 1 : ℝ) = 0 at heq1
    have h := congrArg abs (eq_neg_of_add_eq_zero_left heq1)
    simpa [abs_mul, mul_comm] using h.symm
  have htotal : |Real.log ‖M.t p‖| * parameterL1 lambda ≤
      2 * A * parameterL1 lambda := by
    calc
      _ = |Real.log ‖M.t p‖| *
          (|(shearVector lambda 0 : ℝ)| + |(shearVector lambda 1 : ℝ)|) := by
            rw [shearVector_parameterL1]
      _ = |Real.log ‖M.t p‖| * |(shearVector lambda 0 : ℝ)| +
          |Real.log ‖M.t p‖| * |(shearVector lambda 1 : ℝ)| := by ring
      _ = |Rlambda 0| + |Rlambda 1| := by rw [habs0, habs1]
      _ ≤ A * parameterL1 lambda + A * parameterL1 lambda :=
        add_le_add hR0 hR1
      _ = 2 * A * parameterL1 lambda := by ring
  by_contra hlambda
  have hl1ne : parameterL1 lambda ≠ 0 :=
    fun h ↦ hlambda ((parameterL1_eq_zero_iff lambda).mp h)
  have hl1 : 0 < parameterL1 lambda :=
    lt_of_le_of_ne (parameterL1_nonneg lambda) hl1ne.symm
  exact (not_lt_of_ge htotal) (mul_lt_mul_of_pos_right hlog hl1)

/-- After shrinking the cusp disc, the actual phase-corrected action is free.  The off-central
part is the logarithmic estimate above; the central part uses only preservation of toric ray
components. -/
public theorem exists_shrunk_fixedPointEstimates
    (M : Model) (Q : TorusActionPreservesComponents M) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hradius : r ≤ cuspRadius N.height,
      (restrictedActualLocalPhaseCoefficients N M r hr hradius).FixedPointEstimates := by
  let rho := cuspRadius N.height / 2
  have hrho_pos : 0 < rho := div_pos (cuspRadius_pos N.height) (by norm_num)
  have hrho_lt : rho < cuspRadius N.height := by
    dsimp [rho]
    linarith [cuspRadius_pos N.height]
  obtain ⟨A, hA, hR⟩ := exists_phaseLogMatrix_bound N hrho_lt
  let r := min rho (Real.exp (-(2 * A + 1)))
  have hr_pos : 0 < r := lt_min hrho_pos (Real.exp_pos _)
  have hradius : r ≤ cuspRadius N.height :=
    (min_le_left _ _).trans (le_of_lt hrho_lt)
  refine ⟨r, hr_pos, hradius, ?_⟩
  let C := restrictedActualLocalPhaseCoefficients N M r hr_pos hradius
  change C.FixedPointEstimates
  constructor
  · intro lambda p ht hfixed
    have hpball : ‖M.t p‖ < r := mem_ball_zero_iff.mp p.property
    have hq : M.t p ∈ Metric.closedBall (0 : ℂ) rho := by
      rw [mem_closedBall_zero_iff]
      exact (le_of_lt hpball).trans (min_le_left _ _)
    have hnorm_pos : 0 < ‖M.t p‖ := norm_pos_iff.mpr ht
    have hnorm_exp : ‖M.t p‖ < Real.exp (-(2 * A + 1)) :=
      hpball.trans_le (min_le_right _ _)
    have hlog_lt := Real.strictMonoOn_log hnorm_pos (Real.exp_pos _) hnorm_exp
    rw [Real.log_exp] at hlog_lt
    have hlog_neg : Real.log ‖M.t p‖ < 0 := by linarith
    have hdominates : 2 * A < |Real.log ‖M.t p‖| := by
      rw [abs_of_neg hlog_neg]
      linarith
    exact offCentral_fixedPoint_of_log_dominates N M C rfl hR lambda p hq
      hdominates ht hfixed
  · intro lambda p ht hfixed
    exact
      SphereSixComplex.Geometry.CuspPhaseEstimates.CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.central_fixedPointEstimate
        C Q lambda p ht hfixed

end CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

/-- Indices for the two translated families of bounded affine regions in Lemma 4.4. -/
public abbrev ToricRegionIndex := Bool × ToricLattice

/-- The elementary `ℓ¹` size of a rescaled position vector. -/
public def positionL1 (y : Fin 2 → ℝ) : ℝ :=
  |y 0| + |y 1|

/-- The elementary `ℓ¹` size of an integral rank-two vector. -/
public def latticeL1 (lambda : ParameterLattice) : ℝ :=
  |(lambda 0 : ℝ)| + |(lambda 1 : ℝ)|

public theorem positionL1_nonneg (y : Fin 2 → ℝ) : 0 ≤ positionL1 y := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

public theorem positionL1_sub_le (y z : Fin 2 → ℝ) :
    positionL1 (y - z) ≤ positionL1 y + positionL1 z := by
  simp only [positionL1, Pi.sub_apply]
  linarith [abs_sub (y 0) (z 0), abs_sub (y 1) (z 1)]

/-- An `ℓ¹`-bounded subset of the integral rank-two lattice is finite. -/
public theorem latticeL1_sublevel_finite (B : ℝ) :
    {lambda : ParameterLattice | latticeL1 lambda ≤ B}.Finite := by
  let n : ℤ := ⌈B⌉
  apply (Set.Finite.pi' fun _ : Fin 2 ↦ Set.finite_Icc (-n) n).subset
  intro lambda hlambda i
  have hi : |(lambda i : ℝ)| ≤ B := by
    fin_cases i
    · exact (le_add_of_nonneg_right (abs_nonneg (lambda 1 : ℝ))).trans hlambda
    · exact (le_add_of_nonneg_left (abs_nonneg (lambda 0 : ℝ))).trans hlambda
  have hi' : |(lambda i : ℝ)| ≤ (n : ℝ) := hi.trans (Int.le_ceil B)
  constructor
  · exact_mod_cast (abs_le.mp hi').1
  · exact_mod_cast (abs_le.mp hi').2

/-- The nonzero fibres are dense in every open cusp neighbourhood. -/
public theorem offCentral_dense (M : Model) (r : ℝ) :
    Dense {p : LocalCarrier M r | M.t p ≠ 0} := by
  have htorus : Dense {p : M.Carrier | M.t p ≠ 0} := by
    rw [← M.torus_range]
    exact M.torus_dense
  exact htorus.preimage (cuspNeighborhood M r).isOpen.isOpenMap_subtype_val

/-- The exact quantitative content of Lemma 4.4 and Theorem 4.5, Step 2.  The open bounded
regions cover the cusp model.  Their rescaled positions are bounded chart by chart, while the
actual `B_t` estimate gives a uniform positive lower bound for the displacement of a nonzero
lattice parameter.

This formulation deliberately does not require a globally finite error for
`b - a - B₀ lambda`: the term `(B_t - B₀) lambda` need not be uniformly bounded as `lambda`
varies.  What the argument uses is finiteness of `lambda` for each fixed pair of bounded
regions. -/
public structure QuantitativeToricRegionCover
    {M : Model} {r : ℝ} (C : ExactLocalHolomorphicPhaseCoefficients M r) where
  region : ToricRegionIndex → Set (LocalCarrier M r)
  region_isOpen : ∀ a, IsOpen (region a)
  cover : ∀ p, ∃ a, p ∈ region a
  position : LocalCarrier M r → Fin 2 → ℝ
  region_position_bounded : ∀ a, ∃ B : ℝ, ∀ p ∈ region a,
    M.t p ≠ 0 → positionL1 (position p) ≤ B
  displacement_lower : ∃ c : ℝ, 0 < c ∧ ∀ lambda (p : LocalCarrier M r),
    M.t p ≠ 0 →
      c * latticeL1 lambda ≤ positionL1 (position (C.psiMap lambda p) - position p)

namespace QuantitativeToricRegionCover

variable {M : Model} {r : ℝ} {C : ExactLocalHolomorphicPhaseCoefficients M r}

/-- An overlap of a fixed pair of bounded regions is possible for only finitely many lattice
parameters.  Density of the nonzero fibres is what permits the `B_t` estimate to control an
overlap which may initially be witnessed on the central fibre. -/
public theorem chartPairOverlapFinite (Q : QuantitativeToricRegionCover C)
    (a b : ToricRegionIndex) :
    {lambda : ParameterLattice |
      (C.psiMap lambda '' Q.region a ∩ Q.region b).Nonempty}.Finite := by
  obtain ⟨A, hA⟩ := Q.region_position_bounded a
  obtain ⟨B, hB⟩ := Q.region_position_bounded b
  obtain ⟨c, hc, hdisplacement⟩ := Q.displacement_lower
  apply (latticeL1_sublevel_finite ((A + B) / c)).subset
  intro lambda hoverlap
  obtain ⟨q, ⟨p, hpa, hpq⟩, hqb⟩ := hoverlap
  let U := Q.region a ∩ C.psiMap lambda ⁻¹' Q.region b
  have hU_open : IsOpen U :=
    (Q.region_isOpen a).inter ((Q.region_isOpen b).preimage
      (C.psiMap_holomorphic lambda).continuous)
  have hU_nonempty : U.Nonempty := ⟨p, hpa, by simpa only [Set.mem_preimage, hpq] using hqb⟩
  obtain ⟨p', hp't, hp'U⟩ := (offCentral_dense M r).exists_mem_open hU_open hU_nonempty
  have hp'a : p' ∈ Q.region a := hp'U.1
  have hp'b : C.psiMap lambda p' ∈ Q.region b := hp'U.2
  have hp'qt : M.t (C.psiMap lambda p') ≠ 0 := by
    rw [C.psiMap_preserves_t]
    exact hp't
  have hupper : positionL1 (Q.position (C.psiMap lambda p') - Q.position p') ≤ A + B :=
    (positionL1_sub_le _ _).trans (by
      simpa only [add_comm] using add_le_add (hB _ hp'b hp'qt) (hA _ hp'a hp't))
  have hlower := hdisplacement lambda p' hp't
  apply (le_div_iff₀ hc).mpr
  simpa only [mul_comm] using hlower.trans hupper

/-- The bounded affine cover and fixed-chart-pair estimate prove the compact-overlap conclusion
of Theorem 4.5, Step 3. -/
public theorem compactOverlapEstimate (Q : QuantitativeToricRegionCover C) :
    C.CompactOverlapEstimate := by
  intro K L hK hL
  obtain ⟨IK, hIK⟩ := hK.elim_finite_subcover Q.region Q.region_isOpen fun p _ ↦ by
    obtain ⟨a, ha⟩ := Q.cover p
    exact Set.mem_iUnion.2 ⟨a, ha⟩
  obtain ⟨IL, hIL⟩ := hL.elim_finite_subcover Q.region Q.region_isOpen fun p _ ↦ by
    obtain ⟨a, ha⟩ := Q.cover p
    exact Set.mem_iUnion.2 ⟨a, ha⟩
  let pairOverlap : ToricRegionIndex × ToricRegionIndex → Set ParameterLattice :=
    fun ab ↦ {lambda | (C.psiMap lambda '' Q.region ab.1 ∩ Q.region ab.2).Nonempty}
  have hfinite : (⋃ ab ∈ IK ×ˢ IL, pairOverlap ab).Finite := by
    apply Set.Finite.biUnion (IK.product IL).finite_toSet
    intro ab hab
    exact Q.chartPairOverlapFinite ab.1 ab.2
  apply hfinite.subset
  intro lambda hoverlap
  obtain ⟨q, ⟨p, hpK, hpq⟩, hqL⟩ := hoverlap
  have hpcover := hIK hpK
  have hqcover := hIL hqL
  simp only [Set.mem_iUnion] at hpcover hqcover
  obtain ⟨a, haIK, hpa⟩ := hpcover
  obtain ⟨b, hbIL, hqb⟩ := hqcover
  have hab : (a, b) ∈ IK.product IL := Finset.mem_product.2 ⟨haIK, hbIL⟩
  refine Set.mem_iUnion.2 ⟨(a, b), Set.mem_iUnion.2 ⟨hab, ?_⟩⟩
  exact ⟨q, ⟨p, hpa, hpq⟩, hqb⟩

end QuantitativeToricRegionCover

end SphereSixComplex.Geometry.CuspPhaseEstimates
