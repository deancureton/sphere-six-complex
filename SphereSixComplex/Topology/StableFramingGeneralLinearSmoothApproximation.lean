module

public import SphereSixComplex.Topology.StableFramingBufferedRadialClutching
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Relative smooth approximation for rank-seven general-linear maps

A continuous `GL₇(ℝ)`-valued map which is already coefficientwise smooth near a closed set can
be approximated by a globally coefficientwise-smooth map without changing it on that set.  The
approximation is chosen closer than half the distance to the closed set of singular matrices, so
its values remain invertible.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousMap Set
open scoped Bundle ContDiff Manifold Topology

namespace SphereSixComplex

private abbrev StableSevenMatrix := Matrix (Fin 7) (Fin 7) ℝ

private abbrev StableSevenCoordinates := Fin 7 → Fin 7 → ℝ

/-- A coefficient of the linear automorphism is the corresponding transposed matrix entry. -/
public theorem StableGeneralLinearSeven.coeff_eq_matrixEntry
    (A : StableGeneralLinearSeven) (i j : Fin 7) :
    A.coeff i j = (A : Matrix (Fin 7) (Fin 7) ℝ) j i := by
  simp [StableGeneralLinearSeven.coeff, StableGeneralLinearSeven.toLinearEquiv,
    Matrix.GeneralLinearGroup.toLin]

private def singularStableSevenMatrices : Set StableSevenCoordinates :=
  {A | (Matrix.of A).det = 0}

private theorem singularStableSevenMatrices_isClosed :
    IsClosed singularStableSevenMatrices := by
  apply isClosed_singleton.preimage
  have hmatrix : Continuous (fun A : StableSevenCoordinates ↦ Matrix.of A) :=
    continuous_matrix fun i j ↦ (continuous_apply j).comp (continuous_apply i)
  exact hmatrix.matrix_det

private theorem singularStableSevenMatrices_nonempty :
    singularStableSevenMatrices.Nonempty := by
  refine ⟨0, ?_⟩
  change (Matrix.of (0 : StableSevenCoordinates)).det = 0
  simp

/-- Smooth a continuous `GL₇(ℝ)`-valued map relative to a closed set on whose neighborhood it is
already coefficientwise smooth. -/
public theorem exists_smoothGLSevenApprox_eqOn
    (K : C(ℝ × StableClutchingEquatorFiveSphere, StableGeneralLinearSeven))
    {S U : Set (ℝ × StableClutchingEquatorFiveSphere)}
    (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hKU : ∀ r c : Fin 7, ContMDiffOn
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ (K z : Matrix (Fin 7) (Fin 7) ℝ) r c) U) :
    ∃ L : C(ℝ × StableClutchingEquatorFiveSphere, StableGeneralLinearSeven),
      (∀ i j : Fin 7,
        ContMDiff
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) 𝓘(ℝ, ℝ) ∞
          (fun z ↦ (L z).coeff i j)) ∧
      EqOn L K S := by
  let Kval : ℝ × StableClutchingEquatorFiveSphere → StableSevenCoordinates :=
    fun z ↦ (K z : StableSevenMatrix)
  have approxData :
      ∃ a : ℝ × StableClutchingEquatorFiveSphere → StableSevenCoordinates,
        (∀ r c : Fin 7, ContMDiff
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) 𝓘(ℝ, ℝ) ∞
          (fun z ↦ a z r c)) ∧
        EqOn a Kval S ∧ ∀ z, (Matrix.of (a z)).det ≠ 0 := by
    have hKval : Continuous Kval := by
      have hval : Continuous (fun z ↦ (K z : StableSevenMatrix)) :=
        Units.continuous_val.comp K.continuous
      apply continuous_pi
      intro r
      apply continuous_pi
      intro c
      exact (continuous_apply c).comp ((continuous_apply r).comp hval)
    have hKUmat : ContMDiffOn
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5)))
        𝓘(ℝ, StableSevenCoordinates) ∞ Kval U := by
      rw [contMDiffOn_pi_space]
      intro r
      rw [contMDiffOn_pi_space]
      exact hKU r
    let ε : ℝ × StableClutchingEquatorFiveSphere → ℝ := fun z ↦
      Metric.infDist (Kval z) singularStableSevenMatrices / 2
    have hεcont : Continuous ε :=
      ((Metric.continuous_infDist_pt singularStableSevenMatrices).comp hKval).div_const 2
    have hεpos (z : ℝ × StableClutchingEquatorFiveSphere) : 0 < ε z := by
      apply div_pos
      · apply (singularStableSevenMatrices_isClosed.notMem_iff_infDist_pos
          singularStableSevenMatrices_nonempty).mp
        intro hz
        apply (K z).det_ne_zero
        change (Matrix.of (Kval z)).det = 0 at hz
        have hof : Matrix.of (Kval z) = (K z : StableSevenMatrix) := by
          apply Matrix.ext
          intro i j
          rfl
        rw [hof] at hz
        exact hz
      · norm_num
    obtain ⟨a, ha_approx, ha_eqOn, -⟩ :=
      hKval.exists_contMDiff_approx_and_eqOn
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) ⊤
        hεcont hεpos hS hU hKUmat
    have ha_det (z : ℝ × StableClutchingEquatorFiveSphere) :
        (Matrix.of (a z)).det ≠ 0 := by
      intro hz
      have hmem : a z ∈ singularStableSevenMatrices := hz
      have hle : Metric.infDist (Kval z) singularStableSevenMatrices ≤
          dist (Kval z) (a z) :=
        Metric.infDist_le_dist_of_mem (x := Kval z) hmem
      have hlt := ha_approx z
      change dist (a z) (Kval z) <
        Metric.infDist (Kval z) singularStableSevenMatrices / 2 at hlt
      rw [dist_comm] at hlt
      linarith [Metric.infDist_nonneg (x := Kval z) (s := singularStableSevenMatrices)]
    refine ⟨a, ?_, ha_eqOn, ha_det⟩
    intro r c
    exact contMDiff_pi_space.mp (contMDiff_pi_space.mp a.contMDiff r) c
  obtain ⟨a, ha_smooth, ha_eqOn, ha_det⟩ := approxData
  let amat (z : ℝ × StableClutchingEquatorFiveSphere) : StableSevenMatrix :=
    Matrix.of (a z)
  let lift (z : ℝ × StableClutchingEquatorFiveSphere) : StableGeneralLinearSeven :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (amat z) (ha_det z)
  have ha_cont : Continuous amat :=
    continuous_matrix fun r c ↦ (ha_smooth r c).continuous
  have ha_inv : Continuous
      (fun z ↦ @Inv.inv StableSevenMatrix Matrix.inv (amat z)) := by
    rw [continuous_iff_continuousAt]
    intro z
    apply (continuousAt_matrix_inv (amat z) ?_).comp ha_cont.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (ha_det z)
  have hlift : Continuous lift := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous amat
      exact ha_cont
    · convert ha_inv using 1
      funext z
      simp only [lift, Matrix.GeneralLinearGroup.coe_inv,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]
      rfl
  let L : C(ℝ × StableClutchingEquatorFiveSphere, StableGeneralLinearSeven) :=
    ⟨lift, hlift⟩
  refine ⟨L, ?_, ?_⟩
  · intro i j
    have hentry := ha_smooth j i
    simp_rw [StableGeneralLinearSeven.coeff_eq_matrixEntry]
    change ContMDiff
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 5))) 𝓘(ℝ, ℝ) ∞
      (fun z ↦ amat z j i)
    simpa only [amat, Matrix.of_apply] using hentry
  · intro z hz
    apply Units.ext
    change Matrix.of (a z) = (K z : StableSevenMatrix)
    apply Matrix.ext
    intro i j
    simpa only [Matrix.of_apply, Kval] using congrFun (congrFun (ha_eqOn hz) i) j

end SphereSixComplex
