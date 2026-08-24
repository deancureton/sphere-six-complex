module

public import SphereSixComplex.Periods.Uniformization.ScalarMonodromyAssembly
import all SphereSixComplex.Periods.Uniformization.ScalarMonodromyAssembly
public import SphereSixComplex.Periods.Uniformization.ScalarFundamentalConsistency
import all SphereSixComplex.Periods.Uniformization.ScalarFundamentalConsistency
public import SphereSixComplex.Periods.Uniformization.SourceAutomaticExactAssembly
import all SphereSixComplex.Periods.Uniformization.SourceAutomaticExactAssembly

@[expose] public section

/-!
# Exact scalar data directly from the monodromy branch

The orbit-choice scalar is useful for stating the algebraic effect of fundamental-polygon
consistency, but it is not needed once analytic continuation of the chamber germ has been
constructed.  This file starts the shorter direct route: the global branch supplied by Tau
Ceti obeys the three Schwarz laws on the upper half-plane, hence is invariant under the whole
source triangle group without extending those laws to the lower half-plane.
-/

open Complex Set UpperHalfPlane
open scoped ComplexConjugate

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections
open SphereSixComplex.Periods.SourceAutomaticExactAssembly

namespace MonodromyScalarBranch

variable {S : ChamberCaratheodorySeed sourceBoundedChamber} (B : MonodromyScalarBranch S)

private theorem sourceCircle_mem_sourceUpperHalfPlaneSet (z : UpperHalfPlane) :
    sourceCircle (z : ℂ) ∈ sourceUpperHalfPlaneSet := by
  change 0 < (sourceCircle (z : ℂ)).im
  rw [sourceCircle_im]
  exact div_pos z.im_pos z.normSq_pos

/-- The continued scalar is invariant under the order-three generator. -/
theorem invariant_g₁ : ScalarInvariant B.scalar g₁ := by
  intro z
  have hprod := congrArg ((↑) : UpperHalfPlane → ℂ) (sourceRight_sourceCircle z)
  calc
    B.scalar (((fuchsianSourceAction g₁ • z : UpperHalfPlane) : ℂ)) =
        B.scalar (sourceRight (sourceCircle (z : ℂ))) :=
      congrArg B.scalar hprod.symm
    _ = (starRingEnd ℂ) (B.scalar (sourceCircle (z : ℂ))) :=
      B.reflection_right (sourceCircle_mem_sourceUpperHalfPlaneSet z)
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (B.scalar (z : ℂ))) :=
      congrArg (starRingEnd ℂ) (B.reflection_circle z.im_pos)
    _ = B.scalar (z : ℂ) := starRingEnd_self_apply (R := ℂ) _

/-- The continued scalar is invariant under the order-four generator. -/
theorem invariant_g₂ : ScalarInvariant B.scalar g₂ := by
  intro z
  have hprod := congrArg ((↑) : UpperHalfPlane → ℂ) (sourceCircle_sourceLeft z)
  calc
    B.scalar (((fuchsianSourceAction g₂ • z : UpperHalfPlane) : ℂ)) =
        B.scalar (sourceCircle (sourceLeft (z : ℂ))) :=
      congrArg B.scalar hprod.symm
    _ = (starRingEnd ℂ) (B.scalar (sourceLeft (z : ℂ))) :=
      B.reflection_circle (by
        change 0 < (sourceLeft (z : ℂ)).im
        simpa using z.im_pos)
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (B.scalar (z : ℂ))) :=
      congrArg (starRingEnd ℂ) (B.reflection_left (by
        change 0 < (z : ℂ).im
        exact z.im_pos))
    _ = B.scalar (z : ℂ) := starRingEnd_self_apply (R := ℂ) _

/-- The continued scalar is invariant under the entire source triangle group. -/
theorem invariant (g : Delta) : ScalarInvariant B.scalar g :=
  scalarInvariant_all B.scalar B.invariant_g₁ B.invariant_g₂ g

/-! ## Agreement on the closed source chamber -/

/-- The finite closed source chamber, expressed in the ambient complex plane. -/
def sourceFiniteClosedChamber : Set ℂ :=
  {z | -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧
    0 < z.im ∧ 1 ≤ normSq z}

private theorem re_sq_le_half_of_mem_sourceFiniteClosedChamber {z : ℂ}
    (hz : z ∈ sourceFiniteClosedChamber) : z.re ^ 2 ≤ 1 / 2 := by
  change -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧
    0 < z.im ∧ 1 ≤ normSq z at hz
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rcases le_total z.re 0 with hre | hre
  · have hmul : 0 ≤ (z.re + Real.sqrt 2 / 2) * (-z.re + Real.sqrt 2 / 2) :=
      mul_nonneg (by linarith [hz.1]) (by linarith)
    nlinarith
  · have hmul : 0 ≤ z.re * (1 / 2 - z.re) :=
      mul_nonneg hre (sub_nonneg.mpr hz.2.1)
    nlinarith

private theorem re_sq_lt_im_of_mem_sourceFiniteClosedChamber {z : ℂ}
    (hz : z ∈ sourceFiniteClosedChamber) : z.re ^ 2 < z.im := by
  change -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧
    0 < z.im ∧ 1 ≤ normSq z at hz
  have hx2 := re_sq_le_half_of_mem_sourceFiniteClosedChamber hz
  have hy2 : 1 / 2 ≤ z.im ^ 2 := by
    rw [normSq_apply] at hz
    nlinarith [hz.2.2.2]
  by_contra h
  have hy_le : z.im ≤ z.re ^ 2 := le_of_not_gt h
  have hy_half : z.im ≤ 1 / 2 := hy_le.trans hx2
  have hmul : 0 ≤ z.im * (1 / 2 - z.im) :=
    mul_nonneg hz.2.2.1.le (sub_nonneg.mpr hy_half)
  nlinarith

/-- The open source chamber is dense in its finite closed version. -/
theorem sourceFiniteClosedChamber_subset_closure_sourceOpenChamber :
    sourceFiniteClosedChamber ⊆ closure sourceOpenChamber := by
  intro z hz
  change -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧
    0 < z.im ∧ 1 ≤ normSq z at hz
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let δ : ℝ := min (ε / (2 * (|z.re| + 1))) (1 / 2)
  let w : ℂ := (((1 - δ) * z.re : ℝ) : ℂ) +
    ((z.im + δ : ℝ) : ℂ) * Complex.I
  have hden : 0 < 2 * (|z.re| + 1) := by positivity
  have hδpos : 0 < δ := lt_min (div_pos hε hden) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδone : δ < 1 := lt_of_le_of_lt hδhalf (by norm_num)
  have hwre : w.re = (1 - δ) * z.re := by simp [w]
  have hwim : w.im = z.im + δ := by simp [w]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hleft : -Real.sqrt 2 / 2 < w.re := by
    rw [hwre]
    rcases lt_or_ge z.re 0 with hzneg | hznonneg
    · have hdx : 0 < -δ * z.re :=
        mul_pos_of_neg_of_neg (neg_neg_of_pos hδpos) hzneg
      nlinarith [hz.1]
    · have hfac : 0 ≤ 1 - δ := sub_nonneg.mpr hδone.le
      have : 0 ≤ (1 - δ) * z.re := mul_nonneg hfac hznonneg
      nlinarith
  have hright : w.re < 1 / 2 := by
    rw [hwre]
    rcases le_or_gt z.re 0 with hznonpos | hzpos
    · have hfac : 0 ≤ 1 - δ := sub_nonneg.mpr hδone.le
      have : (1 - δ) * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hfac hznonpos
      linarith
    · have hdx : 0 < δ * z.re := mul_pos hδpos hzpos
      nlinarith [hz.2.1]
  have hnorm : 1 < normSq w := by
    rw [normSq_apply, hwre, hwim]
    have hyx := re_sq_lt_im_of_mem_sourceFiniteClosedChamber hz
    have hzNorm := hz.2.2.2
    rw [normSq_apply] at hzNorm
    have hgain : 0 < δ * (2 * (z.im - z.re ^ 2) + δ * (z.re ^ 2 + 1)) := by
      apply mul_pos hδpos
      have hfirst : 0 < 2 * (z.im - z.re ^ 2) := mul_pos (by norm_num) (sub_pos.mpr hyx)
      have hsecond : 0 ≤ δ * (z.re ^ 2 + 1) := by positivity
      linarith
    nlinarith
  refine ⟨w, ⟨hleft, hright, by rw [hwim]; exact add_pos hz.2.2.1 hδpos, hnorm⟩, ?_⟩
  rw [dist_eq]
  have hdiff : z - w = (((δ * z.re : ℝ) : ℂ) - (δ : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [w] <;> ring
  rw [hdiff]
  calc
    ‖((δ * z.re : ℝ) : ℂ) - (δ : ℂ) * Complex.I‖ ≤
        ‖((δ * z.re : ℝ) : ℂ)‖ + ‖(δ : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = δ * (|z.re| + 1) := by
      rw [norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hδpos,
        norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hδpos, norm_I]
      ring
    _ ≤ (ε / (2 * (|z.re| + 1))) * (|z.re| + 1) := by
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

private theorem cuspExponential_mapsTo_sourceFiniteClosedChamber :
    MapsTo (cuspExponential (1 + Real.sqrt 2)) sourceFiniteClosedChamber
      (closure sourceBoundedChamber \ {sourceCuspVertex}) := by
  intro z hz
  change -Real.sqrt 2 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧
    0 < z.im ∧ 1 ≤ normSq z at hz
  refine ⟨?_, ?_⟩
  · by_cases hcircle : normSq z = 1
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_circleSide hz.1 hz.2.1
          hz.2.2.1 hcircle)
    have hn : 1 < normSq z := lt_of_le_of_ne hz.2.2.2 (Ne.symm hcircle)
    by_cases hleft : z.re = -Real.sqrt 2 / 2
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_leftSide hleft hz.2.2.1 hn)
    by_cases hright : z.re = 1 / 2
    · exact frontier_subset_closure
        (cuspExponential_mem_source_frontier_of_rightSide hright hz.2.2.1 hn)
    apply subset_closure
    exact ⟨z, ⟨lt_of_le_of_ne hz.1 (Ne.symm hleft),
      lt_of_le_of_ne hz.2.1 hright, hz.2.2.1, hn⟩, rfl⟩
  · simpa [sourceCuspVertex] using
      cuspExponential_ne_zero (1 + Real.sqrt 2) z

/-- The boundary-aware chamber seed is continuous at every finite point of the closed source
triangle. -/
theorem sourceScalarTriangleMap_continuousOn_sourceFiniteClosedChamber :
    ContinuousOn (sourceScalarTriangleMap S) sourceFiniteClosedChamber := by
  exact (sourceScalarClosureMap_continuousOn_away_cusp S).comp
    (cuspExponential_continuous (1 + Real.sqrt 2)).continuousOn
    cuspExponential_mapsTo_sourceFiniteClosedChamber

private theorem sourceOpenChamber_subset_sourceFiniteClosedChamber :
    sourceOpenChamber ⊆ sourceFiniteClosedChamber := by
  rintro z ⟨hl, hr, hi, hn⟩
  exact ⟨hl.le, hr.le, hi, hn.le⟩

/-- Agreement of the monodromy branch with the seed extends from the open chamber to its whole
finite closed triangle. -/
theorem eqOn_seed_sourceFiniteClosedChamber :
    EqOn B.scalar (sourceScalarTriangleMap S) sourceFiniteClosedChamber := by
  apply B.eqOn_seed.of_subset_closure
  · exact B.differentiableOn.continuousOn.mono fun z hz ↦ hz.2.2.1
  · exact sourceScalarTriangleMap_continuousOn_sourceFiniteClosedChamber (S := S)
  · exact sourceOpenChamber_subset_sourceFiniteClosedChamber
  · exact sourceFiniteClosedChamber_subset_closure_sourceOpenChamber

private theorem sourceRightUHP_mem_fundamentalTriangle_of_mem_right
    {z : UpperHalfPlane} (hz : z ∈ rightFundamentalTriangle) :
    sourceRightUHP z ∈ fundamentalTriangle := by
  rcases hz with ⟨hl, hr, hn⟩
  change 1 / 2 ≤ (z : ℂ).re at hl
  change (z : ℂ).re ≤ 1 + Real.sqrt 2 / 2 at hr
  refine ⟨?_, ?_, ?_⟩
  · change -Real.sqrt 2 / 2 ≤ (sourceRight (z : ℂ)).re
    rw [sourceRight_re]
    linarith
  · change (sourceRight (z : ℂ)).re ≤ 1 / 2
    rw [sourceRight_re]
    linarith
  · change 1 ≤ normSq (sourceRight (z : ℂ))
    have heq : normSq (sourceRight (z : ℂ)) = normSq (1 - (z : ℂ)) := by
      simp [sourceRight, normSq_apply]
    rwa [heq]

private theorem fundamentalTriangle_coe_mem_sourceFiniteClosedChamber
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle) :
    (z : ℂ) ∈ sourceFiniteClosedChamber := by
  exact ⟨hz.1, hz.2.1, z.im_pos, hz.2.2⟩

/-- The monodromy branch agrees with the explicit right Schwarz double on the entire closed
orientation-preserving fundamental region. -/
theorem eq_rightDouble_on_orientedFundamentalRegion
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion) :
    B.scalar (z : ℂ) = sourceScalarRightDoubleMap S (z : ℂ) := by
  rcases hz with hz | hz
  · have hseed := B.eqOn_seed_sourceFiniteClosedChamber
      (fundamentalTriangle_coe_mem_sourceFiniteClosedChamber hz)
    exact hseed.trans
      (sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1).symm
  · let u : UpperHalfPlane := sourceRightUHP z
    have hu : u ∈ fundamentalTriangle :=
      sourceRightUHP_mem_fundamentalTriangle_of_mem_right hz
    have hseed : B.scalar (u : ℂ) = sourceScalarTriangleMap S (u : ℂ) :=
      B.eqOn_seed_sourceFiniteClosedChamber
        (fundamentalTriangle_coe_mem_sourceFiniteClosedChamber hu)
    have hinv : sourceRight (u : ℂ) = (z : ℂ) := by
      change sourceRight (sourceRight (z : ℂ)) = (z : ℂ)
      exact sourceRight_involutive (z : ℂ)
    have hBreflect := B.reflection_right (z := (u : ℂ)) (by
      change 0 < (u : ℂ).im
      exact u.im_pos)
    have hRreflect := sourceScalarRightDoubleMap_reflected_fundamental_public S hu
    rw [hinv] at hBreflect hRreflect
    exact hBreflect.trans ((congrArg (starRingEnd ℂ) hseed).trans hRreflect.symm)

/-- Fundamental-polygon consistency is a consequence of the monodromy branch, not an additional
input to its global assembly. -/
theorem fundamentalScalarConsistent (B : MonodromyScalarBranch S) :
    SourceFundamentalScalarConsistent S := by
  intro z w hz hw horbit
  obtain ⟨g, hg⟩ := horbit
  have hinv := B.invariant g z
  rw [hg] at hinv
  calc
    sourceScalarRightDoubleMap S (z : ℂ) = B.scalar (z : ℂ) :=
      (B.eq_rightDouble_on_orientedFundamentalRegion hz).symm
    _ = B.scalar (w : ℂ) := hinv.symm
    _ = sourceScalarRightDoubleMap S (w : ℂ) :=
      B.eq_rightDouble_on_orientedFundamentalRegion hw

/-- The continued scalar has the full explicit fundamental-region range. -/
theorem surjective :
    Function.Surjective (fun z : UpperHalfPlane ↦ B.scalar (z : ℂ)) := by
  apply scalar_surjective_of_fundamental B.scalar
  intro q
  obtain ⟨z, hz, hq⟩ :=
    sourceScalarRightDoubleMap_surjective_on_orientedFundamentalRegion S q
  exact ⟨z, hz, (B.eq_rightDouble_on_orientedFundamentalRegion hz).trans hq⟩

/-- The continued scalar has exactly the source-group orbits as fibres. -/
theorem eq_iff_orbit (z w : UpperHalfPlane) :
    B.scalar (z : ℂ) = B.scalar (w : ℂ) ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w := by
  apply scalar_eq_iff_orbit_of_fundamental B.scalar B.invariant
  intro u v hu hv huv
  apply sourceScalarRightDoubleMap_fundamental_fibres S hu hv
  rw [← B.eq_rightDouble_on_orientedFundamentalRegion hu,
    ← B.eq_rightDouble_on_orientedFundamentalRegion hv]
  exact huv

theorem scalar_fuchsianOne : B.scalar (fuchsianOneFixedPoint : ℂ) = 0 := by
  rw [B.eqOn_seed_sourceFiniteClosedChamber
    (fundamentalTriangle_coe_mem_sourceFiniteClosedChamber
      fuchsianOneFixedPoint_mem_fundamentalTriangle)]
  exact sourceScalarTriangleMap_fuchsianOne S

theorem scalar_fuchsianTwo : B.scalar (fuchsianTwoFixedPoint : ℂ) = 1 := by
  rw [B.eqOn_seed_sourceFiniteClosedChamber
    (fundamentalTriangle_coe_mem_sourceFiniteClosedChamber
      fuchsianTwoFixedPoint_mem_fundamentalTriangle)]
  exact sourceScalarTriangleMap_fuchsianTwo S

/-- All non-cusp exact-coordinate data attached to the global monodromy branch. -/
noncomputable def toAutomaticSourceScalarCore :
    SphereSixComplex.Periods.SourceAutomaticExactAssembly.AutomaticSourceScalarCore where
  scalar := B.scalar
  scalar_holomorphic := B.differentiableOn
  scalar_invariant := fun g z ↦ B.invariant g z
  scalar_surjective := B.surjective
  scalar_eq_iff_orbit := B.eq_iff_orbit
  scalar_at_one := B.scalar_fuchsianOne
  scalar_at_two := B.scalar_fuchsianTwo

/-- Tau Ceti continuation of the chamber germ is sufficient, by itself, for the full exact
source coordinate.  The orbit-choice local-patch and translated-atlas interfaces are not
downstream hypotheses. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate
    (B : MonodromyScalarBranch S) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  exact AutomaticSourceScalarCore.nonempty_exactFuchsianOrbifoldCoordinate_of_seed
    B.toAutomaticSourceScalarCore S B.eqOn_seed


end MonodromyScalarBranch

/-- The exact shortest assembly theorem after the local analytic-continuation obligation has
been discharged. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate_of_seed_continuesInside
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (H : TauCeti.ContinuesInside (sourceScalarTriangleMap S)
      sourceUpperHalfPlaneSet sourceScalarContinuationBase) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  exact MonodromyScalarBranch.nonempty_exactFuchsianOrbifoldCoordinate
    (monodromyScalarBranchOfContinuesInside S H)


end SphereSixComplex.Periods.SourceChamberTopology
