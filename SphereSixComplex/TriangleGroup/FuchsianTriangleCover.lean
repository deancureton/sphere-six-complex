module

public import SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
public import SphereSixComplex.Periods.FuchsianCompactCore

/-!
# The orientation-preserving Fuchsian fundamental region

The triangle bounded by the order-three and order-four mirrors is a reflection chamber.  The
orientation-preserving group `C₃ * C₄` has a fundamental region consisting of two adjacent
reflection chambers.  This file proves the resulting translate cover and packages its compact
core for the period construction.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianTriangleCover

open Set SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTessellation
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The reflection chamber adjacent across the order-three mirror. -/
@[expose] public noncomputable def rightFundamentalTriangle : Set UpperHalfPlane :=
  {z | 1 / 2 ≤ z.re ∧ z.re ≤ 1 + Real.sqrt 2 / 2 ∧
    1 ≤ Complex.normSq (1 - (z : ℂ))}

/-- A fundamental region for the orientation-preserving `(3,4,∞)` group. -/
@[expose] public noncomputable def orientedFundamentalRegion : Set UpperHalfPlane :=
  fundamentalTriangle ∪ rightFundamentalTriangle

public theorem gOne_sq_im_eq_div_normSq_one_sub (z : UpperHalfPlane) :
    (fuchsianSourceAction (g₁ ^ 2) • z).im =
      z.im / Complex.normSq (1 - (z : ℂ)) := by
  have h := congrArg Complex.im (FuchsianPingPong.gOne_sq_apply z)
  rw [Complex.div_im] at h
  norm_num at h
  rw [map_pow, fuchsianSourceAction_g₁]
  change ((fuchsianOnePerm ^ 2) z).im = _
  rw [h]
  ring

public theorem normSq_one_sub_ge_one_of_orbitHeightMaximal {z : UpperHalfPlane}
    (hz : IsOrbitHeightMaximal z) : 1 ≤ Complex.normSq (1 - (z : ℂ)) := by
  have hdenom : 0 < Complex.normSq (1 - (z : ℂ)) := by
    rw [Complex.normSq_pos]
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    exact z.im_ne_zero him
  have hheight := hz (g₁ ^ 2)
  rw [gOne_sq_im_eq_div_normSq_one_sub] at hheight
  have hmul := (div_le_iff₀ hdenom).mp hheight
  nlinarith [z.im_pos]

public theorem maximal_coarse_mem_orientedFundamentalRegion {z : UpperHalfPlane}
    (hzMax : IsOrbitHeightMaximal z) (hzCoarse : z ∈ coarseFordRegion) :
    ∃ k : Delta, fuchsianSourceAction k • z ∈ orientedFundamentalRegion := by
  rcases hzCoarse with ⟨hzLower, hzUpper, hzNorm⟩
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  by_cases hzLeft : -Real.sqrt 2 / 2 ≤ z.re
  · by_cases hzRight : z.re ≤ 1 / 2
    · exact ⟨1, by simpa [orientedFundamentalRegion] using
        (Or.inl ⟨hzLeft, hzRight, hzNorm⟩ :
        z ∈ fundamentalTriangle ∪ rightFundamentalTriangle)⟩
    · have hzMem : z ∈ rightFundamentalTriangle :=
        ⟨le_of_not_ge hzRight, by
          unfold cuspWidth at hzUpper
          linarith, normSq_one_sub_ge_one_of_orbitHeightMaximal hzMax⟩
      exact ⟨1, by simpa [orientedFundamentalRegion] using
        (Or.inr hzMem : z ∈ fundamentalTriangle ∪ rightFundamentalTriangle)⟩
  · let w := fuchsianSourceAction (g₁ * g₂) • z
    have hwMax : IsOrbitHeightMaximal w := by
      simpa [w] using hzMax.product_zpow (1 : ℤ)
    have hwRe : w.re = z.re + cuspWidth := by
      simpa [w] using product_zpow_re (1 : ℤ) z
    refine ⟨g₁ * g₂, Or.inr ⟨?_, ?_,
      normSq_one_sub_ge_one_of_orbitHeightMaximal hwMax⟩⟩
    · unfold cuspWidth at hzLower hwRe
      rw [hwRe]
      linarith
    · unfold cuspWidth at hwRe
      rw [hwRe]
      exact le_of_lt (by linarith [lt_of_not_ge hzLeft])

/-- Every upper-half-plane point has a translate in the doubled, orientation-preserving
fundamental region. -/
public theorem exists_smul_mem_orientedFundamentalRegion (z : UpperHalfPlane) :
    ∃ g : Delta, fuchsianSourceAction g • z ∈ orientedFundamentalRegion := by
  obtain ⟨g, hgMax⟩ := exists_fuchsian_orbitHeightMaximal z
  obtain ⟨n, hnCoarse⟩ := hgMax.exists_mem_coarseFordRegion
  let w := fuchsianSourceAction ((g₁ * g₂) ^ n) • (fuchsianSourceAction g • z)
  have hwMax : IsOrbitHeightMaximal w := by
    simpa [w] using hgMax.product_zpow n
  have hwCoarse : w ∈ coarseFordRegion := by
    exact hnCoarse
  obtain ⟨k, hk⟩ := maximal_coarse_mem_orientedFundamentalRegion hwMax hwCoarse
  refine ⟨k * (g₁ * g₂) ^ n * g, ?_⟩
  rw [map_mul, map_mul, mul_smul, mul_smul]
  exact hk

end SphereSixComplex.TriangleGroup.FuchsianTriangleCover

namespace SphereSixComplex.Periods

open Set SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover

/-- Compact rectangle containing the noncuspidal part of both reflection chambers. -/
@[expose] public def orientedFuchsianCompactCore : Set UpperHalfPlane :=
  {z | |z.re| ≤ 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ 1}

public theorem orientedFuchsianCompactCore_isCompact :
    IsCompact orientedFuchsianCompactCore := by
  have hrect : IsCompact ((Set.Icc (-2 : ℝ) 2) ×ℂ Set.Icc (1 / 2 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  convert hrect using 1
  ext z
  constructor
  · rintro ⟨w, ⟨hwre, hwimLower, hwimUpper⟩, rfl⟩
    exact ⟨⟨by simpa using (abs_le.mp hwre).1, by simpa using (abs_le.mp hwre).2⟩,
      hwimLower, hwimUpper⟩
  · rintro ⟨⟨hzreLower, hzreUpper⟩, hzimLower, hzimUpper⟩
    have hzimPos : 0 < z.im := lt_of_lt_of_le (by norm_num) hzimLower
    let w : UpperHalfPlane := ⟨z, hzimPos⟩
    refine ⟨w, ?_, rfl⟩
    exact ⟨abs_le.mpr ⟨hzreLower, hzreUpper⟩, hzimLower, hzimUpper⟩

public theorem rightFundamentalTriangle_mem_cusp_or_compactCore
    {z : UpperHalfPlane} (hz : z ∈ rightFundamentalTriangle) :
    z ∈ fuchsianCuspRegion ∨ z ∈ orientedFuchsianCompactCore := by
  rcases hz with ⟨hzreLower, hzreUpper, hznorm⟩
  by_cases hcusp : 1 ≤ z.im
  · exact Or.inl hcusp
  · right
    have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsqrtUpper : Real.sqrt 2 ≤ 2 := by nlinarith
    have hreLower : -2 ≤ z.re := by linarith
    have hreUpper : z.re ≤ 2 := by linarith
    have hreOffsetSq : (1 - z.re) ^ 2 ≤ 1 / 2 := by
      have hleft : -(Real.sqrt 2 / 2) ≤ 1 - z.re := by linarith
      have hright : 1 - z.re ≤ Real.sqrt 2 / 2 := by nlinarith
      nlinarith
    have hnorm : 1 ≤ (1 - z.re) ^ 2 + z.im ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using hznorm
    have himLower : 1 / 2 ≤ z.im := by
      have himSq : 1 / 2 ≤ z.im ^ 2 := by nlinarith
      nlinarith [z.im_pos]
    exact ⟨abs_le.mpr ⟨hreLower, hreUpper⟩, himLower, le_of_not_ge hcusp⟩

public theorem orientedFundamentalRegion_mem_cusp_or_compactCore
    {z : UpperHalfPlane} (hz : z ∈ orientedFundamentalRegion) :
    z ∈ fuchsianCuspRegion ∨ z ∈ orientedFuchsianCompactCore := by
  rcases hz with hz | hz
  · rcases fundamentalTriangle_mem_cusp_or_compactCore hz with hcusp | hcore
    · exact Or.inl hcusp
    · exact Or.inr ⟨hcore.1.trans (by norm_num), hcore.2⟩
  · exact rightFundamentalTriangle_mem_cusp_or_compactCore hz

/-- Compact quotient core obtained from the correct doubled orientation-preserving domain. -/
@[expose] public noncomputable def orientedFuchsianQuotientCompactCore
    (P : FuchsianModularParameter) : QuotientCompactCore P.toTriangleUniformization where
  carrier := orientedFuchsianCompactCore
  compact := orientedFuchsianCompactCore_isCompact
  cover z := by
    obtain ⟨g, hg⟩ := exists_smul_mem_orientedFundamentalRegion z
    exact ⟨g, orientedFundamentalRegion_mem_cusp_or_compactCore hg⟩

/-- The doubled chamber cover supplies the compact-core input without the false single-reflection-
triangle cover premise. -/
public theorem FuchsianPrePeriodData.theorem3_4Existence_of_orientedTriangleCover
    (D : FuchsianPrePeriodData) :
    Theorem3_4Existence D.toFuchsianModularParameter.toTriangleUniformization :=
  D.theorem3_4Existence
    (orientedFuchsianQuotientCompactCore D.toFuchsianModularParameter)

end SphereSixComplex.Periods
