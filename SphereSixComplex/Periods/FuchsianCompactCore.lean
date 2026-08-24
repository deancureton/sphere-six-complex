module

public import SphereSixComplex.Periods.FuchsianUniformizationBridge
public import SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain

/-!
# A compact core from the explicit Fuchsian triangle

The part of the explicit fundamental triangle below the standard cusp horodisc lies in a fixed
compact rectangle of the upper half-plane.  Consequently, a covering theorem for translates of
the triangle supplies exactly the compact-core input used in the period-function construction.
-/

noncomputable section

namespace SphereSixComplex.Periods

open Set
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain

/-- A fixed compact rectangle containing the non-cuspidal part of the fundamental triangle. -/
@[expose] public def fuchsianFundamentalCompactCore : Set UpperHalfPlane :=
  {z | |z.re| ≤ 1 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ 1}

public theorem fuchsianFundamentalCompactCore_isCompact :
    IsCompact fuchsianFundamentalCompactCore := by
  have hrect : IsCompact ((Set.Icc (-1 : ℝ) 1) ×ℂ Set.Icc (1 / 2 : ℝ) 1) :=
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

/-- Every point of the fundamental triangle is either in the standard cusp region or in the
compact core. -/
public theorem fundamentalTriangle_mem_cusp_or_compactCore
    {z : UpperHalfPlane} (hz : z ∈ fundamentalTriangle) :
    z ∈ fuchsianCuspRegion ∨ z ∈ fuchsianFundamentalCompactCore := by
  rcases hz with ⟨hzreLower, hzreUpper, hznorm⟩
  by_cases hcusp : 1 ≤ z.im
  · exact Or.inl hcusp
  · right
    have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hreLower : -1 ≤ z.re := by nlinarith
    have hreUpper : z.re ≤ 1 := by linarith
    have hreSq : z.re ^ 2 ≤ 1 / 2 := by
      have hleft : -(Real.sqrt 2 / 2) ≤ z.re := by nlinarith [hzreLower]
      have hright : z.re ≤ Real.sqrt 2 / 2 := by nlinarith
      nlinarith
    have hnorm : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using hznorm
    have himLower : 1 / 2 ≤ z.im := by
      have himSq : 1 / 2 ≤ z.im ^ 2 := by nlinarith
      nlinarith [z.im_pos]
    exact ⟨abs_le.mpr ⟨hreLower, hreUpper⟩, himLower, le_of_not_ge hcusp⟩

/-- The remaining covering statement for the explicit Fuchsian fundamental triangle. -/
public def FuchsianFundamentalTriangleCovers : Prop :=
  ∀ z : UpperHalfPlane, ∃ g : Delta,
    fuchsianSourceAction g • z ∈ fundamentalTriangle

/-- A translate-covering theorem for the explicit triangle gives the compact quotient core used
by the Schur-bound argument. -/
@[expose] public noncomputable def fuchsianQuotientCompactCore
    (P : FuchsianModularParameter) (hcover : FuchsianFundamentalTriangleCovers) :
    QuotientCompactCore P.toTriangleUniformization where
  carrier := fuchsianFundamentalCompactCore
  compact := fuchsianFundamentalCompactCore_isCompact
  cover z := by
    obtain ⟨g, hg⟩ := hcover z
    refine ⟨g, ?_⟩
    exact fundamentalTriangle_mem_cusp_or_compactCore hg

/-- Once the explicit triangle covers the upper half-plane, Fuchsian pre-period data produces the
full nondegenerate period family. -/
public theorem FuchsianPrePeriodData.theorem3_4Existence_of_triangleCover
    (D : FuchsianPrePeriodData) (hcover : FuchsianFundamentalTriangleCovers) :
    Theorem3_4Existence D.toFuchsianModularParameter.toTriangleUniformization :=
  D.theorem3_4Existence (fuchsianQuotientCompactCore D.toFuchsianModularParameter hcover)

end SphereSixComplex.Periods
