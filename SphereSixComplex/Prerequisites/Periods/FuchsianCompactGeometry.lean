module

public import SphereSixComplex.Prerequisites.TriangleGroup.FuchsianFundamentalDomain

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


end SphereSixComplex.Periods
