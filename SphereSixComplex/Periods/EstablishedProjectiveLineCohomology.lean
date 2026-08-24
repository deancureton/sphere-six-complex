module

public import SphereSixComplex.Periods.ProjectiveLineTorsors
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Established analytic Cech vanishing on the projective line

The Laurent-polynomial splittings are proved in `ProjectiveLineTorsors`.  Passing from Laurent
polynomials to arbitrary holomorphic functions on `ℂˣ` is the classical Laurent-series theorem.
We isolate exactly the two resulting Cech-surjectivity statements used for `O(-1)` and `O`.
-/

open scoped Manifold

namespace SphereSixComplex.Periods

/-- A complex-valued function is holomorphic on the punctured plane. -/
public def HolomorphicOnPuncturedPlane (f : ℂ → ℂ) : Prop :=
  ∀ z, z ≠ 0 → MDiffAt f z

/-- Analytic two-chart Cech exactness for `O(-1)` on `ℙ¹`.

The zero-chart coordinate is `z`; the infinity-chart coordinate is `z⁻¹`; and the infinity
section is expressed in the zero-chart frame by the transition factor `z⁻¹`. -/
public axiom establishedProjectiveLineCechNegOne
    (c : ℂ → ℂ) (hc : HolomorphicOnPuncturedPlane c) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        c z = fZero z - z⁻¹ * fInfinity (z⁻¹)

/-- Analytic two-chart Cech exactness for the structure sheaf `O` on `ℙ¹`. -/
public axiom establishedProjectiveLineCechZero
    (c : ℂ → ℂ) (hc : HolomorphicOnPuncturedPlane c) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        c z = fZero z - fInfinity (z⁻¹)

/-- Two local `O(-1)` torsor sections with holomorphic overlap mismatch can be corrected by entire
functions so that they agree in the zero-chart frame. -/
public theorem exists_compatibleProjectiveLineNegOneAdjustments
    (sZero sInfinity : ℂ → ℂ)
    (hZero : HolomorphicOnPuncturedPlane sZero)
    (hInfinity : HolomorphicOnPuncturedPlane sInfinity) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        sZero z - fZero z =
          sInfinity z - z⁻¹ * fInfinity (z⁻¹) := by
  have hc : HolomorphicOnPuncturedPlane (fun z ↦ sZero z - sInfinity z) := by
    intro z hz
    exact (hZero z hz).sub (hInfinity z hz)
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechNegOne (fun z ↦ sZero z - sInfinity z) hc
  refine ⟨fZero, fInfinity, hfZero, hfInfinity, ?_⟩
  intro z hz
  have h := hsplit z hz
  linear_combination h

/-- Two local structure-sheaf torsor sections with holomorphic overlap mismatch can be corrected
to agree. -/
public theorem exists_compatibleProjectiveLineZeroAdjustments
    (sZero sInfinity : ℂ → ℂ)
    (hZero : HolomorphicOnPuncturedPlane sZero)
    (hInfinity : HolomorphicOnPuncturedPlane sInfinity) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ≠ 0 →
        sZero z - fZero z = sInfinity z - fInfinity (z⁻¹) := by
  have hc : HolomorphicOnPuncturedPlane (fun z ↦ sZero z - sInfinity z) := by
    intro z hz
    exact (hZero z hz).sub (hInfinity z hz)
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechZero (fun z ↦ sZero z - sInfinity z) hc
  refine ⟨fZero, fInfinity, hfZero, hfInfinity, ?_⟩
  intro z hz
  have h := hsplit z hz
  linear_combination h

end SphereSixComplex.Periods
