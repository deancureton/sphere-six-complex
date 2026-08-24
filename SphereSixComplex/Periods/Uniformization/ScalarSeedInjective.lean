module

public import SphereSixComplex.Periods.Uniformization.ScalarTriangleReflection
import all SphereSixComplex.Periods.Uniformization.ScalarTriangleReflection

@[expose] public section

/-!
# Injectivity of the scalar seed up to a reflected side

The Cayley normalization is injective away from its pole.  Combining this elementary fact with
the closed-disc Carathéodory homeomorphism proves that the boundary-aware scalar seed is injective
on the chamber closure away from the completed cusp.  In particular it is injective on the
closed-positive half of the right-side Schwarz double, exactly the input needed by Tau Ceti's
injective reflection theorem.
-/

open Complex Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

/-- The normalized Cayley scalar is injective wherever its pole is excluded. -/
theorem scalarTriangleDiscMap_injOn_ne_pole
    (pole first second : Circle)
    (hfirst : first ≠ pole) (hsecond : second ≠ pole) (hfinite : first ≠ second) :
    InjOn (scalarTriangleDiscMap pole first second) {z : ℂ | z ≠ pole} := by
  intro z hz w hw hzw
  have hdenR : scalarTriangleDenominator pole first second ≠ 0 :=
    scalarTriangleDenominator_ne_zero hfirst hsecond hfinite
  have hden : (scalarTriangleDenominator pole first second : ℂ) ≠ 0 := by
    exact_mod_cast hdenR
  have hcayley : boundaryCayley pole z = boundaryCayley pole w := by
    unfold scalarTriangleDiscMap at hzw
    exact sub_left_inj.mp ((div_left_inj' hden).mp hzw)
  have hinv := congrArg (boundaryCayleyInv (pole : ℂ)) hcayley
  rw [boundaryCayleyInv_boundaryCayley pole.coe_ne_zero hz,
    boundaryCayleyInv_boundaryCayley pole.coe_ne_zero hw] at hinv
  exact hinv

/-- The totalized inverse of the Carathéodory closure equivalence is injective on the closure. -/
theorem chamberClosureDiscInverse_injOn_closure {Omega : Set ℂ}
    (S : ChamberCaratheodorySeed Omega) :
    InjOn (chamberClosureDiscInverse S) (closure Omega) := by
  intro q hq r hr hqr
  have hsub :
      S.closureEquiv.symm ⟨q, hq⟩ = S.closureEquiv.symm ⟨r, hr⟩ := by
    apply Subtype.ext
    simpa only [chamberClosureDiscInverse_apply_of_mem S hq,
      chamberClosureDiscInverse_apply_of_mem S hr] using hqr
  have himage := congrArg S.closureEquiv hsub
  rw [S.closureEquiv.apply_symm_apply, S.closureEquiv.apply_symm_apply] at himage
  exact congrArg Subtype.val himage

private theorem chamberClosureDiscInverse_ne_cuspCircle
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {q : ℂ}
    (hq : q ∈ closure sourceBoundedChamber) (hne : q ≠ sourceCuspVertex) :
    chamberClosureDiscInverse S q ≠ sourceCuspCircle S := by
  intro heq
  let pole : closedBall (0 : ℂ) 1 :=
    ⟨sourceCuspCircle S, by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
  have hinv : S.closureEquiv.symm ⟨q, hq⟩ = pole := by
    apply Subtype.ext
    simpa [pole, chamberClosureDiscInverse_apply_of_mem S hq] using heq
  have himage := congrArg S.closureEquiv hinv
  have hpole : S.closureEquiv pole =
      ⟨sourceCuspVertex, frontier_subset_closure sourceCuspVertex_mem_frontier⟩ := by
    simpa [pole, sourceCuspCircle] using
      S.closureEquiv_boundaryPreimage sourceBoundedChamber_isOpen sourceCuspVertex
        sourceCuspVertex_mem_frontier
  rw [S.closureEquiv.apply_symm_apply, hpole] at himage
  exact hne (congrArg Subtype.val himage)

/-- The scalar coordinate on the completed bounded chamber is injective away from its cusp. -/
theorem sourceScalarClosureMap_injOn_away_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    InjOn (sourceScalarClosureMap S)
      (closure sourceBoundedChamber \ {sourceCuspVertex}) := by
  intro q hq r hr hqr
  have hdisc : chamberClosureDiscInverse S q = chamberClosureDiscInverse S r := by
    apply scalarTriangleDiscMap_injOn_ne_pole
      (sourceCuspCircle S) (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
      (sourceOrderThreeCircle_ne_cusp S) (sourceOtherEllipticCircle_ne_cusp S)
      (sourceOrderThreeCircle_ne_otherElliptic S)
    · exact chamberClosureDiscInverse_ne_cuspCircle S hq.1 (by simpa using hq.2)
    · exact chamberClosureDiscInverse_ne_cuspCircle S hr.1 (by simpa using hr.2)
    · simpa only [sourceScalarClosureMap, Function.comp_apply] using hqr
  exact chamberClosureDiscInverse_injOn_closure S hq.1 hr.1 hdisc

/-- The part of the right-side double on the original, closed side of the seam. -/
def sourceRightClosedPositive : Set ℂ :=
  sourceRightDouble ∩ {z : ℂ | z.re ≤ 1 / 2}

private theorem cuspExponential_mem_sourceClosure_of_mem_rightClosedPositive
    {z : ℂ} (hz : z ∈ sourceRightClosedPositive) :
    cuspExponential (1 + Real.sqrt 2) z ∈ closure sourceBoundedChamber := by
  rcases hz with ⟨⟨hl, _hrwide, hi, hn, _hnr⟩, hrele⟩
  change z.re ≤ 1 / 2 at hrele
  rcases hrele.lt_or_eq with hre | hre
  · apply subset_closure
    exact ⟨z, ⟨hl, hre, hi, hn⟩, rfl⟩
  · exact frontier_subset_closure
      (cuspExponential_mem_source_frontier_of_rightSide hre hi hn)

private theorem cuspExponential_ne_sourceCuspVertex (z : ℂ) :
    cuspExponential (1 + Real.sqrt 2) z ≠ sourceCuspVertex := by
  simpa [sourceCuspVertex] using cuspExponential_ne_zero (1 + Real.sqrt 2) z

/-- The original closed half of the right Schwarz double is already injectively parametrized by
the scalar triangle seed. -/
theorem sourceScalarTriangleMap_injOn_rightClosedPositive
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    InjOn (sourceScalarTriangleMap S) sourceRightClosedPositive := by
  intro z hz w hw hzw
  have hq := cuspExponential_mem_sourceClosure_of_mem_rightClosedPositive hz
  have hr := cuspExponential_mem_sourceClosure_of_mem_rightClosedPositive hw
  have hexp :
      cuspExponential (1 + Real.sqrt 2) z =
        cuspExponential (1 + Real.sqrt 2) w := by
    apply sourceScalarClosureMap_injOn_away_cusp S
      ⟨hq, by simpa using cuspExponential_ne_sourceCuspVertex z⟩
      ⟨hr, by simpa using cuspExponential_ne_sourceCuspVertex w⟩
    simpa only [sourceScalarTriangleMap, Function.comp_apply] using hzw
  apply source_cuspExponential_injOn_closedStrip
  · exact ⟨hz.1.1.le, hz.2⟩
  · exact ⟨hw.1.1.le, hw.2⟩
  · exact hexp


end SphereSixComplex.Periods.SourceChamberTopology
