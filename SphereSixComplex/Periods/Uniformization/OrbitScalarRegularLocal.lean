module

public import SphereSixComplex.Periods.Uniformization.ScalarFundamentalConsistency
import all SphereSixComplex.Periods.Uniformization.ScalarFundamentalConsistency
public import SphereSixComplex.TriangleGroup.FuchsianSmoothAction
import all SphereSixComplex.TriangleGroup.FuchsianSmoothAction

@[expose] public section

/-!
# A regular local chart for the orbit-assembled source scalar

The first Schwarz double is exactly the interior of the doubled oriented fundamental polygon
away from its circular sides.  Consequently, whenever the chosen fundamental representative of
a point lies in that double, a fixed deck translate identifies the orbit-assembled scalar with a
single holomorphic Schwarz patch on a whole neighbourhood of the point.
-/

open Complex Filter Set Topology UpperHalfPlane
open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.Periods.TriangleReflections

/-- The right Schwarz double lies in the doubled orientation-preserving fundamental region. -/
theorem sourceRightDouble_subset_orientedFundamentalRegion {z : ℂ}
    (hz : z ∈ sourceRightDouble) :
    (⟨z, hz.2.2.1⟩ : UpperHalfPlane) ∈ orientedFundamentalRegion := by
  rcases hz with ⟨hl, hr, hi, hn, hnr⟩
  by_cases hx : z.re ≤ 1 / 2
  · exact Or.inl ⟨hl.le, hx, hn.le⟩
  · exact Or.inr ⟨le_of_not_ge hx, hr.le, by
      have heq : normSq (1 - z) = normSq (sourceRight z) := by
        simp [sourceRight, normSq_apply]
      rw [heq]
      exact hnr.le⟩

/-- On the whole open right double, the algebraic orbit construction is the explicit holomorphic
right Schwarz patch. -/
theorem orbitAssembledScalar_eq_rightDouble_of_mem
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : ℂ}
    (hz : z ∈ sourceRightDouble) :
    orbitAssembledScalar S z = sourceScalarRightDoubleMap S z := by
  let w : UpperHalfPlane := ⟨z, hz.2.2.1⟩
  have hw : w ∈ orientedFundamentalRegion :=
    sourceRightDouble_subset_orientedFundamentalRegion hz
  simpa [w] using
    orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hw

private theorem sourceScalarLeftDoubleMap_eq_seed_of_left_le_re_local
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hre : -Real.sqrt 2 / 2 ≤ z.re) :
    sourceScalarLeftDoubleMap S z = sourceScalarTriangleMap S z := by
  apply TauCeti.lineSchwarzReflection_of_coord_im_nonneg
    (sourceScalarTriangleMap S) (by simp) one_ne_zero
  rw [sourceLeft_coord_im]
  linarith

private theorem sourceRight_sourceLeft_eq_product (z : UpperHalfPlane) :
    sourceRightUHP (sourceLeftUHP z) =
      fuchsianSourceAction (g₁ * g₂) • z := by
  apply UpperHalfPlane.coe_injective
  have h := SphereSixComplex.TriangleGroup.FuchsianTessellation.product_zpow_apply
    (1 : ℤ) z
  have h' : (((fuchsianSourceAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ) =
      (z : ℂ) + SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.cuspWidth := by
    simpa using h
  change (sourceRight (sourceLeft (z : ℂ))) =
    (((fuchsianSourceAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ)
  rw [h']
  simp [sourceRight, sourceLeft,
    SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain.cuspWidth]
  ring

private theorem sourceLeft_sourceRight_eq_product_inv (z : UpperHalfPlane) :
    sourceLeftUHP (sourceRightUHP z) =
      fuchsianSourceAction (g₁ * g₂)⁻¹ • z := by
  let q : UpperHalfPlane := sourceLeftUHP (sourceRightUHP z)
  have hq : fuchsianSourceAction (g₁ * g₂) • q = z := by
    rw [← sourceRight_sourceLeft_eq_product]
    apply UpperHalfPlane.coe_injective
    simp [q, sourceRight, sourceLeft]
  calc
    sourceLeftUHP (sourceRightUHP z) = q := rfl
    _ = fuchsianSourceAction (g₁ * g₂)⁻¹ •
        (fuchsianSourceAction (g₁ * g₂) • q) := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = fuchsianSourceAction (g₁ * g₂)⁻¹ • z := congrArg _ hq

private theorem sourceCircle_sourceRight_eq_g1_inv (z : UpperHalfPlane) :
    sourceCircleUHP (sourceRightUHP z) = fuchsianSourceAction g₁⁻¹ • z := by
  let q : UpperHalfPlane := sourceCircleUHP (sourceRightUHP z)
  have hq : fuchsianSourceAction g₁ • q = z := by
    rw [← sourceRight_sourceCircle]
    apply UpperHalfPlane.coe_injective
    simp [q, sourceRight, sourceCircle]
  calc
    sourceCircleUHP (sourceRightUHP z) = q := rfl
    _ = fuchsianSourceAction g₁⁻¹ • (fuchsianSourceAction g₁ • q) := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = fuchsianSourceAction g₁⁻¹ • z := congrArg _ hq

/-- The algebraic orbit scalar agrees with the left Schwarz patch throughout its open double. -/
theorem orbitAssembledScalar_eq_leftDouble_of_mem
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : ℂ}
    (hz : z ∈ sourceLeftDouble) :
    orbitAssembledScalar S z = sourceScalarLeftDoubleMap S z := by
  rcases hz with ⟨hl, hr, hi, hn, hnl⟩
  let w : UpperHalfPlane := ⟨z, hi⟩
  by_cases hx : -Real.sqrt 2 / 2 ≤ z.re
  · have hw : w ∈ orientedFundamentalRegion := Or.inl ⟨hx, hr.le, hn.le⟩
    calc
      orbitAssembledScalar S z = sourceScalarRightDoubleMap S z := by
        simpa [w] using
          orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hw
      _ = sourceScalarTriangleMap S z :=
        sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hr.le
      _ = sourceScalarLeftDoubleMap S z :=
        (sourceScalarLeftDoubleMap_eq_seed_of_left_le_re_local S hx).symm
  · have hxlt : z.re < -Real.sqrt 2 / 2 := lt_of_not_ge hx
    let y : ℂ := sourceLeft z
    let yu : UpperHalfPlane := sourceLeftUHP w
    let p : UpperHalfPlane := sourceRightUHP yu
    have hyreLower : -Real.sqrt 2 / 2 < y.re := by
      change -Real.sqrt 2 / 2 < (sourceLeft z).re
      rw [sourceLeft_re]
      linarith
    have hyreUpper : y.re < 1 / 2 := by
      change (sourceLeft z).re < 1 / 2
      rw [sourceLeft_re]
      linarith
    have hyn : 1 < normSq y := by simpa [y] using hnl
    have hpn : 1 < normSq (sourceRight y) := by
      rw [sourceRight_normSq]
      rw [normSq_apply] at hyn
      nlinarith
    have hyright : y ∈ sourceRightDouble :=
      ⟨hyreLower, by
        have hs := Real.sqrt_nonneg 2
        linarith, by simpa [y, sourceLeft] using hi,
        hyn, hpn⟩
    have hpreLower : 1 / 2 ≤ p.re := by
      change 1 / 2 ≤ (sourceRight y).re
      rw [sourceRight_re]
      linarith
    have hpreUpper : p.re ≤ 1 + Real.sqrt 2 / 2 := by
      change (sourceRight y).re ≤ 1 + Real.sqrt 2 / 2
      rw [sourceRight_re]
      linarith
    have hpNorm : 1 ≤ normSq (1 - (p : ℂ)) := by
      change 1 ≤ normSq (1 - sourceRight y)
      have heq : normSq (1 - sourceRight y) = normSq y := by
        simp [sourceRight, normSq_apply]
      rw [heq]
      exact hyn.le
    have hpFund : p ∈ orientedFundamentalRegion :=
      Or.inr ⟨hpreLower, hpreUpper, hpNorm⟩
    have hleft_y : sourceScalarLeftDoubleMap S y = sourceScalarTriangleMap S y :=
      sourceScalarLeftDoubleMap_eq_seed_of_left_le_re_local S hyreLower.le
    have hright_y : sourceScalarRightDoubleMap S y = sourceScalarTriangleMap S y :=
      sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hyreUpper.le
    have hleft_reflect := sourceScalarLeftDoubleMap_reflection S
      (sourceLeftDouble_mapsTo ⟨hl, hr, hi, hn, hnl⟩)
    have hright_reflect := sourceScalarRightDoubleMap_reflection S hyright
    have hpOrbit : orbitAssembledScalar S (p : ℂ) =
        sourceScalarRightDoubleMap S (p : ℂ) :=
      orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hpFund
    calc
      orbitAssembledScalar S z = orbitAssembledScalar S (p : ℂ) := by
        have hinv := orbitAssembledScalar_invariant S hconsistent (g₁ * g₂) w
        rw [← sourceRight_sourceLeft_eq_product] at hinv
        simpa [w, yu, p, y] using hinv.symm
      _ = sourceScalarRightDoubleMap S (p : ℂ) := hpOrbit
      _ = (starRingEnd ℂ) (sourceScalarRightDoubleMap S y) := by
        simpa [p, yu, y] using hright_reflect
      _ = (starRingEnd ℂ) (sourceScalarLeftDoubleMap S y) := by
        rw [hright_y, hleft_y]
      _ = sourceScalarLeftDoubleMap S z := by
        have hleft_reflect' :
            sourceScalarLeftDoubleMap S z =
              (starRingEnd ℂ) (sourceScalarLeftDoubleMap S y) := by
          simpa [y] using hleft_reflect
        exact hleft_reflect'.symm

private theorem sourceScalarCircleDoubleMap_eq_seed_of_one_le_normSq
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : ℂ}
    (hz : z ∈ sourceCircleDouble) (hn : 1 ≤ normSq z) :
    sourceScalarCircleDoubleMap S z = sourceScalarTriangleMap S z := by
  apply TauCeti.chartedSchwarzReflection_of_coord_im_nonneg
    sourceCircleCayleyChart sourceScalarTargetLineChart (sourceScalarTriangleMap S)
  · intro w hw
    simp [sourceScalarTargetLineChart]
  · rw [sourceCircleCayleyChart_source]
    exact hz
  · rw [sourceCircleCayleyChart_apply, sourceCircleCayley_im]
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      have hfalse := hz.1
      norm_num at hfalse
    have hden : 0 < normSq (1 - z) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
    exact div_nonneg (by linarith) hden.le

/-- The algebraic orbit scalar agrees with the circular Schwarz patch throughout its double. -/
theorem orbitAssembledScalar_eq_circleDouble_of_mem
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : ℂ}
    (hz : z ∈ sourceCircleDouble) :
    orbitAssembledScalar S z = sourceScalarCircleDoubleMap S z := by
  rcases hz with ⟨hi, hl, hr, hrl, hrr⟩
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hi
  have hnpos : 0 < normSq z := Complex.normSq_pos.mpr hz0
  let w : UpperHalfPlane := ⟨z, hi⟩
  by_cases hn : 1 ≤ normSq z
  · have hw : w ∈ orientedFundamentalRegion := Or.inl ⟨hl.le, hr.le, hn⟩
    calc
      orbitAssembledScalar S z = sourceScalarRightDoubleMap S z := by
        simpa [w] using
          orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hw
      _ = sourceScalarTriangleMap S z :=
        sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hr.le
      _ = sourceScalarCircleDoubleMap S z :=
        (sourceScalarCircleDoubleMap_eq_seed_of_one_le_normSq S
          ⟨hi, hl, hr, hrl, hrr⟩ hn).symm
  · have hnlt : normSq z < 1 := lt_of_not_ge hn
    let y : ℂ := sourceCircle z
    let yu : UpperHalfPlane := sourceCircleUHP w
    let p : UpperHalfPlane := sourceRightUHP yu
    have hyre : y.re = z.re / normSq z := sourceCircle_re z
    have hyreLower : -Real.sqrt 2 / 2 < y.re := by
      rw [hyre]
      exact (lt_div_iff₀ hnpos).2 hrl
    have hyreUpper : y.re < 1 / 2 := by
      rw [hyre]
      exact (div_lt_iff₀ hnpos).2 hrr
    have hyn : 1 < normSq y := by
      change 1 < normSq (sourceCircle z)
      rw [sourceCircle_normSq]
      exact (one_lt_inv₀ hnpos).2 hnlt
    have hpn : 1 < normSq (sourceRight y) := by
      rw [sourceRight_normSq]
      rw [normSq_apply] at hyn
      nlinarith
    have hyright : y ∈ sourceRightDouble :=
      ⟨hyreLower, by
        have hs := Real.sqrt_nonneg 2
        linarith, by
          change 0 < (sourceCircle z).im
          rw [sourceCircle_im]
          exact div_pos hi hnpos,
        hyn, hpn⟩
    have hycircle : y ∈ sourceCircleDouble := by
      change sourceCircle z ∈ sourceCircleDouble
      exact sourceCircleDouble_mapsTo ⟨hi, hl, hr, hrl, hrr⟩
    have hpreLower : 1 / 2 ≤ p.re := by
      change 1 / 2 ≤ (sourceRight y).re
      rw [sourceRight_re]
      linarith
    have hpreUpper : p.re ≤ 1 + Real.sqrt 2 / 2 := by
      change (sourceRight y).re ≤ 1 + Real.sqrt 2 / 2
      rw [sourceRight_re]
      linarith
    have hpNorm : 1 ≤ normSq (1 - (p : ℂ)) := by
      change 1 ≤ normSq (1 - sourceRight y)
      have heq : normSq (1 - sourceRight y) = normSq y := by
        simp [sourceRight, normSq_apply]
      rw [heq]
      exact hyn.le
    have hpFund : p ∈ orientedFundamentalRegion :=
      Or.inr ⟨hpreLower, hpreUpper, hpNorm⟩
    have hcircle_y : sourceScalarCircleDoubleMap S y =
        sourceScalarTriangleMap S y :=
      sourceScalarCircleDoubleMap_eq_seed_of_one_le_normSq S hycircle hyn.le
    have hright_y : sourceScalarRightDoubleMap S y = sourceScalarTriangleMap S y :=
      sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hyreUpper.le
    have hcircle_reflect := sourceScalarCircleDoubleMap_reflection S hycircle
    have hright_reflect := sourceScalarRightDoubleMap_reflection S hyright
    have hpOrbit : orbitAssembledScalar S (p : ℂ) =
        sourceScalarRightDoubleMap S (p : ℂ) :=
      orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hpFund
    calc
      orbitAssembledScalar S z = orbitAssembledScalar S (p : ℂ) := by
        have hinv := orbitAssembledScalar_invariant S hconsistent g₁ w
        rw [← sourceRight_sourceCircle] at hinv
        simpa [w, yu, p, y] using hinv.symm
      _ = sourceScalarRightDoubleMap S (p : ℂ) := hpOrbit
      _ = (starRingEnd ℂ) (sourceScalarRightDoubleMap S y) := by
        simpa [p, yu, y] using hright_reflect
      _ = (starRingEnd ℂ) (sourceScalarCircleDoubleMap S y) := by
        rw [hright_y, hcircle_y]
      _ = sourceScalarCircleDoubleMap S z := by
        have hinvol : sourceCircle y = z := by
          dsimp [y]
          simp [sourceCircle]
        have hcircle_reflect' :
            sourceScalarCircleDoubleMap S z =
              (starRingEnd ℂ) (sourceScalarCircleDoubleMap S y) := by
          rw [hinvol] at hcircle_reflect
          exact hcircle_reflect
        exact hcircle_reflect'.symm

private theorem orbitAssembledScalar_mdifferentiableAt_of_complex_patch
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (U : Set ℂ) (F : ℂ → ℂ) (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U)
    (heq : ∀ {u : ℂ}, u ∈ U → orbitAssembledScalar S u = F u)
    {z : UpperHalfPlane} (hz : (z : ℂ) ∈ U) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have hFat : DifferentiableAt ℂ F (z : ℂ) :=
    (hF z hz).differentiableAt (hU.mem_nhds hz)
  apply hFat.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hz,
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with u huU huH
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos huH]
  exact heq huU

theorem orbitAssembledScalar_mdifferentiableAt_of_mem_rightDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : UpperHalfPlane}
    (hz : (z : ℂ) ∈ sourceRightDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z :=
  orbitAssembledScalar_mdifferentiableAt_of_complex_patch S sourceRightDouble
    (sourceScalarRightDoubleMap S) sourceRightDouble_isOpen
    (sourceScalarRightDoubleMap_differentiableOn S)
    (orbitAssembledScalar_eq_rightDouble_of_mem S hconsistent) hz

theorem orbitAssembledScalar_mdifferentiableAt_of_mem_leftDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : UpperHalfPlane}
    (hz : (z : ℂ) ∈ sourceLeftDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z :=
  orbitAssembledScalar_mdifferentiableAt_of_complex_patch S sourceLeftDouble
    (sourceScalarLeftDoubleMap S) sourceLeftDouble_isOpen
    (sourceScalarLeftDoubleMap_differentiableOn S)
    (orbitAssembledScalar_eq_leftDouble_of_mem S hconsistent) hz

theorem orbitAssembledScalar_mdifferentiableAt_of_mem_circleDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : UpperHalfPlane}
    (hz : (z : ℂ) ∈ sourceCircleDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z :=
  orbitAssembledScalar_mdifferentiableAt_of_complex_patch S sourceCircleDouble
    (sourceScalarCircleDoubleMap S) sourceCircleDouble_isOpen
    (sourceScalarCircleDoubleMap_differentiableOn S)
    (orbitAssembledScalar_eq_circleDouble_of_mem S hconsistent) hz

/-- Holomorphicity of an invariant scalar transports backwards along every deck map. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_smul
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (g : Delta)
    (z : UpperHalfPlane)
    (h : MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ))
      (fuchsianSourceAction g • z)) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  have hcomp : MDiffAt
      (fun w : UpperHalfPlane ↦ orbitAssembledScalar S
        ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ)) z :=
    h.comp z ((fuchsianSourceAction_contMDiff g ⊤).mdifferentiableAt (by simp))
  exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w ↦
    (orbitAssembledScalar_invariant S hconsistent g w).symm)

/-- A far-right patch is carried to the left Schwarz double by the inverse cusp translation. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_mem_farRightDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : UpperHalfPlane}
    (hz : (z : ℂ) ∈ sourceFarRightDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  have hr : sourceRight (z : ℂ) ∈ sourceLeftDouble := by
    simpa [sourceFarRightDouble] using hz
  have hq : sourceLeft (sourceRight (z : ℂ)) ∈ sourceLeftDouble :=
    sourceLeftDouble_mapsTo hr
  let q : UpperHalfPlane := sourceLeftUHP (sourceRightUHP z)
  have hqmem : (q : ℂ) ∈ sourceLeftDouble := by simpa [q] using hq
  have hdiffq := orbitAssembledScalar_mdifferentiableAt_of_mem_leftDouble
    S hconsistent hqmem
  apply orbitAssembledScalar_mdifferentiableAt_of_smul S hconsistent
    (g₁ * g₂)⁻¹ z
  simpa [q, sourceLeft_sourceRight_eq_product_inv] using hdiffq

/-- A right-circular patch is carried to the circular double by `g₁⁻¹`. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_mem_rightCircleDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) {z : UpperHalfPlane}
    (hz : (z : ℂ) ∈ sourceRightCircleDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  have hr : sourceRight (z : ℂ) ∈ sourceCircleDouble := by
    simpa [sourceRightCircleDouble] using hz
  have hq : sourceCircle (sourceRight (z : ℂ)) ∈ sourceCircleDouble :=
    sourceCircleDouble_mapsTo hr
  let q : UpperHalfPlane := sourceCircleUHP (sourceRightUHP z)
  have hqmem : (q : ℂ) ∈ sourceCircleDouble := by simpa [q] using hq
  have hdiffq := orbitAssembledScalar_mdifferentiableAt_of_mem_circleDouble
    S hconsistent hqmem
  apply orbitAssembledScalar_mdifferentiableAt_of_smul S hconsistent g₁⁻¹ z
  simpa [q, sourceCircle_sourceRight_eq_g1_inv] using hdiffq

/-- If the chosen fundamental representative is a regular point of the first Schwarz double,
the orbit-assembled coordinate is holomorphic at the original point. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_representative_mem_rightDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (z : UpperHalfPlane)
    (hz : (sourceFundamentalRepresentative z : ℂ) ∈ sourceRightDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  let g : Delta := sourceFundamentalTransport z
  let p : UpperHalfPlane := fuchsianSourceAction g • z
  have hp : (p : ℂ) ∈ sourceRightDouble := by
    simpa [g, p, sourceFundamentalRepresentative]
  let localPatch : UpperHalfPlane → ℂ := fun w ↦
    sourceScalarRightDoubleMap S ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ)
  have hright : MDiffAt
      (fun u : UpperHalfPlane ↦ sourceScalarRightDoubleMap S (u : ℂ)) p := by
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    have hnhds : sourceRightDouble ∈ 𝓝 (p : ℂ) :=
      sourceRightDouble_isOpen.mem_nhds hp
    exact ((sourceScalarRightDoubleMap_differentiableOn S p hp).differentiableAt hnhds).congr_of_eventuallyEq
      (by
        filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with u hu
        rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hu])
  have hpatch : MDiffAt localPatch z := by
    exact hright.comp z
      ((fuchsianSourceAction_contMDiff g ⊤).mdifferentiableAt (by simp))
  apply hpatch.congr_of_eventuallyEq
  have hmem : ∀ᶠ w : UpperHalfPlane in 𝓝 z,
      ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) ∈ sourceRightDouble := by
    have hc : Continuous (fun w : UpperHalfPlane ↦
        ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ)) :=
      UpperHalfPlane.continuous_coe.comp
        (fuchsianSourceAction_contMDiff g 0).continuous
    exact hc.continuousAt.eventually (sourceRightDouble_isOpen.mem_nhds hp)
  filter_upwards [hmem] with w hw
  change orbitAssembledScalar S (w : ℂ) = localPatch w
  calc
    orbitAssembledScalar S (w : ℂ) =
        orbitAssembledScalar S
          ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) :=
      (orbitAssembledScalar_invariant S hconsistent g w).symm
    _ = sourceScalarRightDoubleMap S
          ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) :=
      orbitAssembledScalar_eq_rightDouble_of_mem S hconsistent hw
    _ = localPatch w := rfl

/-- The analogous regular local chart when the representative lies in the left Schwarz double. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_representative_mem_leftDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (z : UpperHalfPlane)
    (hz : (sourceFundamentalRepresentative z : ℂ) ∈ sourceLeftDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  let g : Delta := sourceFundamentalTransport z
  let p : UpperHalfPlane := fuchsianSourceAction g • z
  have hp : (p : ℂ) ∈ sourceLeftDouble := by
    simpa [g, p, sourceFundamentalRepresentative]
  let localPatch : UpperHalfPlane → ℂ := fun w ↦
    sourceScalarLeftDoubleMap S ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ)
  have hleft : MDiffAt
      (fun u : UpperHalfPlane ↦ sourceScalarLeftDoubleMap S (u : ℂ)) p := by
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    have hnhds : sourceLeftDouble ∈ 𝓝 (p : ℂ) :=
      sourceLeftDouble_isOpen.mem_nhds hp
    exact ((sourceScalarLeftDoubleMap_differentiableOn S p hp).differentiableAt hnhds).congr_of_eventuallyEq
      (by
        filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with u hu
        rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hu])
  have hpatch : MDiffAt localPatch z := by
    exact hleft.comp z
      ((fuchsianSourceAction_contMDiff g ⊤).mdifferentiableAt (by simp))
  apply hpatch.congr_of_eventuallyEq
  have hmem : ∀ᶠ w : UpperHalfPlane in 𝓝 z,
      ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) ∈ sourceLeftDouble := by
    have hc : Continuous (fun w : UpperHalfPlane ↦
        ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ)) :=
      UpperHalfPlane.continuous_coe.comp
        (fuchsianSourceAction_contMDiff g 0).continuous
    exact hc.continuousAt.eventually (sourceLeftDouble_isOpen.mem_nhds hp)
  filter_upwards [hmem] with w hw
  calc
    orbitAssembledScalar S (w : ℂ) =
        orbitAssembledScalar S
          ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) :=
      (orbitAssembledScalar_invariant S hconsistent g w).symm
    _ = sourceScalarLeftDoubleMap S
          ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) :=
      orbitAssembledScalar_eq_leftDouble_of_mem S hconsistent hw
    _ = localPatch w := rfl

/-- The analogous regular local chart when the representative lies in the circular double. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_representative_mem_circleDouble
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (z : UpperHalfPlane)
    (hz : (sourceFundamentalRepresentative z : ℂ) ∈ sourceCircleDouble) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  let g : Delta := sourceFundamentalTransport z
  let p : UpperHalfPlane := fuchsianSourceAction g • z
  have hp : (p : ℂ) ∈ sourceCircleDouble := by
    simpa [g, p, sourceFundamentalRepresentative]
  let localPatch : UpperHalfPlane → ℂ := fun w ↦
    sourceScalarCircleDoubleMap S ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ)
  have hcircle : MDiffAt
      (fun u : UpperHalfPlane ↦ sourceScalarCircleDoubleMap S (u : ℂ)) p := by
    rw [UpperHalfPlane.mdifferentiableAt_iff]
    have hnhds : sourceCircleDouble ∈ 𝓝 (p : ℂ) :=
      sourceCircleDouble_isOpen.mem_nhds hp
    exact ((sourceScalarCircleDoubleMap_differentiableOn S p hp).differentiableAt hnhds).congr_of_eventuallyEq
      (by
        filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with u hu
        rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hu])
  have hpatch : MDiffAt localPatch z := by
    exact hcircle.comp z
      ((fuchsianSourceAction_contMDiff g ⊤).mdifferentiableAt (by simp))
  apply hpatch.congr_of_eventuallyEq
  have hmem : ∀ᶠ w : UpperHalfPlane in 𝓝 z,
      ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) ∈ sourceCircleDouble := by
    have hc : Continuous (fun w : UpperHalfPlane ↦
        ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ)) :=
      UpperHalfPlane.continuous_coe.comp
        (fuchsianSourceAction_contMDiff g 0).continuous
    exact hc.continuousAt.eventually (sourceCircleDouble_isOpen.mem_nhds hp)
  filter_upwards [hmem] with w hw
  calc
    orbitAssembledScalar S (w : ℂ) =
        orbitAssembledScalar S
          ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) :=
      (orbitAssembledScalar_invariant S hconsistent g w).symm
    _ = sourceScalarCircleDoubleMap S
          ((fuchsianSourceAction g • w : UpperHalfPlane) : ℂ) :=
      orbitAssembledScalar_eq_circleDouble_of_mem S hconsistent hw
    _ = localPatch w := rfl

/-- Away from the three displayed vertices of the doubled fundamental polygon, one of the five
explicit Schwarz patches supplies a holomorphic chart at the original point. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_representative_ne_vertices
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (z : UpperHalfPlane)
    (hone : sourceFundamentalRepresentative z ≠ fuchsianOneFixedPoint)
    (htwo : sourceFundamentalRepresentative z ≠ fuchsianTwoFixedPoint)
    (hfar : sourceFundamentalRepresentative z ≠ sourceFarRightVertex) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  have hmem := orientedFundamentalRegion_mem_scalar_local_cover
    (sourceFundamentalRepresentative z) (sourceFundamentalRepresentative_mem z)
  rcases hmem with hright | hleft | hcircle | hfarRight | hrightCircle |
      hone' | htwo' | hfar'
  · exact orbitAssembledScalar_mdifferentiableAt_of_representative_mem_rightDouble
      S hconsistent z hright
  · exact orbitAssembledScalar_mdifferentiableAt_of_representative_mem_leftDouble
      S hconsistent z hleft
  · exact orbitAssembledScalar_mdifferentiableAt_of_representative_mem_circleDouble
      S hconsistent z hcircle
  · have htransported := orbitAssembledScalar_mdifferentiableAt_of_mem_farRightDouble
      S hconsistent hfarRight
    exact orbitAssembledScalar_mdifferentiableAt_of_smul S hconsistent
      (sourceFundamentalTransport z) z (by
        simpa only [sourceFundamentalRepresentative] using htransported)
  · have htransported := orbitAssembledScalar_mdifferentiableAt_of_mem_rightCircleDouble
      S hconsistent hrightCircle
    exact orbitAssembledScalar_mdifferentiableAt_of_smul S hconsistent
      (sourceFundamentalTransport z) z (by
        simpa only [sourceFundamentalRepresentative] using htransported)
  · exact (hone hone').elim
  · exact (htwo htwo').elim
  · exact (hfar hfar').elim

/-- The far-right order-four vertex is the positive cusp translate of the distinguished
order-four vertex. -/
theorem sourceFarRightVertex_eq_product_smul_two :
    sourceFarRightVertex = fuchsianSourceAction (g₁ * g₂) • fuchsianTwoFixedPoint := by
  apply UpperHalfPlane.coe_injective
  have h := FuchsianFundamentalDomain.product_apply fuchsianTwoFixedPoint
  calc
    (sourceFarRightVertex : ℂ) =
        (fuchsianTwoFixedPoint : ℂ) + FuchsianFundamentalDomain.cuspWidth := by
      apply Complex.ext
      · simp [sourceFarRightVertex, sourceRightUHP, sourceRight,
          FuchsianFundamentalDomain.cuspWidth, fuchsianTwoFixedPoint]
        ring
      · simp [sourceFarRightVertex, sourceRightUHP, sourceRight,
          FuchsianFundamentalDomain.cuspWidth, fuchsianTwoFixedPoint]
    _ = ((fuchsianSourceAction (g₁ * g₂) • fuchsianTwoFixedPoint :
          UpperHalfPlane) : ℂ) := h.symm

/-- Every point outside the two elliptic orbits has one of the regular Schwarz charts. -/
theorem orbitAssembledScalar_mdifferentiableAt_of_regular
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (z : UpperHalfPlane)
    (hz : FreeProductTorsion.IsFuchsianRegularPoint z) :
    MDiffAt (fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) z := by
  apply orbitAssembledScalar_mdifferentiableAt_of_representative_ne_vertices
    S hconsistent z
  · exact (hz (sourceFundamentalTransport z)).1
  · exact (hz (sourceFundamentalTransport z)).2
  · intro hfar
    have hfar' :
        fuchsianSourceAction (sourceFundamentalTransport z) • z =
          sourceFarRightVertex := by
      simpa only [sourceFundamentalRepresentative] using hfar
    have htoTwo :
        fuchsianSourceAction ((g₁ * g₂)⁻¹ * sourceFundamentalTransport z) • z =
          fuchsianTwoFixedPoint := by
      rw [map_mul, mul_smul, hfar', sourceFarRightVertex_eq_product_smul_two,
        map_inv, inv_smul_smul]
    exact (hz ((g₁ * g₂)⁻¹ * sourceFundamentalTransport z)).2 htoTwo


end SphereSixComplex.Periods.SourceChamberTopology
