module

public import SphereSixComplex.Periods.Uniformization.OrbitScalarRegularLocal
import all SphereSixComplex.Periods.Uniformization.OrbitScalarRegularLocal
public import SphereSixComplex.Periods.Uniformization.ScalarMonodromyExactAssembly
import all SphereSixComplex.Periods.Uniformization.ScalarMonodromyExactAssembly
public import SphereSixComplex.Geometry.EllipticLocalCoordinates
import all SphereSixComplex.Geometry.EllipticLocalCoordinates
public import SphereSixComplex.Geometry.ProperlyDiscontinuousSlice
import all SphereSixComplex.Geometry.ProperlyDiscontinuousSlice
public import Mathlib.Analysis.Complex.RemovableSingularity
import all Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

/-!
# Removable elliptic corners of the orbit-assembled scalar

The scalar is already holomorphic away from the two elliptic orbit types.  This file proves the
remaining continuity at the finite polygon vertices from the closed-chamber Carathéodory
extension, then applies the removable-singularity theorem.
-/

open Complex Filter Set Topology UpperHalfPlane
open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FreeProductTorsion
open SphereSixComplex.TriangleGroup.FuchsianFundamentalDomain
open SphereSixComplex.TriangleGroup.FuchsianTriangleCover
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.Periods.TriangleReflections
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry

private theorem sourceRightUHP_continuous : Continuous sourceRightUHP := by
  rw [continuous_induced_rng]
  change Continuous (fun z : UpperHalfPlane ↦ sourceRight (z : ℂ))
  unfold sourceRight
  fun_prop

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

private theorem fundamentalTriangle_mapsTo_sourceFiniteClosedChamber :
    MapsTo ((↑) : UpperHalfPlane → ℂ) fundamentalTriangle
      MonodromyScalarBranch.sourceFiniteClosedChamber := by
  intro z hz
  exact ⟨hz.1, hz.2.1, z.im_pos, hz.2.2⟩

private theorem sourceRight_rightFundamentalTriangle_mapsTo_sourceFiniteClosedChamber :
    MapsTo (fun z : UpperHalfPlane ↦ (sourceRightUHP z : ℂ)) rightFundamentalTriangle
      MonodromyScalarBranch.sourceFiniteClosedChamber := by
  intro z hz
  exact fundamentalTriangle_mapsTo_sourceFiniteClosedChamber
    (sourceRightUHP_mem_fundamentalTriangle_of_mem_right hz)

private theorem sourceScalarTriangleMap_continuousOn_fundamentalTriangle
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousOn (fun z : UpperHalfPlane ↦ sourceScalarTriangleMap S (z : ℂ))
      fundamentalTriangle :=
  (MonodromyScalarBranch.sourceScalarTriangleMap_continuousOn_sourceFiniteClosedChamber
      (S := S)).comp UpperHalfPlane.continuous_coe.continuousOn
    fundamentalTriangle_mapsTo_sourceFiniteClosedChamber

private theorem sourceScalarTriangleMap_sourceRight_continuousOn_rightFundamentalTriangle
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousOn
      (fun z : UpperHalfPlane ↦
        star (sourceScalarTriangleMap S (sourceRightUHP z : ℂ)))
      rightFundamentalTriangle := by
  exact ((MonodromyScalarBranch.sourceScalarTriangleMap_continuousOn_sourceFiniteClosedChamber
      (S := S)).comp
        (UpperHalfPlane.continuous_coe.comp sourceRightUHP_continuous).continuousOn
        sourceRight_rightFundamentalTriangle_mapsTo_sourceFiniteClosedChamber).star

private theorem sourceScalarRightDoubleMap_eq_seed_on_fundamentalTriangle
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : UpperHalfPlane}
    (hz : z ∈ fundamentalTriangle) :
    sourceScalarRightDoubleMap S (z : ℂ) = sourceScalarTriangleMap S (z : ℂ) :=
  sourceScalarRightDoubleMap_eq_seed_of_re_le_public S hz.2.1

private theorem sourceScalarRightDoubleMap_eq_reflected_seed_on_rightFundamentalTriangle
    (S : ChamberCaratheodorySeed sourceBoundedChamber) {z : UpperHalfPlane}
    (hz : z ∈ rightFundamentalTriangle) :
    sourceScalarRightDoubleMap S (z : ℂ) =
      star (sourceScalarTriangleMap S (sourceRightUHP z : ℂ)) := by
  let u : UpperHalfPlane := sourceRightUHP z
  have hu : u ∈ fundamentalTriangle :=
    sourceRightUHP_mem_fundamentalTriangle_of_mem_right hz
  have hreflect := sourceScalarRightDoubleMap_reflected_fundamental_public S hu
  have hinvol : sourceRight (u : ℂ) = (z : ℂ) := by
    change sourceRight (sourceRight (z : ℂ)) = (z : ℂ)
    exact sourceRight_involutive (z : ℂ)
  rw [hinvol] at hreflect
  simpa [u] using hreflect

private theorem fuchsianOne_mem_rightFundamentalTriangle :
    fuchsianOneFixedPoint ∈ rightFundamentalTriangle := by
  change 1 / 2 ≤ (1 : ℝ) / 2 ∧
    (1 : ℝ) / 2 ≤ 1 + Real.sqrt 2 / 2 ∧
      1 ≤ normSq (1 - (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ))
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · norm_num
  constructor
  · linarith
  · norm_num [normSq_apply]
    nlinarith

private theorem fuchsianTwo_not_mem_closure_rightFundamentalTriangle :
    fuchsianTwoFixedPoint ∉ closure rightFundamentalTriangle := by
  have hclosed : IsClosed {z : UpperHalfPlane | 1 / 2 ≤ z.re} :=
    isClosed_Ici.preimage (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)
  have hsubset : rightFundamentalTriangle ⊆ {z : UpperHalfPlane | 1 / 2 ≤ z.re} :=
    fun _ hz ↦ hz.1
  intro hmem
  have hre := closure_minimal hsubset hclosed hmem
  change 1 / 2 ≤ -Real.sqrt 2 / 2 at hre
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- The explicit right double is continuous on the doubled closed fundamental polygon at the
order-three vertex. -/
theorem sourceScalarRightDoubleMap_continuousWithinAt_oriented_one
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ sourceScalarRightDoubleMap S (z : ℂ))
      orientedFundamentalRegion fuchsianOneFixedPoint := by
  apply ContinuousWithinAt.union
  · exact (sourceScalarTriangleMap_continuousOn_fundamentalTriangle S
      fuchsianOneFixedPoint fuchsianOneFixedPoint_mem_fundamentalTriangle).congr
        (fun z hz ↦ sourceScalarRightDoubleMap_eq_seed_on_fundamentalTriangle S hz)
        (sourceScalarRightDoubleMap_eq_seed_on_fundamentalTriangle S
          fuchsianOneFixedPoint_mem_fundamentalTriangle)
  · exact
      (sourceScalarTriangleMap_sourceRight_continuousOn_rightFundamentalTriangle S
        fuchsianOneFixedPoint fuchsianOne_mem_rightFundamentalTriangle).congr
          (fun z hz ↦
            sourceScalarRightDoubleMap_eq_reflected_seed_on_rightFundamentalTriangle S hz)
          (sourceScalarRightDoubleMap_eq_reflected_seed_on_rightFundamentalTriangle S
            fuchsianOne_mem_rightFundamentalTriangle)

/-- The same continuity statement at the distinguished order-four vertex. -/
theorem sourceScalarRightDoubleMap_continuousWithinAt_oriented_two
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ sourceScalarRightDoubleMap S (z : ℂ))
      orientedFundamentalRegion fuchsianTwoFixedPoint := by
  apply ContinuousWithinAt.union
  · exact (sourceScalarTriangleMap_continuousOn_fundamentalTriangle S
      fuchsianTwoFixedPoint fuchsianTwoFixedPoint_mem_fundamentalTriangle).congr
        (fun z hz ↦ sourceScalarRightDoubleMap_eq_seed_on_fundamentalTriangle S hz)
        (sourceScalarRightDoubleMap_eq_seed_on_fundamentalTriangle S
          fuchsianTwoFixedPoint_mem_fundamentalTriangle)
  · exact continuousWithinAt_of_notMem_closure
      fuchsianTwo_not_mem_closure_rightFundamentalTriangle

/-! ## Transporting closed-polygon continuity -/

private theorem orbitAssembledScalar_continuousWithinAt_oriented
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (c : UpperHalfPlane)
    (hc : c ∈ orientedFundamentalRegion)
    (h : ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ sourceScalarRightDoubleMap S (z : ℂ))
      orientedFundamentalRegion c) :
    ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      orientedFundamentalRegion c := by
  exact h.congr
    (fun z hz ↦ orbitAssembledScalar_eq_rightDouble_on_fundamental
      S hconsistent hz)
    (orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent
      hc)

private theorem orbitAssembledScalar_continuousWithinAt_smul_preimage
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S)
    (g : Delta) (c d : UpperHalfPlane)
    (hgc : fuchsianSourceAction g • c = d)
    (h : ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      orientedFundamentalRegion d) :
    ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      ((fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) ⁻¹'
        orientedFundamentalRegion) c := by
  let T : UpperHalfPlane → UpperHalfPlane := fun z ↦ fuchsianSourceAction g • z
  have hT : ContinuousWithinAt T (T ⁻¹' orientedFundamentalRegion) c :=
    ((fuchsianSourceAction_contMDiff g 0).continuous.continuousAt).continuousWithinAt
  have hcomp : ContinuousWithinAt
      ((fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ)) ∘ T)
      (T ⁻¹' orientedFundamentalRegion) c :=
    h.comp_of_eq hT (fun _ hz ↦ hz) hgc
  exact hcomp.congr
    (fun z _ ↦ (orbitAssembledScalar_invariant S hconsistent g z).symm)
    (by simpa only [Function.comp_apply, T] using
      (orbitAssembledScalar_invariant S hconsistent g c).symm)

/-! ## The order-three rotation cover -/

private def sourceBroadStrip : Set UpperHalfPlane :=
  {z | -Real.sqrt 2 / 2 < z.re ∧ z.re < 1 + Real.sqrt 2 / 2}

private theorem mem_orientedFundamentalRegion_of_broad_of_two_norms
    {z : UpperHalfPlane} (hb : z ∈ sourceBroadStrip)
    (hn : 1 ≤ normSq (z : ℂ)) (hnr : 1 ≤ normSq (1 - (z : ℂ))) :
    z ∈ orientedFundamentalRegion := by
  by_cases hre : z.re ≤ 1 / 2
  · exact Or.inl ⟨hb.1.le, hre, hn⟩
  · exact Or.inr ⟨le_of_not_ge hre, hb.2.le, hnr⟩

private theorem gOne_normSq_ge_one_of
    (z : UpperHalfPlane)
    (hn : normSq (z : ℂ) ≤ 1)
    (hcmp : normSq (z : ℂ) ≤ normSq (1 - (z : ℂ))) :
    1 ≤ normSq ((fuchsianSourceAction g₁ • z : UpperHalfPlane) : ℂ) ∧
      1 ≤ normSq (1 - ((fuchsianSourceAction g₁ • z : UpperHalfPlane) : ℂ)) := by
  have hzpos : 0 < normSq (z : ℂ) := z.normSq_pos
  have happly := fuchsianSourceAction_g₁_apply z
  constructor
  · change 1 ≤ normSq (((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ)
    rw [happly, normSq_div]
    have hnum : normSq ((z : ℂ) - 1) = normSq (1 - (z : ℂ)) := by
      simp [normSq_apply]
      ring
    rw [hnum]
    exact (le_div_iff₀ hzpos).2 (by simpa using hcmp)
  · have hone : 1 - ((fuchsianSourceAction g₁ • z : UpperHalfPlane) : ℂ) =
        1 / (z : ℂ) := by
      change 1 - (((fuchsianSourceAction g₁) z : UpperHalfPlane) : ℂ) = _
      rw [happly]
      field_simp [z.ne_zero]
      ring
    rw [hone, normSq_div]
    norm_num [one_div]
    exact (one_le_inv₀ hzpos).2 hn

private theorem gOne_sq_normSq_ge_one_of
    (z : UpperHalfPlane)
    (hnr : normSq (1 - (z : ℂ)) ≤ 1)
    (hcmp : normSq (1 - (z : ℂ)) ≤ normSq (z : ℂ)) :
    1 ≤ normSq ((fuchsianSourceAction (g₁ ^ 2) • z : UpperHalfPlane) : ℂ) ∧
      1 ≤ normSq
        (1 - ((fuchsianSourceAction (g₁ ^ 2) • z : UpperHalfPlane) : ℂ)) := by
  have hden : 0 < normSq (1 - (z : ℂ)) := by
    rw [Complex.normSq_pos]
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    exact z.im_pos.ne' him
  have happly := SphereSixComplex.TriangleGroup.FuchsianPingPong.gOne_sq_apply z
  constructor
  · change 1 ≤ normSq (((fuchsianSourceAction (g₁ ^ 2)) z : UpperHalfPlane) : ℂ)
    rw [happly, normSq_div]
    norm_num [one_div]
    exact (one_le_inv₀ hden).2 hnr
  · have hone :
        1 - ((fuchsianSourceAction (g₁ ^ 2) • z : UpperHalfPlane) : ℂ) =
          -(z : ℂ) / (1 - (z : ℂ)) := by
      change 1 - (((fuchsianSourceAction (g₁ ^ 2)) z : UpperHalfPlane) : ℂ) = _
      rw [happly]
      have hne : (1 : ℂ) - (z : ℂ) ≠ 0 := Complex.normSq_pos.mp hden
      field_simp [hne]
      ring
    rw [hone, normSq_div, normSq_neg]
    exact (le_div_iff₀ hden).2 (by simpa using hcmp)

private def sourceDeckSector (g : Delta) : Set UpperHalfPlane :=
  (fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) ⁻¹'
    orientedFundamentalRegion

private def sourceOneBroadNeighborhood : Set UpperHalfPlane :=
  sourceBroadStrip ∩
    (fun z : UpperHalfPlane ↦ fuchsianSourceAction g₁ • z) ⁻¹' sourceBroadStrip ∩
    (fun z : UpperHalfPlane ↦ fuchsianSourceAction (g₁ ^ 2) • z) ⁻¹' sourceBroadStrip

private theorem sourceBroadStrip_isOpen : IsOpen sourceBroadStrip := by
  exact (isOpen_lt continuous_const
    (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)).inter
      (isOpen_lt (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)
        continuous_const)

private theorem fuchsianOne_mem_sourceBroadStrip :
    fuchsianOneFixedPoint ∈ sourceBroadStrip := by
  change -Real.sqrt 2 / 2 < (1 : ℝ) / 2 ∧
    (1 : ℝ) / 2 < 1 + Real.sqrt 2 / 2
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  constructor <;> linarith

private theorem sourceOneBroadNeighborhood_mem_nhds :
    sourceOneBroadNeighborhood ∈ nhds fuchsianOneFixedPoint := by
  have hb : sourceBroadStrip ∈ nhds fuchsianOneFixedPoint :=
    sourceBroadStrip_isOpen.mem_nhds fuchsianOne_mem_sourceBroadStrip
  have hfixOne : fuchsianSourceAction g₁ • fuchsianOneFixedPoint =
      fuchsianOneFixedPoint := fuchsianOneFixedPoint_fixed
  have hfixTwo : fuchsianSourceAction (g₁ ^ 2) • fuchsianOneFixedPoint =
      fuchsianOneFixedPoint :=
    (FreeProductTorsion.fuchsianSourceAction_gOne_sq_fixed_iff _).2 rfl
  refine inter_mem (inter_mem hb ?_) ?_
  · exact (fuchsianSourceAction_contMDiff g₁ 0).continuous.continuousAt
      (by simpa only [hfixOne] using hb)
  · exact (fuchsianSourceAction_contMDiff (g₁ ^ 2) 0).continuous.continuousAt
      (by simpa only [hfixTwo] using hb)

private theorem sourceOneBroadNeighborhood_subset_rotationSectors :
    sourceOneBroadNeighborhood ⊆
      sourceDeckSector 1 ∪ sourceDeckSector g₁ ∪ sourceDeckSector (g₁ ^ 2) := by
  intro z hz
  rcases hz with ⟨⟨hb0, hb1⟩, hb2⟩
  by_cases hn : 1 ≤ normSq (z : ℂ)
  · by_cases hnr : 1 ≤ normSq (1 - (z : ℂ))
    · left
      left
      change z ∈ orientedFundamentalRegion
      exact mem_orientedFundamentalRegion_of_broad_of_two_norms hb0 hn hnr
    · right
      have hpair := gOne_sq_normSq_ge_one_of z (le_of_not_ge hnr)
        ((le_of_not_ge hnr).trans hn)
      exact mem_orientedFundamentalRegion_of_broad_of_two_norms hb2 hpair.1 hpair.2
  · by_cases hcmp : normSq (z : ℂ) ≤ normSq (1 - (z : ℂ))
    · left
      right
      have hpair := gOne_normSq_ge_one_of z (le_of_not_ge hn) hcmp
      exact mem_orientedFundamentalRegion_of_broad_of_two_norms hb1 hpair.1 hpair.2
    · right
      have hpair := gOne_sq_normSq_ge_one_of z
        ((le_of_not_ge hcmp).trans (le_of_not_ge hn)) (le_of_not_ge hcmp)
      exact mem_orientedFundamentalRegion_of_broad_of_two_norms hb2 hpair.1 hpair.2

/-- The orbit-assembled scalar is continuous at the order-three elliptic point. -/
theorem orbitAssembledScalar_continuousAt_fuchsianOne
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    ContinuousAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      fuchsianOneFixedPoint := by
  have hbase := orbitAssembledScalar_continuousWithinAt_oriented S hconsistent
    fuchsianOneFixedPoint (Or.inl fuchsianOneFixedPoint_mem_fundamentalTriangle)
    (sourceScalarRightDoubleMap_continuousWithinAt_oriented_one S)
  have hzero : ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      (sourceDeckSector 1) fuchsianOneFixedPoint := by
    change ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      orientedFundamentalRegion fuchsianOneFixedPoint
    exact hbase
  have hone := orbitAssembledScalar_continuousWithinAt_smul_preimage
    S hconsistent g₁ fuchsianOneFixedPoint fuchsianOneFixedPoint
    fuchsianOneFixedPoint_fixed hbase
  have htwo := orbitAssembledScalar_continuousWithinAt_smul_preimage
    S hconsistent (g₁ ^ 2) fuchsianOneFixedPoint fuchsianOneFixedPoint
    ((FreeProductTorsion.fuchsianSourceAction_gOne_sq_fixed_iff _).2 rfl) hbase
  have hunion : ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      (sourceDeckSector 1 ∪ sourceDeckSector g₁ ∪ sourceDeckSector (g₁ ^ 2))
      fuchsianOneFixedPoint := (hzero.union hone).union htwo
  exact (hunion.mono sourceOneBroadNeighborhood_subset_rotationSectors).continuousAt
    sourceOneBroadNeighborhood_mem_nhds

/-! ## The order-four rotation cover -/

private theorem sourceFarRightVertex_mem_rightFundamentalTriangle :
    sourceFarRightVertex ∈ rightFundamentalTriangle := by
  change 1 / 2 ≤ (sourceRight (fuchsianTwoFixedPoint : ℂ)).re ∧
    (sourceRight (fuchsianTwoFixedPoint : ℂ)).re ≤ 1 + Real.sqrt 2 / 2 ∧
      1 ≤ normSq (1 - sourceRight (fuchsianTwoFixedPoint : ℂ))
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · simp [sourceRight, fuchsianTwoFixedPoint]
    linarith
  constructor
  · simp [sourceRight, fuchsianTwoFixedPoint]
    linarith
  · norm_num [sourceRight, fuchsianTwoFixedPoint, normSq_apply]
    nlinarith

private theorem sourceFarRightVertex_not_mem_closure_fundamentalTriangle :
    sourceFarRightVertex ∉ closure fundamentalTriangle := by
  have hclosed : IsClosed {z : UpperHalfPlane | z.re ≤ 1 / 2} :=
    isClosed_Iic.preimage (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)
  have hsubset : fundamentalTriangle ⊆ {z : UpperHalfPlane | z.re ≤ 1 / 2} :=
    fun _ hz ↦ hz.2.1
  intro hmem
  have hre := closure_minimal hsubset hclosed hmem
  change (sourceRight (fuchsianTwoFixedPoint : ℂ)).re ≤ 1 / 2 at hre
  rw [sourceRight_re] at hre
  norm_num [fuchsianTwoFixedPoint] at hre
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- The explicit right double is continuous at the translated order-four vertex from within the
closed doubled polygon. -/
theorem sourceScalarRightDoubleMap_continuousWithinAt_oriented_far
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ sourceScalarRightDoubleMap S (z : ℂ))
      orientedFundamentalRegion sourceFarRightVertex := by
  apply ContinuousWithinAt.union
  · exact continuousWithinAt_of_notMem_closure
      sourceFarRightVertex_not_mem_closure_fundamentalTriangle
  · exact
      (sourceScalarTriangleMap_sourceRight_continuousOn_rightFundamentalTriangle S
        sourceFarRightVertex sourceFarRightVertex_mem_rightFundamentalTriangle).congr
          (fun z hz ↦
            sourceScalarRightDoubleMap_eq_reflected_seed_on_rightFundamentalTriangle S hz)
          (sourceScalarRightDoubleMap_eq_reflected_seed_on_rightFundamentalTriangle S
            sourceFarRightVertex_mem_rightFundamentalTriangle)

private theorem orderFourCayley_denominator_pos (z : UpperHalfPlane) :
    0 < normSq ((z : ℂ) - starRingEnd ℂ (fuchsianTwoFixedPoint : ℂ)) := by
  rw [Complex.normSq_pos]
  intro hzero
  have him := congrArg Complex.im hzero
  simp [fuchsianTwoFixedPoint] at him
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  linarith [z.im_pos]

private theorem orderFourCayley_re_formula (z : UpperHalfPlane) :
    (orderFourCayley z).re =
      (normSq (z : ℂ) + Real.sqrt 2 * z.re) /
        normSq ((z : ℂ) - starRingEnd ℂ (fuchsianTwoFixedPoint : ℂ)) := by
  unfold orderFourCayley cayleyCoordinate
  rw [Complex.div_re]
  simp only [fuchsianTwoFixedPoint, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  norm_num
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ring_nf

private theorem orderFourCayley_im_formula (z : UpperHalfPlane) :
    (orderFourCayley z).im =
      (-Real.sqrt 2 * z.re - 1) /
        normSq ((z : ℂ) - starRingEnd ℂ (fuchsianTwoFixedPoint : ℂ)) := by
  unfold orderFourCayley cayleyCoordinate
  rw [Complex.div_im]
  simp only [fuchsianTwoFixedPoint, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  norm_num
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hs2]
  ring

private def sourceTwoBroadStrip : Set UpperHalfPlane :=
  {z | -(1 / 2 : ℝ) - Real.sqrt 2 < z.re ∧ z.re < 1 / 2}

private def sourceTwoBaseSector : Set UpperHalfPlane :=
  sourceDeckSector 1 ∪ sourceDeckSector (g₁ * g₂)

private theorem mem_sourceTwoBaseSector_of_broad_of_cone
    {z : UpperHalfPlane} (hb : z ∈ sourceTwoBroadStrip)
    (hcone : |(orderFourCayley z).im| ≤ (orderFourCayley z).re) :
    z ∈ sourceTwoBaseSector := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hden := orderFourCayley_denominator_pos z
  rcases hb with ⟨hbLower, hbUpper⟩
  by_cases him : (orderFourCayley z).im ≤ 0
  · have hsum : 0 ≤ (orderFourCayley z).re + (orderFourCayley z).im := by
      rw [abs_of_nonpos him] at hcone
      linarith
    have hsumEq :
        (orderFourCayley z).re + (orderFourCayley z).im =
          (normSq (z : ℂ) - 1) /
            normSq ((z : ℂ) - starRingEnd ℂ (fuchsianTwoFixedPoint : ℂ)) := by
      rw [orderFourCayley_re_formula, orderFourCayley_im_formula]
      ring
    rw [hsumEq] at hsum
    have hnraw := (le_div_iff₀ hden).mp hsum
    have hn : 1 ≤ normSq (z : ℂ) := by
      simpa only [zero_mul, sub_nonneg] using hnraw
    rw [orderFourCayley_im_formula] at him
    have hreRaw := (div_le_iff₀ hden).mp him
    have hre : -Real.sqrt 2 / 2 ≤ z.re := by
      simp only [zero_mul] at hreRaw
      nlinarith
    left
    change z ∈ orientedFundamentalRegion
    exact Or.inl ⟨hre, hbUpper.le, hn⟩
  · have himnonneg : 0 ≤ (orderFourCayley z).im := le_of_not_ge him
    have hdiff : 0 ≤ (orderFourCayley z).re - (orderFourCayley z).im := by
      rw [abs_of_nonneg himnonneg] at hcone
      linarith
    have hdiffEq :
        (orderFourCayley z).re - (orderFourCayley z).im =
          (normSq (z : ℂ) + 2 * Real.sqrt 2 * z.re + 1) /
            normSq ((z : ℂ) - starRingEnd ℂ (fuchsianTwoFixedPoint : ℂ)) := by
      rw [orderFourCayley_re_formula, orderFourCayley_im_formula]
      ring
    rw [hdiffEq] at hdiff
    have hnraw := (le_div_iff₀ hden).mp hdiff
    have hnshift : 1 ≤ normSq ((z : ℂ) + Real.sqrt 2) := by
      simp only [zero_mul] at hnraw
      have heq : normSq ((z : ℂ) + Real.sqrt 2) =
          normSq (z : ℂ) + 2 * Real.sqrt 2 * z.re + 2 := by
        simp [normSq_apply]
        nlinarith
      rw [heq]
      nlinarith
    rw [orderFourCayley_im_formula] at himnonneg
    have hreRaw := (le_div_iff₀ hden).mp himnonneg
    have hre : z.re ≤ -Real.sqrt 2 / 2 := by
      simp only [zero_mul] at hreRaw
      nlinarith
    right
    change fuchsianSourceAction (g₁ * g₂) • z ∈ orientedFundamentalRegion
    right
    have happly := FuchsianFundamentalDomain.product_apply z
    refine ⟨?_, ?_, ?_⟩
    · have hreApply : (fuchsianSourceAction (g₁ * g₂) • z).re =
          z.re + (1 + Real.sqrt 2) := by
        change (((fuchsianSourceAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ).re = _
        simpa [FuchsianFundamentalDomain.cuspWidth] using congrArg Complex.re happly
      rw [hreApply]
      linarith [hbLower]
    · have hreApply : (fuchsianSourceAction (g₁ * g₂) • z).re =
          z.re + (1 + Real.sqrt 2) := by
        change (((fuchsianSourceAction (g₁ * g₂)) z : UpperHalfPlane) : ℂ).re = _
        simpa [FuchsianFundamentalDomain.cuspWidth] using congrArg Complex.re happly
      rw [hreApply]
      linarith
    · change 1 ≤ normSq (1 - (((fuchsianSourceAction (g₁ * g₂)) z :
        UpperHalfPlane) : ℂ))
      rw [happly]
      have heq : normSq (1 - ((z : ℂ) + FuchsianFundamentalDomain.cuspWidth)) =
          normSq ((z : ℂ) + Real.sqrt 2) := by
        simp [FuchsianFundamentalDomain.cuspWidth, normSq_apply]
        ring
      rwa [heq]

private theorem orderFourCayley_gTwo_pow (k : ℕ) (z : UpperHalfPlane) :
    orderFourCayley (fuchsianSourceAction (g₂ ^ k) • z) =
      orderFourMultiplier ^ k * orderFourCayley z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', map_mul, mul_smul, orderFourCayley_generator, ih,
        pow_succ', mul_assoc]

private theorem quarter_rotation_cone_cases (w : ℂ) :
    |w.im| ≤ w.re ∨
      |(orderFourMultiplier * w).im| ≤ (orderFourMultiplier * w).re ∨
      |(orderFourMultiplier ^ 2 * w).im| ≤ (orderFourMultiplier ^ 2 * w).re ∨
      |(orderFourMultiplier ^ 3 * w).im| ≤ (orderFourMultiplier ^ 3 * w).re := by
  have hcases : |w.im| ≤ w.re ∨ |w.re| ≤ w.im ∨
      |w.im| ≤ -w.re ∨ |w.re| ≤ -w.im := by
    by_cases hxy : |w.im| ≤ |w.re|
    · by_cases hx : 0 ≤ w.re
      · exact Or.inl (by simpa [abs_of_nonneg hx] using hxy)
      · exact Or.inr (Or.inr (Or.inl (by
          rw [abs_of_nonpos (le_of_not_ge hx)] at hxy
          exact hxy)))
    · have hyx : |w.re| ≤ |w.im| := (le_of_not_ge hxy)
      by_cases hy : 0 ≤ w.im
      · exact Or.inr (Or.inl (by simpa [abs_of_nonneg hy] using hyx))
      · exact Or.inr (Or.inr (Or.inr (by
          rw [abs_of_nonpos (le_of_not_ge hy)] at hyx
          exact hyx)))
  rcases hcases with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by
      simpa [orderFourMultiplier, Complex.mul_re, Complex.mul_im] using h))
  · exact Or.inr (Or.inr (Or.inl (by
      norm_num [orderFourMultiplier, pow_two, Complex.mul_re, Complex.mul_im]
      exact h)))
  · exact Or.inr (Or.inr (Or.inr (by
      norm_num [orderFourMultiplier, pow_succ, Complex.mul_re, Complex.mul_im]
      exact h)))

private def sourceTwoRotatedSector (k : ℕ) : Set UpperHalfPlane :=
  sourceDeckSector (g₂ ^ k) ∪ sourceDeckSector ((g₁ * g₂) * g₂ ^ k)

private theorem mem_sourceTwoRotatedSector_of_image_mem_base
    {k : ℕ} {z : UpperHalfPlane}
    (hz : fuchsianSourceAction (g₂ ^ k) • z ∈ sourceTwoBaseSector) :
    z ∈ sourceTwoRotatedSector k := by
  simpa only [sourceTwoBaseSector, sourceTwoRotatedSector, sourceDeckSector,
    Set.mem_union, Set.mem_preimage, map_one, one_smul, map_mul, mul_smul] using hz

private def sourceTwoBroadNeighborhood : Set UpperHalfPlane :=
  sourceTwoBroadStrip ∩
    (fun z : UpperHalfPlane ↦ fuchsianSourceAction g₂ • z) ⁻¹' sourceTwoBroadStrip ∩
    (fun z : UpperHalfPlane ↦ fuchsianSourceAction (g₂ ^ 2) • z) ⁻¹' sourceTwoBroadStrip ∩
    (fun z : UpperHalfPlane ↦ fuchsianSourceAction (g₂ ^ 3) • z) ⁻¹' sourceTwoBroadStrip

private theorem sourceTwoBroadStrip_isOpen : IsOpen sourceTwoBroadStrip := by
  exact (isOpen_lt continuous_const
    (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)).inter
      (isOpen_lt (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)
        continuous_const)

private theorem fuchsianTwo_mem_sourceTwoBroadStrip :
    fuchsianTwoFixedPoint ∈ sourceTwoBroadStrip := by
  change -(1 / 2 : ℝ) - Real.sqrt 2 < -Real.sqrt 2 / 2 ∧
    -Real.sqrt 2 / 2 < 1 / 2
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  constructor <;> linarith

private theorem gTwo_pow_smul_fuchsianTwo (k : ℕ) :
    fuchsianSourceAction (g₂ ^ k) • fuchsianTwoFixedPoint =
      fuchsianTwoFixedPoint := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, map_mul, mul_smul, fuchsianTwoFixedPoint_fixed, ih]

private theorem sourceTwoBroadNeighborhood_mem_nhds :
    sourceTwoBroadNeighborhood ∈ nhds fuchsianTwoFixedPoint := by
  have hb : sourceTwoBroadStrip ∈ nhds fuchsianTwoFixedPoint :=
    sourceTwoBroadStrip_isOpen.mem_nhds fuchsianTwo_mem_sourceTwoBroadStrip
  have hpre (k : ℕ) :
      (fun z : UpperHalfPlane ↦ fuchsianSourceAction (g₂ ^ k) • z) ⁻¹'
          sourceTwoBroadStrip ∈ nhds fuchsianTwoFixedPoint :=
    (fuchsianSourceAction_contMDiff (g₂ ^ k) 0).continuous.continuousAt
      (by simpa only [gTwo_pow_smul_fuchsianTwo] using hb)
  have hzero : sourceTwoBroadStrip ∈ nhds fuchsianTwoFixedPoint := hb
  have hone : (fun z : UpperHalfPlane ↦ fuchsianSourceAction g₂ • z) ⁻¹'
      sourceTwoBroadStrip ∈ nhds fuchsianTwoFixedPoint := by
    simpa only [pow_one] using hpre 1
  exact inter_mem (inter_mem (inter_mem hzero hone) (hpre 2)) (hpre 3)

private theorem sourceTwoBroadNeighborhood_subset_rotationSectors :
    sourceTwoBroadNeighborhood ⊆
      sourceTwoRotatedSector 0 ∪ sourceTwoRotatedSector 1 ∪
        sourceTwoRotatedSector 2 ∪ sourceTwoRotatedSector 3 := by
  intro z hz
  rcases hz with ⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩
  rcases quarter_rotation_cone_cases (orderFourCayley z) with
      hcone | hcone | hcone | hcone
  · left
    left
    left
    apply mem_sourceTwoRotatedSector_of_image_mem_base
    simpa only [pow_zero, map_one, one_smul] using
      (mem_sourceTwoBaseSector_of_broad_of_cone hb0 hcone)
  · left
    left
    right
    apply mem_sourceTwoRotatedSector_of_image_mem_base
    apply mem_sourceTwoBaseSector_of_broad_of_cone hb1
    have heq : orderFourCayley (fuchsianSourceAction g₂ • z) =
        orderFourMultiplier * orderFourCayley z := by
      simpa only [pow_one] using orderFourCayley_gTwo_pow 1 z
    rw [heq]
    exact hcone
  · left
    right
    apply mem_sourceTwoRotatedSector_of_image_mem_base
    apply mem_sourceTwoBaseSector_of_broad_of_cone hb2
    rw [orderFourCayley_gTwo_pow]
    exact hcone
  · right
    apply mem_sourceTwoRotatedSector_of_image_mem_base
    apply mem_sourceTwoBaseSector_of_broad_of_cone hb3
    rw [orderFourCayley_gTwo_pow]
    exact hcone

private theorem product_mul_gTwo_pow_smul_fuchsianTwo (k : ℕ) :
    fuchsianSourceAction ((g₁ * g₂) * g₂ ^ k) • fuchsianTwoFixedPoint =
      sourceFarRightVertex := by
  rw [map_mul, mul_smul, gTwo_pow_smul_fuchsianTwo]
  exact sourceFarRightVertex_eq_product_smul_two.symm

private theorem orbitAssembledScalar_continuousWithinAt_twoRotatedSector
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) (k : ℕ) :
    ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      (sourceTwoRotatedSector k) fuchsianTwoFixedPoint := by
  have hbaseTwo := orbitAssembledScalar_continuousWithinAt_oriented S hconsistent
    fuchsianTwoFixedPoint (Or.inl fuchsianTwoFixedPoint_mem_fundamentalTriangle)
    (sourceScalarRightDoubleMap_continuousWithinAt_oriented_two S)
  have hbaseFar := orbitAssembledScalar_continuousWithinAt_oriented S hconsistent
    sourceFarRightVertex (Or.inr sourceFarRightVertex_mem_rightFundamentalTriangle)
    (sourceScalarRightDoubleMap_continuousWithinAt_oriented_far S)
  have hleft := orbitAssembledScalar_continuousWithinAt_smul_preimage
    S hconsistent (g₂ ^ k) fuchsianTwoFixedPoint fuchsianTwoFixedPoint
    (gTwo_pow_smul_fuchsianTwo k) hbaseTwo
  have hright := orbitAssembledScalar_continuousWithinAt_smul_preimage
    S hconsistent ((g₁ * g₂) * g₂ ^ k) fuchsianTwoFixedPoint
      sourceFarRightVertex (product_mul_gTwo_pow_smul_fuchsianTwo k) hbaseFar
  exact hleft.union hright

/-- The orbit-assembled scalar is continuous at the order-four elliptic point. -/
theorem orbitAssembledScalar_continuousAt_fuchsianTwo
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    ContinuousAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      fuchsianTwoFixedPoint := by
  have hzero := orbitAssembledScalar_continuousWithinAt_twoRotatedSector
    S hconsistent 0
  have hone := orbitAssembledScalar_continuousWithinAt_twoRotatedSector
    S hconsistent 1
  have htwo := orbitAssembledScalar_continuousWithinAt_twoRotatedSector
    S hconsistent 2
  have hthree := orbitAssembledScalar_continuousWithinAt_twoRotatedSector
    S hconsistent 3
  have hunion : ContinuousWithinAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      (sourceTwoRotatedSector 0 ∪ sourceTwoRotatedSector 1 ∪
        sourceTwoRotatedSector 2 ∪ sourceTwoRotatedSector 3)
      fuchsianTwoFixedPoint := ((hzero.union hone).union htwo).union hthree
  exact (hunion.mono sourceTwoBroadNeighborhood_subset_rotationSectors).continuousAt
    sourceTwoBroadNeighborhood_mem_nhds

/-! ## Punctured regularity and removable singularities -/

private theorem orbitAssembledScalar_eventually_regular_one
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    ∀ᶠ z in nhdsWithin fuchsianOneFixedPoint {fuchsianOneFixedPoint}ᶜ,
      FreeProductTorsion.IsFuchsianRegularPoint z := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianSourceAction_properlyDiscontinuous
  let K : UpperHalfPlane → ℂ := fun z ↦ orbitAssembledScalar S (z : ℂ)
  obtain ⟨U, hUopen, honeU, _hUinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) fuchsianOneFixedPoint
  have hKone : K fuchsianOneFixedPoint = 0 := by
    exact orbitAssembledScalar_fuchsianOne S hconsistent
  have hball : K ⁻¹' Metric.ball 0 (1 / 2 : ℝ) ∈ nhds fuchsianOneFixedPoint :=
    (orbitAssembledScalar_continuousAt_fuchsianOne S hconsistent)
      (Metric.isOpen_ball.mem_nhds (by
        change K fuchsianOneFixedPoint ∈ Metric.ball 0 (1 / 2 : ℝ)
        rw [hKone]
        norm_num))
  rw [eventually_nhdsWithin_iff]
  filter_upwards [inter_mem (hUopen.mem_nhds honeU) hball] with z hz hzne
  intro g
  constructor
  · intro hg
    have hinter : (((fun y : UpperHalfPlane ↦ g • y) '' U) ∩ U).Nonempty := by
      refine ⟨fuchsianOneFixedPoint, ⟨z, hz.1, ?_⟩, honeU⟩
      exact hg
    have hfix : fuchsianSourceAction g • fuchsianOneFixedPoint =
        fuchsianOneFixedPoint := (htranslate g).mp hinter
    have hzg : z = fuchsianOneFixedPoint := by
      calc
        z = fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
        _ = fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint := congrArg _ hg
        _ = fuchsianSourceAction g⁻¹ •
            (fuchsianSourceAction g • fuchsianOneFixedPoint) := congrArg _ hfix.symm
        _ = fuchsianOneFixedPoint := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact hzne hzg
  · intro hg
    have hKz : K z = 1 := by
      calc
        K z = K (fuchsianSourceAction g • z) := by
          simpa only [K] using (orbitAssembledScalar_invariant S hconsistent g z).symm
        _ = K fuchsianTwoFixedPoint := congrArg K hg
        _ = 1 := orbitAssembledScalar_fuchsianTwo S hconsistent
    have hzball := hz.2
    change dist (K z) 0 < (1 / 2 : ℝ) at hzball
    rw [hKz] at hzball
    norm_num at hzball

private theorem orbitAssembledScalar_eventually_regular_two
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    ∀ᶠ z in nhdsWithin fuchsianTwoFixedPoint {fuchsianTwoFixedPoint}ᶜ,
      FreeProductTorsion.IsFuchsianRegularPoint z := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianSourceAction_properlyDiscontinuous
  let K : UpperHalfPlane → ℂ := fun z ↦ orbitAssembledScalar S (z : ℂ)
  obtain ⟨U, hUopen, htwoU, _hUinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) fuchsianTwoFixedPoint
  have hKtwo : K fuchsianTwoFixedPoint = 1 := by
    exact orbitAssembledScalar_fuchsianTwo S hconsistent
  have hball : K ⁻¹' Metric.ball 1 (1 / 2 : ℝ) ∈ nhds fuchsianTwoFixedPoint :=
    (orbitAssembledScalar_continuousAt_fuchsianTwo S hconsistent)
      (Metric.isOpen_ball.mem_nhds (by
        change K fuchsianTwoFixedPoint ∈ Metric.ball 1 (1 / 2 : ℝ)
        rw [hKtwo]
        norm_num))
  rw [eventually_nhdsWithin_iff]
  filter_upwards [inter_mem (hUopen.mem_nhds htwoU) hball] with z hz hzne
  intro g
  constructor
  · intro hg
    have hKz : K z = 0 := by
      calc
        K z = K (fuchsianSourceAction g • z) := by
          simpa only [K] using (orbitAssembledScalar_invariant S hconsistent g z).symm
        _ = K fuchsianOneFixedPoint := congrArg K hg
        _ = 0 := orbitAssembledScalar_fuchsianOne S hconsistent
    have hzball := hz.2
    change dist (K z) 1 < (1 / 2 : ℝ) at hzball
    rw [hKz] at hzball
    norm_num at hzball
  · intro hg
    have hinter : (((fun y : UpperHalfPlane ↦ g • y) '' U) ∩ U).Nonempty := by
      refine ⟨fuchsianTwoFixedPoint, ⟨z, hz.1, ?_⟩, htwoU⟩
      exact hg
    have hfix : fuchsianSourceAction g • fuchsianTwoFixedPoint =
        fuchsianTwoFixedPoint := (htranslate g).mp hinter
    have hzg : z = fuchsianTwoFixedPoint := by
      calc
        z = fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
        _ = fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint := congrArg _ hg
        _ = fuchsianSourceAction g⁻¹ •
            (fuchsianSourceAction g • fuchsianTwoFixedPoint) := congrArg _ hfix.symm
        _ = fuchsianTwoFixedPoint := by
          rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact hzne hzg

private theorem orbitAssembledScalar_ambient_continuousAt
    (S : ChamberCaratheodorySeed sourceBoundedChamber) (c : UpperHalfPlane)
    (h : ContinuousAt
      (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ)) c) :
    ContinuousAt (orbitAssembledScalar S) (c : ℂ) := by
  have hcomp : ContinuousAt
      ((fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ)) ∘
        UpperHalfPlane.ofComplex) (c : ℂ) :=
    h.comp_of_eq (UpperHalfPlane.mdifferentiableAt_ofComplex c.im_pos).continuousAt
      (UpperHalfPlane.ofComplex_apply c)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds c.im_pos] with z hz
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

private theorem orbitAssembledScalar_ambient_differentiableAt_of_regular
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S)
    {z : ℂ} (hz : 0 < z.im)
    (hregular : FreeProductTorsion.IsFuchsianRegularPoint
      (⟨z, hz⟩ : UpperHalfPlane)) :
    DifferentiableAt ℂ (orbitAssembledScalar S) z := by
  let u : UpperHalfPlane := ⟨z, hz⟩
  have hmd := orbitAssembledScalar_mdifferentiableAt_of_regular
    S hconsistent u hregular
  have hcomp : DifferentiableAt ℂ
      ((fun w : UpperHalfPlane ↦ orbitAssembledScalar S (w : ℂ)) ∘
        UpperHalfPlane.ofComplex) (u : ℂ) :=
    UpperHalfPlane.mdifferentiableAt_iff.mp hmd
  change DifferentiableAt ℂ (orbitAssembledScalar S) (u : ℂ)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds u.im_pos] with w hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw]

private theorem orbitAssembledScalar_eventually_ambient_differentiable_one
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    ∀ᶠ z in nhdsWithin (fuchsianOneFixedPoint : ℂ)
        {(fuchsianOneFixedPoint : ℂ)}ᶜ,
      DifferentiableAt ℂ (orbitAssembledScalar S) z := by
  have hregular := orbitAssembledScalar_eventually_regular_one S hconsistent
  rw [eventually_nhdsWithin_iff] at hregular ⊢
  have hof : ContinuousAt UpperHalfPlane.ofComplex (fuchsianOneFixedPoint : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_ofComplex fuchsianOneFixedPoint.im_pos).continuousAt
  have hof' : Tendsto UpperHalfPlane.ofComplex (nhds (fuchsianOneFixedPoint : ℂ))
      (nhds fuchsianOneFixedPoint) := by
    change Tendsto UpperHalfPlane.ofComplex (nhds (fuchsianOneFixedPoint : ℂ))
      (nhds (UpperHalfPlane.ofComplex (fuchsianOneFixedPoint : ℂ))) at hof
    rw [show UpperHalfPlane.ofComplex (fuchsianOneFixedPoint : ℂ) =
      fuchsianOneFixedPoint by exact UpperHalfPlane.ofComplex_apply _] at hof
    exact hof
  have hpull := hof' hregular
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      fuchsianOneFixedPoint.im_pos, hpull] with z hz hreg hzne
  apply orbitAssembledScalar_ambient_differentiableAt_of_regular S hconsistent hz
  have hu : UpperHalfPlane.ofComplex z = (⟨z, hz⟩ : UpperHalfPlane) := by
    apply UpperHalfPlane.coe_injective
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  change UpperHalfPlane.ofComplex z ∈ {fuchsianOneFixedPoint}ᶜ →
    FreeProductTorsion.IsFuchsianRegularPoint (UpperHalfPlane.ofComplex z) at hreg
  rw [hu] at hreg
  apply hreg
  intro heq
  apply hzne
  exact congrArg ((↑) : UpperHalfPlane → ℂ) heq

private theorem orbitAssembledScalar_eventually_ambient_differentiable_two
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    ∀ᶠ z in nhdsWithin (fuchsianTwoFixedPoint : ℂ)
        {(fuchsianTwoFixedPoint : ℂ)}ᶜ,
      DifferentiableAt ℂ (orbitAssembledScalar S) z := by
  have hregular := orbitAssembledScalar_eventually_regular_two S hconsistent
  rw [eventually_nhdsWithin_iff] at hregular ⊢
  have hof : ContinuousAt UpperHalfPlane.ofComplex (fuchsianTwoFixedPoint : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_ofComplex fuchsianTwoFixedPoint.im_pos).continuousAt
  have hof' : Tendsto UpperHalfPlane.ofComplex (nhds (fuchsianTwoFixedPoint : ℂ))
      (nhds fuchsianTwoFixedPoint) := by
    change Tendsto UpperHalfPlane.ofComplex (nhds (fuchsianTwoFixedPoint : ℂ))
      (nhds (UpperHalfPlane.ofComplex (fuchsianTwoFixedPoint : ℂ))) at hof
    rw [show UpperHalfPlane.ofComplex (fuchsianTwoFixedPoint : ℂ) =
      fuchsianTwoFixedPoint by exact UpperHalfPlane.ofComplex_apply _] at hof
    exact hof
  have hpull := hof' hregular
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      fuchsianTwoFixedPoint.im_pos, hpull] with z hz hreg hzne
  apply orbitAssembledScalar_ambient_differentiableAt_of_regular S hconsistent hz
  have hu : UpperHalfPlane.ofComplex z = (⟨z, hz⟩ : UpperHalfPlane) := by
    apply UpperHalfPlane.coe_injective
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  change UpperHalfPlane.ofComplex z ∈ {fuchsianTwoFixedPoint}ᶜ →
    FreeProductTorsion.IsFuchsianRegularPoint (UpperHalfPlane.ofComplex z) at hreg
  rw [hu] at hreg
  apply hreg
  intro heq
  apply hzne
  exact congrArg ((↑) : UpperHalfPlane → ℂ) heq

/-- The removable order-three corner is holomorphic in the upper-half-plane manifold. -/
theorem orbitAssembledScalar_mdifferentiableAt_fuchsianOne
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    MDiffAt (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      fuchsianOneFixedPoint := by
  have han : AnalyticAt ℂ (orbitAssembledScalar S) (fuchsianOneFixedPoint : ℂ) :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (orbitAssembledScalar_eventually_ambient_differentiable_one S hconsistent)
      (orbitAssembledScalar_ambient_continuousAt S fuchsianOneFixedPoint
        (orbitAssembledScalar_continuousAt_fuchsianOne S hconsistent))
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  apply han.differentiableAt.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      fuchsianOneFixedPoint.im_pos] with z hz
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- The removable order-four corner is holomorphic in the upper-half-plane manifold. -/
theorem orbitAssembledScalar_mdifferentiableAt_fuchsianTwo
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    MDiffAt (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ))
      fuchsianTwoFixedPoint := by
  have han : AnalyticAt ℂ (orbitAssembledScalar S) (fuchsianTwoFixedPoint : ℂ) :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (orbitAssembledScalar_eventually_ambient_differentiable_two S hconsistent)
      (orbitAssembledScalar_ambient_continuousAt S fuchsianTwoFixedPoint
        (orbitAssembledScalar_continuousAt_fuchsianTwo S hconsistent))
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  apply han.differentiableAt.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
      fuchsianTwoFixedPoint.im_pos] with z hz
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- The consistent orbit construction is holomorphic on the entire upper half-plane; the only
points not covered by regular Schwarz patches are the two removable elliptic orbits. -/
theorem orbitAssembledScalar_mdifferentiable
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    MDiff (fun z : UpperHalfPlane ↦ orbitAssembledScalar S (z : ℂ)) := by
  intro z
  by_cases hone : ∃ g : Delta,
      fuchsianSourceAction g • z = fuchsianOneFixedPoint
  · obtain ⟨g, hg⟩ := hone
    apply orbitAssembledScalar_mdifferentiableAt_of_smul S hconsistent g z
    simpa only [hg] using
      (orbitAssembledScalar_mdifferentiableAt_fuchsianOne S hconsistent)
  by_cases htwo : ∃ g : Delta,
      fuchsianSourceAction g • z = fuchsianTwoFixedPoint
  · obtain ⟨g, hg⟩ := htwo
    apply orbitAssembledScalar_mdifferentiableAt_of_smul S hconsistent g z
    simpa only [hg] using
      (orbitAssembledScalar_mdifferentiableAt_fuchsianTwo S hconsistent)
  apply orbitAssembledScalar_mdifferentiableAt_of_regular S hconsistent z
  intro g
  exact ⟨fun hg ↦ hone ⟨g, hg⟩, fun hg ↦ htwo ⟨g, hg⟩⟩

/-- Ambient holomorphicity on the open upper half-plane, extracted from manifold
holomorphicity. -/
theorem orbitAssembledScalar_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    DifferentiableOn ℂ (orbitAssembledScalar S) scalarUpperHalfPlane := by
  have h := UpperHalfPlane.mdifferentiable_iff.mp
    (orbitAssembledScalar_mdifferentiable S hconsistent)
  exact h.congr (fun z hz ↦ by
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz])

/-- The globally holomorphic orbit scalar itself supplies the local-patch interface used by the
Tau Ceti continuation layer. -/
noncomputable def orbitAssembledScalarLocalPatches
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    OrbitAssembledScalarLocalPatches S where
  patch := fun _ ↦ orbitAssembledScalar S
  patch_analyticAt := fun z ↦
    ((orbitAssembledScalar_differentiableOn S hconsistent).analyticOnNhd
      scalarUpperHalfPlane_isOpen z z.im_pos)
  eventuallyEq := fun _ ↦ Filter.EventuallyEq.rfl

/-- The removable-corner construction gives the original chamber seed a Tau Ceti continuation
throughout the upper half-plane. -/
theorem orbitAssembledScalar_seed_continuesInside
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    TauCeti.ContinuesInside (sourceScalarTriangleMap S) sourceUpperHalfPlaneSet
      sourceScalarContinuationBase :=
  (orbitAssembledScalarLocalPatches S hconsistent).seed_continuesInside hconsistent

/-- Exact source-orbit data packaged for the automatic elliptic and cusp assembly. -/
noncomputable def orbitAssembledScalarAutomaticSourceScalarCore
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    SphereSixComplex.Periods.SourceAutomaticExactAssembly.AutomaticSourceScalarCore where
  scalar := orbitAssembledScalar S
  scalar_holomorphic := orbitAssembledScalar_differentiableOn S hconsistent
  scalar_invariant := orbitAssembledScalar_invariant S hconsistent
  scalar_surjective := orbitAssembledScalar_surjective S hconsistent
  scalar_eq_iff_orbit := orbitAssembledScalar_eq_iff_orbit S hconsistent
  scalar_at_one := orbitAssembledScalar_fuchsianOne S hconsistent
  scalar_at_two := orbitAssembledScalar_fuchsianTwo S hconsistent

private theorem orbitAssembledScalar_eqOn_seed
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    EqOn (orbitAssembledScalar S) (sourceScalarTriangleMap S) sourceOpenChamber := by
  intro z hz
  let w : UpperHalfPlane := ⟨z, hz.2.2.1⟩
  have hwfund : w ∈ orientedFundamentalRegion := by
    left
    exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2.2⟩
  rw [show z = (w : ℂ) by rfl,
    orbitAssembledScalar_eq_rightDouble_on_fundamental S hconsistent hwfund]
  exact sourceScalarRightDoubleMap_eq_seed S hz

/-- Fundamental-polygon consistency alone now produces the full exact source orbifold
coordinate; the finite elliptic corners have been discharged by removability above. -/
theorem nonempty_exactFuchsianOrbifoldCoordinate_of_fundamentalScalarConsistent
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (hconsistent : SourceFundamentalScalarConsistent S) :
    Nonempty ExactFuchsianOrbifoldCoordinate := by
  exact (orbitAssembledScalarAutomaticSourceScalarCore S hconsistent)
    |>.nonempty_exactFuchsianOrbifoldCoordinate_of_seed S
      (orbitAssembledScalar_eqOn_seed S hconsistent)


end SphereSixComplex.Periods.SourceChamberTopology
