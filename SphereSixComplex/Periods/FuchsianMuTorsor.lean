module

public import SphereSixComplex.Periods.EstablishedModularUniformization
public import SphereSixComplex.Periods.EstablishedProjectiveLineCohomology
public import SphereSixComplex.Periods.TorsorAlgebra
import all SphereSixComplex.Periods.FuchsianUniformizationBridge

/-!
# The affine `mu` torsor over the explicit Fuchsian quotient

The finite cyclic consistency and the local elliptic and cusp sections are completely explicit.
The remaining paper-specific step is analytic descent of these local sections to an
`O(-1)`-torsor on the quotient projective line.  We isolate that step as local Cech data and use
the established analytic `O(-1)` splitting to make the two local sections compatible.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

variable (E : EstablishedFuchsianModularParameter)

/-- The explicit local affine-torsor section at the order-three point. -/
@[expose] public def ellipticMuOne (z : UpperHalfPlane) : ℂ :=
  localMuOne (E.modularParameter.tau z)

/-- The explicit local affine-torsor section at the order-four point. -/
@[expose] public def ellipticMuTwo (z : UpperHalfPlane) : ℂ :=
  localMuTwo (E.modularParameter.tau z)

/-- The distinguished local section at the cusp. -/
@[expose] public def cuspLocalMu
    (_E : EstablishedFuchsianModularParameter) (_z : UpperHalfPlane) : ℂ := 0

public theorem tau_coe_ne_one (z : UpperHalfPlane) :
    (E.modularParameter.tau z : ℂ) ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him
  exact (E.modularParameter.tau z).im_pos.ne' him

/-- The order-three affine substitution closes around every explicit source orbit. -/
public theorem muAffineOne_closes (z : UpperHalfPlane) (mu : ℂ) :
    muAffineOne
        (tauOneStep (tauOneStep (E.modularParameter.tau z)))
        (muAffineOne (tauOneStep (E.modularParameter.tau z))
          (muAffineOne (E.modularParameter.tau z) mu)) = mu :=
  muAffineOne_order_three _ _ (E.modularParameter.tau z).ne_zero (tau_coe_ne_one E z)

/-- The order-four affine substitution closes around every explicit source orbit. -/
public theorem muAffineTwo_closes (z : UpperHalfPlane) (mu : ℂ) :
    muAffineTwo
        (tauTwoStep (tauTwoStep (tauTwoStep (E.modularParameter.tau z))))
        (muAffineTwo (tauTwoStep (tauTwoStep (E.modularParameter.tau z)))
          (muAffineTwo (tauTwoStep (E.modularParameter.tau z))
            (muAffineTwo (E.modularParameter.tau z) mu))) = mu :=
  muAffineTwo_order_four _ _ (E.modularParameter.tau z).ne_zero

private theorem tau_transform_one_coe (z : UpperHalfPlane) :
    ((E.modularParameter.tau (fuchsianSourceAction g₁ • z) : UpperHalfPlane) : ℂ) =
      tauOneStep (E.modularParameter.tau z) := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.transform_one z)).trans (rhoTauReal_g₁_smul _)

private theorem tau_transform_two_coe (z : UpperHalfPlane) :
    ((E.modularParameter.tau (fuchsianSourceAction g₂ • z) : UpperHalfPlane) : ℂ) =
      tauTwoStep (E.modularParameter.tau z) := by
  exact (congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.transform_two z)).trans (rhoTauReal_g₂_smul _)

private theorem tau_coe_holomorphic :
    MDiff (fun z ↦ (E.modularParameter.tau z : ℂ)) := by
  intro z
  exact (E.modularParameter.tau z).mdifferentiable_coe.comp z
    (E.modularParameter.tau_holomorphic z)

/-- The order-three local affine section is holomorphic. -/
public theorem ellipticMuOne_holomorphic : MDiff (ellipticMuOne E) := by
  exact (mdifferentiable_const.sub (tau_coe_holomorphic E)).div mdifferentiable_const
    (by norm_num)

/-- The order-four local affine section is holomorphic. -/
public theorem ellipticMuTwo_holomorphic : MDiff (ellipticMuTwo E) := by
  exact (mdifferentiable_const.sub (tau_coe_holomorphic E)).div mdifferentiable_const
    (by norm_num)

/-- The first explicit local section satisfies the order-three affine law. -/
public theorem ellipticMuOne_transform (z : UpperHalfPlane) :
    ellipticMuOne E (fuchsianSourceAction g₁ • z) =
      (1 - ellipticMuOne E z) / (E.modularParameter.tau z : ℂ) := by
  rw [ellipticMuOne, ellipticMuOne, tau_transform_one_coe]
  exact localMuOne_equivariant _ (E.modularParameter.tau z).ne_zero

/-- The second explicit local section satisfies the order-four affine law. -/
public theorem ellipticMuTwo_transform (z : UpperHalfPlane) :
    ellipticMuTwo E (fuchsianSourceAction g₂ • z) =
      1 + ellipticMuTwo E z / (E.modularParameter.tau z : ℂ) := by
  rw [ellipticMuTwo, ellipticMuTwo, tau_transform_two_coe]
  exact localMuTwo_equivariant _ (E.modularParameter.tau z).ne_zero

/-- The order-three local section has the forced fixed-point value. -/
public theorem ellipticMuOne_at_fixedPoint :
    ellipticMuOne E fuchsianOneFixedPoint = localMuOne ellipticThreeParameter := by
  rw [ellipticMuOne, E.tau_at_one]

/-- The order-four local section has the forced fixed-point value. -/
public theorem ellipticMuTwo_at_fixedPoint :
    ellipticMuTwo E fuchsianTwoFixedPoint = localMuTwo UpperHalfPlane.I := by
  rw [ellipticMuTwo, E.tau_at_two]

/-- The cusp section is holomorphic, invariant under the parabolic generator, and bounded on the
distinguished cusp region. -/
public theorem cuspLocalMu_properties :
    MDiff (cuspLocalMu E) ∧
      (∀ z, cuspLocalMu E (fuchsianSourceAction g₀ • z) = cuspLocalMu E z) ∧
      BoundedOn (cuspLocalMu E) fuchsianCuspRegion := by
  refine ⟨mdifferentiable_const, fun _ ↦ rfl, ?_⟩
  exact ⟨0, le_rfl, by simp [cuspLocalMu]⟩

/-- Local analytic data identifying the affine `mu` problem with a Cech torsor under
`O(-1)` on the quotient projective line.

The two sections live only on an invariant open cover.  Thus this contract does not contain a
global `mu`; constructing it is the paper-specific quotient/sheaf descent step. -/
public structure MuTorsorCechLocalData where
  /-- The source region over the finite quotient chart. -/
  zeroRegion : Set UpperHalfPlane
  /-- The source region over the cusp chart. -/
  infinityRegion : Set UpperHalfPlane
  /-- Openness of the finite-chart region. -/
  zeroRegion_open : IsOpen zeroRegion
  /-- Openness of the cusp-chart region. -/
  infinityRegion_open : IsOpen infinityRegion
  /-- The two source regions cover the upper half-plane. -/
  regions_cover : zeroRegion ∪ infinityRegion = Set.univ
  /-- The finite-chart region is invariant under the source deck group. -/
  zeroRegion_invariant : ∀ g z,
    fuchsianSourceAction g • z ∈ zeroRegion ↔ z ∈ zeroRegion
  /-- The cusp-chart region is invariant under the source deck group. -/
  infinityRegion_invariant : ∀ g z,
    fuchsianSourceAction g • z ∈ infinityRegion ↔ z ∈ infinityRegion
  /-- A local affine-torsor section on the finite chart. -/
  sectionZero : UpperHalfPlane → ℂ
  /-- A local affine-torsor section on the cusp chart. -/
  sectionInfinity : UpperHalfPlane → ℂ
  /-- Holomorphicity of the finite-chart section on its region. -/
  sectionZero_holomorphic : ∀ z, z ∈ zeroRegion → MDiffAt sectionZero z
  /-- Holomorphicity of the cusp-chart section on its region. -/
  sectionInfinity_holomorphic : ∀ z, z ∈ infinityRegion → MDiffAt sectionInfinity z
  /-- The finite-chart section obeys the first affine generator law. -/
  sectionZero_one : ∀ z, z ∈ zeroRegion →
    sectionZero (fuchsianSourceAction g₁ • z) =
      (1 - sectionZero z) / E.modularParameter.tau z
  /-- The finite-chart section obeys the second affine generator law. -/
  sectionZero_two : ∀ z, z ∈ zeroRegion →
    sectionZero (fuchsianSourceAction g₂ • z) =
      1 + sectionZero z / E.modularParameter.tau z
  /-- The cusp-chart section obeys the first affine generator law. -/
  sectionInfinity_one : ∀ z, z ∈ infinityRegion →
    sectionInfinity (fuchsianSourceAction g₁ • z) =
      (1 - sectionInfinity z) / E.modularParameter.tau z
  /-- The cusp-chart section obeys the second affine generator law. -/
  sectionInfinity_two : ∀ z, z ∈ infinityRegion →
    sectionInfinity (fuchsianSourceAction g₂ • z) =
      1 + sectionInfinity z / E.modularParameter.tau z
  /-- A homogeneous local frame over the finite chart. -/
  frameZero : UpperHalfPlane → ℂ
  /-- A homogeneous local frame over the cusp chart. -/
  frameInfinity : UpperHalfPlane → ℂ
  /-- Holomorphicity of the finite-chart homogeneous frame. -/
  frameZero_holomorphic : ∀ z, z ∈ zeroRegion → MDiffAt frameZero z
  /-- Holomorphicity of the cusp-chart homogeneous frame. -/
  frameInfinity_holomorphic : ∀ z, z ∈ infinityRegion → MDiffAt frameInfinity z
  /-- First homogeneous automorphy law for the finite-chart frame. -/
  frameZero_one : ∀ z, z ∈ zeroRegion →
    frameZero (fuchsianSourceAction g₁ • z) =
      -frameZero z / E.modularParameter.tau z
  /-- Second homogeneous automorphy law for the finite-chart frame. -/
  frameZero_two : ∀ z, z ∈ zeroRegion →
    frameZero (fuchsianSourceAction g₂ • z) =
      frameZero z / E.modularParameter.tau z
  /-- First homogeneous automorphy law for the cusp-chart frame. -/
  frameInfinity_one : ∀ z, z ∈ infinityRegion →
    frameInfinity (fuchsianSourceAction g₁ • z) =
      -frameInfinity z / E.modularParameter.tau z
  /-- Second homogeneous automorphy law for the cusp-chart frame. -/
  frameInfinity_two : ∀ z, z ∈ infinityRegion →
    frameInfinity (fuchsianSourceAction g₂ • z) =
      frameInfinity z / E.modularParameter.tau z
  /-- The overlap coefficient in the finite quotient coordinate. -/
  overlapCocycle : ℂ → ℂ
  /-- Holomorphicity of the overlap coefficient on the punctured plane. -/
  overlapCocycle_holomorphic : HolomorphicOnPuncturedPlane overlapCocycle
  /-- The quotient coordinate is nonzero throughout the cusp chart. -/
  infinity_coordinate_ne_zero : ∀ z, z ∈ infinityRegion →
    E.sourceCoordinate.coordinate z ≠ 0
  /-- The two frames have the standard `O(-1)` transition on the overlap. -/
  frame_transition : ∀ z, z ∈ zeroRegion ∩ infinityRegion →
    frameInfinity z =
      (E.sourceCoordinate.coordinate z)⁻¹ * frameZero z
  /-- The local affine sections differ by the Cech coefficient in the homogeneous frame. -/
  section_mismatch : ∀ z, z ∈ zeroRegion ∩ infinityRegion →
    sectionZero z - sectionInfinity z =
      overlapCocycle (E.sourceCoordinate.coordinate z) * frameZero z
  /-- The distinguished cusp region lies in the infinity chart. -/
  cusp_subset_infinity : fuchsianCuspRegion ⊆ infinityRegion
  /-- The cusp-chart affine section is bounded on the distinguished component. -/
  sectionInfinity_cusp_bounded : BoundedOn sectionInfinity fuchsianCuspRegion
  /-- A holomorphic infinity-chart coefficient times the infinity frame stays bounded at the
  distinguished cusp.  This is the local regularity of the `O(-1)` frame at infinity. -/
  infinity_frame_cusp_bounded : ∀ f : ℂ → ℂ, MDiff f →
    BoundedOn
      (fun z ↦ f ((E.sourceCoordinate.coordinate z)⁻¹) * frameInfinity z)
      fuchsianCuspRegion

/-- Correct the finite-chart affine section by an `O(-1)` zero-cochain. -/
@[expose] public def adjustedMuZero (D : MuTorsorCechLocalData E)
    (fZero : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  D.sectionZero z -
    fZero (E.sourceCoordinate.coordinate z) * D.frameZero z

/-- Correct the cusp-chart affine section by an `O(-1)` zero-cochain. -/
@[expose] public def adjustedMuInfinity (D : MuTorsorCechLocalData E)
    (fInfinity : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  D.sectionInfinity z -
    fInfinity ((E.sourceCoordinate.coordinate z)⁻¹) * D.frameInfinity z

/-- A holomorphic zero-cochain correction preserves local holomorphicity on the finite chart. -/
public theorem adjustedMuZero_holomorphicAt (D : MuTorsorCechLocalData E)
    {fZero : ℂ → ℂ} (hfZero : MDiff fZero) {z : UpperHalfPlane}
    (hz : z ∈ D.zeroRegion) : MDiffAt (adjustedMuZero E D fZero) z := by
  exact (D.sectionZero_holomorphic z hz).sub
    ((hfZero (E.sourceCoordinate.coordinate z)).comp z
      (E.sourceCoordinate.coordinate_holomorphic z) |>.mul
        (D.frameZero_holomorphic z hz))

/-- A holomorphic zero-cochain correction preserves local holomorphicity on the cusp chart. -/
public theorem adjustedMuInfinity_holomorphicAt (D : MuTorsorCechLocalData E)
    {fInfinity : ℂ → ℂ} (hfInfinity : MDiff fInfinity) {z : UpperHalfPlane}
    (hz : z ∈ D.infinityRegion) : MDiffAt (adjustedMuInfinity E D fInfinity) z := by
  have ht := D.infinity_coordinate_ne_zero z hz
  have hinv : MDiffAt (fun w ↦ (E.sourceCoordinate.coordinate w)⁻¹) z :=
    (E.sourceCoordinate.coordinate_holomorphic z).inv ht
  exact (D.sectionInfinity_holomorphic z hz).sub
    ((hfInfinity _).comp z hinv |>.mul (D.frameInfinity_holomorphic z hz))

/-- Homogeneous finite-chart corrections preserve the first affine generator law. -/
public theorem adjustedMuZero_transform_one (D : MuTorsorCechLocalData E)
    (fZero : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.zeroRegion) :
    adjustedMuZero E D fZero (fuchsianSourceAction g₁ • z) =
      (1 - adjustedMuZero E D fZero z) / E.modularParameter.tau z := by
  rw [adjustedMuZero, adjustedMuZero, D.sectionZero_one z hz, D.frameZero_one z hz,
    E.sourceCoordinate.coordinate_invariant]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- Homogeneous finite-chart corrections preserve the second affine generator law. -/
public theorem adjustedMuZero_transform_two (D : MuTorsorCechLocalData E)
    (fZero : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.zeroRegion) :
    adjustedMuZero E D fZero (fuchsianSourceAction g₂ • z) =
      1 + adjustedMuZero E D fZero z / E.modularParameter.tau z := by
  rw [adjustedMuZero, adjustedMuZero, D.sectionZero_two z hz, D.frameZero_two z hz,
    E.sourceCoordinate.coordinate_invariant]
  ring

/-- Homogeneous cusp-chart corrections preserve the first affine generator law. -/
public theorem adjustedMuInfinity_transform_one (D : MuTorsorCechLocalData E)
    (fInfinity : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.infinityRegion) :
    adjustedMuInfinity E D fInfinity (fuchsianSourceAction g₁ • z) =
      (1 - adjustedMuInfinity E D fInfinity z) / E.modularParameter.tau z := by
  rw [adjustedMuInfinity, adjustedMuInfinity, D.sectionInfinity_one z hz,
    D.frameInfinity_one z hz, E.sourceCoordinate.coordinate_invariant]
  field_simp [(E.modularParameter.tau z).ne_zero]
  ring

/-- Homogeneous cusp-chart corrections preserve the second affine generator law. -/
public theorem adjustedMuInfinity_transform_two (D : MuTorsorCechLocalData E)
    (fInfinity : ℂ → ℂ) (z : UpperHalfPlane) (hz : z ∈ D.infinityRegion) :
    adjustedMuInfinity E D fInfinity (fuchsianSourceAction g₂ • z) =
      1 + adjustedMuInfinity E D fInfinity z / E.modularParameter.tau z := by
  rw [adjustedMuInfinity, adjustedMuInfinity, D.sectionInfinity_two z hz,
    D.frameInfinity_two z hz, E.sourceCoordinate.coordinate_invariant]
  ring

/-- Analytic Cech exactness makes the two local affine-torsor sections agree after homogeneous
corrections.  What remains is the general sheaf-gluing/descent theorem for these compatible local
sections on the explicit quotient. -/
public theorem exists_compatibleAdjustedMuSections (D : MuTorsorCechLocalData E) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
        adjustedMuZero E D fZero z = adjustedMuInfinity E D fInfinity z := by
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechNegOne D.overlapCocycle
      D.overlapCocycle_holomorphic
  refine ⟨fZero, fInfinity, hfZero, hfInfinity, ?_⟩
  intro z hz
  have ht := D.infinity_coordinate_ne_zero z hz.2
  have hc := hsplit (E.sourceCoordinate.coordinate z) ht
  have hm := D.section_mismatch z hz
  have hs : D.sectionZero z = D.sectionInfinity z +
      D.overlapCocycle (E.sourceCoordinate.coordinate z) * D.frameZero z := by
    linear_combination hm
  rw [adjustedMuZero, adjustedMuInfinity, D.frame_transition z hz, hs, hc]
  ring

private theorem mem_infinityRegion_of_not_mem_zeroRegion (D : MuTorsorCechLocalData E)
    {z : UpperHalfPlane} (hz : z ∉ D.zeroRegion) : z ∈ D.infinityRegion := by
  have hcover : z ∈ D.zeroRegion ∪ D.infinityRegion := by
    rw [D.regions_cover]
    exact Set.mem_univ z
  exact hcover.resolve_left hz

/-- The global function obtained by gluing two compatible adjusted local sections. -/
@[expose] public def gluedAdjustedMu (D : MuTorsorCechLocalData E)
    (fZero fInfinity : ℂ → ℂ) (z : UpperHalfPlane) : ℂ := by
  classical
  exact if z ∈ D.zeroRegion then adjustedMuZero E D fZero z
    else adjustedMuInfinity E D fInfinity z

/-- Compatible adjusted sections glue to a holomorphic function. -/
public theorem gluedAdjustedMu_holomorphic (D : MuTorsorCechLocalData E)
    {fZero fInfinity : ℂ → ℂ} (hfZero : MDiff fZero) (hfInfinity : MDiff fInfinity)
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      adjustedMuZero E D fZero z = adjustedMuInfinity E D fInfinity z) :
    MDiff (gluedAdjustedMu E D fZero fInfinity) := by
  classical
  intro z
  by_cases hz : z ∈ D.zeroRegion
  · have heq : gluedAdjustedMu E D fZero fInfinity =ᶠ[nhds z]
        adjustedMuZero E D fZero := by
      filter_upwards [D.zeroRegion_open.mem_nhds hz] with w hw
      simp [gluedAdjustedMu, hw]
    exact heq.mdifferentiableAt_iff.mpr (adjustedMuZero_holomorphicAt E D hfZero hz)
  · have hzInfinity := mem_infinityRegion_of_not_mem_zeroRegion E D hz
    have heq : gluedAdjustedMu E D fZero fInfinity =ᶠ[nhds z]
        adjustedMuInfinity E D fInfinity := by
      filter_upwards [D.infinityRegion_open.mem_nhds hzInfinity] with w hw
      by_cases hwZero : w ∈ D.zeroRegion
      · simpa [gluedAdjustedMu, hwZero] using hcompat w ⟨hwZero, hw⟩
      · simp [gluedAdjustedMu, hwZero]
    exact heq.mdifferentiableAt_iff.mpr
      (adjustedMuInfinity_holomorphicAt E D hfInfinity hzInfinity)

/-- The glued correction obeys the first affine generator law. -/
public theorem gluedAdjustedMu_transform_one (D : MuTorsorCechLocalData E)
    (fZero fInfinity : ℂ → ℂ) (z : UpperHalfPlane) :
    gluedAdjustedMu E D fZero fInfinity (fuchsianSourceAction g₁ • z) =
      (1 - gluedAdjustedMu E D fZero fInfinity z) / E.modularParameter.tau z := by
  classical
  by_cases hz : z ∈ D.zeroRegion
  · have hgz := (D.zeroRegion_invariant g₁ z).mpr hz
    rw [gluedAdjustedMu, if_pos hgz, adjustedMuZero_transform_one E D fZero z hz,
      gluedAdjustedMu, if_pos hz]
  · have hzInfinity := mem_infinityRegion_of_not_mem_zeroRegion E D hz
    have hgz : fuchsianSourceAction g₁ • z ∉ D.zeroRegion := by
      exact fun h ↦ hz ((D.zeroRegion_invariant g₁ z).mp h)
    rw [gluedAdjustedMu, if_neg hgz,
      adjustedMuInfinity_transform_one E D fInfinity z hzInfinity,
      gluedAdjustedMu, if_neg hz]

/-- The glued correction obeys the second affine generator law. -/
public theorem gluedAdjustedMu_transform_two (D : MuTorsorCechLocalData E)
    (fZero fInfinity : ℂ → ℂ) (z : UpperHalfPlane) :
    gluedAdjustedMu E D fZero fInfinity (fuchsianSourceAction g₂ • z) =
      1 + gluedAdjustedMu E D fZero fInfinity z / E.modularParameter.tau z := by
  classical
  by_cases hz : z ∈ D.zeroRegion
  · have hgz := (D.zeroRegion_invariant g₂ z).mpr hz
    rw [gluedAdjustedMu, if_pos hgz, adjustedMuZero_transform_two E D fZero z hz,
      gluedAdjustedMu, if_pos hz]
  · have hzInfinity := mem_infinityRegion_of_not_mem_zeroRegion E D hz
    have hgz : fuchsianSourceAction g₂ • z ∉ D.zeroRegion := by
      exact fun h ↦ hz ((D.zeroRegion_invariant g₂ z).mp h)
    rw [gluedAdjustedMu, if_neg hgz,
      adjustedMuInfinity_transform_two E D fInfinity z hzInfinity,
      gluedAdjustedMu, if_neg hz]

/-- The difference of two bounded functions is bounded. -/
public theorem BoundedOn.sub {f g : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hf : BoundedOn f s) (hg : BoundedOn g s) :
    BoundedOn (fun z ↦ f z - g z) s := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
  intro z hz
  exact (norm_sub_le (f z) (g z)).trans (add_le_add (hf z hz) (hg z hz))

/-- The infinity-chart adjusted section is bounded at the distinguished cusp. -/
public theorem adjustedMuInfinity_cusp_bounded (D : MuTorsorCechLocalData E)
    {fInfinity : ℂ → ℂ} (hfInfinity : MDiff fInfinity) :
    BoundedOn (adjustedMuInfinity E D fInfinity) fuchsianCuspRegion := by
  exact D.sectionInfinity_cusp_bounded.sub
    (D.infinity_frame_cusp_bounded fInfinity hfInfinity)

/-- On the cusp, the glued section is represented by its infinity-chart formula. -/
public theorem gluedAdjustedMu_eq_infinity_on_cusp (D : MuTorsorCechLocalData E)
    {fZero fInfinity : ℂ → ℂ}
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      adjustedMuZero E D fZero z = adjustedMuInfinity E D fInfinity z)
    {z : UpperHalfPlane} (hz : z ∈ fuchsianCuspRegion) :
    gluedAdjustedMu E D fZero fInfinity z = adjustedMuInfinity E D fInfinity z := by
  classical
  have hzInfinity := D.cusp_subset_infinity hz
  by_cases hzZero : z ∈ D.zeroRegion
  · simpa [gluedAdjustedMu, hzZero] using hcompat z ⟨hzZero, hzInfinity⟩
  · simp [gluedAdjustedMu, hzZero]

/-- The glued adjusted section is bounded at the distinguished cusp. -/
public theorem gluedAdjustedMu_cusp_bounded (D : MuTorsorCechLocalData E)
    {fZero fInfinity : ℂ → ℂ} (hfInfinity : MDiff fInfinity)
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      adjustedMuZero E D fZero z = adjustedMuInfinity E D fInfinity z) :
    BoundedOn (gluedAdjustedMu E D fZero fInfinity) fuchsianCuspRegion := by
  obtain ⟨C, hC, hbound⟩ := adjustedMuInfinity_cusp_bounded E D hfInfinity
  refine ⟨C, hC, ?_⟩
  intro z hz
  rw [gluedAdjustedMu_eq_infinity_on_cusp E D hcompat hz]
  exact hbound z hz

/-- The first affine law forces the paper's order-three elliptic value. -/
public theorem mu_at_fuchsianOneFixedPoint_of_transform
    (mu : UpperHalfPlane → ℂ)
    (hmu : ∀ z, mu (fuchsianSourceAction g₁ • z) =
      (1 - mu z) / E.modularParameter.tau z) :
    mu fuchsianOneFixedPoint = localMuOne ellipticThreeParameter := by
  have h := hmu fuchsianOneFixedPoint
  rw [fuchsianOneFixedPoint_fixed, E.tau_at_one] at h
  have ht : (ellipticThreeParameter : ℂ) ≠ 0 := ellipticThreeParameter.ne_zero
  have hden : 1 + (ellipticThreeParameter : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    rw [Complex.add_im] at him
    norm_num at him
    exact ellipticThreeParameter.im_pos.ne' him
  have hforced : mu fuchsianOneFixedPoint =
      1 / (1 + (ellipticThreeParameter : ℂ)) := by
    rw [eq_div_iff hden]
    field_simp [ht] at h
    linear_combination h
  rw [hforced]
  simp only [localMuOne, ellipticThreeParameter]
  change 1 / (1 + ((UpperHalfPlane.ρ : ℂ) + 1)) =
    (2 - ((UpperHalfPlane.ρ : ℂ) + 1)) / 3
  have hrho := UpperHalfPlane.ρ_sq
  have hdenrho : 1 + ((UpperHalfPlane.ρ : ℂ) + 1) ≠ 0 := by
    simpa [ellipticThreeParameter] using hden
  field_simp [hdenrho]
  linear_combination hrho

/-- The second affine law forces the paper's order-four elliptic value. -/
public theorem mu_at_fuchsianTwoFixedPoint_of_transform
    (mu : UpperHalfPlane → ℂ)
    (hmu : ∀ z, mu (fuchsianSourceAction g₂ • z) =
      1 + mu z / E.modularParameter.tau z) :
    mu fuchsianTwoFixedPoint = localMuTwo UpperHalfPlane.I := by
  have h := hmu fuchsianTwoFixedPoint
  rw [fuchsianTwoFixedPoint_fixed, E.tau_at_two] at h
  have ht : ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) ≠ 0 := UpperHalfPlane.I.ne_zero
  have ht1 : ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) - 1 ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    rw [Complex.sub_im] at him
    norm_num at him
  have hforced : mu fuchsianTwoFixedPoint =
      ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) /
        (((UpperHalfPlane.I : UpperHalfPlane) : ℂ) - 1) := by
    rw [eq_div_iff ht1]
    field_simp [ht] at h
    linear_combination h
  rw [hforced]
  change Complex.I / (Complex.I - 1) = (1 - Complex.I) / 2
  have ht1I : Complex.I - 1 ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    norm_num at him
  rw [div_eq_iff ht1I]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  norm_num

/-- Exact local torsor descent plus classical `O(-1)` Cech exactness constructs the global
holomorphic, equivariant, cusp-bounded `mu`. -/
public theorem exists_globalFuchsianMu (D : MuTorsorCechLocalData E) :
    ∃ mu : UpperHalfPlane → ℂ,
      MDiff mu ∧
      (∀ z, mu (fuchsianSourceAction g₁ • z) =
        (1 - mu z) / E.modularParameter.tau z) ∧
      (∀ z, mu (fuchsianSourceAction g₂ • z) =
        1 + mu z / E.modularParameter.tau z) ∧
      BoundedOn mu fuchsianCuspRegion := by
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hcompat⟩ :=
    exists_compatibleAdjustedMuSections E D
  refine ⟨gluedAdjustedMu E D fZero fInfinity,
    gluedAdjustedMu_holomorphic E D hfZero hfInfinity hcompat,
    gluedAdjustedMu_transform_one E D fZero fInfinity,
    gluedAdjustedMu_transform_two E D fZero fInfinity,
    gluedAdjustedMu_cusp_bounded E D hfInfinity hcompat⟩

end SphereSixComplex.Periods
