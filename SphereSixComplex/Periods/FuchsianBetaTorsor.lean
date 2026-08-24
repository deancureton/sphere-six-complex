module

public import SphereSixComplex.Periods.FuchsianMuTorsor
import all SphereSixComplex.Periods.Functions

/-!
# The additive `beta` torsor over the explicit Fuchsian quotient

Once `tau` and `mu` are fixed, two local solutions of the affine `beta` equations differ by an
invariant holomorphic function.  Thus their descent obstruction is a Cech cocycle for the
structure sheaf `O`.  The established two-chart Cech splitting makes the local solutions agree,
after which they glue on an invariant open cover.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods

open SphereSixComplex.TriangleGroup

variable (E : EstablishedFuchsianModularParameter)

/-- Local analytic data identifying the affine `beta` problem with a Cech torsor under `O` on
the quotient projective line.  It contains local sections and their overlap mismatch, but no
global `beta`. -/
public structure BetaTorsorCechLocalData (mu : UpperHalfPlane → ℂ) where
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
      sectionZero z + 2 - 6 * (1 - mu z) ^ 2 / E.modularParameter.tau z
  /-- The finite-chart section obeys the second affine generator law. -/
  sectionZero_two : ∀ z, z ∈ zeroRegion →
    sectionZero (fuchsianSourceAction g₂ • z) =
      sectionZero z - 3 - 6 * mu z ^ 2 / E.modularParameter.tau z
  /-- The cusp-chart section obeys the first affine generator law. -/
  sectionInfinity_one : ∀ z, z ∈ infinityRegion →
    sectionInfinity (fuchsianSourceAction g₁ • z) =
      sectionInfinity z + 2 - 6 * (1 - mu z) ^ 2 / E.modularParameter.tau z
  /-- The cusp-chart section obeys the second affine generator law. -/
  sectionInfinity_two : ∀ z, z ∈ infinityRegion →
    sectionInfinity (fuchsianSourceAction g₂ • z) =
      sectionInfinity z - 3 - 6 * mu z ^ 2 / E.modularParameter.tau z
  /-- The overlap coefficient in the finite quotient coordinate. -/
  overlapCocycle : ℂ → ℂ
  /-- Holomorphicity of the overlap coefficient on the punctured plane. -/
  overlapCocycle_holomorphic : HolomorphicOnPuncturedPlane overlapCocycle
  /-- The quotient coordinate is nonzero throughout the cusp chart. -/
  infinity_coordinate_ne_zero : ∀ z, z ∈ infinityRegion →
    E.sourceCoordinate.coordinate z ≠ 0
  /-- The two local sections differ by the structure-sheaf Cech coefficient. -/
  section_mismatch : ∀ z, z ∈ zeroRegion ∩ infinityRegion →
    sectionZero z - sectionInfinity z = overlapCocycle (E.sourceCoordinate.coordinate z)
  /-- The distinguished cusp region lies in the infinity chart. -/
  cusp_subset_infinity : fuchsianCuspRegion ⊆ infinityRegion
  /-- The normalized cusp-chart affine section has the paper's required bound. -/
  sectionInfinity_add_tau_cusp_bounded :
    BoundedOn (fun z ↦ sectionInfinity z + E.modularParameter.tau z) fuchsianCuspRegion
  /-- An entire function evaluated in the infinity coordinate stays bounded at the cusp. -/
  infinity_coordinate_cusp_bounded : ∀ f : ℂ → ℂ, MDiff f →
    BoundedOn (fun z ↦ f ((E.sourceCoordinate.coordinate z)⁻¹)) fuchsianCuspRegion

/-- Correct the finite-chart affine section by an `O` zero-cochain. -/
@[expose] public def adjustedBetaZero {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fZero : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  D.sectionZero z - fZero (E.sourceCoordinate.coordinate z)

/-- Correct the cusp-chart affine section by an `O` zero-cochain. -/
@[expose] public def adjustedBetaInfinity {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fInfinity : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  D.sectionInfinity z - fInfinity ((E.sourceCoordinate.coordinate z)⁻¹)

/-- A holomorphic zero-cochain correction preserves local holomorphicity on the finite chart. -/
public theorem adjustedBetaZero_holomorphicAt {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) {fZero : ℂ → ℂ} (hfZero : MDiff fZero)
    {z : UpperHalfPlane} (hz : z ∈ D.zeroRegion) :
    MDiffAt (adjustedBetaZero E D fZero) z := by
  exact (D.sectionZero_holomorphic z hz).sub
    ((hfZero _).comp z (E.sourceCoordinate.coordinate_holomorphic z))

/-- A holomorphic zero-cochain correction preserves local holomorphicity on the cusp chart. -/
public theorem adjustedBetaInfinity_holomorphicAt {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) {fInfinity : ℂ → ℂ}
    (hfInfinity : MDiff fInfinity) {z : UpperHalfPlane} (hz : z ∈ D.infinityRegion) :
    MDiffAt (adjustedBetaInfinity E D fInfinity) z := by
  have ht := D.infinity_coordinate_ne_zero z hz
  have hinv : MDiffAt (fun w ↦ (E.sourceCoordinate.coordinate w)⁻¹) z :=
    (E.sourceCoordinate.coordinate_holomorphic z).inv ht
  exact (D.sectionInfinity_holomorphic z hz).sub ((hfInfinity _).comp z hinv)

/-- Finite-chart corrections preserve the first affine generator law. -/
public theorem adjustedBetaZero_transform_one {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fZero : ℂ → ℂ) (z : UpperHalfPlane)
    (hz : z ∈ D.zeroRegion) :
    adjustedBetaZero E D fZero (fuchsianSourceAction g₁ • z) =
      adjustedBetaZero E D fZero z + 2 -
        6 * (1 - mu z) ^ 2 / E.modularParameter.tau z := by
  rw [adjustedBetaZero, adjustedBetaZero, D.sectionZero_one z hz,
    E.sourceCoordinate.coordinate_invariant]
  ring

/-- Finite-chart corrections preserve the second affine generator law. -/
public theorem adjustedBetaZero_transform_two {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fZero : ℂ → ℂ) (z : UpperHalfPlane)
    (hz : z ∈ D.zeroRegion) :
    adjustedBetaZero E D fZero (fuchsianSourceAction g₂ • z) =
      adjustedBetaZero E D fZero z - 3 -
        6 * mu z ^ 2 / E.modularParameter.tau z := by
  rw [adjustedBetaZero, adjustedBetaZero, D.sectionZero_two z hz,
    E.sourceCoordinate.coordinate_invariant]
  ring

/-- Cusp-chart corrections preserve the first affine generator law. -/
public theorem adjustedBetaInfinity_transform_one {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fInfinity : ℂ → ℂ) (z : UpperHalfPlane)
    (hz : z ∈ D.infinityRegion) :
    adjustedBetaInfinity E D fInfinity (fuchsianSourceAction g₁ • z) =
      adjustedBetaInfinity E D fInfinity z + 2 -
        6 * (1 - mu z) ^ 2 / E.modularParameter.tau z := by
  rw [adjustedBetaInfinity, adjustedBetaInfinity, D.sectionInfinity_one z hz,
    E.sourceCoordinate.coordinate_invariant]
  ring

/-- Cusp-chart corrections preserve the second affine generator law. -/
public theorem adjustedBetaInfinity_transform_two {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fInfinity : ℂ → ℂ) (z : UpperHalfPlane)
    (hz : z ∈ D.infinityRegion) :
    adjustedBetaInfinity E D fInfinity (fuchsianSourceAction g₂ • z) =
      adjustedBetaInfinity E D fInfinity z - 3 -
        6 * mu z ^ 2 / E.modularParameter.tau z := by
  rw [adjustedBetaInfinity, adjustedBetaInfinity, D.sectionInfinity_two z hz,
    E.sourceCoordinate.coordinate_invariant]
  ring

/-- Analytic Cech exactness makes the two local affine-torsor sections compatible. -/
public theorem exists_compatibleAdjustedBetaSections {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) :
    ∃ fZero fInfinity : ℂ → ℂ,
      MDiff fZero ∧ MDiff fInfinity ∧
      ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
        adjustedBetaZero E D fZero z = adjustedBetaInfinity E D fInfinity z := by
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hsplit⟩ :=
    establishedProjectiveLineCechZero D.overlapCocycle D.overlapCocycle_holomorphic
  refine ⟨fZero, fInfinity, hfZero, hfInfinity, ?_⟩
  intro z hz
  have ht := D.infinity_coordinate_ne_zero z hz.2
  have hc := hsplit (E.sourceCoordinate.coordinate z) ht
  have hm := D.section_mismatch z hz
  rw [adjustedBetaZero, adjustedBetaInfinity]
  linear_combination hm + hc

private theorem mem_infinityRegion_of_not_mem_zeroRegion {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) {z : UpperHalfPlane} (hz : z ∉ D.zeroRegion) :
    z ∈ D.infinityRegion := by
  have hcover : z ∈ D.zeroRegion ∪ D.infinityRegion := by
    rw [D.regions_cover]
    exact Set.mem_univ z
  exact hcover.resolve_left hz

/-- The global function obtained by gluing two compatible adjusted local sections. -/
@[expose] public def gluedAdjustedBeta {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fZero fInfinity : ℂ → ℂ)
    (z : UpperHalfPlane) : ℂ := by
  classical
  exact if z ∈ D.zeroRegion then adjustedBetaZero E D fZero z
    else adjustedBetaInfinity E D fInfinity z

/-- Compatible adjusted beta sections glue to a holomorphic function. -/
public theorem gluedAdjustedBeta_holomorphic {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) {fZero fInfinity : ℂ → ℂ}
    (hfZero : MDiff fZero) (hfInfinity : MDiff fInfinity)
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      adjustedBetaZero E D fZero z = adjustedBetaInfinity E D fInfinity z) :
    MDiff (gluedAdjustedBeta E D fZero fInfinity) := by
  classical
  intro z
  by_cases hz : z ∈ D.zeroRegion
  · have heq : gluedAdjustedBeta E D fZero fInfinity =ᶠ[nhds z]
        adjustedBetaZero E D fZero := by
      filter_upwards [D.zeroRegion_open.mem_nhds hz] with w hw
      simp [gluedAdjustedBeta, hw]
    exact heq.mdifferentiableAt_iff.mpr (adjustedBetaZero_holomorphicAt E D hfZero hz)
  · have hzInfinity := mem_infinityRegion_of_not_mem_zeroRegion E D hz
    have heq : gluedAdjustedBeta E D fZero fInfinity =ᶠ[nhds z]
        adjustedBetaInfinity E D fInfinity := by
      filter_upwards [D.infinityRegion_open.mem_nhds hzInfinity] with w hw
      by_cases hwZero : w ∈ D.zeroRegion
      · simpa [gluedAdjustedBeta, hwZero] using hcompat w ⟨hwZero, hw⟩
      · simp [gluedAdjustedBeta, hwZero]
    exact heq.mdifferentiableAt_iff.mpr
      (adjustedBetaInfinity_holomorphicAt E D hfInfinity hzInfinity)

/-- The glued beta obeys the first affine generator law. -/
public theorem gluedAdjustedBeta_transform_one {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fZero fInfinity : ℂ → ℂ)
    (z : UpperHalfPlane) :
    gluedAdjustedBeta E D fZero fInfinity (fuchsianSourceAction g₁ • z) =
      gluedAdjustedBeta E D fZero fInfinity z + 2 -
        6 * (1 - mu z) ^ 2 / E.modularParameter.tau z := by
  classical
  by_cases hz : z ∈ D.zeroRegion
  · have hgz := (D.zeroRegion_invariant g₁ z).mpr hz
    rw [gluedAdjustedBeta, if_pos hgz, adjustedBetaZero_transform_one E D fZero z hz,
      gluedAdjustedBeta, if_pos hz]
  · have hzInfinity := mem_infinityRegion_of_not_mem_zeroRegion E D hz
    have hgz : fuchsianSourceAction g₁ • z ∉ D.zeroRegion := by
      exact fun h ↦ hz ((D.zeroRegion_invariant g₁ z).mp h)
    rw [gluedAdjustedBeta, if_neg hgz,
      adjustedBetaInfinity_transform_one E D fInfinity z hzInfinity,
      gluedAdjustedBeta, if_neg hz]

/-- The glued beta obeys the second affine generator law. -/
public theorem gluedAdjustedBeta_transform_two {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) (fZero fInfinity : ℂ → ℂ)
    (z : UpperHalfPlane) :
    gluedAdjustedBeta E D fZero fInfinity (fuchsianSourceAction g₂ • z) =
      gluedAdjustedBeta E D fZero fInfinity z - 3 -
        6 * mu z ^ 2 / E.modularParameter.tau z := by
  classical
  by_cases hz : z ∈ D.zeroRegion
  · have hgz := (D.zeroRegion_invariant g₂ z).mpr hz
    rw [gluedAdjustedBeta, if_pos hgz, adjustedBetaZero_transform_two E D fZero z hz,
      gluedAdjustedBeta, if_pos hz]
  · have hzInfinity := mem_infinityRegion_of_not_mem_zeroRegion E D hz
    have hgz : fuchsianSourceAction g₂ • z ∉ D.zeroRegion := by
      exact fun h ↦ hz ((D.zeroRegion_invariant g₂ z).mp h)
    rw [gluedAdjustedBeta, if_neg hgz,
      adjustedBetaInfinity_transform_two E D fInfinity z hzInfinity,
      gluedAdjustedBeta, if_neg hz]

/-- The infinity-chart adjusted beta has the normalized cusp bound. -/
public theorem adjustedBetaInfinity_add_tau_cusp_bounded {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) {fInfinity : ℂ → ℂ}
    (hfInfinity : MDiff fInfinity) :
    BoundedOn
      (fun z ↦ adjustedBetaInfinity E D fInfinity z + E.modularParameter.tau z)
      fuchsianCuspRegion := by
  have h := D.sectionInfinity_add_tau_cusp_bounded.sub
    (D.infinity_coordinate_cusp_bounded fInfinity hfInfinity)
  simpa [adjustedBetaInfinity, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

/-- On the cusp, the glued section is represented by its infinity-chart formula. -/
public theorem gluedAdjustedBeta_eq_infinity_on_cusp {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) {fZero fInfinity : ℂ → ℂ}
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      adjustedBetaZero E D fZero z = adjustedBetaInfinity E D fInfinity z)
    {z : UpperHalfPlane} (hz : z ∈ fuchsianCuspRegion) :
    gluedAdjustedBeta E D fZero fInfinity z = adjustedBetaInfinity E D fInfinity z := by
  classical
  have hzInfinity := D.cusp_subset_infinity hz
  by_cases hzZero : z ∈ D.zeroRegion
  · simpa [gluedAdjustedBeta, hzZero] using hcompat z ⟨hzZero, hzInfinity⟩
  · simp [gluedAdjustedBeta, hzZero]

/-- The glued beta has the normalized cusp bound. -/
public theorem gluedAdjustedBeta_add_tau_cusp_bounded {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) {fZero fInfinity : ℂ → ℂ}
    (hfInfinity : MDiff fInfinity)
    (hcompat : ∀ z, z ∈ D.zeroRegion ∩ D.infinityRegion →
      adjustedBetaZero E D fZero z = adjustedBetaInfinity E D fInfinity z) :
    BoundedOn
      (fun z ↦ gluedAdjustedBeta E D fZero fInfinity z + E.modularParameter.tau z)
      fuchsianCuspRegion := by
  have hInfinity := adjustedBetaInfinity_add_tau_cusp_bounded E D hfInfinity
  rw [SphereSixComplex.Periods.BoundedOn.eq_def] at hInfinity ⊢
  obtain ⟨C, hC, hbound⟩ := hInfinity
  refine ⟨C, hC, ?_⟩
  intro z hz
  rw [gluedAdjustedBeta_eq_infinity_on_cusp E D hcompat hz]
  exact hbound z hz

/-- Exact local beta descent plus classical structure-sheaf Cech exactness constructs the global
holomorphic, equivariant, cusp-normalized `beta`. -/
public theorem exists_globalFuchsianBeta {mu : UpperHalfPlane → ℂ}
    (D : BetaTorsorCechLocalData E mu) :
    ∃ beta : UpperHalfPlane → ℂ,
      MDiff beta ∧
      (∀ z, beta (fuchsianSourceAction g₁ • z) =
        beta z + 2 - 6 * (1 - mu z) ^ 2 / E.modularParameter.tau z) ∧
      (∀ z, beta (fuchsianSourceAction g₂ • z) =
        beta z - 3 - 6 * mu z ^ 2 / E.modularParameter.tau z) ∧
      BoundedOn (fun z ↦ beta z + E.modularParameter.tau z) fuchsianCuspRegion := by
  obtain ⟨fZero, fInfinity, hfZero, hfInfinity, hcompat⟩ :=
    exists_compatibleAdjustedBetaSections E D
  refine ⟨gluedAdjustedBeta E D fZero fInfinity,
    gluedAdjustedBeta_holomorphic E D hfZero hfInfinity hcompat,
    gluedAdjustedBeta_transform_one E D fZero fInfinity,
    gluedAdjustedBeta_transform_two E D fZero fInfinity,
    gluedAdjustedBeta_add_tau_cusp_bounded E D hfInfinity hcompat⟩

end SphereSixComplex.Periods
