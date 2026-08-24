import SphereSixComplex.Periods.EstablishedFuchsianTorsorDescent

/-!
# Contract audit for orbifold affine-torsor descent

This file gives an axiom-free assembly theorem for a repaired version of
`establishedOrbifoldAffineLineTorsorTwoChartDescent`.  It deliberately separates three kinds of
input:

* the one missing algebraic law on `cuspNormalize`;
* chartwise holomorphic triviality of the affine torsor (the Cartan-B/Cousin obligation);
* descent of a homogeneous punctured-source section through the quotient frame.

The last two interfaces state real analytic work and are not disguised as consequences of the
existing fields.  The final section checks that the concrete `mu` and `beta` problems satisfy the
normalization repair and that its output is exactly the boundedness consumed downstream.
-/

open scoped Manifold

noncomputable section

namespace SphereSixComplex.Periods.AgentContractDesign

open SphereSixComplex.TriangleGroup

/-- The minimal missing law on the cusp normalization.  It permits a base-dependent change of
origin, but requires the fibre coordinate to retain its ordinary affine difference. -/
def NormalizePreservesDifferences
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  ∀ z u v, P.cuspNormalize z u - P.cuspNormalize z v = u - v

/-- Difference preservation is equivalent to saying that normalization is translation by its
value at the fibre origin. -/
theorem normalize_eq_add_origin
    {P : OrbifoldAffineLineTorsorDescentProblem}
    (h : NormalizePreservesDifferences P) (z : UpperHalfPlane) (u : ℂ) :
    P.cuspNormalize z u = u + P.cuspNormalize z 0 := by
  have hsub := h z u 0
  linear_combination hsub

/-- Optional stronger compatibility with the inverse-parabolic affine substitution.  It is true
for both concrete problems, but is not needed by the assembly theorem below. -/
def NormalizeIntertwinesCusp
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  ∀ z u,
    P.cuspNormalize (fuchsianSourceAction g₀ • z) (P.affineCusp z u) =
      P.cuspNormalize z u

/-- Normalization of a holomorphic fibre section remains holomorphic. -/
def NormalizePreservesHolomorphicSections
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  ∀ s : UpperHalfPlane → ℂ, MDiff s →
    MDiff (fun z ↦ P.cuspNormalize z (s z))

/-- The robust local normalization contract selected for the authoritative API.  Difference
preservation is the logically necessary repair for the final bound; the other two laws expose
the holomorphic and parabolic facts used when establishing cusp regularity. -/
structure SoundCuspNormalization
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop where
  sub : NormalizePreservesDifferences P
  holomorphic : NormalizePreservesHolomorphicSections P
  cusp : NormalizeIntertwinesCusp P

/-- The proposed source-level modification, bundled as a wrapper so this audit does not edit the
authoritative structure. -/
structure LocallyRepairedProblem where
  problem : OrbifoldAffineLineTorsorDescentProblem
  normalization : SoundCuspNormalization problem

/-- The actual global analytic content on the two affine quotient charts.  Cusp regularity is
stated intrinsically as a bounded difference from the supplied regular cusp primitive; no
arbitrary choice of normalization occurs in this interface. -/
structure ChartwiseAffineTrivialization
    (P : OrbifoldAffineLineTorsorDescentProblem) where
  sectionZero : UpperHalfPlane → ℂ
  sectionInfinity : UpperHalfPlane → ℂ
  sectionZero_holomorphic : MDiff sectionZero
  sectionInfinity_holomorphic : ∀ z, P.quotient.coordinate z ≠ 0 →
    MDiffAt sectionInfinity z
  sectionZero_one : ∀ z,
    sectionZero (fuchsianSourceAction g₁ • z) =
      P.affineOne z (sectionZero z)
  sectionZero_two : ∀ z,
    sectionZero (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (sectionZero z)
  sectionInfinity_one : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₁ • z) =
      P.affineOne z (sectionInfinity z)
  sectionInfinity_two : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (sectionInfinity z)
  sectionInfinity_sub_cusp_bounded :
    BoundedOn (fun z ↦ sectionInfinity z - P.cuspSection z) fuchsianCuspRegion

/-- A homogeneous section on the source over the punctured finite coordinate chart. -/
structure HomogeneousPuncturedSourceSection
    (P : OrbifoldAffineLineTorsorDescentProblem) where
  value : UpperHalfPlane → ℂ
  holomorphic : ∀ z, P.quotient.coordinate z ≠ 0 → MDiffAt value z
  transform_one : ∀ z, P.quotient.coordinate z ≠ 0 →
    value (fuchsianSourceAction g₁ • z) = P.linearOne z * value z
  transform_two : ∀ z, P.quotient.coordinate z ≠ 0 →
    value (fuchsianSourceAction g₂ • z) = P.linearTwo z * value z

/-- A descended coefficient of a homogeneous source section in the finite-chart frame. -/
structure DescendedFrameCoefficient
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (H : HomogeneousPuncturedSourceSection P) where
  coefficient : ℂ → ℂ
  coefficient_holomorphic : HolomorphicOnPuncturedPlane coefficient
  factorization : ∀ z, P.quotient.coordinate z ≠ 0 →
    H.value z = coefficient (P.quotient.coordinate z) * P.frameZero z

/-- The quotient/frame analytic obligation, stated independently of any affine section.  Exact
covering descent handles regular points; the frame orders encode divisibility at the elliptic
point with nonzero quotient coordinate. -/
def FrameQuotientDescent
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  ∀ H : HomogeneousPuncturedSourceSection P,
    Nonempty (DescendedFrameCoefficient P H)

/-- The difference of two affine chart sections is a homogeneous punctured-source section. -/
def chartMismatch
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (S : ChartwiseAffineTrivialization P) :
    HomogeneousPuncturedSourceSection P where
  value := fun z ↦ S.sectionZero z - S.sectionInfinity z
  holomorphic := by
    intro z hz
    exact S.sectionZero_holomorphic.mdifferentiableAt.sub
      (S.sectionInfinity_holomorphic z hz)
  transform_one := by
    intro z hz
    rw [S.sectionZero_one, S.sectionInfinity_one z hz, P.affineOne_sub]
  transform_two := by
    intro z hz
    rw [S.sectionZero_two, S.sectionInfinity_two z hz, P.affineTwo_sub]

/-- A compact repaired signature.  The normalization law is the missing algebraic contract; the
other two fields explicitly expose, rather than assume away, the two analytic descent steps. -/
structure RepairedDescentInputs
    (P : OrbifoldAffineLineTorsorDescentProblem) where
  normalization : SoundCuspNormalization P
  charts : ChartwiseAffineTrivialization P
  frame_descent : FrameQuotientDescent P

private theorem boundedOn_add
    {f g : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hf : BoundedOn f s) (hg : BoundedOn g s) :
    BoundedOn (fun z ↦ f z + g z) s := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
  intro z hz
  exact (norm_add_le (f z) (g z)).trans (add_le_add (hf z hz) (hg z hz))

/-- The normalization law converts intrinsic cusp control into exactly the normalized bound in
`TwoChartSections`. -/
theorem normalized_infinity_bounded
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hNormalize : NormalizePreservesDifferences P)
    (S : ChartwiseAffineTrivialization P) :
    BoundedOn (fun z ↦ P.cuspNormalize z (S.sectionInfinity z))
      fuchsianCuspRegion := by
  have hsum :
      BoundedOn
        (fun z ↦ P.cuspNormalize z (P.cuspSection z) +
          (S.sectionInfinity z - P.cuspSection z))
        fuchsianCuspRegion :=
    boundedOn_add P.cuspSection_normalized_bounded
      S.sectionInfinity_sub_cusp_bounded
  obtain ⟨C, hC, hsum⟩ := hsum
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hsub := hNormalize z (S.sectionInfinity z) (P.cuspSection z)
  change ‖P.cuspNormalize z (S.sectionInfinity z)‖ ≤ C
  rw [show P.cuspNormalize z (S.sectionInfinity z) =
      P.cuspNormalize z (P.cuspSection z) +
        (S.sectionInfinity z - P.cuspSection z) by
    linear_combination hsub]
  exact hsum z hz

/-- Axiom-free assembly of the requested conclusion from the repaired signature. -/
theorem twoChartSections_of_repaired_inputs
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (A : RepairedDescentInputs P) :
    Nonempty P.TwoChartSections := by
  obtain ⟨D⟩ := A.frame_descent (chartMismatch P A.charts)
  exact ⟨{
    sectionZero := A.charts.sectionZero
    sectionInfinity := A.charts.sectionInfinity
    sectionZero_holomorphic := A.charts.sectionZero_holomorphic
    sectionInfinity_holomorphic := A.charts.sectionInfinity_holomorphic
    sectionZero_one := A.charts.sectionZero_one
    sectionZero_two := A.charts.sectionZero_two
    sectionInfinity_one := A.charts.sectionInfinity_one
    sectionInfinity_two := A.charts.sectionInfinity_two
    overlapCocycle := D.coefficient
    overlapCocycle_holomorphic := D.coefficient_holomorphic
    section_mismatch := D.factorization
    sectionInfinity_normalized_cusp_bounded :=
      normalized_infinity_bounded P A.normalization.sub A.charts }⟩

/-! ## Check against the two actual downstream problems -/

open SphereSixComplex.Periods

variable (E : EstablishedFuchsianModularParameter)

/-- The `mu` problem supplies the repaired algebraic law definitionally. -/
theorem fuchsianMu_normalize_preserves_differences
    (F : ExactLiftedModularNegOneFrame E) :
    NormalizePreservesDifferences (fuchsianMuDescentProblem E F) := by
  intro z u v
  rfl

/-- The stronger parabolic normalization law also holds for `mu`. -/
theorem fuchsianMu_normalize_intertwines_cusp
    (F : ExactLiftedModularNegOneFrame E) :
    NormalizeIntertwinesCusp (fuchsianMuDescentProblem E F) := by
  intro z u
  rfl

/-- The identity `mu` normalization preserves holomorphic sections. -/
theorem fuchsianMu_normalize_preserves_holomorphic
    (F : ExactLiftedModularNegOneFrame E) :
    NormalizePreservesHolomorphicSections (fuchsianMuDescentProblem E F) := by
  intro s hs
  simpa only [fuchsianMuDescentProblem] using hs

/-- The concrete `mu` caller fills the complete three-field normalization contract. -/
theorem fuchsianMu_soundCuspNormalization
    (F : ExactLiftedModularNegOneFrame E) :
    SoundCuspNormalization (fuchsianMuDescentProblem E F) where
  sub := fuchsianMu_normalize_preserves_differences E F
  holomorphic := fuchsianMu_normalize_preserves_holomorphic E F
  cusp := fuchsianMu_normalize_intertwines_cusp E F

/-- The normalized `mu` bound produced by the generic output is literally the bound consumed by
`MuAffineCechSections`. -/
theorem fuchsianMu_normalize_apply
    (F : ExactLiftedModularNegOneFrame E) (z : UpperHalfPlane) (u : ℂ) :
    (fuchsianMuDescentProblem E F).cuspNormalize z u = u :=
  rfl

/-- The actual `mu` constructor lifts to the proposed repaired problem without new input. -/
noncomputable def fuchsianMu_locallyRepaired
    (F : ExactLiftedModularNegOneFrame E) : LocallyRepairedProblem where
  problem := fuchsianMuDescentProblem E F
  normalization := fuchsianMu_soundCuspNormalization E F

/-- The `beta` normalization is translation by `tau`, hence preserves all fibre differences. -/
theorem fuchsianBeta_normalize_preserves_differences
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    NormalizePreservesDifferences (fuchsianBetaDescentProblem E F Dmu) := by
  intro z u v
  simp only [fuchsianBetaDescentProblem]
  ring

/-- The target translation of `tau` exactly cancels the `+1` inverse-parabolic substitution in
the concrete `beta` problem. -/
theorem fuchsianBeta_normalize_intertwines_cusp
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    NormalizeIntertwinesCusp (fuchsianBetaDescentProblem E F Dmu) := by
  intro z u
  have htau := congrArg (fun w : UpperHalfPlane ↦ (w : ℂ))
    (E.modularParameter.equivariant g₀ z)
  rw [rhoTauReal_g0_smul] at htau
  simp only [fuchsianBetaDescentProblem]
  rw [htau]
  ring

/-- Translation by the holomorphic modular parameter preserves holomorphic `beta` sections. -/
theorem fuchsianBeta_normalize_preserves_holomorphic
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    NormalizePreservesHolomorphicSections (fuchsianBetaDescentProblem E F Dmu) := by
  have htau : MDiff (fun z ↦ (E.modularParameter.tau z : ℂ)) := by
    intro z
    exact (E.modularParameter.tau z).mdifferentiable_coe.comp z
      (E.modularParameter.tau_holomorphic z)
  intro s hs
  simp only [fuchsianBetaDescentProblem]
  exact hs.add htau

/-- The concrete `beta` caller fills the complete three-field normalization contract. -/
theorem fuchsianBeta_soundCuspNormalization
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    SoundCuspNormalization (fuchsianBetaDescentProblem E F Dmu) where
  sub := fuchsianBeta_normalize_preserves_differences E F Dmu
  holomorphic := fuchsianBeta_normalize_preserves_holomorphic E F Dmu
  cusp := fuchsianBeta_normalize_intertwines_cusp E F Dmu

/-- The normalized `beta` bound produced by the generic output is exactly `beta + tau`, the field
consumed by `BetaTorsorCechLocalData`. -/
theorem fuchsianBeta_normalize_apply
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E)
    (z : UpperHalfPlane) (u : ℂ) :
    (fuchsianBetaDescentProblem E F Dmu).cuspNormalize z u =
      u + E.modularParameter.tau z := by
  rfl

/-- The actual `beta` constructor also lifts to the proposed repaired problem without new input. -/
noncomputable def fuchsianBeta_locallyRepaired
    (F : ExactLiftedModularNegOneFrame E) (Dmu : MuTorsorCechLocalData E) :
    LocallyRepairedProblem where
  problem := fuchsianBetaDescentProblem E F Dmu
  normalization := fuchsianBeta_soundCuspNormalization E F Dmu

/-!
## Field-by-field map to the authoritative API

The selected local repair has three fields: affine difference preservation, preservation of
holomorphic sections, and parabolic intertwining.  The theorems above show how the existing
definitions of `fuchsianMuDescentProblem` and `fuchsianBetaDescentProblem` fill all three; no new
modular input is required.  Of these, only difference preservation is needed by the final
boundedness assembly once intrinsic cusp control has been constructed.

The fields of `ChartwiseAffineTrivialization` map to the section, holomorphicity, and generator
fields currently returned as `MuAffineCechSections` and `BetaAffineCechSections`.  Its last field
maps to `sectionInfinity_cusp_bounded` for `mu` because `cuspLocalMu = 0`, and to
`sectionInfinity_add_tau_cusp_bounded` for `beta` because `cuspLocalBeta = -tau`.  Crucially, these
sections are outputs of the disputed theorem in the authoritative file; the local primitives
`ellipticOne`, `ellipticTwo`, and `cuspSection` do not already supply them.

`FrameQuotientDescent` is intended to be discharged from the existing quotient fields
`coordinate_eq_iff_orbit`, `regular_covering`, `branch_one`, and `branch_two`, together with the
existing frame holomorphicity, automorphy, frame-order, and zero-locus fields.  The current
authoritative API has all of that geometric data but no proved theorem performing the required
holomorphic quotient/divisibility descent.

Once the two analytic inputs exist, `twoChartSections_of_repaired_inputs` returns the unchanged
`TwoChartSections` structure.  Consequently the existing projections in
`exists_muAffineCechSections` and `exists_betaAffineCechSections` remain type-correct, and the two
pointwise normalization lemmas above identify their cusp bounds exactly.
-/

#print axioms normalize_eq_add_origin
#print axioms chartMismatch
#print axioms normalized_infinity_bounded
#print axioms twoChartSections_of_repaired_inputs
#print axioms fuchsianMu_normalize_preserves_differences
#print axioms fuchsianMu_soundCuspNormalization
#print axioms fuchsianMu_locallyRepaired
#print axioms fuchsianBeta_normalize_preserves_differences
#print axioms fuchsianBeta_normalize_intertwines_cusp
#print axioms fuchsianBeta_soundCuspNormalization
#print axioms fuchsianBeta_locallyRepaired

end SphereSixComplex.Periods.AgentContractDesign
