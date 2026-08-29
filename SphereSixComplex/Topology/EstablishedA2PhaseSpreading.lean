module

public import SphereSixComplex.Periods.EstablishedFuchsianTorsorDescent
public import SphereSixComplex.Periods.FuchsianCuspNormalization
public import SphereSixComplex.Topology.StandardInfiniteA2PolarPhaseDeck

/-!
# Established phase spreading for the standard infinite `A₂` toric model

This boundary records only the standard toric orbit, deck, and stabilizer compatibility package.
It contains no quotient retraction, homology, Euler-characteristic, or global paper conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspStraighteningExtension
open SphereSixComplex.Geometry.CuspToricPhaseAction

/-- The positive real complex unit with the same norm as a given complex unit. -/
public def positiveRadialPart (z : ℂˣ) : ℂˣ :=
  Units.mk0 (‖(z : ℂ)‖ : ℂ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero z)))

public theorem positiveRadialPart_re (z : ℂˣ) :
    0 < ((positiveRadialPart z : ℂˣ) : ℂ).re := by
  change 0 < ‖(z : ℂ)‖
  exact norm_pos_iff.mpr (Units.ne_zero z)

public theorem positiveRadialPart_im (z : ℂˣ) :
    ((positiveRadialPart z : ℂˣ) : ℂ).im = 0 := by
  rfl

public theorem norm_positiveRadialPart (z : ℂˣ) :
    ‖((positiveRadialPart z : ℂˣ) : ℂ)‖ = ‖(z : ℂ)‖ := by
  change ‖(‖(z : ℂ)‖ : ℂ)‖ = ‖(z : ℂ)‖
  exact Complex.norm_of_nonneg (norm_nonneg _)

public theorem positiveRadialPart_mul (z w : ℂˣ) :
    positiveRadialPart (z * w) = positiveRadialPart z * positiveRadialPart w := by
  apply Units.ext
  simp [positiveRadialPart]

/-- The coordinatewise positive radial part of the normalized frozen cusp multiplier. -/
public def normalizedCuspPositiveTwist
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) :
    ParameterLattice → DenseTorus :=
  fun lambda i ↦ positiveRadialPart
    (phaseEmbedding (N.phaseCoefficient lambda 0) i)

@[simp]
public theorem normalizedCuspPositiveTwist_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) :
    normalizedCuspPositiveTwist N 0 = 1 := by
  funext i
  simp [normalizedCuspPositiveTwist, positiveRadialPart]

public theorem normalizedCuspPositiveTwist_add
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda mu : ParameterLattice) :
    normalizedCuspPositiveTwist N (lambda + mu) =
      normalizedCuspPositiveTwist N lambda * normalizedCuspPositiveTwist N mu := by
  funext i
  change positiveRadialPart (phaseEmbedding (N.phaseCoefficient (lambda + mu) 0) i) =
    positiveRadialPart (phaseEmbedding (N.phaseCoefficient lambda 0) i) *
      positiveRadialPart (phaseEmbedding (N.phaseCoefficient mu 0) i)
  rw [N.phaseCoefficient_add, map_mul, Pi.mul_apply, positiveRadialPart_mul]

@[simp]
public theorem normalizedCuspPositiveTwist_last
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) :
    normalizedCuspPositiveTwist N lambda 2 = 1 := by
  apply Units.ext
  simp [normalizedCuspPositiveTwist, positiveRadialPart]

public theorem normalizedCuspPositiveTwist_real
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) (i : Fin 3) :
    0 < ((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ).re ∧
      ((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ).im = 0 :=
  ⟨positiveRadialPart_re _, positiveRadialPart_im _⟩

/-- The canonical positive twist has exactly the frozen cusp multiplier's radial norm. -/
public theorem norm_normalizedCuspPositiveTwist
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) (i : Fin 3) :
    ‖((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ)‖ =
      ‖((phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂˣ) : ℂ)‖ :=
  norm_positiveRadialPart _

/-- The compact phase-orbit map is proper.  The positive part is closed because its modulus map
is a retraction, and the orbit map factors through the compact-torus action homeomorphism
followed by projection away from the compact torus. -/
public theorem compactPhaseOrbit_isProper
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) :
    IsProperMap (compactPhaseOrbit M r P.positivePart) := by
  let J := establishedContinuousTorusAction M
  let localAction : CompactTorus × LocalCarrier M r → LocalCarrier M r :=
    fun z ↦ ⟨M.torusAction (compactTorusEmbedding z.1) z.2, by
      change M.t (M.torusAction (compactTorusEmbedding z.1) z.2) ∈ Metric.ball 0 r
      rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
      change ‖(z.1 2 : ℂ)‖ * ‖M.t z.2‖ < r
      rw [Circle.norm_coe, one_mul]
      simpa only [dist_zero_right] using Metric.mem_ball.mp z.2.property⟩
  have hlocalAction : Continuous localAction := by
    rw [continuous_induced_rng]
    exact J.variable_action
      (continuous_compactTorusEmbedding.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)
  let localActionInv : CompactTorus × LocalCarrier M r → LocalCarrier M r :=
    fun z ↦ ⟨M.torusAction (compactTorusEmbedding z.1)⁻¹ z.2, by
      change M.t (M.torusAction (compactTorusEmbedding z.1)⁻¹ z.2) ∈ Metric.ball 0 r
      rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
      rw [show ‖((((compactTorusEmbedding z.1)⁻¹ 2 : ℂˣ) : ℂ))‖ = 1 by
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv]
        change ‖(z.1 2 : ℂ)‖⁻¹ = 1
        rw [Circle.norm_coe, inv_one], one_mul]
      simpa only [dist_zero_right] using Metric.mem_ball.mp z.2.property⟩
  have hlocalActionInv : Continuous localActionInv := by
    rw [continuous_induced_rng]
    exact J.variable_action
      (continuous_inv.comp
        (continuous_compactTorusEmbedding.comp continuous_fst))
      (continuous_subtype_val.comp continuous_snd)
  let actionHomeomorph : CompactTorus × LocalCarrier M r ≃ₜ
      CompactTorus × LocalCarrier M r := {
    toFun := fun z ↦ (z.1, localAction z)
    invFun := fun z ↦ (z.1, localActionInv z)
    left_inv := by
      intro z
      ext <;> simp [localAction, localActionInv]
    right_inv := by
      intro z
      ext <;> simp [localAction, localActionInv]
    continuous_toFun := continuous_fst.prodMk hlocalAction
    continuous_invFun := continuous_fst.prodMk hlocalActionInv }
  have hclosed : IsClosed P.positivePart := by
    have hrange : P.positivePart =
        Set.range (fun q : P.positivePart ↦ (q : LocalCarrier M r)) := by
      ext x
      simp
    rw [hrange]
    exact (show Function.LeftInverse P.modulus
      (fun q : P.positivePart ↦ (q : LocalCarrier M r)) from P.modulus_fixed).isClosed_range
        P.modulus.continuous continuous_subtype_val
  have hinclusion : Topology.IsClosedEmbedding
      (fun z : CompactTorus × P.positivePart ↦
        (z.1, (z.2 : LocalCarrier M r))) := by
    exact Topology.IsClosedEmbedding.id.prodMap
      hclosed.isClosedEmbedding_subtypeVal
  have hj : IsProperMap (fun z : CompactTorus × P.positivePart ↦
      actionHomeomorph (z.1, (z.2 : LocalCarrier M r))) :=
    actionHomeomorph.isProperMap.comp hinclusion.isProperMap
  have hproper : IsProperMap (fun z : CompactTorus × P.positivePart ↦
      (actionHomeomorph (z.1, (z.2 : LocalCarrier M r))).2) :=
    isProperMap_snd_of_compactSpace.comp hj
  convert hproper using 1
  funext z
  apply Subtype.ext
  rfl

/-- The polar decomposition already proves surjectivity of the compact phase orbit map. -/
public theorem compactPhaseOrbit_surjective
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) :
    Function.Surjective (compactPhaseOrbit M r P.positivePart) := by
  intro p
  obtain ⟨phi, hphi⟩ := P.polar_surjective p
  refine ⟨(phi, P.modulus p), ?_⟩
  apply Subtype.ext
  exact hphi

/-- Properness and polar surjectivity give the exact product quotient map used to descend the
phase-spread homotopy. -/
public theorem compactPhaseOrbit_prod_isQuotientMap
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) :
    Topology.IsQuotientMap
      (Prod.map (id : unitInterval → unitInterval)
        (compactPhaseOrbit M r P.positivePart)) := by
  have hproper : IsProperMap
      (Prod.map (id : unitInterval → unitInterval)
        (compactPhaseOrbit M r P.positivePart)) :=
    isProperMap_id.prodMap (compactPhaseOrbit_isProper M r P)
  exact hproper.isClosedMap.isQuotientMap hproper.continuous
    (Function.Surjective.prodMap Function.surjective_id
      (compactPhaseOrbit_surjective M r P))

private theorem positive_units_eq_of_norm_eq
    (z w : ℂˣ)
    (hz : 0 < ((z : ℂˣ) : ℂ).re ∧ ((z : ℂˣ) : ℂ).im = 0)
    (hw : 0 < ((w : ℂˣ) : ℂ).re ∧ ((w : ℂˣ) : ℂ).im = 0)
    (h : ‖((z : ℂˣ) : ℂ)‖ = ‖((w : ℂˣ) : ℂ)‖) :
    z = w := by
  have hzval : ((z : ℂˣ) : ℂ) = (((z : ℂˣ) : ℂ).re : ℂ) :=
    Complex.ext rfl hz.2
  have hwval : ((w : ℂˣ) : ℂ) = (((w : ℂˣ) : ℂ).re : ℂ) :=
    Complex.ext rfl hw.2
  apply Units.ext
  rw [hzval, hwval, Complex.ofReal_inj]
  rw [hzval, hwval, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hz.1, abs_of_pos hw.1] at h
  exact h

private theorem positiveTwist_eq_normalized_of_basis_aux
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) {M : Model} {r : ℝ}
    (P : PolarHoneycombData M r)
    (hP : ∀ j i : Fin 2,
      ‖((P.positiveTwist (Pi.single j 1) i.castSucc : ℂˣ) : ℂ)‖ =
        ‖((phaseEmbedding (N.phaseCoefficient (Pi.single j 1) 0)
          i.castSucc : ℂˣ) : ℂ)‖) :
    P.positiveTwist = normalizedCuspPositiveTwist N := by
  have hP' : ∀ j : Fin 2, P.positiveTwist (Pi.single j 1) =
      normalizedCuspPositiveTwist N (Pi.single j 1) := by
    intro j
    funext i
    fin_cases i
    · exact positive_units_eq_of_norm_eq _ _
        (P.positiveTwist_real (Pi.single j 1) 0)
        (normalizedCuspPositiveTwist_real N (Pi.single j 1) 0)
        ((hP j 0).trans (norm_normalizedCuspPositiveTwist N (Pi.single j 1) 0).symm)
    · exact positive_units_eq_of_norm_eq _ _
        (P.positiveTwist_real (Pi.single j 1) 1)
        (normalizedCuspPositiveTwist_real N (Pi.single j 1) 1)
        ((hP j 1).trans (norm_normalizedCuspPositiveTwist N (Pi.single j 1) 1).symm)
    · change P.positiveTwist (Pi.single j 1) 2 =
        normalizedCuspPositiveTwist N (Pi.single j 1) 2
      rw [P.positiveTwist_last, normalizedCuspPositiveTwist_last]
  let pTwist : ParameterLattice →+ Additive DenseTorus := {
    toFun := fun lambda ↦ Additive.ofMul (P.positiveTwist lambda)
    map_zero' := congrArg Additive.ofMul P.positiveTwist_zero
    map_add' := fun lambda mu ↦ congrArg Additive.ofMul (P.positiveTwist_add lambda mu) }
  let nTwist : ParameterLattice →+ Additive DenseTorus := {
    toFun := fun lambda ↦ Additive.ofMul (normalizedCuspPositiveTwist N lambda)
    map_zero' := congrArg Additive.ofMul (normalizedCuspPositiveTwist_zero N)
    map_add' := fun lambda mu ↦
      congrArg Additive.ofMul (normalizedCuspPositiveTwist_add N lambda mu) }
  have hHom : pTwist = nTwist := by
    apply AddMonoidHom.functions_ext'
    intro j
    apply AddMonoidHom.ext_int
    exact congrArg Additive.ofMul (hP' j)
  funext lambda
  exact congrArg Additive.toMul (DFunLike.congr_fun hHom lambda)

/-- The genuinely independent input for a polar honeycomb.  Positivity of the height on the
positive part follows from the modulus identities, while contractibility of the central
honeycomb follows from its displayed Euclidean homeomorphism. -/
public structure PolarHoneycombConstructionData (M : Model) (r : ℝ) where
  positivePart : Set (LocalCarrier M r)
  modulus : C(LocalCarrier M r, positivePart)
  modulus_fixed : ∀ q : positivePart, modulus q = q
  modulus_t : ∀ p, M.t (modulus p) = (‖M.t p‖ : ℝ)
  polar_surjective : ∀ p : LocalCarrier M r, ∃ phi : CompactTorus,
    M.torusAction (compactTorusEmbedding phi) (modulus p) = p
  central : Set positivePart
  central_eq : central = {q : positivePart | M.t (q : LocalCarrier M r) = 0}
  honeycomb : (Fin 2 → ℝ) ≃ₜ central
  positiveTwist : ParameterLattice → DenseTorus
  positiveTwist_zero : positiveTwist 0 = 1
  positiveTwist_add : ∀ lambda mu,
    positiveTwist (lambda + mu) = positiveTwist lambda * positiveTwist mu
  positiveTwist_last : ∀ lambda, positiveTwist lambda 2 = 1
  positiveTwist_real : ∀ lambda i,
    0 < ((positiveTwist lambda i : ℂˣ) : ℂ).re ∧
      ((positiveTwist lambda i : ℂˣ) : ℂ).im = 0
  positiveDeckAction : MulAction (Multiplicative ParameterLattice) positivePart
  positiveDeck_coe : ∀ lambda q,
    ((((Multiplicative.ofAdd lambda) • q : positivePart) : LocalCarrier M r) : M.Carrier) =
      M.torusAction (positiveTwist lambda)
        (Additive.toMul (M.fanShear lambda) (q : M.Carrier))
  quotientCovering :
    letI := positiveDeckAction
    IsQuotientCoveringMap
      (PolarHoneycombData.orbitProjection positivePart)
      (Multiplicative ParameterLattice)
  positive_contractible : ContractibleSpace positivePart
  quotient_relativeCW :
    letI := positiveDeckAction
    Topology.RelCWComplex
      (Set.univ : Set (PolarHoneycombData.OrbitQuotient positivePart))
      (PolarHoneycombData.orbitCore central)
  quotient_t2 :
    letI := positiveDeckAction
    T2Space (PolarHoneycombData.OrbitQuotient positivePart)

/-- The displayed formula for the deck action makes each deck transformation continuous. -/
public theorem PolarHoneycombConstructionData.positiveDeckContinuous
    {M : Model} {r : ℝ} (Q : PolarHoneycombConstructionData M r) :
    letI := Q.positiveDeckAction
    ContinuousConstSMul (Multiplicative ParameterLattice) Q.positivePart := by
  let _ := Q.positiveDeckAction
  constructor
  intro g
  rw [continuous_induced_rng, continuous_induced_rng]
  let lambda := Multiplicative.toAdd g
  have heq :
      (fun q : Q.positivePart ↦
        ((((g • q : Q.positivePart) : LocalCarrier M r)) : M.Carrier)) =
      fun q : Q.positivePart ↦ M.torusAction (Q.positiveTwist lambda)
        (Additive.toMul (M.fanShear lambda) (q : M.Carrier)) := by
    funext q
    simpa [lambda] using Q.positiveDeck_coe lambda q
  change Continuous (fun q : Q.positivePart ↦
    ((((g • q : Q.positivePart) : LocalCarrier M r)) : M.Carrier))
  rw [heq]
  exact (M.torusAction_holomorphic (Q.positiveTwist lambda)).continuous.comp
    ((M.fanShear_holomorphic lambda).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- The central honeycomb is saturated under the deck action because the action preserves the
height coordinate. -/
public theorem PolarHoneycombConstructionData.central_preimage
    {M : Model} {r : ℝ} (Q : PolarHoneycombConstructionData M r) :
    letI := Q.positiveDeckAction
    PolarHoneycombData.orbitProjection Q.positivePart ⁻¹'
        PolarHoneycombData.orbitCore Q.central = Q.central := by
  let _ := Q.positiveDeckAction
  have hmem (lambda : ParameterLattice) (q : Q.positivePart) :
      (Multiplicative.ofAdd lambda) • q ∈ Q.central ↔ q ∈ Q.central := by
    rw [Q.central_eq]
    change M.t ((((Multiplicative.ofAdd lambda) • q : Q.positivePart) :
      LocalCarrier M r)) = 0 ↔ M.t (q : LocalCarrier M r) = 0
    rw [Q.positiveDeck_coe, M.t_torusAction, Q.positiveTwist_last,
      M.fanShear_preserves_t]
    simp
  ext q
  constructor
  · rintro ⟨c, hc, hqc⟩
    change Quotient.mk _ c = Quotient.mk _ q at hqc
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqc
    obtain ⟨g, hg⟩ := hqc
    rw [← hg] at hc
    simpa using (hmem (Multiplicative.toAdd g) q).mp hc
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- Assemble the full interface, deriving its four redundant geometric fields. -/
public noncomputable def PolarHoneycombConstructionData.toPolarHoneycombData
    {M : Model} {r : ℝ} (Q : PolarHoneycombConstructionData M r) :
    PolarHoneycombData M r where
  positivePart := Q.positivePart
  modulus := Q.modulus
  modulus_fixed := Q.modulus_fixed
  positive_t := by
    intro q
    have h := Q.modulus_t (q : LocalCarrier M r)
    rw [Q.modulus_fixed q] at h
    rw [h]
    exact ⟨by simp, norm_nonneg _⟩
  modulus_t := Q.modulus_t
  polar_surjective := Q.polar_surjective
  central := Q.central
  central_eq := Q.central_eq
  honeycomb := Q.honeycomb
  positiveTwist := Q.positiveTwist
  positiveTwist_zero := Q.positiveTwist_zero
  positiveTwist_add := Q.positiveTwist_add
  positiveTwist_last := Q.positiveTwist_last
  positiveTwist_real := Q.positiveTwist_real
  positiveDeckAction := Q.positiveDeckAction
  positiveDeck_coe := Q.positiveDeck_coe
  positiveDeckContinuous := Q.positiveDeckContinuous
  quotientCovering := Q.quotientCovering
  central_preimage := Q.central_preimage
  positive_contractible := Q.positive_contractible
  central_contractible := Q.honeycomb.symm.contractibleSpace
  quotient_relativeCW := Q.quotient_relativeCW
  quotient_t2 := Q.quotient_t2

/-- The remaining geometric construction chooses polar coordinates whose positive deck
multiplier is the canonical radial part of the frozen multiplier and whose lifted cellular
homotopy preserves compact-phase fibers. -/
public axiom normalizedPolarHoneycombPhaseGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty { Q : PolarHoneycombConstructionData M r //
      let P := Q.toPolarHoneycombData
      (∀ j i : Fin 2,
        ‖((P.positiveTwist (Pi.single j 1) i.castSucc : ℂˣ) : ℂ)‖ =
          ‖((phaseEmbedding (N.phaseCoefficient (Pi.single j 1) 0)
            i.castSucc : ℂˣ) : ℂ)‖) ∧ PolarPhaseGeometricCore M r P }

/-- Exact choice of the canonical radial multiplier supplies the radial compatibility required
by the algebraic deck correction. -/
public theorem polarHoneycombPhaseSpreadingGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty { P : PolarHoneycombData M r //
      PolarPhaseRadialCompatibility N M r P ∧ PolarPhaseGeometricCore M r P } := by
  obtain ⟨⟨Q, hP, G⟩⟩ := normalizedPolarHoneycombPhaseGeometry N M r hr
  let P := Q.toPolarHoneycombData
  have hTwist := positiveTwist_eq_normalized_of_basis_aux N P hP
  refine ⟨⟨P, ⟨?_, G⟩⟩⟩
  refine ⟨fun lambda i ↦ ?_⟩
  rw [hTwist]
  exact norm_normalizedCuspPositiveTwist N lambda i

/-- The standard polar-honeycomb model can be chosen compatibly with compact phase orbits, the
frozen deck action, and the stabilizers of the positive-part cellular homotopy. -/
public theorem polarHoneycombPhaseSpreadingPackage
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty (Σ P : PolarHoneycombData M r,
      FrozenLocalCuspPhaseSpreadingData N M r P) := by
  obtain ⟨⟨P, H, G⟩⟩ := polarHoneycombPhaseSpreadingGeometry N M r hr
  exact ⟨⟨P, FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData
    (compactPhaseOrbit_prod_isQuotientMap M r P) H.toDeckLift G⟩⟩

/-- Forgetting the phase-spreading compatibility gives the underlying polar-honeycomb model. -/
public theorem polarHoneycombData (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty (PolarHoneycombData M r) := by
  obtain ⟨E⟩ := exists_establishedFuchsianModularParameter
  obtain ⟨F⟩ := establishedExactLiftedModularNegOneFrame E
  let D := establishedFuchsianPeriodLocalData E F
  obtain ⟨N⟩ := FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate E D
  exact Nonempty.map (fun package ↦ package.1)
    (polarHoneycombPhaseSpreadingPackage N M r hr)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
