module

public import SphereSixComplex.Topology.CuspPhaseSpreadingData

/-!
# The algebraic deck correction for polar phase spreading

The phase correction is separated here from the quotient-topology and stabilizer statements.
Once the compact phase multiplier lifting the frozen deck multiplier is specified, compatibility
of the two deck actions follows from the toric action laws and density of the open torus.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.CuspStraighteningRetraction

open SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspToricPhaseAction
open StandardInfiniteA2ToricModel

public theorem denseTorusShear_mul (lambda : ParameterLattice) (x y : DenseTorus) :
    denseTorusShear lambda (x * y) =
      denseTorusShear lambda x * denseTorusShear lambda y := by
  ext i
  fin_cases i <;> simp [denseTorusShear, mul_zpow, mul_assoc, mul_left_comm]

/-- Fan shear conjugates multiplication by an arbitrary dense-torus element to multiplication
by its monomial shear. -/
public theorem fanShear_torusAction (M : Model) (lambda : ParameterLattice)
    (g : DenseTorus) (p : M.Carrier) :
    Additive.toMul (M.fanShear lambda) (M.torusAction g p) =
      M.torusAction (denseTorusShear lambda g)
        (Additive.toMul (M.fanShear lambda) p) := by
  let f : M.Carrier → M.Carrier := fun q ↦
    Additive.toMul (M.fanShear lambda) (M.torusAction g q)
  let h : M.Carrier → M.Carrier := fun q ↦
    M.torusAction (denseTorusShear lambda g)
      (Additive.toMul (M.fanShear lambda) q)
  have hf : Continuous f :=
    (M.fanShear_holomorphic lambda).continuous.comp
      (M.torusAction_holomorphic g).continuous
  have hh : Continuous h :=
    (M.torusAction_holomorphic (denseTorusShear lambda g)).continuous.comp
      (M.fanShear_holomorphic lambda).continuous
  have hfh : f ∘ M.torusEmbedding = h ∘ M.torusEmbedding := by
    funext x
    dsimp [f, h]
    rw [M.torusAction_torus, M.fanShear_torus, M.fanShear_torus,
      M.torusAction_torus, denseTorusShear_mul]
  exact congrFun (M.torus_dense.equalizer hf hh hfh) p

/-- The narrow algebraic datum needed to spread compact phase through the frozen lattice action.
It only says that the frozen multiplier, after monomial shear, admits the displayed compact-phase
factor relative to the positive real deck multiplier. -/
public structure PolarPhaseDeckLift
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (P : PolarHoneycombData M r) where
  deckPhase : Multiplicative ParameterLattice → CompactTorus → CompactTorus
  multiplier_identity : ∀ g k,
    compactTorusEmbedding (deckPhase g k) *
        P.positiveTwist (Multiplicative.toAdd g) =
      phaseEmbedding (N.phaseCoefficient (Multiplicative.toAdd g) 0) *
        denseTorusShear (Multiplicative.toAdd g) (compactTorusEmbedding k)

/-- The radial part of the frozen phase multiplier agrees with the chosen positive deck twist. -/
public structure PolarPhaseRadialCompatibility
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (P : PolarHoneycombData M r) : Prop where
  norm_positiveTwist : ∀ lambda i,
    ‖((P.positiveTwist lambda i : ℂˣ) : ℂ)‖ =
      ‖((phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂˣ) : ℂ)‖

public theorem norm_denseTorusShear_compactTorusEmbedding
    (lambda : ParameterLattice) (k : CompactTorus) (i : Fin 3) :
    ‖((denseTorusShear lambda (compactTorusEmbedding k) i : ℂˣ) : ℂ)‖ = 1 := by
  fin_cases i <;>
    simp [denseTorusShear, compactTorusEmbedding, norm_zpow, Circle.norm_coe]

/-- The compact correction obtained by dividing the frozen sheared multiplier by its positive
radial part. -/
public def radialDeckPhase
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {P : PolarHoneycombData M r} (H : PolarPhaseRadialCompatibility N M r P)
    (g : Multiplicative ParameterLattice) (k : CompactTorus) : CompactTorus :=
  fun i ↦ ⟨((phaseEmbedding (N.phaseCoefficient (Multiplicative.toAdd g) 0) *
      denseTorusShear (Multiplicative.toAdd g) (compactTorusEmbedding k)) i /
        P.positiveTwist (Multiplicative.toAdd g) i : ℂˣ), by
    change (((((phaseEmbedding (N.phaseCoefficient (Multiplicative.toAdd g) 0) *
      denseTorusShear (Multiplicative.toAdd g) (compactTorusEmbedding k)) i /
        P.positiveTwist (Multiplicative.toAdd g) i : ℂˣ)) : ℂ)) ∈
          Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, Units.val_div_eq_div_val, norm_div,
      Pi.mul_apply, Units.val_mul, norm_mul,
      norm_denseTorusShear_compactTorusEmbedding, mul_one,
      H.norm_positiveTwist, div_self]
    exact norm_ne_zero_iff.mpr (Units.ne_zero _ )⟩

@[simp]
public theorem compactTorusEmbedding_radialDeckPhase_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {P : PolarHoneycombData M r} (H : PolarPhaseRadialCompatibility N M r P)
    (g : Multiplicative ParameterLattice) (k : CompactTorus) (i : Fin 3) :
    compactTorusEmbedding (radialDeckPhase H g k) i =
      (phaseEmbedding (N.phaseCoefficient (Multiplicative.toAdd g) 0) *
          denseTorusShear (Multiplicative.toAdd g) (compactTorusEmbedding k)) i /
        P.positiveTwist (Multiplicative.toAdd g) i := by
  apply Units.ext
  simp only [compactTorusEmbedding, Circle.toUnits_apply]
  rfl

/-- Radial compatibility constructs the exact compact multiplier lift. -/
public def PolarPhaseRadialCompatibility.toDeckLift
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {P : PolarHoneycombData M r} (H : PolarPhaseRadialCompatibility N M r P) :
    PolarPhaseDeckLift N M r P where
  deckPhase := radialDeckPhase H
  multiplier_identity := by
    intro g k
    ext i
    simp only [Pi.mul_apply, compactTorusEmbedding_radialDeckPhase_apply]
    exact congrArg Units.val (div_mul_cancel
      ((phaseEmbedding (N.phaseCoefficient (Multiplicative.toAdd g) 0) *
        denseTorusShear (Multiplicative.toAdd g) (compactTorusEmbedding k)) i)
      (P.positiveTwist (Multiplicative.toAdd g) i))

/-- The multiplier identity implies the deck-orbit compatibility required by phase spreading. -/
public theorem PolarPhaseDeckLift.deck_orbit
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {P : PolarHoneycombData M r} (L : PolarPhaseDeckLift N M r P) :
    letI := P.positiveDeckAction
    letI := frozenLocalCuspAction N M r
    ∀ g k p, compactPhaseOrbit M r P.positivePart (L.deckPhase g k, g • p) =
      g • compactPhaseOrbit M r P.positivePart (k, p) := by
  let _ := P.positiveDeckAction
  let _ := frozenLocalCuspAction N M r
  intro g k p
  have hdeck := P.positiveDeck_coe (Multiplicative.toAdd g) p
  rw [ofAdd_toAdd] at hdeck
  apply Subtype.ext
  change M.torusAction (compactTorusEmbedding (L.deckPhase g k))
      (((g • p : P.positivePart) : LocalCarrier M r) : M.Carrier) =
    ToricModel.phaseAction M (N.phaseCoefficient (Multiplicative.toAdd g) 0)
      (Additive.toMul (M.fanShear (Multiplicative.toAdd g))
        (M.torusAction (compactTorusEmbedding k) (p : M.Carrier)))
  rw [hdeck]
  calc
    _ = M.torusAction
          (compactTorusEmbedding (L.deckPhase g k) *
            P.positiveTwist (Multiplicative.toAdd g))
          (Additive.toMul (M.fanShear (Multiplicative.toAdd g)) (p : M.Carrier)) := by
        rw [map_mul, Equiv.Perm.mul_apply]
    _ = M.torusAction
          (phaseEmbedding (N.phaseCoefficient (Multiplicative.toAdd g) 0) *
            denseTorusShear (Multiplicative.toAdd g) (compactTorusEmbedding k))
          (Additive.toMul (M.fanShear (Multiplicative.toAdd g)) (p : M.Carrier)) := by
        rw [L.multiplier_identity]
    _ = ToricModel.phaseAction M (N.phaseCoefficient (Multiplicative.toAdd g) 0)
          (M.torusAction
            (denseTorusShear (Multiplicative.toAdd g) (compactTorusEmbedding k))
            (Additive.toMul (M.fanShear (Multiplicative.toAdd g))
              (p : M.Carrier))) := by
        rw [ToricModel.phaseAction_apply, map_mul, Equiv.Perm.mul_apply]
    _ = _ := by
      rw [← fanShear_torusAction]

/-- The genuinely geometric residue after the deck multiplier calculation: stabilizer
preservation by the lifted cellular homotopy. -/
public structure PolarPhaseGeometricCore
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) where
  homotopy_fiberwise :
    letI := P.positiveDeckAction
    let R := P.positiveEquivariantStrongDeformationRetraction
    ∀ s k p l q,
      compactPhaseOrbit M r P.positivePart (k, p) =
          compactPhaseOrbit M r P.positivePart (l, q) →
        compactPhaseOrbit M r P.positivePart (k, R.homotopy (s, p)) =
          compactPhaseOrbit M r P.positivePart (l, R.homotopy (s, q))

/-- Assemble the phase-spreading interface from its geometric core and the explicit multiplier
lift.  In particular, the deck-orbit field is a theorem rather than an assumed compatibility. -/
public def FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    {P : PolarHoneycombData M r}
    (hquot : Topology.IsQuotientMap
      (Prod.map (id : unitInterval → unitInterval)
        (compactPhaseOrbit M r P.positivePart)))
    (L : PolarPhaseDeckLift N M r P)
    (G : PolarPhaseGeometricCore M r P) :
    FrozenLocalCuspPhaseSpreadingData N M r P where
  phaseOrbit_prod_isQuotientMap := hquot
  deckPhase := L.deckPhase
  deck_orbit := L.deck_orbit
  homotopy_fiberwise := G.homotopy_fiberwise

end SphereSixComplex.Geometry.CuspStraighteningRetraction
