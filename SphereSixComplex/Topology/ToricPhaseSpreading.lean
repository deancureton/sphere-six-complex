module

public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction

/-!
# Spreading a deformation retraction across phase orbits

This file proves the general quotient-topology argument used in the toric phase-spreading step.
The fibrewise hypothesis is the precise orbit-stratum condition needed for well-definedness at
points with nontrivial torus stabilizer.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContinuousMap

namespace SphereSixComplex

variable {G K P X : Type*} [Group G]
  [TopologicalSpace K] [TopologicalSpace P] [TopologicalSpace X]
  [MulAction G P] [MulAction G X]
  {A : Set P} {B : Set X}

/-- Data ensuring that an equivariant deformation on a positive part spreads continuously over
all phase orbits. -/
public structure ToricPhaseSpreadingData
    (D : EquivariantStrongDeformationRetraction G P A) (B : Set X) where
  orbit : C(K × P, X)
  orbit_isOpenQuotientMap : IsOpenQuotientMap orbit
  deckPhase : G → K → K
  deck_orbit : ∀ g k p, orbit (deckPhase g k, g • p) = g • orbit (k, p)
  homotopy_fiberwise : ∀ s k p l q, orbit (k, p) = orbit (l, q) →
    orbit (k, D.homotopy (s, p)) = orbit (l, D.homotopy (s, q))
  target_iff : ∀ k p, orbit (k, p) ∈ B ↔ p ∈ A

namespace ToricPhaseSpreadingData

variable (D : EquivariantStrongDeformationRetraction G P A)
  (S : ToricPhaseSpreadingData (K := K) (X := X) D B)

public theorem orbit_surjective : Function.Surjective S.orbit :=
  S.orbit_isOpenQuotientMap.surjective

public noncomputable def representative (x : X) : K × P :=
  Classical.choose (S.orbit_surjective D x)

public theorem orbit_representative (x : X) : S.orbit (representative D S x) = x :=
  Classical.choose_spec (S.orbit_surjective D x)

public noncomputable def spreadHomotopyToFun (z : unitInterval × X) : X :=
  S.orbit ((representative D S z.2).1,
    D.homotopy (z.1, (representative D S z.2).2))

public theorem spreadHomotopyToFun_orbit
    (s : unitInterval) (k : K) (p : P) :
    spreadHomotopyToFun D S (s, S.orbit (k, p)) =
      S.orbit (k, D.homotopy (s, p)) := by
  apply S.homotopy_fiberwise
  exact orbit_representative D S _

public theorem continuous_spreadHomotopyToFun :
    Continuous (spreadHomotopyToFun D S) := by
  have hq : IsOpenQuotientMap
      (Prod.map (id : unitInterval → unitInterval) S.orbit) :=
    IsOpenQuotientMap.id.prodMap S.orbit_isOpenQuotientMap
  apply hq.isQuotientMap.continuous_iff.mpr
  have hinput : Continuous (fun z : unitInterval × (K × P) ↦
      (z.2.1, D.homotopy (z.1, z.2.2))) :=
    (continuous_fst.comp continuous_snd).prodMk
      (D.homotopy.continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have hcontinuous : Continuous (fun z : unitInterval × (K × P) ↦
      S.orbit (z.2.1, D.homotopy (z.1, z.2.2))) :=
    S.orbit.continuous.comp hinput
  convert hcontinuous using 1
  funext z
  exact spreadHomotopyToFun_orbit D S z.1 z.2.1 z.2.2

public noncomputable def spreadRetract : C(X, X) where
  toFun x := spreadHomotopyToFun D S (1, x)
  continuous_toFun := continuous_spreadHomotopyToFun D S |>.comp
    (continuous_const.prodMk continuous_id)

public noncomputable def spreadHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id X) (spreadRetract D S) where
  toFun := spreadHomotopyToFun D S
  continuous_toFun := continuous_spreadHomotopyToFun D S
  map_zero_left x := by
    rw [show x = S.orbit (representative D S x) from (orbit_representative D S x).symm,
      spreadHomotopyToFun_orbit]
    change S.orbit ((representative D S x).1,
      D.homotopy (0, (representative D S x).2)) = S.orbit (representative D S x)
    exact congrArg (fun p ↦ S.orbit ((representative D S x).1, p))
      (D.homotopy.map_zero_left (representative D S x).2)
  map_one_left _ := rfl

public theorem spreadHomotopyToFun_equivariant
    (g : G) (s : unitInterval) (x : X) :
    spreadHomotopyToFun D S (s, g • x) = g • spreadHomotopyToFun D S (s, x) := by
  let kp := representative D S x
  have hrep : S.orbit kp = x := orbit_representative D S x
  calc
    spreadHomotopyToFun D S (s, g • x) =
        spreadHomotopyToFun D S (s, g • S.orbit kp) := by rw [hrep]
    _ = spreadHomotopyToFun D S
        (s, S.orbit (S.deckPhase g kp.1, g • kp.2)) := by rw [S.deck_orbit]
    _ = S.orbit (S.deckPhase g kp.1, D.homotopy (s, g • kp.2)) :=
      spreadHomotopyToFun_orbit D S _ _ _
    _ = S.orbit (S.deckPhase g kp.1, g • D.homotopy (s, kp.2)) := by
      rw [D.homotopy_equivariant]
    _ = g • S.orbit (kp.1, D.homotopy (s, kp.2)) := S.deck_orbit g kp.1 _
    _ = g • spreadHomotopyToFun D S (s, S.orbit kp) := by
      rw [spreadHomotopyToFun_orbit]
    _ = g • spreadHomotopyToFun D S (s, x) := by rw [hrep]

/-- The phase-spread equivariant strong deformation retraction. -/
public noncomputable def equivariantStrongDeformationRetraction :
    EquivariantStrongDeformationRetraction G X B where
  retract := spreadRetract D S
  homotopy := spreadHomotopy D S
  retract_mem x := by
    rw [show x = S.orbit (representative D S x) from (orbit_representative D S x).symm]
    change spreadHomotopyToFun D S (1, S.orbit (representative D S x)) ∈ B
    rw [spreadHomotopyToFun_orbit]
    have heq : S.orbit ((representative D S x).1,
        D.homotopy (1, (representative D S x).2)) =
        S.orbit ((representative D S x).1, D.retract (representative D S x).2) :=
      congrArg (fun p ↦ S.orbit ((representative D S x).1, p))
        (D.homotopy.map_one_left (representative D S x).2)
    rw [heq]
    exact (S.target_iff _ _).2 (D.retract_mem _)
  retract_fixed x hx := by
    have hx' : S.orbit (representative D S x) ∈ B := by
      rw [orbit_representative D S]
      exact hx
    have hA : (representative D S x).2 ∈ A := (S.target_iff _ _).1 hx'
    rw [show x = S.orbit (representative D S x) from (orbit_representative D S x).symm]
    change spreadHomotopyToFun D S (1, S.orbit (representative D S x)) =
      S.orbit (representative D S x)
    rw [spreadHomotopyToFun_orbit]
    exact congrArg (fun p ↦ S.orbit ((representative D S x).1, p))
      (D.homotopy_fixed 1 _ hA)
  homotopy_fixed s x hx := by
    have hx' : S.orbit (representative D S x) ∈ B := by
      rw [orbit_representative D S]
      exact hx
    have hA : (representative D S x).2 ∈ A := (S.target_iff _ _).1 hx'
    rw [show x = S.orbit (representative D S x) from (orbit_representative D S x).symm]
    change spreadHomotopyToFun D S (s, S.orbit (representative D S x)) =
      S.orbit (representative D S x)
    rw [spreadHomotopyToFun_orbit]
    exact congrArg (fun p ↦ S.orbit ((representative D S x).1, p))
      (D.homotopy_fixed s _ hA)
  retract_equivariant g x := spreadHomotopyToFun_equivariant D S g 1 x
  homotopy_equivariant := spreadHomotopyToFun_equivariant D S

end ToricPhaseSpreadingData

end SphereSixComplex
