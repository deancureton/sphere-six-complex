module

public import SphereSixComplex.Topology.SpecialOrthogonalSevenPiFiveExactness
public import SphereSixComplex.Topology.SixSpherePiFiveVanishing

/-!
# Reduction of `π₅(SO(7))` to stabilization from `SO(6)`

Exactness of `SO(6) → SO(7) → S⁶`, together with the vanishing of `π₅(S⁶)`, makes
degree-five stabilization surjective.  Consequently, the only remaining input for
`Subsingleton (π₅(SO(7)))` is that stabilization kills every class.  This file records both the
group-level reduction and its representative-level generalized-loop form.
-/

@[expose] public section

noncomputable section

open Set
open scoped MatrixGroups Topology.Homotopy

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

/-- Sphere-side vanishing makes degree-five stabilization surjective. -/
public theorem stabilizePiFive_surjective : Function.Surjective stabilizePiFive := by
  intro a
  have ha : firstColumnPiFive a = 1 :=
    (sixSphere_piFive_subsingleton (firstColumn (1 : SO7))).elim _ _
  exact Set.ext_iff.mp range_stabilizePiFive_eq_ker_firstColumnPiFive a |>.mpr ha

/-- Vanishing of stabilization is the only remaining input for `π₅(SO(7)) = 0`. -/
public theorem piFiveSO7_subsingleton_of_stabilize_eq_one
    (hStabilize : ∀ a : HomotopyGroup.Pi 5 SO6 (1 : SO6), stabilizePiFive a = 1) :
    Subsingleton (HomotopyGroup.Pi 5 SO7 (1 : SO7)) := by
  constructor
  intro a b
  obtain ⟨a', rfl⟩ := stabilizePiFive_surjective a
  obtain ⟨b', rfl⟩ := stabilizePiFive_surjective b
  exact (hStabilize a').trans (hStabilize b').symm

/-- Representative nullhomotopies suffice to show that stabilization vanishes. -/
public theorem stabilizePiFive_eq_one_of_representative_null
    (hNull : ∀ g : Ω^ (Fin 5) SO6 (1 : SO6),
      GenLoop.Homotopic
        (GenLoop.map stabilizeMap stabilizeMap_one g)
        (_root_.GenLoop.const : Ω^ (Fin 5) SO7 (1 : SO7))) :
    ∀ a : HomotopyGroup.Pi 5 SO6 (1 : SO6), stabilizePiFive a = 1 := by
  intro a
  induction a using Quotient.inductionOn with
  | h g => exact (Quotient.sound (hNull g)).trans _root_.HomotopyGroup.one_def

/-- A representative-level stabilization theorem closes the degree-five `SO(7)` computation. -/
public theorem piFiveSO7_subsingleton_of_representative_null
    (hNull : ∀ g : Ω^ (Fin 5) SO6 (1 : SO6),
      GenLoop.Homotopic
        (GenLoop.map stabilizeMap stabilizeMap_one g)
        (_root_.GenLoop.const : Ω^ (Fin 5) SO7 (1 : SO7))) :
    Subsingleton (HomotopyGroup.Pi 5 SO7 (1 : SO7)) :=
  piFiveSO7_subsingleton_of_stabilize_eq_one
    (stabilizePiFive_eq_one_of_representative_null hNull)

end SphereSixComplex.SpecialOrthogonalSevenStiefel
