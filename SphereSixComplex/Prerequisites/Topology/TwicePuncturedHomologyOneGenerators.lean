module
public import SphereSixComplex.Prerequisites.Topology.TwicePuncturedComplexFundamentalGroupGeneration
public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Topology
open StandardCircleHomologyLiftDegree EstablishedFirstHurewicz

public theorem twicePuncturedHomologyOneHom_eq_zero
    {B : Type*} [AddCommGroup B]
    (f : IntegralSingularHomology 1 TwicePuncturedComplex →+ B)
    (hzero : f (loopHomologyClass twicePuncturedClockwiseZeroMeridian) = 0)
    (hone : f (loopHomologyClass twicePuncturedClockwiseOneMeridian) = 0) : f = 0 := by
  let _ : PathConnectedSpace TwicePuncturedComplex := TwicePuncturedComplex.ambient_pathConnected
  let E := FirstHurewiczProof.establishedFirstHurewiczData_proof
    TwicePuncturedComplex twicePuncturedComplexBasepoint
  let g : FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint →*
      Multiplicative B :=
    { toFun := fun q ↦ Multiplicative.ofAdd (f (E.equiv (Additive.ofMul (Abelianization.of q))))
      map_one' := by
        change f (E.equiv (Additive.ofMul (Abelianization.of 1))) = 0
        rw [map_one]
        change f (E.equiv 0) = 0
        rw [map_zero, map_zero]
      map_mul' := by
        intro a b
        change f (E.equiv (Additive.ofMul (Abelianization.of (a * b)))) =
          f (E.equiv (Additive.ofMul (Abelianization.of a))) +
            f (E.equiv (Additive.ofMul (Abelianization.of b)))
        rw [map_mul]
        change f (E.equiv (Additive.ofMul (Abelianization.of a) +
          Additive.ofMul (Abelianization.of b))) = _
        rw [map_add, map_add] }
  have hgzero : g TwicePuncturedComplex.zeroMeridianClass = 1 := by
    change f (E.equiv (loopClass twicePuncturedClockwiseZeroMeridian)) = 0
    rw [E.equiv_loopClass, hzero]
  have hgone : g TwicePuncturedComplex.oneMeridianClass = 1 := by
    change f (E.equiv (loopClass twicePuncturedClockwiseOneMeridian)) = 0
    rw [E.equiv_loopClass, hone]
  have hall : (⊤ : Subgroup (FundamentalGroup TwicePuncturedComplex
      twicePuncturedComplexBasepoint)) ≤ g.ker := by
    rw [← TwicePuncturedComplex.markedMeridians_generate]
    apply (Subgroup.closure_le _).mpr
    intro q hq
    rcases hq with rfl | hq
    · exact hgzero
    · rcases hq with rfl
      exact hgone
  ext x
  obtain ⟨p, hp⟩ := loopClass_surjective (E.equiv.symm x)
  have h : g (Path.Homotopic.Quotient.mk p) = 1 := hall (Subgroup.mem_top _)
  change f (E.equiv (loopClass p)) = 0 at h
  rwa [hp, E.equiv.apply_symm_apply] at h

end SphereSixComplex.Topology
end
end
