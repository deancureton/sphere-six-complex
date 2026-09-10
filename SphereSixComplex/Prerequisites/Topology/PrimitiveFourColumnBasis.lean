module

public import SphereSixComplex.Prerequisites.Topology.IntegralPrimitiveComplement
public import SphereSixComplex.Prerequisites.Topology.MixedThreeColumnBasis

@[expose] public section
namespace SphereSixComplex

public theorem exists_fourCoordinates_of_signed_mixed
    {H : Type*} [AddCommGroup H] (e : H ≃+ (Fin 4 → ℤ)) (v : Fin 4 → H)
    (p : H →+ ℤ) (a b c : ℤˣ)
    (hc : ∀ j : Fin 3, e (v j.succ) =
      signedMixedThreeColumnEquiv a b c (Pi.single j.succ 1))
    (hp : ∀ j : Fin 3, p (v j.succ) = 0) (h0 : p (v 0) = 1) :
    ∃ r : H ≃+ (Fin 4 → ℤ), ∀ j : Fin 4, r (v j) = Pi.single j 1 := by
  let d := (signedMixedThreeColumnEquiv a b c).trans e.symm
  have hd (j : Fin 3) : d (Pi.single j.succ 1) = v j.succ := by
    apply e.injective
    change e (e.symm (signedMixedThreeColumnEquiv a b c (Pi.single j.succ 1))) = _
    rw [AddEquiv.apply_symm_apply]
    exact (hc j).symm
  obtain ⟨f, hf0, hft⟩ := exists_equiv_of_integer_primitive_complement 3 d (v 0) p
    (fun j ↦ by rw [hd]; exact hp j) h0
  refine ⟨f.symm, ?_⟩
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · rw [← hf0, AddEquiv.symm_apply_apply]
  · rw [← hd k, ← hft k, AddEquiv.symm_apply_apply]

end SphereSixComplex
