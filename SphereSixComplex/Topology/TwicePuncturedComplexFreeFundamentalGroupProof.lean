module

public import SphereSixComplex.Topology.TwicePuncturedComplexFundamentalGroupGeneration

/-!
# The canonical free-group presentation map for the twice-punctured plane

The two marked clockwise meridians define a canonical map from the free group on two generators
to the based fundamental group.  The existing based van Kampen generation theorem proves that
this map is surjective.  Injectivity is the remaining relation-free part of the usual van Kampen
calculation.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology.TwicePuncturedComplex

/-- The canonical map from the free group on two generators to the fundamental group, sending the
first generator to the clockwise meridian about zero and the second to the clockwise meridian
about one. -/
public def markedMeridianHom :
    FreeGroup (Fin 2) →*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  FreeGroup.lift fun i ↦ if i = 0 then zeroMeridianClass else oneMeridianClass

@[simp]
public theorem markedMeridianHom_first :
    markedMeridianHom (FreeGroup.of 0) = zeroMeridianClass := by
  simp [markedMeridianHom]

@[simp]
public theorem markedMeridianHom_second :
    markedMeridianHom (FreeGroup.of 1) = oneMeridianClass := by
  simp [markedMeridianHom]

/-- The two-piece based van Kampen generation theorem is exactly surjectivity of the canonical
free-group presentation map. -/
public theorem markedMeridianHom_surjective :
    Function.Surjective markedMeridianHom := by
  unfold markedMeridianHom
  apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr
  have hrange :
      Set.range (fun i : Fin 2 ↦ if i = 0 then zeroMeridianClass else oneMeridianClass) =
        {zeroMeridianClass, oneMeridianClass} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [hrange, markedMeridians_generate]

/-- Once injectivity of the canonical presentation map is supplied, the generator-preserving
fundamental-group equivalence is immediate. -/
public noncomputable def markedMeridianMulEquiv
    (hinj : Function.Injective markedMeridianHom) :
    FreeGroup (Fin 2) ≃*
      FundamentalGroup TwicePuncturedComplex twicePuncturedComplexBasepoint :=
  MulEquiv.ofBijective markedMeridianHom ⟨hinj, markedMeridianHom_surjective⟩

end TwicePuncturedComplex
end Topology
end SphereSixComplex

end

end
