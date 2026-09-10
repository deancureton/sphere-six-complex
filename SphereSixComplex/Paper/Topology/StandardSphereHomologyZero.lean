module

public import SphereSixComplex.Prerequisites.Topology.StandardSphereHomologyZeroCore
public import SphereSixComplex.Paper.Topology.SectionSevenLerayRealization

namespace SphereSixComplex

/-- The degree-zero component of the standard sphere's Section 7 realization is now concrete. -/
public theorem sixSphere_sectionSevenHomologyRealization_zero :
    Nonempty (IntegralSingularHomology 0 SixSphere ≃+ SectionSevenComputedHomology 0) :=
  ⟨sixSphere_integralSingularHomology_zero_equiv_integer.trans
    sectionSevenComputedHomologyZeroEquivInteger.symm⟩

end SphereSixComplex
