module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

/-! # Actual relative integral singular chains and the homology sequence

The relative complex is the cokernel of the original inclusion of singular
chains on the actual subspace. Its short exact sequence is proved using
injectivity of that inclusion, and the connecting map is the proved snake
construction on these same complexes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original chain map induced by the original continuous map. -/
abbrev integralSingularChainMap (f : C(X, Y)) : integralSingularChains X ⟶ integralSingularChains Y :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map (TopCat.ofHom f)

/-- The actual continuous inclusion of the specified subspace. -/
def singularSubspaceInclusion (A : Set X) : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- Actual subspace inclusion is injective on the original singular chain complex. -/
instance integralSingularChainMap_subspace_mono (A : Set X) :
    Mono (integralSingularChainMap (singularSubspaceInclusion A)) := by
  have : Mono (TopCat.ofHom (singularSubspaceInclusion A)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  exact inferInstanceAs (Mono
    (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map
      (TopCat.ofHom (singularSubspaceInclusion A))))

/-- The actual relative complex C(X,A;Z), obtained by quotienting the original
singular subcomplex, with no assumed relative-homology interface. -/
def integralRelativeChains (A : Set X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (integralSingularChainMap (singularSubspaceInclusion A))

/-- The original short complex C(A) → C(X) → C(X,A). -/
def integralRelativeChainSequence (A : Set X) : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (integralSingularChainMap (singularSubspaceInclusion A))
    (cokernel.π _) (cokernel.condition _)

/-- Exactness comes from the proved inclusion and the actual cokernel. -/
theorem integralRelativeChainSequence_shortExact (A : Set X) :
    (integralRelativeChainSequence A).ShortExact where
  exact := (integralRelativeChainSequence A).exact_of_g_is_cokernel (cokernelIsCokernel _)
  mono_f := integralSingularChainMap_subspace_mono A
  epi_g := inferInstanceAs (Epi (cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))))

/-- Relative singular homology is the homology of that same quotient complex. -/
abbrev integralRelativeHomology (n : ℕ) (A : Set X) : ModuleCat.{u} ℤ :=
  (integralRelativeChains A).homology n

/-- The canonical map from absolute to relative homology. -/
def integralAbsoluteToRelative (n : ℕ) (A : Set X) :
    integralSingularHomology n X →ₗ[ℤ] integralRelativeHomology n A :=
  (HomologicalComplex.homologyMap (integralRelativeChainSequence A).g n).hom

/-- The actual boundary connecting homomorphism of the same pair. -/
def integralRelativeConnecting (n : ℕ) (A : Set X) :
    integralRelativeHomology (n + 1) A →ₗ[ℤ] integralSingularHomology n A :=
  ((integralRelativeChainSequence_shortExact A).δ (n + 1) n (by simp)).hom

/-- Exactness at the absolute group uses the actual inclusion and quotient maps. -/
theorem integralRelative_exact_absolute (n : ℕ) (A : Set X) :
    Function.Exact (integralSingularHomologyMap n (singularSubspaceInclusion A))
      (integralAbsoluteToRelative n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₂ n)

/-- Exactness at the relative group uses the constructed connecting map. -/
theorem integralRelative_exact_relative (n : ℕ) (A : Set X) :
    Function.Exact (integralAbsoluteToRelative (n + 1) A) (integralRelativeConnecting n A) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₃ (n + 1) n (by simp))

/-- Exactness at the subspace homology completes the actual pair sequence. -/
theorem integralRelative_exact_subspace (n : ℕ) (A : Set X) :
    Function.Exact (integralRelativeConnecting n A)
      (integralSingularHomologyMap n (singularSubspaceInclusion A)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((integralRelativeChainSequence_shortExact A).homology_exact₁ (n + 1) n (by simp))

/-- For a contractible ambient space the actual connecting map is an
isomorphism in positive subspace degree, as required for local homology. -/
def integralRelativeConnectingEquivOfContractible [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) (A : Set X) :
    integralRelativeHomology (n + 1) A ≃ₗ[ℤ] integralSingularHomology n A := by
  let := integralSingularHomology_subsingleton_of_contractible n hn X
  let := integralSingularHomology_subsingleton_of_contractible (n + 1) (by omega) X
  exact ((integralRelativeChainSequence_shortExact A).δIso (n + 1) n (by simp)
    (ModuleCat.isZero_of_subsingleton (integralSingularHomology (n + 1) X))
    (ModuleCat.isZero_of_subsingleton (integralSingularHomology n X))).toLinearEquiv

end DifferentialGeometry.Topology
