module

public import SphereSixComplex.Topology.CellularChainModel
public import SphereSixComplex.Topology.FiniteExactSequenceEuler
public import SphereSixComplex.Topology.IntegralPoincareUCT
public import SphereSixComplex.Topology.SmoothRecognition
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Cellular Euler--Poincaré through degree six

The alternating sum of the cell counts of a finite CW model equals the alternating sum of the
integral Betti numbers.  The proof is the usual rank bookkeeping on the cellular chain complex
supplied by `EstablishedCellularHomology.integralCWCellularChainModel`: in each degree the chain
group splits by rank into the cycles and the boundaries, the cycles split by rank into the
boundaries and the homology, and the boundary ranks telescope out of the alternating sum.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

namespace SphereSixComplex

namespace CellularEulerPoincare

/-! ### Rank bookkeeping over the integers -/

private lemma finrank_eq_of_module_structures {M : Type*} [AddCommGroup M]
    (moduleOne moduleTwo : Module ℤ M) :
    @Module.finrank ℤ M _ _ moduleOne = @Module.finrank ℤ M _ _ moduleTwo := by
  have h : moduleOne = moduleTwo := Subsingleton.elim _ _
  cases h
  rfl

/-- Rank-nullity over the integers, for finitely generated source. -/
public theorem finrank_range_add_finrank_ker {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) :
    Module.finrank ℤ f.range + Module.finrank ℤ (LinearMap.ker f) = Module.finrank ℤ M := by
  have hquotRange :
      @Module.finrank ℤ (M ⧸ f.ker) _ _ (Submodule.Quotient.module f.ker) =
        @Module.finrank ℤ f.range _ _ f.range.module :=
    @LinearEquiv.finrank_eq ℤ (M ⧸ f.ker) f.range _ _
      (Submodule.Quotient.module f.ker) _ f.range.module f.quotKerEquivRange
  have hExplicit :
      @Module.finrank ℤ f.range _ _ f.range.module +
          @Module.finrank ℤ f.ker _ _ f.ker.module = Module.finrank ℤ M := by
    rw [← hquotRange]
    exact Submodule.finrank_quotient_add_finrank _
  calc
    Module.finrank ℤ f.range + Module.finrank ℤ f.ker =
        @Module.finrank ℤ f.range _ _ f.range.module +
          @Module.finrank ℤ f.ker _ _ f.ker.module := by
      rw [finrank_eq_of_module_structures (AddCommGroup.toIntModule f.range) f.range.module,
        finrank_eq_of_module_structures (AddCommGroup.toIntModule f.ker) f.ker.module]
    _ = Module.finrank ℤ M := hExplicit

/-- Postcomposition with an injective map does not change the rank of the image. -/
public theorem finrank_range_comp_of_injective {M N P : Type*}
    [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
    [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) (hg : Function.Injective g) :
    Module.finrank ℤ (LinearMap.range (g.comp f)) = Module.finrank ℤ (LinearMap.range f) := by
  have hker : LinearMap.ker (g.comp f) = LinearMap.ker f := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact ⟨fun h ↦ hg (by simpa using h), fun h ↦ by simp [h]⟩
  have h1 := finrank_range_add_finrank_ker (g.comp f)
  have h2 := finrank_range_add_finrank_ker f
  have h3 : Module.finrank ℤ (LinearMap.ker (g.comp f)) = Module.finrank ℤ (LinearMap.ker f) :=
    congrArg (fun S : Submodule ℤ M ↦ Module.finrank ℤ S) hker
  omega

/-- An image with trivial source has rank zero. -/
public theorem finrank_range_eq_zero_of_range_eq_bot {M N : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (h : LinearMap.range f = ⊥) :
    Module.finrank ℤ (LinearMap.range f) = 0 := by
  have hsub : Subsingleton (LinearMap.range f) := by rw [h]; infer_instance
  exact Module.finrank_zero_of_subsingleton

/-! ### The cycle-boundary splitting of a chain complex of abelian groups -/

/-- The underlying `ℤ`-linear map of a morphism of abelian groups. -/
public def toIntLinearMap {A B : AddCommGrpCat} (f : A ⟶ B) : A →ₗ[ℤ] B :=
  (ConcreteCategory.hom f).toIntLinearMap

local notation "ℓ" => toIntLinearMap

/-- In each degree, the rank of the chain group is the rank of the homology plus the ranks of the
incoming and outgoing boundaries. -/
public theorem finrank_X_eq (K : ChainComplex AddCommGrpCat ℕ) (i j k : ℕ)
    (hi : (ComplexShape.down ℕ).prev j = i) (hj : (ComplexShape.down ℕ).next j = k)
    (hfj : Module.Finite ℤ (K.X j)) (hfi : Module.Finite ℤ (K.X i)) :
    Module.finrank ℤ (K.X j) =
      Module.finrank ℤ (K.homology j)
        + Module.finrank ℤ (LinearMap.range (ℓ (K.d i j)))
        + Module.finrank ℤ (LinearMap.range (ℓ (K.d j k))) := by
  have _ := hfj
  have _ := hfi
  have hinj : Function.Injective (ℓ (K.iCycles j)) := by
    rw [show Function.Injective (ℓ (K.iCycles j)) ↔ Function.Injective (K.iCycles j) from Iff.rfl,
      ← AddCommGrpCat.mono_iff_injective]
    infer_instance
  have hsurj : Function.Surjective (ℓ (K.homologyπ j)) := by
    rw [show Function.Surjective (ℓ (K.homologyπ j)) ↔ Function.Surjective (K.homologyπ j)
        from Iff.rfl, ← AddCommGrpCat.epi_iff_surjective]
    infer_instance
  have hfinCycles : Module.Finite ℤ (K.cycles j) :=
    Module.Finite.of_injective (ℓ (K.iCycles j)) hinj
  have hexactCycles : (ShortComplex.mk (K.iCycles j) (K.d j k) (K.iCycles_d j k)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel j k hj)
  have hexactHomology : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hi)
  have r1 := integral_finrank_eq_add_finrank_range_of_exact (ℓ (K.iCycles j)) (ℓ (K.d j k))
    ((ShortComplex.ab_exact_iff_function_exact _).mp hexactCycles)
  have r2 := integral_finrank_eq_add_finrank_range_of_exact (ℓ (K.toCycles i j))
    (ℓ (K.homologyπ j)) ((ShortComplex.ab_exact_iff_function_exact _).mp hexactHomology)
  have r3 := integral_finrank_range_eq_of_injective (ℓ (K.iCycles j)) hinj
  have r4 := integral_finrank_range_eq_of_surjective (ℓ (K.homologyπ j)) hsurj
  have r5 : Module.finrank ℤ (LinearMap.range (ℓ (K.d i j))) =
      Module.finrank ℤ (LinearMap.range (ℓ (K.toCycles i j))) := by
    have hcomp : (ℓ (K.iCycles j)).comp (ℓ (K.toCycles i j)) = ℓ (K.d i j) := by
      rw [show (ℓ (K.iCycles j)).comp (ℓ (K.toCycles i j))
        = ℓ (K.toCycles i j ≫ K.iCycles j) from rfl, K.toCycles_i]
    rw [← hcomp]
    exact finrank_range_comp_of_injective (ℓ (K.toCycles i j)) (ℓ (K.iCycles j)) hinj
  omega

/-- The alternating sum of the chain ranks through degree six equals the alternating sum of the
homology ranks, provided the complex has no chains in degree seven. -/
public theorem alternating_finrank_six (K : ChainComplex AddCommGrpCat ℕ)
    (hfin : ∀ n, Module.Finite ℤ (K.X n)) (h7 : Module.finrank ℤ (K.X 7) = 0) :
    (Module.finrank ℤ (K.homology 0) : ℤ) - Module.finrank ℤ (K.homology 1)
        + Module.finrank ℤ (K.homology 2) - Module.finrank ℤ (K.homology 3)
        + Module.finrank ℤ (K.homology 4) - Module.finrank ℤ (K.homology 5)
        + Module.finrank ℤ (K.homology 6) =
      (Module.finrank ℤ (K.X 0) : ℤ) - Module.finrank ℤ (K.X 1)
        + Module.finrank ℤ (K.X 2) - Module.finrank ℤ (K.X 3)
        + Module.finrank ℤ (K.X 4) - Module.finrank ℤ (K.X 5)
        + Module.finrank ℤ (K.X 6) := by
  have hprev : ∀ n : ℕ, (ComplexShape.down ℕ).prev n = n + 1 := fun n ↦ ChainComplex.prev ℕ n
  have hs0 := finrank_X_eq K 1 0 0 (hprev 0) ChainComplex.next_nat_zero (hfin 0) (hfin 1)
  have hs1 := finrank_X_eq K 2 1 0 (hprev 1) (ChainComplex.next_nat_succ 0) (hfin 1) (hfin 2)
  have hs2 := finrank_X_eq K 3 2 1 (hprev 2) (ChainComplex.next_nat_succ 1) (hfin 2) (hfin 3)
  have hs3 := finrank_X_eq K 4 3 2 (hprev 3) (ChainComplex.next_nat_succ 2) (hfin 3) (hfin 4)
  have hs4 := finrank_X_eq K 5 4 3 (hprev 4) (ChainComplex.next_nat_succ 3) (hfin 4) (hfin 5)
  have hs5 := finrank_X_eq K 6 5 4 (hprev 5) (ChainComplex.next_nat_succ 4) (hfin 5) (hfin 6)
  have hs6 := finrank_X_eq K 7 6 5 (hprev 6) (ChainComplex.next_nat_succ 5) (hfin 6) (hfin 7)
  have hbot : Module.finrank ℤ (LinearMap.range (ℓ (K.d 0 0))) = 0 := by
    refine finrank_range_eq_zero_of_range_eq_bot _ ?_
    have hd : K.d 0 0 = 0 := K.shape 0 0 (by simp)
    rw [show ℓ (K.d 0 0) = 0 by rw [hd]; rfl, LinearMap.range_zero]
  have htop : Module.finrank ℤ (LinearMap.range (ℓ (K.d 7 6))) = 0 := by
    have _ := hfin 7
    have := finrank_range_add_finrank_ker (ℓ (K.d 7 6))
    omega
  omega

/-! ### Euler--Poincaré for a finite CW carrier -/

/-- The truncated integral-homology Euler characteristic of a space homotopy equivalent to a
finite CW complex with no cells above degree six is the alternating sum of its cell counts. -/
public theorem integralHomologyEulerCharacteristicSix_eq_cellSum
    {X : Type} [TopologicalSpace X] {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] [Topology.CWComplex.Finite (Set.univ : Set Y)]
    (e : X ≃ₕ Y)
    (hempty : ∀ n, 6 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n)) :
    integralHomologyEulerCharacteristicSix X =
      (Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) 0) : ℤ)
        - Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) 1)
        + Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) 2)
        - Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) 3)
        + Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) 4)
        - Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) 5)
        + Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) 6) := by
  have hfinCell : ∀ n, Finite (Topology.CWComplex.cell (Set.univ : Set Y) n) :=
    fun n ↦ Topology.CWComplex.FiniteType.finite_cell (C := (Set.univ : Set Y)) n
  obtain CM := EstablishedCellularHomology.integralCWCellularChainModel Y
  have hXfin : ∀ n, Module.Finite ℤ (CM.chainComplex.X n) := by
    intro n
    have _ := hfinCell n
    exact Module.Finite.equiv (CM.cellBasis n).toIntLinearEquiv
  have hXrank : ∀ n, Module.finrank ℤ (CM.chainComplex.X n) =
      Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) n) := by
    intro n
    have _ := hfinCell n
    have _ : Fintype (Topology.CWComplex.cell (Set.univ : Set Y) n) := Fintype.ofFinite _
    calc Module.finrank ℤ (CM.chainComplex.X n)
        = Module.finrank ℤ (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) :=
          ((CM.cellBasis n).toIntLinearEquiv.finrank_eq).symm
      _ = Fintype.card (Topology.CWComplex.cell (Set.univ : Set Y) n) :=
          Module.finrank_finsupp_self ℤ
      _ = Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) n) :=
          Nat.card_eq_fintype_card.symm
  have hHrank : ∀ n, Module.finrank ℤ (CM.chainComplex.homology n) =
      Module.finrank ℤ (IntegralSingularHomology n X) := by
    intro n
    have _ := CM.comparison_homology_isIso n
    have hcar : CM.chainComplex.homology n ≃+ IntegralSingularHomology n Y :=
      (asIso (CM.chainComplex.homologyMap CM.comparison n)).addCommGroupIsoToAddEquiv
    have hX : IntegralSingularHomology n X ≃+ IntegralSingularHomology n Y :=
      integralSingularHomologyEquivOfHomotopyEquiv n e
    exact hcar.toIntLinearEquiv.finrank_eq.trans hX.toIntLinearEquiv.finrank_eq.symm
  have h7 : Module.finrank ℤ (CM.chainComplex.X 7) = 0 := by
    have _ := hempty 7 (by norm_num)
    rw [hXrank 7, Nat.card_of_isEmpty]
  have hmain := alternating_finrank_six CM.chainComplex hXfin h7
  unfold integralHomologyEulerCharacteristicSix
  rw [← hHrank 0, ← hHrank 1, ← hHrank 2, ← hHrank 3, ← hHrank 4, ← hHrank 5, ← hHrank 6,
    hmain, hXrank 0, hXrank 1, hXrank 2, hXrank 3, hXrank 4, hXrank 5, hXrank 6]

end CellularEulerPoincare

end SphereSixComplex

end

end
