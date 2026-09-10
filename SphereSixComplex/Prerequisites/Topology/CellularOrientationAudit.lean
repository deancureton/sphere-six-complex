module

public import SphereSixComplex.Prerequisites.Topology.CellularHomologyClassicalBoundary

@[expose] public section
noncomputable section
open CategoryTheory
namespace SphereSixComplex.CellularHomology.IntegralComparison

public def reverseDimension (T : CellularHomology.IntegralComparison) (k : ℕ) :
    CellularHomology.IntegralComparison :=
  { T with
    diskOrientation := fun n ↦ if n = k then (T.diskOrientation n).trans (AddEquiv.neg _) else
      T.diskOrientation n
    cellBasis := fun X _ _ _ n ↦ if n = k then (T.cellBasis X n).trans (AddEquiv.neg _) else
      T.cellBasis X n
    cellBasis_single := by
      intro X _ _ _ n e
      by_cases h : n = k
      · simp only [h, ↓reduceIte, AddEquiv.trans_apply, AddEquiv.neg_apply]
        rw [T.cellBasis_single]
        simp
      · simp only [h, ↓reduceIte]
        exact T.cellBasis_single X n e }

public theorem reverseDimension_attachingDegree
    (T : CellularHomology.IntegralComparison)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set X) n) :
    (T.reverseDimension (n + 1)).attachingDegree X n e e' =
      -T.attachingDegree X n e e' := by
  simp [attachingDegree, reverseDimension]

public theorem not_uniform_nonzero_attachingDegree
    (T : CellularHomology.IntegralComparison)
    (X : Type) [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (e : Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
    (e' : Topology.CWComplex.cell (Set.univ : Set X) n)
    (a : ℤ) (ha : a ≠ 0) :
    ¬∀ S : CellularHomology.IntegralComparison, S.attachingDegree X n e e' = a := by
  intro h
  have he := T.reverseDimension_attachingDegree X n e e'
  rw [h, h] at he
  omega

end SphereSixComplex.CellularHomology.IntegralComparison
