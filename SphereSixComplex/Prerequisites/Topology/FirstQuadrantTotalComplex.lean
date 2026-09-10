module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# First-quadrant total complexes

This file isolates the homological-algebra input needed to pass from exact rows of a
first-quadrant bicomplex to its direct-sum total complex.  Mathlib constructs total complexes,
but currently has no spectral-sequence or filtered-complex theorem connecting row homology to
total homology.  We first record the exact finite-filtration induction that such a construction
must feed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

public abbrev FirstQuadrantBicomplex :=
  HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)

public abbrev FirstQuadrantChainComplex :=
  HomologicalComplex AddCommGrpCat (ComplexShape.down ℕ)

/-- The finite antidiagonal indexing the summands of a first-quadrant total complex in degree
`n`.  This is deliberately the same fiber used by `GradedObject.mapObj` inside
`HomologicalComplex₂.total`. -/
public abbrev FirstQuadrantTotalFiber (n : ℕ) :=
  {pq : ℕ × ℕ // pq.1 + pq.2 = n}

noncomputable instance (n : ℕ) : Finite (FirstQuadrantTotalFiber n) := by
  apply Finite.of_injective
    (fun pq : FirstQuadrantTotalFiber n =>
      (⟨pq.1.1, by omega⟩ : Fin (n + 1)))
  intro pq rs h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext_iff.mp h
  · have h₁ : pq.1.1 = rs.1.1 := Fin.ext_iff.mp h
    omega

/-- Before taking the coproduct in total degree `n`, a bicomplex gives the discrete diagram of
its entries on the `n`th antidiagonal. -/
@[simps]
public def firstQuadrantTotalFiberDiagramFunctor (n : ℕ) :
    FirstQuadrantBicomplex ⥤ (Discrete (FirstQuadrantTotalFiber n) ⥤ AddCommGrpCat) where
  obj K := Discrete.functor fun pq => (K.X pq.1.1).X pq.1.2
  map f := Discrete.natTrans fun pq => (f.f pq.as.1.1).f pq.as.1.2

/-- Evaluation of the antidiagonal diagram is the corresponding pair of evaluations of the
bicomplex. -/
public def firstQuadrantTotalFiberEvaluationIso (n : ℕ)
    (pq : Discrete (FirstQuadrantTotalFiber n)) :
    firstQuadrantTotalFiberDiagramFunctor n ⋙
        (evaluation (Discrete (FirstQuadrantTotalFiber n)) AddCommGrpCat).obj pq ≅
      HomologicalComplex.eval FirstQuadrantChainComplex (ComplexShape.down ℕ) pq.as.1.1 ⋙
        HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) pq.as.1.2 :=
  NatIso.ofComponents (fun _ => Iso.refl _)

noncomputable instance (n : ℕ) :
    PreservesFiniteLimits (firstQuadrantTotalFiberDiagramFunctor n) := by
  apply preservesFiniteLimits_of_evaluation
  intro pq
  exact preservesFiniteLimits_of_natIso
    (firstQuadrantTotalFiberEvaluationIso n pq).symm

noncomputable instance (n : ℕ) :
    PreservesFiniteColimits (firstQuadrantTotalFiberDiagramFunctor n) := by
  apply preservesFiniteColimits_of_evaluation
  intro pq
  exact preservesFiniteColimits_of_natIso
    (firstQuadrantTotalFiberEvaluationIso n pq).symm

/-- The exact functor which takes the finite coproduct of all entries in total degree `n`. -/
public noncomputable def firstQuadrantTotalDegreeFunctor (n : ℕ) :
    FirstQuadrantBicomplex ⥤ AddCommGrpCat :=
  firstQuadrantTotalFiberDiagramFunctor n ⋙
    colim (J := Discrete (FirstQuadrantTotalFiber n)) (C := AddCommGrpCat)

noncomputable instance (n : ℕ) :
    PreservesFiniteLimits (firstQuadrantTotalDegreeFunctor n) := by
  dsimp only [firstQuadrantTotalDegreeFunctor]
  infer_instance

noncomputable instance (n : ℕ) :
    PreservesFiniteColimits (firstQuadrantTotalDegreeFunctor n) := by
  dsimp only [firstQuadrantTotalDegreeFunctor]
  infer_instance

@[simp]
public theorem firstQuadrant_totalDegree_eq_add (pq : ℕ × ℕ) :
    ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) pq = pq.1 + pq.2 := rfl

/-- Evaluation of Mathlib's direct-sum total complex agrees with the explicit finite
antidiagonal coproduct functor above. -/
public noncomputable def firstQuadrantTotalEvaluationIso (n : ℕ) :
    HomologicalComplex₂.totalFunctor AddCommGrpCat
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⋙
      HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) n ≅
    firstQuadrantTotalDegreeFunctor n :=
  NatIso.ofComponents (fun _ => Iso.refl _)

noncomputable instance : PreservesFiniteLimits
    (HomologicalComplex₂.totalFunctor AddCommGrpCat
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) := by
  refine ⟨by
    intro J _ _
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    exact preservesLimitsOfShape_of_natIso
      (J := J) (firstQuadrantTotalEvaluationIso n).symm⟩

noncomputable instance : PreservesFiniteColimits
    (HomologicalComplex₂.totalFunctor AddCommGrpCat
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) := by
  refine ⟨by
    intro J _ _
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    exact preservesColimitsOfShape_of_natIso
      (J := J) (firstQuadrantTotalEvaluationIso n).symm⟩

/-- Direct-sum totalization of first-quadrant bicomplexes preserves short exact sequences.
The finiteness of each antidiagonal is the essential boundedness input. -/
public theorem firstQuadrantTotal_shortExact
    (S : ShortComplex FirstQuadrantBicomplex) (hS : S.ShortExact) :
    (S.map (HomologicalComplex₂.totalFunctor AddCommGrpCat
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))).ShortExact :=
  hS.map_of_exact _

/-- The middle-map version of two-out-of-three for a morphism of short exact sequences of
complexes.  Mathlib currently only packages the corresponding result for `τ₃`; this form is
the induction step needed for finite filtrations. -/
public theorem quasiIso_middle_of_shortExact
    {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
    {S₁ S₂ : ShortComplex (HomologicalComplex C c)}
    (f : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso f.τ₁) (h₃ : QuasiIso f.τ₃) : QuasiIso f.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hi₁ : QuasiIsoAt f.τ₁ i := (quasiIso_iff f.τ₁).mp h₁ i
  have hi₃ : QuasiIsoAt f.τ₃ i := (quasiIso_iff f.τ₃).mp h₃ i
  let φ := (HomologicalComplex.homologyFunctor C c i).mapShortComplex.map f
  let _ : IsIso φ.τ₁ := by
    dsimp [φ]
    exact (quasiIsoAt_iff_isIso_homologyMap f.τ₁ i).mp hi₁
  let _ : IsIso φ.τ₃ := by
    dsimp [φ]
    exact (quasiIsoAt_iff_isIso_homologyMap f.τ₃ i).mp hi₃
  let _ : Mono φ.τ₂ := by
    by_cases hi : ∃ k, c.Rel k i
    · obtain ⟨k, hki⟩ := hi
      have hk₃ : QuasiIsoAt f.τ₃ k := (quasiIso_iff f.τ₃).mp h₃ k
      let _ : IsIso (HomologicalComplex.homologyMap f.τ₃ k) :=
        (quasiIsoAt_iff_isIso_homologyMap f.τ₃ k).mp hk₃
      let Φ := ((CategoryTheory.ComposableArrows.δ₀Functor ⋙
        CategoryTheory.ComposableArrows.δ₀Functor).map
          (HomologicalComplex.HomologySequence.mapComposableArrows₅
            f hS₁ hS₂ k i hki))
      apply CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono Φ
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
          hS₁ k i hki).δ₀.δ₀
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
          hS₂ k i hki).δ₀.δ₀
      · change Epi (HomologicalComplex.homologyMap f.τ₃ k)
        infer_instance
      · change Mono (HomologicalComplex.homologyMap f.τ₁ i)
        infer_instance
      · change Mono (HomologicalComplex.homologyMap f.τ₃ i)
        infer_instance
    · let _ : Mono (HomologicalComplex.homologyMap S₂.f i) := by
        have := hS₂.mono_f
        exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S₂.f i
          (by simpa using hi)
      apply ShortComplex.mono_of_mono_of_mono_of_mono φ (hS₁.homology_exact₂ i)
      · change Mono (HomologicalComplex.homologyMap S₂.f i)
        infer_instance
      all_goals infer_instance
  let _ : Epi φ.τ₂ := by
    by_cases hi : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hi
      have hj₁ : QuasiIsoAt f.τ₁ j := (quasiIso_iff f.τ₁).mp h₁ j
      let _ : IsIso (HomologicalComplex.homologyMap f.τ₁ j) :=
        (quasiIsoAt_iff_isIso_homologyMap f.τ₁ j).mp hj₁
      let Φ := ((CategoryTheory.ComposableArrows.δlastFunctor ⋙
        CategoryTheory.ComposableArrows.δlastFunctor).map
          (HomologicalComplex.HomologySequence.mapComposableArrows₅
            f hS₁ hS₂ i j hij))
      apply CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono Φ
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
          hS₁ i j hij).δlast.δlast
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact
          hS₂ i j hij).δlast.δlast
      · change Epi (HomologicalComplex.homologyMap f.τ₁ i)
        infer_instance
      · change Epi (HomologicalComplex.homologyMap f.τ₃ i)
        infer_instance
      · change Mono (HomologicalComplex.homologyMap f.τ₁ j)
        infer_instance
    · let _ : Epi (HomologicalComplex.homologyMap S₁.g i) := by
        have := hS₁.epi_g
        exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S₁.g i
          (by simpa using hi)
      apply ShortComplex.epi_of_epi_of_epi_of_epi φ (hS₂.homology_exact₂ i)
      · change Epi (HomologicalComplex.homologyMap S₁.g i)
        infer_instance
      all_goals infer_instance
  change IsIso φ.τ₂
  apply isIso_of_mono_of_epi

/-- A map between two filtrations is a quasi-isomorphism at every finite stage if it is one on
the initial subobject and on every successive quotient.  The isomorphisms `glue` allow adjacent
short exact sequences to use merely isomorphic (rather than definitionally equal) models for a
filtration stage. -/
public theorem quasiIso_of_successive_shortExact_extensions
    {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
    (A B : ℕ → ShortComplex (HomologicalComplex C c))
    (f : ∀ n, A n ⟶ B n)
    (hA : ∀ n, (A n).ShortExact) (hB : ∀ n, (B n).ShortExact)
    (hbase : QuasiIso (f 0).τ₁) (hgraded : ∀ n, QuasiIso (f n).τ₃)
    (glue : ∀ n, Arrow.mk (f n).τ₂ ≅ Arrow.mk (f (n + 1)).τ₁) :
    ∀ n, QuasiIso (f n).τ₂ := by
  intro n
  induction n with
  | zero =>
      exact quasiIso_middle_of_shortExact (f 0) (hA 0) (hB 0) hbase (hgraded 0)
  | succ n ih =>
      let _ : QuasiIso (f n).τ₂ := ih
      have hleft : QuasiIso (f (n + 1)).τ₁ :=
        quasiIso_of_arrow_mk_iso
          (f n).τ₂ (f (n + 1)).τ₁ (glue n)
      exact quasiIso_middle_of_shortExact (f (n + 1))
        (hA (n + 1)) (hB (n + 1)) hleft (hgraded (n + 1))

/-- The finite-filtration criterion specialized to first-quadrant direct-sum totals.  This is the
formal endpoint consumed by a brutal-column filtration: one supplies short exact bicomplex
layers, quasi-isomorphisms on the initial layer and the single-column quotients, and the canonical
identifications between consecutive stages. -/
public theorem firstQuadrantTotal_quasiIso_of_successive_extensions
    (A B : ℕ → ShortComplex FirstQuadrantBicomplex)
    (f : ∀ n, A n ⟶ B n)
    (hA : ∀ n, (A n).ShortExact) (hB : ∀ n, (B n).ShortExact)
    (hbase : QuasiIso
      ((HomologicalComplex₂.totalFunctor AddCommGrpCat
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
          (f 0).τ₁))
    (hgraded : ∀ n, QuasiIso
      ((HomologicalComplex₂.totalFunctor AddCommGrpCat
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
          (f n).τ₃))
    (glue : ∀ n, Arrow.mk (f n).τ₂ ≅ Arrow.mk (f (n + 1)).τ₁) :
    ∀ n, QuasiIso
      ((HomologicalComplex₂.totalFunctor AddCommGrpCat
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
          (f n).τ₂) := by
  let T := HomologicalComplex₂.totalFunctor AddCommGrpCat
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  apply quasiIso_of_successive_shortExact_extensions
    (fun n => (A n).map T) (fun n => (B n).map T)
    (fun n => T.mapShortComplex.map (f n))
  · exact fun n => firstQuadrantTotal_shortExact (A n) (hA n)
  · exact fun n => firstQuadrantTotal_shortExact (B n) (hB n)
  · exact hbase
  · exact hgraded
  · exact fun n => T.mapArrow.mapIso (glue n)

end SphereSixComplex
