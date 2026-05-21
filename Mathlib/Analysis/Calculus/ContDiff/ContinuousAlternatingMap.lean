/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Smoothness of operations on continuous alternating maps

The pullback operator `compContinuousLinearMapCLM` is `C^n` in its defining continuous linear map,
assuming the typical-fiber data is finite-dimensional. The proof factors through the embedding
of alternating maps into continuous multilinear maps and pulls back via the finite-dimensional
postcomposition iff `ContinuousLinearMap.contDiff_comp_iff`.
-/

public section

open ContinuousAlternatingMap ContinuousMultilinearMap
open scoped ContDiff

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

/-- A continuous multilinear map space over finite-dimensional inputs and a finite-dimensional
target is itself finite-dimensional, via the injection into the (algebraic) multilinear maps. -/
instance ContinuousMultilinearMap.instFiniteDimensional
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Finite ι]
    {M₁ : ι → Type*} [∀ i, NormedAddCommGroup (M₁ i)] [∀ i, NormedSpace 𝕜 (M₁ i)]
    [∀ i, FiniteDimensional 𝕜 (M₁ i)]
    {M₂ : Type*} [NormedAddCommGroup M₂] [NormedSpace 𝕜 M₂] [FiniteDimensional 𝕜 M₂] :
    FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 M₁ M₂) :=
  FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (R' := 𝕜) (A := 𝕜) (M₁ := M₁) (M₂ := M₂))
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- A continuous alternating map space over a finite-dimensional source and target is itself
finite-dimensional, via the injection into the continuous multilinear maps. -/
instance ContinuousAlternatingMap.instFiniteDimensional
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Finite ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
    FiniteDimensional 𝕜 (E [⋀^ι]→L[𝕜] F) :=
  FiniteDimensional.of_injective
    { toFun := ContinuousAlternatingMap.toContinuousMultilinearMap
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl :
      (E [⋀^ι]→L[𝕜] F) →ₗ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F }
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

theorem ContinuousAlternatingMap.contDiff (f : E [⋀^ι]→L[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousMultilinearMap.contDiff

variable [CompleteSpace 𝕜] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] [FiniteDimensional 𝕜 F]

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  have hg : ContDiff 𝕜 n (fun p : E →L[𝕜] E' ↦
      (compContinuousLinearMapL (F := F) (fun _ : ι ↦ p)).comp (toContinuousMultilinearMapCLM 𝕜)) :=
    ContDiff.clm_comp compContinuousLinearMapL_diag_contDiff contDiff_const
  let Φ : ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) →ₗᵢ[𝕜]
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :=
    (toContinuousMultilinearMapLI (𝕜 := 𝕜) (ι := ι) (E := E) (F := F)).postcomp
    (E := E' [⋀^ι]→L[𝕜] F) (σ₁₂ := RingHom.id 𝕜) (σ₁₃ := RingHom.id 𝕜)
  have hg' : ContDiff 𝕜 n (⇑Φ ∘ compContinuousLinearMapCLM
      (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F)) := hg
  exact (Φ.toContinuousLinearMap.contDiff_comp_iff Φ.injective).mp hg'
