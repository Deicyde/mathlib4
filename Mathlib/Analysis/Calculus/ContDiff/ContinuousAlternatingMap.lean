/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

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
  -- TODO: Provide `Module.Finite` instances for ContinuousMultilinearMap and
  -- ContinuousAlternatingMap spaces (currently only available for the algebraic
  -- versions). Then this instance is automatic.
  haveI : FiniteDimensional 𝕜
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) := sorry
  exact (Φ.toContinuousLinearMap.contDiff_comp_iff Φ.injective).mp hg'
