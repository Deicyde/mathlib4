/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
public import Mathlib.Analysis.Calculus.ContDiff.LinearIsometry
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Smoothness of operations on continuous alternating maps

For `n : ℕ∞`, the pullback operator `compContinuousLinearMapCLM` is `C^n` in its defining
continuous linear map, assuming the target space `F` is complete.

The analytic case `n = ω` is not handled here; see
`Mathlib/Analysis/Calculus/ContDiff/LinearIsometry.lean` for the underlying obstruction.
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

variable [CompleteSpace F] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff {n : ℕ∞} :
    ContDiff 𝕜 (n : WithTop ℕ∞) (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  have hg : ContDiff 𝕜 (n : WithTop ℕ∞) (fun p : E →L[𝕜] E' ↦
      (compContinuousLinearMapL (F := F) (fun _ : ι ↦ p)).comp (toContinuousMultilinearMapCLM 𝕜)) :=
    ContDiff.clm_comp compContinuousLinearMapL_diag_contDiff contDiff_const
  let Φ := (toContinuousMultilinearMapLI (𝕜 := 𝕜) (ι := ι) (E := E) (F := F)).postcomp
    (E := E' [⋀^ι]→L[𝕜] F) (σ₁₂ := RingHom.id 𝕜) (σ₁₃ := RingHom.id 𝕜)
  exact (Φ.toContinuousLinearMap.contDiff_comp_iff_of_isometry_completeSpace
    Φ.norm_map).mp hg
