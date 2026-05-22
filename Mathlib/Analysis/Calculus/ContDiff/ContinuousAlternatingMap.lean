/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Smoothness of operations on continuous alternating maps

The pullback operator `compContinuousLinearMapCLM` is `C^n` in its defining continuous linear map.
For `n : ℕ∞` this holds in any characteristic with `[CompleteSpace F]`; the analytic case `n = ω`
requires `[CharZero 𝕜]` so that the polarization formula can lift the order-`n` Taylor coefficient
into the alternating-target operator space.

## Implementation notes

In characteristic 0, the explicit `1/n!`-weighted symmetrized sum produces a continuous
multilinear map whose diagonal recovers the polynomial `p ↦ compContinuousLinearMapCLM p`,
showing that this polynomial of degree `Fintype.card ι` is analytic. In positive characteristic
`p ≤ Fintype.card ι` the polarization formula is unavailable, and no continuous symmetric
multilinear lift into the alternating-target space is known.

The construction here introduces `ContinuousMultilinearMap.alternatizationCLM`, the continuous
linear map upgrade of Mathlib's existing `AddMonoidHom`-valued `alternatization`, and uses it
to plumb `compContinuousLinearMapContinuousMultilinear` (the multi-target version, char-free)
into the alt-target setting via polarization.
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

section Alternatization

variable [DecidableEq ι]

/-- Continuous-linear-map upgrade of `ContinuousMultilinearMap.alternatization`, which Mathlib
provides only as an `AddMonoidHom`. The norm bound `‖alternatization f‖ ≤ (Fintype.card ι)! · ‖f‖`
follows by writing alternatization as a sum over `Equiv.Perm ι` with each summand norm-bounded
by `‖f‖` (the sign acts by `±1` and `domDomCongr` preserves norm). -/
noncomputable def ContinuousMultilinearMap.alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := ContinuousMultilinearMap.alternatization
      map_add' := fun f g ↦ (ContinuousMultilinearMap.alternatization
        (R := 𝕜) (M := E) (N := F) (ι := ι)).map_add f g
      map_smul' := fun c f ↦ by
        ext v
        change (alternatization (c • f)) v = c • alternatization f v
        rw [alternatization_apply_apply, alternatization_apply_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ ↦ ?_
        rw [show (c • f) (v ∘ σ) = c • f (v ∘ σ) from rfl, smul_comm] }
    ⟨(Fintype.card ι).factorial, fun f ↦ by
      rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
      change ‖∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ‖ ≤ _
      refine (norm_sum_le _ _).trans ?_
      rw [show ((Fintype.card ι).factorial : ℝ) * ‖f‖ = ∑ _σ : Equiv.Perm ι, ‖f‖ by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun σ _ ↦ ?_
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsgn | hsgn
      · rw [hsgn]; simp [ContinuousMultilinearMap.norm_domDomCongr]
      · rw [hsgn]; simp [Units.neg_smul, ContinuousMultilinearMap.norm_domDomCongr]⟩

end Alternatization

variable [CompleteSpace F] [CharZero 𝕜]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

section Polarization

variable [DecidableEq ι]

/-- The polarized continuous multilinear lift of `compContinuousLinearMapCLM`. Constructed as
the composition of `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`
(the multi-target CMM-in-`p`) with `toContinuousMultilinearMapCLM` (pre-composition by the
alt ↪ multi embedding) and `alternatizationCLM` (post-composition by the multi → alt projection,
scaled by `(1/k!)`). -/
private noncomputable def compContinuousLinearMapPolarized :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E →L[𝕜] E')
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  -- Step 1: pre-compose with `toContinuousMultilinearMapCLM`:
  --   (CMM E' →L CMM E) →L (alt' →L CMM E)
  -- Step 2: post-compose with `alternatizationCLM`:
  --   (alt' →L CMM E) →L (alt' →L alt)
  -- Combined as a CLM acting on the value of `compContinuousLinearMapContinuousMultilinear`.
  let pre : (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) →L[𝕜]
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :=
    (ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)).flip
      (toContinuousMultilinearMapCLM 𝕜)
  let post : ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) →L[𝕜]
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
    ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (E [⋀^ι]→L[𝕜] F)
      (alternatizationCLM (𝕜 := 𝕜) (ι := ι) (E := E) (F := F))
  ((Fintype.card ι).factorial : 𝕜)⁻¹ • (post ∘L pre).compContinuousMultilinearMap
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ E') F)

omit [CompleteSpace F] in
private theorem compContinuousLinearMapPolarized_diag (p : E →L[𝕜] E') :
    compContinuousLinearMapPolarized (E := E) (E' := E') (F := F) (ι := ι) (fun _ ↦ p) =
      compContinuousLinearMapCLM p := by
  classical
  -- Diagonal: applying `alternatization` to an already-alternating CMM gives `k!` times itself,
  -- and the `(1/k!)` scalar cancels this.
  ext Φ v
  change ((Fintype.card ι).factorial : 𝕜)⁻¹ •
      (alternatization (Φ.toContinuousMultilinearMap.compContinuousLinearMap (fun _ ↦ p))) v
    = Φ (fun i ↦ p (v i))
  rw [alternatization_apply_apply]
  -- Each term in the sum: `sgn σ • Φ((p ∘ v) ∘ σ) = sgn σ • sgn σ • Φ(p ∘ v) = Φ(p ∘ v)`,
  -- using `Φ.toAlternatingMap.map_perm`.
  have hperm : ∀ σ : Equiv.Perm ι,
      Equiv.Perm.sign σ • Φ.toContinuousMultilinearMap.compContinuousLinearMap
        (fun _ : ι ↦ p) (v ∘ σ) = Φ (fun i ↦ p (v i)) := by
    intro σ
    change Equiv.Perm.sign σ • Φ (fun i ↦ p ((v ∘ σ) i)) = Φ (fun i ↦ p (v i))
    rw [show (fun i ↦ p ((v ∘ σ) i)) = (fun i ↦ p (v i)) ∘ σ from rfl,
      show Φ ((fun i ↦ p (v i)) ∘ σ) = Φ.toAlternatingMap ((fun i ↦ p (v i)) ∘ σ) from rfl,
      Φ.toAlternatingMap.map_perm, smul_smul, Int.units_mul_self, one_smul]
    rfl
  rw [Finset.sum_congr rfl (fun σ _ ↦ hperm σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, ← Nat.cast_smul_eq_nsmul (R := 𝕜), smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_smul]

end Polarization

omit [CompleteSpace F] in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  classical
  -- Write `compContinuousLinearMapCLM` as the diagonal of the polarized multilinear lift,
  -- then conclude via `ContinuousMultilinearMap.contDiff` ∘ diagonal.
  have hμ : ContDiff 𝕜 n (compContinuousLinearMapPolarized (𝕜 := 𝕜) (ι := ι)
      (E := E) (E' := E') (F := F)) := ContinuousMultilinearMap.contDiff _
  have hΔ : ContDiff 𝕜 n (fun p : E →L[𝕜] E' ↦ (fun _ : ι ↦ p)) :=
    contDiff_pi.mpr (fun _ ↦ contDiff_id)
  have heq : compContinuousLinearMapCLM (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F) =
      (fun (p : ι → (E →L[𝕜] E')) ↦ compContinuousLinearMapPolarized p) ∘
      (fun p : E →L[𝕜] E' ↦ (fun _ ↦ p)) := by
    funext p
    exact (compContinuousLinearMapPolarized_diag p).symm
  rw [heq]
  exact hμ.comp hΔ
