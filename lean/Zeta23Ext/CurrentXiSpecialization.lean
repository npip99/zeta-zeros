/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentAnalyticInstantiation
import Zeta23Ext.CurrentWindowMoments
import Zeta23.XiPrime.Coeff
import Zeta23.XiPrime.Coeff.Reexpansion
import Zeta23.XiPrime.Final

/-!
# The current window with the proved xi-prime coefficient inputs

This file removes two abstract premises from the current-window analytic
interface by using the pinned upstream theorems for the actual `xiCoeffFamily`:
its coefficient hypotheses and its coefficient re-expansion.  For the actual
`xiDerivZeros₀` configuration it also supplies the unconditional
Riemann--von Mangoldt theorem.

The remaining ratio constant is deliberately written as
`cWin D1 P.lam CurrentWindow.window`.  It is not identified with the paper's
endpoint distance functional `CurrentWindow.c1`: `D1` is the xi-prime
diagonal density, whereas the distance functional corresponds to the linear
density at `lambda = 1`.  Likewise, no upstream theorem supplies `XiEF` for
this exact global cosine-polynomial profile, so that premise remains visible.
-/

noncomputable section

open Filter MeasureTheory Set Topology

namespace Zeta23Ext.CurrentXiSpecialization

open Zeta23
open Zeta23.XiPrime
open Zeta23Ext.CurrentAnalyticInstantiation

/-- Positivity of the exact current-window xi-prime ratio constant. -/
theorem current_cWin_D1_pos {P : Params} (hP : P.Valid)
    (hcert : CurrentWindow.WindowCertificate) :
    0 < cWin D1 P.lam CurrentWindow.window := by
  apply cWin_pos
  · have hm : 0 < CurrentWindow.windowMass CurrentWindow.window := by
      rw [← CurrentWindow.kernel_zero_eq_mass]
      exact CurrentWindow.kernel_zero_pos hcert
    exact ne_of_gt hm
  · exact CurrentWindowMoments.current_window_sq_integral_pos hcert
  · exact jWin_nonneg (fun _ hs => D1_nonneg hs.1)
      (CurrentWindow.window_nonneg_on_support hcert) hP.lam_pos.le
      hP.lam_le_one
  · exact hP.lam_pos

/-- For the actual xi-prime coefficient family, the pinned re-expansion
theorem closes the last coefficient-side premise of trace transfer. -/
theorem current_traceTransfer_xi {Z : ZeroConfig} {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hR : RiemannVonMangoldt Z)
    (hEF : XiEF Z (P.atV CurrentWindow.window)) :
    XiTraceTransfer Z (P.atV CurrentWindow.window) xiCoeffFamily := by
  obtain ⟨e, ρ₀, A, T₀, hρ₀, hE⟩ := xiReexpansion
  exact current_traceTransfer hP hlam hcert hR hEF hρ₀ hE

/-- For `xiCoeffFamily`, the upstream coefficient theorem and the proved
positivity above reduce coefficient moments to the one current-window ratio
limit displayed in the statement. -/
theorem current_coeffMoments_xi {Z : ZeroConfig} {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hR : RiemannVonMangoldt Z)
    (hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (JD D1 (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (Zeta23.l T))) atTop
        (𝓝 (cWin D1 P.lam CurrentWindow.window))) :
    CoeffMoments Z (P.atV CurrentWindow.window) xiCoeffFamily
      (cWin D1 P.lam CurrentWindow.window)⁻¹ := by
  exact current_coeffMoments hP hlam hcert xiCoeffFamily_hyps hR
    (current_cWin_D1_pos hP hcert) hratio

/-- Current-window `GzMoments` for the actual xi-prime coefficients.  The
coefficient hypotheses and re-expansion are no longer assumptions. -/
theorem current_gzMoments_xi {Z : ZeroConfig} {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hR : RiemannVonMangoldt Z)
    (hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (JD D1 (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (Zeta23.l T))) atTop
        (𝓝 (cWin D1 P.lam CurrentWindow.window)))
    (hEF : XiEF Z (P.atV CurrentWindow.window)) :
    GzMoments Z (P.atV CurrentWindow.window)
      (cWin D1 P.lam CurrentWindow.window)⁻¹ :=
  gzMoments_of_transfer Z _ xiCoeffFamily
    (inv_nonneg.mpr (current_cWin_D1_pos hP hcert).le)
    (current_coeffMoments_xi hP hlam hcert hR hratio)
    (current_traceTransfer_xi hP hlam hcert hR hEF)

/-- Concrete xi-prime-zero specialization: the unconditional upstream RvM
theorem is supplied, so the only remaining analytic premises are the exact
current-window ratio limit and the exact current-window explicit formula. -/
theorem current_gzMoments_xiDeriv {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (JD D1 (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (Zeta23.l T))) atTop
        (𝓝 (cWin D1 P.lam CurrentWindow.window)))
    (hEF : XiEF xiDerivZeros₀ (P.atV CurrentWindow.window)) :
    GzMoments xiDerivZeros₀ (P.atV CurrentWindow.window)
      (cWin D1 P.lam CurrentWindow.window)⁻¹ :=
  current_gzMoments_xi hP hlam hcert xiDerivZeros₀_rvm hratio hEF

/-- The first two current-window moments, continuity of the autocorrelation,
the `D1` coefficient hypotheses, coefficient re-expansion, and RvM are all
discharged.  For the concrete xi-prime zero configuration, the remaining
analytic premises are exactly the displayed autocorrelation comparison and
the current-window explicit formula. -/
theorem current_gzMoments_xiDeriv_of_autocorr {P : Params}
    (hP : P.Valid) (hlam : P.lam < 1)
    (hcert : CurrentWindow.WindowCertificate)
    (hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0 : ℝ) (P.L T),
      |AdmWindow.gv (P.phiV CurrentWindow.window T) y -
        P.L T * vConv CurrentWindow.window (y / P.L T)| ≤ 4 * P.w)
    (hEF : XiEF xiDerivZeros₀ (P.atV CurrentWindow.window)) :
    GzMoments xiDerivZeros₀ (P.atV CurrentWindow.window)
      (cWin D1 P.lam CurrentWindow.window)⁻¹ := by
  have hr₀ := CurrentWindowMoments.tendsto_cRatio_current_of_autocorr
    hP hcert (continuousOn_D1 _) (fun _ hs => D1_nonneg hs.1) hg
  have hratio : Tendsto (fun T => ThmD.cRatio (P.lam1 T)
      (AdmWindow.av ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (AdmWindow.bv ((P.atV CurrentWindow.window T).phi T) (P.L T))
      (JD D1 (AdmWindow.gv ((P.atV CurrentWindow.window T).phi T))
        (P.L T) (Zeta23.l T))) atTop
        (𝓝 (cWin D1 P.lam CurrentWindow.window)) := by
    convert hr₀ using 1
    funext T
    rw [Params.atV_phi_valid T hP CurrentWindow.window_even]
  exact current_gzMoments_xiDeriv hP hlam hcert hratio hEF

end Zeta23Ext.CurrentXiSpecialization
