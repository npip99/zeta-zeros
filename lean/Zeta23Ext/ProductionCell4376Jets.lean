/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.SincJetCertificate
import Zeta23Ext.CurrentKernelDerivatives

/-!
# Checked sinc-jet rows for production cell 4376

This generated-style module keeps the large table instantiation separate from
the reusable semantics.  Each row has a Boolean rational jet check plus a
kernel-checked `pi` range reduction for its trigonometric center.
-/

noncomputable section

open Real Set

namespace Zeta23Ext.ProductionCell4376Jets

open SincDerivativeCertificate SincJetCertificate

private def reducedCenter : ℚ := 184814 / 625000

private def plusOneTrig : RationalTrigCell.Witness :=
  ⟨2, reducedCenter, 1 / 100000000, 1, 1 / 5000000⟩

/-- The periodic `j=1` plus argument, centered at `6.5788877`. -/
def plusOne : SincJetCertificate.Witness where
  q := 65788877 / 10000000
  radius := 1 / 2500
  upper := 65792877 / 10000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 1 / 5000000
  valueLower := 44239 / 1000000
  valueUpper := 44351 / 1000000
  firstLower := 138636 / 1000000
  firstUpper := 138707 / 1000000
  secondLower := -86529 / 1000000
  secondUpper := -43187 / 500000

theorem plusOne_checked : plusOne.check = true := by
  norm_num [plusOne, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusOne_reduction :
    |(((plusOne.q : ℝ) - (2 : ℝ) * Real.pi) -
      (plusOneTrig.center : ℝ))| ≤ (plusOneTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusOne, plusOneTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusOne_sin :
    |Real.sin (plusOne.q : ℝ) - (plusOne.sinApprox : ℝ)| ≤
      (plusOne.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusOneTrig)
    (by norm_num [plusOneTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusOne.q : ℝ)) plusOne_reduction
  simpa [plusOne, plusOneTrig, reducedCenter,
    TranscendentalBounds.sinTaylor7] using h

private theorem plusOne_cos :
    |Real.cos (plusOne.q : ℝ) - (plusOne.cosApprox : ℝ)| ≤
      (plusOne.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusOneTrig)
    (by norm_num [plusOneTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusOne.q : ℝ)) plusOne_reduction
  simpa [plusOne, plusOneTrig, reducedCenter,
    TranscendentalBounds.cosTaylor8] using h

theorem plusOne_sound {y : ℝ}
    (hy : |y - (65788877 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((44239 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 44351 / 1000000) ∧
    ((138636 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 138707 / 1000000) ∧
    ((-86529 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -43187 / 500000) := by
  have hy' : |y - (plusOne.q : ℝ)| ≤ (plusOne.radius : ℝ) := by
    simpa [plusOne] using hy
  simpa [plusOne] using plusOne.sound plusOne_checked plusOne_sin plusOne_cos hy'

private def plusTwoTrig : RationalTrigCell.Witness :=
  ⟨3, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=2` plus argument, centered at `9.7204804`. -/
def plusTwo : SincJetCertificate.Witness where
  q := 24301201 / 2500000
  radius := 1 / 2500
  upper := 24302201 / 2500000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := -30019 / 1000000
  valueUpper := -29939 / 1000000
  firstLower := -47674 / 500000
  firstUpper := -19061 / 200000
  secondLower := 49543 / 1000000
  secondUpper := 49643 / 1000000

theorem plusTwo_checked : plusTwo.check = true := by
  norm_num [plusTwo, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusTwo_reduction :
    |(((plusTwo.q : ℝ) - (3 : ℝ) * Real.pi) -
      (plusTwoTrig.center : ℝ))| ≤ (plusTwoTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusTwo, plusTwoTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusTwo_sin :
    |Real.sin (plusTwo.q : ℝ) - (plusTwo.sinApprox : ℝ)| ≤
      (plusTwo.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusTwoTrig)
    (by norm_num [plusTwoTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusTwo.q : ℝ)) plusTwo_reduction
  rw [show |Real.sin (plusTwo.q : ℝ) - (plusTwo.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ plusTwoTrig.k) * Real.sin (plusTwo.q : ℝ) -
        TranscendentalBounds.sinTaylor7 (plusTwoTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusTwoTrig.k) = -1 by norm_num [plusTwoTrig]]
    norm_num [plusTwo, plusTwoTrig, reducedCenter,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem plusTwo_cos :
    |Real.cos (plusTwo.q : ℝ) - (plusTwo.cosApprox : ℝ)| ≤
      (plusTwo.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusTwoTrig)
    (by norm_num [plusTwoTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusTwo.q : ℝ)) plusTwo_reduction
  rw [show |Real.cos (plusTwo.q : ℝ) - (plusTwo.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ plusTwoTrig.k) * Real.cos (plusTwo.q : ℝ) -
        TranscendentalBounds.cosTaylor8 (plusTwoTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusTwoTrig.k) = -1 by norm_num [plusTwoTrig]]
    norm_num [plusTwo, plusTwoTrig, reducedCenter,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem plusTwo_sound {y : ℝ}
    (hy : |y - (24301201 / 2500000 : ℝ)| ≤ 1 / 2500) :
    ((-30019 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -29939 / 1000000) ∧
    ((-47674 / 500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -19061 / 200000) ∧
    ((49543 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 49643 / 1000000) := by
  have hy' : |y - (plusTwo.q : ℝ)| ≤ (plusTwo.radius : ℝ) := by
    simpa [plusTwo] using hy
  simpa [plusTwo] using plusTwo.sound plusTwo_checked plusTwo_sin plusTwo_cos hy'

private def plusThreeTrig : RationalTrigCell.Witness :=
  ⟨4, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=3` plus argument, centered at `12.862073`. -/
def plusThree : SincJetCertificate.Witness where
  q := 12862073 / 1000000
  radius := 1 / 2500
  upper := 12862473 / 1000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 3 / 10000000
  valueLower := 22627 / 1000000
  valueUpper := 11343 / 500000
  firstLower := 36299 / 500000
  firstUpper := 36313 / 500000
  secondLower := -16991 / 500000
  secondUpper := -33913 / 1000000

theorem plusThree_checked : plusThree.check = true := by
  norm_num [plusThree, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusThree_reduction :
    |(((plusThree.q : ℝ) - (4 : ℝ) * Real.pi) -
      (plusThreeTrig.center : ℝ))| ≤ (plusThreeTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusThree, plusThreeTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusThree_sin :
    |Real.sin (plusThree.q : ℝ) - (plusThree.sinApprox : ℝ)| ≤
      (plusThree.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusThreeTrig)
    (by norm_num [plusThreeTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusThree.q : ℝ)) plusThree_reduction
  rw [show ((-1 : ℝ) ^ plusThreeTrig.k) = 1 by norm_num [plusThreeTrig]] at h
  simpa [plusThree, plusThreeTrig, reducedCenter,
    TranscendentalBounds.sinTaylor7] using h

private theorem plusThree_cos :
    |Real.cos (plusThree.q : ℝ) - (plusThree.cosApprox : ℝ)| ≤
      (plusThree.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusThreeTrig)
    (by norm_num [plusThreeTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusThree.q : ℝ)) plusThree_reduction
  rw [show ((-1 : ℝ) ^ plusThreeTrig.k) = 1 by norm_num [plusThreeTrig]] at h
  simpa [plusThree, plusThreeTrig, reducedCenter,
    TranscendentalBounds.cosTaylor8] using h

theorem plusThree_sound {y : ℝ}
    (hy : |y - (12862073 / 1000000 : ℝ)| ≤ 1 / 2500) :
    ((22627 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 11343 / 500000) ∧
    ((36299 / 500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 36313 / 500000) ∧
    ((-16991 / 500000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -33913 / 1000000) := by
  have hy' : |y - (plusThree.q : ℝ)| ≤ (plusThree.radius : ℝ) := by
    simpa [plusThree] using hy
  simpa [plusThree] using plusThree.sound plusThree_checked
    plusThree_sin plusThree_cos hy'

private def plusFourTrig : RationalTrigCell.Witness :=
  ⟨5, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=4` plus argument, centered at `16.0036657`. -/
def plusFour : SincJetCertificate.Witness where
  q := 160036657 / 10000000
  radius := 1 / 2500
  upper := 160040657 / 10000000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := -9117 / 500000
  valueUpper := -2273 / 125000
  firstLower := -7331 / 125000
  firstUpper := -3664 / 62500
  secondLower := 6377 / 250000
  secondUpper := 12783 / 500000

theorem plusFour_checked : plusFour.check = true := by
  norm_num [plusFour, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusFour_reduction :
    |(((plusFour.q : ℝ) - (5 : ℝ) * Real.pi) -
      (plusFourTrig.center : ℝ))| ≤ (plusFourTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusFour, plusFourTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusFour_sin :
    |Real.sin (plusFour.q : ℝ) - (plusFour.sinApprox : ℝ)| ≤
      (plusFour.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusFourTrig)
    (by norm_num [plusFourTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusFour.q : ℝ)) plusFour_reduction
  rw [show |Real.sin (plusFour.q : ℝ) - (plusFour.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ plusFourTrig.k) * Real.sin (plusFour.q : ℝ) -
        TranscendentalBounds.sinTaylor7 (plusFourTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusFourTrig.k) = -1 by norm_num [plusFourTrig]]
    norm_num [plusFour, plusFourTrig, reducedCenter,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem plusFour_cos :
    |Real.cos (plusFour.q : ℝ) - (plusFour.cosApprox : ℝ)| ≤
      (plusFour.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusFourTrig)
    (by norm_num [plusFourTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusFour.q : ℝ)) plusFour_reduction
  rw [show |Real.cos (plusFour.q : ℝ) - (plusFour.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ plusFourTrig.k) * Real.cos (plusFour.q : ℝ) -
        TranscendentalBounds.cosTaylor8 (plusFourTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusFourTrig.k) = -1 by norm_num [plusFourTrig]]
    norm_num [plusFour, plusFourTrig, reducedCenter,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem plusFour_sound {y : ℝ}
    (hy : |y - (160036657 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((-9117 / 500000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -2273 / 125000) ∧
    ((-7331 / 125000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -3664 / 62500) ∧
    ((6377 / 250000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 12783 / 500000) := by
  have hy' : |y - (plusFour.q : ℝ)| ≤ (plusFour.radius : ℝ) := by
    simpa [plusFour] using hy
  simpa [plusFour] using plusFour.sound plusFour_checked
    plusFour_sin plusFour_cos hy'

private def plusFiveTrig : RationalTrigCell.Witness :=
  ⟨6, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=5` plus argument, centered at `19.1452583`. -/
def plusFive : SincJetCertificate.Witness where
  q := 191452583 / 10000000
  radius := 1 / 2500
  upper := 191456583 / 10000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 3 / 10000000
  valueLower := 15201 / 1000000
  valueUpper := 15241 / 1000000
  firstLower := 24581 / 500000
  firstUpper := 49179 / 1000000
  secondLower := -20381 / 1000000
  secondUpper := -10167 / 500000

theorem plusFive_checked : plusFive.check = true := by
  norm_num [plusFive, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusFive_reduction :
    |(((plusFive.q : ℝ) - (6 : ℝ) * Real.pi) -
      (plusFiveTrig.center : ℝ))| ≤ (plusFiveTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusFive, plusFiveTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusFive_sin :
    |Real.sin (plusFive.q : ℝ) - (plusFive.sinApprox : ℝ)| ≤
      (plusFive.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusFiveTrig)
    (by norm_num [plusFiveTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusFive.q : ℝ)) plusFive_reduction
  rw [show ((-1 : ℝ) ^ plusFiveTrig.k) = 1 by norm_num [plusFiveTrig]] at h
  simpa [plusFive, plusFiveTrig, reducedCenter,
    TranscendentalBounds.sinTaylor7] using h

private theorem plusFive_cos :
    |Real.cos (plusFive.q : ℝ) - (plusFive.cosApprox : ℝ)| ≤
      (plusFive.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusFiveTrig)
    (by norm_num [plusFiveTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusFive.q : ℝ)) plusFive_reduction
  rw [show ((-1 : ℝ) ^ plusFiveTrig.k) = 1 by norm_num [plusFiveTrig]] at h
  simpa [plusFive, plusFiveTrig, reducedCenter,
    TranscendentalBounds.cosTaylor8] using h

theorem plusFive_sound {y : ℝ}
    (hy : |y - (191452583 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((15201 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 15241 / 1000000) ∧
    ((24581 / 500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 49179 / 1000000) ∧
    ((-20381 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -10167 / 500000) := by
  have hy' : |y - (plusFive.q : ℝ)| ≤ (plusFive.radius : ℝ) := by
    simpa [plusFive] using hy
  simpa [plusFive] using plusFive.sound plusFive_checked
    plusFive_sin plusFive_cos hy'

private def plusSixTrig : RationalTrigCell.Witness :=
  ⟨7, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=6` plus argument, centered at `22.286851`. -/
def plusSix : SincJetCertificate.Witness where
  q := 22286851 / 1000000
  radius := 1 / 2500
  upper := 22287251 / 1000000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := -13093 / 1000000
  valueUpper := -6529 / 500000
  firstLower := -42343 / 1000000
  firstUpper := -5291 / 125000
  secondLower := 3371 / 200000
  secondUpper := 8447 / 500000

theorem plusSix_checked : plusSix.check = true := by
  norm_num [plusSix, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusSix_reduction :
    |(((plusSix.q : ℝ) - (7 : ℝ) * Real.pi) -
      (plusSixTrig.center : ℝ))| ≤ (plusSixTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusSix, plusSixTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusSix_sin :
    |Real.sin (plusSix.q : ℝ) - (plusSix.sinApprox : ℝ)| ≤
      (plusSix.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusSixTrig)
    (by norm_num [plusSixTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusSix.q : ℝ)) plusSix_reduction
  rw [show |Real.sin (plusSix.q : ℝ) - (plusSix.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ plusSixTrig.k) * Real.sin (plusSix.q : ℝ) -
        TranscendentalBounds.sinTaylor7 (plusSixTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusSixTrig.k) = -1 by norm_num [plusSixTrig]]
    norm_num [plusSix, plusSixTrig, reducedCenter,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem plusSix_cos :
    |Real.cos (plusSix.q : ℝ) - (plusSix.cosApprox : ℝ)| ≤
      (plusSix.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusSixTrig)
    (by norm_num [plusSixTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusSix.q : ℝ)) plusSix_reduction
  rw [show |Real.cos (plusSix.q : ℝ) - (plusSix.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ plusSixTrig.k) * Real.cos (plusSix.q : ℝ) -
        TranscendentalBounds.cosTaylor8 (plusSixTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusSixTrig.k) = -1 by norm_num [plusSixTrig]]
    norm_num [plusSix, plusSixTrig, reducedCenter,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem plusSix_sound {y : ℝ}
    (hy : |y - (22286851 / 1000000 : ℝ)| ≤ 1 / 2500) :
    ((-13093 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -6529 / 500000) ∧
    ((-42343 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -5291 / 125000) ∧
    ((3371 / 200000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 8447 / 500000) := by
  have hy' : |y - (plusSix.q : ℝ)| ≤ (plusSix.radius : ℝ) := by
    simpa [plusSix] using hy
  simpa [plusSix] using plusSix.sound plusSix_checked
    plusSix_sin plusSix_cos hy'

private lemma sincD1_neg (x : ℝ) : sincD1 (-x) = -sincD1 x := by
  simp only [sincD1, Real.cos_neg, Real.sin_neg]
  ring

private lemma sincD2_neg (x : ℝ) : sincD2 (-x) = sincD2 x := by
  simp only [sincD2, secondNumerator, Real.cos_neg, Real.sin_neg]
  ring

/-- The actual `j=1` minus argument is the negative of the delicate reduced
cell.  Parity turns the reusable positive-row certificate into its semantic
production enclosure. -/
theorem minusOne_sound {y : ℝ}
    (hy : |y - (-184814 / 625000 : ℝ)| ≤ 1 / 2500) :
    ((98545 / 100000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 985531 / 1000000) ∧
    ((243935 / 2500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 97843 / 1000000) ∧
    ((-327341 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -40241 / 125000) := by
  have hy' : |-y - (184814 / 625000 : ℝ)| ≤ 1 / 2500 := by
    rw [show -y - (184814 / 625000 : ℝ) =
      -(y - (-184814 / 625000 : ℝ)) by ring, abs_neg]
    exact hy
  have h := SincJetCertificate.productionReducedWitness_sound hy'
  simp only [Real.sinc_neg, sincD1_neg, sincD2_neg] at h
  exact ⟨h.1, ⟨by linarith [h.2.1.2], by linarith [h.2.1.1]⟩, h.2.2⟩

end Zeta23Ext.ProductionCell4376Jets

end
