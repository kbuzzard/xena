import data.complex.basic 

definition has_coe_NZ : has_coe ℕ ℤ := by apply_instance
definition has_coe_NQ : has_coe ℕ ℚ := by apply_instance 
definition has_coe_NR : has_coe ℕ ℝ := by apply_instance 
definition has_coe_NC : has_coe ℕ ℂ := by apply_instance 
definition has_coe_ZQ : has_coe ℤ ℚ := by apply_instance 
definition has_coe_ZR : has_coe ℤ ℝ := by apply_instance
definition has_coe_ZC : has_coe ℤ ℂ := by apply_instance
-- definition has_coe_QR : has_coe ℚ ℝ := by apply_instance -- fails
noncomputable definition has_coe_QR : has_coe ℚ ℝ := by apply_instance
-- definition has_coe_QC : has_coe ℚ ℂ := by apply_instance -- fails
noncomputable definition has_coe_QC : has_coe ℚ ℂ := by apply_instance
definition has_coe_RC : has_coe ℝ ℂ := by apply_instance 

definition coe_NZ : ℕ → ℤ := has_coe_NZ.coe
definition coe_NQ : ℕ → ℚ := has_coe_NQ.coe 
definition coe_NR : ℕ → ℝ := has_coe_NR.coe 
definition coe_NC : ℕ → ℂ := has_coe_NC.coe 
definition coe_ZQ : ℤ → ℚ := has_coe_ZQ.coe 
definition coe_ZR : ℤ → ℝ := has_coe_ZR.coe
definition coe_ZC : ℤ → ℂ := has_coe_ZC.coe 
noncomputable definition coe_QR : ℚ → ℝ := has_coe_QR.coe
noncomputable definition coe_QC : ℚ → ℂ := has_coe_QC.coe 
definition coe_RC : ℝ → ℂ := has_coe_RC.coe 

-- The ten theorems below are what I would like to access easily in Lean.
-- I don't know what to call them; the current names are just placeholders.

-- N to Z is never a problem
theorem NZQ (x : ℕ) : coe_ZQ (coe_NZ x) = coe_NQ x := rfl 
theorem NZR (x : ℕ) : coe_ZR (coe_NZ x) = coe_NR x := rfl
theorem NZC (x : ℕ) : coe_ZC (coe_NZ x) = coe_NC x := rfl

-- the problems start now
theorem ZQR (x : ℤ) : coe_QR (coe_ZQ x) = coe_ZR x := sorry -- simp fails
theorem QRC (x : ℚ) : coe_RC (coe_QR x) = coe_QC x := sorry -- simp fails
theorem ZRC (x : ℤ) : coe_RC (coe_ZR x) = coe_ZC x := sorry -- simp fails

theorem NQR (x : ℕ) : coe_QR (coe_NQ x) = coe_NR x := by rw [←NZQ,ZQR,←NZR]
theorem ZQC (x : ℤ) : coe_QC (coe_ZQ x) = coe_ZC x := by rw [←QRC,←ZRC,←ZQR]
theorem NQC (x : ℕ) : coe_QC (coe_NQ x) = coe_NC x := by rw [←NZC,←NZQ,←ZQC]
theorem NRC (x : ℕ) : coe_RC (coe_NR x) = coe_NC x := by rw [←NQC,←QRC,←NQR]

-- cool stuff my stuents constantly want to be able to do 
example (x : ℤ) : ((x : ℚ) : ℝ) = x := ZQR x 
example (x : ℤ) : let (y : ℚ) := ↑x in let (z : ℝ) := ↑y in z = ↑x := ZQR x 

-- Gabriel's answer
example (x : ℤ) : ((x : ℚ) : ℝ) = x := by simp

