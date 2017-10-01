/-
M1F 2017-18 Sheet 1 Question 1
Author : Kevin Buzzard

Note: this version of the question uses rational numbers instead of real numbers.

TODO (KMB) : Replace topology.real with more user-friendly real numbers.
           : figure out how to use x^2 instead of x*x
           : figure out how to make 3 mean 3:R rather than 3:nat
           : remove some of those stupid brackets round the 3:R's somehow.
           : This is actually the 2016-17 example sheet question; update later.
-/

import topology.real

open real

theorem m1f_sheet01_q01 : ¬ (∀ x : ℝ,(x*x-(3:ℝ)*x+(2:ℝ)=(0:ℝ) → x=(1:ℝ))) := sorry
