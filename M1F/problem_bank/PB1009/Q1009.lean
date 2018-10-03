import data.equiv.denumerable data.set.basic data.real.irrational data.complex.basic
/- 8. 
(i) Prove that if X is a countably infinite set, and Y ⊆ X is an infinite subset, then Y is countably infinite. 
(ii) Are there countably many irrational numbers? Countably many complex numbers? What about Q(i)={a+bi : a,b∈Q}?
-/
variable {α : Type*}
variables {X : set α} {Y : set X}

theorem Q1009i (hp : denumerable X) : denumerable Y := sorry

def Q_R : set ℝ := {x : ℝ | irrational x}

--def new : set ℂ := {a : ℂ | a.1 ∈ ℚ ∧ a.2 : ℚ}

theorem Q1009ii : denumerable Q_R → ff := sorry

theorem Q1009iia : denumerable ℂ := sorry

-- theorem Q1009iib : 