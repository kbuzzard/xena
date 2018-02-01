import data.nat.basic
open nat
/- A teacher gives a non-negative integer m to student A,
   and a non-negative integer n to their opponent, student B.
   The teacher then writes two non-negative integers on the
   board -- one is m+n, and the other is not.

   The teacher then asks the students in turn, again and
   again, if they know the other student's number.

   Prove that at some point one of the students will say "yes".
-/

/- definition of the function which keeps track of everything.
   Let's say that a "round" involves the teacher first asking student A
   and then student B if they know their opponent's number.
   The function takes as input the number of rounds d,
   the students' numbers a and b, and the number c on the board
   which is not a+b.

   The output of the function is a pair consisting of two functions
   from the naturals to {true,false}. The first element of the pair
   is what A knows, the second element is what B knows.
-/
def knowledge : ℕ → ℕ → ℕ → ℕ → (ℕ → Prop) × (ℕ → Prop) 
-- d,a,b,c to <f,g>.

-- After 0 rounds all they know is that their number plus their opponents number is either c or a+b.
| 0 a b c := (λ bb:ℕ, bb = b ∨ a + bb = c,
              λ aa:ℕ, aa = a ∨ aa + b = c)
-- Assuming both students say "I don't know" on round (d+1), 
-- each student knows everything they knew in the previous round, and also that the other student
-- didn't have enough information.
| (succ d) a b c := (λ bb, (knowledge d a b c).1 bb ∧ 
    ¬ (∀ bbb : ℕ, (knowledge d a b c).2 bbb → bbb = b),λ aa, (knowledge d a b c).2 aa ∧ ¬ (∀ aaa, (knowledge d a b c).1 aaa → aaa = a))
/-

    -- bb is used to represent the unknown value of b, b is the actual value
    -- the below two lines mean that brown eyed islanders know whether or not anyone left the previous day.
    -- The first line isn't really necessary, 
    -- since if any brown eyed islanders left, they would have already deduced that brown eyed islanders should leave.
    ((∀ c:ℕ, (island_rules d i b).1 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).1 c → c = bb)) ∧  
    ((∀ c:ℕ, (island_rules d i b).2 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).2 c → c = bb)),
    -- strictly there may be other things that should be added here, but none of them change the result
    λ bb, (island_rules d i b).2 bb ∧ 
    ((∀ c:ℕ, (island_rules d i b).1 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).1 c → c = bb)) ∧  
    ((∀ c:ℕ, (island_rules d i b).2 c → c = b) ↔ (∀ c:ℕ, (island_rules d i bb).2 c → c = bb)))

theorem init_island_1 {d i b bb:ℕ} : (island_rules d i b).2 bb → (b = bb ∨ b - 1 = bb) ∧ bb ≥ 1:=begin
    induction d,simp[island_rules] at *,intros,exact ⟨a,a_1⟩,
    simp [island_rules],intros,exact d_ih a,
end
-/
theorem Cris_numbers_question : ∀ a b c, c ≠ a + b → ∀ d, let ⟨Afacts,Bfacts⟩ := knowledge a b c d in Afacts b b  

