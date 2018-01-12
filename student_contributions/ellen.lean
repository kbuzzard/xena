import algebra.big_operators data.set.finite

definition matrix (R: Type) (n m : nat)[ring R] :=  fin n →( fin m → R ) 
 
 namespace matrix 

definition add ( R : Type) [ring R] {n m: nat }(A:matrix R m n) ( B : matrix R m n): (matrix R m n):= 
λ I J, A I J + B I J
--begin
--unfold matrix,
--intros I J,
--exact A I J + B I J
--end

definition neg ( R : Type) [ring R] {n m: nat } (A:matrix R m n) : (matrix R m n):= 
λ I J, -A I J

definition zero (R : Type) [ring R] {n m : nat} : matrix R m n :=
λ I J, 0

theorem add_assoc1 ( R : Type) [ring R] {m n: nat }(A:matrix R m n) ( B : matrix R m n) ( C : matrix R m n) :
 add R A (add R  B C) = add R (add R A B) C :=
begin
apply funext,
intro,
apply funext,
intro y,
unfold add,
rw [add_assoc],
end

theorem add_assoc2 ( R : Type) [ring R] {m n: nat }(A:matrix R m n) ( B : matrix R m n) ( C : matrix R m n) :
 add R (add R A B) C = add R A (add R  B C)  :=
begin
apply funext,
intro,
apply funext,
intro y,
show  ( A x y + B x y) + C x y = A x y + (B x y + C x y) ,
rw[add_assoc],
end

theorem zero_add   ( R : Type) [ring R] {m n: nat }(A:matrix R m n):
add R (zero R) A = A:=
begin
apply funext,
intro,
apply funext,
intro y,
show 0 + A x y = A x y,
rw[zero_add]
end

theorem add_zero (R : Type) [ring R] {m n: nat }(A:matrix R m n):
add R A (zero R) = A:=
begin
apply funext,
intro,
apply funext,
intro y,
show  A x y + 0 = A x y,
rw[add_zero]
end


theorem add_left_neg (R : Type) [ring R] {m n: nat }(A:matrix R m n) :
add R ( neg R A) A = zero R := 
begin
apply funext,
intro,
apply funext,
intro y,
show  - A x y + A x y = 0 ,
rw[add_left_neg]
end


theorem add_comm (R : Type) [ring R] {m n: nat }(A:matrix R m n)( B : matrix R m n):
add R A B = add R B A :=
begin
apply funext,
intro,
apply funext,
intro y,
show  A x y + B x y = B x y + A x y ,
rw [add_comm]
end


instance add_comm_group ( R : Type) [ring R] {m n: nat }: add_comm_group (matrix R m n):={
add:= matrix.add R ,
add_assoc := @matrix.add_assoc2 R _ m n,
zero := matrix.zero R ,
neg := matrix.neg R,
zero_add := @matrix.zero_add R _ m n,
add_zero := @matrix.add_zero R _ m n,
add_left_neg := @matrix.add_left_neg R _ m n,
add_comm := @matrix.add_comm R _ m n
}
end matrix

definition mul ( R : Type) [ring R] {n m l: nat }(A:matrix R m n) ( B : matrix R n l): (matrix R m l ):=
λ I J, finset.sum finset.univ (λ K, A I K * B K J)

theorem mul_assoc' (R : Type) [ring R] {m n l o : nat} (A : matrix R m n) (B : matrix R n l) (C : matrix R l o) :
mul R A (mul R B C) = mul R (mul R A B) C :=
begin
unfold mul,
apply funext,
intro x,
apply funext,
intro y,

-- This next line just rewrites the goal so that the variables we're summing over 
-- are the same on both sides.

show finset.sum finset.univ (λ (K : fin n), A x K * finset.sum finset.univ (λ (J : fin l), B K J * C J y)) =
     finset.sum finset.univ (λ (J : fin l), finset.sum finset.univ (λ (K : fin n), A x K * B K J) * C J y),

-- So the key things we now need to use are:

-- finset.mul_sum (which says c * sum_n a_n = sum_n (c*a_n))
-- finset.sum_mul (which says the same but multiplication on the right)
-- and finset.sum_comm (which says that two finite sums can be commuted).

-- However, rw finset.sum_mul doesn't work
-- and neither does rw finset.mul_sum,
-- and until we apply these we can't commute the sums.
-- I think the reasons they don't work are that C J y, which we need to move, depends on J,
-- which is not one of our variables.

-- So here's a trick. We prove an intermediate lemma which says we can
-- move C J y into the sum, by checking the things we're summing over are the same.

have H2 : (λ (J : fin l), finset.sum finset.univ (λ (K : fin n), A x K * B K J) * C J y)
        = (λ (J : fin l), finset.sum finset.univ (λ (K : fin n), A x K * B K J * C J y)),
{ apply funext,
  intro J,
  exact finset.sum_mul,
},

-- Now we can commute the sums after using this lemma.

rw [H2],
clear H2,
rw [finset.sum_comm],

-- Now I just rewrite the goal to show that both things are a sum over K in fin n.

show finset.sum finset.univ (λ (K : fin n), A x K * finset.sum finset.univ (λ (K_1 : fin l), B K K_1 * C K_1 y)) =
    finset.sum finset.univ (λ (K : fin n), finset.sum finset.univ (λ (x_1 : fin l), A x K * B K x_1 * C x_1 y)),

-- Now we can cancel the first sum and it's all downhill from here.

apply congr_arg _,
apply funext,
intro z,
rw finset.mul_sum, -- c*sum a_n = sum c*a_n

apply congr_arg,
apply funext,

intro w,
rw mul_assoc,
end

