namespace xena

inductive xnat
| zero : xnat
| succ : xnat → xnat

open xnat 

definition add : xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)

notation a + b := add a b 

definition one := succ zero
definition two := succ one 
definition three := succ two 
definition four := succ three

example : two + two = four :=
begin
dunfold two, -- goal now succ one + succ one = four
admit,
end 
