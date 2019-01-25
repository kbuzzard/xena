example (P Q : Prop) (HP : P) (HPQ : P → Q) : Q := HPQ HP -- HPQ is a function!
example (P Q : Prop) (HP : P) (HnP : ¬P) : false := HnP HP -- So is HnP
