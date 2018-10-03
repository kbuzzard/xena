/- 5. (longer and a little harder.) Let X and Y be sets, and let f : X → Y be a function. Let’s completely take this function apart.
(i)Define a binary relation on X by a∼b if and only if f(a)=f(b). Check that ∼ is an equivalence relation.
(ii) Now say x ∈ X and f(x) = y. Check that the equivalence class cl(x) of x is f−1(y), which means {z ∈ X : f(z) = y}.
(iii) Let Z be the set of equivalence classes for this equivalence relation (so Z is a set of sets 
– each element of Z is a certain subset of X). Let’s define a map g : Z → Y in the following way: 
if W ∈ Z then by definition W is non-empty (as W = cl(x) for some x and hence x ∈ W); 
choose w ∈ W and define g(W) = f(w). This definition is a bit dodgy because we chose an element of W 
and our definition seemed to depend on that choice. Prove that actually g is well-defined, 
in the sense that whichever element of W we chose, our definition of g(W) will not depend on this choice.
In particular g is a well-defined function.
(iv) Prove that g is injective (i.e., one-to-one).
(v) Define h : X → Z by h(x) = cl(x). Prove that h is surjective.
(vi) Prove that f = g ◦ h. In particular, this gives another proof that an arbitrary function is
a surjection followed by an injection.
(vii) Let J be the image of f, so J is a subset of Y . Write down a natural bijection i from J
to Z.
(viii) Let h ̃ denote the map X → J induced by f (by which I mean h ̃(x) = f(x) ∈ J) and let g ̃
denote the inclusion J → Y . Prove that h = i ◦ h ̃ and g ̃ = g ◦ i. You just proved that the following diagram commutes:-/