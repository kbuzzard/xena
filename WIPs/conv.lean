# Conv #

example (m a b c d e f : ℤ) :
m * e * m * f + a * m * f + m * e * c + a * c - a * c = m * m * e * f + m * e * c + m * f * a
:= begin
suffices : m * e * c + (a * m * f + m * e * m * f) = m * e * c + (m * f * a + m * m * e * f),
by simp [this],
conv in (a * m * f) {
rw mul_comm,
rw ←mul_assoc,
rw mul_comm,
rw ←mul_assoc,
},
conv in (m * e * m * f) {
rw mul_assoc m e m,
rw mul_comm e m,
rw ← mul_assoc m m e,
},
end
