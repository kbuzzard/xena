import analysis.real
variable x : real
set_option pp.all true
example : x < (x+1) :=
begin
unfold has_lt.lt,
unfold preorder.lt,
unfold partial_order.lt,
unfold ordered_comm_monoid.lt,
unfold discrete_linear_ordered_field.lt,
unfold has_lt.lt,
unfold preorder.lt,
unfold partial_order.lt,
unfold lattice.semilattice_inf.lt,
unfold lattice.lattice.lt,
unfold lattice.distrib_lattice.lt,
unfold lattice.lattice.lt,
unfold decidable_linear_order.lt,
unfold decidable_linear_ordered_comm_group.lt,
unfold has_lt.lt,
unfold preorder.lt,
unfold partial_order.lt,
unfold linear_order.lt,
admit
end

example : x ≤ x := 
begin
-- is there a cute way to switch goals?
unfold has_le.le,
unfold has_mem.mem,
unfold set.mem,
unfold nonneg,
unfold closure,
unfold set.sInter,
unfold lattice.Inf,
unfold lattice.has_Inf.Inf,
unfold lattice.complete_lattice.Inf,
unfold set_of,
intro t,
unfold has_mem.mem,
unfold set.mem,
intro,
admit
end
