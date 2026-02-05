import Lookup.Spec.vecfunc

namespace Lookup
universe u
variable {F : Type u} [Field F]

/-- The “inverse constraint polynomial” for a table function `t` and witness `z`:
    G(x) = (α - t(x)) * z(x) - 1.
    If z(x) = (α - t(x))⁻¹ on the Boolean cube, then G(x)=0 on the cube. -/
def invConstraint (n : ℕ) (α : F) (t z : func F n) : func F n :=
  fun xs => (α - t xs) * (z xs) - 1

/-- The “difference” polynomial for the sum-of-inverses fingerprint:
    D(x) = zT(x) - zB(x). -/
def invDiff (n : ℕ) (zT zB : func F n) : func F n :=
  fun xs => zT xs - zB xs

end Lookup
