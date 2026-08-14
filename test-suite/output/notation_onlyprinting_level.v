(* rocq#12465: an "only printing" notation contributes no parsing rule, so its
   level need not agree with the level attached to the notation key.  The
   discrepancy is reported by the notation-incompatible-level warning, and the
   printing rule is used with its own level. *)

Declare Scope test_bool_scope.
Notation "x == y" := (Nat.eqb x y) (at level 70, no associativity) : test_bool_scope.
Notation "x != y" := (negb (Nat.eqb x y)) (at level 70, no associativity) : test_bool_scope.

(* Shaped like VST's floyd/Clightnotations.v. *)
Declare Scope test_expr_scope.
Notation "a1 == a2" := (andb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17,
   format "'[' a1  ==  a2 ']'") : test_expr_scope.
Notation "a1 != a2" := (orb a1 a2)
  (only printing, a2 at level 16, left associativity, at level 17,
   format "'[' a1  !=  a2 ']'") : test_expr_scope.

(* Parsing still uses the level 70 rule. *)
Open Scope test_bool_scope.
Check (0 == 1).
Check (0 == 1 + 1).

(* Printing uses the "only printing" rule, at its own level 17 with its own
   argument levels: left associative, so the left argument needs no
   parentheses whereas the right one does. *)
Open Scope test_expr_scope.
Check (andb true false).
Check (orb (andb true false) (andb true false)).
