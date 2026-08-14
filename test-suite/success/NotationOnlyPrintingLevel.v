(* "only printing" notations add no parsing rule, hence no grammar level for
   their key: declaring one at a level incompatible with an existing rule for
   the same key must be accepted (rocq#12465, rocq#12589, rocq#6078).

   This is the situation of VST's floyd/Clightnotations.v, which declares
   "only printing" notations for "_ == _" and "_ != _" at C level 17, while
   ssreflect declares parsing notations for the same keys at level 70. Before
   the fix only one import order was accepted, and the ecosystem had to
   mandate it. *)

(* The declarations below are legal but the discrepancy is reported. *)
Set Warnings "-notation-incompatible-level".

(* Order A: the parsing rule comes first. This used to be an error. *)
Module ParsingFirst.
  Declare Scope test_bool_scope.
  Notation "x == y" := (Nat.eqb x y) (at level 70, no associativity) : test_bool_scope.
  Notation "x != y" := (negb (Nat.eqb x y)) (at level 70, no associativity) : test_bool_scope.

  Declare Scope test_expr_scope.
  Notation "a1 == a2" := (andb a1 a2)
    (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope.
  Notation "a1 != a2" := (orb a1 a2)
    (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope.

  (* The parsing rule is the one at level 70 and it is unaffected. *)
  Open Scope test_bool_scope.
  Check (0 == 1).
  Check (0 == 1 + 1).
End ParsingFirst.

(* Order B: the "only printing" rule comes first. *)
Module OnlyPrintingFirst.
  Declare Scope test_expr_scope.
  Notation "a1 == a2" := (andb a1 a2)
    (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope.
  Notation "a1 != a2" := (orb a1 a2)
    (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope.

  Declare Scope test_bool_scope.
  Notation "x == y" := (Nat.eqb x y) (at level 70, no associativity) : test_bool_scope.
  Notation "x != y" := (negb (Nat.eqb x y)) (at level 70, no associativity) : test_bool_scope.

  (* The "only printing" declaration must not have leaked its argument levels
     into the parsing rule declared afterwards: "1 + 1" is at level 50, which
     would not be accepted by an argument constrained at level 16. *)
  Open Scope test_bool_scope.
  Check (0 == 1).
  Check (0 == 1 + 1).
End OnlyPrintingFirst.

(* Same, against a reserved (hence parsing) notation. *)
Module WithReservedNotation.
  Reserved Notation "x =? y" (at level 70, no associativity).
  Declare Scope test_expr_scope2.
  Notation "a1 =? a2" := (andb a1 a2)
    (only printing, a2 at level 16, left associativity, at level 17) : test_expr_scope2.
  Notation "x =? y" := (Nat.eqb x y) : nat_scope.
  Check (0 =? 1).
End WithReservedNotation.

(* Same, with a reserved "only printing" notation. *)
Module WithReservedOnlyPrintingNotation.
  Reserved Notation "x <?> y" (at level 70, no associativity).
  Reserved Notation "x <?> y" (only printing, at level 17, left associativity, y at level 16).
  Notation "x <?> y" := (Nat.eqb x y) : nat_scope.
  Check (0 <?> 1).
End WithReservedOnlyPrintingNotation.

(* Same, through Infix. *)
Module WithInfix.
  Declare Scope test_infix_scope.
  Infix "===" := Nat.eqb (at level 70, no associativity) : test_infix_scope.
  Declare Scope test_infix_expr_scope.
  Infix "===" := andb (only printing, at level 17, left associativity) : test_infix_expr_scope.
  Open Scope test_infix_scope.
  Check (0 === 1).
  Open Scope test_infix_expr_scope.
  Check (andb true false).
End WithInfix.

(* Same, inside a custom entry. *)
Module WithCustomEntry.
  Declare Custom Entry test_entry.
  Notation "[ x ]" := x (in custom test_entry at level 0, x constr at level 0).
  Notation "x <+> y" := (Nat.add x y) (in custom test_entry at level 70, no associativity).
  Declare Scope test_custom_scope.
  Notation "x <+> y" := (Nat.mul x y)
    (in custom test_entry at level 17, only printing, left associativity, y at level 16)
    : test_custom_scope.
  Notation "<{ e }>" := e (e custom test_entry at level 200).
  Check <{ [0] <+> [1] }>.
End WithCustomEntry.

(* Two parsing rules for the same key at incompatible levels remain an error. *)
Module ParsingVsParsingStillFails.
  Declare Scope test_a_scope.
  Notation "x <=> y" := (Nat.eqb x y) (at level 70, no associativity) : test_a_scope.
  Declare Scope test_b_scope.
  Fail Notation "x <=> y" := (andb x y)
    (y at level 16, left associativity, at level 17) : test_b_scope.
  (* ... and also when declared "only parsing". *)
  Fail Notation "x <=> y" := (andb x y)
    (only parsing, y at level 16, left associativity, at level 17) : test_b_scope.
End ParsingVsParsingStillFails.
