(* -*- coq-prog-args: ("-async-proofs" "on" "-async-proofs-delegation-threshold" "0"); -*- *)

(* Each proof below is checked by a worker process, which receives the
   state the proof starts from by marshalling and so loses the
   declaration hook of the command that opened it. The worker must
   still check the proof, and the master must still run the hook. *)

Require Import Setoid.

Class C := { c : nat }.

#[export] Instance foo : C.
Proof. exact {| c := 0 |}. Qed.

(* Only typechecks if the master registered [foo] as an instance. *)
Definition x : C := _.

Parameter A : Type.
Parameter R : A -> A -> Prop.
Axiom R_equiv : Equivalence R.
#[export] Existing Instance R_equiv.
Parameter f : A -> A.
Axiom f_R : forall a b, R a b -> R (f a) (f b).

Add Morphism f with signature R ==> R as f_morph.
Proof. exact f_R. Qed.

(* Defined, so that the master checks it: [rewrite] needs the
   [Proper] instance declared by the hook of [Add Morphism]. *)
Lemma use_f_morph a b : R a b -> R (f a) (f b).
Proof. intros H. rewrite H. reflexivity. Defined.
