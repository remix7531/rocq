(* [Declare.Proof.is_portable] and [Vernacstate.is_portable] tell
   whether a proof, or every proof open in a state, survives
   marshalling: no declaration hook and a regular proof ending. *)

open Utest

let log_out_ch = open_log_out_ch __FILE__

let () =
  Declaremods.start_library (Names.DirPath.make [Names.Id.of_string "IsPortable"])

(* forall A : Prop, A -> A *)
let identity_type =
  let open EConstr in
  let a = Context.make_annot (Names.Name (Names.Id.of_string "A")) ERelevance.relevant in
  let x = Context.make_annot Names.Anonymous ERelevance.relevant in
  mkProd (a, mkProp, mkProd (x, mkRel 1, mkRel 2))

let start ?hook name =
  let sigma = Evd.from_env (Global.env ()) in
  let info = Declare.Info.make ?hook () in
  let cinfo = Declare.CInfo.make ~name:(Names.Id.of_string name) ~typ:identity_type () in
  Declare.Proof.start ~info ~cinfo sigma

let start_equations name =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, ev =
    Evarutil.new_pure_evar ~relevance:EConstr.ERelevance.relevant
      (Environ.named_context_val env) sigma identity_type
  in
  let types = [env, ev, Evd.find_undefined sigma ev, [], identity_type] in
  let hook ~pm _ _ = pm in
  let goals = Proofview.TCons (env, sigma, identity_type, fun sigma _ -> Proofview.TNil sigma) in
  let info = Declare.Info.make () in
  Declare.Proof.start_equations ~name:(Names.Id.of_string name) ~info ~hook ~types sigma goals

let hook = Declare.Hook.make (fun _ -> ())

let with_lemmas (st : Vernacstate.t) lemmas =
  { st with interp = { st.interp with lemmas } }

let t_proofs =
  mk_test "is-portable-proofs" (OUnit.TestCase (fun () ->
      OUnit.assert_bool "a plain proof is portable"
        (Declare.Proof.is_portable (start "plain"));
      OUnit.assert_bool "a proof with a hook is not portable"
        (not (Declare.Proof.is_portable (start ~hook "hooked")));
      OUnit.assert_bool "a proof with a non-regular ending is not portable"
        (not (Declare.Proof.is_portable (start_equations "equations")))))

let t_states =
  mk_test "is-portable-states" (OUnit.TestCase (fun () ->
      let st = Vernacstate.freeze_full_state () in
      let plain = Vernacstate.LemmaStack.push None (start "plain") in
      let hooked = Vernacstate.LemmaStack.push None (start ~hook "hooked") in
      let plain_on_hooked = Vernacstate.LemmaStack.push (Some hooked) (start "plain_on_hooked") in
      OUnit.assert_bool "a state with no open proof is portable"
        (Vernacstate.is_portable st);
      OUnit.assert_bool "a state with a plain proof open is portable"
        (Vernacstate.is_portable (with_lemmas st (Some plain)));
      OUnit.assert_bool "a state with a hooked proof open is not portable"
        (not (Vernacstate.is_portable (with_lemmas st (Some hooked))));
      OUnit.assert_bool "a hooked proof below the top makes the state not portable"
        (not (Vernacstate.is_portable (with_lemmas st (Some plain_on_hooked))))))

let tests = [ t_proofs; t_states ]

let _ = run_tests __FILE__ log_out_ch tests
