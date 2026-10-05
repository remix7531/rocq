(* Declaration hooks and proof endings are kept behind CEphemeron keys,
   which lose their value when marshalled. Saving a proof that went
   through Marshal must fail loudly rather than declare the constant
   without running its hook or its proof ending. See rocq#22564. *)

open Utest

let log_out_ch = open_log_out_ch __FILE__

let () =
  Declaremods.start_library (Names.DirPath.make [Names.Id.of_string "MarshalledHooks"])

let round_trip (x : 'a) : 'a = Marshal.from_string (Marshal.to_string x []) 0

(* forall A : Prop, A -> A *)
let identity_type =
  let open EConstr in
  let a = Context.make_annot (Names.Name (Names.Id.of_string "A")) ERelevance.relevant in
  let x = Context.make_annot Names.Anonymous ERelevance.relevant in
  mkProd (a, mkProp, mkProd (x, mkRel 1, mkRel 2))

let solve proof =
  let tac = Proofview.tclTHEN Tactics.intros Tactics.assumption in
  fst (Declare.Proof.by (Global.env ()) tac proof)

let start ?hook name =
  let sigma = Evd.from_env (Global.env ()) in
  let info = Declare.Info.make ?hook () in
  let cinfo = Declare.CInfo.make ~name:(Names.Id.of_string name) ~typ:identity_type () in
  solve (Declare.Proof.start ~info ~cinfo sigma)

(* A proof with an [End_equations] ending, whose hook sets [ran] *)
let start_equations ran name =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, ev =
    Evarutil.new_pure_evar ~relevance:EConstr.ERelevance.relevant
      (Environ.named_context_val env) sigma identity_type
  in
  let types = [env, ev, Evd.find_undefined sigma ev, [], identity_type] in
  let hook ~pm _ _ = ran := true; pm in
  let goals = Proofview.TCons (env, sigma, identity_type, fun sigma _ -> Proofview.TNil sigma) in
  let info = Declare.Info.make () in
  solve (Declare.Proof.start_equations ~name:(Names.Id.of_string name) ~info ~hook ~types sigma goals)

let save proof =
  snd (Declare.Proof.save ~pm:Declare.OblState.empty ~proof ~opaque:Vernacexpr.Transparent ~idopt:None)

let outcome f =
  match f () with
  | _ -> "saved"
  | exception e ->
    let msg = Pp.string_of_ppcmds (CErrors.print e) in
    if CErrors.is_sync_anomaly e && CString.string_contains ~where:msg ~what:"marshalled"
    then "anomaly"
    else "other error: " ^ msg

let assert_outcome expected f =
  OUnit.assert_equal ~msg:"outcome of save" ~printer:(fun s -> s) expected (outcome f)

let t_live_hook = mk_test "marshalled-hooks-live" (OUnit.TestCase (fun () ->
    let ran = ref false in
    let proof = start ~hook:(Declare.Hook.make (fun _ -> ran := true)) "live_hooked" in
    assert_outcome "saved" (fun () -> save proof);
    OUnit.assert_bool "saving a live proof runs its hook" !ran))

let t_marshalled_hook = mk_test "marshalled-hooks-lost" (OUnit.TestCase (fun () ->
    let ran = ref false in
    let proof = start ~hook:(Declare.Hook.make (fun _ -> ran := true)) "marshalled_hooked" in
    let proof = round_trip proof in
    assert_outcome "anomaly" (fun () -> save proof);
    OUnit.assert_bool "the lost hook did not run" (not !ran)))

let t_marshalled_plain = mk_test "marshalled-hooks-plain" (OUnit.TestCase (fun () ->
    let proof = round_trip (start "marshalled_plain") in
    assert_outcome "saved" (fun () -> save proof)))

let t_live_equations = mk_test "marshalled-hooks-equations-live" (OUnit.TestCase (fun () ->
    let ran = ref false in
    let proof = start_equations ran "live_equations" in
    assert_outcome "saved" (fun () -> save proof);
    OUnit.assert_bool "saving a live proof runs its proof ending" !ran))

let t_marshalled_equations = mk_test "marshalled-hooks-equations-lost" (OUnit.TestCase (fun () ->
    let ran = ref false in
    let proof = round_trip (start_equations ran "marshalled_equations") in
    assert_outcome "anomaly" (fun () -> save proof);
    OUnit.assert_bool "the lost proof ending did not run" (not !ran)))

let tests =
  [ t_live_hook; t_marshalled_hook; t_marshalled_plain; t_live_equations; t_marshalled_equations ]

let _ = run_tests __FILE__ log_out_ch tests
