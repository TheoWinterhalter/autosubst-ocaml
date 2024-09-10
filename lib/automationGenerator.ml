(* open Coqgen *)
open Util
open VernacGen
open GallinaGen
open AutomationGen
open TacGen
open ClassGen
open NotationGen
open Termutil
open RSEM.Syntax
open RSEM

module AM = AutosubstModules

let gen_auto_unfold () =
  let* auto_unfold_functions = gets auto_unfold_functions in
  let tac = repeat_ (unfold_ auto_unfold_functions) in
  pure @@ TacticLtac ("auto_unfold", tac)

let gen_auto_unfold_star' () =
  let* auto_unfold_functions = gets auto_unfold_functions in
  pure @@ repeat_ (unfold_ ~locus_clause:star_locus_clause auto_unfold_functions)

let gen_auto_unfold_star () =
  let* auf = gen_auto_unfold_star' () in
  pure @@ TacticNotation ([ "\"auto_unfold\""; "\"in\""; "\"*\"" ], auf)

let gen_asimpl_fext' () =
  let* info = get in
  let asimpl_rewrite_fext = info.asimpl_rewrite_fext in
  let asimpl_rewrite_base = info.asimpl_rewrite_base in
  let asimpl_cbn_functions = info.asimpl_cbn_functions in
  let asimpl_unfold_functions = info.asimpl_unfold_functions in
  let rewrites = List.map (fun t -> progress_ (rewrite_ t)) (asimpl_rewrite_base @ asimpl_rewrite_fext) in
  let tac = repeat_ (first_ (rewrites @
                             [ progress_ (unfold_ asimpl_unfold_functions)
                             ; progress_ (cbn_ asimpl_cbn_functions)
                             ; calltac_ "fsimpl_fext" ])) in
  pure @@ TacticLtac ("asimpl_fext'", tac)

let gen_asimpl' () =
  let* info = get in
  let asimpl_rewrite_no_fext = info.asimpl_rewrite_no_fext in
  let asimpl_rewrite_base = info.asimpl_rewrite_base in
  let asimpl_cbn_functions = info.asimpl_cbn_functions in
  let asimpl_unfold_functions = info.asimpl_unfold_functions in
  let rewrites = List.(concat (map (fun t -> [ progress_ (setoid_rewrite_ t) ]) (asimpl_rewrite_base @ asimpl_rewrite_no_fext))) in
  let tac = repeat_ (first_ (rewrites @
                             [ progress_ (unfold_ asimpl_unfold_functions)
                             ; progress_ (cbn_ asimpl_cbn_functions)
                             ; progress_ (calltac_ "fsimpl")
                              ])) in
  pure @@ TacticLtac ("asimpl'", tac)

(*
let gen_asimpl_star () =
  let* info = get in
  let asimpl_rewrite_lemmas = info.asimpl_rewrite_lemmas in
  let asimpl_cbn_functions = info.asimpl_cbn_functions in
  let asimpl_unfold_functions = info.asimpl_unfold_functions in
  let* auto_unfold_star = gen_auto_unfold_star' () in
  let rewrites = List.map (fun t -> progress_ (rewrite_ ~locus_clause:star_locus_clause t)) asimpl_rewrite_lemmas in
  let tac = then1_ auto_unfold_star
      (repeat_ (first_ (rewrites @
                        [ progress_ (unfold_ ~locus_clause:star_locus_clause asimpl_unfold_functions)
                        ; progress_ (cbn_ ~locus_clause:star_locus_clause asimpl_cbn_functions)
                        ; calltac_ "fsimpl" ]))) in
  pure @@ TacticNotation ([ "\"asimpl\""; "\"in\""; "\"*\"" ], tac)
*)

let gen_asimpl_fext () =
  let* auto_unfold_star = gen_auto_unfold_star' () in
  let unfold_funcomp = repeat_ (try_ (calltac_ "unfold_funcomp")) in
  let tac = then_ [ calltac_ "check_no_evars"
                  ; unfold_funcomp
                  ; auto_unfold_star
                  ; calltac_ "asimpl_fext'"
                  ; unfold_funcomp ] in
  pure @@ TacticLtac ("asimpl_fext", tac)

let gen_asimpl () =
  let* auto_unfold_star = gen_auto_unfold_star' () in
  (* let unfold_funcomp = repeat_ (try_ (calltac_ "unfold_funcomp")) in *)
  let tac = then_ [ calltac_ "check_no_evars"
                  (* ; unfold_funcomp *)
                  ; auto_unfold_star
                  ; calltac_ "asimpl'"
                  ; calltac_ "minimize" ] in
  pure @@ TacticLtac ("asimpl", tac)

let gen_asimpl_fext_hyp () =
  let tac = then_ [ calltacArgs_ "revert" [ "J" ]
                  ; calltac_ "asimpl_fext"
                  ; intros_ [ "J" ] ] in
  pure @@  TacticNotation ([ "\"asimpl_fext\""; "\"in\""; "hyp(J)" ], tac)

let gen_asimpl_hyp () =
  let tac = then_ [ calltacArgs_ "revert" [ "J" ]
                  ; calltac_ "asimpl"
                  ; intros_ [ "J" ] ] in
  pure @@  TacticNotation ([ "\"asimpl\""; "\"in\""; "hyp(J)" ], tac)

let gen_auto_case_fext () =
  let inner_tac = then_ [ calltac_ "asimpl_fext"
                        ; cbn_ []
                        ; calltac_ "eauto" ] in
  let tac = calltacTac_ "auto_case" inner_tac in
  pure @@ TacticNotation ([ "\"auto_case_fext\"" ], tac)

let gen_auto_case () =
  let inner_tac = then_ [ calltac_ "asimpl"
                        ; cbn_ []
                        ; calltac_ "eauto" ] in
  let tac = calltacTac_ "auto_case" inner_tac in
  pure @@ TacticNotation ([ "\"auto_case\"" ], tac)

let gen_substify_fext () =
  let* substify_lemmas = gets substify_lemmas_fext in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("substify_fext", tac)

let gen_substify () =
  let* substify_lemmas = gets substify_lemmas in
  let rewrites = List.map (fun t -> try_ (setoid_rewrite_ t)) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("substify", tac)

let gen_renamify_fext () =
  let* substify_lemmas = gets substify_lemmas_fext in
  let rewrites = List.map (fun t -> try_ (repeat_ (rewrite_ ~with_evars:true ~to_left:true t))) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("renamify_fext", tac)

let gen_renamify () =
  let* substify_lemmas = gets substify_lemmas in
  let rewrites = List.map (fun t -> try_ (setoid_rewrite_ ~to_left:true t)) substify_lemmas in
  let tac = then_ (calltac_ "auto_unfold" :: rewrites) in
  pure @@ TacticLtac ("renamify", tac)

let gen_arguments () =
  let* arguments = gets arguments in
  if Settings.is_wellscoped () then
    pure @@ List.filter_map (fun (name, args) ->
        if list_empty args then None
        else Some (impl_arguments_ name args))
      arguments
  else pure []

let gen_opaques () =
  let* ops = gets asimpl_cbn_functions in
  let* version = ask_coq_version in
  pure (List.map (setoid_opaque_hint version) ops)

let gen_classes () =
  let* classes = gets classes in
  let gen_class (inst_type, sort) =
    let open GallinaGen in
    let binders = [ binder_ [ "X"; "Y" ] ] in
    let ctors = [ constructor_ (class_field sort inst_type)
                    (arr1_ (ref_ "X") (ref_ "Y")) ] in
    class_ (class_name sort inst_type) binders ctors in
  pure @@ List.map gen_class classes

let gen_proper_instances () =
  let* proper_instances = gets proper_instances in
  (** We generate two morphisms for each instantiation.
      subst_tm_morphism : pointwise_relation _ eq ==> eq ==> eq
      subst_tm_morphism2 : pointwise_relation _ eq ==> pointwise_relation _ eq
  *)
  let gen_instances (sort, fun_sort, ext_sort) =
    let* v = Variables.genVariables sort [ `MS; `NS ] in
    let [@warning "-8"] [], [ ms; ns ], [], scopeBinders = v in
    let* substSorts = get_substv sort in
    let iname = sep (fun_sort) "morphism" in
    let iname2 = sep (fun_sort) "morphism2" in
    let signature = List.fold_right (fun _ signature ->
        app_ref "respectful" [ app_ref "pointwise_relation" [ underscore_; ref_ "eq" ]
                             ; signature ])
        substSorts (app_ref "respectful" [ ref_ "eq"; ref_ "eq" ]) in
    let signature2 = List.fold_right (fun _ signature ->
        app_ref "respectful" [ app_ref "pointwise_relation" [ underscore_; ref_ "eq" ]
                              ; signature ])
        substSorts (app_ref "pointwise_relation" [ underscore_; ref_ "eq" ]) in
    let itype = app_ref "Proper" [ signature; app_fix ~expl:true (fun_sort) ~sscopes:[ ms; ns ] [] ] in
    let itype2 = app_ref "Proper" [ signature2; app_fix ~expl:true (fun_sort) ~sscopes:[ ms; ns ] [] ] in
    (* a.d. TODO right now this is the easiest way to generate all the names. all the other functions like genRen are too generalized and we can't use the binders they return. So we generate them again fresh *)
    let fs = mk_refs @@ List.map (sep "f") substSorts in
    let gs = mk_refs @@ List.map (sep "g") substSorts in
    let eqs = mk_refs @@ List.map (sep "Eq") substSorts in
    let s = varName "s" in
    let t = varName "t" in
    let eq_st = varName "Eq_st" in
    let proof_binders = binder_ (List.fold_right (fun substSort binders ->
        [ sep "f" substSort; sep "g" substSort; sep "Eq" substSort ] @ binders)
        substSorts [ s; t; eq_st ]) in
    let proof_binders2 = binder_ (List.fold_right (fun substSort binders ->
        [ sep "f" substSort; sep "g" substSort; sep "Eq" substSort ] @ binders)
        substSorts [ s ]) in
    let proof = lambda_ [ proof_binders ]
        (app_ref "eq_ind" [ ref_ s
                          ; abs_ref "t'" (eq_ (app_ref fun_sort (fs @ [ ref_ s])) (app_ref fun_sort (gs @ [ ref_ "t'" ])))
                          ; app_ref ext_sort (fs @ gs @ eqs @ [ ref_ s ])
                          ; ref_ t
                          ; ref_ eq_st ]) in
    let proof2 = lambda_ [ proof_binders2 ]
        (app_ref ext_sort (fs @ gs @ eqs @ [ ref_ s ])) in
    pure @@ [
      instance_ iname scopeBinders itype ~interactive:true proof;
      instance_ iname2 scopeBinders itype2 ~interactive:true proof2
    ]
  in
  a_concat_map gen_instances proper_instances

let gen_instances () =
  let* instances = gets instances in
  (* the instances created here should also be unfolded *)
  let register_instance_unfolds (inst_type, sort, _) =
    let unfolds = instance_unfolds sort inst_type in
    let* info = get in
    put { info with auto_unfold_functions = unfolds @ info.auto_unfold_functions }
  in
  let gen_instance inst_type sort params =
    let iname = instance_name sort inst_type in
    let cname = class_name sort inst_type in
    let fname = function_name sort inst_type in
    let cbinders = guard (Settings.is_wellscoped ()) [ binder_ ~implicit:true ~btype:(ref_ "nat") params ] in
    let args = guard (Settings.is_wellscoped ()) (List.map ref_ params) in
    instance_ iname cbinders (app_ref cname (class_args inst_type)) (app_ref ~expl:true fname args)
  in
  (* TODO better way to chain actions? *)
  let* _ = sequence (List.map register_instance_unfolds instances) in
  let instance_definitions = List.(concat (map (fun (inst_type, sort, params) -> [ gen_instance inst_type sort params ]) instances)) in
  pure instance_definitions

let gen_notations () =
  let* notations = gets notations in
  let gen_notation (ntype, sort) =
    notation_ (notation_string sort ntype) (notation_modifiers sort ntype) ~scope:(notation_scope ntype) (notation_body sort ntype) in
  pure @@ List.map gen_notation notations

(** Definitions for the rasimpl tactic **)

let quoted_ren_ =
  ref_ "quoted_ren"

let gen_quoted_subst_body na =
  let* substs = get_substv na in
  let rens = List.map (fun _ -> quoted_ren_) substs in
  let substs = List.map (fun id -> ref_ ("quoted_subst_" ^ id)) substs in
  let qna = "quoted_subst_" ^ na in
  let ctors = [
    constructor_ ("qsubst_atom_" ^ na) (arr1_ (arr1_ nat_ (ref_ na)) (ref_ qna)) ;
    constructor_ ("qsubst_comp_" ^ na) (arr_ (substs @ [ ref_ qna ]) (ref_ qna)) ;
    constructor_ ("qsubst_compr_" ^ na) (arr_ [ ref_ qna ; quoted_ren_ ] (ref_ qna)) ;
    constructor_ ("qsubst_rcomp_" ^ na) (arr_ (rens @ [ ref_ qna ]) (ref_ qna)) ;
    constructor_ ("qsubst_cons_" ^ na) (arr_ [ ref_ ("quoted_" ^ na) ; ref_ qna ] (ref_ qna)) ;
    constructor_ ("qsubst_id_" ^ na) (ref_ qna) ;
    constructor_ ("qsubst_ren_" ^ na) (arr1_ quoted_ren_ (ref_ qna))
  ] in
  pure @@ inductiveBody_ qna [] ctors

let gen_quoted_body na =
  let* substs = get_substv na in
  let rens = List.map (fun _ -> quoted_ren_) substs in
  let substs = List.map (fun id -> ref_ ("quoted_subst_" ^ id)) substs in
  let qna = "quoted_" ^ na in
  let ctors = [
    constructor_ ("qatom_" ^ na) (arr1_ (ref_ na) (ref_ qna)) ;
    constructor_ ("qren_" ^ na) (arr_ (rens @ [ ref_ qna ]) (ref_ qna)) ;
    constructor_ ("qsubst_" ^ na) (arr_ (substs @ [ ref_ qna ]) (ref_ qna))
  ] in
  pure @@ inductiveBody_ qna [] ctors

let gen_quotes_comp component =
  let* open_component = a_filter check_open component in
  let* qs_bodies = a_map gen_quoted_subst_body open_component in
  let* q_bodies = a_map gen_quoted_body component in
  pure @@ inductive_ (qs_bodies @ q_bodies)

(* TODO

  It's not always needed to generate quoted_subst if there is no corresponding
  substitutions. How to solve this issue?

*)
let gen_quotes () =
  let* components = get_components in
  let* qs_inds = a_map gen_quotes_comp components in
  pure qs_inds

(* TODO MOVE *)
let funcomp_ f g =
  app_ref "funcomp" [f ; g]

let subst_ s =
  ref_ ("subst_" ^ s)

let ren_ s =
  ref_ ("ren_" ^ s)

let unquote_ na t =
  app_ref ("unquote_" ^ na) [ t ]

let unquote_ren_ r =
  app_ref "unquote_ren" [ r ]

let unquote_subst_ s t =
  app_ref ("unquote_subst_" ^ s) [ t ]

let gen_unquote_subst na =
  let* substs = get_substv na in
  let rargs = List.map (fun id -> "r_" ^ id) substs in
  let urargs = List.map (fun id -> unquote_ren_ (ref_ ("r_" ^ id))) substs in
  let args = List.map (fun id -> "s_" ^ id) substs in
  let uargs = List.map (fun id -> unquote_subst_ id (ref_ ("s_" ^ id))) substs in
  let var_na = ref_ (CoqNames.var_ na) in
  let binders = [
    binder1_ ~btype:(ref_ ("quoted_subst_" ^ na)) "q"
  ] in
  let body = match_ (ref_ "q") [
    branch_ ("qsubst_atom_" ^ na) [ "s" ] (ref_ "s") ;
    branch_ ("qsubst_comp_" ^ na) (args @ [ "t" ]) (funcomp_ (app_ (subst_ na) uargs) (unquote_subst_ na (ref_ "t"))) ;
    branch_ ("qsubst_compr_" ^ na) [ "s" ; "r" ] (funcomp_ (unquote_subst_ na (ref_ "s")) (unquote_ren_ (ref_ "r"))) ;
    branch_ ("qsubst_rcomp_" ^ na) (rargs @ [ "s" ]) (funcomp_ (app_ (ren_ na) urargs) (unquote_subst_ na (ref_ "s"))) ;
    branch_ ("qsubst_cons_" ^ na) [ "t" ; "s" ] (app_ cons_ [ unquote_ na (ref_ "t") ; unquote_subst_ na (ref_ "s") ]) ;
    branch_ ("qsubst_id_" ^ na) [] var_na ;
    branch_ ("qsubst_ren_" ^ na) [ "r" ] (funcomp_ var_na (unquote_ren_ (ref_ "r"))) ;
  ] in
  pure @@ fixpointBody_ ("unquote_subst_" ^ na) binders (arr1_ nat_ (ref_ na)) body "q"

let gen_unquote na =
  let binders = [
    binder1_ ~btype:(ref_ ("quoted_" ^ na)) "q"
  ] in
  let* substs = get_substv na in
  let rargs = List.map (fun id -> "r_" ^ id) substs in
  let urargs = List.map (fun id -> unquote_ren_ (ref_ ("r_" ^ id))) substs in
  let args = List.map (fun id -> "s_" ^ id) substs in
  let sargs = List.map (fun id -> unquote_subst_ id (ref_ ("s_" ^ id))) substs in
  let body = match_ (ref_ "q") [
    branch_ ("qatom_" ^ na) [ "t" ] (ref_ "t") ;
    branch_ ("qren_" ^ na) (rargs @ [ "t" ]) (app_ (ren_ na) (urargs @ [ unquote_ na (ref_ "t") ])) ;
    branch_ ("qsubst_" ^ na) (args @ [ "t" ]) (app_ (subst_ na) (sargs @ [ unquote_ na (ref_ "t") ]))
  ] in
  pure @@ fixpointBody_ ("unquote_" ^ na) binders (ref_ na) body "q"

let gen_unquotes_comp component =
  let* open_component = a_filter check_open component in
  let* s_bodies = a_map gen_unquote_subst open_component in
  let* u_bodies = a_map gen_unquote component in
  pure @@ fixpoint_ ~is_rec:true (s_bodies @ u_bodies)

let gen_unquotes () =
  let* components = get_components in
  let* defs = a_map gen_unquotes_comp components in
  pure defs

let gen_eval_subst na =
  let* substs = get_substv na in
  let rargs = List.map (fun id -> "r_" ^ id) substs in
  let urargs = List.map (fun id -> unquote_ren_ (ref_ ("r_" ^ id))) substs in
  let args = List.map (fun id -> "s_" ^ id) substs in
  let uargs = List.map (fun id -> unquote_subst_ id (ref_ ("s_" ^ id))) substs in
  let var_na = ref_ (CoqNames.var_ na) in
  let binders = [
    binder1_ ~btype:(ref_ ("quoted_subst_" ^ na)) "q"
  ] in
  let body = match_ (ref_ "q") [
    branch_ ("qsubst_comp_" ^ na) (args @ [ "t" ]) (ref_ "_") ;
    branch_ ("qsubst_compr_" ^ na) [ "s" ; "r" ] (ref_ "_") ;
    branch_ ("qsubst_rcomp_" ^ na) (rargs @ [ "s" ]) (ref_ "_") ;
    branch_ ("qsubst_cons_" ^ na) [ "t" ; "s" ] (ref_ "_") ;
    branch_ ("qsubst_ren_" ^ na) [ "r" ] (ref_ "_") ;
    branch_ "_" [] (ref_ "q") ;
  ] in
  pure @@ fixpointBody_ ("eval_subst_" ^ na) binders (arr1_ nat_ (ref_ na)) body "q"

let rec lets l t =
  match l with
  | [] -> t
  | (n,b) :: l -> let_ n b None @@ lets l t

let gen_eval_ na =
  let binders = [
    binder1_ ~btype:(ref_ ("quoted_" ^ na)) "q"
  ] in
  let* substs = get_substv na in
  let rargs = List.map (fun id -> "r_" ^ id) substs in
  let eval_rs = List.map (fun id -> (id, app_ref "eval_ren" [ ref_ id ])) rargs in
  let args = List.map (fun id -> "s_" ^ id) substs in
  let sargs = List.map (fun id -> unquote_subst_ id (ref_ ("s_" ^ id))) substs in
  let body = match_ (ref_ "q") [
    branch_ ("qren_" ^ na) (rargs @ [ "t" ]) (
      lets eval_rs @@
      let_ "t" (app_ref ("eval_" ^ na) [ ref_ "t" ]) None @@
      ref_ "_"
    ) ;
    branch_ ("qsubst_" ^ na) (args @ [ "t" ]) (ref_ "_") ;
    branch_ "_" [] (ref_ "q") ;
  ] in
  pure @@ fixpointBody_ ("eval_" ^ na) binders (ref_ na) body "q"

let gen_eval_comp component =
  let* open_component = a_filter check_open component in
  let* s_bodies = a_map gen_eval_subst open_component in
  let* bodies = a_map gen_eval_ component in
  pure @@ fixpoint_ ~is_rec:true (s_bodies @ bodies)

let gen_eval () =
  let* components = get_components in
  let* defs = a_map gen_eval_comp components in
  pure defs

(* TODO
  I build it by hand, maybe it would be better using combinators but I don't
  know which one to use.
*)
let gen_rasimpl () =
  let* q = gen_quotes () in
  let* u = gen_unquotes () in
  let* e = gen_eval () in
  pure (q @ u @ e)

let generate () =
  let* arguments = gen_arguments () in
  let* opaques = gen_opaques () in
  let* classes = gen_classes () in
  let* instances = gen_instances () in
  let* notations = gen_notations () in
  let* proper_instances = gen_proper_instances () in
  let tactic_funs = [
    gen_auto_unfold ;
    gen_auto_unfold_star ;
    gen_asimpl' ;
    gen_asimpl ;
    gen_asimpl_hyp ;
    gen_auto_case ;
    gen_substify ;
    gen_renamify
  ] in
  let tactic_fext_funs = [
    gen_asimpl_fext' ;
    gen_asimpl_fext ;
    gen_asimpl_fext_hyp ;
    gen_auto_case_fext ;
    gen_substify_fext ;
    gen_renamify_fext
  ] in
  let* tactics = a_map (fun f -> f ()) tactic_funs in
  let* tactics_fext = a_map (fun f -> f ()) tactic_fext_funs in
  let* is_gen_fext = ask_gen_fext in
  let* rasimpl = gen_rasimpl () in
  pure AM.(from_list [
    (Core, classes @ instances @ notations @ proper_instances @ tactics @ rasimpl) ;
    (Fext, guard is_gen_fext tactics_fext) ;
    (Extra, arguments @ opaques)
  ])
