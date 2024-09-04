(** Most of the genX functions in this module follow the same pattern.
 **  - declare some scope/renaming/substitution variables and their binders
 **  - build the type of the statement
 **  - build the proof term of the statement
 **
 ** Fixpoints call traversal which generates the match on the principal argument.
 ** Definitions and Lemmas directly call the smart constructor with the type, binders and proof.
 ** *)
open Util

module L = Language
module V = Variables

open ScopeTypes
open Tactics
open CoqNames
open GallinaGen
open VernacGen
module AM = AutosubstModules
open Termutil
open AutomationGen
open RSEM.Syntax
open RSEM

(** We define modules that contain our code generator functions. *)

(** UP_GENERATOR generates the lifting code for a whole up_list. *)
module type UP_GENERATOR = sig
  val gen : (L.binder * L.tId) list -> AM.t RSEM.t
end

(** COMPONENT_GENERATOR generates code for a whole component. *)
module type COMPONENT_GENERATOR = sig
  val gen : L.tId list -> AM.t RSEM.t
end

(** INDUCTIVE_GENERATOR also generates code for a whole component. *)
module type INDUCTIVE_GENERATOR = COMPONENT_GENERATOR

(** A LIFTING_GENERATOR generates lemmas for a single lifting combination. *)
module type LIFTING_GENERATOR = sig
  val gen : (L.binder * L.tId) -> AM.t RSEM.t
end

(** A FIXPOINT_BODY_GENERATOR generates one body of a fixpoint. *)
module type FIXPOINT_BODY_GENERATOR = sig
  (* when a component is a non-empty list we can return the tag from gen, but for now we just specify it in the module itself. *)
  val tag : AM.module_tag
  val gen : L.tId -> fixpoint_expr RSEM.t
end

(** A LEMMA_GENERATOR generates lemmas for a single sort. *)
module type LEMMA_GENERATOR = sig
  val gen : L.tId -> AM.t RSEM.t
end

(** Wrapping modules that generate fixpoint bodies to generate a complete fixpoint. *)
module FixGen (FBGen : FIXPOINT_BODY_GENERATOR) : COMPONENT_GENERATOR = struct
  let gen component =
    let* is_rec = check_recursive component in
    let* bodies = a_map FBGen.gen component in
    pure @@ AM.add_units FBGen.tag [fixpoint_ ~is_rec bodies]
end
(** Wrapping modules that generate one lifting to generate all liftings for an up_list. *)
module LiftGen (LGen : LIFTING_GENERATOR) : UP_GENERATOR = struct
  let gen up_list =
    let* liftings = a_map LGen.gen up_list in
    pure @@ AM.concat liftings
end
(** Wrapping modules that generate lemmas to generate all lemmas for a component. *)
module LemGen (LGen : LEMMA_GENERATOR) : COMPONENT_GENERATOR = struct
  let gen component =
    let* lemmas = a_map LGen.gen component in
    pure @@ AM.concat lemmas
end


module Inductives : INDUCTIVE_GENERATOR = struct
  let genVarConstr sort ns =
    (* register variable constructor instance *)
    let* () = tell_instance (ClassGen.Var, sort, ss_names ns) in
    let* () = tell_notation (NotationGen.VarConstr, sort) in
    let* () = tell_notation (NotationGen.VarInst, sort) in
    let* () = tell_notation (NotationGen.Var, sort) in
    let* () = tell_argument (var_ sort, ss_names ns) in
    let* s = gen_var_arg sort ns in
    let t = [s] ==> app_sort sort ns in
    pure @@ constructor_ (var_ sort) t


  let genConstr sort ns L.{ cparameters; cname; cpositions } =
    let* t =
      let* up_n_x = a_map (fun L.{ binders; head } -> genArg sort ns binders head) cpositions in
      pure @@ (up_n_x ==> app_sort sort ns) in
    let* () = tell_argument (cname, ss_names ns) in
    pure @@ constructor_ cname (if list_empty cparameters then t else forall_ (createBinders cparameters) t)


  let gen_inductive_body sort =
    let* ctors = get_constructors sort in
    let* (ns, bns) = genScopeVarVect ~implicit:false "n" sort in
    let* is_open = check_open sort in
    let* ctors = a_map (genConstr sort ns) ctors in
    let* ctors = if is_open
      then let* varCtor = genVarConstr sort ns in
        pure (varCtor :: ctors)
      else pure ctors
    in
    pure @@ inductiveBody_ sort bns ~rtype:type_ ctors

  (** Generate a mutual inductive type spanning the given definable sorts *)
  let gen def_sorts =
    match def_sorts with
    | [] -> pure (AM.empty)
    | l ->
      let* bodies = a_map gen_inductive_body def_sorts in
      pure (AM.(add_units Core [inductive_ bodies]))
end

module Congruences : COMPONENT_GENERATOR = struct
  (** the proof term is just n-1 eq_trans and n ap's where n is the length of cpositions.
   ** The pattern is that with each f_equal we swap out one s_n for one t_n
   ** and the eq_trans chain all those together
   ** e.g. C s0 s1 s2 = C t0 s1 s2 = C t0 t1 s2 = C t0 t1 t2 *)
  let genCongruence sort L.{ cparameters; cname; cpositions } =
    let* (ms, bms) = genScopeVarVect "m" sort in
    let ss = getPattern "s" cpositions in
    let ts = getPattern "t" cpositions in
    let hs = getPattern "H" cpositions in
    let mkBinders xs = a_map2 (fun x L.{binders; head} ->
        let* arg_type = genArg sort ms binders head in
        pure @@ binder1_ ~implicit:true ~btype:arg_type x)
        xs cpositions in
    let* bss = mkBinders ss in
    let* bts = mkBinders ts in
    (* todo rename parameters *)
    let bparameters = createImpBinders cparameters in
    let parameters' = List.(mk_refs (map fst cparameters)) in
    let ss = mk_refs ss in
    let ts = mk_refs ts in
    let eqs = List.map2 eq_ ss ts in
    let beqs = List.map2 (fun h ty -> binder1_ ~btype:ty h) hs eqs in
    let eq = eq_
        (app_constr cname ms (parameters' @ ss))
        (app_constr cname ms (parameters' @ ts)) in
    let x = varName "x" in
    let (_, proof') = List.fold_left (fun (i, t) h ->
        let feq_args = list_take ts i @ [ref_ x] @ (list_drop ss (i + 1)) in
        let feq_lam = abs_ref "x" (app_constr cname ms (parameters' @ feq_args)) in
        let feq = ap_ feq_lam (ref_ h) in
        (i + 1, eqTrans_ t feq))
        (0, eq_refl_) hs in
    pure @@ AM.(add_units Core [lemma_ (congr_ cname) (bparameters @ bms @ bss @ bts @ beqs) eq proof'])


  let gen component =
    let* congruences = a_concat_map (fun sort ->
        let* ctors = get_constructors sort in
        a_map (genCongruence sort) ctors)
        component in
    pure @@ AM.concat congruences
end

(** Constructs the body of a fixpoint.
 **
 ** no_args: used when an argument of a constructor does not have a substitution vector. E.g. ty in stlc does not have a substitution vector.
 ** sem: used to calculate the branch of a non-variable constructor. Most lemmas use the constructor's congruence lemma in the head position but other things like the subsitution operation use other terms in head position *)
let traversal
    s sort nameF ?(no_args=fun s -> app1_ eq_refl_ s) args
    var_case_body ?(sem=fun _ cname positions -> app_fix (congr_ cname) positions) funsem =
  let open L in
  let* substSorts = get_substv sort in
  (* the underscore pattern is used when constructing the branches to ignore the scope variables. Could also construct a dummy SusbtScope instead of matching the scope_type *)
  let underscore_pattern = List.map (const "_") (match !S.scope_type with | S.Unscoped -> [] | S.Wellscoped -> substSorts) in
  let* ctors = get_constructors sort in
  let* is_open = check_open sort in
  (* Only create the variable branch if the sort is open *)
  let* var_pattern = m_guard is_open (
      let s0 = "s0" in
      let* var_body = var_case_body (ref_ s0) in
      pure [ branch_ (var_ sort) (underscore_pattern @ [s0]) var_body ]
    )
  in
  (* Computes the branch for a constructor *)
  let mk_constr_pattern { cparameters; cname; cpositions; } =
    let extra_arg_list = function
      | None -> []
      | Some s -> [s] in
    let rec arg_map bs extra_arg head = match head with
      | Atom y ->
        let* has_args = check_args y in
        let* args = a_map (castUpSubst sort bs y) args in
        if has_args
        then pure (app_ref (nameF y)
                     (List.(concat (map sty_terms args))
                      @ extra_arg_list extra_arg))
        else
          (* In the case there are no args we check our extra_args to see what we pass to the no_args function.
           * This results in more normalized terms. If we always create an abstraction, we sometimes end up with terms like this (fun x, id x)
           *)
          pure (match extra_arg with
              | None -> abs_ref "x" (no_args (ref_ "x"))
              | Some s -> no_args s)
      | FunApp (fname, _, args) ->
        let* res = a_map (arg_map bs None) args in
        pure (funsem fname (res @ extra_arg_list extra_arg)) in
    let ss = getPattern "s" cpositions in
    let* positions = a_map2
        (fun s { binders; head; } ->
           arg_map binders (Some (ref_ s)) head)
        ss cpositions in
    pure (branch_ cname
            (underscore_pattern @ List.map fst cparameters @ ss)
            (sem (List.map fst cparameters) cname positions))
  in
  let* constr_pattern = a_map mk_constr_pattern ctors in
  let body = match_ (ref_ s) (var_pattern @ constr_pattern) in
  pure body

(** make the default var_case_body *)
let mk_var_case_body (sort: L.tId) (sty: substTy) = fun (s: constr_expr) ->
  let* toVarT = to_var sort sty in
  pure @@ app1_ toVarT s


module UpRens : UP_GENERATOR = LiftGen(struct
    (* UpRen in sort x by the binder *)
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `M; `N; `XI (`M, `N) ] in
      let [@warning "-8"] [ m; n; xi ], [], [], scopeBinders = v in
      (** register upRen for unfolding *)
      let* () = tell_unfold_function (upRen_ sort binder) in
      let (_, bpms) = blist_args ~implicit:false binder in
      let m' = succ_ m sort binder in
      let n' = succ_ n sort binder in
      let defBody = definitionBody sort binder
          (up_ren_ xi, xi)
          (fun p _ -> app_ref "upRen_p" [ref_ p; xi], xi) in
      pure @@ AM.(add_units Core [lemma_ ~opaque:false (upRen_ sort binder) (bpms @ scopeBinders) (renT m' n') defBody])
  end)

module Renamings : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
      let [@warning "-8"] _, [ ms; ns ], [ xis ], scopeBinders = v in
      (** automation *)
      let* substSorts = get_substv sort in
      let* () = tell_instance (ClassGen.Ren (List.length substSorts), sort, ss_names ms @ ss_names ns) in
      let* () = tell_cbn_function (ren_ sort) in
      let* () = tell_notation (NotationGen.RenApply substSorts, sort) in
      let* () = tell_notation (NotationGen.Ren substSorts, sort) in
      let* () = tell_proper_instance (sort, ren_ sort, extRen_ sort) in
      (* DONE what is the result of to_var here?\
       * when I call it with sort=tm, xi=[xity;xivl] I get this weird error term that to_var constructs. This is then probably ignored by some similar logic in the traversal. Seems brittle.
       * When I call it instead with sort=vl I get xivl. So it seems get the renaming of the sort that I'm currently inspecting *)
      (* register renaming instance & and unfolding *)
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = app_sort sort ns in
      (** body *)
      let* body = traversal s sort ren_ ~no_args:id [xis]
          (fun s ->
             let* toVarT = to_var sort xis in
             pure @@ app1_ (app_var_constr sort ns) (app1_ toVarT s))
          ~sem:(fun pms cname positions -> app_constr cname ns (mk_refs pms @ positions))
          map_ in
      pure @@ fixpointBody_ (ren_ sort) (scopeBinders @ bs) type_ body s
  end)

module UpSubsts : UP_GENERATOR = LiftGen(struct
    let mk_scons sort binder sigma ms =
      match binder with
      | L.Single y ->
        if sort = y
        then
          let zero_ = app1_ (app_var_constr sort ms) var_zero_ in
          app_ cons_ [zero_; sigma]
        else sigma
      | L.BinderList (p, y) ->
        if sort = y
        then
          let zero_ = app_ref "zero_p" [ref_ p] >>> app_var_constr sort ms in
          app_ref "scons_p" [ref_ p; zero_; sigma]
        else sigma

    let upSubstT binder sort ms sigma =
      let* pat = patternSId sort binder in
      let* ms' = upSubstScope sort [binder] ms in
      let* hasRen = hasRenamings sort in
      let sigma' = sigma >>> app_fix (if hasRen then (ren_ sort) else (subst_ sort)) pat in
      pure @@ mk_scons sort binder sigma' ms'

    let gen (binder, sort) =
      let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS) ] in
      let [@warning "-8"] [ m; sigma ], [ ns ], [], scopeBinders = v in
      (* TODO hack so that I only tell the instance when it's a single binder *)
      let* () = match binder with
        | L.Single x ->
          (* register up instance *)
          let* () = tell_instance (ClassGen.Up x, sort, "m" :: ss_names ns) in
          tell_notation (NotationGen.UpInst x, sort)
        | L.BinderList _ -> pure ()
      in
      (* register up for unfolding *)
      let* () = tell_unfold_function (up_ sort binder) in
      (* compute the lifted sigma  *)
      let* sigma_up = upSubstT binder sort ns sigma in
      let (_, bpms) = blist_args ~implicit:false binder in
      let m' = succ_ m sort binder in
      let* ns' = upSubstScope sort [binder] ns in
      pure @@ AM.(add_units Core [lemma_ ~opaque:false (up_ sort binder) (bpms @ scopeBinders) (substT m' ns' sort) sigma_up])
  end)

module Substitutions : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core


    (** Generate the substitution function
     ** e.g. Fixpoint subst_tm ... *)
    let gen sort =
      let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ sigmas ], scopeBinders = v in
      (** automation *)
      (* register subst instance & unfolding & up class *)
      let* substSorts = get_substv sort in
      let* () = tell_instance (ClassGen.Subst (List.length substSorts), sort, ss_names ms @ ss_names ns) in
      let* () = tell_cbn_function (subst_ sort) in
      let* () = tell_class (ClassGen.Up "", sort) in
      let* () = tell_notation (NotationGen.Up, sort) in
      let* () = tell_notation (NotationGen.SubstApply substSorts, sort) in
      let* () = tell_notation (NotationGen.Subst substSorts, sort) in
      let* () = tell_proper_instance (sort, subst_ sort, ext_ sort) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = app_sort sort ns in
      (** body *)
      let* body = traversal s sort subst_ ~no_args:id [sigmas]
          (mk_var_case_body sort sigmas)
          ~sem:(fun pms cname positions -> app_constr cname ns (mk_refs pms @ positions))
          map_ in
      pure @@ fixpointBody_ (subst_ sort) (scopeBinders @ bs) type_ body s
  end)

module UpIds : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* (ms, bms) = genScopeVarVect "m" sort in
      let* m_var = to_var_scope sort ms in
      let (sigma, bsigma) = genSubst "sigma" sort (m_var, ms) in
      let (eq, beq) = genEq "Eq" sigma (app_var_constr sort ms) in
      let n = varName "n" in
      let* ms' = upSubstScope sort [binder] ms in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (up_ sort binder) (pms @ [sigma]))
          (app_var_constr sort ms') in
      let* shift = patternSId sort binder in
      let* hasRen = hasRenamings sort in
      let t n = ap_
          (app_ref (if hasRen then ren_ sort else subst_ sort) shift)
          (app1_ eq n) in
      let defBody = definitionBody sort binder
          (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
          (const2 (app_ref "scons_p_eta" [app_var_constr sort ms'; abs_ref n (t (ref_ n)); abs_ref n eq_refl_], t (ref_ n))) in
      pure @@ AM.(add_units Core [lemma_ (upId_ sort binder) (bpms @ bms @ bsigma @ beq) ret (abs_ref n defBody)])
  end)

module IdLemmas : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort [ `MS; `SIGMAS (`MS, `MS) ] in
      let [@warning "-8"] [], [ ms ], [ sigmas ], scopeBinders = v in
      let* eqs' = mk_var_apps sort ms in
      let* (eqs, beqs) = genEqVect "Eq" sort (sty_terms sigmas) eqs'
          (fun x y s -> pure @@ app_ref (upId_ x y) [underscore_; s]) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_ (app_fix (subst_ sort) ~scopes:[sigmas] [ref_ s]) (ref_ s) in
      (** body *)
      let* body = traversal s sort idSubst_ [sigmas; eqs]
          (mk_var_case_body sort eqs)
          mapId_ in
      pure @@ fixpointBody_ (idSubst_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module UpExtRens : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `M; `N; `XI (`M, `N); `ZETA (`M, `N) ] in
      let [@warning "-8"] [ m; n; xi; zeta ], [], [], scopeBinders = v in
      let (eq, b_eq) = genEq "Eq" xi zeta in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (upRen_ sort binder) (pms @ [xi]))
          (app_ref (upRen_ sort binder) (pms @ [zeta])) in
      let n = varName "n" in
      let t n = app1_ eq n in
      let s = matchFin_ (ref_ n) (fun n -> ap_ shift_ (t n)) eq_refl_ in
      let defBody = definitionBody sort binder
          (s, t (ref_ n))
          (fun p _ -> (app_ref "scons_p_congr" [
               abs_ref "n" eq_refl_;
               abs_ref "n" @@ ap_ (app_ref "shift_p" [ref_ p]) (t (ref_ "n"))
             ], t (ref_ n))) in
      pure @@ AM.(add_units Core [lemma_ (upExtRen_ sort binder) (bpms @ scopeBinders @ b_eq) ret (abs_ref "n" defBody)])
  end)

module ExtRens : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `ZETAS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ xis; zetas ], scopeBinders = v in
      let* (eqs, beqs) = genEqVect "Eq" sort (sty_terms xis) (sty_terms zetas)
          (fun sort binder s -> pure @@ app_ref (upExtRen_ sort binder) [underscore_; underscore_; s]) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_
          (app_fix (ren_ sort) ~scopes:[xis] [ref_ s])
          (app_fix (ren_ sort) ~scopes:[zetas] [ref_ s]) in
      (** body *)
      let* body = traversal s sort extRen_ [xis; zetas; eqs]
          (fun s ->
             let* toVarT = to_var sort eqs in
             pure @@ ap_ (app_var_constr sort ns) (app1_ toVarT s))
          mapExt_ in
      pure @@ fixpointBody_ (extRen_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module UpExtSubsts : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `M; `NS; `SIGMA (`M, `NS); `TAU (`M, `NS) ] in
      let [@warning "-8"] [ m; sigma; tau ], [ ns ], [], scopeBinders = v in
      let (eq, beq) = genEq "Eq" sigma tau in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (up_ sort binder) (pms @ [sigma]))
          (app_ref (up_ sort binder) (pms @ [tau])) in
      let* shift = patternSId sort binder in
      let n = varName "n" in
      let* hasRen = hasRenamings sort in
      let t n = ap_
          (app_ref (if hasRen then ren_ sort else subst_ sort) shift)
          (app1_ eq n) in
      let defBody = definitionBody sort binder
          (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
          (const2 @@ (scons_p_congr_ (abs_ref "n" (t (ref_ "n")))
                        (abs_ref "n" eq_refl_),
                      t (ref_ n))) in
      pure @@ AM.(add_units Core [lemma_ (upExt_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)])
  end)

module ExtSubsts : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS); `TAUS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ sigmas; taus ], scopeBinders = v in
      let* (eqs, beqs) = genEqVect "Eq" sort (sty_terms sigmas) (sty_terms taus)
          (fun x y s -> pure @@ app_ref (upExt_ x y) [underscore_; underscore_; s]) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_
          (app_fix (subst_ sort) ~scopes:[sigmas] [ref_ s])
          (app_fix (subst_ sort) ~scopes:[taus] [ref_ s]) in
      (** body *)
      let* body = traversal s sort ext_ [sigmas; taus; eqs]
          (mk_var_case_body sort eqs)
          mapExt_ in
      pure @@ fixpointBody_ (ext_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module UpRenRens : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `K; `L; `M; `XI (`K, `L); `ZETA (`L, `M); `RHO (`K, `M) ] in
      let [@warning "-8"] [ k; l; m; xi; zeta; rho ], [], [], scopeBinders = v in
      let (eq, beq) = genEq "Eq" (xi >>> zeta) rho in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (upRen_ sort binder) (pms @ [xi])
           >>> app_ref (upRen_ sort binder) (pms @ [zeta]))
          (app_ref (upRen_ sort binder) (pms @ [rho])) in
      let defBody = definitionBody sort binder
          (app_ref up_ren_ren__ [xi; zeta; rho; eq], eq)
          (const2 @@ (app_ref "up_ren_ren_p" [eq], eq)) in
      pure @@ AM.(add_units Core [lemma_ (up_ren_ren_ sort binder) (bpms @ scopeBinders @ beq) ret defBody])
  end)

module CompRenRens : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    (* TODO consistent order of klmn *)
    let gen sort =
      let* v = V.genVariables sort [ `KS; `LS; `MS;
                                     `XIS (`MS, `KS); `ZETAS (`KS, `LS); `RHOS (`MS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ xis; zetas; rhos ], scopeBinders = v in
      let* (eqs, beqs) = genEqVect "Eq" sort
          (List.map2 (>>>) (sty_terms xis) (sty_terms zetas)) (sty_terms rhos)
          (fun x y s -> pure @@ match y with
             | L.Single z -> if z = x
               then app_ref up_ren_ren__ [underscore_; underscore_; underscore_; s]
               else s
             | L.BinderList (_, z) -> if z = x
               then app_ref "up_ren_ren_p" [s]
               else s) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_
          (app_fix (ren_ sort) (sty_terms zetas
                                @ [ app_ref (ren_ sort) (sty_terms xis @ [ref_ s]) ]))
          (app_ref (ren_ sort) (sty_terms rhos @ [ref_ s])) in
      (** body *)
      let* body = traversal s sort compRenRen_ [xis; zetas; rhos; eqs]
          (fun s ->
             let* toVarT = to_var sort eqs in
             pure (ap_ (app_var_constr sort ls) (app1_ toVarT s)))
          mapComp_ in
      pure @@ fixpointBody_ (compRenRen_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module UpRenSubsts : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `K; `L; `MS;
                                     `XI (`K, `L); `TAU (`L, `MS); `THETA (`K, `MS) ] in
      let [@warning "-8"] [ k; l; xi; tau; theta ], [ ms ], [], scopeBinders = v in
      let (eq, beq) = genEq "Eq" (xi >>> tau) theta in
      let n = varName "n" in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (upRen_ sort binder) (pms @ [xi])
           >>> app_ref (up_ sort binder) (pms @ [tau]))
          (app_ref (up_ sort binder) (pms @ [theta])) in
      let* shift = patternSId sort binder in
      let t n = ap_ (app_ref (ren_ sort) shift) (app1_ eq n) in
      let s = eqTrans_
          (scons_p_comp' (ref_ n))
          (scons_p_congr_ (abs_ref "z" (eqTrans_
                                          (scons_p_tail' (app1_ xi (ref_ "z")))
                                          (t (ref_ "z"))))
             (abs_ref "z" @@ scons_p_head' (ref_ "z"))) in
      let defBody = definitionBody sort binder
          (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
          (const2 (s, t (ref_ n))) in
      pure @@ AM.(add_units Core [lemma_ (up_ren_subst_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)])
  end)

module CompRenSubsts : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort
          [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ xis; taus; thetas ], scopeBinders = v in
      let* (eqs, beqs) = genEqVect "Eq" sort
          (List.map2 (>>>) (sty_terms xis) (sty_terms taus))
          (sty_terms thetas)
          (fun x y s -> pure @@ app_ref (up_ren_subst_ x y) [underscore_; underscore_; underscore_; s]) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_
          (app_ref (subst_ sort) (sty_terms taus @ [app_ref (ren_ sort) (sty_terms xis @ [ref_ s])]))
          (app_ref (subst_ sort) (sty_terms thetas @ [ref_ s])) in
      (** body *)
      let* body = traversal s sort compRenSubst_ [xis; taus; thetas; eqs]
          (mk_var_case_body sort eqs)
          mapComp_ in
      pure @@ fixpointBody_ (compRenSubst_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module UpSubstRens : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                                   ; `ZETAS (`LS, `MS); `THETA (`K, `MS) ] in
      let [@warning "-8"] [ k; sigma; theta ], [ ls; ms ], [ zetas ], scopeBinders = v in
      let (eq, beq) = genEq "Eq" (sigma >>> app_ref (ren_ sort) (sty_terms zetas)) theta in
      let n = varName "n" in
      let* ms_up = upSubstScope sort [binder] ms in
      let* substSorts = get_substv sort in
      (* TODO document *)
      let* zetas' = upSubst sort [binder] zetas in
      let* pat = patternSId sort binder in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (up_ sort binder) (pms @ [sigma])
           >>> app_ref (ren_ sort) (sty_terms zetas'))
          (app_ref (up_ sort binder) (pms @ [theta])) in
      let* shift = patternSId sort binder in
      (* TODO refactor these. But I don't see how.
       * We have huge terms like this in UpSubstRens, UpRenSubsts, etc. but they are too different from each
       * other that I can easily refactor them. *)
      let t n = eqTrans_
          (app_ref (compRenRen_ sort) (pat @ sty_terms zetas'
                                       @ List.map2 (>>>) (sty_terms zetas) pat
                                       @ List.map (const (abs_ref "x" eq_refl_)) pat
                                       @ [ app1_ sigma n ]))
          (eqTrans_
             (eqSym_ (app_ref (compRenRen_ sort) (sty_terms zetas @ pat
                                                  @ List.map2 (>>>) (sty_terms zetas) pat
                                                  @ List.map (const (abs_ref "x" eq_refl_)) pat
                                                  @ [ app1_ sigma n ])))
             (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
      let t' n z' = eqTrans_
          (app_ref (compRenRen_ sort) (pat @ sty_terms zetas'
                                       @ List.map2 (>>>) (sty_terms zetas) pat
                                       @ List.map (fun x ->
                                           (abs_ref "x" (if x = z'
                                                         then scons_p_tail' (ref_ "x")
                                                         else eq_refl_))) substSorts
                                       @ [ app1_ sigma n ]))
          (eqTrans_
             (eqSym_ (app_ref (compRenRen_ sort) (sty_terms zetas @ pat
                                                  @ List.map2 (>>>) (sty_terms zetas) pat
                                                  @ List.map (const (abs_ref "x" eq_refl_)) pat
                                                  @ [ app1_ sigma n ])))
             (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
      let hd = abs_ref "x" (ap_ (app_var_constr sort ms_up) (scons_p_head' (ref_ "x"))) in
      let defBody = definitionBody sort binder
          (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
          (fun _ sort' -> (eqTrans_
                             (scons_p_comp' (ref_ n))
                             (scons_p_congr_ (abs_ref "n" (t' (ref_ "n") sort')) hd),
                           t' (ref_ n) sort')) in
      pure @@ AM.(add_units Core [lemma_ (up_subst_ren_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)])
  end)

module CompSubstRens : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                                   ; `ZETAS (`KS, `LS); `THETAS (`MS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; zetas; thetas ], scopeBinders = v in
      let* sigmazeta = comp_ren_or_subst sort zetas sigmas in
      let* (eqs, beqs) = genEqVect "Eq" sort sigmazeta (sty_terms thetas)
          (fun z y s ->
             let* zetas' = castSubst sort z zetas in
             pure @@ app_ref (up_subst_ren_ z y) ([underscore_]
                                                  @ List.map (const underscore_) (sty_terms zetas')
                                                  @ [underscore_; s])) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_
          (app_ref (ren_ sort) (sty_terms zetas
                                @ [app_ref (subst_ sort) (sty_terms sigmas @ [ref_ s])]))
          (app_ref (subst_ sort) (sty_terms thetas @ [ref_ s])) in
      (** body *)
      let* body = traversal s sort compSubstRen_ [sigmas; zetas; thetas; eqs]
          (mk_var_case_body sort eqs)
          mapComp_ in
      pure @@ fixpointBody_ (compSubstRen_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module UpSubstSubsts : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS)
                                   ; `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
      let [@warning "-8"] [ k; sigma; theta ], [ ls; ms ], [ taus ], scopeBinders = v in
      let (eq, beq) = genEq "Eq" (sigma >>> app_ref (subst_ sort) (sty_terms taus)) theta in
      let n = varName "n" in
      let* ls' = upSubstScope sort [binder] ls in
      let* taus' = upSubst sort [binder] taus in
      let* pat = patternSId sort binder in
      let (pms, bpms) = blist_args binder in
      (* TODO document *)
      let ret = equiv_
          (app_ref (up_ sort binder) (pms @ [sigma])
           >>> app_ref (subst_ sort) (sty_terms taus'))
          (app_ref (up_ sort binder) (pms @ [theta])) in
      let* substSorts = get_substv sort in
      (* TODO document *)
      let* pat' = comp_ren_or_subst sort (SubstRen pat) taus in
      (* TODO there are some repeated code segments in this and other functions. abstract them out *)
      let t n = eqTrans_
          (app_ref (compRenSubst_ sort) (pat @ sty_terms taus'
                                         @ List.map2 (>>>) pat (sty_terms taus')
                                         @ List.map (const (abs_ref "x" eq_refl_)) pat
                                         @ [ app1_ sigma n ]))
          (eqTrans_
             (eqSym_ (app_ref (compSubstRen_ sort) (sty_terms taus @ pat @ pat'
                                                    @ List.map (const (abs_ref "x" eq_refl_)) pat
                                                    @ [ app1_ sigma n ])))
             (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
      let t' n z' = eqTrans_
          (app_ref (compRenSubst_ sort) (pat @ sty_terms taus'
                                         @ List.map2 (>>>) pat (sty_terms taus')
                                         @ List.map (const (abs_ref "x" eq_refl_)) pat
                                         @ [ app1_ sigma n ]))
          (eqTrans_
             (eqSym_ (app_ref (compSubstRen_ sort)
                        (sty_terms taus @ pat
                         @ List.map (const underscore_) pat'
                         @ List.map (fun substSort ->
                             abs_ref "x" @@ eqSym_ (if substSort = z'
                                                    then scons_p_tail' (ref_ "x")
                                                    else eq_refl_)) substSorts
                         @ [ app1_ sigma n ])))
             (ap_ (app_ref (ren_ sort) pat) (app1_ eq n))) in
      let hd = abs_ref "x" (app_ref "scons_p_head'" [ underscore_
                                                    ; abs_ref "z" (app_ref (ren_ sort)
                                                                     (pat @ [underscore_]))
                                                    ; ref_ "x" ]) in
      let defBody = definitionBody sort binder
          (matchFin_ (ref_ n) t eq_refl_ , t (ref_ n))
          (fun p sort' -> (eqTrans_
                             (app_ref "scons_p_comp'" [ app_ref "zero_p" [ref_ p]
                                                        >>> app_var_constr sort ls'
                                                      ; underscore_; underscore_
                                                      ; ref_ n ])
                             (scons_p_congr_ (abs_ref "n" (t' (ref_ "n") sort')) hd),
                           t' (ref_ n) sort')) in
      pure @@ AM.(add_units Core [lemma_ (up_subst_subst_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)])
  end)

module CompSubstSubsts : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS)
                                   ; `TAUS (`KS, `LS); `THETAS (`MS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; taus; thetas ], scopeBinders = v in
      let* sigmatau = comp_ren_or_subst sort taus sigmas in
      let* (eqs, beqs) = genEqVect "Eq" sort sigmatau (sty_terms thetas) (fun z y s ->
          let* taus' = castSubst sort z taus in
          pure @@ app_ref (up_subst_subst_ z y) ([underscore_]
                                                 @ List.map (const underscore_) (sty_terms taus')
                                                 @ [underscore_; s])) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_
          (app_ref (subst_ sort) (sty_terms taus
                                  @ [app_ref (subst_ sort) (sty_terms sigmas @ [ref_ s])]))
          (app_ref (subst_ sort) (sty_terms thetas @ [ref_ s])) in
      (** body *)
      let* body = traversal s sort compSubstSubst_ [sigmas; taus; thetas; eqs]
          (mk_var_case_body sort eqs)
          mapComp_ in
      pure @@ fixpointBody_ (compSubstSubst_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module UpSubstSubstNoRens : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `K; `LS; `MS; `SIGMA (`K, `LS); `TAUS (`LS, `MS); `THETA (`K, `MS) ] in
      let [@warning "-8"] [ k; sigma; theta ], [ ls; ms ], [ taus ], scopeBinders = v in
      let (eq, beq) = genEq "Eq" (sigma >>> app_ref (subst_ sort) (sty_terms taus)) theta in
      let n = varName "n" in
      (* TODO fix variable names *)
      let* ms = upSubstScope sort [binder] ms in
      let* ls' = upSubstScope sort [binder] ls in
      let* taus_up = upSubst sort [binder] taus in
      let* pat = patternSId sort binder in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (up_ sort binder) (pms @ [sigma])
           >>> app_ref (subst_ sort) (sty_terms taus_up))
          (app_ref (up_ sort binder) (pms @ [theta])) in
      let* patNoRen = patternSIdNoRen sort binder in
      let* substSorts = get_substv sort in
      let* pat' = comp_ren_or_subst sort (SubstSubst pat) taus in
      let t n = eqTrans_
          (app_ref (compSubstSubst_ sort)
             (pat @ sty_terms taus_up
              @ List.map2 (>>>) patNoRen (sty_terms taus_up)
              @ List.map (const (abs_ref "x" eq_refl_)) pat
              @ [ app1_ sigma n ]))
          (eqTrans_
             (eqSym_ (app_ref (compSubstSubst_ sort)
                        (sty_terms taus @ pat @ pat'
                         @ List.map (const (abs_ref "x" eq_refl_)) pat
                         @ [ app1_ sigma n ])))
             (ap_ (app_ref (subst_ sort) pat) (app1_ eq n))) in
      let t' n z' = eqTrans_
          (app_ref (compSubstSubst_ sort)
             (pat @ sty_terms taus_up
              @ List.map2 (>>>) patNoRen (sty_terms taus_up)
              @ List.map (const (abs_ref "x" eq_refl_)) pat
              @ [ app1_ sigma n ]))
          (eqTrans_
             (eqSym_ (app_ref (compSubstSubst_ sort)
                        (sty_terms taus @ pat
                         @ List.map (const underscore_) pat'
                         @ List.map (fun substSort ->
                             abs_ref "x" (eqSym_ (if substSort = z'
                                                  then scons_p_tail' (ref_ "x")
                                                  else eq_refl_)))
                           substSorts
                         @ [ app1_ sigma n ])))
             (ap_ (app_ref (subst_ sort) pat) (app1_ eq n))) in
      let hd = abs_ref "x" (app_ref "scons_p_head'"
                              [ underscore_
                              ; abs_ref "z" (app_ref (subst_ sort) (pat @ [underscore_]))
                              ; ref_ "x" ]) in
      let defBody = definitionBody sort binder
          (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
          (fun p z' -> (eqTrans_
                          (app_ref "scons_p_comp'"
                             [ app_ref "zero_p" [ref_ p] >>> (app_var_constr sort ls')
                             ; underscore_
                             ; underscore_
                             ; ref_ n ])
                          (scons_p_congr_ (abs_ref "n" (t' (ref_ "n") z')) hd),
                        t' (ref_ n) z')) in
      pure @@ AM.(add_units Core [lemma_ (up_subst_subst_ sort binder) (bpms @ scopeBinders @ beq) ret (abs_ref "n" defBody)])
  end)

module UpRinstInsts : UP_GENERATOR = LiftGen(struct
    let gen (binder, sort) =
      let* v = V.genVariables sort [ `M; `NS ] in
      let [@warning "-8"] [ m ], [ ns ], [], scopeBinders = v in
      let* n_var = to_var_scope sort ns in
      let (xi, bxi) = genRen "xi" (m, n_var) in
      (* the sigma cannot be part of genVariables because of the xi. I we added it, the binders would be in the wrong order. *)
      let (sigma, bsigma) = genSubst "sigma" sort (m, ns) in
      let (eq, beq) = genEq "Eq" (xi >>> app_var_constr sort ns) sigma in
      let* ns' = upSubstScope sort [binder] ns in
      let (pms, bpms) = blist_args binder in
      let ret = equiv_
          (app_ref (upRen_ sort binder) (pms @ [xi]) >>> app_var_constr sort ns')
          (app_ref (up_ sort binder) (pms @ [sigma])) in
      let* shift = patternSId sort binder in
      let t n = ap_ (app_ref (ren_ sort) shift) (app1_ eq n) in
      let n = varName "n" in
      let s = eqTrans_
          (app_ref "scons_p_comp'" [underscore_; underscore_; app_var_constr sort ns'; ref_ n])
          (scons_p_congr_ (abs_ref "n" (t (ref_ "n"))) (abs_ref "z" eq_refl_)) in
      let defBody = definitionBody sort binder
          (matchFin_ (ref_ n) t eq_refl_, t (ref_ n))
          (const2 (s, t (ref_ n))) in
      pure @@ AM.(add_units Core [lemma_ (up_rinstInst_ sort binder) (bpms @ scopeBinders @ bxi @ bsigma @ beq) ret (abs_ref "n" defBody)])
  end)

module RinstInsts : COMPONENT_GENERATOR = FixGen(struct
    let tag = AM.Core

    let gen sort =
      let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS); `SIGMAS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ xis; sigmas ], scopeBinders = v in
      let* xis' = substify sort ns xis in
      let* (eqs, beqs) = genEqVect "Eq" sort xis' (sty_terms sigmas)
          (fun x y s -> pure (app_ref (up_rinstInst_ x y) [underscore_; underscore_; s])) in
      (** type *)
      let (s, bs) = genMatchVar sort ms in
      let type_ = eq_
          (app_ref (ren_ sort) (sty_terms xis @ [ref_ s]))
          (app_ref (subst_ sort) (sty_terms sigmas @ [ref_ s])) in
      (** body *)
      let* body = traversal s sort rinstInst_ [xis; sigmas; eqs]
          (mk_var_case_body sort eqs)
          mapExt_ in
      pure @@ fixpointBody_ (rinstInst_ sort) (scopeBinders @ beqs @ bs) type_ body s
  end)

module LemmaRinstInsts : COMPONENT_GENERATOR = LemGen(struct
    let gen_lemma sort =
      (* register substify lemma *)
      let* () = tell_substify_lemma_fext (rinstInstFun_ sort) in
      let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
      let* substSorts = get_substv sort in
      let* xis_subst = substify sort ns xis in
      let ret = eq_
          (app_ref (ren_ sort) (sty_terms xis))
          (app_ref (subst_ sort) xis_subst) in
      let proof = fext_ (abs_ref "x"
                           (app_ref (rinstInst_ sort)
                              (sty_terms xis
                               @ List.map (const underscore_) substSorts
                               @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                               @ [ ref_ "x" ]))) in
      pure @@ AM.(add_units Fext [lemma_ (rinstInstFun_ sort) scopeBinders ret proof])

    let gen_lemma_pointwise sort =
      (* register substify lemma *)
      let* () = tell_substify_lemma (rinstInst'Fun_ sort) in
      let* () = tell_substify_lemma (rinstInst'FunPointwise_ sort) in
      let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
      let* substSorts = get_substv sort in
      let* xis_subst = substify sort ns xis in
      let s = varName "s" in
      let ret = eq_
          (app_ref (ren_ sort) (sty_terms xis @ [ ref_ s ]))
          (app_ref (subst_ sort) (xis_subst @ [ ref_ s ])) in
      let proof = app_ref (rinstInst_ sort) (sty_terms xis
                                             @ List.map (const underscore_) substSorts
                                             @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                             @ [ ref_ s ]) in
      let ret_pointwise = pointwise_
          (app_ref (ren_ sort) (sty_terms xis))
          (app_ref (subst_ sort) xis_subst) in
      let proof_pointwise = abs_ref "s" proof in
      pure @@ AM.(add_units Core [
          lemma_ (rinstInst'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(app_sort sort ms) s ]) ret proof;
          lemma_ (rinstInst'FunPointwise_ sort) (scopeBinders) ret_pointwise proof_pointwise
        ])

    let gen sort =
      let* lemma = gen_lemma sort in
      let* lemma_pointwise = gen_lemma_pointwise sort in
      pure @@ AM.concat [lemma; lemma_pointwise]
  end)

module LemmaVarLs : COMPONENT_GENERATOR = LemGen(struct
    let gen_lemma sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_fext (varLFun_ sort) in
      let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ sigmas ], scopeBinders = v in
      let* sigma' = to_var sort sigmas in
      let ret = eq_ (app_var_constr sort ms >>> app_ref (subst_ sort) (sty_terms sigmas)) sigma' in
      let proof = fext_ (abs_ref "x" eq_refl_) in
      pure @@ AM.(add_units Fext [lemma_ (varLFun_ sort) scopeBinders ret proof])

    (* varL' the extensional variant of varL *)
    let gen_lemma_pointwise sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_no_fext (varL'Fun_ sort) in
      let* () = tell_rewrite_no_fext (varL'FunPointwise_ sort) in
      let* v = V.genVariables sort [ `MS; `NS; `SIGMAS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ sigmas ], scopeBinders = v in
      (* generate type *)
      (* on the right hand side we only need the sigma for the current sort *)
      let* sigma' = to_var sort sigmas in
      let* m' = to_var_scope sort ms in
      let x = varName "x" in
      let ret = eq_
          (app_ref (subst_ sort) (sty_terms sigmas
                                  @ [ app_constr (var_ sort) ms [ ref_ x ] ]))
          (app1_ sigma' (ref_ x)) in
      let proof = eq_refl_ in
      let ret_pointwise = pointwise_ (app_var_constr sort ms >>> app_ref (subst_ sort) (sty_terms sigmas)) sigma' in
      let proof_pointwise = abs_ref "x" eq_refl_ in
      pure @@ AM.(add_units Core [
          lemma_ (varL'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(varT m') x ]) ret proof;
          lemma_ (varL'FunPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
        ])

    let gen sort =
      let* lemma = gen_lemma sort in
      let* lemma_pointwise = gen_lemma_pointwise sort in
      pure @@ AM.concat [lemma; lemma_pointwise]
  end)

module LemmaVarLRens : COMPONENT_GENERATOR = LemGen(struct
    let gen_lemma sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_fext (varLRenFun_ sort) in
      let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
      let* xi' = to_var sort xis in
      let ret = eq_
          (app_var_constr sort ms >>> app_ref (ren_ sort) (sty_terms xis))
          (xi' >>> (app_var_constr sort ns)) in
      let proof = fext_ (abs_ref "x" eq_refl_) in
      pure @@ AM.(add_units Fext [lemma_ (varLRenFun_ sort) scopeBinders ret proof])

    (* varLRen' the extensional variant of varLRen *)
    let gen_lemma_pointwise sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_no_fext (varLRen'Fun_ sort) in
      let* () = tell_rewrite_no_fext (varLRen'FunPointwise_ sort) in
      let* v = V.genVariables sort [ `MS; `NS; `XIS (`MS, `NS) ] in
      let [@warning "-8"] [], [ ms; ns ], [ xis ], scopeBinders = v in
      let* xi' = to_var sort xis in
      let* m' = to_var_scope sort ms in
      let x = varName "x" in
      let ret = eq_
          (app_ref (ren_ sort) (sty_terms xis
                                @ [ app_constr (var_ sort) ms [ ref_ x ] ]))
          (app_constr (var_ sort) ns [ app1_ xi' (ref_ x) ]) in
      let proof = eq_refl_ in
      let ret_pointwise = pointwise_
          (app_var_constr sort ms >>> app_ref (ren_ sort) (sty_terms xis))
          (xi' >>> (app_var_constr sort ns)) in
      let proof_pointwise = abs_ref "x" eq_refl_ in
      pure @@ AM.(add_units Core [
          lemma_ (varLRen'Fun_ sort) (scopeBinders @ [binder1_ ~btype:(varT m') x ]) ret proof;
          lemma_ (varLRen'FunPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
        ])

    let gen sort =
      let* lemma = gen_lemma sort in
      let* lemma_pointwise = gen_lemma_pointwise sort in
      pure @@ AM.concat [lemma; lemma_pointwise]
  end)

module LemmaInstIds : COMPONENT_GENERATOR = LemGen(struct
    let gen_lemma sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_fext (instIdFun_ sort) in
      let* (ms, bms) = genScopeVarVect "m" sort in
      let* substSorts = get_substv sort in
      let* vars = mk_var_apps sort ms in
      let ret = eq_ (app_fix (subst_ sort) vars) id_ in
      let proof = fext_ (abs_ref "x"
                           (app_ref (idSubst_ sort)
                              (vars
                               @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                               @ [ app_id_ (ref_ "x") ]))) in
      pure @@ AM.(add_units Fext [lemma_ (instIdFun_ sort) bms ret proof])

    let gen_lemma_pointwise sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_no_fext (instId'Fun_ sort) in
      let* () = tell_rewrite_no_fext (instId'FunPointwise_ sort) in
      let* v = V.genVariables sort [ `MS ] in
      let [@warning "-8"] [], [ ms ], [], scopeBinders = v in
      let* substSorts = get_substv sort in
      let* vars = mk_var_apps sort ms in
      let s = varName "s" in
      let ret = eq_ (app_ref (subst_ sort) (vars @ [ ref_ s ])) (ref_ s) in
      let proof = app_ref (idSubst_ sort) (vars
                                           @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                           @ [ ref_ "s" ]) in
      let ret_pointwise = pointwise_ (app_ref (subst_ sort) vars) id_ in
      let proof_pointwise = abs_ref "s" proof in
      pure @@ AM.(add_units Core [
          lemma_ (instId'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(app_sort sort ms) s ]) ret proof;
          lemma_ (instId'FunPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
        ])

    let gen sort =
      let* lemma = gen_lemma sort in
      let* lemma_pointwise = gen_lemma_pointwise sort in
      pure @@ AM.concat [lemma; lemma_pointwise]
  end)

module LemmaRinstIds : COMPONENT_GENERATOR = LemGen(struct
    let gen_lemma sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_fext (rinstIdFun_ sort) in
      let* (ms, bms) = genScopeVarVect "m" sort in
      let* substSorts = get_substv sort in
      let* vars = mk_var_apps sort ms in
      let ret = eq_
          (app_fix ~expl:true (ren_ sort) ~sscopes:[ms; ms] (List.map (const id_) substSorts))
          id_ in
      let proof = eqTrans_
          (app_ref (rinstInstFun_ sort) (List.map (const (app_id_ underscore_)) substSorts))
          (ref_ (instIdFun_ sort)) in
      pure @@ AM.(add_units Fext [lemma_ (rinstIdFun_ sort) bms ret proof])

    let gen_lemma_pointwise sort =
      (* register lemma for asimpl *)
      let* () = tell_rewrite_no_fext (rinstId'Fun_ sort) in
      let* () = tell_rewrite_no_fext (rinstId'FunPointwise_ sort) in
      let* v = V.genVariables sort [ `MS ] in
      let [@warning "-8"] [], [ ms ], [], scopeBinders = v in
      let* substSorts = get_substv sort in
      let* vars = mk_var_apps sort ms in
      let ids = List.map (const id_) substSorts in
      let s = varName "s" in
      let t = varName "t" in
      let ret = eq_ (app_ref (ren_ sort) (ids @ [ ref_ s ])) (ref_ s) in
      (* a.d. I think this is the only instance of rewriting used. Can probably also be done without but it makes it much easier. *)
      let proof = app_ref "eq_ind_r" [ abs_ref t (eq_ (ref_ t) (ref_ s))
                                     ; app_ref (instId'Fun_ sort) [ ref_ s ]
                                     ; app_ref (rinstInst'Fun_ sort) (ids @ [ ref_ s ]) ] in
      let ret_pointwise = pointwise_
          (app_fix ~expl:true (ren_ sort) ~sscopes:[ms; ms] (List.map (const id_) substSorts))
          id_ in
      let proof_pointwise = abs_ref "s" proof in
      pure @@ AM.(add_units Core [
          lemma_ (rinstId'Fun_ sort) (scopeBinders @ [ binder1_ ~btype:(app_sort sort ms) s ]) ret proof;
          lemma_ (rinstId'FunPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
        ])

    let gen sort =
      let* lemma = gen_lemma sort in
      let* lemma_pointwise = gen_lemma_pointwise sort in
      pure @@ AM.concat [lemma; lemma_pointwise]
  end)

module LemmaCompRenRens : COMPONENT_GENERATOR = LemGen(struct
    let gen sort =
      (* register lemmas for asimpl *)
      let* () = tell_rewrite_base (renRen_ sort) in
      let* () = tell_rewrite_base (renRenPointwise_ sort) in
      let* () = tell_rewrite_fext (renRen'_ sort) in
      let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `ZETAS (`KS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ xis; zetas ], scopeBinders = v in
      let* substSorts = get_substv sort in
      let sigmazeta = xis <<>> zetas in
      let s = varName "s" in
      let ret = eq_
          (app_ref (ren_ sort) (sty_terms zetas
                                @ [ app_ref (ren_ sort) (sty_terms xis
                                                         @ [ ref_ s ]) ]))
          (app_ref (ren_ sort) (sigmazeta @ [ ref_ s ])) in
      let proof = app_ref (compRenRen_ sort) (sty_terms xis
                                              @ sty_terms zetas
                                              @ List.map (const underscore_) substSorts
                                              @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                              @ [ ref_ s ]) in
      let ret' = eq_
          (app_ref (ren_ sort) (sty_terms xis) >>> app_ref (ren_ sort) (sty_terms zetas))
          (app_ref (ren_ sort) sigmazeta) in
      let proof' = fext_ (abs_ref "n"
                            (app_ref (renRen_ sort)
                               (sty_terms xis
                                @ sty_terms zetas
                                @ [ ref_ "n" ]))) in
      let ret_pointwise = pointwise_
          (app_ref (ren_ sort) (sty_terms xis) >>> app_ref (ren_ sort) (sty_terms zetas))
          (app_ref (ren_ sort) sigmazeta) in
      let proof_pointwise = abs_ref "s" proof in
      pure @@ AM.(from_list [
          (Fext, [lemma_ (renRen'_ sort) scopeBinders ret' proof']);
          (Core, [lemma_ (renRen_ sort) (scopeBinders
                                         @ [ binder1_ ~btype:(app_sort sort ms) s ])
                    ret proof;
                  lemma_ (renRenPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
                 ])
        ])

  end)

module LemmaCompSubstRens : COMPONENT_GENERATOR = LemGen(struct
    let gen sort =
      (* register lemmas for asimpl *)
      let* () = tell_rewrite_base (substRen_ sort) in
      let* () = tell_rewrite_base (substRenPointwise_ sort) in
      let* () = tell_rewrite_fext (substRen'_ sort) in
      let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `ZETAS (`KS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; zetas ], scopeBinders = v in
      let* substSorts = get_substv sort in
      let s = varName "s" in
      let* sigmazetas = comp_ren_or_subst sort zetas sigmas in
      let ret = eq_
          (app_ref (ren_ sort) (sty_terms zetas
                                @ [ app_ref (subst_ sort) (sty_terms sigmas
                                                           @ [ ref_ s ]) ]))
          (app_ref (subst_ sort) (sigmazetas @ [ ref_ s ])) in
      let proof = app_ref (compSubstRen_ sort) (sty_terms sigmas
                                                @ sty_terms zetas
                                                @ List.map (const underscore_) substSorts
                                                @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                                @ [ ref_ s ]) in
      let ret' = eq_
          (app_ref (subst_ sort) (sty_terms sigmas) >>> app_ref (ren_ sort) (sty_terms zetas))
          (app_ref (subst_ sort) sigmazetas) in
      let proof' = fext_ (abs_ref "n"
                            (app_ref (substRen_ sort)
                               (sty_terms sigmas
                                @ sty_terms zetas
                                @ [ ref_ "n" ]))) in
      let ret_pointwise = pointwise_
          (app_ref (subst_ sort) (sty_terms sigmas) >>> app_ref (ren_ sort) (sty_terms zetas))
          (app_ref (subst_ sort) sigmazetas) in
      let proof_pointwise = abs_ref "s" proof in
      pure @@ AM.(from_list [
          (Fext, [lemma_ (substRen'_ sort) scopeBinders ret' proof']);
          (Core, [lemma_ (substRen_ sort) (scopeBinders
                                           @ [ binder1_ ~btype:(app_sort sort ms) s ])
                    ret proof;
                  lemma_ (substRenPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
                 ])
        ])
  end)

module LemmaCompRenSubsts : COMPONENT_GENERATOR = LemGen(struct
    let gen sort =
      (* register lemmas for asimpl *)
      let* () = tell_rewrite_base (renSubst_ sort) in
      let* () = tell_rewrite_base (renSubstPointwise_ sort) in
      let* () = tell_rewrite_fext (renSubst'_ sort) in
      let* v = V.genVariables sort [ `KS; `LS; `MS; `XIS (`MS, `KS); `TAUS (`KS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ xis; taus ], scopeBinders = v in
      let* substSorts = get_substv sort in
      let xitaus =  xis <<>> taus in
      let s = varName "s" in
      let ret = eq_
          (app_ref (subst_ sort) (sty_terms taus
                                  @ [ app_ref (ren_ sort) (sty_terms xis
                                                           @ [ref_ s])]))
          (app_ref (subst_ sort) (xitaus @ [ref_ s])) in
      let proof = app_ref (compRenSubst_ sort) (sty_terms xis
                                                @ sty_terms taus
                                                @ List.map (const underscore_) substSorts
                                                @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                                @ [ref_ s]) in
      let ret' = eq_
          (app_ref (ren_ sort) (sty_terms xis) >>> (app_ref (subst_ sort) (sty_terms taus)))
          (app_ref (subst_ sort) xitaus) in
      let proof' = fext_ (abs_ref "n"
                            (app_ref (renSubst_ sort)
                               (sty_terms xis
                                @ sty_terms taus
                                @ [ref_ "n"]))) in
      let ret_pointwise = pointwise_
          (app_ref (ren_ sort) (sty_terms xis) >>> (app_ref (subst_ sort) (sty_terms taus)))
          (app_ref (subst_ sort) xitaus) in
      let proof_pointwise = abs_ref "s" proof in
      pure @@ AM.(from_list [
          (Fext, [lemma_ (renSubst'_ sort) scopeBinders ret' proof']);
          (Core, [
              lemma_ (renSubst_ sort) (scopeBinders
                                       @ [ binder1_ ~btype:(app_sort sort ms) s ])
                ret proof;
              lemma_ (renSubstPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
            ])
        ])
  end)

module LemmaCompSubstSubsts : COMPONENT_GENERATOR = LemGen(struct
    let gen sort =
      (* register lemmas for asimpl *)
      let* () = tell_rewrite_base (substSubst_ sort) in
      let* () = tell_rewrite_base (substSubstPointwise_ sort) in
      let* () = tell_rewrite_fext (substSubst'_ sort) in
      let* v = V.genVariables sort [ `KS; `LS; `MS; `SIGMAS (`MS, `KS); `TAUS (`KS, `LS) ] in
      let [@warning "-8"] [], [ ks; ls; ms ], [ sigmas; taus ], scopeBinders = v in
      let* substSorts = get_substv sort in
      let s = varName "s" in
      let* sigmatau = comp_ren_or_subst sort taus sigmas in
      let ret = eq_
          (app_ref (subst_ sort) (sty_terms taus
                                  @ [ app_ref (subst_ sort) (sty_terms sigmas
                                                             @ [ref_ s])]))
          (app_ref (subst_ sort) (sigmatau @ [ref_ s])) in
      let proof = app_ref (compSubstSubst_ sort) (sty_terms sigmas
                                                  @ sty_terms taus
                                                  @ List.map (const underscore_) substSorts
                                                  @ List.map (const (abs_ref "n" eq_refl_)) substSorts
                                                  @ [ref_ s]) in
      let ret' = eq_
          (app_ref (subst_ sort) (sty_terms sigmas) >>> app_ref (subst_ sort) (sty_terms taus))
          (app_ref (subst_ sort) sigmatau) in
      let proof' = fext_ (abs_ref "n"
                            (app_ref (substSubst_ sort)
                               (sty_terms sigmas
                                @ sty_terms taus
                                @ [ref_ "n"]))) in
      let ret_pointwise = pointwise_
          (app_ref (subst_ sort) (sty_terms sigmas) >>> app_ref (subst_ sort) (sty_terms taus))
          (app_ref (subst_ sort) sigmatau) in
      let proof_pointwise = abs_ref "s" proof in
      pure @@ AM.(from_list [
          (Fext, [lemma_ (substSubst'_ sort) scopeBinders ret' proof']);
          (Core, [
              lemma_ (substSubst_ sort) (scopeBinders
                                         @ [ binder1_ ~btype:(app_sort sort ms) s ])
                ret proof;
              lemma_ (substSubstPointwise_ sort) scopeBinders ret_pointwise proof_pointwise
            ])
        ])
  end)

(** For a given component generate the inductive type and congruence lemmas.
 ** These will always be generated, no matter if the component has renamings/substitutions. *)
let gen_common component =
  let* def_sorts = a_filter check_definable component in
  let* inductive = Inductives.gen def_sorts in
  let* congruences = Congruences.gen def_sorts in
  pure @@ AM.concat [inductive; congruences]

let gen_lemmas component up_list =
  let* var_sorts = a_filter check_open component in
  let* modules = sequence [
      (* INSTANTIATIONS *)
      UpRens.gen up_list;
      Renamings.gen component;
      UpSubsts.gen up_list;
      Substitutions.gen component;
      UpIds.gen up_list;
      IdLemmas.gen component;
      (* EXTENSIONALITY LEMMAS *)
      UpExtRens.gen up_list;
      ExtRens.gen component;
      UpExtSubsts.gen up_list;
      ExtSubsts.gen component;
      (* COMPOSITIONALITY LEMMAS *)
      UpRenRens.gen up_list;
      CompRenRens.gen component;
      UpRenSubsts.gen up_list;
      CompRenSubsts.gen component;
      UpSubstRens.gen up_list;
      CompSubstRens.gen component;
      UpSubstSubsts.gen up_list;
      CompSubstSubsts.gen component;
      LemmaCompRenRens.gen component;
      LemmaCompRenSubsts.gen component;
      LemmaCompSubstRens.gen component;
      LemmaCompSubstSubsts.gen component;
      (* Relation of renamings and substitutions *)
      UpRinstInsts.gen up_list;
      RinstInsts.gen component;
      LemmaRinstInsts.gen component;
      LemmaInstIds.gen component;
      LemmaRinstIds.gen component;
      LemmaVarLs.gen var_sorts;
      LemmaVarLRens.gen var_sorts
    ] in
  pure @@ AM.concat modules

let gen_lemmas_no_ren component up_list =
  let* var_sorts = a_filter check_open component in
  let* modules = sequence [
      (* INSTANTIATION *)
      Substitutions.gen component;
      UpSubsts.gen up_list;
      UpIds.gen up_list;
      IdLemmas.gen component;
      (* EXTENSIONALITY LEMMAS *)
      UpExtSubsts.gen up_list;
      ExtSubsts.gen component;
      (* COMPOSITIONALITY LEMMAS *)
      CompSubstSubsts.gen component;
      UpSubstSubstNoRens.gen up_list;
      LemmaCompSubstSubsts.gen component;
      LemmaInstIds.gen component;
      LemmaVarLs.gen var_sorts;
    ] in
  pure @@ AM.concat modules

(** This function delegates to all the different code generation functions and in the end
 ** aggregates all the returned vernacular commands. *)
let generate component up_list =
  let* common = gen_common component in
  (* a.d. DONE if one sort in a component has a non-zero substitution vector, all of them have?
   * Yes, if the component has only one sort, the statement is trivial
   * if the component has two or more sorts, then each sort's subsitution vector contains at least the other sorts fo the component. *)
  let* has_substs = map list_nempty (get_substv (List.hd component)) in
  if not has_substs
  (* return early and don't generate anything else *)
  then pure common
  else
    let* has_ren = hasRenamings (List.hd component) in
    (* let () = print_endline ("sort " ^ List.hd sorts ^ " has_ren " ^ string_of_bool has_ren) in *)
    let* lemmas = if has_ren
      then gen_lemmas component up_list
      else gen_lemmas_no_ren component up_list in
    let* is_gen_allfv = ask_gen_allfv in
    let* allfv_lemmas = if is_gen_allfv
      then AllfvGenerator.generate component up_list
      else pure AM.empty in
    pure (AM.concat [common; lemmas; allfv_lemmas])
