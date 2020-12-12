open Base
open Util

module M = Monadic
module H = Hsig
module AL = AssocList

type 'a wrapped = 'a M.Result.Make(String).t
type 'a actual_t = H.t -> 'a M.Result.Make(String).t

module RE = M.Reader.MakeT(ErrorM)(struct type t = H.t end)

include RE

let ask = peek
let asks f = f <$> ask

let error s = ErrorM.error s |> elevate

include M.Monad.ApplicativeFunctionsList(RE)
include M.Monad.MonadFunctionsList(RE)
include Monads.ExtraFunctionsList(RE)

(** In the following we collect the functions that are used either in
 ** code generation or signature graph generation.
 ** TODO implement signature graph generation in dot format.
 ** The ocamlgraph library seems to support it ootb *)
open RE.Syntax

(** return non-variable constructors of a sort *)
let constructors sort =
  let* spec = asks H.sigSpec in
  match AL.assoc sort spec with
  | Some cs -> pure cs
  | None -> error @@ "constructors called with unknown sort " ^ sort

(** return the substitution vector for a sort *)
let substOf sort =
  let* substs = asks H.sigSubstOf in
  match AL.assoc sort substs with
  | Some substSorts -> pure substSorts
  | None -> error @@ "substOf called with unknown sort " ^ sort

(** check whether a sort has a variable constructor *)
let isOpen sort =
  let* opens = asks H.sigIsOpen in
  pure @@ Set.mem opens sort

(** A sort is definable if it has any constructor *)
let definable sort =
  let* b = isOpen sort in
  let* cs = constructors sort in
  pure (b || not (List.is_empty cs))

(** check if a sort has a substitution vector *)
let hasArgs sort = (fun l -> List.is_empty l |> not) <$> substOf sort

(** return the arguments (all sorts in head positions) of a sort *)
let getArguments sort =
  let* args = asks H.sigArguments in
  match AL.assoc sort args with
  | Some ts -> pure ts
  | None -> error @@ "arguments called with unknown sort" ^ sort

(** return all components *)
let getComponents = asks H.sigComponents

(** return all known sorts *)
let getAllSorts = List.concat <$> getComponents

(** get the component that a sort belongs to *)
let getComponent s =
  let* components = asks H.sigComponents in
  pure @@ List.(concat @@ filter_map components ~f:(fun component ->
      if List.mem component s ~equal:String.equal
      then Some component
      else None))

(** Check if the arguments of the first sort of a components and the component itself overlaps
 ** TODO why check only for the first sort? *)
let isRecursive xs =
  if (List.is_empty xs) then error "Can't determine whether the component is recursive."
  else let* args = getArguments (List.hd_exn xs) in
    list_intersection xs args |> List.is_empty |> not |> pure

(** get all the bound sorts that appear in a component *)
let boundBinders component =
  let* constructors = a_concat_map constructors component in
  let binders =
    let open Monadic.List.Make.Syntax in
    let* H.{ cpositions; _ } = constructors in
    let* H.{ binders; _ } = cpositions in
    let* binder = binders in
    H.getBinders binder in
  pure binders

(** A sort needs renamings
 ** either if it is an argument in a sort of a different component that needs renamings
 ** or if any sort of the component appears as a binder in the component  *)
let rec hasRenamings sort =
  let* component = getComponent sort in
  let* boundBinders = boundBinders component in
  let* all_types = getAllSorts in
  let all_other_types = list_diff all_types component in
  let* occ = a_filter (fun sort' ->
      let* arguments' = getArguments sort' in
      pure @@ List.mem arguments' sort ~equal:String.equal)
      all_other_types in
  (* TODO that is not structural recursion. But it probably terminates. We might have to additionally keep track of all previously visited components. *)
  let* bs = a_map hasRenamings occ in
  let xs_bb = list_intersection component boundBinders |> List.is_empty |> not in
  let bs' = list_any id bs in
  pure (xs_bb || bs')
