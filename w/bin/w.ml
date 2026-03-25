(* ----------------------------------------- data types ----------------------------------------- *)
type lit =
  | Int of int64
  | Bool of bool
[@@deriving show]


and expression =
  | Variable of string
  | Abstraction of string * expression
  | Application of expression * expression
  | Let of string * expression * expression
  | Lit of lit
  | Tuple of expression list
[@@deriving show]


type wtype =
  | Variable of string (* the unknown *)
  | Arrow of wtype * wtype (* func (params -> return type) *)
  | Int
  | Bool
  | Tuple of wtype list
[@@deriving show]


(* again the unknown types which will be resolved during type inference *)
type type_variable = string
[@@deriving show]

(* hack to use it in a map type *)
module TypeVariableMap = Map.Make(struct
  type t = type_variable
  let compare = Stdlib.compare
end)


module TypeVariableSet = Set.Make(struct
  type t = type_variable
  let compare = Stdlib.compare
end)


(* real program variables *)
type term_variable = string
module TermVariableMap = Map.Make(struct
  type t = term_variable
  let compare = Stdlib.compare
end)


(* we use scheme as a generalization for polymorphic types *)
(* to be used as the values in the type environment *)
(* to allow let bound identifiers by polymorphic *)
type scheme = Forall of type_variable list * wtype
[@@deriving show]


(* the environment maps terms to polymorphic types *)
type environment = scheme TermVariableMap.t


(* we substitute type variables (the unknowns) with monotypes *)
type substitutions = wtype TypeVariableMap.t


type type_inference_state = {
  mutable counter : int;
}



(* ----------------------------------------- helpers ----------------------------------------- *)
let new_type_inference_state () : type_inference_state = {
  counter = 0
}


let fresh_type_variable(inference: type_inference_state) : type_variable =
  let var = Printf.sprintf "t%d" inference.counter in
  inference.counter <- inference.counter + 1;
  var



(* ----------------------------------------- substitutions ----------------------------------------- *)
(* materializing the solutions found by unification *)

(* substitute type within type *)
let rec substitute (t : wtype) (subs : substitutions) : wtype =
  match t with
  | Variable v -> TypeVariableMap.find_opt v subs  |> Option.value ~default:t
  | Arrow (t1, t2) -> Arrow (substitute t1 subs, substitute t2  subs)
  | Tuple (ts) -> Tuple (List.map (fun x -> substitute x subs) ts)
  | Int -> t
  | Bool -> t


let compose_substitutions (subs_a : substitutions) (subs_b : substitutions) : substitutions =
  let subs_a_fixed = TypeVariableMap.map (fun t -> substitute t subs_b) subs_a
                           (* func for conflict resolution *)
  in TypeVariableMap.union (fun _k v1 _v2 -> Some v1) subs_a_fixed subs_b


let substitute_in_scheme (subs : substitutions) (sch : scheme) : scheme =
  match sch with
  | Forall (type_var, mono_type) ->
    Forall (type_var, substitute mono_type subs)


let substitute_in_environment (env : environment) (subs : substitutions) : environment =
  TermVariableMap.map (substitute_in_scheme subs) env


let show_substitutions (subs : substitutions) : string =
  if TypeVariableMap.is_empty subs then
    "{}"
  else
    let bindings = TypeVariableMap.bindings subs in
    "{" ^
    (String.concat ", " (List.map (fun (v, t) ->
       Printf.sprintf "%s/%s" (show_wtype t) v
     ) bindings)) ^
    "}"



(* ----------------------------------------- unification ----------------------------------------- *)
(* unification is the root of the constraints solving. its product are the substitutions*)

type inference_tree = {
  rule     : string;
  input    : string;
  output   : string;
  children : inference_tree list;
}
[@@deriving show]
let make_tree (rule : string) (input : string) (output : string) (children : inference_tree list)
  : inference_tree =
  { rule; input; output; children }


let rec occurs_check (v : type_variable) (t : wtype) : bool =
  match t with
  | Variable name -> name = v
  | Arrow (t1, t2) -> occurs_check v t1 || occurs_check v t2
  | Tuple ts -> List.exists (occurs_check v) ts
  | Int | Bool -> false


exception TypeError of string


let rec unify (t1 : wtype) (t2 : wtype) : substitutions * inference_tree =
  let input = Printf.sprintf "%s ~ %s" (show_wtype t1) (show_wtype t2) in

  match (t1, t2) with
  | (Int, Int) | (Bool, Bool) ->
      let tree = make_tree "concrete" input "{}" [] in
      (* these are both concrete types so nothing to unify *)
      (TypeVariableMap.empty, tree)

  | (Variable v, t) when t = Variable v ->
      (* it's the same variable, nothing to unify *)
      let tree = make_tree "same-variable" input "{}" [] in
      (TypeVariableMap.empty, tree)

  | (Variable v, t) | (t, Variable v) ->
      if occurs_check v t then
        (* infinite type is just unrecoverable *)
        raise (TypeError (Printf.sprintf "occurs_check failed: %s occurs in %s" v (show_wtype t)))
      else
        (* not the same variable, so add a substitution from the var name to the type *)
        let subs = TypeVariableMap.singleton v t in
        let output = show_substitutions subs in
        let tree = make_tree "unify-variables" input output [] in
        (subs, tree)

  | (Arrow (a1, a2), Arrow (b1, b2)) ->
      (* this is s bit more nuanced than the rest but the idea is to basically *)
      (* first unify the params -> get substitution -> fix return types based on it -> unify return types *)
      (* -> compose the param substitution and return substitution into the final substitution *)
      let (s1, tree1) = unify a1 b1 in
      let a2' = substitute a2 s1 in
      let b2' = substitute b2 s1 in
      let (s2, tree2) = unify a2' b2' in
      let final_s = compose_substitutions s2 s1 in
      let output = show_substitutions final_s in
      let tree = make_tree "unify-arrows" input output [tree1; tree2] in
      (final_s, tree)

  | (Tuple ts1, Tuple ts2) ->
      (* unify in a zip-like manner *)
      if List.length ts1 <> List.length ts2 then
        raise (TypeError (Printf.sprintf "length mismatch: %d vs %d"
                          (List.length ts1) (List.length ts2)));

      let rec loop (current_subs : substitutions) (trees : inference_tree list)
                   (remaining1 : wtype list) (remaining2 : wtype list) =
        match remaining1, remaining2 with
        | [], [] -> (current_subs, List.rev trees)
        | t1 :: r1, t2 :: r2 ->
            let t1s = substitute t1 current_subs in
            let t2s = substitute t2 current_subs in
            let (s_new, tree) = unify t1s t2s in
            let new_subs = compose_substitutions s_new current_subs in
            loop new_subs (tree :: trees) r1 r2
        | _ -> assert false

      in
      let (final_subs, child_trees) = loop TypeVariableMap.empty [] ts1 ts2 in
      let output = show_substitutions final_subs in
      let tree = make_tree "unify-tuples" input output child_trees in
      (final_subs, tree)

  | _ ->
      raise (TypeError (Printf.sprintf "unify failure: %s and %s"
                        (show_wtype t1) (show_wtype t2)))



(* ------------------------------- generalization x instantiation ------------------------------- *)
let rec find_free_type_variables_in_type (t : wtype) =
  match t with
  | Variable name ->
      TypeVariableSet.singleton name
  | Arrow (p, r) ->
      TypeVariableSet.union (find_free_type_variables_in_type p) (find_free_type_variables_in_type r)
  | Int ->
      TypeVariableSet.empty
  | Bool ->
      TypeVariableSet.empty
  | Tuple tuples ->
      List.fold_left
        (fun acc t -> TypeVariableSet.union acc (find_free_type_variables_in_type t))
        TypeVariableSet.empty tuples


let find_free_type_variables_in_scheme (sch : scheme) =
  (* plan for scheme is to find all the ftvs in the scheme's mono type *)
  (* and filter out all the ones that are bound in the forall*)
  match sch with
  | Forall (bound_vars, t) ->
      let ftv_in_scheme = find_free_type_variables_in_type t in
      List.fold_left (fun s v -> TypeVariableSet.remove v s) ftv_in_scheme bound_vars


let find_free_type_vars_in_env (env : environment) : TypeVariableSet.t =
  TermVariableMap.fold
    (fun _name sch acc -> TypeVariableSet.union acc (find_free_type_variables_in_scheme sch))
    env TypeVariableSet.empty


let generalization (env : environment) (t : wtype) : scheme =
  (* generalization is basically just getting the types in T that could be made polymorphic *)
  (* we do this by simply diffing with the env *)
  (* then just return a new scheme with the unique vars *)
  let type_vars = find_free_type_variables_in_type(t) in
  let env_vars = find_free_type_vars_in_env(env) in
  let diff = TypeVariableSet.diff type_vars env_vars in
  let quantified_vars = TypeVariableSet.elements diff in

  Forall (quantified_vars, t)


let instantiate (sch : scheme) (infer_state : type_inference_state) : wtype =
  (* instantiate fresh vars for type vars within the scheme *)
  match sch with
  | Forall (vars, t) ->
    let subs =
      List.fold_left(fun sub var ->
          let fresh = fresh_type_variable (infer_state) in
          TypeVariableMap.add var (Variable fresh) sub
      ) TypeVariableMap.empty vars in

    substitute t subs



(* ----------------------------------------- inference ----------------------------------------- *)
exception UnboundVariable of string

let rec infer (state : type_inference_state) (env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Variable    _ -> infer_variable    state env expr
  | Abstraction _ -> infer_abstraction state env expr
  | Application _ -> infer_application state env expr
  | Let         _ -> infer_let         state env expr
  | Lit (Int _)   -> infer_literal_int state env expr
  | Lit (Bool _)  -> infer_literal_bool state env expr
  | Tuple       _ -> infer_tuple       state env expr


and infer_variable (state : type_inference_state) (env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Variable x ->
      (match TermVariableMap.find_opt x env with
       | None -> raise (UnboundVariable x)
       | Some scheme ->
           let t = instantiate scheme state in
           let rule   = "infer-variable" in
           let input  = show_expression expr in
           let output = show_wtype t in
           (TypeVariableMap.empty, t, make_tree rule input output []))
  | _ -> failwith "impossible: infer_variable called on non variable"


and infer_abstraction (state : type_inference_state) (env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Abstraction (param, body) ->
      let alpha = fresh_type_variable state in

      (* new env for param *)
      let param_scheme = Forall ([], Variable alpha) in
      let new_env = TermVariableMap.add param param_scheme env in

      (* infer body and populate new scheme with it *)
      let (s1, tau, body_tree) = infer state new_env body in

      (* sub param in body *)
      let alpha' = substitute (Variable alpha) s1 in
      let arrow_ty = Arrow (alpha', tau) in

      let rule   = "infer-abstraction" in
      let input  = show_expression expr in
      let output = show_wtype arrow_ty in
      let tree   = make_tree rule input output [body_tree] in

      (s1, arrow_ty, tree)

  | _ -> failwith "impossible: infer_abstraction called on non abstraction"


and infer_application (state : type_inference_state) (env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Application (func, arg) ->
      let (s1, t1, func_tree) = infer state env func in
      let env' = substitute_in_environment env s1 in
      let (s2, t2, arg_tree) = infer state env' arg in
      (* alpha will be the result *)
      let alpha = fresh_type_variable state in

      (* the body may have added constraints so we apply those aswell*)
      let t1' = substitute t1 s2 in

      (* body must equal t2 → α *)
      let (s3, unify_tree) = unify t1' (Arrow (t2, Variable alpha)) in

      let s = compose_substitutions s3 (compose_substitutions s2 s1) in

      let result_type = substitute (Variable alpha) s3  in

      let rule   = "infer-application" in
      let input  = show_expression expr in
      let output = show_wtype result_type in
      let tree   = make_tree rule input output [func_tree; arg_tree; unify_tree] in

      (s, result_type, tree)

  | _ -> failwith "impossible: infer_application called on non application"


and infer_let (state : type_inference_state) (env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Let (x, value, body) ->
      let (s1, t1, value_tree) = infer state env value in

      let env1 = substitute_in_environment env s1 in
      let t1'  = substitute t1 s1 in

      (* get a polymorphic scheme *)
      let scheme = generalization env1 t1' in
      let new_env = TermVariableMap.add x scheme env1 in

      (* type it *)
      let (s2, t2, body_tree) = infer state new_env body in

      let s = compose_substitutions s2 s1 in
      let rule = "infer-let" in
      let input = show_expression expr in
      let output = show_wtype t2 in
      let tree = make_tree rule input output [value_tree; body_tree] in

      (s, t2, tree)

  | _ -> failwith "impossible: infer_let called on non let"


and infer_literal_int (_state : type_inference_state) (_env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Lit (Int _) ->
      let rule   = "infer-int" in
      let input  = show_expression expr in
      let output = show_wtype Int in
      let tree   = make_tree rule input output [] in

      (TypeVariableMap.empty, Int, tree)

  | _ -> failwith "impossible: infer_int called on non int"


and infer_literal_bool (_state : type_inference_state) (_env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Lit (Bool _) ->
      let rule   = "infer-bool" in
      let input  = show_expression expr in
      let output = show_wtype Bool in
      let tree   = make_tree rule input output [] in

      (TypeVariableMap.empty, Bool, tree)

  | _ -> failwith "impossible: infer_bool called on non bool"


and infer_tuple (state : type_inference_state) (env : environment) (expr : expression)
  : substitutions * wtype * inference_tree =
  match expr with
  | Tuple exprs ->
      (* (current_subst, current_env, reversed_types, reversed_trees) *)
      let initial = (TypeVariableMap.empty, env, [], []) in

      let (final_subst, _, rev_types, rev_trees) =
        List.fold_left
          (fun (s_acc, env_acc, types_acc, trees_acc) e ->
            let (s_i, ty_i, tree_i) = infer state env_acc e in

            let env' = substitute_in_environment env_acc s_i in

            let s_new = compose_substitutions s_i s_acc in

            let ty_i' = substitute ty_i s_i in

            (s_new, env', ty_i' :: types_acc, tree_i :: trees_acc)
          )
          initial
          exprs
      in

      let tuple_type = Tuple (List.rev rev_types) in
      let child_trees = List.rev rev_trees in

      let rule   = "infer-tuple" in
      let input  = show_expression expr in
      let output = show_wtype tuple_type in
      let tree   = make_tree rule input output child_trees in

      (final_subst, tuple_type, tree)

  | _ -> failwith "impossible: infer_tuple called on non tuple"

(* ------------------------------------------------------------------------------------------ *)
(* testing *)

let test_substitute () =
  let subs = TypeVariableMap.singleton "t0" Int in

  (* t0 -> t1 *)
  let arrow = Arrow (Variable "t0", Variable "t1") in
  (* (t0, t1) *)
  let tuple = Tuple [Variable "t0"; Bool; Variable "t1"] in
  (* (t0, t2) -> t0 *)
  let nested = Arrow (Tuple [Variable "t0"; Variable "t2"], Variable "t0") in

  Printf.printf "Arrow  (t0 → t1)   [t0:=Int] → %s\n" (show_wtype (substitute arrow subs));
  Printf.printf "Tuple  [t0; Bool; t1] [t0:=Int] → %s\n" (show_wtype (substitute tuple subs));
  Printf.printf "Nested (t0,t2)→t0 [t0:=Int] → %s\n" (show_wtype (substitute nested subs));

  assert (substitute arrow subs = Arrow (Int, Variable "t1"));
  print_endline "substitute passed"


let test_compose () =
  (* s1: t0 := Int, t1 := t2 *)
  let s1 = TypeVariableMap.of_list [("t0", Int); ("t1", Variable "t2")] in
  (* s2: t2 := Bool *)
  let s2 = TypeVariableMap.singleton "t2" Bool in

  let composed = compose_substitutions s1 s2 in

  Printf.printf "After compose (s1 ∘ s2):\n";
  Printf.printf "  t0 := %s\n" (show_wtype (TypeVariableMap.find "t0" composed));
  Printf.printf "  t1 := %s\n" (show_wtype (TypeVariableMap.find "t1" composed));

  let t1_to_t3 = Arrow (Variable "t1", Variable "t3") in
  let after_composed = substitute t1_to_t3 composed in

  Printf.printf "Applied to (t1 → t3) → %s\n" (show_wtype after_composed);
  let s3 = TypeVariableMap.of_list [("t4", t1_to_t3); ("t3", Int)] in

  let s4 = compose_substitutions s3 composed in
  let t4_final = substitute (TypeVariableMap.find "t4" s4) s4 in

  Printf.printf "Final t4 after full composition → %s\n" (show_wtype t4_final);

  assert (t4_final = Arrow (Bool, Int));
  print_endline "compose_substitutions works hell yea"


let test_scheme_and_env () =
  let subs = TypeVariableMap.singleton "t0" Bool in

  let sch = Forall (["a"], Arrow (Variable "a", Variable "t0")) in
  let new_sch = substitute_in_scheme subs sch in
  (match new_sch with
   | Forall (vars, body) ->
       Printf.printf "scheme after sub: Forall.%s. %s\n" (String.concat "," vars) (show_wtype body));

  let env = TermVariableMap.empty
    |> TermVariableMap.add "x" (Forall ([], Variable "t0"))
    |> TermVariableMap.add "id" (Forall (["b"], Arrow (Variable "b", Variable "b"))) in

  let env2 = substitute_in_environment env subs in
  Printf.printf "environment after sub: x now has %s\n"
    (match TermVariableMap.find "x" env2 with Forall (_, t) -> show_wtype t);

  print_endline "substitute_in_scheme + substitute_in_environment passin"


let test_const () =
  (* let const = λx.λy.x *)
  (* in const 42 true*)
  let test_const_ast : expression =
    Let (
        "const",
        Abstraction ("x",
        Abstraction ("y", Variable "x")
        ),
        Application (
        Application (
            Variable "const",
            Lit (Int 42L)
        ),
        Lit (Bool true)
        )
    ) in

  let state : type_inference_state = { counter = 0 } in
  let env   : environment          = TermVariableMap.empty in

  let (_final_subst, inferred_type, _inference_tree) =
    infer state env test_const_ast
  in

  Printf.printf "Inferred type: %s\n" (show_wtype inferred_type);
  (* Printf.printf "Final substitution: %s\n" (show_substitutions final_subst);  (\* optional *\) *)
  (* Printf.printf "\nInference tree:\n%s\n" (show_inference_tree inference_tree); *)
  print_endline "const inference passin"


let test_id () =
  let test_id_ast : expression =
    Let (
      "id",
      Abstraction ("x", Variable "x"),               (* let λx.x *)
      Tuple [                                        (* in (id 42, id true) *)
        Application (Variable "id", Lit (Int 42L)) ;
        Application (Variable "id", Lit (Bool true))
      ]
    ) in

  let state : type_inference_state = { counter = 0 } in
  let env : environment = TermVariableMap.empty in

  let (_final_subst, inferred_type, _inference_tree) =
    infer state env test_id_ast
  in

  Printf.printf "Inferred type: %s\n" (show_wtype inferred_type);
  print_endline "id inference passed"

let () =
  print_endline "\n";

  print_endline "baseline substitute test:";
  test_substitute ();
  print_endline "-----------------------------------------";

  print_endline "baseline composition test:";
  test_compose ();
  print_endline "-----------------------------------------";

  print_endline "baseline scheme and env test:";
  test_scheme_and_env ();
  print_endline "-----------------------------------------";

  print_endline "const test:";
  test_const ();
  print_endline "-----------------------------------------";

  print_endline "const id:";
  test_id ();
  print_endline "-----------------------------------------";
