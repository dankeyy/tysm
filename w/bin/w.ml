type lit =
  | Int of int64
  | Bool of bool
[@@deriving show]


and expr =
  | Variable of string
  | Abstraction of string * expr
  | Application of expr * expr
  | Let of string * expr * expr
  | Lit of lit
  | Tuple of expr list
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


let new_type_inference_state () : type_inference_state = {
  counter = 0
}


let fresh_type_variable(inference: type_inference_state) : type_variable =
  let var = Printf.sprintf "t%d" inference.counter in
  inference.counter <- inference.counter + 1;
  var


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
