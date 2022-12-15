(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
   match exp with
   | Var v -> SS.singleton v
   | Num _ -> SS.empty
   | Bool _ -> SS. empty
   | Unop (_, x) -> free_vars x
   | Binop (_, x, y) -> SS.union (free_vars x) (free_vars y)
   | Conditional (x, y, z) -> SS.union (free_vars x) 
                             (SS.union (free_vars x) (free_vars z))
   | Fun (f, x) -> SS.diff (free_vars x) (SS.singleton f)
   | Let (f, def, bdy) -> SS.union (free_vars def) 
                         (SS.diff (free_vars bdy) (SS.singleton f))
   | Letrec (f, def, bdy) -> SS.diff (SS.union (free_vars def) (free_vars bdy)) 
                            (SS.singleton f)
   | Raise -> SS.empty
   | Unassigned -> SS.singleton "unassigned"
   | App (a, b) -> SS.union (free_vars a) (free_vars b) ;;
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)
let new_varname =
  let ctr = ref ~-1 in
  fun () -> ctr := !ctr + 1;
  "var" ^ (string_of_int (!ctr)) ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  if not (SS.mem var_name (free_vars exp)) then exp
  else 
    match exp with
    | Var v -> if v = var_name then repl else Var v
    | Num n -> Num n
    | Bool b -> Bool b
    | Unop (u, x) -> Unop (u, subst var_name repl x)
    | Binop (b, x, y) -> Binop (b, subst var_name repl x, subst var_name repl y)
    | Conditional (x, y, z) -> Conditional (subst var_name repl x, 
                                            subst var_name repl y, 
                                            subst var_name repl z)
    | Fun (f, x) -> if f = var_name then Fun (f, x)
                    else if not (SS. mem f (free_vars repl))
                    then Fun (f, subst var_name repl x)
                    else let y = new_varname () in
                         let subst_y = subst f (Var y) x in
                         Fun (y, subst var_name repl subst_y)
    | Let (f, def, bdy) -> if f = var_name then Let (f, subst var_name repl def, bdy)
                           else if not (SS.mem f (free_vars repl))
                           then Let (f, subst var_name repl def, subst var_name repl bdy)
                           else let y = new_varname () in
                                let subst_y = subst f (Var y) bdy in
                                Let (y, subst var_name repl def, 
                                        subst var_name repl subst_y)
    | Letrec (f, def, bdy) -> if f = var_name then Letrec (f, def, bdy)
                           else if not (SS.mem f (free_vars repl))
                           then Letrec (f, subst var_name repl def, subst var_name repl bdy)
                           else let y = new_varname () in
                                let subst_y_bdy = subst f (Var y) bdy in
                                let subst_y_def = subst f (Var y) def in
                                Letrec (y, subst var_name repl subst_y_def,
                                           subst var_name repl subst_y_bdy)
    | Raise -> Raise
    | Unassigned -> Unassigned
    | App (a, b) -> App (subst var_name repl a, subst var_name repl b) ;;

     
(*......................................................................
  String representations of expressions
 *)
   
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  let con_bin_hlp b x y : string = 
    (exp_to_concrete_string x) ^ (b) ^ (exp_to_concrete_string y) in
  match exp with
  | Var v -> v                         (* variables *)
  | Num n -> string_of_int n           (* integers *)
  | Bool b -> string_of_bool b         (* booleans *)
  | Unop (u, x) -> (match u with
    | Negate -> "~-" ^ (exp_to_concrete_string x))                (* unary operators *)
  | Binop (b, x, y) -> (match b with      (* binary operators *)
    | Plus -> con_bin_hlp " + " x y
    | Minus -> con_bin_hlp " - " x y
    | Times -> con_bin_hlp " * " x y
    | Equals -> con_bin_hlp " = " x y
    | LessThan -> con_bin_hlp " < " x y)
                                 
  | Conditional (x, y, z) -> "if " ^ (exp_to_concrete_string x) ^   
                             " then " ^ (exp_to_concrete_string y) ^
                             " else " ^ (exp_to_concrete_string z)      (* if then else *)
  | Fun (f, x) -> "fun " ^ f ^ " -> " ^ (exp_to_concrete_string x)                  (* function definitions *)
  | Let (f, def, bdy) -> "let " ^ f ^ " = " ^ exp_to_concrete_string def ^
                         " in " ^ (exp_to_concrete_string bdy)          (* local naming *)
  | Letrec (f, def, bdy) -> " let rec" ^ f ^ " = " ^ (exp_to_concrete_string def) ^
                            " in " ^ (exp_to_concrete_string bdy)       (* recursive local naming *)
  | Raise -> "raise"                               (* exceptions *)
  | Unassigned -> "unassigned"                     (* (temporarily) unassigned *)
  | App (a, b) -> (exp_to_concrete_string a) ^ " " ^ (exp_to_concrete_string b) ;; 
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  let abs_bin_hlp b x y : string = 
    "Binop (" ^ b ^ ", " ^ (exp_to_abstract_string x) ^ 
    ", " ^ (exp_to_abstract_string y) ^ ")" in
  match exp with
  | Var v -> "Var " ^ v                       (* variables *)
  | Num n -> "Num " ^ (string_of_int n)         (* integers *)
  | Bool b -> "bool " ^ (string_of_bool b)      (* booleans *)
  | Unop (u, x) ->       (* unary operators *)
    (match u with 
    | Negate -> "Unop Negate, " ^ (exp_to_abstract_string x) ^ ")")  
     
  | Binop (b, x, y) ->   (* binary operators *)
    (match b with
    | Plus -> abs_bin_hlp "Plus" x y
    | Minus -> abs_bin_hlp "Minus" x y
    | Times -> abs_bin_hlp "Times" x y
    | Equals -> abs_bin_hlp "Equals" x y
    | LessThan -> abs_bin_hlp "LessThan" x y)

  | Conditional (x, y, z) -> "Conditional (" ^ (exp_to_abstract_string
                             x) ^ ", " ^ (exp_to_abstract_string y) ^ ", "
                             ^ (exp_to_abstract_string y) ^ ", " ^
                             (exp_to_abstract_string y) ^ ")"    (* if then else *)
  | Fun (f, x) -> "Fun (" ^ f ^ ", " ^ (exp_to_abstract_string x)                (* function definitions *)
  | Let (f, def, bdy) -> "Let (" ^ f ^ ", " ^ (exp_to_abstract_string def)
                         ^ (exp_to_abstract_string bdy) ^ ")"           (* local naming *)
  | Letrec (f, def, bdy) -> "Letrec (" ^ f ^ ", " ^ (exp_to_abstract_string
                            def) ^ ", " ^ (exp_to_abstract_string bdy) ^ ")"       (* recursive local naming *)
  | Raise -> "Raise"                           (* exceptions *)
  | Unassigned -> "Unassigned"                          (* (temporarily) unassigned *)
  | App (a, b) -> "App (" ^ (exp_to_abstract_string a) ^ ", " ^
                  (exp_to_abstract_string b) ^ ")" ;;      (* function applications *)
