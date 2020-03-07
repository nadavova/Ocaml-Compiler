#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;


type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_box_failed1;;
exception X_box_failed2;;
exception X_box_failed3;;
exception X_box_failed4;;
exception X_box_failed5;;
exception X_box_failed6;;
exception X_lambda_failed
exception X_tail_failed1
exception X_list_empty_shouldnt_happen


type 'a pointer = Null | Pointer of 'a ref;;

		 
let rec list_not_contains element =
    function a::c -> if (a = element) then false else  (list_not_contains element c)
                                   | []   -> true
;;

let rec list_contains element =
    function a::c -> if (a = element) then (list_contains element c) else true
                                   | []   -> false
;;


let rec list_contains_rev  =
    function a::c -> if (a) then true else  (list_contains_rev  c)
                                   | []   -> false    
  ;;

  
  let rec list_contains_aux element =
    function a::c -> if (a = element) then true else  (list_contains_aux element c)
                                   | []   -> false
;;


let rec list_contains_add element list =
  if (list_contains_aux element list) then list else []
;;


let rec list_index_number expr env_list index =
      (match env_list with
           | [] -> raise X_no_match
           | hd :: tl -> (match (hd = expr) with
                         | true -> index
                         | (_) ->  (list_index_number expr tl (1 + index))));;

let body_ref_list_handlerer = ref 0;;

let rec unfold f x =
  match f x with
  | None -> []
  | Some (y, x') -> y :: unfold f x';;

let mapa f = unfold (function [] -> None | x::xs -> Some (f x, xs));;

let list_append xs ys zs = (List.rev_append (List.rev xs) (List.rev_append (List.rev ys) zs)) ;; 

                            
(*addressing helper*)
  let var_addressing var lex =
    (match  (list_contains_aux var (List.hd lex)) with
     | true -> VarParam(var, list_index_number var (List.hd lex) 0)
     | false -> let bound_or_free = List.filter (fun( aux ) -> if (List.length aux > 0) then true else false) (List.map (fun( x )-> list_contains_add var x) (List.tl lex)) in
                      if(List.length bound_or_free > 0)
                      then VarBound(var, list_index_number (List.hd bound_or_free) (List.tl lex) 0 , list_index_number var (List.hd bound_or_free) 0)
                        else VarFree(var))
;;                            

                                           
  let rec var_box indicator body _bound =
     let rec set_box _bound indicator _expr  =
    (match _bound , _expr with
     | true, Set'(Var'( VarBound(repack, major, minor)), to_set) ->
        if (repack <> indicator)
        then Set'( Var'( VarBound(repack, major, minor)),(var_box indicator to_set _bound))
        else  BoxSet'(VarBound(repack, major, minor),(var_box indicator to_set _bound)) 
     | false, Set'(Var'(VarBound(repack, major, minor)), to_set) ->  Set'(Var'(VarBound(repack, major, minor)), (var_box indicator to_set _bound))                                            
     | true, Set'(Var'(VarParam(repack, minor)),to_set) ->
        (match _bound, repack with
         | true, indicator -> BoxSet'( VarParam(repack, minor),(var_box indicator to_set _bound))
         |(_), (_) -> Set'( Var'(VarParam(repack, minor)),(var_box indicator to_set _bound)))
     | false, Set'(Var'( VarParam(repack, minor)), to_set) -> Set'(Var'(VarParam(repack, minor)),(var_box indicator to_set _bound))
     | (_), Set'(x, y) -> Set'((var_box indicator x _bound), (var_box indicator y _bound))
     | _ -> raise X_box_failed3) in
    (match body with
     | Const'(x) -> Const' (x)
     | Var'(_expr) -> (match _bound,_expr with
     | true, (VarBound(repack, major, minor)) ->
        if(repack <> indicator) then  Var'(VarBound(repack, major, minor))
        else  BoxGet'(VarBound(repack, major, minor))
     |false, (VarBound(repack, major, minor)) -> Var'(VarBound(repack, major, minor))
     | true, (VarParam(repack, minor)) -> 
        if (repack <> indicator) then 
          Var'(VarParam(repack, minor))
        else  BoxGet'(VarParam(repack, minor))
     |false, (VarParam(repack, minor)) -> Var'(VarParam(repack, minor))
  | (_),(VarFree( repack)) -> Var'(VarFree( repack)))
     | If' (test, dit, dif) -> If' (var_box indicator test _bound,var_box indicator dit _bound,var_box indicator dif _bound)
     | Seq' (list) -> Seq' (mapa (fun (x) ->var_box indicator x _bound) list)
     | Set' (_, _) -> set_box _bound indicator body 
     | Or' (list) -> Or' (mapa (fun (x) ->var_box indicator x _bound) list)    
     | LambdaSimple'(args, to_set) -> (match _bound with
                               |true ->  LambdaSimple'(args, (var_box indicator to_set (list_not_contains indicator args)))
                               |false -> LambdaSimple'(args, (var_box indicator to_set _bound)))
     | LambdaOpt'(args, opt, to_set) -> (match _bound with
                               |true ->  LambdaOpt'(args, opt, (var_box indicator to_set (list_not_contains indicator (list_append args [opt] []))))
                               |false -> LambdaOpt'(args, opt, (var_box indicator to_set _bound)))                          
     | Applic' (procedure, sexprs) -> Applic'(var_box indicator procedure _bound, (mapa (fun (x) ->var_box indicator x _bound) sexprs))
     | ApplicTP'(procedure, sexprs) -> ApplicTP'(var_box indicator procedure _bound, (mapa (fun (x) ->var_box indicator x _bound) sexprs))
     | Box'(y) -> Box'(y)
     | BoxGet'(y) -> BoxGet'(y)
     | BoxSet'(y, to_set) -> BoxSet'(y,(var_box indicator to_set _bound))
     | (_) -> raise X_box_failed4)
    ;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct


  let rec lexical_addressing exp env = 
  match exp with
    | Const(sexpr) -> Const'(sexpr)
    | Var(name) -> Var'( if env = [] then VarFree(name) else var_addressing name env)
    | If(_test, _then, _else) -> If'(lexical_addressing _test env, lexical_addressing _then env, lexical_addressing _else env)
    | Seq(expList) -> Seq'(List.map (fun (exp) -> lexical_addressing exp env) expList )
    | Set(var,newVal) -> Set'(lexical_addressing var env, lexical_addressing newVal env)
    | Def(var, vall) -> Def'(lexical_addressing var env, lexical_addressing vall env)
     | Or(expList) -> Or'(List.map (fun (exp) -> lexical_addressing exp env) expList )
     | LambdaSimple(vars, body) -> LambdaSimple'(vars, lexical_addressing body (List.cons vars env))
     | LambdaOpt(vars, optVar, body) -> 
        let conc = (List.rev (List.cons optVar (List.rev vars))::env) in
        LambdaOpt'(vars, optVar, lexical_addressing body conc)
    | Applic(func ,expList) -> Applic'(lexical_addressing func env, (List.map (fun (exp) -> lexical_addressing exp env) expList));;
  ;;
 
 
let rec annotating_tail_calls _expr tp =
      match _expr, tp with
      | Const'(x), false -> Const'(x)
      | Const'(x), true -> Const'(x) 
      | Var'(var), false -> Var'(var)
      | Var'(var), true -> Var'(var)
      | Set'(arg,to_set), false-> Set'(annotating_tail_calls arg tp, annotating_tail_calls to_set false)
      | Set'(arg,to_set), true-> Set'(annotating_tail_calls arg tp, annotating_tail_calls to_set false)
      | Applic' (func, l), true ->  ApplicTP'((annotating_tail_calls func false), List.map (fun (x) -> annotating_tail_calls x false) l)
      | Applic' (func, l), false ->  Applic'((annotating_tail_calls func false), List.map (fun (x)-> annotating_tail_calls x false) l)
      | Def'(name , body), false -> Def'((annotating_tail_calls name tp), annotating_tail_calls body tp)
      | Def'(name , body), true -> Def'((annotating_tail_calls name tp), annotating_tail_calls body tp)
      | Seq'(seq), false -> or_seq_handler seq false
      | Seq'(seq), true-> or_seq_handler seq false
      | LambdaSimple'(args, body), false-> LambdaSimple'(args, annotating_tail_calls body true)
      | LambdaOpt'(args, opt, body),false-> LambdaOpt'(args, opt, annotating_tail_calls body true)
      | LambdaSimple'(args, body), true-> LambdaSimple'(args, annotating_tail_calls body true)
      | LambdaOpt'(args, opt, body), true-> LambdaOpt'(args, opt, annotating_tail_calls body true)
      | If'(_test, _then, _else), false-> If' (annotating_tail_calls _test false, annotating_tail_calls _then tp, annotating_tail_calls _else tp)
      | If'(_test, _then, _else), true-> If' (annotating_tail_calls _test false, annotating_tail_calls _then tp, annotating_tail_calls _else tp)
      | Or'(orr), false -> or_seq_handler orr true
      | Or'(orr), true-> or_seq_handler orr true
      | _, _ -> raise X_tail_failed1
    
and or_seq_handler handle bool =
  let hd = List.map (fun (exp) -> annotating_tail_calls exp false) (remove_last_element handle) in
  let tl = annotating_tail_calls (last_element handle) true in
  match bool with
   |true ->
     Or'(list_append hd [tl] [])
   |false ->
     Seq'(list_append hd [tl] [])
  
  and last_element list = 
    match list with 
       | [] ->raise X_list_empty_shouldnt_happen
       | [x] -> x
       | first_el::rest_of_list -> last_element rest_of_list

  and remove_last_element list =
    match list with 
    | [] -> []
    | [x] -> []
    |  first_el::rest_of_list -> List.cons first_el  (remove_last_element rest_of_list) ;;
;;



let rec boxing_of_variables box_var =
let container = fun(body)-> (fun (args) -> (read_write args body)) in
    (match box_var with
        | Const'(var) -> Const'(var) 
        | Var'(var) -> Var'(var)
        | Box'(var) -> Box'(var)
        | BoxGet'(var) -> BoxGet'(var)
        | BoxSet'(var, to_set) -> BoxSet'(var, (boxing_of_variables to_set))
        | If'(_test, _then, _else) -> If'(boxing_of_variables _test,boxing_of_variables _then,boxing_of_variables _else)
        | Seq'(list_expr) ->  Seq'(mapa (fun (aux) ->boxing_of_variables aux) list_expr)
        | Set'(name, value) -> Set'(boxing_of_variables name, boxing_of_variables value)  
        | Def'(name, value) -> Def'(boxing_of_variables name, boxing_of_variables value)
        | Or'(list_expr) -> Or'(mapa (fun (temp) -> boxing_of_variables temp) list_expr)
        |LambdaSimple'(args, body) ->  let iter =  (mapa (container body) args) in check_if_box box_var iter true  
        |LambdaOpt'(args, opt, body) -> let app = list_append args [opt] [] in let iter = (mapa (container body) app) in check_if_box box_var iter true
        | Applic'(func, exp_list) -> Applic'(boxing_of_variables func, (mapa (fun (aux ) -> boxing_of_variables aux) exp_list))
        | ApplicTP'(func, exp_list) -> let app = boxing_of_variables func in let mapper = mapa boxing_of_variables exp_list in ApplicTP'(app, mapper))

		
  and check_if_box box expr_list bool=
    (match bool with
    |true -> (match box with
              | LambdaOpt'(args, opt, body) ->
                 let app = list_append args [opt] [] in
                 let updated =  boxing_of_variables (change_lambda body app expr_list) in
                 LambdaOpt'(args, opt, updated)
              | LambdaSimple'(args, body) ->
                 let updated = boxing_of_variables (change_lambda body args expr_list) in
                 LambdaSimple'(args, updated)
              | (_) -> raise  X_lambda_failed)
    |_ -> raise  X_lambda_failed)
    
  and change_lambda body args expr_list =
    let args_aux =args in
        (match  Seq'(set_box_rec body args args_aux expr_list 2 ) with
                         | Seq'([]) -> aux_lambda body args args_aux expr_list 1 
                         | Seq'(exp_lst) ->
                            let add_lambda_box = aux_lambda body args args_aux expr_list 1 in
                            let app = List.append exp_lst [add_lambda_box] in
                            Seq'(app)
                         | _ -> raise X_lambda_failed) 
          
  and read_write arg body =
     let ref_to = (boxing_cases false arg body true true (ref 0)) in
       let ref_from = (boxing_cases true arg body true true  (ref 0)) in
       let too = read_or_write ref_to ref_from true in
       let from = read_or_write ref_to ref_from false in
       match  (list_contains_rev too),  (list_contains_rev from) with
       |(true,_) -> "true"
       |(_,true) -> "true"
       |(_) -> "false"

     
and read_or_write ref_to ref_from direction =
  match direction with
  | true ->  (mapa (fun (x) -> (list_contains x ref_to)) ref_from)
  | false -> (mapa (fun (x) -> (list_contains x ref_from)) ref_to)
            
   and set_box_rec body args args_aux lst_check ref_list_handler=
     (match ref_list_handler, lst_check with
      | 2,[] -> []
      | 2,first_hd :: first_tl -> (match first_hd,args_aux with
                     |(_), [] -> []
                     |"true", second_hd :: second_tl -> let index = (list_index_number second_hd args 0) in
                                   let add_lambda_box =  set_box_rec body args second_tl first_tl 2 in
                                   let var_param = VarParam(second_hd, index) in
                                   let set_var = Set'(Var'(var_param),Box'(var_param)) in
                                   let app = list_append [set_var] add_lambda_box [] in
                                   app
                 |"false", second_hd :: second_tl -> set_box_rec body args second_tl first_tl 2
                 |(_) -> raise X_lambda_failed)
     |_ -> raise  X_lambda_failed)


   and aux_lambda body args args_aux lst_check ref_list_handler =
    (match ref_list_handler,lst_check with
     | 1,[] -> body
     | 1,first_hd :: first_tl -> (match first_hd, args with
                           | "true", [] -> body
                           | "true", second_hd :: second_tl -> aux_lambda (var_box second_hd body true) second_tl args_aux first_tl 1
                           | "false",[] -> body
                           | "false",second_hd :: second_tl -> aux_lambda body second_tl args_aux first_tl 1
                           |(_) ->raise  X_lambda_failed)
     |_ -> raise  X_lambda_failed)

          
   and lambda_handler read_or_write indicator _expr _param _bound ref_list_handler=
     let auxiliary bool  body param ref_list = (boxing_cases read_or_write indicator body bool (list_not_contains indicator param) ref_list) in
     let ref_aux = ref_list_handler in ( ref_list_handler := (1 + !ref_list_handler)) ;
       (match _expr,_param, _bound with
        | LambdaSimple'(args, body),true, (_) ->  (auxiliary false body args ref_list_handler)
        | LambdaSimple'(args, body), (_), true ->  (auxiliary  _param body args ref_list_handler)
        | LambdaSimple'(args, body),(_), (_) -> (boxing_cases read_or_write indicator body _param _bound ref_list_handler)
        | LambdaOpt'(args, opt, body),true, (_) ->  (auxiliary false body (list_append args [opt] [] ) ref_aux)
        | LambdaOpt'(args, opt, body),(_) , true -> (auxiliary _param body (list_append args [opt] []) ref_list_handler)
        | LambdaOpt'(args, opt, body),(_), (_) -> (boxing_cases read_or_write indicator body _param _bound ref_list_handler)
        | _ -> raise X_lambda_failed)

		
   and set_handler read_or_write args body _param _bound ref_list =
    let auxiliary bool mod_body = boxing_cases bool args mod_body _param _bound ref_list in
    (match read_or_write, body with
     | true, Set'( Var'( VarBound( repack, major, minor) ), to_set) ->
        (match _bound, args with
         |true, repack -> auxiliary true to_set
         |(_) , (_) ->  list_append (auxiliary true (Var'(VarBound(repack, major,minor)))) (auxiliary true to_set) [])
     | false, Set'( Var'( VarBound(repack, major, minor) ), to_set) ->
        if ((args = repack) && _bound)
                                              then list_append [!ref_list] (auxiliary false to_set) []
                                              else auxiliary false to_set
         | (_),Set'( Var'( VarParam(repack, minor)), to_set) -> (match read_or_write, _param, args, _bound with 
							| false, true, repack, _ -> list_append [0] (auxiliary false to_set) []
							| false, _ , _ , _-> auxiliary false to_set
							| true, true, repack , true-> auxiliary true to_set
							| true, _, _ ,false -> list_append (auxiliary true (Var'(VarParam(repack ,minor)))) (auxiliary true to_set) []
							|(_) -> auxiliary false to_set)
         | (_), Set'(x, y) -> list_append (auxiliary read_or_write x) (auxiliary read_or_write y ) [] 
         | _ -> raise X_box_failed6)

and  boxing_cases read_or_write indicator _expr _param _bound ref_list_handler =
  let com bool vpn = boxing_cases bool indicator vpn _param _bound ref_list_handler in
  let fold bool l = (List.fold_left (fun hd tl-> list_append hd tl []) [] (mapa (fun (x) -> (com bool x)) l)) in
    match read_or_write, _expr with
     | _, Const'(var) -> []
     | false, Var'(var)-> []
     | true, Var'(var)-> (match _expr with
                        | Var'(VarParam(repack, minor)) ->
                           if (_param) then
                             if (repack <> indicator) then []
                             else [0]
                               else []
                        | Var'(VarBound(repack, major, minor)) ->
                              if (_bound) then
                             if (repack <> indicator) then []
                             else [!ref_list_handler]
                               else []
                        | Var'(VarFree(_)) -> []
                        | _ -> raise X_box_failed1)	                     
     | true, If'(test, _then, _else) -> (list_append (com true test)  (com true _then ) (com true _else))
     | false, If'(test, _then, _else) -> list_append (com false test) (com false _then ) (com false _else)  
     | true, Seq'(l) ->  fold true l    
     | false, Seq'(l) ->  fold false l
     | true, Def'(x, y) -> raise X_syntax_error
     | true, Set'(var, to_set) -> (set_handler read_or_write indicator _expr _param _bound ref_list_handler)
     | false, Set'(var, to_set) -> (set_handler read_or_write indicator _expr _param _bound ref_list_handler)
     | true, Or'(l) -> fold true l 
     | false, Or'(l) -> fold false l 
     | true, LambdaSimple'(args, body) -> lambda_handler read_or_write indicator _expr _param _bound ref_list_handler
     | false, LambdaSimple'(args, body) -> lambda_handler read_or_write indicator _expr _param _bound ref_list_handler
     | true, LambdaOpt'(args, opt, body) -> lambda_handler read_or_write indicator _expr _param _bound ref_list_handler
     | false, LambdaOpt'(args, opt, body) -> lambda_handler read_or_write indicator _expr _param _bound ref_list_handler
     | true, Applic'(app, l) -> list_append (com true app) (fold true l) []
     | false, Applic'(app, l) -> list_append (com false  app) (fold false l) []
     | true, ApplicTP'(app, l) -> list_append (com true app) (fold true l) []
     | false, ApplicTP'(app, l) -> list_append (com false app) (fold false l) []
     | _, Box'(var) -> []
     | _, BoxGet'(var) -> []
     | true, BoxSet'(var, to_set) -> (com true to_set)
     | false, BoxSet'(var, to_set) -> (com false to_set)
     | (_) -> raise X_box_failed2
                                
;;

let annotate_lexical_addresses e = lexical_addressing e [];;

let annotate_tail_calls e = annotating_tail_calls e false;;

let box_set e = boxing_of_variables e (*raise X_not_yet_implemented*);;

let run_semantics expr =
   box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
