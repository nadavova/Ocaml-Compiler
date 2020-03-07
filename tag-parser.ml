#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;


let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  


let rec flat_pair pair = 
  match pair with
  | Pair(hd, tl) -> hd :: (flat_pair tl)
  | x -> x :: [];;

let rec flat_pair_nil pair = 
  match pair with
  | Pair(hd, tl) -> hd :: (flat_pair_nil tl)
  | Nil -> []
  | x -> x :: [];;


let vars_dot_vals vars_and_vals =
    let rec get_vals temp1 =
    (match temp1 with
     | (Pair (Pair(_, (Pair (x, Nil))), y))-> Pair(x, (get_vals y))
     | Nil -> Nil
     | (_) -> raise X_no_match) in
  let rec get_vars temp  =
    (match temp with
     | (Pair(Pair(x, (Pair(_, Nil))), y))-> Pair(x, (get_vars y))
     | Nil -> Nil
     | (_) -> raise X_no_match) in
  (get_vars vars_and_vals, get_vals vars_and_vals);;
  


let rec clean_n n = function
  | hd :: tl -> if n != 0 then  hd :: clean_n (n-1) tl else tl
  | [] -> [];;


let fix_symbol = function (exp) ->
                                 match exp with 
                                 | Symbol(x) -> x
                                 | (_) -> raise X_no_match;;

let check_vars vars = 
 (List.compare_lengths(List.sort_uniq compare vars) vars);;


let rec ast_parser sexpr =
  match sexpr with
      (*Constants*)
      |Bool(x) -> Const(Sexpr(Bool(x)))
      |Char(x) -> Const(Sexpr(Char(x)))
      |Number(x) -> Const(Sexpr(Number(x)))
      |Pair(Number(x),Nil) -> Const(Sexpr(Number(x)))     
      |String(x) -> Const(Sexpr(String(x)))
      |Nil -> Const(Void)
      |TagRef(s) -> Const(Sexpr(TagRef(s)))
      |TaggedSexpr(x,Pair(Symbol("quote"),Pair(Nil,Nil))) -> Const(Sexpr(TaggedSexpr(x,Nil)))
      |TaggedSexpr(x,sexpr) -> Const(Sexpr(TaggedSexpr(x,sexpr)))
      |Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
       (*Variables*)
      |Symbol(x) -> if List.mem x reserved_word_list 
          then raise X_no_match 
                    else Var(x)
      (*lambda *)
      |Pair(Symbol("lambda"), Pair(args, body)) -> (lambda_parser args body)
      (*Conditionals*)
      |Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(ast_parser test, ast_parser dit, Const(Void))
      |Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(ast_parser test, ast_parser dit, ast_parser dif)
      (*Let Expressions*)
      |Pair(Symbol("let"), x) -> slet_parser x
      |Pair(Symbol("let*"), x) -> sletStar_parser x
      |Pair(Symbol("letrec"), x) -> sletrec_parser x
      (*Defenitions*)
      |Pair(Symbol("define"),Pair(Pair(var,arglist),expr)) -> ast_parser (Pair(Symbol("define"),Pair(var,Pair(Pair(Symbol("lambda"),
                                                      Pair(arglist,expr)),Nil)))) 
      |Pair(Symbol("define"),Pair(name,Nil))->Def(ast_parser name,ast_parser Nil)
      |Pair(Symbol("define"),Pair(name,Pair(expr,Nil)))->Def(ast_parser name,ast_parser expr)
      (*Disjunctions*)
      |Pair(Symbol("or"),Nil) -> Const(Sexpr(Bool(false)))
      |Pair(Symbol("or"),Pair(x,Nil)) -> ast_parser(x)
      |Pair(Symbol("or"),x) -> 
        let rec dis_parse exp = 
          match exp with
            |Pair(x,Nil) -> [ast_parser(x)]
            |Pair(x,y) -> ast_parser(x) :: dis_parse(y)
            |(_) -> raise X_no_match in 
            Or(dis_parse(x))
      (*And*)
      |Pair(Symbol("and"),Nil) -> Const(Sexpr(Bool(true)))
      |Pair(Symbol("and"),Pair(x,Nil)) -> ast_parser(x)
      |Pair(Symbol("and"),Pair(x1,exprs)) -> ast_parser (Pair(Symbol("if"),Pair(x1,Pair(Pair(Symbol("and"),exprs),
                                                      Pair((Bool(false)), Nil)))))
      (*Assignments*)
      |Pair(Symbol("set!"),Pair(x,Nil)) -> raise X_no_match
      |Pair(Symbol("set!"),Pair(x,y)) -> 
        let rec set_parse exp = 
          match exp with
            |Pair(x,Nil) -> ast_parser(x)
            |Pair(x,y) -> set_parse(y)
            |(_) -> raise X_no_match in 
            Set(ast_parser(x),set_parse(y))
      (*Sequences*)
      |Pair(Symbol("begin"),Nil) -> Const(Void)
      |Pair(Symbol("begin"),x) -> seq_parse(x)
      (*Quasiquote*)
      |Pair(Symbol("quasiquote"),Pair(x, Nil)) -> quasiquote_parser (x) 
      |Pair(Symbol("cond"), x) -> (cond_expand x)
      (*Applications- this procedure must be the last!*)
      |Pair(x,y) -> (applic_parser x y)

      (*|(_) -> raise X_no_match*)

and seq_parse exp =
          match exp with
            |Pair(x,Nil) -> ast_parser(x)
            |Pair(x,y) -> Seq(List.map (fun (x) -> ast_parser x)(flat_pair_nil exp))
            |Nil -> Const (Void)
            |(_) -> raise X_no_match
                  
and cond_expand s  =
   (match s with
    | Pair(Pair(Symbol ("else"), x), Pair(y,Nil)) -> 
      (match x with
        | Nil -> (Const (Void))
        | (_) -> (seq_parse x))
    | Pair(Pair(Symbol ("else"), x), Nil) ->
       (match x with
        | Nil -> (Const (Void))
        | (_) -> (seq_parse x))
    | Pair (Pair (x, Pair(Symbol "=>" ,Pair(y,Nil))), z) ->
       (match z with
        | Nil -> (slet_parser(Pair(Pair(Pair(Symbol("value"), Pair(x, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"),
                      Pair(Nil, Pair(y, Nil))), Nil)), Nil)), Pair(Pair(Symbol("if"), Pair(Symbol("value"),
                      Pair(Pair(Pair(Symbol("f"), Nil),Pair(Symbol("value"), Nil)), Nil))), Nil))))           
        | (_) -> (slet_parser(Pair(Pair(Pair(Symbol("value"), Pair(x, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"),
                    Pair(Nil,Pair(y, Nil))), Nil)),Pair(Pair(Symbol("rest"),Pair(Pair(Symbol("lambda"),Pair(Nil, Pair(Pair(Symbol("cond"), z), Nil))), Nil)), Nil))),
                    Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil),Pair(Symbol("value"), Nil)),Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil)))))
    | Pair(Pair(x, y), z) -> (match z with
                                  | Nil -> If (ast_parser x, seq_parse y, Const (Void)) 
                                  | (_) -> If (ast_parser x, seq_parse y, cond_expand z))
    | _ -> raise X_no_match)


and slet_parser exp =
  match exp with
  | Pair (x, Nil) -> 
     let (vars, vals) = vars_dot_vals x in
     ast_parser((Pair((Pair((Symbol("lambda")),(Pair(vars, Nil)))),vals)))
  | Pair(x, y) ->
     let (vars, vals) = vars_dot_vals x in
     ast_parser(Pair(Pair(Symbol("lambda"),Pair(vars, y)),vals))
  | (_) -> raise X_not_yet_implemented

 and sletStar_parser exp =
  match exp with
  | Pair(Nil, body) -> 
     ast_parser (Pair(Symbol("let"), Pair(Nil, body)))
  | Pair(Pair(arg,Nil), body) -> 
     ast_parser (Pair(Symbol("let"), Pair(Pair(arg,Nil), body)))
  | Pair(Pair(head,tail), body) -> 
     ast_parser (Pair(Symbol("let"),Pair(Pair(head,Nil), Pair(Pair(Symbol("let*"),Pair(tail, body)),Nil))))
  | (_) -> raise X_not_yet_implemented

and sletrec_parser exp =
   match exp with
      | Pair(hd, tl) -> slet_parser (sletrec_aux hd tl)
      | (_) -> raise X_no_match 
  
and sletrec_aux hd tl =
    let rec get_tl temp temp1 =
    (match temp with
     | Pair(Pair(Symbol(x), y), z) ->
        Pair(Pair(Symbol("set!"), Pair(Symbol(x), y)),(get_tl z temp1))
     | (_) -> temp1) in
    let rec get_hd temp1 =
    (match temp1 with
     | Pair(Pair(Symbol(x), _),y) ->
        Pair(Pair(Symbol(x), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), (get_hd y))
     | (_) -> Nil) in
    Pair(get_hd hd, get_tl hd tl )   

    
and quasiquote_parser instance =
  match instance with
  |Bool(x) -> Const(Sexpr(Bool(x)))
  |Char(x) -> Const(Sexpr(Char(x)))
  |Number(x) -> Const(Sexpr(Number(x)))
  |String(x) -> Const(Sexpr(String(x)))
  |Symbol(x) -> Const(Sexpr(Symbol(x)))
  |Nil -> Const(Sexpr(Nil))
  |Pair(Symbol("unquote"), Pair(x, Nil)) -> ast_parser(x)
  |Pair(Pair(Symbol("unquote"), Pair(x, Nil)),Nil) -> 
    Applic(ast_parser(Symbol("cons")),[ast_parser(x);Const(Sexpr(Nil))])
  |Pair(Pair(Symbol("unquote"), Pair(x, Nil)),Pair(Symbol("unquote-splicing"), Pair(y, Nil))) -> 
    Applic (ast_parser (Symbol("cons")), [ast_parser(x); ast_parser(y)])
  |Pair(Pair(Symbol("unquote"), Pair(x, Nil)),y) -> 
    Applic(ast_parser(Symbol("cons")),[ast_parser(x); ast_parser(Pair(Symbol ("quasiquote"),Pair(y, Nil)))])
  |Pair(Symbol("unquote-splicing"), Pair(x, Nil)) -> raise X_no_match 
  |Pair(Nil,Nil)-> (ast_parser (Pair(Symbol("quote"), Pair(Nil, Nil))))
  |Pair(Symbol(x),Nil)-> 
    Applic(ast_parser(Symbol("cons")),[ast_parser(Pair(Symbol ("quote"),Pair(Symbol(x), Nil)));Const(Sexpr(Nil))])                                
  |Pair(Pair(Symbol("unquote-splicing"), Pair(x, Nil)), y) -> 
                                Applic (ast_parser (Symbol("append")), [(ast_parser x);(ast_parser (Pair(Symbol ("quasiquote"), Pair(y, Nil))))])
  |Pair(Pair(y,Pair(Symbol("unquote-splicing"), Pair(x, Nil))), Nil) -> 
                                Applic (ast_parser (Symbol("cons")), [(ast_parser (Pair(Symbol ("quasiquote"), Pair(y, Nil))));(ast_parser x)])
  |Pair(x,y)-> 
    Applic(ast_parser(Symbol("cons")),[ast_parser(Pair(Symbol ("quasiquote"),Pair(x, Nil))); ast_parser(Pair(Symbol ("quasiquote"),Pair(y, Nil)))])
  |(_) -> raise X_no_match 
   
and applic_parser x y =
  let list_y = flat_pair y in
  let last = List.partition(fun exp -> Nil = exp)  list_y  in
  let last = (fun(h,t) -> t) last in
  let len = (List.length(list_y)-1) in
  let bool = (List.nth (list_y) len = Nil) in
  let exprr =  match bool with
    | (true) -> List.map ast_parser (last)
    | (_) -> raise X_no_match in
  Applic(ast_parser x, exprr)
            
and lambda_parser args body =
  let list_args = flat_pair args in
  let list_body = flat_pair body in
  let last = List.partition(fun exp -> Nil = exp)  list_body  in
  let last = (fun(h,t) -> t) last in
  if(check_vars(list_args) = 0) then
    if (List.nth (list_args) (List.length(list_args) -1) = Nil) then
      (lambda_simple args body list_body last)
    else (lambda_opt args body list_body last)
  else raise X_syntax_error

and lambda_simple args body list_body last=
   let first = match body with
   | Pair(hd, tl) -> hd
   | (_) -> raise X_no_match in
   let flat = flat_pair args in
  let fixed_args =  (fun(hd,tl) -> tl)
                          (List.partition(fun (exp) -> Nil = exp) flat) in
  let strings_list = List.map fix_symbol fixed_args in 
  let exprr =  if (List.nth (list_body) (List.length(list_body)-1) = Nil) then
                 if List.length(last) = 1 then
                   ast_parser first
                  else
                    if List.length(last) = 0 then
                      raise X_no_match
                    else
                      Seq(List.map ast_parser (last))
               else raise X_no_match in
  LambdaSimple(strings_list, exprr)


  
and lambda_opt args body list_body last =
  let first = match body with
   | Pair(hd, tl) -> hd
   | (_) -> raise X_no_match in
  let flat = flat_pair args in
  let fixed_args =  (fun(hd,tl) -> tl)
                          (List.partition(fun (exp) -> Nil = exp) flat) in
  let strings_list = List.map fix_symbol fixed_args in 
  let nth_string = List.nth strings_list (List.length(strings_list) -1) in
  let shorter_list = clean_n (List.length(strings_list) -1) strings_list in
  let exprr = if List.length(last) = 1 
              then  ast_parser first
              else Seq(List.map ast_parser (last)) in
  LambdaOpt(shorter_list, nth_string, exprr)
  

let tag_parse_expression sexpr = (ast_parser sexpr);;
let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr);;


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)



module Tag_Parser : TAG_PARSER = struct


let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let tag_parse_expression sexpr = (ast_parser sexpr);;
let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr);;


end;; (* struct Tag_Parser *)
