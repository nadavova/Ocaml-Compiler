#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (int * constant * string) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate :  (int * constant * string) list -> (string * int) list -> expr' -> string
 
end;;

exception X_scan_ast_failed
exception X_create_constants_failed
exception X_generate_failed
exception X_map_table_add_tagged
exception X_set_failed
exception  X_def_failed
let list_append xs ys zs = (List.rev_append (List.rev xs) (List.rev_append (List.rev ys) zs)) ;; 


(* Constructing the constants-table stage 1 - scan_ast *)
let rec scan_ast sexpr consts =
  let scan_fold l c =  List.fold_left(fun hd tl -> list_append hd (scan_ast tl c ) [] ) [] l in
  match  sexpr with
  | Const'(var) ->  [var]@ consts 
        | Var'(var) -> consts
        | If'(_test, _then, _else) -> (list_append (scan_ast _test consts)  (scan_ast _then consts) (scan_ast _else consts))
        | Seq'(list_expr) -> scan_fold list_expr consts
        | Or'(list_expr) -> scan_fold list_expr consts
        | Set'(name, value) -> list_append (scan_ast name consts) (scan_ast value consts) []
        | Def'(name, value) -> list_append (scan_ast name consts) (scan_ast value consts) []
        | LambdaSimple'(args, body) -> scan_ast body consts
        | LambdaOpt'(args, opt, body) -> scan_ast body consts
        | Applic'(func, exp_list) -> (list_append (scan_ast func consts) ( scan_fold exp_list consts) [])
        | ApplicTP'(func, exp_list) -> (list_append (scan_ast func consts) ( scan_fold exp_list consts) [])
        | Box'(var) -> consts
        | BoxGet'(var) -> consts
        | BoxSet'(var, to_set) -> scan_ast to_set consts
;;


(* Constructing the constants-table stage 2 - convert_to_set *)

let remove_elt e l =
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x::xs when e = x -> go xs acc
    | x::xs -> go xs (List.cons x acc)
  in go l [];;


let convert_to_set l =  
  let rec go l acc = match l with
    | [] -> List.rev acc
    | x :: xs -> go (remove_elt x xs) (List.cons x acc)
  in go l [];;


(* Constructing the constants-table stage 3 - extend_consts, from the recitation class *)
  let rec extend_sym consts =
    (match consts with
     |Sexpr(sexpr)->
       (match sexpr with
                  | Pair(hd, tl)-> list_append (extend_sym (Sexpr(hd)))  (extend_sym (Sexpr(tl))) [consts]
                  | Symbol(sym)-> list_append [Sexpr(String(sym))] [consts] []
                  | TaggedSexpr(tag, expr) -> list_append (extend_sym (Sexpr(expr))) [consts] [] (* im not sure if this line is necessary, maybe error here *)
                  |(_)-> [consts]
       )
     |_else->[_else]
    ) 
 ;;


let extend_consts consts =
   List.fold_right (fun hd tl-> list_append (extend_sym hd) tl []) consts [] ;;


(* Constructing the constants-table stage 4 - expand_to_include_sub_constants *)
(*sort_uniq - same as List.sort, but also remove duplicates*)


(* Constructing the constants-table stage 5 - create_constants_table *)

let offset = ref 0;;

(* if tests fails, try to implement topologic sort? *)
let map_table consts_list =
  let offset_map = ref (List.map (fun(v) ->  (v, -1)) consts_list) in
  let rec create_constants_table consts_list =
  (match consts_list with
   | Void ->
 let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
      let () = offset := 1 + !offset in
     
      [(!offset-1, Void, "MAKE_VOID")]
   | Sexpr(Nil) ->
      let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
      let () = offset := 1 + !offset in
    
      [(!offset -1, Sexpr(Nil), "MAKE_NIL")]
   | Sexpr(Bool false) -> let () = offset := 2 + !offset in
                          let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
                          [(!offset -2, Sexpr(Bool false), "MAKE_BOOL(0)")]
   | Sexpr(Bool true) ->
       let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
      let () = offset := 2 + !offset in
     
      [(!offset -2, Sexpr(Bool true), "MAKE_BOOL(1)")]
   | Sexpr(Symbol (sym)) ->
       let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
      let () = offset := 9 + !offset in
                            
                             [(!offset -9, Sexpr(Symbol (sym)),"MAKE_LITERAL_SYMBOL(const_tbl+" ^ string_of_int (List.assoc (Sexpr(String (sym))) !offset_map) ^ ")" )] (*maybe error from here*)
   | Sexpr(Pair (hd, tl)) ->
      let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
      let () = offset := 17 + !offset in                      
      [(!offset -17, Sexpr(Pair(hd, tl)),"MAKE_LITERAL_PAIR(const_tbl+" ^ string_of_int (List.assoc (Sexpr(hd)) !offset_map) ^", const_tbl+"^ string_of_int (List.assoc (Sexpr(tl)) !offset_map) ^ ")" )]
   (*maybe error from here*)
   | Sexpr(Number(num)) ->
       let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map  in
      let () = offset := 9 + !offset in
      (match num with
       |Float(numb)->  [(!offset -9, Sexpr(Number (num)),"MAKE_LITERAL_FLOAT("^ (string_of_float numb) ^")" )]
       |Int(numb) ->  [(!offset -9, Sexpr(Number (num)),"MAKE_LITERAL_INT("^ (string_of_int numb) ^")" )]
      )
   | Sexpr(String(str)) -> let ascii_string = (String.concat "," (List.map (fun(e)->  Printf.sprintf "%d" e) (List.map (fun(e)-> int_of_char e) (string_to_list str)))) in 
 let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
      let () = offset := 9 + !offset + (String.length str) in
      [(!offset -9 -  (String.length str), Sexpr(String (str)), Printf.sprintf("MAKE_LITERAL_STRING %s") ascii_string )]
   | Sexpr(Char(ch)) ->   let () = offset_map := (consts_list,!offset) ::List.remove_assoc consts_list !offset_map   in
      let () = offset := 2 + !offset in
      [(!offset -2, Sexpr(Char (ch)), "MAKE_LITERAL_CHAR(" ^ string_of_int (Char.code ch)  ^ ")" )]
   | Sexpr(TagRef(name)) -> [(!offset, Sexpr(TagRef(name)), "")]
   | (_) ->  raise X_create_constants_failed
  ) in
  let ans =List.map (fun(exp) -> create_constants_table exp ) consts_list in
  let () = offset:=0 in
  ans
;;


let stages ast =
  let scan = List.flatten (List.map(fun(v) -> scan_ast v []) ast)  in
  let init=  [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))]  in
  let stage1 = list_append init scan [] in 
   let stage2 = convert_to_set stage1 in
  let stage3 = extend_consts stage2 in
  let stage4 = convert_to_set stage3 in
  let stage5 = List.flatten (map_table stage4) in (* maybe remove flatten *)
  (* let stage6 = map_table_add_tagged stage5 in*)
  stage5;;
   
  
(*--------------------------FREE VAR TABLE----------------------------------*)

let rec scan_ast_free sexpr free =
  let scan_fold l c =  List.fold_left(fun hd tl -> list_append hd (scan_ast_free tl c) [] ) [] l in
    match sexpr with
        | Const'(var) -> free 
        | Var'(var) -> (match var with
                        | VarFree(x) -> List.cons [x] free
                        | (_) -> free
           )
        | If'(_test, _then, _else) -> (list_append (scan_ast_free _test free)  (scan_ast_free _then free) (scan_ast_free _else free))
        | Seq'(list_expr) -> scan_fold list_expr free
        | Or'(list_expr) -> scan_fold list_expr free
        | Set'(name, value) -> list_append (scan_ast_free name free) (scan_ast_free value free) []
        | Def'(name, value) -> list_append (scan_ast_free name free) (scan_ast_free value free) []
        | LambdaSimple'(args, body) -> scan_ast_free body free
        | LambdaOpt'(args, opt, body) -> scan_ast_free body free
        | Applic'(func, exp_list) -> (list_append (scan_ast_free func free) ( scan_fold exp_list free) [])
        | ApplicTP'(func, exp_list) -> (list_append (scan_ast_free func free) ( scan_fold exp_list free) [])
        | Box'(var) -> free
        | BoxGet'(var) -> free
        | BoxSet'(var, to_set) -> scan_ast_free to_set free
;;


(* implement the other primitives and add them to this list *)
let primitives = ["boolean?"; "float?"; "integer?"; "pair?";
   "null?"; "char?"; "string?";
   "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "symbol->string"; 
   "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "=";
   "car"; "cdr"; "cons"; "set-car!"; "set-cdr!" ; "apply"] ;;

let make_free_pairs free_list =
  let counter = ref 0 in
  let tuple free = (free,  let () = counter:= !counter + 1 in  (!counter -1)) in
  List.map (fun(fvar) -> tuple fvar) free_list ;;
  
 
let stages_free ast =
  let stage1 = List.flatten (List.fold_left (fun curr acc-> curr@acc) [] (List.map (fun(v) -> scan_ast_free v []) ast))@primitives in (*check again *)
  let stage2 = convert_to_set stage1 in
  let stage3 = make_free_pairs stage2 in
  stage3;;


(*--------------------------GENERATE----------------------------------*)


let rec address_in_const_table const const_table =
    (match const_table with
          | [] -> raise X_generate_failed
          | hd::tl -> let (offset, exp, (_)) = hd in 
                          if( expr_eq (Const(const)) (Const(exp))) 
                          then ( let address = string_of_int offset in
                    Printf.sprintf "mov rax, const_tbl+ " ^ address)
                          else address_in_const_table const tl)
;;



let depth_ref = ref 0;;

let count = ref 1;;

let rec generate_nasm const_tbl fvar_table expres count_l =
  let label = !count in(* MAYBE ERRORS FROM HERE NOTICE!! *)
  count := (!count+1);
  match expres with
  |Const'(var) -> address_in_const_table var const_tbl
  |LambdaSimple'(args, body) ->lambdasimple_to_code args body const_tbl fvar_table count_l label
  |LambdaOpt' (args, opt, body) -> lambdaopt_to_code args opt body const_tbl fvar_table count_l label
  |Var'(var) -> var_to_code var fvar_table 
  |Set'(name, value) -> set_to_code name value const_tbl fvar_table count_l 
  |Def'(name, value) -> def_to_code name value const_tbl fvar_table count_l
  |Seq'(list_expr) -> seq_to_code list_expr const_tbl fvar_table count_l
  |Applic'(func, list_expr) -> applic_to_code func list_expr const_tbl fvar_table count_l false
  |ApplicTP'(func, list_expr) -> applic_to_code func list_expr const_tbl fvar_table count_l true
  |Or'(list_expr) -> or_to_code list_expr const_tbl fvar_table count_l label
  |If'(_test, _then, _else) ->if_to_code _test _then _else const_tbl fvar_table count_l label
  |Box'(var) -> box_to_code var const_tbl fvar_table count_l			
  |BoxGet'(var) ->boxget_to_code var const_tbl fvar_table count_l 
  |BoxSet'(var,to_set) ->boxset_to_code var to_set const_tbl fvar_table count_l 


and if_to_code test dit dif const_tbl fvar_table count_l label=
  let test_code =  generate_nasm const_tbl fvar_table test count_l in
  let then_code =  generate_nasm const_tbl fvar_table dit count_l in
  let else_code =  generate_nasm const_tbl fvar_table dif count_l in
  let index = string_of_int(label) in
  let ans = String.concat "\n" [test_code;
              "cmp rax, SOB_FALSE_ADDRESS";
                Printf.sprintf "je Lelse%s" index;
                 then_code;
                    Printf.sprintf "jmp Lexit%s" index;
                      Printf.sprintf "Lelse%s:" index;
                        else_code;
                        Printf.sprintf "Lexit%s:" index;""] in
                                ans

and  seq_to_code exp const_tbl fvar_table count_l =
  let code =  (List.map (fun( x) -> generate_nasm const_tbl fvar_table x count_l) exp) in
  let code = String.concat "\n" code in
  code
                                                              
and or_to_code exp const_tbl fvar_table count_l label =
  let index = string_of_int label in
  let code = String.concat "\n" (List.map (fun( x)->String.concat "\n" [generate_nasm const_tbl fvar_table x count_l; 
                                                                           "cmp rax, SOB_FALSE_ADDRESS";
                                                                           Printf.sprintf "jne Lexit%s" index;""]) exp) in
  let code = code  ^ (Printf.sprintf  "\nLexit%s:" index) in
  code

                                                              
and boxset_to_code var exp const_tbl fvar_table count_l =
  let gen_exp = generate_nasm const_tbl fvar_table exp count_l in
  let gen_var = generate_nasm const_tbl fvar_table (Var'(var)) count_l in
  let code = String.concat "\n" [gen_exp;
                                 "push rax";
                                 gen_var;
                                 "pop qword [rax]";
                                 "mov rax, SOB_VOID_ADDRESS";""] in
  code 
  
and  box_to_code var const_tbl fvar_table count_l =
  String.concat "\n" [generate_nasm const_tbl fvar_table (Var'(var)) count_l; 
	       "MALLOC rbx, WORD_SIZE";
               "mov [rbx], rax";
               "mov rax, rbx";""]
		
and boxget_to_code var const_tbl fvar_table count_l = (* maybe error here? *)
  let gen = generate_nasm const_tbl fvar_table (Var'(var)) count_l in
      let code = String.concat "\n" [gen; "mov rax, qword [rax]";""] in
      code 
  
and  applic_to_code func expression const_tbl fvar_table count_l tp =
  let exp_rev =  (List.rev expression) in
  let exp_len =  string_of_int (List.length expression) in
  let shift_len = string_of_int((List.length expression)+5) in
  let gen =  generate_nasm const_tbl fvar_table func count_l in
  let gen_map = List.map (fun( exp)-> generate_nasm const_tbl fvar_table exp count_l ^ "\npush rax") exp_rev in
  let gen_map = String.concat "\n" gen_map in
  let app = String.concat "\n" ["push SOB_NIL_ADDRESS";
                     gen_map;
                     Printf.sprintf "push %s" exp_len ;
		     gen;
                     "CLOSURE_ENV rbx, rax" ;
                     "push rbx";""] in
 (match tp with
 |false -> 
      let not_tp= "NOT_TAIL_POSITION" in
      String.concat "\n" [app;not_tp;""]
 |true ->
   let yes_tp = Printf.sprintf "YES_TAIL_POSITION %s" shift_len in
   String.concat "\n" [app; yes_tp;""]
 )
   

and lambdasimple_to_code args body const_tbl fvar_table count_l label =
  let index = string_of_int(label)in
  let len =  (List.length args) in
  let depth = !depth_ref in 
  if depth = 0 then
     (depth_ref := !depth_ref + 1;
                               let gen =  generate_nasm const_tbl fvar_table body len in
                                depth_ref := !depth_ref - 1;
                                    String.concat "\n" ["mov rbx, SOB_NIL_ADDRESS" ;
                                    (make_closure index) ;
                                   gen ;
                                   (leave index)])
  else
    if depth = 1 then
       (depth_ref := !depth_ref + 1;
                               let gen = generate_nasm const_tbl fvar_table body len in
                               depth_ref := !depth_ref - 1;
                               String.concat "\n" ["DEPTHS_ONE";
			                           (aux index count_l "_one") ; (make_closure index) ; gen;
                                                   (leave index)])
    else
       (let str = (frame_aux index) ^
                                    (aux index count_l "_two") ^
                                     (make_closure index) ^
                                  generate_nasm const_tbl fvar_table body len ^ "\n" ^
                                    (leave index) in
                                   depth_ref := !depth_ref - 1;
                                     str) 

and make_closure index =
   String.concat "\n" [Printf.sprintf "MAKE_CLOSURE(rax, rbx, closure_%s)" index;
                                  Printf.sprintf  "jmp leave_%s" index;
                                    Printf.sprintf "closure_%s:" index ;
                                    "PUSH_STACK";""]
			   
    and  lambdaopt_to_code args arg body const_tbl fvar_table count_l label=
      let index = string_of_int(label) in
      let len = (List.length args) in
      let depth =  !depth_ref in
      if depth= 0 then
        ( depth_ref := !depth_ref + 1;
                                  let gen =  generate_nasm const_tbl fvar_table body (len + 1) in
                                    depth_ref := !depth_ref - 1;
                                      String.concat "\n" ["mov rbx, SOB_NIL_ADDRESS";
                                                          (opt_aux index len); gen; (leave index)])
      else
        if depth = 1 then
          (depth_ref := !depth_ref + 1;
      let gen =  generate_nasm const_tbl fvar_table body (len + 1) in
      depth_ref := !depth_ref - 1;
      String.concat "\n" ["DEPTHS_ONE";
                          (aux index count_l "_optone") ;(opt_aux index len) ; gen; (leave index)])
        else
          ( let str = (frame_aux index) ^
                                        (aux index count_l "_opttwo") ^
                                       (opt_aux index len) ^
                                       generate_nasm const_tbl fvar_table body (len + 1)^ "\n" ^
                                         (leave index) in
                                          depth_ref := !depth_ref - 1;
                                         str)

    and frame_aux index =
      depth_ref := !depth_ref + 1;
      let depth = !depth_ref -1 in
               Printf.sprintf "FRAME_INS %d, %s, %d\n" depth index (depth -1)
                  
    and aux index count_l case=
      Printf.sprintf "LAMBDA_LOOPS %d, %s, %s\n" count_l case index

and leave index = 
      String.concat "\n" ["DONE_TASK" ; 
          Printf.sprintf "leave_%s:" index] 

    and opt_aux index len  =
       Printf.sprintf "LAMBDAOPT_LOOPS %s, %d\n" index len 
                         
    and set_to_code expr vals const_tbl fvar_table count_l =
      let gen =  generate_nasm const_tbl fvar_table vals count_l in
      let free_p var =  string_of_int(List.assoc var fvar_table) in
      (match expr with
  |Var'( VarParam(var, minor)) ->
    String.concat "\n" [gen;
                        Printf.sprintf "mov qword[rbp + WORD_SIZE*(4 + %d)], rax" minor;
                        "mov rax, SOB_VOID_ADDRESS";""]
  |Var'( VarBound(var, major, minor)) ->
    String.concat "\n" [gen;
                        "mov rbx, qword [rbp + 8*2]"; 
                        Printf.sprintf "mov rbx, qword [rbx + WORD_SIZE*%d]" major;
                        Printf.sprintf "mov qword [rbx + WORD_SIZE*%d], rax" minor;
                        "mov rax, SOB_VOID_ADDRESS";""]
  |Var'( VarFree(var) ) ->
    String.concat "\n" [gen;
                        Printf.sprintf "mov qword [fvar_tbl+%s*WORD_SIZE], rax" (free_p var);
                        "mov rax, SOB_VOID_ADDRESS";""]
                      | (_) -> raise X_set_failed)
  
  
and  def_to_code name vals const_tbl fvar_table count_l =
  match name with
   |Var'( VarFree( var)) ->
     let get_free = string_of_int (List.assoc var fvar_table) in
     String.concat "\n" [generate_nasm const_tbl fvar_table vals count_l;
                         Printf.sprintf "mov qword [fvar_tbl+%s*WORD_SIZE], rax" get_free;
                         "mov rax, SOB_VOID_ADDRESS";""]
   |_-> raise X_def_failed

and  var_to_code var fvar_table =
  let get_free name = string_of_int  (List.assoc name fvar_table) in
  (match var with
   |VarFree(name) ->  Printf.sprintf "mov rax, [fvar_tbl+%s*WORD_SIZE]" (get_free name)  
   |VarParam(name, minor) -> Printf.sprintf "mov rax, PVAR(%s)" (string_of_int minor)
   |VarBound(name, major, minor) -> String.concat "\n" ["mov rax, qword [rbp + WORD_SIZE*2]"; 
                                                       Printf.sprintf "mov rax, qword [rax + WORD_SIZE*%s]" (string_of_int major) ; 
                                                       Printf.sprintf "mov rax, qword [rax + WORD_SIZE*%s]" (string_of_int minor) ;""]              
  )         ;;

(*
let run_generate ast =
  let const_table = stages ast in
let const_table = List.flatten const_table in
  let free_table = stages_free ast in
 (* (free_table, const_table)*)
  (generate_nasm const_table free_table ast (-1)) 
;;
 *)
let constt ast= stages ast;;
let freee ast = stages_free ast;;

module Code_Gen : CODE_GEN = struct
  
  let make_consts_tbl asts =   stages asts;;
  let make_fvars_tbl asts =  stages_free asts;;
  let generate consts fvars e =  (generate_nasm consts fvars e (-1));;
end;;

