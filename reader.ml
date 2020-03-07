
#use "pc.ml";;
open PC
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;



let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;




(*##################Boolean#######################*)

let bool_parse bool=
  let hash_mark = char '#' in
  let f = char_ci 'f' in
  let t = char_ci 't' in
  let combined= caten hash_mark (disj t f) in
  let packed = pack combined (fun (hd,tl)->
                   if (lowercase_ascii tl) = 't' 
                             then Bool(true)
                                         else Bool(false)) in
   packed bool;;

(*##################Number#######################*)

let digit_parse dig =
  let packed = pack (range '0' '9') (fun (hd) -> hd) in 
  packed dig;;


  let natural_parse natural =
    let nat = plus digit_parse in
    let packed = pack nat (fun (hd) ->
                     int_of_string(list_to_string hd)) in
    packed natural;;

	
  let integer_parse inte =
    let s = maybe ( disj (char '+') (char '-')  ) in
    let s = caten s natural_parse in
    let packed = pack s (fun (hd,tl)->
    match hd with
        | Some('+') -> Int(tl) 
        | Some('-') -> Int(tl*(-1))
        |(_) -> Int(tl)) in
    packed inte;;

    let float_parse floa =
    let dottt = char '.' in
    let s =  maybe( disj (char '+') (char '-'))   in
    let s = caten  s  natural_parse in
    let s1 = caten dottt natural_parse in
    let s = caten s s1 in
    let s = pack s  (fun ((sign, integer), (dot,natural)) ->
                  let integerr =  (string_of_int (integer)) in                     
                           let dott = String.make 1 dot in
                           let naturall = string_of_int (natural) in
                match sign with
                | Some('+') ->  
                           let s = String.concat "" ["";"+" ;integerr; dott; naturall] in
                           float_of_string s
        | Some('-') ->  
                           let s = String.concat "" ["";"-" ;integerr; dott; naturall] in
                           float_of_string s
        |(_) -> 
                           let s = String.concat "" ["" ;integerr; dott; naturall] in
                           float_of_string s) in 
    let s = pack s (fun (a) -> Float(a)) in
    s floa;;
	
(*##################Scientific Notation#######################*)
(* exponent function taken from stackoverflow *)

let rec expt : int -> int -> int= fun b n ->
    if n = 0 then 1
    else 
      let b2 = expt b (n / 2) in
      if n mod 2 = 0 then b2 * b2 
      else b * b2 * b2;;
 

let scientificNotation_parse sci =
  let char_e = char_ci 'e' in
  let beginwith =  disj float_parse integer_parse in
  let followed = caten beginwith char_e in
  let science = caten followed integer_parse in
  let wrap = pack science (fun ((first,e),inte) ->
                   let x = match inte with |Int a ->float_of_int a | Float b -> b in
                   let before = 10.0 ** x in
                   let s = match first with |Int a ->float_of_int a | Float b -> b in
                   let after = s *. before in
                   let s = String.concat "" ["" ;string_of_float after] in
                   s) in
  let packedd = pack wrap (fun(a) ->Float(float_of_string a)) in
  packedd sci;;
 
(*##################Radix Notation#######################*)

 let string_of_chars chars = 
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

  
 let from_base b ds =
  List.fold_left (fun n k -> n * b + k) 0 ds

  
let from_alpha_digit c = match c with
    '0'..'9' -> int_of_char c - int_of_char '0'
  | 'A'..'Z' -> int_of_char c - int_of_char 'A' + 10
  | 'a'..'z' -> int_of_char c - int_of_char 'a' + 10
  | (_) -> raise X_no_match 

         
let from_alpha_digits s =
  let result = ref [] in
    String.iter (fun c -> result := from_alpha_digit c :: !result) s;
    List.rev !result

    
let from_base_after_dot b ds =
let length = List.length ds in
 let orig_int = List.fold_left (fun n k ->
     n *.  float_of_int(b) +.k
            
                  ) 0.0 ds in
 orig_int *. (float_of_int(b) ** (-1.0 *. ( float_of_int length)));;

let from_alpha_digits_float s =
  let result = ref [] in
    String.iter (fun c -> result :=float_of_int( from_alpha_digit c) :: !result) s;
      List.rev  !result

    
let radixNotation_withoutDot_parse radix =
  let hash_mark = char '#' in
  let base = plus (range '0' '9') in 
  let r = char_ci 'r' in
  let sign = maybe (disj (char '-') (char '+')) in
  let numb = star  (disj (char '-') (disj (char '+') ( disj (range '0' '9') ( disj (range 'a' 'z') (range 'A' 'Z'))))) in
  let news = caten hash_mark (caten base (caten r (caten sign numb))) in
  let packed = pack news (fun (hash, (base, (rr , (sign , num)))  )->
                   let int_base = int_of_string (string_of_chars base) in                 
                   match sign with
                   | Some('-') ->
                      let s = string_of_chars num in
                      let s = from_base int_base (from_alpha_digits s) in 
                      (*let s = (float_of_int s)*. -1. in*)
                      let s = s * (-1) in
                      Int(s)
                   | (_) ->
                      let s = string_of_chars num in
                      let s = from_base int_base (from_alpha_digits s) in
                      (*let s = float_of_int s in*)
                      Int(s)
                 ) in
packed radix;;
      
   
let radixNotation_withDot_parse radix =
  let hash_mark = char '#' in
  let base = plus (range '0' '9') in 
  let r = char_ci 'r' in
  let sign = maybe (disj (char '-') (char '+')) in
  let num_before_dot = star(disj (char '-') (disj (char '+') ( disj (range '0' '9') ( disj (range 'a' 'z') (range 'A' 'Z'))))) in
  let dot = char '.' in
  let num_after_dot = star (disj (range '0' '9') ( disj (range 'a' 'z') (range 'A' 'Z')))in
  let news = caten hash_mark (caten base (caten r (caten sign (caten num_before_dot( caten dot num_after_dot))))) in
  let packed = pack news (fun (hash,  (base, (rr , (sign,  (num , (dott, num_after)))))) ->
                   let int_base = int_of_string (string_of_chars base) in
                   match sign with
                   | Some('-') ->
                      let num_bef = string_of_chars num in
                      let num_aft = string_of_chars num_after in
                      let value_bef = from_base int_base (from_alpha_digits num_bef) in
                      let value_aft = from_base_after_dot int_base (from_alpha_digits_float num_aft) in
                          let sum = (value_aft +.float_of_int( value_bef)) in
                    Float(sum)
                        | (_) ->
                      let num_bef = string_of_chars num in
                      let num_aft = string_of_chars num_after in
                      let value_bef =  from_base int_base (from_alpha_digits num_bef) in
                      let value_aft =  from_base_after_dot int_base (from_alpha_digits_float num_aft) in
                     let sum = (value_aft +. float_of_int(value_bef)) in
                      Float(sum)
                 ) in
  packed radix;;
  
  
let radixNotation_parse radix =
  let packed = pack (disj radixNotation_withDot_parse  radixNotation_withoutDot_parse) (fun (a)->a )in
  packed radix;;

(*##################Symbol#######################*)

  let symbolChar_parse sym =
    let digits = (range '0' '9') in
    let chars = (range 'a' 'z') in
    let caps_chars = range 'A' 'Z' in 
    let symbols = disj_list [char '!' ; char '$' ; char '^' ; char '*' ; char '-' ; char '_' ; char '=' ; char '+' ; char '<' ; char '>' ; char '?' ; char '/' ; char ':' ;] in
    let dis = disj_list [digits ; chars ; caps_chars ; symbols] in
    let packed = pack dis (fun (hd) ->(lowercase_ascii hd)) in
    packed sym;;
	
  let symbol_parse sym =
    let p = plus symbolChar_parse in
    let packed = pack p (fun (hd) -> Symbol(list_to_string hd)) in
    packed sym;;

  let symbolCharR_parse sym =
    let digits = (range '0' '9') in
    let chars = (range 'a' 'z') in
    let caps_chars = range 'A' 'Q' in 
    let cap_char = range 'S' 'Z' in 
    let symbols = disj_list [char '!' ; char '$' ; char '^' ; char '*' ; char '-' ; char '_' ; char '=' ; char '+' ; char '<' ; char '>' ; char '?' ; char '/' ; char ':' ;] in
    let dis = disj_list [digits ; chars ; caps_chars ; cap_char ; symbols] in
    let packed = pack dis (fun (hd) ->(lowercase_ascii hd)) in
    packed sym;;

  let symbolR_parse sym =
    let p = plus symbolCharR_parse in
    let packed = pack p (fun (hd) -> Symbol(list_to_string hd)) in
    packed sym;;

  let number_parse num = 
    let all = disj_list[scientificNotation_parse; radixNotation_parse; float_parse; integer_parse] in
    let packed = pack (not_followed_by all symbolR_parse) (fun (hd)-> Number(hd)) in
    packed num;;

  (*##################String#######################*)

  let  literal_parse str =
    if ( fst(str) = "a" || fst(str) = "b" ) then
        fun (a)-> "c" else
          fun (c) -> "d" ;;

  let stringLiteralChar_parse str =
    let bool = const (fun (hd) -> hd  !=  '\\' && hd  !=  '\"' ) in
    let packed = pack bool ( fun (hd) -> hd) in
    packed str;;

 
  let stringMetaChar_parse str =
    let sym = disj_list [char_ci '\\' ; char_ci '\"' ; char_ci 't' ; char_ci 'f' ; char_ci 'n' ; char_ci 'r'] in     
    let back = char '\\' in 
    let packed = pack (caten back sym) (fun (hd,tl) ->  
    match tl with
        | '\\' -> Char.chr 92 
        | '\"' -> Char.chr 34
        | 't' -> Char.chr 9 
        | 'f' -> Char.chr 12
        | 'n' -> Char.chr 10
        | 'r'->  Char.chr 13
        |(_) -> raise X_no_match) in
    packed str;;
  
  let stringChar_parse str =
    let s = disj stringLiteralChar_parse stringMetaChar_parse in
    s  str;;

  
let string_parse str =
  let s = caten (caten ( char '\"') (star (diff stringChar_parse (char '\"')))) (char '\"') in
  let packed = pack s (fun ((hd, tl), tll) -> String(list_to_string tl)) in
  packed str;;

(*##################Char#######################*)

  let stringMetaChar_parse str =
    let sym = disj_list [char '\\' ; char '\"' ; char '\t'   ; char '\n' ; char '\r'] in    
    let packed = pack sym (fun (hd) ->  hd) in
    packed str;;
    

 let charPrefix_parse c =  
    let hash_mark = char '#' in
    let pre = char '\\' in
    let combined = caten hash_mark pre in
    let packed = pack combined (fun (hd,tl) -> Nil) in
    packed c;;

let namedChar_parse name =
    let names = disj_list [word_ci "newline" ; word_ci "nul" ; word_ci "page" ; word_ci "return" ; word_ci "space" ; word_ci "tab"] in 
    let packed = pack names (fun (hd) ->  
    match String.lowercase_ascii (list_to_string(hd)) with
        | "newline" -> Char(char_of_int 10) 
        | "nul" ->  Char(char_of_int 0)
        | "page" ->  Char(char_of_int 12)
        | "return" ->  Char(char_of_int 13)
        | "space" ->  Char(char_of_int 32)
        | "tab" ->  Char(char_of_int 9)
        |(_) -> raise X_no_match) in
    packed name;;

let visibleSimpleChar_parse c =
    let check = const (fun (hd)-> int_of_char (hd) > 32) in
    let packed = pack check (fun(hd)-> Char(hd)) in 
    packed c;;

let char_parse c = 
    let dis =  disj namedChar_parse visibleSimpleChar_parse in
    let chars = caten charPrefix_parse dis in
    let packed = pack chars (fun (hd,tl)->tl) in
    packed c;;

(*##################whitespaces#######################*)

let whitespaces_parse white =
  let s = const (fun (ch) -> ch <= ' ') in
  let s = pack s (fun (ch) -> Nil) in
  s white;;

(*##################Line Comments#######################*)

let nt_end_of_inputs = function
  | []  -> char '\000'
  | _ -> raise X_no_match;;

(*##################Sexpr#######################*)

let rec sexpr_parse exp = 
  let all = disj_list [nil_parse;bool_parse;char_parse;number_parse;string_parse;symbol_parse;list_parse;dottedList_parse;
  quoted_parse;quasiQuoted_parse;unQuoted_parse;unQuoteAndSpliced_parse;taggedExpr_parse] in

  let cat = caten skip_parse all in
  let cat = caten cat skip_parse in

  let packed = pack cat (fun ((comment,sexp),comment1)->sexp) in
  packed exp


and lineComments_parse line =
  let semicolon = char ';' in
  let newline_diff = star(diff nt_any (char '\n')) in
  let end_of_input = pack (not_followed_by (word "") nt_any) (fun (hd) -> '_') in
  let disjoint = disj (char '\n') end_of_input in
  let first =  semicolon in
  let second = caten first newline_diff in
  let third = caten second  disjoint in  
  let packed = pack third (fun (hd) -> Nil) in
  packed line

(*##################Nil#######################*)

and nil_parse n = 
  let pL = char '(' in
  let pR = char ')' in
  let may = star (disj (whitespaces_parse) (lineComments_parse)) in
  let p = caten pL may in
  let p = caten p pR in
  let packed = pack p (fun (hd)->Nil) in
  packed n


and  sexprComments_parse_temp comment =
  let hash_mark = char '#' in
  let semicolon = char ';' in
  let whitespaces = star ( char ' ' ) in
  let comment_mark_space = caten (caten hash_mark semicolon) whitespaces  in
  let recursive = caten comment_mark_space sexpr_parse in
  let packed = pack recursive (fun (hd) -> Nil) in
  packed comment


(*##################Skip#######################*)

and skip_parse skip =
  let par = star(disj lineComments_parse (disj whitespaces_parse sexprComments_parse_temp)) in
  let packed = pack par (fun(a) -> Nil) in
    packed skip

and skip_parse_nil skip =
  let par = star(disj lineComments_parse (disj whitespaces_parse (disj nil_parse sexprComments_parse_temp))) in
  let packed = pack par (fun(a) -> Nil) in
    packed skip

(*##################List#######################*)

and list_parse exp =
  let pL = char '(' in
  let pR = char ')' in
  let p = star sexpr_parse in
  let pL_s = caten pL p in
  let before = pack pL_s (fun (hd,tl) -> tl) in
  let after = pack pR (fun (hd) -> Nil) in
  let all = caten before after in
  let packed = pack all (fun (hd, tl) -> List.fold_right (fun sexp n -> Pair(sexp, n)) hd tl) in
  packed exp
  

  and dottedList_parse exp = 
    let pL = char '(' in
    let pR = char ')' in
    let dott = char '.' in 
    let p = plus sexpr_parse in
    let cat1 = caten pL p in
    let cat2 = caten cat1 dott in
    let cat3 = caten cat2 sexpr_parse in 
    let cat = caten cat3 pR in 
    let packed = pack cat (fun ((((pl, sexpr), dot), sexpr2), pr)->
                  List.fold_right (fun sexp n -> Pair(sexp, n)) sexpr sexpr2) in 
    packed exp
     
(*##################Sexpr Comments#######################*)

and  sexprComments_parse comment =
  let hash_mark = char '#' in
  let semicolon = char ';' in
  let whitespaces = star ( char ' ' ) in
  let comment_mark_space =caten (caten hash_mark semicolon) whitespaces  in
  let recursive = caten comment_mark_space sexpr_parse in
  let packed = pack recursive (fun (hd) -> Nil) in
  packed comment

(*##################Quote#######################*)

and quoted_parse exp =
    let ch = char '\'' in
    let cat = caten ch sexpr_parse in
    let packed = pack cat (fun (hd,tl)->Pair(Symbol("quote"), Pair(tl,Nil))) in 
    packed exp

  and quasiQuoted_parse exp =
    let ch = char '`' in
    let cat = caten ch sexpr_parse in
    let packed = pack cat (fun (hd,tl)->Pair(Symbol("quasiquote"), Pair(tl,Nil))) in 
    packed exp

  and unQuoted_parse exp =
    let ch = char ',' in
    let cat = caten ch sexpr_parse in
    let packed = pack cat (fun (hd,tl)->Pair(Symbol("unquote"), Pair(tl,Nil))) in 
    packed exp

  and unQuoteAndSpliced_parse exp =  
    let ch = char ',' in
    let shtrudel = char '@' in
    let combined = caten ch shtrudel in
    let cat = caten combined sexpr_parse in
    let packed = pack cat (fun (hd,tl) -> Pair(Symbol("unquote-splicing"), Pair(tl,Nil))) in
    packed exp

    
  and taggedExpr_parse exp = 
    let tag = tag_parse in
    let eq = char '=' in 
    let cat = caten eq sexpr_parse in 
    let s = maybe (cat) in
    let combined = caten tag s in
    let packed = pack combined (fun (tag_name, equal_sexp)->
                    match equal_sexp with
                          | Some(equal,sexpr) ->
                            (match tag_name with
                                | Symbol(symbolToString) ->
                                    let tagref = TagRef(symbolToString) in
                                    let paired = 
                                      match sexpr with
                                      | Pair(a,Pair(b,c)) -> sexpr
                                      | Pair(a,b) -> Pair(a,tagref)
                                      | a -> a in
                                    TaggedSexpr(symbolToString, paired)
                                | (_) -> raise X_no_match)
                          | None -> 
                            match tag_name with
                            | Symbol(symbolToString) -> TagRef(symbolToString)
                            | (_) -> String("this should not happend")
                     ) in
  let isCycle tag =
  let rec check d = match d with 
  | Pair(hd, tl) ->List.append (check hd) (check tl)
  | TaggedSexpr(tagged, rest) ->
        List.append [tagged] (check rest) 
  | (_) -> [] in 
  let rec isdup = function
  | [] -> false
  | hd::tl -> List.exists ((=) hd)
                tl ||
                isdup tl in 
  let checkdup = isdup
                   (check tag) in 
    match checkdup with 
          | false -> tag
          | true -> raise X_this_should_not_happen in
    let packed = pack packed isCycle in
    packed exp

   
  and tag_parse tag =
    let hash_mark = char '#' in 
    let pL = char '{' in
    let pR = char '}' in
    let addP = caten hash_mark pL in
    let cat = caten addP symbol_parse in
    let combined = caten cat pR in
    let packed = pack combined (fun (((hash, l), sexpr), r)->sexpr) in
    packed tag;;

let read_sexprs  (str : string): sexpr list = 
 let (dones, nil) = (star sexpr_parse) (string_to_list str) in
  dones;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
        
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr  (str : string): sexpr = 
  let (dones, nil) = sexpr_parse (string_to_list str) in
  dones;;
     
let read_sexprs  (str : string): sexpr list = 
 let (dones, nil) = (star sexpr_parse) (string_to_list str) in
  dones;;
                                                               
end;; (* struct Reader *)

