type variable = string;;

type bexp = 
  | Bcst of bool
  | Ava of variable
  | And of bexp * bexp
  | Or of bexp * bexp
  | Not of bexp
  | Equal of bexp * bexp
;;

type winstr =
  | Skip 
  | Assign of variable * bexp
  | Seq of winstr * winstr
  | If of bexp * winstr * winstr
  | While of bexp * winstr
;;


let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0
;;

type 'a inflist = unit -> 'a contentsil
and 'a contentsil = Cons of 'a * 'a inflist
;;

exception Echec;;
let rec inflist_of_string s =
  let n = String.length s in
  let rec aux i =
    if i >= n then
      fun () -> raise Echec  (* Ou retourner une sorte de valeur de fin de liste *)
    else
      fun () -> Cons (s.[i], aux (i + 1))
  in aux 0
;;

let string_of_inflist infl =
  let rec aux acc l =
    try
      match l () with
      | Cons (x, rest) -> aux (acc ^ String.make 1 x) rest
    with
    | Echec -> acc  (* Attraper l'exception si utilisée pour marquer la fin *)
  in aux "" infl
;;
"abcd" |> inflist_of_string |> string_of_inflist;;


(* Le type des aspirateurs (fonctions qui aspirent le préfixe d'une liste) *)
(* type 'term analist = 'term list -> 'term list;; *)
type 'term analist = 'term inflist -> 'term inflist;;

(* Exception pour signaler un échec *)



(* terminal constant *)
let terminal (c : 't) : 't analist = fun l ->
  match l () with
  | Cons(x, l) when x = c -> l
  | _ -> raise Echec
;;
(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : 'term analist = fun
  l -> match l () with
  | Cons(x, l) when p x -> l
  | _ -> raise Echec
;;

(* non-terminal vide *)
let epsilon : 'term analist = fun l -> l;;

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs purs *)
(* ------------------------------------------------------------ *)

(* a1 suivi de a2 *)
let (-->) (a1 : 'term analist) (a2 : 'term analist) : 'term analist =
  fun l -> let l = a1 l in a2 l
;;

(((terminal 'a') --> (terminal 'b')) (inflist_of_string "abc")) |> string_of_inflist;;



(* Choix entre a1 ou a2 *)
let (-|) (a1 : 'term analist) (a2 : 'term analist) : 'term analist =
  fun l -> try a1 l with Echec -> a2 l
;;

(((terminal 'a') -| (terminal 'b')) (inflist_of_string "bc")) |> string_of_inflist;;

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let rec star (a : 'term analist) : 'term analist = 
  fun l -> l |>
           ( a --> star a ) -| epsilon
;;

(((terminal 'a') --> (star (terminal 'b'))) (inflist_of_string "abbbb")) |> string_of_inflist;;

(* ------------------------------------------------------------ *)
(* Exemple : analyseur d'expressions booléennes *)
(* ------------------------------------------------------------ *)

(* Corresponding to previous language *)

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs
   avec calcul supplémentaire, ex. d'un AST *)
(* ------------------------------------------------------------ *)

(* Le type des aspirateurs qui, en plus, rendent un résultat *)
type ('res, 'term) ranalist = 'term inflist -> 'res * 'term inflist;;

(* Un epsilon informatif *)
let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)
;;
(* Terminal conditionnel avec résultat *)
(* [f] ne retourne pas un booléen mais un résultat optionnel *)
let terminal_res (f : 'term -> 'res option) : ('res, 'term) ranalist =
  fun l -> 
    match l () with
    | Cons(x, l) -> (match f x with Some y -> y, l | None -> raise Echec)
    | _ -> raise Echec
;;
(* a1 sans résultat suivi de a2 donnant un résultat *)
let ( -+>) (a1 : 'term analist) (a2 : ('res, 'term) ranalist) :
  ('res, 'term) ranalist =
  fun l -> let l = a1 l in a2 l
;;

(* a1 rendant un résultat suivi de a2 rendant un résultat *)
let (++>) (a1 : ('resa, 'term) ranalist) (a2 : 'resa -> ('resb, 'term) ranalist) :
  ('resb, 'term) ranalist =
  fun l -> let (x, l) = a1 l in a2 x l
;;
(* a1 rendant un résultat suivi de a2 sans résultat est peu utile *)


(* Choix entre a1 ou a2 informatifs *)
let (+|) (a1 : ('res, 'term) ranalist) (a2 : ('res, 'term) ranalist) :
  ('res, 'term) ranalist =
  fun l -> try a1 l with Echec -> a2 l
;;
(* ==================================================================== *)
(* Facultatif *)

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let (<<) f g = fun x -> f (g x);;
let (>>) f g = fun x -> g (f x);;

(* Pipeline right to left*)
let star_pipe_R2L (a : ('r -> 'r, 'term) ranalist) : ('r -> 'r, 'term) ranalist =
  let rec a_star = fun l ->
    ( ( a ++> fun f -> a_star ++> fun f_star -> epsilon_res (f << f_star) )
      +|
      epsilon_res (fun x -> x)
    ) l
  in a_star
;;
let star_R2L (a : ('r -> 'r, 'term) ranalist) (r0 : 'r) : ('r, 'term) ranalist =
  star_pipe_R2L a ++> fun f -> epsilon_res (f r0)
;;
(* Special case: building lists *)
let star_list (a : ('a, 'term) ranalist) : ('a list, 'term) ranalist =
  star_R2L (a ++> fun x -> epsilon_res (fun l -> x :: l)) []
;;

(* Add an element to the beginning of the inflist *)
let conc_inflist : ('term -> 'term inflist -> 'term inflist) =
  fun x l -> fun () -> Cons(x, l)
;;
(* Special case: building lists *)
let star_inflist (a : ('a, 'term) ranalist) : ('a inflist, 'term) ranalist =
  star_R2L (a ++> fun x -> epsilon_res (fun l -> conc_inflist x l)) (fun () -> raise Echec)
;;

(* Pipeline left to right*)
let star_pipe_L2R (a : ('r -> 'r, 'term) ranalist) : ('r -> 'r, 'term) ranalist =
  let rec a_star = fun l ->
    ( ( a ++> fun f -> a_star ++> fun f_star -> epsilon_res (f >> f_star) )
      +|
      epsilon_res (fun x -> x)
    ) l
  in a_star
;;

let star_L2R (r0 : 'r) (a : ('r -> 'r, 'term) ranalist) : ('r, 'term) ranalist =
  star_pipe_L2R a ++> fun f -> epsilon_res (r0 |> f)
;;
(*
A partir d'ici, nous ajoutons nous même quelques outils qui seront utiles pour la suite.
*)

(* rendant un résultat suivi de a2 sans résultat donnent un resultat  *)
let (+->) (a1 : ('res, 'term) ranalist) (a2 : 'term analist) :
  ('res, 'term) ranalist =
  fun l -> let r1,l1 = a1 l in (r1,a2 l1)
;;


(* terminal pour les string *)
let terminal_string (s : string) : char analist =
  let rec aux : (char list -> char analist) = fun l ->
    match l with
    | [] -> epsilon
    | c :: queue -> (terminal c) --> (aux queue)
  in aux (list_of_string s)
;;

(* terminal conditionnel avec resultat *)
let terminal_cond_res (p : 'term -> bool) : ('res ,'term) ranalist =
  fun l -> match l () with
  | Cons(x, l) when p x -> (x,l) 
  | _ -> raise Echec
;;

(* Corresponding to previous language *)
type token =
  | LexBoolean of bool (* 1|0*)
  | LexVariable of string (* x *)
  | LexOpenBrace (* { *)
  | LexCloseBrace (* }*)
  | LexSemicolon (* ; *)
  | LexAssignement (* := *)
  | LexWhile (* while *)
  | LexIf (* if *)
  | LexThen (* then *)
  | LexElse (* else *)
  | LexNot (* not ou ! *)
  | LexAnd (* && *)
  | LexOr (* || *)
  | LexOpenPar (* ( *)
  | LexClosePar (* ) *)
  | LexEqual
;;

(* Lexing *)
let is_alpha_numeric c =
  (Char.code c >= Char.code 'a' && Char.code c <= Char.code 'z') ||
  (Char.code c >= Char.code 'A' && Char.code c <= Char.code 'Z') ||
  (Char.code c >= Char.code '0' && Char.code c <= Char.code '9')
;;

let terminal_lex : (string -> (token) -> (token, char) ranalist) =
  fun str tok -> terminal_string str -+> epsilon_res tok
;;

let terminal_key_lex : (string -> (token) -> (token, char) ranalist) =
  fun s tok l -> let (newToken, newList) =  (terminal_lex s tok l) 
    in 
  try 
    match newList () with
    | Cons(x, _) when (is_alpha_numeric x) -> raise Echec
    | _ -> (newToken, newList)
  with Echec -> (newToken, newList)
;;

terminal_key_lex "true" (LexBoolean true) (inflist_of_string "true");;

let whitespace : char analist = 
  fun l -> l |>
           terminal_cond (fun c -> c = ' ' || c = '\n' || c = '\t')
;;

let string_of_charlist l = 
  let rec aux l = match l with
    | [] -> ""
    | c :: l -> (String.make 1 c) ^ (aux l)
  in aux l
;;

let is_letter c =
  (Char.code c >= Char.code 'a' && Char.code c <= Char.code 'z') ||
  (Char.code c >= Char.code 'A' && Char.code c <= Char.code 'Z')
;;

(* Lexer for a variable *)
let variable_lexer : (token, char) ranalist =
  let rec collect_chars acc = 
    fun l -> 
    try 
      match l () with
      | Cons(x,xs) when is_alpha_numeric x -> collect_chars (acc ^ Char.escaped x) xs
      | l' -> (acc, l)
    with Echec -> (acc, l)
  in
  fun l -> match l () with
    | Cons(x, xs) when is_letter x -> let (acc, l) = collect_chars (Char.escaped x) xs in
      (LexVariable acc, l)
    | _ -> raise Echec
;;

(* Variable *)

(("abcde" |> inflist_of_string) |> variable_lexer);;

(* Word Expressions *)

let rec wordExprs =
  fun l ->l |>
          terminal_key_lex "true"   (LexBoolean true)
          +|
          terminal_key_lex "false"  (LexBoolean false)
          +| 
          terminal_key_lex "1"      (LexBoolean true)
          +|
          terminal_key_lex "0"      (LexBoolean false)
          +|
          terminal_key_lex "while"  LexWhile
          +|
          terminal_key_lex "if"     LexIf
          +|
          terminal_key_lex "then"   LexThen
          +|
          terminal_key_lex "else"   LexElse
          +|
          variable_lexer
;;

let rec transi : ((token, char) ranalist) = 
  fun l -> l 
           |>
           terminal_lex "{"    LexOpenBrace
           +|
           terminal_lex "}"    LexCloseBrace
           +|
           terminal_lex ";"    LexSemicolon
           +|
           terminal_lex ":="   LexAssignement
           +|
           terminal_lex "!"    LexNot
           +|
           terminal_lex "&&"   LexAnd
           +|
           terminal_lex "||"   LexOr
           +|
           terminal_lex "("    LexOpenPar
           +|
           terminal_lex ")"    LexClosePar
           +|
           terminal_lex "=="   LexEqual
;;

let rec allPaths : (token, char) ranalist =
  fun l -> l 
           |>
           (wordExprs)
           +|
           (transi)
           +|
           (whitespace -+> allPaths)
;;


let lexer : (token inflist, char) ranalist = star_inflist allPaths;;

(* Test *)

lexer (inflist_of_string "if(hagrid == true) then !1 else false ");;

(* Système de Variable TODO*)

type env = (string * bool) list;;

let empty_env = [];;
let add_env x v env = (x,v) :: env;;
let rec find_env x env = match env with
  | [] -> raise Not_found
  | (y,v) :: env -> if x = y then v else find_env x env
;;

(* Parser *)


(* Rappel Grammaires :
   ----- BEXP ----- (début E)
   VAL  ::= [Boolean]
   VAR  ::= [Variable]
   A    ::= VAL | VAR
   E    ::= OR E'
   E'   ::= [Equal] OR E' | ε
   OR    ::= AND OR'
   OR'   ::= [Or] AND OR' | ε
   AND    ::= F AND'
   AND'   ::= [And] F AND' | ε
   F    ::= [Not] F | A | [OpenPar] E [ClosePar]

   ----- INSTR ----- (début BLOCK)

   EXPR  ::= E
   SKIP  ::= ε
   WHILE ::= [While] [OpenPar] EXPR [ClosePar] [OpenBrace] BLOCK [CloseBrace]
   ASSIG ::= VAR [Assignement] EXPR
   IF    ::= [If] [OpenPar] EXPR [ClosePar] [Then] [OpenBrace] BLOCK [CloseBrace] ELSE
   ELSE  ::= [Else] [OpenBrace] BLOCK [CloseBrace] | ε
   SEQ   ::= ([SemiColon] INSTR SEQ) | ε
   INSTR ::= ( WHILE | IF | ASSIGN | SKIP )
   BLOCK ::= INSTR SEQ 
*)

let rVAL : (bexp, token) ranalist =
  fun l -> match l () with
    | Cons(LexBoolean b, l) -> (Bcst b, l)
    | _ -> raise Echec
;;

let rVAR : (variable, token) ranalist =
  fun l -> match l () with
    | Cons (LexVariable v, l) -> (v, l)
    | _ -> raise Echec
;;

let rA : (bexp, token) ranalist = rVAL +| (rVAR ++> fun v -> epsilon_res (Ava v) );;

let rec rE : (bexp, token) ranalist = fun l -> 
  l |>
  (rOR ++> fun left -> rE' left)

and rE' : bexp -> (bexp, token) ranalist = fun left l -> 
  l |>
  (terminal LexEqual -+> rOR ++> fun right -> rE' (Equal (left, right)))
  +|
  epsilon_res left

and rOR : (bexp, token) ranalist = fun l ->
  l |>
  (rAND ++> fun left -> rOR' left)

and rOR' : bexp -> (bexp, token) ranalist = fun left l ->
  l |>
  (terminal LexOr -+> rAND ++> fun right -> rOR' (Or (left, right)))
  +|
  epsilon_res left

and rAND : (bexp, token) ranalist = fun l ->
  l |>
  (rF ++> fun left -> rAND' left)

and rAND' : bexp -> (bexp, token) ranalist = fun left l ->
  l |>
  (terminal LexAnd -+> rF ++> fun right -> rAND' (And (left, right)))
  +|
  epsilon_res left

and rF : (bexp, token) ranalist = fun l ->
  l |>
  (terminal LexNot -+> rF ++> fun exp -> epsilon_res (Not exp))
  +|
  rA
  +|
  (terminal LexOpenPar -+> rE +-> terminal LexClosePar)
;;

let rEXPR : (bexp, token) ranalist = rE;;

let rSKIP : (winstr, token) ranalist = epsilon_res Skip;;

let rASSIG : (winstr, token) ranalist = 
  fun l -> l |>
           rVAR +-> terminal LexAssignement ++> fun var -> rEXPR
                                                           ++> fun expr -> epsilon_res (Assign (var, expr))
;;

let rec rWHILE : (winstr, token) ranalist = 
  fun l -> l |>
           terminal LexWhile --> terminal LexOpenPar -+> rEXPR +-> terminal LexClosePar
           +-> terminal LexOpenBrace ++> fun cond -> rBLOCK +-> terminal LexCloseBrace
                                                     ++> fun codeBlock -> epsilon_res (While (cond, codeBlock))

and rIF : (winstr, token) ranalist = 
  fun l -> l |>
           terminal LexIf --> terminal LexOpenPar -+> rEXPR +-> terminal LexClosePar
           +-> terminal LexThen +-> terminal LexOpenBrace ++> fun cond -> rBLOCK +-> terminal LexCloseBrace
                                                                          ++> fun thenBlock -> rELSE ++> fun elseBlock -> epsilon_res (If (cond, thenBlock, elseBlock))

and rELSE : (winstr, token) ranalist =
  fun l -> l |>
           (terminal LexElse --> terminal LexOpenBrace -+> rBLOCK +-> terminal LexCloseBrace
            ++> fun elseBlock -> epsilon_res elseBlock)
           +|
           epsilon_res Skip

and rINSTR : (winstr, token) ranalist = fun l -> l |> rWHILE +| rIF +| rASSIG +| rSKIP 

and rSEQ : winstr -> (winstr, token) ranalist = fun left l ->
  l |>
  (terminal LexSemicolon -+> rINSTR ++> fun right -> rSEQ (Seq (left, right)))
  +|
  epsilon_res left

and rBLOCK : (winstr, token) ranalist = 
  fun l -> l |> 
           rINSTR ++> fun left -> rSEQ left
;;

let myLangToAST : (string -> winstr*token inflist) = fun l ->
  let (toks, _) = (lexer (inflist_of_string l)) in
  rBLOCK toks 
;;


(* Test *)

myLangToAST 
  "
a:=1;
if (a==true) 
then {b:=1} 
else {b:=false};

while (true) {}
";;

myLangToAST
  "
bb := 1;
ac := 1;
if (hagrid && bouteille == true) 
  then {bouteille := 1} 
  else{bouteille := false}
"
;;
